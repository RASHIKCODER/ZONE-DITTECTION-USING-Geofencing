"""
ble_trilateration_map.py

Features:
- Load/paste GeoJSON office map (lon/lat) or use built-in sample.
- Uses real beacon coordinates (user-provided).
- Converts GeoJSON to local meters and aligns with beacon coordinates.
- Shows beacons, RSSI distance circles, trilaterated person, and movement trail.
- Toggle between MQTT live input and simulated RSSI for testing.
- Simple UI controls: Load GeoJSON, Toggle Simulation, Clear Trail.

Author: Generated for you
"""

import json
import math
import threading
import time
import random
import socket
import tkinter as tk
from tkinter import filedialog, simpledialog, messagebox

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from shapely.geometry import Polygon, shape

import paho.mqtt.client as mqtt

# ---------------------------
# Configuration (change if needed)
# ---------------------------
BROKER = ""   # use IP if DNS problems
PORT = 1883
USERNAME = ""
PASSWORD = ""
TOPIC = "sos"

SIMULATE = False  # start with simulation off by default

# ---------------------------
# Real beacon coordinates (meters) - user provided earlier
# ---------------------------
beacons = {
    "6720001010ed": {"x": 0.0, "y": 0.0, "rssi": -70},
    "672000101114": {"x": 10.58, "y": 0.0, "rssi": -70},
    "67200010110a": {"x": 10.43, "y": 8.03, "rssi": -70},
    "672000101129": {"x": 0.0, "y": 8.30, "rssi": -70},
}

# ---------------------------
# Default small sample GeoJSON (lon,lat) - used if user doesn't load a file
# ---------------------------
SAMPLE_GEOJSON = {
    "type": "FeatureCollection",
    "features": [
        {
            "type": "Feature",
            "geometry": {
                "type": "Polygon",
                "coordinates": [
                    [
                        [76.96853003379664, 28.40234456676545],
                        [76.96862090807213, 28.40238585484549],
                        [76.96864519579265, 28.402346007047527],
                        [76.96855295703642, 28.40230183838669],
                        [76.96853003379664, 28.40234456676545]
                    ]
                ]
            }
        }
    ]
}

# ---------------------------
# Globals used by plotting & threading
# ---------------------------
office_polygon = None   # shapely polygon in local meters aligned to beacons
trail = []
max_trail_len = 300
gui_root = None
fig = None
ax = None
canvas = None
position_label = None

# ---------------------------
# Utility: convert GeoJSON lon/lat -> local meters and align with beacons
# ---------------------------
def geojson_to_local_meters_and_align(geojson, beacons_dict):
    """
    Convert GeoJSON coordinates (lon,lat) to a local meters coordinate frame,
    scale/translate polygon so it fits/aligns reasonably with beacon coordinate frame.

    Returns: shapely Polygon (in meters aligned with beacons)
    """
    # Extract coordinates (support Polygon or LineString)
    feat = geojson["features"][0]
    geom = feat["geometry"]
    coords_list = []
    if geom["type"].lower() == "polygon":
        coords_list = geom["coordinates"][0]  # use first (outer) ring
    elif geom["type"].lower() == "linestring":
        coords_list = geom["coordinates"]
    else:
        # attempt to parse via shapely if possible
        shp = shape(geom)
        coords_list = list(shp.exterior.coords)

    # base lon/lat
    base_lon, base_lat = coords_list[0]
    m_per_deg_lat = 111139.0
    m_per_deg_lon = 111139.0 * math.cos(math.radians(base_lat))

    office_xy = [((lon - base_lon) * m_per_deg_lon, (lat - base_lat) * m_per_deg_lat) for lon, lat in coords_list]

    # normalize polygon so min -> (0,0)
    xs = [p[0] for p in office_xy]
    ys = [p[1] for p in office_xy]
    min_x, min_y = min(xs), min(ys)
    office_xy_norm = [(x - min_x, y - min_y) for x, y in office_xy]

    poly = Polygon(office_xy_norm)
    poly_minx, poly_miny, poly_maxx, poly_maxy = poly.bounds
    poly_w = poly_maxx - poly_minx if poly_maxx - poly_minx > 0 else 1.0
    poly_h = poly_maxy - poly_miny if poly_maxy - poly_miny > 0 else 1.0

    # beacon extents
    beacon_xs = [b["x"] for b in beacons_dict.values()]
    beacon_ys = [b["y"] for b in beacons_dict.values()]
    b_minx, b_miny, b_maxx, b_maxy = min(beacon_xs), min(beacon_ys), max(beacon_xs), max(beacon_ys)
    b_w = b_maxx - b_minx if b_maxx - b_minx > 0 else 1.0
    b_h = b_maxy - b_miny if b_maxy - b_miny > 0 else 1.0

    # Choose scale to fit polygon into beacon area (shrink-only)
    scale_x = b_w / poly_w
    scale_y = b_h / poly_h
    scale = min(scale_x, scale_y, 1.0)  # don't enlarge, only shrink if necessary

    # scale and translate polygon
    scaled = [((x - poly_minx) * scale, (y - poly_miny) * scale) for x, y in office_xy_norm]
    poly_scaled = Polygon(scaled)

    # center polygon near beacons centroid
    poly_cx, poly_cy = poly_scaled.centroid.x, poly_scaled.centroid.y
    beacon_cx = (b_minx + b_maxx) / 2.0
    beacon_cy = (b_miny + b_maxy) / 2.0
    dx = beacon_cx - poly_cx
    dy = beacon_cy - poly_cy
    final = [ (x + dx, y + dy) for x, y in scaled ]
    return Polygon(final)

# ---------------------------
# Positioning math
# ---------------------------
def rssi_to_distance(rssi, tx_power=-59, n=2.6):
    # log-distance path loss model
    return 10 ** ((tx_power - rssi) / (10 * n))

def trilaterate(b1, b2, b3):
    x1, y1, r1 = b1["x"], b1["y"], b1["dist"]
    x2, y2, r2 = b2["x"], b2["y"], b2["dist"]
    x3, y3, r3 = b3["x"], b3["y"], b3["dist"]

    A = 2 * (x2 - x1)
    B = 2 * (y2 - y1)
    C = r1**2 - r2**2 + x2**2 - x1**2 + y2**2 - y1**2
    D = 2 * (x3 - x1)
    E = 2 * (y3 - y1)
    F = r1**2 - r3**2 + x3**2 - x1**2 + y3**2 - y1**2

    denom = A * E - B * D
    if abs(denom) < 1e-6:
        return None
    x = (C * E - B * F) / denom
    y = (A * F - C * D) / denom
    return x, y

def calculate_position():
    # pick top 3 strongest RSSI beacons
    sorted_b = sorted(beacons.items(), key=lambda x: x[1]["rssi"], reverse=True)[:3]
    for _, b in beacons.items():
        b["dist"] = rssi_to_distance(b["rssi"])
    if len(sorted_b) < 3:
        return None
    try:
        b1, b2, b3 = [b[1] for b in sorted_b]
    except Exception:
        return None
    return trilaterate(b1, b2, b3)

# ---------------------------
# Plot update
# ---------------------------
def update_plot():
    global ax, canvas, position_label, office_polygon, trail

    ax.cla()

    # draw polygon if present
    if office_polygon is not None:
        px, py = office_polygon.exterior.xy
        ax.plot(px, py, linestyle="--", linewidth=2, label="Office (GeoJSON)")
        ax.fill(px, py, alpha=0.06)

    # draw beacons and distance circles
    for bid, b in beacons.items():
        ax.scatter(b["x"], b["y"], color="green", s=80, zorder=5)
        ax.text(b["x"] + 0.08, b["y"] + 0.08, bid[-6:], fontsize=9, color="darkgreen")
        dist = rssi_to_distance(b["rssi"])
        circle = plt.Circle((b["x"], b["y"]), dist, alpha=0.18, zorder=2)
        ax.add_patch(circle)

    # calculate position and draw person and trail
    pos = calculate_position()
    if pos:
        # append to trail
        trail.append(pos)
        if len(trail) > max_trail_len:
            trail.pop(0)
        txs = [p[0] for p in trail]
        tys = [p[1] for p in trail]
        ax.plot(txs, tys, "-", linewidth=2, alpha=0.7, zorder=4)
        ax.scatter(pos[0], pos[1], color="red", s=140, zorder=6, label="👤 Person")
        ax.text(pos[0] + 0.12, pos[1] + 0.12, f"({pos[0]:.2f},{pos[1]:.2f})", fontsize=10)
        position_label.config(text=f"📍 Person Position: X={pos[0]:.2f} m, Y={pos[1]:.2f} m")
    else:
        position_label.config(text="⚠️ Unable to calculate position")

    # limits - ensure beacons and polygon visible
    xs = [b["x"] for b in beacons.values()]
    ys = [b["y"] for b in beacons.values()]
    if office_polygon is not None:
        px, py = office_polygon.exterior.xy
        xs += list(px)
        ys += list(py)
    margin = 1.0
    ax.set_xlim(min(xs) - margin, max(xs) + margin)
    ax.set_ylim(min(ys) - margin, max(ys) + margin)

    ax.set_title("BLE Trilateration Map (GeoJSON Office + Beacon Layout)")
    ax.set_xlabel("X (m)")
    ax.set_ylabel("Y (m)")
    ax.grid(True)
    ax.legend(loc="upper right")
    ax.set_aspect("equal", adjustable="box")

    canvas.draw()

# ---------------------------
# MQTT handlers
# ---------------------------
def on_connect(client, userdata, flags, rc):
    if rc == 0:
        print("✅ Connected to MQTT broker")
        client.subscribe(TOPIC)
        print("📡 Subscribed to:", TOPIC)
    else:
        print("❌ MQTT connect failed rc=", rc)

def try_parse_rssi_value(raw):
    # Accept strings like "-70dBm", -70, or numeric
    if raw is None:
        return None
    if isinstance(raw, (int, float)):
        return float(raw)
    if isinstance(raw, str):
        rv = raw.replace("dBm", "").strip()
        try:
            return float(rv)
        except:
            return None
    # else
    return None

def on_message(client, userdata, msg):
    try:
        payload = msg.payload.decode()
        print("📩 MQTT:", payload)
        data = json.loads(payload)

        updated = False

        # Try common formats:
        # 1) { "uuid1":"id", "uuid1_rssi":"-70dBm", ... }
        for i in range(1, 9):
            uuid_key = f"uuid{i}"
            rssi_key = f"uuid{i}_rssi"
            if uuid_key in data and rssi_key in data and data[uuid_key] in beacons:
                val = try_parse_rssi_value(data[rssi_key])
                if val is not None:
                    beacons[data[uuid_key]]["rssi"] = val
                    updated = True

        # 2) If payload is a dict of id->rssi, e.g. { "6720001010ed": -70, ... }
        for k, v in data.items():
            if k in beacons:
                val = try_parse_rssi_value(v)
                if val is not None:
                    beacons[k]["rssi"] = val
                    updated = True

        # 3) If payload has "devices": [ {"id": "...", "rssi": -70}, ... ]
        if "devices" in data and isinstance(data["devices"], list):
            for d in data["devices"]:
                if "id" in d and "rssi" in d and d["id"] in beacons:
                    val = try_parse_rssi_value(d["rssi"])
                    if val is not None:
                        beacons[d["id"]]["rssi"] = val
                        updated = True

        if updated:
            gui_root.after(0, update_plot)

    except Exception as e:
        print("⚠️ MQTT parse error:", e)

def mqtt_thread():
    client = mqtt.Client()
    client.username_pw_set(USERNAME, PASSWORD)
    client.on_connect = on_connect
    client.on_message = on_message
    try:
        socket.gethostbyname(BROKER)
        client.connect(BROKER, PORT, 60)
    except Exception as e:
        print("❌ MQTT connection error:", e)
        return
    client.loop_forever()

# ---------------------------
# Simulation thread (smooth oscillation)
# ---------------------------
def simulate_rssi_loop():
    while True:
        t = time.time()
        # gentle oscillation so device appears to move
        for idx, bid in enumerate(list(beacons.keys())):
            beacons[bid]["rssi"] = -58 - 8 * math.sin(t * 0.5 + idx * 1.0) - (random.random() * 1.5)
        gui_root.after(0, update_plot)
        time.sleep(0.7)

# ---------------------------
# UI Callbacks
# ---------------------------
def load_geojson_from_file():
    global office_polygon
    path = filedialog.askopenfilename(title="Select GeoJSON file", filetypes=[("GeoJSON", "*.geojson *.json"), ("All files", "*.*")])
    if not path:
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            gj = json.load(f)
        office_polygon = geojson_to_local_meters_and_align(gj, beacons)
        update_plot()
        messagebox.showinfo("Loaded", "GeoJSON loaded and aligned to beacon frame.")
    except Exception as e:
        messagebox.showerror("Error", f"Failed to load GeoJSON: {e}")

def paste_geojson_text():
    global office_polygon
    text = simpledialog.askstring("Paste GeoJSON", "Paste the GeoJSON text (geometry or full featurecollection):")
    if not text:
        return
    try:
        gj = json.loads(text)
        office_polygon = geojson_to_local_meters_and_align(gj, beacons)
        update_plot()
        messagebox.showinfo("Loaded", "Pasted GeoJSON loaded and aligned.")
    except Exception as e:
        messagebox.showerror("Error", f"Invalid GeoJSON: {e}")

def toggle_simulation():
    global SIMULATE
    SIMULATE = not SIMULATE
    if SIMULATE:
        sim_btn.config(text="Simulation: ON", bg="#d0ffd0")
        # start simulation thread
        threading.Thread(target=simulate_rssi_loop, daemon=True).start()
    else:
        sim_btn.config(text="Simulation: OFF", bg="#ffd0d0")

def clear_trail():
    global trail
    trail = []
    update_plot()

def load_sample_geojson():
    global office_polygon
    office_polygon = geojson_to_local_meters_and_align(SAMPLE_GEOJSON, beacons)
    update_plot()
    messagebox.showinfo("Loaded", "Sample GeoJSON loaded and aligned.")

# ---------------------------
# Build GUI
# ---------------------------
def build_gui_and_start():
    global gui_root, fig, ax, canvas, position_label, sim_btn
    gui_root = tk.Tk()
    gui_root.title("BLE Trilateration Map (GeoJSON + Beacons)")
    gui_root.geometry("1100x760")

    # top frame controls
    top_frame = tk.Frame(gui_root)
    top_frame.pack(side=tk.TOP, fill=tk.X, padx=6, pady=4)

    btn_load = tk.Button(top_frame, text="Load GeoJSON File", command=load_geojson_from_file)
    btn_load.pack(side=tk.LEFT, padx=4)

    btn_paste = tk.Button(top_frame, text="Paste GeoJSON", command=paste_geojson_text)
    btn_paste.pack(side=tk.LEFT, padx=4)

    btn_sample = tk.Button(top_frame, text="Use Sample GeoJSON", command=load_sample_geojson)
    btn_sample.pack(side=tk.LEFT, padx=4)

    sim_btn = tk.Button(top_frame, text="Simulation: OFF", command=toggle_simulation, bg="#ffd0d0")
    sim_btn.pack(side=tk.LEFT, padx=12)

    clear_btn = tk.Button(top_frame, text="Clear Trail", command=clear_trail)
    clear_btn.pack(side=tk.LEFT, padx=4)

    info_label = tk.Label(top_frame, text="MQTT topic: {} (broker: {})".format(TOPIC, BROKER))
    info_label.pack(side=tk.RIGHT, padx=6)

    # plotting area
    fig_local, ax_local = plt.subplots(figsize=(10, 6))
    canvas_local = FigureCanvasTkAgg(fig_local, master=gui_root)
    canvas_local.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    fig, ax, canvas = fig_local, ax_local, canvas_local

    # position label
    position_label_local = tk.Label(gui_root, text="📍 Waiting for position data...", font=("Arial", 13), fg="blue")
    position_label_local.pack(side=tk.BOTTOM, pady=6)
    position_label = position_label_local

    # initialize office polygon with sample so UI isn't empty
    load_sample_geojson()

    # start MQTT thread
    threading.Thread(target=mqtt_thread, daemon=True).start()

    gui_root.protocol("WM_DELETE_WINDOW", gui_root.quit)
    gui_root.mainloop()

# ---------------------------
# Run
# ---------------------------
if __name__ == "__main__":
    build_gui_and_start()
