#!/usr/bin/env python3
r"""Generate the Galton-board frame sequences used by the slides.

Two PNG sequences are produced, consumed by ``\animategraphics`` in main.tex:

  figs/single/frame_<n>.png   a single ball tracing one random path
  figs/swarm/frame_<n>.png    many balls falling and forming the bell curve

Usage (run from the slides/ directory so the figs/ paths line up)::

    python3 figs/galton_frames.py

Requires numpy + matplotlib.  When it finishes it prints the frame counts and
the exact ``\animategraphics`` lines to paste into the deck -- the LaTeX side
only needs the {first}{last} frame indices, which change if you tweak the
counts below.

Frame files use plain (non zero-padded) integer suffixes, e.g. frame_0.png,
frame_1.png, ... which is the form the `animate` package expects for its
{first}{last} arguments.
"""

import os
import numpy as np
import matplotlib

matplotlib.use("Agg")  # headless: write PNGs, never open a window
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle

# ----------------------------------------------------------------------
#  Board geometry and styling
# ----------------------------------------------------------------------
ROWS = 12          # number of peg rows  ->  ROWS + 1 bins
SX = 1.0           # horizontal peg spacing
SY = 1.0           # vertical peg spacing
PEG_TOP_Y = 0.0    # y of the apex peg (row 0)

BIN_TOP_Y = -ROWS * SY - 0.6     # top of the collecting bins
BIN_DEPTH = 6.0                  # vertical room the stacks may grow into
BIN_BOT_Y = BIN_TOP_Y - BIN_DEPTH

BALL_R = 0.20
PEG_R = 0.07

# Colours chosen to match the contribution slide: blue balls, gold curve.
BG = "white"
PEG_C = "#b0b0b0"
WALL_C = "#cccccc"
BALL_C = "#1565C0"   # \wprob blue
STACK_C = "#1565C0"
CURVE_C = "#C8960A"  # \wmech gold

# A little breathing room either side of the widest bin row.
HALF_W = ROWS / 2.0 * SX + 1.2
XLIM = (-HALF_W, HALF_W)
YLIM = (BIN_BOT_Y - 0.4, 1.4)

FIGSIZE = (6.4, 5.4)
DPI = 120

DIR_SINGLE = os.path.join("figs", "single")
DIR_SWARM = os.path.join("figs", "swarm")


# ----------------------------------------------------------------------
#  Lattice helpers
# ----------------------------------------------------------------------
def peg_x(r, k):
    """x of peg index k (0..r) in row r, centred on the board."""
    return (k - r / 2.0) * SX


def peg_y(r):
    return PEG_TOP_Y - r * SY


def bin_x(b):
    """Centre x of bin b (0..ROWS); aligns with the row-ROWS lattice."""
    return (b - ROWS / 2.0) * SX


def new_ax():
    """A fresh axes with the fixed extent every frame shares."""
    fig, ax = plt.subplots(figsize=FIGSIZE)
    ax.set_xlim(*XLIM)
    ax.set_ylim(*YLIM)
    ax.set_aspect("equal")
    ax.axis("off")
    fig.subplots_adjust(left=0, right=1, bottom=0, top=1)
    return fig, ax


def draw_board(ax, peg_alpha=1.0):
    """Pegs plus the bin dividers -- the static scaffolding."""
    for r in range(ROWS):
        for k in range(r + 1):
            ax.add_patch(
                Circle((peg_x(r, k), peg_y(r)), PEG_R,
                       color=PEG_C, alpha=peg_alpha, lw=0, zorder=1)
            )
    # Bin dividers: one wall between / around each of the ROWS+1 bins.
    for b in range(ROWS + 2):
        x = bin_x(b) - SX / 2.0
        ax.plot([x, x], [BIN_BOT_Y, BIN_TOP_Y],
                color=WALL_C, lw=1.0, zorder=1)


def save(fig, path):
    fig.savefig(path, dpi=DPI, facecolor=BG)
    plt.close(fig)


# ----------------------------------------------------------------------
#  Animation 1: a single ball
# ----------------------------------------------------------------------
SEED_SINGLE = 7
STEPS = 7      # interpolation frames per peg-to-peg segment
HOLD_SINGLE = 12   # frames the ball rests in its bin at the end


def hop(p0, p1, t, arc):
    """Interpolate p0->p1 with a small upward arc, for a bouncy feel."""
    x = p0[0] + (p1[0] - p0[0]) * t
    y = p0[1] + (p1[1] - p0[1]) * t + arc * np.sin(np.pi * t)
    return (x, y)


def single_waypoints(rng):
    rights = rng.integers(0, 2, size=ROWS)
    cum = np.concatenate(([0], np.cumsum(rights)))  # cum[r] = rights in first r rows
    total = int(cum[ROWS])

    wps = [(0.0, 1.0)]                       # falling in, above the apex
    for r in range(ROWS):
        wps.append((peg_x(r, int(cum[r])), peg_y(r)))   # peg it strikes in row r
    wps.append((bin_x(total), peg_y(ROWS - 1) - 0.8))   # clearing the last peg
    wps.append((bin_x(total), BIN_BOT_Y + BALL_R + 0.05))  # resting in the bin
    return wps


def build_single_positions(rng):
    wps = single_waypoints(rng)
    positions = [wps[0]]
    last = len(wps) - 1
    for i in range(last):
        # straight fall for the final plunge into the bin, gentle hop otherwise
        arc = 0.0 if i >= last - 1 else 0.18
        for s in range(1, STEPS + 1):
            positions.append(hop(wps[i], wps[i + 1], s / STEPS, arc))
    positions.extend([positions[-1]] * HOLD_SINGLE)
    return positions


def render_single():
    os.makedirs(DIR_SINGLE, exist_ok=True)
    rng = np.random.default_rng(SEED_SINGLE)
    positions = build_single_positions(rng)

    trail_len = 6
    for idx, pos in enumerate(positions):
        fig, ax = new_ax()
        draw_board(ax)
        # fading trail behind the ball
        lo = max(0, idx - trail_len)
        trail = positions[lo:idx]
        for j, (tx, ty) in enumerate(trail):
            a = 0.18 * (j + 1) / max(1, len(trail))
            ax.add_patch(Circle((tx, ty), BALL_R * 0.85,
                                 color=BALL_C, alpha=a, lw=0, zorder=2))
        ax.add_patch(Circle(pos, BALL_R, color=BALL_C, lw=0, zorder=3))
        save(fig, os.path.join(DIR_SINGLE, f"frame_{idx}.png"))
    return len(positions)


# ----------------------------------------------------------------------
#  Animation 2: a swarm forming the bell curve
# ----------------------------------------------------------------------
SEED_SWARM = 3
N_BALLS = 240
RELEASE_EVERY = 1     # frames between successive ball releases
T_FALL = 26           # frames for a ball to fall from the top to the bins
HOLD_SWARM = 18       # frames to linger on the finished histogram


def ease(t):
    """Ease-in (accelerating fall)."""
    return t * t


def render_swarm():
    os.makedirs(DIR_SWARM, exist_ok=True)
    rng = np.random.default_rng(SEED_SWARM)

    finals = rng.integers(0, 2, size=(N_BALLS, ROWS)).sum(axis=1)  # bin per ball
    start = np.arange(N_BALLS) * RELEASE_EVERY
    phase = rng.uniform(0, 2 * np.pi, size=N_BALLS)
    targets_x = np.array([bin_x(int(b)) for b in finals])

    total_frames = int(start[-1] + T_FALL + HOLD_SWARM)

    # Scale a ball-count into a stack height that just fits BIN_DEPTH.
    std_x = np.sqrt(ROWS * 0.25) * SX
    pdf0 = 1.0 / (std_x * np.sqrt(2 * np.pi))
    peak_count = N_BALLS * pdf0 * SX
    unit = BIN_DEPTH / (peak_count * 1.18)

    top_y = 1.0
    xs_curve = np.linspace(XLIM[0] + 0.5, XLIM[1] - 0.5, 240)

    for f in range(total_frames):
        fig, ax = new_ax()
        draw_board(ax, peg_alpha=0.55)

        landed = start + T_FALL <= f
        counts = np.bincount(finals[landed], minlength=ROWS + 1)
        n_landed = int(counts.sum())

        # stacked histogram, one bar per bin
        for b in range(ROWS + 1):
            h = counts[b] * unit
            if h <= 0:
                continue
            ax.add_patch(Rectangle((bin_x(b) - SX * 0.45, BIN_BOT_Y),
                                    SX * 0.9, h, color=STACK_C,
                                    alpha=0.85, lw=0, zorder=2))

        # emerging normal curve, fading in as the pile grows
        if n_landed > 4:
            pdf = np.exp(-(xs_curve ** 2) / (2 * std_x ** 2)) / (
                std_x * np.sqrt(2 * np.pi))
            ys_curve = BIN_BOT_Y + n_landed * pdf * SX * unit
            a = min(0.9, n_landed / N_BALLS + 0.15)
            ax.plot(xs_curve, ys_curve, color=CURVE_C, lw=2.4,
                    alpha=a, zorder=4)

        # balls currently in flight
        active = (start <= f) & (~landed)
        for i in np.where(active)[0]:
            t = (f - start[i]) / T_FALL
            y = top_y + (BIN_TOP_Y - top_y) * ease(t)
            wiggle = 0.35 * (1 - t) * np.sin(6.0 * np.pi * t + phase[i])
            x = targets_x[i] * t + wiggle
            ax.add_patch(Circle((x, y), BALL_R * 0.8,
                                 color=BALL_C, alpha=0.9, lw=0, zorder=3))

        save(fig, os.path.join(DIR_SWARM, f"frame_{f}.png"))
    return total_frames


# ----------------------------------------------------------------------
def main():
    n1 = render_single()
    n2 = render_swarm()
    print(f"\nsingle: {n1} frames in {DIR_SINGLE}/  (frame_0.png .. frame_{n1 - 1}.png)")
    print(f"swarm : {n2} frames in {DIR_SWARM}/  (frame_0.png .. frame_{n2 - 1}.png)")
    print("\nPaste into the deck (autoplay needs Adobe/pdfpc; others show one frame):")
    print(f"  \\animategraphics[autoplay,controls,width=0.7\\linewidth]"
          f"{{20}}{{figs/single/frame_}}{{0}}{{{n1 - 1}}}")
    print(f"  \\animategraphics[autoplay,loop,controls,width=0.85\\linewidth]"
          f"{{25}}{{figs/swarm/frame_}}{{0}}{{{n2 - 1}}}")


if __name__ == "__main__":
    main()
