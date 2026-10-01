"""Figure for the defect of transport and the curvature it fixes.

Writes docs/figures/defect_curvature.png.

Left: the path on n + 1 sites with the 2g non-local links {0, j + 2} of `handleGraph`; each link
closes one cycle (Lean: `cycleRank_handleGraph`). Middle: defect 2g·δ∞ and total curvature
2π(2 − 2g) against the genus; one handle is +2δ∞ and −4π (Lean: `handle_quanta`, exact values,
Gauss–Bonnet declared). Right: |(L^k − T_d^k) ψ| for T_d with one link {a, b}, a random state ψ;
outside the cone it is exactly zero (Lean: `link_inside_cone`; values here numerical).

Run:  python3 docs/simulation/figures_defect_curvature.py
"""

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Arc

from style import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE

C_INF = np.sqrt(np.pi ** 2 / 3 - 2)
DELTA_INF = C_INF - 1


def transport(d):
    a = np.diag(np.ones(d - 1), 1) + np.diag(np.ones(d - 1), -1)
    return a / (2 * np.cos(np.pi / (d + 1)))


def panel_graph(ax, n=9, g=2):
    xs = np.arange(n + 1)
    ax.plot(xs, np.zeros_like(xs), color=INK2, lw=2, zorder=1)
    for j in range(2 * g):
        b = j + 2
        ax.add_patch(Arc((b / 2, 0), b, 0.55 * b, theta1=0, theta2=180,
                         color=ORANGE if j // 2 == 0 else BLUE, lw=1.8))
    ax.scatter(xs, np.zeros_like(xs), s=70, color=SURFACE, edgecolor=INK, lw=1.4, zorder=3)
    for x in xs:
        ax.text(x, -0.45, str(x), ha="center", va="top", color=MUTED, fontsize=9)
    ax.text(0, 2.25, f"path on {n + 1} sites (a tree)\n+ {2 * g} links {{0, j+2}}\n"
            f"= cycle rank {2 * g} = b₁(Σ_{g})", color=INK2, fontsize=9.5, va="top")
    ax.text(5.6, 1.15, "two links per handle:\norange = handle 1\nblue = handle 2",
            color=INK2, fontsize=9, va="center")
    ax.set_xlim(-0.6, n + 0.6)
    ax.set_ylim(-1.0, 2.4)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title("Each non-local link closes one cycle", loc="left", fontsize=11.5)


def panel_genus(ax):
    g = np.arange(0, 6)
    defect = 2 * g * DELTA_INF
    curv = 2 * np.pi * (2 - 2 * g)
    ax.plot(g, defect, "o-", color=BLUE, mec=SURFACE, ms=7, label="defect 2g·δ∞")
    ax.set_xlabel("genus g")
    ax.set_ylabel("defect  Ω(Σ_g)", color=BLUE)
    ax.set_ylim(-0.1, 1.5)
    bx = ax.twinx()
    bx.plot(g, curv, "s-", color=ORANGE, mec=SURFACE, ms=7, label="∫K dA = 2π(2 − 2g)")
    bx.set_ylabel("total curvature  ∫K dA", color=ORANGE)
    bx.spines["right"].set_visible(True)
    bx.grid(False)
    bx.set_ylim(-60, 18)
    ax.annotate("+2δ∞", xy=(3, defect[3]), xytext=(2.2, defect[3] + 0.28), color=BLUE,
                fontsize=9.5, arrowprops=dict(arrowstyle="-", color=BLUE, lw=0.8))
    bx.annotate("−4π", xy=(3, curv[3]), xytext=(3.4, curv[3] + 8), color=ORANGE,
                fontsize=9.5, arrowprops=dict(arrowstyle="-", color=ORANGE, lw=0.8))
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = bx.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, loc="upper center", fontsize=8.6)
    ax.set_title(f"One handle: +2δ∞ ({2 * DELTA_INF:.4f}) and −4π", loc="left",
                 fontsize=11.5)


def panel_cone(ax, d=41, a=17, b=23, eps=0.35, kmax=14):
    t = transport(d)
    lnk = t.copy()
    lnk[a, b] += eps
    lnk[b, a] += eps
    rng = np.random.default_rng(16)
    psi = rng.normal(size=d) + 1j * rng.normal(size=d)
    psi /= np.linalg.norm(psi)
    diff = np.zeros((kmax + 1, d))
    pt, pl = np.eye(d), np.eye(d)
    for k in range(kmax + 1):
        diff[k] = np.abs(pl @ psi - pt @ psi)
        pt, pl = t @ pt, lnk @ pl
    img = np.where(diff > 0, np.log10(np.maximum(diff, 1e-300)), np.nan)
    cmap = plt.get_cmap("Blues").copy()
    cmap.set_bad(GRID)
    im = ax.imshow(img, origin="lower", aspect="auto", cmap=cmap, vmin=-6, vmax=0,
                   extent=(-0.5, d - 0.5, -0.5, kmax + 0.5))
    ks = np.arange(kmax + 1)
    ax.plot(a - ks, ks, color=ORANGE, lw=1.4, ls="--")
    ax.plot(b + ks, ks, color=ORANGE, lw=1.4, ls="--", label="cone: one site per step")
    ax.axvline(a, color=INK2, lw=0.6, ymax=0.04)
    ax.axvline(b, color=INK2, lw=0.6, ymax=0.04)
    ax.set_xlabel(f"site i   (link {{{a}, {b}}})")
    ax.set_ylabel("steps k")
    ax.grid(False)
    ax.legend(loc="upper right", fontsize=8.6)
    cb = plt.colorbar(im, ax=ax, fraction=0.05, pad=0.02)
    cb.set_label("log₁₀ |(L^k − T^k) ψ|_i   (grey: exactly 0)", fontsize=8.6, color=INK2)
    ax.set_title("The new cycle stays inside the cone", loc="left", fontsize=11.5)
    outside = [diff[k, i] for k in ks for i in range(d)
               if k <= abs(i - a) and k <= abs(i - b)]
    return max(outside)


def fig_defect_curvature():
    fig, axs = plt.subplots(1, 3, figsize=(16.5, 4.9), dpi=150,
                            gridspec_kw={"width_ratios": [1.05, 1, 1.15]})
    panel_graph(axs[0])
    panel_genus(axs[1])
    worst = panel_cone(axs[2])
    fig.suptitle("NRS³ · the defect of transport fixes the curvature (D16–D16f)", x=0.01,
                 ha="left", fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "defect_curvature.png", facecolor=SURFACE)
    plt.close(fig)
    print("max |difference| outside the cone:", worst)


if __name__ == "__main__":
    fig_defect_curvature()
