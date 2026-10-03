"""Figure for EntropyCurvature: the entropy of a surface counts its curvature.

Writes docs/figures/entropy_curvature.png.

Left: the path on n + 1 = 9 sites with the 2g = 4 links {0, j + 2} of Σ₂; all of them cross the
cut between the sites 0 and 1, so the surface is one configuration of 2g quanta on that cut
(Lean: `handleLinks_mem`). Right: S(Σ_g) = 2g log M against ∫K dA = 2π(2 − 2g) for several M;
every genus lies on the line S = (log M / 2π)(4π − ∫K dA) (`entropy_eq_curvature`), and each
handle moves by 2 log M up and 4π left (`entropy_handle_step`). Exact values; Gauss–Bonnet is the
declared hypothesis `HGaussBonnet`.

Run:  python3 docs/simulation/figures_entropy_curvature.py
"""

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Arc

from style import BLUE, INK, INK2, MUTED, ORANGE, OUT, SURFACE


def fig_entropy_curvature():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12.4, 4.8), dpi=150,
                                 gridspec_kw={"width_ratios": [1, 1.05]})

    n, g = 8, 2
    ax.plot([0, n], [0, 0], color=INK2, lw=2, zorder=1)
    for j in range(2 * g):
        b = j + 2
        ax.add_patch(Arc((b / 2, 0), b, 0.55 * b, theta1=0, theta2=180, lw=2,
                         color=ORANGE if j // 2 % 2 == 0 else BLUE))
    ax.scatter(range(n + 1), np.zeros(n + 1), s=55, color=SURFACE, edgecolor=INK, zorder=3)
    for i in range(n + 1):
        ax.text(i, -0.35, str(i), ha="center", color=MUTED, fontsize=9.5)
    ax.axvline(0.5, color=INK, lw=1.2, ls="--")
    ax.text(0.58, 1.75, "cut between 0 and 1:\nall 2g links cross it", color=INK2, fontsize=9.5)
    ax.text(n, 1.75, f"g = {g}: {2 * g} links = {g} handles\nM = n − 1 = {n - 1} crossing links",
            ha="right", color=INK2, fontsize=9.5)
    ax.set_xlim(-0.5, n + 0.5)
    ax.set_ylim(-0.6, 2.2)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title("Σ₂ is a configuration on the cut", loc="left", fontsize=11.5)

    gs = np.arange(0, 6)
    curv = 2 * np.pi * (2 - 2 * gs)
    for m, c in [(2, BLUE), (4, ORANGE), (7, INK)]:
        s = 2 * gs * np.log(m)
        k = np.linspace(curv.min() - 2, 4 * np.pi + 2, 50)
        bx.plot(k, np.log(m) / (2 * np.pi) * (4 * np.pi - k), color=c, lw=1.2, alpha=0.7)
        bx.plot(curv, s, "o", color=c, ms=6.5, mec=SURFACE, mew=1,
                label=f"M = {m}: slope −log M / 2π = {-np.log(m) / (2 * np.pi):.3f}")
    i = 2
    bx.annotate("", (curv[i + 1], 2 * (i + 1) * np.log(7)), (curv[i], 2 * i * np.log(7)),
                arrowprops=dict(arrowstyle="->", color=INK, lw=1.2))
    bx.text(curv[i] - 2 * np.pi - 1, 2 * (i + 0.5) * np.log(7) - 4.2,
            "one handle:\n+2 log M, −4π", ha="center", color=INK2, fontsize=9.5)
    for gg, kk in zip(gs, curv):
        bx.text(kk, -1.1, f"g={gg}", ha="center", color=MUTED, fontsize=8.5)
    bx.set_xlabel("total curvature ∫K dA = 2π(2 − 2g)")
    bx.set_ylabel("entropy S(Σ_g) = log M²ᵍ")
    bx.set_ylim(-1.8, 21)
    bx.legend(loc="upper right", fontsize=8.8)
    bx.set_title("S(Σ_g) = (log M / 2π)(4π − ∫K dA)", loc="left", fontsize=11.5)

    fig.suptitle("Boltzmann–Planck meets Gauss–Bonnet: the entropy of a surface counts its "
                 "curvature", x=0.01, ha="left", fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "entropy_curvature.png", facecolor=SURFACE)
    plt.close(fig)


if __name__ == "__main__":
    fig_entropy_curvature()
