"""Figure for the entropy of a cut and the horizon that hides it.

Writes docs/figures/entropy_horizon.png.

Left: entropy against the number of quanta k on the cut of a path with 21 sites between 10
and 11 (M crossing links): k log M for distinguishable quanta, which is (log M / δ∞) · Ω
(Lean: `entropy_counts_defect`); log C(M, k) for distinct links, the log of the number of
graphs (`simpleEntropy_eq_log_card_graphs`); the ceiling M log 2 (`simpleEntropy_le_max`).
Exact values. Right: |(L_S^k − L_S'^k) ψ| for two configurations S, S' of links within w sites
of the cut and a random state ψ; left of the cone it is exactly zero, so a site there cannot
tell S from S' (Lean: `horizon_hides_entropy`; values here numerical).

Run:  python3 docs/simulation/figures_entropy_horizon.py
"""

from math import comb, log

import matplotlib.pyplot as plt
import numpy as np

from style import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE

C_INF = np.sqrt(np.pi ** 2 / 3 - 2)
DELTA_INF = C_INF - 1


def cross_links(n, c, w=None):
    out = []
    for a in range(n + 1):
        for b in range(n + 1):
            if a <= c < b and a + 2 <= b and (w is None or (c + 1 <= a + w and b <= c + w)):
                out.append((a, b))
    return out


def links_matrix(d, links, eps):
    m = np.diag(np.ones(d - 1), 1) + np.diag(np.ones(d - 1), -1)
    m = m / (2 * np.cos(np.pi / (d + 1)))
    for a, b in links:
        m[a, b] += eps
        m[b, a] += eps
    return m


def panel_entropy(ax, n=20, c=10):
    m = len(cross_links(n, c))
    ks = np.arange(0, 31)
    s_dist = ks * log(m)
    s_simple = np.array([log(comb(m, k)) for k in ks])
    ax.plot(ks, s_dist, color=BLUE, lw=2, label=f"k quanta: k·log M = (log M/δ∞)·Ω")
    ax.plot(ks, s_simple, "o", color=ORANGE, mec=SURFACE, ms=5,
            label="k distinct links: log C(M, k) = log #graphs")
    ax.axhline(m * log(2), color=INK2, lw=1, ls="--")
    ax.text(30, m * log(2) - 3, f"ceiling for distinct links: M·log 2 = {m * log(2):.1f}", ha="right", va="top",
            color=INK2, fontsize=9.5)
    ax.set_xlabel("quanta on the cut  k = Ω / δ∞")
    ax.set_ylabel("entropy  S")
    sec = ax.secondary_xaxis("top", functions=(lambda k: k * DELTA_INF,
                                               lambda o: o / DELTA_INF))
    sec.set_xlabel("defect  Ω = k·δ∞", color=MUTED)
    ax.legend(loc="upper left", fontsize=8.8)
    ax.set_title(f"Entropy counts the defect  (21 sites, cut 10|11, M = {m})", loc="left",
                 fontsize=11.5)


def panel_horizon(ax, n=40, c=24, w=4, eps=0.35, kmax=16):
    d = n + 1
    near = cross_links(n, c, w)
    rng = np.random.default_rng(12)
    s1 = [near[i] for i in rng.choice(len(near), 3, replace=False)]
    s2 = [near[i] for i in rng.choice(len(near), 3, replace=False)]
    l1, l2 = links_matrix(d, s1, eps), links_matrix(d, s2, eps)
    psi = rng.normal(size=d) + 1j * rng.normal(size=d)
    psi /= np.linalg.norm(psi)
    v1, v2, diff = psi, psi, []
    for _ in range(kmax + 1):
        diff.append(np.abs(v1 - v2))
        v1, v2 = l1 @ v1, l2 @ v2
    diff = np.array(diff)
    img = np.where(diff > 0, np.log10(np.maximum(diff, 1e-300)), np.nan)
    cmap = plt.get_cmap("Oranges").copy()
    cmap.set_bad(GRID)
    im = ax.imshow(img, origin="lower", aspect="auto", cmap=cmap, vmin=-6, vmax=0,
                   extent=(-0.5, d - 0.5, -0.5, kmax + 0.5))
    ks = np.arange(kmax + 1)
    left = c + 1 - w
    ax.plot(left - ks - 0.5, ks, color=BLUE, lw=1.4, ls="--",
            label="horizon: i + k + w = c + 1")
    ax.axvspan(c + 1 - w - 0.5, c + w + 0.5, color=BLUE, alpha=0.06)
    ax.axvline(c + 0.5, color=INK2, lw=0.8)
    ax.text(c + 0.8, -0.2, "cut", color=INK2, fontsize=9, va="bottom")
    ax.set_xlabel(f"site i   (window of w = {w} sites around the cut {c}|{c + 1})")
    ax.set_ylabel("steps k")
    ax.grid(False)
    ax.legend(loc="upper left", fontsize=8.6)
    cb = plt.colorbar(im, ax=ax, fraction=0.05, pad=0.02)
    cb.set_label("log₁₀ |(L_S^k − L_S'^k) ψ|_i   (grey: exactly 0)", fontsize=8.6, color=INK2)
    ax.set_title("Two configurations, the same reading beyond the horizon", loc="left",
                 fontsize=11.5)
    hidden = max(diff[k, i] for k in ks for i in range(d) if i + k + w <= c + 1)
    return hidden


def fig_entropy_horizon():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(14.5, 4.9), dpi=150,
                                 gridspec_kw={"width_ratios": [1, 1.15]})
    panel_entropy(ax)
    hidden = panel_horizon(bx)
    fig.suptitle("NRS³ · the entropy of a cut and what its horizon hides (D16g–D16i)", x=0.01,
                 ha="left", fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "entropy_horizon.png", facecolor=SURFACE)
    plt.close(fig)
    print("max |difference| beyond the horizon:", hidden)


if __name__ == "__main__":
    fig_entropy_horizon()
