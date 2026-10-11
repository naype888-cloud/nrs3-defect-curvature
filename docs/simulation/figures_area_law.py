"""Figuras de AreaLaw: la ley de área del cubo y el interior oscuro leído en las caras.

Escribe docs/figures/area_law.png y docs/figures/area_law_dark.png.

area_law.png
(a)–(c) el plano entre x = c y x = c + 1 lo cruzan exactamente dy · dz pasos del transporte T3
(Lean: `T3_ne_zero_iff`, `card_crossSteps`): 4 × 4 × 4 y 10 × 4 × 4 dan 16, 4 × 8 × 8 da 64.
(d) S = dy · dz · log 2 no cambia con la profundidad dx; el volumen sí (`cutEntropy_eq`,
`cutEntropy_eq_of_depth`).
(e) S = (log 2 / δ(dx)) Ω desde dx ≥ 4; en dx = 2, 3 el defecto es 0 (`cutEntropy_eq_mul_cutDefect`,
`cutDefect_eq_zero`).
(f) Bekenstein–Hawking S = A / (4 ℓ_P²) se cumple iff cada paso ocupa a² = 4 ℓ_P² log 2
(`bekensteinHawking_iff`).

area_law_dark.png
(a) los tres cortes del cubo 4 × 7 × 10 y el cuanto volumétrico 𝒱 = δ(dx) δ(dy) δ(dz) adentro.
(b) los defectos de las tres caras de cuatro cajas.
(c) 𝒱 calculado adentro contra 𝒱 leído en las caras, (log 2)³ Ω_x Ω_y Ω_z / (S_x S_y S_z), para
todas las cajas de 4 a 12 posiciones por eje (`prod_cutDefect`, `volQuantum_eq_boundary`).
(d) la cadena: qué está firmado en Lean, qué es hipótesis declarada y qué falta (el gravitón).

δ(d) = C_Nava(d) − 1 se evalúa con la forma cerrada de C_Nava² (D19, D20) del repositorio base.

Run:  python3 docs/simulation/figures_area_law.py
"""

import itertools

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

from style import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE

GREEN, DARK = "#2f8f5b", "#1d1b2e"
plt.rcParams["font.family"] = ["DejaVu Sans", "STIXGeneral"]
C_INF = np.sqrt(np.pi ** 2 / 3 - 2)
LOG2 = np.log(2)


def c_nava(d):
    th = np.pi / (d + 1)
    s2 = np.sin(th) ** 2
    var_h = 4 * s2 * (d - 1) / (d + 1)
    var_x = ((d + 1) ** 2 + 2) / 12 - 1 / (2 * s2)
    return np.sqrt(max(var_h * var_x / np.cos(th) ** 2, 1.0))


def delta(d):
    return c_nava(d) - 1


def entropy(dy, dz):
    """S del corte en x: dy · dz pasos, cada uno abierto o cerrado."""
    return dy * dz * LOG2


def defect(dx, dy, dz):
    """Ω del corte en x: el cuanto δ(dx) en cada uno de los dy · dz pasos."""
    return dy * dz * delta(dx)


# ---------------------------------------------------------------- figura 1


def draw_cut(ax, box, c, title, col):
    dx, dy, dz = box
    pts = np.array(list(itertools.product(range(dx), range(dy), range(dz))))
    for (x, y, z) in pts:
        for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
            q = (x + e[0], y + e[1], z + e[2])
            if q[0] < dx and q[1] < dy and q[2] < dz and not (e[0] and x == c):
                ax.plot(*zip((x, y, z), q), color=GRID, lw=0.6, zorder=1)
    ax.scatter(*pts.T, s=6, color=MUTED, depthshade=False, zorder=2)
    plane = [[(c + .5, -.3, -.3), (c + .5, dy - .7, -.3), (c + .5, dy - .7, dz - .7),
              (c + .5, -.3, dz - .7)]]
    ax.add_collection3d(Poly3DCollection(plane, facecolor=col, alpha=0.13, edgecolor=col,
                                         linewidth=1))
    for y in range(dy):
        for z in range(dz):
            ax.plot([c, c + 1], [y, y], [z, z], color=col, lw=2.4, zorder=5)
    m = max(box)
    ax.set_xlim(0, m - 1); ax.set_ylim(0, m - 1); ax.set_zlim(0, m - 1)
    ax.set_box_aspect((dx, dy, dz), zoom=1.15 if dx > 4 else 1.0)
    ax.set_axis_off()
    ax.view_init(elev=18, azim=-58)
    ax.set_title(title, fontsize=10.5, color=INK, pad=-4)
    ax.text2D(0.5, 0.04, f"pasos que cruzan: {dy} · {dz} = {dy * dz}\n"
              f"volumen: {dx * dy * dz} posiciones", ha="center", va="top", fontsize=9.5,
              color=col, transform=ax.transAxes)


def fig_area_law():
    fig = plt.figure(figsize=(16, 10.6), dpi=150)
    gs = fig.add_gridspec(2, 3, height_ratios=[1.05, 1], hspace=0.32, wspace=0.28)
    fig.suptitle("La ley de área del cubo: la entropía de un corte cuenta su cara, no su volumen",
                 x=0.012, ha="left", fontsize=15, color=INK)

    draw_cut(fig.add_subplot(gs[0, 0], projection="3d"),
             (4, 4, 4), 1, "(a) 4 × 4 × 4, plano entre x = 1 y x = 2", ORANGE)
    draw_cut(fig.add_subplot(gs[0, 1], projection="3d"), (10, 4, 4), 4,
             "(b) 10 × 4 × 4: más profundo, los mismos pasos", ORANGE)
    draw_cut(fig.add_subplot(gs[0, 2], projection="3d"), (4, 8, 8), 1,
             "(c) 4 × 8 × 8: cara ×4, pasos ×4", BLUE)
    fig.text(0.5, 0.468, "T3 sólo avanza un paso en un eje (T3_local); por eso los únicos pasos que "
             "cruzan el plano van de (c, y, z) a (c + 1, y, z):  T3_ne_zero_iff, card_crossSteps",
             ha="center", fontsize=10, color=INK2)

    # (d) entropía contra profundidad
    ax = fig.add_subplot(gs[1, 0])
    depth = np.arange(4, 41)
    for (f, col) in ((4, ORANGE), (6, GREEN), (8, BLUE)):
        ax.plot(depth, np.full_like(depth, f * f), color=col, lw=2.2,
                label=f"cara {f} × {f}: S = {f * f} · log 2")
    ax.plot(depth, depth * 16 / 4, color=ORANGE, lw=1.4, ls="--",
            label="si fuera volumen (cara 4 × 4): crecería con dx")
    ax.set_xlabel("profundidad dx (posiciones a lo largo del corte)")
    ax.set_ylabel("entropía del corte  S / log 2  (bits)")
    ax.set_title("(d) S no cambia con la profundidad", loc="left")
    ax.set_ylim(0, 170)
    ax.legend(fontsize=9, loc="upper left")
    ax.text(40, 4, "cutEntropy_eq, cutEntropy_eq_of_depth", ha="right", fontsize=8.5,
            color=MUTED)

    # (e) entropía contra defecto
    bx = fig.add_subplot(gs[1, 1])
    faces = np.arange(0, 101)
    for (d, col) in ((4, ORANGE), (7, GREEN), (10, BLUE)):
        om = faces * delta(d)
        bx.plot(om, faces, color=col, lw=2.2,
                label=f"dx = {d}: δ = {delta(d):.4f},  pendiente log 2/δ = {LOG2 / delta(d):.1f}")
    bx.plot([0, 0], [0, 100], color=INK, lw=3, zorder=5,
            label="dx = 2, 3: δ = 0, Ω = 0 aunque S > 0 (satura)")
    bx.set_xlabel("defecto del corte  Ω = (dy · dz) · δ(dx)")
    bx.set_ylabel("S / log 2 = dy · dz  (pasos que cruzan)")
    bx.set_title("(e) desde dx ≥ 4:  S = (log 2 / δ) · Ω", loc="left")
    bx.set_xlim(-0.1, 6)
    bx.legend(fontsize=8.6, loc="lower right")
    bx.text(0.98, 0.30, "cutEntropy_eq_mul_cutDefect,\ncutDefect_eq_zero", transform=bx.transAxes,
            ha="right", fontsize=8.5, color=MUTED)

    # (f) Bekenstein–Hawking
    cx = fig.add_subplot(gs[1, 2])
    a = 2 * np.sqrt(LOG2)
    for i in range(4):
        for j in range(4):
            cx.add_patch(plt.Rectangle((i * a, j * a), a, a, facecolor=ORANGE, alpha=0.18,
                                       edgecolor=ORANGE, lw=1.2))
            cx.text((i + .5) * a, (j + .5) * a, "1 bit", ha="center", va="center", fontsize=8.5,
                    color=ORANGE)
    cx.add_patch(plt.Rectangle((4 * a + 0.6, 0), 1, 1, facecolor=INK, alpha=0.85))
    cx.text(4 * a + 1.1, 1.25, "ℓ_P × ℓ_P", ha="center", fontsize=9, color=INK)
    cx.annotate("", (0, -0.45), (a, -0.45), arrowprops=dict(arrowstyle="<->", color=INK2))
    cx.text(a / 2, -0.95, f"a = 2√(log 2) ℓ_P ≈ {a:.3f} ℓ_P", ha="center", fontsize=9,
            color=INK2)
    cx.set_xlim(-0.3, 4 * a + 2.6); cx.set_ylim(-1.4, 4 * a + 2.6)
    cx.set_aspect("equal"); cx.axis("off")
    cx.set_title("(f) Bekenstein–Hawking fija el área de un paso", loc="left")
    cx.text(0, 4 * a + 2.3, "cara 4 × 4 vista de frente: 16 pasos, 16 bits", fontsize=9.5,
            color=INK2, va="top")
    cx.text(0, 4 * a + 1.4, "S = A / (4 ℓ_P²)   ⟺   a² = 4 ℓ_P² log 2 ≈ 2.77 ℓ_P²",
            fontsize=10.5, color=INK, va="top")
    cx.text(0, 4 * a + 0.6, "(el bit de área de Bekenstein–Mukhanov 1995)  bekensteinHawking_iff",
            fontsize=8.5, color=MUTED, va="top")

    fig.text(0.012, 0.012, "Lean: nrs3-defect-curvature/NRS3DefectCurvature/AreaLaw.lean (sobre "
             "T3, T3_local de D37f). Entropía configuracional: cada paso que cruza está abierto o "
             "cerrado. δ(d) = C_Nava(d) − 1 (D25) de la forma cerrada de C_Nava² (D19, D20).",
             fontsize=8.5, color=MUTED)
    fig.savefig(OUT / "area_law.png", bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------- figura 2

FAMILY = {1: BLUE, 2: ORANGE, 3: GREEN}


def family(box):
    return {3: 3, 2: 2, 1: 1}[len(set(box))]


def box_faces(o, s):
    x0, y0, z0 = o
    a, b, c = s
    v = np.array([[x0 + i * a, y0 + j * b, z0 + k * c] for i in (0, 1) for j in (0, 1)
                  for k in (0, 1)])
    idx = [(0, 1, 3, 2), (4, 5, 7, 6), (0, 1, 5, 4), (2, 3, 7, 6), (0, 2, 6, 4), (1, 3, 7, 5)]
    return [[v[i] for i in f] for f in idx]


def fig_dark():
    fig = plt.figure(figsize=(16, 10.6), dpi=150)
    gs = fig.add_gridspec(2, 2, width_ratios=[1, 1.1], hspace=0.3, wspace=0.18)
    fig.suptitle("El interior oscuro se lee en las caras:  Ω_x Ω_y Ω_z = V² · 𝒱",
                 x=0.012, ha="left", fontsize=15, color=INK)

    # (a) tres cortes y el cuanto adentro
    ax = fig.add_subplot(gs[0, 0], projection="3d")
    dx, dy, dz = 4, 7, 10
    ax.add_collection3d(Poly3DCollection(box_faces((0, 0, 0), (dx - 1, dy - 1, dz - 1)),
                                         facecolor=(0, 0, 0, 0), edgecolor=MUTED, lw=0.7))
    cuts = [(ORANGE, [(1.5, 0, 0), (1.5, dy - 1, 0), (1.5, dy - 1, dz - 1), (1.5, 0, dz - 1)]),
            (BLUE, [(0, 3.5, 0), (dx - 1, 3.5, 0), (dx - 1, 3.5, dz - 1), (0, 3.5, dz - 1)]),
            (GREEN, [(0, 0, 4.5), (dx - 1, 0, 4.5), (dx - 1, dy - 1, 4.5), (0, dy - 1, 4.5)])]
    for col, q in cuts:
        ax.add_collection3d(Poly3DCollection([q], facecolor=col, alpha=0.16, edgecolor=col,
                                             lw=1.2))
    s = 1.4 / delta(dz)
    dims = [delta(d) * s for d in (dx, dy, dz)]
    o = (1.5 - dims[0] / 2, 3.5 - dims[1] / 2, 4.5 - dims[2] / 2)
    ax.add_collection3d(Poly3DCollection(box_faces(o, dims), facecolor=DARK, alpha=0.85,
                                         edgecolor=INK, lw=0.6))
    ax.set_xlim(0, 9); ax.set_ylim(0, 9); ax.set_zlim(0, 9)
    ax.set_box_aspect((1, 1, 1))
    ax.set_axis_off()
    ax.view_init(elev=16, azim=-60)
    ax.set_title("(a) caja 4 × 7 × 10: la luz cruza las tres caras;\n"
                 "adentro queda 𝒱 = δ(4) δ(7) δ(10) (dibujado ampliado)", fontsize=10.5,
                 color=INK)
    ax.text2D(0.08, 0.0, f"corte en x (naranja): Ω_x = 7·10·δ(4) = {defect(4, 7, 10):.3f}\n"
              f"corte en y (azul):    Ω_y = 10·4·δ(7) = {defect(7, 10, 4):.3f}\n"
              f"corte en z (verde):   Ω_z = 4·7·δ(10) = {defect(10, 4, 7):.3f}\n"
              f"𝒱 = {delta(4) * delta(7) * delta(10):.3e}", transform=ax.transAxes, va="top",
              fontsize=9, color=INK2)

    # (b) defectos de cara
    bx = fig.add_subplot(gs[0, 1])
    boxes = [(4, 4, 4), (10, 10, 10), (4, 10, 10), (4, 7, 10)]
    xs, labels = [], []
    for k, b in enumerate(boxes):
        dx_, dy_, dz_ = b
        oms = [defect(dx_, dy_, dz_), defect(dy_, dz_, dx_), defect(dz_, dx_, dy_)]
        col = FAMILY[family(b)]
        for j, (om, lab) in enumerate(zip(oms, ("Ω_x", "Ω_y", "Ω_z"))):
            x = k * 4 + j
            bx.bar(x, om, color=col, width=0.8)
            bx.text(x, om * 1.12, f"{om:.2f}", ha="center", fontsize=8, color=INK2)
            xs.append(x); labels.append(lab)
        prod = np.prod(oms)
        vq = np.prod([delta(d) for d in b])
        bx.text(k * 4 + 1, 220, f"{b[0]}×{b[1]}×{b[2]}", ha="center", fontsize=10, color=col)
        bx.text(k * 4 + 1, 90, f"Ω_xΩ_yΩ_z = {prod:.3g}\nV²·𝒱 = {np.prod(b) ** 2 * vq:.3g}",
                ha="center", fontsize=8, color=INK2)
    bx.set_yscale("log")
    bx.set_ylim(0.05, 400)
    bx.set_xticks(xs, labels, fontsize=8.5)
    bx.set_ylabel("Ω = área · δ(eje normal)")
    bx.set_title("(b) cada cara lleva el cuanto de su eje; el producto da V² · 𝒱  "
                 "(prod_cutDefect)", loc="left", fontsize=11.5)

    # (c) 𝒱 adentro contra 𝒱 leído en las caras
    cx = fig.add_subplot(gs[1, 0])
    for col_f, name in ((BLUE, "regular"), (ORANGE, "dos ejes iguales"),
                        (GREEN, "tres ejes distintos")):
        pts = []
        for b in itertools.product(range(4, 13), repeat=3):
            if FAMILY[family(b)] != col_f:
                continue
            inside = np.prod([delta(d) for d in b])
            oms = [defect(b[0], b[1], b[2]), defect(b[1], b[2], b[0]), defect(b[2], b[0], b[1])]
            ss = [entropy(b[1], b[2]), entropy(b[2], b[0]), entropy(b[0], b[1])]
            pts.append((inside, LOG2 ** 3 * np.prod(oms) / np.prod(ss)))
        pts = np.array(pts)
        cx.scatter(*pts.T, s=12 if col_f != BLUE else 40, color=col_f, alpha=0.7,
                   label=f"{name} ({len(pts)} cajas)", zorder=3 if col_f == BLUE else 2)
    lo, hi = delta(4) ** 3, (C_INF - 1) ** 3
    cx.plot([lo / 2, hi * 2], [lo / 2, hi * 2], color=INK, lw=1, ls="--", zorder=1)
    cx.axvline(hi, color=MUTED, lw=1, ls=":")
    cx.text(hi * 0.93, lo, "δ_∞³ (d → ∞,\nnunca se alcanza)", ha="right", fontsize=8.5,
            color=MUTED)
    cx.set_xscale("log"); cx.set_yscale("log")
    cx.set_xlabel("𝒱 calculado adentro:  δ(dx) δ(dy) δ(dz)")
    cx.set_ylabel("𝒱 leído en las caras:  (log 2)³ Ω_x Ω_y Ω_z / (S_x S_y S_z)")
    cx.set_title("(c) 729 cajas de 4 a 12 por eje: todas sobre la diagonal\n"
                 "     (volQuantum_eq_boundary)", loc="left", fontsize=11.5)
    cx.legend(fontsize=9, loc="upper left")

    # (d) la cadena
    dxa = fig.add_subplot(gs[1, 1])
    dxa.axis("off")
    dxa.set_title("(d) la cadena hacia la gravedad: qué está firmado y qué falta", loc="left",
                  fontsize=11.5)
    rows = [
        ("interior oscuro 𝒱 > 0 desde 4×4×4", "Lean", "D37e, nrs3-dark"),
        ("caras: Ω_x Ω_y Ω_z = V² · 𝒱", "Lean", "prod_cutDefect"),
        ("entropía del corte  S = área · log 2", "Lean", "cutEntropy_eq"),
        ("S = (log 2 / δ) · Ω", "Lean", "cutEntropy_eq_mul_cutDefect"),
        ("𝒱 se lee en la frontera", "Lean", "volQuantum_eq_boundary"),
        ("Bekenstein–Hawking ⟺ a² = 4 ℓ_P² log 2", "Lean", "bekensteinHawking_iff"),
        ("el valor 1/4 (ℓ_P real)", "calibración", "se fija, no se deriva"),
        ("curvatura = defecto (Gauss–Bonnet)", "hipótesis", "HGaussBonnet, D16"),
        ("cortes en y, z sobre el mismo cubo", "falta lema", "simetría de T3 (D37h)"),
        ("gravitón: diag(Ω_x, Ω_y, Ω_z) como espín 2", "abierto", "D37h + SL(2,ℂ)"),
        ("ecuaciones de Einstein", "abierto", "requiere RG en Lean"),
    ]
    tone = {"Lean": GREEN, "calibración": BLUE, "hipótesis": ORANGE, "falta lema": ORANGE,
            "abierto": INK}
    y = 0.95
    dxa.text(0.0, y, "eslabón", fontsize=10, color=INK, weight="bold", transform=dxa.transAxes)
    dxa.text(0.60, y, "estado", fontsize=10, color=INK, weight="bold", transform=dxa.transAxes)
    dxa.text(0.75, y, "dónde", fontsize=10, color=INK, weight="bold", transform=dxa.transAxes)
    for (what, st, where) in rows:
        y -= 0.083
        dxa.text(0.0, y, what, fontsize=9.6, color=INK2, transform=dxa.transAxes)
        dxa.text(0.60, y, st, fontsize=9.6, color=tone[st], weight="bold",
                 transform=dxa.transAxes)
        dxa.text(0.75, y, where, fontsize=8.8, color=MUTED, transform=dxa.transAxes)

    fig.text(0.012, 0.012, "Corte en y = corte en x de la caja con y primero (cutDefect dy dz dx); "
             "en z, cutDefect dz dx dy. Valores exactos de la forma cerrada de C_Nava² (D19, D20).",
             fontsize=8.5, color=MUTED)
    fig.savefig(OUT / "area_law_dark.png", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    fig_area_law()
    fig_dark()
