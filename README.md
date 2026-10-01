# NRS³ · Defect and curvature

**The defect of transport fixes the curvature.** Transport `T_d` moves on the path, a tree. A
link between two sites closes a cycle exactly when it is not local; every cycle carries one
quantum `δ∞ = C∞ − 1`; `2g` links carry the defect `2g·δ∞` of a closed surface of genus `g`,
and under Gauss–Bonnet that defect fixes its total curvature. The change travels inside the light
cone, one site per step. In Lean 4.

**[▶ Try it: add handles and watch the cone](https://naype888-cloud.github.io/nrs3-defect-curvature/)**

![NRS³ · Defect and curvature](docs/figures/defect_curvature.png)

## Results

| Statement | Lean |
|---|---|
| the path with `2g` links `{0, j + 2}` has cycle rank `2g`, defect `Ω(Σ_g) = 2g·δ∞` and `∫K dA = 4π − (2π/δ∞) Ω(Σ_g)` | `defect_fixes_curvature` |
| one handle is two links: `+2δ∞` of defect and `−4π` of curvature | `handle_quanta` |
| a link closes a cycle iff it joins sites at distance `≥ 2` | `cycle_iff_far` |
| the new cycle is unseen at distance `≥ k` for `k` steps, for every state | `link_inside_cone` |
| at `d = 2, 3` the defect is `0` while the curvature still jumps; from `d = 4`, `0 < 2δ(d) < 2δ∞` | `quantum_by_dimension` |

The proofs are the modules `D16`–`D16f` of the
[base repository](https://github.com/naype888-cloud/nava-robertson-schrodinger), which this package requires;
`NRS3DefectCurvature/Chain.lean` states the chain in one place.

## What is declared

- **Gauss–Bonnet**, `∫K dA = 2πχ` (`HGaussBonnet`): Mathlib has no Gauss–Bonnet. It is shown
  satisfiable.
- The classical cell structure of `Σ_g`, whose `1`-skeleton has `2g` independent cycles. The
  graph of transport realizes those `2g` cycles (`cycleRank_handleGraph`); that it is the
  `1`-skeleton of a surface is not formalized.

Nothing here is a claim about spin or mass. The interior of the path is flat (`D28`, `D28b` in
the base repository): the curvature lives in the cycles, not on sites.

## Build

Lean 4 `v4.34.0`, Mathlib `v4.34.0` through the base repository.

```bash
lake exe cache get
lake build
lake env lean Verification/Axioms.lean   # only propext, Classical.choice, Quot.sound
```

Every file: no `sorry`, lines of at most 100 characters, English headers. The figure:
`python3 docs/simulation/figures_defect_curvature.py`.

## The mosaic

- [NRS and NRS³ — the base theorem](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [NRS³ · Mandelstam–Tamm and Cramér–Rao](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao)
- [NRS³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose)
- [NRS³ · Pauli–Dirac](https://github.com/naype888-cloud/nrs3-pauli-dirac)
- [NRS³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)
- **[NRS³ · Defect and curvature](https://github.com/naype888-cloud/nrs3-defect-curvature)** (this one)

## License

NRS Noncommercial License 1.0.0, see [`LICENSE`](LICENSE). Author: Eduardo Nava-Hernandez.
