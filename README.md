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

### Entropy and horizon

![Entropy and horizon](docs/figures/entropy_horizon.png)

| Statement | Lean |
|---|---|
| `k` quanta on the `M` crossing links of a cut have entropy `k log M = (log M / δ∞)·Ω`; `k` distinct links are exactly the graphs with `k` new cycles | `entropy_counts_defect` |
| a far site reads every configuration of `m` links near the cut as plain transport for `k` steps; `C(M_w, m)` of them, each with defect `m δ∞` | `horizon_hides_entropy` |
| under the declared bridge `S = A/(4ℓ_P²)`, `A = a₀ Ω`, the area per unit of defect is `a₀ = 4ℓ_P² log M / δ∞` | `bekenstein_hawking_fixes_area` |

The proofs are the modules `D16`–`D16i` of the
[base repository](https://github.com/naype888-cloud/nava-robertson-schrodinger), which this package requires;
`NRS3DefectCurvature/Chain.lean` and `NRS3DefectCurvature/Entropy.lean` state them in one place.

## What is declared

- **Gauss–Bonnet**, `∫K dA = 2πχ` (`HGaussBonnet`): Mathlib has no Gauss–Bonnet. It is shown
  satisfiable.
- **Bekenstein–Hawking**, `S = A/(4ℓ_P²)` (`HBekensteinHawking`): the `1/4` and the scale are
  not derived; the bridge is shown satisfiable. The coefficient `log M` depends on the cut.
  The horizon here is the finite-time light cone, not a black hole.
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
`python3 docs/simulation/figures_defect_curvature.py` and
`figures_entropy_horizon.py`.

## The mosaic

- [NRS and NRS³ — the base theorem](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [NRS³ · Mandelstam–Tamm and Cramér–Rao](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao)
- [NRS³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose)
- [NRS³ · Pauli–Dirac](https://github.com/naype888-cloud/nrs3-pauli-dirac)
- [NRS³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)
- **[NRS³ · Defect and curvature](https://github.com/naype888-cloud/nrs3-defect-curvature)** (this one)

## License

NRS Noncommercial License 1.0.0, see [`LICENSE`](LICENSE). Author: Eduardo Nava-Hernandez.
