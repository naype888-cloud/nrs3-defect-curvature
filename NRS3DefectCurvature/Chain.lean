/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16f_HandleGraph

/-!
# The defect of transport fixes the curvature

The chain `D16`–`D16f` of the base repository, stated in one place. Transport `T_d` moves on the
path, a tree. A link between two sites creates a cycle exactly when it is not local; each cycle
carries one quantum `δ_∞ = C_∞ − 1` of defect; `2g` links carry the defect `2g δ_∞` of a closed
surface of genus `g`, and under Gauss–Bonnet that defect fixes its total curvature.

* `defect_fixes_curvature` : for the path with `2g` links, cycle rank `2g`, defect `Ω(Σ_g)` and
  `∫K dA = 4π − (2π/δ_∞) Ω(Σ_g)`.
* `handle_quanta` : one more handle is two links, `+2δ_∞` of defect and `−4π` of curvature.
* `cycle_iff_far` : a link creates a cycle iff it joins sites at distance `≥ 2`.
* `link_inside_cone` : the new cycle is unseen at distance `≥ k` for `k` steps.
* `quantum_by_dimension` : at `d = 2, 3` the defect is blind to the curvature; from `d = 4` the
  step `2δ(d)` is positive and below `2δ_∞`.

`HGaussBonnet` is a declared hypothesis, since Mathlib has no Gauss–Bonnet. Nothing here is a
claim about spin or mass.
-/

@[expose] public section

open SimpleGraph TransportPosition LightCone DefectExcitation DefectCycle HandleGraph Gnomon
  DimensionalQuantum

namespace DefectCurvature

/-- **The defect of transport fixes the curvature.** The path on `n + 1` sites with `2g`
non-local links has cycle rank `2g`; its defect is that of `Σ_g`, which fixes `∫K dA`. -/
theorem defect_fixes_curvature (H : HGaussBonnet) {n g : ℕ} (h : 2 * g + 1 ≤ n) :
    cycleRank (handleGraph n (2 * g)) = 2 * g ∧
      cycleDefectSum (cycleRank (handleGraph n (2 * g))) (fun _ => deltaInf) =
        closedSurfaceDefect g ∧
      H.totalCurvature g = 4 * Real.pi - (2 * Real.pi / deltaInf) * closedSurfaceDefect g :=
  ⟨cycleRank_handleGraph (by omega), handleGraph_defect h, H.totalCurvature_of_defect g⟩

/-- **One handle, two quanta.** The defect rises by `2δ_∞` and the curvature falls by `4π`. -/
theorem handle_quanta (H : HGaussBonnet) {n g : ℕ} (h : 2 * g + 3 ≤ n) :
    cycleDefectSum (cycleRank (handleGraph n (2 * (g + 1)))) (fun _ => deltaInf) -
        cycleDefectSum (cycleRank (handleGraph n (2 * g))) (fun _ => deltaInf) =
      2 * deltaInf ∧
      H.totalCurvature (g + 1) - H.totalCurvature g = -(4 * Real.pi) :=
  ⟨handleGraph_step h, DefectExcitation.HGaussBonnet.curvature_step H g⟩

/-- **Every cycle costs locality.** -/
theorem cycle_iff_far {n : ℕ} {a b : Fin (n + 1)} (hab : a ≠ b) :
    ¬ (withLink a b).IsAcyclic ↔ 2 ≤ distPath a b := by
  rw [withLink_isAcyclic_iff hab]
  omega

/-- **The new cycle travels inside the cone.** -/
theorem link_inside_cone {d : ℕ} (a b : Fin d) (ε : ℂ) (k : ℕ) (i : Fin d)
    (ha : k ≤ distPath i a) (hb : k ≤ distPath i b) (ψ : Hd d) :
    Matrix.toEuclideanLin (linkMatrix a b ε ^ k) ψ i =
      Matrix.toEuclideanLin (Td d ^ k) ψ i :=
  link_unseen a b ε k i ha hb ψ

/-- **The quantum by dimension.** Blind at `d = 2, 3`; from `d = 4`, `0 < 2δ(d) < 2δ_∞`. -/
theorem quantum_by_dimension (H : HGaussBonnet) :
    (∀ d, (d = 2 ∨ d = 3) → ∀ g, defectWith (dimQuantum d) g = 0) ∧
      H.totalCurvature 1 ≠ H.totalCurvature 0 ∧
      ∀ d, 4 ≤ d → 0 < 2 * dimQuantum d ∧ 2 * dimQuantum d < 2 * deltaInf :=
  ⟨fun _ hd => (DefectExcitation.HGaussBonnet.blind_at_saturation H hd).1,
    (DefectExcitation.HGaussBonnet.blind_at_saturation H (d := 2) (Or.inl rfl)).2,
    fun _ hd => dimStep_pos_lt hd⟩

end DefectCurvature
