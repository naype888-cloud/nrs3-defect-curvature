/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3DefectCurvature.Chain
public import NRS3DefectCurvature.Entropy

/-!
# The entropy of a surface counts its curvature

The two halves of this repository meet. The `2g` links `{0, j + 2}` that fix the curvature of
`Σ_g` (`Chain`) all cross the cut between the sites `0` and `1`, so the surface is one of the
configurations whose entropy `Entropy` counts. Boltzmann and Planck's `S = log W` with
`W = M^{2g}`, and Einstein's curvature through Gauss–Bonnet, then give one line:

  `S(Σ_g) = (log M / 2π) · (4π − ∫K dA)`.

Each handle adds two quanta of defect, `2 log M` of entropy and `−4π` of curvature. The quantum
`δ_∞` cancels in the ratio and stays positive in each link: the defect is not swept away.

`HGaussBonnet` is the only hypothesis, declared as in `Chain`.

## Main results

- `EntropyCurvature.handleGraph_eq_linksGraph` : the graph of `Σ_g` is the path with the links
  of `handleLinks`.
- `EntropyCurvature.handleLinks_mem` : those `2g` links are a configuration on the cut at `0`.
- `EntropyCurvature.entropy_eq_curvature` : `S(Σ_g) = (log M / 2π) (4π − ∫K dA)`.
- `EntropyCurvature.entropy_handle_step` : one handle, `2 log M` of entropy and `−4π` of
  curvature.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectCycle HandleGraph CutEntropy CutCycles Gnomon

namespace EntropyCurvature

/-- The links `{0, j + 2}`, `j < k`, of the handle graph. -/
def handleLinks (n k : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  (Finset.range k).image fun j => (0, link n j)

/-- **The handle graph is a graph of links.** -/
theorem handleGraph_eq_linksGraph (n k : ℕ) : handleGraph n k = linksGraph n (handleLinks n k) := by
  induction k with
  | zero => simp [handleGraph, linksGraph, handleLinks]
  | succ k ih =>
    rw [handleGraph, ih, handleLinks, handleLinks, Finset.range_add_one, Finset.image_insert,
      linksGraph_insert]

theorem handleLinks_subset {n k : ℕ} (h : k + 1 ≤ n) : handleLinks n k ⊆ crossLinks n 0 := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  rw [mem_crossLinks]
  have := link_val (n := n) (j := j) (by simp at hj; omega)
  simp only [Fin.val_zero]
  omega

theorem card_handleLinks {n k : ℕ} (h : k + 1 ≤ n) : (handleLinks n k).card = k := by
  rw [handleLinks, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio, Prod.mk.injEq, true_and] at hi hj hij
  have := congrArg Fin.val hij
  rwa [link_val (by omega), link_val (by omega), Nat.add_right_cancel_iff] at this

/-- **The bridge**: the `2g` links of `Σ_g` are a configuration of `2g` quanta on the cut at
`0`; their graph is the graph of `Σ_g`. -/
theorem handleLinks_mem {n g : ℕ} (h : 2 * g + 1 ≤ n) :
    handleLinks n (2 * g) ∈ (crossLinks n 0).powersetCard (2 * g) ∧
      linksGraph n (handleLinks n (2 * g)) = handleGraph n (2 * g) :=
  ⟨Finset.mem_powersetCard.mpr ⟨handleLinks_subset h, card_handleLinks h⟩,
    (handleGraph_eq_linksGraph n _).symm⟩

/-- **The entropy of a surface counts its curvature**: `S(Σ_g) = (log M / 2π)(4π − ∫K dA)`. -/
theorem entropy_eq_curvature (H : HGaussBonnet) (n g : ℕ) :
    entropy n 0 (2 * g) =
      Real.log (numCross n 0) / (2 * Real.pi) * (4 * Real.pi - H.totalCurvature g) := by
  rw [entropy_eq, H.totalCurvature_of_defect, closedSurfaceDefect_eq_two_mul_genus_mul]
  field_simp [deltaInf_pos.ne', Real.pi_pos.ne']
  push_cast
  ring

/-- **One handle**: `2 log M` of entropy and `−4π` of curvature. -/
theorem entropy_handle_step (H : HGaussBonnet) (n g : ℕ) :
    entropy n 0 (2 * (g + 1)) - entropy n 0 (2 * g) = 2 * Real.log (numCross n 0) ∧
      H.totalCurvature (g + 1) - H.totalCurvature g = -(4 * Real.pi) := by
  refine ⟨?_, DefectExcitation.HGaussBonnet.curvature_step H g⟩
  rw [entropy_eq, entropy_eq]
  push_cast
  ring

end EntropyCurvature
