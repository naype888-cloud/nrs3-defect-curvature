/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16i_CutHorizon

/-!
# The entropy of a cut, and what its horizon hides

The chain `D16g`–`D16i` of the base repository, stated in one place. Cut the path between
`c` and `c + 1`; the `M` non-local links across the cut each close a cycle.

* `entropy_counts_defect` : `k` quanta on the cut have entropy `(log M / δ_∞) · Ω`, and `k`
  distinct links are exactly the graphs of transport with `k` new cycles across the cut.
* `horizon_hides_entropy` : a site far from the cut reads every configuration of `m` links
  near it as plain transport for `k` steps; there are `C(M_w, m)` of them, each with defect
  `m δ_∞`.
* `bekenstein_hawking_fixes_area` : under the declared bridge `S = A / (4 ℓ_P²)`, the area per
  unit of defect is `4 ℓ_P² log M / δ_∞`.

The bridge is a declared hypothesis, shown satisfiable; the `1/4` is not derived.
-/

@[expose] public section

open SimpleGraph TransportPosition LightCone DefectCycle CutEntropy CutCycles CutHorizon

namespace DefectEntropy

open Classical in
/-- **The entropy counts the defect.** -/
theorem entropy_counts_defect (n c k : ℕ) :
    entropy n c k = Real.log (numCross n c) / Gnomon.deltaInf * defect k ∧
      (∀ S ∈ (crossLinks n c).powersetCard k, cycleRank (linksGraph n S) = k) ∧
      simpleEntropy n c k =
        Real.log (((crossLinks n c).powersetCard k).image (linksGraph n)).card := by
  refine ⟨entropy_eq_mul_defect n c k, fun S hS => ?_, ?_⟩
  · rw [Finset.mem_powersetCard] at hS
    rw [cycleRank_linksGraph hS.1, hS.2]
  · exact simpleEntropy_eq_log_card_graphs n c k

/-- **The horizon hides the entropy.** -/
theorem horizon_hides_entropy {n c w k m : ℕ} (ε : ℂ) {i : Fin (n + 1)}
    (hi : i.val + k + w ≤ c + 1) (ψ : Hd (n + 1)) :
    (∀ S ∈ (nearLinks n c w).powersetCard m,
      Matrix.toEuclideanLin (linksMatrix S ε ^ k) ψ i =
          Matrix.toEuclideanLin (Td (n + 1) ^ k) ψ i ∧
        Gnomon.cycleDefectSum (cycleRank (linksGraph n S)) (fun _ => Gnomon.deltaInf) =
          defect m) ∧
      ((nearLinks n c w).powersetCard m).card = (nearLinks n c w).card.choose m :=
  hidden_configurations ε hi ψ

/-- **Bekenstein–Hawking fixes the area of a quantum** (declared bridge). -/
theorem bekenstein_hawking_fixes_area {n c : ℕ} (H : HBekensteinHawking n c) :
    H.areaPerDefect = 4 * H.planckArea * Real.log (numCross n c) / Gnomon.deltaInf :=
  H.areaPerDefect_eq

end DefectEntropy
