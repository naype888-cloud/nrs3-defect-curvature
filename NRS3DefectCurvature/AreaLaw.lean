/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37f_LightCone
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The area law of the cube

Cut the cube `dx × dy × dz` by the plane between `x = c` and `x = c + 1`. The total transport
`T3` moves one step along one axis (`T3_local`), so the only steps that cross the plane go from
`(c, y, z)` to `(c + 1, y, z)`: there are exactly `dy · dz` of them, the area of the face, and
their number does not depend on the depth `dx` nor on where the plane sits. Each crossing step is
open or closed, so the entropy of the cut is `S = dy · dz · log 2`: it grows as the area, not as
the volume `dx · dy · dz`.

From `dx ≥ 4` every crossing step carries the dimensional quantum `δ(dx) > 0`, and the entropy
is proportional to the defect of the cut, `S = (log 2 / δ) Ω`. The law
`S = A / (4 ℓ_P²)` of Bekenstein and Hawking is then no longer a hypothesis on the shape of `S`:
it holds exactly when each step has area `a² = 4 ℓ_P² log 2`, the bit of area of
Bekenstein and Mukhanov.

Cut the cube across each of its three axes. The light crosses the faces; the volumetric quantum
`𝒱 = δ(dx) δ(dy) δ(dz)` of `D37e` sits inside, where no face resolves it. The three face
defects multiply to `V² · 𝒱`, with `V = dx dy dz`, so the interior quantum is read on the
boundary: `𝒱 = (log 2)³ Ω_x Ω_y Ω_z / (S_x S_y S_z)`, the same at every size. It vanishes iff
one axis has `2` or `3` positions. The cut across an axis is the `x` cut of the cube with that
axis first: `cutDefect dy dz dx` cuts across `y`, `cutDefect dz dx dy` across `z`.

## Main results

- `AreaLaw.T3_ne_zero_iff` : a step crosses the plane iff it goes from `x = c` to `x = c + 1`
  keeping `y` and `z`.
- `AreaLaw.card_crossSteps` : there are `dy · dz` crossing steps.
- `AreaLaw.cutEntropy_eq` : the entropy of the cut is `dy · dz · log 2`.
- `AreaLaw.cutEntropy_eq_of_depth` : it does not depend on the depth nor on the plane.
- `AreaLaw.cutEntropy_eq_mul_cutDefect` : for `dx ≥ 4`, `S = (log 2 / δ) Ω`.
- `AreaLaw.bekensteinHawking_iff` : `S = a² A / (4 ℓ_P²)` iff `a² = 4 ℓ_P² log 2`.
- `AreaLaw.prod_cutDefect` : the three faces carry `Ω_x Ω_y Ω_z = V² · 𝒱`.
- `AreaLaw.volQuantum_eq_boundary` : the dark quantum of the interior is read on the faces,
  `𝒱 = (log 2)³ Ω_x Ω_y Ω_z / (S_x S_y S_z)`.
- `AreaLaw.bracketX_apply` : the bracket `[T3, P_x]` is `T3 p q (x_q − x_p)`.
- `AreaLaw.bracketCrossSteps_eq` : across the plane the bracket is nonzero exactly on the
  crossing steps, so `card_bracketCrossSteps` : the bracket sees `dy · dz` steps.
- `AreaLaw.cutEntropy_eq_bracket` : the entropy of the cut is read on the bracket.
- `AreaLaw.faceArea_eq`, `AreaLaw.faceArea_zero` : the face is the pseudovector
  `(dy ŷ) × (dz ẑ) = dy · dz · x̂`, whose length is the number of steps the bracket sees.
- `AreaLaw.bracketX_crossStep` : on a crossing step the bracket is `κ` forward and `−κ` back,
  `κ = 2 / (ρ (dx − 1))`: two values, one per direction of crossing.
- `AreaLaw.bracketX_stepTerm` : the bracket reads only the coherence `z = ψ̄_p ψ_q` of a step,
  through `κ (z − z̄)`.
- `AreaLaw.cutPatterns_eq` : every set of crossing steps is the set of open steps (`z ≠ 0`) of
  some unit state, so `card_cutPatterns` : there are `2 ^ (dy · dz)` patterns.
- `AreaLaw.cutCosmologicalConstant_eq` : the constant of a de Sitter horizon with the entropy of
  the cut, `Λ = 3 π / (ℓ² S) = 3 π / (ℓ² dy dz log 2)`.
- `AreaLaw.horizonArea_cutCosmologicalConstant` : with `a² = 4 ℓ² log 2` per step, the horizon
  area `12 π / Λ` is the area `a² dy dz` of the face.
- `AreaLaw.cutEntropy_eq_cutPatterns` : `S = log #patterns`. "Open or closed" is not a
  definition: it is whether the bracket reads a coherence on the step.
- `AreaLaw.openBackSteps_eq` : a step is open on the way back iff it is open on the way there;
  the coherence `ψ̄_p ψ_q` has no direction.
- `AreaLaw.backEntropy_eq_cutEntropy` : the entropy of the cut does not depend on the direction
  in which the plane is crossed.
- `AreaLaw.roundTripEntropy_eq`, `AreaLaw.roundTripEntropy_pos` : there and back gives
  `2 dy dz log 2 > 0`. The way back adds; it does not undo.

## References

* J. D. Bekenstein, *Black holes and entropy*, Phys. Rev. D 7 (1973) 2333–2346.
* S. W. Hawking, *Particle creation by black holes*, Commun. Math. Phys. 43 (1975) 199–220.
* J. D. Bekenstein and V. F. Mukhanov, *Spectroscopy of the quantum black hole*,
  Phys. Lett. B 360 (1995) 7–12.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone DimensionalQuantum VolumetricQuantum
open PathGraph3D (Site3D)

namespace AreaLaw

variable {dx dy dz : ℕ}

/-! ## 1. The steps that cross a plane -/

/-- Off the `x` axis the cube transport is the `x` transport on equal `y, z`. -/
lemma T3_apply_of_ne {p q : Site3D dx dy dz} (h : p.1 ≠ q.1) :
    T3 dx dy dz p q = Td dx p.1 q.1 * if p.2 = q.2 then 1 else 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only at h
  simp [T3, liftAlong, eX, eY, eZ, h]

/-- **A step crosses the plane iff it goes from `x = c` to `x = c + 1`, keeping `y, z`.** -/
theorem T3_ne_zero_iff (hd : 2 ≤ dx) {c : ℕ} {p q : Site3D dx dy dz} (hp : p.1.val ≤ c)
    (hq : c < q.1.val) :
    T3 dx dy dz p q ≠ 0 ↔ p.1.val = c ∧ q.1.val = c + 1 ∧ p.2 = q.2 := by
  have hne : p.1 ≠ q.1 := fun h => by rw [h] at hp; omega
  have hr : (rho dx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos dx hd).ne'
  rw [T3_apply_of_ne hne]
  by_cases hs : MinStep p.1 q.1
  · have : p.1.val = c ∧ q.1.val = c + 1 := by unfold MinStep at hs; omega
    by_cases h2 : p.2 = q.2 <;> simp [Td, Ad, hs, h2, hr, this]
  · simp only [Td, Ad, hs, ite_false, zero_div, zero_mul, ne_eq, not_true_eq_false, false_iff]
    exact fun ⟨h1, h2, _⟩ => hs (Or.inl (by omega))

open Classical in
/-- The steps of the cube transport across the plane between `x = c` and `x = c + 1`. -/
def crossSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.filter fun pq => pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ T3 dx dy dz pq.1 pq.2 ≠ 0

/-- **There are `dy · dz` crossing steps: the area of the face.** -/
theorem card_crossSteps {c : ℕ} (hc : c + 1 < dx) : (crossSteps dx dy dz c).card = dy * dz := by
  let f : Fin dy × Fin dz → Site3D dx dy dz × Site3D dx dy dz :=
    fun yz => ((⟨c, by omega⟩, yz), (⟨c + 1, hc⟩, yz))
  have hf : Function.Injective f := fun a b h => by
    simpa [f] using congrArg (fun pq => pq.1.2) h
  have : crossSteps dx dy dz c = Finset.univ.image f := by
    ext ⟨p, q⟩
    simp only [crossSteps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, f]
    constructor
    · rintro ⟨hp, hq, h⟩
      obtain ⟨h1, h2, h3⟩ := (T3_ne_zero_iff (by omega) hp hq).mp h
      exact ⟨p.2, by ext <;> simp [h1, h2, h3]⟩
    · rintro ⟨yz, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨le_rfl, by simp, (T3_ne_zero_iff (c := c) (by omega) le_rfl (by simp)).mpr (by simp)⟩
  rw [this, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

/-! ## 2. The entropy of the cut is an area -/

/-- Each crossing step is open or closed: the entropy of the cut is the log of the number of
sets of open steps. -/
def cutEntropy (dx dy dz c : ℕ) : ℝ := Real.log (crossSteps dx dy dz c).powerset.card

/-- **The area law: `S = dy · dz · log 2`.** -/
theorem cutEntropy_eq {c : ℕ} (hc : c + 1 < dx) :
    cutEntropy dx dy dz c = (dy * dz : ℕ) * Real.log 2 := by
  rw [cutEntropy, Finset.card_powerset, card_crossSteps hc, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]

/-- **The entropy does not see the depth.** Any depth, any plane: the same entropy. -/
theorem cutEntropy_eq_of_depth {dx' c c' : ℕ} (hc : c + 1 < dx) (hc' : c' + 1 < dx') :
    cutEntropy dx dy dz c = cutEntropy dx' dy dz c' := by
  rw [cutEntropy_eq hc, cutEntropy_eq hc']

/-! ## 3. Entropy and defect of the cut -/

/-- The defect of the cut: the quantum `δ(dx)` on each crossing step. -/
def cutDefect (dx dy dz c : ℕ) : ℝ := (crossSteps dx dy dz c).card * dimQuantum dx

/-- Below `4` positions the cut carries no defect. -/
theorem cutDefect_eq_zero (h : dx = 2 ∨ dx = 3) (c : ℕ) : cutDefect dx dy dz c = 0 := by
  rcases h with rfl | rfl <;> simp [cutDefect, dimQuantum_two, dimQuantum_three]

theorem cutDefect_pos (hd : 4 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ} (hc : c + 1 < dx) :
    0 < cutDefect dx dy dz c := by
  rw [cutDefect, card_crossSteps hc]
  exact mul_pos (by positivity) (dimQuantum_pos hd)

/-- **The entropy counts the defect: `S = (log 2 / δ) Ω`** from `4` positions on. -/
theorem cutEntropy_eq_mul_cutDefect (hd : 4 ≤ dx) {c : ℕ} (hc : c + 1 < dx) :
    cutEntropy dx dy dz c = Real.log 2 / dimQuantum dx * cutDefect dx dy dz c := by
  have := (dimQuantum_pos hd).ne'
  rw [cutEntropy_eq hc, cutDefect, card_crossSteps hc]
  field_simp

/-! ## 4. Bekenstein–Hawking -/

/-- **Bekenstein–Hawking fixes the area of a step.** With area `a²` per crossing step, the
law `S = A / (4 ℓ_P²)` holds iff `a² = 4 ℓ_P² log 2`. -/
theorem bekensteinHawking_iff {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ}
    (hc : c + 1 < dx) :
    cutEntropy dx dy dz c = a ^ 2 * (dy * dz : ℕ) / (4 * ℓ ^ 2) ↔
      a ^ 2 = 4 * ℓ ^ 2 * Real.log 2 := by
  have hA : ((dy * dz : ℕ) : ℝ) ≠ 0 := by positivity
  rw [cutEntropy_eq hc, eq_div_iff (by positivity)]
  constructor
  · intro h
    apply mul_right_cancel₀ hA
    linarith
  · intro h
    rw [h]
    ring

/-! ## 5. The interior is read on the faces -/

/-- **The three faces carry the interior: `Ω_x Ω_y Ω_z = V² · 𝒱`.** -/
theorem prod_cutDefect {cx cy cz : ℕ} (hx : cx + 1 < dx) (hy : cy + 1 < dy) (hz : cz + 1 < dz) :
    cutDefect dx dy dz cx * cutDefect dy dz dx cy * cutDefect dz dx dy cz =
      ((dx * dy * dz : ℕ) : ℝ) ^ 2 * volQuantum dx dy dz := by
  rw [cutDefect, cutDefect, cutDefect, card_crossSteps hx, card_crossSteps hy,
    card_crossSteps hz, volQuantum]
  push_cast
  ring

/-- **The dark quantum is read on the boundary:** `𝒱 = (log 2)³ Ω_x Ω_y Ω_z / (S_x S_y S_z)`. -/
theorem volQuantum_eq_boundary {cx cy cz : ℕ} (hx : cx + 1 < dx) (hy : cy + 1 < dy)
    (hz : cz + 1 < dz) :
    volQuantum dx dy dz = Real.log 2 ^ 3 *
      (cutDefect dx dy dz cx * cutDefect dy dz dx cy * cutDefect dz dx dy cz) /
      (cutEntropy dx dy dz cx * cutEntropy dy dz dx cy * cutEntropy dz dx dy cz) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hV : ((dx * dy * dz : ℕ) : ℝ) ≠ 0 := by
    have : 0 < dx * dy * dz := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    positivity
  rw [prod_cutDefect hx hy hz, cutEntropy_eq hx, cutEntropy_eq hy, cutEntropy_eq hz]
  push_cast at hV ⊢
  field_simp
  rw [eq_div_iff hV]
  ring

/-! ## 6. The bracket sees the crossing steps -/

/-- The `x` position of the cube: `P_d` on the `x` axis, identity on `y, z`. -/
def posX (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Pd dx)

/-- The bracket of the cube transport with the `x` position: `[T3, P_x]`. -/
def bracketX (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  T3 dx dy dz * posX dx dy dz - posX dx dy dz * T3 dx dy dz

lemma posX_apply (p q : Site3D dx dy dz) :
    posX dx dy dz p q = if p = q then (posCoord dx p.1 : ℂ) else 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  by_cases h : i = i' <;> by_cases h' : (j, k) = (j', k') <;>
    simp_all [posX, liftAlong, eX, Pd]

/-- **The bracket on a step is the step times the distance it moves in `x`.** -/
theorem bracketX_apply (p q : Site3D dx dy dz) :
    bracketX dx dy dz p q = T3 dx dy dz p q * ((posCoord dx q.1 : ℂ) - posCoord dx p.1) := by
  simp only [bracketX, Matrix.sub_apply, Matrix.mul_apply, posX_apply, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Distinct positions have distinct coordinates. -/
lemma posCoord_ne (hd : 2 ≤ dx) {i j : Fin dx} (h : i ≠ j) : posCoord dx i ≠ posCoord dx j := by
  intro h'
  have hd1 : (dx : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < dx := by exact_mod_cast (show 1 < dx by omega)
    linarith
  unfold posCoord at h'
  rw [div_left_inj' hd1] at h'
  exact h (Fin.ext (by exact_mod_cast (by linarith : (i.val : ℝ) = j.val)))

/-- **Across the plane the bracket is nonzero exactly where the transport is.** -/
theorem bracketX_ne_zero_iff (hd : 2 ≤ dx) {c : ℕ} {p q : Site3D dx dy dz} (hp : p.1.val ≤ c)
    (hq : c < q.1.val) : bracketX dx dy dz p q ≠ 0 ↔ T3 dx dy dz p q ≠ 0 := by
  have hne : q.1 ≠ p.1 := fun h => by rw [h] at hq; omega
  have hs : (posCoord dx q.1 : ℂ) - posCoord dx p.1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast posCoord_ne hd hne)
  rw [bracketX_apply, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

open Classical in
/-- The steps across the plane on which the bracket `[T3, P_x]` does not vanish. -/
def bracketCrossSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.filter fun pq => pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ bracketX dx dy dz pq.1 pq.2 ≠ 0

/-- **The bracket sees exactly the crossing steps.** -/
theorem bracketCrossSteps_eq (hd : 2 ≤ dx) (c : ℕ) :
    bracketCrossSteps dx dy dz c = crossSteps dx dy dz c := by
  ext ⟨p, q⟩
  simp only [bracketCrossSteps, crossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (bracketX_ne_zero_iff hd hp hq).mp h⟩
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (bracketX_ne_zero_iff hd hp hq).mpr h⟩

/-- **The bracket sees `dy · dz` steps across the plane, the area of the face.** -/
theorem card_bracketCrossSteps {c : ℕ} (hc : c + 1 < dx) :
    (bracketCrossSteps dx dy dz c).card = dy * dz := by
  rw [bracketCrossSteps_eq (by omega), card_crossSteps hc]

/-- **The entropy of the cut is read on the bracket.** -/
theorem cutEntropy_eq_bracket {c : ℕ} (hc : c + 1 < dx) :
    cutEntropy dx dy dz c = Real.log (bracketCrossSteps dx dy dz c).powerset.card := by
  rw [cutEntropy, bracketCrossSteps_eq (by omega)]

/-! ## 7. The face is a pseudovector -/

/-- The face across `x`: the pseudovector `(dy ŷ) × (dz ẑ)`. -/
def faceArea (dy dz : ℕ) : Fin 3 → ℝ :=
  crossProduct ((dy : ℝ) • ![(0 : ℝ), 1, 0]) ((dz : ℝ) • ![(0 : ℝ), 0, 1])

/-- **The face across `x` is `dy · dz · x̂`.** -/
theorem faceArea_eq (dy dz : ℕ) : faceArea dy dz = ![(dy * dz : ℝ), 0, 0] := by
  ext i
  fin_cases i <;> simp [faceArea, cross_apply]

/-- **The length of the face is the number of steps the bracket sees.** -/
theorem faceArea_zero {c : ℕ} (hc : c + 1 < dx) :
    faceArea dy dz 0 = (bracketCrossSteps dx dy dz c).card := by
  rw [faceArea_eq, card_bracketCrossSteps hc]
  simp

/-! ## 8. Open and closed: the bracket reads the coherence of a step -/

/-- A crossing step goes from `(c, y, z)` to `(c + 1, y, z)`. -/
lemma mem_crossSteps_iff (hd : 2 ≤ dx) {c : ℕ} {s : Site3D dx dy dz × Site3D dx dy dz} :
    s ∈ crossSteps dx dy dz c ↔ s.1.1.val = c ∧ s.2.1.val = c + 1 ∧ s.1.2 = s.2.2 := by
  simp only [crossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hq, h⟩
    exact (T3_ne_zero_iff hd hp hq).mp h
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.le, by omega, (T3_ne_zero_iff hd h1.le (by omega)).mpr ⟨h1, h2, h3⟩⟩

/-- A crossing step is fixed by where it lands. -/
lemma crossSteps_eq_of_snd (hd : 2 ≤ dx) {c : ℕ} {s t : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ crossSteps dx dy dz c) (ht : t ∈ crossSteps dx dy dz c) (h : s.2 = t.2) :
    s = t := by
  rw [mem_crossSteps_iff hd] at hs ht
  obtain ⟨⟨a, a'⟩, b⟩ := s
  obtain ⟨⟨e, e'⟩, f⟩ := t
  simp only at hs ht h
  subst h
  have : a = e := Fin.ext (by omega)
  rw [this, hs.2.2, ht.2.2]

/-- The constant of the bracket on one crossing step: `κ = 2 / (ρ (dx − 1))`. -/
def stepBracket (dx : ℕ) : ℝ := 2 / (rho dx * ((dx : ℝ) - 1))

/-- **On a crossing step the bracket is `κ` forward and `−κ` backward.** -/
theorem bracketX_crossStep (hd : 2 ≤ dx) {c : ℕ} {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ crossSteps dx dy dz c) :
    bracketX dx dy dz s.1 s.2 = (stepBracket dx : ℂ) ∧
      bracketX dx dy dz s.2 s.1 = -(stepBracket dx : ℂ) := by
  rw [mem_crossSteps_iff hd] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have hne : s.1.1 ≠ s.2.1 := fun h => by rw [h] at h1; omega
  have hpos := posCoord_succ_sub dx hd s.1.1 s.2.1 (by omega)
  have hr : (rho dx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos dx hd).ne'
  have hd1 : (dx : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < dx := by exact_mod_cast (show 1 < dx by omega)
    linarith
  have hT : T3 dx dy dz s.1 s.2 = 1 / (rho dx : ℂ) := by
    rw [T3_apply_of_ne hne]
    simp [Td, Ad, MinStep, h3, show s.1.1.val + 1 = s.2.1.val by omega]
  have hT' : T3 dx dy dz s.2 s.1 = 1 / (rho dx : ℂ) := by
    rw [T3_apply_of_ne hne.symm]
    simp [Td, Ad, MinStep, h3, show s.1.1.val + 1 = s.2.1.val by omega]
  have hx : (posCoord dx s.2.1 : ℂ) - posCoord dx s.1.1 = ((2 / ((dx : ℝ) - 1) : ℝ) : ℂ) := by
    rw [← hpos]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [bracketX_apply, hT, hx, stepBracket]
    push_cast
    field_simp
  · rw [bracketX_apply, hT', ← neg_sub, hx, stepBracket]
    push_cast
    field_simp

/-- The bracket has nothing on the diagonal. -/
theorem bracketX_self (p : Site3D dx dy dz) : bracketX dx dy dz p p = 0 := by
  rw [bracketX_apply, sub_self, mul_zero]

/-- **The bracket reads only the coherence of a step.** The contribution of a crossing step
to `⟨ψ, [T3, P_x] ψ⟩` is `κ (z − z̄)`, with `z = ψ̄_p ψ_q` the coherence between its two ends. -/
theorem bracketX_stepTerm (hd : 2 ≤ dx) {c : ℕ} {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ crossSteps dx dy dz c) (ψ : H3D dx dy dz) :
    star (ψ s.1) * bracketX dx dy dz s.1 s.2 * ψ s.2 +
        star (ψ s.2) * bracketX dx dy dz s.2 s.1 * ψ s.1 =
      (stepBracket dx : ℂ) * (star (ψ s.1) * ψ s.2 - star (star (ψ s.1) * ψ s.2)) := by
  obtain ⟨h1, h2⟩ := bracketX_crossStep hd hs
  rw [h1, h2, star_mul, star_star]
  ring

open Classical in
/-- The open steps of `ψ`: the crossing steps whose two ends carry coherence, `ψ̄_p ψ_q ≠ 0`.
On the others the bracket reads zero. -/
def openSteps (dx dy dz c : ℕ) (ψ : H3D dx dy dz) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  (crossSteps dx dy dz c).filter fun s => star (ψ s.1) * ψ s.2 ≠ 0

lemma openSteps_subset (c : ℕ) (ψ : H3D dx dy dz) :
    openSteps dx dy dz c ψ ⊆ crossSteps dx dy dz c :=
  Finset.filter_subset _ _

/-- Rescaling a state does not open or close a step. -/
lemma openSteps_smul (c : ℕ) {r : ℂ} (hr : r ≠ 0) (ψ : H3D dx dy dz) :
    openSteps dx dy dz c (r • ψ) = openSteps dx dy dz c ψ := by
  ext s
  have : star r * r ≠ 0 := mul_ne_zero (star_ne_zero.mpr hr) hr
  simp only [openSteps, Finset.mem_filter, PiLp.smul_apply, smul_eq_mul, star_mul]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun h0 => h' (by rw [show star (ψ s.1) * star r * (r * ψ s.2) =
      (star r * r) * (star (ψ s.1) * ψ s.2) by ring, h0, mul_zero])⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, by rw [show star (ψ s.1) * star r * (r * ψ s.2) =
      (star r * r) * (star (ψ s.1) * ψ s.2) by ring]; exact mul_ne_zero this h'⟩

open Classical in
/-- The vector that opens exactly the steps of `S`: `1` on their ends and on `p₀`. -/
def patternVec (p₀ : Site3D dx dy dz) (S : Finset (Site3D dx dy dz × Site3D dx dy dz)) :
    H3D dx dy dz :=
  WithLp.toLp 2 fun p => if p = p₀ ∨ ∃ s ∈ S, s.1 = p ∨ s.2 = p then 1 else 0

/-- **`patternVec p₀ S` opens exactly the steps of `S`.** -/
theorem openSteps_patternVec (hd : 2 ≤ dx) {c : ℕ} {p₀ : Site3D dx dy dz} (hp₀ : p₀.1.val = c)
    {S : Finset (Site3D dx dy dz × Site3D dx dy dz)} (hS : S ⊆ crossSteps dx dy dz c) :
    openSteps dx dy dz c (patternVec p₀ S) = S := by
  ext s
  rw [openSteps, Finset.mem_filter]
  simp only [patternVec]
  constructor
  · rintro ⟨hs, h⟩
    have hs' := (mem_crossSteps_iff hd).mp hs
    by_contra hns
    apply h
    have h2 : ¬ (s.2 = p₀ ∨ ∃ t ∈ S, t.1 = s.2 ∨ t.2 = s.2) := by
      rintro (h0 | ⟨t, ht, h0 | h0⟩)
      · rw [← h0] at hp₀; omega
      · have := ((mem_crossSteps_iff hd).mp (hS ht)).1
        rw [h0] at this; omega
      · exact hns (crossSteps_eq_of_snd hd hs (hS ht) h0.symm ▸ ht)
    simp only [h2, ↓reduceIte, mul_zero]
  · intro hs
    refine ⟨hS hs, ?_⟩
    have e1 : s.1 = p₀ ∨ ∃ t ∈ S, t.1 = s.1 ∨ t.2 = s.1 := Or.inr ⟨s, hs, Or.inl rfl⟩
    have e2 : s.2 = p₀ ∨ ∃ t ∈ S, t.1 = s.2 ∨ t.2 = s.2 := Or.inr ⟨s, hs, Or.inr rfl⟩
    simp only [e1, e2, ↓reduceIte]
    simp

open Classical in
/-- The patterns of open steps that unit states realize across the plane. -/
def cutPatterns (dx dy dz c : ℕ) : Finset (Finset (Site3D dx dy dz × Site3D dx dy dz)) :=
  (crossSteps dx dy dz c).powerset.filter fun S =>
    ∃ ψ : H3D dx dy dz, ‖ψ‖ = 1 ∧ openSteps dx dy dz c ψ = S

/-- **Every set of crossing steps is the open set of some unit state.** -/
theorem cutPatterns_eq {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    cutPatterns dx dy dz c = (crossSteps dx dy dz c).powerset := by
  classical
  ext S
  simp only [cutPatterns, Finset.mem_filter, Finset.mem_powerset, and_iff_left_iff_imp]
  intro hS
  let p₀ : Site3D dx dy dz := (⟨c, by omega⟩, ⟨0, hy⟩, ⟨0, hz⟩)
  let φ := patternVec p₀ S
  have hφ : φ ≠ 0 := fun h => by
    have := congrArg (fun v : H3D dx dy dz => v p₀) h
    simp [φ, patternVec] at this
  have hn : (‖φ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hφ)
  refine ⟨(‖φ‖ : ℂ)⁻¹ • φ, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)]
  · rw [openSteps_smul c (inv_ne_zero hn)]
    exact openSteps_patternVec (by omega) rfl hS

/-- **There are `2 ^ (dy · dz)` patterns: two per step, open or closed.** -/
theorem card_cutPatterns {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    (cutPatterns dx dy dz c).card = 2 ^ (dy * dz) := by
  rw [cutPatterns_eq hc hy hz, Finset.card_powerset, card_crossSteps hc]

/-- **The entropy of the cut counts the patterns the bracket reads.** No definition of
"open or closed" enters: `S = log #patterns = dy · dz · log 2`. -/
theorem cutEntropy_eq_cutPatterns {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    cutEntropy dx dy dz c = Real.log (cutPatterns dx dy dz c).card := by
  rw [cutEntropy, cutPatterns_eq hc hy hz]

/-! ## 9. The cosmological constant of the cut -/

/-- The constant of a de Sitter horizon of entropy `S = A / (4 ℓ²)` with `A = 12 π / Λ`, taking
for `S` the entropy of the cut: `Λ = 3 π / (ℓ² S)`. -/
def cutCosmologicalConstant (dx dy dz c : ℕ) (ℓ : ℝ) : ℝ :=
  3 * Real.pi / (ℓ ^ 2 * cutEntropy dx dy dz c)

/-- **`Λ = 3 π / (ℓ² dy dz log 2)`.** -/
theorem cutCosmologicalConstant_eq {c : ℕ} (hc : c + 1 < dx) (ℓ : ℝ) :
    cutCosmologicalConstant dx dy dz c ℓ =
      3 * Real.pi / (ℓ ^ 2 * ((dy * dz : ℕ) * Real.log 2)) := by
  rw [cutCosmologicalConstant, cutEntropy_eq hc]

theorem cutCosmologicalConstant_pos {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) : 0 < cutCosmologicalConstant dx dy dz c ℓ := by
  rw [cutCosmologicalConstant_eq hc]
  have : (0 : ℝ) < (dy * dz : ℕ) := by exact_mod_cast Nat.mul_pos hy hz
  have := Real.log_pos one_lt_two
  positivity

/-- **The horizon has the area of the face.** With `a² = 4 ℓ² log 2` per step, the area
`12 π / Λ` of the de Sitter horizon is `a² dy dz`. -/
theorem horizonArea_cutCosmologicalConstant {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy)
    (hz : 0 < dz) {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    12 * Real.pi / cutCosmologicalConstant dx dy dz c ℓ = a ^ 2 * (dy * dz : ℕ) := by
  have h1 : (0 : ℝ) < (dy * dz : ℕ) := by exact_mod_cast Nat.mul_pos hy hz
  have h2 := Real.log_pos one_lt_two
  rw [cutCosmologicalConstant_eq hc, ha]
  field_simp
  ring

/-! ## 10. The way back: the entropy of the cut has no direction -/

/-- A step run backwards: `(p, q) ↦ (q, p)`. -/
def reverseStep : Site3D dx dy dz × Site3D dx dy dz ↪ Site3D dx dy dz × Site3D dx dy dz :=
  (Equiv.prodComm _ _).toEmbedding

@[simp] lemma reverseStep_apply (s : Site3D dx dy dz × Site3D dx dy dz) :
    reverseStep s = s.swap := rfl

/-- The crossing steps run backwards, from `x = c + 1` to `x = c`. -/
def backSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  (crossSteps dx dy dz c).map reverseStep

lemma card_backSteps (c : ℕ) : (backSteps dx dy dz c).card = (crossSteps dx dy dz c).card :=
  Finset.card_map _

/-- The coherence of a step has no direction: `ψ̄_q ψ_p = conj (ψ̄_p ψ_q)`. -/
lemma coherence_swap_ne_zero (ψ : H3D dx dy dz) (p q : Site3D dx dy dz) :
    star (ψ q) * ψ p ≠ 0 ↔ star (ψ p) * ψ q ≠ 0 := by
  rw [show star (ψ q) * ψ p = star (star (ψ p) * ψ q) by rw [star_mul, star_star], ne_eq,
    star_eq_zero]

open Classical in
/-- The open steps of `ψ` on the way back. -/
def openBackSteps (dx dy dz c : ℕ) (ψ : H3D dx dy dz) :
    Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  (backSteps dx dy dz c).filter fun s => star (ψ s.1) * ψ s.2 ≠ 0

/-- **A step is open on the way back iff it is open on the way there.** -/
theorem openBackSteps_eq (c : ℕ) (ψ : H3D dx dy dz) :
    openBackSteps dx dy dz c ψ = (openSteps dx dy dz c ψ).map reverseStep := by
  ext s
  simp only [openBackSteps, backSteps, openSteps, Finset.mem_filter, Finset.mem_map,
    reverseStep_apply]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, h⟩
    exact ⟨t, ⟨ht, (coherence_swap_ne_zero ψ t.1 t.2).mp h⟩, rfl⟩
  · rintro ⟨t, ⟨ht, h⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (coherence_swap_ne_zero ψ t.1 t.2).mpr h⟩

open Classical in
/-- The patterns of open steps that unit states realize on the way back. -/
def backPatterns (dx dy dz c : ℕ) : Finset (Finset (Site3D dx dy dz × Site3D dx dy dz)) :=
  (backSteps dx dy dz c).powerset.filter fun S =>
    ∃ ψ : H3D dx dy dz, ‖ψ‖ = 1 ∧ openBackSteps dx dy dz c ψ = S

/-- **Every set of steps on the way back is the open set of some unit state.** -/
theorem backPatterns_eq {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    backPatterns dx dy dz c = (backSteps dx dy dz c).powerset := by
  classical
  ext T
  simp only [backPatterns, Finset.mem_filter, Finset.mem_powerset, and_iff_left_iff_imp]
  intro hT
  have hS : T.map reverseStep ⊆ crossSteps dx dy dz c := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp (hT ht)
    simpa using hu
  have hmem : T.map reverseStep ∈ cutPatterns dx dy dz c := by
    rw [cutPatterns_eq hc hy hz]
    exact Finset.mem_powerset.mpr hS
  obtain ⟨ψ, hψ, hψS⟩ := (Finset.mem_filter.mp hmem).2
  refine ⟨ψ, hψ, ?_⟩
  rw [openBackSteps_eq, hψS, Finset.map_map]
  ext s
  simp

/-- The entropy of the cut on the way back: `log #patterns`. -/
def backEntropy (dx dy dz c : ℕ) : ℝ := Real.log (backPatterns dx dy dz c).card

/-- **The entropy of the cut does not depend on the direction.** -/
theorem backEntropy_eq_cutEntropy {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    backEntropy dx dy dz c = cutEntropy dx dy dz c := by
  rw [backEntropy, backPatterns_eq hc hy hz, Finset.card_powerset, card_backSteps, cutEntropy,
    Finset.card_powerset]

/-- The entropy of a round trip across the plane: there and back. -/
def roundTripEntropy (dx dy dz c : ℕ) : ℝ := cutEntropy dx dy dz c + backEntropy dx dy dz c

/-- **The way back adds, it does not undo: `S_there + S_back = 2 dy dz log 2`.** -/
theorem roundTripEntropy_eq {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    roundTripEntropy dx dy dz c = 2 * ((dy * dz : ℕ) * Real.log 2) := by
  rw [roundTripEntropy, backEntropy_eq_cutEntropy hc hy hz, cutEntropy_eq hc]
  ring

/-- **The way back returns nothing: a round trip has positive entropy.** -/
theorem roundTripEntropy_pos {c : ℕ} (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    0 < roundTripEntropy dx dy dz c := by
  rw [roundTripEntropy_eq hc hy hz]
  have : (0 : ℝ) < (dy * dz : ℕ) := by exact_mod_cast Nat.mul_pos hy hz
  have := Real.log_pos one_lt_two
  positivity

end AreaLaw
