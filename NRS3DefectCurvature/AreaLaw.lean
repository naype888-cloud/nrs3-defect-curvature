/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37f_LightCone
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum

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

end AreaLaw
