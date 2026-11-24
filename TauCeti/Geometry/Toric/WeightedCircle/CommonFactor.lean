/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.WeightedCircle.Basic
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Weighted circle actions with a common weight factor

Let `a` and `b` be positive weights, not necessarily coprime, and let `g = gcd(a, b)`. The circle
acts on `ℂ²` by `u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)` (`TauCeti.Toric.weightedRotation a b u`) and
preserves the ellipsoid `E : a |z₁|² + b |z₂|² = 2 ε` (`TauCeti.Toric.weightedEllipsoid a b ε`).
When `g > 1` this action is not effective: the stabilizer of every point off the two axes is the
cyclic group of `g`-th roots of unity
(`TauCeti.Toric.natCard_stabilizer_weightedEllipsoid_of_ne_zero`), so the generic isotropy is
ineffective of order `g`. This file records how such an action is related to the action with the
coprime weights `a / g` and `b / g`, keeping the two actions distinct.

* **Factoring through a power.** For weights `(k a, k b)`, the action of `u` is the action of
  `u ^ k` with weights `(a, b)` (`TauCeti.Toric.weightedRotation_pow`), and the ellipsoids agree
  after rescaling the level: `E(k a, k b, k ε) = E(a, b, ε)`
  (`TauCeti.Toric.weightedEllipsoid_mul_mul_mul`).
* **The ineffective kernel.** For `ε > 0`, a circle element acts trivially on the whole ellipsoid
  exactly when `u ^ g = 1` (`TauCeti.Toric.forall_smul_weightedEllipsoid_eq_self_iff`), so the
  kernel of the action is the cyclic group of `g`-th roots of unity, of order `g`
  (`TauCeti.Toric.natCard_fixingSubgroup_univ_weightedEllipsoid`). So the action on `E` is
  effective exactly when the weights are coprime
  (`TauCeti.Toric.faithfulSMul_weightedEllipsoid_iff`).
* **Orbits.** Since every circle element is a `k`-th power, the two actions have the same orbits
  (`TauCeti.Toric.exists_weightedRotation_mul_mul_eq_iff`). Hence the orbit spaces of the ellipsoid
  for the weights `(k a, k b)` at level `k ε` and for the weights `(a, b)` at level `ε` are
  homeomorphic, by the identity on points (`TauCeti.Toric.commonFactorOrbitHomeomorph`).
* **The quotient.** Composing with the coprime case `TauCeti.Toric.weightedOrbitHomeomorph`, for all
  positive weights and `ε > 0` the orbit space `E / S¹` is homeomorphic to the complex projective
  line by the reduced power map `[z] ↦ [z₁ ^ (b / g) : z₂ ^ (a / g)]`
  (`TauCeti.Toric.reducedWeightedOrbitHomeomorph`). The axis `z₂ = 0` is the fibre over `[1 : 0]`
  and the axis `z₁ = 0` the fibre over `[0 : 1]`. The reduction is needed: the power map
  `[z₁ ^ b : z₂ ^ a]` with the original weights separates the orbits exactly when the weights are
  coprime (`TauCeti.Toric.forall_weightedHopf_eq_imp_mem_orbit_iff`).

These are statements about the topology of the quotient and the isotropy of the action. The
homeomorphism with the coprime quotient is the identity on points, but the original action retains
its generic stabilizer of order `g` and its axial stabilizers of orders `a` and `b`; only the
action with the reduced weights is effective.

## References

* Eugene Lerman and Susan Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230 (weighted projective spaces as
  symplectic quotients).
-/

public section

noncomputable section

open Set Projectivization Real
open scoped LinearAlgebra.Projectivization

namespace TauCeti.Toric

variable {a b k : ℕ} {ε : ℝ}

/-! ### Factoring through a power of the circle -/

/-- **The action with weights `(k a, k b)` factors through the `k`-th power.** Rotating by `u ^ k`
with weights `(a, b)` is rotating by `u` with weights `(k a, k b)`. -/
theorem weightedRotation_pow (u : Circle) (z : ℂ × ℂ) :
    weightedRotation a b (u ^ k) z = weightedRotation (k * a) (k * b) u z :=
  Prod.ext (by simp [← pow_mul]) (by simp [← pow_mul])

/-- **Rescaling the ellipsoid.** The level `k ε` for the weights `(k a, k b)` is the level `ε` for
the weights `(a, b)`. -/
theorem weightedEllipsoid_mul_mul_mul (hk : k ≠ 0) :
    weightedEllipsoid (k * a) (k * b) (k * ε) = weightedEllipsoid a b ε := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  ext z
  simp only [mem_weightedEllipsoid, Nat.cast_mul]
  constructor <;> intro h
  · exact mul_left_cancel₀ hk' (by linear_combination h)
  · linear_combination k * h

/-- **The actions with weights `(k a, k b)` and `(a, b)` have the same orbits** on `ℂ²`, since every
circle element is a `k`-th power. -/
theorem exists_weightedRotation_mul_mul_eq_iff (hk : k ≠ 0) {z w : ℂ × ℂ} :
    (∃ u : Circle, weightedRotation (k * a) (k * b) u w = z) ↔
      ∃ u : Circle, weightedRotation a b u w = z := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u ^ k, by rwa [weightedRotation_pow]⟩, fun ⟨u, hu⟩ ↦ ?_⟩
  obtain ⟨v, rfl⟩ := Circle.exists_pow_nat_eq u hk
  exact ⟨v, by rwa [← weightedRotation_pow]⟩

/-! ### The ineffective kernel -/

/-- A point of the ellipsoid with both coordinates nonzero, for positive weights and `ε > 0`. -/
theorem exists_mem_weightedEllipsoid_ne_zero (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ z ∈ weightedEllipsoid a b ε, z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  obtain ⟨t, ht, hz⟩ := exists_pos_mem_weightedEllipsoid ha hb hε
    (r := (1, 1)) (by simp [Prod.ext_iff])
  exact ⟨_, hz, by simp [ht.ne'], by simp [ht.ne']⟩

/-- A point of the ellipsoid off the axis `z₁ = 0`, for a positive weight `a` and `ε > 0`. The
weight `b` may vanish. -/
private theorem exists_mem_weightedEllipsoid_fst_ne_zero (ha : 0 < a) (hε : 0 < ε) :
    ∃ z ∈ weightedEllipsoid a b ε, z.1 ≠ 0 := by
  have : (0 : ℝ) < a := Nat.cast_pos.2 ha
  refine ⟨((√(2 * ε / a) : ℝ), 0), ?_,
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by positivity))⟩
  rw [mem_weightedEllipsoid, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]
  field_simp
  simp

/-- **The ineffective kernel of the action.** For `ε > 0`, a circle element acts trivially on the
whole ellipsoid exactly when it is a `gcd(a, b)`-th root of unity. The weights may vanish. -/
theorem forall_smul_weightedEllipsoid_eq_self_iff (hε : 0 < ε) {u : Circle} :
    (∀ z : weightedEllipsoid a b ε, u • z = z) ↔ u ^ a.gcd b = 1 := by
  simp only [pow_gcd_eq_one, ← Subtype.coe_inj, coe_smul_weightedEllipsoid,
    weightedRotation_eq_self_iff, Subtype.forall]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h _ _ ↦ ⟨fun _ ↦ h.1, fun _ ↦ h.2⟩⟩
  · rcases a.eq_zero_or_pos with rfl | ha
    · exact pow_zero u
    obtain ⟨z, hz, h₁⟩ := exists_mem_weightedEllipsoid_fst_ne_zero (b := b) ha hε
    exact (h z hz).1 h₁
  · rcases b.eq_zero_or_pos with rfl | hb
    · exact pow_zero u
    obtain ⟨z, hz, h₂⟩ := exists_mem_weightedEllipsoid_fst_ne_zero (b := a) hb hε
    exact (h z.swap (swap_mem_weightedEllipsoid.2 hz)).2 h₂

/-- **The ineffective kernel as a subgroup.** For `ε > 0`, the subgroup of circle elements fixing
every point of the ellipsoid is the group of `gcd(a, b)`-th roots of unity. -/
theorem fixingSubgroup_univ_weightedEllipsoid (hε : 0 < ε) :
    fixingSubgroup Circle (univ : Set (weightedEllipsoid a b ε)) =
      (powMonoidHom (a.gcd b)).ker := by
  ext u
  simpa [mem_fixingSubgroup_iff] using forall_smul_weightedEllipsoid_eq_self_iff hε

/-- **The `Nat.card` of the ineffective kernel is `gcd(a, b)`** for `ε > 0`. When at least one
weight is positive, this is the finite order of the kernel. For `a = b = 0` the kernel is the whole
circle, which is infinite, so its `Nat.card` is `0` rather than an order. -/
theorem natCard_fixingSubgroup_univ_weightedEllipsoid (hε : 0 < ε) :
    Nat.card (fixingSubgroup Circle (univ : Set (weightedEllipsoid a b ε))) = a.gcd b := by
  rw [fixingSubgroup_univ_weightedEllipsoid hε]
  rcases (a.gcd b).eq_zero_or_pos with h | h
  · have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
    have : Infinite Circle := .of_injective _ (AddCircle.injective_toCircle two_pi_pos.ne')
    simp [h]
  · have : NeZero (a.gcd b) := ⟨h.ne'⟩
    exact natCard_powMonoidHom_ker Circle _

/-- **The action on the ellipsoid is effective exactly for coprime weights**, for `ε > 0`. The
weights may vanish. -/
theorem faithfulSMul_weightedEllipsoid_iff (hε : 0 < ε) :
    FaithfulSMul Circle (weightedEllipsoid a b ε) ↔ a.Coprime b := by
  rw [Nat.Coprime, ← natCard_fixingSubgroup_univ_weightedEllipsoid hε, Subgroup.card_eq_one,
    Subgroup.eq_bot_iff_forall, faithfulSMul_iff]
  simp [mem_fixingSubgroup_iff]

/-! ### The orbit space -/

/-- **The orbit space does not see a common weight factor.** For `k ≠ 0`, `a = k a'`, `b = k b'`
and `ε = k ε'`, the ellipsoids `E(a, b, ε)` and `E(a', b', ε')` are the same subset of `ℂ²`, with
the same orbits, so their orbit spaces are homeomorphic by the identity on points. The action with
the weights `(a, b)` is the action with the weights `(a', b')` precomposed with `u ↦ u ^ k`, and
has the additional ineffective stabilizer of `k`-th roots of unity. -/
def commonFactorOrbitHomeomorph {a' b' : ℕ} {ε' : ℝ} (hk : k ≠ 0) (ha : a = k * a')
    (hb : b = k * b') (hε : ε = k * ε') :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) ≃ₜ
      MulAction.orbitRel.Quotient Circle (weightedEllipsoid a' b' ε') :=
  Homeomorph.Quotient.congr
    (Homeomorph.setCongr (by rw [ha, hb, hε, weightedEllipsoid_mul_mul_mul hk])) fun z w ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← Subtype.coe_inj,
        coe_smul_weightedEllipsoid, Homeomorph.setCongr, Homeomorph.homeomorph_mk_coe,
        Set.equivOfEq_apply]
      subst ha hb
      exact exists_weightedRotation_mul_mul_eq_iff hk

/-- The homeomorphism of orbit spaces sends the orbit of `z` to the orbit of the same point. -/
theorem commonFactorOrbitHomeomorph_mk {a' b' : ℕ} {ε' : ℝ} (hk : k ≠ 0) (ha : a = k * a')
    (hb : b = k * b') (hε : ε = k * ε') (z : weightedEllipsoid a b ε)
    (hz : (z : ℂ × ℂ) ∈ weightedEllipsoid a' b' ε') :
    commonFactorOrbitHomeomorph hk ha hb hε (Quotient.mk _ z) = Quotient.mk _ ⟨z, hz⟩ :=
  (rfl)

/-- **The power map separates orbits exactly for coprime weights.** For positive weights and
`ε > 0`, the weighted Hopf map `z ↦ [z₁ ^ b : z₂ ^ a]` has the orbits as its fibres exactly when
`a` and `b` are coprime. If `g = gcd(a, b) > 1`, the points `(z₁, z₂)` and `(z₁, ζ z₂)` of the
ellipsoid, for a primitive `a`-th root of unity `ζ`, have the same image but lie in different
orbits: a circle element `u` carrying one to the other has `uᵃ = 1` and `uᵇ = ζ`, so
`ζ ^ (a / g) = (uᵃ) ^ (b / g) = 1`. -/
theorem forall_weightedHopf_eq_imp_mem_orbit_iff (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    (∀ z w : weightedEllipsoid a b ε, weightedHopf hε z = weightedHopf hε w →
      z ∈ MulAction.orbit Circle w) ↔ a.Coprime b := by
  refine ⟨fun h ↦ ?_, fun hab z w ↦ (weightedHopf_eq_weightedHopf_iff ha hb hab hε).1⟩
  by_contra hab
  have hg : 1 < a.gcd b := lt_of_le_of_ne (Nat.gcd_pos_of_pos_left b ha) (Ne.symm hab)
  have hag : a / a.gcd b ≠ 0 := (Nat.div_gcd_pos_of_pos_left b ha).ne'
  obtain ⟨z, hz, h₁, h₂⟩ := exists_mem_weightedEllipsoid_ne_zero ha hb hε
  have : NeZero a := ⟨ha.ne'⟩
  obtain ⟨ζ, hprim⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Circle a
  have hw : (z.1, (ζ : ℂ) * z.2) ∈ weightedEllipsoid a b ε := by simpa using hz
  have hhopf : weightedHopf hε ⟨z, hz⟩ = weightedHopf hε ⟨_, hw⟩ := by
    rw [weightedHopf_def, weightedHopf_def]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp [mul_pow, ← Circle.coe_pow, hprim.pow_eq_one]
  obtain ⟨u, hu⟩ := h _ _ hhopf.symm
  rw [← Subtype.coe_inj, coe_smul_weightedEllipsoid] at hu
  have hua : u ^ a = 1 := by
    have h₁' := congrArg Prod.fst hu
    simp only [weightedRotation_fst] at h₁'
    exact Circle.coe_eq_one.1 (by rw [Circle.coe_pow]; exact (mul_eq_right₀ h₁).1 h₁')
  have hub : u ^ b = ζ := by
    have h₂' := congrArg Prod.snd hu
    simp only [weightedRotation_snd] at h₂'
    exact Circle.coe_injective (by rw [Circle.coe_pow]; exact mul_right_cancel₀ h₂ h₂')
  -- `ζ` has order `a`, but `ζ ^ (a / g) = 1` with `0 < a / g < a`.
  have e : b * (a / a.gcd b) = a * (b / a.gcd b) := by
    rw [← Nat.mul_div_assoc _ (a.gcd_dvd_left b), ← Nat.mul_div_assoc _ (a.gcd_dvd_right b),
      mul_comm]
  have hζg : ζ ^ (a / a.gcd b) = 1 := by
    rw [← hub, ← pow_mul, e, pow_mul, hua, one_pow]
  exact (Nat.div_lt_self ha hg).not_ge
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hag) (hprim.dvd_of_pow_eq_one _ hζg))

/-- The ellipsoid for the weights `(a, b)` at level `ε` is the ellipsoid for the reduced weights
`(a / gcd(a, b), b / gcd(a, b))` at level `ε / gcd(a, b)`. -/
theorem weightedEllipsoid_div_gcd (hab : a.gcd b ≠ 0) :
    weightedEllipsoid (a / a.gcd b) (b / a.gcd b) (ε / a.gcd b) = weightedEllipsoid a b ε := by
  have h := weightedEllipsoid_mul_mul_mul (a := a / a.gcd b) (b := b / a.gcd b)
    (ε := ε / a.gcd b) hab
  rw [Nat.mul_div_cancel' (a.gcd_dvd_left b), Nat.mul_div_cancel' (a.gcd_dvd_right b),
    mul_div_cancel₀ ε (Nat.cast_ne_zero.2 hab)] at h
  exact h.symm

/-- **The orbit space of the ellipsoid is a sphere, for all positive weights.** For positive
weights `a, b` and `ε > 0`, with `g = gcd(a, b)`, the reduced power map
`[z] ↦ [z₁ ^ (b / g) : z₂ ^ (a / g)]` is a homeomorphism from the orbit space of the weighted
circle action on the ellipsoid `a |z₁|² + b |z₂|² = 2 ε` onto the complex projective line. For
coprime weights it is the map `TauCeti.Toric.weightedOrbitHomeomorph`. -/
def reducedWeightedOrbitHomeomorph (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    MulAction.orbitRel.Quotient Circle (weightedEllipsoid a b ε) ≃ₜ ℙ ℂ (Fin 2 → ℂ) :=
  have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  (commonFactorOrbitHomeomorph hg.ne' (Nat.mul_div_cancel' (a.gcd_dvd_left b)).symm
      (Nat.mul_div_cancel' (a.gcd_dvd_right b)).symm
      (mul_div_cancel₀ ε (Nat.cast_ne_zero.2 hg.ne')).symm).trans
    (weightedOrbitHomeomorph (Nat.div_gcd_pos_of_pos_left b ha)
      (Nat.div_gcd_pos_of_pos_right a hb) (Nat.coprime_div_gcd_div_gcd hg)
      (div_pos hε (Nat.cast_pos.2 hg)))

/-- The point `z` of the ellipsoid, as a point of the ellipsoid for the reduced weights. -/
theorem mem_weightedEllipsoid_div_gcd (hab : a.gcd b ≠ 0) (z : weightedEllipsoid a b ε) :
    (z : ℂ × ℂ) ∈ weightedEllipsoid (a / a.gcd b) (b / a.gcd b) (ε / a.gcd b) := by
  rw [weightedEllipsoid_div_gcd hab]
  exact z.property

/-- The homeomorphism `reducedWeightedOrbitHomeomorph` sends the orbit of `z` to the line through
`(z₁ ^ (b / g), z₂ ^ (a / g))`, the weighted Hopf map of `z` for the reduced weights. -/
@[simp]
theorem reducedWeightedOrbitHomeomorph_mk (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (z : weightedEllipsoid a b ε) :
    reducedWeightedOrbitHomeomorph ha hb hε (Quotient.mk _ z) =
      weightedHopf (div_pos hε (Nat.cast_pos.2 (Nat.gcd_pos_of_pos_left b ha)))
        ⟨z, mem_weightedEllipsoid_div_gcd (Nat.gcd_pos_of_pos_left b ha).ne' z⟩ := by
  rw [reducedWeightedOrbitHomeomorph, Homeomorph.trans_apply, commonFactorOrbitHomeomorph_mk,
    weightedOrbitHomeomorph_mk]

/-- The reduced power map sends the orbit of `z` to `[1 : 0]` exactly when `z` lies on the axis
`z₂ = 0`, where the stabilizer has order `a`. -/
theorem reducedWeightedOrbitHomeomorph_mk_eq_mk_iff_snd_eq_zero (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (z : weightedEllipsoid a b ε) :
    reducedWeightedOrbitHomeomorph ha hb hε (Quotient.mk _ z) = mk ℂ ![1, 0] (by simp) ↔
      (z : ℂ × ℂ).2 = 0 := by
  rw [reducedWeightedOrbitHomeomorph_mk]
  exact weightedHopf_eq_mk_iff_snd_eq_zero (Nat.div_gcd_pos_of_pos_left b ha) _ _

/-- The reduced power map sends the orbit of `z` to `[0 : 1]` exactly when `z` lies on the axis
`z₁ = 0`, where the stabilizer has order `b`. -/
theorem reducedWeightedOrbitHomeomorph_mk_eq_mk_iff_fst_eq_zero (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (z : weightedEllipsoid a b ε) :
    reducedWeightedOrbitHomeomorph ha hb hε (Quotient.mk _ z) = mk ℂ ![0, 1] (by simp) ↔
      (z : ℂ × ℂ).1 = 0 := by
  rw [reducedWeightedOrbitHomeomorph_mk]
  exact weightedHopf_eq_mk_iff_fst_eq_zero (Nat.div_gcd_pos_of_pos_right a hb) _ _

end TauCeti.Toric
