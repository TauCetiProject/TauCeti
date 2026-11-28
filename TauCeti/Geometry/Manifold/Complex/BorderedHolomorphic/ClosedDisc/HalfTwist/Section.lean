/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc.HalfTwist
public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong.Section

/-!
# Sections of the half-twisted bundle pairs with real boundary values

The half-twisted pair `(ℂ, z^{k/2} ℝ)` over the closed unit disc (`halfTwistCore k`) has continuous
sections with values in `z^{k/2} ℝ` along the circle and finitely many zeros, which double to
sections of the doubled bundle over the Riemann sphere with finitely many zeros. The sum of the
local indices of the zeros of the doubled section, a zero of order `m` at `0` on each sheet (with
sign) and, for odd `k`, a simple zero at `-1` on the seam, is `k`; it computes the Maslov index
`μ(halfTwistCore k) = k`.

Write `|k| = 2m + e` with `e ∈ {0, 1}`. The *half-twist profile* (`halfTwistProfile k`) is the
function `z ↦ z^m (1 + z)^e` for `k ≥ 0` and its complex conjugate for `k < 0`. On the circle,
divided by the frame `z^{k/2}` of the pair, it becomes the real number `(r + r⁻¹)^e` for
`r = z^{1/2}`, as `r⁻¹ = conj r` (`cpow_inv_mul_halfTwistProfile`). Its zeros are `0` (for
`|k| ≥ 2`) and `-1` (for odd `k`) (`halfTwistProfile_eq_zero_iff`).

The section `halfTwistSection k` of `halfTwistCore k` is the profile, read through the isomorphism
`halfTwistIso k` with the trivial line core. It is real along the circle
(`halfTwistSection_real`), vanishes exactly at the zeros of the profile
(`halfTwistSection_eq_zero_iff`), and its double
(`TauCeti.FiniteRankBundleCore.doubleAlongSection`) has finitely many zeros
(`finite_setOf_doubleAlongSection_halfTwistSection_eq_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.3.5 (normalization of the boundary Maslov index), Appendix C.3 (doubling).
-/

public section

noncomputable section

open Set CategoryTheory TauCeti TauCeti.FiniteRankBundleCore ComplexConjugate
open scoped Manifold Complex.UnitDisc

namespace Complex.UnitClosedDisc

local notation "A" => (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ

/-- The half-twist profile: `z ↦ z^m (1 + z)^e` for `k = 2m + e ≥ 0` with `e ∈ {0, 1}`, and its
complex conjugate for `k < 0`. -/
def halfTwistProfile (k : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ k then z ^ (k.natAbs / 2) * (1 + z) ^ (k.natAbs % 2)
  else conj (z ^ (k.natAbs / 2) * (1 + z) ^ (k.natAbs % 2))

theorem continuous_halfTwistProfile (k : ℤ) : Continuous (halfTwistProfile k) := by
  unfold halfTwistProfile
  split_ifs
  · fun_prop
  · exact continuous_conj.comp (by fun_prop)

/-- For `k ≥ 0` the half-twist profile is `z^m (1 + z)^e`, `|k| = 2m + e`. -/
theorem halfTwistProfile_of_nonneg {k : ℤ} (hk : 0 ≤ k) (z : ℂ) :
    halfTwistProfile k z = z ^ (k.natAbs / 2) * (1 + z) ^ (k.natAbs % 2) := by
  simp only [halfTwistProfile, hk, ↓reduceIte]

/-- For `k < 0` the half-twist profile is the conjugate of `z^m (1 + z)^e`, `|k| = 2m + e`. -/
theorem halfTwistProfile_of_neg {k : ℤ} (hk : k < 0) (z : ℂ) :
    halfTwistProfile k z = conj (z ^ (k.natAbs / 2) * (1 + z) ^ (k.natAbs % 2)) := by
  simp only [halfTwistProfile, not_le.2 hk, ↓reduceIte]

/-- The half-twist profile vanishes at `0` when `|k| ≥ 2` and at `-1` when `k` is odd, and
nowhere else. -/
theorem halfTwistProfile_eq_zero_iff {k : ℤ} {z : ℂ} :
    halfTwistProfile k z = 0 ↔ (z = 0 ∧ 2 ≤ k.natAbs) ∨ (z = -1 ∧ k.natAbs % 2 = 1) := by
  have h : z ^ (k.natAbs / 2) * (1 + z) ^ (k.natAbs % 2) = 0 ↔
      (z = 0 ∧ 2 ≤ k.natAbs) ∨ (z = -1 ∧ k.natAbs % 2 = 1) := by
    have hz : 1 + z = 0 ↔ z = -1 := by
      rw [add_eq_zero_iff_eq_neg']
    rw [mul_eq_zero, pow_eq_zero_iff', pow_eq_zero_iff', hz, Nat.mod_two_ne_zero,
      show k.natAbs / 2 ≠ 0 ↔ 2 ≤ k.natAbs by omega]
  rcases le_or_gt 0 k with hk | hk
  · rw [halfTwistProfile_of_nonneg hk, h]
  · rw [halfTwistProfile_of_neg hk, map_eq_zero, h]

/-- **The half-twist profile divided by the frame is real on the circle**: for `‖a‖ = 1`,
`a^{-k/2}` times the profile at `a` is `(r + r⁻¹)^e` with `r = a^{1/2}` and `e = |k| mod 2`, a real
number since `r⁻¹ = conj r`. -/
theorem cpow_inv_mul_halfTwistProfile (k : ℤ) {a : ℂ} (ha : ‖a‖ = 1) :
    (a ^ ((k : ℂ) / 2))⁻¹ * halfTwistProfile k a =
      (a ^ (2⁻¹ : ℂ) + (a ^ (2⁻¹ : ℂ))⁻¹) ^ (k.natAbs % 2) := by
  set r := a ^ (2⁻¹ : ℂ)
  have hr2 : r ^ 2 = a := cpow_nat_inv_pow a two_ne_zero
  have hrn : ‖r‖ = 1 := by simpa [ha] using norm_cpow_inv_nat a 2
  have hr0 : r ≠ 0 := fun h ↦ by simp [h] at hrn
  have hconj : conj r = r⁻¹ := (inv_eq_conj hrn).symm
  have hk : a ^ ((k : ℂ) / 2) = r ^ k := by
    rw [show (k : ℂ) / 2 = (2⁻¹ : ℂ) * k by ring, cpow_mul_int]
  rw [hk, halfTwistProfile, ← hr2]
  -- Split `|k| = 2 m + e` with `e ∈ {0, 1}`.
  have key (n : ℕ) : r ^ n = (r ^ 2) ^ (n / 2) * r ^ (n % 2) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have he (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  split_ifs with h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [Int.natAbs_natCast, zpow_natCast, key n]
    rcases he n with h | h
    · rw [h]
      field_simp
    · rw [h]
      field_simp
      ring
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.1 h0))
    rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, inv_inv, key n]
    simp only [map_mul, map_pow, map_add, map_one, hconj, inv_pow]
    rcases he n with h | h
    · rw [h]
      field_simp
    · rw [h]
      field_simp

/-- On the circle, the half-twist profile divided by the frame `a^{k/2}` is real. -/
theorem conj_cpow_inv_mul_halfTwistProfile (k : ℤ) {a : ℂ} (ha : ‖a‖ = 1) :
    conj ((a ^ ((k : ℂ) / 2))⁻¹ * halfTwistProfile k a) =
      (a ^ ((k : ℂ) / 2))⁻¹ * halfTwistProfile k a := by
  have hr : ‖a ^ (2⁻¹ : ℂ)‖ = 1 := by simpa [ha] using norm_cpow_inv_nat a 2
  rw [cpow_inv_mul_halfTwistProfile k ha, map_pow, map_add, map_inv₀, ← inv_eq_conj hr, inv_inv,
    add_comm]

/-- **The boundary-real section of the half-twisted pair**: the half-twist profile, read through
the isomorphism of `halfTwistCore k` with the trivial line core. -/
def halfTwistSection (k : ℤ) : trivial ℂ 𝕔𝔻 1 ⟶ halfTwistCore k :=
  smulTrivial (fun z : 𝕔𝔻 ↦ halfTwistProfile k z)
      ((continuous_halfTwistProfile k).comp continuous_coe) ≫
    (halfTwistIso k).inv

/-- The fibre map of the section over `z` is multiplication by the profile divided by the frame. -/
theorem fiberMap_halfTwistSection (k : ℤ) (z : 𝕔𝔻) :
    (halfTwistSection k).fiberMap z =
      ((exp (halfTwistExponent k z z))⁻¹ * halfTwistProfile k z) •
        ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  have h (c p : ℂ) : (c • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)).comp
      (p • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) =
        (c * p) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp,
      smul_smul]
  rw [halfTwistSection, fiberMap_comp, fiberMap_smulTrivial, fiberMap_halfTwistIso_inv]
  -- The fibres of both cores are `Fin 1 → ℂ` (`rank_trivial`, `rank_halfTwistCore`).
  exact h _ _

/-- The section of the half-twisted pair is real along the circle: its values there lie in
`z^{k/2} ℝ`. -/
theorem halfTwistSection_real (k : ℤ) :
    ∀ a ∈ A, ∀ v, (halfTwistSection k).fiberMap a (star v) =
      star ((halfTwistSection k).fiberMap a v) := by
  intro a ha v
  have ha1 : ‖(a : ℂ)‖ = 1 := notMem_borderedInterior_iff.1 ha
  have key (c : ℂ) (hc : conj c = c) (w : Fin 1 → ℂ) :
      (c • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) (star w) =
        star ((c • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) w) := by
    rw [_root_.smul_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.id_apply, star_smul]
    exact congrArg (· • _) hc.symm
  rw [fiberMap_halfTwistSection, exp_halfTwistExponent_self k ha1]
  -- The fibres of both cores are `Fin 1 → ℂ` (`rank_trivial`, `rank_halfTwistCore`).
  exact key _ (conj_cpow_inv_mul_halfTwistProfile k ha1) v

/-- The section of the half-twisted pair vanishes exactly at the zeros of the profile. -/
theorem halfTwistSection_eq_zero_iff (k : ℤ) (z : 𝕔𝔻) :
    (halfTwistSection k).fiberMap z = 0 ↔ halfTwistProfile k z = 0 := by
  have h (c : ℂ) : c • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) = 0 ↔ c = 0 := by
    refine ⟨fun hc ↦ ?_, fun hc ↦ by ext; simp [hc]⟩
    simpa using congrArg (fun f ↦ f (fun _ ↦ 1) 0) hc
  rw [fiberMap_halfTwistSection]
  -- The fibres of both cores are `Fin 1 → ℂ` (`rank_trivial`, `rank_halfTwistCore`).
  refine (h _).trans ?_
  rw [mul_eq_zero, inv_eq_zero, or_iff_right (exp_ne_zero _)]

/-- The section of the half-twisted pair has finitely many zeros. -/
theorem finite_setOf_halfTwistSection_eq_zero (k : ℤ) :
    {z | (halfTwistSection k).fiberMap z = 0}.Finite := by
  refine ((finite_singleton (0 : ℂ)).insert (-1)).preimage coe_injective.injOn |>.subset ?_
  intro z hz
  rcases halfTwistProfile_eq_zero_iff.1 ((halfTwistSection_eq_zero_iff k z).1 hz) with h | h
  · exact .inr h.1
  · exact .inl h.1

/-- The double of the boundary-real section of the half-twisted pair has finitely many zeros on
the Riemann sphere. -/
theorem finite_setOf_doubleAlongSection_halfTwistSection_eq_zero (k : ℤ) :
    {y | (doubleAlongSection (isRealAlong_halfTwistCore k) (halfTwistSection k)
      (halfTwistSection_real k)).fiberMap y = 0}.Finite :=
  finite_setOf_doubleAlongSection_eq_zero _ _ _ (finite_setOf_halfTwistSection_eq_zero k)

end Complex.UnitClosedDisc
