/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Class
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
-- Proof-only: the global-minimality class detects globally minimal equations, the algebra norm of
-- a quadratic algebra is its explicit norm form, and units of a ring of integers have norm `±1`.
import Mathlib.NumberTheory.NumberField.Units.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.Algebra.QuadraticAlgebra.NormTrace

/-!
# Worked example: a principal minimal discriminant with no global minimal model

Let `K = ℚ(√65)` (of class number `2`, a fact not used here) and let `θ = (1 + √65) / 2`, a
root of `X² - X - 16`. The elliptic curve

`E : y² = x³ + (-15221331 θ - 53748576) x + (-79617688290 θ - 281140318368)`

over `K` has **good reduction at every prime** of `𝓞 K`, so its minimal discriminant ideal
`𝔇_{E/K}` is the unit ideal, as principal as an ideal can be
(`TauCeti.WorkedExamples.minimalDiscriminantIdeal_curveSqrt65`). Yet its global-minimality class
is nontrivial (`TauCeti.WorkedExamples.globalMinimalityClass_curveSqrt65_ne_one`): no Weierstrass
equation of `E` is minimal at every prime of `𝓞 K`, and no equation of `E` over `𝓞 K` has unit
discriminant. So the obstruction to a global minimal model is the class of the defect ideal, and
not the principality of the minimal discriminant ideal (Silverman VIII.8).

Good reduction everywhere is certified by two integral models. Over `𝓞 K` the equation `E` is
isomorphic to an equation whose discriminant is a unit times `(1 - θ)⁹`, and to one whose
discriminant is a unit times `θ¹⁵`. Since `θ + (1 - θ) = 1`, every prime of `𝓞 K` misses one of
the two discriminants, and the minimal discriminant ideal divides both
(`WeierstrassCurve.minimalDiscriminantIdeal_dvd_span_of_smul_eq_baseChange`).

The obstruction is a norm computation. The discriminant of the short equation has norm
`N(Δ) = -2³⁶ 3²⁴ = -72¹²`. An equation over `𝓞 K` with unit discriminant `Δ'` would be related
to `E` by a change of variables with `Δ = u¹² Δ'`, so `N(u) = ±72`. But `±72` is not a norm from
`K`: in `a² - 65 b² = ±72 m²` with integers, reducing modulo `5` forces `5 ∣ a, b, m`, and an
infinite descent leaves `m = 0`. This is the Hilbert symbol `(±72, 65)₅ = -1`.

## Main results

* `TauCeti.WorkedExamples.minimalDiscriminantIdeal_curveSqrt65`: `𝔇_{E/K} = (1)`.
* `TauCeti.WorkedExamples.hasGoodReduction_minimal_curveSqrt65`: `E` has good reduction at every
  height-one prime of `𝓞 K`.
* `TauCeti.WorkedExamples.not_isUnit_Δ_of_smul_curveSqrt65_eq_baseChange`: no equation of `E`
  over `𝓞 K` has unit discriminant.
* `TauCeti.WorkedExamples.not_isGlobalMinimal_smul_curveSqrt65`: no equation of `E` is globally
  minimal over `𝓞 K`.
* `TauCeti.WorkedExamples.globalMinimalityClass_curveSqrt65_ne_one`: the global-minimality class
  of `E` is nontrivial.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.8.
* J. E. Cremona's implementation of global and semi-global minimal models over number fields in
  SageMath (the modules `sage.schemes.elliptic_curves.kraus` and
  `sage.schemes.elliptic_curves.ell_number_field`), the source of this curve as an example with
  everywhere good reduction and no global minimal model.
-/

public section

open NumberField WeierstrassCurve QuadraticAlgebra IsDedekindDomain

namespace TauCeti.WorkedExamples

/-- `65` is not a square in `ℚ`, so `ℚ[√65]` is a field. -/
instance fact_not_isSquare_sixtyFive : Fact (¬ IsSquare (65 : ℚ)) := ⟨by
  rw [Rat.isSquare_ofNat_iff]
  rintro ⟨r, hr⟩
  have h : r ≤ 8 := by nlinarith
  interval_cases r <;> omega⟩

/-- The real quadratic field `ℚ(√65)`, as the quadratic algebra `ℚ[√65]` with basis `1, √65`. -/
abbrev QSqrt65 : Type := QuadraticAlgebra ℚ 65 0

/-- `θ = (1 + √65) / 2` is an algebraic integer: it is a root of `X² - X - 16`. -/
theorem isIntegral_sqrt65Theta : IsIntegral ℤ (⟨1 / 2, 1 / 2⟩ : QSqrt65) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X - 16, by monicity!, ?_⟩
  ext <;> simp [sq] <;> norm_num

/-- The algebraic integer `θ = (1 + √65) / 2` of `ℚ(√65)`, a root of `X² - X - 16`. -/
def sqrt65Theta : 𝓞 QSqrt65 :=
  ⟨⟨1 / 2, 1 / 2⟩, isIntegral_sqrt65Theta⟩

/-- `θ` has coordinates `(1/2, 1/2)` in the basis `1, √65`. -/
@[simp]
theorem coe_sqrt65Theta : (sqrt65Theta : QSqrt65) = ⟨1 / 2, 1 / 2⟩ := (rfl)

/-- The elliptic curve `y² = x³ + (-15221331 θ - 53748576) x + (-79617688290 θ - 281140318368)`
over `ℚ(√65)`, with `θ = (1 + √65) / 2`. -/
noncomputable def curveSqrt65 : WeierstrassCurve QSqrt65 :=
  ⟨0, 0, 0, -15221331 * (sqrt65Theta : QSqrt65) - 53748576,
    -79617688290 * (sqrt65Theta : QSqrt65) - 281140318368⟩

/-- The coefficient `a₁` of `curveSqrt65` is `0`. -/
@[simp]
theorem curveSqrt65_a₁ : curveSqrt65.a₁ = 0 := (rfl)

/-- The coefficient `a₂` of `curveSqrt65` is `0`. -/
@[simp]
theorem curveSqrt65_a₂ : curveSqrt65.a₂ = 0 := (rfl)

/-- The coefficient `a₃` of `curveSqrt65` is `0`. -/
@[simp]
theorem curveSqrt65_a₃ : curveSqrt65.a₃ = 0 := (rfl)

/-- The coefficient `a₄` of `curveSqrt65` is `-15221331 θ - 53748576`. -/
@[simp]
theorem curveSqrt65_a₄ :
    curveSqrt65.a₄ = -15221331 * (sqrt65Theta : QSqrt65) - 53748576 := (rfl)

/-- The coefficient `a₆` of `curveSqrt65` is `-79617688290 θ - 281140318368`. -/
@[simp]
theorem curveSqrt65_a₆ :
    curveSqrt65.a₆ = -79617688290 * (sqrt65Theta : QSqrt65) - 281140318368 := (rfl)

/-- The discriminant of `curveSqrt65` in the basis `1, √65`. Its norm is `-2³⁶ 3²⁴`. -/
theorem curveSqrt65_Δ :
    curveSqrt65.Δ = ⟨-29859555657159315059116032, -3703622060887453530261504⟩ := by
  simp only [curveSqrt65, Δ, b₂, b₄, b₆, b₈, coe_sqrt65Theta]
  ext <;> simp [pow_succ] <;> norm_num

/-- `curveSqrt65` is an elliptic curve: its discriminant is nonzero. -/
instance : curveSqrt65.IsElliptic := by
  rw [isElliptic_iff, curveSqrt65_Δ, isUnit_iff_ne_zero]
  intro h
  have := congrArg QuadraticAlgebra.re h
  norm_num at this

/-! ### Two integral models with coprime discriminants -/

/-- An equation over `𝓞 K` isomorphic to `curveSqrt65`, with discriminant a unit times
`(1 - θ)⁹`. -/
private noncomputable def modelA : WeierstrassCurve (𝓞 QSqrt65) :=
  ⟨1 + sqrt65Theta, 1 + sqrt65Theta, 0, -402967 - 114118 * sqrt65Theta,
    -184293144 - 52190999 * sqrt65Theta⟩

/-- An equation over `𝓞 K` isomorphic to `curveSqrt65`, with discriminant a unit times `θ¹⁵`. -/
private noncomputable def modelB : WeierstrassCurve (𝓞 QSqrt65) :=
  ⟨sqrt65Theta, -1 + sqrt65Theta, sqrt65Theta, -17481845 - 4950776 * sqrt65Theta,
    -52200463523 - 14782939216 * sqrt65Theta⟩

/-- The change of variables `u = -3θ/4`, `r = 21 + 105θ/16`, `s = -6 - 3θ/4`, `t = 0`, written in
the basis `1, √65`; `u⁻¹ = (1 - θ)/12`. -/
private noncomputable def variableChangeA : VariableChange QSqrt65 where
  u := ⟨⟨-3 / 8, -3 / 8⟩, ⟨1 / 24, -1 / 24⟩, by ext <;> simp <;> norm_num,
    by ext <;> simp <;> norm_num⟩
  r := ⟨777 / 32, 105 / 32⟩
  s := ⟨-51 / 8, -3 / 8⟩
  t := 0

/-- The change of variables `u = 3(θ - 1)/8`, `r = 93/64 + 51θ/64`, `s = 3`,
`t = 459/64 - 27θ/64`, written in the basis `1, √65`; `u⁻¹ = θ/6`. -/
private noncomputable def variableChangeB : VariableChange QSqrt65 where
  u := ⟨⟨-3 / 16, 3 / 16⟩, ⟨1 / 12, 1 / 12⟩, by ext <;> simp <;> norm_num,
    by ext <;> simp <;> norm_num⟩
  r := ⟨237 / 128, 51 / 128⟩
  s := 3
  t := ⟨891 / 128, -27 / 128⟩

private theorem variableChangeA_smul :
    variableChangeA • curveSqrt65 = modelA.baseChange QSqrt65 := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, curveSqrt65, modelA, variableChangeA,
      WeierstrassCurve.baseChange, pow_succ, map_ofNat] <;>
    norm_num

private theorem variableChangeB_smul :
    variableChangeB • curveSqrt65 = modelB.baseChange QSqrt65 := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, curveSqrt65, modelB, variableChangeB,
      WeierstrassCurve.baseChange, pow_succ, map_ofNat] <;>
    norm_num

private theorem modelA_Δ_mul :
    modelA.Δ * (165740568560225 - 36578206703808 * sqrt65Theta) = (1 - sqrt65Theta) ^ 9 := by
  apply RingOfIntegers.coe_injective
  simp only [modelA, Δ, b₂, b₄, b₆, b₈, map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat,
    map_one, map_zero, ← RingOfIntegers.coe_eq_algebraMap, coe_sqrt65Theta]
  ext <;> simp [pow_succ] <;> norm_num

private theorem coe_sqrt65Theta_pow_three : (sqrt65Theta : QSqrt65) ^ 3 = ⟨49 / 2, 17 / 2⟩ := by
  ext <;> simp [pow_succ] <;> norm_num

private theorem modelB_Δ_mul :
    modelB.Δ * (165740568560225 - 36578206703808 * sqrt65Theta) = -sqrt65Theta ^ 15 := by
  apply RingOfIntegers.coe_injective
  simp only [modelB, Δ, b₂, b₄, b₆, b₈, map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat,
    map_one, ← RingOfIntegers.coe_eq_algebraMap]
  have h15 : (sqrt65Theta : QSqrt65) ^ 15 = ((sqrt65Theta : QSqrt65) ^ 3) ^ 5 := by
    rw [← pow_mul]
  rw [h15, coe_sqrt65Theta_pow_three, coe_sqrt65Theta]
  ext <;> simp [pow_succ] <;> norm_num

/-- The two integral models have coprime discriminants, since `θ` and `1 - θ` are coprime. -/
private theorem isCoprime_modelA_Δ_modelB_Δ : IsCoprime modelA.Δ modelB.Δ := by
  have h : IsCoprime ((1 - sqrt65Theta) ^ 9) (-sqrt65Theta ^ 15) :=
    (IsCoprime.pow ⟨1, 1, by ring⟩).neg_right
  rw [← modelA_Δ_mul, ← modelB_Δ_mul] at h
  exact h.of_mul_left_left.of_mul_right_left

/-! ### Good reduction everywhere -/

/-- **The minimal discriminant ideal of `curveSqrt65` is the unit ideal**: the curve has good
reduction at every prime of `𝓞 K`. -/
theorem minimalDiscriminantIdeal_curveSqrt65 :
    minimalDiscriminantIdeal (𝓞 QSqrt65) curveSqrt65 = ⊤ := by
  have hA := Ideal.dvd_span_singleton.mp
    (minimalDiscriminantIdeal_dvd_span_of_smul_eq_baseChange variableChangeA_smul)
  have hB := Ideal.dvd_span_singleton.mp
    (minimalDiscriminantIdeal_dvd_span_of_smul_eq_baseChange variableChangeB_smul)
  obtain ⟨a, b, hab⟩ := isCoprime_modelA_Δ_modelB_Δ
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ a hA) (Ideal.mul_mem_left _ b hB)

/-- **`curveSqrt65` has good reduction at every height-one prime of `𝓞 K`.** -/
theorem hasGoodReduction_minimal_curveSqrt65 (v : HeightOneSpectrum (𝓞 QSqrt65)) :
    (curveSqrt65.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
      (Localization.AtPrime v.asIdeal) :=
  (minimalDiscriminantIdeal_eq_top_iff _ _).mp minimalDiscriminantIdeal_curveSqrt65 v

/-! ### No global minimal model -/

/-- The integral form of the descent: if `(A² - 65 B²)² = (72 m²)²` in integers, then `m = 0`.
Modulo `5` the left side is `A⁴` and the right side `4 m⁴`, which forces `5 ∣ m` and `5 ∣ A`,
then `5 ∣ B`, and dividing by `5` gives a smaller solution. -/
private theorem eq_zero_of_sq_sub_sixtyFive_mul_sq_sq_eq (A B m : ℤ)
    (h : (A ^ 2 - 65 * B ^ 2) ^ 2 = (72 * m ^ 2) ^ 2) : m = 0 := by
  induction hn : m.natAbs using Nat.strong_induction_on generalizing A B m with
  | _ n ih =>
  by_contra hm
  have key : ∀ a b c : ZMod 5, (a ^ 2 - 65 * b ^ 2) ^ 2 = (72 * c ^ 2) ^ 2 → c = 0 ∧ a = 0 := by
    decide
  have h₅ := congrArg (Int.cast : ℤ → ZMod 5) h
  push_cast at h₅
  obtain ⟨hc, ha⟩ := key _ _ _ h₅
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ha
  obtain ⟨m', rfl⟩ := hc
  obtain ⟨A', rfl⟩ := ha
  have hB : (B : ZMod 5) = 0 := by
    have h13 : ((13 * B ^ 2 : ℤ) : ZMod 5) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
      · exact ⟨A' ^ 2 - 72 * m' ^ 2, by push_cast at h' ⊢; linarith⟩
      · exact ⟨A' ^ 2 + 72 * m' ^ 2, by push_cast at h' ⊢; linarith⟩
    push_cast at h13
    generalize (B : ZMod 5) = b at h13 ⊢
    revert b
    decide
  obtain ⟨B', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd B 5).mp hB
  push_cast at h hn hm
  have h' : (A' ^ 2 - 65 * B' ^ 2) ^ 2 = (72 * m' ^ 2) ^ 2 := by
    have h625 : (625 : ℤ) * (A' ^ 2 - 65 * B' ^ 2) ^ 2 = 625 * (72 * m' ^ 2) ^ 2 := by
      linear_combination h
    exact mul_left_cancel₀ (by norm_num) h625
  have hm' : m' ≠ 0 := by rintro rfl; simp at hm
  have hpos : 0 < m'.natAbs := Int.natAbs_pos.mpr hm'
  exact hm' (ih _ (by rw [← hn, Int.natAbs_mul]; norm_num; omega) A' B' m' h' rfl)

/-- No element of `ℚ(√65)` has norm `±1/72`, equivalently `±72`. -/
private theorem sq_seventyTwo_mul_norm_ne_one (z : QSqrt65) : (72 * z.norm) ^ 2 ≠ 1 := by
  intro h
  rw [norm_def] at h
  have hden : ((z.re.den * z.im.den : ℕ) : ℤ) ≠ 0 := by positivity
  refine hden (eq_zero_of_sq_sub_sixtyFive_mul_sq_sq_eq (72 * z.re.num * z.im.den)
    (72 * z.im.num * z.re.den) _ ?_)
  have hre : (z.re : ℚ) = z.re.num / z.re.den := (Rat.num_div_den _).symm
  have him : (z.im : ℚ) = z.im.num / z.im.den := (Rat.num_div_den _).symm
  rw [hre, him] at h
  have hre₀ : (z.re.den : ℚ) ≠ 0 := by positivity
  have him₀ : (z.im.den : ℚ) ≠ 0 := by positivity
  field_simp at h
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination (72 : ℚ) ^ 2 * h

/-- **No equation of `curveSqrt65` over `𝓞 K` has unit discriminant.** The norm of a unit is `±1`,
while `N(Δ) = -72¹²` and a change of variables multiplies `Δ` by `u⁻¹²`; so `N(u⁻¹) = ±1/72`,
which is not a norm from `ℚ(√65)`. -/
theorem not_isUnit_Δ_of_smul_curveSqrt65_eq_baseChange {C : VariableChange QSqrt65}
    {W : WeierstrassCurve (𝓞 QSqrt65)} (hC : C • curveSqrt65 = W.baseChange QSqrt65) :
    ¬ IsUnit W.Δ := by
  intro hu
  have hΔ : algebraMap (𝓞 QSqrt65) QSqrt65 W.Δ = (C.u⁻¹ : QSqrt65ˣ) ^ 12 * curveSqrt65.Δ := by
    rw [← variableChange_Δ, hC, WeierstrassCurve.baseChange, map_Δ]
  have hN : |(algebraMap (𝓞 QSqrt65) QSqrt65 W.Δ).norm| = 1 := by
    simpa [RingOfIntegers.coe_eq_algebraMap] using NumberField.isUnit_iff_norm.mp hu
  have hNΔ : curveSqrt65.Δ.norm = -72 ^ 12 := by
    rw [curveSqrt65_Δ, norm_def]
    norm_num
  rw [hΔ, map_mul, map_pow, hNΔ] at hN
  set x := ((C.u⁻¹ : QSqrt65ˣ) : QSqrt65).norm
  have h12 : ((72 * x) ^ 2) ^ 6 = 1 := by
    rw [← pow_mul, mul_pow]
    norm_num at hN
    rw [pow_abs, abs_of_nonneg (by positivity)] at hN
    norm_num
    linear_combination hN
  exact sq_seventyTwo_mul_norm_ne_one _ ((pow_eq_one_iff_of_nonneg (by positivity)
    (by norm_num)).mp h12)

/-- **`curveSqrt65` has no globally minimal equation over `𝓞 K`.** A globally minimal equation
would have discriminant generating `𝔇_{E/K} = (1)`, hence a unit discriminant. -/
theorem not_isGlobalMinimal_smul_curveSqrt65 (C : VariableChange QSqrt65) :
    ¬ IsGlobalMinimal (𝓞 QSqrt65) (C • curveSqrt65) := by
  intro h
  have := h.isIntegral
  have hspan := minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal h
    (integralModel_Δ_eq (𝓞 QSqrt65) (C • curveSqrt65))
  rw [minimalDiscriminantIdeal_smul, minimalDiscriminantIdeal_curveSqrt65, eq_comm,
    Ideal.span_singleton_eq_top] at hspan
  exact not_isUnit_Δ_of_smul_curveSqrt65_eq_baseChange
    (baseChange_integralModel_eq (𝓞 QSqrt65) (C • curveSqrt65)).symm hspan

/-- **The global-minimality class of `curveSqrt65` is nontrivial**, although its minimal
discriminant ideal is the unit ideal (`minimalDiscriminantIdeal_curveSqrt65`). -/
theorem globalMinimalityClass_curveSqrt65_ne_one :
    globalMinimalityClass (𝓞 QSqrt65) curveSqrt65 ≠ 1 := by
  rw [Ne, globalMinimalityClass_eq_one_iff]
  rintro ⟨C, hC⟩
  exact not_isGlobalMinimal_smul_curveSqrt65 C hC

end TauCeti.WorkedExamples
