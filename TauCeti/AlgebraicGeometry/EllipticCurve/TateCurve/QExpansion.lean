/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.ModularForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Tate `q`-expansions of integral modular forms

An integral modular form `f ∈ ℤ[a₁, a₂, a₃, a₄, a₆]` of the Weierstrass coordinate-change action
(`WeierstrassCurve.IsIntegralModularForm`) has a *Tate `q`-expansion*: its value
`tateCurve.specialize f ∈ ℤ⟦q⟧` on the Tate curve `y² + xy = x³ + a₄(q) x + a₆(q)`. This file
compares these expansions with the `q`-expansions of the analytic modular forms of level one.

The invariants of the Tate curve are the `q`-expansions of `E₄`, `-E₆` and `Δ`. The sign of `c₆`
is part of the comparison: the constant term of `c₆` on the Tate curve is `-1`, while `E₆` is
normalised to have constant term `1`. Since the Tate expansion and the analytic `q`-expansion are
both multiplicative, and every integral modular form lies in `ℤ[c₄, c₆, Δ]`
(`WeierstrassCurve.IsIntegralModularForm.mem_adjoin`), every weight-`k` integral modular form has
the Tate expansion of a unique level-one modular form of weight `k` (unique since the
`q`-expansion is injective on forms of a fixed weight).

Conversely, the image is the full integral lattice: every level-one modular form of weight `k`
with integer `q`-expansion coefficients arises in this way. The proof is by induction on the
weight, as in Mathlib's proof that `E₄` and `E₆` generate the level-one modular forms
(`ModularForm.evalE₄E₆_surjective`). A form of odd weight or of weight `2` vanishes. Otherwise
`k = 4a + 6b` and the integral form `c₄ᵃ (-c₆)ᵇ` has Tate expansion `1 + ⋯`, so subtracting an
integer multiple of it leaves a cusp form with integer coefficients. That cusp form is `Δ` times a
form of weight `k - 12`, and its coefficients stay integral because the Tate discriminant is `q`
times a unit of `ℤ⟦q⟧`.

## Main results

* `TauCeti.map_tateCurve_c₄_eq_qExpansion_E₄`, `TauCeti.map_tateCurve_c₆_eq_neg_qExpansion_E₆`,
  `TauCeti.map_tateCurve_Δ_eq_qExpansion_discriminant`: the invariants `c₄`, `c₆` and `Δ` of the
  Tate curve are the `q`-expansions of `E₄`, `-E₆` and `Δ`.
* `WeierstrassCurve.IsIntegralModularForm.exists_qExpansion_eq_map_specialize_tateCurve`: an
  integral modular form of weight `k` has the Tate expansion of a level-one modular form of
  weight `k`.
* `ModularForm.exists_isIntegralModularForm_specialize_tateCurve_eq`: a level-one modular form of
  weight `k` with integer `q`-expansion is the Tate expansion of an integral modular form of
  weight `k` in `ℤ[c₄, c₆, Δ]`.

## References

* P. Deligne, *Courbes elliptiques : formulaire d'après J. Tate*, in *Modular functions of one
  variable IV*, Lecture Notes in Math. 476, Springer, 1975.
* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer, 1973, §1.
* H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of
  modular forms*, in *Modular functions of one variable III*, Lecture Notes in Math. 350,
  Springer, 1973, §1.
* J.-P. Serre, *A Course in Arithmetic*, Ch. VII.
-/

public section

open PowerSeries UpperHalfPlane ModularForm EisensteinSeries WeierstrassCurve
open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti

/-- The invariant `c₄ = 1 + 240 ∑ σ₃(n) qⁿ` of the Tate curve is the `q`-expansion of `E₄`. -/
theorem map_tateCurve_c₄_eq_qExpansion_E₄ :
    tateCurve.c₄.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  rw [tateCurve_c₄, TauCeti.ModularForm.qExpansion_E₄_eq]

/-- The invariant `c₆ = -1 + 504 ∑ σ₅(n) qⁿ` of the Tate curve is the `q`-expansion of `-E₆`. -/
theorem map_tateCurve_c₆_eq_neg_qExpansion_E₆ :
    tateCurve.c₆.map (Int.castRingHom ℂ) = -qExpansion 1 E₆ := by
  rw [tateCurve_c₆, TauCeti.ModularForm.qExpansion_E₆_eq, ← map_neg, neg_sub, sub_eq_neg_add]

/-- The discriminant of the Tate curve is the `q`-expansion of the modular discriminant `Δ`. -/
theorem map_tateCurve_Δ_eq_qExpansion_discriminant :
    tateCurve.Δ.map (Int.castRingHom ℂ) = qExpansion 1 discriminant := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) tateCurve.c_relation
  simp only [map_sub, map_pow, map_mul, map_ofNat, map_tateCurve_c₄_eq_qExpansion_E₄,
    map_tateCurve_c₆_eq_neg_qExpansion_E₆, neg_sq] at h
  rw [TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, ← h]
  ext n
  simp [coeff_ofNat_mul]

/-- The polynomials in the Weierstrass coefficients whose Tate expansion is the `q`-expansion of a
level-one modular form of weight `k`. They form a graded family under multiplication. -/
private def tateGraded (k : ℕ) : Submodule ℤ (MvPolynomial Coeff ℤ) where
  carrier := {f | ∃ F : ModularForm 𝒮ℒ k,
    qExpansion 1 F = (tateCurve.specialize f).map (Int.castRingHom ℂ)}
  zero_mem' := ⟨0, by simp [qExpansion_zero]⟩
  add_mem' := by
    rintro f g ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F + G, by
      rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, hF, hG,
        map_add, map_add]⟩
  smul_mem' := by
    rintro n f ⟨F, hF⟩
    refine ⟨n • F, ?_⟩
    rw [ModularForm.qExpansion_zsmul one_pos one_mem_strictPeriods_SL, hF, map_zsmul,
      map_zsmul]

private instance : SetLike.GradedMonoid tateGraded where
  one_mem := ⟨ModularForm.mcast Nat.cast_zero.symm 1, by
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_one, map_one, map_one]⟩
  mul_mem := by
    rintro i j f g ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨ModularForm.mcast (Nat.cast_add i j).symm (F.mul G), by
      rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
        one_mem_strictPeriods_SL, hF, hG, map_mul, map_mul]⟩

private theorem c₄_mem_tateGraded : Universal.curve.c₄ ∈ tateGraded 4 :=
  ⟨E₄, by rw [specialize_c₄, map_tateCurve_c₄_eq_qExpansion_E₄]⟩

private theorem c₆_mem_tateGraded : Universal.curve.c₆ ∈ tateGraded 6 :=
  ⟨-E₆, by rw [specialize_c₆, map_tateCurve_c₆_eq_neg_qExpansion_E₆, FunLike.coe_neg,
    ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL]⟩

private theorem Δ_mem_tateGraded : Universal.curve.Δ ∈ tateGraded 12 :=
  ⟨ModularForm.mcast rfl (CuspForm.discriminant : ModularForm 𝒮ℒ 12), by
    rw [ModularForm.qExpansion_mcast, specialize_Δ, map_tateCurve_Δ_eq_qExpansion_discriminant,
      ModularFormClass.coe_modularForm, CuspForm.coe_discriminant]⟩

/-- **Integral modular forms have analytic Tate expansions.** An integral modular form `f` of
weight `k` has as Tate expansion the `q`-expansion of a level-one modular form of weight `k`; it is
unique by `ModularForm.qExpansion_injective`. -/
theorem _root_.WeierstrassCurve.IsIntegralModularForm.exists_qExpansion_eq_map_specialize_tateCurve
    {k : ℕ} {f : MvPolynomial Coeff ℤ} (hf : IsIntegralModularForm k f) :
    ∃ F : ModularForm 𝒮ℒ k, qExpansion 1 F = (tateCurve.specialize f).map (Int.castRingHom ℂ) := by
  -- Write `f = P(c₄, c₆, Δ)`. As `f` has weight `k`, so has `P` for the weights `4, 6, 12`.
  have hmem := hf.mem_adjoin
  set v := ![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ]
  set w : Fin 3 → ℕ := ![4, 6, 12]
  have hv (i : Fin 3) : (v i).IsWeightedHomogeneous coefficientWeight (w i) := by
    fin_cases i
    · exact isIntegralModularForm_c₄.isWeightedHomogeneous
    · exact isIntegralModularForm_c₆.isWeightedHomogeneous
    · exact isIntegralModularForm_Δ.isWeightedHomogeneous
  have hrange : ({Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} :
      Set (MvPolynomial Coeff ℤ)) = Set.range v := by
    simp only [v, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hrange, Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨P, rfl⟩ := hmem
  rw [← MvPolynomial.weightedHomogeneousComponent_eq_self hf.isWeightedHomogeneous,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.weightedHomogeneousComponent_aeval hv]
  refine (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k P).aeval_mem
    (𝒜 := tateGraded) fun i ↦ ?_
  fin_cases i
  · exact c₄_mem_tateGraded
  · exact c₆_mem_tateGraded
  · exact Δ_mem_tateGraded

/-- In every even weight `k ≠ 2` there is an integral modular form in `ℤ[c₄, c₆, Δ]`, a monomial
`c₄ᵃ (-c₆)ᵇ`, whose Tate expansion has constant coefficient `1`. -/
private theorem exists_isIntegralModularForm_constantCoeff_specialize_eq_one {k : ℕ}
    (hk : ¬Odd k) (h₂ : k ≠ 2) :
    ∃ g ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ},
      IsIntegralModularForm k g ∧ constantCoeff (tateCurve.specialize g) = 1 := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, 4 * a + 6 * b = k :=
    ⟨k / 4 - k % 4 / 2, k % 4 / 2, by grind⟩
  refine ⟨Universal.curve.c₄ ^ a * (-Universal.curve.c₆) ^ b,
    mul_mem (pow_mem (Algebra.subset_adjoin (by simp)) a)
      (pow_mem (neg_mem (Algebra.subset_adjoin (by simp))) b),
    (isIntegralModularForm_c₄.pow a).mul (isIntegralModularForm_c₆.neg.pow b), ?_⟩
  simp [specialize_c₄, specialize_c₆, constantCoeff_divisorSumSeries]

/-- Division by `Δ` preserves integral `q`-expansions: if a cusp form has the integral expansion
`P`, its quotient by `Δ` has an integral expansion `Q` with `P = Δ(q) Q`, where `Δ(q)` is the Tate
discriminant. -/
private theorem exists_qExpansion_discriminantEquiv_eq {k : ℤ} {F : ModularForm 𝒮ℒ k}
    (hF : (qExpansion 1 F).coeff 0 = 0) {P : ℤ⟦X⟧}
    (hP : qExpansion 1 F = P.map (Int.castRingHom ℂ)) :
    ∃ Q : ℤ⟦X⟧, qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm F hF)) =
      Q.map (Int.castRingHom ℂ) ∧ tateCurve.Δ * Q = P := by
  -- The Tate discriminant is `q u` for a unit `u`, and `P = q P₁` since `F` is a cusp form.
  obtain ⟨u, -, hu, hΔu⟩ := exists_tateCurve_Δ_eq_X_mul
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨P₁, rfl⟩ : X ∣ P := X_dvd_iff.mpr (by simpa [hP] using hF)
  refine ⟨v * P₁, ?_, by rw [hΔu]; linear_combination X * P₁ * hv⟩
  have h := qExpansion_eq_qExpansion_discriminant_mul F hF
  rw [hP, ← map_tateCurve_Δ_eq_qExpansion_discriminant, hΔu, map_mul, map_mul, map_X,
    mul_assoc] at h
  rw [map_mul, mul_left_cancel₀ X_ne_zero h, ← mul_assoc, ← map_mul, hv, map_one, one_mul]

/-- **The integral lattice of level-one modular forms.** A level-one modular form of weight `k`
whose `q`-expansion `P` has integer coefficients is the Tate expansion of an integral modular form
of weight `k` lying in `ℤ[c₄, c₆, Δ]`. -/
theorem _root_.ModularForm.exists_isIntegralModularForm_specialize_tateCurve_eq {k : ℕ}
    (F : ModularForm 𝒮ℒ k) {P : ℤ⟦X⟧} (hP : qExpansion 1 F = P.map (Int.castRingHom ℂ)) :
    ∃ f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ},
      IsIntegralModularForm k f ∧ tateCurve.specialize f = P := by
  induction k using Nat.strong_induction_on generalizing P with
  | _ k ih =>
  set A := Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}
  have hinj : Function.Injective (PowerSeries.map (Int.castRingHom ℂ)) :=
    map_injective _ Int.cast_injective
  -- Forms of odd weight or of weight `2` vanish.
  by_cases hzero : Odd k ∨ k = 2
  · have hF : F = 0 := by
      rcases hzero with hodd | rfl
      · exact levelOne_odd_weight_eq_zero hodd.natCast F
      · exact rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero F
    refine ⟨0, zero_mem _, isIntegralModularForm_zero k, hinj ?_⟩
    rw [map_zero, map_zero, ← hP, hF, FunLike.coe_zero, qExpansion_zero]
  push Not at hzero
  -- Otherwise subtracting `a₀ g`, with `g = 1 + ⋯`, from `F` leaves a cusp form `F'`.
  obtain ⟨g, hgA, hg, hg₀⟩ :=
    exists_isIntegralModularForm_constantCoeff_specialize_eq_one hzero.1 hzero.2
  obtain ⟨G, hG⟩ := hg.exists_qExpansion_eq_map_specialize_tateCurve
  set a₀ := constantCoeff P
  set F' := F - a₀ • G
  have hF' : qExpansion 1 F' = (P - a₀ • tateCurve.specialize g).map (Int.castRingHom ℂ) := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_zsmul one_pos one_mem_strictPeriods_SL, hP, hG, map_sub,
      map_zsmul]
  have hcusp : (qExpansion 1 F').coeff 0 = 0 := by
    rw [hF', coeff_map, coeff_zero_eq_constantCoeff_apply]
    simp [hg₀, a₀]
  -- Then `F' = Δ H` with `H` integral, and by induction `H` comes from some `h` (or vanishes, if
  -- `k < 12`); so `F` comes from `a₀ g + Δ h`.
  obtain ⟨Q, hHQ, hQ⟩ := exists_qExpansion_discriminantEquiv_eq hcusp hF'
  set H := CuspForm.discriminantEquiv (toCuspForm F' hcusp)
  obtain ⟨h, hhA, hh, hhQ⟩ : ∃ h ∈ A, IsIntegralModularForm k (Universal.curve.Δ * h) ∧
      tateCurve.specialize h = Q := by
    rcases lt_or_ge k 12 with hk | hk
    · have hH₀ : H = 0 :=
        rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by omega)) H
      refine ⟨0, zero_mem _, by simp [isIntegralModularForm_zero], hinj ?_⟩
      rw [map_zero, map_zero, ← hHQ, hH₀, FunLike.coe_zero, qExpansion_zero]
    · obtain ⟨h, hhA, hh, hhQ⟩ := ih (k - 12) (by omega)
        (ModularForm.mcast (by omega) H) (by rwa [ModularForm.qExpansion_mcast])
      have hk12 : 12 + (k - 12) = k := by omega
      refine ⟨h, hhA, ?_, hhQ⟩
      simpa [hk12] using isIntegralModularForm_Δ.mul hh
  refine ⟨a₀ • g + Universal.curve.Δ * h,
    add_mem (zsmul_mem hgA a₀) (mul_mem (Algebra.subset_adjoin (by simp)) hhA),
    (hg.smul a₀).add hh, ?_⟩
  rw [map_add, map_zsmul, map_mul _ Universal.curve.Δ, specialize_Δ, hhQ, hQ]
  abel

end TauCeti
