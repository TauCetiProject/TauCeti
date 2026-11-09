/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.ModularForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.AlgebraicGeometry.EllipticCurve.Invariants.Presentation
import TauCeti.NumberTheory.ModularForms.LevelOne.GradedRing
import TauCeti.NumberTheory.ModularForms.QExpansion.Graded

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

Because `qExpansion 1 E₄` and `qExpansion 1 E₆` are algebraically independent over `ℂ`
(`TauCeti.ModularForm.algebraicIndependent_qExpansion_E₄_E₆`), the Tate invariants `c₄(q)` and
`c₆(q)` are algebraically independent over `ℤ`, so `ℤ[c₄(q), c₆(q), Δ(q)]` has the same
presentation `ℤ[C₄, C₆, D] / (C₄³ - C₆² - 1728D)` as `ℤ[c₄, c₆, Δ]` on the universal curve.
Specializing to the Tate curve is therefore injective on `ℤ[c₄, c₆, Δ]` and on all integral modular
forms (`TauCeti.injOn_specialize_tateCurve`,
`WeierstrassCurve.IsIntegralModularForm.eq_of_specialize_tateCurve_eq`). Weight by weight this
identifies `TauCeti.WeierstrassCurve.integralModularFormSubmodule k` with the analytic integral
lattice `TauCeti.ModularForm.integralAtCusps (Int.castRingHom ℂ).range 𝒮ℒ k`
(`TauCeti.integralModularFormEquivIntegralAtCusps`), and extending scalars along the ring
presentations yields the `ℂ`-algebra isomorphism
`ℂ ⊗[ℤ] ℤ[c₄, c₆, Δ] ≃ₐ[ℂ] ⨁ k : ℤ, ModularForm 𝒮ℒ k`
(`TauCeti.complexAdjoinC₄C₆ΔEquivModularForms`) compatible with `q`-expansions, without assuming
complex uniformization of elliptic curves.

## Main definitions

* `TauCeti.adjoinC₄C₆ΔEquivTate`: the `ℤ`-algebra isomorphism
  `ℤ[c₄, c₆, Δ] ≃ₐ[ℤ] ℤ[tateCurve.c₄, tateCurve.c₆, tateCurve.Δ]` induced by Tate specialization.
* `TauCeti.integralModularFormToModularForm`: the comparison `ℤ`-linear map from weight-`k`
  integral modular forms to `ModularForm 𝒮ℒ k`.
* `TauCeti.integralModularFormEquivIntegralAtCusps`: the weight-`k` `ℤ`-linear isomorphism onto
  `TauCeti.ModularForm.integralAtCusps (Int.castRingHom ℂ).range 𝒮ℒ k`.
* `TauCeti.adjoinC₄C₆ΔToModularForms`: the injective `ℤ`-algebra homomorphism
  `ℤ[c₄, c₆, Δ] →ₐ[ℤ] DirectSum ℤ (ModularForm 𝒮ℒ)` sending `c₄, c₆, Δ` to `E₄, -E₆, Δ`.
* `TauCeti.complexAdjoinC₄C₆ΔEquivModularForms`: the `ℂ`-algebra isomorphism
  `ℂ ⊗[ℤ] ℤ[c₄, c₆, Δ] ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ)`.

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
* `TauCeti.algebraicIndependent_tateCurve_c₄_c₆`, `TauCeti.injOn_specialize_tateCurve`,
  `WeierstrassCurve.IsIntegralModularForm.eq_of_specialize_tateCurve_eq`: algebraic independence of
  `tateCurve.c₄, tateCurve.c₆` and injectivity of the Tate `q`-expansion.

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
open scoped MatrixGroups ArithmeticFunction.sigma TensorProduct

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

/-- **Algebraic independence of `c₄` and `c₆` of the Tate curve.** Since the Tate invariants map to
the `q`-expansions of `E₄` and `-E₆`, which are algebraically independent over `ℂ`
(`TauCeti.ModularForm.algebraicIndependent_qExpansion_E₄_E₆`), `tateCurve.c₄` and `tateCurve.c₆`
are algebraically independent over `ℤ` inside `ℤ⟦X⟧`. -/
theorem algebraicIndependent_tateCurve_c₄_c₆ :
    AlgebraicIndependent ℤ ![tateCurve.c₄, tateCurve.c₆] := by
  have h : AlgebraicIndependent ℂ (PowerSeries.map (Int.castRingHom ℂ) ∘
      ![tateCurve.c₄, tateCurve.c₆]) := by
    rw [show PowerSeries.map (Int.castRingHom ℂ) ∘ ![tateCurve.c₄, tateCurve.c₆] =
        ![qExpansion 1 E₄, -qExpansion 1 E₆] by
      funext i
      fin_cases i
      · exact map_tateCurve_c₄_eq_qExpansion_E₄
      · exact map_tateCurve_c₆_eq_neg_qExpansion_E₆]
    let signFlip : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
      MvPolynomial.aeval ![MvPolynomial.X 0, -MvPolynomial.X 1]
    have hid : Function.LeftInverse signFlip signFlip :=
      DFunLike.congr_fun (by ext i; fin_cases i <;> simp [signFlip] :
        signFlip.comp signFlip = AlgHom.id ℂ _)
    have haeval : (MvPolynomial.aeval ![qExpansion 1 E₄, qExpansion 1 E₆]).comp signFlip =
        MvPolynomial.aeval ![qExpansion 1 E₄, -qExpansion 1 E₆] := by
      ext i
      fin_cases i <;> simp [signFlip]
    rw [algebraicIndependent_iff_injective_aeval, ← haeval, AlgHom.coe_comp]
    exact (algebraicIndependent_iff_injective_aeval.mp
      TauCeti.ModularForm.algebraicIndependent_qExpansion_E₄_E₆).comp hid.injective
  exact h.of_ringHom_of_comp_eq (Int.castRingHom ℂ) (PowerSeries.map (Int.castRingHom ℂ))
    Int.cast_injective (RingHom.ext_int _ _)

/-- **Isomorphism of the universal invariant ring with its Tate `q`-expansion image.** Since both
`ℤ[c₄, c₆, Δ]` on the universal curve and `ℤ[c₄(q), c₆(q), Δ(q)] ⊆ ℤ⟦q⟧` on the Tate curve are
presented by `c₄³ - c₆² = 1728Δ`, specialization to the Tate curve induces an isomorphism of
`ℤ`-algebras between them. -/
noncomputable def adjoinC₄C₆ΔEquivTate :
    Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} ≃ₐ[ℤ]
      Algebra.adjoin ℤ {tateCurve.c₄, tateCurve.c₆, tateCurve.Δ} :=
  (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆).symm.trans
    (tateCurve.adjoinC₄C₆ΔEquiv algebraicIndependent_tateCurve_c₄_c₆)

@[simp]
theorem coe_adjoinC₄C₆ΔEquivTate
    (x : Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    (adjoinC₄C₆ΔEquivTate x : ℤ⟦X⟧) = tateCurve.specialize (x : MvPolynomial Coeff ℤ) := by
  obtain ⟨q, rfl⟩ :=
    (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆).surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [adjoinC₄C₆ΔEquivTate, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    WeierstrassCurve.adjoinC₄C₆ΔEquiv_mk, WeierstrassCurve.adjoinC₄C₆ΔEquiv_mk]
  have hcomp : tateCurve.specialize.comp
      (MvPolynomial.aeval (R := ℤ)
        ![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ]).toRingHom =
      (MvPolynomial.aeval (R := ℤ) ![tateCurve.c₄, tateCurve.c₆, tateCurve.Δ]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ match i with
    | 0 => by simp [specialize_c₄]
    | 1 => by simp [specialize_c₆]
    | 2 => by simp [specialize_Δ]
  exact (DFunLike.congr_fun hcomp P).symm

/-- **Injectivity of Tate `q`-expansion on `ℤ[c₄, c₆, Δ]`.** Specializing to the Tate curve is
injective on the subring generated by the universal invariants `c₄`, `c₆` and `Δ`. -/
theorem injOn_specialize_tateCurve :
    Set.InjOn tateCurve.specialize
      (Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) := by
  intro f hf g hg hfg
  have hsub : adjoinC₄C₆ΔEquivTate ⟨f, hf⟩ = adjoinC₄C₆ΔEquivTate ⟨g, hg⟩ :=
    Subtype.ext (by simpa only [coe_adjoinC₄C₆ΔEquivTate] using hfg)
  exact congrArg Subtype.val (adjoinC₄C₆ΔEquivTate.injective hsub)

/-- **Injectivity of the Tate `q`-expansion on integral modular forms.** Two integral modular forms
(possibly of different weights) with the same Tate `q`-expansion are equal. -/
theorem _root_.WeierstrassCurve.IsIntegralModularForm.eq_of_specialize_tateCurve_eq
    {k l : ℕ} {f g : MvPolynomial Coeff ℤ}
    (hf : IsIntegralModularForm k f) (hg : IsIntegralModularForm l g)
    (h : tateCurve.specialize f = tateCurve.specialize g) : f = g :=
  injOn_specialize_tateCurve hf.mem_adjoin hg.mem_adjoin h

/-- The comparison `ℤ`-linear map sending a weight-`k` integral modular form of the Weierstrass
coordinate-change action to the unique analytic level-one modular form of weight `k` with the same
`q`-expansion. -/
noncomputable def integralModularFormToModularForm (k : ℕ) :
    TauCeti.WeierstrassCurve.integralModularFormSubmodule k →ₗ[ℤ] ModularForm 𝒮ℒ k where
  toFun f :=
    (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
      f.2).exists_qExpansion_eq_map_specialize_tateCurve.choose
  map_add' f g := by
    refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
    dsimp only
    rw [(TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
        (f + g).2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec,
      FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
      (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
        f.2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec,
      (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
        g.2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec]
    simp
  map_smul' n f := by
    refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
    dsimp only
    rw [(TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
        (n • f).2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec,
      RingHom.id_apply, ModularForm.qExpansion_zsmul one_pos one_mem_strictPeriods_SL,
      (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
        f.2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec,
      Submodule.coe_smul, map_zsmul, map_zsmul]

@[simp]
theorem qExpansion_integralModularFormToModularForm (k : ℕ)
    (f : TauCeti.WeierstrassCurve.integralModularFormSubmodule k) :
    qExpansion 1 (integralModularFormToModularForm k f) =
      (tateCurve.specialize (f : MvPolynomial Coeff ℤ)).map (Int.castRingHom ℂ) :=
  (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
    f.2).exists_qExpansion_eq_map_specialize_tateCurve.choose_spec

/-- The comparison map `integralModularFormToModularForm k` from weight-`k` integral modular forms
to analytic level-one modular forms of weight `k` is injective. -/
theorem integralModularFormToModularForm_injective (k : ℕ) :
    Function.Injective (integralModularFormToModularForm k) := by
  intro f g h
  ext1
  refine (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp
    f.2).eq_of_specialize_tateCurve_eq
    (TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mp g.2) ?_
  refine PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective ?_
  rw [← qExpansion_integralModularFormToModularForm,
    ← qExpansion_integralModularFormToModularForm, h]

-- In the next four `@[simp]` lemmas, `F` is given explicitly so the implicit `DFunLike.coe`
-- weight is `(k : ℤ)` rather than `Nat.cast k`, putting the left-hand sides in `simp`-normal form.
@[simp]
theorem integralModularFormToModularForm_one :
    DFunLike.coe (F := _ →ₗ[ℤ] ModularForm 𝒮ℒ 0) (integralModularFormToModularForm 0)
      ⟨1, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr
        isIntegralModularForm_one⟩ = (1 : ModularForm 𝒮ℒ 0) := by
  refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
  dsimp only
  rw [qExpansion_integralModularFormToModularForm, ModularForm.qExpansion_one, map_one, map_one]

@[simp]
theorem integralModularFormToModularForm_c₄ :
    DFunLike.coe (F := _ →ₗ[ℤ] ModularForm 𝒮ℒ 4) (integralModularFormToModularForm 4)
      ⟨Universal.curve.c₄, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr
        isIntegralModularForm_c₄⟩ = E₄ := by
  refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
  dsimp only
  rw [qExpansion_integralModularFormToModularForm, specialize_c₄,
    map_tateCurve_c₄_eq_qExpansion_E₄]

@[simp]
theorem integralModularFormToModularForm_c₆ :
    DFunLike.coe (F := _ →ₗ[ℤ] ModularForm 𝒮ℒ 6) (integralModularFormToModularForm 6)
      ⟨Universal.curve.c₆, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr
        isIntegralModularForm_c₆⟩ = -E₆ := by
  refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
  dsimp only
  rw [qExpansion_integralModularFormToModularForm, specialize_c₆,
    map_tateCurve_c₆_eq_neg_qExpansion_E₆, FunLike.coe_neg,
    ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL]

@[simp]
theorem integralModularFormToModularForm_Δ :
    DFunLike.coe (F := _ →ₗ[ℤ] ModularForm 𝒮ℒ 12) (integralModularFormToModularForm 12)
      ⟨Universal.curve.Δ, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr
        isIntegralModularForm_Δ⟩ =
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12) := by
  refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
  dsimp only
  rw [qExpansion_integralModularFormToModularForm, specialize_Δ,
    map_tateCurve_Δ_eq_qExpansion_discriminant, ModularFormClass.coe_modularForm,
    CuspForm.coe_discriminant]

/-- `integralModularFormToModularForm` respects graded multiplication of integral modular forms
across weights. -/
theorem integralModularFormToModularForm_mul {k l : ℕ}
    (f : TauCeti.WeierstrassCurve.integralModularFormSubmodule k)
    (g : TauCeti.WeierstrassCurve.integralModularFormSubmodule l) :
    integralModularFormToModularForm (k + l) ⟨f.1 * g.1, SetLike.mul_mem_graded f.2 g.2⟩ =
      ModularForm.mcast (Nat.cast_add k l).symm
        ((integralModularFormToModularForm k f).mul (integralModularFormToModularForm l g)) := by
  refine ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_
  dsimp only
  rw [qExpansion_integralModularFormToModularForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    qExpansion_integralModularFormToModularForm, qExpansion_integralModularFormToModularForm,
    map_mul, map_mul]

/-- **Weight-by-weight isomorphism with the integral lattice of level-one modular forms.** For each
weight `k : ℕ`, the Tate `q`-expansion identifies the `ℤ`-module of weight-`k` integral modular
forms of the Weierstrass coordinate-change action with the integral lattice
`TauCeti.ModularForm.integralAtCusps (Int.castRingHom ℂ).range 𝒮ℒ k` of analytic level-one modular
forms whose cusp `q`-expansion has integer coefficients. -/
noncomputable def integralModularFormEquivIntegralAtCusps (k : ℕ) :
    TauCeti.WeierstrassCurve.integralModularFormSubmodule k ≃ₗ[ℤ]
      TauCeti.ModularForm.integralAtCusps (Int.castRingHom ℂ).range 𝒮ℒ k :=
  LinearEquiv.ofBijective
    ((integralModularFormToModularForm k).codRestrict _ fun f ↦
      TauCeti.ModularForm.mem_integralAtCusps_intCast_SL2Z_iff.mpr
        ⟨tateCurve.specialize f.1, qExpansion_integralModularFormToModularForm k f⟩)
    ⟨fun f g h ↦ integralModularFormToModularForm_injective k (congrArg Subtype.val h),
     fun F ↦ by
       obtain ⟨P, hP⟩ := TauCeti.ModularForm.mem_integralAtCusps_intCast_SL2Z_iff.mp F.2
       obtain ⟨f, -, hf, hfP⟩ :=
         ModularForm.exists_isIntegralModularForm_specialize_tateCurve_eq F.1 hP
       let fSub : TauCeti.WeierstrassCurve.integralModularFormSubmodule k :=
         ⟨f, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr hf⟩
       refine ⟨fSub, Subtype.ext <|
         ModularForm.qExpansion_injective one_pos one_mem_strictPeriods_SL ?_⟩
       dsimp only
       rw [LinearMap.codRestrict_apply, qExpansion_integralModularFormToModularForm, hfP, ← hP]⟩

@[simp]
theorem coe_integralModularFormEquivIntegralAtCusps (k : ℕ)
    (f : TauCeti.WeierstrassCurve.integralModularFormSubmodule k) :
    (integralModularFormEquivIntegralAtCusps k f : ModularForm 𝒮ℒ k) =
      integralModularFormToModularForm k f :=
  (rfl)

private theorem aeval_E₄_neg_E₆_discriminant_relation :
    MvPolynomial.aeval (R := ℤ)
      ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
        DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
        DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12)]
      (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 - 1728 * MvPolynomial.X 2) = 0 := by
  have hΔ := (eq_inv_smul_iff₀ (by norm_num : (1728 : ℂ) ≠ 0)).mp
    (by simpa using discriminant_eq_E₄_cube_sub_E₆_sq_graded)
  rw [ofNat_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at hΔ
  simp [hΔ]

/-- The canonical `ℤ`-algebra homomorphism from `ℤ[c₄, c₆, Δ]` to the graded ring
`⨁ k : ℤ, ModularForm 𝒮ℒ k` sending `c₄ ↦ E₄`, `c₆ ↦ -E₆` and `Δ ↦ Δ`, constructed directly from
the presentation `c₄³ - c₆² = 1728Δ` (`WeierstrassCurve.adjoinC₄C₆ΔEquiv`). -/
noncomputable def adjoinC₄C₆ΔToModularForms :
    Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} →ₐ[ℤ]
      DirectSum ℤ (ModularForm 𝒮ℒ) :=
  let evalHom := MvPolynomial.aeval (R := ℤ)
    ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
      DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
      DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12)]
  (Ideal.Quotient.liftₐ
    (Ideal.span {(MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 - 1728 * MvPolynomial.X 2 :
      MvPolynomial (Fin 3) ℤ)})
    evalHom
    (fun _ hP ↦ RingHom.mem_ker.mp <| (Ideal.span_le (I := RingHom.ker evalHom.toRingHom)).mpr
      (Set.singleton_subset_iff.mpr aeval_E₄_neg_E₆_discriminant_relation) hP)).comp
    (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆).symm.toAlgHom

private theorem adjoinC₄C₆ΔToModularForms_aeval (P : MvPolynomial (Fin 3) ℤ) :
    adjoinC₄C₆ΔToModularForms
      (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆
        (Ideal.Quotient.mk _ P)) =
      MvPolynomial.aeval (R := ℤ)
        ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
          DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
          DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12)] P := by
  rw [adjoinC₄C₆ΔToModularForms, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rfl

private noncomputable def adjoinGen (i : Fin 3) :
    Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} :=
  Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆
    (Ideal.Quotient.mk _ (MvPolynomial.X i))

@[simp]
private theorem coe_adjoinGen (i : Fin 3) :
    (adjoinGen i : MvPolynomial Coeff ℤ) =
      ![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ] i := by
  simp [adjoinGen]

private theorem mk_eq_adjoinGen (i : Fin 3)
    (h : ![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ] i ∈
      Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    (⟨![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ] i, h⟩ :
      Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) =
      adjoinGen i := by
  ext1
  simp

@[simp]
private theorem adjoinC₄C₆ΔToModularForms_adjoinGen (i : Fin 3) :
    adjoinC₄C₆ΔToModularForms (adjoinGen i) =
      ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
        DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
        DirectSum.of (ModularForm 𝒮ℒ) 12
          (CuspForm.discriminant : ModularForm 𝒮ℒ 12)] i := by
  rw [adjoinGen, adjoinC₄C₆ΔToModularForms_aeval, MvPolynomial.aeval_X]

@[simp]
theorem adjoinC₄C₆ΔToModularForms_c₄ :
    adjoinC₄C₆ΔToModularForms
      ⟨Universal.curve.c₄, Algebra.subset_adjoin (by simp)⟩ =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ :=
  mk_eq_adjoinGen 0 _ ▸ adjoinC₄C₆ΔToModularForms_adjoinGen 0

@[simp]
theorem adjoinC₄C₆ΔToModularForms_c₆ :
    adjoinC₄C₆ΔToModularForms
      ⟨Universal.curve.c₆, Algebra.subset_adjoin (by simp)⟩ =
      DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆) :=
  mk_eq_adjoinGen 1 _ ▸ adjoinC₄C₆ΔToModularForms_adjoinGen 1

@[simp]
theorem adjoinC₄C₆ΔToModularForms_Δ :
    adjoinC₄C₆ΔToModularForms
      ⟨Universal.curve.Δ, Algebra.subset_adjoin (by simp)⟩ =
      DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12) :=
  mk_eq_adjoinGen 2 _ ▸ adjoinC₄C₆ΔToModularForms_adjoinGen 2

/-- **Compatibility of `adjoinC₄C₆ΔToModularForms` with `q`-expansions.** Applying
`ModularForm.qExpansionRingHom` to the analytic image of `x ∈ ℤ[c₄, c₆, Δ]` recovers its Tate
`q`-expansion `tateCurve.specialize x`. -/
@[simp]
theorem qExpansionRingHom_adjoinC₄C₆ΔToModularForms
    (x : Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    ModularForm.qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
      (adjoinC₄C₆ΔToModularForms x) =
      (tateCurve.specialize (x : MvPolynomial Coeff ℤ)).map (Int.castRingHom ℂ) := by
  obtain ⟨q, rfl⟩ :=
    (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆).surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [adjoinC₄C₆ΔToModularForms_aeval, WeierstrassCurve.adjoinC₄C₆ΔEquiv_mk]
  have hhom : (ModularForm.qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL).comp
      (MvPolynomial.aeval (R := ℤ)
        ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
          DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
          DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12)]).toRingHom =
      ((PowerSeries.map (Int.castRingHom ℂ)).comp tateCurve.specialize).comp
        (MvPolynomial.aeval (R := ℤ)
          ![Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ match i with
    | 0 => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, Matrix.cons_val_zero, ModularForm.qExpansionRingHom_apply,
        specialize_c₄, map_tateCurve_c₄_eq_qExpansion_E₄]
    | 1 => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero,
        ModularForm.qExpansionRingHom_apply, FunLike.coe_neg,
        ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, specialize_c₆,
        map_tateCurve_c₆_eq_neg_qExpansion_E₆]
    | 2 => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ModularForm.qExpansionRingHom_apply, ModularFormClass.coe_modularForm,
        CuspForm.coe_discriminant, specialize_Δ, map_tateCurve_Δ_eq_qExpansion_discriminant]
  exact DFunLike.congr_fun hhom P

/-- The comparison `ℤ`-algebra homomorphism `adjoinC₄C₆ΔToModularForms` from `ℤ[c₄, c₆, Δ]` to the
graded ring of level-one modular forms is injective. -/
theorem adjoinC₄C₆ΔToModularForms_injective :
    Function.Injective adjoinC₄C₆ΔToModularForms := by
  intro x y hxy
  ext1
  refine injOn_specialize_tateCurve x.2 y.2 ?_
  refine PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective ?_
  simpa only [qExpansionRingHom_adjoinC₄C₆ΔToModularForms] using
    congrArg (ModularForm.qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL) hxy

/-- On a weight-`k` integral modular form `f`, the ring homomorphism `adjoinC₄C₆ΔToModularForms`
agrees with `integralModularFormToModularForm k` placed in degree `k`. -/
theorem adjoinC₄C₆ΔToModularForms_eq_of {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : IsIntegralModularForm k f) :
    adjoinC₄C₆ΔToModularForms ⟨f, hf.mem_adjoin⟩ =
      DirectSum.of (ModularForm 𝒮ℒ) (k : ℤ)
        (integralModularFormToModularForm k
          ⟨f, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule.mpr hf⟩) := by
  refine TauCeti.ModularForm.qExpansionRingHom_injective one_pos one_mem_strictPeriods_SL ?_
  rw [qExpansionRingHom_adjoinC₄C₆ΔToModularForms, ModularForm.qExpansionRingHom_apply,
    qExpansion_integralModularFormToModularForm]

private noncomputable def complexAdjoinToModularForms :
    (ℂ ⊗[ℤ] Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) →ₐ[ℂ]
      DirectSum ℤ (ModularForm 𝒮ℒ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) adjoinC₄C₆ΔToModularForms
    fun _ _ ↦ Commute.all _ _

private noncomputable def modularFormsToComplexAdjoin :
    DirectSum ℤ (ModularForm 𝒮ℒ) →ₐ[ℂ]
      (ℂ ⊗[ℤ] Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :=
  (MvPolynomial.aeval (R := ℂ)
    ![Algebra.TensorProduct.includeRight (adjoinGen 0),
      Algebra.TensorProduct.includeRight (-adjoinGen 1)]).comp
    TauCeti.ModularForm.mvPolynomialEquivModularForms.symm.toAlgHom

private theorem modularFormsToComplexAdjoin_E₄ :
    modularFormsToComplexAdjoin (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄) =
      Algebra.TensorProduct.includeRight (adjoinGen 0) := by
  have h : DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ =
      TauCeti.ModularForm.mvPolynomialEquivModularForms (MvPolynomial.X 0) := by
    simp
  rw [h, modularFormsToComplexAdjoin, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero]

private theorem modularFormsToComplexAdjoin_E₆ :
    modularFormsToComplexAdjoin (DirectSum.of (ModularForm 𝒮ℒ) 6 E₆) =
      Algebra.TensorProduct.includeRight (-adjoinGen 1) := by
  have h : DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ =
      TauCeti.ModularForm.mvPolynomialEquivModularForms (MvPolynomial.X 1) := by
    simp
  rw [h, modularFormsToComplexAdjoin, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]

private theorem modularFormsToComplexAdjoin_discriminant :
    modularFormsToComplexAdjoin
      (DirectSum.of (ModularForm 𝒮ℒ) 12 (CuspForm.discriminant : ModularForm 𝒮ℒ 12)) =
      Algebra.TensorProduct.includeRight (adjoinGen 2) := by
  have hrel : adjoinGen 0 ^ 3 - (-adjoinGen 1) ^ 2 = (1728 : ℕ) • adjoinGen 2 := by
    ext1
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    simpa using Universal.curve.c_relation.symm
  -- Keep `includeRight (-adjoinGen 1)` unexpanded so cancellation stays at the `AlgHom` level.
  have hrelT :
      (Algebra.TensorProduct.includeRight (adjoinGen 0) : ℂ ⊗[ℤ] _) ^ 3 -
        Algebra.TensorProduct.includeRight (-adjoinGen 1) ^ 2 =
        (1728 : ℂ) • Algebra.TensorProduct.includeRight (adjoinGen 2) := by
    simpa [-Algebra.TensorProduct.includeRight_apply, -map_neg, map_ofNat,
      ofNat_smul_eq_nsmul] using
      congrArg (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)) hrel
  simp [-Algebra.TensorProduct.includeRight_apply, -map_neg,
    discriminant_eq_E₄_cube_sub_E₆_sq_graded, modularFormsToComplexAdjoin_E₄,
    modularFormsToComplexAdjoin_E₆, hrelT]

private theorem complexAdjoinToModularForms_comp_modularFormsToComplexAdjoin :
    complexAdjoinToModularForms.comp modularFormsToComplexAdjoin = AlgHom.id ℂ _ := by
  have hpoly : (complexAdjoinToModularForms.comp modularFormsToComplexAdjoin).comp
      TauCeti.ModularForm.mvPolynomialEquivModularForms.toAlgHom =
      TauCeti.ModularForm.mvPolynomialEquivModularForms.toAlgHom := by
    refine MvPolynomial.algHom_ext fun i ↦ match i with
    | 0 => by simp [modularFormsToComplexAdjoin_E₄, complexAdjoinToModularForms]
    | 1 => by simp [modularFormsToComplexAdjoin_E₆, complexAdjoinToModularForms]
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨p, rfl⟩ := TauCeti.ModularForm.mvPolynomialEquivModularForms.surjective x
  exact DFunLike.congr_fun hpoly p

private theorem modularFormsToComplexAdjoin_adjoinC₄C₆ΔToModularForms
    (x : Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    modularFormsToComplexAdjoin (adjoinC₄C₆ΔToModularForms x) = 1 ⊗ₜ[ℤ] x := by
  obtain ⟨q, rfl⟩ :=
    (Universal.curve.adjoinC₄C₆ΔEquiv Universal.algebraicIndependent_c₄_c₆).surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [adjoinC₄C₆ΔToModularForms_aeval]
  have hhom : modularFormsToComplexAdjoin.toRingHom.comp
      (MvPolynomial.aeval (R := ℤ)
        ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
          DirectSum.of (ModularForm 𝒮ℒ) 6 (-E₆),
          DirectSum.of (ModularForm 𝒮ℒ) 12
            (CuspForm.discriminant : ModularForm 𝒮ℒ 12)]).toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp
        ((Universal.curve.adjoinC₄C₆ΔEquiv
          Universal.algebraicIndependent_c₄_c₆).toAlgHom.toRingHom.comp (Ideal.Quotient.mk _)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ match i with
    | 0 => by simp [modularFormsToComplexAdjoin_E₄, adjoinGen]
    | 1 => by
      simp [-Algebra.TensorProduct.includeRight_apply, modularFormsToComplexAdjoin_E₆, adjoinGen]
    | 2 => by simp [modularFormsToComplexAdjoin_discriminant, adjoinGen]
  exact DFunLike.congr_fun hhom P

private theorem modularFormsToComplexAdjoin_comp_complexAdjoinToModularForms :
    modularFormsToComplexAdjoin.comp complexAdjoinToModularForms = AlgHom.id ℂ _ := by
  ext1
  refine AlgHom.ext fun x ↦ ?_
  simp [complexAdjoinToModularForms, modularFormsToComplexAdjoin_adjoinC₄C₆ΔToModularForms]

/-- **Comparison of `ℂ ⊗[ℤ] ℤ[c₄, c₆, Δ]` with the graded `ℂ`-algebra of level-one modular
forms.** Extending scalars of `adjoinC₄C₆ΔToModularForms` to `ℂ` gives an isomorphism of
`ℂ`-algebras `ℂ ⊗[ℤ] ℤ[c₄, c₆, Δ] ≃ₐ[ℂ] ⨁ k : ℤ, ModularForm 𝒮ℒ k`, proved purely from the
presentations `c₄³ - c₆² = 1728Δ` and `ℂ[E₄, E₆] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` without complex
uniformization. -/
noncomputable def complexAdjoinC₄C₆ΔEquivModularForms :
    (ℂ ⊗[ℤ] Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) ≃ₐ[ℂ]
      DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofAlgHom complexAdjoinToModularForms modularFormsToComplexAdjoin
    complexAdjoinToModularForms_comp_modularFormsToComplexAdjoin
    modularFormsToComplexAdjoin_comp_complexAdjoinToModularForms

@[simp]
theorem complexAdjoinC₄C₆ΔEquivModularForms_tmul (c : ℂ)
    (x : Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    complexAdjoinC₄C₆ΔEquivModularForms (c ⊗ₜ[ℤ] x) = c • adjoinC₄C₆ΔToModularForms x := by
  rw [complexAdjoinC₄C₆ΔEquivModularForms, AlgEquiv.ofAlgHom_apply, complexAdjoinToModularForms,
    Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

/-- Under `complexAdjoinC₄C₆ΔEquivModularForms`, the analytic `q`-expansion of a pure tensor
`c ⊗ₜ x` in `ℂ ⊗[ℤ] ℤ[c₄, c₆, Δ]` equals `c` times the Tate `q`-expansion of `x`. -/
theorem qExpansionAlgHom_complexAdjoinC₄C₆ΔEquivModularForms_tmul (c : ℂ)
    (x : Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    ModularForm.qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL
      (complexAdjoinC₄C₆ΔEquivModularForms (c ⊗ₜ[ℤ] x)) =
      c • (tateCurve.specialize (x : MvPolynomial Coeff ℤ)).map (Int.castRingHom ℂ) := by
  rw [complexAdjoinC₄C₆ΔEquivModularForms_tmul, map_smul]
  exact congrArg (c • ·) (qExpansionRingHom_adjoinC₄C₆ΔToModularForms x)

end TauCeti
