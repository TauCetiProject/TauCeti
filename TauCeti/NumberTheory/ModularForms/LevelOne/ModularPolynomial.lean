/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.NumberTheory.ModularForms.LevelOne.SingularModuli

/-!
# The classical modular polynomial over `ℤ`

For a positive integer `n`, the cyclic-isogeny polynomial
`TauCeti.ModularForm.cyclicIsogenyPolynomial n j τ` is the monic polynomial

  `∏_{(a b; 0 d)} (X - j((a τ + b) / d))`

over the primitive upper-triangular matrices `(a b; 0 d)` of determinant `n` with `0 < a` and
`0 ≤ b < d` (`FixedDetMatrices.primitiveReps n`). Each coefficient of `X ^ k` is a holomorphic
`SL(2, ℤ)`-invariant function on the upper half-plane. This file proves that these coefficients
are meromorphic at the cusp with integer Laurent `q`-coefficients, descends the polynomial to a
monic integral bivariate polynomial `Φ_n(X, Y) ∈ ℤ[Y][X]`, and proves Kronecker's theorem that the
leading coefficient of the diagonal specialization `Φ_n(X, X) ∈ ℤ[X]` is `±1` when `n` is not a
square.

The integrality of the `q`-coefficients follows the classical cyclotomic Galois argument. In the
ramified parameter `q_{1/n} = exp(2 π i τ / n)`, the factor `j((a τ + b) / d)` has Laurent
expansion `J(ζ_n^{a b} q_{1/n}^{a^2})`, where `J ∈ ℤ⸨q⸩` is the `q`-expansion of `j` and
`ζ_n = exp(2 π i / n)`. Every coefficient of the product therefore lies in `ℤ[ζ_n]`, hence is
integral over `ℤ`. An element `σ ∈ Gal(ℚ(ζ_n) / ℚ)` sends `ζ_n` to `ζ_n^c` for some unit
`c ∈ (ℤ / nℤ)ˣ`, and `FixedDetMatrices.permRep c` permutes the primitive representatives of
determinant `n` via `(a b; 0 d) ↦ (a, c b mod d; 0, d)`, so `σ` fixes every coefficient of the
product. Fixed elements of `ℚ(ζ_n)` lie in `ℚ`, and algebraic integers in `ℚ` lie in `ℤ`.

For non-square `n`,
`TauCeti.ModularForm.isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial` shows that the
leading coefficient of `Φ_n(X, X)` is a unit in the ring of algebraic integers; since
`ℤ → integralClosure ℤ ℂ` is an injective integral extension, that leading coefficient is a unit in
`ℤ`, i.e., `±1`.

## Main definitions

* `TauCeti.ModularForm.modularPolynomial n`: the classical modular polynomial `Φ_n ∈ ℤ[X][X]`,
  characterized by
  `(modularPolynomial n).map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ`.
* `TauCeti.ModularForm.modularPolynomialDiag n`: the diagonal specialization
  `Φ_n(X, X) = (modularPolynomial n).eval X ∈ ℤ[X]`.

## Main results

* `TauCeti.ModularForm.laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range`: integrality of
  the Laurent `q`-coefficients of `(cyclicIsogenyPolynomial n j ·).coeff k`.
* `TauCeti.ModularForm.map_aeval_j_modularPolynomial`,
  `TauCeti.ModularForm.monic_modularPolynomial`,
  `TauCeti.ModularForm.natDegree_modularPolynomial`, and
  `TauCeti.ModularForm.eq_modularPolynomial_of_map_aeval_j_eq`: basic API and uniqueness of `Φ_n`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_modularPolynomialDiag`: for non-square `n`, the leading
  coefficient of `Φ_n(X, X)` is `±1`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C, Theorems 11.18 and 11.20.
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §3.
-/

public noncomputable section

open Matrix Polynomial UpperHalfPlane Filter Topology
open scoped MatrixGroups Manifold LaurentSeries

/-! ### Cyclotomic Galois descent and integrality of `q`-coefficients -/

namespace TauCeti.ModularForm

open FixedDetMatrices

section GaloisDescent

private abbrev cycField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / n)}

private def cycZeta (n : ℕ) : cycField n :=
  ⟨Complex.exp (2 * Real.pi * Complex.I / n), IntermediateField.mem_adjoin_simple_self ℚ _⟩

private theorem isPrimitiveRoot_cycZeta (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (cycZeta n) n := by
  have hC := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  rw [IsPrimitiveRoot.iff_def] at hC ⊢
  refine ⟨Subtype.ext (by simpa [cycZeta] using hC.1), fun l hl ↦ hC.2 l ?_⟩
  simpa [cycZeta] using congrArg Subtype.val hl

private def cycUnit (n : ℕ) [NeZero n] : (cycField n)ˣ :=
  Units.mk0 (cycZeta n) ((isPrimitiveRoot_cycZeta n).ne_zero (NeZero.ne n))

private theorem orderOf_cycUnit (n : ℕ) [NeZero n] : orderOf (cycUnit n) = n := by
  rw [← orderOf_units, cycUnit, Units.val_mk0, ← (isPrimitiveRoot_cycZeta n).eq_orderOf]

private theorem cycUnit_zpow_eq_pow_emod (n : ℕ) [NeZero n] (s : ℤ) :
    ((cycUnit n ^ s : (cycField n)ˣ) : cycField n) =
      cycZeta n ^ (s % (n : ℤ)).toNat := by
  conv_lhs =>
    rw [← zpow_mod_orderOf, orderOf_cycUnit,
      ← Int.toNat_of_nonneg (Int.emod_nonneg s (NeZero.ne (n : ℤ)))]
  rw [_root_.zpow_natCast, Units.val_pow_eq_pow_val, cycUnit, Units.val_mk0]

private theorem aut_apply_cycUnit_zpow {n : ℕ} [NeZero n] (σ : cycField n ≃ₐ[ℚ] cycField n)
    (s : ℤ) :
    σ ((cycUnit n ^ s : (cycField n)ˣ) : cycField n) =
      ((cycUnit n ^ ((((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val : ℤ) * s) :
        (cycField n)ˣ) : cycField n) := by
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, cycUnit, Units.val_mk0,
    map_zpow₀, ← (isPrimitiveRoot_cycZeta n).autToPow_spec ℚ σ,
    ← _root_.zpow_natCast, ← _root_.zpow_mul]

private def factorSeriesAux (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (a b : ℕ) : LaurentSeries (cycField n) :=
  LaurentSeries.expand (cycField n) (a ^ 2).toPNat'
    (TauCeti.LaurentSeries.rescale
      (cycUnit n ^ (a * b))
      (HahnSeries.mapRingHom (Int.castRingHom (cycField n)) jZ))

private def factorSeries (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : LaurentSeries (cycField n) :=
  factorSeriesAux n jZ (M 0 0).natAbs (M 0 1).natAbs

private theorem map_val_factorSeriesAux (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ) (a b : ℕ) :
    HahnSeries.mapRingHom (cycField n).val.toRingHom (factorSeriesAux n jZ a b) =
      LaurentSeries.expand ℂ (a ^ 2).toPNat'
        (TauCeti.LaurentSeries.rescale
          (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n) ^ (a * b))
            (pow_ne_zero _ (Complex.exp_ne_zero _)))
          (HahnSeries.mapRingHom (Int.castRingHom ℂ) jZ)) := by
  have hu : Units.map (cycField n).val.toRingHom.toMonoidHom (cycUnit n ^ (a * b)) =
      Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n) ^ (a * b))
        (pow_ne_zero _ (Complex.exp_ne_zero _)) := by
    apply Units.ext
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    simp [cycUnit, cycZeta]
  rw [factorSeriesAux, LaurentSeries.mapRingHom_expand,
    TauCeti.LaurentSeries.mapRingHom_rescale, ← RingHom.comp_apply,
    ← HahnSeries.mapRingHom_comp,
    RingHom.ext_int ((cycField n).val.toRingHom.comp (Int.castRingHom (cycField n)))
      (Int.castRingHom ℂ), hu]

private theorem map_val_factorSeries {n : ℕ} [NeZero n] {jZ : LaurentSeries ℤ}
    (hjZ : HahnSeries.mapRingHom (Int.castRingHom ℂ) jZ = UpperHalfPlane.laurentQExpansion 1 j)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    HahnSeries.mapRingHom (cycField n).val.toRingHom (factorSeries n jZ A.val) =
      UpperHalfPlane.laurentQExpansion n (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  have hn_pos : (0 : ℤ) < n := Int.natCast_pos.mpr (NeZero.pos n)
  have hd_pos : 0 < A.val 1 1 := pos_val_one_one_of_mem_reps hn_pos hA
  have hu : Units.mk0
        (Complex.exp (2 * Real.pi * Complex.I / n) ^
          ((A.val 0 0).natAbs * (A.val 0 1).natAbs))
        (pow_ne_zero _ (Complex.exp_ne_zero _)) =
      Units.mk0 (Function.Periodic.qParam 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ))
        (Function.Periodic.qParam_ne_zero _) := by
    apply Units.ext
    simp only [Units.val_mk0, Function.Periodic.qParam, ← Complex.exp_natCast_mul]
    congr 1
    have ha_eq : (((A.val 0 0).natAbs : ℕ) : ℂ) = A.val 0 0 := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hA.2.1.le]
    have hb_eq : (((A.val 0 1).natAbs : ℕ) : ℂ) = A.val 0 1 := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hA.2.2.1]
    have had : (A.val 0 0 : ℂ) * A.val 1 1 = n := by
      exact_mod_cast apply_zero_zero_mul_apply_one_one hA.1
    have hd_ne : (A.val 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd_pos.ne'
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    push_cast
    rw [ha_eq, hb_eq]
    field_simp
    rw [← had]
    ring
  have hcomp := TauCeti.UpperHalfPlane.laurentQExpansion_comp_toGLReal_smul hn_pos hA
    periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j
  rw [Int.cast_natCast] at hcomp
  exact (map_val_factorSeriesAux n jZ (A.val 0 0).natAbs (A.val 0 1).natAbs).trans
    (by rw [hjZ, hu, ← hcomp])

private theorem isIntegral_coeff_factorSeries (n : ℕ) [NeZero n] (jZ : LaurentSeries ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℤ) :
    IsIntegral ℤ ((factorSeries n jZ M).coeff m) := by
  rw [factorSeries, factorSeriesAux]
  set a := (M 0 0).natAbs
  set b := (M 0 1).natAbs
  set d : ℕ+ := (a ^ 2).toPNat'
  by_cases hm : ((d : ℕ) : ℤ) ∣ m
  · obtain ⟨r, rfl⟩ := hm
    rw [LaurentSeries.coeff_expand_mul (R := cycField n) d,
      TauCeti.LaurentSeries.coeff_rescale (R := cycField n),
      HahnSeries.coeff_mapRingHom, ← _root_.zpow_natCast, ← _root_.zpow_mul,
      cycUnit_zpow_eq_pow_emod]
    exact (((isPrimitiveRoot_cycZeta n).isIntegral (NeZero.pos n)).pow _).mul
      isIntegral_algebraMap
  · rw [LaurentSeries.coeff_expand_of_not_dvd (R := cycField n) d _ hm]
    exact isIntegral_zero

private theorem isIntegral_coeff_prod_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (s : Finset (FixedDetMatrix (Fin 2) ℤ n)) :
    ∀ (k : ℕ) (m : ℤ),
      IsIntegral ℤ (((∏ A ∈ s, (X - C (factorSeries n jZ A.val))).coeff k).coeff m) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k m
    rw [Finset.prod_empty, Polynomial.coeff_one]
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [↓reduceIte]
      rcases eq_or_ne m 0 with rfl | hm
      · simpa using (isIntegral_one : IsIntegral ℤ (1 : cycField n))
      · simp [HahnSeries.coeff_one, hm, isIntegral_zero]
    · simp [hk, isIntegral_zero]
  | cons a t hat ih =>
    intro k m
    have hmul : ∀ j, IsIntegral ℤ
        ((factorSeries n jZ a.val *
          (∏ i ∈ t, (X - C (factorSeries n jZ i.val))).coeff j).coeff m) :=
      fun j ↦ by
        rw [HahnSeries.coeff_mul]
        exact IsIntegral.sum _ fun p _ ↦
          (isIntegral_coeff_factorSeries n jZ a.val p.1).mul (ih j p.2)
    rcases k with _ | k
    · rw [Finset.prod_cons, Polynomial.mul_coeff_zero, Polynomial.coeff_sub,
        Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, HahnSeries.coeff_mul]
      exact IsIntegral.sum _ fun p _ ↦ by
        rw [HahnSeries.coeff_neg]
        exact (isIntegral_coeff_factorSeries n jZ a.val p.1).neg.mul (ih 0 p.2)
    · rw [Finset.prod_cons, Polynomial.coeff_X_sub_C_mul, HahnSeries.coeff_sub]
      exact (ih k m).sub (hmul (k + 1))

private theorem map_aut_factorSeriesAux {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) (a b b' : ℕ) {q : ℤ}
    (hcong : (((isPrimitiveRoot_cycZeta n).autToPow ℚ σ : ZMod n).val : ℤ) * ((a * b : ℕ) : ℤ) =
      (n : ℤ) * q + ((a * b' : ℕ) : ℤ)) :
    HahnSeries.mapRingHom (σ : cycField n →+* cycField n) (factorSeriesAux n jZ a b) =
      factorSeriesAux n jZ a b' := by
  have hu : Units.map (σ : cycField n →+* cycField n).toMonoidHom (cycUnit n ^ (a * b)) =
      cycUnit n ^ (a * b') := by
    apply Units.ext
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_coe,
      ← _root_.zpow_natCast, aut_apply_cycUnit_zpow, ← _root_.zpow_natCast (cycUnit n) (a * b')]
    apply congrArg Units.val
    rw [zpow_eq_zpow_iff_modEq, orderOf_cycUnit, Int.modEq_iff_dvd]
    exact ⟨-q, by linear_combination -hcong⟩
  rw [factorSeriesAux, factorSeriesAux, LaurentSeries.mapRingHom_expand,
    TauCeti.LaurentSeries.mapRingHom_rescale, ← RingHom.comp_apply,
    ← HahnSeries.mapRingHom_comp,
    RingHom.ext_int ((σ : cycField n →+* cycField n).comp (Int.castRingHom (cycField n)))
      (Int.castRingHom (cycField n)), hu]

private theorem map_aut_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ primitiveReps (n : ℤ)) :
    HahnSeries.mapRingHom (σ : cycField n →+* cycField n) (factorSeries n jZ A.val) =
      factorSeries n jZ (permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ) A).val := by
  obtain ⟨⟨h₁₀, h₀₀, h₀₁, -⟩, -⟩ := mem_primitiveReps.mp hA
  have hprod : A.val 0 0 * A.val 1 1 = (n : ℤ) := apply_zero_zero_mul_apply_one_one h₁₀
  have hd : 0 < A.val 1 1 :=
    pos_val_one_one_of_mem_reps (Int.natCast_pos.mpr (NeZero.pos n)) (mem_primitiveReps.mp hA).1
  set u := (isPrimitiveRoot_cycZeta n).autToPow ℚ σ
  have hperm₀₀ : (permRep u A).val 0 0 = A.val 0 0 := val_permRep_zero_zero u A
  have hperm₀₁ : (permRep u A).val 0 1 = (((u : ZMod n).val : ℤ) * A.val 0 1) % A.val 1 1 :=
    val_permRep_zero_one u h₁₀
  set q := (((u : ZMod n).val : ℤ) * A.val 0 1) / A.val 1 1
  have hdiv := Int.emod_add_mul_ediv (((u : ZMod n).val : ℤ) * A.val 0 1) (A.val 1 1)
  have ha_eq : ((A.val 0 0).natAbs : ℤ) = A.val 0 0 := Int.natAbs_of_nonneg h₀₀.le
  have hb_eq : ((A.val 0 1).natAbs : ℤ) = A.val 0 1 := Int.natAbs_of_nonneg h₀₁
  have hb'_eq : (((permRep u A).val 0 1).natAbs : ℤ) =
      (((u : ZMod n).val : ℤ) * A.val 0 1) % A.val 1 1 :=
    (congrArg (fun x : ℤ ↦ (x.natAbs : ℤ)) hperm₀₁).trans
      (Int.natAbs_of_nonneg (Int.emod_nonneg _ hd.ne'))
  have hcong : ((u : ZMod n).val : ℤ) * (((A.val 0 0).natAbs * (A.val 0 1).natAbs : ℕ) : ℤ) =
      (n : ℤ) * q + (((A.val 0 0).natAbs * ((permRep u A).val 0 1).natAbs : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, ha_eq, hb_eq, hb'_eq]
    linear_combination -A.val 0 0 * hdiv + q * hprod
  exact (map_aut_factorSeriesAux jZ σ (A.val 0 0).natAbs (A.val 0 1).natAbs
    ((permRep u A).val 0 1).natAbs hcong).trans
      (congrArg (fun a ↦ factorSeriesAux n jZ a ((permRep u A).val 0 1).natAbs)
        (congrArg Int.natAbs hperm₀₀.symm))

private theorem map_aut_prod_X_sub_C_factorSeries {n : ℕ} [NeZero n] (jZ : LaurentSeries ℤ)
    (σ : cycField n ≃ₐ[ℚ] cycField n) :
    (∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.val))).map
        (HahnSeries.mapRingHom (σ : cycField n →+* cycField n)) =
      ∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.val)) := by
  rw [Polynomial.map_prod]
  refine Finset.prod_bij (fun A _ ↦ permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ) A)
    (fun _ hA ↦ permRep_mem_primitiveReps _ hA)
    (fun A₁ hA₁ A₂ hA₂ hEq ↦ by
      have := congrArg (permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹) hEq
      rwa [permRep_inv_permRep _ (mem_primitiveReps.mp hA₁).1,
        permRep_inv_permRep _ (mem_primitiveReps.mp hA₂).1] at this)
    (fun B hB ↦ ⟨permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹ B,
      permRep_mem_primitiveReps _ hB, by
        simpa using permRep_inv_permRep ((isPrimitiveRoot_cycZeta n).autToPow ℚ σ)⁻¹
          (mem_primitiveReps.mp hB).1⟩)
    fun A hA ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_aut_factorSeries jZ σ hA]

private theorem periodic_coeff_cyclicIsogenyPolynomial_j (n : ℕ) [NeZero n] (k : ℕ) :
    Function.Periodic ((fun τ : ℍ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) ∘ ofComplex) 1 :=
  TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mpr fun τ ↦ by
    rw [← modular_T_smul]
    exact congrArg (·.coeff k) (cyclicIsogenyPolynomial_smul (n := n) j_smul_SL2Z _ τ)

private theorem meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j (n : ℕ) [NeZero n]
    (k : ℕ) :
    MeromorphicAt (cuspFunction 1 fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) 0 := by
  have hn_pos : (0 : ℤ) < n := Int.natCast_pos.mpr (NeZero.pos n)
  have hmer_n : MeromorphicAt
      (cuspFunction n fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) 0 := by
    simp only [cyclicIsogenyPolynomial_def]
    have h := UpperHalfPlane.meromorphicAt_cuspFunction_coeff_prod_X_sub_C
      (s := primitiveReps (n : ℤ))
      (fun A hA ↦ TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_comp_toGLReal_smul hn_pos
        (mem_primitiveReps.mp hA).1 periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j) k
    simpa only [Int.cast_natCast] using h
  exact TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pnat_mul one_pos
    (periodic_coeff_cyclicIsogenyPolynomial_j n k)
    (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k)
    ⟨n, NeZero.pos n⟩ (by simpa using hmer_n)

private theorem laurentQExpansion_n_coeff_cyclicIsogenyPolynomial_j_mem_range (n : ℕ) [NeZero n]
    (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  have hn_pos : (0 : ℤ) < n := Int.natCast_pos.mpr (NeZero.pos n)
  obtain ⟨jZ, hjZ⟩ : UpperHalfPlane.laurentQExpansion 1 j ∈
      (HahnSeries.mapRingHom (Int.castRingHom ℂ) : LaurentSeries ℤ →+* LaurentSeries ℂ).rangeS :=
    HahnSeries.mem_map_rangeS.mpr fun g ↦
      let ⟨z, hz⟩ := exists_laurentQExpansion_j_coeff_eq_intCast g
      ⟨z, hz.symm⟩
  set ΦK : (LaurentSeries (cycField n))[X] :=
    ∏ A ∈ primitiveReps (n : ℤ), (X - C (factorSeries n jZ A.val)) with hΦK_def
  have hΦ_map : ΦK.map (HahnSeries.mapRingHom (cycField n).val.toRingHom) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (X - C (UpperHalfPlane.laurentQExpansion n
          (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun A hA ↦ ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_val_factorSeries hjZ (mem_primitiveReps.mp hA).1]
  have hcoeffC : (UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m =
      (cycField n).val (((ΦK.coeff k).coeff m)) := by
    simp only [cyclicIsogenyPolynomial_def]
    rw [UpperHalfPlane.laurentQExpansion_coeff_prod_X_sub_C
        (fun A hA ↦ by
          simpa only [Int.cast_natCast] using
            TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_comp_toGLReal_smul hn_pos
              (mem_primitiveReps.mp hA).1 periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j) k,
      ← hΦ_map, Polynomial.coeff_map, HahnSeries.coeff_mapRingHom]
    rfl
  have hcyc : IsCyclotomicExtension {n} ℚ (cycField n) :=
    (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ (cycField n) := IsCyclotomicExtension.isGalois {n} ℚ (cycField n)
  have : FiniteDimensional ℚ (cycField n) := IsCyclotomicExtension.finite {n} ℚ (cycField n)
  have hfixed : ∀ σ : cycField n ≃ₐ[ℚ] cycField n, σ ((ΦK.coeff k).coeff m) =
      (ΦK.coeff k).coeff m := fun σ ↦ by
    have := congrArg (fun P : (LaurentSeries (cycField n))[X] ↦ (P.coeff k).coeff m)
      (map_aut_prod_X_sub_C_factorSeries jZ σ)
    simpa [ΦK, Polynomial.coeff_map, HahnSeries.coeff_mapRingHom] using this
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hfixed)
  have hint_q : IsIntegral ℤ q := by
    refine isIntegral_ratCast_iff (K := cycField n).mp ?_
    have hint := isIntegral_coeff_prod_factorSeries jZ (primitiveReps (n : ℤ)) k m
    rwa [← hΦK_def, ← hq] at hint
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint_q
  refine ⟨z, ?_⟩
  rw [hcoeffC, ← hq]
  simp

/-- **Every Laurent `q`-coefficient of every coefficient of `cyclicIsogenyPolynomial n j` is an
integer.** -/
theorem laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range (n : ℕ) [NeZero n]
    (k : ℕ) (m : ℤ) :
    (UpperHalfPlane.laurentQExpansion 1
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k)).coeff m ∈
      (algebraMap ℤ ℂ).range := by
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  have hmer := meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j n k
  have hexp : UpperHalfPlane.laurentQExpansion n
      (fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) =
      LaurentSeries.expand ℂ d
        (UpperHalfPlane.laurentQExpansion 1
          fun τ ↦ (cyclicIsogenyPolynomial n j τ).coeff k) := by
    simpa [mul_one, d] using UpperHalfPlane.laurentQExpansion_pnat_mul (h := 1)
      (periodic_coeff_cyclicIsogenyPolynomial_j n k) hmer d
  have hm := laurentQExpansion_n_coeff_cyclicIsogenyPolynomial_j_mem_range n k
    (((d : ℕ) : ℤ) * m)
  rwa [hexp, LaurentSeries.coeff_expand_mul (R := ℂ) d] at hm

end GaloisDescent

/-! ### The classical modular polynomial `Φ_n(X, Y) ∈ ℤ[Y][X]` -/

section ModularPolynomial

private theorem exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial (n : ℕ) [NeZero n] (k : ℕ) :
    ∃ P : ℤ[X], ∀ τ : ℍ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).coeff k :=
  exists_aeval_j_eq (mdifferentiable_coeff_cyclicIsogenyPolynomial j_mdifferentiable k)
    (fun γ τ ↦ congrArg (fun Q ↦ Q.coeff k)
      (cyclicIsogenyPolynomial_smul (n := n) j_smul_SL2Z γ τ))
    (meromorphicAt_cuspFunction_coeff_cyclicIsogenyPolynomial_j n k)
    fun m _ ↦ laurentQExpansion_coeff_cyclicIsogenyPolynomial_j_mem_range n k m

/-- **The classical modular polynomial** `Φ_n(X, Y) ∈ ℤ[Y][X]`, represented as a polynomial over
`ℤ[X]`: the unique integral bivariate polynomial whose specialization `Y ↦ j(τ)` is
`cyclicIsogenyPolynomial n j τ = ∏_{(a b; 0 d)} (X - j((a τ + b) / d))`. -/
noncomputable def modularPolynomial (n : ℕ) [NeZero n] : ℤ[X][X] :=
  ∑ k ∈ Finset.range ((primitiveReps (n : ℤ)).card + 1),
    Polynomial.monomial k (exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose

/-- Evaluating the `X ^ k`-coefficient of `modularPolynomial n` at `j(τ)` recovers the `X ^ k`
coefficient of `cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem aeval_j_coeff_modularPolynomial (n : ℕ) [NeZero n] (k : ℕ) (τ : ℍ) :
    aeval (j τ) ((modularPolynomial n).coeff k) = (cyclicIsogenyPolynomial n j τ).coeff k := by
  rw [modularPolynomial, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ (primitiveReps (n : ℤ)).card
  · rw [Finset.sum_eq_single k
      (fun i _ hik ↦ by simp [coeff_monomial, hik.symm])
      (fun hnot ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hnot)]
    simp [(exists_aeval_j_eq_coeff_cyclicIsogenyPolynomial n k).choose_spec τ]
  · rw [Finset.sum_eq_zero fun i hi ↦ by
        have hi' := Finset.mem_range.mp hi
        have hik : i ≠ k := by omega
        simp [coeff_monomial, hik],
      map_zero, coeff_eq_zero_of_natDegree_lt]
    rw [natDegree_cyclicIsogenyPolynomial]
    omega

/-- Specializing the coefficient ring of `modularPolynomial n` along `Y ↦ j(τ)` recovers
`cyclicIsogenyPolynomial n j τ`. -/
@[simp]
theorem map_aeval_j_modularPolynomial (n : ℕ) [NeZero n] (τ : ℍ) :
    (modularPolynomial n).map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ := by
  ext k
  rw [Polynomial.coeff_map, RingHom.coe_coe]
  exact aeval_j_coeff_modularPolynomial n k τ

/-- **Uniqueness of the modular polynomial**: `modularPolynomial n` is the unique polynomial in
`ℤ[X][X]` whose specialization at `j(τ)` equals `cyclicIsogenyPolynomial n j τ` for all `τ ∈ ℍ`. -/
theorem eq_modularPolynomial_of_map_aeval_j_eq {n : ℕ} [NeZero n] {P : ℤ[X][X]}
    (h : ∀ τ : ℍ, P.map (aeval (R := ℤ) (j τ)) = cyclicIsogenyPolynomial n j τ) :
    P = modularPolynomial n := by
  ext k : 2
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  have hτ := congrArg (fun Q : ℂ[X] ↦ Q.coeff k) (h τ)
  rw [Polynomial.coeff_map, RingHom.coe_coe] at hτ
  exact hτ.trans (aeval_j_coeff_modularPolynomial n k τ).symm

private theorem coeff_modularPolynomial_eq_zero_of_lt {n : ℕ} [NeZero n] {k : ℕ}
    (hk : (primitiveReps (n : ℤ)).card < k) :
    (modularPolynomial n).coeff k = 0 := by
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  rw [aeval_j_coeff_modularPolynomial, map_zero, coeff_eq_zero_of_natDegree_lt]
  rwa [natDegree_cyclicIsogenyPolynomial]

private theorem coeff_modularPolynomial_card (n : ℕ) [NeZero n] :
    (modularPolynomial n).coeff (primitiveReps (n : ℤ)).card = 1 := by
  refine aeval_j_injective (Int.cast_injective (α := ℂ)) (funext fun τ ↦ ?_)
  dsimp only
  rw [aeval_j_coeff_modularPolynomial, map_one, ← natDegree_cyclicIsogenyPolynomial (n := n) j τ]
  exact (monic_cyclicIsogenyPolynomial j τ).leadingCoeff

/-- The degree of `modularPolynomial n` in `X` is the number of cyclic `n`-isogenies. -/
@[simp]
theorem natDegree_modularPolynomial (n : ℕ) [NeZero n] :
    (modularPolynomial n).natDegree = (primitiveReps (n : ℤ)).card :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ hk ↦ coeff_modularPolynomial_eq_zero_of_lt hk)
    (by rw [coeff_modularPolynomial_card]; exact one_ne_zero)

/-- `modularPolynomial n` is monic in `X`. -/
theorem monic_modularPolynomial (n : ℕ) [NeZero n] : (modularPolynomial n).Monic := by
  rw [Monic, leadingCoeff, natDegree_modularPolynomial, coeff_modularPolynomial_card]

/-- For every primitive integral matrix `A` of determinant `n`, `j(A • τ)` is a root of
`Φ_n(X, j(τ))`. -/
theorem isRoot_map_aeval_j_modularPolynomial {n : ℕ} [NeZero n] {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.val) (τ : ℍ) :
    ((modularPolynomial n).map (aeval (R := ℤ) (j τ))).IsRoot
      (j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  rw [map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hA τ

/-- The classical modular identity `Φ_n(j(n τ), j(τ)) = 0`. -/
theorem isRoot_map_aeval_j_modularPolynomial_scaleGL_smul (n : ℕ) [NeZero n] (τ : ℍ) :
    ((modularPolynomial n).map (aeval (R := ℤ) (j τ))).IsRoot (j (scaleGL n • τ)) := by
  rw [map_aeval_j_modularPolynomial]
  exact isRoot_cyclicIsogenyPolynomial_scaleGL_smul j_smul_SL2Z τ

end ModularPolynomial

/-! ### The diagonal specialization `Φ_n(X, X)` and its leading coefficient -/

section Diagonal

/-- **The diagonal modular polynomial** `Φ_n(X, X) ∈ ℤ[X]`, obtained by specializing both variables
of `modularPolynomial n` to `X`. -/
noncomputable def modularPolynomialDiag (n : ℕ) [NeZero n] : ℤ[X] :=
  (modularPolynomial n).eval X

/-- The defining equation of `modularPolynomialDiag`. -/
theorem modularPolynomialDiag_def (n : ℕ) [NeZero n] :
    modularPolynomialDiag n = (modularPolynomial n).eval X := (rfl)

/-- Evaluating `modularPolynomialDiag n` at `x ∈ R` evaluates `Φ_n(x, x)`. -/
theorem aeval_modularPolynomialDiag (n : ℕ) [NeZero n] {R : Type*} [CommRing R] (x : R) :
    aeval x (modularPolynomialDiag n) =
      ((modularPolynomial n).map (aeval (R := ℤ) x)).eval x := by
  rw [modularPolynomialDiag_def, eval_eq_sum_range, map_sum, eval_map,
    eval₂_eq_sum_range' (aeval (R := ℤ) x)
      (Nat.lt_succ_self (modularPolynomial n).natDegree) x]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp

/-- Evaluating `modularPolynomialDiag n` at `j(τ)` gives
`(cyclicIsogenyPolynomial n j τ).eval (j τ)`. -/
@[simp]
theorem aeval_j_modularPolynomialDiag (n : ℕ) [NeZero n] (τ : ℍ) :
    aeval (j τ) (modularPolynomialDiag n) = (cyclicIsogenyPolynomial n j τ).eval (j τ) := by
  rw [aeval_modularPolynomialDiag, map_aeval_j_modularPolynomial]

/-- **Kronecker's leading-coefficient theorem for `Φ_n(X, X)`.** When `n` is not a square, the
leading coefficient of `modularPolynomialDiag n` is a unit in `ℤ` (that is, `±1`). -/
theorem isUnit_leadingCoeff_modularPolynomialDiag {n : ℕ} [NeZero n] (hn : ¬ IsSquare n) :
    IsUnit (modularPolynomialDiag n).leadingCoeff := by
  have hu : IsUnit (((modularPolynomialDiag n).map
      (algebraMap ℤ (integralClosure ℤ ℂ))).leadingCoeff) :=
    isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial hn fun τ ↦ by
      rw [← aeval_map_algebraMap ℂ (j τ), Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
        aeval_map_algebraMap, aeval_j_modularPolynomialDiag]
  rwa [leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective _ _),
    isUnit_map_iff (algebraMap ℤ (integralClosure ℤ ℂ))] at hu

/-- When `n` is not a square, `modularPolynomialDiag n` is nonzero. -/
theorem modularPolynomialDiag_ne_zero {n : ℕ} [NeZero n] (hn : ¬ IsSquare n) :
    modularPolynomialDiag n ≠ 0 :=
  leadingCoeff_ne_zero.mp (isUnit_leadingCoeff_modularPolynomialDiag hn).ne_zero

end Diagonal

end TauCeti.ModularForm
