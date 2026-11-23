/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.Coalgebra.MulOpposite

/-!
# Basis-free Frobenius dual-basis reconstruction from integrals and cointegrals

Over an arbitrary commutative semiring, normalized integrals and cointegrals on a Hopf algebra `H`
satisfy explicit basis-free Frobenius dual-basis reconstruction formulas (and their partner
formulas) without assuming finite-dimensionality, the Orzech property, or a base field.

## Main results

* `TauCeti.IsRightCointegral.sum_apply_mul_smul_antipode`:
  `∑ φ (x * t₁) • S(t₂) = x` for a right cointegral `φ` and normalized left integral `t`.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_antipode`:
  `∑ φ (t₂ * x) • S(t₁) = x` for a left cointegral `φ` and normalized right integral `t`.
* `TauCeti.IsRightCointegral.sum_apply_mul_smul_eq_antipode`:
  `∑ φ (t₁ * x) • t₂ = S(x)` for a right cointegral `φ` and normalized right integral `t`.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_eq_antipode`:
  `∑ φ (x * t₂) • t₁ = S(x)` for a left cointegral `φ` and normalized left integral `t`.
* `TauCeti.IsRightCointegral.sum_apply_mul_smul_inverseAntipode`:
  `∑ φ (t₁ * x) • S⁻¹(t₂) = x` when `S` is bijective.
* `TauCeti.IsLeftCointegral.sum_apply_mul_smul_inverseAntipode`:
  `∑ φ (x * t₂) • S⁻¹(t₁) = x` when `S` is bijective.
* `TauCeti.IsRightCointegral.sum_apply_antipode_mul_smul`,
  `TauCeti.IsLeftCointegral.sum_apply_mul_antipode_smul`,
  `TauCeti.IsRightCointegral.sum_apply_mul_inverseAntipode_smul`,
  `TauCeti.IsLeftCointegral.sum_apply_inverseAntipode_mul_smul`: dual-basis partner formulas over
  an arbitrary commutative semiring.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, AMS, 1993, Chapter 2.
* D. Fischman, S. Montgomery, and H.-J. Schneider, *Frobenius extensions of subalgebras of Hopf
  algebras*, Trans. Amer. Math. Soc. 349 (1997), 4857–4895, Lemma 1.5.
-/

public section

open scoped Coalgebra TensorProduct

namespace TauCeti

universe u v

section Semiring

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- Reconstruction from a right cointegral and a normalized left integral:
`∑ φ (x * t₁) • S(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.left i) • HopfAlgebra.antipode R (r.right i) = x := by
  classical
  have hxt (y : H) : φ (y * t) = Coalgebra.counit (R := R) y := by
    simp [(mem_leftIntegral_iff.mp ht) y, htφ]
  rw [← (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [hxt] using Coalgebra.sum_counit_smul (ℛ R x)

/-- Reconstruction from a left cointegral and a normalized right integral:
`∑ φ (t₂ * x) • S(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.right i * x) • HopfAlgebra.antipode R (r.left i) = x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [← (LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    (ℛ R x) r]
  simpa only [htx] using Coalgebra.sum_smul_counit (ℛ R x)

/-- Applying strong right invariance to a normalized right integral yields the antipode:
`∑ φ (t₁ * x) • t₂ = S(x)`. -/
theorem IsRightCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • r.right i = HopfAlgebra.antipode R x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [(LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [htx, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_counit_smul (ℛ R x))

/-- Applying strong left invariance to a normalized left integral yields the antipode:
`∑ φ (x * t₂) • t₁ = S(x)`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.right i) • r.left i = HopfAlgebra.antipode R x := by
  classical
  have hxt (y : H) : φ (y * t) = Coalgebra.counit (R := R) y := by
    simp [(mem_leftIntegral_iff.mp ht) y, htφ]
  rw [(LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).strong_invariance
    r (ℛ R x)]
  simpa only [hxt, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_smul_counit (ℛ R x))

/-- Reconstruction from a right cointegral and a normalized right integral using the inverse
antipode: `∑ φ (t₁ * x) • S⁻¹(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_inverseAntipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • TauCeti.HopfAlgebra.inverseAntipode hS (r.right i) = x := by
  have h := congrArg (TauCeti.HopfAlgebra.inverseAntipode hS)
    (hφ.sum_apply_mul_smul_eq_antipode ht htφ r x)
  simpa only [map_sum, map_smul, TauCeti.HopfAlgebra.inverseAntipode_antipode] using h

/-- Reconstruction from a left cointegral and a normalized left integral using the inverse
antipode: `∑ φ (x * t₂) • S⁻¹(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_inverseAntipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.right i) • TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) = x := by
  have h := congrArg (TauCeti.HopfAlgebra.inverseAntipode hS)
    (hφ.sum_apply_mul_smul_eq_antipode ht htφ r x)
  simpa only [map_sum, map_smul, TauCeti.HopfAlgebra.inverseAntipode_antipode] using h

/-- Auxiliary linear map used to establish `leftIntegral_tensor_antipode`. -/
private noncomputable def leftIntegralPhi (R H : Type*) [CommSemiring R] [Semiring H]
    [HopfAlgebra R H] (t : H) : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] H :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun ab c ↦ ((LinearMap.mulRight R c ∘ₗ HopfAlgebra.antipode R).lTensor H)
      (ab * Coalgebra.comul (R := R) t))
    (fun ab₁ ab₂ c ↦ by simp [add_mul])
    (fun r ab c ↦ by simp)
    (fun ab c₁ c₂ ↦ by
      have hadd : LinearMap.mulRight R (c₁ + c₂) =
          LinearMap.mulRight R c₁ + LinearMap.mulRight R c₂ :=
        LinearMap.ext fun y ↦ mul_add y c₁ c₂
      simp [hadd, LinearMap.add_comp, LinearMap.lTensor_add])
    (fun r ab c ↦ by
      have hsmul : LinearMap.mulRight R (r • c) = r • LinearMap.mulRight R c :=
        LinearMap.ext fun y ↦ mul_smul_comm r y c
      simp [hsmul, LinearMap.smul_comp, LinearMap.lTensor_smul])

private theorem leftIntegralPhi_rTensor_comul {t : H} (ht : t ∈ leftIntegral R H)
    (w : H ⊗[R] H) :
    leftIntegralPhi R H t ((Coalgebra.comul (R := R)).rTensor H w) =
      ((LinearMap.mulRight R (TensorProduct.lid R H ((Coalgebra.counit (R := R)).rTensor H w)) ∘ₗ
        HopfAlgebra.antipode R).lTensor H) (Coalgebra.comul t) := by
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    have hadd (a b : H) : LinearMap.mulRight R (a + b) =
        LinearMap.mulRight R a + LinearMap.mulRight R b :=
      LinearMap.ext fun y ↦ mul_add y a b
    simp only [map_add, hu, hv, hadd, LinearMap.add_comp, LinearMap.lTensor_add,
      LinearMap.add_apply]
  | tmul d c =>
    have hdt : Coalgebra.comul (R := R) d * Coalgebra.comul (R := R) t =
        Coalgebra.counit (R := R) d • Coalgebra.comul (R := R) t := by
      rw [← Bialgebra.comul_mul, (mem_leftIntegral_iff.mp ht) d, map_smul]
    have hsmul (r : R) (y : H) :
        LinearMap.mulRight R (r • y) = r • LinearMap.mulRight R y :=
      LinearMap.ext fun z ↦ mul_smul_comm r z y
    simp [leftIntegralPhi, hdt, hsmul, LinearMap.smul_comp, LinearMap.lTensor_smul]

private theorem leftIntegralPhi_assoc_symm_tmul (t a : H) (z : H ⊗[R] H) :
    leftIntegralPhi R H t ((TensorProduct.assoc R H H H).symm (a ⊗ₜ[R] z)) =
      (LinearMap.mulLeft R a).rTensor H
        (((LinearMap.mulRight R (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H z)) ∘ₗ
          HopfAlgebra.antipode R).lTensor H) (Coalgebra.comul (R := R) t)) := by
  induction z using TensorProduct.inductionOn with
  | add u v hu hv =>
    have hadd (y₁ y₂ : H) : LinearMap.mulRight R (y₁ + y₂) =
        LinearMap.mulRight R y₁ + LinearMap.mulRight R y₂ :=
      LinearMap.ext fun y ↦ mul_add y y₁ y₂
    simp only [TensorProduct.tmul_add, map_add, hu, hv, hadd, LinearMap.add_comp,
      LinearMap.lTensor_add, LinearMap.add_apply]
  | tmul b c =>
    simp only [TensorProduct.assoc_symm_tmul, leftIntegralPhi, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
    induction Coalgebra.comul (R := R) t using TensorProduct.inductionOn with
    | add u v hu hv => simp only [mul_add, map_add, hu, hv]
    | tmul u v => simp [HopfAlgebra.antipode_mul_antidistrib, mul_assoc]

private theorem leftIntegralPhi_assoc_symm_lTensor_comul (t : H) (w : H ⊗[R] H) :
    leftIntegralPhi R H t ((TensorProduct.assoc R H H H).symm
      ((Coalgebra.comul (R := R)).lTensor H w)) =
      (LinearMap.mulLeft R (TensorProduct.rid R H
        ((Coalgebra.counit (R := R)).lTensor H w))).rTensor H
          ((HopfAlgebra.antipode R).lTensor H (Coalgebra.comul (R := R) t)) := by
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    have hadd (y₁ y₂ : H) : LinearMap.mulLeft R (y₁ + y₂) =
        LinearMap.mulLeft R y₁ + LinearMap.mulLeft R y₂ :=
      LinearMap.ext fun y ↦ add_mul y₁ y₂ y
    simp only [map_add, hu, hv, hadd, LinearMap.rTensor_add, LinearMap.add_apply]
  | tmul a d =>
    have hsmul (r : R) (y : H) :
        LinearMap.mulLeft R (r • y) = r • LinearMap.mulLeft R y :=
      LinearMap.ext fun z ↦ smul_mul_assoc r y z
    have hmulR (r : R) :
        LinearMap.mulRight R (algebraMap R H r) ∘ₗ HopfAlgebra.antipode R =
          r • HopfAlgebra.antipode R :=
      LinearMap.ext fun y ↦ by simp [Algebra.algebraMap_eq_smul_one]
    simp [leftIntegralPhi_assoc_symm_tmul, hmulR, hsmul, LinearMap.lTensor_smul,
      LinearMap.rTensor_smul]

/-- For a left integral `t`, multiplying the first coproduct leg on the left by `x` after
applying `S` to the second leg equals multiplying `S(t₂)` on the right by `x`. -/
private theorem leftIntegral_tensor_antipode {t : H} (ht : t ∈ leftIntegral R H) (x : H) :
    (LinearMap.mulLeft R x).rTensor H ((HopfAlgebra.antipode R).lTensor H (Coalgebra.comul t)) =
      ((LinearMap.mulRight R x ∘ₗ HopfAlgebra.antipode R).lTensor H) (Coalgebra.comul t) := by
  have hco : (Coalgebra.comul (R := R)).rTensor H (Coalgebra.comul x) =
      (TensorProduct.assoc R H H H).symm ((Coalgebra.comul (R := R)).lTensor H
        (Coalgebra.comul x)) := by
    apply (TensorProduct.assoc R H H H).injective
    simp [Coalgebra.coassoc_apply x]
  have heq := congrArg (leftIntegralPhi R H t) hco
  rw [leftIntegralPhi_rTensor_comul ht, leftIntegralPhi_assoc_symm_lTensor_comul,
    Coalgebra.rTensor_counit_comul, Coalgebra.lTensor_counit_comul] at heq
  simpa using heq.symm

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_antipode`: for a right cointegral
`φ` and a left integral `t` with `φ t = 1`, `∑ φ (S(t₂) * x) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_antipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * x) • r.left i = x := by
  have hpair (y : H) :
      ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * y) • r.left i =
        φ (HopfAlgebra.antipode R t) • y := by
    have hL :
        TensorProduct.rid R H (φ.lTensor H ((LinearMap.mulLeft R y).rTensor H
          ((HopfAlgebra.antipode R).lTensor H (Coalgebra.comul (R := R) t)))) =
          φ (HopfAlgebra.antipode R t) • y := by
      have hcomp := (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).comp_antipode
      have hrid (z : H ⊗[R] H) :
          TensorProduct.rid R H (φ.lTensor H ((LinearMap.mulLeft R y).rTensor H z)) =
            y * TensorProduct.rid R H (φ.lTensor H z) := by
        induction z using TensorProduct.inductionOn with
        | add u v hu hv => simp [map_add, mul_add, hu, hv]
        | tmul a b => simp
      rw [hrid, ← LinearMap.lTensor_comp_apply, (LinearMap.isLeftInvariantIntegral_iff.mp hcomp) t]
      simp [Algebra.smul_def, Algebra.commutes]
    have hR :
        TensorProduct.rid R H (φ.lTensor H
          (((LinearMap.mulRight R y ∘ₗ HopfAlgebra.antipode R).lTensor H)
            (Coalgebra.comul (R := R) t))) =
          ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * y) • r.left i := by
      rw [← r.eq]
      simp [map_sum]
    rw [← hR, ← leftIntegral_tensor_antipode ht y, hL]
  have hSt : φ (HopfAlgebra.antipode R t) = 1 := by
    have ht_eq := hpair t
    have hLHS : ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * t) • r.left i =
        φ t • t := by
      calc ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * t) • r.left i
          = ∑ i ∈ r.index, φ (Coalgebra.counit (R := R) (r.right i) • t) • r.left i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [(mem_leftIntegral_iff.mp ht) _, HopfAlgebra.counit_antipode]
        _ = φ t • ∑ i ∈ r.index, Coalgebra.counit (R := R) (r.right i) • r.left i := by
            simp [smul_smul, mul_comm, Finset.smul_sum]
        _ = φ t • t := by rw [Coalgebra.sum_smul_counit r]
    have hφ_eq := congrArg φ (hLHS.symm.trans ht_eq)
    simpa [map_smul, smul_eq_mul, htφ] using hφ_eq.symm
  simpa [hSt] using hpair x

section Symmetry

@[instance_reducible]
private noncomputable def mulOppositeBialgebra (R A : Type*) [CommSemiring R] [Semiring A]
    [Bialgebra R A] : Bialgebra R Aᵐᵒᵖ :=
  Bialgebra.mk' R Aᵐᵒᵖ
    (by simp [MulOpposite.counit_def])
    (fun {a b} ↦ by
      induction a using MulOpposite.rec' with | h a =>
      induction b using MulOpposite.rec' with | h b =>
      simp [MulOpposite.counit_def, mul_comm])
    (by simp [MulOpposite.comul_def, Algebra.TensorProduct.one_def])
    (fun {a b} ↦ by
      induction a using MulOpposite.rec' with | h a =>
      induction b using MulOpposite.rec' with | h b =>
      have hmul (u v : A ⊗[R] A) :
          TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
              (MulOpposite.opLinearEquiv R).toLinearMap (u * v) =
            TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
                (MulOpposite.opLinearEquiv R).toLinearMap v *
              TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
                (MulOpposite.opLinearEquiv R).toLinearMap u := by
        induction u using TensorProduct.inductionOn with
        | add u₁ u₂ h₁ h₂ => simp [add_mul, mul_add, h₁, h₂]
        | tmul u₁ u₂ =>
          induction v using TensorProduct.inductionOn with
          | add v₁ v₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]
          | tmul v₁ v₂ => simp
      change TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap (Coalgebra.comul (R := R) (b * a)) =
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
            (MulOpposite.opLinearEquiv R).toLinearMap (Coalgebra.comul (R := R) a) *
          TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
            (MulOpposite.opLinearEquiv R).toLinearMap (Coalgebra.comul (R := R) b)
      rw [Bialgebra.comul_mul, hmul])

private structure Coop (A : Type v) : Type v where
  mk :: val : A

private def coopEquiv (A : Type v) : Coop A ≃ A where
  toFun := Coop.val
  invFun := Coop.mk
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible]
private def coopSemiring (A : Type v) [Semiring A] : Semiring (Coop A) :=
  Equiv.semiring (coopEquiv A)

@[instance_reducible]
private def coopAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] :
    @Algebra R (Coop A) _ (coopSemiring A) :=
  Equiv.algebra R (coopEquiv A)

private def coopLinearEquiv (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] :
    letI := coopSemiring A
    letI := coopAlgebra R A
    Coop A ≃ₗ[R] A :=
  letI := coopSemiring A
  letI := coopAlgebra R A
  { toFun := Coop.val
    invFun := Coop.mk
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

private def coopComul (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A] :
    letI := coopSemiring A
    letI := coopAlgebra R A
    Coop A →ₗ[R] Coop A ⊗[R] Coop A :=
  letI := coopSemiring A
  letI := coopAlgebra R A
  let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
  TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
    (TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul ∘ₗ e.toLinearMap

private def coopTau (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] :
    A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] A) :=
  (TensorProduct.comm R A A).toLinearMap.lTensor A ∘ₗ
    (TensorProduct.comm R (A ⊗[R] A) A).toLinearMap ∘ₗ
    (TensorProduct.assoc R A A A).symm.toLinearMap

private theorem coopTau_assoc_rTensor (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [Bialgebra R A] :
    coopTau R A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        (Coalgebra.comul (R := R) (A := A)).rTensor A =
      ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).lTensor A ∘ₗ
        (TensorProduct.comm R A A).toLinearMap := by
  refine TensorProduct.ext' fun a₁ a₂ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, TensorProduct.comm_tmul, coopTau]
  induction Coalgebra.comul (R := R) a₁ using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hu, hv]
  | tmul b₁ b₂ => simp

private theorem coopTau_lTensor (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [Bialgebra R A] :
    coopTau R A ∘ₗ (Coalgebra.comul (R := R) (A := A)).lTensor A =
      (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A ∘ₗ
        (TensorProduct.comm R A A).toLinearMap := by
  refine TensorProduct.ext' fun a₁ a₂ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, TensorProduct.comm_tmul, coopTau]
  induction Coalgebra.comul (R := R) a₂ using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hu, hv]
  | tmul b₁ b₂ => simp

private theorem coopComul_coassoc (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [Bialgebra R A] :
    letI := coopSemiring A
    letI := coopAlgebra R A
    (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
        (coopComul R A).rTensor (Coop A) ∘ₗ coopComul R A =
      (coopComul R A).lTensor (Coop A) ∘ₗ coopComul R A := by
  let _ := coopSemiring A
  let _ := coopAlgebra R A
  let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
  have he (a : A) : (coopLinearEquiv R A) (e.symm a) = a := rfl
  have hLHS :
      (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
          (coopComul R A).rTensor (Coop A) ∘ₗ
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap =
        TensorProduct.map e.symm.toLinearMap
            (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
          (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
          ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A := by
    refine TensorProduct.ext' fun a₁ a₂ ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      LinearMap.rTensor_tmul, coopComul, he]
    induction Coalgebra.comul (R := R) a₁ using TensorProduct.inductionOn with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul b₁ b₂ => simp [e]
  have hRHS :
      (coopComul R A).lTensor (Coop A) ∘ₗ
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap =
        TensorProduct.map e.symm.toLinearMap
            (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
          ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).lTensor A :=
    TensorProduct.ext' fun a₁ a₂ ↦ by simp [coopComul, he, e]
  refine LinearMap.ext fun x ↦ ?_
  have hco := congrArg (coopTau R A) (Coalgebra.coassoc_apply (R := R) (e x))
  have hL' := LinearMap.congr_fun (coopTau_assoc_rTensor R A) (Coalgebra.comul (R := R) (e x))
  have hR' := LinearMap.congr_fun (coopTau_lTensor R A) (Coalgebra.comul (R := R) (e x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL' hR'
  rw [hL', hR'] at hco
  have hmap := congrArg (TensorProduct.map e.symm.toLinearMap
    (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap)) hco.symm
  have hLHS' := LinearMap.congr_fun hLHS
    ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e x)))
  have hRHS' := LinearMap.congr_fun hRHS
    ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e x)))
  simp only [LinearMap.comp_apply] at hLHS' hRHS'
  exact hLHS'.trans (hmap.trans hRHS'.symm)

private theorem coopComul_rTensor_counit (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [Bialgebra R A] :
    letI := coopSemiring A
    letI := coopAlgebra R A
    let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
    (Coalgebra.counit ∘ₗ e.toLinearMap).rTensor (Coop A) ∘ₗ coopComul R A =
      (TensorProduct.lid R (Coop A)).symm.toLinearMap := by
  let _ := coopSemiring A
  let _ := coopAlgebra R A
  let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
  have hL :
      (Coalgebra.counit ∘ₗ e.toLinearMap).rTensor (Coop A) ∘ₗ
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
          (TensorProduct.comm R A A).toLinearMap =
        TensorProduct.map (LinearMap.id (R := R)) e.symm.toLinearMap ∘ₗ
          (TensorProduct.lid R A).symm.toLinearMap ∘ₗ (TensorProduct.rid R A).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R)).lTensor A :=
    TensorProduct.ext' fun a b ↦ by simp [TensorProduct.smul_tmul']
  refine LinearMap.ext fun x ↦ ?_
  have heq := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Coalgebra.lTensor_counit_comul] at heq
  simpa [coopComul] using heq

private theorem coopComul_lTensor_counit (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [Bialgebra R A] :
    letI := coopSemiring A
    letI := coopAlgebra R A
    let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
    (Coalgebra.counit ∘ₗ e.toLinearMap).lTensor (Coop A) ∘ₗ coopComul R A =
      (TensorProduct.rid R (Coop A)).symm.toLinearMap := by
  let _ := coopSemiring A
  let _ := coopAlgebra R A
  let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
  have hL :
      (Coalgebra.counit ∘ₗ e.toLinearMap).lTensor (Coop A) ∘ₗ
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
          (TensorProduct.comm R A A).toLinearMap =
        TensorProduct.map e.symm.toLinearMap (LinearMap.id (R := R)) ∘ₗ
          (TensorProduct.rid R A).symm.toLinearMap ∘ₗ (TensorProduct.lid R A).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R)).rTensor A :=
    TensorProduct.ext' fun a b ↦ by simp [← TensorProduct.tmul_smul]
  refine LinearMap.ext fun x ↦ ?_
  have heq := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Coalgebra.rTensor_counit_comul] at heq
  simpa [coopComul] using heq

@[instance_reducible]
private def coopCoalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A] :
    @Coalgebra R (Coop A) _ (coopSemiring A).toAddCommMonoid (coopAlgebra R A).toModule :=
  letI := coopSemiring A
  letI := coopAlgebra R A
  { comul := coopComul R A
    counit := Coalgebra.counit ∘ₗ (coopLinearEquiv R A).toLinearMap
    coassoc := coopComul_coassoc R A
    rTensor_counit_comp_comul := coopComul_rTensor_counit R A
    lTensor_counit_comp_comul := coopComul_lTensor_counit R A }

@[instance_reducible]
private def coopBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A] :
    @Bialgebra R (Coop A) _ (coopSemiring A) :=
  letI := coopSemiring A
  letI := coopAlgebra R A
  letI := coopCoalgebra R A
  let e : Coop A ≃ₗ[R] A := coopLinearEquiv R A
  Bialgebra.mk' R (Coop A)
    (Bialgebra.counit_one (R := R) (A := A))
    (fun {a b} ↦ Bialgebra.counit_mul (R := R) a.val b.val)
    (by
      have h1 : (coopLinearEquiv R A) 1 = 1 := rfl
      have hm : coopComul R A 1 = 1 := by
        simp [coopComul, h1, Algebra.TensorProduct.one_def]; rfl
      exact hm)
    (fun {a b} ↦ by
      have hmul (u v : A ⊗[R] A) :
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
              ((TensorProduct.comm R A A) (u * v)) =
            TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
                ((TensorProduct.comm R A A) u) *
              TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
                ((TensorProduct.comm R A A) v) := by
        induction u using TensorProduct.inductionOn with
        | add u₁ u₂ h₁ h₂ => simp [add_mul, map_add, h₁, h₂]
        | tmul u₁ u₂ =>
          induction v using TensorProduct.inductionOn with
          | add v₁ v₂ h₁ h₂ => simp [mul_add, map_add, h₁, h₂]
          | tmul v₁ v₂ => simp [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      have heab : e (a * b) = e a * e b := rfl
      change TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
          ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e (a * b)))) =
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
            ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e a))) *
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
            ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e b)))
      rw [heab, Bialgebra.comul_mul, hmul])

private theorem opCoop_mul_antipode_rTensor (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [HopfAlgebra R H] :
    letI := coopSemiring H
    letI := coopAlgebra R H
    letI := coopCoalgebra R H
    letI := coopBialgebra R H
    letI := mulOppositeBialgebra R (Coop H)
    let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
    let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
      (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
        HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let _ := coopSemiring H
  let _ := coopAlgebra R H
  let _ := coopCoalgebra R H
  let _ := coopBialgebra R H
  let _ := mulOppositeBialgebra R (Coop H)
  let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
  let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ ∘ₗ
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (TensorProduct.comm R H H).toLinearMap =
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
          LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).lTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ)
      (Coalgebra.comul (R := R) (MulOpposite.op x)) = _
  rw [MulOpposite.comul_def]
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ ∘ₗ
      TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
      (TensorProduct.comm R H H).toLinearMap) (Coalgebra.comul (R := R) (e x)) = _
  rw [hL']
  simp only [LinearMap.comp_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [MulOpposite.counit_def, Algebra.algebraMap_eq_smul_one]
  rfl

private theorem opCoop_mul_antipode_lTensor (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [HopfAlgebra R H] :
    letI := coopSemiring H
    letI := coopAlgebra R H
    letI := coopCoalgebra R H
    letI := coopBialgebra R H
    letI := mulOppositeBialgebra R (Coop H)
    let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
    let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
      (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
        HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let _ := coopSemiring H
  let _ := coopAlgebra R H
  let _ := coopCoalgebra R H
  let _ := coopBialgebra R H
  let _ := mulOppositeBialgebra R (Coop H)
  let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
  let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ ∘ₗ
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (TensorProduct.comm R H H).toLinearMap =
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
          LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ)
      (Coalgebra.comul (R := R) (MulOpposite.op x)) = _
  rw [MulOpposite.comul_def]
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ ∘ₗ
      TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
      (TensorProduct.comm R H H).toLinearMap) (Coalgebra.comul (R := R) (e x)) = _
  rw [hL']
  simp only [LinearMap.comp_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [MulOpposite.counit_def, Algebra.algebraMap_eq_smul_one]
  rfl

@[instance_reducible]
private noncomputable def opCoopHopfAlgebra (R : Type u) (H : Type v) [CommSemiring R] [Semiring H]
    [HopfAlgebra R H] :
    letI := coopSemiring H
    @HopfAlgebra R (Coop H)ᵐᵒᵖ _ MulOpposite.instSemiring :=
  letI := coopSemiring H
  letI := coopAlgebra R H
  letI := coopCoalgebra R H
  letI := coopBialgebra R H
  letI := mulOppositeBialgebra R (Coop H)
  let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
  { antipode := (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
    mul_antipode_rTensor_comul := opCoop_mul_antipode_rTensor R H
    mul_antipode_lTensor_comul := opCoop_mul_antipode_lTensor R H }

private theorem mulOpposite_mul_antipode_rTensor (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [HopfAlgebra R H]
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    letI := mulOppositeBialgebra R H
    let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
      (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
        (MulOpposite.opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let _ := mulOppositeBialgebra R H
  let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
      (MulOpposite.opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ ∘ₗ
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap =
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ LinearMap.mul' R H ∘ₗ
          (TauCeti.HopfAlgebra.inverseAntipode hS).lTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap :=
    TensorProduct.ext' fun a b ↦ by simp [S]
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ)
      (Coalgebra.comul (R := R) (MulOpposite.op x)) = _
  rw [MulOpposite.comul_def]
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ ∘ₗ
      TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        (MulOpposite.opLinearEquiv R).toLinearMap) (Coalgebra.comul (R := R) x) = _
  rw [hL']
  simp [MulOpposite.counit_def, Algebra.algebraMap_eq_smul_one]

private theorem mulOpposite_mul_antipode_lTensor (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [HopfAlgebra R H]
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    letI := mulOppositeBialgebra R H
    let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
      (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
        (MulOpposite.opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let _ := mulOppositeBialgebra R H
  let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
      (MulOpposite.opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ ∘ₗ
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap =
        (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ LinearMap.mul' R H ∘ₗ
          (TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap :=
    TensorProduct.ext' fun a b ↦ by simp [S]
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ)
      (Coalgebra.comul (R := R) (MulOpposite.op x)) = _
  rw [MulOpposite.comul_def]
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ ∘ₗ
      TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
        (MulOpposite.opLinearEquiv R).toLinearMap) (Coalgebra.comul (R := R) x) = _
  rw [hL']
  simp [MulOpposite.counit_def, Algebra.algebraMap_eq_smul_one]

@[instance_reducible]
private noncomputable def mulOppositeHopfAlgebra (R : Type u) (H : Type v) [CommSemiring R]
    [Semiring H] [HopfAlgebra R H]
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    HopfAlgebra R Hᵐᵒᵖ :=
  letI := mulOppositeBialgebra R H
  { antipode := (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
      TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
    mul_antipode_rTensor_comul := mulOpposite_mul_antipode_rTensor R H hS
    mul_antipode_lTensor_comul := mulOpposite_mul_antipode_lTensor R H hS }

private theorem opCoop_isRightCointegral {φ : Module.Dual R H} (hφ : IsLeftCointegral φ) :
    let _ := coopSemiring H
    let _ := coopAlgebra R H
    let _ := coopCoalgebra R H
    let f : (Coop H)ᵐᵒᵖ ≃ₗ[R] H := (MulOpposite.opLinearEquiv R).symm.trans (coopLinearEquiv R H)
    IsRightCointegral (φ ∘ₗ f.toLinearMap) := by
  let _ := coopSemiring H
  let _ := coopAlgebra R H
  let _ := coopCoalgebra R H
  let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
  let f : (Coop H)ᵐᵒᵖ ≃ₗ[R] H := (MulOpposite.opLinearEquiv R).symm.trans e
  rw [isRightCointegral_def]
  intro y
  induction y using MulOpposite.rec' with | h y =>
  have hswap :
      (TensorProduct.lid R (Coop H)ᵐᵒᵖ).toLinearMap ∘ₗ
          (φ ∘ₗ f.toLinearMap).rTensor (Coop H)ᵐᵒᵖ ∘ₗ
        TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (TensorProduct.comm R H H).toLinearMap =
        f.symm.toLinearMap ∘ₗ (TensorProduct.rid R H).toLinearMap ∘ₗ φ.lTensor H :=
    TensorProduct.ext' fun a b ↦ by simp [f]
  have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := R) (e y))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
  have h1 : MulOpposite.op (e.symm (1 : H)) = 1 := rfl
  rw [MulOpposite.comul_def]
  exact hL.trans (by rw [(isLeftCointegral_def φ).mp hφ (e y)]; simp [e, f, h1])

end Symmetry

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_antipode`: for a left cointegral
`φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S(t₁)) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_mul_antipode_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * HopfAlgebra.antipode R (r.left i)) • r.right i = x := by
  let _ := coopSemiring H
  let _ := coopAlgebra R H
  let _ := coopCoalgebra R H
  let _ := coopBialgebra R H
  let _ := mulOppositeBialgebra R (Coop H)
  let _ := opCoopHopfAlgebra R H
  let e : Coop H ≃ₗ[R] H := coopLinearEquiv R H
  let f : (Coop H)ᵐᵒᵖ ≃ₗ[R] H := (MulOpposite.opLinearEquiv R).symm.trans e
  let φ' : Module.Dual R (Coop H)ᵐᵒᵖ := φ ∘ₗ f.toLinearMap
  have hφ' : IsRightCointegral φ' := opCoop_isRightCointegral hφ
  have ht' : f.symm t ∈ leftIntegral R (Coop H)ᵐᵒᵖ := by
    rw [mem_leftIntegral_iff]
    intro h
    induction h using MulOpposite.rec' with | h h =>
    have heq := congrArg (fun u ↦ MulOpposite.op (e.symm u)) (mem_rightIntegral_iff.mp ht (e h))
    have hmul : MulOpposite.op h * f.symm t = MulOpposite.op (e.symm (t * e h)) := rfl
    have hcounit : Coalgebra.counit (R := R) h = Coalgebra.counit (R := R) (e h) := rfl
    rw [hmul, heq]
    simp [MulOpposite.counit_def, hcounit, f]
  have htφ' : φ' (f.symm t) = 1 := by simp [φ', htφ]
  let r' : Coalgebra.Repr R (f.symm t) ι :=
    { index := r.index
      left := fun i ↦ f.symm (r.right i)
      right := fun i ↦ f.symm (r.left i)
      eq := by
        have h := congrArg (TensorProduct.map f.symm.toLinearMap f.symm.toLinearMap ∘ₗ
          (TensorProduct.comm R H H).toLinearMap) r.eq
        have hswap :
            TensorProduct.map f.symm.toLinearMap f.symm.toLinearMap ∘ₗ
              (TensorProduct.comm R H H).toLinearMap =
              TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
                  (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ
                TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
                (TensorProduct.comm R H H).toLinearMap :=
          TensorProduct.ext' fun a b ↦ rfl
        have hcomul : Coalgebra.comul (R := R) (e.symm t) = coopComul R H (e.symm t) := rfl
        have he (a : H) : (coopLinearEquiv R H) (e.symm a) = a := rfl
        rw [LinearMap.comp_apply, LinearMap.congr_fun hswap _] at h
        simpa [MulOpposite.comul_def, hcomul, coopComul, he, e, map_sum, f] using h }
  have hres := congrArg f (hφ'.sum_apply_antipode_mul_smul ht' htφ' r' (f.symm x))
  have hS (a : H) : f (HopfAlgebra.antipode R (f.symm a) * f.symm x) =
      x * HopfAlgebra.antipode R a := rfl
  simpa [r', φ', map_sum, map_smul, hS] using hres

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_inverseAntipode`: for a right
cointegral `φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S⁻¹(t₂)) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_mul_inverseAntipode_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * TauCeti.HopfAlgebra.inverseAntipode hS (r.right i)) • r.left i = x := by
  let _ := mulOppositeBialgebra R H
  let _ := mulOppositeHopfAlgebra R H hS
  let φ' : Module.Dual R Hᵐᵒᵖ := φ ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  have hφ' : IsRightCointegral φ' := by
    rw [isRightCointegral_def]
    intro y
    induction y using MulOpposite.rec' with | h y =>
    have hswap :
        (TensorProduct.lid R Hᵐᵒᵖ).toLinearMap ∘ₗ φ'.rTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
            (MulOpposite.opLinearEquiv R).toLinearMap =
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
            φ.rTensor H :=
      TensorProduct.ext' fun a b ↦ by simp [φ']
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := R) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg MulOpposite.op ((isRightCointegral_def φ).mp hφ y)
    rw [MulOpposite.comul_def]
    exact hL.trans (by simpa [φ'] using heq)
  have ht' : MulOpposite.op t ∈ leftIntegral R Hᵐᵒᵖ := by
    rw [mem_leftIntegral_iff]
    intro h
    induction h using MulOpposite.rec' with | h h =>
    have heq := congrArg MulOpposite.op (mem_rightIntegral_iff.mp ht h)
    simpa [MulOpposite.counit_def, ← MulOpposite.op_mul] using heq
  have htφ' : φ' (MulOpposite.op t) = 1 := by simpa [φ'] using htφ
  let r' : Coalgebra.Repr R (MulOpposite.op t) ι :=
    { index := r.index
      left := fun i ↦ MulOpposite.op (r.left i)
      right := fun i ↦ MulOpposite.op (r.right i)
      eq := by
        have h := congrArg (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap) r.eq
        simpa [MulOpposite.comul_def, map_sum] using h }
  have hres := congrArg MulOpposite.unop
    (hφ'.sum_apply_antipode_mul_smul ht' htφ' r' (MulOpposite.op x))
  have hS' (a : H) : MulOpposite.unop (HopfAlgebra.antipode R (MulOpposite.op a)) =
      TauCeti.HopfAlgebra.inverseAntipode hS a := rfl
  simpa [r', φ', map_sum, map_smul, ← MulOpposite.op_mul, hS'] using hres

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_inverseAntipode`: for a left
cointegral `φ` and a left integral `t` with `φ t = 1`, `∑ φ (S⁻¹(t₁) * x) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_inverseAntipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) * x) • r.right i = x := by
  let _ := mulOppositeBialgebra R H
  let _ := mulOppositeHopfAlgebra R H hS
  let φ' : Module.Dual R Hᵐᵒᵖ := φ ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap
  have hφ' : IsLeftCointegral φ' := by
    rw [isLeftCointegral_def]
    intro y
    induction y using MulOpposite.rec' with | h y =>
    have hswap :
        (TensorProduct.rid R Hᵐᵒᵖ).toLinearMap ∘ₗ φ'.lTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
            (MulOpposite.opLinearEquiv R).toLinearMap =
          (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ (TensorProduct.rid R H).toLinearMap ∘ₗ
            φ.lTensor H :=
      TensorProduct.ext' fun a b ↦ by simp [φ']
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := R) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg MulOpposite.op ((isLeftCointegral_def φ).mp hφ y)
    rw [MulOpposite.comul_def]
    exact hL.trans (by simpa [φ'] using heq)
  have ht' : MulOpposite.op t ∈ rightIntegral R Hᵐᵒᵖ := by
    rw [mem_rightIntegral_iff]
    intro h
    induction h using MulOpposite.rec' with | h h =>
    have heq := congrArg MulOpposite.op (mem_leftIntegral_iff.mp ht h)
    simpa [MulOpposite.counit_def, ← MulOpposite.op_mul] using heq
  have htφ' : φ' (MulOpposite.op t) = 1 := by simpa [φ'] using htφ
  let r' : Coalgebra.Repr R (MulOpposite.op t) ι :=
    { index := r.index
      left := fun i ↦ MulOpposite.op (r.left i)
      right := fun i ↦ MulOpposite.op (r.right i)
      eq := by
        have h := congrArg (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
          (MulOpposite.opLinearEquiv R).toLinearMap) r.eq
        simpa [MulOpposite.comul_def, map_sum] using h }
  have hres := congrArg MulOpposite.unop
    (hφ'.sum_apply_mul_antipode_smul ht' htφ' r' (MulOpposite.op x))
  have hS' (a : H) : MulOpposite.unop (HopfAlgebra.antipode R (MulOpposite.op a)) =
      TauCeti.HopfAlgebra.inverseAntipode hS a := rfl
  simpa [r', φ', map_sum, map_smul, ← MulOpposite.op_mul, hS'] using hres

end Semiring

end TauCeti

