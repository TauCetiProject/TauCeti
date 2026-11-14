/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Complexification
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Complexification of exterior sesquilinear Gram forms

Let `V` be a real module and `B : LinearMap.BilinForm ℝ V` a real bilinear form on `V`, with
sesquilinear complexification `B.sesqComplexification` on `ℂ ⊗[ℝ] V`. Complexifying first and
taking exterior Gram forms commutes with taking real exterior Gram forms first and complexifying
sesquilinearly:

* on each exterior power, `TauCeti.exteriorPower.equivBaseChange ℂ n` intertwines
  `B.sesqComplexification.sesqExteriorPower n` on `⋀[ℂ]^n (ℂ ⊗[ℝ] V)` with
  `LinearMap.BilinForm.sesqComplexification (B.sesqExteriorPower n)` on `ℂ ⊗[ℝ] ⋀[ℝ]^n V`;
* on the exterior algebra, `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` intertwines
  `B.sesqComplexification.sesqExteriorAlgebra` on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` with
  `LinearMap.BilinForm.sesqComplexification B.sesqExteriorAlgebra` on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`;
* on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`, the complexified Gram form restricts in homogeneous degree `n`
  along `(⋀[ℝ]^n V).subtype.baseChange ℂ` to
  `LinearMap.BilinForm.sesqComplexification (B.sesqExteriorPower n)`, and makes distinct
  complexified exterior powers `(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ` orthogonal;
* when `V` has a finite ordered basis `b`, the Hermitian form making
  `(b.baseChange ℂ).ExteriorAlgebra` orthonormal is
  `(LinearMap.BilinForm.sesqComplexification (Matrix.toLinearMap₂ b b 1)).sesqExteriorAlgebra`.

No finiteness, flatness, or basis assumption is needed for the comparison theorems.

## Main results

* `LinearMap.BilinForm.sesqComplexification_sesqExteriorPower` and
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorPower_equivBaseChange_symm`: compatibility
  of `sesqExteriorPower` with `sesqComplexification` across `equivBaseChange ℂ n`.
* `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv`: compatibility of
  `sesqExteriorAlgebra` with `sesqComplexification` across `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`.
* `LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_subtype_baseChange` and
  `LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_eq_zero_of_mem_baseChange_of_ne`:
  degree-`n` restriction and degree orthogonality on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`.
* `Matrix.toLinearMapₛₗ₂_baseChange_complex_one` and
  `ExteriorAlgebra.toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one`: basis coordinate
  comparisons on `ℂ ⊗[ℝ] V` and `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open scoped TensorProduct
open LinearMap (BilinForm)
open Matrix

namespace LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Complexification commutes with exterior Gram forms on exterior powers** (inverse comparison
form): pulling `B.sesqComplexification.sesqExteriorPower n` back along
`(TauCeti.exteriorPower.equivBaseChange ℂ n).symm` gives the sesquilinear complexification of
`B.sesqExteriorPower n`. -/
theorem sesqComplexification_sesqExteriorPower_equivBaseChange_symm (B : BilinForm ℝ V) (n : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^n V) :
    B.sesqComplexification.sesqExteriorPower n
        ((TauCeti.exteriorPower.equivBaseChange ℂ n).symm x)
        ((TauCeti.exteriorPower.equivBaseChange ℂ n).symm y) =
      sesqComplexification (B.sesqExteriorPower n) x y := by
  let e := (TauCeti.exteriorPower.equivBaseChange (R := ℝ) ℂ (M := V) n).symm.toLinearMap
  let K := TauCeti.tmulConj (⋀[ℝ]^n V)
  have h : (((B.sesqComplexification.sesqExteriorPower n).comp e).compl₂ e ∘ₛₗ K :
        ℂ ⊗[ℝ] ⋀[ℝ]^n V →ₗ[ℂ] ℂ ⊗[ℝ] ⋀[ℝ]^n V →ₗ[ℂ] ℂ) =
      (sesqComplexification (B.sesqExteriorPower n) ∘ₛₗ K) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span ℝ n V) fun u ↦ ?_
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span ℝ n V) fun v ↦ ?_
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, K, e,
      TauCeti.tmulConj_tmul, map_one, LinearEquiv.coe_coe,
      TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul,
      LinearMap.sesqExteriorPower_ιMulti_ιMulti, sesqComplexification_tmul_tmul, one_mul]
    have hmat : (Matrix.of fun i j ↦ ((B (u i) (v j) : ℝ) : ℂ)) =
        (algebraMap ℝ ℂ).mapMatrix (Matrix.of fun i j ↦ B (u i) (v j)) := by
      ext i j
      rfl
    rw [hmat, ← RingHom.map_det]
    rfl
  simpa [K, e, TauCeti.tmulConj_tmulConj] using LinearMap.congr_fun₂ h (K x) y

/-- **Complexification commutes with exterior Gram forms on exterior powers**: under
`TauCeti.exteriorPower.equivBaseChange ℂ n`, `B.sesqComplexification.sesqExteriorPower n` agrees
with `(B.sesqExteriorPower n).sesqComplexification`. -/
@[simp]
theorem sesqComplexification_sesqExteriorPower (B : BilinForm ℝ V) (n : ℕ)
    (x y : ⋀[ℂ]^n (ℂ ⊗[ℝ] V)) :
    B.sesqComplexification.sesqExteriorPower n x y =
      sesqComplexification (B.sesqExteriorPower n)
        (TauCeti.exteriorPower.equivBaseChange ℂ n x)
        (TauCeti.exteriorPower.equivBaseChange ℂ n y) := by
  rw [← sesqComplexification_sesqExteriorPower_equivBaseChange_symm,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- **Complexified exterior Gram form in homogeneous degree `n`**: on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`,
restricting `B.sesqExteriorAlgebra.sesqComplexification` along `(⋀[ℝ]^n V).subtype.baseChange ℂ`
gives `(B.sesqExteriorPower n).sesqComplexification`. -/
@[simp]
theorem sesqExteriorAlgebra_sesqComplexification_subtype_baseChange (B : BilinForm ℝ V) (n : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^n V) :
    sesqComplexification B.sesqExteriorAlgebra
        ((⋀[ℝ]^n V).subtype.baseChange ℂ x) ((⋀[ℝ]^n V).subtype.baseChange ℂ y) =
      sesqComplexification (B.sesqExteriorPower n) x y :=
  sesqComplexification_baseChange_baseChange
    (B := B.sesqExteriorPower n) (B' := B.sesqExteriorAlgebra)
    (B.sesqExteriorAlgebra_coe_coe) x y

/-- **Distinct complexified exterior powers are orthogonal**: for `p ≠ q`, the subspaces
`(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ` of `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` are
orthogonal with respect to `B.sesqExteriorAlgebra.sesqComplexification`. -/
theorem sesqExteriorAlgebra_sesqComplexification_eq_zero_of_mem_baseChange_of_ne
    (B : BilinForm ℝ V) {p q : ℕ} (hpq : p ≠ q) {x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V}
    (hx : x ∈ (⋀[ℝ]^p V).baseChange ℂ) (hy : y ∈ (⋀[ℝ]^q V).baseChange ℂ) :
    sesqComplexification B.sesqExteriorAlgebra x y = 0 := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  induction x' using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, LinearMap.add_apply, hu₁, hu₂, add_zero]
  | tmul z u =>
    induction y' using TensorProduct.inductionOn with
    | add v₁ v₂ hv₁ hv₂ => simp only [map_add, hv₁, hv₂, add_zero]
    | tmul w v =>
      simp [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq u.2 v.2]

/-- **Complexification commutes with exterior Gram forms on the exterior algebra**: under
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, `B.sesqComplexification.sesqExteriorAlgebra` on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` agrees with `B.sesqExteriorAlgebra.sesqComplexification` on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`. -/
@[simp]
theorem sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv (B : BilinForm ℝ V)
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    B.sesqComplexification.sesqExteriorAlgebra
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x) (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      sesqComplexification B.sesqExteriorAlgebra x y := by
  let e := (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).toLinearMap
  let K := TauCeti.tmulConj (ExteriorAlgebra ℝ V)
  have hhom {k : ℕ} (u : ⋀[ℝ]^k V) :
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ ((1 : ℂ) ⊗ₜ[ℝ] (u : ExteriorAlgebra ℝ V)) =
        (((TauCeti.exteriorPower.equivBaseChange ℂ k).symm ((1 : ℂ) ⊗ₜ[ℝ] u) :
          ⋀[ℂ]^k (ℂ ⊗[ℝ] V)) : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) := by
    apply (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm.injective
    rw [AlgEquiv.symm_apply_apply, ← TauCeti.exteriorPower.subtype_baseChange_equivBaseChange,
      LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul, Submodule.coe_subtype]
  have h : (((B.sesqComplexification.sesqExteriorAlgebra.comp e).compl₂ e) ∘ₛₗ K :
        ℂ ⊗[ℝ] ExteriorAlgebra ℝ V →ₗ[ℂ] ℂ ⊗[ℝ] ExteriorAlgebra ℝ V →ₗ[ℂ] ℂ) =
      sesqComplexification B.sesqExteriorAlgebra ∘ₛₗ K := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext fun s ↦ ?_
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext fun t ↦ ?_
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, K, e,
      TauCeti.tmulConj_tmul, map_one, AlgEquiv.toLinearMap_apply]
    induction s using DirectSum.Decomposition.inductionOn fun p ↦ ⋀[ℝ]^p V with
    | zero => simp
    | add s₁ s₂ hs₁ hs₂ =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hs₁, hs₂]
    | @homogeneous p s =>
      induction t using DirectSum.Decomposition.inductionOn fun q ↦ ⋀[ℝ]^q V with
      | zero => simp
      | add t₁ t₂ ht₁ ht₂ => simp only [TensorProduct.tmul_add, map_add, ht₁, ht₂]
      | @homogeneous q t =>
        rw [hhom, hhom]
        rcases eq_or_ne p q with rfl | hpq
        · rw [LinearMap.sesqExteriorAlgebra_coe_coe,
            sesqComplexification_sesqExteriorPower_equivBaseChange_symm,
            ← sesqExteriorAlgebra_sesqComplexification_subtype_baseChange,
            LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Submodule.coe_subtype]
        · rw [B.sesqComplexification.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq
              (Subtype.prop _) (Subtype.prop _),
            sesqComplexification_tmul_tmul,
            B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq s.2 t.2,
            Complex.ofReal_zero, mul_zero]
  simpa [K, e, TauCeti.tmulConj_tmulConj] using LinearMap.congr_fun₂ h (K x) y

/-- Inverse form of `sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv`. -/
@[simp]
theorem sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv_symm (B : BilinForm ℝ V)
    (x y : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    sesqComplexification B.sesqExteriorAlgebra
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm x)
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm y) =
      B.sesqComplexification.sesqExteriorAlgebra x y := by
  rw [← sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end LinearMap.BilinForm

namespace Matrix

/-- For a finite basis `b` of a real module `V`, the Hermitian form on `ℂ ⊗[ℝ] V` making
`b.baseChange ℂ` orthonormal is the sesquilinear complexification of the real bilinear form making
`b` orthonormal. -/
theorem toLinearMapₛₗ₂_baseChange_complex_one {V I : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.baseChange ℂ) (b.baseChange ℂ) (1 : Matrix I I ℂ) =
      LinearMap.BilinForm.sesqComplexification (toLinearMap₂ b b (1 : Matrix I I ℝ)) := by
  refine LinearMap.ext_basis (b.baseChange ℂ) (b.baseChange ℂ) fun i j ↦ ?_
  rw [toLinearMapₛₗ₂_apply_basis, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.sesqComplexification_tmul_tmul, toLinearMap₂_apply_basis, map_one, one_mul,
    one_mul]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Matrix

namespace ExteriorAlgebra

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [LinearOrder I]
  (b : Module.Basis I ℝ V)

/-- For a finite ordered basis `b` of a real module `V`, the Hermitian form on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` making `(b.baseChange ℂ).ExteriorAlgebra` orthonormal is the
exterior Gram form of `LinearMap.BilinForm.sesqComplexification (toLinearMap₂ b b 1)`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.baseChange ℂ).ExteriorAlgebra
        (b.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ) =
      (LinearMap.BilinForm.sesqComplexification
        (toLinearMap₂ b b (1 : Matrix I I ℝ))).sesqExteriorAlgebra := by
  rw [toLinearMapₛₗ₂_exteriorAlgebra_one, toLinearMapₛₗ₂_baseChange_complex_one]

/-- Pulling the Hermitian wedge-basis form of `b.baseChange ℂ` back along
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` gives the sesquilinear complexification of the real
exterior Gram form `(toLinearMap₂ b b 1).sesqExteriorAlgebra`. -/
theorem toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_baseChangeEquiv
    (x y : ℂ ⊗[ℝ] _root_.ExteriorAlgebra ℝ V) :
    toLinearMapₛₗ₂ (starRingEnd ℂ) (b.baseChange ℂ).ExteriorAlgebra
        (b.baseChange ℂ).ExteriorAlgebra (1 : Matrix (Finset I) (Finset I) ℂ)
        (_root_.ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
        (_root_.ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      LinearMap.BilinForm.sesqComplexification
        (toLinearMap₂ b b (1 : Matrix I I ℝ)).sesqExteriorAlgebra x y := by
  rw [toLinearMapₛₗ₂_baseChange_complex_exteriorAlgebra_one,
    LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv]

end ExteriorAlgebra
