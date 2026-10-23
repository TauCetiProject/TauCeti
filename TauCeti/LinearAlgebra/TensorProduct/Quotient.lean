/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Cokernels commute with tensor products, heterobasically

Tensoring is right exact: for a linear map `f : M' → M` and a module `N`, the cokernel of
`f ⊗ 𝟙 N` is `(M ⧸ range f) ⊗ N`. Mathlib proves this over a commutative ring, as the exactness
of the tensored pair (`rTensor_exact`) and as the isomorphism `LinearMap.rTensor.equiv`. When
`M'` and `M` are modules over an `R`-algebra `A` and `f` is `A`-linear, the comparison isomorphism
is `A`-linear for the module structure of `TensorProduct.AlgebraTensorModule` on the left factor,
and this file records that heterobasic form.

For the cokernel `M ⧸ rM = QuotSMulTop r M` of multiplication by a scalar `r`, the base change
`A ⊗[R] (M ⧸ rM)` is the cokernel of multiplication by the image of `r` on `A ⊗[R] M`. When `r`
maps to `0` in `A` that cokernel is all of `A ⊗[R] M`, so the base change of the quotient map
`M → M ⧸ rM` is bijective (`QuotSMulTop.baseChange_mkQ_bijective`), and `A ⊗[R] M` is finitely
generated over `A` as soon as `M ⧸ rM` is finitely generated over `R`
(`QuotSMulTop.finite_baseChange`). For `R = ℤ` and a ring `A` of characteristic `ℓ`, this says
that `A ⊗[ℤ] M` only depends on `M ⧸ ℓM`, and is finitely generated when `M ⧸ ℓM` is finite
(`TauCeti.finite_baseChange_of_finite_quotSMulTop`), even when `M` is not finitely generated.

For a map of modules over a commutative ring, the same right exactness identifies scalar
extension of its cokernel with the cokernel of its scalar extension. This is the module form of
Stacks Project, Lemma 10.12.10, [Tag 00DF](https://stacks.math.columbia.edu/tag/00DF).

The heterobasic version is what identifies the base change of a module presented by generators
and relations over a noncommutative algebra `A` with the module presented by the base-changed
relations, for instance the rationalisation of a module over an integral group ring `ℤ_p[G]`.

## Main definitions

* `TensorProduct.AlgebraTensorModule.quotientRangeTensorEquiv`: the `A`-linear
  isomorphism `(M ⧸ range f) ⊗[R] N ≃ₗ[A] (M ⊗[R] N) ⧸ range (f ⊗ 𝟙 N)`.
* `LinearMap.cokernelBaseChangeEquiv`: the `S`-linear isomorphism
  `S ⊗[R] cokernel f ≃ₗ[S] cokernel (S ⊗[R] f)`.

## Main results

* `TensorProduct.exists_one_tmul_eq`: every element of `(R ⧸ I) ⊗ M` is `1 ⊗ x`.
* `TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq`: `1 ⊗ x` vanishes in
  `(R ⧸ (r)) ⊗ M` exactly when `x` is a multiple of `r`.
* `TensorProduct.AlgebraTensorModule.ker_rTensor_mkQ`: the kernel of the tensored
  quotient map `mkQ ⊗ 𝟙 N` is the range of `f ⊗ 𝟙 N`.
* `TensorProduct.AlgebraTensorModule.rTensor_mkQ_surjective`: the tensored quotient map
  is surjective.
* `Submodule.baseChange_eq_top_iff_subsingleton`: the extension of scalars of `p ≤ M` to `A` is
  all of `A ⊗[R] M` exactly when `A ⊗[R] (M ⧸ p) = 0`.
* `QuotSMulTop.baseChange_mkQ_bijective`: if `r` maps to `0` in `A`, the base change of
  `M → M ⧸ rM` to `A` is bijective.
* `QuotSMulTop.finite_baseChange`: if `r` maps to `0` in `A` and `M ⧸ rM` is finitely generated,
  then so is `A ⊗[R] M`.
* `TauCeti.finite_baseChange_of_finite_quotSMulTop`: in characteristic `ℓ`, `k ⊗_ℤ V` is finitely
  generated over `k` when `V ⧸ ℓV` is finite.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Every element of `(R ⧸ I) ⊗[R] M` is of the form `1 ⊗ x`. -/
theorem exists_one_tmul_eq (I : Ideal R) (y : (R ⧸ I) ⊗[R] M) : ∃ x : M, 1 ⊗ₜ x = y := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul M I y)
  exact ⟨x, by rw [← quotTensorEquivQuotSMul_symm_mk, hx, LinearEquiv.symm_apply_apply]⟩

/-- In `(R ⧸ (r)) ⊗[R] M`, the element `1 ⊗ x` vanishes exactly when `x` is a multiple of `r`. -/
@[simp]
theorem one_tmul_eq_zero_iff_exists_smul_eq (r : R) (x : M) :
    (1 : R ⧸ Ideal.span {r}) ⊗ₜ[R] x = 0 ↔ ∃ y : M, r • y = x := by
  rw [← quotTensorEquivQuotSMul_symm_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Submodule.mem_top, hy⟩⟩

end TensorProduct

namespace TensorProduct.AlgebraTensorModule

open LinearMap

section Surjective

variable {R A M N : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N]

/-- The tensored quotient map `mkQ ⊗ 𝟙 N` is surjective. -/
theorem rTensor_mkQ_surjective (p : Submodule A M) :
    Function.Surjective (AlgebraTensorModule.rTensor R N p.mkQ) := by
  rw [AlgebraTensorModule.coe_rTensor]
  exact rTensor_surjective N (Submodule.mkQ_surjective p)

end Surjective

variable {R A M M' N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  [AddCommGroup N] [Module R N]

/-- Tensoring the exact pair `M' → M → M ⧸ range f` with `N` keeps it exact: the kernel of
`mkQ ⊗ 𝟙 N` is the range of `f ⊗ 𝟙 N`, as `A`-submodules of `M ⊗[R] N`. -/
theorem ker_rTensor_mkQ (f : M' →ₗ[A] M) :
    ker (AlgebraTensorModule.rTensor R N (range f).mkQ) =
      range (AlgebraTensorModule.rTensor R N f) := by
  have hexact : Function.Exact (f.restrictScalars R) ((range f).mkQ.restrictScalars R) := by
    rw [LinearMap.exact_iff, ker_restrictScalars, Submodule.ker_mkQ, range_restrictScalars]
  have hsurj : Function.Surjective ((range f).mkQ.restrictScalars R) :=
    Submodule.mkQ_surjective (range f)
  have h := (rTensor_exact N hexact hsurj).linearMap_ker_eq
  ext x
  rw [SetLike.ext_iff] at h
  simpa only [mem_ker, mem_range, AlgebraTensorModule.coe_rTensor] using h x

/-- **Cokernels commute with tensor products.** For an `A`-linear map `f : M' → M` and an
`R`-module `N`, the base change `(M ⧸ range f) ⊗[R] N` of the cokernel of `f` is the cokernel of
`f ⊗ 𝟙 N`, as left `A`-modules. -/
noncomputable def quotientRangeTensorEquiv (f : M' →ₗ[A] M) :
    ((M ⧸ range f) ⊗[R] N) ≃ₗ[A] (M ⊗[R] N) ⧸ range (AlgebraTensorModule.rTensor R N f) :=
  ((AlgebraTensorModule.rTensor R N (range f).mkQ).quotKerEquivOfSurjective
      (rTensor_mkQ_surjective (range f))).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_rTensor_mkQ f))

@[simp]
theorem quotientRangeTensorEquiv_mk_tmul (f : M' →ₗ[A] M) (x : M) (n : N) :
    quotientRangeTensorEquiv (N := N) f (Submodule.Quotient.mk x ⊗ₜ[R] n) =
      Submodule.Quotient.mk (x ⊗ₜ[R] n) := by
  rw [quotientRangeTensorEquiv, LinearEquiv.trans_apply, ← Submodule.mkQ_apply,
    ← AlgebraTensorModule.rTensor_tmul, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk]

@[simp]
theorem quotientRangeTensorEquiv_symm_mk_tmul (f : M' →ₗ[A] M) (x : M) (n : N) :
    (quotientRangeTensorEquiv (N := N) f).symm (Submodule.Quotient.mk (x ⊗ₜ[R] n)) =
      Submodule.Quotient.mk x ⊗ₜ[R] n :=
  (LinearEquiv.symm_apply_eq _).mpr (quotientRangeTensorEquiv_mk_tmul f x n).symm

end TensorProduct.AlgebraTensorModule

namespace LinearMap

open TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Cokernels commute with scalar extension.** The scalar extension of the cokernel of an
`R`-linear map is canonically the cokernel of its scalar extension. No flatness hypothesis is
needed. -/
noncomputable def cokernelBaseChangeEquiv (f : M →ₗ[R] N) :
    S ⊗[R] (N ⧸ range f) ≃ₗ[S] (S ⊗[R] N) ⧸ range (f.baseChange S) :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S (range f) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      rw [← baseChange_range, Submodule.baseChange]
      ext x
      constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩)

/-- The cokernel base-change equivalence sends a pure tensor represented by `n` to the class of
the corresponding pure tensor. -/
@[simp]
theorem cokernelBaseChangeEquiv_tmul (f : M →ₗ[R] N) (s : S) (n : N) :
    f.cokernelBaseChangeEquiv (S := S) (s ⊗ₜ[R] Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (s ⊗ₜ[R] n) := by
  rw [cokernelBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul,
    Submodule.quotEquivOfEq_mk]

/-- The inverse cokernel base-change equivalence sends the class of a pure tensor to the pure
tensor represented by its class. -/
@[simp]
theorem cokernelBaseChangeEquiv_symm_mk_tmul (f : M →ₗ[R] N) (s : S) (n : N) :
    (f.cokernelBaseChangeEquiv (S := S)).symm (Submodule.Quotient.mk (s ⊗ₜ[R] n)) =
      s ⊗ₜ[R] Submodule.Quotient.mk n := by
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- The cokernel base-change equivalence intertwines the base-changed quotient map with the
quotient map of the base-changed linear map. -/
theorem cokernel_baseChange_square (f : M →ₗ[R] N) :
    (f.cokernelBaseChangeEquiv (S := S) :
      S ⊗[R] (N ⧸ range f) →ₗ[S] (S ⊗[R] N) ⧸ range (f.baseChange S)) ∘ₗ
        (range f).mkQ.baseChange S = (range (f.baseChange S)).mkQ := by
  ext n
  simp

end LinearMap

namespace Submodule

variable {R M : Type*} (A : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Ring A]
  [Algebra R A]

/-- The extension of scalars `p.baseChange A` of a submodule `p ≤ M` is all of `A ⊗[R] M` exactly
when the base change `A ⊗[R] (M ⧸ p)` of the quotient vanishes. -/
theorem baseChange_eq_top_iff_subsingleton (p : Submodule R M) :
    p.baseChange A = ⊤ ↔ Subsingleton (A ⊗[R] (M ⧸ p)) := by
  -- `A ⊗ p → A ⊗ M → A ⊗ (M ⧸ p) → 0` is exact, and the first map has range `p.baseChange A`
  have hexact := lTensor_exact A (LinearMap.exact_subtype_mkQ p) p.mkQ_surjective
  have hrange (x : A ⊗[R] M) : x ∈ p.baseChange A ↔ x ∈ LinearMap.range (p.subtype.lTensor A) := by
    simp [baseChange, LinearMap.baseChange_eq_lTensor]
  refine ⟨fun h ↦ ⟨fun y z ↦ ?_⟩, fun _ ↦ eq_top_iff.mpr fun x _ ↦
    (hrange x).mpr ((hexact x).mp (Subsingleton.elim _ _))⟩
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective A p.mkQ_surjective y
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective A p.mkQ_surjective z
  rw [(hexact y).mpr ((hrange y).mp (h ▸ mem_top)), (hexact z).mpr ((hrange z).mp (h ▸ mem_top))]

end Submodule

namespace QuotSMulTop

open LinearMap TensorProduct
open scoped Pointwise

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Base change kills reduction modulo a vanishing scalar.** If `r : R` maps to `0` in the
`R`-algebra `A`, the base change `A ⊗[R] M → A ⊗[R] (M ⧸ rM)` of the quotient map is
bijective. -/
theorem baseChange_mkQ_bijective {r : R} (hr : algebraMap R A r = 0) :
    Function.Bijective ((r • ⊤ : Submodule R M).mkQ.baseChange A) := by
  let p := r • (⊤ : Submodule R M)
  have hzero : lTensor A p.subtype = 0 := by
    ext a v
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp v.2
    simp [← hw, smul_tmul', Algebra.smul_def, hr]
  rw [baseChange_eq_lTensor]
  exact ⟨(injective_iff_eq_zero_of_exact
    (lTensor_exact A (exact_subtype_mkQ p) p.mkQ_surjective)).mpr hzero,
    lTensor_surjective A p.mkQ_surjective⟩

/-- **Finiteness of a base change killing a scalar.** If `r : R` maps to `0` in the `R`-algebra
`A` and `M ⧸ rM` is finitely generated over `R`, then `A ⊗[R] M` is finitely generated over `A`:
it is isomorphic to `A ⊗[R] (M ⧸ rM)` (`QuotSMulTop.baseChange_mkQ_bijective`). -/
theorem finite_baseChange {r : R} (hr : algebraMap R A r = 0) [Module.Finite R (QuotSMulTop r M)] :
    Module.Finite A (A ⊗[R] M) :=
  Module.Finite.equiv (LinearEquiv.ofBijective _ (baseChange_mkQ_bijective (M := M) hr)).symm

end QuotSMulTop

namespace TauCeti

open scoped TensorProduct

/-- **Finiteness of the reduction in characteristic `ℓ`.** If `k` has characteristic `ℓ` and
`V ⧸ ℓV` is finite, then `k ⊗_ℤ V` is finitely generated over `k`, even when `V` is not. -/
theorem finite_baseChange_of_finite_quotSMulTop (k : Type*) [Ring k] (ℓ : ℕ) [CharP k ℓ]
    (V : Type*) [AddCommGroup V] [Finite (QuotSMulTop (ℓ : ℤ) V)] :
    Module.Finite k (k ⊗[ℤ] V) :=
  have := AddMonoid.FG.to_moduleFinite_int (G := QuotSMulTop (ℓ : ℤ) V)
  QuotSMulTop.finite_baseChange (r := (ℓ : ℤ)) (by simp)

end TauCeti
