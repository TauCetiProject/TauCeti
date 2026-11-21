/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed

/-!
# Invariants of a cofree comodule

The invariant vectors of the cofree comodule `M ⊗ H` are exactly the tensors `m ⊗ 1`.
Counit evaluation identifies them naturally with `M`. This is the degree-zero
calculation for cofree coefficients in rational cohomology; it needs neither flatness
nor injectivity of `M` and holds over a commutative semiring.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §4.7(a).
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable (R H M : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H]
  [AddCommMonoid M] [Module R M]

attribute [local instance] cofree

/-- An invariant cofree vector is recovered by tensoring its counit evaluation with `1`. -/
theorem eq_counit_tmul_one_of_mem_fixedSubcomodule
    (x : M ⊗[R] H) (hx : x ∈ fixedSubcomodule R H (M ⊗[R] H)) :
    x = (TensorProduct.rid R M (Coalgebra.counit.lTensor M x)) ⊗ₜ[R] (1 : H) := by
  let e := (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := H)).lTensor M
  have h := congrArg (e.rTensor H) (mem_fixedSubcomodule.mp hx)
  have he : e.rTensor H (cofreeCoact R H M x) = x :=
    LinearMap.congr_fun (rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
      (R := R) (C := H) (M := M)) x
  rw [cofree_coact, ← cofreeCoact_def, he] at h
  simpa [e] using h

/-- Counit evaluation identifies the invariants of a cofree comodule with its
coefficient module. Its inverse sends `m` to `m ⊗ 1`. -/
noncomputable def cofreeInvariantsEquiv :
    fixedSubcomodule R H (M ⊗[R] H) ≃ₗ[R] M where
  toLinearMap := ((TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := H)).lTensor M).comp
      (SMulMemClass.subtype (fixedSubcomodule R H (M ⊗[R] H)))
  invFun m := ⟨m ⊗ₜ[R] 1, by simp [Algebra.TensorProduct.one_def]⟩
  left_inv x := Subtype.ext
    (eq_counit_tmul_one_of_mem_fixedSubcomodule R H M x x.property).symm
  right_inv m := by simp

/-- The forward cofree-invariants comparison is counit evaluation. -/
@[simp]
theorem cofreeInvariantsEquiv_apply (x : fixedSubcomodule R H (M ⊗[R] H)) :
    cofreeInvariantsEquiv R H M x =
      TensorProduct.rid R M (Coalgebra.counit.lTensor M (x : M ⊗[R] H)) :=
  (rfl)

/-- The inverse cofree-invariants comparison tensors with `1`. -/
@[simp]
theorem cofreeInvariantsEquiv_symm_apply (m : M) :
    ((cofreeInvariantsEquiv R H M).symm m : M ⊗[R] H) = m ⊗ₜ[R] (1 : H) :=
  (rfl)

/-- The cofree-invariants comparison is natural in the coefficient module. -/
theorem cofreeInvariantsEquiv_naturality {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : fixedSubcomodule R H (M ⊗[R] H)) :
    cofreeInvariantsEquiv R H N ((Hom.cofreeMap f).fixedMap x) =
      f (cofreeInvariantsEquiv R H M x) := by
  simpa only [cofreeInvariantsEquiv_apply, Hom.fixedMap_apply, Hom.cofreeMap_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun
      (rid_comp_lTensor_counit_comp_rTensor (C := H) f) (x : M ⊗[R] H)

end TauCeti.Comodule
