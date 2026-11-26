/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice

/-!
# Self-dual lattices and perfect pairings

An integral pairing, nondegenerate over the fraction field, is perfect exactly when the image of
the lattice in its fraction-field extension is self-dual.
-/

public section

open scoped TensorProduct
open Module

namespace LinearMap.BilinForm

/-- An integral form with nondegenerate scalar extension identifies the original module with its
linear dual exactly when the integral lattice in the fraction-field extension is self-dual. -/
theorem dualSubmodule_range_mk_eq_self_iff_isPerfPair {R K M : Type*}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (B : LinearMap.BilinForm R M) (hB : (B.baseChange K).Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    (B.baseChange K).dualSubmodule N = N ↔ B.IsPerfPair := by
  let f := TensorProduct.mk R K M 1
  let N := LinearMap.range f
  let C := B.baseChange K
  let D := C.dualSubmodule N
  have hND : N ≤ D := by
    rintro _ ⟨x, rfl⟩
    refine (mem_dualSubmodule _).2 ?_
    rintro _ ⟨y, rfl⟩
    exact Submodule.mem_one.2 ⟨B x y, by simp [C, f, Algebra.algebraMap_eq_smul_one]⟩
  let i : M →ₗ[R] D := f.codRestrict D fun x ↦ hND ⟨x, rfl⟩
  let u : M ≃ₗ[R] N := TensorProduct.unitTmulEquiv R K M
  let e : D ≃ₗ[R] Module.Dual R M := (C.dualSubmoduleEquivDual hB N).trans u.dualMap
  have hcomp : e.toLinearMap.comp i = B := by
    ext x y
    apply FaithfulSMul.algebraMap_injective R K
    have hp := dualSubmodulePairing_spec C (i x) (u y)
    rw [← dualSubmoduleToDual_apply_apply, ← dualSubmoduleEquivDual_apply] at hp
    calc
      algebraMap R K (((e.toLinearMap.comp i) x) y) = C (i x : K ⊗[R] M) (u y) := by
        simpa only [e, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.trans_apply, LinearEquiv.dualMap_apply] using hp
      _ = _ := by
        have hx : (i x : K ⊗[R] M) = 1 ⊗ₜ[R] x := (rfl)
        have hy : (u y : K ⊗[R] M) = 1 ⊗ₜ[R] y := TensorProduct.coe_unitTmulEquiv_apply y
        rw [hx, hy]
        simp [C, Algebra.algebraMap_eq_smul_one]
  have hi : Function.Injective i := fun x y h ↦
    (Module.Flat.tensorProduct_mk_injective R M K) (congrArg Subtype.val h)
  constructor
  · intro h
    have hD : D = N := h
    have hs : Function.Surjective i := by
      intro x
      obtain ⟨y, hy⟩ := (hD ▸ x.property : (x : K ⊗[R] M) ∈ N)
      exact ⟨y, Subtype.ext hy⟩
    exact .of_bijective B (hcomp ▸ e.bijective.comp ⟨hi, hs⟩)
  · intro h
    apply le_antisymm (fun x hx ↦ ?_) hND
    obtain ⟨y, hy⟩ := h.bijective_left.surjective (e ⟨x, hx⟩)
    have hxy : i y = ⟨x, hx⟩ := e.injective (by
      simpa only [← hcomp, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hy)
    exact ⟨y, congrArg Subtype.val hxy⟩

end LinearMap.BilinForm
