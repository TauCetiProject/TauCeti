/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Injective maps between free abelian groups of equal rank

An injective `ℤ`-linear map `f : M → N` into a finitely generated free abelian group of the same
rank has image of finite index `c`, so `c • y` lies in the image of `f` for every `y : N`.
Dividing by `f` gives a map `g : N → M` such that `f ∘ g` and `g ∘ f` are both multiplication by
`c`: an inverse of `f` up to a nonzero scalar. Over `ℚ` the map `f` becomes invertible with
inverse `c⁻¹ • g`; over `ℤ` an inverse up to a scalar is the best available.

## Main results

* `LinearMap.exists_comp_eq_nsmul_id_of_injective`: an injective map between finitely generated
  free abelian groups of equal rank has an inverse up to multiplication by a nonzero natural
  number.
-/

public section

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- An injective `ℤ`-linear map into a finitely generated free abelian group of the same rank
has an inverse up to multiplication by a nonzero natural number `c`, namely the index of its
image. -/
theorem exists_comp_eq_nsmul_id_of_injective {f : M →ₗ[ℤ] N} (hf : Function.Injective f)
    (hrank : Module.finrank ℤ M = Module.finrank ℤ N) :
    ∃ c : ℕ, c ≠ 0 ∧ ∃ g : N →ₗ[ℤ] M, f ∘ₗ g = c • LinearMap.id ∧ g ∘ₗ f = c • LinearMap.id := by
  have : Finite (N ⧸ range f) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ ((finrank_range_of_inj hf).trans hrank)
  have : Finite (N ⧸ (range f).toAddSubgroup) := ‹Finite (N ⧸ range f)›
  set c := (range f).toAddSubgroup.index
  let g : N →ₗ[ℤ] M := (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
    (c • LinearMap.id).codRestrict (range f) fun y ↦ (range f).toAddSubgroup.nsmul_index_mem y
  have hfg : f ∘ₗ g = c • LinearMap.id := by
    ext y
    simp [g]
  refine ⟨c, AddSubgroup.index_ne_zero_of_finite, g, hfg, ?_⟩
  ext x
  apply hf
  simpa using congr($hfg (f x))

end LinearMap
