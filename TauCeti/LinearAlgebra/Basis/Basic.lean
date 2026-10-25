/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Basic lemmas about bases

A vector whose coordinates in a basis vanish outside a single index is that one coordinate times
the corresponding basis vector.  This repackages `Module.Basis.repr_symm_single`, which it runs
through in the same direction, for the common situation where what one holds is a bound on the
support rather than an explicit `Finsupp.single`.

The coordinate and linear-map lemmas hold over a semiring of scalars. For a finite integer basis of
an additive group, we also express an additive map in coordinates. A ring homomorphism's values on
an integer basis cannot all vanish when its target is nontrivial.

## Main results

* `Module.Basis.eq_smul_of_repr_support_subset_singleton`: a vector supported on one coordinate is
  that coordinate times the corresponding basis vector.
* `Module.Basis.intertwines_of_apply`: a linear map that intertwines two endomorphisms on a basis
  intertwines them everywhere.
* `Module.Basis.coord_map_apply`: the coordinates with respect to a basis transported along a
  linear equivalence are the coordinates of the vector transported back.
* `Module.Basis.linearIndependent_coe_basis`: the vectors of a basis of a submodule `U`, viewed in
  the ambient module, are linearly independent.
* `Module.Basis.apply_eq_sum_repr_zsmul`: an additive map evaluated at a vector is the sum of its
  values on a finite integer basis, weighted by the coordinates.
* `Module.Basis.ringHom_comp_ne_zero`: the values of a ring homomorphism to a nontrivial ring on
  an integer basis do not all vanish.
-/

public section

namespace Module.Basis

variable {ι K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

/-- **A vector whose only possibly nonzero coordinate is the `i`-th one is that coordinate times
the `i`-th basis vector.** -/
theorem eq_smul_of_repr_support_subset_singleton (b : Module.Basis ι K V) {w : V} {i : ι}
    (h : (b.repr w).support ⊆ {i}) : w = b.repr w i • b i :=
  calc w = b.repr.symm (b.repr w) := (b.repr.symm_apply_apply w).symm
    _ = b.repr.symm (Finsupp.single i (b.repr w i)) :=
        congrArg _ (Finsupp.support_subset_singleton.1 h)
    _ = b.repr w i • b i := b.repr_symm_single i _

/-- A linear map carrying one basis to another preserves the corresponding coordinates. -/
theorem repr_map_eq_of_map_basis
    {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (b : Module.Basis ι R M) (c : Module.Basis ι R N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b i) = c i) (x : M) : c.repr (f x) = b.repr x := by
  have h : c.repr.toLinearMap ∘ₗ f = b.repr.toLinearMap := by
    apply b.ext
    intro i
    exact (congrArg c.repr (hf i)).trans
      ((c.repr_self i).trans (b.repr_self i).symm)
  exact DFunLike.congr_fun h x

/-- A linear map intertwines two endomorphisms if it does so on every vector of a basis. -/
theorem intertwines_of_apply {W : Type*} [AddCommMonoid W] [Module K W]
    (b : Module.Basis ι K V) (e : V →ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ i, e (f (b i)) = g (e (b i))) (x : V) : e (f x) = g (e x) := by
  have hmap : e.comp f = g.comp e := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply] using h i
  exact LinearMap.congr_fun hmap x

/-- The coordinates with respect to the basis `b.map f` transported along a linear equivalence
`f` are the coordinates with respect to `b` of the vector transported back along `f`. Not a simp
lemma: simp already unfolds the left side through `Module.Basis.coord_apply`. -/
theorem coord_map_apply {R M M' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] (b : Module.Basis ι R M) (f : M ≃ₗ[R] M') (i : ι) (x : M') :
    (b.map f).coord i x = b.coord i (f.symm x) := by
  simp only [coord_apply, map_repr, LinearEquiv.trans_apply]

section Submodule

variable {R M n : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {U : Submodule R M}

/-- The vectors of a basis of a submodule `U`, viewed in the ambient module, are linearly
independent. -/
theorem linearIndependent_coe_basis (b : Module.Basis n R U) :
    LinearIndependent R fun i ↦ (b i : M) :=
  b.linearIndependent.map_injOn U.subtype U.injective_subtype.injOn

end Submodule

/-- An additive map evaluated at a vector is the sum of its values on a finite integer basis,
weighted by the coordinates. -/
theorem apply_eq_sum_repr_zsmul {M N F : Type*} [AddCommGroup M] [AddCommGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] [Fintype ι] (b : Basis ι ℤ M) (f : F) (y : M) :
    f y = ∑ l, b.repr y l • f (b l) := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, map_zsmul]

section RingHom

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] (b : Basis ι ℤ R)

/-- The values of a ring homomorphism to a nontrivial ring on an integer basis do not all
vanish. The basis need not be finite. -/
theorem ringHom_comp_ne_zero [Nontrivial S] (ψ : R →+* S) : ⇑ψ ∘ ⇑b ≠ 0 := fun h ↦ by
  have : ψ.toAddMonoidHom.toIntLinearMap = 0 := b.ext fun l ↦ by simpa using congrFun h l
  simpa using LinearMap.congr_fun this 1

end RingHom

end Module.Basis
