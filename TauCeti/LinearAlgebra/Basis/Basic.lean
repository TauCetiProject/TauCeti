/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Basic lemmas about bases

A vector whose coordinates in a basis vanish outside a single index is that one coordinate times
the corresponding basis vector.  This repackages `Module.Basis.repr_symm_single`, which it runs
through in the same direction, for the common situation where what one holds is a bound on the
support rather than an explicit `Finsupp.single`.

These lemmas need no additive inverses: they hold over a semiring of scalars. Their proofs combine
coordinate isomorphisms and `Finsupp.support_subset_singleton` with basis extensionality and
linear-map composition.

## Main results

* `Module.Basis.eq_smul_of_repr_support_subset_singleton`: a vector supported on one coordinate is
  that coordinate times the corresponding basis vector.
* `Module.Basis.intertwines_of_apply`: a linear map that intertwines two endomorphisms on a basis
  intertwines them everywhere.
* `Module.Basis.coord_map_apply`: the coordinates with respect to a basis transported along a
  linear equivalence are the coordinates of the vector transported back.
* `Module.Basis.linearIndependent_coe_basis`: the vectors of a basis of a submodule `U`, viewed in
  the ambient module, are linearly independent.
* `Module.Basis.linearIndependent_of_repr_eq_single`: a family indexed by a finite set `S` of
  indices, whose `s`-th member has the coordinates of `b s` at the indices in `S`, is linearly
  independent.
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

/-- A family of vectors indexed by a finite set `S` of indices, whose `s`-th member has the
coordinates of `b s` at the indices in `S`, is linearly independent. -/
theorem linearIndependent_of_repr_eq_single {b : Module.Basis ι K V} {S : Finset ι} {v : S → V}
    (hv : ∀ s : S, ∀ t ∈ S, b.repr (v s) t = Finsupp.single (s : ι) 1 t) :
    LinearIndependent K v := by
  classical
  let π : V →ₗ[K] (S → K) := LinearMap.pi fun t ↦ b.coord t
  have hπ : π ∘ v = fun s ↦ Pi.single s 1 := by
    funext s t
    simp only [Function.comp_apply, π, LinearMap.pi_apply, coord_apply]
    rw [hv s t t.2]
    by_cases hst : t = s
    · simp [hst]
    · rw [Finsupp.single_eq_of_ne (fun h : (t : ι) = s ↦ hst (Subtype.ext h)),
        Pi.single_eq_of_ne hst]
  exact LinearIndependent.of_comp π (hπ ▸ Pi.linearIndependent_single_one S K)

section Submodule

variable {R M n : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {U : Submodule R M}

/-- The vectors of a basis of a submodule `U`, viewed in the ambient module, are linearly
independent. -/
theorem linearIndependent_coe_basis (b : Module.Basis n R U) :
    LinearIndependent R fun i ↦ (b i : M) :=
  b.linearIndependent.map_injOn U.subtype U.injective_subtype.injOn

end Submodule

end Module.Basis
