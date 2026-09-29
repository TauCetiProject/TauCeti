/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveCover.Existence
public import TauCeti.RingTheory.KrullSchmidt.Cancellation

/-!
# Surjections from a projective module over a semiprimary ring

Over a semiprimary ring every module has a projective cover, and this makes a map from a projective
module of finite length determined, up to an automorphism of its source, by its range: if
`a b : F → E` have the same range `X`, then `b ∘ θ = a` for an automorphism `θ` of `F`. Both maps
factor through the projective cover `P → X` by surjections `F → P`, and two surjections onto the
projective module `P` of finite length differ by an automorphism, by Krull–Schmidt cancellation of
`P` (`TauCeti.exists_linearEquiv_comp_eq_of_surjective`).

For `F` free this says that two presentations of the same module by the same number of generators
are related by a change of generators, the module-theoretic analogue of Gaschütz's lemma. Over the
group algebra of a finite group over a field it compares two presentations of the augmentation
ideal; lifting from the residue field, it compares them over a local ring as well.

## Main results

* `TauCeti.exists_linearEquiv_comp_eq_of_range_eq`: two maps with the same range from a projective
  module of finite length over a semiprimary ring differ by an automorphism of the source.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, Graduate Texts in Mathematics 131,
  Springer (2001), §24 (projective covers over semiperfect rings).
* K. W. Gruenberg, *Relation modules of finite groups*, CBMS Regional Conference Series in
  Mathematics 25, American Mathematical Society (1976).
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] [IsSemiprimaryRing R]
  {F : Type v} [AddCommGroup F] [Module R F] {E : Type w} [AddCommGroup E] [Module R E]

/-- **Maps from a projective module of finite length with the same range differ by an
automorphism.** Over a semiprimary ring, if `F` is projective of finite length and `a b : F → E`
have the same range, then `b ∘ θ = a` for some automorphism `θ` of `F`. In particular two
surjections from `F` onto the same module have isomorphic kernels. -/
theorem exists_linearEquiv_comp_eq_of_range_eq [Module.Projective R F] (hF : IsFiniteLength R F)
    {a b : F →ₗ[R] E} (h : LinearMap.range a = LinearMap.range b) :
    ∃ θ : F ≃ₗ[R] F, b ∘ₗ θ.toLinearMap = a := by
  -- Corestrict both maps to their common range and lift them to a projective cover of it.
  let a' : F →ₗ[R] LinearMap.range a := a.rangeRestrict
  let b' : F →ₗ[R] LinearMap.range a := b.codRestrict _ fun x ↦ h ▸ LinearMap.mem_range_self b x
  have hb' : Function.Surjective b' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h ▸ hy
    exact ⟨x, rfl⟩
  obtain ⟨P, hP⟩ := exists_isProjectiveCover R (LinearMap.range a)
  have := hP.projective
  let π : P →ₗ[R] LinearMap.range a := Finsupp.linearCombination R id ∘ₗ P.subtype
  obtain ⟨s, hs, hs'⟩ := IsProjectiveCover.exists_surjective (P := P) (f := π) hP
    a.surjective_rangeRestrict
  obtain ⟨t, ht, ht'⟩ := IsProjectiveCover.exists_surjective (P := P) (f := π) hP hb'
  -- The cover is a quotient of `F`, hence of finite length, so the two lifts differ by an
  -- automorphism of `F`.
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hF
  have : IsNoetherian R P := isNoetherian_of_surjective s (LinearMap.range_eq_top.mpr hs')
  have : IsArtinian R P := isArtinian_of_surjective F s hs'
  have hPfin : IsFiniteLength R P :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨θ, hθ⟩ := exists_linearEquiv_comp_eq_of_surjective (t := t) hPfin hs' ht'
  refine ⟨θ, LinearMap.ext fun x ↦ ?_⟩
  have := congr((π ($hθ x) : E))
  simpa [← LinearMap.comp_apply, ← LinearMap.comp_assoc, ht, hs, b'] using this

end TauCeti
