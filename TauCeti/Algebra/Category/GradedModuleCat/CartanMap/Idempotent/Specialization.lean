/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.RepresentationTheory.GrothendieckGroup.ProjectiveBasis

/-!
# Forgetting the grading on the idempotent projective basis

Let `A` be a nonnegatively graded finite-dimensional algebra over a field `k` whose degree-zero
piece is spanned by a complete family of orthogonal nonzero idempotents `eᵢ`. The graded
projectives `A eᵢ` form a Laurent basis of `K₀^gr(proj A)`
(`TauCeti.gradedIdempotentProjectiveBasis`). This file shows that the underlying ungraded modules
`A eᵢ` form a `ℤ`-basis of `K₀(proj A)`, so that forgetting the grading identifies graded
projective `K₀` specialized at `q = 1` with ordinary projective `K₀`. No finite global dimension is
assumed: the comparison goes through the two bases, not through the Cartan maps.

The ungraded input is that each `eᵢ` is primitive
(`TauCeti.isPrimitiveIdempotent_of_gradeZero_le_span`) and that the ungraded modules `A eᵢ` are
pairwise nonisomorphic (`TauCeti.isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span`). Over
the Artinian ring `A` they then form the basis `TauCeti.idempotentProjectiveBasis`.

## Main definitions

* `TauCeti.gradedIdempotentProjectiveForgetK0Equiv`: forgetting the grading identifies
  `K₀^gr(proj A)` specialized at `q = 1` with `K₀(proj A)`.

## Main results

* `TauCeti.gradedIdempotentProjectiveForgetK0Equiv_toLinearMap`: the underlying map of that
  equivalence is `TauCeti.gradedFiniteProjectiveModulesForgetK0`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Sections 2.3--2.4, for graded
  projectives over a graded algebra.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for graded
  Grothendieck groups and their specialization at `q = 1`.
* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter I, Section 4, for primitive idempotents and indecomposable projectives.
-/

public section

namespace TauCeti

open CategoryTheory _root_.DirectSum

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} {e : I → A}

/-! ### Forgetting the grading at `q = 1` -/

section ForgetGrading

variable [Fintype I] [Module.Finite k A] (he : CompleteOrthogonalIdempotents e)
  (he₀ : ∀ i, e i ∈ 𝒜 0) (hneg : ∀ p < 0, 𝒜 p = ⊥) (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))
  (hne : ∀ i, e i ≠ 0)

include he₀ hneg hspan hne in
/-- **Forgetting the grading identifies projective `K₀` at `q = 1`** for a nonnegatively graded
finite-dimensional algebra whose degree-zero piece is spanned by a complete family of orthogonal
nonzero idempotents `eᵢ`: it sends the specialized graded basis `[A eᵢ]` to the ungraded basis
`[A eᵢ]` of `K₀(proj A)`. The underlying map is
`TauCeti.gradedFiniteProjectiveModulesForgetK0`
(`TauCeti.gradedIdempotentProjectiveForgetK0Equiv_toLinearMap`). -/
noncomputable def gradedIdempotentProjectiveForgetK0Equiv :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) ≃ₗ[ℤ]
      ExactK0.{uA} (finiteProjectiveModulesExactStructure A) :=
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hI (i : I) : (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜 :=
    Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ i⟩
  (LaurentSpecialization.basis 1
      (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)).repr.trans
    (idempotentProjectiveBasis he
      (fun i => isPrimitiveIdempotent_of_gradeZero_le_span he₀ he.toOrthogonalIdempotents hneg
        hspan i (hne i))
      (fun i _ hij => isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span
        he₀ he.toOrthogonalIdempotents hneg hspan hij (hne i))).repr.symm

/-- The equivalence `TauCeti.gradedIdempotentProjectiveForgetK0Equiv` is the map induced by
forgetting the grading. -/
@[simp]
theorem gradedIdempotentProjectiveForgetK0Equiv_toLinearMap :
    (gradedIdempotentProjectiveForgetK0Equiv he he₀ hneg hspan hne).toLinearMap =
      gradedFiniteProjectiveModulesForgetK0 𝒜 := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hI (i : I) : (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜 :=
    Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ i⟩
  let b :=
    LaurentSpecialization.basis 1 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
  refine b.ext fun i => ?_
  calc
    gradedIdempotentProjectiveForgetK0Equiv he he₀ hneg hspan hne (b i) =
        ExactK0.of.{uA} (⟨ModuleCat.of A (Ideal.span {e i}), finiteProjectiveModules_iff.2
          ⟨inferInstance, (he.idem i).projective_span_singleton⟩⟩ :
            (finiteProjectiveModules A).FullSubcategory) := by
      simp only [gradedIdempotentProjectiveForgetK0Equiv, b, LinearEquiv.trans_apply,
        Module.Basis.repr_self, Module.Basis.repr_symm_single_one]
      exact idempotentProjectiveBasis_apply _ _ _ i
    _ = gradedFiniteProjectiveModulesForgetK0 𝒜 (b i) := by
      -- The rewrite closes the goal by `rfl`: the underlying module of the graded ideal
      -- `GradedModuleCat.ofIdeal` is the ideal itself.
      rw [LaurentSpecialization.basis_apply, gradedIdempotentProjectiveBasis_apply,
        gradedFiniteProjectiveModulesForgetK0_mk_of, gradedFiniteProjectiveModulesForget_obj]

/-- On a specialized graded projective class, the equivalence returns its underlying ungraded
class. -/
-- A simp rule here would normalize the inner application before generic inverse laws match.
theorem gradedIdempotentProjectiveForgetK0Equiv_mk_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedIdempotentProjectiveForgetK0Equiv he he₀ hneg hspan hne
        (LaurentSpecialization.mk 1
          (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M)) =
      ExactK0.of.{uA} ((gradedFiniteProjectiveModulesForget 𝒜).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedIdempotentProjectiveForgetK0Equiv_toLinearMap]
  exact gradedFiniteProjectiveModulesForgetK0_mk_of 𝒜 M

/-- The inverse equivalence sends the class of the underlying module of a finite graded
projective, for instance of an ideal `A eᵢ`, to its specialized graded class. -/
theorem gradedIdempotentProjectiveForgetK0Equiv_symm_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    (gradedIdempotentProjectiveForgetK0Equiv he he₀ hneg hspan hne).symm
        (ExactK0.of.{uA} ((gradedFiniteProjectiveModulesForget 𝒜).obj M)) =
      LaurentSpecialization.mk 1
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M) := by
  rw [LinearEquiv.symm_apply_eq, gradedIdempotentProjectiveForgetK0Equiv_mk_of]

end ForgetGrading

end TauCeti
