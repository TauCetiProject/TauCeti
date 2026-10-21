/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.RepresentationTheory.GrothendieckGroup.ProjectiveBasis
import TauCeti.RingTheory.GradedAlgebra.Basic
import TauCeti.RingTheory.Idempotents.Hom

/-!
# Forgetting the grading on the idempotent projective basis

Let `A` be a nonnegatively graded finite-dimensional algebra over a field `k` whose degree-zero
piece is spanned by a complete family of orthogonal nonzero idempotents `eᵢ`. The graded
projectives `A eᵢ` form a Laurent basis of `K₀^gr(proj A)`
(`TauCeti.gradedIdempotentProjectiveBasis`). This file shows that the underlying ungraded modules
`A eᵢ` form a `ℤ`-basis of `K₀(proj A)`, so that forgetting the grading identifies graded
projective `K₀` specialized at `q = 1` with ordinary projective `K₀`. No finite global dimension is
assumed: the comparison goes through the two bases, not through the Cartan maps.

The ungraded input is a degree-zero computation in `A` itself. The degree-zero component of a
product is the product of the degree-zero components, and an idempotent without degree-zero
component vanishes (`TauCeti.GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero`). An
idempotent `f` of the corner `eᵢ A eᵢ` has degree-zero component in `eᵢ A eᵢ ∩ 𝒜 0 = k eᵢ`,
an idempotent multiple of `eᵢ`; so `f` or `eᵢ - f` has no degree-zero component and vanishes, and
`eᵢ` is primitive. An isomorphism `A eᵢ ≅ A eⱼ` with `i ≠ j` would write `eᵢ = x y` with
`x ∈ eᵢ A eⱼ`, whose degree-zero component vanishes, so the `A eᵢ` are pairwise nonisomorphic.
Over the Artinian ring `A` they then form the basis `TauCeti.idempotentProjectiveBasis`.

## Main definitions

* `TauCeti.gradedIdempotentProjectiveForgetK0Equiv`: forgetting the grading identifies
  `K₀^gr(proj A)` specialized at `q = 1` with `K₀(proj A)`.

## Main results

* `TauCeti.coe_decompose_mem_cornerSubmodule`: the homogeneous components of an element of a
  corner `aAb` cut out by idempotents of degree zero lie in that corner.
* `TauCeti.isPrimitiveIdempotent_of_gradeZero_le_span`: each `eᵢ` is a primitive idempotent of
  `A`, so `A eᵢ` is indecomposable as an ungraded module.
* `TauCeti.isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span`: the ungraded modules `A eᵢ`
  are pairwise nonisomorphic.
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

variable {A : Type uA} [Ring A]

/-! ### Corners and degree-zero components -/

section Corner

variable {k : Type uk} [CommRing k] [Algebra k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The homogeneous components of an element of the corner `aAb` cut out by two idempotents of
degree zero lie in the same corner. -/
theorem coe_decompose_mem_cornerSubmodule {a b x : A} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (ha₀ : a ∈ 𝒜 0) (hb₀ : b ∈ 𝒜 0)
    (hx : x ∈ cornerSubmodule k a b) (p : ℤ) :
    (decompose 𝒜 x p : A) ∈ cornerSubmodule k a b := by
  rw [mem_cornerSubmodule_iff k ha hb] at hx ⊢
  rw [← coe_decompose_mul_of_left_mem_zero 𝒜 ha₀, ← coe_decompose_mul_of_right_mem_zero 𝒜 hb₀, hx]

end Corner

variable {k : Type uk} [Field k] [Algebra k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} {e : I → A}

/-! ### The ungraded modules `A eᵢ` -/

section Ungraded

variable (ho : OrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0) (hneg : ∀ p < 0, 𝒜 p = ⊥)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

include ho he₀ hneg hspan in
/-- **Each `eᵢ` is a primitive idempotent of `A`** when `A` is nonnegatively graded and its
degree-zero piece is spanned by the orthogonal idempotents `eᵢ`. The degree-zero component of an
idempotent `f` of the corner `eᵢ A eᵢ` is an idempotent of `eᵢ A eᵢ ∩ 𝒜 0 = k eᵢ`, hence `0` or
`eᵢ`; accordingly `f` or `eᵢ - f` is an idempotent without degree-zero component, hence zero. -/
theorem isPrimitiveIdempotent_of_gradeZero_le_span (i : I) (hne : e i ≠ 0) :
    IsPrimitiveIdempotent (e i) := by
  have hei := ho.idem i
  refine isPrimitiveIdempotent_of_eq_zero_or_eq hei hne fun f hf hef hfe => ?_
  have hmem : (decompose 𝒜 f 0 : A) ∈ cornerSubmodule k (e i) (e i) ⊓ 𝒜 0 :=
    ⟨coe_decompose_mem_cornerSubmodule hei hei (he₀ i) (he₀ i)
      ((mem_cornerSubmodule_iff k hei hei).2 (by rw [hef, hfe])) 0, (decompose 𝒜 f 0).2⟩
  rw [cornerSubmodule_inf_zero_eq_span_singleton he₀ ho hspan i,
    Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcc : c * c = c := by
    have h := GradedAlgebra.coe_decompose_mul_zero_of_nonneg hneg f f
    rw [hf.eq, ← hc, smul_mul_smul_comm, hei.eq] at h
    exact smul_left_injective k hne h.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hcc with rfl | rfl
  · exact .inl (GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero hneg hf
      (by rw [← hc, zero_smul]))
  · refine .inr (sub_eq_zero.1 ?_).symm
    refine GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero hneg
      (hf.sub hei hfe hef) ?_
    rw [decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, decompose_of_mem_same 𝒜 (he₀ i),
      ← hc, one_smul, sub_self]

include ho he₀ hneg hspan in
/-- **The ungraded modules `A eᵢ` are pairwise nonisomorphic** when `A` is nonnegatively graded
and its degree-zero piece is spanned by the orthogonal idempotents `eᵢ`. An isomorphism
`A eᵢ ≅ A eⱼ` and its inverse send the generators to `x ∈ eᵢ A eⱼ` and `y ∈ eⱼ A eᵢ` with
`eᵢ = x y`; the degree-zero component of `x` lies in `eᵢ A eⱼ ∩ 𝒜 0 = 0`, so the degree-zero
component `eᵢ` of `x y` vanishes. -/
theorem isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span {i j : I} (hij : i ≠ j)
    (hi : e i ≠ 0) :
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)) := by
  refine ⟨fun φ => hi ?_⟩
  set x : A := (φ (spanSingletonGenerator (e i)) : A) with hxdef
  have hx : x ∈ cornerSubmodule k (e i) (e j) :=
    apply_generator_mem_cornerSubmodule (ho.idem i) (ho.idem j) φ.toLinearMap
  have hxy : e i = x * (φ.symm (spanSingletonGenerator (e j)) : A) := by
    have h := coe_apply_eq_mul_apply_generator (ho.idem j) φ.symm.toLinearMap
      (φ (spanSingletonGenerator (e i)))
    simpa using h
  have hx₀ : (decompose 𝒜 x 0 : A) = 0 := by
    by_contra h
    exact lt_irrefl 0 (pos_of_mem_cornerSubmodule_inf ho hneg hspan hij
      ⟨coe_decompose_mem_cornerSubmodule (ho.idem i) (ho.idem j) (he₀ i) (he₀ j) hx 0,
        (decompose 𝒜 x 0).2⟩ h)
  rw [← decompose_of_mem_same 𝒜 (he₀ i), hxy, GradedAlgebra.coe_decompose_mul_zero_of_nonneg hneg,
    hx₀, zero_mul]

end Ungraded

/-! ### Forgetting the grading at `q = 1` -/

section ForgetGrading

variable [Fintype I] [Module.Finite k A] (he : CompleteOrthogonalIdempotents e)
  (he₀ : ∀ i, e i ∈ 𝒜 0) (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) (hne : ∀ i, e i ≠ 0)

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
  (LaurentSpecialization.basis 1
      (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)).repr.trans
    (idempotentProjectiveBasis he
      (fun i => isPrimitiveIdempotent_of_gradeZero_le_span he.toOrthogonalIdempotents he₀ hneg
        hspan i (hne i))
      (fun i _ hij => isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span
        he.toOrthogonalIdempotents he₀ hneg hspan hij (hne i))).repr.symm

/-- The equivalence `TauCeti.gradedIdempotentProjectiveForgetK0Equiv` is the map induced by
forgetting the grading. -/
@[simp]
theorem gradedIdempotentProjectiveForgetK0Equiv_toLinearMap :
    (gradedIdempotentProjectiveForgetK0Equiv he he₀ hI hneg hspan hne).toLinearMap =
      gradedFiniteProjectiveModulesForgetK0 𝒜 := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let b :=
    LaurentSpecialization.basis 1 (gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne)
  refine b.ext fun i => ?_
  calc
    gradedIdempotentProjectiveForgetK0Equiv he he₀ hI hneg hspan hne (b i) =
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
@[simp]
theorem gradedIdempotentProjectiveForgetK0Equiv_mk_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedIdempotentProjectiveForgetK0Equiv he he₀ hI hneg hspan hne
        (LaurentSpecialization.mk 1
          (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M)) =
      ExactK0.of.{uA} ((gradedFiniteProjectiveModulesForget 𝒜).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedIdempotentProjectiveForgetK0Equiv_toLinearMap]
  exact gradedFiniteProjectiveModulesForgetK0_mk_of 𝒜 M

/-- The inverse equivalence sends the class of the underlying module of a finite graded
projective, for instance of an ideal `A eᵢ`, to its specialized graded class. -/
theorem gradedIdempotentProjectiveForgetK0Equiv_symm_of
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    (gradedIdempotentProjectiveForgetK0Equiv he he₀ hI hneg hspan hne).symm
        (ExactK0.of.{uA} ((gradedFiniteProjectiveModulesForget 𝒜).obj M)) =
      LaurentSpecialization.mk 1
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M) := by
  rw [LinearEquiv.symm_apply_eq, gradedIdempotentProjectiveForgetK0Equiv_mk_of]

end ForgetGrading

end TauCeti
