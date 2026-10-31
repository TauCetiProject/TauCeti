/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.ProjectiveCover
public import TauCeti.RingTheory.Idempotents.Simple

/-!
# Graded heads of primitive idempotents over a semisimple degree-zero part

Let `A` be a nonnegatively graded algebra over a field `k` whose degree-zero part `A₀ = 𝒜 0` is
a semisimple ring, and let `f` be a primitive idempotent of `A` of degree zero. The graded module
`Sf = A f / A₊f` (`TauCeti.gradedPositiveMulQuotient`) is concentrated in degree zero, where it is
a nonzero quotient of the `A₀`-module `A₀ f`, and positive-degree elements act on it by zero.
Since `f` stays primitive in `A₀` and `A₀` is semisimple, this quotient is a simple `A₀`-module, so
`Sf` is a simple `A`-module. When `A` is finite-dimensional, the quotient map `A f ⟶ Sf` is a
projective cover.

Unlike the split situation of `TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head`, the
degree-zero corner `f A₀ f` need not be the line `k f`: it is isomorphic to the opposite of the
division algebra `End_A(Sf)`, so its dimension is `dim_k End_A(Sf)`, the constant graded dimension
of `f • Sf`. A second primitive idempotent
`f'` whose ungraded left ideal `A f'` is not isomorphic to `A f` kills `Sf`: otherwise `A f'`
would cover `Sf` as well, and projective covers are unique.

For a complete family of orthogonal primitive idempotents `eᵢ` of degree zero with pairwise
nonisomorphic left ideals `A eᵢ`, the heads `Sᵢ` therefore satisfy the hypotheses of the general
simple-class basis of graded `G₀`: `gdim(eⱼ • Sᵢ) = 0` for `i ≠ j`, `gdim(eᵢ • Sᵢ)` is the
nonzero constant `dim_k End_A(Sᵢ)`, and every simple finite graded module is a shift of some `Sᵢ`.
These are the hypotheses of `TauCeti.gradedIdempotentProjectiveBasisOfPrimitive` together with
semisimplicity of `A₀` and nonnegativity of the grading, so the field need not split the simples.

## Main results

* `TauCeti.isSimpleModule_gradedPositiveMulQuotient`: `A f / A₊f` is a simple module.
* `TauCeti.isProjectiveCover_gradedPositiveMulQuotientMk`: `A f ⟶ A f / A₊f` is a projective
  cover.
* `TauCeti.smul_gradedPositiveMulQuotient_eq_zero`: a primitive idempotent with nonisomorphic left
  ideal kills `A f / A₊f`.
* `TauCeti.smulGradedDimension_gradedPositiveMulQuotient_self`: `gdim(f • Sf) = dim_k End_A(Sf)`.
* `TauCeti.isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent`:
  the heads of a complete family of primitive idempotents exhaust the simple finite graded
  modules up to shift.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded simple
  modules.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for positively graded rings with semisimple degree-zero part.
* Peter Webb, *A Course in Finite Group Representation Theory*, Section 7.4, for the
  division-endomorphism factor over a general field.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory _root_.DirectSum
open scoped Pointwise

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] (hneg : ∀ p < 0, 𝒜 p = ⊥)

include hneg

/-- **The quotient map `A f ⟶ A f / A₊f` is a projective cover** for a primitive idempotent `f`
of degree zero of a finite-dimensional nonnegatively graded algebra: `A f / A₊f` is a nonzero
quotient of `A f`. -/
theorem isProjectiveCover_gradedPositiveMulQuotientMk [Module.Finite k A] {f : A}
    (hf : IsPrimitiveIdempotent f) (hf₀ : f ∈ 𝒜 0) :
    IsProjectiveCover (gradedPositiveMulQuotientMk hf₀) := by
  have := IsArtinianRing.of_finite k A
  have := nontrivial_gradedPositiveMulQuotient hneg hf₀ hf.ne_zero
  exact hf.isProjectiveCover_of_surjective (gradedPositiveMulQuotientMk_surjective hf₀)

/-- The graded dimension of `f • (A f / A₊f)` is nonzero for a nonzero idempotent `f` of degree
zero: `f • (A f / A₊f)` contains the nonzero class of `f`. -/
theorem smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero [Module.Finite k A] {f : A}
    (hf : IsIdempotentElem f) (hf₀ : f ∈ 𝒜 0) (hne : f ≠ 0) :
    (gradedPositiveMulQuotient 𝒜 hf₀).smulGradedDimension f ≠ 0 := by
  intro h
  have h₀ : f • (gradedPositiveMulQuotient 𝒜 hf₀).grading.piece 0 = ⊥ := by
    have := congrArg (fun P : LaurentPolynomial ℤ => P.coeff 0) h
    simpa [GradedModuleCat.coeff_smulGradedDimension] using this
  apply gradedPositiveMulQuotientMk_spanSingletonGenerator_ne_zero hneg hf₀ hne
  have hmem : f • gradedPositiveMulQuotientMk hf₀ (spanSingletonGenerator f) ∈
      f • (gradedPositiveMulQuotient 𝒜 hf₀).grading.piece 0 :=
    Submodule.smul_mem_pointwise_smul _ _ _
      ((gradedPositiveMulQuotient_piece_zero_eq_top hneg hf hf₀).ge Submodule.mem_top)
  have hgen : f • spanSingletonGenerator f = spanSingletonGenerator f :=
    Subtype.ext (by simp [hf.eq])
  rwa [h₀, Submodule.mem_bot, ← map_smul, hgen] at hmem

variable [IsSemisimpleRing (𝒜 0)]

/-- **The head `A f / A₊f` of a primitive idempotent is a simple module** over a nonnegatively
graded algebra whose degree-zero part is semisimple. As an `A₀`-module it is a nonzero quotient
of the indecomposable left ideal `A₀ f` of the semisimple ring `A₀`, and positive-degree elements
act on it by zero. -/
theorem isSimpleModule_gradedPositiveMulQuotient {f : A} (hf : IsPrimitiveIdempotent f)
    (hf₀ : f ∈ 𝒜 0) : IsSimpleModule A (gradedPositiveMulQuotient 𝒜 hf₀) := by
  -- Mathlib's ring structure on `𝒜 0` is that of the degree-zero subalgebra acting on modules.
  let R₀ := SetLike.GradeZero.subalgebra 𝒜
  have : IsSemisimpleRing R₀ := ‹IsSemisimpleRing (𝒜 0)›
  have hf₀' : IsPrimitiveIdempotent (⟨f, hf₀⟩ : R₀) :=
    IsPrimitiveIdempotent.of_map R₀.val Subtype.val_injective (b := ⟨f, hf₀⟩) hf
  have : Nontrivial (gradedPositiveMulQuotient 𝒜 hf₀) :=
    nontrivial_gradedPositiveMulQuotient hneg hf₀ hf.ne_zero
  have hmem (x : (Ideal.span {⟨f, hf₀⟩} : Ideal R₀)) : ((x : R₀) : A) ∈ Ideal.span {f} :=
    (mem_span_singleton_iff_mul_eq_self hf.isIdempotentElem).2 <| congrArg Subtype.val <|
      (mem_span_singleton_iff_mul_eq_self hf₀'.isIdempotentElem).1 x.2
  -- The class map `A₀ f ⟶ A f / A₊f` is `A₀`-linear and onto, since every class has a
  -- degree-zero representative.
  let π : (Ideal.span {⟨f, hf₀⟩} : Ideal R₀) →ₗ[R₀] gradedPositiveMulQuotient 𝒜 hf₀ :=
    -- Both laws reduce to the `A`-linearity of the class map, up to the coercion `A₀ f → A f`.
    { toFun x := gradedPositiveMulQuotientMk hf₀ ⟨_, hmem x⟩
      map_add' x y := by rw [← map_add]; rfl
      map_smul' r x := by
        rw [RingHom.id_apply, Subalgebra.smul_def, ← map_smul]
        rfl }
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨x, hx, rfl⟩ := (mem_gradedPositiveMulQuotient_piece_iff hf₀).1
      ((gradedPositiveMulQuotient_piece_zero_eq_top hneg hf.isIdempotentElem hf₀).ge
        (Submodule.mem_top (x := y)))
    refine ⟨⟨⟨x, hx⟩, (mem_span_singleton_iff_mul_eq_self hf₀'.isIdempotentElem).2
      (Subtype.ext ((mem_span_singleton_iff_mul_eq_self hf.isIdempotentElem).1 x.2))⟩, rfl⟩
  have : IsSimpleModule R₀ (gradedPositiveMulQuotient 𝒜 hf₀) := hf₀'.isSimpleModule_of_surjective hπ
  -- Simplicity over `A₀` gives simplicity over `A`, as `A₀` acts through `A`.
  refine (isSimpleModule_iff_toSpanSingleton_surjective).2 ⟨inferInstance, fun z hz y => ?_⟩
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective R₀ hz y
  exact ⟨r, by simpa [Subalgebra.smul_def] using hr⟩

variable [Module.Finite k A]

/-- **A primitive idempotent with a nonisomorphic left ideal kills the head of `A f`.** If
`f'` acted nontrivially on `A f / A₊f`, then `x ↦ x • (f' • z)` would make `A f'` a second
projective cover of this simple module, and projective covers are unique up to isomorphism. -/
theorem smul_gradedPositiveMulQuotient_eq_zero {f f' : A} (hf : IsPrimitiveIdempotent f)
    (hf₀ : f ∈ 𝒜 0) (hf' : IsPrimitiveIdempotent f')
    (hnoniso : IsEmpty ((Ideal.span {f} : Ideal A) ≃ₗ[A] (Ideal.span {f'} : Ideal A)))
    (z : gradedPositiveMulQuotient 𝒜 hf₀) : f' • z = 0 := by
  by_contra hz
  have := IsArtinianRing.of_finite k A
  have := isSimpleModule_gradedPositiveMulQuotient hneg hf hf₀
  have := nontrivial_gradedPositiveMulQuotient hneg hf₀ hf.ne_zero
  -- The map `A f' ⟶ A f / A₊f`, `x ↦ x • (f' • z)`, is nonzero, hence onto the simple head.
  let g := LinearMap.toSpanSingleton A _ (f' • z) ∘ₗ (Ideal.span {f'} : Ideal A).subtype
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range g)).resolve_left fun h => hz ?_
    have h' : g (spanSingletonGenerator f') ∈ (⊥ : Submodule A _) :=
      h ▸ LinearMap.mem_range_self g _
    rw [Submodule.mem_bot] at h'
    simpa [g, smul_smul, hf'.isIdempotentElem.eq] using h'
  obtain ⟨φ, -⟩ := (isProjectiveCover_gradedPositiveMulQuotientMk hneg hf hf₀).exists_linearEquiv
    (hf'.isProjectiveCover_of_surjective hg)
  exact hnoniso.false φ

/-- The graded dimension of `f' • (A f / A₊f)` vanishes for a primitive idempotent `f'` whose
left ideal is not isomorphic to `A f`. -/
theorem smulGradedDimension_gradedPositiveMulQuotient_eq_zero {f f' : A}
    (hf : IsPrimitiveIdempotent f) (hf₀ : f ∈ 𝒜 0) (hf' : IsPrimitiveIdempotent f')
    (hnoniso : IsEmpty ((Ideal.span {f} : Ideal A) ≃ₗ[A] (Ideal.span {f'} : Ideal A))) :
    (gradedPositiveMulQuotient 𝒜 hf₀).smulGradedDimension f' = 0 := by
  have hbot (p : ℤ) : f' • (gradedPositiveMulQuotient 𝒜 hf₀).grading.piece p = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun y hy => by
      obtain ⟨z, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hy
      exact smul_gradedPositiveMulQuotient_eq_zero hneg hf hf₀ hf' hnoniso z
  ext p
  simp [GradedModuleCat.coeff_smulGradedDimension, hbot]

/-- **The graded dimension of `f • (A f / A₊f)` is the constant `dim_k End_A(A f / A₊f)`**, the
dimension of a division algebra by Schur, which need not be one over a field that does not split
the simple modules. -/
theorem smulGradedDimension_gradedPositiveMulQuotient_self {f : A} (hf : IsPrimitiveIdempotent f)
    (hf₀ : f ∈ 𝒜 0) :
    (gradedPositiveMulQuotient 𝒜 hf₀).smulGradedDimension f =
      LaurentPolynomial.C
        (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 hf₀)) : ℤ) := by
  have := isSimpleModule_gradedPositiveMulQuotient hneg hf hf₀
  exact GradedModuleCat.smulGradedDimension_eq_C_finrank_end_of_isProjectiveCover _
    hf.isIdempotentElem (fun _ hp => gradedPositiveMulQuotient_piece_eq_bot hneg
      hf.isIdempotentElem hf₀ hp) (isProjectiveCover_gradedPositiveMulQuotientMk hneg hf hf₀)

variable {I : Type uI} [Fintype I] {e : I → A}

/-- **The heads of a complete family of primitive idempotents exhaust the simple finite graded
modules** up to shift, over a finite-dimensional nonnegatively graded algebra with semisimple
degree-zero part. -/
theorem isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent
    (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (hprim : ∀ i, IsPrimitiveIdempotent (e i)) :
    IsExhaustiveGradedSimpleFamily fun i =>
      (⟨gradedPositiveMulQuotient 𝒜 (he₀ i),
        gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)⟩ :
        (gradedFiniteModules 𝒜).FullSubcategory) :=
  isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient he he₀ fun i _ =>
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)

end TauCeti
