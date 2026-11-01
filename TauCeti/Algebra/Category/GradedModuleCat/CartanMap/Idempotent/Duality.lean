/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Duality
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
import TauCeti.Algebra.Polynomial.Laurent.Units

/-!
# Projective/simple q-Euler duality over a nonsplitting field

Let `A` be a nonnegatively graded finite-dimensional algebra over a field `k` whose degree-zero
part is a semisimple ring, and let `eᵢ` be a complete family of orthogonal primitive idempotents of
degree zero whose left ideals `A eᵢ` are pairwise nonisomorphic. The classes `[A eᵢ]` form a
Laurent basis of `K₀^gr(proj A)` (`TauCeti.gradedIdempotentProjectiveBasisOfPrimitive`) and the
classes of the heads `Sᵢ = A eᵢ / A₊eᵢ` form a Laurent basis of `G₀^gr(mod A)`
(`TauCeti.gradedIdempotentHeadBasisOfPrimitive`).

In these bases the projective/module q-Euler pairing is diagonal with entries the constants
`dim_k End_A(Sᵢ)`, the dimensions of the Schur division algebras. Consequently both of its radicals
vanish, but it identifies either Grothendieck group with the dual of the other exactly when every
`Sᵢ` has `dim_k End_A(Sᵢ) = 1`, that is, when `k` splits the simple modules. This is the graded
form of the general-field correction to the duality between projective covers and simple modules:
nondegeneracy survives over every field, while perfectness of the raw q-Euler pairing does not.

## Main results

* `TauCeti.gradedProjectiveExtEuler_nondegenerate_of_isPrimitiveIdempotent`: both radicals of the
  q-Euler pairing vanish.
* `TauCeti.gradedProjectiveExtEuler_bijective_iff_finrank_end_eq_one` and
  `TauCeti.gradedProjectiveExtEuler_flip_bijective_iff_finrank_end_eq_one`: the q-Euler pairing
  identifies either side with the dual of the other exactly when `dim_k End_A(Sᵢ) = 1` for
  every `i`.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Proposition 7.4.1, for
  the factor `dim_k End_A(Sᵢ)` in the pairing of projective covers with simples.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Sections 2.2 and
  3.1--3.2, for the q-Euler form and its duals.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsSemisimpleRing (𝒜 0)]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

omit [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)] in
include hneg in
/-- The diagonal graded dimension `gdim(f • A f / A₊f) = dim_k End_A(A f / A₊f)` of a primitive
idempotent `f` of degree zero is a unit of `ℤ[q,q⁻¹]` exactly when it is `1`. -/
private theorem isUnit_smulGradedDimension_gradedPositiveMulQuotient_iff {f : A}
    (hf : IsPrimitiveIdempotent f) (hf₀ : f ∈ 𝒜 0) :
    IsUnit ((gradedPositiveMulQuotient 𝒜 hf₀).smulGradedDimension f) ↔
      Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 hf₀)) = 1 := by
  rw [smulGradedDimension_gradedPositiveMulQuotient_self hneg hf hf₀, isUnit_C, Int.isUnit_iff]
  -- A natural number is `1` exactly when its integer cast is `1` or `-1`.
  omega

include hneg he he₀ hI hprim hnoniso

/-- **The projective/module q-Euler pairing is nondegenerate over every field**: for primitive
idempotents over a semisimple degree-zero part, the only projective class pairing to zero with
every finite graded module is zero, and dually. -/
theorem gradedProjectiveExtEuler_nondegenerate_of_isPrimitiveIdempotent :
    (gradedProjectiveExtEuler 𝒜).Nondegenerate :=
  gradedProjectiveExtEuler_nondegenerate _ he.idem he₀ hI
    (fun _ _ hij => smulGradedDimension_gradedPositiveMulQuotient_eq_zero hneg (hprim _) (he₀ _)
      (hprim _) (hnoniso hij.symm))
    _ (gradedIdempotentProjectiveBasisOfPrimitive_apply he he₀ hI hprim hnoniso)
    (fun i => smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero)
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)

/-- **The q-Euler pairing identifies the projective group with the dual of the module group
exactly over a splitting field.** For primitive idempotents over a semisimple degree-zero part,
every linear functional on `G₀^gr(mod A)` is `χ_q(x, -)` for exactly one projective class `x` if
and only if every head `Sᵢ = A eᵢ / A₊eᵢ` has `dim_k End_A(Sᵢ) = 1`. -/
theorem gradedProjectiveExtEuler_bijective_iff_finrank_end_eq_one :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) ↔
      ∀ i, Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) = 1 := by
  rw [gradedProjectiveExtEuler_bijective_iff _ he.idem he₀ hI
    (fun _ _ hij => smulGradedDimension_gradedPositiveMulQuotient_eq_zero hneg (hprim _) (he₀ _)
      (hprim _) (hnoniso hij.symm))
    _ (gradedIdempotentProjectiveBasisOfPrimitive_apply he he₀ hI hprim hnoniso)
    (fun i => smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero)
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)]
  exact forall_congr' fun i => isUnit_smulGradedDimension_gradedPositiveMulQuotient_iff hneg
    (hprim i) (he₀ i)

/-- **The q-Euler pairing identifies the module group with the semilinear dual of the projective
group exactly over a splitting field.** For primitive idempotents over a semisimple degree-zero
part, every `q ↦ q⁻¹` semilinear functional on `K₀^gr(proj A)` is `χ_q(-, y)` for exactly one
module class `y` if and only if every head `Sᵢ = A eᵢ / A₊eᵢ` has `dim_k End_A(Sᵢ) = 1`. -/
theorem gradedProjectiveExtEuler_flip_bijective_iff_finrank_end_eq_one :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip ↔
      ∀ i, Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) = 1 := by
  rw [gradedProjectiveExtEuler_flip_bijective_iff _ he.idem he₀ hI
    (fun _ _ hij => smulGradedDimension_gradedPositiveMulQuotient_eq_zero hneg (hprim _) (he₀ _)
      (hprim _) (hnoniso hij.symm))
    _ (gradedIdempotentProjectiveBasisOfPrimitive_apply he he₀ hI hprim hnoniso)
    (fun i => smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero)
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)]
  exact forall_congr' fun i => isUnit_smulGradedDimension_gradedPositiveMulQuotient_iff hneg
    (hprim i) (he₀ i)

end TauCeti
