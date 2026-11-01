/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.PrimitiveHead
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis

/-!
# The simple-class basis from graded idempotent heads

For a nonnegatively graded finite-dimensional algebra with split degree-zero part, the heads
of the projectives associated to its complete orthogonal idempotents form an exhaustive family
of graded simples. Their classes form a basis of the graded Grothendieck group over `ℤ[q,q⁻¹]`,
and its coordinates are the graded idempotent coordinates.

Over a field that does not split the simple modules, take instead a degree-zero part `A₀` that is
a semisimple ring and a complete family of orthogonal primitive idempotents `eᵢ` of degree zero
whose left ideals `A eᵢ` are pairwise nonisomorphic. The heads `Sᵢ = A eᵢ / A₊eᵢ` again give a
basis of the graded Grothendieck group. Now the `eᵢ`-coordinate is `dim_k End_A(Sᵢ)` times the
`i`th basis coordinate, as in the ungraded `TauCeti.simpleClassBasis` over a general field. The
hypotheses on the `eᵢ` are those of the projective basis
`TauCeti.gradedIdempotentProjectiveBasisOfPrimitive`.

## Main definitions

* `TauCeti.gradedIdempotentHeadBasis`: the basis `[Sᵢ]` for a split degree-zero part.
* `TauCeti.gradedIdempotentHeadBasisOfPrimitive`: the basis `[Sᵢ]` for primitive idempotents
  over a semisimple degree-zero part.

## Main results

* `TauCeti.gradedIdempotentHeadBasis_repr_apply`: in the split case the coordinates are the
  idempotent coordinates.
* `TauCeti.gradedIdempotentCoordinate_eq_mul_gradedIdempotentHeadBasisOfPrimitive_repr`: in
  general the `eᵢ`-coordinate is `dim_k End_A(Sᵢ)` times the `i`th coordinate.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA uI

section Field

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) (hne : ∀ i, e i ≠ 0)

/-- The heads `Sᵢ` of the `A eᵢ`, as finite graded modules. -/
private abbrev headFamily (i : I) : (gradedFiniteModules 𝒜).FullSubcategory :=
  ⟨gradedPositiveMulQuotient 𝒜 (he₀ i), gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)⟩

/-! ### The simple-class basis -/

variable [Module.Finite k A]

include hneg he hspan hne in
/-- **The graded heads of the `A eᵢ` form a basis of `G₀^gr(mod A)`** over `ℤ[q,q⁻¹]`, for a
nonnegatively graded finite-dimensional algebra whose degree-zero piece is spanned by a complete
family of orthogonal nonzero idempotents `eᵢ`. Its basis vector at `i` is the class `[Sᵢ]`. -/
def gradedIdempotentHeadBasis :
    Module.Basis I (LaurentPolynomial ℤ) (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :=
  gradedSimpleClassBasis (fun i => headFamily he₀ i) he.idem he₀
    (fun j i hji => by
      classical
      simpa [hji] using smulGradedDimension_gradedIdempotentHead
        hneg he.toOrthogonalIdempotents he₀ hspan j i (hne i))
    (fun i => by
      classical
      simpa using smulGradedDimension_gradedIdempotentHead
        hneg he.toOrthogonalIdempotents he₀ hspan i i (hne i))
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan)

/-- The basis vector of `TauCeti.gradedIdempotentHeadBasis` at `i` is the class `[Sᵢ]` of the
graded head of `A eᵢ`. -/
@[simp]
theorem gradedIdempotentHeadBasis_apply (i : I) :
    gradedIdempotentHeadBasis hneg he he₀ hspan hne i =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨gradedPositiveMulQuotient 𝒜 (he₀ i),
          gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)⟩ := by
  exact gradedSimpleClassBasis_apply _ _ _ _ _ _ i

/-- **The coordinates in the basis `[Sᵢ]` are the idempotent coordinates**: the `i`th coordinate
of the class of `M` is the graded dimension `∑ₚ dim_k(eᵢ • Mₚ) qᵖ`. -/
@[simp]
theorem gradedIdempotentHeadBasis_repr_apply
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (i : I) :
    (gradedIdempotentHeadBasis hneg he he₀ hspan hne).repr x i =
      gradedIdempotentCoordinate (he.idem i) (he₀ i) x := by
  exact gradedSimpleClassBasis_repr_apply _ _ _ _ _ _ x i

/-! ### Primitive idempotents over a semisimple degree-zero part -/

section Primitive

variable [IsSemisimpleRing (𝒜 0)] (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

include hneg he hprim hnoniso in
/-- **The graded heads of primitive idempotents form a basis of `G₀^gr(mod A)`** over
`ℤ[q,q⁻¹]`, for a nonnegatively graded finite-dimensional algebra whose degree-zero part is a
semisimple ring, and a complete family of orthogonal primitive idempotents `eᵢ` of degree zero
whose left ideals `A eᵢ` are pairwise nonisomorphic. Its basis vector at `i` is the class `[Sᵢ]`
of `Sᵢ = A eᵢ / A₊eᵢ`. The field need not split the simple modules. -/
def gradedIdempotentHeadBasisOfPrimitive :
    Module.Basis I (LaurentPolynomial ℤ) (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :=
  gradedSimpleClassBasisOfNeZero (fun i => headFamily he₀ i) he.idem he₀
    (fun _ _ hij => smulGradedDimension_gradedPositiveMulQuotient_eq_zero hneg (hprim _) (he₀ _)
      (hprim _) (hnoniso hij.symm))
    (fun i => smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero)
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)

/-- The basis vector of `TauCeti.gradedIdempotentHeadBasisOfPrimitive` at `i` is the class `[Sᵢ]`
of `Sᵢ = A eᵢ / A₊eᵢ`. -/
@[simp]
theorem gradedIdempotentHeadBasisOfPrimitive_apply (i : I) :
    gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso i =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨gradedPositiveMulQuotient 𝒜 (he₀ i),
          gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)⟩ :=
  gradedSimpleClassBasisOfNeZero_apply _ _ _ _ _ _ i

/-- **The idempotent coordinates are the basis coordinates scaled by `dim_k End_A(Sᵢ)`**: the
`eᵢ`-coordinate of `x`, the graded dimension `∑ₚ dim_k(eᵢ • Mₚ) qᵖ` on the class of `M`, is
`dim_k End_A(Sᵢ)` times the `i`th coordinate of `x` in the basis `[Sᵢ]`. -/
theorem gradedIdempotentCoordinate_eq_mul_gradedIdempotentHeadBasisOfPrimitive_repr
    (x : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (i : I) :
    gradedIdempotentCoordinate (he.idem i) (he₀ i) x =
      LaurentPolynomial.C
          (Module.finrank k (Module.End A (gradedPositiveMulQuotient 𝒜 (he₀ i))) : ℤ) *
        (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso).repr x i := by
  rw [gradedIdempotentHeadBasisOfPrimitive,
    gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr fun i => headFamily he₀ i]
  exact congrArg (· * _) (smulGradedDimension_gradedPositiveMulQuotient_self hneg (hprim i) (he₀ i))

end Primitive

end Field

end TauCeti
