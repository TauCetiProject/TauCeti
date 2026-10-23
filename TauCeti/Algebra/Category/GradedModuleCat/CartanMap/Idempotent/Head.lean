/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis

/-!
# The simple-class basis from graded idempotent heads

For a nonnegatively graded finite-dimensional algebra with split degree-zero part, the heads
of the projectives associated to its complete orthogonal idempotents form an exhaustive family
of graded simples. Their classes form a basis of the graded Grothendieck group over `ℤ[q,q⁻¹]`,
and its coordinates are the graded idempotent coordinates.
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

end Field

end TauCeti
