/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.EmptyOpen

/-!
# Examples: morphisms that are not the `p` of a square with empty open part

An elementary distinguished square `Q` over a reduced scheme with empty open part `U` has `p` an
isomorphism (`ElementaryDistinguishedSquare.isIso_p_of_isEmpty`). Hence:

* for a field extension `K → L` of degree two, for instance `ℝ → ℂ`, no such `Q` over `Spec K` has
  `p` isomorphic over `Spec K` to `Spec L ⟶ Spec K` (an étale morphism when the extension is
  separable);
* over `X = Spec ℝ`, no such `Q` has `p` isomorphic over `X` to the morphism
  `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`, which has two points over the single point of `X`: the structure
  rejects it, although it has exactly one point with residue field `ℝ` over that point.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample

open TauCeti.AlgebraicGeometry.Scheme

universe u

/-- **An extension of degree other than one is not distinguished with empty `U`.** For an algebra
`K → L` over a nontrivial reduced commutative ring `K` with `finrank K L ≠ 1` (for instance a field
extension of degree two), no elementary distinguished square over `Spec K` with empty open part
has `p` isomorphic over `Spec K` to `Spec L ⟶ Spec K`, since that morphism is not an
isomorphism. -/
theorem isEmpty_iso_SpecMap_of_finrank_ne_one (K L : Type u) [CommRing K] [IsReduced K]
    [Nontrivial K] [CommRing L] [Algebra K L] (h : Module.finrank K L ≠ 1)
    (Q : ElementaryDistinguishedSquare (Spec (.of K))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap K L)) :=
  Q.isEmpty_iso_of_not_isIso _ fun hi ↦
    h (Module.finrank_of_bijective_algebraMap (isIso_SpecMap_iff.1 hi))

/-- The degree-two case. -/
example (K L : Type u) [Field K] [Field L] [Algebra K L] (h : Module.finrank K L = 2)
    (Q : ElementaryDistinguishedSquare (Spec (.of K))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap K L)) :=
  isEmpty_iso_SpecMap_of_finrank_ne_one K L (by omega) Q

/-- The case `ℝ → ℂ`. -/
example (Q : ElementaryDistinguishedSquare (Spec (.of ℝ))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.algebraMap ℝ ℂ)) :=
  isEmpty_iso_SpecMap_of_finrank_ne_one ℝ ℂ (by rw [Complex.finrank_real_complex]; omega) Q

/-- The morphism `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`: the identity on `Spec ℝ` and `Spec ℂ ⟶ Spec ℝ`. -/
noncomputable abbrev realComplexToReal :
    Spec (.of ℝ) ⨿ Spec (.of ℂ) ⟶ Spec (.of ℝ) :=
  coprod.desc (𝟙 _) (Spec.algebraMap ℝ ℂ)

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` is not an isomorphism: it identifies the points of the two
components. -/
theorem not_isIso_realComplexToReal : ¬ IsIso realComplexToReal := by
  intro _
  obtain ⟨a⟩ : Nonempty (Spec (.of ℝ)) := inferInstance
  obtain ⟨b⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  exact inl_ne_inr _ _ a b (realComplexToReal.isOpenEmbedding.injective (Subsingleton.elim _ _))

/-- **`Spec ℝ ⨿ Spec ℂ` is rejected.** No elementary distinguished square over `Spec ℝ` with empty
open part has `p` isomorphic over `Spec ℝ` to `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`. -/
theorem isEmpty_iso_realComplexToReal (Q : ElementaryDistinguishedSquare (Spec (.of ℝ)))
    [IsEmpty Q.U] : IsEmpty (Over.mk Q.p ≅ Over.mk realComplexToReal) :=
  Q.isEmpty_iso_of_not_isIso _ not_isIso_realComplexToReal

end TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample
