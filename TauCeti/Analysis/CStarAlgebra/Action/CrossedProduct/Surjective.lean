/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Functoriality
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.DenseRange
public import TauCeti.Analysis.CStarAlgebra.Action.Ideal

/-!
# Surjectivity of full crossed-product maps

An equivariant coefficient homomorphism with dense range induces a surjective homomorphism
of full crossed products. In particular, the canonical map from the full crossed product to
that of an invariant-ideal quotient is onto. This establishes the right endpoint of the
invariant-ideal sequence, without asserting exactness in the middle.

The compact-support convolution map has L¹-dense range. The canonical inclusion into the
full crossed product is L¹-continuous with dense range, so the induced homomorphism has
dense range. Closedness of ranges of C⋆-homomorphisms then gives surjectivity. No continuous
lifting of compactly supported quotient-valued functions is required.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19, for the quotient map in
the invariant-ideal sequence. The proof combines `Hom.denseRange_convolutionMap` with
`NonUnitalStarAlgHom.surjective_of_denseRange`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (μ : Measure G) [μ.IsHaarMeasure]

namespace Hom

/-- A dense-range equivariant coefficient homomorphism induces a surjective full
crossed-product homomorphism. For a surjective coefficient map, use `hφ.denseRange`. -/
theorem surjective_fullCrossedProductMap (φ : Hom α β) (hφ : DenseRange φ) :
    Function.Surjective (φ.fullCrossedProductMap μ) := by
  apply NonUnitalStarAlgHom.surjective_of_denseRange
  have hd := (FullCrossedProduct.denseRange_of (α := β) (μ := μ)).comp
    (φ.denseRange_convolutionMap μ hφ) (FullCrossedProduct.continuous_of (α := β) (μ := μ))
  apply hd.mono
  rintro _ ⟨f, rfl⟩
  exact ⟨FullCrossedProduct.of α μ f, φ.fullCrossedProductMap_of μ f⟩

end Hom

/-- The canonical homomorphism to the full crossed product of an invariant-ideal quotient is
surjective, including for nonunital coefficients and the zero quotient. -/
theorem surjective_fullCrossedProductMap_quotientMkHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Surjective ((α.quotientMkHom I hI).fullCrossedProductMap μ) :=
  (α.quotientMkHom I hI).surjective_fullCrossedProductMap μ
    (α.quotientMkHom_surjective I hI).denseRange

end TauCeti.CStarAction
