/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Basic

/-!
# Local triviality of the sheaf of sections of a holomorphic line bundle

Let `V` be a holomorphic line bundle, with any normed rank-one model `F`, over a complex manifold
`X`. On an open set `U` inside the base set of a holomorphic trivialization `τ`, a scalar model
coordinate `q : F ≃L[ℂ] ℂ` identifies the holomorphic sections of `V` over every open subset of `U`
with holomorphic functions there (`Bundle.Trivialization.holomorphicSectionLinearEquiv`). These
identifications commute with restriction, so the restriction of the sheaf `𝒪(L)` of holomorphic
sections to `U` is isomorphic to the restriction of the holomorphic structure sheaf `𝒪`. This is
the local input for comparing the cohomology of `𝒪(L)` with that of `𝒪` on small opens, for
instance for the acyclicity of coordinate discs on which `L` is trivial.

## Main definitions

* `Bundle.Trivialization.holomorphicSectionSheafIso`: for `U ⊆ τ.baseSet`, the isomorphism
  between the restrictions to `U` of `𝒪(L)` and of `𝒪`, given on sections by the frame coordinate
  `x ↦ q (τ x (s x))`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
-/

public noncomputable section

open Bundle CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace Bundle.Trivialization

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type u} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ω F V I]
  (τ : Trivialization F (π F V)) [τ.IsLinear ℂ] (q : F ≃L[ℂ] ℂ)
  (hτa : τ.toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear X F I ω).maximalAtlas (TotalSpace F V))
  {U : Opens X}

omit [ContMDiffVectorBundle ω F V I] in
/-- An open subset of `U`, read in `X`, lies in `U`. -/
private theorem functor_obj_le (V' : Opens ((Opens.toTopCat (TopCat.of X)).obj U)) :
    (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V' ≤ U := by
  simpa only [Opens.isOpenEmbedding_obj_top] using
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map (homOfLE (le_top : V' ≤ ⊤))).le

/-- **Local triviality of `𝒪(L)`.** On an open set `U` inside the base set of a holomorphic
trivialization `τ` of a line bundle, a scalar model coordinate `q` identifies the restriction to `U`
of the sheaf of holomorphic sections with the restriction to `U` of the holomorphic structure sheaf:
a section `s` corresponds to the holomorphic function `x ↦ q (τ x (s x))`. -/
def holomorphicSectionSheafIso (hτ : (U : Set X) ⊆ τ.baseSet) :
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).sheafPullback (ModuleCat.{u} ℂ)).obj
        (holomorphicSectionSheaf I F V) ≅
      ((Opens.isOpenEmbedding (X := TopCat.of X) U).sheafPullback (ModuleCat.{u} ℂ)).obj
        (holomorphicStructureSheafModules I X) := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun V' ↦ (τ.holomorphicSectionLinearEquiv q hτa
    ((SetLike.coe_subset_coe.2 (functor_obj_le V'.unop)).trans hτ)).toModuleIso) ?_
  intro V₁ V₂ i
  ext s : 2
  exact τ.holomorphicSectionLinearEquiv_restrict q hτa
    ((SetLike.coe_subset_coe.2 (functor_obj_le V₁.unop)).trans hτ)
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map i.unop).le s

/-- The components of the local trivialization are the frame-coordinate equivalences
`Bundle.Trivialization.holomorphicSectionLinearEquiv`. -/
theorem holomorphicSectionSheafIso_hom_app (hτ : (U : Set X) ⊆ τ.baseSet)
    (V' : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (s : (holomorphicSectionSheaf I F V).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V')))
    (hV : ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V' : Set X) ⊆ τ.baseSet) :
    (τ.holomorphicSectionSheafIso q hτa hτ).hom.hom.app (op V') s =
      τ.holomorphicSectionLinearEquiv q hτa hV s :=
  (rfl)

/-- The components of the inverse local trivialization are the inverse frame-coordinate
equivalences. -/
theorem holomorphicSectionSheafIso_inv_app (hτ : (U : Set X) ⊆ τ.baseSet)
    (V' : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : (holomorphicStructureSheafModules I X).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V')))
    (hV : ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V' : Set X) ⊆ τ.baseSet) :
    (τ.holomorphicSectionSheafIso q hτa hτ).inv.hom.app (op V') f =
      (τ.holomorphicSectionLinearEquiv q hτa hV).symm f :=
  (rfl)

end Bundle.Trivialization
