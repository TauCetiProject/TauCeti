/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Graph.Basic
public import TauCeti.AlgebraicGeometry.Birational.InversePartialIso
public import TauCeti.AlgebraicGeometry.Birational.PartialIso

/-!
# The graph of the inverse of a birational map

Let `φ` be a partial isomorphism of reduced schemes `X` and `Y` (Mathlib's
`AlgebraicGeometry.Scheme.PartialIso`), an isomorphism `φ : U ≅ V` of dense opens. The exchange of
factors `X × Y ≅ Y × X` maps the graph `Γ_φ` of the rational map of `φ` onto the graph `Γ_{φ⁻¹}`
of the rational map of `φ.symm`, exchanging the two projections.

The proof compares kernels. The graph morphism `(ι_U, ι_V ∘ φ) : U → X × Y` followed by the
exchange of factors is `(ι_V ∘ φ, ι_U) = (ι_V, ι_U ∘ φ⁻¹) ∘ φ`, the isomorphism `φ` followed by the
graph morphism of `φ.symm` on `V`. Composing with an isomorphism on the source does not change
the kernel, and the graphs of `φ` and `φ.symm` do not depend on the representative
(`AlgebraicGeometry.Scheme.RationalMap.ker_opensGraph_eq_ker_graphLift`), so the closed
immersion `Γ_φ → X × Y → Y × X` has the same kernel as `Γ_{φ⁻¹} → Y × X`. Two closed immersions
with the same kernel are isomorphic over the target (Mathlib's `IsClosedImmersion.isIso_lift`).

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.graphSwapIso`: for rational maps `f : X ⤏ Y` and
  `g : Y ⤏ X` such that the exchange of factors maps `Γ_f` onto `Γ_g` (as an equality of kernels),
  the isomorphism `Γ_f ≅ Γ_g` induced by the exchange of factors; `graphSwapIso_hom_graphι`,
  `graphSwapIso_hom_graphFst` and their companions show it is compatible with the closed
  immersions and exchanges the projections.

## Main results

* `AlgebraicGeometry.Scheme.PartialIso.ker_graphLift_comp_pullbackSymmetry_hom`: the graph
  morphism of a partial isomorphism `φ` followed by the exchange of factors has the kernel of the
  graph morphism of `φ.symm`, so `graphSwapIso` gives `Γ_φ ≅ Γ_{φ⁻¹}`.
* `AlgebraicGeometry.Scheme.RationalMap.ker_graphLift_comp_pullbackSymmetry_hom`: for mutually
  inverse dominant rational maps `f` and `g` of integral separated schemes, the exchange of
  factors maps `Γ_f` onto `Γ_g`. Such `f` is the rational map of a
  partial isomorphism `φ`
  (`AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`) and `g` is that of
  `φ.symm`
  (`AlgebraicGeometry.Scheme.PartialIso.eq_symm_toRationalMap_of_comp_eq_id`).
* `AlgebraicGeometry.Scheme.RationalMap.ker_graphι_comp_pullbackSymmetry_hom`: the same kernel
  equality for the closed immersions of the graphs.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

universe u

namespace PartialIso

variable {X Y : Scheme.{u}} (φ : X.PartialIso Y)

/-- The graph morphism `(ι_U, ι_V ∘ φ) : U → X × Y` of a partial isomorphism `φ : U ≅ V`, followed
by the exchange of factors, is `φ` followed by the graph morphism `(ι_V, ι_U ∘ φ⁻¹) : V → Y × X` of
`φ.symm`. -/
@[reassoc]
theorem opensGraph_comp_pullbackSymmetry_hom :
    opensGraph (terminal.from X) (terminal.from Y) φ.source (φ.iso.hom ≫ φ.target.ι)
        (terminal.hom_ext _ _) ≫ (pullbackSymmetry _ _).hom =
      φ.iso.hom ≫ opensGraph (terminal.from Y) (terminal.from X) φ.target
        (φ.iso.inv ≫ φ.source.ι) (terminal.hom_ext _ _) := by
  apply pullback.hom_ext <;> simp

variable [IsReduced X] [IsReduced Y]

/-- The graph morphism `γ_φ` of the rational map of a partial isomorphism `φ`, followed by the
exchange of factors `X × Y ≅ Y × X`, has the kernel of the graph morphism of the rational map of
`φ.symm`: the exchange of factors maps `Γ_φ` onto `Γ_{φ⁻¹}`. -/
theorem ker_graphLift_comp_pullbackSymmetry_hom :
    (RationalMap.graphLift φ.toRationalMap ≫ (pullbackSymmetry _ _).hom).ker =
      (RationalMap.graphLift φ.symm.toRationalMap).ker := by
  rw [Hom.ker_comp, ← RationalMap.ker_opensGraph_eq_ker_graphLift _ φ.toPartialMap rfl,
    ← RationalMap.ker_opensGraph_eq_ker_graphLift _ φ.symm.toPartialMap rfl, ← Hom.ker_comp]
  exact (congrArg Hom.ker (opensGraph_comp_pullbackSymmetry_hom φ)).trans
    (Hom.ker_comp_of_isIso _ _)

end PartialIso

namespace RationalMap

section Swap

variable {X Y : Scheme.{u}} {f : X ⤏ Y} {g : Y ⤏ X}

/-- If the graph morphism `γ_f` followed by the exchange of factors `X × Y ≅ Y × X` has the kernel
of `γ_g`, then so does the closed immersion of `Γ_f` followed by the exchange of factors, with
the closed immersion of `Γ_g`. -/
theorem ker_graphι_comp_pullbackSymmetry_hom
    (hk : (graphLift f ≫ (pullbackSymmetry _ _).hom).ker = (graphLift g).ker) :
    (graphι f ≫ (pullbackSymmetry _ _).hom).ker = (graphι g).ker := by
  rw [Hom.ker_comp, ker_graphι, IdealSheafData.map_ker, hk, ker_graphι]

/-- If the exchange of factors `X × Y ≅ Y × X` maps the graph `Γ_f` of `f : X ⤏ Y` onto the graph
`Γ_g` of `g : Y ⤏ X`, that is, the graph morphism `γ_f` followed by the exchange of factors has
the kernel of `γ_g`, then the exchange of factors induces an isomorphism `Γ_f ≅ Γ_g`. For a
partial isomorphism `φ`, take `hk := φ.ker_graphLift_comp_pullbackSymmetry_hom`; for mutually
inverse dominant rational maps of integral separated schemes, take
`hk := ker_graphLift_comp_pullbackSymmetry_hom f g h h'`. -/
def graphSwapIso (hk : (graphLift f ≫ (pullbackSymmetry _ _).hom).ker = (graphLift g).ker) :
    graph f ≅ graph g :=
  have := IsClosedImmersion.isIso_lift (graphι g) (graphι f ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom hk).symm
  asIso (IsClosedImmersion.lift (graphι g) (graphι f ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom hk).symm.le)

variable (hk : (graphLift f ≫ (pullbackSymmetry _ _).hom).ker = (graphLift g).ker)

/-- The isomorphism `Γ_f ≅ Γ_g` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphι :
    (graphSwapIso hk).hom ≫ graphι g = graphι f ≫ (pullbackSymmetry _ _).hom :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse of `Γ_f ≅ Γ_g` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphι :
    (graphSwapIso hk).inv ≫ graphι f = graphι g ≫ (pullbackSymmetry _ _).inv := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphι_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism `Γ_f ≅ Γ_g` carries the first projection of `Γ_g` to the second projection
of `Γ_f`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphFst : (graphSwapIso hk).hom ≫ graphFst g = graphSnd f := by
  rw [graphFst, graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The isomorphism `Γ_f ≅ Γ_g` carries the second projection of `Γ_g` to the first projection
of `Γ_f`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphSnd : (graphSwapIso hk).hom ≫ graphSnd g = graphFst f := by
  rw [graphFst, graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The inverse of `Γ_f ≅ Γ_g` carries the first projection of `Γ_f` to the second projection
of `Γ_g`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphFst : (graphSwapIso hk).inv ≫ graphFst f = graphSnd g := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphSnd]

/-- The inverse of `Γ_f ≅ Γ_g` carries the second projection of `Γ_f` to the first projection
of `Γ_g`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphSnd : (graphSwapIso hk).inv ≫ graphSnd f = graphFst g := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphFst]

end Swap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]

/-- **The graph of the inverse of a birational map.** For mutually inverse dominant rational maps
`f : X ⤏ Y` and `g : Y ⤏ X` of integral separated schemes, the exchange of factors
`X × Y ≅ Y × X` maps the graph `Γ_f` onto the graph `Γ_g`: the graph morphism of `f` followed by
the exchange of factors has the kernel of the graph morphism of `g`. -/
theorem ker_graphLift_comp_pullbackSymmetry_hom (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X)
    [g.IsDominant] (h : f.comp g = RationalMap.id X) (h' : g.comp f = RationalMap.id Y) :
    (graphLift f ≫ (pullbackSymmetry _ _).hom).ker = (graphLift g).ker := by
  obtain ⟨φ, rfl⟩ := f.exists_partialIso_toRationalMap_eq g h h'
  obtain rfl := φ.eq_symm_toRationalMap_of_comp_eq_id g h
  exact φ.ker_graphLift_comp_pullbackSymmetry_hom

end AlgebraicGeometry.Scheme.RationalMap
