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

* `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso`: the isomorphism `Γ_φ ≅ Γ_{φ⁻¹}` induced by
  the exchange of factors.
* `AlgebraicGeometry.Scheme.RationalMap.graphSwapIso`: for mutually inverse dominant rational maps
  `f` and `g` of integral separated schemes, the isomorphism `Γ_f ≅ Γ_g` induced by the exchange
  of factors; `graphSwapIso_hom_graphFst` and its companions show it exchanges the projections.

## Main results

* `AlgebraicGeometry.Scheme.PartialIso.ker_graphLift_comp_pullbackSymmetry_hom`: the graph
  morphism of `φ` followed by the exchange of factors has the kernel of the graph morphism of
  `φ.symm`.
* `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso_hom_graphι`: `graphSymmIso` is compatible
  with the closed immersions of the graphs and the exchange of factors.
* `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso_hom_graphFst`,
  `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso_hom_graphSnd`,
  `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso_inv_graphFst`,
  `AlgebraicGeometry.Scheme.PartialIso.graphSymmIso_inv_graphSnd`: `graphSymmIso` exchanges the
  two projections.
* `AlgebraicGeometry.Scheme.RationalMap.ker_graphLift_comp_pullbackSymmetry_hom`,
  `AlgebraicGeometry.Scheme.RationalMap.ker_graphι_comp_pullbackSymmetry_hom`: for mutually
  inverse dominant rational maps `f` and `g` of integral separated schemes, the exchange of
  factors maps `Γ_f` onto `Γ_g`. Such `f` is the rational map of a
  partial isomorphism `φ`
  (`AlgebraicGeometry.Scheme.RationalMap.exists_partialIso_toRationalMap_eq`) and `g` is that of
  `φ.symm`
  (`AlgebraicGeometry.Scheme.PartialIso.eq_symm_toRationalMap_of_comp_eq_id`).
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

/-- The closed immersion of `Γ_φ` followed by the exchange of factors `X × Y ≅ Y × X` has the
kernel of the closed immersion of `Γ_{φ⁻¹}`. -/
theorem ker_graphι_comp_pullbackSymmetry_hom :
    (RationalMap.graphι φ.toRationalMap ≫ (pullbackSymmetry _ _).hom).ker =
      (RationalMap.graphι φ.symm.toRationalMap).ker := by
  rw [Hom.ker_comp, RationalMap.ker_graphι, IdealSheafData.map_ker,
    ker_graphLift_comp_pullbackSymmetry_hom, RationalMap.ker_graphι]

/-- **The graph of the inverse.** The exchange of factors `X × Y ≅ Y × X` induces an isomorphism
of the graph `Γ_φ` of the rational map of a partial isomorphism `φ` with the graph `Γ_{φ⁻¹}` of
the rational map of `φ.symm`. -/
def graphSymmIso : RationalMap.graph φ.toRationalMap ≅ RationalMap.graph φ.symm.toRationalMap :=
  have := IsClosedImmersion.isIso_lift (RationalMap.graphι φ.symm.toRationalMap)
    (RationalMap.graphι φ.toRationalMap ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom φ).symm
  asIso (IsClosedImmersion.lift (RationalMap.graphι φ.symm.toRationalMap)
    (RationalMap.graphι φ.toRationalMap ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom φ).symm.le)

/-- The isomorphism `Γ_φ ≅ Γ_{φ⁻¹}` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_hom_graphι :
    (graphSymmIso φ).hom ≫ RationalMap.graphι φ.symm.toRationalMap =
      RationalMap.graphι φ.toRationalMap ≫ (pullbackSymmetry _ _).hom :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse of `Γ_φ ≅ Γ_{φ⁻¹}` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_inv_graphι :
    (graphSymmIso φ).inv ≫ RationalMap.graphι φ.toRationalMap =
      RationalMap.graphι φ.symm.toRationalMap ≫ (pullbackSymmetry _ _).inv := by
  rw [Iso.inv_comp_eq, graphSymmIso_hom_graphι_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism `Γ_φ ≅ Γ_{φ⁻¹}` carries the first projection of `Γ_{φ⁻¹}` to the second
projection of `Γ_φ`. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_hom_graphFst :
    (graphSymmIso φ).hom ≫ RationalMap.graphFst φ.symm.toRationalMap =
      RationalMap.graphSnd φ.toRationalMap := by
  rw [RationalMap.graphFst, RationalMap.graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The isomorphism `Γ_φ ≅ Γ_{φ⁻¹}` carries the second projection of `Γ_{φ⁻¹}` to the first
projection of `Γ_φ`. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_hom_graphSnd :
    (graphSymmIso φ).hom ≫ RationalMap.graphSnd φ.symm.toRationalMap =
      RationalMap.graphFst φ.toRationalMap := by
  rw [RationalMap.graphFst, RationalMap.graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The inverse of `Γ_φ ≅ Γ_{φ⁻¹}` carries the first projection of `Γ_φ` to the second projection
of `Γ_{φ⁻¹}`. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_inv_graphFst :
    (graphSymmIso φ).inv ≫ RationalMap.graphFst φ.toRationalMap =
      RationalMap.graphSnd φ.symm.toRationalMap := by
  rw [Iso.inv_comp_eq, graphSymmIso_hom_graphSnd]

/-- The inverse of `Γ_φ ≅ Γ_{φ⁻¹}` carries the second projection of `Γ_φ` to the first projection
of `Γ_{φ⁻¹}`. -/
@[reassoc (attr := simp)]
theorem graphSymmIso_inv_graphSnd :
    (graphSymmIso φ).inv ≫ RationalMap.graphSnd φ.toRationalMap =
      RationalMap.graphFst φ.symm.toRationalMap := by
  rw [Iso.inv_comp_eq, graphSymmIso_hom_graphFst]

end PartialIso

namespace RationalMap

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

/-- For mutually inverse dominant rational maps `f` and `g` of integral separated schemes, the
closed immersion of `Γ_f` followed by the exchange of factors `X × Y ≅ Y × X` has the kernel of
the closed immersion of `Γ_g`. -/
theorem ker_graphι_comp_pullbackSymmetry_hom (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X)
    [g.IsDominant] (h : f.comp g = RationalMap.id X) (h' : g.comp f = RationalMap.id Y) :
    (graphι f ≫ (pullbackSymmetry _ _).hom).ker = (graphι g).ker := by
  rw [Hom.ker_comp, ker_graphι, IdealSheafData.map_ker,
    ker_graphLift_comp_pullbackSymmetry_hom f g h h', ker_graphι]

/-- **The graph of the inverse of a birational map.** For mutually inverse dominant rational maps
`f : X ⤏ Y` and `g : Y ⤏ X` of integral separated schemes, the exchange of factors
`X × Y ≅ Y × X` induces an isomorphism `Γ_f ≅ Γ_g`. -/
def graphSwapIso (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X) [g.IsDominant]
    (h : f.comp g = RationalMap.id X) (h' : g.comp f = RationalMap.id Y) : graph f ≅ graph g :=
  have := IsClosedImmersion.isIso_lift (graphι g) (graphι f ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom f g h h').symm
  asIso (IsClosedImmersion.lift (graphι g) (graphι f ≫ (pullbackSymmetry _ _).hom)
    (ker_graphι_comp_pullbackSymmetry_hom f g h h').symm.le)

variable (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X) [g.IsDominant] (h : f.comp g = RationalMap.id X)
  (h' : g.comp f = RationalMap.id Y)

/-- The isomorphism `Γ_f ≅ Γ_g` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphι :
    (graphSwapIso f g h h').hom ≫ graphι g = graphι f ≫ (pullbackSymmetry _ _).hom :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse of `Γ_f ≅ Γ_g` is the exchange of factors on the ambient products. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphι :
    (graphSwapIso f g h h').inv ≫ graphι f = graphι g ≫ (pullbackSymmetry _ _).inv := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphι_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism `Γ_f ≅ Γ_g` carries the first projection of `Γ_g` to the second projection
of `Γ_f`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphFst : (graphSwapIso f g h h').hom ≫ graphFst g = graphSnd f := by
  rw [graphFst, graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The isomorphism `Γ_f ≅ Γ_g` carries the second projection of `Γ_g` to the first projection
of `Γ_f`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_hom_graphSnd : (graphSwapIso f g h h').hom ≫ graphSnd g = graphFst f := by
  rw [graphFst, graphSnd, graphClosureFst_def, graphClosureSnd_def]
  simp

/-- The inverse of `Γ_f ≅ Γ_g` carries the first projection of `Γ_f` to the second projection
of `Γ_g`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphFst : (graphSwapIso f g h h').inv ≫ graphFst f = graphSnd g := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphSnd]

/-- The inverse of `Γ_f ≅ Γ_g` carries the second projection of `Γ_f` to the first projection
of `Γ_g`. -/
@[reassoc (attr := simp)]
theorem graphSwapIso_inv_graphSnd : (graphSwapIso f g h h').inv ≫ graphSnd f = graphFst g := by
  rw [Iso.inv_comp_eq, graphSwapIso_hom_graphFst]

end AlgebraicGeometry.Scheme.RationalMap
