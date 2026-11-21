/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Range
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing
public import TauCeti.Topology.Category.TopCat.Subspace

/-!
# Relative smooth singular chains

Let `X` be a Hausdorff `σ`-compact smooth manifold over a finite-dimensional real model with
corners `I`, and let `W ⊆ X` be open. This file compares the smooth singular chains of `X` relative
to those with image in `W` with the singular chains of `X` relative to those with image in `W`.

Both sides are pairs of simplicial sets (`SSetPair`):

* `TauCeti.singularPairIn X W` is the singular simplicial set of `X` together with its subcomplex
  `TopCat.smallSingularSubcomplex` of the simplices with image in `W`;
* `TauCeti.smoothPairIn I X W` is the smooth singular subcomplex
  `TauCeti.smoothSingularSubcomplex I X` together with its intersection with that subcomplex;
* `TauCeti.smoothPairToSingular I X W` is the inclusion of the first pair into the second.

Their relative chain complexes (`SSetPair.chainComplex`) are `C^∞(X) / C^∞(W)` and `C(X) / C(W)`.
The main theorem, `TauCeti.quasiIso_smoothPairToSingular`, says that the inclusion is a
quasi-isomorphism on relative chains, with coefficients in any abelian category in which countable
coproducts are exact. By the five lemma for pairs (`SSetPair.quasiIso_chainComplexMap`) it reduces
to the absolute smoothing theorem (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`)
on `X` and on the open subset `W`: a singular simplex of `X` with image in `W` is a singular simplex
of `W` (`TopCat.range_toSSet_map_subtypeVal`), and it is smooth in `X` exactly when it is smooth in
`W` (`TauCeti.range_smoothSingularSubcomplex_ι_comp_subtypeVal`).

For projective coefficients, for instance `ℝ`, every term of both relative chain complexes is
projective, so the comparison upgrades to a chain homotopy equivalence
(`TauCeti.smoothPairChainHomotopyEquiv`), and dually restriction of relative singular cochains to
relative smooth cochains is a quasi-isomorphism
(`TauCeti.quasiIso_cochainComplexMap_smoothPairToSingular`). The pair `singularPairIn X W` is
isomorphic to the singular pair `TopPair.toSSetPair.obj (TopPair.ofSubset W)` of the topological
pair `(X, W)` (`TauCeti.singularPairInIso`), so the relative singular cochains of `(X, W)`
(`TopPair.singularCochainComplex`) restrict quasi-isomorphically to the relative smooth cochains
(`TauCeti.quasiIso_cochainComplexMap_smoothPairToSingular_comp_singularPairInIso_inv`).

Both pairs are functorial in maps of pairs (`TauCeti.singularPairInMap` for continuous maps,
`TauCeti.smoothPairInMap` for smooth maps; see `TauCeti.singularPairInMap_comp` and
`TauCeti.smoothPairInMap_comp`), and the inclusion of the smooth pair into the singular pair is
natural in smooth maps of pairs (`TauCeti.smoothPairInMap_comp_smoothPairToSingular`); enlargement
of `W` is the case of the identity map.

These relative chains are the domain of relative integration of differential forms over smooth
simplices, which compares the relative de Rham complex of an open pair with relative singular
cohomology.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 (the absolute
  smoothing theorem).
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I–III (relative
  chains and the five lemma).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

section Defs

variable (X : Type u) [TopologicalSpace X] (W : Set X)

/-- The singular simplicial set of `X` together with its subcomplex of the simplices with image in
`W`. Its relative chain complex is `C(X) / C(W)`. -/
abbrev singularPairIn : SSetPair.{u} :=
  ((TopCat.of X).smallSingularSubcomplex fun _ : Unit ↦ W).pair

/-- The pair `singularPairIn X W` is the singular pair of the topological pair `(X, W)`: a singular
simplex of `W` is a singular simplex of `X` with image in `W`. -/
def singularPairInIso :
    TopPair.toSSetPair.obj (TopPair.ofSubset (X := TopCat.of X) W) ≅ singularPairIn X W :=
  MorphismProperty.Arrow.isoMk (TopCat.singularSubspaceIso (X := TopCat.of X) W) (Iso.refl _) (by
    rw [TopCat.singularSubspaceIso_hom]
    exact (TopCat.toSmallSingularSubcomplex_ι _ _).trans (Category.comp_id _).symm)

/-- On the subspaces, `singularPairInIso` is `TopCat.singularSubspaceIso`. -/
@[simp]
theorem singularPairInIso_hom_left :
    (singularPairInIso X W).hom.left = (TopCat.singularSubspaceIso (X := TopCat.of X) W).hom := by
  rw [singularPairInIso]
  rfl

/-- On the ambient simplicial sets, `singularPairInIso` is the identity. -/
@[simp]
theorem singularPairInIso_hom_right : (singularPairInIso X W).hom.right = 𝟙 _ := by
  rw [singularPairInIso]
  rfl

end Defs

section SmoothDefs

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (X : Type u) [TopologicalSpace X] [ChartedSpace H X] (W : Set X)

/-- The smooth singular subcomplex of `X` together with its subcomplex of the smooth simplices with
image in `W`. Its relative chain complex is `C^∞(X) / C^∞(W)`. -/
abbrev smoothPairIn : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I X ⊓
    (TopCat.of X).smallSingularSubcomplex (fun _ : Unit ↦ W) ≤ smoothSingularSubcomplex I X))

/-- The inclusion of the smooth pair `smoothPairIn I X W` into the singular pair
`singularPairIn X W`. -/
def smoothPairToSingular : smoothPairIn I X W ⟶ singularPairIn X W :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_right) (smoothSingularSubcomplex I X).ι (by rfl)

/-- On the subspaces, `smoothPairToSingular` is the inclusion of the smooth simplices with image in
`W` into all simplices with image in `W`. -/
@[simp]
theorem smoothPairToSingular_left :
    (smoothPairToSingular I X W).left = SSet.Subcomplex.homOfLE inf_le_right :=
  (rfl)

/-- On the ambient simplicial sets, `smoothPairToSingular` is the inclusion of the smooth singular
subcomplex. -/
@[simp]
theorem smoothPairToSingular_right :
    (smoothPairToSingular I X W).right = (smoothSingularSubcomplex I X).ι :=
  (rfl)

end SmoothDefs

section Naturality

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {Y : Type u} [TopologicalSpace Y] [ChartedSpace H' Y]
  {W : Set X} {W' : Set Y}

/-- The map of singular pairs induced by a continuous map `φ : X → Y` carrying `W` into `W'`. -/
def singularPairInMap (φ : C(X, Y)) (hφ : Set.MapsTo φ W W') :
    singularPairIn X W ⟶ singularPairIn Y W' :=
  SSetPair.homMk
    (TopCat.smallSingularSubcomplexMap _ _ (TopCat.ofHom φ) id fun _ ↦ hφ)
    (TopCat.toSSet.map (TopCat.ofHom φ))
    (TopCat.smallSingularSubcomplexMap_ι _ _ _ _ _)

/-- On the ambient simplicial sets, `singularPairInMap` is the map of singular simplicial sets. -/
@[simp]
theorem singularPairInMap_right (φ : C(X, Y)) (hφ : Set.MapsTo φ W W') :
    (singularPairInMap φ hφ).right = TopCat.toSSet.map (TopCat.ofHom φ) :=
  (rfl)

/-- On the subspaces, `singularPairInMap` is the map of small singular subcomplexes. -/
@[simp]
theorem singularPairInMap_left (φ : C(X, Y)) (hφ : Set.MapsTo φ W W') :
    (singularPairInMap φ hφ).left =
      TopCat.smallSingularSubcomplexMap _ _ (TopCat.ofHom φ) id fun _ ↦ hφ :=
  (rfl)

/-- The identity map induces the identity of singular pairs. -/
@[simp]
theorem singularPairInMap_id :
    singularPairInMap (ContinuousMap.id X) (Set.mapsTo_id W) = 𝟙 (singularPairIn X W) := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact TopCat.smallSingularSubcomplexMap_id _
  · exact TopCat.toSSet.map_id _

/-- The map of singular pairs induced by a composite is the composite of the induced maps. -/
theorem singularPairInMap_comp {Z : Type u} [TopologicalSpace Z] {W'' : Set Z} (φ : C(X, Y))
    (ψ : C(Y, Z)) (hφ : Set.MapsTo φ W W') (hψ : Set.MapsTo ψ W' W'') :
    singularPairInMap (ψ.comp φ) (hψ.comp hφ) =
      singularPairInMap φ hφ ≫ singularPairInMap ψ hψ := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact TopCat.smallSingularSubcomplexMap_comp _ _ _ (TopCat.ofHom φ) (TopCat.ofHom ψ) id id
      (fun _ ↦ hφ) (fun _ ↦ hψ)
  · exact TopCat.toSSet.map_comp _ _

variable (W W') in
/-- A smooth map carries smooth simplices with image in `W` to smooth simplices with image in `W'`
when it carries `W` into `W'`. -/
theorem smoothSingularSubcomplex_inf_smallSingularSubcomplex_le_preimage {φ : X → Y}
    (hφ : ContMDiff I J ∞ φ) (hW : Set.MapsTo φ W W') :
    smoothSingularSubcomplex I X ⊓ (TopCat.of X).smallSingularSubcomplex (fun _ : Unit ↦ W) ≤
      (smoothSingularSubcomplex J Y ⊓
        (TopCat.of Y).smallSingularSubcomplex (fun _ : Unit ↦ W')).preimage
        (TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := by
  have h : (TopCat.of X).smallSingularSubcomplex (fun _ : Unit ↦ W) ≤
      ((TopCat.of Y).smallSingularSubcomplex (fun _ : Unit ↦ W')).preimage
        (TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := by
    rw [TopCat.preimage_smallSingularSubcomplex]
    exact TopCat.smallSingularSubcomplex_mono _ fun _ _ hx ↦ hW hx
  exact fun n σ hσ ↦ ⟨smoothSingularSubcomplex_le_preimage hφ n hσ.1, h n hσ.2⟩

/-- The map of smooth pairs induced by a smooth map `φ : X → Y` carrying `W` into `W'`. -/
def smoothPairInMap {φ : X → Y} (hφ : ContMDiff I J ∞ φ) (hW : Set.MapsTo φ W W') :
    smoothPairIn I X W ⟶ smoothPairIn J Y W' :=
  SSetPair.homMk
    (SSet.Subcomplex.lift
      (SSet.Subcomplex.ι _ ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) (by
        rintro n _ ⟨σ, rfl⟩
        exact smoothSingularSubcomplex_inf_smallSingularSubcomplex_le_preimage W W' hφ hW n
          σ.property))
    (smoothSingularSubcomplexMap φ hφ)
    ((cancel_mono (smoothSingularSubcomplex J Y).ι).1 (by
      -- The codomain of `(smoothPairIn J Y W').hom` is `(smoothPairIn J Y W').right`, which is the
      -- smooth singular subcomplex only after unfolding `SSetPair.of`, so `rw` cannot match the
      -- composites. Both sides are `(S ⊓ T).ι ≫ toSSet.map φ`: the right side by
      -- `smoothSingularSubcomplexMap_ι` and `homOfLE_ι`, the left side by `homOfLE_ι` and
      -- `lift_ι`.
      erw [Category.assoc, Category.assoc, smoothSingularSubcomplexMap_ι,
        SSet.Subcomplex.homOfLE_ι_assoc inf_le_left, SSet.Subcomplex.homOfLE_ι inf_le_left,
        SSet.Subcomplex.lift_ι]))

/-- On the subspaces, `smoothPairInMap` is the restriction of the map of singular simplicial
sets. -/
@[simp, reassoc]
theorem smoothPairInMap_left_ι {φ : X → Y} (hφ : ContMDiff I J ∞ φ) (hW : Set.MapsTo φ W W') :
    (smoothPairInMap hφ hW).left ≫ (smoothSingularSubcomplex J Y ⊓
        (TopCat.of Y).smallSingularSubcomplex (fun _ : Unit ↦ W')).ι =
      (smoothSingularSubcomplex I X ⊓ (TopCat.of X).smallSingularSubcomplex (fun _ : Unit ↦ W)).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩) :=
  (rfl)

/-- On the ambient simplicial sets, `smoothPairInMap` is the map of smooth singular subcomplexes. -/
@[simp]
theorem smoothPairInMap_right {φ : X → Y} (hφ : ContMDiff I J ∞ φ) (hW : Set.MapsTo φ W W') :
    (smoothPairInMap hφ hW).right = smoothSingularSubcomplexMap φ hφ :=
  (rfl)

variable (I W) in
/-- The identity map induces the identity of smooth pairs. -/
@[simp]
theorem smoothPairInMap_id :
    smoothPairInMap (J := I) (φ := id) contMDiff_id (Set.mapsTo_id W) = 𝟙 (smoothPairIn I X W) := by
  refine MorphismProperty.Arrow.Hom.ext ?_ smoothSingularSubcomplexMap_id
  -- Both sides send a smooth simplex with image in `W` to the same underlying singular simplex.
  ext n σ
  rfl

/-- The map of smooth pairs induced by a composite is the composite of the induced maps. -/
theorem smoothPairInMap_comp {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace H'' Z] {W'' : Set Z} {φ : X → Y} {ψ : Y → Z} (hφ : ContMDiff I J ∞ φ)
    (hψ : ContMDiff J K ∞ ψ) (hW : Set.MapsTo φ W W') (hW' : Set.MapsTo ψ W' W'') :
    smoothPairInMap (hψ.comp hφ) (hW'.comp hW) =
      smoothPairInMap hφ hW ≫ smoothPairInMap hψ hW' := by
  refine MorphismProperty.Arrow.Hom.ext ?_ (smoothSingularSubcomplexMap_comp hψ hφ)
  -- Both sides postcompose the underlying singular simplex with `ψ ∘ φ`.
  ext n σ
  rfl

/-- The inclusion of smooth pairs into singular pairs is natural in smooth maps of pairs. -/
@[reassoc (attr := simp)]
theorem smoothPairInMap_comp_smoothPairToSingular {φ : X → Y} (hφ : ContMDiff I J ∞ φ)
    (hW : Set.MapsTo φ W W') :
    smoothPairInMap hφ hW ≫ smoothPairToSingular J Y W' =
      smoothPairToSingular I X W ≫ singularPairInMap ⟨φ, hφ.continuous⟩ hW := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · refine (cancel_mono ((TopCat.of Y).smallSingularSubcomplex fun _ : Unit ↦ W').ι).1 ?_
    -- As in `smoothPairInMap`, the pair components agree with the subcomplexes only after
    -- unfolding `SSet.Subcomplex.pair`, so `rw` cannot match the composites. Both sides are
    -- `(S ⊓ T).ι ≫ toSSet.map φ`: the right side by `smallSingularSubcomplexMap_ι` and
    -- `homOfLE_ι`, the left side by `homOfLE_ι` and `smoothPairInMap_left_ι`.
    erw [Category.assoc, Category.assoc, TopCat.smallSingularSubcomplexMap_ι,
      SSet.Subcomplex.homOfLE_ι_assoc inf_le_right, SSet.Subcomplex.homOfLE_ι inf_le_right,
      smoothPairInMap_left_ι]
  · exact smoothSingularSubcomplexMap_ι hφ

end Naturality

section QuasiIso

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
  [T2Space X] [SigmaCompactSpace X] [IsManifold I ∞ X] (W : Opens X)
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

/-- On the subspaces, the inclusion of smooth singular simplices with image in an open set `W` into
all singular simplices with image in `W` is a quasi-isomorphism: these are the smooth and the
singular simplices of the manifold `W`. -/
instance quasiIso_chainComplexMap_smoothPairToSingular_left :
    QuasiIso (SSet.chainComplexMap (smoothPairToSingular I X W).left R) := by
  exact (SSet.quasiIso_chainComplexMap_iff_homOfLE_of_range_eq R (smoothSingularSubcomplex I W).ι
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set X)))) inf_le_right
    ((range_smoothSingularSubcomplex_ι_comp_subtypeVal W).trans
      (congrArg _ (TopCat.range_toSSet_map_subtypeVal (X := TopCat.of X) _)))
    (TopCat.range_toSSet_map_subtypeVal (X := TopCat.of X) _)).1
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (I := I) R W)

/-- On the ambient simplicial sets, the inclusion of smooth singular simplices of `X` is a
quasi-isomorphism, by the smoothing theorem. -/
instance quasiIso_chainComplexMap_smoothPairToSingular_right :
    QuasiIso (SSet.chainComplexMap (smoothPairToSingular I X W).right R) := by
  rw [smoothPairToSingular_right]
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι R

/-- **The relative smoothing theorem.** For an open subset `W` of a Hausdorff `σ`-compact smooth
manifold `X` over a finite-dimensional real model with corners, the inclusion of the smooth singular
chains of `X` relative to those with image in `W` into the singular chains of `X` relative to those
with image in `W` is a quasi-isomorphism, with coefficients in any abelian category in which
countable coproducts are exact. -/
instance quasiIso_smoothPairToSingular :
    QuasiIso (SSetPair.chainComplexMap (smoothPairToSingular I X W) R) :=
  SSetPair.quasiIso_chainComplexMap _ R

/-- The inclusion of relative smooth singular chains induces an isomorphism on relative homology. -/
instance isIso_homologyMap_smoothPairToSingular (n : ℕ) :
    IsIso (SSetPair.homologyMap (smoothPairToSingular I X W) R n) :=
  SSetPair.isIso_homologyMap_of_quasiIso _ R n

section Projective

variable [Projective R]

/-- **The relative smoothing theorem, chain homotopy equivalence form.** For projective
coefficients `R`, for instance `ℝ` or `ℤ`, every term of both relative chain complexes is
projective, so the inclusion of relative smooth singular chains into relative singular chains is a
chain homotopy equivalence. -/
def smoothPairChainHomotopyEquiv :
    HomotopyEquiv ((smoothPairIn I X W).chainComplex R) ((singularPairIn X W).chainComplex R) :=
  let h := (ChainComplex.quasiIso_iff_of_projective
    (SSetPair.chainComplexMap (smoothPairToSingular I X W) R)).1 inferInstance
  h.choose.copy (Homotopy.ofEq h.choose_spec)

/-- The forward map of `smoothPairChainHomotopyEquiv` is the relative chain map of the inclusion of
pairs. -/
@[simp]
theorem smoothPairChainHomotopyEquiv_hom :
    (smoothPairChainHomotopyEquiv I X W R).hom =
      SSetPair.chainComplexMap (smoothPairToSingular I X W) R := by
  rw [smoothPairChainHomotopyEquiv, HomotopyEquiv.copy_hom]

variable (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- For projective coefficients, restriction of relative singular cochains to relative smooth
singular cochains is a quasi-isomorphism. -/
instance quasiIso_cochainComplexMap_smoothPairToSingular :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y)
      (smoothPairToSingular I X W)) :=
  ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective _ k Y

/-- For projective coefficients, restriction from the relative singular cochains of the topological
pair `(X, W)` (`TopPair.singularCochainComplex`) to the relative smooth singular cochains is a
quasi-isomorphism. -/
instance quasiIso_cochainComplexMap_smoothPairToSingular_comp_singularPairInIso_inv :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y)
      (smoothPairToSingular I X W ≫ (singularPairInIso X (W : Set X)).inv)) := by
  have : IsIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y)
      (singularPairInIso X (W : Set X)).inv) :=
    Functor.map_isIso _ _
  rw [SSetPair.cochainComplexMap_comp]
  infer_instance

end Projective

end QuasiIso

end TauCeti
