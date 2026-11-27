/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Analysis.Convex.Star
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl
public import TauCeti.Topology.Homotopy.HomotopyEquiv

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Relative homology of the Thom pair of a product bundle

Let `B` be a topological space and `F` a real normed space of finite dimension `r`. The product
bundle `B × F → B` has Thom pair `(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`). This file
computes its relative singular homology with coefficients in an object `R` of an abelian category:
it vanishes below the rank (`TauCeti.isZero_singularHomology_prodThomPair`), and in degree `n + r`
it is the singular homology of the base in degree `n`
(`TauCeti.prodThomPairSingularHomologyIso`), naturally in the base
(`TauCeti.prodThomPairSingularHomologyIso_hom_naturality`). In particular
`H_r(B × F, B × (F ∖ {0})) ≅ H₀(B)`. This is the local, product case of the Thom isomorphism in
homology, the case of a single trivializing open set in its proof by Mayer–Vietoris over unions
of trivializing open sets.

The computation removes one dimension of `F` at a time. Let `W ⊆ W'` be subspaces of `F` with
`W = W' ∩ ker φ` for a linear functional `φ` and a vector `v ∈ W'` with `φ v = 1`, so `W'` is
spanned by `W` and `v`. The set `B × (F ∖ W)` is the union of the two open sets
`B × (F ∖ {x ∈ W' | φ x ≤ 0})` and `B × (F ∖ {x ∈ W' | 0 ≤ φ x})`, whose intersection is
`B × (F ∖ W')`. The complement in `F` of each closed half-subspace is star-convex, about `v` and
`-v` respectively, so the fibrewise straight-line homotopy kills the relative homology of
`B × F` modulo either open set. The relative Mayer–Vietoris sequence of the two open sets
(`TopCat.relativeMayerVietorisδ`) then identifies `Hₙ₊₁(B × F, B × (F ∖ W))` with
`Hₙ(B × F, B × (F ∖ W'))`, and shows that `H₀(B × F, B × (F ∖ W))` vanishes. Starting from
`W = 0` and repeating `r` times reaches `W = F`, where the subspace is empty, and
`B × F → B` is a homotopy equivalence. This chain of steps is the general computation
`TauCeti.subspaceComplPairSingularHomologyIso` for the projection `B × F → F`.

The isomorphism is built from a choice of such a step for each proper subspace of `F`
(`Submodule.lineExtension`), made independently of `B`; for these choices it is natural in `B`.

## Main definitions and results

* `TauCeti.prodThomPair`: the pair `(B × F, B × (F ∖ {0}))`.
* `TauCeti.prodThomPairMap`: the map of pairs induced by a continuous map of the bases.
* `TauCeti.prodThomPairFiberMap`: the inclusion of the fibre pair `(F, F ∖ {0})` over a point.
* `TauCeti.prodThomPairSnd`: the projection onto the fibre pair, a retraction of each fibre
  inclusion (`TauCeti.prodThomPairFiberMap_comp_prodThomPairSnd`).
* `TauCeti.complZeroPairIsoProdThomPair`: over a point, the fibre inclusion is an isomorphism of
  pairs.

* `TauCeti.prodThomPairProj`, `TauCeti.prodThomPairPuncturedProj`: the projections
  `B × F → B` and `B × (F ∖ {0}) → B`.
* `TauCeti.prodThomPairPuncturedSection`: the section `b ↦ (b, x)` of the punctured product
  bundle, for `x ≠ 0`.
* `TauCeti.prodThomPairPuncturedHomotopyEquiv`: for `e : F ≃L[ℝ] ℝᵈ⁺¹`, the punctured product
  `B × (F ∖ {0})` is homotopy equivalent to `Sᵈ × B` by `(b, x) ↦ (e x / ‖e x‖, b)`.
* `TauCeti.prodThomPairPuncturedHomotopyEquivSphere`: the same without coordinates,
  `B × (F ∖ {0}) ≃ₕ S × B` for `S` the unit sphere of `F`.
* `TauCeti.shortExact_singularHomology_prodThomPair`: the long exact sequence of the Thom pair
  breaks up into short exact sequences
  `0 ⟶ Hₘ₊₁(B × F, B × (F ∖ {0})) ⟶ Hₘ(B × (F ∖ {0})) ⟶ Hₘ(B × F) ⟶ 0`, since the punctured
  product bundle has a section.
* `TauCeti.isZero_singularHomology_prodThomPair`: `Hₙ(B × F, B × (F ∖ {0})) = 0` for
  `n < dim F`.
* `TauCeti.prodThomPairSingularHomologyIso`: `Hₙ₊ᵣ(B × F, B × (F ∖ {0})) ≅ Hₙ(B)`, `r = dim F`.
* `TauCeti.prodThomPairSingularHomologyIso_hom_naturality`,
  `TauCeti.prodThomPairSingularHomologyIso_inv_naturality`: its naturality in the base.
* `TauCeti.complZeroPairPointHom`: the isomorphism `R ≅ Hᵣ(F, F ∖ {0})` given by the class of
  the point under `Hᵣ(F, F ∖ {0}) ≅ H₀(pt)`; the fibre inclusion over `b` carries it to the class of
  `b` (`TauCeti.complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap`).
* `TauCeti.isLocalOrientation_complZeroPairPointHom_one`: with integral coefficients the point
  class of `1` is a local orientation of `(F, F ∖ {0})`.
* `TauCeti.span_complZeroPairPointHom_one`,
  `TauCeti.exists_eq_units_smul_complZeroPairPointHom_one`: with coefficients in a commutative
  ring `K`, the point class of `1` generates `Hᵣ(F, F ∖ {0}; K)`, and every generator is a unit
  multiple of it; `TauCeti.eq_complZeroPairPointHom_one`: it is the only generator when `1` is
  the only unit of `K`.
* `TauCeti.singularHomologyMap_prodThomPairFiberMap_eq_of_joined`: fibre inclusions over points
  joined by a path agree on `Hᵣ`.
* `TauCeti.singularHomology_prodThomPair_hom_ext`: morphisms out of
  `Hᵣ(B × F, B × (F ∖ {0}))` are determined by their restrictions to the fibre pairs.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first over a trivializing open set and then by Mayer–Vietoris).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe w v u

namespace TauCeti

section Defs

variable (B : Type w) [TopologicalSpace B] (F : Type w) [TopologicalSpace F] [Zero F]

/-- The Thom pair `(B × F, B × (F ∖ {0}))` of the product bundle `B × F → B`. -/
abbrev prodThomPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (B × F)) {p | p.2 ≠ 0}

variable {B} {B' : Type w} [TopologicalSpace B'] {B'' : Type w} [TopologicalSpace B'']

/-- The map of Thom pairs of product bundles `(B × F, B × (F ∖ {0})) ⟶ (B' × F, B' × (F ∖ {0}))`
induced by a continuous map `g : B → B'` of the bases. -/
def prodThomPairMap (g : C(B, B')) : prodThomPair B F ⟶ prodThomPair B' F :=
  TopPair.ofSubsetMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) fun _ hp ↦ hp

@[simp]
lemma prodThomPairMap_fst_apply (g : C(B, B')) (p : B × F) :
    TopPair.Hom.fst (prodThomPairMap F g) p = (g p.1, p.2) :=
  TopPair.ofSubsetMap_fst_apply _ _ _

@[simp]
lemma prodThomPairMap_snd_apply (g : C(B, B')) (p : (prodThomPair B F).snd) :
    (TopPair.Hom.snd (prodThomPairMap F g) p).val = (g p.val.1, p.val.2) :=
  TopPair.ofSubsetMap_snd_apply _ _ _

@[simp]
lemma prodThomPairMap_id : prodThomPairMap F (ContinuousMap.id B) = 𝟙 _ :=
  TopPair.ofSubsetMap_id _

@[reassoc]
lemma prodThomPairMap_comp (g : C(B, B')) (g' : C(B', B'')) :
    prodThomPairMap F (g'.comp g) = prodThomPairMap F g ≫ prodThomPairMap F g' :=
  (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext <;> rfl)).symm

/-- The inclusion `(F, F ∖ {0}) ⟶ (B × F, B × (F ∖ {0}))` of the fibre pair over `b` into the Thom
pair of the product bundle. -/
def prodThomPairFiberMap (b : B) :
    TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) ⟶ prodThomPair B F :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨fun x ↦ (b, x), by fun_prop⟩) fun _ hx ↦ hx

@[simp]
lemma prodThomPairFiberMap_fst_apply (b : B) (x : F) :
    TopPair.Hom.fst (prodThomPairFiberMap F b) x = (b, x) :=
  TopPair.ofSubsetMap_fst_apply _ _ _

/-- The map of Thom pairs induced by a map of the bases carries the fibre over `b` to the fibre
over `g b`. -/
@[reassoc (attr := simp)]
lemma prodThomPairFiberMap_comp_prodThomPairMap (b : B) (g : C(B, B')) :
    prodThomPairFiberMap F b ≫ prodThomPairMap F g = prodThomPairFiberMap F (g b) :=
  TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext <;> rfl)

variable (B) in
/-- The projection `(B × F, B × (F ∖ {0})) ⟶ (F, F ∖ {0})` of the Thom pair of the product bundle
onto its fibre pair. -/
def prodThomPairSnd :
    prodThomPair B F ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) fun _ hp ↦ hp

@[simp]
lemma prodThomPairSnd_fst_apply (p : B × F) :
    TopPair.Hom.fst (prodThomPairSnd B F) p = p.2 :=
  TopPair.ofSubsetMap_fst_apply _ _ _

/-- The projection to the fibre is a retraction of each fibre inclusion. -/
@[reassoc (attr := simp)]
lemma prodThomPairFiberMap_comp_prodThomPairSnd (b : B) :
    prodThomPairFiberMap F b ≫ prodThomPairSnd B F = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    (prodThomPairSnd_fst_apply F _).trans
      (congrArg Prod.snd (prodThomPairFiberMap_fst_apply F b x)))

/-- Over a point, the projection to the fibre is also a section of the fibre inclusion. -/
theorem prodThomPairSnd_comp_prodThomPairFiberMap :
    prodThomPairSnd PUnit.{w + 1} F ≫ prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1}) = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
    (prodThomPairFiberMap_fst_apply F _ _).trans
      (congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)))

/-- Over a point, the fibre inclusion is an isomorphism from the pair `(F, F ∖ {0})` onto the Thom
pair of the product bundle, with inverse the projection to the fibre. -/
@[expose, simps]
def complZeroPairIsoProdThomPair :
    TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) ≅ prodThomPair PUnit.{w + 1} F where
  hom := prodThomPairFiberMap F PUnit.unit
  inv := prodThomPairSnd PUnit.{w + 1} F
  hom_inv_id := prodThomPairFiberMap_comp_prodThomPairSnd F _
  inv_hom_id := prodThomPairSnd_comp_prodThomPairFiberMap F

variable (B) in
/-- The projection `B × F → B` of the product bundle onto its base, as a morphism out of the
ambient space of the Thom pair. -/
def prodThomPairProj : (prodThomPair B F).fst ⟶ TopCat.of B :=
  TopCat.ofHom ContinuousMap.fst

@[simp]
lemma prodThomPairProj_apply (p : B × F) : prodThomPairProj B F p = p.1 :=
  (rfl)

variable (B) in
/-- The projection `B × (F ∖ {0}) → B` of the punctured product bundle onto its base. -/
def prodThomPairPuncturedProj : (prodThomPair B F).snd ⟶ TopCat.of B :=
  (prodThomPair B F).map ≫ prodThomPairProj B F

@[simp]
lemma prodThomPairPuncturedProj_apply (p : (prodThomPair B F).snd) :
    prodThomPairPuncturedProj B F p = p.val.1 :=
  (rfl)

/-- The projection of the punctured product bundle is the restriction of the projection of the
product bundle. -/
@[reassoc]
lemma map_comp_prodThomPairProj :
    (prodThomPair B F).map ≫ prodThomPairProj B F = prodThomPairPuncturedProj B F :=
  (rfl)

variable (B) {F} in
/-- The section `b ↦ (b, x)` of the punctured product bundle `B × (F ∖ {0}) → B`, for a nonzero
`x : F`. -/
def prodThomPairPuncturedSection (x : F) (hx : x ≠ 0) : TopCat.of B ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom ⟨fun b ↦ ⟨(b, x), hx⟩, (continuous_id.prodMk continuous_const).subtype_mk _⟩

variable {F} in
@[simp]
lemma prodThomPairPuncturedSection_apply (x : F) (hx : x ≠ 0) (b : B) :
    (prodThomPairPuncturedSection B x hx b).val = (b, x) :=
  (rfl)

variable {F} in
/-- The map `b ↦ (b, x)` is a section of the projection of the punctured product bundle. -/
@[reassoc (attr := simp)]
lemma prodThomPairPuncturedSection_comp_prodThomPairPuncturedProj (x : F) (hx : x ≠ 0) :
    prodThomPairPuncturedSection B x hx ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (prodThomPairPuncturedSection B x hx b)

/-- The projections of the punctured product bundles commute with the map of the bases. -/
@[reassoc]
theorem snd_prodThomPairMap_comp_prodThomPairPuncturedProj (g : C(B, B')) :
    TopPair.Hom.snd (prodThomPairMap F g) ≫ prodThomPairPuncturedProj B' F =
      prodThomPairPuncturedProj B F ≫ TopCat.ofHom g :=
  TopCat.ext fun p ↦ congrArg Prod.fst (prodThomPairMap_snd_apply F g p)

end Defs

section Punctured

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

open MonoidalCategory CartesianMonoidalCategory

/-- The punctured product `B × (F ∖ {0})` is `B × (F ∖ {0})` as a product of spaces. -/
private def prodThomPairPuncturedHomeomorphProd :
    (prodThomPair B F).snd ≃ₜ B × ({0}ᶜ : Set F) where
  toFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  invFun q := ⟨(q.1, q.2), q.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.fst).prodMk
    (continuous_subtypeVal.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).subtype_mk _

/-- In the coordinates `e`, the punctured product `B × (F ∖ {0})` is `B × (ℝᵈ⁺¹ ∖ {0})`. -/
private def prodThomPairPuncturedHomeomorph (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd ≃ₜ B × ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
  prodThomPairPuncturedHomeomorphProd.trans
    ((Homeomorph.refl B).prodCongr (e.toHomeomorph.subtype fun x ↦ by simp))

variable (B) in
/-- `B × (E ∖ {0})` is homotopy equivalent to `S × B`, for `S` the unit sphere of a real normed
space `E`, by `(b, y) ↦ (y / ‖y‖, b)`. -/
private def prodComplZeroHomotopyEquivSphere (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv (B × ({0}ᶜ : Set E)) (Metric.sphere (0 : E) 1 × B) :=
  ((ContinuousMap.HomotopyEquiv.refl B).prodCongr (complSingletonHomotopyEquivSphere 0)).trans
    (Homeomorph.prodComm _ _).toHomotopyEquiv

variable (B) in
/-- **The punctured product bundle is homotopy equivalent to a product with a sphere.** For a
continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹`, the complement `B × (F ∖ {0})` of the zero
section of the product bundle `B × F → B` is homotopy equivalent to `Sᵈ × B`, by
`(b, x) ↦ (e x / ‖e x‖, b)`. -/
def prodThomPairPuncturedHomotopyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    ContinuousMap.HomotopyEquiv (prodThomPair B F).snd
      ↑(TopCat.sphere.{w} d ⊗ TopCat.of B : TopCat.{w}) :=
  ((prodThomPairPuncturedHomeomorph e).toHomotopyEquiv.trans
    (prodComplZeroHomotopyEquivSphere B _)).trans
    ((Homeomorph.ulift.{w}).symm.prodCongr (Homeomorph.refl B)).toHomotopyEquiv

/-- The second component of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is the base point. -/
@[simp]
theorem prodThomPairPuncturedHomotopyEquiv_apply_snd (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (p : (prodThomPair B F).snd) :
    (prodThomPairPuncturedHomotopyEquiv B e p).2 = p.val.1 :=
  (rfl)

/-- The first component of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is the radial projection
`(b, x) ↦ e x / ‖e x‖` onto the unit sphere of `ℝᵈ⁺¹`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquiv_apply_fst
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p : (prodThomPair B F).snd) :
    ((prodThomPairPuncturedHomotopyEquiv B e p).1.down : EuclideanSpace ℝ (Fin (d + 1))) =
      ‖e p.val.2‖⁻¹ • e p.val.2 :=
  (coe_complSingletonHomotopyEquivSphere_apply _ ⟨e p.val.2, _⟩).trans (by simp)

/-- The homotopy inverse of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is
`(s, b) ↦ (b, e⁻¹ s)`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquiv_symm_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (q : ↑(TopCat.sphere.{w} d ⊗ TopCat.of B : TopCat.{w})) :
    ((prodThomPairPuncturedHomotopyEquiv B e).symm q).val = (q.2, e.symm q.1.down) :=
  Prod.ext rfl (congrArg e.symm
    ((coe_complSingletonHomotopyEquivSphere_symm_apply _ q.1.down).trans (add_zero _)))

end Punctured

section PuncturedSphere

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (B F) in
/-- **The punctured product bundle is homotopy equivalent to a product with the unit sphere**:
`B × (F ∖ {0})` is homotopy equivalent to `S × B` for `S` the unit sphere of the real normed space
`F`, by `(b, x) ↦ (x / ‖x‖, b)`. This is the coordinate-free form of
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
def prodThomPairPuncturedHomotopyEquivSphere :
    ContinuousMap.HomotopyEquiv (prodThomPair B F).snd (Metric.sphere (0 : F) 1 × B) :=
  prodThomPairPuncturedHomeomorphProd.toHomotopyEquiv.trans (prodComplZeroHomotopyEquivSphere B F)

/-- The second component of `TauCeti.prodThomPairPuncturedHomotopyEquivSphere` is the base
point. -/
@[simp]
theorem prodThomPairPuncturedHomotopyEquivSphere_apply_snd (p : (prodThomPair B F).snd) :
    (prodThomPairPuncturedHomotopyEquivSphere B F p).2 = p.val.1 :=
  (rfl)

/-- The first component of `TauCeti.prodThomPairPuncturedHomotopyEquivSphere` is the radial
projection `(b, x) ↦ x / ‖x‖` onto the unit sphere of `F`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquivSphere_apply_fst (p : (prodThomPair B F).snd) :
    ((prodThomPairPuncturedHomotopyEquivSphere B F p).1 : F) = ‖p.val.2‖⁻¹ • p.val.2 :=
  (coe_complSingletonHomotopyEquivSphere_apply _ ⟨p.val.2, p.property⟩).trans (by simp)

/-- The homotopy inverse of `TauCeti.prodThomPairPuncturedHomotopyEquivSphere` is
`(s, b) ↦ (b, s)`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquivSphere_symm_apply
    (q : Metric.sphere (0 : F) 1 × B) :
    ((prodThomPairPuncturedHomotopyEquivSphere B F).symm q).val = (q.2, (q.1 : F)) :=
  Prod.ext rfl ((coe_complSingletonHomotopyEquivSphere_symm_apply _ q.1).trans (add_zero _))

end PuncturedSphere

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {B : Type w} [TopologicalSpace B] {B' : Type w} [TopologicalSpace B']
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

section PuncturedSection

open AlgebraicTopology

variable (B F)

/-- The projection `B × F → B` induces isomorphisms on homology, since `F` is contractible. -/
theorem isIso_singularHomologyMap_prodThomPairProj (m : ℕ) :
    IsIso (((singularHomologyFunctor C m).obj R).map (prodThomPairProj B F)) := by
  have h : prodThomPairProj B F =
      TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodContractible B F).toFun := by
    rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun]
    exact TopCat.ext fun p ↦ prodThomPairProj_apply F p
  rw [h]
  exact (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_homologyMap R m

variable {F} in
/-- The section `b ↦ (b, x)` of the punctured product bundle followed by the inclusion
`B × (F ∖ {0}) → B × F` induces isomorphisms on homology. -/
theorem isIso_singularHomologyMap_prodThomPairPuncturedSection_comp_map (x : F) (hx : x ≠ 0)
    (m : ℕ) :
    IsIso (((singularHomologyFunctor C m).obj R).map
      (prodThomPairPuncturedSection B x hx ≫ (prodThomPair B F).map)) := by
  have := isIso_singularHomologyMap_prodThomPairProj R B F m
  have : IsIso (((singularHomologyFunctor C m).obj R).map
      (prodThomPairPuncturedSection B x hx ≫ (prodThomPair B F).map) ≫
        ((singularHomologyFunctor C m).obj R).map (prodThomPairProj B F)) := by
    rw [← Functor.map_comp, Category.assoc, map_comp_prodThomPairProj,
      prodThomPairPuncturedSection_comp_prodThomPairPuncturedProj, CategoryTheory.Functor.map_id]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((singularHomologyFunctor C m).obj R).map
    (prodThomPairProj B F))

/-- The inclusion `B × (F ∖ {0}) → B × F` is an epimorphism on homology, split by the section
`b ↦ (b, x)` for any `x ≠ 0`. -/
theorem epi_singularHomologyMap_prodThomPair_map [Nontrivial F] (m : ℕ) :
    Epi (((singularHomologyFunctor C m).obj R).map (prodThomPair B F).map) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : F)
  have := isIso_singularHomologyMap_prodThomPairPuncturedSection_comp_map R B x hx m
  rw [Functor.map_comp] at this
  exact epi_of_epi (((singularHomologyFunctor C m).obj R).map
    (prodThomPairPuncturedSection B x hx)) _

/-- **The long exact sequence of the Thom pair of a product bundle breaks up** into short exact
sequences

`0 ⟶ Hₘ₊₁(B × F, B × (F ∖ {0})) ⟶ Hₘ(B × (F ∖ {0})) ⟶ Hₘ(B × F) ⟶ 0`,

with maps the connecting morphism and the inclusion, for every nonzero real normed space `F`:
each nonzero `x : F` gives a section `b ↦ (b, x)` of the punctured product bundle, so the
inclusion is a split epimorphism on homology. -/
theorem shortExact_singularHomology_prodThomPair [Nontrivial F] (m : ℕ) :
    (ShortComplex.mk _ _ ((prodThomPair B F).singularHomologyδ_comp R (m + 1) m)).ShortExact :=
  .mk' ((prodThomPair B F).singularHomology_exact_subspace R (m + 1) m)
    -- The map from ambient to relative homology vanishes, since the inclusion is onto.
    (((prodThomPair B F).singularHomology_exact_relative R (m + 1) m).mono_g
      (((prodThomPair B F).singularHomology_exact_space R (m + 1)).epi_f_iff.1
        (epi_singularHomologyMap_prodThomPair_map R B F (m + 1))))
    (epi_singularHomologyMap_prodThomPair_map R B F m)

end PuncturedSection

namespace ProdThomPair

/-- The projection `B × F → F`. -/
private abbrev proj (B : Type w) [TopologicalSpace B] : C(TopCat.of (B × F), F) :=
  ContinuousMap.snd

/-- The pair `(B × F, B × (F ∖ W))` for a subspace `W` of `F`. -/
private abbrev pair (B : Type w) [TopologicalSpace B] (W : Submodule ℝ F) : TopPair.{w} :=
  subspaceComplPair (proj B) ∅ W

/-- The map of pairs `(B × F, B × (F ∖ W)) ⟶ (B' × F, B' × (F ∖ W))` induced by `g : B → B'`. -/
private abbrev pairMap (g : C(B, B')) (W : Submodule ℝ F) : pair B W ⟶ pair B' W :=
  subspaceComplPairMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) (fun _ ↦ rfl)
    (Set.mapsTo_empty _ _) W

variable (B) in
/-- `B × F` deforms into the complement of `B` times a closed half-subspace `{y ∈ W | φ y ≤ 0}`
with `φ v = 1` for some `v ∈ W`, through maps keeping that complement inside itself: the homotopy
moves along straight lines towards `v` in each fibre. -/
theorem exists_homotopy_halfCompl (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F) (hv : v ∈ W)
    (hφv : φ v = 1) :
    ∃ (ρ : TopCat.of (B × F) ⟶ TopCat.of (B × F))
      (H : (TopCat.Hom.hom (𝟙 (TopCat.of (B × F)))).Homotopy ρ.hom),
      (∀ (τ : unitInterval) (p : TopCat.of (B × F)),
        p ∈ SubspaceComplPair.halfCompl (ContinuousMap.snd : C(TopCat.of (B × F), F)) W φ →
          H (τ, p) ∈
            SubspaceComplPair.halfCompl (ContinuousMap.snd : C(TopCat.of (B × F), F)) W φ) ∧
      ∀ p, ρ p ∈ SubspaceComplPair.halfCompl (ContinuousMap.snd : C(TopCat.of (B × F), F)) W φ :=
  ⟨TopCat.ofHom ⟨fun p ↦ (p.1, v), by fun_prop⟩,
    { toFun q := (q.2.1, (q.1 : ℝ) • v + (1 - (q.1 : ℝ)) • q.2.2)
      continuous_toFun := by fun_prop
      map_zero_left _ := by simp
      map_one_left _ := by simp },
    fun τ _ hp ↦ starConvex_compl_setOf_mem_and_nonpos hv (by simp [hφv]) hp τ.property.1
      (sub_nonneg.2 τ.property.2) (add_sub_cancel _ _),
    fun _ h ↦ (hφv ▸ one_pos : 0 < φ v).not_ge h.2⟩

variable (B) in
/-- The relative homology of `B × F` modulo the complement of a closed half-subspace vanishes:
`B × F` deforms into that complement along straight lines towards `v`. -/
private lemma isZero_singularHomology_halfCompl (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F)
    (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset
      (∅ ∪ SubspaceComplPair.halfCompl (proj B) W φ)).singularHomology R n) := by
  rw [Set.empty_union]
  obtain ⟨ρ, H, hS, hρ⟩ := exists_homotopy_halfCompl B W φ v hv hφv
  exact TopPair.isZero_singularHomology_ofSubset_of_homotopy H hS hρ R n

variable (B)

private instance : IsEmpty (pair B (⊤ : Submodule ℝ F)).snd :=
  ⟨fun p ↦ p.property.elim id fun h ↦ h Submodule.mem_top⟩

variable (F) in
/-- `Hₙ(B × F, ∅) ≅ Hₙ(B)`, through the projection. -/
private def emptyIso (n : ℕ) :
    (pair B (⊤ : Submodule ℝ F)).singularHomology R n ≅
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (TopCat.of B) :=
  (asIso ((pair B (⊤ : Submodule ℝ F)).singularHomologyπ R n)).symm ≪≫
    (ContinuousMap.HomotopyEquiv.prodContractible B F).singularHomologyIso R n

variable (F) in
/-- The identification of `(B × F, B × (F ∖ {0}))` with `(B × F, B × (F ∖ ⊥))`. -/
private def botIso : prodThomPair B F ≅ pair B (⊥ : Submodule ℝ F) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun p ↦ by
    simp only [Set.mem_ofPred_eq, Set.empty_union]
    rfl

/-! ### Naturality in the base -/

variable (g : C(B, B'))

variable (F) in
/-- The map from ambient to relative homology followed by `emptyIso` is the map induced by the
projection `B × F → B`. -/
private lemma singularHomologyπ_emptyIso_hom (n : ℕ) :
    (pair B (⊤ : Submodule ℝ F)).singularHomologyπ R n ≫ (emptyIso R B F n).hom =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (TopCat.ofHom (ContinuousMap.fst : C(B × F, B))) :=
  -- A term proof: the source of the relative map is the homology of the singular simplicial set
  -- of `B × F`, which agrees with Mathlib's singular homology of `B × F` only up to unfolding.
  (IsIso.hom_inv_id_assoc _ _).trans
    (((ContinuousMap.HomotopyEquiv.prodContractible B F).singularHomologyIso_hom R n).trans
      (by rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun]))

private lemma emptyIso_hom_naturality (n : ℕ) :
    (emptyIso R B F n).hom ≫ ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (TopCat.ofHom g) =
      TopPair.singularHomologyMap (pairMap g (⊤ : Submodule ℝ F)) R n ≫
        (emptyIso R B' F n).hom := by
  let H := (AlgebraicTopology.singularHomologyFunctor C n).obj R
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(B × F, B)) ≫ TopCat.ofHom g =
      TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F)) ≫
        TopCat.ofHom (ContinuousMap.fst : C(B' × F, B')) := by
    have hpair : TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F)) =
        TopCat.ofHom (g.prodMap (ContinuousMap.id F)) :=
      subspaceComplPairMap_fst _ _ _ _
    rw [hpair]
    rfl
  rw [← cancel_epi ((pair B (⊤ : Submodule ℝ F)).singularHomologyπ R n)]
  -- The intermediate terms mix the homology of singular simplicial sets with Mathlib's singular
  -- homology functor, which agree only up to unfolding, so the steps are chained as terms.
  have hmap : H.map (TopCat.ofHom (ContinuousMap.fst : C(B × F, B))) ≫ H.map (TopCat.ofHom g) =
      H.map (TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F))) ≫
        H.map (TopCat.ofHom (ContinuousMap.fst : C(B' × F, B'))) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map hfst).trans (H.map_comp _ _))
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ H.map (TopCat.ofHom g)) (singularHomologyπ_emptyIso_hom R B F n))).trans
    (hmap.trans ((congrArg (H.map (TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F))) ≫ ·)
      (singularHomologyπ_emptyIso_hom R B' F n).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (emptyIso R B' F n).hom)
        (TopPair.singularHomologyπ_naturality (pairMap g (⊤ : Submodule ℝ F)) R n)).trans
        (Category.assoc _ _ _)))))

private lemma botIso_hom_naturality :
    (botIso B F).hom ≫ pairMap g ⊥ = prodThomPairMap F g ≫ (botIso B' F).hom := by
  have h : pairMap g (⊥ : Submodule ℝ F) =
      TopPair.ofSubsetMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) fun _ hx ↦ hx :=
    subspaceComplPairMap_eq_ofSubsetMap _ _ _ _ _
  simp only [botIso, h, prodThomPairMap, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl

end ProdThomPair

open ProdThomPair

variable (B F) [FiniteDimensional ℝ F]

/-- **The relative homology of the Thom pair of a product bundle vanishes below the rank**:
`Hₙ(B × F, B × (F ∖ {0})) = 0` for `n < dim F`. -/
theorem isZero_singularHomology_prodThomPair {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((prodThomPair B F).singularHomology R n) :=
  (isZero_singularHomology_subspaceComplPair R (proj B) ∅ isOpen_empty
    (isZero_singularHomology_halfCompl R B) n ⊥ (by simpa using hn)).of_iso
    (asIso (TopPair.singularHomologyMap (botIso B F).hom R n))

/-- **The homology of the Thom pair of a product bundle**: for `F` of dimension `r` and
`m = n + r`, `Hₘ(B × F, B × (F ∖ {0})) ≅ Hₙ(B)`. In particular `Hᵣ(B × F, B × (F ∖ {0}))` is
`H₀(B)`. The isomorphism is built from choices of subspaces and functionals of `F` that do not
depend on `B`, and it is natural in `B` (`TauCeti.prodThomPairSingularHomologyIso_hom_naturality`).
-/
def prodThomPairSingularHomologyIso (n m : ℕ) (h : n + finrank ℝ F = m := by lia) :
    (prodThomPair B F).singularHomology R m ≅
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (TopCat.of B) :=
  asIso (TopPair.singularHomologyMap (botIso B F).hom R m) ≪≫
    subspaceComplPairSingularHomologyIso R (proj B) ∅ isOpen_empty
      (isZero_singularHomology_halfCompl R B) (finrank ℝ F) ⊥ (by simp) n m h ≪≫ emptyIso R B F n

/-- The isomorphism `Hₙ₊ᵣ(B × F, B × (F ∖ {0})) ≅ Hₙ(B)` is natural in continuous maps of the
base. -/
@[reassoc]
theorem prodThomPairSingularHomologyIso_hom_naturality (g : C(B, B')) (n m : ℕ)
    (h : n + finrank ℝ F = m := by lia) :
    TopPair.singularHomologyMap (prodThomPairMap F g) R m ≫
        (prodThomPairSingularHomologyIso R B' F n m h).hom =
      (prodThomPairSingularHomologyIso R B F n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map (TopCat.ofHom g) := by
  simp only [prodThomPairSingularHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [emptyIso_hom_naturality, subspaceComplPairSingularHomologyIso_hom_naturality_assoc R
      isOpen_empty (isZero_singularHomology_halfCompl R B) isOpen_empty
      (isZero_singularHomology_halfCompl R B') (TopCat.ofHom (g.prodMap (ContinuousMap.id F)))
      (fun _ ↦ rfl) (Set.mapsTo_empty _ _),
    ← TopPair.singularHomologyMap_comp_assoc (botIso B F).hom, botIso_hom_naturality,
    TopPair.singularHomologyMap_comp_assoc]

/-- The inverse isomorphism `Hₙ(B) ≅ Hₙ₊ᵣ(B × F, B × (F ∖ {0}))` is natural in continuous maps of
the base. -/
@[reassoc]
theorem prodThomPairSingularHomologyIso_inv_naturality (g : C(B, B')) (n m : ℕ)
    (h : n + finrank ℝ F = m := by lia) :
    (prodThomPairSingularHomologyIso R B F n m h).inv ≫
        TopPair.singularHomologyMap (prodThomPairMap F g) R m =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map (TopCat.ofHom g) ≫
        (prodThomPairSingularHomologyIso R B' F n m h).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact prodThomPairSingularHomologyIso_hom_naturality R B F g n m h

/-- **The point class of the fibre pair**: the map `R ⟶ H_d(F, F ∖ {0}; R)`, `d = dim F`, carrying
the coefficients to the classes of the point under `H_d(F, F ∖ {0}) ≅ H_d(pt × F, pt × (F ∖ {0}))
≅ H₀(pt)`. It is an isomorphism (`TauCeti.isIso_complZeroPairPointHom`), and the fibre inclusion
over `b` carries it to the class of `b` in `H₀(B) ≅ H_d(B × F, B × (F ∖ {0}))`
(`TauCeti.complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap`). -/
def complZeroPairPointHom (d : ℕ) (hd : finrank ℝ F = d) :
    R ⟶ (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology R d :=
  singularHomology₀Section R (X := TopCat.of PUnit.{w + 1}) PUnit.unit ≫
    (prodThomPairSingularHomologyIso R PUnit.{w + 1} F 0 d (by lia)).inv ≫
      TopPair.singularHomologyMap (complZeroPairIsoProdThomPair F).inv R d

instance isIso_complZeroPairPointHom (d : ℕ) (hd : finrank ℝ F = d) :
    IsIso (complZeroPairPointHom R F d hd) := by
  have : IsIso (singularHomology₀Section R (X := TopCat.of PUnit.{w + 1}) PUnit.unit) :=
    ⟨_, singularHomology₀Section_singularHomology₀ε R _,
      singularHomology₀ε_singularHomology₀Section R _⟩
  rw [complZeroPairPointHom]
  infer_instance

/-- With integral coefficients, the point class of `1` is a local orientation of `(F, F ∖ {0})`:
it generates `H_d(F, F ∖ {0}; ℤ) ≅ ℤ`. -/
theorem isLocalOrientation_complZeroPairPointHom_one (d : ℕ) (hd : finrank ℝ F = d) :
    IsLocalOrientation (0 : F) d
      (complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F d hd (ULift.up 1)) :=
  isLocalOrientation_inv_one
    (asIso (complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F d hd)).symm

/-- The fibre inclusion over `b` carries the point class of the fibre pair to the class of `b` in
`H₀(B) ≅ H_d(B × F, B × (F ∖ {0}))`. -/
@[reassoc]
theorem complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap (d : ℕ)
    (hd : finrank ℝ F = d) (b : B) :
    complZeroPairPointHom R F d hd ≫ TopPair.singularHomologyMap (prodThomPairFiberMap F b) R d =
      singularHomology₀Section R (X := TopCat.of B) b ≫
        (prodThomPairSingularHomologyIso R B F 0 d (by lia)).inv := by
  -- The fibre over `b` is the Thom pair over a point, mapped in by the constant map at `b`.
  let c : C(PUnit.{w + 1}, B) := ContinuousMap.const _ b
  have hc : prodThomPairSnd PUnit.{w + 1} F ≫ prodThomPairFiberMap F b = prodThomPairMap F c :=
    (congrArg (prodThomPairSnd PUnit.{w + 1} F ≫ ·)
      (prodThomPairFiberMap_comp_prodThomPairMap F PUnit.unit c)).symm.trans (by
        rw [← Category.assoc, prodThomPairSnd_comp_prodThomPairFiberMap, Category.id_comp])
  rw [complZeroPairPointHom, complZeroPairIsoProdThomPair_inv, Category.assoc, Category.assoc,
    ← TopPair.singularHomologyMap_comp, hc,
    prodThomPairSingularHomologyIso_inv_naturality R PUnit.{w + 1} F c 0 d, ← Category.assoc,
    singularHomology₀Section_naturality, TopCat.ofHom_apply, ContinuousMap.const_apply]

variable {B} in
/-- Fibre inclusions over points joined by a path induce the same map on the homology of the Thom
pair of the product bundle in the degree `d = dim F`. -/
theorem singularHomologyMap_prodThomPairFiberMap_eq_of_joined (d : ℕ) (hd : finrank ℝ F = d)
    {x y : B} (h : Joined x y) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F x) R d =
      TopPair.singularHomologyMap (prodThomPairFiberMap F y) R d := by
  rw [← cancel_epi (complZeroPairPointHom R F d hd),
    complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap,
    complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap,
    singularHomology₀Section_eq_of_joined R (X := TopCat.of B) h]

variable {R B F} in
/-- **Morphisms out of the top-degree homology are determined on the fibres**: two morphisms out
of `Hᵣ(B × F, B × (F ∖ {0}))`, `r = dim F`, which agree after the inclusion of the fibre pair
`(F, F ∖ {0})` over every point of `B`, are equal. Equivalently, the images of the fibre pairs
generate this homology, which is `H₀(B)`. -/
theorem singularHomology_prodThomPair_hom_ext {T : C}
    {g g' : (prodThomPair B F).singularHomology R (finrank ℝ F) ⟶ T}
    (h : ∀ b, TopPair.singularHomologyMap (prodThomPairFiberMap F b) R _ ≫ g =
      TopPair.singularHomologyMap (prodThomPairFiberMap F b) R _ ≫ g') : g = g' := by
  -- Read `g` and `g'` on `H₀(B)`, where they are determined by the classes of points.
  rw [← cancel_epi (prodThomPairSingularHomologyIso R B F 0 (finrank ℝ F)).inv]
  refine singularHomology₀_hom_ext R fun b ↦ ?_
  rw [← Category.assoc, ← Category.assoc,
    ← complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap R B F _ rfl b,
    Category.assoc, Category.assoc, h b]

section Generator

variable (K : Type w)

/-- The point class of `1` generates `Hᵣ(F, F ∖ {0}; K) ≅ K`. -/
theorem span_complZeroPairPointHom_one [Ring K] :
    Submodule.span K {complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)} = ⊤ :=
  (ModuleCat.span_singleton_apply_eq_top_iff _).2 Ideal.span_singleton_one

variable [CommRing K]

/-- Every generator of `Hᵣ(F, F ∖ {0}; K) ≅ K` is a unit multiple of the point class of `1`. -/
theorem exists_eq_units_smul_complZeroPairPointHom_one {x : ((TopPair.ofSubset
    (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) :
      ModuleCat.{w} K)} (hx : Submodule.span K {x} = ⊤) :
    ∃ u : Kˣ,
      x = (u : K) • complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K) := by
  let φ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)).toLinearEquiv
  have hx' := φ.span_singleton_eq_top_iff_isUnit.1 hx
  have hg := φ.span_singleton_eq_top_iff_isUnit.1 (span_complZeroPairPointHom_one F K)
  refine ⟨hx'.unit * hg.unit⁻¹, φ.injective ?_⟩
  rw [map_smul, smul_eq_mul, Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one,
    IsUnit.unit_spec]

/-- With coefficients in a ring whose only unit is `1`, the point class of `1` is the only
generator of `Hᵣ(F, F ∖ {0}; K) ≅ K`. -/
theorem eq_complZeroPairPointHom_one [Subsingleton Kˣ] {x : ((TopPair.ofSubset
    (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology (ModuleCat.of K K) (finrank ℝ F) :
      ModuleCat.{w} K)} (hx : Submodule.span K {x} = ⊤) :
    x = complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K) :=
  LinearEquiv.eq_of_span_singleton_eq_top (singularHomologyComplSingletonFinrankIso
      (ModuleCat.of K K) (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)).toLinearEquiv hx
    (span_complZeroPairPointHom_one F K)

end Generator

end TauCeti
