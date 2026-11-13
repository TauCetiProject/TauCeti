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
* `TauCeti.prodThomPairPuncturedHomotopyEquiv`: for `e : F ≃L[ℝ] ℝᵈ⁺¹`, the punctured product
  `B × (F ∖ {0})` is homotopy equivalent to `Sᵈ × B` by `(b, x) ↦ (e x / ‖e x‖, b)`.
* `TauCeti.isZero_singularHomology_prodThomPair`: `Hₙ(B × F, B × (F ∖ {0})) = 0` for
  `n < dim F`.
* `TauCeti.prodThomPairSingularHomologyIso`: `Hₙ₊ᵣ(B × F, B × (F ∖ {0})) ≅ Hₙ(B)`, `r = dim F`.
* `TauCeti.prodThomPairSingularHomologyIso_hom_naturality`,
  `TauCeti.prodThomPairSingularHomologyIso_inv_naturality`: its naturality in the base.

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
    (TopPair.Hom.snd (prodThomPairMap F g) p).1 = (g p.1.1, p.1.2) :=
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
    prodThomPairPuncturedProj B F p = p.1.1 :=
  (rfl)

/-- The projection of the punctured product bundle is the restriction of the projection of the
product bundle. -/
@[reassoc]
lemma map_comp_prodThomPairProj :
    (prodThomPair B F).map ≫ prodThomPairProj B F = prodThomPairPuncturedProj B F :=
  (rfl)

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

/-- In the coordinates `e`, the punctured product `B × (F ∖ {0})` is `B × (ℝᵈ⁺¹ ∖ {0})`. -/
private def prodThomPairPuncturedHomeomorph (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd ≃ₜ B × ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  toFun p := (p.1.1, ⟨e p.1.2, by simpa using p.2⟩)
  invFun q := ⟨(q.1, e.symm q.2), fun h ↦ q.2.2 (by simpa using congrArg e h)⟩
  left_inv p := Subtype.ext (by simp)
  right_inv q := Prod.ext rfl (Subtype.ext (by simp))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable (B) in
/-- **The punctured product bundle is homotopy equivalent to a product with a sphere.** For a
continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹`, the complement `B × (F ∖ {0})` of the zero
section of the product bundle `B × F → B` is homotopy equivalent to `Sᵈ × B`, by
`(b, x) ↦ (e x / ‖e x‖, b)`. -/
def prodThomPairPuncturedHomotopyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    ContinuousMap.HomotopyEquiv (prodThomPair B F).snd
      ↑(TopCat.sphere.{w} d ⊗ TopCat.of B : TopCat.{w}) :=
  ((prodThomPairPuncturedHomeomorph e).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl B).prodCongr (complSingletonHomotopyEquivSphere 0))).trans
    ((Homeomorph.prodComm _ _).trans
      ((Homeomorph.ulift.{w}).symm.prodCongr (Homeomorph.refl B))).toHomotopyEquiv

/-- The second component of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is the base point. -/
@[simp]
theorem prodThomPairPuncturedHomotopyEquiv_apply_snd (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (p : (prodThomPair B F).snd) :
    (prodThomPairPuncturedHomotopyEquiv B e p).2 = p.1.1 :=
  (rfl)

/-- The first component of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is the radial projection
`(b, x) ↦ e x / ‖e x‖` onto the unit sphere of `ℝᵈ⁺¹`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquiv_apply_fst
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p : (prodThomPair B F).snd) :
    ((prodThomPairPuncturedHomotopyEquiv B e p).1.down : EuclideanSpace ℝ (Fin (d + 1))) =
      ‖e p.1.2‖⁻¹ • e p.1.2 :=
  (coe_complSingletonHomotopyEquivSphere_apply _ ⟨e p.1.2, _⟩).trans (by simp)

/-- The homotopy inverse of `TauCeti.prodThomPairPuncturedHomotopyEquiv` is
`(s, b) ↦ (b, e⁻¹ s)`. -/
@[simp]
theorem coe_prodThomPairPuncturedHomotopyEquiv_symm_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (q : ↑(TopCat.sphere.{w} d ⊗ TopCat.of B : TopCat.{w})) :
    ((prodThomPairPuncturedHomotopyEquiv B e).symm q).1 = (q.2, e.symm q.1.down) :=
  Prod.ext rfl (congrArg e.symm
    ((coe_complSingletonHomotopyEquivSphere_symm_apply _ q.1.down).trans (add_zero _)))

end Punctured

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {B : Type w} [TopologicalSpace B] {B' : Type w} [TopologicalSpace B']
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ProdThomPair

/-- The projection `B × F → F`. -/
private abbrev proj (B : Type w) [TopologicalSpace B] : C(TopCat.of (B × F), F) :=
  ContinuousMap.snd

/-- The pair `(B × F, B × (F ∖ W))` for a subspace `W` of `F`. -/
private abbrev pair (B : Type w) [TopologicalSpace B] (W : Submodule ℝ F) : TopPair.{w} :=
  subspaceComplPair (proj B) W

/-- The map of pairs `(B × F, B × (F ∖ W)) ⟶ (B' × F, B' × (F ∖ W))` induced by `g : B → B'`. -/
private abbrev pairMap (g : C(B, B')) (W : Submodule ℝ F) : pair B W ⟶ pair B' W :=
  subspaceComplPairMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) (fun _ ↦ rfl) W

/-- The complement in `B × F` of `B` times the closed half-subspace `{x ∈ W | φ x ≤ 0}`. -/
private abbrev halfCompl (B : Type w) [TopologicalSpace B] (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) :
    Set (TopCat.of (B × F)) :=
  proj B ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ

variable (B) in
/-- The relative homology of `B × F` modulo the complement of a closed half-subspace vanishes:
`B × F` deforms into that complement along straight lines towards `v`. -/
private lemma isZero_singularHomology_halfCompl (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F)
    (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (halfCompl B W φ)).singularHomology R n) := by
  let P := TopPair.ofSubset (halfCompl B W φ)
  have hmem : ∀ p : B × F, (p.1, v) ∈ halfCompl B W φ := fun p h ↦
    (hφv ▸ one_pos : 0 < φ v).not_ge h.2
  let c : TopCat.of (B × F) ⟶ TopCat.of (B × F) :=
    TopCat.ofHom ⟨fun p ↦ (p.1, v), by fun_prop⟩
  let H : (TopCat.Hom.hom (𝟙 (TopCat.of (B × F)))).Homotopy c.hom :=
    { toFun q := (q.2.1, (q.1 : ℝ) • v + (1 - (q.1 : ℝ)) • q.2.2)
      continuous_toFun := by fun_prop
      map_zero_left _ := by simp
      map_one_left _ := by simp [c] }
  have hH := TopPair.ofSubsetHomotopy (B := halfCompl B W φ) (B' := halfCompl B W φ) H
    fun τ p hp ↦ starConvex_compl_setOf_mem_and_nonpos hv (by simp [hφv]) hp τ.2.1
      (sub_nonneg.2 τ.2.2) (add_sub_cancel _ _)
  let g : P.fst ⟶ P.snd :=
    TopCat.ofHom ⟨fun p ↦ ⟨(p.1, v), hmem p⟩, by fun_prop⟩
  refine TopPair.isZero_singularHomology_of_homotopy
    (f := TopPair.ofSubsetMap c fun p _ ↦ hmem p) ?_ g ?_ R n
  · rw [← TopPair.ofSubsetMap_id (B := halfCompl B W φ) fun _ hx ↦ hx]
    exact hH
  · ext p
    exact (TopPair.ofSubsetMap_fst_apply _ _ p).symm

variable (B)

private instance : IsEmpty (pair B (⊤ : Submodule ℝ F)).snd :=
  ⟨fun p ↦ p.2 Submodule.mem_top⟩

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
    simp only [Set.mem_ofPred_eq]
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
      TopPair.singularHomologyMap (pairMap g ⊤) R n ≫ (emptyIso R B' F n).hom := by
  let H := (AlgebraicTopology.singularHomologyFunctor C n).obj R
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(B × F, B)) ≫ TopCat.ofHom g =
      TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F)) ≫
        TopCat.ofHom (ContinuousMap.fst : C(B' × F, B')) := by
    have hpair : TopPair.Hom.fst (pairMap g (⊤ : Submodule ℝ F)) =
        TopCat.ofHom (g.prodMap (ContinuousMap.id F)) :=
      subspaceComplPairMap_fst _ _ _
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
    (hmap.trans ((congrArg (H.map (TopPair.Hom.fst (pairMap g ⊤)) ≫ ·)
      (singularHomologyπ_emptyIso_hom R B' F n).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (emptyIso R B' F n).hom)
        (TopPair.singularHomologyπ_naturality (pairMap g ⊤) R n)).trans
        (Category.assoc _ _ _)))))

private lemma botIso_hom_naturality :
    (botIso B F).hom ≫ pairMap g ⊥ = prodThomPairMap F g ≫ (botIso B' F).hom := by
  have h : pairMap g (⊥ : Submodule ℝ F) =
      TopPair.ofSubsetMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) fun _ hx ↦ hx :=
    subspaceComplPairMap_eq_ofSubsetMap _ _ _ _
  simp only [botIso, h, prodThomPairMap, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl

end ProdThomPair

open ProdThomPair

variable (B F) [FiniteDimensional ℝ F]

/-- **The relative homology of the Thom pair of a product bundle vanishes below the rank**:
`Hₙ(B × F, B × (F ∖ {0})) = 0` for `n < dim F`. -/
theorem isZero_singularHomology_prodThomPair {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((prodThomPair B F).singularHomology R n) :=
  (isZero_singularHomology_subspaceComplPair R (proj B) (isZero_singularHomology_halfCompl R B) n
    ⊥ (by simpa using hn)).of_iso
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
    subspaceComplPairSingularHomologyIso R (proj B) (isZero_singularHomology_halfCompl R B)
      (finrank ℝ F) ⊥ (by simp) n m h ≪≫ emptyIso R B F n

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
      (isZero_singularHomology_halfCompl R B) (isZero_singularHomology_halfCompl R B')
      (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) (fun _ ↦ rfl),
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

end TauCeti
