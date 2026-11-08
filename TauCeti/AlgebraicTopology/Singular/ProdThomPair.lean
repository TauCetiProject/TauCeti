/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Analysis.Convex.Star
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl
public import TauCeti.Topology.Homotopy.HomotopyEquiv

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
* `TauCeti.isZero_singularHomology_prodThomPair`: `Hₙ(B × F, B × (F ∖ {0})) = 0` for
  `n < dim F`.
* `TauCeti.prodThomPairSingularHomologyIso`: `Hₙ₊ᵣ(B × F, B × (F ∖ {0})) ≅ Hₙ(B)`, `r = dim F`.
* `TauCeti.prodThomPairSingularHomologyIso_hom_naturality`: its naturality in the base.

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

/-- The projection `(pt × F, pt × (F ∖ {0})) ⟶ (F, F ∖ {0})` of the Thom pair of the product bundle
over a point onto its fibre pair. -/
def prodThomPairPUnitSnd :
    prodThomPair PUnit.{w + 1} F ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) fun _ hp ↦ hp

/-- Over a point, the projection to the fibre is a retraction of the fibre inclusion. -/
theorem prodThomPairPUnitSnd_comp_prodThomPairFiberMap :
    prodThomPairPUnitSnd F ≫ prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1}) = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
    (prodThomPairFiberMap_fst_apply F _ _).trans
      (congrArg (Prod.mk PUnit.unit) (TopPair.ofSubsetMap_fst_apply _ _ p)))

end Defs

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
    (show ¬ φ v ≤ 0 by norm_num [hφv]) h.2
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
      TopPair.ofSubsetMap_fst _ _
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
  simp only [botIso, pairMap, subspaceComplPairMap, prodThomPairMap, TopPair.ofSubsetIso_hom]
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

end TauCeti
