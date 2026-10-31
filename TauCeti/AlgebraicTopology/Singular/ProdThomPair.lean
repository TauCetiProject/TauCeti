/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Analysis.Convex.Star
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative
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
`B × F → B` is a homotopy equivalence.

The isomorphism is built from a choice of such a step for each proper subspace of `F`, made
independently of `B`; for these choices it is natural in `B`.

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

/-- The pair `(B × F, B × (F ∖ W))` for a subspace `W` of `F`. -/
private abbrev pair (B : Type w) [TopologicalSpace B] (W : Submodule ℝ F) : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (B × F)) {p | p.2 ∉ W}

/-- The map of pairs `(B × F, B × (F ∖ W)) ⟶ (B' × F, B' × (F ∖ W))` induced by `g : B → B'`. -/
private def pairMap (g : C(B, B')) (W : Submodule ℝ F) : pair B W ⟶ pair B' W :=
  TopPair.ofSubsetMap (TopCat.ofHom (g.prodMap (ContinuousMap.id F))) fun _ hp ↦ hp

/-- The complement in `B × F` of `B` times the closed half-subspace `{x ∈ W | φ x ≤ 0}`. -/
private def halfCompl (B : Type w) [TopologicalSpace B] (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) :
    Set (TopCat.of (B × F)) :=
  {p | ¬ (p.2 ∈ W ∧ φ p.2 ≤ 0)}

variable (B) in
private lemma isOpen_halfCompl [FiniteDimensional ℝ F] (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) :
    IsOpen (halfCompl B W φ) :=
  ((W.closed_of_finiteDimensional.preimage continuous_snd).inter
    (isClosed_le (φ.continuous_of_finiteDimensional.comp continuous_snd)
      continuous_const)).isOpen_compl

variable (B) in
/-- The relative homology of `B × F` modulo the complement of a closed half-subspace vanishes:
`B × F` deforms into that complement along straight lines towards `v`. -/
private lemma isZero_singularHomology_halfCompl {W : Submodule ℝ F} {φ : F →ₗ[ℝ] ℝ} {v : F}
    (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (halfCompl B W φ)).singularHomology R n) := by
  let P := TopPair.ofSubset (halfCompl B W φ)
  have hmem : ∀ p : B × F, (p.1, v) ∈ halfCompl B W φ := fun p h ↦ by
    norm_num [hφv] at h
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

/-- The data of one step of the computation: a subspace `W'` containing `W` with one more
dimension, together with a functional `φ` cutting out `W` in `W'` and a vector `v ∈ W'` with
`φ v = 1`. -/
private structure Step (W : Submodule ℝ F) where
  /-- The larger subspace. -/
  W' : Submodule ℝ F
  /-- The functional cutting out `W` inside `W'`. -/
  φ : F →ₗ[ℝ] ℝ
  /-- The vector of `W'` on which `φ` is one. -/
  v : F
  v_mem : v ∈ W'
  apply_v : φ v = 1
  le : W ≤ W'
  apply_eq_zero : ∀ x ∈ W, φ x = 0
  mem_of_apply_eq_zero : ∀ x ∈ W', φ x = 0 → x ∈ W
  finrank_eq : finrank ℝ W' = finrank ℝ W + 1

/-- Every proper subspace admits a step. -/
private lemma nonempty_step [FiniteDimensional ℝ F] {W : Submodule ℝ F} (hW : W ≠ ⊤) :
    Nonempty (Step W) := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra! h
    exact hW (eq_top_iff.2 fun x _ ↦ h x)
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  replace hfW : ∀ x ∈ W, f x = 0 := fun x hx ↦
    (Submodule.mem_bot ℝ).1 (hfW ▸ Submodule.mem_map_of_mem hx)
  refine ⟨⟨W ⊔ ℝ ∙ v, (f v)⁻¹ • f, v,
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self v), ?_, le_sup_left,
    fun x hx ↦ ?_, fun x hx hφx ↦ ?_, ?_⟩⟩
  · simp [inv_mul_cancel₀ hfv]
  · simp [hfW x hx]
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have ha : a = 0 := by simpa [hfW y hy, hfv] using hφx
    simpa [ha] using hy
  · exact Submodule.finrank_sup_span_singleton hv

variable (B) {W : Submodule ℝ F}

private lemma halfCompl_union (s : Step W) :
    halfCompl B s.W' s.φ ∪ halfCompl B s.W' (-s.φ) = {p | p.2 ∉ W} := by
  ext p
  simp only [halfCompl, Set.mem_union, Set.mem_ofPred_eq, LinearMap.neg_apply, neg_nonpos]
  constructor
  · rintro (h | h) hp <;> exact h ⟨s.le hp, by simp [s.apply_eq_zero _ hp]⟩
  · intro hp
    by_contra! h
    exact hp (s.mem_of_apply_eq_zero _ h.1.1 (le_antisymm h.1.2 h.2.2))

private lemma halfCompl_inter (s : Step W) :
    halfCompl B s.W' s.φ ∩ halfCompl B s.W' (-s.φ) = {p | p.2 ∉ s.W'} := by
  ext p
  simp only [halfCompl, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.neg_apply, neg_nonpos]
  constructor
  · rintro ⟨h₁, h₂⟩ hp
    rcases le_total (s.φ p.2) 0 with h | h
    exacts [h₁ ⟨hp, h⟩, h₂ ⟨hp, h⟩]
  · intro hp
    exact ⟨fun h ↦ hp h.1, fun h ↦ hp h.1⟩

/-- The identification of `(B × F, B × (F ∖ W))` with the pair modulo the union of the two
half-subspace complements of a step. -/
private def unionIso (s : Step W) :
    pair B W ≅ TopPair.ofSubset (halfCompl B s.W' s.φ ∪ halfCompl B s.W' (-s.φ)) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun p ↦ by rw [halfCompl_union]; rfl

/-- The identification of the pair modulo the intersection of the two half-subspace complements of
a step with `(B × F, B × (F ∖ W'))`. -/
private def interIso (s : Step W) :
    TopPair.ofSubset (halfCompl B s.W' s.φ ∩ halfCompl B s.W' (-s.φ)) ≅ pair B s.W' :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun p ↦ by rw [halfCompl_inter]; rfl

private lemma isZero_biprod (s : Step W) (n : ℕ) :
    IsZero ((TopPair.ofSubset (halfCompl B s.W' s.φ)).singularHomology R n ⊞
      (TopPair.ofSubset (halfCompl B s.W' (-s.φ))).singularHomology R n) :=
  biprod_isZero_iff _ _ |>.2 ⟨isZero_singularHomology_halfCompl R B s.v_mem s.apply_v n,
    isZero_singularHomology_halfCompl R B (neg_mem s.v_mem) (by simp [s.apply_v]) n⟩

variable [FiniteDimensional ℝ F]

private lemma isIso_relativeMayerVietorisδ (s : Step W) (n : ℕ) :
    IsIso (TopCat.relativeMayerVietorisδ R (isOpen_halfCompl B s.W' s.φ)
      (isOpen_halfCompl B s.W' (-s.φ)) (n + 1) n rfl) := by
  have := (TopCat.relativeMayerVietoris_exact₃ R (isOpen_halfCompl B s.W' s.φ)
    (isOpen_halfCompl B s.W' (-s.φ)) (n + 1) n rfl).mono_g ((isZero_biprod R B s _).eq_of_src _ _)
  have := (TopCat.relativeMayerVietoris_exact₁ R (isOpen_halfCompl B s.W' s.φ)
    (isOpen_halfCompl B s.W' (-s.φ)) (n + 1) n rfl).epi_f ((isZero_biprod R B s _).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- One step of the computation: `Hₙ₊₁(B × F, B × (F ∖ W)) ≅ Hₙ(B × F, B × (F ∖ W'))`. -/
private def stepIso (s : Step W) (n : ℕ) :
    (pair B W).singularHomology R (n + 1) ≅ (pair B s.W').singularHomology R n :=
  haveI := isIso_relativeMayerVietorisδ R B s n
  asIso (TopPair.singularHomologyMap (unionIso B s).hom R (n + 1)) ≪≫
    asIso (TopCat.relativeMayerVietorisδ R (isOpen_halfCompl B s.W' s.φ)
      (isOpen_halfCompl B s.W' (-s.φ)) (n + 1) n rfl) ≪≫
    asIso (TopPair.singularHomologyMap (interIso B s).hom R n)

private lemma isZero_singularHomology_zero (s : Step W) :
    IsZero ((pair B W).singularHomology R 0) := by
  have := TopCat.epi_relativeMayerVietorisFromBiprod_zero R (isOpen_halfCompl B s.W' s.φ)
    (isOpen_halfCompl B s.W' (-s.φ))
  exact ((isZero_biprod R B s 0).of_epi (TopCat.relativeMayerVietorisFromBiprod R _ _ 0)).of_iso
    (asIso (TopPair.singularHomologyMap (unionIso B s).hom R 0))

/-- A chosen step from a proper subspace. -/
private def step (W : Submodule ℝ F) (hW : W ≠ ⊤) : Step W :=
  (nonempty_step hW).some

/-- `Hₙ(B × F, B × (F ∖ W)) = 0` below the codimension of `W`. -/
private lemma isZero_singularHomology_pair_of_lt :
    ∀ (n : ℕ) (W : Submodule ℝ F), n + finrank ℝ W < finrank ℝ F →
      IsZero ((pair B W).singularHomology R n)
  | 0, W, h =>
    isZero_singularHomology_zero R B (step W (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne)
  | n + 1, W, h =>
    let s := step W (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    (isZero_singularHomology_pair_of_lt n s.W' (by rw [s.finrank_eq]; omega)).of_iso
      (stepIso R B s n)

/-- The identification of `(B × F, B × (F ∖ W))` with `(B × F, ∅)` for `W` of full dimension. -/
private def topIso {W : Submodule ℝ F} (hW : finrank ℝ W = finrank ℝ F) :
    pair B W ≅ pair B (⊤ : Submodule ℝ F) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun p ↦ by
    rw [Submodule.eq_top_of_finrank_eq hW]
    rfl

/-- `Hₘ(B × F, B × (F ∖ W)) ≅ Hₙ(B × F, ∅)` for `m = n + c`, with `c` the codimension of `W`,
by `c` successive steps. -/
private def chainIso : ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F →
    ∀ (n m : ℕ), n + c = m →
      ((pair B W).singularHomology R m ≅ (pair B (⊤ : Submodule ℝ F)).singularHomology R n)
  | 0, _, hW, n, _, rfl => asIso (TopPair.singularHomologyMap (topIso B hW).hom R n)
  | c + 1, W, hW, n, _, rfl =>
    let s := step W (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    stepIso R B s (n + c) ≪≫ chainIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

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
    simp only [Set.mem_ofPred_eq, Submodule.mem_bot]
    rfl

/-! ### Naturality in the base -/

variable (g : C(B, B'))

@[reassoc]
private lemma stepIso_hom_naturality {W : Submodule ℝ F} (s : Step W) (n : ℕ) :
    (stepIso R B s n).hom ≫ TopPair.singularHomologyMap (pairMap g s.W') R n =
      TopPair.singularHomologyMap (pairMap g W) R (n + 1) ≫ (stepIso R B' s n).hom := by
  let f : TopCat.of (B × F) ⟶ TopCat.of (B' × F) :=
    TopCat.ofHom (g.prodMap (ContinuousMap.id F))
  have hU : Set.MapsTo f (halfCompl B s.W' s.φ) (halfCompl B' s.W' s.φ) := fun _ hp ↦ hp
  have hV : Set.MapsTo f (halfCompl B s.W' (-s.φ)) (halfCompl B' s.W' (-s.φ)) := fun _ hp ↦ hp
  have hinter : (interIso B s).hom ≫ pairMap g s.W' =
      TopPair.ofSubsetMap f (hU.inter_inter hV) ≫ (interIso B' s).hom := by
    simp only [interIso, pairMap, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  have hunion : (unionIso B s).hom ≫ TopPair.ofSubsetMap f (hU.union_union hV) =
      pairMap g W ≫ (unionIso B' s).hom := by
    simp only [unionIso, pairMap, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  simp only [stepIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← TopPair.singularHomologyMap_comp, hinter, TopPair.singularHomologyMap_comp,
    TopCat.relativeMayerVietorisδ_naturality_assoc R _ _ (isOpen_halfCompl B' s.W' s.φ)
      (isOpen_halfCompl B' s.W' (-s.φ)) f hU hV (n + 1) n rfl,
    ← TopPair.singularHomologyMap_comp_assoc, hunion,
    TopPair.singularHomologyMap_comp_assoc]

@[reassoc]
private lemma chainIso_hom_naturality : ∀ (c : ℕ) (W : Submodule ℝ F)
    (hW : finrank ℝ W + c = finrank ℝ F) (n m : ℕ) (h : n + c = m),
    (chainIso R B c W hW n m h).hom ≫ TopPair.singularHomologyMap (pairMap g ⊤) R n =
      TopPair.singularHomologyMap (pairMap g W) R m ≫ (chainIso R B' c W hW n m h).hom
  | 0, W, hW, n, _, rfl => by
    have h : (topIso B hW).hom ≫ pairMap g ⊤ = pairMap g W ≫ (topIso B' hW).hom := by
      simp only [topIso, pairMap, TopPair.ofSubsetIso_hom]
      exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
    rw [chainIso, chainIso, asIso_hom, asIso_hom, ← TopPair.singularHomologyMap_comp, h,
      TopPair.singularHomologyMap_comp]
    rfl
  | c + 1, W, hW, n, _, rfl => by
    rw [chainIso, chainIso, Iso.trans_hom, Iso.trans_hom, Category.assoc,
      chainIso_hom_naturality c, stepIso_hom_naturality_assoc]
    rfl

omit [FiniteDimensional ℝ F] in
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

omit [FiniteDimensional ℝ F] in
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

omit [FiniteDimensional ℝ F] in
private lemma botIso_hom_naturality :
    (botIso B F).hom ≫ pairMap g ⊥ = prodThomPairMap F g ≫ (botIso B' F).hom := by
  simp only [botIso, pairMap, prodThomPairMap, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl

end ProdThomPair

open ProdThomPair

variable (B F) [FiniteDimensional ℝ F]

/-- **The relative homology of the Thom pair of a product bundle vanishes below the rank**:
`Hₙ(B × F, B × (F ∖ {0})) = 0` for `n < dim F`. -/
theorem isZero_singularHomology_prodThomPair {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((prodThomPair B F).singularHomology R n) :=
  (isZero_singularHomology_pair_of_lt R B n ⊥ (by simpa using hn)).of_iso
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
    chainIso R B (finrank ℝ F) ⊥ (by simp) n m h ≪≫ emptyIso R B F n

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
  rw [emptyIso_hom_naturality, chainIso_hom_naturality_assoc,
    ← TopPair.singularHomologyMap_comp_assoc (botIso B F).hom, botIso_hom_naturality,
    TopPair.singularHomologyMap_comp_assoc]

end TauCeti
