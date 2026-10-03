/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# The cellular chain complex of a relative CW complex

The skeleta of a relative CW complex filter it by closed subspaces, and the relative singular
homology of consecutive skeleta assembles into a chain complex: the cellular chain complex.  Its
group in degree `n` is `Hₙ(Xⁿ, Xⁿ⁻¹)`, and its differential is the connecting morphism of the long
exact sequence of the triple `(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)` of three consecutive skeleta.  That connecting
morphism factors as `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` through the singular homology of the
middle skeleton.  Composing two consecutive differentials puts the map `Hₙ₊₁(Xⁿ⁺¹) ⟶ Hₙ₊₁(Xⁿ⁺¹, Xⁿ)`
next to the connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ)`; those two are consecutive in the long
exact sequence of the pair `(Xⁿ⁺¹, Xⁿ)`, so they compose to zero, and hence so do the two
differentials.

A degree carrying no cells has equal consecutive skeleta, hence a zero cellular chain group, so
the cellular chain complex of a finite-dimensional complex vanishes in high degrees.

Inclusions between arbitrary skeleta and into the whole complex give maps of pairs relative to
the base. Their induced homology maps connect skeletal relative homology to the homology of the
whole pair `(X, X⁻¹)` and are used in the cellular-to-singular comparison.

Coefficients are an object `R` of an abelian category with coproducts, as everywhere in relative
singular homology; no ring or module structure is needed.

## Main definitions

* `TauCeti.skeletonPair`, `TauCeti.skeletonTriple`: the pair and the triple of consecutive
  skeleta.
* `TauCeti.skeletonBasePair`, `TauCeti.skeletonBaseTriple`: the pair `(Xⁿ, X⁻¹)` of a skeleton
  relative to the base, and the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`.
* `TauCeti.skeletonBasePairToSucc`, `TauCeti.skeletonBasePairToSkeletonPair`: the maps of pairs
  `(Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, X⁻¹)` and `(Xⁿ, X⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`.
* `TauCeti.skeletonBasePairInclusion`: the inclusion `(Xⁿ, X⁻¹) ⟶ (Xᵐ, X⁻¹)` for `n ≤ m`.
* `TauCeti.complexBasePair`: the whole relative CW complex as the pair `(X, X⁻¹)`.
* `TauCeti.skeletonBasePairToComplex`: the inclusion `(Xⁿ, X⁻¹) ⟶ (X, X⁻¹)`.
* `TauCeti.cellularChainGroup`: the relative homology `Hₙ(Xⁿ, Xⁿ⁻¹)`.
* `TauCeti.cellularDifferential`: the cellular differential.
* `TauCeti.cellularChainComplex`: the resulting chain complex.

## Main results

* `TauCeti.cellularDifferential_eq_singularHomologyδ`: the cellular differential is the
  connecting morphism of the triple of three consecutive skeleta.
* `TauCeti.cellularDifferential_comp_cellularDifferential`: consecutive cellular differentials
  compose to zero.
* `TauCeti.isZero_cellularChainGroup` and `TauCeti.eventually_isZero_cellularChainGroup`:
  vanishing of the cellular chain groups in degrees without cells, and in all high degrees of a
  finite-dimensional complex.

The source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- Consecutive skeleta of a relative CW complex are nested.  This is `skeletonLT_mono` in the
natural-number indexing used by the skeletal filtration below. -/
lemma skeletonLT_subset_skeletonLT_succ (n : ℕ) :
    (skeletonLT C (n : ℕ∞) : Set X) ⊆ skeletonLT C ((n + 1 : ℕ) : ℕ∞) :=
  skeletonLT_mono (mod_cast n.le_succ)

/-- The topological pair of consecutive skeleta of a relative CW complex.  In the indexing used
here `skeletonPair C n` is the pair `(Xⁿ, Xⁿ⁻¹)`: its ambient space is `skeletonLT C (n + 1)`,
the `n`-skeleton, and its subspace is `skeletonLT C n`. -/
abbrev skeletonPair (n : ℕ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of X) (skeletonLT_subset_skeletonLT_succ C n)

/-- The triple `(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)` of three consecutive skeleta of a relative CW complex.  Its
outer pair is `skeletonPair C (n + 1)` and its inner pair is `skeletonPair C n`. -/
abbrev skeletonTriple (n : ℕ) : TopTriple.{w} :=
  TopTriple.ofInclusions (X := TopCat.of X) (skeletonLT_subset_skeletonLT_succ C n)
    (skeletonLT_subset_skeletonLT_succ C (n + 1))

/-- The subspace of the `n`-th skeletal pair is the `(n-1)`-skeleton. -/
@[simp]
lemma skeletonPair_snd (n : ℕ) : (skeletonPair C n).snd = skeletonObj C n := rfl

/-- The ambient space of the `n`-th skeletal pair is the `n`-skeleton. -/
@[simp]
lemma skeletonPair_fst (n : ℕ) : (skeletonPair C n).fst = skeletonObj C (n + 1) := rfl

/-- The base `X⁻¹ = skeletonLT C 0` of the skeletal filtration lies in every skeleton. -/
lemma skeletonLT_zero_subset_skeletonLT (n : ℕ) :
    (skeletonLT C ((0 : ℕ) : ℕ∞) : Set X) ⊆ skeletonLT C (n : ℕ∞) :=
  skeletonLT_mono (mod_cast n.zero_le)

/-- The pair `(Xⁿ, X⁻¹)` of the `n`-skeleton relative to the base of a relative CW complex.  Its
ambient space is `skeletonLT C (n + 1)` and its subspace is `skeletonLT C 0`, which is the base
of the complex (`TauCeti.range_skeletonBasePair_snd`). -/
abbrev skeletonBasePair (n : ℕ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of X) (skeletonLT_zero_subset_skeletonLT C (n + 1))

/-- The subspace of the `n`-th base pair is the `(-1)`-skeleton. -/
lemma skeletonBasePair_snd (n : ℕ) : (skeletonBasePair C n).snd = skeletonObj C 0 := rfl

/-- The ambient space of the `n`-th base pair is the `n`-skeleton. -/
lemma skeletonBasePair_fst (n : ℕ) : (skeletonBasePair C n).fst = skeletonObj C (n + 1) := rfl

/-- The subspace `X⁻¹` of the base pair `(Xⁿ, X⁻¹)` is the base of the relative CW complex. -/
lemma range_skeletonBasePair_snd (n : ℕ) :
    Set.range (fun x : (skeletonBasePair C n).snd ↦ (x.1 : X)) = D :=
  Subtype.range_coe.trans <| by rw [Nat.cast_zero, skeletonLT_zero_eq_base]

/-- The triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`.  Its inner pair is `skeletonBasePair C n`, its total pair is
`skeletonBasePair C (n + 1)`, and its outer pair is `skeletonPair C (n + 1)`
(`TauCeti.innerPair_obj_skeletonBaseTriple`, `TauCeti.totalPair_obj_skeletonBaseTriple`,
`TauCeti.outerPair_obj_skeletonBaseTriple`). -/
abbrev skeletonBaseTriple (n : ℕ) : TopTriple.{w} :=
  TopTriple.ofInclusions (X := TopCat.of X) (skeletonLT_zero_subset_skeletonLT C (n + 1))
    (skeletonLT_subset_skeletonLT_succ C (n + 1))

/-- The inner pair of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` is the base pair `(Xⁿ, X⁻¹)`. -/
lemma innerPair_obj_skeletonBaseTriple (n : ℕ) :
    TopTriple.innerPair.obj (skeletonBaseTriple C n) = skeletonBasePair C n := rfl

/-- The total pair of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` is the base pair `(Xⁿ⁺¹, X⁻¹)`. -/
lemma totalPair_obj_skeletonBaseTriple (n : ℕ) :
    TopTriple.totalPair.obj (skeletonBaseTriple C n) = skeletonBasePair C (n + 1) := rfl

/-- The outer pair of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)` is the skeletal pair `(Xⁿ⁺¹, Xⁿ)`. -/
lemma outerPair_obj_skeletonBaseTriple (n : ℕ) :
    TopTriple.outerPair.obj (skeletonBaseTriple C n) = skeletonPair C (n + 1) := rfl

/-- The inclusion `(Xⁿ, X⁻¹) ⟶ (Xⁿ⁺¹, X⁻¹)` of consecutive base pairs.  It is the map from the
inner pair to the total pair of the triple `TauCeti.skeletonBaseTriple C n`
(`TauCeti.skeletonBasePairToSucc_def`). -/
def skeletonBasePairToSucc (n : ℕ) : skeletonBasePair C n ⟶ skeletonBasePair C (n + 1) :=
  TopTriple.innerToTotal.app (skeletonBaseTriple C n)

/-- `TauCeti.skeletonBasePairToSucc` is the map from the inner pair to the total pair of the
triple `TauCeti.skeletonBaseTriple C n`. -/
lemma skeletonBasePairToSucc_def (n : ℕ) :
    skeletonBasePairToSucc C n = TopTriple.innerToTotal.app (skeletonBaseTriple C n) := (rfl)

/-- The map of pairs `(Xⁿ, X⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)` which is the identity on `Xⁿ`. -/
def skeletonBasePairToSkeletonPair (n : ℕ) : skeletonBasePair C n ⟶ skeletonPair C n :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.id _)
    fun _ hx ↦ skeletonLT_zero_subset_skeletonLT C n hx

/-- On the ambient spaces, `TauCeti.skeletonBasePairToSucc` is the inclusion `Xⁿ ⊆ Xⁿ⁺¹`. -/
@[simp]
lemma coe_skeletonBasePairToSucc_fst_apply (n : ℕ) (x : (skeletonBasePair C n).fst) :
    (TopPair.Hom.fst (skeletonBasePairToSucc C n) x).1 = x.1 :=
  congrArg (fun f ↦ (f x).1) (TopTriple.innerToTotal_app_fst (T := skeletonBaseTriple C n))

/-- On the subspaces, `TauCeti.skeletonBasePairToSucc` is the identity of `X⁻¹`. -/
@[simp]
lemma skeletonBasePairToSucc_snd_apply (n : ℕ) (x : (skeletonBasePair C n).snd) :
    TopPair.Hom.snd (skeletonBasePairToSucc C n) x = x :=
  congrArg (fun f ↦ f x) (TopTriple.innerToTotal_app_snd (T := skeletonBaseTriple C n))

/-- On the ambient spaces, `TauCeti.skeletonBasePairToSkeletonPair` is the identity of `Xⁿ`. -/
lemma skeletonBasePairToSkeletonPair_fst_apply (n : ℕ) (x : (skeletonBasePair C n).fst) :
    TopPair.Hom.fst (skeletonBasePairToSkeletonPair C n) x = x :=
  TopPair.ofInclusionMap_fst_apply _ _ _

/-- On the subspaces, `TauCeti.skeletonBasePairToSkeletonPair` is the inclusion `X⁻¹ ⊆ Xⁿ⁻¹`. -/
lemma coe_skeletonBasePairToSkeletonPair_snd_apply (n : ℕ) (x : (skeletonBasePair C n).snd) :
    (TopPair.Hom.snd (skeletonBasePairToSkeletonPair C n) x).1 = x.1 :=
  TopPair.ofInclusionMap_snd_apply _ _ _

/-- In degree `0` the map `(X⁰, X⁻¹) ⟶ (X⁰, X⁻¹)` is the identity. -/
@[simp]
lemma skeletonBasePairToSkeletonPair_zero :
    skeletonBasePairToSkeletonPair C 0 = 𝟙 (skeletonPair C 0) := by
  ext x : 2
  · exact Subtype.ext (coe_skeletonBasePairToSkeletonPair_snd_apply C 0 x)
  · exact skeletonBasePairToSkeletonPair_fst_apply C 0 x

/-- In positive degree the map `(Xⁿ⁺¹, X⁻¹) ⟶ (Xⁿ⁺¹, Xⁿ)` is the map from the total pair to the
outer pair of the triple `(Xⁿ⁺¹, Xⁿ, X⁻¹)`. -/
lemma skeletonBasePairToSkeletonPair_succ (n : ℕ) :
    skeletonBasePairToSkeletonPair C (n + 1) =
      TopTriple.totalToOuter.app (skeletonBaseTriple C n) := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · refine Eq.trans ?_ (TopTriple.totalToOuter_app_snd (T := skeletonBaseTriple C n)).symm
    ext x
    exact Subtype.ext (coe_skeletonBasePairToSkeletonPair_snd_apply C (n + 1) x)
  · refine Eq.trans ?_ (TopTriple.totalToOuter_app_fst (T := skeletonBaseTriple C n)).symm
    ext x
    exact skeletonBasePairToSkeletonPair_fst_apply C (n + 1) x

/-- Inclusion of base pairs `(Xⁿ, X⁻¹) ⟶ (Xᵐ, X⁻¹)` for `n ≤ m`. -/
def skeletonBasePairInclusion {n m : ℕ} (h : n ≤ m) :
    skeletonBasePair C n ⟶ skeletonBasePair C m :=
  TopPair.ofInclusionMap _ _
    (ContinuousMap.inclusion (skeletonLT_mono (mod_cast Nat.add_le_add_right h 1)))
    (fun _ hx ↦ hx)

@[simp]
lemma coe_skeletonBasePairInclusion_fst_apply {n m : ℕ} (h : n ≤ m)
    (x : (skeletonBasePair C n).fst) :
    (TopPair.Hom.fst (skeletonBasePairInclusion C h) x).1 = x.1 :=
  congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ _)

@[simp]
lemma skeletonBasePairInclusion_snd_apply {n m : ℕ} (h : n ≤ m)
    (x : (skeletonBasePair C n).snd) :
    TopPair.Hom.snd (skeletonBasePairInclusion C h) x = x :=
  Subtype.ext (TopPair.ofInclusionMap_snd_apply _ _ _)

@[simp]
lemma skeletonBasePairInclusion_refl (n : ℕ) :
    skeletonBasePairInclusion C (le_refl n) = 𝟙 _ := by
  exact TopPair.ofInclusionMap_id

/-- Inclusions of base pairs compose as inclusions. -/
@[reassoc]
lemma skeletonBasePairInclusion_comp {n m l : ℕ} (h : n ≤ m) (h' : m ≤ l) :
    skeletonBasePairInclusion C h ≫ skeletonBasePairInclusion C h' =
      skeletonBasePairInclusion C (h.trans h') := by
  unfold skeletonBasePairInclusion
  -- The preservation proofs compute through the subtype inclusions.
  erw [← TopPair.ofInclusionMap_comp]
  rfl

/-- The inclusion into the next base pair is the map of the skeletal triple. -/
lemma skeletonBasePairInclusion_succ (n : ℕ) :
    skeletonBasePairInclusion C n.le_succ = skeletonBasePairToSucc C n := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · ext x
    exact (skeletonBasePairInclusion_snd_apply C n.le_succ x).trans
      (skeletonBasePairToSucc_snd_apply C n x).symm
  · ext x
    exact Subtype.ext ((coe_skeletonBasePairInclusion_fst_apply C _ x).trans
      (coe_skeletonBasePairToSucc_fst_apply C n x).symm)

/-- The whole relative CW complex as a pair with its base `X⁻¹ = skeletonLT C 0`. -/
abbrev complexBasePair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of X) (skeletonLT C 0).subset_complex

/-- The base in `complexBasePair` is the actual base `D` of the relative CW complex. -/
lemma complexBasePair_eq_ofInclusion :
    complexBasePair C = TopPair.ofInclusion (X := TopCat.of X) (base_subset_complex (C := C)) := by
  simp only [complexBasePair, skeletonLT_zero_eq_base]

/-- Inclusion of a skeleton relative to the base into the whole relative CW complex. -/
def skeletonBasePairToComplex (n : ℕ) : skeletonBasePair C n ⟶ complexBasePair C :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion (skeletonLT C _).subset_complex)
    (fun _ hx ↦ hx)

@[simp]
lemma coe_skeletonBasePairToComplex_fst_apply (n : ℕ) (x : (skeletonBasePair C n).fst) :
    (TopPair.Hom.fst (skeletonBasePairToComplex C n) x).1 = x.1 :=
  congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ _)

@[simp]
lemma skeletonBasePairToComplex_snd_apply (n : ℕ) (x : (skeletonBasePair C n).snd) :
    TopPair.Hom.snd (skeletonBasePairToComplex C n) x = x :=
  Subtype.ext (TopPair.ofInclusionMap_snd_apply _ _ _)

/-- Inclusion into the whole pair factors through any larger skeleton. -/
@[reassoc (attr := simp)]
lemma skeletonBasePairInclusion_comp_toComplex {n m : ℕ} (h : n ≤ m) :
    skeletonBasePairInclusion C h ≫ skeletonBasePairToComplex C m =
      skeletonBasePairToComplex C n := by
  unfold skeletonBasePairInclusion skeletonBasePairToComplex
  -- The preservation proofs compute through the subtype inclusions.
  erw [← TopPair.ofInclusionMap_comp]
  rfl

/-- If a skeleton is the whole complex, its inclusion as a pair is an isomorphism. -/
lemma isIso_skeletonBasePairToComplex_of_eq (m : ℕ)
    (hm : (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) = C) :
    IsIso (skeletonBasePairToComplex C m) := by
  have hf : TopPair.Hom.fst (skeletonBasePairToComplex C m) =
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C _).subset_complex) := by
    ext x
    exact Subtype.ext (coe_skeletonBasePairToComplex_fst_apply C m x)
  have : IsIso (TopPair.Hom.fst (skeletonBasePairToComplex C m)) := by
    rw [hf]
    exact ⟨TopCat.ofHom (ContinuousMap.inclusion hm.symm.subset),
      by ext x; rfl, by ext x; rfl⟩
  exact TopPair.isIso_of_isIso_fst_of_surjective_snd _
    (fun x ↦ ⟨x, skeletonBasePairToComplex_snd_apply C m x⟩)

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The singular homology, with coefficients in `R`, of the `n`-th stage of the skeletal
filtration of a relative CW complex, in degree `k`. -/
abbrev skeletonHomology (n k : ℕ) : A := (TopCat.toSSet.obj (skeletonObj C n)).homology R k

/-- The cellular chain group of a relative CW complex in degree `n` with coefficients in `R`: the
relative singular homology `Hₙ(Xⁿ, Xⁿ⁻¹)` of the pair of consecutive skeleta. -/
abbrev cellularChainGroup (n : ℕ) : A := (skeletonPair C n).singularHomology R n

/-- The connecting morphism `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ)` of the long exact sequence of the skeletal
pair. -/
abbrev skeletonPairδ (n : ℕ) : cellularChainGroup C R (n + 1) ⟶ skeletonHomology C R (n + 1) n :=
  (skeletonPair C (n + 1)).singularHomologyδ R (n + 1) n

/-- The map `Hₙ(Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)` from the singular homology of the `n`-skeleton to the
relative homology of the skeletal pair. -/
abbrev skeletonPairπ (n : ℕ) : skeletonHomology C R (n + 1) n ⟶ cellularChainGroup C R n :=
  (skeletonPair C n).singularHomologyπ R n

/-- The cellular differential `Hₙ₊₁(Xⁿ⁺¹, Xⁿ) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹)`, namely the connecting morphism of
the skeletal pair followed by the map to the relative homology of the next skeletal pair.  It is
the connecting morphism of the triple of three consecutive skeleta, by
`TauCeti.cellularDifferential_eq_singularHomologyδ`. -/
def cellularDifferential (n : ℕ) :
    cellularChainGroup C R (n + 1) ⟶ cellularChainGroup C R n :=
  skeletonPairδ C R n ≫ skeletonPairπ C R n

/-- The cellular differential is the connecting morphism of the skeletal pair followed by the
map to the relative homology of the next skeletal pair. -/
lemma cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ (n : ℕ) :
    cellularDifferential C R n = skeletonPairδ C R n ≫ skeletonPairπ C R n := (rfl)

/-- The cellular differential is the connecting morphism of the long exact sequence of the triple
`(Xⁿ⁺¹, Xⁿ, Xⁿ⁻¹)` of three consecutive skeleta. -/
lemma cellularDifferential_eq_singularHomologyδ (n : ℕ) :
    cellularDifferential C R n = (skeletonTriple C n).singularHomologyδ R (n + 1) n :=
  ((skeletonTriple C n).singularHomologyδ_eq_comp_singularHomologyπ R (n + 1) n).symm

/-- The map from the singular homology of a skeleton to the relative homology of the skeletal
pair below it, followed by the connecting morphism of that pair, is zero: these are consecutive
maps in the long exact sequence of the pair `(Xⁿ⁺¹, Xⁿ)`. -/
@[simp]
lemma skeletonPairπ_comp_skeletonPairδ (n : ℕ) :
    skeletonPairπ C R (n + 1) ≫ skeletonPairδ C R n = 0 :=
  (skeletonPair C (n + 1)).singularHomologyπ_comp_singularHomologyδ R (n + 1) n

/-- Two consecutive cellular differentials compose to zero. -/
@[simp]
lemma cellularDifferential_comp_cellularDifferential (n : ℕ) :
    cellularDifferential C R (n + 1) ≫ cellularDifferential C R n = 0 := by
  simp only [cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ, Category.assoc,
    reassoc_of% skeletonPairπ_comp_skeletonPairδ C R n, zero_comp, comp_zero]

/-- The cellular chain complex of a relative CW complex with coefficients in `R`. -/
def cellularChainComplex : ChainComplex A ℕ :=
  ChainComplex.of (cellularChainGroup C R) (cellularDifferential C R)
    (cellularDifferential_comp_cellularDifferential C R)

/-- The objects of the cellular chain complex are the cellular chain groups. -/
@[simp]
lemma cellularChainComplex_X (n : ℕ) :
    (cellularChainComplex C R).X n = cellularChainGroup C R n := (rfl)

/-- The differentials of the cellular chain complex are the cellular differentials, transported
across `TauCeti.cellularChainComplex_X`. -/
@[simp]
lemma cellularChainComplex_d (n : ℕ) :
    (cellularChainComplex C R).d (n + 1) n =
      eqToHom (cellularChainComplex_X C R (n + 1)) ≫ cellularDifferential C R n ≫
        eqToHom (cellularChainComplex_X C R n).symm := by
  -- The object equations hold by definition, so both transports are identities; the body of
  -- `cellularChainComplex` is not exposed, so reducing its differential needs an `unfold`.
  have h : ∀ m : ℕ, cellularChainComplex_X C R m = rfl := fun _ ↦ Subsingleton.elim _ _
  rw [h (n + 1), h n]
  unfold cellularChainComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ChainComplex.of_d _ _ n

end

section Vanishing

variable (n : ℕ) [IsEmpty (cell C n)]

/-- A relative CW complex with no `n`-cells has equal `n`-skeleton and `(n-1)`-skeleton. -/
lemma skeletonLT_succ_eq_of_isEmpty_cell :
    (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) = skeletonLT C (n : ℕ∞) := by
  push_cast
  rw [← skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
  simp

/-- With no `n`-cells the inclusion `Xⁿ⁻¹ ⟶ Xⁿ` of the skeletal pair is an isomorphism. -/
lemma isIso_skeletonPair_map : IsIso (skeletonPair C n).map :=
  ⟨⟨TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_succ_eq_of_isEmpty_cell C n).subset),
    by ext x; rfl, by ext x; rfl⟩⟩

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The cellular chain group of a degree carrying no cells is zero: the two skeleta of the
skeletal pair agree, so its relative singular chain complex vanishes. -/
lemma isZero_cellularChainGroup : IsZero (cellularChainGroup C R n) := by
  have h : IsIso (skeletonPair C n).map := isIso_skeletonPair_map C n
  have h' : IsIso (TopCat.toSSet.map (skeletonPair C n).map) := inferInstance
  have h'' : IsIso (TopPair.toSSetPair.obj (skeletonPair C n)).hom := h'
  exact (HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n).map_isZero
    (SSetPair.isZero_chainComplex _ R)

end Vanishing

/-- The cellular chain groups of a finite-dimensional relative CW complex vanish in all
sufficiently large degrees. -/
lemma eventually_isZero_cellularChainGroup [FiniteDimensional C] {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A] (R : A) :
    ∀ᶠ n in Filter.atTop, IsZero (cellularChainGroup C R n) :=
  FiniteDimensional.eventually_isEmpty_cell.mono fun n hn ↦
    have : IsEmpty (cell C n) := hn
    isZero_cellularChainGroup C n R

end TauCeti
