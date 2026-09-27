/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.AlgebraicTopology.Singular.Triple

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

Coefficients are an object `R` of an abelian category with coproducts, as everywhere in relative
singular homology; no ring or module structure is needed.

## Main definitions

* `TauCeti.skeletonPair`, `TauCeti.skeletonTriple`: the pair and the triple of consecutive
  skeleta.
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

/-- The `n`-th stage `skeletonLT C n` of the skeletal filtration, as an object of `TopCat`. -/
abbrev skeletonObj (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT C (n : ℕ∞) : Set X)

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
