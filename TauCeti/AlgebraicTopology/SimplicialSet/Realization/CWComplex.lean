/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import TauCeti.AlgebraicTopology.RelativeCellComplex.Map
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Boundary
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Map

/-!
# The CW structure on geometric realizations of simplicial sets

This file equips the geometric realization `|X|` of any simplicial set `X` with its canonical
CW complex structure, with one `n`-cell for each nondegenerate `n`-simplex of `X` and
characteristic map `SSet.toTopObjMk σ.1 ∘ TauCeti.standardCellBallToOrderedSimplex n`.

For any monomorphism `i : X ⟶ Y` in `SSet`, transporting Mathlib's simplicial relative cell complex
`SSet.relativeCellComplexOfMono i` along the left adjoint `SSet.toTop` and reindexing its basic
cells along `SSet.toTopBoundaryInclusionArrowIso` yields a categorical relative CW complex
`SSet.toTopRelativeCWComplex i : TopCat.RelativeCWComplex (SSet.toTop.map i)`. In particular,
monomorphisms of simplicial sets realize to closed embeddings (`SSet.isClosedEmbedding_toTop_map`),
every realization `|X|` carries a categorical CW structure (`SSet.toTopCWComplex X`), is Hausdorff
(`SSet.t2Space_toTop`), has CW type (`SSet.cwType_toTop`), and receives a classical CW structure
`TauCeti.simplicialRealizationCW X`.

Under this CW structure:
* the `n`-cells identify canonically with `X.nonDegenerate n`
  (`TauCeti.simplicialRealizationCWCellEquiv`), with characteristic maps given explicitly by
  `TauCeti.simplicialRealizationCW_map_apply`;
* the realization of `X.skeleton n` is `skeletonLT univ n`, so `|X.skeleton (n + 1)|` is the
  classical `n`-skeleton `CWComplex.skeleton univ n` (`SSet.range_toTop_map_skeleton_ι`,
  `SSet.range_toTop_map_skeleton_succ_ι`);
* every simplicial map `f : X ⟶ Y` realizes to a cellular map (`SSet.mapsTo_toTop_map_skeletonLT`,
  `SSet.isCellular_toTop_map`);
* every subcomplex `A : X.Subcomplex` realizes to a CW subcomplex
  (`SSet.Subcomplex.toTopCWSubcomplex`), so the image of any monomorphism is a CW subcomplex
  (`SSet.range_toTop_map_eq_toTopCWSubcomplex`);
* every compact subset of `|X|` is contained in the realization of a finite simplicial subcomplex
  (`SSet.exists_finite_subcomplex_of_isCompact`).

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, Chapter III, Theorem 14.1.
* A. Hatcher, *Algebraic Topology*, Appendix, Propositions A.1 and A.2.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial Metric Topology HomotopicalAlgebra

universe u

namespace SSet

/-- The geometric realization of a monomorphism `i : X ⟶ Y` of simplicial sets carries a canonical
categorical relative CW complex structure, obtained by transporting `relativeCellComplexOfMono i`
along the left adjoint `SSet.toTop` and replacing each realized simplex boundary inclusion
`|∂Δ[n].ι|` by `TopCat.diskBoundaryInclusion n` via `SSet.toTopBoundaryInclusionArrowIso n`. -/
def toTopRelativeCWComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.RelativeCWComplex (toTop.map i) :=
  haveI : PreservesWellOrderContinuousOfShape ℕ toTop.{u} := ⟨fun _ _ ↦ inferInstance⟩
  ((relativeCellComplexOfMono i).map toTop).reindexCellTypes
    TopCat.RelativeCWComplex.basicCell (fun _ _ ↦ .unit)
    fun n _ ↦ toTopBoundaryInclusionArrowIso n

/-- **Monomorphisms of simplicial sets realize to closed embeddings.** -/
theorem isClosedEmbedding_toTop_map {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    IsClosedEmbedding (toTop.map i) :=
  (toTopRelativeCWComplex i).isClosedEmbedding

private def isInitialToTopBot (X : SSet.{u}) :
    IsInitial |((⊥ : X.Subcomplex) : SSet.{u})| :=
  IsInitial.ofUniqueHom
    (fun T ↦ (sSetTopAdj.homEquiv _ T).symm (Subcomplex.isInitialBot.to _))
    (fun T _ ↦ (sSetTopAdj.homEquiv _ T).injective (Subcomplex.isInitialBot.hom_ext _ _))

private def toTopBotArrowIso (X : SSet.{u}) :
    Arrow.mk (toTop.map (Subcomplex.ι (⊥ : X.Subcomplex))) ≅ Arrow.mk (initial.to |X|) :=
  Arrow.isoMk ((isInitialToTopBot X).uniqueUpToIso initialIsInitial) (Iso.refl _)
    ((isInitialToTopBot X).hom_ext _ _)

/-- The canonical categorical CW complex structure on the geometric realization `|X|` of a
simplicial set `X`. -/
def toTopCWComplex (X : SSet.{u}) : TopCat.CWComplex |X| :=
  (toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))).ofArrowIso (toTopBotArrowIso X)

/-- The geometric realization of every simplicial set is Hausdorff. -/
instance t2Space_toTop (X : SSet.{u}) : T2Space |X| :=
  (toTopCWComplex X).t2Space

/-- The geometric realization of every simplicial set has CW type. -/
theorem cwType_toTop (X : SSet.{u}) : TauCeti.CWType |X| :=
  (toTopCWComplex X).cwType

private lemma toTopCWComplex_cells_ι (X : SSet.{u}) (n : ℕ)
    (c : ((toTopCWComplex X).attachCells n (not_isMax n)).ι) :
    (⟨n, not_isMax n, c⟩ : (toTopCWComplex X).Cells).ι =
      (toTopStdSimplexIsoDisk.{u} n).inv ≫
        toTop.map (yonedaEquiv.symm
          (c : relativeCellComplexOfMono.Cell (Subcomplex.ι (⊥ : X.Subcomplex)) n).simplex) := by
  have : PreservesWellOrderContinuousOfShape ℕ toTop.{u} := ⟨fun _ _ ↦ inferInstance⟩
  let c' : relativeCellComplexOfMono.Cell (Subcomplex.ι (⊥ : X.Subcomplex)) n := c
  have h1 : (⟨n, not_isMax n, c⟩ : (toTopCWComplex X).Cells).ι =
      (⟨n, not_isMax n, c'⟩ :
        (toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))).Cells).ι ≫ 𝟙 |X| :=
    RelativeCellComplex.ofArrowIso_cells_ι
      (c := toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex)))
      (toTopBotArrowIso X) n (not_isMax n) c'
  have h2 : (⟨n, not_isMax n, c'⟩ :
      (toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))).Cells).ι =
      Arrow.rightFunc.map (toTopBoundaryInclusionArrowIso.{u} n).inv ≫
        (⟨n, not_isMax n, c'⟩ : ((relativeCellComplex X).map toTop).Cells).ι :=
    RelativeCellComplex.reindexCellTypes_cells_ι
      ((relativeCellComplex X).map toTop) TopCat.RelativeCWComplex.basicCell
      (fun _ _ ↦ .unit) (fun k _ ↦ toTopBoundaryInclusionArrowIso k) n (not_isMax n) c'
  have h3 : (⟨n, not_isMax n, c'⟩ : ((relativeCellComplex X).map toTop).Cells).ι =
      toTop.map (yonedaEquiv.symm c'.simplex) :=
    (RelativeCellComplex.map_cells_ι (relativeCellComplex X) toTop n (not_isMax n) c').trans
      (congrArg toTop.map (relativeCellComplexOfMono.Cell.ι_b_ι c'))
  rw [h1, Category.comp_id, h2, h3]
  exact congrArg (· ≫ _) (toTopBoundaryInclusionArrowIso_inv_right n)

private lemma range_toTop_map_comp_iso {A B C : SSet.{u}} (e : A ≅ B) (g : B ⟶ C) :
    Set.range (toTop.map (e.hom ≫ g)) = Set.range (toTop.map g) := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨toTop.map e.hom a, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  · rintro ⟨b, rfl⟩
    refine ⟨toTop.map e.inv b, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, e.inv_hom_id_assoc]

end SSet

namespace TauCeti

open SSet

/-- The canonical classical CW complex structure on the geometric realization `|X|` of a simplicial
set `X`. Its `n`-cells correspond to the nondegenerate `n`-simplices of `X`, and each characteristic
map is `SSet.toTopObjMk σ.1 ∘ TauCeti.standardCellBallToOrderedSimplex n`. -/
@[instance_reducible]
def simplicialRealizationCW (X : SSet.{u}) : CWComplex (Set.univ : Set |X|) :=
  (SSet.toTopCWComplex X).toCWComplex

/-- The `n`-cells of `simplicialRealizationCW X` are in canonical bijection with the nondegenerate
`n`-simplices of `X`. -/
def simplicialRealizationCWCellEquiv (X : SSet.{u}) (n : ℕ) :
    (simplicialRealizationCW X).cell n ≃ X.nonDegenerate n :=
  ((SSet.toTopCWComplex X).toCWComplexCellEquiv n).trans
    { toFun c := ⟨c.simplex, c.nonDegenerate⟩
      invFun σ := { simplex := σ.1, nonDegenerate := σ.2, notMem := by simp }
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The characteristic map of a cell `i` of `simplicialRealizationCW X` on the closed unit ball is
the simplex map `SSet.toTopObjMk` of the corresponding nondegenerate `n`-simplex, precomposed with
`TauCeti.standardCellBallToOrderedSimplex n`. -/
lemma simplicialRealizationCW_map_apply (X : SSet.{u}) (n : ℕ)
    (i : (simplicialRealizationCW X).cell n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := simplicialRealizationCW X
    RelCWComplex.map (C := (Set.univ : Set |X|)) n i x =
      SSet.toTopObjMk (simplicialRealizationCWCellEquiv X n i).1
        (standardCellBallToOrderedSimplex n x) := by
  let _ := simplicialRealizationCW X
  rw [(toTopCWComplex X).toCWComplex_map_apply n i x, toTopCWComplex_cells_ι,
    ConcreteCategory.comp_apply, toTopStdSimplexIsoDisk_inv_diskHomeomorphClosedBall_symm,
    toTop_map_yonedaEquiv_symm_toTopHomeo_symm]
  rfl

/-- Variant of `simplicialRealizationCW_map_apply` indexed directly by a nondegenerate simplex. -/
lemma simplicialRealizationCW_map_symm_apply (X : SSet.{u}) (n : ℕ) (σ : X.nonDegenerate n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := simplicialRealizationCW X
    RelCWComplex.map (C := (Set.univ : Set |X|)) n
        ((simplicialRealizationCWCellEquiv X n).symm σ) x =
      SSet.toTopObjMk σ.1 (standardCellBallToOrderedSimplex n x) :=
  (simplicialRealizationCW_map_apply X n _ x).trans (by simp)

end TauCeti

namespace SSet

open TauCeti

/-- The realization of `X.skeleton n` is the classical subcomplex `skeletonLT univ n` of
`TauCeti.simplicialRealizationCW X`, the union of all closed cells of dimension `< n`. -/
theorem range_toTop_map_skeleton_ι (X : SSet.{u}) (n : ℕ) :
    letI := simplicialRealizationCW X
    Set.range (toTop.map (X.skeleton n).ι) =
      (RelCWComplex.skeletonLT (Set.univ : Set |X|) n : Set |X|) := by
  let _ := simplicialRealizationCW X
  have heq : (X.skeleton n : X.Subcomplex) =
      skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n := by
    simp [skeletonOfMono]
  have hrange : Set.range ((toTopCWComplex X).incl.app n) =
      Set.range (toTop.map (X.skeleton n).ι) := by
    have hincl : Set.range ((toTopCWComplex X).incl.app n) =
        Set.range (toTop.map (skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n).ι) := by
      have h : (toTopCWComplex X).incl.app n =
          toTop.map (skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n).ι ≫ 𝟙 |X| := rfl
      rw [h, Category.comp_id]
      rfl
    rw [hincl]
    have hι : (skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n).ι =
        (Subcomplex.eqToIso heq.symm).hom ≫ (X.skeleton n).ι := by
      simp
    rw [hι]
    exact range_toTop_map_comp_iso (Subcomplex.eqToIso heq.symm) (X.skeleton n).ι
  rw [← hrange]
  exact (toTopCWComplex X).range_incl_app_eq_toCWComplex_skeletonLT n

/-- The realization of `X.skeleton (n + 1)` is the classical `n`-skeleton
`CWComplex.skeleton univ n` of `TauCeti.simplicialRealizationCW X`. -/
theorem range_toTop_map_skeleton_succ_ι (X : SSet.{u}) (n : ℕ) :
    letI := simplicialRealizationCW X
    Set.range (toTop.map (X.skeleton (n + 1)).ι) =
      (CWComplex.skeleton (Set.univ : Set |X|) n : Set |X|) := by
  let _ := simplicialRealizationCW X
  simpa [CWComplex.skeleton] using range_toTop_map_skeleton_ι X (n + 1)

private lemma skeleton_le_preimage_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    X.skeleton n ≤ (Y.skeleton n).preimage f := by
  -- Expose the defining supremum of `X.skeleton n` without unfolding the `OrderHom` structure.
  change (⨆ (i : Fin n) (x : X.nonDegenerate i), Subcomplex.ofSimplex x.1) ≤ _
  simp only [iSup_le_iff]
  intro k x
  rw [Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage]
  exact Y.mem_skeleton (f.app _ x.1) k.isLt

/-- The geometric realization of any simplicial map preserves every `skeletonLT` stage of
`TauCeti.simplicialRealizationCW`. -/
theorem mapsTo_toTop_map_skeletonLT {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := simplicialRealizationCW X
    letI := simplicialRealizationCW Y
    Set.MapsTo (toTop.map f)
      (RelCWComplex.skeletonLT (Set.univ : Set |X|) n : Set |X|)
      (RelCWComplex.skeletonLT (Set.univ : Set |Y|) n : Set |Y|) := by
  let _ := simplicialRealizationCW X
  let _ := simplicialRealizationCW Y
  rw [← range_toTop_map_skeleton_ι X n, ← range_toTop_map_skeleton_ι Y n]
  let g : (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u}) :=
    Subcomplex.lift ((X.skeleton n).ι ≫ f) (by
      rintro m _ ⟨⟨y, hy⟩, rfl⟩
      exact skeleton_le_preimage_skeleton f n m hy)
  have hg : g ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f := Subcomplex.lift_ι _ _
  rintro _ ⟨x, rfl⟩
  refine ⟨toTop.map g x, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, hg]

/-- The geometric realization of any simplicial map preserves every classical `n`-skeleton of
`TauCeti.simplicialRealizationCW`. -/
theorem mapsTo_toTop_map_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := simplicialRealizationCW X
    letI := simplicialRealizationCW Y
    Set.MapsTo (toTop.map f)
      (CWComplex.skeleton (Set.univ : Set |X|) n : Set |X|)
      (CWComplex.skeleton (Set.univ : Set |Y|) n : Set |Y|) := by
  let _ := simplicialRealizationCW X
  let _ := simplicialRealizationCW Y
  simpa [CWComplex.skeleton] using mapsTo_toTop_map_skeletonLT f (n + 1)

/-- **Every simplicial map realizes to a cellular map** between the canonical CW structures
`TauCeti.simplicialRealizationCW`. -/
theorem isCellular_toTop_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    letI := simplicialRealizationCW X
    letI := simplicialRealizationCW Y
    IsCellular (Set.univ : Set |X|) (Set.univ : Set |Y|)
      (TopCat.ofHom ⟨fun x ↦ ⟨toTop.map f x.1, trivial⟩, by fun_prop⟩) :=
  fun n _ hx ↦ mapsTo_toTop_map_skeletonLT f n hx

namespace Subcomplex

/-- Every simplicial subcomplex `A : X.Subcomplex` realizes to a classical CW subcomplex of
`TauCeti.simplicialRealizationCW X`, whose cells are the nondegenerate simplices of `X` lying in
`A` and whose underlying closed subset is `Set.range (SSet.toTop.map A.ι)`. -/
def toTopCWSubcomplex {X : SSet.{u}} (A : X.Subcomplex) :
    letI := simplicialRealizationCW X
    CWComplex.Subcomplex (Set.univ : Set |X|) :=
  letI := simplicialRealizationCW X
  have hclosed : ∀ (n : ℕ)
      (i : Set.ofPred fun i : (simplicialRealizationCW X).cell n ↦
        (simplicialRealizationCWCellEquiv X n i).1 ∈ A.obj (op ⦋n⦌)),
      RelCWComplex.closedCell (C := (Set.univ : Set |X|)) n i.1 ⊆ Set.range (toTop.map A.ι) := by
    rintro n ⟨i, hi⟩ _ ⟨x, hx, rfl⟩
    rw [simplicialRealizationCW_map_apply X n i ⟨x, hx⟩]
    refine ⟨toTopObjMk (⟨(simplicialRealizationCWCellEquiv X n i).1, hi⟩ : (A : SSet.{u}) _⦋n⦌)
        (standardCellBallToOrderedSimplex n ⟨x, hx⟩), ?_⟩
    rw [toTop_map_toTopObjMk]
    rfl
  CWComplex.Subcomplex.mk' (Set.univ : Set |X|) (Set.range (toTop.map A.ι))
    (fun n ↦ Set.ofPred fun i ↦ (simplicialRealizationCWCellEquiv X n i).1 ∈ A.obj (op ⦋n⦌))
    hclosed
    (by
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_subset fun n i ↦
          (RelCWComplex.openCell_subset_closedCell n i.1).trans (hclosed n i)
      · rintro _ ⟨z, rfl⟩
        have hz : z ∈ (Set.univ : Set |A|) := trivial
        rw [← (simplicialRealizationCW A).iUnion_openCell_eq_complex] at hz
        obtain ⟨n, i, x, hx, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using hz
        let σA := simplicialRealizationCWCellEquiv A n i
        have hnd : σA.1.1 ∈ X.nonDegenerate n := (A.mem_nonDegenerate_iff σA.1).1 σA.2
        let j := (simplicialRealizationCWCellEquiv X n).symm ⟨σA.1.1, hnd⟩
        refine Set.mem_iUnion₂.2 ⟨n, ⟨j, by simp [j]⟩, ⟨x, hx, ?_⟩⟩
        rw [simplicialRealizationCW_map_apply X n j ⟨x, ball_subset_closedBall hx⟩,
          simplicialRealizationCW_map_apply A n i ⟨x, ball_subset_closedBall hx⟩,
          toTop_map_toTopObjMk]
        simp [j, σA])

/-- The underlying set of `A.toTopCWSubcomplex` is `Set.range (SSet.toTop.map A.ι)`. -/
@[simp]
lemma coe_toTopCWSubcomplex {X : SSet.{u}} (A : X.Subcomplex) :
    letI := simplicialRealizationCW X
    (A.toTopCWSubcomplex : Set |X|) = Set.range (toTop.map A.ι) :=
  (rfl)

/-- A cell of `TauCeti.simplicialRealizationCW X` belongs to `A.toTopCWSubcomplex` precisely when
its nondegenerate simplex belongs to `A`. -/
@[simp]
lemma mem_toTopCWSubcomplex_I_iff {X : SSet.{u}} (A : X.Subcomplex) (n : ℕ)
    (i : (simplicialRealizationCW X).cell n) :
    letI := simplicialRealizationCW X
    i ∈ A.toTopCWSubcomplex.I n ↔
      (simplicialRealizationCWCellEquiv X n i).1 ∈ A.obj (op ⦋n⦌) :=
  Iff.rfl

end Subcomplex

/-- The image of the realization of any monomorphism `i : X ⟶ Y` is the CW subcomplex
`(Subcomplex.range i).toTopCWSubcomplex`. -/
lemma range_toTop_map_eq_toTopCWSubcomplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    letI := simplicialRealizationCW Y
    Set.range (toTop.map i) = ((Subcomplex.range i).toTopCWSubcomplex : Set |Y|) := by
  let _ := simplicialRealizationCW Y
  rw [Subcomplex.coe_toTopCWSubcomplex]
  have hcomp : Subcomplex.toRange i ≫ (Subcomplex.range i).ι = i := Subcomplex.toRange_ι i
  conv_lhs => rw [← hcomp]
  exact range_toTop_map_comp_iso (asIso (Subcomplex.toRange i)) (Subcomplex.range i).ι

/-- **Compact subsets of geometric realizations lie in finite simplicial subcomplexes.**
For any compact subset `K ⊆ |X|`, there is a finite subcomplex `A : X.Subcomplex` (`SSet.Finite A`)
whose realization contains `K`. -/
theorem exists_finite_subcomplex_of_isCompact {X : SSet.{u}} {K : Set |X|} (hK : IsCompact K) :
    ∃ A : X.Subcomplex, SSet.Finite A ∧ K ⊆ Set.range (toTop.map A.ι) := by
  let _ := simplicialRealizationCW X
  have hSfin := finite_setOf_nonempty_inter_openCell_of_isCompact (C := (Set.univ : Set |X|)) hK
  set S := Set.ofPred fun a : Σ n, RelCWComplex.cell (Set.univ : Set |X|) n ↦
    (K ∩ RelCWComplex.openCell (C := (Set.univ : Set |X|)) a.1 a.2).Nonempty
  have : _root_.Finite S := hSfin.to_subtype
  let A : X.Subcomplex :=
    ⨆ a : S, Subcomplex.ofSimplex (simplicialRealizationCWCellEquiv X a.1.1 a.1.2).1
  refine ⟨A, (finite_iSup_iff _).2 fun _ ↦ inferInstance, fun y hy ↦ ?_⟩
  have hyU : y ∈ (Set.univ : Set |X|) := trivial
  rw [← (simplicialRealizationCW X).iUnion_openCell_eq_complex] at hyU
  obtain ⟨n, i, hyi⟩ := by simpa only [Set.mem_iUnion] using hyU
  have ha : (⟨n, i⟩ : Σ n, RelCWComplex.cell (Set.univ : Set |X|) n) ∈ S := ⟨y, hy, hyi⟩
  have hiA : i ∈ A.toTopCWSubcomplex.I n := by
    rw [Subcomplex.mem_toTopCWSubcomplex_I_iff]
    exact le_iSup (fun a : S ↦
      Subcomplex.ofSimplex (simplicialRealizationCWCellEquiv X a.1.1 a.1.2).1)
      ⟨⟨n, i⟩, ha⟩ _ (Subcomplex.mem_ofSimplex_obj _)
  rw [← Subcomplex.coe_toTopCWSubcomplex, ← A.toTopCWSubcomplex.union, Set.empty_union]
  exact Set.mem_iUnion₂.2 ⟨n, ⟨i, hiA⟩, hyi⟩

end SSet

namespace TauCeti

open SSet

/-- The CW structure on `|Δ[0]|` has a unique `0`-cell. -/
@[instance_reducible]
noncomputable def uniqueSimplicialRealizationCWStdSimplexZeroCellZero :
    Unique ((simplicialRealizationCW (Δ[0] : SSet.{u})).cell 0) := by
  haveI : Unique (Set.ofPred fun S : Finset (Fin 1) ↦ S.card = 1) :=
    { default := ⟨Finset.univ, by decide⟩
      uniq := fun ⟨S, hS⟩ ↦ Subtype.ext (Finset.eq_univ_of_card S (by simpa using hS)) }
  exact ((simplicialRealizationCWCellEquiv (Δ[0] : SSet.{u}) 0).trans
    (stdSimplex.nonDegenerateEquiv' (n := 0) (d := 0))).unique

/-- The CW structure on `|Δ[0]|` has no cells of positive dimension. -/
lemma isEmpty_simplicialRealizationCW_stdSimplex_zero_cell_succ (n : ℕ) :
    IsEmpty ((simplicialRealizationCW (Δ[0] : SSet.{u})).cell (n + 1)) := by
  refine (simplicialRealizationCWCellEquiv (Δ[0] : SSet.{u}) (n + 1)).isEmpty_congr.2 ?_
  refine (stdSimplex.nonDegenerateEquiv' (n := 0) (d := n + 1)).isEmpty_congr.2 ?_
  refine ⟨fun ⟨S, hS⟩ ↦ ?_⟩
  have hle : S.card ≤ Fintype.card (Fin 1) := Finset.card_le_univ S
  have hcard : S.card = n + 2 := hS
  simp only [Fintype.card_fin] at hle
  omega

/-- The number of `k`-cells of `simplicialRealizationCW Δ[n]` is `Nat.choose (n + 1) (k + 1)`. -/
lemma natCard_simplicialRealizationCW_stdSimplex_cell (n k : ℕ) :
    Nat.card ((simplicialRealizationCW (Δ[n] : SSet.{u})).cell k) =
      Nat.choose (n + 1) (k + 1) := by
  let e := (simplicialRealizationCWCellEquiv (Δ[n] : SSet.{u}) k).trans
    (stdSimplex.nonDegenerateEquiv' (n := n) (d := k))
  rw [Nat.card_congr e]
  let e' : (Set.ofPred fun S : Finset (Fin (n + 1)) ↦ S.card = k + 1) ≃
      (Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1) :=
    { toFun S := ⟨S.1, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, S.2⟩⟩
      invFun S := ⟨S.1, (Finset.mem_powersetCard.1 S.2).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e', Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

end TauCeti
