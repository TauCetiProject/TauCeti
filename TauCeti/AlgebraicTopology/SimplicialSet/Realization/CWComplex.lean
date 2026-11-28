/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import TauCeti.AlgebraicTopology.RelativeCellComplex.Map
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Boundary
public import TauCeti.AlgebraicTopology.SimplicialSet.Skeleton
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Map
import Mathlib.Data.Set.PowersetCard
import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# The CW structure on geometric realizations of simplicial sets

This file equips the geometric realization `|X|` of any simplicial set `X` with a CW complex
structure (using the chosen disk parametrization `TauCeti.standardCellBallToOrderedSimplex`),
with canonical `n`-cell indexing by the nondegenerate `n`-simplices of `X`, canonical skeletal
filtration by `|X.skeleton n|`, and characteristic maps
`SSet.toTopObjMk σ.1 ∘ TauCeti.standardCellBallToOrderedSimplex n`.

For any monomorphism `i : X ⟶ Y` in `SSet`, transporting Mathlib's simplicial relative cell complex
`SSet.relativeCellComplexOfMono i` along the left adjoint `SSet.toTop` and reindexing its basic
cells along `SSet.toTopBoundaryInclusionArrowIso` yields a categorical relative CW complex
`SSet.toTopRelativeCWComplex i : TopCat.RelativeCWComplex (SSet.toTop.map i)`. In particular,
monomorphisms of simplicial sets realize to closed embeddings (`SSet.isClosedEmbedding_toTop_map`),
every realization `|X|` carries a categorical CW structure (`SSet.toTopCWComplex X`), is Hausdorff
(`SSet.t2Space_toTop`), has CW type (`SSet.cwType_toTop`), and receives a classical CW structure
`SSet.simplicialRealizationCW X`.

Under this CW structure:
* the `n`-cells identify canonically with `X.nonDegenerate n`
  (`SSet.simplicialRealizationCWCellEquiv`), with characteristic maps given explicitly by
  `SSet.simplicialRealizationCW_map_apply`;
* the realization of `X.skeleton n` is `skeletonLT univ n`, so `|X.skeleton (n + 1)|` is the
  classical `n`-skeleton `CWComplex.skeleton univ n` (`SSet.range_toTop_map_skeleton_ι`,
  `SSet.range_toTop_map_skeleton_succ_ι`);
* every simplicial map `f : X ⟶ Y` realizes to a cellular map (`SSet.mapsTo_toTop_map_skeletonLT`,
  `SSet.isCellular_toTop_map`);
* every subcomplex `A : X.Subcomplex` realizes to a CW subcomplex
  (`SSet.Subcomplex.toTopCWSubcomplex`), so the image of any simplicial map is a CW subcomplex
  (`SSet.range_toTop_map_eq_toTopCWSubcomplex`);
* every compact subset of `|X|` is contained in the realization of a finite simplicial subcomplex
  (`SSet.exists_finite_subcomplex_of_isCompact`).

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, Chapter III, Theorem 14.1.
* A. Hatcher, *Algebraic Topology*, Appendix, Propositions A.1 and A.2.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial Convexity Metric Topology HomotopicalAlgebra

universe u

namespace SSet

/-- The geometric realization of a monomorphism `i : X ⟶ Y` of simplicial sets carries a
categorical relative CW complex structure, obtained by transporting `relativeCellComplexOfMono i`
along the left adjoint `SSet.toTop` and replacing each realized simplex boundary inclusion
`|∂Δ[n].ι|` by `TopCat.diskBoundaryInclusion n` via the chosen isomorphism
`SSet.toTopBoundaryInclusionArrowIso n`. -/
def toTopRelativeCWComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.RelativeCWComplex (toTop.map i) :=
  ((relativeCellComplexOfMono i).map toTop).reindexCellTypes
    TopCat.RelativeCWComplex.basicCell (fun _ _ ↦ .unit)
    fun n _ ↦ toTopBoundaryInclusionArrowIso n

/-- **Monomorphisms of simplicial sets realize to closed embeddings.** -/
theorem isClosedEmbedding_toTop_map {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    IsClosedEmbedding (toTop.map i) :=
  (toTopRelativeCWComplex i).isClosedEmbedding

/-- Geometric realization preserves monomorphisms of simplicial sets. -/
instance preservesMonomorphisms_toTop : toTop.{u}.PreservesMonomorphisms where
  preserves {_ _} {i} _ :=
    (TopCat.mono_iff_injective _).2 (isClosedEmbedding_toTop_map i).injective

private def toTopBotArrowIso (X : SSet.{u}) :
    Arrow.mk (toTop.map (Subcomplex.ι (⊥ : X.Subcomplex))) ≅ Arrow.mk (initial.to |X|) :=
  Arrow.isoMk ((isInitialToTopBot X).uniqueUpToIso initialIsInitial) (Iso.refl _)
    ((isInitialToTopBot X).hom_ext _ _)

@[simp]
private lemma toTopBotArrowIso_hom_right (X : SSet.{u}) :
    (toTopBotArrowIso X).hom.right = 𝟙 |X| :=
  rfl

/-- The categorical CW complex structure on the geometric realization `|X|` of a simplicial set `X`
induced by `SSet.toTopRelativeCWComplex` and `SSet.toTopBoundaryInclusionArrowIso`. -/
def toTopCWComplex (X : SSet.{u}) : TopCat.CWComplex |X| :=
  (toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))).ofArrowIso (toTopBotArrowIso X)

/-- The geometric realization of every simplicial set is Hausdorff. -/
instance t2Space_toTop (X : SSet.{u}) : T2Space |X| :=
  (toTopCWComplex X).t2Space

/-- The geometric realization of every simplicial set has CW type. -/
theorem cwType_toTop (X : SSet.{u}) : TauCeti.CWType |X| :=
  (toTopCWComplex X).cwType

/-- The stage functor of `SSet.toTopRelativeCWComplex i` is
`(relativeCellComplexOfMono i).F ⋙ SSet.toTop`. -/
@[simp]
lemma toTopRelativeCWComplex_F {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    (toTopRelativeCWComplex i).F = (relativeCellComplexOfMono i).F ⋙ toTop := by
  simp [toTopRelativeCWComplex]

/-- The `n`-th categorical stage of `SSet.toTopRelativeCWComplex i` identifies with the geometric
realization of `SSet.skeletonOfMono i n`. -/
def toTopRelativeCWComplexStageIso {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (toTopRelativeCWComplex i).F.obj n ≅ |(skeletonOfMono i n : SSet.{u})| :=
  eqToIso (congrArg (fun F ↦ F.obj n) (toTopRelativeCWComplex_F i))

/-- The stage isomorphism `SSet.toTopRelativeCWComplexStageIso` intertwines the stage inclusion of
`SSet.toTopRelativeCWComplex i` with the realization of `(SSet.skeletonOfMono i n).ι`. -/
@[simp, reassoc]
lemma toTopRelativeCWComplexStageIso_hom_comp {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (toTopRelativeCWComplexStageIso i n).hom ≫ toTop.map (skeletonOfMono i n).ι =
      (toTopRelativeCWComplex i).incl.app n := by
  symm
  dsimp only [toTopRelativeCWComplex]
  rw [RelativeCellComplex.reindexCellTypes_incl_app, RelativeCellComplex.map_incl_app,
    eqToHom_trans_assoc, relativeCellComplexOfMono_incl_app]
  congr 1

/-- The stage isomorphism `SSet.toTopRelativeCWComplexStageIso` intertwines the realization of
`(SSet.skeletonOfMono i n).ι` with the stage inclusion of `SSet.toTopRelativeCWComplex i`. -/
@[simp, reassoc]
lemma toTopRelativeCWComplexStageIso_inv_comp {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (toTopRelativeCWComplexStageIso i n).inv ≫ (toTopRelativeCWComplex i).incl.app n =
      toTop.map (skeletonOfMono i n).ι := by
  rw [← toTopRelativeCWComplexStageIso_hom_comp, Iso.inv_hom_id_assoc]

private lemma stageIso_hom_naturality_of_comp {Y : SSet.{u}} {W : TopCat.{u}} {f : W ⟶ |Y|}
    (c : TopCat.RelativeCWComplex f)
    {S : ℕ → Y.Subcomplex} (hS : Monotone S) {m n : ℕ} (h : m ≤ n)
    {eₘ : c.F.obj m ≅ |(S m : SSet.{u})|} {eₙ : c.F.obj n ≅ |(S n : SSet.{u})|}
    (hm : eₘ.hom ≫ toTop.map (S m).ι = c.incl.app m)
    (hn : eₙ.hom ≫ toTop.map (S n).ι = c.incl.app n) :
    c.F.map (homOfLE h) ≫ eₙ.hom =
      eₘ.hom ≫ toTop.map (Subcomplex.homOfLE (hS h)) := by
  have hnat := c.incl.naturality (homOfLE h)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hnat
  rw [← cancel_mono (toTop.map (S n).ι), Category.assoc, Category.assoc,
    hn, hnat, ← toTop.map_comp, Subcomplex.homOfLE_ι, hm]

/-- The stage isomorphism `SSet.toTopRelativeCWComplexStageIso` intertwines the categorical
transition maps of `SSet.toTopRelativeCWComplex i` with the realizations of the skeletal
inclusions of `SSet.skeletonOfMono i`. -/
@[reassoc]
lemma toTopRelativeCWComplexStageIso_hom_naturality {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    {m n : ℕ} (h : m ≤ n) :
    (toTopRelativeCWComplex i).F.map (homOfLE h) ≫ (toTopRelativeCWComplexStageIso i n).hom =
      (toTopRelativeCWComplexStageIso i m).hom ≫
        toTop.map (Subcomplex.homOfLE ((skeletonOfMono i).monotone h)) :=
  stageIso_hom_naturality_of_comp (toTopRelativeCWComplex i) (skeletonOfMono i).monotone h
    (toTopRelativeCWComplexStageIso_hom_comp i m) (toTopRelativeCWComplexStageIso_hom_comp i n)

/-- The `n`-th categorical stage of `SSet.toTopCWComplex X` identifies with the geometric
realization of `X.skeleton n`. -/
def toTopCWComplexStageIso (X : SSet.{u}) (n : ℕ) :
    (toTopCWComplex X).F.obj n ≅ |(X.skeleton n : SSet.{u})| :=
  eqToIso (congrArg (fun F ↦ F.obj n)
      (RelativeCellComplex.ofArrowIso_F
        (c := toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))) (toTopBotArrowIso X))) ≪≫
    toTopRelativeCWComplexStageIso (Subcomplex.ι (⊥ : X.Subcomplex)) n ≪≫
    toTop.mapIso (Subcomplex.eqToIso (skeletonOfMono_bot_eq_skeleton X n))

/-- The stage isomorphism `SSet.toTopCWComplexStageIso` intertwines the stage inclusion of
`SSet.toTopCWComplex X` with the realization of `(X.skeleton n).ι`. -/
@[simp, reassoc]
lemma toTopCWComplexStageIso_hom_comp (X : SSet.{u}) (n : ℕ) :
    (toTopCWComplexStageIso X n).hom ≫ toTop.map (X.skeleton n).ι =
      (toTopCWComplex X).incl.app n := by
  have hι : (skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n).ι =
      (Subcomplex.eqToIso (skeletonOfMono_bot_eq_skeleton X n)).hom ≫ (X.skeleton n).ι := by
    simp
  simp only [toTopCWComplexStageIso, Iso.trans_hom, Category.assoc, Functor.mapIso_hom]
  rw [← toTop.map_comp, ← hι, toTopRelativeCWComplexStageIso_hom_comp]
  dsimp only [toTopCWComplex]
  rw [RelativeCellComplex.ofArrowIso_incl_app, toTopBotArrowIso_hom_right]
  simp

/-- The stage isomorphism `SSet.toTopCWComplexStageIso` intertwines the realization of
`(X.skeleton n).ι` with the stage inclusion of `SSet.toTopCWComplex X`. -/
@[simp, reassoc]
lemma toTopCWComplexStageIso_inv_comp (X : SSet.{u}) (n : ℕ) :
    (toTopCWComplexStageIso X n).inv ≫ (toTopCWComplex X).incl.app n =
      toTop.map (X.skeleton n).ι := by
  rw [← toTopCWComplexStageIso_hom_comp, Iso.inv_hom_id_assoc]

/-- The stage isomorphism `SSet.toTopCWComplexStageIso` intertwines the categorical transition
maps of `SSet.toTopCWComplex X` with the realizations of the skeletal inclusions of
`X.skeleton`. -/
@[reassoc]
lemma toTopCWComplexStageIso_hom_naturality (X : SSet.{u}) {m n : ℕ} (h : m ≤ n) :
    (toTopCWComplex X).F.map (homOfLE h) ≫ (toTopCWComplexStageIso X n).hom =
      (toTopCWComplexStageIso X m).hom ≫
        toTop.map (Subcomplex.homOfLE (X.skeleton.monotone h)) :=
  stageIso_hom_naturality_of_comp (toTopCWComplex X) X.skeleton.monotone h
    (toTopCWComplexStageIso_hom_comp X m) (toTopCWComplexStageIso_hom_comp X n)

private noncomputable abbrev toTopRelativeCWComplexReindexEquiv
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :=
  RelativeCellComplex.reindexCellTypesAttachCellsEquiv
    ((relativeCellComplexOfMono i).map toTop) TopCat.RelativeCWComplex.basicCell
    (fun _ _ ↦ .unit) (fun k _ ↦ toTopBoundaryInclusionArrowIso k) n (not_isMax n)

/-- The `n`-cells attached in `toTopRelativeCWComplex i` identify canonically with the simplicial
`n`-cells of `relativeCellComplexOfMono i`. -/
def toTopRelativeCWComplexCellEquiv {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    ((toTopRelativeCWComplex i).attachCells n (not_isMax n)).ι ≃
      relativeCellComplexOfMono.Cell i n :=
  (toTopRelativeCWComplexReindexEquiv i n).trans
    (RelativeCellComplex.mapAttachCellsEquiv
      (relativeCellComplexOfMono i) toTop n (not_isMax n))

/-- The inclusion of an `n`-cell of `toTopRelativeCWComplex i` is the classifying map of its
nondegenerate simplex, precomposed with `(toTopStdSimplexIsoDisk n).inv`. -/
lemma toTopRelativeCWComplex_cells_ι {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ)
    (c : ((toTopRelativeCWComplex i).attachCells n (not_isMax n)).ι) :
    (⟨n, not_isMax n, c⟩ : (toTopRelativeCWComplex i).Cells).ι =
      (toTopStdSimplexIsoDisk.{u} n).inv ≫
        toTop.map (yonedaEquiv.symm (toTopRelativeCWComplexCellEquiv i n c).simplex) := by
  dsimp only [toTopRelativeCWComplex] at c ⊢
  rw [RelativeCellComplex.reindexCellTypes_cells_ι]
  have hstep1 :
      ∀ (γ : ((relativeCellComplexOfMono i).map toTop).Cells)
        (_ : γ = ⟨n, not_isMax n, toTopRelativeCWComplexReindexEquiv i n c⟩)
        (hp : TopCat.disk.{u} n = TopCat.disk.{u} γ.j),
        eqToHom hp ≫ Arrow.rightFunc.map (toTopBoundaryInclusionArrowIso γ.j).inv ≫ γ.ι =
          (toTopStdSimplexIsoDisk.{u} n).inv ≫
            toTop.map (yonedaEquiv.symm (toTopRelativeCWComplexCellEquiv i n c).simplex) := by
    rintro _ rfl _
    rw [eqToHom_refl, Category.id_comp, RelativeCellComplex.map_cells_ι]
    have hstep2 :
        ∀ (δ : (relativeCellComplexOfMono i).Cells)
          (_ : δ = ⟨n, not_isMax n, toTopRelativeCWComplexCellEquiv i n c⟩)
          (hp : toTop.obj (Δ[n] : SSet.{u}) = toTop.obj (Δ[δ.j] : SSet.{u})),
          eqToHom hp ≫ toTop.map δ.ι =
            toTop.map (yonedaEquiv.symm (toTopRelativeCWComplexCellEquiv i n c).simplex) := by
      rintro _ rfl _
      rw [eqToHom_refl, Category.id_comp]
      exact congrArg toTop.map
        (relativeCellComplexOfMono.Cell.ι_b_ι (toTopRelativeCWComplexCellEquiv i n c))
    dsimp only [Arrow.rightFunc_map]
    rw [toTopBoundaryInclusionArrowIso_inv_right]
    exact congrArg ((toTopStdSimplexIsoDisk.{u} n).inv ≫ ·)
      (hstep2 _ (RelativeCellComplex.mapCellsEquiv_mk _ _ _ _ _) _)
  exact hstep1 _ (RelativeCellComplex.reindexCellTypesCellsEquiv_mk _ _ _ _ _ _ _) _

/-- The `n`-cells attached in `toTopCWComplex X` identify canonically with the simplicial
`n`-cells of `relativeCellComplexOfMono (Subcomplex.ι (⊥ : X.Subcomplex))`. -/
def toTopCWComplexCellEquiv (X : SSet.{u}) (n : ℕ) :
    ((toTopCWComplex X).attachCells n (not_isMax n)).ι ≃
      relativeCellComplexOfMono.Cell (Subcomplex.ι (⊥ : X.Subcomplex)) n :=
  (RelativeCellComplex.ofArrowIsoAttachCellsEquiv
      (c := toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex)))
      (toTopBotArrowIso X) n (not_isMax n)).trans
    (toTopRelativeCWComplexCellEquiv (Subcomplex.ι (⊥ : X.Subcomplex)) n)

/-- The inclusion of an `n`-cell of `toTopCWComplex X` is the classifying map of its
nondegenerate simplex, precomposed with `(toTopStdSimplexIsoDisk n).inv`. -/
lemma toTopCWComplex_cells_ι (X : SSet.{u}) (n : ℕ)
    (c : ((toTopCWComplex X).attachCells n (not_isMax n)).ι) :
    (⟨n, not_isMax n, c⟩ : (toTopCWComplex X).Cells).ι =
      (toTopStdSimplexIsoDisk.{u} n).inv ≫
        toTop.map (yonedaEquiv.symm (toTopCWComplexCellEquiv X n c).simplex) := by
  dsimp only [toTopCWComplex] at c ⊢
  rw [RelativeCellComplex.ofArrowIso_cells_ι]
  have hstep :
      ∀ (γ : (toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex))).Cells)
        (_ : γ = ⟨n, not_isMax n,
          RelativeCellComplex.ofArrowIsoAttachCellsEquiv
            (c := toTopRelativeCWComplex (Subcomplex.ι (⊥ : X.Subcomplex)))
            (toTopBotArrowIso X) n (not_isMax n) c⟩)
        (hp : TopCat.disk.{u} n = TopCat.disk.{u} γ.j),
        eqToHom hp ≫ γ.ι ≫ (toTopBotArrowIso X).hom.right =
          (toTopStdSimplexIsoDisk.{u} n).inv ≫
            toTop.map (yonedaEquiv.symm (toTopCWComplexCellEquiv X n c).simplex) := by
    rintro _ rfl _
    simp [toTopRelativeCWComplex_cells_ι]
    rfl
  exact hstep _ (RelativeCellComplex.ofArrowIsoCellsEquiv_mk _ _ _ _ _) _

/-- The classical CW complex structure on the geometric realization `|X|` of a simplicial set `X`
induced by `SSet.toTopCWComplex X`. Its `n`-cells correspond canonically to the nondegenerate
`n`-simplices of `X`, its skeletal filtration is the canonical realization filtration
`|X.skeleton n|`, and each characteristic map is
`SSet.toTopObjMk σ.1 ∘ TauCeti.standardCellBallToOrderedSimplex n`. -/
@[instance_reducible]
def simplicialRealizationCW (X : SSet.{u}) : CWComplex (Set.univ : Set |X|) :=
  (toTopCWComplex X).toCWComplex

/-- The `n`-cells of `simplicialRealizationCW X` are in canonical bijection with the nondegenerate
`n`-simplices of `X`. -/
def simplicialRealizationCWCellEquiv (X : SSet.{u}) (n : ℕ) :
    (simplicialRealizationCW X).cell n ≃ X.nonDegenerate n :=
  ((toTopCWComplex X).toCWComplexCellEquiv n).trans <|
    (toTopCWComplexCellEquiv X n).trans
      { toFun c := ⟨c.simplex, c.nonDegenerate⟩
        invFun σ := { simplex := σ.val, nonDegenerate := σ.property, notMem := by simp }
        left_inv _ := rfl
        right_inv _ := rfl }

/-- The nondegenerate simplex corresponding to a cell `i` of `simplicialRealizationCW X`. -/
private lemma simplicialRealizationCWCellEquiv_coe (X : SSet.{u}) (n : ℕ)
    (i : (simplicialRealizationCW X).cell n) :
    (simplicialRealizationCWCellEquiv X n i).val =
      (toTopCWComplexCellEquiv X n ((toTopCWComplex X).toCWComplexCellEquiv n i)).simplex := by
  simp [simplicialRealizationCWCellEquiv]

/-- The characteristic map of a cell `i` of `simplicialRealizationCW X` on the closed unit ball is
the simplex map `SSet.toTopObjMk` of the corresponding nondegenerate `n`-simplex, precomposed with
`TauCeti.standardCellBallToOrderedSimplex n`. -/
lemma simplicialRealizationCW_map_apply (X : SSet.{u}) (n : ℕ)
    (i : (simplicialRealizationCW X).cell n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := simplicialRealizationCW X
    RelCWComplex.map (C := (Set.univ : Set |X|)) n i x =
      toTopObjMk (simplicialRealizationCWCellEquiv X n i).val
        (TauCeti.standardCellBallToOrderedSimplex n x) := by
  let _ := simplicialRealizationCW X
  rw [(toTopCWComplex X).toCWComplex_map_apply n i x, toTopCWComplex_cells_ι,
    ConcreteCategory.comp_apply, toTopStdSimplexIsoDisk_inv_diskHomeomorphClosedBall_symm,
    toTop_map_yonedaEquiv_symm_toTopHomeo_symm, simplicialRealizationCWCellEquiv_coe]

/-- Variant of `simplicialRealizationCW_map_apply` indexed directly by a nondegenerate simplex. -/
lemma simplicialRealizationCW_map_cellEquiv_symm_apply (X : SSet.{u}) (n : ℕ)
    (σ : X.nonDegenerate n) (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := simplicialRealizationCW X
    RelCWComplex.map (C := (Set.univ : Set |X|)) n
        ((simplicialRealizationCWCellEquiv X n).symm σ) x =
      toTopObjMk σ.val (TauCeti.standardCellBallToOrderedSimplex n x) := by
  let _ := simplicialRealizationCW X
  rw [simplicialRealizationCW_map_apply, Equiv.apply_symm_apply]

/-- The open cell of `SSet.simplicialRealizationCW X` indexed by a nondegenerate `n`-simplex `σ`
is the image under `SSet.toTopObjMk σ.val` of the points with strictly positive barycentric
weights. -/
lemma simplicialRealizationCW_openCell_cellEquiv_symm (X : SSet.{u}) (n : ℕ)
    (σ : X.nonDegenerate n) :
    letI := simplicialRealizationCW X
    RelCWComplex.openCell (C := (Set.univ : Set |X|)) n
        ((simplicialRealizationCWCellEquiv X n).symm σ) =
      toTopObjMk σ.val ''
        Set.ofPred fun y : StdSimplex ℝ (Fin (n + 1)) ↦ ∀ k : Fin (n + 1), 0 < y.weights k := by
  let _ := simplicialRealizationCW X
  ext p
  simp only [RelCWComplex.openCell, Set.mem_image, Metric.mem_ball, dist_zero_right,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z : closedBall (0 : Fin n → ℝ) 1 := ⟨x, mem_closedBall_zero_iff.2 hx.le⟩
    refine ⟨TauCeti.standardCellBallToOrderedSimplex n z,
      (TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff n z).2 hx, ?_⟩
    exact (simplicialRealizationCW_map_cellEquiv_symm_apply X n σ z).symm
  · rintro ⟨y, hy, rfl⟩
    let z := (TauCeti.standardCellBallToOrderedSimplex n).symm y
    have hz : ‖z.val‖ < 1 := by
      rw [← TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff n z]
      simpa [z] using hy
    refine ⟨z.val, hz, ?_⟩
    simpa [z] using simplicialRealizationCW_map_cellEquiv_symm_apply X n σ z

/-- The closed cell of `SSet.simplicialRealizationCW X` indexed by a nondegenerate `n`-simplex `σ`
is the full range of `SSet.toTopObjMk σ.val`. -/
lemma simplicialRealizationCW_closedCell_cellEquiv_symm (X : SSet.{u}) (n : ℕ)
    (σ : X.nonDegenerate n) :
    letI := simplicialRealizationCW X
    RelCWComplex.closedCell (C := (Set.univ : Set |X|)) n
        ((simplicialRealizationCWCellEquiv X n).symm σ) =
      Set.range (toTopObjMk σ.val) := by
  let _ := simplicialRealizationCW X
  ext p
  simp only [RelCWComplex.closedCell, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
    Set.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z : closedBall (0 : Fin n → ℝ) 1 := ⟨x, mem_closedBall_zero_iff.2 hx⟩
    exact ⟨TauCeti.standardCellBallToOrderedSimplex n z,
      (simplicialRealizationCW_map_cellEquiv_symm_apply X n σ z).symm⟩
  · rintro ⟨y, rfl⟩
    let z := (TauCeti.standardCellBallToOrderedSimplex n).symm y
    refine ⟨z.val, mem_closedBall_zero_iff.1 z.property, ?_⟩
    simpa [z] using simplicialRealizationCW_map_cellEquiv_symm_apply X n σ z

/-- The realization of `X.skeleton n` is the classical subcomplex `skeletonLT univ n` of
`SSet.simplicialRealizationCW X`, the union of all closed cells of dimension `< n`. -/
theorem range_toTop_map_skeleton_ι (X : SSet.{u}) (n : ℕ) :
    letI := simplicialRealizationCW X
    Set.range (toTop.map (X.skeleton n).ι) =
      (RelCWComplex.skeletonLT (Set.univ : Set |X|) n : Set |X|) := by
  let _ := simplicialRealizationCW X
  rw [← toTopCWComplexStageIso_inv_comp X n, ConcreteCategory.coe_comp,
    (ConcreteCategory.bijective_of_isIso (toTopCWComplexStageIso X n).inv).surjective.range_comp _]
  exact (toTopCWComplex X).range_incl_app_eq_toCWComplex_skeletonLT n

/-- The realization of `X.skeleton (n + 1)` is the classical `n`-skeleton
`CWComplex.skeleton univ n` of `SSet.simplicialRealizationCW X`. -/
theorem range_toTop_map_skeleton_succ_ι (X : SSet.{u}) (n : ℕ) :
    letI := simplicialRealizationCW X
    Set.range (toTop.map (X.skeleton (n + 1)).ι) =
      (CWComplex.skeleton (Set.univ : Set |X|) n : Set |X|) := by
  let _ := simplicialRealizationCW X
  simpa [CWComplex.skeleton] using range_toTop_map_skeleton_ι X (n + 1)

/-- The geometric realization of any simplicial map preserves every `skeletonLT` stage of
`SSet.simplicialRealizationCW`. -/
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
  have hpt := ConcreteCategory.congr_hom (congrArg toTop.map hg) x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hpt
  exact ⟨toTop.map g x, hpt⟩

/-- The geometric realization of any simplicial map preserves every classical `n`-skeleton of
`SSet.simplicialRealizationCW`. -/
theorem mapsTo_toTop_map_skeleton {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := simplicialRealizationCW X
    letI := simplicialRealizationCW Y
    Set.MapsTo (toTop.map f)
      (CWComplex.skeleton (Set.univ : Set |X|) n : Set |X|)
      (CWComplex.skeleton (Set.univ : Set |Y|) n : Set |Y|) := by
  let _ := simplicialRealizationCW X
  let _ := simplicialRealizationCW Y
  simpa [CWComplex.skeleton] using mapsTo_toTop_map_skeletonLT f (n + 1)

/-- **Every simplicial map realizes to a cellular map** between the induced CW structures
`SSet.simplicialRealizationCW`. -/
theorem isCellular_toTop_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    letI := simplicialRealizationCW X
    letI := simplicialRealizationCW Y
    TauCeti.IsCellular (Set.univ : Set |X|) (Set.univ : Set |Y|)
      (TopCat.ofHom ⟨fun x ↦ ⟨toTop.map f x.val, trivial⟩, by fun_prop⟩) :=
  fun n _ hx ↦ mapsTo_toTop_map_skeletonLT f n hx

namespace Subcomplex

/-- Any closed cell of `SSet.simplicialRealizationCW X` whose nondegenerate simplex belongs to a
subcomplex `A` is contained in `Set.range (SSet.toTop.map A.ι)`. -/
lemma closedCell_subset_range_toTop_map_ι {X : SSet.{u}} (A : X.Subcomplex) {n : ℕ}
    (i : (simplicialRealizationCW X).cell n)
    (hi : (simplicialRealizationCWCellEquiv X n i).val ∈ A.obj (op ⦋n⦌)) :
    letI := simplicialRealizationCW X
    RelCWComplex.closedCell (C := (Set.univ : Set |X|)) n i ⊆ Set.range (toTop.map A.ι) := by
  let _ := simplicialRealizationCW X
  rintro _ ⟨x, hx, rfl⟩
  rw [simplicialRealizationCW_map_apply X n i ⟨x, hx⟩]
  refine ⟨toTopObjMk
      (⟨(simplicialRealizationCWCellEquiv X n i).val, hi⟩ : (A : SSet.{u}) _⦋n⦌)
      (TauCeti.standardCellBallToOrderedSimplex n ⟨x, hx⟩), ?_⟩
  simp [toTop_map_toTopObjMk]

/-- The image of `SSet.toTop.map A.ι` is covered by the open cells of
`SSet.simplicialRealizationCW X` indexed by nondegenerate simplices belonging to `A`. -/
lemma range_toTop_map_ι_subset_iUnion_openCell {X : SSet.{u}} (A : X.Subcomplex) :
    letI := simplicialRealizationCW X
    Set.range (toTop.map A.ι) ⊆
      ⋃ n, ⋃ (i : Set.ofPred fun i : (simplicialRealizationCW X).cell n ↦
        (simplicialRealizationCWCellEquiv X n i).val ∈ A.obj (op ⦋n⦌)),
        RelCWComplex.openCell (C := (Set.univ : Set |X|)) n i.val := by
  let _ := simplicialRealizationCW X
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ (Set.univ : Set |A|) := trivial
  rw [← (simplicialRealizationCW A).iUnion_openCell_eq_complex] at hz
  obtain ⟨n, i, x, hx, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using hz
  let σA := simplicialRealizationCWCellEquiv A n i
  have hnd : σA.val.val ∈ X.nonDegenerate n := (A.mem_nonDegenerate_iff σA.val).1 σA.property
  let j := (simplicialRealizationCWCellEquiv X n).symm ⟨σA.val.val, hnd⟩
  refine Set.mem_iUnion₂.2 ⟨n, ⟨j, by simp [j]⟩, ⟨x, hx, ?_⟩⟩
  rw [simplicialRealizationCW_map_apply X n j ⟨x, ball_subset_closedBall hx⟩,
    simplicialRealizationCW_map_apply A n i ⟨x, ball_subset_closedBall hx⟩,
    toTop_map_toTopObjMk]
  simp [j, σA]

/-- Every simplicial subcomplex `A : X.Subcomplex` realizes to a classical CW subcomplex of
`SSet.simplicialRealizationCW X`, whose cells are the nondegenerate simplices of `X` lying in
`A` and whose underlying closed subset is `Set.range (SSet.toTop.map A.ι)`. -/
def toTopCWSubcomplex {X : SSet.{u}} (A : X.Subcomplex) :
    letI := simplicialRealizationCW X
    CWComplex.Subcomplex (Set.univ : Set |X|) :=
  letI := simplicialRealizationCW X
  CWComplex.Subcomplex.mk' (Set.univ : Set |X|) (Set.range (toTop.map A.ι))
    (fun n ↦ Set.ofPred fun i ↦ (simplicialRealizationCWCellEquiv X n i).val ∈ A.obj (op ⦋n⦌))
    (fun _ i ↦ closedCell_subset_range_toTop_map_ι A i.val i.property)
    (Set.Subset.antisymm
      (Set.iUnion₂_subset fun _ i ↦
        (RelCWComplex.openCell_subset_closedCell _ i.val).trans
          (closedCell_subset_range_toTop_map_ι A i.val i.property))
      (range_toTop_map_ι_subset_iUnion_openCell A))

/-- The underlying set of `A.toTopCWSubcomplex` is `Set.range (SSet.toTop.map A.ι)`. -/
@[simp]
lemma coe_toTopCWSubcomplex {X : SSet.{u}} (A : X.Subcomplex) :
    letI := simplicialRealizationCW X
    (A.toTopCWSubcomplex : Set |X|) = Set.range (toTop.map A.ι) :=
  (rfl)

/-- A cell of `SSet.simplicialRealizationCW X` belongs to `A.toTopCWSubcomplex` precisely when
its nondegenerate simplex belongs to `A`. -/
@[simp]
lemma mem_toTopCWSubcomplex_I_iff {X : SSet.{u}} (A : X.Subcomplex) (n : ℕ)
    (i : (simplicialRealizationCW X).cell n) :
    letI := simplicialRealizationCW X
    i ∈ A.toTopCWSubcomplex.I n ↔
      (simplicialRealizationCWCellEquiv X n i).val ∈ A.obj (op ⦋n⦌) :=
  Iff.rfl

/-- `SSet.Subcomplex.toTopCWSubcomplex` is monotone with respect to inclusion of simplicial
subcomplexes. -/
lemma toTopCWSubcomplex_monotone (X : SSet.{u}) :
    Monotone (toTopCWSubcomplex (X := X)) := by
  intro A B hAB
  let _ := simplicialRealizationCW X
  rw [Topology.RelCWComplex.Subcomplex.le_iff_I_subset]
  intro n i hi
  rw [mem_toTopCWSubcomplex_I_iff] at hi ⊢
  exact hAB _ hi

end Subcomplex

/-- The image of the realization of any simplicial map `i : X ⟶ Y` is the CW subcomplex
`(Subcomplex.range i).toTopCWSubcomplex`. -/
lemma range_toTop_map_eq_toTopCWSubcomplex {X Y : SSet.{u}} (i : X ⟶ Y) :
    letI := simplicialRealizationCW Y
    Set.range (toTop.map i) = ((Subcomplex.range i).toTopCWSubcomplex : Set |Y|) := by
  let _ := simplicialRealizationCW Y
  rw [Subcomplex.coe_toTopCWSubcomplex, ← Subcomplex.toRange_ι i, toTop.map_comp]
  exact ((TopCat.epi_iff_surjective _).1 inferInstance).range_comp _

/-- **Compact subsets of geometric realizations lie in finite simplicial subcomplexes.**
For any compact subset `K ⊆ |X|`, there is a finite subcomplex `A : X.Subcomplex` (`SSet.Finite A`)
whose realization contains `K`. -/
theorem exists_finite_subcomplex_of_isCompact {X : SSet.{u}} {K : Set |X|} (hK : IsCompact K) :
    ∃ A : X.Subcomplex, SSet.Finite A ∧ K ⊆ Set.range (toTop.map A.ι) := by
  let _ := simplicialRealizationCW X
  have hSfin := TauCeti.finite_setOf_nonempty_inter_openCell_of_isCompact
    (C := (Set.univ : Set |X|)) hK
  set S := Set.ofPred fun a : Σ n, RelCWComplex.cell (Set.univ : Set |X|) n ↦
    (K ∩ RelCWComplex.openCell (C := (Set.univ : Set |X|)) a.fst a.snd).Nonempty
  have : _root_.Finite S := hSfin.to_subtype
  let A : X.Subcomplex :=
    ⨆ a : S, Subcomplex.ofSimplex (simplicialRealizationCWCellEquiv X a.val.fst a.val.snd).val
  refine ⟨A, (finite_iSup_iff _).2 fun _ ↦ inferInstance, fun y hy ↦ ?_⟩
  have hyU : y ∈ (Set.univ : Set |X|) := trivial
  rw [← (simplicialRealizationCW X).iUnion_openCell_eq_complex] at hyU
  obtain ⟨n, i, hyi⟩ := by simpa only [Set.mem_iUnion] using hyU
  have ha : (⟨n, i⟩ : Σ n, RelCWComplex.cell (Set.univ : Set |X|) n) ∈ S := ⟨y, hy, hyi⟩
  have hiA : i ∈ A.toTopCWSubcomplex.I n := by
    rw [Subcomplex.mem_toTopCWSubcomplex_I_iff]
    exact le_iSup (fun a : S ↦
      Subcomplex.ofSimplex (simplicialRealizationCWCellEquiv X a.val.fst a.val.snd).val)
      ⟨⟨n, i⟩, ha⟩ _ (Subcomplex.mem_ofSimplex_obj _)
  rw [← Subcomplex.coe_toTopCWSubcomplex, ← A.toTopCWSubcomplex.union, Set.empty_union]
  exact Set.mem_iUnion₂.2 ⟨n, ⟨i, hiA⟩, hyi⟩

end SSet

namespace TauCeti

open SSet

private def simplicialRealizationCWStdSimplexCellEquiv (n k : ℕ) :
    (simplicialRealizationCW (Δ[n] : SSet.{u})).cell k ≃
      Set.powersetCard (Fin (n + 1)) (k + 1) :=
  (simplicialRealizationCWCellEquiv (Δ[n] : SSet.{u}) k).trans
    (stdSimplex.nonDegenerateEquiv' (n := n) (d := k))

/-- The number of `k`-cells of `simplicialRealizationCW Δ[n]` is `Nat.choose (n + 1) (k + 1)`. -/
lemma natCard_simplicialRealizationCW_stdSimplex_cell (n k : ℕ) :
    Nat.card ((simplicialRealizationCW (Δ[n] : SSet.{u})).cell k) =
      Nat.choose (n + 1) (k + 1) := by
  rw [Nat.card_congr (simplicialRealizationCWStdSimplexCellEquiv.{u} n k),
    Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The CW structure on `|Δ[0]|` has a unique `0`-cell. -/
@[instance_reducible]
noncomputable def uniqueSimplicialRealizationCWStdSimplexZeroCellZero :
    Unique ((simplicialRealizationCW (Δ[0] : SSet.{u})).cell 0) :=
  have hcard := Nat.card_eq_one_iff_unique.1
    (natCard_simplicialRealizationCW_stdSimplex_cell 0 0)
  ⟨⟨Classical.choice hcard.2⟩, fun y ↦ @Subsingleton.elim _ hcard.1 y _⟩

/-- The CW structure on `|Δ[0]|` has no cells of positive dimension. -/
lemma isEmpty_simplicialRealizationCW_stdSimplex_zero_cell_succ (n : ℕ) :
    IsEmpty ((simplicialRealizationCW (Δ[0] : SSet.{u})).cell (n + 1)) := by
  have : _root_.Finite ((simplicialRealizationCW (Δ[0] : SSet.{u})).cell (n + 1)) :=
    (Equiv.finite_iff (simplicialRealizationCWStdSimplexCellEquiv.{u} 0 (n + 1))).2 inferInstance
  rw [← Finite.card_eq_zero_iff, natCard_simplicialRealizationCW_stdSimplex_cell]
  exact Nat.choose_eq_zero_of_lt (by omega)

end TauCeti
