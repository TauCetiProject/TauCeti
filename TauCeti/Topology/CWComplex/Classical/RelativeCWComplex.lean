/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Abstract.Basic
public import TauCeti.Topology.CWComplex.Classical.Skeleton.CellMap
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Colimit

/-!
# Classical relative CW complexes are categorical relative CW complexes

Mathlib has two notions of CW complex.  The classical `Topology.RelCWComplex C D` describes a
subset `C` of a topological space through explicit cells and characteristic maps, while the
categorical `TopCat.RelativeCWComplex f` presents the target of a morphism `f : X ⟶ Y` of `TopCat`
as the colimit of a sequence of spaces, each obtained from the previous one by attaching disks
along their boundary spheres in a pushout square.  This file goes from the first to the second:
when the ambient space is Hausdorff (a `T2Space`, which this file assumes throughout), a classical
relative CW complex `C` with base `D` gives a categorical relative CW complex structure on the
inclusion of `D` into `C` (`TauCeti.toRelativeCWComplex`).

The `n`-th space of the sequence is the skeleton `skeletonLT C n` itself, and the cells attached at
step `n` are the `n`-cells `cell C n`.  The two ingredients are the following.

* Attaching the `n`-cells to `skeletonLT C n` along their boundaries gives `skeletonLT C (n + 1)`:
  the square formed by the coproducts of the disks `𝔻 n` and of their boundaries `∂𝔻 n` over the
  `n`-cells, the characteristic maps and the inclusion of skeleta is a pushout in `TopCat`
  (`TauCeti.isPushout_skeletonObj`).  The disk `𝔻 n` of `TopCat` is the Euclidean unit ball, which
  is carried onto the closed unit ball of the sup norm on `Fin n → ℝ`, the domain of the
  characteristic maps, by the radial homeomorphism `TauCeti.diskHomeomorphClosedBall`.  The
  characteristic and attaching maps on `𝔻 n` and `∂𝔻 n` are `TauCeti.cellDiskHom` and
  `TauCeti.cellAttachingMap`, from `TauCeti.Topology.CWComplex.Classical.Skeleton.CellMap`.
* `C` is the colimit in `TopCat` of its skeleta (`TauCeti.isColimitSkeletonCocone`, proved in
  `TauCeti.Topology.CWComplex.Classical.Skeleton.Colimit`).

In both cases the universal property comes from the weak topology of the complex: maps out of
the next skeleton, or out of the whole complex, are built cell by cell and skeleton by skeleton
with `TauCeti.exists_continuousMap_prod_skeletonLT_succ` and
`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`.  These rest on the closedness axiom of
the classical structure in a Hausdorff space.  The Hausdorff hypothesis cannot be dropped: the
indiscrete two-point space with two `0`-cells satisfies the axioms of a classical CW complex, while
attaching two `0`-cells to the empty space gives the discrete two-point space.

## Main definitions and results

* `TauCeti.isPushout_skeletonObj`, `TauCeti.skeletonAttachCells`: `skeletonLT C (n + 1)` is
  obtained from `skeletonLT C n` by attaching the `n`-cells.
* `TauCeti.toRelativeCWComplex`: the categorical relative CW complex structure on `D ⟶ C`.  Its
  `n`-th space is `skeletonLT C n` (`TauCeti.range_toRelativeCWComplex_incl_app`), its cells are
  those of `C` (`TauCeti.toRelativeCWComplexCellsEquiv`), and its cell inclusions are the
  characteristic maps (`TauCeti.coe_toRelativeCWComplex_cells_ι_apply`).
* `TopCat.toTopCatCWComplex`: the absolute categorical `TopCat.CWComplex` structure on a
  Hausdorff space `Y` carrying a classical `CWComplex` structure on `Set.univ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.2, on the equivalence of the two definitions of CW complexes.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical definition.
-/

public section

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Metric Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

section AttachCells

variable {C} {n : ℕ}

/-- The attaching map of a cell is the characteristic map on the boundary of the disk. -/
@[reassoc]
lemma cellAttachingMap_comp_skeletonFunctor_map (j : cell C n) :
    cellAttachingMap j ≫ (skeletonFunctor C).map (homOfLE n.le_succ) =
      TopCat.diskBoundaryInclusion n ≫ cellDiskHom j := by
  ext z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact (coe_cellAttachingMap_apply j z).trans (coe_cellDiskHom_apply j _).symm

/-- Two maps out of `skeletonLT C (n + 1)` agree when they agree on `skeletonLT C n` and through
the characteristic map of every `n`-cell. -/
private lemma skeletonObj_succ_hom_ext {Y : TopCat.{w}} {φ φ' : skeletonObj C (n + 1) ⟶ Y}
    (h₀ : (skeletonFunctor C).map (homOfLE n.le_succ) ≫ φ =
      (skeletonFunctor C).map (homOfLE n.le_succ) ≫ φ')
    (h : ∀ j, cellDiskHom j ≫ φ = cellDiskHom j ≫ φ') : φ = φ' := by
  ext ⟨x, hx⟩
  obtain hx' | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hx
  · exact ConcreteCategory.congr_hom h₀ ⟨x, hx'⟩
  · have hz : cellDiskHom j
        ((diskHomeomorphClosedBall n).symm ⟨y, mem_closedBall_zero_iff.2 hy.le⟩) =
          ⟨map n j y, hx⟩ :=
      Subtype.ext (by rw [coe_cellDiskHom_apply, Homeomorph.apply_symm_apply])
    rw [← hz]
    exact ConcreteCategory.congr_hom (h j) _

/-- A map on `skeletonLT C n` and maps on the disks of the `n`-cells that are compatible along the
attaching maps glue to a map on `skeletonLT C (n + 1)`. -/
private lemma exists_desc_skeletonObj_succ {Y : TopCat.{w}} (φ : skeletonObj C n ⟶ Y)
    (ψ : cell C n → (TopCat.disk.{w} n ⟶ Y))
    (h : ∀ j, cellAttachingMap j ≫ φ = TopCat.diskBoundaryInclusion n ≫ ψ j) :
    ∃ χ : skeletonObj C (n + 1) ⟶ Y,
      (skeletonFunctor C).map (homOfLE n.le_succ) ≫ χ = φ ∧ ∀ j, cellDiskHom j ≫ χ = ψ j := by
  obtain ⟨F, hF₀, hF⟩ := exists_continuousMap_prod_skeletonLT_succ (Z := Unit)
    (φ.hom.comp ContinuousMap.snd)
    (fun j ↦ ((ψ j).hom.comp ((diskHomeomorphClosedBall n).symm : C(_, _))).comp
      ContinuousMap.snd)
    fun j _ y hy ↦ by
      obtain ⟨z, hz⟩ := (norm_diskHomeomorphClosedBall_eq_one_iff
        ((diskHomeomorphClosedBall n).symm y)).1
          (by rwa [Homeomorph.apply_symm_apply, ← mem_sphere_zero_iff_norm])
      have hb : cellAttachingMap j z =
          ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩ :=
        Subtype.ext (by rw [coe_cellAttachingMap_apply, hz, Homeomorph.apply_symm_apply])
      have := ConcreteCategory.congr_hom (h j) z
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hb, hz] at this
      exact this.symm
  refine ⟨TopCat.ofHom (F.comp ((ContinuousMap.const _ ()).prodMk (ContinuousMap.id _))), ?_,
    fun j ↦ ?_⟩
  · ext x
    exact hF₀ () x.1 x.2
  · ext z
    rw [ConcreteCategory.comp_apply]
    refine (congrArg (fun x ↦ F ((), x)) (Subtype.ext (coe_cellDiskHom_apply j z))).trans
      ((hF j () (diskHomeomorphClosedBall n z)).trans ?_)
    exact congrArg (ψ j) ((diskHomeomorphClosedBall n).symm_apply_apply z)

variable (C n) in
/-- **Attaching the `n`-cells to the `(n - 1)`-skeleton gives the `n`-skeleton.**  The square
formed by the inclusion of the boundary spheres into the disks over the `n`-cells, the attaching
maps, the characteristic maps and the inclusion `skeletonLT C n ⊆ skeletonLT C (n + 1)` is a
pushout in `TopCat`. -/
theorem isPushout_skeletonObj :
    IsPushout (Sigma.desc (cellAttachingMap (C := C) (n := n)))
      (Limits.Sigma.map fun _ : cell C n ↦ TopCat.diskBoundaryInclusion.{w} n)
      ((skeletonFunctor C).map (homOfLE n.le_succ)) (Sigma.desc cellDiskHom) := by
  have w : Sigma.desc (cellAttachingMap (C := C) (n := n)) ≫
      (skeletonFunctor C).map (homOfLE n.le_succ) =
        (Limits.Sigma.map fun _ : cell C n ↦ TopCat.diskBoundaryInclusion.{w} n) ≫
          Sigma.desc cellDiskHom := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc,
      cellAttachingMap_comp_skeletonFunctor_map]
  -- A pushout cocone restricts to compatible maps on `skeletonLT C n` and on the disks.
  have hs (s : PushoutCocone (Sigma.desc (cellAttachingMap (C := C) (n := n)))
      (Limits.Sigma.map fun _ : cell C n ↦ TopCat.diskBoundaryInclusion.{w} n)) (j : cell C n) :
      cellAttachingMap j ≫ s.inl = TopCat.diskBoundaryInclusion n ≫
        Sigma.ι (fun _ : cell C n ↦ TopCat.disk.{w} n) j ≫ s.inr := by
    have := Sigma.ι (fun _ : cell C n ↦ TopCat.diskBoundary.{w} n) j ≫= s.condition
    rwa [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc] at this
  let desc s := exists_desc_skeletonObj_succ s.inl _ (hs s)
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w (fun s ↦ (desc s).choose)
    (fun s ↦ (desc s).choose_spec.1) (fun s ↦ ?_) fun s m h₁ h₂ ↦ ?_)
  · refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [Sigma.ι_comp_desc_assoc]
    exact (desc s).choose_spec.2 j
  · refine skeletonObj_succ_hom_ext ?_ fun j ↦ ?_
    · rw [h₁, (desc s).choose_spec.1]
    · rw [(desc s).choose_spec.2 j, ← Sigma.ι_comp_desc_assoc]
      exact Sigma.ι _ j ≫= h₂

variable (C n) in
/-- The `n`-skeleton `skeletonLT C (n + 1)` is obtained from `skeletonLT C n` by attaching one
`n`-disk along its boundary sphere for each `n`-cell, through the attaching maps
`TauCeti.cellAttachingMap`.  The body is exposed so that the cells are `cell C n` by definition. -/
@[expose] def skeletonAttachCells :
    AttachCells.{w} (TopCat.RelativeCWComplex.basicCell n)
      ((skeletonFunctor C).map (homOfLE n.le_succ)) where
  ι := cell C n
  π _ := ()
  cofan₁ := Cofan.mk _ (Sigma.ι fun _ : cell C n ↦ TopCat.diskBoundary.{w} n)
  cofan₂ := Cofan.mk _ (Sigma.ι fun _ : cell C n ↦ TopCat.disk.{w} n)
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := Limits.Sigma.map fun _ ↦ TopCat.diskBoundaryInclusion n
  hm j := Sigma.ι_map _ j
  g₁ := Sigma.desc cellAttachingMap
  g₂ := Sigma.desc cellDiskHom
  isPushout := isPushout_skeletonObj C n

/-- The inclusion of an `n`-cell attached in `TauCeti.skeletonAttachCells` is its characteristic
map. -/
@[simp]
lemma skeletonAttachCells_cell (j : cell C n) : (skeletonAttachCells C n).cell j = cellDiskHom j :=
  Sigma.ι_comp_desc _ j

end AttachCells

section RelativeCWComplex

/-- **A classical relative CW complex in a Hausdorff space is a categorical relative CW complex.**
The inclusion of the base `D` into `C` is the transfinite composition of the inclusions of the
skeleta `skeletonLT C n`, and the step from `skeletonLT C n` to `skeletonLT C (n + 1)` attaches
the `n`-cells of `C` along their attaching maps.  The body is exposed so that the `n`-th space is
the skeleton `skeletonObj C n` and the cells attached at step `n` are `cell C n` by definition. -/
@[expose] def toRelativeCWComplex :
    TopCat.RelativeCWComplex.{w}
      (TopCat.ofHom (ContinuousMap.inclusion (base_subset_complex (C := C)))) where
  F := skeletonFunctor C
  isoBot := TopCat.isoOfHomeo (Homeomorph.setCongr (s := (skeletonLT C ((⊥ : ℕ) : ℕ∞) : Set X))
    (t := D) (by rw [Nat.bot_eq_zero, Nat.cast_zero, skeletonLT_zero_eq_base]))
  incl := (skeletonCocone C).ι
  isColimit := isColimitSkeletonCocone C
  fac := rfl
  attachCells n _ := skeletonAttachCells C n

variable {C}

/-- The `n`-th space of `TauCeti.toRelativeCWComplex C` is the skeleton `skeletonLT C n`, included
in `C`. -/
lemma coe_toRelativeCWComplex_incl_app_apply (n : ℕ) (x : (toRelativeCWComplex C).F.obj n) :
    ((toRelativeCWComplex C).incl.app n x).1 = x.1 :=
  (rfl)

/-- The image in `C` of the `n`-th space of `TauCeti.toRelativeCWComplex C` is `skeletonLT C n`. -/
lemma range_toRelativeCWComplex_incl_app (n : ℕ) :
    range (fun x : (toRelativeCWComplex C).F.obj n ↦ ((toRelativeCWComplex C).incl.app n x).1) =
      skeletonLT C n :=
  Subtype.range_coe

/-- The cells of `TauCeti.toRelativeCWComplex C` are the cells of `C`: a cell attached at step `n`
is an `n`-cell. -/
def toRelativeCWComplexCellsEquiv : (toRelativeCWComplex C).Cells ≃ Σ n, cell C n where
  toFun γ := ⟨γ.j, γ.k⟩
  invFun γ := ⟨γ.1, not_isMax γ.1, γ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma toRelativeCWComplexCellsEquiv_apply (γ : (toRelativeCWComplex C).Cells) :
    toRelativeCWComplexCellsEquiv γ = ⟨γ.j, γ.k⟩ :=
  (rfl)

@[simp]
lemma toRelativeCWComplexCellsEquiv_symm_apply (n : ℕ) (i : cell C n) :
    toRelativeCWComplexCellsEquiv.symm ⟨n, i⟩ = ⟨n, not_isMax n, i⟩ :=
  (rfl)

/-- The inclusion of a cell of `TauCeti.toRelativeCWComplex C` is the characteristic map of the
corresponding cell of `C`, read on the Euclidean disk through
`TauCeti.diskHomeomorphClosedBall`. -/
lemma coe_toRelativeCWComplex_cells_ι_apply (γ : (toRelativeCWComplex C).Cells)
    (z : TopCat.disk.{w} γ.j) :
    (γ.ι z : X) = map γ.j γ.k (diskHomeomorphClosedBall γ.j z) := by
  rw [RelativeCellComplex.Cells.ι, ConcreteCategory.comp_apply]
  exact (congrArg Subtype.val (ConcreteCategory.congr_hom (skeletonAttachCells_cell γ.k) z)).trans
    (coe_cellDiskHom_apply γ.k z)

end RelativeCWComplex

end TauCeti

namespace TopCat

open TauCeti

section ToTopCatCWComplex

variable (Y : TopCat.{w}) [T2Space Y] [Topology.CWComplex (univ : Set Y)]

/-- **A Hausdorff space carrying a classical `CWComplex` structure on `Set.univ` is a categorical
`TopCat.CWComplex`.** -/
def toTopCatCWComplex : TopCat.CWComplex Y where
  __ := (toRelativeCWComplex (univ : Set Y)).toTransfiniteCompositionOfShape.ofArrowIso
    (Arrow.isoMk
      { hom := TopCat.ofHom ⟨fun x ↦ x.2.elim, continuous_of_discreteTopology⟩
        inv := Limits.initial.to _
        hom_inv_id := by ext x; exact x.2.elim
        inv_hom_id := Limits.initial.hom_ext _ _ }
      (TopCat.isoOfHomeo (Homeomorph.Set.univ Y)) (by ext x; exact x.2.elim))
  attachCells := (toRelativeCWComplex (univ : Set Y)).attachCells

@[simp] lemma toTopCatCWComplex_F : (Y.toTopCatCWComplex).F = skeletonFunctor (univ : Set Y) := by
  simp [toTopCatCWComplex, toRelativeCWComplex]

lemma toTopCatCWComplex_obj (n : ℕ) :
    (Y.toTopCatCWComplex).F.obj n = skeletonObj (univ : Set Y) n := (rfl)

lemma toTopCatCWComplex_map {m n : ℕ} (f : m ⟶ n) :
    (Y.toTopCatCWComplex).F.map f =
      eqToHom (Y.toTopCatCWComplex_obj m) ≫ (skeletonFunctor (univ : Set Y)).map f ≫
        eqToHom (Y.toTopCatCWComplex_obj n).symm :=
  CategoryTheory.Functor.congr_hom Y.toTopCatCWComplex_F f

lemma toTopCatCWComplex_incl_app (n : ℕ) :
    (Y.toTopCatCWComplex).incl.app n = eqToHom (Y.toTopCatCWComplex_obj n) ≫
      TopCat.ofHom (ContinuousMap.subtypeVal (skeletonLT (univ : Set Y) n : Set Y)) := by
  dsimp only [toTopCatCWComplex, MorphismProperty.TransfiniteCompositionOfShape.ofArrowIso,
    TransfiniteCompositionOfShape.ofArrowIso]
  rw [NatTrans.comp_app, Functor.const_map_app]; dsimp only [toRelativeCWComplex]; generalize_proofs
  rw [eqToHom_refl, Category.id_comp]; refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  simp only [ConcreteCategory.comp_apply, CategoryTheory.Arrow.isoMk_hom_right,
    TopCat.isoOfHomeo_hom, Homeomorph.Set.univ, Equiv.Set.univ, ContinuousMap.subtypeVal]
  exact coe_skeletonCocone_ι_app_apply (univ : Set Y) n x

lemma range_toTopCatCWComplex_incl_app (n : ℕ) :
    (range ((Y.toTopCatCWComplex).incl.app n) : Set Y) = skeletonLT (univ : Set Y) n := by
  have hsurj : Function.Surjective (eqToHom (Y.toTopCatCWComplex_obj n)) :=
    (TopCat.homeoOfIso (eqToIso (Y.toTopCatCWComplex_obj n))).surjective
  rw [Y.toTopCatCWComplex_incl_app n, TopCat.coe_comp, hsurj.range_comp]
  simp [ContinuousMap.subtypeVal]

/-- The `n`-cells attached at step `n` of `Y.toTopCatCWComplex` are `cell (univ : Set Y) n`. -/
def toTopCatCWComplexAttachCellsEquiv (n : ℕ) (hn : ¬ IsMax n) :
    ((Y.toTopCatCWComplex).attachCells n hn).ι ≃ cell (univ : Set Y) n := Equiv.refl _

/-- The cells of `Y.toTopCatCWComplex` are `Σ n, cell (univ : Set Y) n`. -/
def toTopCatCWComplexCellsEquiv : (Y.toTopCatCWComplex).Cells ≃ Σ n : ℕ, cell (univ : Set Y) n where
  toFun γ := ⟨γ.j, Y.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k⟩
  invFun γ :=
    ⟨γ.1, not_isMax γ.1, (Y.toTopCatCWComplexAttachCellsEquiv γ.1 (not_isMax γ.1)).symm γ.2⟩
  left_inv γ := by cases γ; rfl
  right_inv _ := rfl

@[simp] lemma toTopCatCWComplexCellsEquiv_apply (γ : (Y.toTopCatCWComplex).Cells) :
    Y.toTopCatCWComplexCellsEquiv γ = ⟨γ.j, Y.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k⟩ :=
  (rfl)

@[simp] lemma toTopCatCWComplexCellsEquiv_symm_apply (n : ℕ) (i : cell (univ : Set Y) n) :
    (Y.toTopCatCWComplexCellsEquiv).symm ⟨n, i⟩ =
      ⟨n, not_isMax n, (Y.toTopCatCWComplexAttachCellsEquiv n (not_isMax n)).symm i⟩ := (rfl)

/-- The inclusion of a cell of `Y.toTopCatCWComplex` is the characteristic map of the corresponding
classical cell, read on the Euclidean disk through `TauCeti.diskHomeomorphClosedBall`. -/
@[simp] lemma toTopCatCWComplex_cells_ι_apply (γ : (Y.toTopCatCWComplex).Cells)
    (z : TopCat.disk.{w} γ.j) :
    γ.ι z = map (C := (univ : Set Y)) γ.j (Y.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k)
      (diskHomeomorphClosedBall γ.j z) := by
  let γ' : (toRelativeCWComplex (univ : Set Y)).Cells := ⟨γ.j, γ.hj, γ.k⟩
  have hincl : eqToHom (Y.toTopCatCWComplex_obj (Order.succ γ.j))
      ((Y.toTopCatCWComplex.attachCells γ.j γ.hj).cell γ.k z) =
      ((toRelativeCWComplex (univ : Set Y)).attachCells γ'.j γ'.hj).cell γ'.k z := by
    dsimp only [toTopCatCWComplex, MorphismProperty.TransfiniteCompositionOfShape.ofArrowIso,
      TransfiniteCompositionOfShape.ofArrowIso, toRelativeCWComplex, γ']
    generalize_proofs; rw [eqToHom_refl]; exact ConcreteCategory.id_apply _
  refine (?_ : γ.ι z = (γ'.ι z : Y)).trans (coe_toRelativeCWComplex_cells_ι_apply γ' z)
  rw [RelativeCellComplex.Cells.ι, Y.toTopCatCWComplex_incl_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, TopCat.ofHom_apply, hincl]
  exact (coe_toRelativeCWComplex_incl_app_apply (Order.succ γ'.j) _).symm

end ToTopCatCWComplex

end TopCat
