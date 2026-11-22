/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.BlockSucc
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Category.CompactlyGenerated.GrpObj
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Homotopy.HomotopyGroup.SequentialColimit
public import TauCeti.Topology.Grassmannian.StiefelFibration.Stability
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Stable orthogonal and special orthogonal groups

Placing an `n × n` orthogonal or special orthogonal matrix in the upper-left block and extending
with `1` on the diagonal (`TauCeti.orthogonalBlockSucc` and `TauCeti.specialOrthogonalBlockSucc`)
gives sequential diagrams of compact Hausdorff topological groups indexed by `ℕ`.

Using the colimit-creation machinery for group objects in the Cartesian closed category
`CompactlyGenerated` (`TauCeti.CategoryTheory.Monoidal.SiftedColimits` and
`TauCeti.Topology.Category.CompactlyGenerated.GrpObj`), together with the fact that the ordinary
product of two sequential colimits of compact Hausdorff spaces along embeddings is compactly
generated (`TauCeti.TopCat.uCompactlyGeneratedSpace_prod_of_isColimit`), the sequential colimits
form Hausdorff (`T4`), compactly generated topological groups:
* `TauCeti.StableOrthogonalGroup` (`O`), the sequential colimit of
  `O(n) := Matrix.orthogonalGroup (Fin n) ℝ`;
* `TauCeti.StableSpecialOrthogonalGroup` (`SO`), the sequential colimit of
  `SO(n) := Matrix.specialOrthogonalGroup (Fin n) ℝ`.

Because the finite stages are compact and the colimit topology coincides with the `TopCat` colimit
topology, both stable groups enjoy full topological-group universal properties (`lift`, into
arbitrary topological groups) as well as continuous-map universal properties (`liftContinuous`),
their finite stages embed as closed subgroups (`isClosedEmbedding_of`), the determinant descends to
a continuous homomorphism `TauCeti.StableOrthogonalGroup.det : StableOrthogonalGroup →ₜ* ℤˣ`,
and `SO` embeds as the identity path component of `O`. Combining the stability theorem for the
Stiefel fibrations (`TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne`) with
`TauCeti.TopCat.isNConnected_ι_of_forall_succ`, each inclusion `SO(n) → SO` and `O(n) → O`
(`n ≥ 1`) is `(n - 1)`-connected and induces isomorphisms `π_N(SO(n)) ≃* π_N(SO)` and
`π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and `Nat.card N + 2 ≤ n`, as well as
`π_N(SO) ≃* π_N(O)` for every nonempty `N`.

## Main definitions

* `TauCeti.StableOrthogonalGroup`, `TauCeti.StableSpecialOrthogonalGroup`: the stable orthogonal
  and special orthogonal groups `O` and `SO`.
* `TauCeti.StableOrthogonalGroup.of`, `TauCeti.StableSpecialOrthogonalGroup.of`: the canonical
  continuous inclusions `O(n) →ₜ* O` and `SO(n) →ₜ* SO`.
* `TauCeti.StableOrthogonalGroup.lift`, `TauCeti.StableSpecialOrthogonalGroup.lift`: universal
  properties for continuous homomorphisms into arbitrary topological groups.
* `TauCeti.StableOrthogonalGroup.det`: the continuous determinant homomorphism `O →ₜ* ℤˣ`.
* `TauCeti.StableSpecialOrthogonalGroup.toStableOrthogonalGroup`: the inclusion `SO →ₜ* O`.

## Main results

* `TauCeti.StableOrthogonalGroup.isClosedEmbedding_of`,
  `TauCeti.StableSpecialOrthogonalGroup.isClosedEmbedding_of`: the finite-stage inclusions are
  closed embeddings.
* `TauCeti.StableSpecialOrthogonalGroup.isClosedEmbedding_toStableOrthogonalGroup`,
  `TauCeti.StableSpecialOrthogonalGroup.isOpenEmbedding_toStableOrthogonalGroup`: `SO → O` is both
  a closed and an open embedding with image `det.ker`.
* `TauCeti.StableOrthogonalGroup.joined_iff_det_eq`: path components of `O` are classified by
  determinant.
* `TauCeti.StableSpecialOrthogonalGroup.isNConnected_of`,
  `TauCeti.StableOrthogonalGroup.isNConnected_of`: `SO(n) → SO` and `O(n) → O` (`n ≥ 1`) are
  `(n - 1)`-connected.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf`,
  `TauCeti.StableOrthogonalGroup.homotopyGroupMulEquivOf`: stable homotopy group isomorphisms
  `π_N(SO(n)) ≃* π_N(SO)` and `π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and
  `Nat.card N + 2 ≤ n`.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup`:
  `π_N(SO) ≃* π_N(O)` for all nonempty `N`.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Set

namespace TauCeti

attribute [local instance] starRingOfComm

section FiniteStages

/-- The block inclusion `O(n) → O(n + 1)` is continuous. -/
theorem continuous_orthogonalBlockSucc (n : ℕ) :
    Continuous (orthogonalBlockSucc ℝ n) := by
  refine continuous_induced_rng.2 ?_
  have hcoe : (Subtype.val ∘ orthogonalBlockSucc ℝ n) =
      fun A : Matrix.orthogonalGroup (Fin n) ℝ ↦
        Matrix.blockSucc (A : Matrix (Fin n) (Fin n) ℝ) :=
    funext fun A ↦ coe_orthogonalBlockSucc ℝ n A
  rw [hcoe]
  refine continuous_matrix fun i j ↦ ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [continuous_const]
    | cast j => simp [continuous_const]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [continuous_const]
    | cast j =>
      have h : (fun A : Matrix.orthogonalGroup (Fin n) ℝ ↦
          Matrix.blockSucc (A : Matrix (Fin n) (Fin n) ℝ) i.castSucc j.castSucc) =
          fun A : Matrix.orthogonalGroup (Fin n) ℝ ↦ (A : Matrix (Fin n) (Fin n) ℝ) i j :=
        funext fun A ↦ Matrix.blockSucc_castSucc_castSucc _ i j
      rw [h]
      exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtypeVal)

private theorem isClosedEmbedding_orthogonalBlockSucc (n : ℕ) :
    IsClosedEmbedding (orthogonalBlockSucc ℝ n) :=
  (continuous_orthogonalBlockSucc n).isClosedEmbedding (orthogonalBlockSucc_injective ℝ n)

/-- The orthogonal block inclusion as a continuous monoid homomorphism `O(n) →ₜ* O(n + 1)`. -/
@[expose]
def continuousOrthogonalBlockSucc (n : ℕ) :
    Matrix.orthogonalGroup (Fin n) ℝ →ₜ* Matrix.orthogonalGroup (Fin (n + 1)) ℝ where
  __ := orthogonalBlockSucc ℝ n
  continuous_toFun := continuous_orthogonalBlockSucc n

@[simp]
theorem continuousOrthogonalBlockSucc_apply (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    continuousOrthogonalBlockSucc n A = orthogonalBlockSucc ℝ n A := rfl

/-- The block inclusion `SO(n) → SO(n + 1)` is continuous. -/
theorem continuous_specialOrthogonalBlockSucc (n : ℕ) :
    Continuous (specialOrthogonalBlockSucc ℝ n) := by
  refine continuous_induced_rng.2 ?_
  have hcoe : (Subtype.val ∘ specialOrthogonalBlockSucc ℝ n) =
      fun A : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦
        Matrix.blockSucc (A : Matrix (Fin n) (Fin n) ℝ) :=
    funext fun A ↦ coe_specialOrthogonalBlockSucc ℝ n A
  rw [hcoe]
  refine continuous_matrix fun i j ↦ ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [continuous_const]
    | cast j => simp [continuous_const]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [continuous_const]
    | cast j =>
      have h : (fun A : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦
          Matrix.blockSucc (A : Matrix (Fin n) (Fin n) ℝ) i.castSucc j.castSucc) =
          fun A : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦
            (A : Matrix (Fin n) (Fin n) ℝ) i j :=
        funext fun A ↦ Matrix.blockSucc_castSucc_castSucc _ i j
      rw [h]
      exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtypeVal)

private theorem isClosedEmbedding_specialOrthogonalBlockSucc (n : ℕ) :
    IsClosedEmbedding (specialOrthogonalBlockSucc ℝ n) :=
  (continuous_specialOrthogonalBlockSucc n).isClosedEmbedding
    (specialOrthogonalBlockSucc_injective ℝ n)

/-- The special orthogonal block inclusion as a continuous monoid homomorphism
`SO(n) →ₜ* SO(n + 1)`. -/
@[expose]
def continuousSpecialOrthogonalBlockSucc (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →ₜ*
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ where
  __ := specialOrthogonalBlockSucc ℝ n
  continuous_toFun := continuous_specialOrthogonalBlockSucc n

@[simp]
theorem continuousSpecialOrthogonalBlockSucc_apply (n : ℕ)
    (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    continuousSpecialOrthogonalBlockSucc n A = specialOrthogonalBlockSucc ℝ n A := rfl

private theorem continuous_toOrthogonalGroup (n : ℕ) :
    Continuous (Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ)) := by
  refine continuous_induced_rng.2 ?_
  have hcoe : (Subtype.val ∘
      Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ)) =
      fun A : Matrix.specialOrthogonalGroup (Fin n) ℝ ↦ (A : Matrix (Fin n) (Fin n) ℝ) :=
    funext fun A ↦ Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup A
  rw [hcoe]
  exact continuous_subtypeVal

private theorem isClosedEmbedding_toOrthogonalGroup (n : ℕ) :
    IsClosedEmbedding
      (Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ)) :=
  (continuous_toOrthogonalGroup n).isClosedEmbedding fun _ _ h ↦ Subtype.ext <| by
    have hval := congrArg (fun X : Matrix.orthogonalGroup (Fin n) ℝ ↦
      (X : Matrix (Fin n) (Fin n) ℝ)) h
    simpa [Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup] using hval

private instance instCompactSpaceOrthogonalGroup (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  isCompact_iff_compactSpace.1 (TauCeti.Matrix.isCompact_unitaryGroup (n := Fin n) (𝕜 := ℝ))

private instance instCompactSpaceSpecialOrthogonalGroup (n : ℕ) :
    CompactSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  isCompact_iff_compactSpace.1
    (TauCeti.Matrix.isCompact_specialUnitaryGroup (n := Fin n) (𝕜 := ℝ))

private instance : IsSifted ℕ := IsFiltered.isSifted

/-- One step `O(n) ⟶ O(n + 1)` of the sequential diagram defining `StableOrthogonalGroup`
in `Grp CompactlyGenerated`. -/
@[expose]
def orthogonalGrpStep (n : ℕ) :
    (⟨CompactlyGenerated.of.{0, 0} (Matrix.orthogonalGroup (Fin n) ℝ)⟩ :
      Grp CompactlyGenerated.{0, 0}) ⟶
      ⟨CompactlyGenerated.of.{0, 0} (Matrix.orthogonalGroup (Fin (n + 1)) ℝ)⟩ :=
  Grp.homMk (CompactlyGenerated.ofHom (continuousOrthogonalBlockSucc n : C(_, _)))

/-- The sequential diagram `n ↦ O(n)` in `Grp CompactlyGenerated`. -/
@[expose]
def orthogonalGrpDiagram : ℕ ⥤ Grp CompactlyGenerated.{0, 0} :=
  Functor.ofSequence orthogonalGrpStep

/-- One step `SO(n) ⟶ SO(n + 1)` of the sequential diagram defining
`StableSpecialOrthogonalGroup` in `Grp CompactlyGenerated`. -/
@[expose]
def specialOrthogonalGrpStep (n : ℕ) :
    (⟨CompactlyGenerated.of.{0, 0} (Matrix.specialOrthogonalGroup (Fin n) ℝ)⟩ :
      Grp CompactlyGenerated.{0, 0}) ⟶
      ⟨CompactlyGenerated.of.{0, 0} (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)⟩ :=
  Grp.homMk (CompactlyGenerated.ofHom (continuousSpecialOrthogonalBlockSucc n : C(_, _)))

/-- The sequential diagram `n ↦ SO(n)` in `Grp CompactlyGenerated`. -/
@[expose]
def specialOrthogonalGrpDiagram : ℕ ⥤ Grp CompactlyGenerated.{0, 0} :=
  Functor.ofSequence specialOrthogonalGrpStep

/-- The underlying diagram of topological spaces `n ↦ O(n)` in `TopCat`. -/
abbrev orthogonalTopDiagram : ℕ ⥤ TopCat.{0} :=
  orthogonalGrpDiagram ⋙ Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop

/-- The underlying diagram of topological spaces `n ↦ SO(n)` in `TopCat`. -/
abbrev specialOrthogonalTopDiagram : ℕ ⥤ TopCat.{0} :=
  specialOrthogonalGrpDiagram ⋙ Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop

private instance (n : ℕ) : CompactSpace (orthogonalTopDiagram.obj n) := by
  change CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T2Space (orthogonalTopDiagram.obj n) := by
  change T2Space (Matrix.orthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T1Space (orthogonalTopDiagram.obj n) := by
  change T1Space (Matrix.orthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T4Space (orthogonalTopDiagram.obj n) := by
  change T4Space (Matrix.orthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : CompactSpace (specialOrthogonalTopDiagram.obj n) := by
  change CompactSpace (Matrix.specialOrthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T2Space (specialOrthogonalTopDiagram.obj n) := by
  change T2Space (Matrix.specialOrthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T1Space (specialOrthogonalTopDiagram.obj n) := by
  change T1Space (Matrix.specialOrthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T4Space (specialOrthogonalTopDiagram.obj n) := by
  change T4Space (Matrix.specialOrthogonalGroup (Fin n) ℝ); infer_instance

private lemma orthogonalTopDiagram_map_succ (n : ℕ) (x : Matrix.orthogonalGroup (Fin n) ℝ) :
    orthogonalTopDiagram.map (homOfLE n.le_succ) x = orthogonalBlockSucc ℝ n x := by
  change (Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop).map
      ((Functor.ofSequence orthogonalGrpStep).map (homOfLE (Nat.le_add_right n 1))) x = _
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

private lemma specialOrthogonalTopDiagram_map_succ (n : ℕ)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    specialOrthogonalTopDiagram.map (homOfLE n.le_succ) x =
      specialOrthogonalBlockSucc ℝ n x := by
  change (Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop).map
      ((Functor.ofSequence specialOrthogonalGrpStep).map (homOfLE (Nat.le_add_right n 1))) x = _
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

private lemma orthogonalTopDiagram_naturality {Y : Type*}
    (f : ∀ n, Matrix.orthogonalGroup (Fin n) ℝ → Y)
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A)
    {i j : ℕ} (hij : i ≤ j) (A : orthogonalTopDiagram.obj i) :
    f j (orthogonalTopDiagram.map (homOfLE hij) A) = f i A := by
  refine @Nat.le_induction i
    (fun j h ↦ f j (orthogonalTopDiagram.map (homOfLE h) A) = f i A)
    ?_ (fun k hk ih ↦ ?_) j hij
  · have hid : homOfLE (le_refl i) = 𝟙 i := rfl
    rw [hid, orthogonalTopDiagram.map_id]
    rfl
  · have hsucc : (homOfLE hk.step : i ⟶ k + 1) = homOfLE hk ≫ homOfLE k.le_succ := rfl
    calc f (k + 1) (orthogonalTopDiagram.map (homOfLE hk.step) A)
        = f (k + 1) (orthogonalTopDiagram.map (homOfLE k.le_succ)
            (orthogonalTopDiagram.map (homOfLE hk) A)) := by
          rw [hsucc, orthogonalTopDiagram.map_comp, ConcreteCategory.comp_apply]
      _ = f (k + 1) (orthogonalBlockSucc ℝ k (orthogonalTopDiagram.map (homOfLE hk) A)) :=
          congrArg (f (k + 1)) (orthogonalTopDiagram_map_succ k _)
      _ = f k (orthogonalTopDiagram.map (homOfLE hk) A) := hf _ _
      _ = f i A := ih

private lemma specialOrthogonalTopDiagram_naturality {Y : Type*}
    (f : ∀ n, Matrix.specialOrthogonalGroup (Fin n) ℝ → Y)
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A)
    {i j : ℕ} (hij : i ≤ j) (A : specialOrthogonalTopDiagram.obj i) :
    f j (specialOrthogonalTopDiagram.map (homOfLE hij) A) = f i A := by
  refine @Nat.le_induction i
    (fun j h ↦ f j (specialOrthogonalTopDiagram.map (homOfLE h) A) = f i A)
    ?_ (fun k hk ih ↦ ?_) j hij
  · have hid : homOfLE (le_refl i) = 𝟙 i := rfl
    rw [hid, specialOrthogonalTopDiagram.map_id]
    rfl
  · have hsucc : (homOfLE hk.step : i ⟶ k + 1) = homOfLE hk ≫ homOfLE k.le_succ := rfl
    calc f (k + 1) (specialOrthogonalTopDiagram.map (homOfLE hk.step) A)
        = f (k + 1) (specialOrthogonalTopDiagram.map (homOfLE k.le_succ)
            (specialOrthogonalTopDiagram.map (homOfLE hk) A)) := by
          rw [hsucc, specialOrthogonalTopDiagram.map_comp, ConcreteCategory.comp_apply]
      _ = f (k + 1)
            (specialOrthogonalBlockSucc ℝ k (specialOrthogonalTopDiagram.map (homOfLE hk) A)) :=
          congrArg (f (k + 1)) (specialOrthogonalTopDiagram_map_succ k _)
      _ = f k (specialOrthogonalTopDiagram.map (homOfLE hk) A) := hf _ _
      _ = f i A := ih

end FiniteStages

/-! ### The stable orthogonal group `O` -/

/-- **The stable orthogonal group `O`**: the sequential colimit of the real matrix orthogonal
groups `O(n)` along the block inclusions `A ↦ diag(A, 1)`, equipped with the sequential colimit
topology (which is `T4`, compactly generated, and makes multiplication and inversion jointly
continuous). -/
@[expose]
def StableOrthogonalGroup : Type :=
  (colimit orthogonalGrpDiagram).X

namespace StableOrthogonalGroup

/-- The colimit cocone in `TopCat` underlying `StableOrthogonalGroup`. -/
@[expose]
def topCocone : Cocone orthogonalTopDiagram :=
  (Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop).mapCocone
      (colimit.cocone orthogonalGrpDiagram)

private def isColimitTopCocone : IsColimit topCocone :=
  isColimitOfPreserves
    (Grp.forget CompactlyGenerated.{0, 0} ⋙ CompactlyGenerated.compactlyGeneratedToTop)
    (colimit.isColimit orthogonalGrpDiagram)

instance : TopologicalSpace StableOrthogonalGroup :=
  (colimit orthogonalGrpDiagram).X.toTop.str

instance : Group StableOrthogonalGroup :=
  CompactlyGenerated.groupOfGrpObj (colimit orthogonalGrpDiagram).X

instance : UCompactlyGeneratedSpace.{0} StableOrthogonalGroup :=
  (colimit orthogonalGrpDiagram).X.is_compactly_generated

private lemma isClosedEmbedding_topDiagram_succ (n : ℕ) :
    IsClosedEmbedding (orthogonalTopDiagram.map (homOfLE n.le_succ)) := by
  have hfn : (orthogonalTopDiagram.map (homOfLE n.le_succ) :
      Matrix.orthogonalGroup (Fin n) ℝ → Matrix.orthogonalGroup (Fin (n + 1)) ℝ) =
      orthogonalBlockSucc ℝ n :=
    funext (orthogonalTopDiagram_map_succ n)
  exact hfn ▸ isClosedEmbedding_orthogonalBlockSucc n

private instance instUCompactlyGeneratedSpaceProd :
    UCompactlyGeneratedSpace.{0} (StableOrthogonalGroup × StableOrthogonalGroup) :=
  TopCat.uCompactlyGeneratedSpace_prod_of_isColimit isColimitTopCocone isColimitTopCocone
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
      isColimitTopCocone · |>.isEmbedding)
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
      isColimitTopCocone · |>.isEmbedding)

instance : IsTopologicalGroup StableOrthogonalGroup :=
  CompactlyGenerated.isTopologicalGroup_of_grpObj (colimit orthogonalGrpDiagram).X
    instUCompactlyGeneratedSpaceProd

instance : T4Space StableOrthogonalGroup :=
  TopCat.t4Space_of_isColimit isClosedEmbedding_topDiagram_succ isColimitTopCocone

/-- The canonical continuous inclusion `O(n) →ₜ* O` from stage `n` into the stable orthogonal
group. -/
@[expose]
def of (n : ℕ) : Matrix.orthogonalGroup (Fin n) ℝ →ₜ* StableOrthogonalGroup where
  toFun := (topCocone.ι.app n).hom
  map_one' := ConcreteCategory.congr_hom
    (IsMonHom.one_hom ((colimit.cocone orthogonalGrpDiagram).ι.app n).hom.hom) PUnit.unit
  map_mul' x y := ConcreteCategory.congr_hom
    (IsMonHom.mul_hom ((colimit.cocone orthogonalGrpDiagram).ι.app n).hom.hom) (x, y)
  continuous_toFun := (topCocone.ι.app n).hom.continuous

private lemma coe_of_eq_topCocone (n : ℕ) :
    (of n : Matrix.orthogonalGroup (Fin n) ℝ → StableOrthogonalGroup) =
      topCocone.ι.app n := rfl

@[simp]
theorem of_orthogonalBlockSucc (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    of (n + 1) (orthogonalBlockSucc ℝ n A) = of n A := by
  change (topCocone.ι.app (n + 1)).hom (orthogonalBlockSucc ℝ n A) = (topCocone.ι.app n).hom A
  rw [← orthogonalTopDiagram_map_succ n A]
  exact ConcreteCategory.congr_hom (topCocone.w (homOfLE n.le_succ)) A

@[simp]
theorem of_comp_continuousOrthogonalBlockSucc (n : ℕ) :
    (of (n + 1)).comp (continuousOrthogonalBlockSucc n) = of n :=
  ContinuousMonoidHom.ext (of_orthogonalBlockSucc n)

theorem of_le {m n : ℕ} (h : m ≤ n) (A : Matrix.orthogonalGroup (Fin m) ℝ) :
    of n (orthogonalTopDiagram.map (homOfLE h) A) = of m A := by
  have hw := topCocone.w (homOfLE h)
  exact ConcreteCategory.congr_hom hw A

/-- Every finite-stage inclusion `O(n) → O` is a closed embedding. -/
theorem isClosedEmbedding_of (n : ℕ) : IsClosedEmbedding (of n) :=
  TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
    isColimitTopCocone n

/-- Every finite-stage inclusion `O(n) → O` is injective. -/
theorem of_injective (n : ℕ) : Function.Injective (of n) :=
  (isClosedEmbedding_of n).injective

/-- Every element of `O` lies in the image of some finite stage `O(n)`. -/
theorem exists_of (x : StableOrthogonalGroup) :
    ∃ (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ), of n A = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) isColimitTopCocone) x

/-- Any two elements of `O` lie in the image of a common finite stage `O(n)`. -/
theorem exists_of₂ (x y : StableOrthogonalGroup) :
    ∃ (n : ℕ) (A B : Matrix.orthogonalGroup (Fin n) ℝ), of n A = x ∧ of n B = y := by
  obtain ⟨m, A, rfl⟩ := exists_of x
  obtain ⟨k, B, rfl⟩ := exists_of y
  refine ⟨max m k, orthogonalTopDiagram.map (homOfLE (le_max_left m k)) A,
    orthogonalTopDiagram.map (homOfLE (le_max_right m k)) B, ?_, ?_⟩
  · exact of_le (le_max_left m k) A
  · exact of_le (le_max_right m k) B

/-- Two continuous homomorphisms out of `O` agree when they agree on every finite stage `O(n)`. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] [TopologicalSpace G] {f g : StableOrthogonalGroup →ₜ* G}
    (h : ∀ n, f.comp (of n) = g.comp (of n)) : f = g := by
  ext x
  obtain ⟨n, A, rfl⟩ := exists_of x
  exact DFunLike.congr_fun (h n) A

/-- Two continuous maps out of `O` agree when they agree on every finite stage `O(n)`. -/
@[ext]
theorem continuousMap_ext {Y : Type*} [TopologicalSpace Y] {f g : C(StableOrthogonalGroup, Y)}
    (h : ∀ n, f.comp (of n : C(Matrix.orthogonalGroup (Fin n) ℝ, StableOrthogonalGroup)) =
      g.comp (of n : C(Matrix.orthogonalGroup (Fin n) ℝ, StableOrthogonalGroup))) :
    f = g := by
  ext x
  obtain ⟨n, A, rfl⟩ := exists_of x
  exact ContinuousMap.congr_fun (h n) A

private def liftCocone {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.orthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A) :
    letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
      CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
    Cocone orthogonalGrpDiagram :=
  letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let target : Grp CompactlyGenerated.{0, 0} :=
    ⟨TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)⟩
  Cocone.mk target
    { app n :=
        Grp.homMk''
          (CompactlyGenerated.adj.{0, 0}.homEquiv
            (CompactlyGenerated.of.{0, 0} (Matrix.orthogonalGroup (Fin n) ℝ)) (TopCat.of G)
            (TopCat.ofHom (f n : C(_, _))))
          (ConcreteCategory.hom_ext _ _ fun _ ↦ map_one (f n))
          (ConcreteCategory.hom_ext _ _ fun p ↦ map_mul (f n) p.1 p.2)
      naturality i j u := Grp.hom_ext _ _ <| ConcreteCategory.hom_ext _ _ fun A ↦ by
        change f j (orthogonalTopDiagram.map u A) = f i A
        exact orthogonalTopDiagram_naturality (fun k X ↦ f k X) hf (leOfHom u) A }

/-- **Universal property of `O` as a topological group**: a family of continuous homomorphisms out
of `O(n)` into any topological group `G : Type` that is compatible with `orthogonalBlockSucc`
descends to a unique continuous homomorphism `O →ₜ* G`. -/
def lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.orthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A) :
    StableOrthogonalGroup →ₜ* G :=
  letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let coc := liftCocone f hf
  let φ : colimit orthogonalGrpDiagram ⟶ coc.pt :=
    (colimit.isColimit orthogonalGrpDiagram).desc coc
  let fTop : (colimit orthogonalGrpDiagram).X.toTop ⟶ TopCat.of G :=
    (CompactlyGenerated.adj.{0, 0}.homEquiv (colimit orthogonalGrpDiagram).X (TopCat.of G)).symm
      φ.hom.hom
  let fMon : StableOrthogonalGroup →* G := CompactlyGenerated.monoidHomOfIsMonHom φ.hom.hom
  { toFun := fMon
    map_one' := fMon.map_one
    map_mul' := fMon.map_mul
    continuous_toFun := fTop.hom.continuous }

@[simp]
theorem lift_of {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.orthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A)
    (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    lift f hf (of n A) = f n A := by
  let _ : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let coc := liftCocone f hf
  have hfac : ((colimit.cocone orthogonalGrpDiagram).ι.app n ≫
      (colimit.isColimit orthogonalGrpDiagram).desc coc) = coc.ι.app n :=
    (colimit.isColimit orthogonalGrpDiagram).fac coc n
  have hmap := congrArg (fun g ↦ g.hom.hom) hfac
  have h := ConcreteCategory.congr_hom hmap A
  exact h

private def liftContinuousCocone {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.orthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A) :
    Cocone orthogonalTopDiagram :=
  Cocone.mk (TopCat.of Y)
    { app n := TopCat.ofHom (f n)
      naturality i j u := ConcreteCategory.hom_ext _ _ fun A ↦ by
        change f j (orthogonalTopDiagram.map u A) = f i A
        exact orthogonalTopDiagram_naturality (fun k X ↦ f k X) hf (leOfHom u) A }

/-- **Universal property of `O` as a topological space**: a family of continuous maps out of `O(n)`
into a space `Y : Type` compatible with `orthogonalBlockSucc` descends to a unique continuous map
`C(O, Y)`. -/
def liftContinuous {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.orthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A) :
    C(StableOrthogonalGroup, Y) :=
  (isColimitTopCocone.desc (liftContinuousCocone f hf)).hom

@[simp]
theorem liftContinuous_of {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.orthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (orthogonalBlockSucc ℝ n A) = f n A)
    (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    liftContinuous f hf (of n A) = f n A := by
  have hfac := isColimitTopCocone.fac (liftContinuousCocone f hf) n
  have h := ConcreteCategory.congr_hom hfac A
  exact h

private def orthogonalDetSign (n : ℕ) : Matrix.orthogonalGroup (Fin n) ℝ →* ℤˣ where
  toFun A := if (A : Matrix (Fin n) (Fin n) ℝ).det = 1 then 1 else -1
  map_one' := by simp
  map_mul' A B := by
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property with hA | hA <;>
      rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup B.property with hB | hB <;>
      simp [hA, hB, Matrix.det_mul]
    norm_num

private theorem continuous_orthogonalDetSign (n : ℕ) : Continuous (orthogonalDetSign n) := by
  refine Continuous.if ?_ continuous_const continuous_const
  intro A hA
  have hdet : Continuous fun B : Matrix.orthogonalGroup (Fin n) ℝ ↦
      (B : Matrix (Fin n) (Fin n) ℝ).det :=
    continuous_subtypeVal.matrix_det
  have hclopen : IsClopen {B : Matrix.orthogonalGroup (Fin n) ℝ |
      (B : Matrix (Fin n) (Fin n) ℝ).det = 1} := by
    refine ⟨isClosed_singleton.preimage hdet, ?_⟩
    have heq : {B : Matrix.orthogonalGroup (Fin n) ℝ |
        (B : Matrix (Fin n) (Fin n) ℝ).det = 1} =
        {B : Matrix.orthogonalGroup (Fin n) ℝ |
          (0 : ℝ) < (B : Matrix (Fin n) (Fin n) ℝ).det} := by
      ext B
      rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup B.property with hB | hB
      · simp [hB]
      · simp [hB]; norm_num
    rw [heq]
    exact isOpen_lt continuous_const hdet
  rw [hclopen.frontier_eq] at hA
  exact hA.elim

/-- The determinant on `O`, taking values in `ℤˣ = {±1}` (with the discrete topology). -/
def det : StableOrthogonalGroup →ₜ* ℤˣ :=
  lift
    (fun n ↦ ⟨orthogonalDetSign n, continuous_orthogonalDetSign n⟩)
    (fun n A ↦ by
      change orthogonalDetSign (n + 1) (orthogonalBlockSucc ℝ n A) = orthogonalDetSign n A
      apply Units.ext
      simp [orthogonalDetSign])

@[simp]
theorem det_of (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    det (of n A) = if (A : Matrix (Fin n) (Fin n) ℝ).det = 1 then 1 else -1 := by
  rw [det, lift_of]
  rfl

theorem coe_det_of (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    ((det (of n A) : ℤ) : ℝ) = (A : Matrix (Fin n) (Fin n) ℝ).det := by
  rw [det_of]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property with hA | hA
  · simp [hA]
  · simp [hA]; norm_num

end StableOrthogonalGroup

/-! ### The stable special orthogonal group `SO` -/

/-- **The stable special orthogonal group `SO`**: the sequential colimit of the real special
orthogonal groups `SO(n)` along the block inclusions `A ↦ diag(A, 1)`. -/
@[expose]
def StableSpecialOrthogonalGroup : Type :=
  (colimit specialOrthogonalGrpDiagram).X

namespace StableSpecialOrthogonalGroup

/-- The colimit cocone in `TopCat` underlying `StableSpecialOrthogonalGroup`. -/
@[expose]
def topCocone : Cocone specialOrthogonalTopDiagram :=
  (Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop).mapCocone
      (colimit.cocone specialOrthogonalGrpDiagram)

private def isColimitTopCocone : IsColimit topCocone :=
  isColimitOfPreserves
    (Grp.forget CompactlyGenerated.{0, 0} ⋙ CompactlyGenerated.compactlyGeneratedToTop)
    (colimit.isColimit specialOrthogonalGrpDiagram)

instance : TopologicalSpace StableSpecialOrthogonalGroup :=
  (colimit specialOrthogonalGrpDiagram).X.toTop.str

instance : Group StableSpecialOrthogonalGroup :=
  CompactlyGenerated.groupOfGrpObj (colimit specialOrthogonalGrpDiagram).X

instance : UCompactlyGeneratedSpace.{0} StableSpecialOrthogonalGroup :=
  (colimit specialOrthogonalGrpDiagram).X.is_compactly_generated

private lemma isClosedEmbedding_topDiagram_succ (n : ℕ) :
    IsClosedEmbedding (specialOrthogonalTopDiagram.map (homOfLE n.le_succ)) := by
  have hfn : (specialOrthogonalTopDiagram.map (homOfLE n.le_succ) :
      Matrix.specialOrthogonalGroup (Fin n) ℝ →
        Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) =
      specialOrthogonalBlockSucc ℝ n :=
    funext (specialOrthogonalTopDiagram_map_succ n)
  exact hfn ▸ isClosedEmbedding_specialOrthogonalBlockSucc n

private instance instUCompactlyGeneratedSpaceProd :
    UCompactlyGeneratedSpace.{0} (StableSpecialOrthogonalGroup × StableSpecialOrthogonalGroup) :=
  TopCat.uCompactlyGeneratedSpace_prod_of_isColimit isColimitTopCocone isColimitTopCocone
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
      isColimitTopCocone · |>.isEmbedding)
    (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
      isColimitTopCocone · |>.isEmbedding)

instance : IsTopologicalGroup StableSpecialOrthogonalGroup :=
  CompactlyGenerated.isTopologicalGroup_of_grpObj (colimit specialOrthogonalGrpDiagram).X
    instUCompactlyGeneratedSpaceProd

instance : T4Space StableSpecialOrthogonalGroup :=
  TopCat.t4Space_of_isColimit isClosedEmbedding_topDiagram_succ isColimitTopCocone

/-- The canonical continuous inclusion `SO(n) →ₜ* SO` from stage `n` into the stable special
orthogonal group. -/
@[expose]
def of (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →ₜ* StableSpecialOrthogonalGroup where
  toFun := (topCocone.ι.app n).hom
  map_one' := ConcreteCategory.congr_hom
    (IsMonHom.one_hom ((colimit.cocone specialOrthogonalGrpDiagram).ι.app n).hom.hom)
    PUnit.unit
  map_mul' x y := ConcreteCategory.congr_hom
    (IsMonHom.mul_hom ((colimit.cocone specialOrthogonalGrpDiagram).ι.app n).hom.hom)
    (x, y)
  continuous_toFun := (topCocone.ι.app n).hom.continuous

private lemma coe_of_eq_topCocone (n : ℕ) :
    (of n : Matrix.specialOrthogonalGroup (Fin n) ℝ → StableSpecialOrthogonalGroup) =
      topCocone.ι.app n := rfl

@[simp]
theorem of_specialOrthogonalBlockSucc (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    of (n + 1) (specialOrthogonalBlockSucc ℝ n A) = of n A := by
  change (topCocone.ι.app (n + 1)).hom (specialOrthogonalBlockSucc ℝ n A) =
    (topCocone.ι.app n).hom A
  rw [← specialOrthogonalTopDiagram_map_succ n A]
  exact ConcreteCategory.congr_hom (topCocone.w (homOfLE n.le_succ)) A

@[simp]
theorem of_comp_continuousSpecialOrthogonalBlockSucc (n : ℕ) :
    (of (n + 1)).comp (continuousSpecialOrthogonalBlockSucc n) = of n :=
  ContinuousMonoidHom.ext (of_specialOrthogonalBlockSucc n)

theorem of_le {m n : ℕ} (h : m ≤ n) (A : Matrix.specialOrthogonalGroup (Fin m) ℝ) :
    of n (specialOrthogonalTopDiagram.map (homOfLE h) A) = of m A := by
  have hw := topCocone.w (homOfLE h)
  exact ConcreteCategory.congr_hom hw A

/-- Every finite-stage inclusion `SO(n) → SO` is a closed embedding. -/
theorem isClosedEmbedding_of (n : ℕ) : IsClosedEmbedding (of n) :=
  TopCat.isClosedEmbedding_ι_of_isColimit_of_succ isClosedEmbedding_topDiagram_succ
    isColimitTopCocone n

/-- Every finite-stage inclusion `SO(n) → SO` is injective. -/
theorem of_injective (n : ℕ) : Function.Injective (of n) :=
  (isClosedEmbedding_of n).injective

/-- Every element of `SO` lies in the image of some finite stage `SO(n)`. -/
theorem exists_of (x : StableSpecialOrthogonalGroup) :
    ∃ (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ), of n A = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) isColimitTopCocone) x

/-- Any two elements of `SO` lie in the image of a common finite stage `SO(n)`. -/
theorem exists_of₂ (x y : StableSpecialOrthogonalGroup) :
    ∃ (n : ℕ) (A B : Matrix.specialOrthogonalGroup (Fin n) ℝ), of n A = x ∧ of n B = y := by
  obtain ⟨m, A, rfl⟩ := exists_of x
  obtain ⟨k, B, rfl⟩ := exists_of y
  refine ⟨max m k, specialOrthogonalTopDiagram.map (homOfLE (le_max_left m k)) A,
    specialOrthogonalTopDiagram.map (homOfLE (le_max_right m k)) B, ?_, ?_⟩
  · exact of_le (le_max_left m k) A
  · exact of_le (le_max_right m k) B

/-- Two continuous homomorphisms out of `SO` agree when they agree on every finite stage `SO(n)`. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] [TopologicalSpace G]
    {f g : StableSpecialOrthogonalGroup →ₜ* G}
    (h : ∀ n, f.comp (of n) = g.comp (of n)) : f = g := by
  ext x
  obtain ⟨n, A, rfl⟩ := exists_of x
  exact DFunLike.congr_fun (h n) A

/-- Two continuous maps out of `SO` agree when they agree on every finite stage `SO(n)`. -/
@[ext]
theorem continuousMap_ext {Y : Type*} [TopologicalSpace Y]
    {f g : C(StableSpecialOrthogonalGroup, Y)}
    (h : ∀ n, f.comp (of n : C(Matrix.specialOrthogonalGroup (Fin n) ℝ,
        StableSpecialOrthogonalGroup)) =
      g.comp (of n : C(Matrix.specialOrthogonalGroup (Fin n) ℝ,
        StableSpecialOrthogonalGroup))) :
    f = g := by
  ext x
  obtain ⟨n, A, rfl⟩ := exists_of x
  exact ContinuousMap.congr_fun (h n) A

private def liftCocone {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.specialOrthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A) :
    letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
      CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
    Cocone specialOrthogonalGrpDiagram :=
  letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let target : Grp CompactlyGenerated.{0, 0} :=
    ⟨TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)⟩
  Cocone.mk target
    { app n :=
        Grp.homMk''
          (CompactlyGenerated.adj.{0, 0}.homEquiv
            (CompactlyGenerated.of.{0, 0} (Matrix.specialOrthogonalGroup (Fin n) ℝ)) (TopCat.of G)
            (TopCat.ofHom (f n : C(_, _))))
          (ConcreteCategory.hom_ext _ _ fun _ ↦ map_one (f n))
          (ConcreteCategory.hom_ext _ _ fun p ↦ map_mul (f n) p.1 p.2)
      naturality i j u := Grp.hom_ext _ _ <| ConcreteCategory.hom_ext _ _ fun A ↦ by
        change f j (specialOrthogonalTopDiagram.map u A) = f i A
        exact specialOrthogonalTopDiagram_naturality (fun k X ↦ f k X) hf (leOfHom u) A }

/-- **Universal property of `SO` as a topological group**: a family of continuous homomorphisms out
of `SO(n)` into any topological group `G : Type` compatible with `specialOrthogonalBlockSucc`
descends to a unique continuous homomorphism `SO →ₜ* G`. -/
def lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.specialOrthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A) :
    StableSpecialOrthogonalGroup →ₜ* G :=
  letI : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let coc := liftCocone f hf
  let φ : colimit specialOrthogonalGrpDiagram ⟶ coc.pt :=
    (colimit.isColimit specialOrthogonalGrpDiagram).desc coc
  let fTop : (colimit specialOrthogonalGrpDiagram).X.toTop ⟶ TopCat.of G :=
    (CompactlyGenerated.adj.{0, 0}.homEquiv
      (colimit specialOrthogonalGrpDiagram).X (TopCat.of G)).symm φ.hom.hom
  let fMon : StableSpecialOrthogonalGroup →* G :=
    CompactlyGenerated.monoidHomOfIsMonHom φ.hom.hom
  { toFun := fMon
    map_one' := fMon.map_one
    map_mul' := fMon.map_mul
    continuous_toFun := fTop.hom.continuous }

@[simp]
theorem lift_of {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ∀ n, Matrix.specialOrthogonalGroup (Fin n) ℝ →ₜ* G)
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A)
    (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    lift f hf (of n A) = f n A := by
  let _ : GrpObj (TopCat.toCompactlyGenerated.{0, 0}.obj (TopCat.of G)) :=
    CompactlyGenerated.instGrpObjToCompactlyGeneratedOf G
  let coc := liftCocone f hf
  have hfac : ((colimit.cocone specialOrthogonalGrpDiagram).ι.app n ≫
      (colimit.isColimit specialOrthogonalGrpDiagram).desc coc) = coc.ι.app n :=
    (colimit.isColimit specialOrthogonalGrpDiagram).fac coc n
  have hmap := congrArg (fun g ↦ g.hom.hom) hfac
  have h := ConcreteCategory.congr_hom hmap A
  exact h

private def liftContinuousCocone {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.specialOrthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A) :
    Cocone specialOrthogonalTopDiagram :=
  Cocone.mk (TopCat.of Y)
    { app n := TopCat.ofHom (f n)
      naturality i j u := ConcreteCategory.hom_ext _ _ fun A ↦ by
        change f j (specialOrthogonalTopDiagram.map u A) = f i A
        exact specialOrthogonalTopDiagram_naturality (fun k X ↦ f k X) hf (leOfHom u) A }

/-- **Universal property of `SO` as a topological space**: a family of continuous maps out of
`SO(n)` into a space `Y : Type` compatible with `specialOrthogonalBlockSucc` descends to a unique
continuous map `C(SO, Y)`. -/
def liftContinuous {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.specialOrthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A) :
    C(StableSpecialOrthogonalGroup, Y) :=
  (isColimitTopCocone.desc (liftContinuousCocone f hf)).hom

@[simp]
theorem liftContinuous_of {Y : Type} [TopologicalSpace Y]
    (f : ∀ n, C(Matrix.specialOrthogonalGroup (Fin n) ℝ, Y))
    (hf : ∀ n A, f (n + 1) (specialOrthogonalBlockSucc ℝ n A) = f n A)
    (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    liftContinuous f hf (of n A) = f n A := by
  have hfac := isColimitTopCocone.fac (liftContinuousCocone f hf) n
  have h := ConcreteCategory.congr_hom hfac A
  exact h

/-- **The stable special orthogonal group is path-connected.** -/
instance : PathConnectedSpace StableSpecialOrthogonalGroup := by
  refine ⟨⟨1⟩, fun x y ↦ ?_⟩
  obtain ⟨n, A, B, rfl, rfl⟩ := exists_of₂ x y
  exact (PathConnectedSpace.joined A B).map (of n).continuous

/-- The canonical inclusion `SO →ₜ* O`, induced by `SO(n) →* O(n)`. -/
def toStableOrthogonalGroup : StableSpecialOrthogonalGroup →ₜ* StableOrthogonalGroup :=
  lift
    (fun n ↦ (StableOrthogonalGroup.of n).comp
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup, continuous_toOrthogonalGroup n⟩)
    (fun n A ↦ by
      change StableOrthogonalGroup.of (n + 1)
        (Matrix.specialOrthogonalGroup.toOrthogonalGroup (specialOrthogonalBlockSucc ℝ n A)) =
        StableOrthogonalGroup.of n (Matrix.specialOrthogonalGroup.toOrthogonalGroup A)
      rw [toOrthogonalGroup_specialOrthogonalBlockSucc,
        StableOrthogonalGroup.of_orthogonalBlockSucc])

@[simp]
theorem toStableOrthogonalGroup_of (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    toStableOrthogonalGroup (of n A) =
      StableOrthogonalGroup.of n (Matrix.specialOrthogonalGroup.toOrthogonalGroup A) := by
  rw [toStableOrthogonalGroup, lift_of]
  rfl

theorem toStableOrthogonalGroup_injective : Function.Injective toStableOrthogonalGroup := by
  intro x y hxy
  obtain ⟨n, A, B, rfl, rfl⟩ := exists_of₂ x y
  simp only [toStableOrthogonalGroup_of] at hxy
  have h1 := StableOrthogonalGroup.of_injective n hxy
  exact congrArg (of n) ((isClosedEmbedding_toOrthogonalGroup n).injective h1)

@[simp]
theorem det_toStableOrthogonalGroup (x : StableSpecialOrthogonalGroup) :
    StableOrthogonalGroup.det (toStableOrthogonalGroup x) = 1 := by
  obtain ⟨n, A, rfl⟩ := exists_of x
  rw [toStableOrthogonalGroup_of, StableOrthogonalGroup.det_of,
    Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup,
    (Matrix.mem_specialOrthogonalGroup_iff.1 A.property).2]
  simp

theorem range_toStableOrthogonalGroup :
    Set.range toStableOrthogonalGroup = (StableOrthogonalGroup.det :
      StableOrthogonalGroup →* ℤˣ).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact det_toStableOrthogonalGroup x
  · intro hy
    obtain ⟨n, B, rfl⟩ := StableOrthogonalGroup.exists_of y
    have hdet : (B : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
      have h := StableOrthogonalGroup.coe_det_of n B
      rw [show (StableOrthogonalGroup.det (StableOrthogonalGroup.of n B) : ℤ) = 1 from
        congrArg Units.val hy] at h
      simpa using h.symm
    refine ⟨of n ⟨B, B.property, hdet⟩, ?_⟩
    rw [toStableOrthogonalGroup_of]
    congr 1
    exact Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup _)

/-- `SO → O` is a closed embedding. -/
theorem isClosedEmbedding_toStableOrthogonalGroup :
    IsClosedEmbedding toStableOrthogonalGroup := by
  refine .of_continuous_injective_isClosedMap toStableOrthogonalGroup.continuous
    toStableOrthogonalGroup_injective fun Z hZ ↦ ?_
  change IsClosed (toStableOrthogonalGroup '' Z : Set StableOrthogonalGroup.topCocone.pt)
  rw [TopCat.isClosed_iff_of_isColimit _ StableOrthogonalGroup.isColimitTopCocone]
  intro n
  have hpre : (StableOrthogonalGroup.of n ⁻¹' (toStableOrthogonalGroup '' Z) :
        Set (Matrix.orthogonalGroup (Fin n) ℝ)) =
      Matrix.specialOrthogonalGroup.toOrthogonalGroup '' (of n ⁻¹' Z) := by
    ext (B : Matrix.orthogonalGroup (Fin n) ℝ)
    constructor
    · rintro ⟨x, hxZ, hxB⟩
      have hx_det : StableOrthogonalGroup.det (StableOrthogonalGroup.of n B) = 1 := by
        rw [← hxB]
        exact det_toStableOrthogonalGroup x
      have hdet : (B : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
        have h := StableOrthogonalGroup.coe_det_of n B
        rw [show (StableOrthogonalGroup.det (StableOrthogonalGroup.of n B) : ℤ) = 1 from
          congrArg Units.val hx_det] at h
        simpa using h.symm
      let B' : Matrix.specialOrthogonalGroup (Fin n) ℝ := ⟨B, B.property, hdet⟩
      have hB' : toStableOrthogonalGroup (of n B') = toStableOrthogonalGroup x := by
        rw [toStableOrthogonalGroup_of]
        have hto : Matrix.specialOrthogonalGroup.toOrthogonalGroup B' = B :=
          Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup B')
        rw [hto, hxB]
      have hxeq : of n B' = x := toStableOrthogonalGroup_injective hB'
      exact ⟨B', by simpa [hxeq] using hxZ,
        Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup B')⟩
    · rintro ⟨B', hB', rfl⟩
      exact ⟨of n B', hB', toStableOrthogonalGroup_of n B'⟩
  change IsClosed (StableOrthogonalGroup.of n ⁻¹' (toStableOrthogonalGroup '' Z))
  rw [hpre]
  exact (isClosedEmbedding_toOrthogonalGroup n).isClosedMap _ (hZ.preimage (of n).continuous)

/-- `SO → O` is an open embedding (its image is the clopen kernel of `det`). -/
theorem isOpenEmbedding_toStableOrthogonalGroup :
    IsOpenEmbedding toStableOrthogonalGroup := by
  refine (isOpenEmbedding_iff _).2 ⟨isClosedEmbedding_toStableOrthogonalGroup.isEmbedding, ?_⟩
  rw [range_toStableOrthogonalGroup]
  exact (isOpen_discrete ({1} : Set ℤˣ)).preimage StableOrthogonalGroup.det.continuous

end StableSpecialOrthogonalGroup

namespace StableOrthogonalGroup

/-- **Path components of `O`**: two points in the stable orthogonal group are joined by a path
exactly when they have the same determinant. -/
theorem joined_iff_det_eq {x y : StableOrthogonalGroup} : Joined x y ↔ det x = det y := by
  constructor
  · rintro ⟨γ⟩
    have hconst : Continuous (det ∘ γ) := det.continuous.comp γ.continuous
    simpa only [Function.comp_apply, γ.source, γ.target] using
      isPreconnected_univ.constant hconst.continuousOn (mem_univ 0) (mem_univ 1)
  · intro h
    obtain ⟨n, A, B, rfl, rfl⟩ := exists_of₂ x y
    have hdet : (A : Matrix (Fin n) (Fin n) ℝ).det = (B : Matrix (Fin n) (Fin n) ℝ).det := by
      rw [← coe_det_of n A, ← coe_det_of n B, h]
    exact (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 hdet).map (of n).continuous

end StableOrthogonalGroup

/-! ### Connectivity and homotopy-group stability -/

section Connectivity

/-- Reindexing `Matrix.orthogonalGroup m ℝ` along an equivalence `e : m ≃ n` as a
topological group isomorphism. -/
def orthogonalReindexContinuousMulEquiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    Matrix.orthogonalGroup m ℝ ≃ₜ* Matrix.orthogonalGroup n ℝ where
  toFun A :=
    ⟨Matrix.reindex e e A.val,
      (Matrix.submatrix_equiv_mem_unitary (A := A.val) (e₁ := e.symm) (e₂ := e.symm)).2
        A.property⟩
  invFun B :=
    ⟨Matrix.reindex e.symm e.symm B.val,
      (Matrix.submatrix_equiv_mem_unitary (A := B.val) (e₁ := e) (e₂ := e)).2 B.property⟩
  left_inv A := Subtype.ext (by simp)
  right_inv B := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext <| by simp [Matrix.reindex_apply]
  continuous_toFun := continuous_induced_rng.2 (continuous_subtypeVal.matrix_reindex e e)
  continuous_invFun := continuous_induced_rng.2 (continuous_subtypeVal.matrix_reindex e.symm e.symm)

/-- Reindexing `Matrix.specialOrthogonalGroup m ℝ` along an equivalence `e : m ≃ n` as a
topological group isomorphism. -/
def specialOrthogonalReindexContinuousMulEquiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    Matrix.specialOrthogonalGroup m ℝ ≃ₜ* Matrix.specialOrthogonalGroup n ℝ where
  toFun A :=
    ⟨Matrix.reindex e e A.val,
      (Matrix.submatrix_equiv_mem_unitary (A := A.val) (e₁ := e.symm) (e₂ := e.symm)).2
        A.property.1,
      by simpa using (Matrix.det_reindex_self e A.val).trans A.property.2⟩
  invFun B :=
    ⟨Matrix.reindex e.symm e.symm B.val,
      (Matrix.submatrix_equiv_mem_unitary (A := B.val) (e₁ := e) (e₂ := e)).2 B.property.1,
      by simpa using (Matrix.det_reindex_self e.symm B.val).trans B.property.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv B := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext <| by simp [Matrix.reindex_apply]
  continuous_toFun := continuous_induced_rng.2 (continuous_subtypeVal.matrix_reindex e e)
  continuous_invFun := continuous_induced_rng.2 (continuous_subtypeVal.matrix_reindex e.symm e.symm)

private def specialOrthogonalToSub (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃ₜ
      {A : Matrix.orthogonalGroup (Fin n) ℝ // (A : Matrix (Fin n) (Fin n) ℝ).det = 1} where
  toFun A :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup A, by
      rw [Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup]
      exact (Matrix.mem_specialOrthogonalGroup_iff.1 A.property).2⟩
  invFun A := ⟨A.val.val, A.val.property, A.property⟩
  left_inv A := Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup A)
  right_inv A := Subtype.ext (Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup _))
  continuous_toFun := (continuous_toOrthogonalGroup n).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtypeVal.comp (continuous_subtypeVal :
      Continuous fun A : {A : Matrix.orthogonalGroup (Fin n) ℝ //
        (A : Matrix (Fin n) (Fin n) ℝ).det = 1} ↦ A.val)) _

/-- **Step connectivity for `SO`**: the block inclusion `SO(n) → SO(n + 1)` is
`(n - 1)`-connected. -/
theorem isNConnected_specialOrthogonalBlockSucc (n : ℕ) :
    (continuousSpecialOrthogonalBlockSucc n).toContinuousMap.IsNConnected (n - 1) := by
  let e : Fin (n + 1) ≃ Fin (1 + n) :=
    (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin 1))).trans finSumFinEquiv
  let φHomeo : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ ≃ₜ
      Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ :=
    (specialOrthogonalReindexContinuousMulEquiv e).toHomeomorph
  let φ : C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ) :=
    φHomeo.toHomotopyEquiv.toFun
  have hcomp : φ.comp (continuousSpecialOrthogonalBlockSucc n).toContinuousMap =
      ⟨Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
        finiteOrthonormalFrame.continuous_fromBlocksOne n⟩ := by
    ext A i j
    exact congrFun (congrFun (reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne ℝ n A) i) j
  have hwhe : φ.IsWeakHomotopyEquivalence :=
    φHomeo.toHomotopyEquiv.isWeakHomotopyEquivalence
  refine (ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff hwhe).1 ?_
  rw [hcomp]
  exact TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne 1 n

/-- **Stability connectivity for `SO`**: the stage inclusion `SO(n) → SO` is
`(n - 1)`-connected. -/
theorem StableSpecialOrthogonalGroup.isNConnected_of (n : ℕ) :
    (StableSpecialOrthogonalGroup.of n).toContinuousMap.IsNConnected (n - 1) := by
  have hι : (StableSpecialOrthogonalGroup.topCocone.ι.app n).hom =
      (StableSpecialOrthogonalGroup.of n).toContinuousMap :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← hι]
  refine TopCat.isNConnected_ι_of_forall_succ StableSpecialOrthogonalGroup.isColimitTopCocone
    (fun m ↦ (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      StableSpecialOrthogonalGroup.isClosedEmbedding_topDiagram_succ
      StableSpecialOrthogonalGroup.isColimitTopCocone m).isEmbedding) n (n - 1) fun k hnk ↦ ?_
  have hconn := (isNConnected_specialOrthogonalBlockSucc k).mono (Nat.sub_le_sub_right hnk 1)
  have hfn : (specialOrthogonalTopDiagram.map (homOfLE k.le_succ)).hom =
      (continuousSpecialOrthogonalBlockSucc k).toContinuousMap :=
    ContinuousMap.ext fun A ↦ specialOrthogonalTopDiagram_map_succ k A
  rwa [hfn]

private theorem bijective_homotopyGroup_toOrthogonalGroup {n : ℕ} (N : Type*) [Nonempty N] :
    Function.Bijective (HomotopyGroup.map (N := N)
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ),
        continuous_toOrthogonalGroup n⟩
      (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) := by
  let S : Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
    {A | (A : Matrix (Fin n) (Fin n) ℝ).det = 1}
  have hS : pathComponent (1 : Matrix.orthogonalGroup (Fin n) ℝ) ⊆ S := fun A hA ↦ by
    have hdet := (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.1 hA).symm
    simpa [S] using hdet
  have h1S : (1 : Matrix.orthogonalGroup (Fin n) ℝ) ∈ S := by simp [S]
  have hsub : Function.Bijective (HomotopyGroup.map (N := N)
      ⟨Subtype.val, continuous_subtypeVal⟩
      (rfl : ((⟨1, h1S⟩ : S) : Matrix.orthogonalGroup (Fin n) ℝ) = 1)) :=
    HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
      (x := (⟨1, h1S⟩ : S)) hS rfl
  let toSubC : C(Matrix.specialOrthogonalGroup (Fin n) ℝ, S) :=
    ⟨specialOrthogonalToSub n, (specialOrthogonalToSub n).continuous⟩
  have hcomp :
      (⟨Subtype.val, continuous_subtypeVal⟩ : C(S, _)).comp toSubC =
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ),
        continuous_toOrthogonalGroup n⟩ :=
    ContinuousMap.ext fun _ ↦ rfl
  have h1 : toSubC 1 = (⟨1, h1S⟩ : S) :=
    Subtype.ext (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)
  have he0 : Function.Bijective (HomotopyGroup.map (N := N) toSubC rfl) :=
    (HomotopyGroup.homeomorphEquiv (N := N) (specialOrthogonalToSub n) 1).bijective
  have he : Function.Bijective (HomotopyGroup.map (N := N) toSubC h1) :=
    (HomotopyGroup.bijective_map_congr (f₁ := toSubC) (f₂ := toSubC) rfl rfl h1).1 he0
  have hbij := hsub.comp he
  rw [HomotopyGroup.map_comp_map_of_comp_eq hcomp
    (rfl : ((⟨1, h1S⟩ : S) : Matrix.orthogonalGroup (Fin n) ℝ) = 1) h1
    (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)] at hbij
  exact hbij

/-- **Step connectivity for `O`**: for `n ≥ 1`, the block inclusion `O(n) → O(n + 1)` is
`(n - 1)`-connected. Equivalently, `O(n + 1) → O(n + 2)` is `n`-connected for every `n`. -/
theorem isNConnected_orthogonalBlockSucc (n : ℕ) :
    (continuousOrthogonalBlockSucc (n + 1)).toContinuousMap.IsNConnected n := by
  let f : C(Matrix.orthogonalGroup (Fin (n + 1)) ℝ, Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    (continuousOrthogonalBlockSucc (n + 1)).toContinuousMap
  have hf1 : f 1 = 1 := map_one (continuousOrthogonalBlockSucc (n + 1))
  let fSO :
      C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
        Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ) :=
    (continuousSpecialOrthogonalBlockSucc (n + 1)).toContinuousMap
  have hfSO1 : fSO 1 = 1 := map_one (continuousSpecialOrthogonalBlockSucc (n + 1))
  let i₁ : C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup, continuous_toOrthogonalGroup (n + 1)⟩
  let i₂ : C(Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ,
      Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup, continuous_toOrthogonalGroup (n + 2)⟩
  have hSO_sq (m : ℕ) :
      HomotopyGroup.map (N := Fin (m + 1)) i₂
          (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) ∘
        HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1 =
      HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
        HomotopyGroup.map (N := Fin (m + 1)) i₁
          (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) := by
    have hcomp : i₂.comp fSO = f.comp i₁ := by
      ext A i j
      exact congrFun (congrFun (congrArg Subtype.val
        (toOrthogonalGroup_specialOrthogonalBlockSucc ℝ (n + 1) A)) i) j
    exact (HomotopyGroup.map_comp_map i₂ _ fSO hfSO1).trans
      (HomotopyGroup.map_comp_map_of_comp_eq hcomp.symm hf1
        (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) _).symm
  let mulX (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
      C(Matrix.orthogonalGroup (Fin (n + 1)) ℝ, Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :=
    ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩
  let mulFx (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
      C(Matrix.orthogonalGroup (Fin (n + 2)) ℝ, Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    ⟨Homeomorph.mulLeft (f x), (Homeomorph.mulLeft (f x)).continuous⟩
  have hmul_sq (m : ℕ) (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (hf1fx : mulFx x 1 = f x) :
      HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx ∘
        HomotopyGroup.map (N := Fin (m + 1)) f hf1 =
      HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
        HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x) := by
    have hcomm : (mulFx x).comp f = f.comp (mulX x) := by
      ext y i j
      change (continuousOrthogonalBlockSucc (n + 1) x *
        continuousOrthogonalBlockSucc (n + 1) y : Matrix _ _ ℝ) i j =
        (continuousOrthogonalBlockSucc (n + 1) (x * y) : Matrix _ _ ℝ) i j
      rw [← map_mul (continuousOrthogonalBlockSucc (n + 1))]
    exact (HomotopyGroup.map_comp_map (mulFx x) hf1fx f hf1).trans
      (HomotopyGroup.map_comp_map_of_comp_eq hcomm.symm rfl (mul_one x) _).symm
  have hex : ∀ y : Matrix.orthogonalGroup (Fin (n + 2)) ℝ, ∃ x, Joined (f x) y := by
    intro y
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup y.property with hy | hy
    · refine ⟨1, TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 ?_⟩
      simp [f, hy]
    · refine ⟨orthogonalDiagonalReflection ℝ 0,
        TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 ?_⟩
      change ((continuousOrthogonalBlockSucc (n + 1)
          (orthogonalDiagonalReflection ℝ 0) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).det =
        (y : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).det
      rw [continuousOrthogonalBlockSucc_apply, coe_orthogonalBlockSucc, Matrix.det_blockSucc,
        det_orthogonalDiagonalReflection, hy]
  refine ⟨hex, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · cases k with
    | zero =>
      refine HomotopyGroup.map_injective_of_isEmpty_of_joined f rfl fun a b hab ↦ ?_
      rw [TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq] at hab ⊢
      simpa [f] using hab
    | succ m =>
      have hinjSO : Function.Injective (HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1) :=
        (HomotopyGroup.injective_map_congr rfl rfl hfSO1).1
          ((isNConnected_specialOrthogonalBlockSucc (n + 1)).injective (m + 1)
            (by omega) 1)
      have bi₁ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 1) (Fin (m + 1))
      have bi₂ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 2) (Fin (m + 1))
      have hinj1 : Function.Injective (HomotopyGroup.map (N := Fin (m + 1)) f hf1) := by
        intro a b hab
        obtain ⟨a', rfl⟩ := bi₁.2 a
        obtain ⟨b', rfl⟩ := bi₁.2 b
        have hcomp :
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) a' =
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) b' := hab
        rw [← hSO_sq m] at hcomp
        exact congrArg (HomotopyGroup.map (N := Fin (m + 1)) i₁ _) (hinjSO (bi₂.1 hcomp))
      have hx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft x) 1).bijective
      have hx : Function.Bijective
          (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulX x) (f₂ := mulX x) rfl rfl (mul_one x)).1
          hx0
      have hf1fx : mulFx x 1 = f x := mul_one (f x)
      have hfx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft (f x)) 1).bijective
      have hfx : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulFx x) (f₂ := mulFx x) rfl rfl hf1fx).1 hfx0
      intro a b hab
      obtain ⟨a', rfl⟩ := hx.2 a
      obtain ⟨b', rfl⟩ := hx.2 b
      have hcomp :
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) a' =
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) b' := hab
      rw [← hmul_sq m x hf1fx] at hcomp
      exact congrArg (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x))
        (hinj1 (hfx.1 hcomp))
  · cases k with
    | zero =>
      exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined f rfl hex
    | succ m =>
      have hsurjSO : Function.Surjective (HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1) :=
        (HomotopyGroup.surjective_map_congr rfl rfl hfSO1).1
          ((isNConnected_specialOrthogonalBlockSucc (n + 1)).surjective (m + 1)
            (by omega) 1)
      have bi₂ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 2) (Fin (m + 1))
      have hsurj1 : Function.Surjective (HomotopyGroup.map (N := Fin (m + 1)) f hf1) := by
        have hcomp : Function.Surjective
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) := by
          rw [← hSO_sq m]
          exact bi₂.2.comp hsurjSO
        exact hcomp.of_comp
      have hf1fx : mulFx x 1 = f x := mul_one (f x)
      have hfx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft (f x)) 1).bijective
      have hfx : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulFx x) (f₂ := mulFx x) rfl rfl hf1fx).1 hfx0
      have hcomp : Function.Surjective
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) := by
        rw [← hmul_sq m x hf1fx]
        exact hfx.2.comp hsurj1
      exact hcomp.of_comp

/-- **Stability connectivity for `O`**: for `n ≥ 1`, the stage inclusion `O(n) → O` is
`(n - 1)`-connected. -/
theorem StableOrthogonalGroup.isNConnected_of (n : ℕ) (hn : 1 ≤ n) :
    (StableOrthogonalGroup.of n).toContinuousMap.IsNConnected (n - 1) := by
  have hι : (StableOrthogonalGroup.topCocone.ι.app n).hom =
      (StableOrthogonalGroup.of n).toContinuousMap :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← hι]
  refine TopCat.isNConnected_ι_of_forall_succ StableOrthogonalGroup.isColimitTopCocone
    (fun m ↦ (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      StableOrthogonalGroup.isClosedEmbedding_topDiagram_succ
      StableOrthogonalGroup.isColimitTopCocone m).isEmbedding) n (n - 1) fun k hnk ↦ ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hconn := (isNConnected_orthogonalBlockSucc m).mono (by omega : n - 1 ≤ m)
  have hfn : (orthogonalTopDiagram.map (homOfLE (m + 1).le_succ)).hom =
      (continuousOrthogonalBlockSucc (m + 1)).toContinuousMap :=
    ContinuousMap.ext fun A ↦ orthogonalTopDiagram_map_succ (m + 1) A
  rwa [hfn]

/-- **Homotopy group stability for `SO`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `SO(n) → SO` induces a group isomorphism
`π_N(SO(n), x) ≃* π_N(SO, of n x)`. -/
@[expose]
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableSpecialOrthogonalGroup (StableSpecialOrthogonalGroup.of n x) :=
  let hc := StableSpecialOrthogonalGroup.isNConnected_of n
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N) (StableSpecialOrthogonalGroup.of n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map (StableSpecialOrthogonalGroup.of n).toContinuousMap rfl a :=
  rfl

/-- **Homotopy group stability for `O`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `O(n) → O` induces a group isomorphism
`π_N(O(n), x) ≃* π_N(O, of n x)`. -/
@[expose]
def StableOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableOrthogonalGroup (StableOrthogonalGroup.of n x) :=
  let hc := StableOrthogonalGroup.isNConnected_of n (by omega)
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N) (StableOrthogonalGroup.of n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

@[simp]
theorem StableOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x) :
    StableOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map (StableOrthogonalGroup.of n).toContinuousMap rfl a :=
  rfl

/-- **Positive-dimensional homotopy groups of `SO` and `O` coincide**: since `SO` embeds onto the
identity path component of `O`, the inclusion `SO → O` induces a group isomorphism
`π_N(SO, x) ≃* π_N(O, toStableOrthogonalGroup x)` for every nonempty cube-index type `N`. -/
@[expose]
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup) :
    HomotopyGroup N StableSpecialOrthogonalGroup x ≃*
      HomotopyGroup N StableOrthogonalGroup
        (StableSpecialOrthogonalGroup.toStableOrthogonalGroup x) :=
  let S := Set.range StableSpecialOrthogonalGroup.toStableOrthogonalGroup
  let e : StableSpecialOrthogonalGroup ≃ₜ S :=
    { toFun a := ⟨StableSpecialOrthogonalGroup.toStableOrthogonalGroup a, a, rfl⟩
      invFun b := Classical.choose b.property
      left_inv a := StableSpecialOrthogonalGroup.toStableOrthogonalGroup_injective
        (Classical.choose_spec (⟨a, rfl⟩ :
          StableSpecialOrthogonalGroup.toStableOrthogonalGroup a ∈ S))
      right_inv b := Subtype.ext (Classical.choose_spec b.property)
      continuous_toFun :=
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.continuous.subtype_mk _
      continuous_invFun := by
        rw [StableSpecialOrthogonalGroup.isClosedEmbedding_toStableOrthogonalGroup
          |>.isEmbedding.continuous_iff]
        refine continuous_subtypeVal.congr fun b ↦ ?_
        exact (Classical.choose_spec b.property).symm }
  let hS : pathComponent (StableSpecialOrthogonalGroup.toStableOrthogonalGroup x) ⊆ S :=
    fun y hy ↦ by
      rw [mem_pathComponent_iff, StableOrthogonalGroup.joined_iff_det_eq,
        StableSpecialOrthogonalGroup.det_toStableOrthogonalGroup] at hy
      dsimp only [S]
      rw [StableSpecialOrthogonalGroup.range_toStableOrthogonalGroup]
      exact hy.symm
  let hbij : Function.Bijective (HomotopyGroup.map (N := N)
      StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl) := by
    have hcomp : (⟨Subtype.val, continuous_subtypeVal⟩ : C(S, StableOrthogonalGroup)).comp
        ⟨e, e.continuous⟩ =
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap :=
      ContinuousMap.ext fun _ ↦ rfl
    have he : Function.Bijective (HomotopyGroup.map (N := N) (x := x)
        (⟨e, e.continuous⟩ : C(StableSpecialOrthogonalGroup, S)) rfl) :=
      (HomotopyGroup.homeomorphMulEquiv (N := N) e x).bijective
    have hsub := HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
      (N := N) (x := e x) hS rfl
    have h := hsub.comp he
    rw [HomotopyGroup.map_comp_map_of_comp_eq hcomp
      (rfl : ((e x : S) : StableOrthogonalGroup) =
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup x)
      (rfl : e x = e x) rfl] at h
    exact h
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N)
      StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl)
    hbij

@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup_apply
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup)
    (a : HomotopyGroup N StableSpecialOrthogonalGroup x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup x a =
      HomotopyGroup.map
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl a :=
  rfl

end Connectivity

end TauCeti
