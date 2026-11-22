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
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Algebra.Matrix.UnitaryGroup

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
and `SO` embeds as the identity path component of `O`. Connectivity and homotopy-group stability
for `O` and `SO` are proved in `TauCeti.Topology.Algebra.StableOrthogonalGroup.Stability`.

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
-/

public section

noncomputable section

open CategoryTheory Limits Topology Set

namespace TauCeti

attribute [local instance] starRingOfComm

section FiniteStages

/-- Entrywise continuity of the upper-left block extension `Matrix.blockSucc (M x)`. -/
@[continuity, fun_prop]
theorem _root_.Continuous.matrix_blockSucc {X k : Type*} {n : ℕ} [TopologicalSpace X]
    [Semiring k] [TopologicalSpace k] {M : X → Matrix (Fin n) (Fin n) k} (hM : Continuous M) :
    Continuous fun x ↦ Matrix.blockSucc (M x) := by
  refine continuous_matrix fun i j ↦ ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simpa using continuous_const
  · simpa using continuous_const
  · simpa using continuous_const
  · simpa using hM.matrix_elem _ _

/-- The block inclusion `O(n) → O(n + 1)` is continuous. -/
theorem continuous_orthogonalBlockSucc (n : ℕ) :
    Continuous (orthogonalBlockSucc ℝ n) :=
  continuous_induced_rng.2 <|
    continuous_subtypeVal.matrix_blockSucc.congr fun A ↦ (coe_orthogonalBlockSucc ℝ n A).symm

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
    Continuous (specialOrthogonalBlockSucc ℝ n) :=
  continuous_induced_rng.2 <|
    continuous_subtypeVal.matrix_blockSucc.congr
      fun A ↦ (coe_specialOrthogonalBlockSucc ℝ n A).symm

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

/-- The canonical inclusion `SO(n) → O(n)` is continuous. -/
theorem continuous_toOrthogonalGroup (n : ℕ) :
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

/-- On successor steps `n ⟶ n + 1`, `orthogonalTopDiagram` acts as `orthogonalBlockSucc ℝ n`. -/
lemma orthogonalTopDiagram_map_succ (n : ℕ) (x : Matrix.orthogonalGroup (Fin n) ℝ) :
    orthogonalTopDiagram.map (homOfLE n.le_succ) x = orthogonalBlockSucc ℝ n x := by
  change (Grp.forget CompactlyGenerated.{0, 0} ⋙
    CompactlyGenerated.compactlyGeneratedToTop).map
      ((Functor.ofSequence orthogonalGrpStep).map (homOfLE (Nat.le_add_right n 1))) x = _
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- On successor steps `n ⟶ n + 1`, `specialOrthogonalTopDiagram` acts as
`specialOrthogonalBlockSucc ℝ n`. -/
lemma specialOrthogonalTopDiagram_map_succ (n : ℕ)
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

/-- `topCocone` is a colimit cocone in `TopCat`. -/
@[expose]
def isColimitTopCocone : IsColimit topCocone :=
  isColimitOfPreserves
    (Grp.forget CompactlyGenerated.{0, 0} ⋙ CompactlyGenerated.compactlyGeneratedToTop)
    (colimit.isColimit orthogonalGrpDiagram)

instance : TopologicalSpace StableOrthogonalGroup :=
  (colimit orthogonalGrpDiagram).X.toTop.str

instance : Group StableOrthogonalGroup :=
  CompactlyGenerated.groupOfGrpObj (colimit orthogonalGrpDiagram).X

instance : UCompactlyGeneratedSpace.{0} StableOrthogonalGroup :=
  (colimit orthogonalGrpDiagram).X.is_compactly_generated

/-- Every successor transition map in `orthogonalTopDiagram` is a closed embedding. -/
lemma isClosedEmbedding_topDiagram_succ (n : ℕ) :
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

/-- `topCocone` is a colimit cocone in `TopCat`. -/
@[expose]
def isColimitTopCocone : IsColimit topCocone :=
  isColimitOfPreserves
    (Grp.forget CompactlyGenerated.{0, 0} ⋙ CompactlyGenerated.compactlyGeneratedToTop)
    (colimit.isColimit specialOrthogonalGrpDiagram)

instance : TopologicalSpace StableSpecialOrthogonalGroup :=
  (colimit specialOrthogonalGrpDiagram).X.toTop.str

instance : Group StableSpecialOrthogonalGroup :=
  CompactlyGenerated.groupOfGrpObj (colimit specialOrthogonalGrpDiagram).X

instance : UCompactlyGeneratedSpace.{0} StableSpecialOrthogonalGroup :=
  (colimit specialOrthogonalGrpDiagram).X.is_compactly_generated

/-- Every successor transition map in `specialOrthogonalTopDiagram` is a closed embedding. -/
lemma isClosedEmbedding_topDiagram_succ (n : ℕ) :
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

end TauCeti
