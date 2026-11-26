/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.Cube.Radius
public import TauCeti.Topology.Homotopy.Extension.Ball

import TauCeti.AlgebraicTopology.Sphere.Puncture
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Convex.Contractible
import TauCeti.Topology.Homotopy.Contractible
import TauCeti.Topology.UnitInterval.OpenSquare

/-!
# Euclidean disks and their boundaries

The closed Euclidean disk is contractible, explicitly by the straight-line contraction
`TauCeti.diskContraction` onto its centre `TauCeti.diskCenter`, and its boundary is
path-connected when the disk has
dimension at least two, so `TopCat.sphere (n + 1)` is path-connected
(`TauCeti.TopCat.pathConnectedSpace_sphere`).  The disk is a `T₃` space, in particular Hausdorff,
so the inclusion of its boundary sphere is a closed embedding
(`TauCeti.TopCat.isClosedEmbedding_diskBoundaryInclusion`), and every sphere `TopCat.sphere n` is
Hausdorff and compact (`TauCeti.TopCat.t2Space_sphere`, `TauCeti.TopCat.compactSpace_sphere`).
This module also constructs the standard `TopPair` consisting of a disk and its boundary, providing
the topological input for relative-homology calculations. A map out of the boundary sphere is
null-homotopic exactly when it extends over the disk
(`TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq`), which is how maps are
extended over attached cells.

Mathlib's `TopCat.diskBoundary n` is the universe lift of the unit sphere of
`EuclideanSpace ℝ (Fin n)`.  It is homeomorphic to the unit sphere of the Euclidean space
`EuclideanSpace ℝ (ULift (Fin n))` of the same dimension in the lifted universe
(`TauCeti.diskBoundaryHomeomorph`), and more generally the unit sphere of any real normed space of
dimension `n + 1` is homeomorphic to `TopCat.sphere n` (`TauCeti.sphereHomeomorphTopCatSphere`,
transporting homotopy equivalences via `ContinuousMap.HomotopyEquiv.topCatSphere`), which lets
results about unit spheres of inner product spaces in that universe be applied to it.  In
particular the boundary of the `n`-disk is empty exactly
when `n = 0` (`TauCeti.nonempty_diskBoundary_iff`), removing a single point leaves a contractible
subspace (`TauCeti.contractibleSpace_diskBoundary_compl_singleton`), and a point of the boundary
`S⁰` of the `1`-disk, like a point of the `1`-disk itself, is determined by its coordinate
(`TauCeti.diskBoundary_one_ext`, `TauCeti.disk_one_ext`), so `S⁰`
(`TopCat.sphere 0`) is a finite discrete two-point space (`TauCeti.TopCat.finite_sphere_zero`,
`TauCeti.TopCat.discreteTopology_sphere_zero`) consisting of the poles `e₀` and `-e₀`
(`TauCeti.spherePlus`, `TauCeti.sphereMinus`, `TauCeti.eq_sphereMinus_or_eq_spherePlus` on
`TopCat.diskBoundary 1`, and `TauCeti.sphereZeroPlus`, `TauCeti.sphereZeroMinus`,
`TauCeti.eq_sphereZeroMinus_or_eq_sphereZeroPlus` typed on `TopCat.sphere 0`), joined in the
`1`-disk by the straight path `TauCeti.diskSegment`.  The antipodal map of
the boundary sphere is `TauCeti.diskBoundaryNeg`.  More generally, a linear isometry `e` of
`EuclideanSpace ℝ (Fin n)` induces homeomorphisms of the disk and of its boundary sphere,
compatible with the boundary
inclusion (`LinearIsometryEquiv.diskIso`, `LinearIsometryEquiv.diskBoundaryIso`); these are the
orthogonal reparametrizations of attached cells. Likewise a linear isometry of a normed space onto
`EuclideanSpace ℝ (Fin n)` identifies its closed unit ball with the disk
(`LinearIsometryEquiv.closedBallHomeomorphDisk`), which relabels the coordinates of balls in
`EuclideanSpace ℝ ι` for a finite index type `ι` of cardinality `n`.

The disk is also homeomorphic to the closed unit ball of the sup norm on `Fin n → ℝ`, with its
boundary going to the unit sphere (`TauCeti.diskHomeomorphClosedBall`); this is how the disk is
compared with the domains of characteristic maps of CW complexes and with the cube. In dimension one
it is the identity on coordinates (`TauCeti.coe_diskHomeomorphClosedBall_one_apply`). Composing it
with the affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto the same ball
identifies the disk pair with the pair `TauCeti.cubeBoundaryPair n = (Iⁿ, ∂Iⁿ)` formed by the cube
and its boundary (`TauCeti.diskBoundaryPairIsoCube`). A singular cube of a pair sending the boundary
of the cube into the subspace is a map of pairs out of the cube pair
(`TauCeti.cubeBoundaryPairHom`). The product `Y × (Iᵐ, ∂Iᵐ)` of a space with the cube pair is the
pair of `Y × Iᵐ` over the preimage of the boundary of the cube
(`TauCeti.cubeBoundaryPairProdLeftIso`).
-/

public section

noncomputable section
open CategoryTheory
universe u

namespace TauCeti.TopCat

/-- The `n`-dimensional Euclidean disk is contractible. -/
instance contractibleSpace_disk (n : ℕ) :
    ContractibleSpace (TopCat.disk n) := by
  -- `TopCat.disk` stores its metric closed ball inside a `ULift`; the lift of the contractible
  -- closed ball is contractible by `ULift.contractibleSpace`.
  exact inferInstanceAs
    (ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- The boundary of the `n`-dimensional disk is path-connected when `n ≥ 2`. -/
lemma pathConnectedSpace_diskBoundary {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (TopCat.diskBoundary n) := by
  -- The `TopCat` carrier is the lift of the metric sphere.
  change PathConnectedSpace (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (E := EuclideanSpace ℝ (Fin n))
        (by
          rw [← Module.finrank_eq_rank]
          norm_num [finrank_euclideanSpace_fin]
          omega)
        0 (by norm_num))
  exact Homeomorph.ulift.symm.pathConnectedSpace

/-- The sphere `TopCat.sphere (n + 1)` of positive dimension, the boundary of the `(n + 2)`-disk,
is path-connected. -/
instance pathConnectedSpace_sphere (n : ℕ) : PathConnectedSpace (TopCat.sphere.{u} (n + 1)) :=
  pathConnectedSpace_diskBoundary (by omega)

/-- The `n`-dimensional disk is a `T₃` space, in particular Hausdorff, being homeomorphic to a
closed ball in Euclidean space. -/
instance t3Space_disk (n : ℕ) : T3Space (TopCat.disk.{u} n) :=
  -- The `TopCat` carrier of `TopCat.disk n` is, by definition, the lift of the metric closed
  -- ball; instance synthesis does not unfold the `TopCat.disk` wrapper on its own.
  inferInstanceAs (T3Space (ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- The `n`-dimensional disk is compact, being homeomorphic to a closed ball in Euclidean space. -/
instance compactSpace_disk (n : ℕ) : CompactSpace (TopCat.disk.{u} n) :=
  -- As for `TauCeti.TopCat.t3Space_disk`, the carrier is the lift of the metric closed ball.
  inferInstanceAs (CompactSpace (ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary sphere of the disk is a closed embedding, being an
injective map from a compact space to a Hausdorff one. -/
theorem isClosedEmbedding_diskBoundaryInclusion (n : ℕ) :
    Topology.IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n) :=
  (TopCat.diskBoundaryInclusion n).hom.continuous.isClosedEmbedding
    ((TopCat.mono_iff_injective _).1 inferInstance)

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary sphere of the disk keeps the underlying vector of
`EuclideanSpace ℝ (Fin n)`. -/
lemma coe_diskBoundaryInclusion_apply_down (n : ℕ) (s : TopCat.diskBoundary.{u} n) :
    ((TopCat.diskBoundaryInclusion n s :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) =
      ((s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) :=
  rfl

/-- A point of the boundary sphere has norm `1` in the disk. -/
@[simp]
theorem norm_diskBoundaryInclusion {n : ℕ} (s : TopCat.diskBoundary.{u} n) :
    ‖(TopCat.diskBoundaryInclusion n s).down.val‖ = 1 :=
  mem_sphere_zero_iff_norm.1 s.down.property

end TauCeti.TopCat

namespace TopCat.Hom

/-- **A map out of the boundary sphere of a disk is null-homotopic exactly when it extends over
the disk.** -/
theorem nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq {Y : TopCat.{u}} {n : ℕ}
    (φ : TopCat.diskBoundary.{u} n ⟶ Y) :
    φ.hom.Nullhomotopic ↔ ∃ F : TopCat.disk.{u} n ⟶ Y, TopCat.diskBoundaryInclusion n ≫ F = φ := by
  constructor
  · intro hφ
    obtain ⟨G, hG⟩ := (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall
      (φ.hom.comp ⟨ULift.up, continuous_uliftUp⟩)).1 (hφ.comp_left _)
    exact ⟨TopCat.ofHom (G.comp ⟨ULift.down, continuous_uliftDown⟩), by ext s; exact hG s.down⟩
  · rintro ⟨F, rfl⟩
    exact ((id_nullhomotopic (TopCat.disk n)).comp_right F.hom).comp_left
      (TopCat.diskBoundaryInclusion n).hom

end TopCat.Hom

namespace TauCeti

/-- The standard pair consisting of the `n`-dimensional disk and its boundary, used to express
relative singular homology of the disk with respect to its boundary. -/
abbrev diskBoundaryPair (n : ℕ) : TopPair.{u} :=
  TopPair.of (TopCat.diskBoundaryInclusion n)
    (TopCat.isClosedEmbedding_diskBoundaryInclusion n).isEmbedding

@[simp]
lemma diskBoundaryPair_fst (n : ℕ) :
    (diskBoundaryPair n).fst = TopCat.disk n := rfl

@[simp]
lemma diskBoundaryPair_snd (n : ℕ) :
    (diskBoundaryPair n).snd = TopCat.diskBoundary n := rfl

/-- The underlying map of `diskBoundaryPair n` is the standard boundary inclusion. -/
-- This equation is definitional for the reducible abbreviation; an `@[simp]` attribute would be
-- rejected by `simpNF` as a duplicate rule.
lemma diskBoundaryPair_map (n : ℕ) :
    (diskBoundaryPair n).map = TopCat.diskBoundaryInclusion n := (rfl)

/-- The ambient space of the pair consisting of a disk and its boundary is contractible.  This
lets instances about pairs with contractible ambient space apply to `diskBoundaryPair n`. -/
instance contractibleSpace_diskBoundaryPair_fst (n : ℕ) :
    ContractibleSpace (diskBoundaryPair.{u} n).fst :=
  TopCat.contractibleSpace_disk n

/-- Mathlib's boundary `TopCat.diskBoundary n` of the `n`-disk, the universe lift of the unit
sphere of `EuclideanSpace ℝ (Fin n)`, is homeomorphic to the unit sphere of the Euclidean space
`EuclideanSpace ℝ (ULift (Fin n))` of the same dimension in the lifted universe. -/
def diskBoundaryHomeomorph (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1 :=
  Homeomorph.ulift.trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.ulift.{u}.symm : Fin n ≃ ULift.{u} (Fin n)))
      |>.toHomeomorph.subtype fun x ↦ by simp

/-- The point of the unit sphere of `EuclideanSpace ℝ (ULift (Fin n))` corresponding to a point of
the boundary sphere under `TauCeti.diskBoundaryHomeomorph` has the same coordinates, reindexed. -/
lemma coe_diskBoundaryHomeomorph_apply {n : ℕ} (x : TopCat.diskBoundary.{u} n) :
    (diskBoundaryHomeomorph n x : EuclideanSpace ℝ (ULift.{u} (Fin n))) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.ulift.{u}.symm : Fin n ≃ ULift.{u} (Fin n))
        x.down :=
  (rfl)

/-- The coordinates of the point of the boundary sphere corresponding to a point of the unit sphere
of `EuclideanSpace ℝ (ULift (Fin n))` under `TauCeti.diskBoundaryHomeomorph`. -/
lemma diskBoundaryHomeomorph_symm_apply_down_apply {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1) (i : Fin n) :
    ((((diskBoundaryHomeomorph n).symm v : TopCat.diskBoundary.{u} n) :
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) i = (v : EuclideanSpace ℝ (ULift.{u} (Fin n))) (ULift.up i) := by
  rw [diskBoundaryHomeomorph]
  rfl

/-- The antipodal map `x ↦ -x` of the boundary sphere `TopCat.diskBoundary n` of the `n`-disk. -/
def diskBoundaryNeg (n : ℕ) : TopCat.diskBoundary.{u} n ⟶ TopCat.diskBoundary.{u} n :=
  TopCat.ofHom ⟨fun x ↦ ULift.up (-x.down), by fun_prop⟩

@[simp]
lemma diskBoundaryNeg_apply_down {n : ℕ} (x : TopCat.diskBoundary.{u} n) :
    (diskBoundaryNeg n x).down = -x.down :=
  (rfl)

/-- The antipodal map of the boundary sphere of a disk is an involution. -/
@[simp]
lemma diskBoundaryNeg_diskBoundaryNeg_apply {n : ℕ} (x : TopCat.diskBoundary.{u} n) :
    diskBoundaryNeg n (diskBoundaryNeg n x) = x :=
  ULift.ext (neg_neg x.down)

/-- The homeomorphism from the Euclidean closed unit disk `TopCat.disk n` onto the closed unit ball
of the sup norm on `Fin n → ℝ`: the radial rescaling `ContinuousLinearEquiv.unitBallHomeomorph` of
the coordinate identification `EuclideanSpace.equiv` (`TauCeti.coe_diskHomeomorphClosedBall_apply`).
It carries the boundary sphere onto the unit sphere of the sup norm
(`TauCeti.norm_diskHomeomorphClosedBall_eq_one_iff`). -/
def diskHomeomorphClosedBall (n : ℕ) : TopCat.disk.{u} n ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
  Homeomorph.ulift.trans <| ((EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph.image _).trans
    (Homeomorph.setCongr (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_closedBall)

@[simp]
lemma coe_diskHomeomorphClosedBall_apply {n : ℕ} (z : TopCat.disk.{u} n) :
    (diskHomeomorphClosedBall n z : Fin n → ℝ) =
      (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
        ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
          EuclideanSpace ℝ (Fin n)) :=
  (rfl)

/-- A point of the Euclidean disk `TopCat.disk n` lies on its boundary sphere exactly when it has
norm one. -/
lemma mem_range_diskBoundaryInclusion_iff {n : ℕ} (z : TopCat.disk.{u} n) :
    z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) ↔
      ‖((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n))‖ = 1 := by
  refine ⟨?_, fun h ↦ ⟨ULift.up ⟨_, mem_sphere_zero_iff_norm.2 h⟩, rfl⟩⟩
  rintro ⟨s, rfl⟩
  -- The boundary inclusion keeps the underlying point of the sphere.
  exact mem_sphere_zero_iff_norm.1
    (s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down.property

/-- The centre `0` of the Euclidean disk `TopCat.disk n`. -/
def diskCenter (n : ℕ) : TopCat.disk.{u} n :=
  (ULift.up ⟨0, Metric.mem_closedBall_self zero_le_one⟩ :
    ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))

@[simp]
lemma coe_diskCenter_down (n : ℕ) :
    (((diskCenter.{u} n : TopCat.disk.{u} n) :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) = 0 :=
  (rfl)

/-- The centre of the disk does not lie on its boundary sphere. -/
lemma diskCenter_notMem_range_diskBoundaryInclusion (n : ℕ) :
    diskCenter.{u} n ∉ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [mem_range_diskBoundaryInclusion_iff, coe_diskCenter_down]
  simp

/-- The straight-line contraction of the disk `TopCat.disk n` onto its centre: at time `t` it
sends `x` to `(1 - t) • x`. -/
def diskContraction (n : ℕ) :
    (ContinuousMap.id (TopCat.disk.{u} n)).Homotopy
      (ContinuousMap.const (TopCat.disk.{u} n) (diskCenter n)) where
  toFun p := (ULift.up ⟨(unitInterval.symm p.1 : ℝ) •
      ((p.2 : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)),
      (convex_closedBall _ _).smul_mem_of_zero_mem (Metric.mem_closedBall_self zero_le_one)
        (p.2 : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down.property
        (unitInterval.symm p.1).property⟩ :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  continuous_toFun := continuous_uliftUp.comp <| Continuous.subtype_mk
    ((continuous_subtypeVal.comp (unitInterval.continuous_symm.comp continuous_fst)).smul
      (continuous_subtypeVal.comp (continuous_uliftDown.comp continuous_snd))) _
  map_zero_left _ := ULift.ext (Subtype.ext (by simp))
  map_one_left _ := ULift.ext (Subtype.ext (by simp))

/-- The straight-line contraction sends `x` at time `t` to `(1 - t) • x`. -/
@[simp]
lemma coe_diskContraction_apply_down (n : ℕ) (t : unitInterval) (x : TopCat.disk.{u} n) :
    (((diskContraction n (t, x) : TopCat.disk.{u} n) :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) =
      (1 - (t : ℝ)) • ((x : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) :=
  (rfl)

/-- A point of the disk is sent to the unit sphere of the sup norm by
`TauCeti.diskHomeomorphClosedBall` exactly when it lies on the boundary sphere. -/
lemma norm_diskHomeomorphClosedBall_eq_one_iff {n : ℕ} (z : TopCat.disk.{u} n) :
    ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ = 1 ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [coe_diskHomeomorphClosedBall_apply, ← mem_sphere_zero_iff_norm,
    mem_range_diskBoundaryInclusion_iff, ← mem_sphere_zero_iff_norm]
  conv_lhs => rw [← (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_sphere]
  exact (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph.injective.mem_set_image

/-- The radial comparison sends exactly the points outside the boundary sphere to the open
max-norm unit ball. -/
lemma diskHomeomorphClosedBall_mem_ball_iff {n : ℕ} (z : TopCat.disk.{u} n) :
    (diskHomeomorphClosedBall n z : Fin n → ℝ) ∈ Metric.ball 0 1 ↔
      z ∈ (Set.range (TopCat.diskBoundaryInclusion n))ᶜ := by
  rw [mem_ball_zero_iff, Set.mem_compl_iff,
    ← norm_diskHomeomorphClosedBall_eq_one_iff]
  exact (lt_iff_le_and_ne).trans
    (and_iff_right (mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n z).property))

/-- The dimension of the Euclidean space `EuclideanSpace ℝ (ULift (Fin n))`. -/
lemma finrank_euclideanSpace_ulift_fin (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin n))) = n := by
  rw [finrank_euclideanSpace, Fintype.card_ulift, Fintype.card_fin]

/-- A disk boundary is Hausdorff, as a lifted subspace of Euclidean space. -/
instance t2Space_diskBoundary (n : ℕ) : T2Space (TopCat.diskBoundary.{u} n) :=
  -- Expose the carrier once here, so consumers need not unfold the `TopCat` wrapper.
  inferInstanceAs (T2Space (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- A disk boundary is compact, as a lifted sphere in Euclidean space. -/
instance compactSpace_diskBoundary (n : ℕ) : CompactSpace (TopCat.diskBoundary.{u} n) :=
  -- Expose the carrier once here, so consumers need not unfold the `TopCat` wrapper.
  inferInstanceAs (CompactSpace (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- The `n`-sphere is Hausdorff, being the boundary of the `(n + 1)`-disk. -/
instance t2Space_sphere (n : ℕ) : T2Space (TopCat.sphere.{u} n) :=
  inferInstanceAs (T2Space (TopCat.diskBoundary.{u} (n + 1)))

/-- The `n`-sphere is compact, being the boundary of the `(n + 1)`-disk. -/
instance compactSpace_sphere (n : ℕ) : CompactSpace (TopCat.sphere.{u} n) :=
  inferInstanceAs (CompactSpace (TopCat.diskBoundary.{u} (n + 1)))

/-- **A punctured boundary sphere is contractible**: removing a single point from
`TopCat.diskBoundary n` leaves a contractible subspace, in every universe and every dimension. -/
theorem contractibleSpace_diskBoundary_compl_singleton {n : ℕ}
    (s : TopCat.diskBoundary.{u} n) :
    ContractibleSpace ({s}ᶜ : Set (TopCat.diskBoundary.{u} n)) :=
  let e : (TopCat.diskBoundary.{u} n : Type u) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  (e.subtype (q := (· ∈ ({e s}ᶜ : Set _))) fun _ ↦
    e.injective.ne_iff.symm).contractibleSpace_iff.mpr
    (contractibleSpace_sphere_compl_singleton (e s))

/-- The boundary of the `0`-disk is empty. -/
instance isEmpty_diskBoundary_zero : IsEmpty (TopCat.diskBoundary.{u} 0) :=
  have : Subsingleton (EuclideanSpace ℝ (ULift.{u} (Fin 0))) :=
    Module.finrank_zero_iff.mp (finrank_euclideanSpace_ulift_fin 0)
  have : IsEmpty (Metric.sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin 0))) 1) :=
    Set.isEmpty_coe_sort.mpr (Metric.sphere_eq_empty_of_subsingleton one_ne_zero)
  (diskBoundaryHomeomorph 0).toEquiv.isEmpty

/-- The `0`-disk is a single point, the origin of the zero space. -/
instance uniqueDiskZero : Unique (TopCat.disk.{u} 0) where
  default := diskCenter 0
  uniq _ := ULift.ext (Subtype.ext (Subsingleton.elim _ _))

/-- A point of the boundary `S⁰` of the `1`-disk is determined by its coordinate. -/
lemma diskBoundary_one_ext {p q : TopCat.diskBoundary.{u} 1}
    (h : ((p : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 =
      ((q : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0) : p = q := by
  refine ULift.ext (Subtype.ext (PiLp.ext fun i ↦ ?_))
  rwa [Subsingleton.elim i 0]

/-- A point of the `1`-disk is determined by its coordinate. -/
lemma disk_one_ext {x y : TopCat.disk.{u} 1}
    (h : ((x : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 =
      ((y : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0) : x = y := by
  refine ULift.ext (Subtype.ext (PiLp.ext fun i ↦ ?_))
  rwa [Subsingleton.elim i 0]

/-- The coordinate of a point of the boundary `S⁰` of the `1`-disk is `±1`: its square is `1`. -/
lemma sq_diskBoundary_one_eq_one (s : TopCat.diskBoundary.{u} 1) :
    ((s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0 ^ 2 = 1 := by
  rw [← sq_abs, ← EuclideanSpace.norm_fin_one, mem_sphere_zero_iff_norm.1 s.down.property, one_pow]

/-- The boundary sphere of a disk of positive dimension is nonempty. -/
instance nonempty_diskBoundary_succ (n : ℕ) : Nonempty (TopCat.diskBoundary.{u} (n + 1)) :=
  ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The boundary sphere of the `n`-disk is nonempty exactly when `n ≠ 0`. -/
@[simp]
theorem nonempty_diskBoundary_iff {n : ℕ} : Nonempty (TopCat.diskBoundary.{u} n) ↔ n ≠ 0 := by
  cases n
  · simpa using not_nonempty_iff.2 isEmpty_diskBoundary_zero
  · simpa using nonempty_diskBoundary_succ _

/-- The `n`-sphere is nonempty. -/
instance nonempty_topCatSphere (n : ℕ) : Nonempty (TopCat.sphere.{u} n) :=
  nonempty_diskBoundary_succ n

/-- The positive first-coordinate pole `e₀ = (1, 0, …, 0)` of `TopCat.sphere n`. -/
def sphereBasepoint (n : ℕ) : TopCat.sphere.{u} n :=
  (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩ :
    ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- The underlying vector of `TauCeti.sphereBasepoint n` is the first standard basis vector. -/
@[simp]
lemma coe_sphereBasepoint_down (n : ℕ) :
    (((sphereBasepoint.{u} n : TopCat.sphere.{u} n) :
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) = EuclideanSpace.single 0 1 :=
  (rfl)

/-- The standard orthonormal basis of `EuclideanSpace ℝ (ULift (Fin 1))`. -/
abbrev sphereZeroBasis : OrthonormalBasis (Fin 1) ℝ (EuclideanSpace ℝ (ULift.{u} (Fin 1))) :=
  (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℝ).reindex Equiv.ulift

/-- The positive pole `e₀` (`1`) of `TopCat.sphere 0` (`= TopCat.diskBoundary 1`). -/
def spherePlus : TopCat.diskBoundary.{u} 1 :=
  (diskBoundaryHomeomorph 1).symm ⟨sphereZeroBasis 0, by simp⟩

/-- The negative pole `-e₀` (`-1`) of `TopCat.sphere 0` (`= TopCat.diskBoundary 1`). -/
def sphereMinus : TopCat.diskBoundary.{u} 1 :=
  (diskBoundaryHomeomorph 1).symm (-⟨sphereZeroBasis 0, by simp⟩)

/-- `TauCeti.spherePlus` is the image of `sphereZeroBasis 0` under `(diskBoundaryHomeomorph 1)⁻¹`.
-/
lemma spherePlus_def :
    spherePlus.{u} = (diskBoundaryHomeomorph 1).symm ⟨sphereZeroBasis 0, by simp⟩ := (rfl)

/-- `TauCeti.sphereMinus` is the image of `-sphereZeroBasis 0` under `(diskBoundaryHomeomorph 1)⁻¹`.
-/
lemma sphereMinus_def :
    sphereMinus.{u} = (diskBoundaryHomeomorph 1).symm (-⟨sphereZeroBasis 0, by simp⟩) := (rfl)

/-- The coordinate of `TauCeti.spherePlus` in `EuclideanSpace ℝ (Fin 1)` is `1`. -/
@[simp]
lemma spherePlus_down_apply_zero :
    (((spherePlus.{u} : TopCat.diskBoundary.{u} 1) :
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  simp [spherePlus, diskBoundaryHomeomorph_symm_apply_down_apply]

/-- The coordinate of `TauCeti.sphereMinus` in `EuclideanSpace ℝ (Fin 1)` is `-1`. -/
@[simp]
lemma sphereMinus_down_apply_zero :
    (((sphereMinus.{u} : TopCat.diskBoundary.{u} 1) :
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  simp [sphereMinus, diskBoundaryHomeomorph_symm_apply_down_apply]

/-- Under `TopCat.diskBoundaryInclusion 1`, `TauCeti.spherePlus` has coordinate `1`. -/
@[simp]
lemma spherePlus_coord :
    (((TopCat.diskBoundaryInclusion.{u} 1 spherePlus) :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  rw [TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down, spherePlus_down_apply_zero]

/-- Under `TopCat.diskBoundaryInclusion 1`, `TauCeti.sphereMinus` has coordinate `-1`. -/
@[simp]
lemma sphereMinus_coord :
    (((TopCat.diskBoundaryInclusion.{u} 1 sphereMinus) :
      ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  rw [TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down, sphereMinus_down_apply_zero]

/-- The straight path in the `1`-disk from the pole `-e₀` to the pole `e₀`, with coordinate
`2 * t - 1` at time `t` (`TauCeti.diskSegment_coord`). -/
def diskSegment : Path ((diskBoundaryPair.{u} 1).map sphereMinus)
    ((diskBoundaryPair.{u} 1).map spherePlus) where
  toFun t := ULift.up ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm fun _ ↦ 2 * (t : ℝ) - 1, by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_fin_one]
    exact unitInterval.abs_two_mul_sub_one_le_one t⟩
  continuous_toFun := by fun_prop
  source' := disk_one_ext ((show (2 * ((0 : unitInterval) : ℝ) - 1) = -1 by norm_num).trans
    sphereMinus_coord.{u}.symm)
  target' := disk_one_ext ((show (2 * ((1 : unitInterval) : ℝ) - 1) = 1 by norm_num).trans
    spherePlus_coord.{u}.symm)

/-- At time `t`, the straight path `TauCeti.diskSegment` has coordinate `2 * t - 1`. -/
lemma diskSegment_coord (t : unitInterval) :
    ((diskSegment.{u} t : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 = 2 * (t : ℝ) - 1 :=
  (rfl)

/-- **`S⁰` consists of the two points `-e₀` and `e₀`.** -/
lemma eq_sphereMinus_or_eq_spherePlus (p : TopCat.diskBoundary.{u} 1) :
    p = sphereMinus ∨ p = spherePlus := by
  rcases sq_eq_one_iff.1 (sq_diskBoundary_one_eq_one p) with h | h
  · exact Or.inr (diskBoundary_one_ext (h.trans spherePlus_down_apply_zero.{u}.symm))
  · exact Or.inl (diskBoundary_one_ext (h.trans sphereMinus_down_apply_zero.{u}.symm))

/-- The two points `-e₀` and `e₀` of `S⁰` are distinct. -/
lemma sphereMinus_ne_spherePlus : (sphereMinus : TopCat.diskBoundary.{u} 1) ≠ spherePlus := by
  intro h
  have h' := congrArg (fun p : TopCat.diskBoundary.{u} 1 ↦
    ((p : ULift.{u} _).down : EuclideanSpace ℝ (Fin 1)) 0) h
  norm_num [sphereMinus_down_apply_zero, spherePlus_down_apply_zero] at h'

/-- The positive pole `e₀` (`1`) of `TopCat.sphere 0`, defined from `TauCeti.spherePlus` with
syntactic type `TopCat.sphere 0`. -/
def sphereZeroPlus : TopCat.sphere.{u} 0 := spherePlus

/-- The negative pole `-e₀` (`-1`) of `TopCat.sphere 0`, defined from `TauCeti.sphereMinus` with
syntactic type `TopCat.sphere 0`. -/
def sphereZeroMinus : TopCat.sphere.{u} 0 := sphereMinus

/-- **`TopCat.sphere 0` consists of the two poles `-e₀` and `e₀`.** -/
lemma eq_sphereZeroMinus_or_eq_sphereZeroPlus (p : TopCat.sphere.{u} 0) :
    p = sphereZeroMinus ∨ p = sphereZeroPlus :=
  eq_sphereMinus_or_eq_spherePlus p

/-- The two poles `-e₀` and `e₀` of `TopCat.sphere 0` are distinct. -/
lemma sphereZeroMinus_ne_sphereZeroPlus :
    (sphereZeroMinus : TopCat.sphere.{u} 0) ≠ sphereZeroPlus :=
  sphereMinus_ne_spherePlus

/-- The boundary `S⁰` of the `1`-disk is finite. -/
instance TopCat.finite_diskBoundary_one : Finite (TopCat.diskBoundary.{u} 1) :=
  Finite.of_surjective (fun b : Bool ↦ cond b spherePlus sphereMinus) fun p ↦
    (eq_sphereMinus_or_eq_spherePlus p).elim (fun hp ↦ ⟨false, hp.symm⟩) fun hp ↦ ⟨true, hp.symm⟩

/-- The zero-sphere `TopCat.sphere 0` is finite. -/
instance TopCat.finite_sphere_zero : Finite (TopCat.sphere.{u} 0) :=
  TopCat.finite_diskBoundary_one

/-- The boundary `S⁰` of the `1`-disk has the discrete topology. -/
instance TopCat.discreteTopology_diskBoundary_one :
    DiscreteTopology (TopCat.diskBoundary.{u} 1) :=
  inferInstance

/-- The zero-sphere `TopCat.sphere 0` has the discrete topology. -/
instance TopCat.discreteTopology_sphere_zero : DiscreteTopology (TopCat.sphere.{u} 0) :=
  TopCat.discreteTopology_diskBoundary_one

/-- The subspace of the pair consisting of the `0`-disk and its boundary is empty.  This lets
instances about pairs with empty subspace apply to `diskBoundaryPair 0`. -/
instance isEmpty_diskBoundaryPair_zero_snd : IsEmpty (diskBoundaryPair.{u} 0).snd :=
  inferInstanceAs (IsEmpty (TopCat.diskBoundary.{u} 0))

section CubePair

open scoped unitInterval Topology

variable (n : ℕ)

/-- The cube `Iⁿ` and its boundary `∂Iⁿ` as a topological pair, lifted to the universe `w`. -/
abbrev cubeBoundaryPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin n))))
    (ULift.down ⁻¹' Cube.boundary (Fin n))

/-- The isomorphism of pairs `(Iᵐ × Iⁿ, ∂Iᵐ × Iⁿ ∪ Iᵐ × ∂Iⁿ) ≅ (Iᵐ⁺ⁿ, ∂Iᵐ⁺ⁿ)` induced by
`Fin.appendHomeomorph`. -/
def cubeBoundaryPairProdIso (m n : ℕ) :
    TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
      ((ULift.down ⁻¹' Cube.boundary (Fin m)) ×ˢ Set.univ ∪
        Set.univ ×ˢ (ULift.down ⁻¹' Cube.boundary (Fin n))) ≅
      cubeBoundaryPair.{u} (m + n) :=
  TopPair.ofSubsetIso
    (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
    (Y := TopCat.of (ULift.{u} (I^(Fin (m + n)))))
    ((Homeomorph.ulift.prodCongr Homeomorph.ulift).trans
      ((Fin.appendHomeomorph (X := I) m n).trans Homeomorph.ulift.symm))
    fun ⟨_, _⟩ ↦
      ⟨fun h ↦ Cube.append_mem_boundary_iff.2 (h.imp And.left And.right),
       fun h ↦ (Cube.append_mem_boundary_iff.1 h).imp (⟨·, trivial⟩) (⟨trivial, ·⟩)⟩

@[simp]
lemma cubeBoundaryPairProdIso_hom_fst_apply (m n : ℕ)
    (p : ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))) :
    TopPair.Hom.fst (cubeBoundaryPairProdIso.{u} m n).hom p =
      ULift.up (Fin.append p.1.down p.2.down) := by
  rw [cubeBoundaryPairProdIso]
  apply TopPair.ofSubsetIso_hom_fst_apply

/-- A singular `m`-cube of the ambient space of a pair `P` sending the boundary of the cube into
the subspace, as a map of pairs `(Iᵐ, ∂Iᵐ) ⟶ P`. -/
def cubeBoundaryPairHom {P : TopPair.{u}} {m : ℕ} (c : C(I^(Fin m), P.fst))
    (hc : Set.MapsTo c (Cube.boundary (Fin m)) (Set.range P.map)) :
    cubeBoundaryPair.{u} m ⟶ P :=
  TopPair.ofHom (TopCat.ofHom (c.comp ⟨ULift.down, continuous_uliftDown⟩))
    (TopCat.ofHom (P.liftSnd ((c.comp ⟨ULift.down, continuous_uliftDown⟩).comp
      ⟨Subtype.val, continuous_subtypeVal⟩) fun z ↦ hc z.property))
    (by ext z; exact TopPair.map_liftSnd _ _ z)

@[simp]
lemma cubeBoundaryPairHom_fst_apply {P : TopPair.{u}} {m : ℕ} (c : C(I^(Fin m), P.fst))
    (hc : Set.MapsTo c (Cube.boundary (Fin m)) (Set.range P.map))
    (z : (cubeBoundaryPair.{u} m).fst) :
    TopPair.Hom.fst (cubeBoundaryPairHom c hc) z = c z.down :=
  (rfl)

/-- The ambient map of `TauCeti.cubeBoundaryPairHom c hc` is `c` precomposed with `ULift.down`. -/
lemma cubeBoundaryPairHom_fst_hom {P : TopPair.{u}} {m : ℕ} (c : C(I^(Fin m), P.fst))
    (hc : Set.MapsTo c (Cube.boundary (Fin m)) (Set.range P.map)) :
    (TopPair.Hom.fst (cubeBoundaryPairHom c hc)).hom = c.comp ⟨ULift.down, continuous_uliftDown⟩ :=
  (rfl)

/-- The pair `Y × (Iᵐ, ∂Iᵐ)`, whose cube is lifted to the universe of `Y`, is the pair of
`Y × Iᵐ` over the boundary of the cube, the preimage of `∂Iᵐ` under the projection
`Y × Iᵐ → Iᵐ`. This identifies the relative homology of `Y × (Iᵐ, ∂Iᵐ)` with the relative
homology of a space over the cube restricted to the boundary. -/
def cubeBoundaryPairProdLeftIso (Y : TopCat.{u}) (m : ℕ) :
    (cubeBoundaryPair.{u} m).prodLeft Y ≅
      TopPair.ofSubset (X := TopCat.of (Y × (Fin m → I)))
        (ContinuousMap.snd ⁻¹' Cube.boundary (Fin m)) where
  hom := TopPair.ofHom
    (TopCat.ofHom ((ContinuousMap.id _).prodMap ⟨ULift.down, continuous_uliftDown⟩))
    (TopCat.ofHom ⟨fun x ↦ ⟨(x.1, x.2.val.down), x.2.property⟩, by fun_prop⟩) rfl
  inv := TopPair.ofHom
    (TopCat.ofHom ((ContinuousMap.id _).prodMap ⟨ULift.up, continuous_uliftUp⟩))
    (TopCat.ofHom ⟨fun x ↦ (x.val.1, ⟨ULift.up x.val.2, x.property⟩), by fun_prop⟩) rfl
  hom_inv_id := by ext : 2 <;> rfl
  inv_hom_id := by ext : 2 <;> rfl

/-- `TauCeti.cubeBoundaryPairProdLeftIso` lowers the cube coordinate out of `ULift`. -/
@[simp]
theorem cubeBoundaryPairProdLeftIso_hom_fst_apply (Y : TopCat.{u}) (m : ℕ)
    (z : Y × ULift.{u} (Fin m → I)) :
    TopPair.Hom.fst (cubeBoundaryPairProdLeftIso Y m).hom z = (z.1, z.2.down) :=
  (rfl)

/-- The inverse of `TauCeti.cubeBoundaryPairProdLeftIso` lifts the cube coordinate to `ULift`. -/
@[simp]
theorem cubeBoundaryPairProdLeftIso_inv_fst_apply (Y : TopCat.{u}) (m : ℕ)
    (z : Y × (Fin m → I)) :
    TopPair.Hom.fst (cubeBoundaryPairProdLeftIso Y m).inv z = (z.1, ULift.up z.2) :=
  (rfl)

/-- The homeomorphism from the Euclidean disk `Dⁿ` onto the cube `Iⁿ`: the radial rescaling of the
disk onto the closed unit ball of the sup norm on `Fin n → ℝ`, followed by the inverse of the affine
homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto that ball. -/
def diskHomeomorphCube : TopCat.disk.{u} n ≃ₜ (I^(Fin n)) :=
  (diskHomeomorphClosedBall n).trans (cubeHomeomorphClosedBall (Fin n)).symm

variable {n} in
/-- `TauCeti.diskHomeomorphCube` is the radial rescaling of the disk onto the closed unit ball of
the sup norm, followed by the inverse of the affine homeomorphism of the cube onto that ball. -/
lemma diskHomeomorphCube_apply (z : TopCat.disk.{u} n) :
    diskHomeomorphCube n z =
      (cubeHomeomorphClosedBall (Fin n)).symm (diskHomeomorphClosedBall n z) := by
  rw [diskHomeomorphCube, Homeomorph.trans_apply]

variable {n} in
/-- `TauCeti.diskHomeomorphCube` depends only on the underlying point of the closed Euclidean ball,
so inverting it in another universe recovers that point; in particular this compares
`TauCeti.diskHomeomorphCube.{u}` with `TauCeti.diskHomeomorphCube.{0}`, where
`TauCeti.cubeToSphere` is fixed at universe `0`. -/
lemma diskHomeomorphCube_symm_diskHomeomorphCube_down.{v} (z : TopCat.disk.{u} n) :
    ((diskHomeomorphCube.{v} n).symm (diskHomeomorphCube.{u} n z) :
        ULift.{v} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down =
      (z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down := by
  let z' : TopCat.disk.{v} n :=
    (ULift.up (z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      ULift.{v} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  have hcb : diskHomeomorphClosedBall.{u} n z = diskHomeomorphClosedBall.{v} n z' :=
    Subtype.ext ((coe_diskHomeomorphClosedBall_apply z).trans
      (coe_diskHomeomorphClosedBall_apply z').symm)
  have hcube : diskHomeomorphCube.{u} n z = diskHomeomorphCube.{v} n z' := by
    rw [diskHomeomorphCube_apply, diskHomeomorphCube_apply, hcb]
  rw [hcube, Homeomorph.symm_apply_apply]

variable {n} in
/-- `TauCeti.diskHomeomorphCube` carries the boundary sphere of the disk onto the boundary of the
cube. -/
theorem diskHomeomorphCube_mem_boundary_iff (z : TopCat.disk.{u} n) :
    diskHomeomorphCube n z ∈ Cube.boundary (Fin n) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [← norm_diskHomeomorphClosedBall_eq_one_iff, ← norm_cubeHomeomorphClosedBall_eq_one_iff,
    diskHomeomorphCube, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]

/-- A point of the disk `𝔻 2` lies on its boundary circle exactly when the corresponding point of
the square `I × I` lies on the boundary of the square. -/
lemma piFinTwo_diskHomeomorphCube_notMem_iff (z : TopCat.disk.{u} 2) :
    Homeomorph.piFinTwo (fun _ ↦ I) (diskHomeomorphCube 2 z) ∉
        Set.Ioo (0 : I) 1 ×ˢ Set.Ioo (0 : I) 1 ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} 2) := by
  rw [← diskHomeomorphCube_mem_boundary_iff, unitInterval.notMem_Ioo_prod_Ioo_iff]
  simp [Cube.boundary, Fin.exists_fin_two, or_assoc]

variable {n} in
/-- The point of the closed ball corresponding to a point of the cube has norm one exactly when the
point lies on the boundary of the cube. -/
theorem norm_down_diskHomeomorphCube_symm_eq_one_iff (y : I^(Fin n)) :
    ‖(((diskHomeomorphCube.{u} n).symm y :
        ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
          EuclideanSpace ℝ (Fin n))‖ = 1 ↔ y ∈ Cube.boundary (Fin n) := by
  rw [← mem_range_diskBoundaryInclusion_iff, ← diskHomeomorphCube_mem_boundary_iff,
    Homeomorph.apply_symm_apply]

/-- The homeomorphism `TauCeti.diskHomeomorphCube` as an isomorphism in `TopCat` from the disk
onto the lifted cube. -/
private def diskIsoCube : TopCat.disk.{u} n ≅ TopCat.of (ULift.{u} (I^(Fin n))) :=
  TopCat.isoOfHomeo ((diskHomeomorphCube n).trans Homeomorph.ulift.{u}.symm)

/-- The homeomorphism `TauCeti.diskHomeomorphCube` as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Iⁿ, ∂Iⁿ)`. -/
def diskBoundaryPairToCube : diskBoundaryPair.{u} n ⟶ cubeBoundaryPair.{u} n :=
  TopPair.ofHom (diskIsoCube n).hom
    (TopCat.ofHom ⟨fun s ↦ ⟨ULift.up (diskHomeomorphCube n (TopCat.diskBoundaryInclusion n s)),
      (diskHomeomorphCube_mem_boundary_iff _).2 ⟨s, rfl⟩⟩,
      (continuous_uliftUp.comp ((diskHomeomorphCube n).continuous.comp
        (TopCat.diskBoundaryInclusion n).hom.continuous)).subtype_mk _⟩)
    (by ext; rfl)

variable {n} in
/-- On the disk, `TauCeti.diskBoundaryPairToCube` is `TauCeti.diskHomeomorphCube`. -/
lemma diskBoundaryPairToCube_fst_apply_down (z : (diskBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (diskBoundaryPairToCube.{u} n) z).down = diskHomeomorphCube n z :=
  (rfl)

variable {n} in
/-- On the boundary sphere, `TauCeti.diskBoundaryPairToCube` is `TauCeti.diskHomeomorphCube`. -/
lemma diskBoundaryPairToCube_snd_apply_down (s : (diskBoundaryPair.{u} n).snd) :
    (TopPair.Hom.snd (diskBoundaryPairToCube.{u} n) s).val.down =
      diskHomeomorphCube n (TopCat.diskBoundaryInclusion n s) := by
  rw [diskBoundaryPairToCube]
  rfl

private lemma surjective_snd_diskBoundaryPairToCube :
    Function.Surjective (TopPair.Hom.snd (diskBoundaryPairToCube.{u} n)) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs⟩ := (diskHomeomorphCube_mem_boundary_iff ((diskHomeomorphCube n).symm y.down)).1
    (by rwa [Homeomorph.apply_symm_apply])
  refine ⟨s, Subtype.ext (ULift.ext ?_)⟩
  -- The subspace component of the map is `TauCeti.diskHomeomorphCube` on the boundary sphere.
  change diskHomeomorphCube n (TopCat.diskBoundaryInclusion n s) = y.down
  rw [hs, Homeomorph.apply_symm_apply]

/-- **The disk pair is the cube pair**: `TauCeti.diskBoundaryPairToCube` is an isomorphism of
pairs `(Dⁿ, Sⁿ⁻¹) ≅ (Iⁿ, ∂Iⁿ)`. -/
def diskBoundaryPairIsoCube : diskBoundaryPair.{u} n ≅ cubeBoundaryPair.{u} n :=
  have : IsIso (TopPair.Hom.fst (diskBoundaryPairToCube.{u} n)) :=
    inferInstanceAs (IsIso (diskIsoCube n).hom)
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd _ (surjective_snd_diskBoundaryPairToCube n)
  asIso (diskBoundaryPairToCube n)

@[simp]
lemma diskBoundaryPairIsoCube_hom : (diskBoundaryPairIsoCube.{u} n).hom =
    diskBoundaryPairToCube n :=
  (rfl)

variable {n} in
/-- On the disk, `TauCeti.diskBoundaryPairIsoCube` sends `z` to `TauCeti.diskHomeomorphCube n z`. -/
lemma diskBoundaryPairIsoCube_hom_fst_apply_down (z : TopCat.disk.{u} n) :
    (TopPair.Hom.fst (diskBoundaryPairIsoCube.{u} n).hom z).down = diskHomeomorphCube n z := by
  rw [diskBoundaryPairIsoCube_hom]
  exact diskBoundaryPairToCube_fst_apply_down z

/-- In dimension one the radial rescaling `TauCeti.diskHomeomorphClosedBall` is the identity on
coordinates, since the Euclidean and the sup norms on `ℝ¹` agree. -/
lemma coe_diskHomeomorphClosedBall_one_apply (z : TopCat.disk.{u} 1) :
    (diskHomeomorphClosedBall 1 z : Fin 1 → ℝ) =
      fun _ ↦ ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 := by
  have hc (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace.equiv (Fin 1) ℝ x = fun _ ↦ x 0 :=
    funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
  rw [coe_diskHomeomorphClosedBall_apply,
    ContinuousLinearEquiv.unitBallHomeomorph_apply_of_norm_map _ (fun x ↦ by
      rw [hc, pi_norm_const, EuclideanSpace.norm_fin_one, Real.norm_eq_abs]), hc]

/-- The homeomorphism of the `1`-disk onto the interval sends the boundary point with positive
coordinate to `1`. -/
lemma diskHomeomorphCube_one_of_pos (z : TopCat.disk.{u} 1)
    (hz : z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} 1))
    (hpos : 0 < ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0) :
    diskHomeomorphCube 1 z = fun _ ↦ 1 := by
  have habs := (mem_range_diskBoundaryInclusion_iff z).1 hz
  rw [EuclideanSpace.norm_fin_one, abs_of_pos hpos] at habs
  have h1 : (diskHomeomorphClosedBall 1 z : Fin 1 → ℝ) 0 = 1 :=
    (congrFun (coe_diskHomeomorphClosedBall_one_apply z) 0).trans habs
  funext i
  rw [Subsingleton.elim i 0]
  ext
  rw [diskHomeomorphCube_apply, coe_cubeHomeomorphClosedBall_symm_apply, h1]
  norm_num

/-- The homeomorphism of the `1`-disk onto the interval sends the boundary point with negative
coordinate to `0`. -/
lemma diskHomeomorphCube_one_of_neg (z : TopCat.disk.{u} 1)
    (hz : z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} 1))
    (hneg : ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0 < 0) :
    diskHomeomorphCube 1 z = fun _ ↦ 0 := by
  have habs := (mem_range_diskBoundaryInclusion_iff z).1 hz
  rw [EuclideanSpace.norm_fin_one, abs_of_neg hneg] at habs
  have h1 : (diskHomeomorphClosedBall 1 z : Fin 1 → ℝ) 0 = -1 :=
    (congrFun (coe_diskHomeomorphClosedBall_one_apply z) 0).trans (neg_eq_iff_eq_neg.1 habs)
  funext i
  rw [Subsingleton.elim i 0]
  ext
  rw [diskHomeomorphCube_apply, coe_cubeHomeomorphClosedBall_symm_apply, h1]
  norm_num

/-- The cube `Iⁿ` is contractible, being homeomorphic to the disk. -/
instance contractibleSpace_cubeBoundaryPair_fst (n : ℕ) :
    ContractibleSpace (cubeBoundaryPair.{u} n).fst :=
  ((diskHomeomorphCube.{u} n).trans Homeomorph.ulift.symm).symm.contractibleSpace

end CubePair

end TauCeti

namespace LinearIsometryEquiv

section ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

/-- The homeomorphism `x ↦ e x` from the closed unit ball of `E` onto the disk `TopCat.disk n`
induced by a linear isometry `e` of `E` onto `EuclideanSpace ℝ (Fin n)`. For instance, through
`LinearIsometryEquiv.piLpCongrLeft`, a bijection `ι ≃ Fin n` of coordinates identifies the closed
unit ball of `EuclideanSpace ℝ ι` with the disk. -/
def closedBallHomeomorphDisk : Metric.closedBall (0 : E) 1 ≃ₜ TopCat.disk.{u} n :=
  (e.toHomeomorph.subtype fun x ↦ by simp).trans Homeomorph.ulift.symm

@[simp]
lemma coe_closedBallHomeomorphDisk_apply_down (x : Metric.closedBall (0 : E) 1) :
    ((e.closedBallHomeomorphDisk.{u} x).down : EuclideanSpace ℝ (Fin n)) = e x :=
  (rfl)

@[simp]
lemma coe_closedBallHomeomorphDisk_symm_apply (z : TopCat.disk.{u} n) :
    (e.closedBallHomeomorphDisk.symm z : E) = e.symm z.down :=
  (rfl)

end ClosedBall

variable {n : ℕ} (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

/-- The homeomorphism `x ↦ e x` of the disk `TopCat.disk n` induced by a linear isometry `e` of
`EuclideanSpace ℝ (Fin n)`. It restricts on the boundary sphere to
`LinearIsometryEquiv.diskBoundaryIso e`
(`LinearIsometryEquiv.diskBoundaryIso_hom_comp_diskBoundaryInclusion`). -/
def diskIso : TopCat.disk.{u} n ≅ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo <| Homeomorph.ulift.trans <|
    (e.toHomeomorph.subtype fun x ↦ by simp).trans Homeomorph.ulift.symm

/-- The homeomorphism `x ↦ e x` of the boundary sphere `TopCat.diskBoundary n` of the disk induced
by a linear isometry `e` of `EuclideanSpace ℝ (Fin n)`. -/
def diskBoundaryIso : TopCat.diskBoundary.{u} n ≅ TopCat.diskBoundary.{u} n :=
  TopCat.isoOfHomeo <| Homeomorph.ulift.trans <|
    (e.toHomeomorph.subtype fun x ↦ by simp).trans Homeomorph.ulift.symm

@[simp]
lemma coe_diskIso_hom_apply_down (z : TopCat.disk.{u} n) :
    ((e.diskIso.hom z).down : EuclideanSpace ℝ (Fin n)) = e z.down :=
  (rfl)

@[simp]
lemma coe_diskIso_inv_apply_down (z : TopCat.disk.{u} n) :
    ((e.diskIso.inv z).down : EuclideanSpace ℝ (Fin n)) = e.symm z.down :=
  (rfl)

@[simp]
lemma coe_diskBoundaryIso_hom_apply_down (z : TopCat.diskBoundary.{u} n) :
    ((e.diskBoundaryIso.hom z).down : EuclideanSpace ℝ (Fin n)) = e z.down :=
  (rfl)

@[simp]
lemma coe_diskBoundaryIso_inv_apply_down (z : TopCat.diskBoundary.{u} n) :
    ((e.diskBoundaryIso.inv z).down : EuclideanSpace ℝ (Fin n)) = e.symm z.down :=
  (rfl)

/-- The homeomorphism of the disk induced by a linear isometry restricts on the boundary sphere to
the homeomorphism of the sphere induced by the same isometry. -/
@[reassoc]
lemma diskBoundaryIso_hom_comp_diskBoundaryInclusion :
    e.diskBoundaryIso.hom ≫ TopCat.diskBoundaryInclusion.{u} n =
      TopCat.diskBoundaryInclusion.{u} n ≫ e.diskIso.hom := by
  ext z
  refine ULift.ext (Subtype.ext ?_)
  simp [TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down]

/-- The antipodal map `TauCeti.diskBoundaryNeg` of the boundary sphere is induced by the linear
isometry `x ↦ -x`. -/
@[simp]
lemma diskBoundaryIso_neg_hom :
    (LinearIsometryEquiv.neg ℝ).diskBoundaryIso.hom = TauCeti.diskBoundaryNeg.{u} n := by
  ext z
  refine ULift.ext (Subtype.ext ?_)
  simp

end LinearIsometryEquiv

namespace TauCeti

/-- The unit sphere of any real normed space `F` of dimension `n + 1` is homeomorphic to
`TopCat.sphere.{u} n` in any target universe `u`. -/
def sphereHomeomorphTopCatSphere {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hF : Module.finrank ℝ F = n + 1) :
    Metric.sphere (0 : F) 1 ≃ₜ TopCat.sphere.{u} n :=
  haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  (sphereHomeomorphOfFinrankEq
      (hF.trans (finrank_euclideanSpace_ulift_fin.{u} (n + 1)).symm)).trans
    (diskBoundaryHomeomorph (n + 1)).symm

@[simp]
theorem sphereHomeomorphTopCatSphere_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hF : Module.finrank ℝ F = n + 1) (x : Metric.sphere (0 : F) 1) :
    haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
    sphereHomeomorphTopCatSphere.{u} hF x =
      (diskBoundaryHomeomorph (n + 1)).symm
        (sphereHomeomorphOfFinrankEq
          (hF.trans (finrank_euclideanSpace_ulift_fin.{u} (n + 1)).symm) x) :=
  (rfl)

@[simp]
theorem sphereHomeomorphTopCatSphere_symm_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hF : Module.finrank ℝ F = n + 1) (y : TopCat.sphere.{u} n) :
    haveI : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
    (sphereHomeomorphTopCatSphere.{u} hF).symm y =
      (sphereHomeomorphOfFinrankEq
        (hF.trans (finrank_euclideanSpace_ulift_fin.{u} (n + 1)).symm)).symm
        (diskBoundaryHomeomorph (n + 1) y) :=
  (rfl)

end TauCeti

namespace ContinuousMap.HomotopyEquiv

open scoped ContinuousMap

variable {X : Type u} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transport a homotopy equivalence `X ≃ₕ Metric.sphere (0 : F) 1` (with `F` in any universe and
`Module.finrank ℝ F = n + 1`) to `X ≃ₕ TopCat.sphere.{u} n` in the universe of `X`. -/
def topCatSphere {n : ℕ} (e : X ≃ₕ Metric.sphere (0 : F) 1) (hF : Module.finrank ℝ F = n + 1) :
    X ≃ₕ TopCat.sphere.{u} n :=
  e.trans (TauCeti.sphereHomeomorphTopCatSphere.{u} hF).toHomotopyEquiv

@[simp]
theorem topCatSphere_apply {n : ℕ} (e : X ≃ₕ Metric.sphere (0 : F) 1)
    (hF : Module.finrank ℝ F = n + 1) (x : X) :
    e.topCatSphere hF x = TauCeti.sphereHomeomorphTopCatSphere.{u} hF (e x) :=
  (rfl)

@[simp]
theorem topCatSphere_symm_apply {n : ℕ} (e : X ≃ₕ Metric.sphere (0 : F) 1)
    (hF : Module.finrank ℝ F = n + 1) (y : TopCat.sphere.{u} n) :
    (e.topCatSphere hF).symm y =
      e.symm ((TauCeti.sphereHomeomorphTopCatSphere.{u} hF).symm y) :=
  (rfl)

end ContinuousMap.HomotopyEquiv

end
