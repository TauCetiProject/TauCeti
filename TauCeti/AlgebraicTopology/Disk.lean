/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Euclidean disks and their boundaries

The closed Euclidean disk is contractible, and its boundary is path-connected when the disk has
dimension at least two.  This module also constructs the standard `TopPair` consisting of a disk
and its boundary, providing the topological input for relative-homology calculations.

Mathlib's `TopCat.diskBoundary n` is the universe lift of the unit sphere of
`EuclideanSpace ℝ (Fin n)`.  It is homeomorphic to the unit sphere of the Euclidean space
`EuclideanSpace ℝ (ULift (Fin n))` of the same dimension in the lifted universe
(`TauCeti.diskBoundaryHomeomorph`), which lets results about unit spheres of inner product spaces
in that universe be applied to it.  In particular the boundary of the `0`-disk is empty.

The disk is also homeomorphic to the closed unit ball of the sup norm on `Fin n → ℝ`, with its
boundary going to the unit sphere (`TauCeti.diskHomeomorphClosedBall`); this is how the disk is
compared with the domains of characteristic maps of CW complexes and with the cube.  Composing it
with the affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto the same ball
identifies the disk pair with the pair `TauCeti.cubeBoundaryPair n = (Iⁿ, ∂Iⁿ)` formed by the cube
and its boundary (`TauCeti.diskBoundaryPairIsoCube`).
-/

public section

noncomputable section
open CategoryTheory
universe u

namespace TauCeti.TopCat

/-- The `n`-dimensional Euclidean disk is contractible. -/
instance contractibleSpace_disk (n : ℕ) :
    ContractibleSpace (TopCat.disk n) := by
  -- `TopCat.disk` stores its metric closed ball inside a `ULift`; expose that carrier so the
  -- closed-ball contractibility instance can be transported through the lift equivalence.
  change ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  let hX : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_closedBall (x := 0) (r := 1) (by norm_num)
  have h : (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  exact h.contractibleSpace_iff.mpr hX

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

end TauCeti.TopCat

namespace TauCeti

/-- The standard pair consisting of the `n`-dimensional disk and its boundary, used to express
relative singular homology of the disk with respect to its boundary. -/
abbrev diskBoundaryPair (n : ℕ) : TopPair.{u} :=
  TopPair.of (TopCat.diskBoundaryInclusion n) (by
    let hT2 : T2Space (TopCat.disk n) := by
      -- Typeclass synthesis does not unfold the `TopCat.disk` wrapper, whose carrier is the
      -- lifted closed ball.
      change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
      infer_instance
    exact
      (((ConcreteCategory.hom (TopCat.diskBoundaryInclusion n)).continuous_toFun).isClosedEmbedding
        ((TopCat.mono_iff_injective _).mp
          (inferInstance : Mono (TopCat.diskBoundaryInclusion n)))).isEmbedding)

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

/-- A point of the disk is sent to the unit sphere of the sup norm by
`TauCeti.diskHomeomorphClosedBall` exactly when it lies on the boundary sphere. -/
lemma norm_diskHomeomorphClosedBall_eq_one_iff {n : ℕ} (z : TopCat.disk.{u} n) :
    ‖(diskHomeomorphClosedBall n z : Fin n → ℝ)‖ = 1 ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  set w : EuclideanSpace ℝ (Fin n) :=
    ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      EuclideanSpace ℝ (Fin n))
  have hs : (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph w ∈ Metric.sphere 0 1 ↔
      w ∈ Metric.sphere 0 1 := by
    conv_lhs => rw [← (EuclideanSpace.equiv (Fin n) ℝ).image_unitBallHomeomorph_sphere]
    exact (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph.injective.mem_set_image
  rw [coe_diskHomeomorphClosedBall_apply, ← mem_sphere_zero_iff_norm]
  refine hs.trans ⟨fun h ↦ ⟨ULift.up ⟨w, h⟩, rfl⟩, ?_⟩
  rintro ⟨s, rfl⟩
  -- The boundary inclusion keeps the underlying point of the sphere.
  exact (s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down.2

/-- The dimension of the Euclidean space `EuclideanSpace ℝ (ULift (Fin n))`. -/
lemma finrank_euclideanSpace_ulift_fin (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin n))) = n := by
  rw [finrank_euclideanSpace, Fintype.card_ulift, Fintype.card_fin]

/-- The boundary of the `0`-disk is empty. -/
instance isEmpty_diskBoundary_zero : IsEmpty (TopCat.diskBoundary.{u} 0) :=
  have : Subsingleton (EuclideanSpace ℝ (ULift.{u} (Fin 0))) :=
    Module.finrank_zero_iff.mp (finrank_euclideanSpace_ulift_fin 0)
  have : IsEmpty (Metric.sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin 0))) 1) :=
    Set.isEmpty_coe_sort.mpr (Metric.sphere_eq_empty_of_subsingleton one_ne_zero)
  (diskBoundaryHomeomorph 0).toEquiv.isEmpty

/-- The `n`-sphere is nonempty. -/
instance nonempty_topCatSphere (n : ℕ) : Nonempty (TopCat.sphere.{u} n) :=
  ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩⟩

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

/-- The homeomorphism from the Euclidean disk `Dⁿ` onto the cube `Iⁿ`: the radial rescaling of the
disk onto the closed unit ball of the sup norm on `Fin n → ℝ`, followed by the inverse of the affine
homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto that ball. -/
def diskHomeomorphCube : TopCat.disk.{u} n ≃ₜ (I^(Fin n)) :=
  (diskHomeomorphClosedBall n).trans (cubeHomeomorphClosedBall (Fin n)).symm

variable {n} in
/-- `TauCeti.diskHomeomorphCube` carries the boundary sphere of the disk onto the boundary of the
cube. -/
theorem diskHomeomorphCube_mem_boundary_iff (z : TopCat.disk.{u} n) :
    diskHomeomorphCube n z ∈ Cube.boundary (Fin n) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [← norm_diskHomeomorphClosedBall_eq_one_iff, ← norm_cubeHomeomorphClosedBall_eq_one_iff,
    diskHomeomorphCube, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]

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

end CubePair

end TauCeti
end
