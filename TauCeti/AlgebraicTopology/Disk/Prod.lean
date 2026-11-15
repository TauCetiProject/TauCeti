/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff

/-!
# Products of disks and handle attachments

A handle of index `k` and dimension `k + l` is the product `𝔻 k × 𝔻 l` of two Euclidean disks,
attached along its attaching region `∂𝔻 k × 𝔻 l` through the map
`(TopCat.diskBoundaryInclusion k).hom.prodMap (ContinuousMap.id _)`. This is the convention of the
handle attachment across a critical level of a Morse function
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`). This file records the point-set topology
of handles and of handle attachments.

* A handle is a disk: `𝔻 k × 𝔻 l` is homeomorphic to the closed unit ball of every real normed
  space of dimension `k + l` (`TauCeti.TopCat.diskProdHomeomorphClosedBall`), by a homeomorphism
  carrying the boundary `∂𝔻 k × 𝔻 l ∪ 𝔻 k × ∂𝔻 l` of the handle onto the unit sphere
  (`TauCeti.TopCat.norm_diskProdHomeomorphClosedBall_eq_one_iff`). The closed unit ball of the
  product norm on the product of the two Euclidean spaces is the product of their closed unit
  balls, and `TauCeti.closedBallHomeomorphOfFinrankEq` compares it with the closed unit ball of
  any other norm by rescaling rays. For a handle of index `k ≤ m` in dimension `m`, take
  `l = m - k` and `F = EuclideanSpace ℝ (Fin m)`.
* Attaching any family of handles to a space `X` along any map `φ` gives a space `P` containing
  `X` as a closed subspace (`TauCeti.TopCat.isClosedEmbedding_of_isPushout_handles`), and `P` is
  Hausdorff when `X` is (`TauCeti.TopCat.t2Space_of_isPushout_handles`). No finiteness of the
  family and no condition on `φ` are needed, and the second factor `𝔻 (l i)` of each handle may be
  replaced by any space `Y i`, regular and Hausdorff for the second statement. The attaching
  regions are closed in the handles, and each has a neighbourhood `‖x‖ > 1 / 2` retracting onto it
  radially, so its inclusion extends disjoint open sets
  (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion_prodMap`); the attachment is then
  Hausdorff by the argument for cell attachments (`HomotopicalAlgebra.AttachCells.t2Space`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (handles `Dᵏ × Dⁿ⁻ᵏ` attached along `∂Dᵏ × Dⁿ⁻ᵏ`).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, proof of Proposition A.3: separating the points of an attachment space by radially
  extended open sets.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe u v

namespace TauCeti.TopCat

section Homeomorph

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The product `𝔻 k × 𝔻 l` of two Euclidean disks is homeomorphic to the closed unit ball of every
real normed space `F` of dimension `k + l`. The two disks form the closed unit ball of the product
norm on `EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)`, which
`TauCeti.closedBallHomeomorphOfFinrankEq` carries onto the closed unit ball of `F`
(`TauCeti.TopCat.coe_diskProdHomeomorphClosedBall_apply`). The boundary of the product goes to the
unit sphere (`TauCeti.TopCat.norm_diskProdHomeomorphClosedBall_eq_one_iff`). -/
def diskProdHomeomorphClosedBall (k l : ℕ) (hF : Module.finrank ℝ F = k + l) :
    TopCat.disk.{u} k × TopCat.disk.{v} l ≃ₜ closedBall (0 : F) 1 :=
  (Homeomorph.ulift.prodCongr Homeomorph.ulift).trans <|
    ((Homeomorph.Set.prod _ _).symm.trans
      (Homeomorph.setCongr (closedBall_prod_same (0 : EuclideanSpace ℝ (Fin k))
        (0 : EuclideanSpace ℝ (Fin l)) 1))).trans <|
      closedBallHomeomorphOfFinrankEq (by simp [hF])

/-- `TauCeti.TopCat.diskProdHomeomorphClosedBall` is the radial rescaling
`ContinuousLinearEquiv.unitBallHomeomorph` of a linear equivalence, applied to the pair of
underlying vectors. -/
@[simp]
theorem coe_diskProdHomeomorphClosedBall_apply {k l : ℕ} (hF : Module.finrank ℝ F = k + l)
    (z : TopCat.disk.{u} k × TopCat.disk.{v} l) :
    (diskProdHomeomorphClosedBall k l hF z : F) =
      (ContinuousLinearEquiv.ofFinrankEq (E := EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))
        (by simp [hF])).unitBallHomeomorph
        (((z.1 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).down :
            EuclideanSpace ℝ (Fin k)),
          ((z.2 : ULift.{v} (closedBall (0 : EuclideanSpace ℝ (Fin l)) 1)).down :
            EuclideanSpace ℝ (Fin l))) :=
  coe_closedBallHomeomorphOfFinrankEq_apply _ _

/-- A point of `𝔻 k × 𝔻 l` is sent to the unit sphere by
`TauCeti.TopCat.diskProdHomeomorphClosedBall` exactly when it lies on the boundary of the product,
that is, when one of its two coordinates lies on the boundary sphere of its disk. -/
theorem norm_diskProdHomeomorphClosedBall_eq_one_iff {k l : ℕ} (hF : Module.finrank ℝ F = k + l)
    (z : TopCat.disk.{u} k × TopCat.disk.{v} l) :
    ‖(diskProdHomeomorphClosedBall k l hF z : F)‖ = 1 ↔
      z.1 ∈ range (TopCat.diskBoundaryInclusion.{u} k) ∨
        z.2 ∈ range (TopCat.diskBoundaryInclusion.{v} l) := by
  rw [coe_diskProdHomeomorphClosedBall_apply,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff, mem_range_diskBoundaryInclusion_iff,
    mem_range_diskBoundaryInclusion_iff, Prod.norm_def]
  have h₁ := mem_closedBall_zero_iff.1
    (z.1 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).down.2
  have h₂ := mem_closedBall_zero_iff.1
    (z.2 : ULift.{v} (closedBall (0 : EuclideanSpace ℝ (Fin l)) 1)).down.2
  rw [max_eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    exacts [Or.inl h, Or.inr h]
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]; exact h₂⟩
    · exact Or.inr ⟨h, by rw [h]; exact h₁⟩

end Homeomorph

section Attachment

variable {ι : Type u} {k : ι → ℕ} {Y : ι → TopCat.{u}} {X P : TopCat.{u}}
  {φ : ∐ (fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × Y i)) ⟶ X}
  {j : X ⟶ P} {χ : ∐ (fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Y i)) ⟶ P}

/-- Attaching handles `𝔻 (k i) × Y i` to a space `X` along their attaching regions
`∂𝔻 (k i) × Y i`, by any map `φ`, gives a space `P` containing `X` as a closed subspace: in a
pushout square in `TopCat` of `φ` and the inclusion of the attaching regions, the map `j : X ⟶ P`
is a closed embedding. In Morse theory `Y i` is the disk `𝔻 (l i)`. -/
theorem isClosedEmbedding_of_isPushout_handles
    (sq : IsPushout φ (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    IsClosedEmbedding j :=
  isClosedEmbedding_of_isPushout sq <| isClosedEmbedding_sigmaMap _ fun i ↦
    (isClosedEmbedding_diskBoundaryInclusion (k i)).prodMap IsClosedEmbedding.id

/-- Attaching handles `𝔻 (k i) × Y i` to a Hausdorff space `X` along their attaching regions
`∂𝔻 (k i) × Y i`, by any map `φ`, gives a Hausdorff space when each `Y i` is regular and
Hausdorff, for instance the disk `𝔻 (l i)` of Morse theory: in a pushout square in `TopCat` of `φ`
and the inclusion of the attaching regions, the corner `P` is Hausdorff. -/
theorem t2Space_of_isPushout_handles [T2Space X] [∀ i, T2Space (Y i)] [∀ i, RegularSpace (Y i)]
    (sq : IsPushout φ (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    T2Space P :=
  -- The square presents `P` as `X` with cells attached along closed embeddings which extend
  -- disjoint open sets, into regular Hausdorff handles.
  HomotopicalAlgebra.AttachCells.t2Space
    (g := fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Y i))))
    { ι := ι
      π := id
      cofan₁ := Cofan.mk _ (Sigma.ι _)
      cofan₂ := Cofan.mk _ (Sigma.ι _)
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := _
      g₁ := φ
      g₂ := χ
      isPushout := sq }
    (fun i ↦ extendsDisjointOpens_diskBoundaryInclusion_prodMap _ _)
    (fun i ↦ (isClosedEmbedding_diskBoundaryInclusion (k i)).prodMap IsClosedEmbedding.id)

end Attachment

end TauCeti.TopCat
