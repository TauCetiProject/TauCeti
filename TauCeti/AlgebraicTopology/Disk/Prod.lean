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
public import TauCeti.Topology.ContinuousMap.Sigma

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

The handle of index `l` in dimension `m` is also given its own name, as a type:
`TauCeti.TopCat.handle l m` is `𝔻 l × 𝔻 (m - l)`, `TauCeti.TopCat.attachingRegion l m` is
`∂𝔻 l × 𝔻 (m - l)`, and for indices `k : ι → ℕ` the map `TauCeti.TopCat.attachingRegionIncl k m`
includes the disjoint union `Σ i, attachingRegion (k i) m` of the attaching regions into the
disjoint union `Σ i, handle (k i) m` of the handles, summand by summand. A handle is compact,
Hausdorff and contractible, and for `l ≤ m` it is homeomorphic to the closed unit ball of every
real normed space of dimension `m` (`TauCeti.TopCat.diskProdHomeomorphClosedBall`). Its attaching
region is compact, and it is nonempty exactly when `l ≠ 0`
(`TauCeti.TopCat.nonempty_attachingRegion_iff`), so a handle of index `0` is attached along
nothing. With these names, attaching handles to `X` along a map `φ` is the pushout in `TopCat` of
`φ` and `attachingRegionIncl k m`. Such a square is the same as the square of coproducts above
(`TauCeti.TopCat.isPushout_attachingRegionIncl_iff`), read through Mathlib's identification
`TopCat.sigmaIsoSigma` of coproducts in `TopCat` with disjoint unions. So
`attachingRegionIncl k m` is a closed embedding
(`TauCeti.TopCat.isClosedEmbedding_attachingRegionIncl`), the pushout contains `X` as a closed
subspace (`TauCeti.TopCat.isClosedEmbedding_pushout_inl`), and the pushout is Hausdorff when `X` is
(`TauCeti.TopCat.t2Space_pushout`). It deformation retracts, relative to `X`, onto `X` with the
cores `𝔻 (k i) × {0}` of the handles attached
(`CategoryTheory.IsPushout.exists_strong_deformation_retraction_cores`, in
`TauCeti.AlgebraicTopology.Disk.Handle`).

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
    (z.1 : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).down.property
  have h₂ := mem_closedBall_zero_iff.1
    (z.2 : ULift.{v} (closedBall (0 : EuclideanSpace ℝ (Fin l)) 1)).down.property
  rw [max_eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    exacts [Or.inl h, Or.inr h]
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]; exact h₂⟩
    · exact Or.inr ⟨h, by rw [h]; exact h₁⟩

end Homeomorph

section Handle

/-- The **handle** of index `l` in dimension `m`: the product `𝔻 l × 𝔻 (m - l)` of the closed unit
balls of `EuclideanSpace ℝ (Fin l)` and `EuclideanSpace ℝ (Fin (m - l))`. It is compact, Hausdorff
and contractible, and for `l ≤ m` it is homeomorphic to the closed unit ball of every real normed
space of dimension `m` (`TauCeti.TopCat.diskProdHomeomorphClosedBall l (m - l)`). -/
abbrev handle (l m : ℕ) : Type u :=
  TopCat.disk.{u} l × TopCat.disk.{u} (m - l)

/-- The **attaching region** `∂𝔻 l × 𝔻 (m - l)` of the handle of index `l` in dimension `m`: the
product of the unit sphere of `EuclideanSpace ℝ (Fin l)` and the closed unit ball of
`EuclideanSpace ℝ (Fin (m - l))`. It is compact, and empty exactly when `l = 0`
(`TauCeti.TopCat.nonempty_attachingRegion_iff`). -/
abbrev attachingRegion (l m : ℕ) : Type u :=
  TopCat.diskBoundary.{u} l × TopCat.disk.{u} (m - l)

/-- For handles of indices `k i` in dimension `m`, the inclusion of the disjoint union of their
attaching regions `∂𝔻 (k i) × 𝔻 (m - k i)` into the disjoint union of the handles
`𝔻 (k i) × 𝔻 (m - k i)`, summand by summand. -/
def attachingRegionIncl {ι : Type v} (k : ι → ℕ) (m : ℕ) :
    C((i : ι) × attachingRegion.{u} (k i) m, (i : ι) × handle.{u} (k i) m) where
  toFun := Sigma.map id fun i ↦ Prod.map (TopCat.diskBoundaryInclusion (k i)) id
  continuous_toFun := continuous_sigma_map.2 fun i ↦
    (TopCat.diskBoundaryInclusion (k i)).hom.continuous.prodMap continuous_id

/-- `TauCeti.TopCat.attachingRegionIncl` is the map of disjoint unions induced by the inclusions
`∂𝔻 (k i) × 𝔻 (m - k i) → 𝔻 (k i) × 𝔻 (m - k i)`. -/
theorem coe_attachingRegionIncl {ι : Type v} (k : ι → ℕ) (m : ℕ) :
    ⇑(attachingRegionIncl.{u} k m) =
      Sigma.map id fun (i : ι) ↦ Prod.map (TopCat.diskBoundaryInclusion (k i)) id :=
  (rfl)

/-- `TauCeti.TopCat.attachingRegionIncl` keeps the summand and includes the sphere factor into
the disk. -/
@[simp]
theorem attachingRegionIncl_apply {ι : Type v} (k : ι → ℕ) (m : ℕ) (i : ι)
    (q : attachingRegion.{u} (k i) m) :
    attachingRegionIncl k m ⟨i, q⟩ = ⟨i, TopCat.diskBoundaryInclusion (k i) q.1, q.2⟩ :=
  (rfl)

/-- The attaching region `∂𝔻 l × 𝔻 (m - l)` is nonempty exactly when `l ≠ 0`: a handle of index
`0` is attached along the empty set. -/
theorem nonempty_attachingRegion_iff {l m : ℕ} : Nonempty (attachingRegion.{u} l m) ↔ l ≠ 0 := by
  rw [nonempty_prod, nonempty_diskBoundary_iff]
  exact and_iff_left ⟨diskCenter _⟩

/-- The inclusion of the attaching regions into the handles is a closed embedding. -/
theorem isClosedEmbedding_attachingRegionIncl {ι : Type v} (k : ι → ℕ) (m : ℕ) :
    IsClosedEmbedding (attachingRegionIncl.{u} k m) := by
  rw [coe_attachingRegionIncl]
  exact (Topology.isClosedEmbedding_sigmaMap Function.injective_id).2 fun i ↦
    (isClosedEmbedding_diskBoundaryInclusion (k i)).prodMap IsClosedEmbedding.id

end Handle

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

section Pushout

variable {ι : Type u} {k : ι → ℕ} {m : ℕ} {X P : _root_.TopCat.{u}}

/-- **Handle attachments along disjoint unions and along coproducts.** A square in `TopCat` with
the inclusion `attachingRegionIncl k m` of the disjoint union of the attaching regions into that of
the handles, a map `φ` out of the attaching regions and a map `χ` out of the handles, is a pushout
exactly when the corresponding square of coproducts is one, with the restrictions of `φ` and `χ` to
the summands. The second form is the one of `TauCeti.TopCat.isClosedEmbedding_of_isPushout_handles`,
`TauCeti.TopCat.t2Space_of_isPushout_handles` and
`CategoryTheory.IsPushout.exists_coreAttachment_deformation`. -/
theorem isPushout_attachingRegionIncl_iff
    {φ : _root_.TopCat.of ((i : ι) × attachingRegion.{u} (k i) m) ⟶ X} {j : X ⟶ P}
    {χ : _root_.TopCat.of ((i : ι) × handle.{u} (k i) m) ⟶ P} :
    IsPushout φ (TopCat.ofHom (attachingRegionIncl k m)) j χ ↔
      IsPushout (Sigma.desc fun i ↦ TopCat.ofHom
          (φ.hom.comp (ContinuousMap.sigmaMk (X := fun i ↦ attachingRegion.{u} (k i) m) i)))
        (Limits.Sigma.map fun i ↦ TopCat.ofHom ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap
          (ContinuousMap.id (TopCat.disk.{u} (m - k i)))))
        j (Sigma.desc fun i ↦ TopCat.ofHom
          (χ.hom.comp (ContinuousMap.sigmaMk (X := fun i ↦ handle.{u} (k i) m) i))) := by
  let A (i : ι) := TopCat.of (attachingRegion.{u} (k i) m)
  let B (i : ι) := TopCat.of (handle.{u} (k i) m)
  -- Mathlib's identification `TopCat.sigmaIsoSigma` of the coproducts with the disjoint unions
  -- carries each map out of a disjoint union to the map glued from its restrictions.
  have hφ : (TopCat.sigmaIsoSigma A).hom ≫ φ = Sigma.desc fun i ↦ TopCat.ofHom
      (φ.hom.comp (ContinuousMap.sigmaMk (X := fun i ↦ attachingRegion.{u} (k i) m) i)) :=
    Sigma.hom_ext _ _ fun i ↦ by
      rw [TopCat.sigmaIsoSigma_hom_ι_assoc, Sigma.ι_comp_desc]
      ext
      simp
  have hincl : (TopCat.sigmaIsoSigma A).hom ≫ TopCat.ofHom (attachingRegionIncl k m) =
      Limits.Sigma.map (fun i ↦ TopCat.ofHom ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap
        (ContinuousMap.id (TopCat.disk.{u} (m - k i))))) ≫ (TopCat.sigmaIsoSigma B).hom :=
    Sigma.hom_ext _ _ fun i ↦ by
      rw [TopCat.sigmaIsoSigma_hom_ι_assoc, Sigma.ι_map_assoc, TopCat.sigmaIsoSigma_hom_ι]
      -- Both maps send `q` to `⟨i, (TopCat.diskBoundaryInclusion (k i) q.1, q.2)⟩`.
      exact TopCat.hom_ext (ContinuousMap.ext fun q ↦ attachingRegionIncl_apply k m i q)
  have hχ : (TopCat.sigmaIsoSigma B).hom ≫ χ = Sigma.desc fun i ↦ TopCat.ofHom
      (χ.hom.comp (ContinuousMap.sigmaMk (X := fun i ↦ handle.{u} (k i) m) i)) :=
    Sigma.hom_ext _ _ fun i ↦ by
      rw [TopCat.sigmaIsoSigma_hom_ι_assoc, Sigma.ι_comp_desc]
      ext
      simp
  refine ⟨fun h ↦ h.of_iso' (TopCat.sigmaIsoSigma A) (Iso.refl X) (TopCat.sigmaIsoSigma B)
    (Iso.refl P) (by simpa using hφ) hincl (by simp) (by simpa using hχ), fun h ↦ h.of_iso
    (TopCat.sigmaIsoSigma A) (Iso.refl X) (TopCat.sigmaIsoSigma B) (Iso.refl P)
    (by simpa using hφ.symm) hincl.symm (by simp) (by simpa using hχ.symm)⟩

/-- Attaching handles to a space `X` along any map `φ` of their attaching regions gives a space
containing `X` as a closed subspace: the first inclusion of the pushout of `φ` and
`attachingRegionIncl k m` is a closed embedding. -/
theorem isClosedEmbedding_pushout_inl
    (φ : _root_.TopCat.of ((i : ι) × attachingRegion.{u} (k i) m) ⟶ X) :
    IsClosedEmbedding (pushout.inl φ (TopCat.ofHom (attachingRegionIncl k m))) :=
  isClosedEmbedding_of_isPushout (IsPushout.of_hasPushout _ _)
    (isClosedEmbedding_attachingRegionIncl k m)

/-- Attaching handles to a Hausdorff space `X` along any map `φ` of their attaching regions gives a
Hausdorff space: the pushout of `φ` and `attachingRegionIncl k m` is Hausdorff. No finiteness of
the family of handles is needed. -/
instance t2Space_pushout [T2Space X]
    (φ : _root_.TopCat.of ((i : ι) × attachingRegion.{u} (k i) m) ⟶ X) :
    T2Space (pushout φ (TopCat.ofHom (attachingRegionIncl k m)) : _root_.TopCat.{u}) := by
  have h := (isPushout_attachingRegionIncl_iff (φ := φ)).1
    (IsPushout.of_hasPushout φ (TopCat.ofHom (attachingRegionIncl k m)))
  exact t2Space_of_isPushout_handles h

end Pushout

end TauCeti.TopCat
