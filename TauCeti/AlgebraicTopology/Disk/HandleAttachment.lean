/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.DisjointOpens

import TauCeti.Topology.CWComplex.Abstract.Hausdorff
import TauCeti.Topology.MetricSpace.Isometry.Basic

/-!
# Handles and handle attachments

A *handle* of index `k` and dimension `n = k + l` is the product `𝔻 k × 𝔻 l` of two closed
Euclidean disks, attached along its *attaching region* `∂𝔻 k × 𝔻 l` by the map
`(TopCat.diskBoundaryInclusion k).hom.prodMap (ContinuousMap.id _)`. Crossing a critical level of
a Morse function attaches one handle for each critical point, as a pushout in `TopCat`
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`). This file records the point-set topology of
handles and of the spaces obtained by attaching them.

* The handle `𝔻 k × 𝔻 l` is homeomorphic to the disk `𝔻 (k + l)`, by a homeomorphism carrying the
  boundary `∂𝔻 k × 𝔻 l ∪ 𝔻 k × ∂𝔻 l` of the handle onto the boundary sphere
  (`TauCeti.TopCat.diskProdHomeomorph`,
  `TauCeti.TopCat.diskProdHomeomorph_apply_mem_range_diskBoundaryInclusion_iff`). Both disks are
  read as closed unit balls of the sup norm (`TauCeti.diskHomeomorphClosedBall`), where the
  product of the balls is the ball of the concatenated coordinates (`Fin.appendIsometryOfEq`).
* The inclusion of the attaching region extends disjoint open sets, as the boundary sphere of a
  cell does (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion_prodMap`, beside the
  statement for cells): the points `(x, y)` with `1 / 2 < ‖x‖` form a collar of the attaching
  region, retracted onto it by the radial projection `(x, y) ↦ (x / ‖x‖, y)`.
* Hence, in a pushout square attaching any family of handles to a space `X` along any map, the
  inclusion of `X` is a closed embedding
  (`TauCeti.TopCat.isClosedEmbedding_of_isPushout_diskBoundaryInclusion_prodMap`), and the result
  is Hausdorff when `X` is (`TauCeti.TopCat.t2Space_of_isPushout_diskBoundaryInclusion_prodMap`).
  The family of handles may be infinite and the attaching map is arbitrary. Both statements hold
  for products `𝔻 k × Y` attached along `∂𝔻 k × Y`, with `Y` regular and Hausdorff for the
  second; a handle is the case `Y = 𝔻 l`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, for the handle `D^λ × D^(n-λ)` attached across a critical level.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Appendix, Proposition A.3 and its proof, for separating the
  points of a space with cells attached through collar neighbourhoods.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe u

namespace TauCeti.TopCat

/-! ### A product of disks is a disk -/

/-- The closed unit ball of the sup norm on `Fin k → ℝ` times that on `Fin l → ℝ` is the closed
unit ball of the sup norm on `Fin n → ℝ`, `k + l = n`, by concatenating coordinates. -/
private def closedBallProdHomeomorph {k l n : ℕ} (h : k + l = n) :
    closedBall (0 : Fin k → ℝ) 1 × closedBall (0 : Fin l → ℝ) 1 ≃ₜ
      closedBall (0 : Fin n → ℝ) 1 :=
  (Homeomorph.Set.prod _ _).symm.trans <|
    (Fin.appendIsometryOfEq h).toHomeomorph.subtype fun p ↦ by
      rw [IsometryEquiv.coe_toHomeomorph, ← Fin.image_closedBall_prod_appendIsometryOfEq h 1,
        (Fin.appendIsometryOfEq h).injective.mem_set_image]

/-- `closedBallProdHomeomorph` concatenates the coordinates of the two factors. Mathlib has no
evaluation lemmas for `Homeomorph.Set.prod` and `Homeomorph.subtype`, so this holds by unfolding
both definitions. -/
private theorem coe_closedBallProdHomeomorph_apply {k l n : ℕ} (h : k + l = n)
    (p : closedBall (0 : Fin k → ℝ) 1 × closedBall (0 : Fin l → ℝ) 1) :
    (closedBallProdHomeomorph h p : Fin n → ℝ) = Fin.appendIsometryOfEq h (p.1, p.2) :=
  rfl

/-- **The handle `𝔻 k × 𝔻 l` is the disk `𝔻 n`**, for `k + l = n`; in particular the handle
`𝔻 k × 𝔻 (n - k)` of index `k ≤ n` is homeomorphic to `𝔻 n`. Read in the closed unit balls
of the sup norm (`TauCeti.diskHomeomorphClosedBall`), the homeomorphism concatenates coordinates
(`TauCeti.TopCat.coe_diskHomeomorphClosedBall_diskProdHomeomorph`); it carries the boundary of
the handle onto the boundary sphere
(`TauCeti.TopCat.diskProdHomeomorph_apply_mem_range_diskBoundaryInclusion_iff`). -/
def diskProdHomeomorph {k l n : ℕ} (h : k + l = n) :
    TopCat.disk.{u} k × TopCat.disk.{u} l ≃ₜ TopCat.disk.{u} n :=
  ((diskHomeomorphClosedBall k).prodCongr (diskHomeomorphClosedBall l)).trans <|
    (closedBallProdHomeomorph h).trans (diskHomeomorphClosedBall n).symm

/-- Read in the closed unit balls of the sup norm, `TauCeti.TopCat.diskProdHomeomorph`
concatenates the coordinates of the two factors. -/
theorem coe_diskHomeomorphClosedBall_diskProdHomeomorph {k l n : ℕ} (h : k + l = n)
    (z : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    (diskHomeomorphClosedBall n (diskProdHomeomorph h z) : Fin n → ℝ) =
      Fin.appendIsometryOfEq h
        ((diskHomeomorphClosedBall k z.1 : Fin k → ℝ), (diskHomeomorphClosedBall l z.2 : _)) := by
  rw [diskProdHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, coe_closedBallProdHomeomorph_apply, Homeomorph.coe_prodCongr,
    Prod.map_fst, Prod.map_snd]

/-- Read in the closed unit balls of the sup norm, the inverse of
`TauCeti.TopCat.diskProdHomeomorph` splits the coordinates into the first `k` and the last `l`. -/
theorem coe_diskHomeomorphClosedBall_diskProdHomeomorph_symm {k l n : ℕ} (h : k + l = n)
    (z : TopCat.disk.{u} n) :
    ((diskHomeomorphClosedBall k ((diskProdHomeomorph h).symm z).1 : Fin k → ℝ),
        (diskHomeomorphClosedBall l ((diskProdHomeomorph h).symm z).2 : Fin l → ℝ)) =
      (Fin.appendIsometryOfEq h).symm (diskHomeomorphClosedBall n z) := by
  rw [IsometryEquiv.eq_symm_apply, ← coe_diskHomeomorphClosedBall_diskProdHomeomorph,
    Homeomorph.apply_symm_apply]

/-- The homeomorphism `TauCeti.TopCat.diskProdHomeomorph` carries the boundary
`∂𝔻 k × 𝔻 l ∪ 𝔻 k × ∂𝔻 l` of the handle onto the boundary sphere of the disk. -/
theorem diskProdHomeomorph_apply_mem_range_diskBoundaryInclusion_iff {k l n : ℕ}
    (h : k + l = n) (z : TopCat.disk.{u} k × TopCat.disk.{u} l) :
    diskProdHomeomorph h z ∈ range (TopCat.diskBoundaryInclusion.{u} n) ↔
      z.1 ∈ range (TopCat.diskBoundaryInclusion.{u} k) ∨
        z.2 ∈ range (TopCat.diskBoundaryInclusion.{u} l) := by
  rw [← norm_diskHomeomorphClosedBall_eq_one_iff, ← norm_diskHomeomorphClosedBall_eq_one_iff,
    ← norm_diskHomeomorphClosedBall_eq_one_iff, coe_diskHomeomorphClosedBall_diskProdHomeomorph,
    (Fin.appendIsometryOfEq h).isometry.norm_map_of_map_zero (Fin.appendIsometryOfEq_zero h),
    Prod.norm_mk]
  -- Both norms are at most `1`, so their maximum is `1` exactly when one of them is.
  have h₁ := mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall k z.1).2
  have h₂ := mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall l z.2).2
  constructor
  · intro hmax
    rcases max_choice ‖(diskHomeomorphClosedBall k z.1 : Fin k → ℝ)‖
      ‖(diskHomeomorphClosedBall l z.2 : Fin l → ℝ)‖ with hm | hm
    · exact .inl (hm ▸ hmax)
    · exact .inr (hm ▸ hmax)
  · rintro (h' | h')
    · rw [h', max_eq_left h₂]
    · rw [h', max_eq_right h₁]

/-! ### Attaching handles -/

variable {ι : Type u} (k : ι → ℕ) (Y : ι → Type u) [∀ i, TopologicalSpace (Y i)]
  {X P : _root_.TopCat.{u}}
  {α : ∐ (fun i ↦ _root_.TopCat.of (TopCat.diskBoundary.{u} (k i) × Y i)) ⟶ X} {j : X ⟶ P}
  {χ : ∐ (fun i ↦ _root_.TopCat.of (TopCat.disk.{u} (k i) × Y i)) ⟶ P}

/-- The inclusion of the attaching regions `∂𝔻 (k i) × Y i` into the products `𝔻 (k i) × Y i` is
a closed embedding. -/
private theorem isClosedEmbedding_sigmaMap_diskBoundaryInclusion_prodMap :
    IsClosedEmbedding (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id (Y i)))) :=
  isClosedEmbedding_sigmaMap _ fun i ↦
    (isClosedEmbedding_diskBoundaryInclusion (k i)).prodMap .id

/-- **Attaching handles embeds the base as a closed subspace.** In a pushout square attaching
products `𝔻 (k i) × Y i` to a space `X` along the subspaces `∂𝔻 (k i) × Y i`, by any map `α`, the
inclusion `j` of `X` is a closed embedding. For `Y i = 𝔻 (l i)` this is the attachment of handles
`𝔻 (k i) × 𝔻 (l i)` along their attaching regions. -/
theorem isClosedEmbedding_of_isPushout_diskBoundaryInclusion_prodMap
    (sq : IsPushout α (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    IsClosedEmbedding j :=
  isClosedEmbedding_of_isPushout sq (isClosedEmbedding_sigmaMap_diskBoundaryInclusion_prodMap k Y)

/-- **Attaching handles to a Hausdorff space gives a Hausdorff space.** In a pushout square
attaching products `𝔻 (k i) × Y i` of disks with regular Hausdorff spaces to a Hausdorff space `X`
along the subspaces `∂𝔻 (k i) × Y i`, by any map `α`, the resulting space `P` is Hausdorff. For
`Y i = 𝔻 (l i)` this is the attachment of handles `𝔻 (k i) × 𝔻 (l i)` along their attaching
regions. The family may be infinite. -/
theorem t2Space_of_isPushout_diskBoundaryInclusion_prodMap [T2Space X] [∀ i, T2Space (Y i)]
    [∀ i, RegularSpace (Y i)]
    (sq : IsPushout α (Limits.Sigma.map fun i ↦ _root_.TopCat.ofHom
      ((TopCat.diskBoundaryInclusion.{u} (k i)).hom.prodMap (ContinuousMap.id (Y i)))) j χ) :
    T2Space P := by
  -- The disjoint union of the products is their sigma type, a regular Hausdorff space.
  let e := _root_.TopCat.homeoOfIso
    (_root_.TopCat.sigmaIsoSigma.{u, u} fun i ↦ _root_.TopCat.of (TopCat.disk.{u} (k i) × Y i))
  have : T2Space
      ((∐ fun i ↦ _root_.TopCat.of (TopCat.disk.{u} (k i) × Y i) : _root_.TopCat.{u})) :=
    e.symm.t2Space
  have : RegularSpace
      ((∐ fun i ↦ _root_.TopCat.of (TopCat.disk.{u} (k i) × Y i) : _root_.TopCat.{u})) :=
    e.isInducing.regularSpace
  exact t2Space_of_isPushout sq
    (MorphismProperty.colimMap _ fun ⟨i⟩ ↦ extendsDisjointOpens_diskBoundaryInclusion_prodMap _ _)
    (isClosedEmbedding_sigmaMap_diskBoundaryInclusion_prodMap k Y).isClosed_range

end TauCeti.TopCat
