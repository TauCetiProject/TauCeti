/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Handles: products of disks and their attachment

A handle of index `k` is a product `𝔻 k × Z` of the closed Euclidean disk `𝔻 k`, its core, with
a space `Z`, attached along its attaching region `∂𝔻 k × Z`. For a manifold of dimension `n` the
handles of index `k` are the products `𝔻 k × 𝔻 (n - k)`: crossing a critical level of a Morse
function attaches one of them at each critical point of index `k`
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`). This file records the topology of handles
and of their attachment.

* A handle `𝔻 k × 𝔻 l` is a disk: it is homeomorphic to `𝔻 (k + l)`
  (`TauCeti.TopCat.nonempty_homeomorph_disk_prod_disk`). The product of the two closed unit balls
  is the closed unit ball of the product norm on a space of dimension `k + l`.
* The inclusion `∂𝔻 k × Z ⟶ 𝔻 k × Z` of the attaching region extends disjoint open sets in the
  sense of `TauCeti.TopCat.extendsDisjointOpens`, for every space `Z`
  (`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion_prodMap`, which is proved alongside
  its case of a point `Z` in `TauCeti.Topology.CWComplex.Abstract.Hausdorff`): an open subset `U`
  of `∂𝔻 k × Z` is the trace of the open set of the points `(x, z)` with `1 / 2 < ‖x‖` and
  `(x / ‖x‖, z) ∈ U`.
* **Attaching handles to a Hausdorff space gives a Hausdorff space**
  (`TauCeti.TopCat.t2Space_of_isPushout_handles`), when each `Z i` is regular and Hausdorff, as
  the disks `𝔻 l` are. The family of handles may be infinite, and handles of index `0`, whose
  attaching region is empty, are allowed. In the pushout `P` of
  `α : ∐ᵢ ∂𝔻 (k i) × Z i ⟶ X` along the inclusion of the attaching regions, the map `X ⟶ P` is a
  closed embedding by `TauCeti.TopCat.isClosedEmbedding_of_isPushout` and
  `TauCeti.TopCat.isClosedEmbedding_sigmaMap`, since each attaching region is a closed subspace of
  its handle.

The Hausdorff property is an instance of the general statement for attaching cells
(`HomotopicalAlgebra.AttachCells.t2Space`): two points of `X` are separated in `P` by extending
disjoint open sets of `X` over the handles, and a point off `X` is separated from the other points
inside the handles, which are regular.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3, where the handle `Dᵏ × Dⁿ⁻ᵏ` is attached along `∂Dᵏ × Dⁿ⁻ᵏ`.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix: the radial neighbourhoods of subsets of a cell complex.
-/

public section

open CategoryTheory Limits Metric Topology

universe u

namespace TauCeti.TopCat

/-- **A handle is a disk.** The product `𝔻 k × 𝔻 l` of two closed Euclidean disks is homeomorphic
to the disk `𝔻 (k + l)`. -/
theorem nonempty_homeomorph_disk_prod_disk (k l : ℕ) :
    Nonempty (TopCat.disk.{u} k × TopCat.disk.{u} l ≃ₜ TopCat.disk.{u} (k + l)) := by
  -- The product of the two closed unit balls is the closed unit ball of the product norm, in a
  -- space of dimension `k + l`.
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + l))) := by
    simp [Module.finrank_prod]
  let e := (Homeomorph.setCongr (closedBall_prod_same (0 : EuclideanSpace ℝ (Fin k))
    (0 : EuclideanSpace ℝ (Fin l)) 1)).trans (closedBallHomeomorphOfFinrankEq hdim)
  -- The carriers of `TopCat.disk` are, by definition, the universe lifts of the closed unit balls.
  let eₖ : TopCat.disk.{u} k ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := Homeomorph.ulift
  let eₗ : TopCat.disk.{u} l ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin l)) 1 := Homeomorph.ulift
  let eₖₗ : TopCat.disk.{u} (k + l) ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (k + l))) 1 :=
    Homeomorph.ulift
  exact ⟨(eₖ.prodCongr eₗ).trans <| (Homeomorph.Set.prod _ _).symm.trans <| e.trans eₖₗ.symm⟩

/-- **Attaching handles to a Hausdorff space gives a Hausdorff space.** Let `P` be obtained from a
Hausdorff space `X` by attaching handles `𝔻 (k i) × Z i`, with each `Z i` regular and Hausdorff,
along maps `α i : ∂𝔻 (k i) × Z i ⟶ X`: a pushout in `TopCat` of `α` and the inclusion of the
attaching regions. Then `P` is Hausdorff. The family of handles may be infinite. -/
theorem t2Space_of_isPushout_handles {ι : Type u} {k : ι → ℕ} {Z : ι → Type u}
    [∀ i, TopologicalSpace (Z i)] [∀ i, T2Space (Z i)] [∀ i, RegularSpace (Z i)]
    {X P : TopCat.{u}} [T2Space X]
    {α : (∐ fun i ↦ TopCat.of (TopCat.diskBoundary.{u} (k i) × Z i)) ⟶ X} {j : X ⟶ P}
    {χ : (∐ fun i ↦ TopCat.of (TopCat.disk.{u} (k i) × Z i)) ⟶ P}
    (sq : IsPushout α (Limits.Sigma.map fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Z i)))) j χ) :
    T2Space P :=
  HomotopicalAlgebra.AttachCells.t2Space (f := j) (g := fun i ↦ TopCat.ofHom
      ((TopCat.diskBoundaryInclusion (k i)).hom.prodMap (ContinuousMap.id (Z i))))
    { ι := ι
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := coproductIsCoproduct _
      isColimit₂ := coproductIsCoproduct _
      m := _
      hm := fun i ↦ Sigma.ι_map _ i
      g₁ := α
      g₂ := χ
      isPushout := sq }
    (fun i ↦ extendsDisjointOpens_diskBoundaryInclusion_prodMap (k i) (Z i))
    (fun i ↦ (isClosedEmbedding_diskBoundaryInclusion (k i)).prodMap IsClosedEmbedding.id)

end TauCeti.TopCat
