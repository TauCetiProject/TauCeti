/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DiscBundle.Basic
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.VectorBundle.Thom.Space
import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# Cell structures of Thom spaces

Let `E → B` be a real vector bundle of rank `r` over a Hausdorff CW complex `B`, with
finite-dimensional model fibre and fibre inner products whose norm is continuous on the total
space. The unit disc bundle `D(E)` is a CW complex relative to the unit sphere bundle `S(E)`, with
one `(m + r)`-cell for each `m`-cell of `B` (`TauCeti.relCWComplexDiscBundleSphereBundle`, the
case of an absolute CW complex in `TauCeti.relCWComplexDiscBundle`).

Gluing `S(E)` to a point (whose skeleta contain everything in positive dimensions, so the attaching
map is cellular via `CategoryTheory.IsPushout.cwComplexOfMapsToSkeletonLT`), the Thom space
`Th(E) = D(E)/S(E)` (`TauCeti.thomSpace`) acquires a CW complex structure with one `0`-cell, the
basepoint, and one `(m + r)`-cell for each `m`-cell of `B` (`TauCeti.thomSpaceCWComplex`,
`TauCeti.thomSpaceCWComplexCellEquiv`). It is finite when `B` is
(`TauCeti.finite_thomSpaceCWComplex`). In rank zero the cells are those of `B` together with the
basepoint, matching `TauCeti.thomSpaceHomeomorphOfSubsingleton`.

No orientation of `E` is used.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cell structure of the Thom space of a bundle over a
  CW complex).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (disc bundles and Thom spaces).
-/

public section

noncomputable section

open Bundle Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] [CWComplex (univ : Set B)]

section ThomSpace

/-- **The Thom space of a bundle over a CW complex is a CW complex.** If `B` is a CW complex, the
Thom space `Th(E) = D(E)/S(E)` is a CW complex with one `0`-cell, the basepoint, and one
`(m + r)`-cell for each `m`-cell of `B`, where `r` is the rank of the bundle
(`TauCeti.thomSpaceCWComplexCellEquiv`). -/
@[instance_reducible]
def thomSpaceCWComplex : CWComplex (univ : Set (thomSpace F E)) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT
    (mem_skeletonLT_univ_of_mem_cellFrontier _)

/-- The `n`-cells of the Thom space are the `n`-cells of the point, a single `0`-cell for the
basepoint, together with the `m`-cells of `B` with `m + r = n`, where `r` is the rank of the
bundle. -/
def thomSpaceCWComplexCellEquiv (n : ℕ) :
    letI := thomSpaceCWComplex F E
    cell (univ : Set (thomSpace F E)) n ≃
      cell (univ : Set PUnit.{u + 1}) n ⊕
        Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSphereBundle F E
  ((isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLTCellEquiv
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n).trans
      (Equiv.sumCongr (.refl _) (relCWComplexDiscBundleSphereBundleCellEquiv F E n))

/-- The cell of the point in the Thom space is the basepoint. -/
@[simp]
theorem thomSpaceCWComplex_map_inl {n : ℕ} (c : cell (univ : Set PUnit.{u + 1}) n)
    (x : Fin n → ℝ) :
    letI := thomSpaceCWComplex F E
    map n ((thomSpaceCWComplexCellEquiv F E n).symm (.inl c)) x = thomSpaceBasepoint F E :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT_map_inl
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n c x

/-- The characteristic map of the cell of the Thom space over an `m`-cell of `B` is the
characteristic map of the corresponding cell of the disc bundle, followed by the collapse map
`D(E) → Th(E)`. -/
@[simp]
theorem thomSpaceCWComplex_map_inr {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := thomSpaceCWComplex F E
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((thomSpaceCWComplexCellEquiv F E n).symm (.inr c)) x =
      thomSpaceπ F E ⟨map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x,
        closedCell_subset_complex n _ (mem_image_of_mem _ x.property)⟩ :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).cwComplexOfMapsToSkeletonLT_map_inr
    (mem_skeletonLT_univ_of_mem_cellFrontier _) n _ x

/-- The Thom space of a bundle over a finite CW complex is a finite CW complex. -/
theorem finite_thomSpaceCWComplex [RelCWComplex.Finite (univ : Set B)] :
    letI := thomSpaceCWComplex F E
    RelCWComplex.Finite (univ : Set (thomSpace F E)) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  haveI := finite_relCWComplexDiscBundleSphereBundle F E
  (isPushout_thomSpace F E).finite_cwComplexOfMapsToSkeletonLT
    (mem_skeletonLT_univ_of_mem_cellFrontier _)

end ThomSpace

end TauCeti
