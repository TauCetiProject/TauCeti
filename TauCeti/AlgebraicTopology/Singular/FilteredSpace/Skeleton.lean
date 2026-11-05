/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Exhaustive
public import TauCeti.AlgebraicTopology.Cellular.Homology
public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# The filtration by preimages of skeleta

Let `C` be a relative CW complex in a Hausdorff space `B`, with base `D`, and let `f : E → B` be a
map. The preimages `E_q = f⁻¹(C^(q))` of the skeleta of `C` form an increasing filtration of `E`
(`TauCeti.preimageSkeleton`, monotone by `TauCeti.monotone_preimageSkeleton`). Here the
`q`-skeleton `C^(q)` is `skeletonLT C (q + 1)`, the union of `D` and the cells of dimension at most
`q`, so `E_q = f⁻¹(D)` for `q < 0` (`TauCeti.preimageSkeleton_of_neg`), and `E_{-1} = ∅` when `C`
is an absolute CW complex (`TauCeti.preimageSkeleton_eq_empty`). For a Serre fibration
`f : E → B` over a CW complex `B` this is the filtration whose spectral sequence is the Serre
spectral sequence. These topological statements live in
`TauCeti.Topology.CWComplex.Classical.Skeleton.Basic` and
`TauCeti.Topology.CWComplex.Classical.CompactSupport`; this file adds the homological applications.

If `f` is continuous with values in `C`, the filtration absorbs every compact subset of `E`
(`TauCeti.exists_subset_preimageSkeleton_of_isCompact`), since the image of a compact set lies in a
finite skeleton; no finiteness or dimension bound is imposed on `C`. So the convergence theorems for
exhaustive filtrations of spaces apply. If the relative homology `Hₙ(E_{i+1}, E_i)`, which lives
over the `(i + 1)`-cells, vanishes whenever `n ≤ i`, then on every late enough page the object at
`(p, q)` is the graded piece `F_{q+1} H / F_q H` of `H_{-(p+q)}(E)`
(`TauCeti.preimageSkeletonSpectralSequencePageXIsoGraded`). For a Serre fibration this vanishing
says that the first page is concentrated in nonnegative fibre degrees.

For the identity of a CW complex the filtration is the skeletal filtration, and the vanishing holds
by the computation of the homology of consecutive skeleta
(`TauCeti.isZero_singularHomology_preimageSkeleton_id`).

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1, the filtration of a total space by the preimages of the skeleta of the base.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
* A. Hatcher, *Algebraic Topology*, Proposition A.1 (compact subsets of CW complexes).
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] [T2Space B] {E : TopCat.{w}}

section Absolute

variable {C : Set B} [CWComplex C]

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- **Convergence of the spectral sequence of the skeletal filtration.** Let `f : E → B` be a
continuous map with values in a CW complex `C`, with no finiteness or dimension bound on `C`, and
filter `E` by the preimages `E_q` of the skeleta. Suppose that `Hₙ(E_{i+1}, E_i) = 0` whenever
`n ≤ i`. Then on every page `r ≥ 2` with `q + 3 ≤ r` and `2 - p - 2q ≤ r`, the object at `(p, q)`
is the graded piece `F_{q+1} H / F_q H` of the filtration of the abutment in degree `p + q`, which
is `H_{-(p+q)}(E)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def preimageSkeletonSpectralSequencePageXIsoGraded {f : E → B} (hf : Continuous f)
    (hfC : Set.range f ⊆ C)
    (hvanish : ∀ (i : ℤ) (n : ℕ), n ≤ i →
      IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton f (Int.le_add_one le_rfl) :
        preimageSkeleton C f i ⊆ preimageSkeleton C f (i + 1))).singularHomology M n))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 + 3 ≤ r) (hrb : 2 - pq.1 - 2 * pq.2 ≤ r) :
    ((filteredSpaceSpectralSequence M (monotone_preimageSkeleton (C := C) f)).page r).X pq ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          (monotone_singularChainFiltration M (monotone_preimageSkeleton (C := C) f))))
        pq.2 (pq.1 + pq.2)) :=
  filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive M _
    (fun _ hK ↦ exists_subset_preimageSkeleton_of_isCompact hf hfC hK)
    (preimageSkeleton_eq_empty f (by lia : (-1 : ℤ) < 0)) r hr pq (by lia)
    fun i hi n hn ↦ hvanish i n (by lia)

end Absolute

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- The filtration of a CW complex by its own skeleta satisfies the vanishing hypothesis of
`TauCeti.preimageSkeletonSpectralSequencePageXIsoGraded`: `Hₙ(X^(i+1), X^(i)) = 0` for `n ≤ i`. -/
theorem isZero_singularHomology_preimageSkeleton_id [CWComplex (Set.univ : Set B)] (i : ℤ) (n : ℕ)
    (hn : n ≤ i) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (E := TopCat.of B) id
      (Int.le_add_one le_rfl) : preimageSkeleton Set.univ id i ⊆
        preimageSkeleton Set.univ id (i + 1))).singularHomology M n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ i)
  refine (TopPair.isZero_singularHomology_ofInclusion_congr M _
    (skeletonLT_subset_skeletonLT_succ (Set.univ : Set B) (m + 1)) ?_ ?_ n).2
    (isZero_singularHomology_skeletonPair_of_ne _ M (by lia))
  all_goals
    rw [preimageSkeleton, Set.preimage_id]
    congr 2

end TauCeti
