/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Boundary
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension

/-!
# The closure relation between projective orbits

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, acting
on a finite-dimensional representation `M`. For lines `[m]` and `[n]` in `P(M)` with orbits `Oₘ`
and `Oₙ`, the full topological images of the projective orbit morphisms, this file compares
`Oₙ` with the closure of `Oₘ`:

* `Oₙ ⊆ closure Oₘ` exactly when the line `[n]` lies in `closure Oₘ`, because the closure is closed
  and invariant under rational translations;
* if `[n]` lies in `closure Oₘ`, then `dim Oₙ ≤ dim Oₘ`, with equality only when `Oₙ = Oₘ`;
* consequently, if each of `[m]` and `[n]` lies in the closure of the orbit of the other, the two
  orbits coincide.

These are the reflexivity, transitivity and antisymmetry inputs for the closure order on orbits,
in which `O ≤ O'` means `O ⊆ closure O'`. Neither connectedness, smoothness nor reducedness of the
group is assumed.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- The orbit of the line `[n]` lies in the closure of the orbit of `[m]` exactly when the line
`[n]` itself does. -/
theorem range_projectiveOrbitMap_subset_closure_iff
    (m : M) (hm : Module.IsUnimodular k m) (n : M) (hn : Module.IsUnimodular k n) :
    Set.range (projectiveOrbitMap (H := H) n hn) ⊆
        closure (Set.range (projectiveOrbitMap (H := H) m hm)) ↔
      projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) m hm)) :=
  range_projectiveOrbitMap_subset_iff_of_isClosed n hn isClosed_closure fun g ↦
    Set.mapsTo_iff_image_subset.mpr
      (image_projectivePointTranslation_closure_range_projectiveOrbitMap g m hm).subset

/-- The closure of the orbit of the line `[n]` lies in the closure of the orbit of `[m]` exactly
when the line `[n]` lies in the closure of the orbit of `[m]`. -/
theorem closure_range_projectiveOrbitMap_subset_closure_iff
    (m : M) (hm : Module.IsUnimodular k m) (n : M) (hn : Module.IsUnimodular k n) :
    closure (Set.range (projectiveOrbitMap (H := H) n hn)) ⊆
        closure (Set.range (projectiveOrbitMap (H := H) m hm)) ↔
      projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) m hm)) :=
  isClosed_closure.closure_subset_iff.trans (range_projectiveOrbitMap_subset_closure_iff m hm n hn)

/-- An orbit whose line lies in the closure of another orbit has at most its Krull dimension. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_le_of_mem_closure
    {m : M} (hm : Module.IsUnimodular k m) {n : M} (hn : Module.IsUnimodular k n)
    (hnm : projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm))) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) n hn)) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  rw [← topologicalKrullDim_closure_range_projectiveOrbitMap m hm]
  exact (Topology.IsEmbedding.inclusion ((range_projectiveOrbitMap_subset_closure_iff
    m hm n hn).mpr hnm)).isInducing.topologicalKrullDim_le

/-- **An orbit in the closure of an orbit of no larger dimension is that orbit.** If the line
`[n]` lies in the closure of the orbit of `[m]` and `dim Oₘ ≤ dim Oₙ`, then `Oₙ = Oₘ`. -/
theorem range_projectiveOrbitMap_eq_of_mem_closure_of_le
    {m : M} (hm : Module.IsUnimodular k m) {n : M} (hn : Module.IsUnimodular k n)
    (hnm : projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)))
    (hdim : topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) n hn))) :
    Set.range (projectiveOrbitMap (H := H) n hn) =
      Set.range (projectiveOrbitMap (H := H) m hm) := by
  refine (range_projectiveOrbitMap_eq_iff m hm n hn).mpr ?_
  by_contra h
  exact (topologicalKrullDim_range_projectiveOrbitMap_lt hm hn ⟨hnm, h⟩).not_ge hdim

/-- **Antisymmetry of the closure relation.** If each of the lines `[m]` and `[n]` lies in the
closure of the orbit of the other, the two orbits coincide. -/
theorem range_projectiveOrbitMap_eq_of_mem_closure_of_mem_closure
    {m : M} (hm : Module.IsUnimodular k m) {n : M} (hn : Module.IsUnimodular k n)
    (hnm : projectiveOrbitMap (H := H) n hn (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)))
    (hmn : projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) n hn))) :
    Set.range (projectiveOrbitMap (H := H) n hn) =
      Set.range (projectiveOrbitMap (H := H) m hm) :=
  range_projectiveOrbitMap_eq_of_mem_closure_of_le hm hn hnm
    (topologicalKrullDim_range_projectiveOrbitMap_le_of_mem_closure hn hm hmn)

end TauCeti.Comodule
