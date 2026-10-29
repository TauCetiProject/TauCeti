/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Boundary
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension

/-!
# The closed-orbit lemma for projective orbits

Let `O` be the orbit of a line `[m]` in the projective space `P(V)` of a finite-dimensional
representation of an affine group of finite type over an algebraically closed field `k`, that
is, the full image of the projective orbit morphism. Since `O` is locally closed, its boundary
`closure O \ O` is closed (`TauCeti.Comodule.isClosed_closure_diff_range_projectiveOrbitMap`, in
`ProjectiveOrbit/LocallyClosed.lean`).

The boundary has strictly smaller Krull dimension than `O`, including when the group is
disconnected (`TauCeti.Comodule.topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt`, in
`ProjectiveOrbit/Dimension.lean`). The orbit of
a line `[m']` in the boundary lies in the boundary
(`TauCeti.Comodule.closure_range_projectiveOrbitMap_subset_boundary`, in
`ProjectiveOrbit/Boundary.lean`), so it has strictly smaller dimension than `O`. A nonempty
closed subset of the quasi-compact space `P(V)` contains a closed point, which is a line, so an
orbit whose dimension is minimal among the orbits of the lines in its closure has empty boundary,
that is, it is closed. By induction on the dimension, the closure of every orbit contains a
closed orbit.

Neither connectedness, smoothness nor reducedness of the group is assumed.

## Main declarations

* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt`: the orbit of a line in the
  boundary of `O` has strictly smaller Krull dimension than `O`.
* `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem_closure`,
  `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem`: an orbit of minimal
  dimension is closed.
* `TauCeti.Comodule.exists_isClosed_range_projectiveOrbitMap_subset_closure`: the closure of
  every orbit contains a closed orbit.

## References

* C. Chevalley, *Classification des groupes de Lie algébriques*, Séminaire Chevalley
  1956–1958, Exposé 5, Lemme 4 and its corollary.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8, the closed orbit lemma.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
* J. S. Milne, *Algebraic Groups* (2017), §7.c, orbits and isotropy groups.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- **Boundary orbits are smaller.** If the line `[m']` lies in the boundary `closure O \ O` of
the orbit `O` of `[m]`, then the orbit of `[m']` has strictly smaller Krull dimension than `O`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_lt
    {m m' : M} (hm : Module.IsUnimodular k m) (hm' : Module.IsUnimodular k m')
    (hm'O : projectiveOrbitMap (H := H) m' hm'
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m' hm')) <
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  -- The orbit of `[m']` lies in the boundary, which is smaller than `O`.
  refine lt_of_le_of_lt ?_ (topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt m hm)
  exact (Topology.IsEmbedding.inclusion (subset_closure.trans
    (closure_range_projectiveOrbitMap_subset_boundary m hm m' hm' hm'O))).isInducing
    |>.topologicalKrullDim_le

/-- **Closed-orbit lemma.** If the orbit `O` of a line has minimal Krull dimension among the
orbits of the lines in its closure, then `O` is closed. -/
theorem isClosed_range_projectiveOrbitMap_of_forall_mem_closure
    (m : M) (hm : Module.IsUnimodular k m)
    (hmin : ∀ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
          closure (Set.range (projectiveOrbitMap (H := H) m hm)) →
        topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) ≤
          topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m' hm'))) :
    IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  refine closure_subset_iff_isClosed.mp (Set.sdiff_eq_empty.mp ?_)
  by_contra hne
  -- A nonempty closed subset of projective space contains a closed point, which is a line.
  obtain ⟨y, hy, hyc⟩ :=
    (isClosed_closure_diff_range_projectiveOrbitMap m hm).exists_closed_singleton
      (Set.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨m', hm', rfl⟩ :=
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) y).mp hyc
  exact (hmin m' hm' hy.1).not_gt (topologicalKrullDim_range_projectiveOrbitMap_lt hm hm' hy)

/-- **Closed-orbit lemma**, relative form. If the orbit `O` of a line lies in a closed subset `Z`
of projective space and has minimal Krull dimension among the orbits of the lines in `Z`, then
`O` is closed. -/
theorem isClosed_range_projectiveOrbitMap_of_forall_mem
    (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z) (hmZ : Set.range (projectiveOrbitMap (H := H) m hm) ⊆ Z)
    (hmin : ∀ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z →
        topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) ≤
          topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m' hm'))) :
    IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) :=
  isClosed_range_projectiveOrbitMap_of_forall_mem_closure m hm fun m' hm' h ↦
    hmin m' hm' (closure_minimal hmZ hZ h)

/-- **Existence of closed orbits.** The closure of the orbit of every line contains a closed
orbit of a line. -/
theorem exists_isClosed_range_projectiveOrbitMap_subset_closure
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m' hm')) ∧
        Set.range (projectiveOrbitMap (H := H) m' hm') ⊆
          closure (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  obtain ⟨d, hd⟩ : ∃ d, topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) = d :=
    ⟨_, rfl⟩
  -- Induction on the Krull dimension of the orbit: a nonclosed orbit has a line in its boundary,
  -- and the orbit of that line is smaller and lies in the boundary.
  induction d using WellFoundedLT.induction generalizing m with
  | ind d ih =>
  by_cases hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))
  · exact ⟨m, hm, hclosed, subset_closure⟩
  -- A nonempty closed subset of projective space contains a closed point, which is a line.
  obtain ⟨y, hy, hyc⟩ :=
    (isClosed_closure_diff_range_projectiveOrbitMap m hm).exists_closed_singleton
      (Set.sdiff_nonempty.mpr (mt closure_subset_iff_isClosed.mp hclosed))
  obtain ⟨m', hm', rfl⟩ :=
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) y).mp hyc
  obtain ⟨n, hn, hnclosed, hnsub⟩ :=
    ih _ (hd ▸ topologicalKrullDim_range_projectiveOrbitMap_lt hm hm' hy) m' hm' rfl
  exact ⟨n, hn, hnclosed, hnsub.trans
    ((closure_range_projectiveOrbitMap_subset_boundary m hm m' hm' hy).trans Set.sdiff_subset)⟩

/-- Every nonempty closed subset of projective space invariant under rational group
translations contains a closed orbit. -/
theorem exists_isClosed_range_projectiveOrbitMap_subset_of_isClosed
    {Z : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z) (hne : Z.Nonempty)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z) :
    ∃ (m : M) (hm : Module.IsUnimodular k m),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) ∧
        Set.range (projectiveOrbitMap (H := H) m hm) ⊆ Z := by
  obtain ⟨x, hx, hxc⟩ := hZ.exists_closed_singleton hne
  obtain ⟨m, hm, rfl⟩ :=
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) x).mp hxc
  have horbit := (range_projectiveOrbitMap_subset_iff_of_isClosed m hm hZ hinvariant).mpr hx
  obtain ⟨n, hn, hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_closure (H := H) m hm
  exact ⟨n, hn, hclosed, hsub.trans (closure_minimal horbit hZ)⟩

end TauCeti.Comodule
