/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# The closed-orbit lemma for projective orbits

Let `O` be the orbit of a line `[m]` in the projective space `P(V)` of a finite-dimensional
representation of an affine group of finite type over an algebraically closed field `k`, that
is, the full image of the projective orbit morphism. Since `O` is locally closed, its boundary
`closure O \ O` is closed, and it is stable under every rational translation, as `O` and its
closure are.

If the spectrum of the coordinate Hopf algebra is irreducible, so is `O`, and `O` is a nonempty
open part of its irreducible closure; hence `O` and `closure O` have the same Krull dimension and
the boundary, a proper closed subset of `closure O`, has strictly smaller dimension. A closed
point of the boundary is a line `[m']`, and its whole orbit lies in the boundary: the boundary
is closed and translation invariant, and the closed points of the group are dense. Hence every
orbit of a closed point of the boundary has strictly smaller dimension than `O`. A nonempty
closed subset of the quasi-compact space `P(V)` contains a closed point, so an orbit whose
dimension is minimal among the orbits of the closed points of its closure has empty boundary,
that is, it is closed. Over an algebraically closed field, irreducibility of the group follows
from its connectedness (`CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace`).

Neither smoothness nor reducedness of the group is assumed.

## Main declarations

* `TauCeti.Comodule.isClosed_closure_diff_range_projectiveOrbitMap`: the boundary of an orbit
  is closed.
* `TauCeti.Comodule.image_projectivePointTranslation_closure_diff_range_projectiveOrbitMap`:
  the boundary of an orbit is stable under rational translations.
* `TauCeti.Comodule.isIrreducible_range_projectiveOrbitMap`: the orbit of a line under an
  irreducible group is irreducible.
* `TauCeti.Comodule.topologicalKrullDim_closure_range_projectiveOrbitMap`: an orbit and its
  closure have the same Krull dimension.
* `TauCeti.Comodule.range_projectiveOrbitMap_subset_of_isClosed`: a closed translation-invariant
  set containing a line contains its whole orbit.
* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt`: the orbit of a line in the
  boundary of `O` has strictly smaller Krull dimension than `O`.
* `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem_closure`,
  `TauCeti.Comodule.isClosed_range_projectiveOrbitMap_of_forall_mem`: an orbit of minimal
  dimension is closed.

## References

* C. Chevalley, *Classification des groupes de Lie algébriques*, Séminaire Chevalley
  1956–1958, Exposé 5, Lemme 4 and its corollary.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8, the closed orbit lemma.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
* J. S. Milne, *Algebraic Groups* (2017), §7.c, orbits and isotropy groups.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

section CommRing

variable {R H M : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [Module.Finite R M] [Module.Projective R M]

/-- The orbit of a line under an affine group with irreducible spectrum is irreducible. -/
theorem isIrreducible_range_projectiveOrbitMap [IrreducibleSpace (PrimeSpectrum H)]
    (m : M) (hm : Module.IsUnimodular R m) :
    IsIrreducible (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum H)).image _
    (projectiveOrbitMap (H := H) m hm).continuous.continuousOn

/-- Translation by every base-valued group point maps the closure of the orbit of a line onto
itself. -/
theorem image_projectivePointTranslation_closure_range_projectiveOrbitMap
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m) :
    (projectivePointTranslation (M := M) g).hom ''
        closure (Set.range (projectiveOrbitMap (H := H) m hm)) =
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have he : ⇑(Scheme.homeoOfIso (projectivePointTranslation (M := M) g)) =
      (projectivePointTranslation (M := M) g).hom :=
    funext (Scheme.homeoOfIso_apply _)
  rw [← he, Homeomorph.image_closure, he,
    image_projectivePointTranslation_range_projectiveOrbitMap]

/-- Translation by every base-valued group point maps the boundary `closure O \ O` of the orbit
`O` of a line onto itself. -/
theorem image_projectivePointTranslation_closure_diff_range_projectiveOrbitMap
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : Module.IsUnimodular R m) :
    (projectivePointTranslation (M := M) g).hom ''
        (closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
          Set.range (projectiveOrbitMap (H := H) m hm)) =
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm) := by
  rw [Set.image_sdiff (f := (projectivePointTranslation (M := M) g).hom)
      (Scheme.homeoOfIso (projectivePointTranslation (M := M) g)).injective,
    image_projectivePointTranslation_closure_range_projectiveOrbitMap,
    image_projectivePointTranslation_range_projectiveOrbitMap]

end CommRing

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- The boundary `closure O \ O` of the orbit `O` of a line is closed, because the orbit is
locally closed. -/
theorem isClosed_closure_diff_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m) :
    IsClosed (closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
      Set.range (projectiveOrbitMap (H := H) m hm)) :=
  isOpen_compl_iff.mp (isLocallyClosed_range_projectiveOrbitMap (H := H) m hm).isOpen_coborder

/-- If the spectrum of the group is irreducible, the orbit of a line has the Krull dimension of
its closure: it is a nonempty open part of its irreducible closure. -/
theorem topologicalKrullDim_closure_range_projectiveOrbitMap [IrreducibleSpace (PrimeSpectrum H)]
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (closure (Set.range (projectiveOrbitMap (H := H) m hm))) =
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have hO := isLocallyClosed_range_projectiveOrbitMap (H := H) m hm
  have h := TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType
    (SymmetricAlgebra.projToSpec k (Module.Dual k M))
    (isIrreducible_range_projectiveOrbitMap m hm).closure isClosed_closure hO.isOpen_coborder
    ⟨_, subset_closure ⟨AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩,
      subset_coborder ⟨AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩⟩
  rwa [Set.inter_comm, coborder_inter_closure, eq_comm] at h

/-- If the spectrum of the group is irreducible, the boundary `closure O \ O` of the orbit `O`
of a line has strictly smaller Krull dimension than `O`. -/
theorem topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt
    [IrreducibleSpace (PrimeSpectrum H)] (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim ↥(closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) <
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have hdim := topologicalKrullDim_closure_range_projectiveOrbitMap (H := H) m hm
  rw [← hdim]
  refine (isIrreducible_range_projectiveOrbitMap m hm).closure.topologicalKrullDim_lt
    (isClosed_closure_diff_range_projectiveOrbitMap m hm)
    (Set.sdiff_ssubset_left_iff.mpr ?_)
    (hdim ▸ topologicalKrullDim_range_projectiveOrbitMap_ne_top m hm)
  exact ⟨_, subset_closure ⟨AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩,
    AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩

/-- A closed subset of projective space that is stable under all rational translations and
contains a line `[m]` contains the whole orbit of `[m]`, including its nonclosed points. -/
theorem range_projectiveOrbitMap_subset_of_isClosed (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z) (hZg : ∀ g : WithConv (H →ₐ[k] k),
      (projectivePointTranslation (M := M) g).hom '' Z ⊆ Z)
    (hmZ : projectiveOrbitMap (H := H) m hm
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z) :
    Set.range (projectiveOrbitMap (H := H) m hm) ⊆ Z := by
  have := isJacobsonRing_of_finiteType (A := k) (B := H)
  -- The closed points of the group are its rational points, whose images are translates of
  -- `[m]`; they are dense, and the preimage of `Z` is closed.
  have hpts : closedPoints (Spec (.of H)) ⊆ projectiveOrbitMap (H := H) m hm ⁻¹' Z := by
    rw [← range_kernelPoint_eq_closedPoints (k := k) (A := H)]
    rintro _ ⟨g, rfl⟩
    have h := hZg (toConv g) ⟨_, hmZ, rfl⟩
    have h1 : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := by
      simp [AlgHom.convOne_def]
    rwa [← h1, projectivePointTranslation_projectiveOrbitMap_kernelPoint, mul_one] at h
  have hcl := closure_minimal hpts (hZ.preimage (projectiveOrbitMap (H := H) m hm).continuous)
  rw [closure_closedPoints] at hcl
  rintro _ ⟨x, rfl⟩
  exact hcl (Set.mem_univ x)

/-- **Boundary orbits are smaller.** If the spectrum of the group is irreducible and the line
`[m']` lies in the boundary `closure O \ O` of the orbit `O` of `[m]`, then the orbit of `[m']`
has strictly smaller Krull dimension than `O`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_lt [IrreducibleSpace (PrimeSpectrum H)]
    {m m' : M} (hm : Module.IsUnimodular k m) (hm' : Module.IsUnimodular k m')
    (hm'O : projectiveOrbitMap (H := H) m' hm'
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m' hm')) <
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  refine lt_of_le_of_lt ?_ (topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt m hm)
  exact (Topology.IsEmbedding.inclusion (range_projectiveOrbitMap_subset_of_isClosed m' hm'
    (isClosed_closure_diff_range_projectiveOrbitMap m hm)
    (fun g ↦ (image_projectivePointTranslation_closure_diff_range_projectiveOrbitMap g m hm).le)
    hm'O)).isInducing.topologicalKrullDim_le

/-- **Closed-orbit lemma.** If the spectrum of the group is irreducible and the orbit `O` of a
line has minimal Krull dimension among the orbits of the lines in its closure, then `O` is
closed. -/
theorem isClosed_range_projectiveOrbitMap_of_forall_mem_closure
    [IrreducibleSpace (PrimeSpectrum H)] (m : M) (hm : Module.IsUnimodular k m)
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

/-- **Closed-orbit lemma**, relative form. If the spectrum of the group is irreducible and the
orbit `O` of a line lies in a closed subset `Z` of projective space and has minimal Krull
dimension among the orbits of the lines in `Z`, then `O` is closed. -/
theorem isClosed_range_projectiveOrbitMap_of_forall_mem [IrreducibleSpace (PrimeSpectrum H)]
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

end TauCeti.Comodule
