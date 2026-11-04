/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.Topology.KrullDimension.Basic

/-!
# Krull dimension of projective orbits

The projective orbit scheme of a line is a locally closed subscheme of projective space whose
underlying set is the orbit, the full image of the projective orbit morphism. Since an
immersion is a homeomorphism onto its image, the orbit scheme and the orbit have the same Krull
dimension. The orbit has finite Krull dimension because projective space over a field is
quasi-compact and of finite type. Only finite-dimensionality of the representation is needed
for the latter. A locally closed subset of a finite-type scheme has the dimension of its
closure, and its boundary has strictly smaller dimension if the subset is nonempty.
Thus these orbit dimension statements apply also to disconnected groups.

## Main declarations

* `TauCeti.Comodule.topologicalKrullDim_projectiveOrbitScheme`: the orbit scheme has the Krull
  dimension of the orbit.
* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_ne_top` and
  `TauCeti.Comodule.exists_topologicalKrullDim_range_projectiveOrbitMap_eq_natCast`: the orbit
  has finite Krull dimension, a natural number.
* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_one_le_finrank`: the orbit
  of a line in `M` has Krull dimension at most `dim M - 1`.
* `TauCeti.Comodule.topologicalKrullDim_closure_range_projectiveOrbitMap`: the orbit of a line
  has the Krull dimension of its closure.
* `TauCeti.Comodule.topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt`: its boundary
  has strictly smaller Krull dimension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

section Range

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The orbit of a line, the image of its projective orbit morphism, has finite Krull
dimension. No finiteness or algebraic closedness hypothesis is needed beyond finite
dimensionality of the representation. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_ne_top
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) ≠ ⊤ :=
  ne_top_of_le_ne_top (TauCeti.AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType
    (SymmetricAlgebra.projToSpec k (Module.Dual k M))) (topologicalKrullDim_subspace_le _ _)

/-- The orbit of a line has the Krull dimension of a natural number: it is finite, and it is not
`⊥` because the orbit is nonempty. -/
theorem exists_topologicalKrullDim_range_projectiveOrbitMap_eq_natCast
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ n : ℕ, topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) = n := by
  have : Nonempty (Set.range (projectiveOrbitMap (H := H) m hm)) :=
    ⟨⟨_, Set.mem_range_self (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))⟩⟩
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    ((WithBot.bot_lt_coe _).trans_le (TauCeti.coheight_le_topologicalKrullDim
      (Classical.arbitrary (Set.range (projectiveOrbitMap (H := H) m hm))))).ne'
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (show d ≠ ⊤ by
    rintro rfl; exact topologicalKrullDim_range_projectiveOrbitMap_ne_top (H := H) m hm hd.symm)
  exact ⟨n, hd.symm⟩

/-- **Orbits have dimension at most that of the projective space.** The orbit of a line in `M`
has Krull dimension at most `dim M - 1`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_one_le_finrank
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) + 1 ≤
      Module.finrank k M := by
  grw [topologicalKrullDim_subspace_le]
  exact (SymmetricAlgebra.topologicalKrullDim_proj_add_one_le_finrank (Module.Dual k M) k).trans_eq
    (by rw [Subspace.dual_finrank_eq])

end Range

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- The projective orbit scheme of a line has the Krull dimension of the orbit. -/
theorem topologicalKrullDim_projectiveOrbitScheme (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (projectiveOrbitScheme (H := H) m hm) =
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  rw [← range_projectiveOrbitι,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_range_of_isPreimmersion]

/-- The orbit of a line has the Krull dimension of its closure, including for disconnected
groups. -/
theorem topologicalKrullDim_closure_range_projectiveOrbitMap
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (closure (Set.range (projectiveOrbitMap (H := H) m hm))) =
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  exact TauCeti.AlgebraicGeometry.topologicalKrullDim_closure_of_isLocallyClosed
    (SymmetricAlgebra.projToSpec k (Module.Dual k M))
    (isLocallyClosed_range_projectiveOrbitMap m hm)

/-- The boundary `closure O \ O` of the orbit `O` of a line has strictly smaller Krull
dimension than `O`, including for disconnected groups. -/
theorem topologicalKrullDim_closure_diff_range_projectiveOrbitMap_lt
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim ↥(closure (Set.range (projectiveOrbitMap (H := H) m hm)) \
        Set.range (projectiveOrbitMap (H := H) m hm)) <
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  exact TauCeti.AlgebraicGeometry.topologicalKrullDim_closure_sdiff_lt_of_isLocallyClosed
    (SymmetricAlgebra.projToSpec k (Module.Dual k M))
    (isLocallyClosed_range_projectiveOrbitMap m hm)
    ⟨_, AlgHom.kernelPoint (Bialgebra.counitAlgHom k H), rfl⟩

end TauCeti.Comodule
