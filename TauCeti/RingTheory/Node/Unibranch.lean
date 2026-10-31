/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Unibranch
public import TauCeti.RingTheory.Node.Branches
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The split node is not unibranch

Over a domain `R`, the local ring of the split node `xy = 0` at its origin is not unibranch: the
two coordinates multiply to zero and neither is nilpotent, so the reduction of the local ring is
not a domain. Geometrically, the two branches `x = 0` and `y = 0` both pass through
the origin.

The non-nilpotence is detected on the two branches: the restriction of a coordinate to its own
branch is the branch parameter, and an element outside the origin has nonzero value at the
origin of each branch.

## Main results

* `TauCeti.NodeAlgebra.not_isUnibranch_localization_ker_origin`: the local ring of the split node
  at the origin is not unibranch.

## References

* [Stacks Project, Definition 15.108.1](https://stacks.math.columbia.edu/tag/0BPZ)
-/

public section

namespace TauCeti.NodeAlgebra

open Polynomial

variable (R : Type*) [CommRing R] [IsDomain R]

/-- In the local ring of the split node at the origin, neither coordinate is nilpotent. -/
theorem not_isNilpotent_algebraMap_coord (i : Fin 2) :
    ¬ IsNilpotent (algebraMap (NodeAlgebra R 0)
      (Localization.AtPrime (RingHom.ker (origin R).toRingHom)) (coord (0 : R) i)) := by
  rintro ⟨n, hn⟩
  rw [← map_pow, IsLocalization.map_eq_zero_iff (RingHom.ker (origin R).toRingHom).primeCompl]
    at hn
  obtain ⟨⟨s, hs⟩, hs0⟩ := hn
  refine hs (RingHom.mem_ker.mpr ?_)
  have hval := AlgHom.congr_fun (branchValues_comp_branchMap R) s
  have hzero := congrArg (branchMap R) hs0
  simp only [AlgHom.comp_apply, Algebra.ofId_apply, branchValues_apply, Prod.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Prod.mk.injEq] at hval
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, map_mul, map_pow,
    branchMap_coord_zero, branchMap_coord_one, Prod.ext_iff] at hzero
  · have h1 : (branchMap R s).1 = 0 := by simpa [X_ne_zero] using hzero.1
    simp [← hval.1, h1]
  · have h2 : (branchMap R s).2 = 0 := by simpa [X_ne_zero] using hzero.2
    simp [← hval.2, h2]

/-- The local ring of the split node `xy = 0` over a domain at its origin is not unibranch: its
reduction is not a domain, since the two coordinates multiply to zero and neither is nilpotent.
-/
theorem not_isUnibranch_localization_ker_origin :
    ¬ IsLocalRing.IsUnibranch (Localization.AtPrime (RingHom.ker (origin R).toRingHom)) := by
  intro h
  have := h.isDomain
  set L := Localization.AtPrime (RingHom.ker (origin R).toRingHom)
  have hmul : Ideal.Quotient.mk (nilradical L) (algebraMap _ L (coord (0 : R) 0)) *
      Ideal.Quotient.mk (nilradical L) (algebraMap _ L (coord (0 : R) 1)) = 0 := by
    rw [← map_mul, ← map_mul, coord_zero_mul_coord_one, map_zero, map_zero, map_zero]
  rcases mul_eq_zero.mp hmul with h0 | h1
  · exact not_isNilpotent_algebraMap_coord R 0 (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  · exact not_isNilpotent_algebraMap_coord R 1 (Ideal.Quotient.eq_zero_iff_mem.mp h1)

end TauCeti.NodeAlgebra
