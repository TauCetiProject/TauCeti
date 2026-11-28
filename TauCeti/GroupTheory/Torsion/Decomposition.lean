/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.GroupTheory.Torsion

import TauCeti.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Primary decomposition of torsion abelian groups

A torsion abelian group is the internal direct sum of its primary components indexed by the
natural primes. The proof transports the primary decomposition of torsion modules over the
integers along the equivalence between the height-one prime ideals of `ℤ` and natural primes.

## Main results

* `IsAddTorsion.primaryComponent_isInternal`: a torsion abelian group is the internal direct sum
  of its primary components indexed by the natural primes.

## References

* L. Fuchs, *Abelian Groups* (2015), Chapter 4, Theorem 3.1, pp. 140–141.
-/

public section

namespace TauCeti

/-- A torsion abelian group is the internal direct sum of its prime-primary components. -/
theorem _root_.IsAddTorsion.primaryComponent_isInternal {A : Type*} [AddCommGroup A]
    [DecidableEq Nat.Primes] (hA : IsAddTorsion A) :
    DirectSum.IsInternal
      (fun p : Nat.Primes ↦ (AddCommGroup.primaryComponent A p).toIntSubmodule) := by
  classical
  let e := Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext n
    simp
  have hgen (p : Nat.Primes) : Ideal.span {(p : ℤ)} = (e.symm p).asIdeal := by
    have hpr := congrArg Subtype.val (e.apply_symm_apply p)
    -- The prime underlying `e v` is the natural generator of the ideal.
    change Rat.HeightOneSpectrum.natGenerator (e.symm p) = (p : ℕ) at hpr
    have h := Rat.HeightOneSpectrum.span_natGenerator (e.symm p)
    rw [hpr, he] at h
    -- Display the ring homomorphism of the identity equivalence for `Ideal.map_id`.
    change Ideal.span {(p : ℤ)} = Ideal.map (RingHom.id ℤ) _ at h
    simpa only [Ideal.map_id] using h
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · simp only [primaryComponent_toIntSubmodule_eq, hgen]
    exact (Ideal.iSupIndep_primaryComponent ℤ A).comp e.symm.injective
  · simp only [primaryComponent_toIntSubmodule_eq, hgen]
    exact (e.symm.surjective.iSup_comp
      (fun P : IsDedekindDomain.HeightOneSpectrum ℤ ↦ P.asIdeal.primaryComponent A)).trans
      (Ideal.iSup_primaryComponent_eq_top (isAddTorsion_iff_isTorsion_int.mp hA))

end TauCeti
