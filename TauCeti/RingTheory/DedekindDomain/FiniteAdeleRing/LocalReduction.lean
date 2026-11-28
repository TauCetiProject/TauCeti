/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# Reduction of integral finite adeles at a place

Project an integral finite adele to the local integers at a finite place and reduce to their
residue field. The reduction kills every completed ideal whose underlying ideal lies in the
prime of the place, so it can be used on entries of matrices subject to a congruence condition.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Reduction of an integral finite adele to the residue field at `w`. -/
noncomputable def integralAdelesResidue (w : HeightOneSpectrum R) :
    integralAdeles R K →+* IsLocalRing.ResidueField (w.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp
    (((proj K w).toAlgHom.toRingHom.comp (integralAdeles R K).val).codRestrict
      (w.adicCompletionIntegers K).toSubring fun x ↦ by
        have hproj : (proj K w).toAlgHom.toRingHom ((integralAdeles R K).val x) =
            (x : FiniteAdeleRing R K) w := proj_apply w (x : FiniteAdeleRing R K)
        exact hproj.symm ▸ mem_integralAdeles.mp x.property w)

/-- Reduction is the residue of the integral component at `w`. -/
theorem integralAdelesResidue_apply (w : HeightOneSpectrum R) (x : integralAdeles R K) :
    w.integralAdelesResidue x = IsLocalRing.residue (w.adicCompletionIntegers K)
      ⟨(x : FiniteAdeleRing R K) w, mem_integralAdeles.mp x.property w⟩ := by
  rw [integralAdelesResidue, RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  exact proj_apply w (x : FiniteAdeleRing R K)

/-- A completed ideal coming from an ideal contained in the prime of `w` reduces to zero. -/
theorem integralAdelesResidue_eq_zero_of_mem_completedIdeal (w : HeightOneSpectrum R)
    {I : Ideal R} (hI : I ≤ w.asIdeal) {x : integralAdeles R K} (hx : x ∈ completedIdeal K I) :
    w.integralAdelesResidue x = 0 := by
  rw [integralAdelesResidue_apply, IsLocalRing.residue_eq_zero_iff,
    ← pow_one (IsLocalRing.maximalIdeal _), mem_maximalIdeal_pow_iff]
  exact valued_le_of_mem_completedIdeal (v := w) (k := 1) (by simpa using hI) hx

end IsDedekindDomain.HeightOneSpectrum
