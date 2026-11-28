/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Length
public import TauCeti.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.Artinian.FiniteLength

/-!
# Finite length on the support of a module

A finite module over a Noetherian ring has finite length precisely when its support has
dimension at most zero. Localizing at a minimal prime of its support therefore gives a
finite length, the multiplicity of that irreducible component in the module cycle.
See [Stacks Project, Section 42.10](https://stacks.math.columbia.edu/tag/02QV).
-/

public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Module.Finite R M]

/-- A finite module over a Noetherian ring has finite length exactly when its support has
dimension at most zero. This includes the zero module, whose support is empty. -/
theorem isFiniteLength_iff_supportDim_le_zero : IsFiniteLength R M ↔ supportDim R M ≤ 0 := by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator, ← Nat.cast_zero (R := WithBot ℕ∞),
    ← Ring.krullDimLE_iff,
    ← isArtinianRing_iff_krullDimLE_zero (R := R ⧸ annihilator R M)]
  refine ⟨TauCeti.isArtinianRing_quotient_annihilator, fun h ↦ ?_⟩
  let _ := quotientAnnihilator (R := R) (M := M)
  have : Module.Finite (R ⧸ annihilator R M) M := .of_restrictScalars_finite R _ M
  rw [← length_ne_top_iff, length_eq_of_surjective (R := R ⧸ annihilator R M)
    Ideal.Quotient.mk_surjective]
  exact length_ne_top

/-- At a minimal prime of its support a finite module has finite length over the local ring. -/
theorem isFiniteLength_localizedModule_of_mem_minimalPrimes {p : Ideal R}
    (hp : p ∈ (annihilator R M).minimalPrimes) :
    let _ := hp.isPrime
    IsFiniteLength (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  intro hpPrime
  exact isFiniteLength_iff_supportDim_le_zero.2
    ((supportDim_localizedModule_nonpos_iff hp.1.2).2 hp)

/-- Under a finite bound on the support dimension, all local lengths in that dimension are
finite, including the zero lengths off the support. -/
theorem isFiniteLength_localizedModule_of_ringKrullDim_quotient_eq {d : ℕ}
    (hM : supportDim R M ≤ d) {p : PrimeSpectrum R} (hd : ringKrullDim (R ⧸ p.asIdeal) = d) :
    IsFiniteLength (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  by_cases hp : p ∈ support R M
  · exact isFiniteLength_localizedModule_of_mem_minimalPrimes
      (mem_minimalPrimes_annihilator_of_ringKrullDim_quotient_eq hM hp hd)
  · have := notMem_support_iff.mp hp
    simp [← length_ne_top_iff]

end Module
