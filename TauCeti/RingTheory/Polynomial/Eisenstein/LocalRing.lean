/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Eisenstein polynomials over local rings

Over a local ring, an Eisenstein polynomial at the maximal ideal has a unit leading coefficient.

## Main results

* `Polynomial.IsEisensteinAt.exists_monic_aeval_eq_zero`: an Eisenstein polynomial can be scaled by
  a unit to a monic Eisenstein polynomial of the same degree with the same roots.
-/

public section

open IsLocalRing

namespace Polynomial.IsEisensteinAt

variable {R : Type*} [CommSemiring R] [IsLocalRing R] {S : Type*} [Semiring S] [Algebra R S]
  {f : R[X]} {x : S}

/-- Over a local ring, an Eisenstein polynomial at the maximal ideal has a unit leading
coefficient, so scaling it by the inverse gives a monic Eisenstein polynomial of the same degree
with the same roots. -/
theorem exists_monic_aeval_eq_zero (hf : f.IsEisensteinAt (maximalIdeal R)) (hx : aeval x f = 0) :
    ∃ g : R[X], g.Monic ∧ g.IsEisensteinAt (maximalIdeal R) ∧ aeval x g = 0 ∧
      g.natDegree = f.natDegree := by
  obtain ⟨u, hu⟩ := notMem_maximalIdeal.mp hf.leading
  have hdeg : (C (↑u⁻¹ : R) * f).natDegree = f.natDegree :=
    natDegree_C_mul_eq_of_mul_eq_one u.mul_inv
  have hmo : (C (↑u⁻¹ : R) * f).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [← hu])
  refine ⟨C (↑u⁻¹ : R) * f, hmo, ⟨?_, fun {n} hn ↦ ?_, fun h ↦ hf.notMem ?_⟩, by simp [hx], hdeg⟩
  · rw [hmo.leadingCoeff]
    exact (maximalIdeal.isMaximal R).ne_top ∘ (Ideal.eq_top_iff_one _).mpr
  · rw [coeff_C_mul]
    exact Ideal.mul_mem_left _ _ (hf.mem (hdeg ▸ hn))
  · have := Ideal.mul_mem_left _ (u : R) h
    rwa [coeff_C_mul, ← mul_assoc, Units.mul_inv, one_mul] at this

end Polynomial.IsEisensteinAt
