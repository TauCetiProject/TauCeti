/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.OneParameter.Smooth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth vectors of representations of the real line: checks

Checks for `ContRepresentation.isLieSmoothVector_iff_isSmoothVector_toSemigroup`.

* For `π(t)v = eᵗv` on `ℂ`, the orbit maps are smooth although `‖π(t)‖ = eᵗ` is unbounded, so
  every vector is smooth in both senses: the semigroup smooth vectors are everything.
* For the trivial representation every orbit is constant, so again every vector is smooth in both
  senses.

## Main declarations

* `TauCeti.OneParameterSmoothChecks.expRep`: the representation `π(t)v = eᵗv` of `ℝ` on `ℂ`.
* `TauCeti.OneParameterSmoothChecks.isLieSmoothVector_expRep`: every vector is Lie-smooth for it.
* `TauCeti.OneParameterSmoothChecks.continuous_expRep_apply`: its orbit maps are continuous.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), §2.
-/

public noncomputable section

open ContRepresentation TauCeti.Semigroups
open scoped ContDiff Manifold

namespace TauCeti.OneParameterSmoothChecks

/-- The representation `π(t)v = eᵗv` of `(ℝ, +)` on `ℂ`. -/
def expRep : ContRepresentation ℂ (Multiplicative ℝ) ℂ :=
  .ofMonoidHom
    { toFun g := algebraMap ℂ (ℂ →L[ℂ] ℂ) (Real.exp g.toAdd)
      map_one' := by simp
      map_mul' g h := by rw [toAdd_mul, Real.exp_add, Complex.ofReal_mul, map_mul] }

/-- The representation `π(t)v = eᵗv` multiplies by `eᵗ`. -/
theorem expRep_apply (g : Multiplicative ℝ) (v : ℂ) : expRep g v = Real.exp g.toAdd * v :=
  (rfl)

/-- Every vector is Lie-smooth for `π(t)v = eᵗv`: its orbit `t ↦ eᵗv` is smooth. -/
theorem isLieSmoothVector_expRep (v : ℂ) : IsLieSmoothVector 𝓘(ℝ) expRep v := by
  rw [isLieSmoothVector_iff_contDiff]
  simp only [expRep_apply, toAdd_ofAdd]
  exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const

/-- The orbit maps of `π(t)v = eᵗv` are continuous. -/
theorem continuous_expRep_apply (v : ℂ) : Continuous fun g => expRep g v :=
  ((isLieSmoothVector_iff_contDiff expRep v).mp (isLieSmoothVector_expRep v)).continuous

/-- For `π(t)v = eᵗv`, every vector is a smooth vector of the forward semigroup. -/
example : (expRep.toStronglyContinuousGroup continuous_expRep_apply).toSemigroup.smoothVectors =
    ⊤ := by
  rw [← restrictScalars_lieSmoothVectors_eq_smoothVectors, eq_top_iff]
  intro v _
  rw [Submodule.restrictScalars_mem, mem_lieSmoothVectors]
  exact isLieSmoothVector_expRep v

/-- For the trivial representation of `ℝ` on `ℂ`, every vector is a smooth vector of the forward
semigroup, since every orbit is constant. -/
example (hπ : ∀ v, Continuous fun g => trivial ℂ (Multiplicative ℝ) ℂ g v) :
    ((trivial ℂ (Multiplicative ℝ) ℂ).toStronglyContinuousGroup hπ).toSemigroup.smoothVectors =
      ⊤ := by
  rw [← restrictScalars_lieSmoothVectors_eq_smoothVectors, eq_top_iff]
  intro v _
  rw [Submodule.restrictScalars_mem, mem_lieSmoothVectors, isLieSmoothVector_iff_contDiff]
  simpa only [trivial_apply] using contDiff_const

end TauCeti.OneParameterSmoothChecks
