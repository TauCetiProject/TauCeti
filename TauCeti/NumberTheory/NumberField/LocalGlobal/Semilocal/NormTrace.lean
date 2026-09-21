/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# Norm and trace in the semilocal decomposition

The semilocal decomposition transports the norm and trace of a number-field extension to the
finite family of completed extensions above a finite place.  The generic determinant, trace, and
finite-product calculations live in `TauCeti.RingTheory.NormTrace.Pi`.
-/

public section

namespace TauCeti

open IsDedekindDomain NumberField Module

open scoped TensorProduct NumberField AdicCompletionExtension Valued BigOperators

universe u v

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type u} [Field K] [NumberField K]
variable (L : Type v) [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝒪 K))

attribute [local instance] Fintype.ofFinite in
/-- The norm of a number-field element is the product of its norms in the completions above `v`. -/
theorem algebraMap_norm_eq_prod_norm (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.1.adicCompletion L) x) := by
  calc
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
        Algebra.norm (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] x) :=
      (Algebra.norm_baseChange_tmul (A := v.adicCompletion K) (B := L) x).symm
    _ = Algebra.norm (v.adicCompletion K)
        (semilocalEquiv L v ((1 : v.adicCompletion K) ⊗ₜ[K] x)) := by
      symm
      exact Algebra.norm_eq_of_algEquiv (semilocalEquiv L v) _
    _ = ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K)
        (semilocalEquiv L v ((1 : v.adicCompletion K) ⊗ₜ[K] x) w) :=
      Algebra.norm_pi _
    _ = ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.1.adicCompletion L) x) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [semilocalEquiv_tmul]
      simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of a number-field element is the sum of its traces in the completions above `v`. -/
theorem algebraMap_trace_eq_sum_trace (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
  calc
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
        Algebra.trace (v.adicCompletion K) (TensorProduct K (v.adicCompletion K) L)
          ((1 : v.adicCompletion K) ⊗ₜ[K] x) :=
      (Algebra.trace_baseChange_tmul (A := v.adicCompletion K) (B := L) x).symm
    _ = Algebra.trace (v.adicCompletion K)
        ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
          w.1.adicCompletion L)
        (semilocalEquiv L v ((1 : v.adicCompletion K) ⊗ₜ[K] x)) := by
      symm
      exact Algebra.trace_eq_of_algEquiv (semilocalEquiv L v) _
    _ = ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (semilocalEquiv L v ((1 : v.adicCompletion K) ⊗ₜ[K] x) w) :=
      Algebra.trace_pi _
    _ = ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [semilocalEquiv_tmul]
      simp

end TauCeti
