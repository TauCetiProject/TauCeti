/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers
public import TauCeti.RingTheory.NormTrace.Pi
public import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Norm and trace in the semilocal decomposition

The semilocal decomposition transports the norm and trace of a number-field extension to the
finite family of completed extensions above a finite place.  The generic determinant, trace, and
finite-product calculations live in `TauCeti.RingTheory.NormTrace.Pi`.  The scalar-extension
identities are from `TauCeti.RingTheory.NormTrace.BaseChange`.

## Main results

* `TauCeti.norm_eq_prod_norm_semilocalEquiv` and `TauCeti.trace_eq_sum_trace_semilocalEquiv`: the
  norm and trace of `K_v ⊗[K] L` over `K_v` are the product and sum of those of the components of
  the semilocal decomposition.
* `TauCeti.algebraMap_norm_eq_prod_norm` and `TauCeti.algebraMap_trace_eq_sum_trace`: the norm
  and trace of `x ∈ L` are the product and sum of the local norms and traces of `x`.
* `TauCeti.trace_semilocalEquiv_symm_single_mul`: the trace pairing of one semilocal component
  with a global element is its local trace pairing.
* `TauCeti.trace_integralSemilocalToField_tmul_mul`: the trace pairing of an integral pure tensor
  with a global element commutes with extension to the completed field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, (8.4).
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

/-- The trace of a pure integral tensor paired with a global element is a scalar extension of
the global trace pairing. -/
theorem trace_integralSemilocalToField_tmul_mul
    (a : v.adicCompletionIntegers K) (x : 𝒪 L) (d : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (integralSemilocalToField L v (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : v.adicCompletion K) *
        algebraMap K (v.adicCompletion K) (Algebra.trace K L ((x : L) * d)) := by
  have ha : (a : v.adicCompletion K) ⊗ₜ[K] ((x : L) * d) =
      (a : v.adicCompletion K) • ((1 : v.adicCompletion K) ⊗ₜ[K] ((x : L) * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul]

attribute [local instance] Fintype.ofFinite in
/-- The norm of the semilocal algebra `K_v ⊗[K] L` over `K_v` is the product of the norms of the
components of the semilocal decomposition. -/
@[simp] theorem norm_eq_prod_norm_semilocalEquiv (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.norm (v.adicCompletion K) ξ =
      ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (semilocalEquiv L v ξ w) := by
  rw [← Algebra.norm_eq_of_algEquiv (semilocalEquiv L v)]
  exact Algebra.norm_pi _

attribute [local instance] Fintype.ofFinite in
/-- The norm of a number-field element is the product of its norms in the completions above `v`. -/
theorem algebraMap_norm_eq_prod_norm (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← Algebra.norm_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    norm_eq_prod_norm_semilocalEquiv]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [semilocalEquiv_tmul]
  simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of the semilocal algebra `K_v ⊗[K] L` over `K_v` is the sum of the traces of the
components of the semilocal decomposition. -/
@[simp] theorem trace_eq_sum_trace_semilocalEquiv (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) ξ =
      ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) (semilocalEquiv L v ξ w) := by
  rw [← Algebra.trace_eq_of_algEquiv (semilocalEquiv L v)]
  exact Algebra.trace_pi _

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
/-- An element of `L_w`, placed in the `w`-component of `K_v ⊗[K] L`, has the same trace pairing
with a global element as in `L_w`. -/
theorem trace_semilocalEquiv_symm_single_mul
    (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]
    (z : w.adicCompletion L) (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((semilocalEquiv L v).symm (Pi.single (⟨w, inferInstance⟩ :
          {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) z) * (1 ⊗ₜ x)) =
      Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) x) := by
  classical
  rw [trace_eq_sum_trace_semilocalEquiv, Finset.sum_eq_single
    (⟨w, inferInstance⟩ : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal})]
  · simp [semilocalEquiv_tmul]
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of a number-field element is the sum of its traces in the completions above `v`. -/
theorem algebraMap_trace_eq_sum_trace (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← Algebra.trace_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    trace_eq_sum_trace_semilocalEquiv]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [semilocalEquiv_tmul]
  simp

end TauCeti
