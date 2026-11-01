/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.QuantumGroups.UqSl2.Basic

/-!
# Quantum traces of `U_q(sl₂)`-modules

The square of the antipode of `U_q(sl₂)` is conjugation by `K⁻¹`, so a finite-dimensional module
`V` is identified with its double dual by `v ↦ (ξ ↦ ξ(K⁻¹ v))`. The two traces of a module
endomorphism `φ` induced by this identification are the twisted traces `tr_V(K⁻¹ φ)` and
`tr_V(K φ)`. This file proves that they coincide, for every module and every module
endomorphism, as soon as `q - q⁻¹ ≠ 0`; no finiteness, genericity or semisimplicity is needed.

## Main results

* `TauCeti.UqSl2.trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp`: `tr_V(K φ) = tr_V(K⁻¹ φ)` for
  every module endomorphism `φ`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for quantum traces
  and quantum dimensions of modules over Hopf algebras.
* A. Virelizier, *Quantum groups*, Section 2.3, for the rank-one Hopf convention.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- **The two quantum traces agree.** For `q - q⁻¹ ≠ 0` and every `UqSl2 q`-linear endomorphism
`φ` of a module `V`, the traces of `K ∘ φ` and of `K⁻¹ ∘ φ` coincide. -/
theorem trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp (hq : q - q⁻¹ ≠ 0)
    (φ : V →ₗ[UqSl2 q] V) :
    LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V (k q) ∘ₗ φ.restrictScalars ℂ) =
      LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V (kInv q) ∘ₗ φ.restrictScalars ℂ) := by
  set ρ := Algebra.lsmul ℂ ℂ V (A := UqSl2 q)
  set ψ := φ.restrictScalars ℂ
  -- We show that `(K - K⁻¹) φ` is a multiple of a commutator of endomorphisms of `V`.
  -- The defining relation, transported to `V`: `K - K⁻¹ = (q - q⁻¹) [E, F]`.
  have hrel : ρ (k q) - ρ (kInv q) = (q - q⁻¹) • ⁅ρ (e q), ρ (f q)⁆ := by
    have h := congrArg ρ (e_mul_f_sub_f_mul_e (q := q))
    simp only [map_sub, map_mul, map_smul] at h
    rw [Ring.lie_def, h, smul_smul, mul_inv_cancel₀ hq, one_smul]
  -- Since `φ` commutes with `E`, `[E, F] φ = [E, F φ]`.
  have hcomm : ⁅ρ (e q), ρ (f q)⁆ * ψ = ⁅ρ (e q), ρ (f q) * ψ⁆ := by
    have hψ : ψ * ρ (e q) = ρ (e q) * ψ :=
      LinearMap.ext fun v => by simp [ρ, ψ]
    simp only [Ring.lie_def, sub_mul, mul_assoc, hψ]
  -- Hence `(K - K⁻¹) φ` is a multiple of a commutator, whose trace vanishes.
  have key : (ρ (k q) - ρ (kInv q)) * ψ = (q - q⁻¹) • ⁅ρ (e q), ρ (f q) * ψ⁆ := by
    rw [hrel, smul_mul_assoc, hcomm]
  simpa [sub_mul, Module.End.mul_eq_comp, LinearMap.trace_lie, sub_eq_zero] using
    congrArg (LinearMap.trace ℂ V) key

end TauCeti.UqSl2
