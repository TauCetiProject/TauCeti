/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic

/-!
# Quantum traces of `U_q(sl₂)`-modules

The square of the antipode of `U_q(sl₂)` is conjugation by `K⁻¹`, so a finite-dimensional module
`V` is identified with its double dual by `v ↦ (ξ ↦ ξ(K⁻¹ v))`. The two traces of a module
endomorphism `φ` induced by this identification are the twisted traces `tr_V(K⁻¹ φ)` and
`tr_V(K φ)`. This file proves that they coincide, for every module and every module
endomorphism, as soon as `q - q⁻¹ ≠ 0`; no finiteness, genericity or semisimplicity is needed.

The proof is a commutator computation. The defining relation gives
`K - K⁻¹ = (q - q⁻¹)(EF - FE)` on `V`, and since `φ` commutes with `E`,
`(EF - FE) φ = E (F φ) - (F φ) E` is the commutator of the endomorphisms `E` and `F φ`, whose
trace vanishes.

Applied to the identity of the signed ladder module `L_m^ε`, this shows that its two quantum
dimensions both equal `ε [m + 1]_q`.

## Main results

* `TauCeti.UqSl2.trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp`: `tr_V(K φ) = tr_V(K⁻¹ φ)` for
  every module endomorphism `φ`.
* `TauCeti.UqSl2.LadderModule.trace_rep_k`: the trace of `K` on `L_m^ε` is `ε [m + 1]_q`.

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
  -- The defining relation, multiplied out: `K - K⁻¹ = (q - q⁻¹) [E, F]`.
  have hrel : ρ (k q) - ρ (kInv q) = (q - q⁻¹) • ⁅ρ (e q), ρ (f q)⁆ := by
    rw [Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, ← map_sub, ← map_smul,
      e_mul_f_sub_f_mul_e, smul_smul, mul_inv_cancel₀ hq, one_smul]
  -- Since `φ` commutes with `E`, `[E, F] φ = [E, F φ]`.
  have hcomm : ⁅ρ (e q), ρ (f q)⁆ * ψ = ⁅ρ (e q), ρ (f q) * ψ⁆ := by
    have hψ : ψ * ρ (e q) = ρ (e q) * ψ :=
      LinearMap.ext fun v => by simp [ρ, ψ]
    rw [Ring.lie_def, Ring.lie_def, sub_mul, mul_assoc, mul_assoc, mul_assoc, hψ]
  rw [← sub_eq_zero, ← map_sub, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← sub_mul,
    hrel, smul_mul_assoc, hcomm, map_smul, LinearMap.trace_lie, smul_zero]

namespace LadderModule

variable [Fact (q ≠ 0)] {m : ℕ} {ε : ℤˣ}

/-- The trace of `K` on `L_m^ε` is `ε [m + 1]_q`, the same as the trace of `K⁻¹`. -/
theorem trace_rep_k (hq : q - q⁻¹ ≠ 0) :
    LinearMap.trace ℂ _ (rep q m ε (k q)) = ε * quantumInteger q ((m : ℤ) + 1) := by
  have hrep (a : UqSl2 q) : rep q m ε a = Algebra.lsmul ℂ ℂ (LadderModule q m ε) a :=
    LinearMap.ext fun x => by rw [Algebra.lsmul_coe]; exact (smul_def a x).symm
  have h := trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp hq
    (LinearMap.id : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q m ε)
  rw [LinearMap.restrictScalars_id, LinearMap.comp_id, LinearMap.comp_id, ← hrep, ← hrep] at h
  rw [h, trace_rep_kInv hq]

end LadderModule

end TauCeti.UqSl2
