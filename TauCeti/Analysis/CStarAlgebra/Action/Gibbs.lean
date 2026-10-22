/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.CStarAlgebra.Action.Inner
public import TauCeti.Analysis.CStarAlgebra.Action.KMS
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.LinearAlgebra.Matrix.Trace.Duality

/-!
# Gibbs states of matrix Hamiltonians

Let `K` be a Hermitian complex `m × m` matrix, the Hamiltonian of a finite quantum system, and
let `τ_t a = exp (itK) a exp (-itK)` be its time evolution, the inner dynamics
`TauCeti.CStarAction.ofSelfAdjoint` of `K` on the C⋆-algebra of complex matrices.

For a real inverse temperature `β`, the *Gibbs state* is
`x ↦ Tr (exp (-βK) x) / Tr (exp (-βK))`, `TauCeti.CStarAction.gibbsState`. It is a β-KMS state
of `τ`, `TauCeti.CStarAction.isKMSState_gibbsState`, and it is the only one: a state is β-KMS
for `τ` exactly when it is the Gibbs state, `TauCeti.CStarAction.isKMSState_iff_eq_gibbsState`.
This holds for every real `β`. At `β = 0` the Gibbs state is the normalised trace
`x ↦ Tr x / m`, `TauCeti.CStarAction.gibbsState_zero_apply`.

The matrices carry the C⋆-algebra structure of operators on Euclidean space and the order by
positive semidefiniteness, from the scoped instances `Matrix.Norms.L2Operator` and
`MatrixOrder`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, for the Gibbs state as the KMS state of a finite quantum system.
-/

public section

noncomputable section

open Complex NormedSpace
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace TauCeti.CStarAction

variable {m : Type*} [Fintype m] [DecidableEq m] {K : Matrix m m ℂ}

/-- `exp ((s + t)K) = exp (sK) exp (tK)`. -/
private theorem exp_add_smul (K : Matrix m m ℂ) (s t : ℝ) :
    exp ((s + t) • K) = exp (s • K) * exp (t • K) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl K).smul_left _).smul_right _)]

/-- `exp (βK) exp (-βK) = 1`. -/
private theorem exp_smul_mul_exp_neg_smul (K : Matrix m m ℂ) (β : ℝ) :
    exp (β • K) * exp (-β • K) = 1 := by
  rw [← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

/-- For Hermitian `K`, `exp (βK)` is Hermitian. -/
private theorem isHermitian_exp_smul (hK : K.IsHermitian) (β : ℝ) :
    (exp (β • K)).IsHermitian :=
  Matrix.IsHermitian.exp ((IsSelfAdjoint.all β).smul hK)

/-- At imaginary time `iβ` the time evolution is `τ_{iβ} b = exp (-βK) b exp (βK)`. -/
private theorem entireExtension_ofSelfAdjoint_mul_I (hK : K.IsHermitian) (b : Matrix m m ℂ)
    (β : ℝ) :
    (ofSelfAdjoint ⟨K, hK⟩).entireExtension b (β * I) = exp (-β • K) * b * exp (β • K) := by
  have h : I * (β * I) = -β := by rw [mul_left_comm, I_mul_I, mul_neg_one]
  simp only [entireExtension_ofSelfAdjoint, h, neg_neg, ← Complex.coe_smul, ofReal_neg]

/-- For Hermitian `K`, `x ↦ Tr (exp (βK) x)` is a positive functional. -/
private theorem trace_exp_smul_mul_nonneg (hK : K.IsHermitian) (β : ℝ) {x : Matrix m m ℂ}
    (hx : 0 ≤ x) : 0 ≤ (exp (β • K) * x).trace := by
  have hF : star (exp ((β / 2) • K)) = exp ((β / 2) • K) := (isHermitian_exp_smul hK _).eq
  rw [← add_halves β, exp_add_smul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  refine Matrix.PosSemidef.trace_nonneg (Matrix.nonneg_iff_posSemidef.mp ?_)
  simpa [hF, Matrix.mul_assoc] using star_left_conjugate_nonneg hx (exp ((β / 2) • K))

variable [Nonempty m]

/-- For Hermitian `K`, `Tr (exp (βK))` is positive. -/
private theorem trace_exp_smul_pos (hK : K.IsHermitian) (β : ℝ) : 0 < (exp (β • K)).trace := by
  have h := Matrix.PosDef.conjTranspose_mul_self (exp ((β / 2) • K))
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp _))
  rw [(isHermitian_exp_smul hK _).eq, ← exp_add_smul, add_halves] at h
  exact h.trace_pos

/-- The *Gibbs state* `x ↦ Tr (exp (-βK) x) / Tr (exp (-βK))` of a Hermitian matrix `K` at
inverse temperature `β`. -/
def gibbsState (K : Matrix m m ℂ) (hK : K.IsHermitian) (β : ℝ) : Matrix m m ℂ →P[ℂ] ℂ :=
  .mk₀ (LinearMap.toContinuousLinearMap ((exp (-β • K)).trace⁻¹ •
      (Matrix.traceLinearMap m ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (exp (-β • K)))))
    fun x hx => by
      simpa using mul_nonneg (inv_nonneg.mpr (trace_exp_smul_pos hK (-β)).le)
        (trace_exp_smul_mul_nonneg hK (-β) hx)

/-- The Gibbs state is `x ↦ Tr (exp (-βK) x) / Tr (exp (-βK))`. -/
@[simp]
theorem gibbsState_apply (hK : K.IsHermitian) (β : ℝ) (x : Matrix m m ℂ) :
    gibbsState K hK β x = (exp (-β • K) * x).trace / (exp (-β • K)).trace := by
  simp [gibbsState, div_eq_inv_mul]

/-- At inverse temperature `0` the Gibbs state is the normalised trace `x ↦ Tr x / m`. -/
theorem gibbsState_zero_apply (hK : K.IsHermitian) (x : Matrix m m ℂ) :
    gibbsState K hK 0 x = x.trace / Fintype.card m := by
  simp [Matrix.trace_one]

/-- **The Gibbs state is a KMS state** for the time evolution generated by a Hermitian matrix,
at every real inverse temperature. -/
theorem isKMSState_gibbsState (hK : K.IsHermitian) (β : ℝ) :
    (ofSelfAdjoint ⟨K, hK⟩).IsKMSState β (gibbsState K hK β) := by
  have htr := (trace_exp_smul_pos hK (-β)).ne'
  refine (isKMSState_iff_of_forall_isEntireAnalytic (isEntireAnalytic_ofSelfAdjoint _)).mpr
    ⟨?_, fun a b => ?_⟩
  · have h1 := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one (gibbsState K hK β)
    rw [gibbsState_apply, Matrix.mul_one, div_self htr] at h1
    exact_mod_cast h1
  rw [entireExtension_ofSelfAdjoint_mul_I, gibbsState_apply, gibbsState_apply]
  congr 1
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    exp_smul_mul_exp_neg_smul, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- **Uniqueness of the KMS state.** A state is a β-KMS state for the time evolution generated
by a Hermitian matrix `K` exactly when it is the Gibbs state, for every real `β`. -/
theorem isKMSState_iff_eq_gibbsState (hK : K.IsHermitian) (β : ℝ) {ω : Matrix m m ℂ →P[ℂ] ℂ} :
    (ofSelfAdjoint ⟨K, hK⟩).IsKMSState β ω ↔ ω = gibbsState K hK β := by
  refine ⟨fun hω => ?_, fun h => h ▸ isKMSState_gibbsState hK β⟩
  obtain ⟨hnorm, hkms⟩ :=
    (isKMSState_iff_of_forall_isEntireAnalytic (isEntireAnalytic_ofSelfAdjoint _)).mp hω
  obtain ⟨ρ, hρ, -⟩ := Matrix.existsUnique_trace_mul_eq ω.toLinearMap
  replace hρ (x : Matrix m m ℂ) : ω x = (ρ * x).trace := by simpa using hρ x
  have hinv (x : Matrix m m ℂ) : exp (β • K) * (exp (-β • K) * x) = x := by
    rw [← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.one_mul]
  have hinv' : exp (-β • K) * exp (β • K) = 1 := by
    simpa using exp_smul_mul_exp_neg_smul K (-β)
  -- the KMS identity says that `exp (βK) ρ` is central, hence scalar
  obtain ⟨c, hc⟩ := (Matrix.mem_range_scalar_iff_trace_mul_mul_comm
    (M := exp (β • K) * ρ)).mpr fun a b => by
      have := hkms (a * exp (β • K)) b
      rw [entireExtension_ofSelfAdjoint_mul_I, hρ, hρ] at this
      simp only [Matrix.mul_assoc, hinv] at this ⊢
      rw [Matrix.trace_mul_comm (exp (β • K)), Matrix.trace_mul_comm (exp (β • K))]
      simpa only [Matrix.mul_assoc] using this
  have hEρ : ρ = c • exp (-β • K) := by
    calc ρ = exp (-β • K) * exp (β • K) * ρ := by rw [hinv', Matrix.one_mul]
      _ = c • exp (-β • K) := by
        rw [Matrix.mul_assoc, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
          Matrix.mul_smul, Matrix.mul_one]
  have hω1 : ω 1 = 1 := by
    have h1 := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω
    rw [hnorm] at h1
    exact_mod_cast h1.symm
  have hc1 : c * (exp (-β • K)).trace = 1 := by
    rw [← hω1, hρ, Matrix.mul_one, hEρ, Matrix.trace_smul, smul_eq_mul]
  ext x
  rw [gibbsState_apply, hρ, hEρ, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    eq_inv_of_mul_eq_one_left hc1, div_eq_inv_mul]

end TauCeti.CStarAction
