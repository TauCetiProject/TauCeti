/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Trace.TransposeMul

/-!
# Newtonian stress and its contractions

For a velocity gradient `A` (a real square matrix), a pressure `p` and a constant real viscosity
`μ`, this file develops the pointwise linear algebra of a Newtonian fluid
(Kim–Karrila, *Microhydrodynamics*, §1.2):

* the strain rate, or symmetric gradient, `e(A) = (A + Aᵀ)/2`, which is the symmetric part
  `TauCeti.PDE.coefficientSymmetricPart A`;
* the Newtonian stress `σ(A,p) = -p I + 2μ e(A) = μ (A + Aᵀ) - p I`
  (`TauCeti.Stokes.newtonianStress`);
* the traction `σ(A,p) n` on a surface with normal `n`, spelled `newtonianStress μ p A *ᵥ n`.
  Its linearity in the normal and its sign under normal reversal are Mathlib's
  `Matrix.mulVec_add`, `Matrix.mulVec_smul` and `Matrix.mulVec_neg`.

Contractions are spelled with the trace pairing `A : B = tr (Aᵀ * B)`, whose general properties
live in `TauCeti.LinearAlgebra.Matrix.Trace.TransposeMul`. The central identity is the pairing
`σ(A,p) : B = 2μ e(A) : e(B) - p tr B` (`TauCeti.Stokes.trace_transpose_newtonianStress_mul`).
It yields the reciprocal contraction `σ(A,p) : B - σ(B,q) : A = -p tr B + q tr A`, and for
trace-free `A` the dissipative contraction `σ(A,p) : A = 2μ e(A) : e(A)`. These are the pointwise
identities behind the Lorentz reciprocal theorem and the work–dissipation identity of Stokes flow
(Kim–Karrila, §2.2–2.3). They hold for every real `μ` and every finite index type; only
nonnegativity of the dissipative contraction uses `0 ≤ μ`.

Finally, the stress and the traction are covariant under an orthogonal change of frame
`A ↦ O A Oᵀ`, `n ↦ O n`, with no condition on `det O`, so reflections are included. The
corresponding facts for the strain rate and the trace pairing are
`TauCeti.PDE.coefficientSymmetricPart_mul_mul_transpose` and
`Matrix.trace_transpose_mul_of_transpose_mul_eq_one`.

## References

* Sangtae Kim and Seppo J. Karrila, *Microhydrodynamics: Principles and Selected Applications*,
  Butterworth–Heinemann, 1991, §1.2 and §2.2–2.3.
-/

public section

open Matrix TauCeti.PDE

namespace TauCeti.Stokes

variable {n : Type*} [DecidableEq n]

/-! ### Newtonian stress -/

/-- The Newtonian stress `σ(A,p) = μ (A + Aᵀ) - p I = -p I + 2μ e(A)` with viscosity `μ`,
pressure `p` and velocity gradient `A`. -/
noncomputable def newtonianStress (μ p : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  μ • (A + Aᵀ) - p • 1

theorem newtonianStress_def (μ p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ p A = μ • (A + Aᵀ) - p • 1 := (rfl)

/-- The entries of the Newtonian stress: `σᵢⱼ = μ (Aᵢⱼ + Aⱼᵢ) - p δᵢⱼ`. -/
@[simp]
theorem newtonianStress_apply (μ p : ℝ) (A : Matrix n n ℝ) (i j : n) :
    newtonianStress μ p A i j = μ * (A i j + A j i) - if i = j then p else 0 := by
  simp [newtonianStress_def, Matrix.one_apply, mul_ite, mul_add]

/-- The Newtonian stress is `-p I + 2μ e(A)`, for the strain rate `e(A)` of `A`. -/
theorem newtonianStress_eq_coefficientSymmetricPart (μ p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ p A = (2 * μ) • coefficientSymmetricPart A - p • 1 := by
  rw [newtonianStress_def, coefficientSymmetricPart_def, smul_smul, mul_one_div,
    mul_div_cancel_left₀ μ two_ne_zero]

/-- The Newtonian stress depends on the velocity gradient only through its strain rate. -/
@[simp]
theorem newtonianStress_coefficientSymmetricPart (μ p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ p (coefficientSymmetricPart A) = newtonianStress μ p A := by
  rw [newtonianStress_eq_coefficientSymmetricPart,
    coefficientSymmetricPart_eq_self_of_isSymm (coefficientSymmetricPart_isSymm A),
    newtonianStress_eq_coefficientSymmetricPart]

@[simp]
theorem newtonianStress_transpose (μ p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ p Aᵀ = newtonianStress μ p A := by
  rw [newtonianStress_def, newtonianStress_def, transpose_transpose, add_comm]

theorem isSymm_newtonianStress (μ p : ℝ) (A : Matrix n n ℝ) :
    (newtonianStress μ p A).IsSymm :=
  ((isSymm_add_transpose_self A).smul μ).sub (isSymm_one.smul p)

@[simp]
theorem transpose_newtonianStress (μ p : ℝ) (A : Matrix n n ℝ) :
    (newtonianStress μ p A)ᵀ = newtonianStress μ p A :=
  (isSymm_newtonianStress μ p A).eq

/-- A skew-symmetric velocity gradient, an infinitesimal rigid rotation, carries the purely
isotropic stress `-p I`. -/
theorem newtonianStress_of_transpose_eq_neg (μ p : ℝ) {A : Matrix n n ℝ} (hA : Aᵀ = -A) :
    newtonianStress μ p A = -(p • 1) := by
  rw [newtonianStress_def, hA, add_neg_cancel, smul_zero, zero_sub]

/-- Linearity of the stress in the pair `(p, A)`: additivity. -/
theorem newtonianStress_add (μ p q : ℝ) (A B : Matrix n n ℝ) :
    newtonianStress μ (p + q) (A + B) = newtonianStress μ p A + newtonianStress μ q B := by
  simp only [newtonianStress_def, transpose_add, add_smul, smul_add]
  abel

/-- Linearity of the stress in the pair `(p, A)`: homogeneity. -/
theorem newtonianStress_smul (μ c p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ (c * p) (c • A) = c • newtonianStress μ p A := by
  simp only [newtonianStress_def, transpose_smul, ← smul_add, smul_sub, smul_smul, mul_comm c μ]

@[simp]
theorem newtonianStress_zero (μ : ℝ) : newtonianStress μ 0 (0 : Matrix n n ℝ) = 0 := by
  simp [newtonianStress_def]

/-- Linearity of the stress in the pair `(p, A)`: finite superposition. -/
theorem newtonianStress_sum {ι : Type*} (s : Finset ι) (μ : ℝ) (p : ι → ℝ)
    (A : ι → Matrix n n ℝ) :
    newtonianStress μ (∑ a ∈ s, p a) (∑ a ∈ s, A a) = ∑ a ∈ s, newtonianStress μ (p a) (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      newtonianStress_add, ih]

/-- Shifting the pressure by a constant `c` shifts the stress by `-c I`. -/
theorem newtonianStress_add_pressure (μ p c : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ (p + c) A = newtonianStress μ p A - c • 1 := by
  rw [newtonianStress_def, newtonianStress_def, add_smul, sub_add_eq_sub_sub]

theorem trace_newtonianStress [Fintype n] (μ p : ℝ) (A : Matrix n n ℝ) :
    (newtonianStress μ p A).trace = 2 * μ * A.trace - p * Fintype.card n := by
  simp [newtonianStress_def, trace_sub, trace_add, trace_smul, trace_transpose, trace_one]
  ring

/-! ### Traction -/

/-- The traction `σ(A,p) n = μ (A n + Aᵀ n) - p n` on a surface with normal `n`. -/
theorem newtonianStress_mulVec [Fintype n] (μ p : ℝ) (A : Matrix n n ℝ) (ν : n → ℝ) :
    newtonianStress μ p A *ᵥ ν = μ • (A *ᵥ ν + Aᵀ *ᵥ ν) - p • ν := by
  rw [newtonianStress_def, sub_mulVec, smul_mulVec, add_mulVec, smul_mulVec, one_mulVec]

/-- The coordinates of the traction: `(σ n)ᵢ = μ ∑ⱼ (Aᵢⱼ + Aⱼᵢ) nⱼ - p nᵢ`. -/
theorem newtonianStress_mulVec_apply [Fintype n] (μ p : ℝ) (A : Matrix n n ℝ) (ν : n → ℝ)
    (i : n) :
    (newtonianStress μ p A *ᵥ ν) i = μ * ∑ j, (A i j + A j i) * ν j - p * ν i := by
  rw [newtonianStress_mulVec]
  simp [mulVec, dotProduct, add_mul, mul_add, Finset.sum_add_distrib]

/-! ### Contractions -/

/-- The pairing identity `σ(A,p) : B = 2μ e(A) : e(B) - p tr B`, for arbitrary matrices `A` and
`B`. -/
theorem trace_transpose_newtonianStress_mul [Fintype n] (μ p : ℝ) (A B : Matrix n n ℝ) :
    ((newtonianStress μ p A)ᵀ * B).trace =
      2 * μ * ((coefficientSymmetricPart A)ᵀ * coefficientSymmetricPart B).trace -
        p * B.trace := by
  have hBt : (A * Bᵀ).trace = (Aᵀ * B).trace := by
    simpa using (trace_transpose_mul A Bᵀ).symm
  rw [transpose_newtonianStress, (coefficientSymmetricPart_isSymm A).eq, newtonianStress_def,
    coefficientSymmetricPart_def, coefficientSymmetricPart_def]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, trace_sub, trace_smul, trace_add, trace_transpose_mul, hBt, smul_eq_mul]
  ring

/-- **Reciprocal contraction.** For arbitrary matrices `A`, `B`, pressures `p`, `q` and real
viscosity `μ`, `σ(A,p) : B - σ(B,q) : A = -p tr B + q tr A`. -/
theorem trace_transpose_newtonianStress_mul_sub [Fintype n] (μ p q : ℝ) (A B : Matrix n n ℝ) :
    ((newtonianStress μ p A)ᵀ * B).trace - ((newtonianStress μ q B)ᵀ * A).trace =
      -p * B.trace + q * A.trace := by
  rw [trace_transpose_newtonianStress_mul, trace_transpose_newtonianStress_mul,
    trace_transpose_mul_comm (coefficientSymmetricPart B)]
  ring

/-- Reciprocal contraction for trace-free gradients: `σ(A,p) : B = σ(B,q) : A`. -/
theorem trace_transpose_newtonianStress_mul_eq_of_trace_eq_zero [Fintype n] (μ p q : ℝ)
    {A B : Matrix n n ℝ} (hA : A.trace = 0) (hB : B.trace = 0) :
    ((newtonianStress μ p A)ᵀ * B).trace = ((newtonianStress μ q B)ᵀ * A).trace := by
  rw [← sub_eq_zero, trace_transpose_newtonianStress_mul_sub, hA, hB]
  ring

/-- **Dissipative contraction.** For a trace-free gradient `A`, `σ(A,p) : A = 2μ e(A) : e(A)`,
whatever the pressure. -/
theorem trace_transpose_newtonianStress_mul_of_trace_eq_zero [Fintype n] (μ p : ℝ)
    {A : Matrix n n ℝ} (hA : A.trace = 0) :
    ((newtonianStress μ p A)ᵀ * A).trace =
      2 * μ * ((coefficientSymmetricPart A)ᵀ * coefficientSymmetricPart A).trace := by
  rw [trace_transpose_newtonianStress_mul, hA, mul_zero, sub_zero]

/-- For nonnegative viscosity the dissipative contraction `σ(A,p) : A` of a trace-free gradient
is nonnegative. -/
theorem trace_transpose_newtonianStress_mul_nonneg_of_trace_eq_zero [Fintype n] {μ : ℝ}
    (hμ : 0 ≤ μ) (p : ℝ) {A : Matrix n n ℝ} (hA : A.trace = 0) :
    0 ≤ ((newtonianStress μ p A)ᵀ * A).trace := by
  rw [trace_transpose_newtonianStress_mul_of_trace_eq_zero μ p hA]
  exact mul_nonneg (mul_nonneg zero_le_two hμ) (trace_transpose_mul_self_nonneg _)

/-! ### Orthogonal covariance -/

/-- The Newtonian stress is covariant under an orthogonal change of frame `A ↦ O A Oᵀ`. -/
theorem newtonianStress_mul_mul_transpose [Fintype n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) (μ p : ℝ) (A : Matrix n n ℝ) :
    newtonianStress μ p (O * A * Oᵀ) = O * newtonianStress μ p A * Oᵀ := by
  simp [newtonianStress_eq_coefficientSymmetricPart, coefficientSymmetricPart_mul_mul_transpose,
    Matrix.mul_sub, Matrix.sub_mul, (mem_orthogonalGroup_iff n ℝ).mp hO]

/-- The traction is covariant under an orthogonal change of frame: the stress of `O A Oᵀ` on the
normal `O n` is `O` applied to the traction `σ(A,p) n`. -/
theorem newtonianStress_mul_mul_transpose_mulVec [Fintype n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) (μ p : ℝ) (A : Matrix n n ℝ) (ν : n → ℝ) :
    newtonianStress μ p (O * A * Oᵀ) *ᵥ (O *ᵥ ν) = O *ᵥ (newtonianStress μ p A *ᵥ ν) := by
  rw [newtonianStress_mul_mul_transpose hO, mulVec_mulVec, Matrix.mul_assoc, mulVec_mulVec,
    (mem_orthogonalGroup_iff' n ℝ).mp hO, Matrix.mul_one]

end TauCeti.Stokes
