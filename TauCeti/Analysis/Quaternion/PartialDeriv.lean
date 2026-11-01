/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Quaternion.MulMatrix

/-!
# Partial derivatives of quaternion-valued functions

Write a function `f : E → ℍ` on a real normed space as `f = K + iL + jM + kN`, with real
component functions `K = re ∘ f`, `L = imI ∘ f`, `M = imJ ∘ f` and `N = imK ∘ f`. If `f` has real
Fréchet derivative `f'` at `x`, then the derivative of each component in the direction `v` is the
corresponding coordinate of `f' v`. For `E = ℍ` and `v = 1, i, j, k`
these are the partial derivatives `∂ₜ, ∂ₓ, ∂ᵧ, ∂_z` of `K, L, M, N` in the coordinates
`q = t + i x + j y + k z`.

Combined with the component equations of `TauCeti.Algebra.Quaternion.MulMatrix`, this decides
from the sixteen partial derivatives `K_t, …, N_z` whether a real Fréchet derivative
`D : ℍ →L[ℝ] ℍ` is a left multiplication `L_a = ContinuousLinearMap.mul ℝ ℍ a`, the shape of the
derivative of a function with a right quotient derivative, or a right multiplication
`R_b = (ContinuousLinearMap.mul ℝ ℍ).flip b`, the shape of the derivative of a function with a
left quotient derivative:

```text
L_a:  K_t = L_x = M_y = N_z,  K_x = -L_t = M_z = -N_y,
      K_y = -L_z = -M_t = N_x,  K_z = L_y = -M_x = -N_t;
R_b:  K_t = L_x = M_y = N_z,  K_x = -L_t = -M_z = N_y,
      K_y = L_z = -M_t = -N_x,  K_z = -L_y = M_x = -N_t.
```

For example `q ↦ i * q` has `K = -x`, `L = t`, `M = -z`, `N = y`, satisfying the first system
and not the second (`M_z = -1` while `-K_x = 1`), and conjugation `q ↦ star q` satisfies neither,
since `K_t = 1` and `L_x = -1`.

## Main results

* `Quaternion.fderiv_re_apply`, `Quaternion.fderiv_imI_apply`, `Quaternion.fderiv_imJ_apply`,
  `Quaternion.fderiv_imK_apply`: the derivative of a component of `f` is the component of the
  derivative of `f`.
* `Quaternion.exists_eq_mul_iff_components`: a continuous real-linear map `ℍ →L[ℝ] ℍ` is a left
  multiplication exactly when its partials satisfy the first system above.
* `Quaternion.exists_eq_mul_flip_iff_components`: it is a right multiplication exactly when its
  partials satisfy the second system.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225,
  for the one-sided quotient derivatives whose real derivatives are these multiplication maps.
* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.1, for the multiplication rules.
-/

public section

namespace Quaternion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℍ} {f' : E →L[ℝ] ℍ}
  {x : E}

/-- The derivative of the real part of a quaternion-valued function is the real part of its
derivative. -/
theorem fderiv_re_apply (hf : HasFDerivAt f f' x) (v : E) :
    fderiv ℝ (fun y ↦ (f y).re) x v = (f' v).re := by
  have h : HasFDerivAt (fun y ↦ (f y).re)
      ((QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.comp f') x :=
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.hasFDerivAt.comp x hf
  simp [h.fderiv]

/-- The derivative of the `i`-component of a quaternion-valued function is the `i`-component of
its derivative. -/
theorem fderiv_imI_apply (hf : HasFDerivAt f f' x) (v : E) :
    fderiv ℝ (fun y ↦ (f y).imI) x v = (f' v).imI := by
  have h : HasFDerivAt (fun y ↦ (f y).imI)
      ((QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.comp f') x :=
    (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.hasFDerivAt.comp x hf
  simp [h.fderiv]

/-- The derivative of the `j`-component of a quaternion-valued function is the `j`-component of
its derivative. -/
theorem fderiv_imJ_apply (hf : HasFDerivAt f f' x) (v : E) :
    fderiv ℝ (fun y ↦ (f y).imJ) x v = (f' v).imJ := by
  have h : HasFDerivAt (fun y ↦ (f y).imJ)
      ((QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.comp f') x :=
    (QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.hasFDerivAt.comp x hf
  simp [h.fderiv]

/-- The derivative of the `k`-component of a quaternion-valued function is the `k`-component of
its derivative. -/
theorem fderiv_imK_apply (hf : HasFDerivAt f f' x) (v : E) :
    fderiv ℝ (fun y ↦ (f y).imK) x v = (f' v).imK := by
  have h : HasFDerivAt (fun y ↦ (f y).imK)
      ((QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.comp f') x :=
    (QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.hasFDerivAt.comp x hf
  simp [h.fderiv]

/-- A continuous real-linear map `D : ℍ →L[ℝ] ℍ` is a left multiplication
`L_a = ContinuousLinearMap.mul ℝ ℍ a` exactly when its partials satisfy
`K_t = L_x = M_y = N_z`, `K_x = -L_t = M_z = -N_y`, `K_y = -L_z = -M_t = N_x` and
`K_z = L_y = -M_x = -N_t`, where `D q = K + iL + jM + kN` and the subscripts `t, x, y, z` denote
evaluation at `1, i, j, k`. -/
theorem exists_eq_mul_iff_components {D : ℍ →L[ℝ] ℍ} :
    (∃ a, D = ContinuousLinearMap.mul ℝ ℍ a) ↔
      ((D 1).re = (D ⟨0, 1, 0, 0⟩).imI ∧ (D ⟨0, 1, 0, 0⟩).imI = (D ⟨0, 0, 1, 0⟩).imJ ∧
        (D ⟨0, 0, 1, 0⟩).imJ = (D ⟨0, 0, 0, 1⟩).imK) ∧
      ((D ⟨0, 1, 0, 0⟩).re = -(D 1).imI ∧ -(D 1).imI = (D ⟨0, 0, 0, 1⟩).imJ ∧
        (D ⟨0, 0, 0, 1⟩).imJ = -(D ⟨0, 0, 1, 0⟩).imK) ∧
      ((D ⟨0, 0, 1, 0⟩).re = -(D ⟨0, 0, 0, 1⟩).imI ∧ -(D ⟨0, 0, 0, 1⟩).imI = -(D 1).imJ ∧
        -(D 1).imJ = (D ⟨0, 1, 0, 0⟩).imK) ∧
      ((D ⟨0, 0, 0, 1⟩).re = (D ⟨0, 0, 1, 0⟩).imI ∧
        (D ⟨0, 0, 1, 0⟩).imI = -(D ⟨0, 1, 0, 0⟩).imJ ∧
        -(D ⟨0, 1, 0, 0⟩).imJ = -(D 1).imK) := by
  have h : (∃ a, D = ContinuousLinearMap.mul ℝ ℍ a) ↔
      ∃ a, (D : ℍ →ₗ[ℝ] ℍ) = LinearMap.mulLeft ℝ a := by
    simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]
  exact h.trans exists_eq_mulLeft_iff_components

/-- A continuous real-linear map `D : ℍ →L[ℝ] ℍ` is a right multiplication
`R_b = (ContinuousLinearMap.mul ℝ ℍ).flip b` exactly when its partials satisfy
`K_t = L_x = M_y = N_z`, `K_x = -L_t = -M_z = N_y`, `K_y = L_z = -M_t = -N_x` and
`K_z = -L_y = M_x = -N_t`, where `D q = K + iL + jM + kN` and the subscripts `t, x, y, z` denote
evaluation at `1, i, j, k`. -/
theorem exists_eq_mul_flip_iff_components {D : ℍ →L[ℝ] ℍ} :
    (∃ b, D = (ContinuousLinearMap.mul ℝ ℍ).flip b) ↔
      ((D 1).re = (D ⟨0, 1, 0, 0⟩).imI ∧ (D ⟨0, 1, 0, 0⟩).imI = (D ⟨0, 0, 1, 0⟩).imJ ∧
        (D ⟨0, 0, 1, 0⟩).imJ = (D ⟨0, 0, 0, 1⟩).imK) ∧
      ((D ⟨0, 1, 0, 0⟩).re = -(D 1).imI ∧ -(D 1).imI = -(D ⟨0, 0, 0, 1⟩).imJ ∧
        -(D ⟨0, 0, 0, 1⟩).imJ = (D ⟨0, 0, 1, 0⟩).imK) ∧
      ((D ⟨0, 0, 1, 0⟩).re = (D ⟨0, 0, 0, 1⟩).imI ∧ (D ⟨0, 0, 0, 1⟩).imI = -(D 1).imJ ∧
        -(D 1).imJ = -(D ⟨0, 1, 0, 0⟩).imK) ∧
      ((D ⟨0, 0, 0, 1⟩).re = -(D ⟨0, 0, 1, 0⟩).imI ∧
        -(D ⟨0, 0, 1, 0⟩).imI = (D ⟨0, 1, 0, 0⟩).imJ ∧
        (D ⟨0, 1, 0, 0⟩).imJ = -(D 1).imK) := by
  have h : (∃ b, D = (ContinuousLinearMap.mul ℝ ℍ).flip b) ↔
      ∃ b, (D : ℍ →ₗ[ℝ] ℍ) = LinearMap.mulRight ℝ b := by
    simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]
  exact h.trans exists_eq_mulRight_iff_components

end Quaternion
