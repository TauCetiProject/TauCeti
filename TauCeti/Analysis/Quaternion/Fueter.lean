/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The left and right Fueter operators

Write a quaternion as `q = t + i x + j y + k z`. For a function `f : ℍ → ℍ`, the left and right
Cauchy–Riemann–Fueter operators are
```text
∂̄ₗ f = ∂ₜf + i * ∂ₓf + j * ∂ᵧf + k * ∂_zf,      ∂̄ᵣ f = ∂ₜf + ∂ₓf * i + ∂ᵧf * j + ∂_zf * k,
```
and `f` is *left* (respectively *right*) *Fueter regular* where the corresponding operator
vanishes. Since `ℍ` is not commutative these are different conditions, and the order of every
product is part of the statement.

When `f` has real Fréchet derivative `D` at `q`, the four partial derivatives are
`D 1, D i, D j, D k`. We therefore define the operators on real-linear maps, as the linear maps
`TauCeti.fueterLeft, TauCeti.fueterRight : (ℍ →L[ℝ] ℍ) →ₗ[ℝ] ℍ`, and call `f` left Fueter regular
at `q` when it has *some* real derivative `D` at `q` with `fueterLeft D = 0`. Only the existence
of the derivative at the point is assumed; no continuity of the derivative is required.

The class of Fueter regular functions is much larger than the class of functions with a
one-sided quaternionic difference quotient. A function whose real derivative is right
multiplication `h ↦ h * b` is left regular only when `b = 0`, since `fueterLeft` of that map is
`-2 * b`; whereas every holomorphic function of `t + i x` is regular on both sides.

## Main declarations

* `TauCeti.fueterLeft`, `TauCeti.fueterRight`: the Fueter operators on real-linear maps.
* `TauCeti.LeftFueterAt`, `TauCeti.RightFueterAt`: pointwise Fueter regularity.
* `TauCeti.LeftFueterOn`, `TauCeti.RightFueterOn`: Fueter regularity at every point of a set.
* `TauCeti.fueterLeft_eq_zero_iff`, `TauCeti.fueterRight_eq_zero_iff`: the two real
  component systems of four equations each.
* `TauCeti.fueterLeft_mul_flip`, `TauCeti.fueterRight_mul`: the operators on the derivatives
  `h ↦ h * b` and `h ↦ b * h` of the one-sided affine maps; with
  `HasFDerivAt.leftFueterAt_iff_eq_zero` and `HasFDerivAt.rightFueterAt_iff_eq_zero`, such a map
  is regular on the matching side exactly when `b = 0`.
* `TauCeti.leftFueterAt_coeComplex_comp`, `TauCeti.rightFueterAt_coeComplex_comp`: a complex
  differentiable function of `t + i x` is regular on both sides, while
  `TauCeti.not_rightFueterAt_coeComplex_mul_j` and `TauCeti.not_leftFueterAt_j_mul_coeComplex`
  show that `(t + i x) * j` and `j * (t + i x)` are regular on one side only.
* `TauCeti.LeftFueterAt.mul_const`, `TauCeti.RightFueterAt.const_mul`: left regularity is
  preserved by constant multiplication on the right, and right regularity by constant
  multiplication on the left.

## References

* R. Fueter, *Die Funktionentheorie der Differentialgleichungen Δu = 0 und ΔΔu = 0 mit vier
  reellen Variablen*, Comment. Math. Helv. 7 (1934), 307–330.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Definition 1.
-/

public section

open Quaternion Topology

namespace TauCeti

/-! ### The operators on real-linear maps -/

/-- The left Fueter operator on a real-linear map `D : ℍ →L[ℝ] ℍ`:
`D 1 + i * D i + j * D j + k * D k`. Applied to the real derivative of `f` at `q`, it is
`∂̄ₗ f (q) = ∂ₜf + i * ∂ₓf + j * ∂ᵧf + k * ∂_zf`. -/
noncomputable def fueterLeft : (ℍ →L[ℝ] ℍ) →ₗ[ℝ] ℍ where
  toFun D := D 1 + ⟨0, 1, 0, 0⟩ * D ⟨0, 1, 0, 0⟩ + ⟨0, 0, 1, 0⟩ * D ⟨0, 0, 1, 0⟩ +
    ⟨0, 0, 0, 1⟩ * D ⟨0, 0, 0, 1⟩
  map_add' D E := by simp only [add_apply, mul_add]; abel
  map_smul' r D := by simp only [smul_apply, mul_smul_comm, smul_add,
    RingHom.id_apply]

/-- The right Fueter operator on a real-linear map `D : ℍ →L[ℝ] ℍ`:
`D 1 + D i * i + D j * j + D k * k`. Applied to the real derivative of `f` at `q`, it is
`∂̄ᵣ f (q) = ∂ₜf + ∂ₓf * i + ∂ᵧf * j + ∂_zf * k`. -/
noncomputable def fueterRight : (ℍ →L[ℝ] ℍ) →ₗ[ℝ] ℍ where
  toFun D := D 1 + D ⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ + D ⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ +
    D ⟨0, 0, 0, 1⟩ * ⟨0, 0, 0, 1⟩
  map_add' D E := by simp only [add_apply, add_mul]; abel
  map_smul' r D := by simp only [smul_apply, smul_mul_assoc, smul_add,
    RingHom.id_apply]

theorem fueterLeft_apply (D : ℍ →L[ℝ] ℍ) :
    fueterLeft D = D 1 + ⟨0, 1, 0, 0⟩ * D ⟨0, 1, 0, 0⟩ + ⟨0, 0, 1, 0⟩ * D ⟨0, 0, 1, 0⟩ +
      ⟨0, 0, 0, 1⟩ * D ⟨0, 0, 0, 1⟩ := (rfl)

theorem fueterRight_apply (D : ℍ →L[ℝ] ℍ) :
    fueterRight D = D 1 + D ⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ + D ⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ +
      D ⟨0, 0, 0, 1⟩ * ⟨0, 0, 0, 1⟩ := (rfl)

/-- The left Fueter equation in real components. Writing `K, L, M, N` for the `re, imI, imJ, imK`
components of the output and `t, x, y, z` for the input directions `1, i, j, k`, so that
`K_x = (D i).re`, it reads
`Kₜ - Lₓ - M_y - N_z = 0`, `Lₜ + Kₓ + N_y - M_z = 0`, `Mₜ - Nₓ + K_y + L_z = 0` and
`Nₜ + Mₓ - L_y + K_z = 0`. -/
theorem fueterLeft_eq_zero_iff (D : ℍ →L[ℝ] ℍ) :
    fueterLeft D = 0 ↔
      (D 1).re - (D ⟨0, 1, 0, 0⟩).imI - (D ⟨0, 0, 1, 0⟩).imJ - (D ⟨0, 0, 0, 1⟩).imK = 0 ∧
      (D 1).imI + (D ⟨0, 1, 0, 0⟩).re + (D ⟨0, 0, 1, 0⟩).imK - (D ⟨0, 0, 0, 1⟩).imJ = 0 ∧
      (D 1).imJ - (D ⟨0, 1, 0, 0⟩).imK + (D ⟨0, 0, 1, 0⟩).re + (D ⟨0, 0, 0, 1⟩).imI = 0 ∧
      (D 1).imK + (D ⟨0, 1, 0, 0⟩).imJ - (D ⟨0, 0, 1, 0⟩).imI + (D ⟨0, 0, 0, 1⟩).re = 0 := by
  rw [fueterLeft_apply, Quaternion.ext_iff]
  simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul, re_zero,
    imI_zero, imJ_zero, imK_zero]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The right Fueter equation in real components. With the notation of `fueterLeft_eq_zero_iff`
it reads `Kₜ - Lₓ - M_y - N_z = 0`, `Lₜ + Kₓ - N_y + M_z = 0`, `Mₜ + Nₓ + K_y - L_z = 0` and
`Nₜ - Mₓ + L_y + K_z = 0`; it differs from the left system in the signs of the six terms that
pair two imaginary directions. -/
theorem fueterRight_eq_zero_iff (D : ℍ →L[ℝ] ℍ) :
    fueterRight D = 0 ↔
      (D 1).re - (D ⟨0, 1, 0, 0⟩).imI - (D ⟨0, 0, 1, 0⟩).imJ - (D ⟨0, 0, 0, 1⟩).imK = 0 ∧
      (D 1).imI + (D ⟨0, 1, 0, 0⟩).re - (D ⟨0, 0, 1, 0⟩).imK + (D ⟨0, 0, 0, 1⟩).imJ = 0 ∧
      (D 1).imJ + (D ⟨0, 1, 0, 0⟩).imK + (D ⟨0, 0, 1, 0⟩).re - (D ⟨0, 0, 0, 1⟩).imI = 0 ∧
      (D 1).imK - (D ⟨0, 1, 0, 0⟩).imJ + (D ⟨0, 0, 1, 0⟩).imI + (D ⟨0, 0, 0, 1⟩).re = 0 := by
  rw [fueterRight_apply, Quaternion.ext_iff]
  simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul, re_zero,
    imI_zero, imJ_zero, imK_zero]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- On the real derivative `h ↦ h * b` of a map with left slope `b`, the left Fueter operator
is `-2 * b`. -/
@[simp]
theorem fueterLeft_mul_flip (b : ℍ) :
    fueterLeft ((ContinuousLinearMap.mul ℝ ℍ).flip b) = -2 * b := by
  rw [fueterLeft_apply]
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

/-- On the real derivative `h ↦ a * h` of a map with right slope `a`, the left Fueter operator
is `-2 * star a`. -/
@[simp]
theorem fueterLeft_mul (a : ℍ) : fueterLeft (ContinuousLinearMap.mul ℝ ℍ a) = -2 * star a := by
  rw [fueterLeft_apply]
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

/-- On the real derivative `h ↦ a * h` of a map with right slope `a`, the right Fueter operator
is `-2 * a`. -/
@[simp]
theorem fueterRight_mul (a : ℍ) : fueterRight (ContinuousLinearMap.mul ℝ ℍ a) = -2 * a := by
  rw [fueterRight_apply]
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

/-- On the real derivative `h ↦ h * b` of a map with left slope `b`, the right Fueter operator
is `-2 * star b`. -/
@[simp]
theorem fueterRight_mul_flip (b : ℍ) :
    fueterRight ((ContinuousLinearMap.mul ℝ ℍ).flip b) = -2 * star b := by
  rw [fueterRight_apply]
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

/-- Multiplying a real-linear map by a constant on the right multiplies its left Fueter operator
by the same constant on the right. -/
theorem fueterLeft_mulRight (D : ℍ →L[ℝ] ℍ) (b : ℍ) :
    fueterLeft (((ContinuousLinearMap.mul ℝ ℍ).flip b).comp D) = fueterLeft D * b := by
  simp only [fueterLeft_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', add_mul, mul_assoc]

/-- Multiplying a real-linear map by a constant on the left multiplies its right Fueter operator
by the same constant on the left. -/
theorem fueterRight_mulLeft (D : ℍ →L[ℝ] ℍ) (a : ℍ) :
    fueterRight ((ContinuousLinearMap.mul ℝ ℍ a).comp D) = a * fueterRight D := by
  simp only [fueterRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    mul_add, mul_assoc]

/-! ### Pointwise Fueter regularity -/

/-- `f` is *left Fueter regular* at `q`: it has a real Fréchet derivative `D` at `q` with
`D 1 + i * D i + j * D j + k * D k = 0`. -/
def LeftFueterAt (f : ℍ → ℍ) (q : ℍ) : Prop :=
  ∃ D : ℍ →L[ℝ] ℍ, HasFDerivAt f D q ∧ fueterLeft D = 0

/-- `f` is *right Fueter regular* at `q`: it has a real Fréchet derivative `D` at `q` with
`D 1 + D i * i + D j * j + D k * k = 0`. -/
def RightFueterAt (f : ℍ → ℍ) (q : ℍ) : Prop :=
  ∃ D : ℍ →L[ℝ] ℍ, HasFDerivAt f D q ∧ fueterRight D = 0

/-- `f` is left Fueter regular at every point of `s`. -/
def LeftFueterOn (f : ℍ → ℍ) (s : Set ℍ) : Prop :=
  ∀ q ∈ s, LeftFueterAt f q

/-- `f` is right Fueter regular at every point of `s`. -/
def RightFueterOn (f : ℍ → ℍ) (s : Set ℍ) : Prop :=
  ∀ q ∈ s, RightFueterAt f q

variable {f g : ℍ → ℍ} {D : ℍ →L[ℝ] ℍ} {q : ℍ} {s t : Set ℍ}

/-- Given a derivative of `f` at `q`, left regularity is the left Fueter equation for it. -/
theorem _root_.HasFDerivAt.leftFueterAt_iff (hf : HasFDerivAt f D q) :
    LeftFueterAt f q ↔ fueterLeft D = 0 :=
  ⟨fun ⟨_, hE, h⟩ ↦ hf.unique hE ▸ h, fun h ↦ ⟨D, hf, h⟩⟩

/-- Given a derivative of `f` at `q`, right regularity is the right Fueter equation for it. -/
theorem _root_.HasFDerivAt.rightFueterAt_iff (hf : HasFDerivAt f D q) :
    RightFueterAt f q ↔ fueterRight D = 0 :=
  ⟨fun ⟨_, hE, h⟩ ↦ hf.unique hE ▸ h, fun h ↦ ⟨D, hf, h⟩⟩

/-- Left regularity at `q` is differentiability at `q` together with the left Fueter equation for
`fderiv ℝ f q`. -/
theorem leftFueterAt_iff :
    LeftFueterAt f q ↔ DifferentiableAt ℝ f q ∧ fueterLeft (fderiv ℝ f q) = 0 :=
  ⟨fun ⟨_, hD, h⟩ ↦ ⟨hD.differentiableAt, hD.fderiv ▸ h⟩,
    fun ⟨hf, h⟩ ↦ ⟨_, hf.hasFDerivAt, h⟩⟩

/-- Right regularity at `q` is differentiability at `q` together with the right Fueter equation
for `fderiv ℝ f q`. -/
theorem rightFueterAt_iff :
    RightFueterAt f q ↔ DifferentiableAt ℝ f q ∧ fueterRight (fderiv ℝ f q) = 0 :=
  ⟨fun ⟨_, hD, h⟩ ↦ ⟨hD.differentiableAt, hD.fderiv ▸ h⟩,
    fun ⟨hf, h⟩ ↦ ⟨_, hf.hasFDerivAt, h⟩⟩

namespace LeftFueterAt

/-- A left regular function is real differentiable at the point. -/
theorem differentiableAt (hf : LeftFueterAt f q) : DifferentiableAt ℝ f q :=
  (leftFueterAt_iff.1 hf).1

/-- The left Fueter equation holds for the derivative `fderiv ℝ f q`. -/
theorem fueterLeft_fderiv (hf : LeftFueterAt f q) : fueterLeft (fderiv ℝ f q) = 0 :=
  (leftFueterAt_iff.1 hf).2

theorem congr_of_eventuallyEq (hf : LeftFueterAt f q) (h : g =ᶠ[𝓝 q] f) :
    LeftFueterAt g q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.congr_of_eventuallyEq h, hD0⟩

theorem add (hf : LeftFueterAt f q) (hg : LeftFueterAt g q) :
    LeftFueterAt (fun x ↦ f x + g x) q :=
  let ⟨D, hD, hD0⟩ := hf
  let ⟨E, hE, hE0⟩ := hg
  ⟨D + E, hD.add hE, by rw [map_add, hD0, hE0, add_zero]⟩

theorem const_smul (hf : LeftFueterAt f q) (r : ℝ) : LeftFueterAt (fun x ↦ r • f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨r • D, hD.const_smul r, by rw [map_smul, hD0, smul_zero]⟩

theorem neg (hf : LeftFueterAt f q) : LeftFueterAt (fun x ↦ -f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨-D, hD.neg, by rw [map_neg, hD0, neg_zero]⟩

theorem sub (hf : LeftFueterAt f q) (hg : LeftFueterAt g q) :
    LeftFueterAt (fun x ↦ f x - g x) q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem add_const (hf : LeftFueterAt f q) (c : ℍ) : LeftFueterAt (fun x ↦ f x + c) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.add_const c, hD0⟩

theorem const_add (hf : LeftFueterAt f q) (c : ℍ) : LeftFueterAt (fun x ↦ c + f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.const_add c, hD0⟩

/-- Left regularity is preserved by multiplication by a constant on the right. -/
theorem mul_const (hf : LeftFueterAt f q) (b : ℍ) : LeftFueterAt (fun x ↦ f x * b) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨_, ((ContinuousLinearMap.mul ℝ ℍ).flip b).hasFDerivAt.comp q hD,
    by rw [fueterLeft_mulRight, hD0, zero_mul]⟩

end LeftFueterAt

namespace RightFueterAt

/-- A right regular function is real differentiable at the point. -/
theorem differentiableAt (hf : RightFueterAt f q) : DifferentiableAt ℝ f q :=
  (rightFueterAt_iff.1 hf).1

/-- The right Fueter equation holds for the derivative `fderiv ℝ f q`. -/
theorem fueterRight_fderiv (hf : RightFueterAt f q) : fueterRight (fderiv ℝ f q) = 0 :=
  (rightFueterAt_iff.1 hf).2

theorem congr_of_eventuallyEq (hf : RightFueterAt f q) (h : g =ᶠ[𝓝 q] f) :
    RightFueterAt g q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.congr_of_eventuallyEq h, hD0⟩

theorem add (hf : RightFueterAt f q) (hg : RightFueterAt g q) :
    RightFueterAt (fun x ↦ f x + g x) q :=
  let ⟨D, hD, hD0⟩ := hf
  let ⟨E, hE, hE0⟩ := hg
  ⟨D + E, hD.add hE, by rw [map_add, hD0, hE0, add_zero]⟩

theorem const_smul (hf : RightFueterAt f q) (r : ℝ) : RightFueterAt (fun x ↦ r • f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨r • D, hD.const_smul r, by rw [map_smul, hD0, smul_zero]⟩

theorem neg (hf : RightFueterAt f q) : RightFueterAt (fun x ↦ -f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨-D, hD.neg, by rw [map_neg, hD0, neg_zero]⟩

theorem sub (hf : RightFueterAt f q) (hg : RightFueterAt g q) :
    RightFueterAt (fun x ↦ f x - g x) q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem add_const (hf : RightFueterAt f q) (c : ℍ) : RightFueterAt (fun x ↦ f x + c) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.add_const c, hD0⟩

theorem const_add (hf : RightFueterAt f q) (c : ℍ) : RightFueterAt (fun x ↦ c + f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨D, hD.const_add c, hD0⟩

/-- Right regularity is preserved by multiplication by a constant on the left. -/
theorem const_mul (hf : RightFueterAt f q) (a : ℍ) : RightFueterAt (fun x ↦ a * f x) q :=
  let ⟨D, hD, hD0⟩ := hf
  ⟨_, (ContinuousLinearMap.mul ℝ ℍ a).hasFDerivAt.comp q hD,
    by rw [fueterRight_mulLeft, hD0, mul_zero]⟩

end RightFueterAt

theorem leftFueterAt_const (c q : ℍ) : LeftFueterAt (fun _ ↦ c) q :=
  ⟨0, hasFDerivAt_const c q, map_zero _⟩

theorem rightFueterAt_const (c q : ℍ) : RightFueterAt (fun _ ↦ c) q :=
  ⟨0, hasFDerivAt_const c q, map_zero _⟩

/-- A map with derivative `h ↦ h * b` at `q`, for instance `x ↦ a + x * b`, is left regular at
`q` exactly when `b = 0`. -/
theorem _root_.HasFDerivAt.leftFueterAt_iff_eq_zero {b : ℍ}
    (hf : HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip b) q) : LeftFueterAt f q ↔ b = 0 := by
  have h2 : (2 : ℍ) ≠ 0 := fun h ↦ by
    simpa [QuaternionAlgebra.re_ofNat] using congrArg QuaternionAlgebra.re h
  rw [hf.leftFueterAt_iff, fueterLeft_mul_flip, neg_mul, neg_eq_zero, mul_eq_zero,
    or_iff_right h2]

/-- A map with derivative `h ↦ a * h` at `q`, for instance `x ↦ c + a * x`, is right regular at
`q` exactly when `a = 0`. -/
theorem _root_.HasFDerivAt.rightFueterAt_iff_eq_zero {a : ℍ}
    (hf : HasFDerivAt f (ContinuousLinearMap.mul ℝ ℍ a) q) : RightFueterAt f q ↔ a = 0 := by
  have h2 : (2 : ℍ) ≠ 0 := fun h ↦ by
    simpa [QuaternionAlgebra.re_ofNat] using congrArg QuaternionAlgebra.re h
  rw [hf.rightFueterAt_iff, fueterRight_mul, neg_mul, neg_eq_zero, mul_eq_zero,
    or_iff_right h2]

/-! ### Holomorphic functions of `t + i x` -/

/-- If `g : ℂ → ℂ` has complex derivative `c` at `t + i x`, then `x ↦ g (t + i x)`, viewed in
`ℍ`, has a real derivative at `q` taking the values `c, i * c, 0, 0` on `1, i, j, k`. -/
private theorem exists_hasFDerivAt_coeComplex_comp {g : ℂ → ℂ} {c : ℂ}
    (hg : HasDerivAt g c ⟨q.re, q.imI⟩) :
    ∃ D : ℍ →L[ℝ] ℍ, HasFDerivAt (fun x : ℍ ↦ (g ⟨x.re, x.imI⟩ : ℍ)) D q ∧ D 1 = c ∧
      D ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * c ∧ D ⟨0, 0, 1, 0⟩ = 0 ∧ D ⟨0, 0, 0, 1⟩ = 0 := by
  -- The real-linear projection `x ↦ x.re + x.imI * I` and the coercion `ℂ → ℍ`.
  let p : ℍ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun x := ⟨x.re, x.imI⟩
      map_add' _ _ := by apply Complex.ext <;> simp
      map_smul' _ _ := by apply Complex.ext <;> simp }
  let ι : ℂ →L[ℝ] ℍ := LinearMap.toContinuousLinearMap Quaternion.ofComplex.toLinearMap
  refine ⟨_, ι.hasFDerivAt.comp q ((hg.hasFDerivAt.restrictScalars ℝ).comp q p.hasFDerivAt),
    ?_, ?_, ?_, ?_⟩ <;> ext <;> simp [p, ι]

/-- A complex differentiable function of `t + i x` is left Fueter regular: if `g : ℂ → ℂ` is
differentiable at `q.re + q.imI * I`, then `x ↦ g (x.re + x.imI * I)`, viewed in `ℍ`, is left
regular at `q`. -/
theorem leftFueterAt_coeComplex_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g ⟨q.re, q.imI⟩) :
    LeftFueterAt (fun x : ℍ ↦ (g ⟨x.re, x.imI⟩ : ℍ)) q := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ := exists_hasFDerivAt_coeComplex_comp hg.hasDerivAt
  refine ⟨D, hD, ?_⟩
  rw [fueterLeft_apply, h1, hi, hj, hk]
  ext <;> simp

/-- A complex differentiable function of `t + i x` is right Fueter regular: if `g : ℂ → ℂ` is
differentiable at `q.re + q.imI * I`, then `x ↦ g (x.re + x.imI * I)`, viewed in `ℍ`, is right
regular at `q`. -/
theorem rightFueterAt_coeComplex_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g ⟨q.re, q.imI⟩) :
    RightFueterAt (fun x : ℍ ↦ (g ⟨x.re, x.imI⟩ : ℍ)) q := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ := exists_hasFDerivAt_coeComplex_comp hg.hasDerivAt
  refine ⟨D, hD, ?_⟩
  rw [fueterRight_apply, h1, hi, hj, hk]
  ext <;> simp

/-- A function holomorphic on an open set `U ⊆ ℂ`, as a function of `t + i x`, is left Fueter
regular on the cylinder `{q | q.re + q.imI * I ∈ U}`. -/
theorem leftFueterOn_coeComplex_comp {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    LeftFueterOn (fun x : ℍ ↦ (g ⟨x.re, x.imI⟩ : ℍ)) {q | (⟨q.re, q.imI⟩ : ℂ) ∈ U} :=
  fun _ hq ↦ leftFueterAt_coeComplex_comp (hg.differentiableAt (hU.mem_nhds hq))

/-- A function holomorphic on an open set `U ⊆ ℂ`, as a function of `t + i x`, is right Fueter
regular on the cylinder `{q | q.re + q.imI * I ∈ U}`. -/
theorem rightFueterOn_coeComplex_comp {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    RightFueterOn (fun x : ℍ ↦ (g ⟨x.re, x.imI⟩ : ℍ)) {q | (⟨q.re, q.imI⟩ : ℂ) ∈ U} :=
  fun _ hq ↦ rightFueterAt_coeComplex_comp (hg.differentiableAt (hU.mem_nhds hq))

/-- The two sides differ: `x ↦ (t + i x) * j` is left regular (by
`leftFueterAt_coeComplex_comp` and `LeftFueterAt.mul_const`) but not right regular. -/
theorem not_rightFueterAt_coeComplex_mul_j :
    ¬ RightFueterAt (fun x : ℍ ↦ ((⟨x.re, x.imI⟩ : ℂ) : ℍ) * ⟨0, 0, 1, 0⟩) q := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ :=
    exists_hasFDerivAt_coeComplex_comp (g := id) (q := q) (hasDerivAt_id _)
  have h : HasFDerivAt (fun x : ℍ ↦ ((⟨x.re, x.imI⟩ : ℂ) : ℍ) * ⟨0, 0, 1, 0⟩)
      (((ContinuousLinearMap.mul ℝ ℍ).flip ⟨0, 0, 1, 0⟩).comp D) q :=
    ((ContinuousLinearMap.mul ℝ ℍ).flip _).hasFDerivAt.comp q hD
  rw [h.rightFueterAt_iff, fueterRight_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', h1, hi, hj, hk]
  intro h0
  simpa using congrArg QuaternionAlgebra.imJ h0

/-- The two sides differ: `x ↦ j * (t + i x)` is right regular (by
`rightFueterAt_coeComplex_comp` and `RightFueterAt.const_mul`) but not left regular. -/
theorem not_leftFueterAt_j_mul_coeComplex :
    ¬ LeftFueterAt (fun x : ℍ ↦ ⟨0, 0, 1, 0⟩ * ((⟨x.re, x.imI⟩ : ℂ) : ℍ)) q := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ :=
    exists_hasFDerivAt_coeComplex_comp (g := id) (q := q) (hasDerivAt_id _)
  have h : HasFDerivAt (fun x : ℍ ↦ ⟨0, 0, 1, 0⟩ * ((⟨x.re, x.imI⟩ : ℂ) : ℍ))
      ((ContinuousLinearMap.mul ℝ ℍ ⟨0, 0, 1, 0⟩).comp D) q :=
    (ContinuousLinearMap.mul ℝ ℍ _).hasFDerivAt.comp q hD
  rw [h.leftFueterAt_iff, fueterLeft_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', h1, hi, hj, hk]
  intro h0
  simpa using congrArg QuaternionAlgebra.imJ h0

/-! ### Regularity on a set -/

namespace LeftFueterOn

theorem mono (hf : LeftFueterOn f t) (hst : s ⊆ t) : LeftFueterOn f s :=
  fun q hq ↦ hf q (hst hq)

theorem differentiableOn (hf : LeftFueterOn f s) : DifferentiableOn ℝ f s :=
  fun q hq ↦ (hf q hq).differentiableAt.differentiableWithinAt

end LeftFueterOn

namespace RightFueterOn

theorem mono (hf : RightFueterOn f t) (hst : s ⊆ t) : RightFueterOn f s :=
  fun q hq ↦ hf q (hst hq)

theorem differentiableOn (hf : RightFueterOn f s) : DifferentiableOn ℝ f s :=
  fun q hq ↦ (hf q hq).differentiableAt.differentiableWithinAt

end RightFueterOn

end TauCeti
