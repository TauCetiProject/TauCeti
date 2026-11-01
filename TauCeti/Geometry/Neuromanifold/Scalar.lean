/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import TauCeti.Geometry.Neuromanifold.Neurovariety
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Set.Infinite

/-!
# Scalar models and a non-closed polynomial image

A scalar model `w ↦ (x ↦ φ w * x)` on the line has a single coefficient `φ w`. Its finite
function presentation is the one-coordinate space `K^Unit` together with the evaluation
`scalarEvaluation K : (Unit → K) →ₗ[K] (K → K)`, `a ↦ (x ↦ a () * x)`. This evaluation is
injective, so coefficients and functions have the same image and the same parameter fibres.

Two instances show how the coefficient image compares with its neurovariety.

* For `f_w(x) = w x` the coefficient map `w ↦ w` is onto `K^Unit`, so its image is the whole
  coordinate space and equals its neurovariety (`isAlgebraicImage_const`).
* Over `ℝ`, for `g_w(x) = w² x` the coefficient image is the closed half-line
  `{z | 0 ≤ z ()}` (`range_const_sq`). Only the zero polynomial vanishes on it, so its
  neurovariety is all of `ℝ^Unit` (`neurovariety_const_sq`), and the image is not algebraic
  (`not_isAlgebraicImage_const_sq`).

The second example shows that a polynomial parametrization need not have a Zariski closed
coefficient image, which is why the neurovariety and the algebraic-image property are kept
separate. The closure convention is that of Finkel–Rodriguez–Wu–Yahl, *Activation degree
thresholds and expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), §1.1, equations (3)–(4); these
elementary examples are not taken from that paper.
-/

public section

namespace TauCeti.Neuromanifold

variable {W : Type*}

section Evaluation

variable (K : Type*) [CommSemiring K]

/-- The faithful evaluation of a single coefficient `a : Unit → K` as the scalar function
`x ↦ a () * x`. -/
def scalarEvaluation : (Unit → K) →ₗ[K] K → K :=
  (LinearMap.proj ()).smulRight id

/-- The scalar evaluation multiplies the input by the coefficient. -/
@[simp] theorem scalarEvaluation_apply (a : Unit → K) (x : K) :
    scalarEvaluation K a x = a () * x := by
  simp [scalarEvaluation]

variable {K}

/-- The scalar evaluation is faithful: a coefficient is recovered from its function. -/
theorem scalarEvaluation_injective : Function.Injective (scalarEvaluation K) := by
  intro a b h
  funext u
  simpa using congrFun h 1

/-- Evaluating the coefficients `φ w` gives the scalar model `w ↦ (x ↦ φ w * x)`. -/
theorem scalarEvaluation_comp_const (φ : W → K) :
    scalarEvaluation K ∘ (fun w => Function.const Unit (φ w)) = fun w x => φ w * x := by
  funext w x
  simp

/-- The functions realized by a scalar model are the evaluations of its coefficient image. -/
theorem realizedFunctions_mul (φ : W → K) :
    realizedFunctions (fun w (x : K) => φ w * x) =
      scalarEvaluation K '' Set.range (fun w => Function.const Unit (φ w)) := by
  rw [realizedFunctions_def, ← Set.range_comp, scalarEvaluation_comp_const]

/-- A scalar model and its coefficient map have the same parameter fibres. -/
theorem fiber_mul_scalarEvaluation (φ : W → K) (a : Unit → K) :
    fiber (fun w (x : K) => φ w * x) (scalarEvaluation K a) =
      fiber (fun w => Function.const Unit (φ w)) a := by
  ext w
  have h : scalarEvaluation K (Function.const Unit (φ w)) = fun x => φ w * x := by
    funext x
    simp
  rw [mem_fiber, mem_fiber, ← scalarEvaluation_injective.eq_iff, h]

end Evaluation

section Linear

variable {K : Type*} [Field K]

/-- The coefficient map `w ↦ w` of the scalar model `f_w(x) = w x` is onto `K^Unit`, so its
neurovariety is the whole coordinate space. -/
@[simp] theorem neurovariety_const :
    neurovariety (Function.const Unit : K → Unit → K) = Set.univ :=
  neurovariety_eq_univ_of_surjective fun a => ⟨a (), funext fun _ => rfl⟩

/-- The coefficient image of the scalar model `f_w(x) = w x` is algebraic: it is the whole
coordinate space `K^Unit`. -/
theorem isAlgebraicImage_const : IsAlgebraicImage (Function.const Unit : K → Unit → K) :=
  isAlgebraicImage_of_surjective fun a => ⟨a (), funext fun _ => rfl⟩

end Linear

section Square

/-- The coefficient image of the real scalar model `g_w(x) = w² x` is the closed half-line. -/
theorem range_const_sq :
    Set.range (fun w : ℝ => Function.const Unit (w ^ 2)) = {z | 0 ≤ z ()} := by
  ext z
  refine ⟨?_, fun hz => ⟨√(z ()), funext fun _ => Real.sq_sqrt hz⟩⟩
  rintro ⟨w, rfl⟩
  exact sq_nonneg w

/-- The real scalar model `g_w(x) = w² x` realizes exactly the functions `x ↦ a * x` with
`0 ≤ a`. -/
theorem realizedFunctions_sq_mul :
    realizedFunctions (fun w x : ℝ => w ^ 2 * x) = scalarEvaluation ℝ '' {z | 0 ≤ z ()} := by
  rw [realizedFunctions_mul, range_const_sq]

/-- The neurovariety of the coefficient map `w ↦ w²` over `ℝ` is the whole line: only the zero
polynomial vanishes on the closed half-line, which is infinite. -/
@[simp] theorem neurovariety_const_sq :
    neurovariety (fun w : ℝ => Function.const Unit (w ^ 2)) = Set.univ := by
  have h : {z : Unit → ℝ | 0 ≤ z ()} = Set.univ.pi fun _ => Set.Ici 0 := by
    ext z
    simp [Pi.le_def, Unique.forall_iff]
  rw [neurovariety_def, range_const_sq, h,
    MvPolynomial.zariskiClosure_pi_eq_univ fun _ => Set.Ici_infinite 0]

/-- The coefficient image of the real scalar model `g_w(x) = w² x` is not algebraic: its
neurovariety contains the coefficient `-1`, which is not a square. -/
theorem not_isAlgebraicImage_const_sq :
    ¬IsAlgebraicImage (fun w : ℝ => Function.const Unit (w ^ 2)) := by
  rw [isAlgebraicImage_iff, neurovariety_const_sq, range_const_sq]
  intro h
  have : Function.const Unit (-1 : ℝ) ∈ {z : Unit → ℝ | 0 ≤ z ()} := h ▸ Set.mem_univ _
  norm_num at this

end Square

end TauCeti.Neuromanifold
