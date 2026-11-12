/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# The continuous functional calculus on eigenvectors

For a point `μ`, let `g x = (f x - f μ) / (x - μ)` be the difference quotient of `f` at `μ`. The
scalar identity `f x = g x (x - μ) + f μ` (valid at `x = μ` as well, since division by zero is
zero) passes to the continuous functional calculus whenever `g` is continuous on the spectrum
of `a`:

`cfc f a - f(μ) = cfc g a * (a - μ)`.

The hypothesis holds for every `f` when the spectrum of `a` is finite (`Set.Finite.continuousOn`),
and for every `f` continuous on the spectrum when `μ` lies outside it.

Consequently `cfc f a` acts as multiplication by `f μ` on every eigenvector of `a` for the
eigenvalue `μ`, in any module over the algebra. This is the description of the functional
calculus through eigenvectors, which is exact in finite dimension: the main examples of elements
with finite spectrum are the bounded operators on a finite-dimensional normed space, whose
spectrum is finite over every field of scalars acting compatibly
(`ContinuousLinearMap.finite_spectrum`). There the eigenvector action identifies the continuous
functional calculus with any spectral construction acting by `f μ` on the eigenvectors for `μ`.

## Main results

* `TauCeti.cfc_sub_algebraMap_eq_mul`: `cfc f a - f(μ) = cfc g a * (a - μ)` for the difference
  quotient `g` of `f` at `μ`, whenever `g` is continuous on the spectrum of `a`.
* `TauCeti.cfc_smul_of_smul_eq_algebraMap_smul`: if `a • m = μ • m` and the difference quotient
  of `f` at `μ` is continuous on the spectrum of `a`, then `cfc f a • m = f(μ) • m`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **Factoring out an eigenvalue.** For any point `μ`, if the difference quotient of `f` at `μ`
is continuous on the spectrum of `a`, then `cfc f a - f(μ)` factors through `a - μ` via that
difference quotient. The hypothesis holds for every `f` when the spectrum is finite
(`Set.Finite.continuousOn`), and for `f` continuous on the spectrum when `μ` lies outside it. -/
theorem cfc_sub_algebraMap_eq_mul (f : R → R) (a : A) (μ : R)
    (hg : ContinuousOn (fun x ↦ (f x - f μ) / (x - μ)) (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc f a - algebraMap R A (f μ) =
      cfc (fun x ↦ (f x - f μ) / (x - μ)) a * (a - algebraMap R A μ) := by
  have hf : f = fun x ↦ (f x - f μ) / (x - μ) * (x - μ) + f μ := by
    funext x
    rcases eq_or_ne x μ with rfl | hx
    · simp
    · rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hx), sub_add_cancel]
  -- Rewrite only the symbol `f` of `cfc f a`, not the constant `f μ`.
  nth_rw 1 [hf]
  rw [cfc_add .., cfc_const .., cfc_mul .., cfc_sub .., cfc_id' .., cfc_const ..,
    add_sub_cancel_right]

/-- **Eigenvector action.** If `a • m = μ • m` in a module over the algebra and the difference
quotient of `f` at `μ` is continuous on the spectrum of `a`, then `cfc f a • m = f(μ) • m`. When
the spectrum of `a` is finite, the hypothesis holds for every scalar function `f`
(`Set.Finite.continuousOn`). -/
theorem cfc_smul_of_smul_eq_algebraMap_smul {M : Type*} [AddCommGroup M] [Module A M]
    (f : R → R) {a : A} {μ : R} {m : M} (hm : a • m = algebraMap R A μ • m)
    (hg : ContinuousOn (fun x ↦ (f x - f μ) / (x - μ)) (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc f a • m = algebraMap R A (f μ) • m := by
  rw [← sub_eq_zero, ← sub_smul, cfc_sub_algebraMap_eq_mul f a μ hg, mul_smul, sub_smul,
    hm, sub_self, smul_zero]

end TauCeti
