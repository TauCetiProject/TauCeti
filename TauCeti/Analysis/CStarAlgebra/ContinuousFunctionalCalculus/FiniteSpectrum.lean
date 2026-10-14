/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The continuous functional calculus of an element with finite spectrum

If the spectrum of `a` is finite, every scalar function is continuous on it, so `cfc f a` is
the genuine functional calculus of `a` for every `f`. For a point `μ`, the difference quotient
`g x = (f x - f μ) / (x - μ)` is then also an admissible symbol, and the scalar identity
`f x = g x (x - μ) + f μ` (valid at `x = μ` as well, since division by zero is zero) passes to
the calculus:

`cfc f a - f(μ) = cfc g a * (a - μ)`.

Consequently `cfc f a` acts as multiplication by `f μ` on every eigenvector of `a` for the
eigenvalue `μ`, in any module over the algebra. This is the description of the functional
calculus through eigenvectors, which is exact in finite dimension: the main examples of elements
with finite spectrum are the bounded operators on a finite-dimensional normed space, whose
spectrum is finite over every field of scalars acting compatibly. There the eigenvector action
identifies the continuous functional calculus with any spectral construction acting by `f μ` on
the eigenvectors for `μ`.

## Main results

* `TauCeti.cfc_sub_algebraMap_eq_mul`: `cfc f a - f(μ) = cfc g a * (a - μ)` for the difference
  quotient `g` of `f` at `μ`.
* `TauCeti.cfc_smul_of_smul_eq_algebraMap_smul`: if `a • m = μ • m`, then
  `cfc f a • m = f(μ) • m`.
* `ContinuousLinearMap.finite_spectrum`: a bounded operator on a finite-dimensional normed space
  has finite spectrum, also over subfields of the scalars such as `ℝ ⊆ ℂ`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **Factoring out an eigenvalue.** For an element `a` with finite spectrum and any point `μ`,
`cfc f a - f(μ)` factors through `a - μ` via the difference quotient of `f` at `μ`. No
continuity of `f` is needed, since every function is continuous on a finite set. -/
theorem cfc_sub_algebraMap_eq_mul (f : R → R) {a : A} (hfin : (spectrum R a).Finite) (μ : R)
    (ha : p a := by cfc_tac) :
    cfc f a - algebraMap R A (f μ) =
      cfc (fun x ↦ (f x - f μ) / (x - μ)) a * (a - algebraMap R A μ) := by
  have hf : f = fun x ↦ (f x - f μ) / (x - μ) * (x - μ) + f μ := by
    funext x
    rcases eq_or_ne x μ with rfl | hx
    · simp
    · rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hx), sub_add_cancel]
  have hc (g : R → R) : ContinuousOn g (spectrum R a) := hfin.continuousOn g
  -- Rewrite only the symbol `f` of `cfc f a`, not the constant `f μ`.
  nth_rw 1 [hf]
  rw [cfc_add (hf := hc _) (hg := hc _), cfc_const .., cfc_mul (hf := hc _) (hg := hc _),
    cfc_sub (hf := hc _) (hg := hc _), cfc_id' .., cfc_const .., add_sub_cancel_right]

/-- **Eigenvector action.** If `a` has finite spectrum and `a • m = μ • m` in a module over the
algebra, then `cfc f a • m = f(μ) • m` for every scalar function `f`. -/
theorem cfc_smul_of_smul_eq_algebraMap_smul {M : Type*} [AddCommGroup M] [Module A M]
    (f : R → R) {a : A} (hfin : (spectrum R a).Finite) {μ : R} {m : M}
    (hm : a • m = algebraMap R A μ • m) (ha : p a := by cfc_tac) :
    cfc f a • m = algebraMap R A (f μ) • m := by
  rw [← sub_eq_zero, ← sub_smul, cfc_sub_algebraMap_eq_mul f hfin μ ha, mul_smul, sub_smul, hm,
    sub_self, smul_zero]

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- A bounded operator on a finite-dimensional normed space has finite spectrum over any field
`S` of scalars acting compatibly, for instance over `ℝ` for an operator on a complex space. -/
theorem finite_spectrum (S : Type*) [Field S] [Algebra S 𝕜] [Algebra S (V →L[𝕜] V)]
    [IsScalarTower S 𝕜 (V →L[𝕜] V)] (T : V →L[𝕜] V) : (spectrum S T).Finite := by
  have := FiniteDimensional.complete 𝕜 V
  rw [← spectrum.preimage_algebraMap 𝕜, spectrum_eq]
  exact (Module.End.finite_spectrum _).preimage (algebraMap S 𝕜).injective.injOn

end ContinuousLinearMap
