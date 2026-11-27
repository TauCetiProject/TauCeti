/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries

/-!
# The Schrödinger propagator of a time-dependent Hamiltonian

Let `B` be a complete normed complex algebra, `H : ℝ → B` a continuous family of Hamiltonians and
`T` a real time scale. The Schrödinger propagator `U = TauCeti.hamiltonianPropagator H T` is the
solution of the Schrödinger equation

`i U' s = T H(s) U(s)`, `U 0 = 1`,

that is `U' = -iT H U`. It is the left Dyson series of the path `r ↦ -iT H r`. Rescaling time by
`T` turns a slow sweep of `H` over `[0, 1]` into this equation on `[0, 1]`, which is the setting of
the adiabatic theorem; the main example of `B` is the algebra of complex square matrices with the
Euclidean operator norm (the scoped instances `Matrix.Norms.L2Operator`).

When every `H s` is self-adjoint, `U s` is unitary, and in a C⋆-algebra two such propagators
differ at time `s ≥ 0` by at most `|T| ∫₀ˢ ‖H₁ - H₂‖`. With `hamiltonianPropagator_comp_const_add`
and `hamiltonianPropagator_const`, this compares the propagator over a short time step with the
exponential of the Hamiltonian frozen at the start of the step.

## Main declarations

* `TauCeti.hamiltonianPropagator`: the propagator `U` of `i U' = T H U`, `U 0 = 1`.
* `TauCeti.hamiltonianPropagator_eq_dysonSeriesLeft`: `U` is the left Dyson series of
  `r ↦ -iT H r`.
* `TauCeti.hasDerivAt_hamiltonianPropagator`, `TauCeti.eq_hamiltonianPropagator`: `U` solves the
  Schrödinger equation, and it is the only solution with `U 0 = 1`.
* `TauCeti.hamiltonianPropagator_mem_unitary`: `U s` is unitary for a self-adjoint family.
* `TauCeti.isUnit_hamiltonianPropagator`: `U s` is invertible for a continuous family.
* `TauCeti.hamiltonianPropagator_const`: for a constant Hamiltonian `h`, `U s = exp (-iTs h)`.
* `TauCeti.hamiltonianPropagator_add`, `TauCeti.hamiltonianPropagator_comp_const_add`:
  `U (a + s) = Uₐ s U a` for the propagator `Uₐ` of the translated family `r ↦ H (a + r)`, so
  that `Uₐ s = U (a + s) U(a)⁻¹`.
* `TauCeti.hamiltonianPropagator_comp_const_add_eq_mul_star`: `Uₐ s = U (a + s) U(a)⋆` for a
  self-adjoint family.
* `TauCeti.norm_hamiltonianPropagator_sub_le`: `‖U₁ s - U₂ s‖ ≤ |T| ∫₀ˢ ‖H₁ - H₂‖` for `s ≥ 0`.

## References

* S. Jansen, M.-B. Ruskai and R. Seiler, *Bounds for the adiabatic approximation with
  applications to quantum computation*, J. Math. Phys. **48** (2007), 102111,
  arXiv:quant-ph/0603175, for the Schrödinger equation in the rescaled time `s = t / T`.
-/

public section

noncomputable section

open Complex intervalIntegral

namespace TauCeti

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] {H H₁ H₂ : ℝ → B} {T : ℝ}

/-- The **Schrödinger propagator** of the family of Hamiltonians `H` at the time scale `T`: the
solution of `i U' s = T H(s) U(s)` with `U 0 = 1`, defined as the left Dyson series of
`r ↦ -iT H r`. For continuous `H` it solves this equation (`hasDerivAt_hamiltonianPropagator`)
and is its only solution (`eq_hamiltonianPropagator`). -/
def hamiltonianPropagator (H : ℝ → B) (T s : ℝ) : B :=
  dysonSeriesLeft (fun r => (-(T * I) : ℂ) • H r) s

/-- The Schrödinger propagator is the left Dyson series of `r ↦ -iT H r`. -/
theorem hamiltonianPropagator_eq_dysonSeriesLeft (H : ℝ → B) (T s : ℝ) :
    hamiltonianPropagator H T s = dysonSeriesLeft (fun r => (-(T * I) : ℂ) • H r) s :=
  (rfl)

@[simp]
theorem hamiltonianPropagator_zero (H : ℝ → B) (T : ℝ) : hamiltonianPropagator H T 0 = 1 :=
  dysonSeriesLeft_zero _

variable [CompleteSpace B]

/-- The Schrödinger propagator solves `U' s = -iT H(s) U(s)`. -/
theorem hasDerivAt_hamiltonianPropagator (hH : Continuous H) (T s : ℝ) :
    HasDerivAt (hamiltonianPropagator H T)
      ((-(T * I) : ℂ) • (H s * hamiltonianPropagator H T s)) s := by
  rw [← smul_mul_assoc]
  exact hasDerivAt_dysonSeriesLeft (hH.const_smul _) s

/-- The Schrödinger propagator of a continuous family is continuous. -/
theorem continuous_hamiltonianPropagator (hH : Continuous H) (T : ℝ) :
    Continuous (hamiltonianPropagator H T) :=
  continuous_dysonSeriesLeft (hH.const_smul _)

/-- Every solution of `f' s = -iT H(s) f(s)` is `f s = U s * f 0`. -/
theorem eq_hamiltonianPropagator_mul (hH : Continuous H) {f : ℝ → B}
    (hf : ∀ s, HasDerivAt f ((-(T * I) : ℂ) • (H s * f s)) s) (s : ℝ) :
    f s = hamiltonianPropagator H T s * f 0 :=
  eq_dysonSeriesLeft_mul (hH.const_smul _) (fun s => (hf s).congr_deriv (smul_mul_assoc ..).symm) s

/-- The Schrödinger propagator is the only solution of `f' s = -iT H(s) f(s)` with `f 0 = 1`. -/
theorem eq_hamiltonianPropagator (hH : Continuous H) {f : ℝ → B} (hf₀ : f 0 = 1)
    (hf : ∀ s, HasDerivAt f ((-(T * I) : ℂ) • (H s * f s)) s) :
    f = hamiltonianPropagator H T :=
  funext fun s => by rw [eq_hamiltonianPropagator_mul hH hf s, hf₀, mul_one]

/-- For a constant Hamiltonian `h`, the Schrödinger propagator is `U s = exp (-iTs h)`. -/
@[simp]
theorem hamiltonianPropagator_const (h : B) (T s : ℝ) :
    hamiltonianPropagator (fun _ => h) T s = NormedSpace.exp ((-(T * s * I) : ℂ) • h) := by
  rw [hamiltonianPropagator_eq_dysonSeriesLeft, dysonSeriesLeft_const, ← algebraMap_smul ℂ s,
    smul_smul, Complex.coe_algebraMap]
  congr 2
  ring

/-- The Schrödinger propagator of a continuous family is invertible. -/
theorem isUnit_hamiltonianPropagator (hH : Continuous H) (T s : ℝ) :
    IsUnit (hamiltonianPropagator H T s) :=
  isUnit_dysonSeriesLeft (hH.const_smul _) s

/-- The propagator of the translated family `r ↦ H (a + r)` composed with the propagator up to
time `a` is the propagator up to time `a + s`: `U (a + s) = Uₐ s * U a`. -/
theorem hamiltonianPropagator_add (hH : Continuous H) (T a s : ℝ) :
    hamiltonianPropagator H T (a + s) =
      hamiltonianPropagator (fun r => H (a + r)) T s * hamiltonianPropagator H T a :=
  dysonSeriesLeft_add (hH.const_smul _) a s

/-- The propagator of the translated family `r ↦ H (a + r)` is `U (a + s) U(a)⁻¹`. -/
theorem hamiltonianPropagator_comp_const_add (hH : Continuous H) (T a s : ℝ) :
    hamiltonianPropagator (fun r => H (a + r)) T s =
      hamiltonianPropagator H T (a + s) * Ring.inverse (hamiltonianPropagator H T a) := by
  rw [hamiltonianPropagator_add hH,
    Ring.mul_inverse_cancel_right _ _ (isUnit_hamiltonianPropagator hH T a)]

section Star

variable [StarRing B] [StarModule ℂ B]

omit [CompleteSpace B] in
/-- The generator `-iT h` of a self-adjoint Hamiltonian `h` is skew-adjoint. -/
private theorem star_neg_mul_I_smul {h : B} (hh : IsSelfAdjoint h) (T : ℝ) :
    star ((-(T * I) : ℂ) • h) = -((-(T * I) : ℂ) • h) :=
  skewAdjoint.mem_iff.1 <| hh.smul_mem_skewAdjoint <| skewAdjoint.mem_iff.2 <| by simp

variable [ContinuousStar B]

/-- The Schrödinger propagator of a continuous self-adjoint family is unitary. -/
theorem hamiltonianPropagator_mem_unitary (hH : Continuous H) (hsa : ∀ r, IsSelfAdjoint (H r))
    (T s : ℝ) : hamiltonianPropagator H T s ∈ unitary B :=
  dysonSeriesLeft_mem_unitary (hH.const_smul _) (fun r => star_neg_mul_I_smul (hsa r) T) s

/-- For a self-adjoint family, the propagator of the translated family `r ↦ H (a + r)` is
`U (a + s) U(a)⋆`. -/
theorem hamiltonianPropagator_comp_const_add_eq_mul_star (hH : Continuous H)
    (hsa : ∀ r, IsSelfAdjoint (H r)) (T a s : ℝ) :
    hamiltonianPropagator (fun r => H (a + r)) T s =
      hamiltonianPropagator H T (a + s) * star (hamiltonianPropagator H T a) := by
  rw [hamiltonianPropagator_add hH, mul_assoc,
    Unitary.mul_star_self_of_mem (hamiltonianPropagator_mem_unitary hH hsa T a), mul_one]

/-- **Comparison of Schrödinger propagators.** In a C⋆-algebra, the propagators of two continuous
self-adjoint families satisfy `‖U₁ s - U₂ s‖ ≤ |T| |∫₀ˢ ‖H₁ - H₂‖|`. -/
theorem norm_hamiltonianPropagator_sub_le_abs [CStarRing B] (h₁ : Continuous H₁)
    (h₂ : Continuous H₂) (hH₁ : ∀ r, IsSelfAdjoint (H₁ r)) (hH₂ : ∀ r, IsSelfAdjoint (H₂ r))
    (T s : ℝ) :
    ‖hamiltonianPropagator H₁ T s - hamiltonianPropagator H₂ T s‖ ≤
      |T| * |∫ r in 0..s, ‖H₁ r - H₂ r‖| := by
  have hc : ‖(-(T * I) : ℂ)‖ = |T| := by simp
  rw [hamiltonianPropagator_eq_dysonSeriesLeft, hamiltonianPropagator_eq_dysonSeriesLeft]
  refine (norm_dysonSeriesLeft_sub_le (h₁.const_smul _) (h₂.const_smul _)
    (fun r => star_neg_mul_I_smul (hH₁ r) T) (fun r => star_neg_mul_I_smul (hH₂ r) T) s).trans_eq ?_
  simp only [Pi.smul_apply, ← smul_sub, norm_smul, hc, intervalIntegral.integral_const_mul,
    abs_mul, abs_abs]

/-- **Comparison of Schrödinger propagators.** In a C⋆-algebra, the propagators of two continuous
self-adjoint families satisfy `‖U₁ s - U₂ s‖ ≤ |T| ∫₀ˢ ‖H₁ - H₂‖` for `s ≥ 0`. -/
theorem norm_hamiltonianPropagator_sub_le [CStarRing B] (h₁ : Continuous H₁)
    (h₂ : Continuous H₂) (hH₁ : ∀ r, IsSelfAdjoint (H₁ r)) (hH₂ : ∀ r, IsSelfAdjoint (H₂ r))
    (T : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ‖hamiltonianPropagator H₁ T s - hamiltonianPropagator H₂ T s‖ ≤
      |T| * ∫ r in 0..s, ‖H₁ r - H₂ r‖ := by
  simpa [abs_of_nonneg (integral_nonneg hs fun r _ => norm_nonneg (H₁ r - H₂ r))] using
    norm_hamiltonianPropagator_sub_le_abs h₁ h₂ hH₁ hH₂ T s

end Star

end TauCeti
