/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The continuous functional calculus of an element with finite spectrum

If the spectrum of `a` is finite, every scalar function is continuous on it, so `cfc f a` is
the genuine functional calculus of `a` for every `f`. When the spectrum lies in a finite set `s`,
the functional calculus is Lagrange interpolation on the nodes `s`:
`cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)`, where `ℓ_μ` is the Lagrange basis polynomial that is `1` at `μ`
and `0` at the other nodes. The elements `ℓ_μ(a)` do not depend on `f`, so every `cfc f a` is a
fixed linear combination of polynomials in `a`, with coefficients the values of `f`.

## Main results

* `TauCeti.cfc_eq_sum_smul_aeval_lagrangeBasis`: if the spectrum of `a` lies in the finite set `s`,
  then `cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)` for the Lagrange basis polynomials `ℓ_μ` of `s`.
* `TauCeti.exists_support_projection_of_finite_spectrum`: a positive element `x` of a unital
  C⋆-algebra with finite spectrum has a star projection `p` and a self-adjoint `g` with
  `x^{1/2} g = g x^{1/2} = g x g = p` and `x^{1/2} (1 - p) = x (1 - p) = 0`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **The functional calculus as Lagrange interpolation.** If the spectrum of `a` lies in the
finite set `s`, then `cfc f a = ∑ μ ∈ s, f μ • ℓ_μ(a)`, where `ℓ_μ = Lagrange.basis s id μ` is
the Lagrange basis polynomial of the nodes `s` that is `1` at `μ` and `0` at the other nodes. -/
theorem cfc_eq_sum_smul_aeval_lagrangeBasis [DecidableEq R] (f : R → R) {a : A} {s : Finset R}
    (hs : spectrum R a ⊆ s) (ha : p a := by cfc_tac) :
    cfc f a = ∑ μ ∈ s, f μ • Polynomial.aeval a (Lagrange.basis s id μ) := by
  rw [cfc_congr (g := (Lagrange.interpolate s id f).eval) fun x hx ↦
      (Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hs hx)).symm,
    cfc_polynomial _ a ha, Lagrange.interpolate_apply, map_sum]
  simp [Algebra.smul_def]

section SupportProjection

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The support projection of a positive element with finite spectrum.** A positive element `x`
with finite spectrum has a star projection `p` and a self-adjoint `g` with
`x^{1/2} g = g x^{1/2} = g x g = p` and `x^{1/2} (1 - p) = x (1 - p) = 0`. -/
theorem exists_support_projection_of_finite_spectrum {x : B} (hx : 0 ≤ x)
    (hfin : (spectrum ℝ x).Finite) :
    ∃ p g : B, IsStarProjection p ∧ IsSelfAdjoint g ∧ CFC.sqrt x * g = p ∧ g * CFC.sqrt x = p ∧
      g * x * g = p ∧ CFC.sqrt x * (1 - p) = 0 ∧ x * (1 - p) = 0 := by
  -- The spectrum is finite, so the continuous functional calculus applies to the discontinuous
  -- functions `[t ≠ 0]` and `[t ≠ 0] t^{-1/2}`, which give `p` and `g`.
  have hspec : ∀ t ∈ spectrum ℝ x, 0 ≤ t := fun t ht => spectrum_nonneg_of_nonneg hx ht
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ x) := hfin.continuousOn f
  have hh : CFC.sqrt x = cfc Real.sqrt x := by rw [CFC.sqrt_eq_real_sqrt x hx, cfcₙ_eq_cfc]
  have hmul (f₁ f₂ : ℝ → ℝ) : cfc f₁ x * cfc f₂ x = cfc (fun t => f₁ t * f₂ t) x :=
    (cfc_mul _ _ x (hc _) (hc _)).symm
  set p := cfc (fun t : ℝ => if t = 0 then 0 else 1) x with hpdef
  set g := cfc (fun t : ℝ => if t = 0 then 0 else (Real.sqrt t)⁻¹) x with hgdef
  have hsg : CFC.sqrt x * g = p := by
    rw [hh, hgdef, hmul]
    refine cfc_congr fun t ht => ?_
    rcases (hspec t ht).eq_or_lt with h0 | h0
    · simp [← h0]
    · simp [h0.ne', (Real.sqrt_pos.mpr h0).ne']
  have hcomm : g * CFC.sqrt x = CFC.sqrt x * g := by
    rw [hh, hgdef, hmul, hmul]
    exact cfc_congr fun t _ => mul_comm _ _
  have hgxg : g * x * g = p := by
    conv_lhs => rw [← cfc_id' ℝ x]
    rw [hgdef, hmul, hmul]
    refine cfc_congr fun t ht => ?_
    rcases (hspec t ht).eq_or_lt with h0 | h0
    · simp [← h0]
    · have hs := Real.mul_self_sqrt h0.le
      have hs0 := (Real.sqrt_pos.mpr h0).ne'
      simp only [h0.ne', ite_false]
      field_simp
      linarith
  have hsp : CFC.sqrt x * p = CFC.sqrt x := by
    rw [hh, hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  have hxp : x * p = x := by
    conv_rhs => rw [← cfc_id' ℝ x]
    conv_lhs => rw [← cfc_id' ℝ x]
    rw [hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  have hpp : p * p = p := by
    rw [hpdef, hmul]
    exact cfc_congr fun t _ => by by_cases h0 : t = 0 <;> simp [h0]
  refine ⟨p, g, ⟨hpp, (cfc_predicate _ x : IsSelfAdjoint p)⟩, cfc_predicate _ x, hsg,
    hcomm.trans hsg, hgxg, ?_, ?_⟩
  · rw [mul_sub, mul_one, hsp, sub_self]
  · rw [mul_sub, mul_one, hxp, sub_self]

end SupportProjection

end TauCeti
