/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import TauCeti.Analysis.Calculus.IteratedDerivWithin

/-!
# Continuous derivative jets on a closed interval

On a nondegenerate closed time interval, derivatives at the endpoints are one-sided.
An interior derivative with a continuous extension to the closed interval is the derivative
within that interval, including at its endpoints. Applying this observation successively
identifies every field of a continuous derivative jet with `iteratedDerivWithin`.

The jet criterion `contDiffOn_Icc_iff_exists_continuous_jet` characterizes finite-order
smoothness on a closed interval using only continuous fields and ordinary interior
derivatives. It allows time derivatives of functions on closed slabs to be specified by
continuous extensions without choosing an extension of the function outside the slab.
The codomain may itself be a space of continuous multilinear maps.

The endpoint argument uses Mathlib's
`hasFDerivWithinAt_closure_of_tendsto_fderiv`; higher orders use
`iteratedDerivWithin_succ` and the native criterion for `ContDiffOn` in terms of iterated
derivatives. No completeness assumption on the codomain is needed.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b : ℝ} {f g : ℝ → F}

/-- A continuous extension of an interior derivative is the derivative within the closed
interval, also at its two endpoints. -/
theorem hasDerivWithinAt_Icc_of_continuousOn (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  have hlim : Tendsto (fderiv ℝ f) (𝓝[Ioo a b] x)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (g x))) := by
    have h := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).continuous.tendsto (g x)
    apply (h.comp ((hg x hx).mono Ioo_subset_Icc_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).hasFDerivAt.fderiv.symm
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← closure_Ioo hab.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo _ hlim
  intro y hy
  rw [closure_Ioo hab.ne] at hy
  exact (hf y hy).mono Ioo_subset_Icc_self

/-- Every field in a finite continuous interior derivative jet is the corresponding iterated
derivative within the closed interval. In particular its endpoint values are canonical. -/
theorem eqOn_iteratedDerivWithin_Icc_of_continuous_jet (hab : a < b)
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x)
    {j : ℕ} (hj : j ≤ n) : EqOn (iteratedDerivWithin j f (Icc a b)) (J j) (Icc a b) := by
  induction j with
  | zero => simpa using hzero.symm
  | succ j ih =>
    have hjn : j < n := by omega
    have heq := ih (by omega)
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq hx)]
    exact (hasDerivWithinAt_Icc_of_continuousOn hab (hc j (by omega))
      (hc (j + 1) hj) (hd j hjn) hx).derivWithin (uniqueDiffOn_Icc hab x hx)

/-- A finite continuous derivative jet in the interior yields smoothness up to both endpoints.
Only the jet values on the closed interval matter. -/
theorem contDiffOn_Icc_of_continuous_jet (hab : a < b)
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x) :
    ContDiffOn ℝ n f (Icc a b) := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hab)).2
  constructor
  · intro j hj
    exact (hc j hj).congr
      (eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd hj)
  · intro j hj x hx
    have heq := eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd
      (Nat.le_of_lt hj)
    exact ((hasDerivWithinAt_Icc_of_continuousOn hab (hc j (by omega))
      (hc (j + 1) (by omega)) (hd j hj) hx).congr heq (heq hx)).differentiableWithinAt

/-- Finite-order smoothness on a nondegenerate closed interval is equivalent to the existence
of continuous derivative fields satisfying the ordinary derivative identities in the interior.
There is no condition on the fields outside the interval or above the specified order. -/
theorem contDiffOn_Icc_iff_exists_continuous_jet (hab : a < b) {n : ℕ} :
    ContDiffOn ℝ n f (Icc a b) ↔
      ∃ J : ℕ → ℝ → F, EqOn (J 0) f (Icc a b) ∧
        (∀ j ≤ n, ContinuousOn (J j) (Icc a b)) ∧
        ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x := by
  constructor
  · intro hf
    refine ⟨fun j ↦ iteratedDerivWithin j f (Icc a b), ?_, ?_, ?_⟩
    · simp only [iteratedDerivWithin_zero]
      exact eqOn_refl _ _
    · intro j hj
      exact hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hab)
    · intro j hj x hx
      exact ContDiffOn.hasDerivAt_iteratedDerivWithin (hf.of_le (by exact_mod_cast hj))
        (uniqueDiffOn_Icc hab) (Icc_mem_nhds hx.1 hx.2)
  · rintro ⟨J, hzero, hc, hd⟩
    exact contDiffOn_Icc_of_continuous_jet hab hzero hc hd

end TauCeti
