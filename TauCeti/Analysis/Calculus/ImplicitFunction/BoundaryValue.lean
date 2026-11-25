/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Mathlib's implicit function theorem packaged for boundary-value problems

Let `P`, `X`, `Y`, `Z` be Banach spaces: parameters `p ∈ P` (for instance a metric), unknowns
`u ∈ X` (for instance `C^{2,α}(closure B)`), values `N(p, u) ∈ Y` of a nonlinear operator
(for instance `C^{0,α}(closure B)`), and boundary data `φ ∈ Z` (for instance `C^{2,α}(∂B)`),
with a bounded trace
`T : X → Z`. Consider the boundary-value problem

`N(p, u) = 0`, `T u = φ`.

Let `N(p₀, u₀) = 0`, let `N` be `C^n` at `(p₀, u₀)` with `n ≥ 1`, and suppose that the linearized
problem is uniquely solvable: `A v = (∂ᵤN(p₀, u₀) v, T v)` is a Banach-space isomorphism
`X → Y × Z`. For the minimal graph operator at `(g_Eucl, 0)` this is the Dirichlet problem for the
Laplacian. This file is a corollary of Mathlib's implicit function theorem
(`ContDiffAt.implicitFunction`, with `ContDiffAt.hasStrictFDerivAt_implicitFunction` and
`ContDiffAt.contDiffAt_implicitFunction`) applied to `((p, φ), u) ↦ (N(p, u), T u - φ)`, stated
in the form used for boundary-value problems; it has no PDE content of its own. It gives: near
`(p₀, T u₀)` there is a solution `u = ψ(p, φ)`, it is the only solution near `u₀`, and `ψ` is
`C^n` with derivative `dψ(dp, dφ) = A⁻¹(-∂ₚN(p₀, u₀) dp, dφ)` at `(p₀, T u₀)`. In particular
`‖ψ(p, φ) - u₀‖ ≤ C ‖(p, φ) - (p₀, T u₀)‖` near `(p₀, T u₀)`: small data give small solutions.

## Main declarations

* `ContDiffAt.exists_boundaryValue_implicitFunction`: the solution map, its uniqueness, its
  derivative, its linear bound at `(p₀, T u₀)` and its smoothness.
-/

public section

open Filter
open scoped Topology ContDiff

namespace ContDiffAt

variable {𝕜 : Type*} [RCLike 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- **Mathlib's implicit function theorem, packaged for boundary-value problems.** This is
`ContDiffAt.implicitFunction` applied to `((p, φ), u) ↦ (N(p, u), T u - φ)`. Let
`N : P × X → Y` be `C^n` at `(p₀, u₀)`, `n ≠ 0`, with `N(p₀, u₀) = 0`, and let `T : X → Z` be a
bounded linear map such that `A v = (∂ᵤN(p₀, u₀) v, T v)` is invertible. Then there is a map
`ψ : P × Z → X` with `ψ(p₀, T u₀) = u₀` such that, near `(p₀, T u₀)`, `u = ψ(p, φ)` solves
`N(p, u) = 0`, `T u = φ`; near `((p₀, T u₀), u₀)` it is the only solution; `ψ` has strict
derivative `(dp, dφ) ↦ A⁻¹(-∂ₚN(p₀, u₀) dp, dφ)` at `(p₀, T u₀)`; the solution satisfies
the linear bound `‖ψ(p, φ) - u₀‖ ≤ C ‖(p, φ) - (p₀, T u₀)‖` near `(p₀, T u₀)`; and `ψ` is
`C^n` at `(p₀, T u₀)`. -/
theorem exists_boundaryValue_implicitFunction {N : P × X → Y} {p₀ : P} {u₀ : X} {n : ℕ∞ω}
    (hN : ContDiffAt 𝕜 n N (p₀, u₀)) (hn : n ≠ 0) (hN₀ : N (p₀, u₀) = 0) (T : X →L[𝕜] Z)
    (hA : ((fderiv 𝕜 N (p₀, u₀) ∘L .inr 𝕜 P X).prod T).IsInvertible) :
    ∃ ψ : P × Z → X, ψ (p₀, T u₀) = u₀ ∧
      (∀ᶠ q in 𝓝 (p₀, T u₀), N (q.1, ψ q) = 0 ∧ T (ψ q) = q.2) ∧
      (∀ᶠ w in 𝓝 ((p₀, T u₀), u₀), N (w.1.1, w.2) = 0 ∧ T w.2 = w.1.2 ↔ ψ w.1 = w.2) ∧
      HasStrictFDerivAt ψ (((fderiv 𝕜 N (p₀, u₀) ∘L .inr 𝕜 P X).prod T).inverse ∘L
        (-(fderiv 𝕜 N (p₀, u₀) ∘L .inl 𝕜 P X)).prodMap (.id 𝕜 Z)) (p₀, T u₀) ∧
      (∃ C : ℝ, ∀ᶠ q in 𝓝 (p₀, T u₀), ‖ψ q - u₀‖ ≤ C * ‖q - (p₀, T u₀)‖) ∧
      ContDiffAt 𝕜 n ψ (p₀, T u₀) := by
  set N' := fderiv 𝕜 N (p₀, u₀)
  set A := (N' ∘L .inr 𝕜 P X).prod T
  set g : (P × Z) × X →L[𝕜] P × X :=
    (ContinuousLinearMap.fst 𝕜 P Z ∘L .fst 𝕜 (P × Z) X).prod (.snd 𝕜 (P × Z) X)
  set L : (P × Z) × X →L[𝕜] Z := T ∘L .snd 𝕜 (P × Z) X - .snd 𝕜 P Z ∘L .fst 𝕜 (P × Z) X
  set f : (P × Z) × X → Y × Z := fun w ↦ (N (g w), L w)
  set w₀ : (P × Z) × X := ((p₀, T u₀), u₀)
  have hg : g w₀ = (p₀, u₀) := rfl
  have hf : ContDiffAt 𝕜 n f w₀ :=
    (hN.comp w₀ g.contDiff.contDiffAt).prodMk L.contDiff.contDiffAt
  have hf' : HasFDerivAt f ((N' ∘L g).prod L) w₀ :=
    ((hN.differentiableAt hn).hasFDerivAt.comp w₀ g.hasFDerivAt).prodMk L.hasFDerivAt
  have hfd : fderiv 𝕜 f w₀ = (N' ∘L g).prod L := hf'.fderiv
  have hinr : fderiv 𝕜 f w₀ ∘L .inr 𝕜 (P × Z) X = A := by
    rw [hfd]
    ext v <;> simp [A, g, L]
  have hinl : fderiv 𝕜 f w₀ ∘L .inl 𝕜 (P × Z) X =
      -(((-(N' ∘L .inl 𝕜 P X)).prodMap (.id 𝕜 Z))) := by
    rw [hfd]
    ext q <;> simp [g, L]
  have hinv : (fderiv 𝕜 f w₀ ∘L .inr 𝕜 (P × Z) X).IsInvertible := hinr ▸ hA
  set ψ := hf.implicitFunction hn hinv
  have hfw₀ : f w₀ = (0, 0) := by simp [f, hg, hN₀, L, w₀]
  have hsol : ∀ w : (P × Z) × X, f w = f w₀ ↔ N (w.1.1, w.2) = 0 ∧ T w.2 = w.1.2 := by
    intro w
    rw [hfw₀, Prod.ext_iff]
    simp [f, g, L, sub_eq_zero]
  have hderiv : HasStrictFDerivAt ψ (A.inverse ∘L
      (-(N' ∘L .inl 𝕜 P X)).prodMap (.id 𝕜 Z)) (p₀, T u₀) := by
    have h := hf.hasStrictFDerivAt_implicitFunction hn hinv
    rwa [hinr, hinl, ContinuousLinearMap.comp_neg, neg_neg] at h
  have hψ₀ : ψ (p₀, T u₀) = u₀ := hf.implicitFunction_apply_self hn hinv
  refine ⟨ψ, hψ₀, ?_, ?_, hderiv,
    ?_, hf.contDiffAt_implicitFunction hn hinv⟩
  · filter_upwards [hf.eventually_apply_implicitFunction hn hinv] with q hq
    exact (hsol (q, ψ q)).1 hq
  · filter_upwards [hf.eventually_apply_eq_iff_implicitFunction hn hinv] with w hw
    rw [← hsol w]
    exact hw
  · simpa only [hψ₀] using hderiv.hasFDerivAt.isBigO_sub.bound

end ContDiffAt
