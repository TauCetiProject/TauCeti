/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.MvPolynomial.DirectionalOrder
public import TauCeti.Analysis.Polynomial.Order
public import TauCeti.Analysis.Analytic.ConstantOrder

/-!
# Analytic preparation along a fixed direction

If a polynomial has constant finite ambient order along an analytic parametrization, a
single affine direction detects that order on every nearby slice. Consequently evaluation
along that direction is a power of the line parameter times an analytic unit. This converts
ambient polynomial order into the distinguished-variable form used in analytic preparation
of discriminants. The direction and unit are constructed; no slice-order hypothesis is needed.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, Lemma 4.4.
-/

public section

open Filter Topology

namespace MvPolynomial

variable {σ 𝕜 E : Type*}

/-- Along a continuous parametrization of a set of constant finite ambient order, a single
direction detects that order analytically on every nearby slice. -/
theorem exists_eventually_analyticOrderAt_eval_add_smul_eq [NontriviallyNormedField 𝕜]
    [TopologicalSpace E]
    (p : MvPolynomial σ 𝕜) {φ : E → σ → 𝕜} {x₀ : E} {m : ℕ}
    (hφ : ContinuousAt φ x₀) (hm : ∀ᶠ x in 𝓝 x₀, p.orderAt (φ x) = m) :
    ∃ v : σ → 𝕜, ∀ᶠ x in 𝓝 x₀,
      analyticOrderAt (fun t : 𝕜 ↦ eval (φ x + t • v) p) 0 = m := by
  obtain ⟨v, hn, hv⟩ := p.exists_natTrailingDegree_aeval_C_add_C_mul_X_eq
    (φ x₀) hm.self_of_nhds
  have hc :
      Polynomial.coeff
        (aeval (fun i ↦ Polynomial.C (φ x₀ i) + Polynomial.C (v i) * Polynomial.X) p) m ≠ 0 := by
    rw [← hv]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.2 hn
  have hto : Tendsto φ (𝓝 x₀) (𝓝[{a | p.orderAt a = m}] (φ x₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ, hm⟩
  have hev := hto.eventually
    (p.eventually_natTrailingDegree_aeval_C_add_C_mul_X_eq (fun _ h ↦ h) hc)
  refine ⟨v, hev.mono fun x hx ↦ ?_⟩
  have heval := p.eval_aeval_C_add_C_mul_X (φ x) v
  rw [← _root_.funext heval, Polynomial.analyticOrderAt_eval_zero,
    Polynomial.trailingDegree_eq_natTrailingDegree hx.1, hx.2]

/-- Constant finite ambient order along an analytic parametrization gives a fixed direction
and a local power-times-unit factorization in the line parameter. -/
theorem exists_analyticAt_eval_add_smul_eq_pow_mul [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : MvPolynomial σ 𝕜) {φ : E → σ → 𝕜} {x₀ : E} {m : ℕ}
    (hφ : ∀ i, AnalyticAt 𝕜 (fun x ↦ φ x i) x₀)
    (hm : ∀ᶠ x in 𝓝 x₀, p.orderAt (φ x) = m) :
    ∃ v : σ → 𝕜, ∃ u : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 u (x₀, 0) ∧ u (x₀, 0) ≠ 0 ∧
        ∀ᶠ z in 𝓝 (x₀, 0), eval (φ z.1 + z.2 • v) p = z.2 ^ m * u z := by
  obtain ⟨v, hv⟩ := p.exists_eventually_analyticOrderAt_eval_add_smul_eq
    (continuousAt_pi.2 fun i ↦ (hφ i).continuousAt) hm
  have hG : AnalyticAt 𝕜 (fun z : E × 𝕜 ↦ eval (φ z.1 + z.2 • v) p) (x₀, 0) := by
    have hcoord (i : σ) :
        AnalyticAt 𝕜 (fun z : E × 𝕜 ↦ (φ z.1 + z.2 • v) i) (x₀, 0) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hf : AnalyticAt 𝕜 (fun z : E × 𝕜 ↦ z.1) (x₀, 0) := analyticAt_fst
      have hs : AnalyticAt 𝕜 (fun z : E × 𝕜 ↦ z.2) (x₀, 0) := analyticAt_snd
      exact ((hφ i).comp hf).add (hs.mul analyticAt_const)
    simpa only [aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hcoord p
  obtain ⟨u, hu, hu0, heq⟩ := hG.eventually_analyticOrderAt_eq_natCast_iff.1 hv
  exact ⟨v, u, hu, hu0, by simpa only [sub_zero, smul_eq_mul] using heq⟩

end MvPolynomial
