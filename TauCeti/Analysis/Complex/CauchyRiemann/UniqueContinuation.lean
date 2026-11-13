/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Unique continuation from a similarity factorization

The vector similarity principle (McDuff–Salamon, Theorem 2.3.5) writes a solution `ξ` of a linear
Cauchy–Riemann equation near each of its zeros `z₀` as `ξ = Φ σ`, with `Φ` a continuous family of
invertible real-linear maps and `σ` holomorphic. This file derives the consequences of that
factorization shape alone, without reference to the equation: `TauCeti.HasSimilarityFactorizationAt
ξ z₀` asks for such `Φ` and `σ` near `z₀`, with `Φ` continuous at `z₀` and invertible there and `σ`
complex analytic at `z₀`.

Since `Φ` is invertible near `z₀` with locally bounded inverse, `‖ξ‖` and `‖σ‖` are comparable
near `z₀` (`TauCeti.isTheta_clm_apply_of_isUnit`, in `TauCeti.Analysis.Normed.Operator.Basic`),
so `ξ` inherits from `σ` the zero structure of a holomorphic function. For a continuous `ξ` on an
open preconnected `Ω ⊆ ℂ` that admits a factorization at every zero in `Ω`:

* a solution vanishing on a nonempty open subset of `Ω`, or near one point, vanishes on `Ω`
  (`TauCeti.eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero`,
  `TauCeti.eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero`);
* a solution vanishing to infinite order at one point, `ξ = O(‖z - z₀‖ⁿ)` for every `n`, vanishes
  on `Ω` (`TauCeti.eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO`);
* otherwise the zeros are isolated (`TauCeti.eventually_ne_zero_of_hasSimilarityFactorizationAt`,
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt`) and each zero
  `z₀` has a finite positive order `m`, the analytic order of `σ` at `z₀` for any factorization,
  characterized by `‖ξ z‖ ≍ ‖z - z₀‖ ^ m`
  (`TauCeti.exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt`). That the order does not
  depend on the factorization is `TauCeti.analyticOrderAt_eq_of_eventually_eq_clm_apply`.

A scalar power factorization `f w = (w - z₀) ^ m * v w` at a zero `z₀`, with `v` continuous and
nonzero at `z₀`, is itself a similarity factorization with `Φ = v • id` and `σ = (· - z₀) ^ m`
(`TauCeti.hasSimilarityFactorizationAt_of_eventually_eq_pow_mul`). Then `m` is positive
(`TauCeti.pos_of_eventually_eq_pow_mul`), `‖f w‖ ≍ ‖w - z₀‖ ^ m`
(`TauCeti.isTheta_pow_of_eventually_eq_pow_mul`), and `m` is the analytic order of the holomorphic
factor of every factorization of `f` at `z₀`
(`TauCeti.analyticOrderAt_eq_of_eventually_eq_pow_mul`); the last two hold without assuming
`f z₀ = 0`.

For example, a continuous invertible family preserves quadratic vanishing:
`TauCeti.isTheta_clm_apply_sq_smul` shows that `Φ z (z ^ 2 • v)` has an isolated zero of order
`2` at `0` for every `Φ` continuous and invertible at `0` and `v ≠ 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3.
-/

public noncomputable section

open Asymptotics Filter Metric Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  {ξ σ σ' : ℂ → V} {Φ Φ' : ℂ → V →L[ℝ] V} {z₀ : ℂ} {Ω : Set ℂ}

section Local

/-- `ξ` factors near `z₀` as `Φ σ`, with `Φ` a family of real-linear maps continuous at `z₀`
and invertible there, and `σ` complex analytic at `z₀`. This is the local shape in which the
vector similarity principle presents a solution of a linear Cauchy–Riemann equation near a zero.
-/
def HasSimilarityFactorizationAt (ξ : ℂ → V) (z₀ : ℂ) : Prop :=
  ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ ∧ IsUnit (Φ z₀) ∧
    AnalyticAt ℂ σ z₀ ∧ ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)

omit [CompleteSpace V] in
/-- The local factorization unfolded into its defining data. -/
theorem hasSimilarityFactorizationAt_iff : HasSimilarityFactorizationAt ξ z₀ ↔
    ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ ∧ IsUnit (Φ z₀) ∧
      AnalyticAt ℂ σ z₀ ∧ ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z) :=
  Iff.rfl

/-- The disc form of the factorization: `ξ = Φ σ` on a disc about `z₀`, with `Φ` continuous on
the disc and invertible at `z₀`, and `σ` complex differentiable on the disc. -/
theorem HasSimilarityFactorizationAt.of_eqOn_ball {r : ℝ} (hr : 0 < r)
    (hΦ : ContinuousOn Φ (ball z₀ r)) (hΦ₀ : IsUnit (Φ z₀)) (hσ : DifferentiableOn ℂ σ (ball z₀ r))
    (hξ : EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r)) : HasSimilarityFactorizationAt ξ z₀ :=
  ⟨Φ, σ, hΦ.continuousAt (ball_mem_nhds z₀ hr), hΦ₀,
    hσ.analyticAt (ball_mem_nhds z₀ hr), eventually_of_mem (ball_mem_nhds z₀ hr) hξ⟩

omit [CompleteSpace V] in
/-- A family of real-linear maps continuous at `z₀` and invertible there carries a factorization of
`η` at `z₀` to one of `z ↦ Φ z (η z)`. This reduces factorizations for a variable complex
structure to the standard one. -/
theorem HasSimilarityFactorizationAt.clm_apply {η : ℂ → V} (h : HasSimilarityFactorizationAt η z₀)
    (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀)) :
    HasSimilarityFactorizationAt (fun z ↦ Φ z (η z)) z₀ := by
  obtain ⟨Φ', σ, hΦ', hΦ'₀, hσ, hη⟩ := h
  exact ⟨fun z ↦ Φ z ∘L Φ' z, σ, hΦ.clm_comp hΦ', hΦ₀.mul hΦ'₀, hσ,
    hη.mono fun z hz ↦ by simp [hz]⟩

omit [CompleteSpace V] in
/-- A function analytic at `z₀` factors there with `Φ = 1`. -/
theorem _root_.AnalyticAt.hasSimilarityFactorizationAt (hξ : AnalyticAt ℂ ξ z₀) :
    HasSimilarityFactorizationAt ξ z₀ :=
  ⟨fun _ ↦ 1, ξ, continuousAt_const, isUnit_one, hξ, by simp⟩

/-- A function factoring near `z₀` as `Φ σ`, with `Φ` continuous and invertible at `z₀`, is
comparable in size to `σ` near `z₀`. -/
theorem isTheta_of_eventually_eq_clm_apply (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀))
    (hξ : ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) : ξ =Θ[𝓝 z₀] σ :=
  EventuallyEq.trans_isTheta hξ (isTheta_clm_apply_of_isUnit hΦ hΦ₀)

/-- For a factorization `ξ = Φ σ` near `z₀`, the analytic order of `σ` at `z₀` is `n` exactly when
`‖ξ z‖` is comparable to `‖z - z₀‖ ^ n` near `z₀`. -/
theorem analyticOrderAt_eq_natCast_iff_isTheta_of_eventually_eq_clm_apply
    (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀)) (hσ : AnalyticAt ℂ σ z₀)
    (hξ : ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) {n : ℕ} :
    analyticOrderAt σ z₀ = n ↔ ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  have h := isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hξ
  rw [hσ.analyticOrderAt_eq_natCast_iff_isTheta]
  exact ⟨h.trans, h.symm.trans⟩

/-- For a factorization `ξ = Φ σ` near `z₀`, the analytic order of `σ` at `z₀` is infinite exactly
when `ξ` vanishes near `z₀`. -/
theorem analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply
    (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀)) (hξ : ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) :
    analyticOrderAt σ z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, ξ z = 0 := by
  have h := isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hξ
  rw [analyticOrderAt_eq_top]
  exact ⟨fun hσ ↦ isBigO_zero_right_iff.1 (h.isBigO.trans_eventuallyEq hσ),
    fun hξ₀ ↦ isBigO_zero_right_iff.1 (h.isBigO_symm.trans_eventuallyEq hξ₀)⟩

/-- For a factorization `ξ = Φ σ` near `z₀`, the analytic order of `σ` at `z₀` is infinite exactly
when `ξ` vanishes to infinite order at `z₀`. -/
theorem analyticOrderAt_eq_top_iff_forall_isBigO_of_eventually_eq_clm_apply
    (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀)) (hσ : AnalyticAt ℂ σ z₀)
    (hξ : ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) :
    analyticOrderAt σ z₀ = ⊤ ↔ ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  have h := isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hξ
  rw [hσ.analyticOrderAt_eq_top_iff_forall_isBigO]
  exact ⟨fun H n ↦ h.isBigO.trans (H n), fun H n ↦ h.isBigO_symm.trans (H n)⟩

/-- The analytic order of `σ` in a factorization `ξ = Φ σ` near `z₀` does not depend on the
factorization. -/
theorem analyticOrderAt_eq_of_eventually_eq_clm_apply
    (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀)) (hσ : AnalyticAt ℂ σ z₀)
    (hξ : ∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z))
    (hΦ' : ContinuousAt Φ' z₀) (hΦ'₀ : IsUnit (Φ' z₀)) (hσ' : AnalyticAt ℂ σ' z₀)
    (hξ' : ∀ᶠ z in 𝓝 z₀, ξ z = Φ' z (σ' z)) :
    analyticOrderAt σ z₀ = analyticOrderAt σ' z₀ := by
  refine hσ.analyticOrderAt_eq_of_isTheta hσ' ?_
  exact (isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hξ).symm.trans
    (isTheta_of_eventually_eq_clm_apply hΦ' hΦ'₀ hξ')

/-- A scalar power factorization `f w = (w - z₀) ^ m * v w` near `z₀`, with `v` continuous and
nonzero at `z₀`, is a similarity factorization of `f` at `z₀`. -/
theorem hasSimilarityFactorizationAt_of_eventually_eq_pow_mul {f : ℂ → ℂ} {m : ℕ} {v : ℂ → ℂ}
    (hv : ContinuousAt v z₀) (hv₀ : v z₀ ≠ 0) (hfv : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ m * v w) :
    HasSimilarityFactorizationAt f z₀ := by
  refine hasSimilarityFactorizationAt_iff.2 ⟨fun w ↦ v w • ContinuousLinearMap.id ℝ ℂ,
    fun w ↦ (w - z₀) ^ m, hv.smul continuousAt_const,
    ContinuousLinearMap.isUnit_smul_id_of_ne_zero hv₀, by fun_prop, ?_⟩
  filter_upwards [hfv] with w hw
  simp [hw, mul_comm]

/-- A power factorization `f w = (w - z₀) ^ m * v w` near `z₀`, with `v` continuous and nonzero at
`z₀`, makes `‖f w‖` comparable to `‖w - z₀‖ ^ m` near `z₀`. -/
theorem isTheta_pow_of_eventually_eq_pow_mul {f : ℂ → ℂ} {m : ℕ} {v : ℂ → ℂ}
    (hv : ContinuousAt v z₀) (hv₀ : v z₀ ≠ 0) (hfv : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ m * v w) :
    f =Θ[𝓝 z₀] fun w ↦ (w - z₀) ^ m :=
  EventuallyEq.trans_isTheta hfv <| by
    simpa using (isTheta_refl (fun w ↦ (w - z₀) ^ m) (𝓝 z₀)).mul (hv.isTheta (F := ℂ) hv₀)

/-- The exponent of a power factorization `f w = (w - z₀) ^ m * v w` at a zero `z₀` of `f`, with
`v z₀ ≠ 0`, is positive. -/
theorem pos_of_eventually_eq_pow_mul {f : ℂ → ℂ} (hf₀ : f z₀ = 0) {m : ℕ} {v : ℂ → ℂ}
    (hv₀ : v z₀ ≠ 0) (hfv : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ m * v w) : 0 < m :=
  Nat.pos_of_ne_zero fun h0 ↦ hv₀ <| by simpa [h0, hf₀] using hfv.self_of_nhds.symm

/-- **Orders of zeros** from a power factorization. If `f : ℂ → ℂ` has a power factorization
`f w = (w - z₀) ^ m * v w` near `z₀`, with `v` continuous and nonzero at `z₀`, such as the one of
`TauCeti.exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul` for a solution of
`bar∂ f = a f` not vanishing near `z₀`, then `m` is the analytic order at `z₀` of the holomorphic
factor `σ` of every similarity factorization `f = Φ σ` near `z₀`. -/
theorem analyticOrderAt_eq_of_eventually_eq_pow_mul {f : ℂ → ℂ} {m : ℕ} {v : ℂ → ℂ}
    (hv : ContinuousAt v z₀) (hv₀ : v z₀ ≠ 0) (hfv : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ m * v w)
    {Φ : ℂ → ℂ →L[ℝ] ℂ} {σ : ℂ → ℂ} (hΦ : ContinuousAt Φ z₀) (hΦ₀ : IsUnit (Φ z₀))
    (hσ : AnalyticAt ℂ σ z₀) (hfΦ : ∀ᶠ w in 𝓝 z₀, f w = Φ w (σ w)) :
    analyticOrderAt σ z₀ = m :=
  (analyticOrderAt_eq_natCast_iff_isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hσ hfΦ).2
    (isTheta_pow_of_eventually_eq_pow_mul hv hv₀ hfv)

/-- A function factoring at `z₀` either vanishes near `z₀` or has no zeros in a punctured
neighbourhood of `z₀`. -/
theorem HasSimilarityFactorizationAt.eventually_eq_zero_or_eventually_ne_zero
    (h : HasSimilarityFactorizationAt ξ z₀) :
    (∀ᶠ z in 𝓝 z₀, ξ z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  obtain ⟨Φ, σ, hΦ, hΦ₀, hσ, hξ⟩ := h
  refine hσ.eventually_eq_zero_or_eventually_ne_zero.imp
    (fun hσ₀ ↦ (analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply hΦ hΦ₀ hξ).1
      (analyticOrderAt_eq_top.2 hσ₀)) fun hσ₀ ↦ ?_
  filter_upwards [hσ₀, nhdsWithin_le_nhds hξ,
    nhdsWithin_le_nhds (hΦ.eventually (Units.isOpen.mem_nhds hΦ₀))] with z hz hzξ hzΦ
  rw [hzξ]
  exact fun h0 ↦ hz ((injective_iff_map_eq_zero _).1
    ((ContinuousLinearMap.isUnit_iff_bijective.1 hzΦ).1) _ h0)

end Local

section Global

/-- At every point of `Ω`, a continuous function factoring at each of its zeros in `Ω` either
vanishes near the point or has no zeros in a punctured neighbourhood of it. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_hasSimilarityFactorizationAt
    (hΩ : IsOpen Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∀ᶠ z in 𝓝 z₀, ξ z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  by_cases h0 : ξ z₀ = 0
  · exact (hfac z₀ hz₀ h0).eventually_eq_zero_or_eventually_ne_zero
  · exact .inr (nhdsWithin_le_nhds
      ((hξ.continuousAt (hΩ.mem_nhds hz₀)).eventually_ne h0))

/-- **Unique continuation.** On an open preconnected `Ω`, a continuous function factoring at each
of its zeros in `Ω` and vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) : EqOn ξ 0 Ω := by
  -- the points near which `ξ` vanishes and the points of `Ω` near which it does not are open
  let u : Set ℂ := {z | ∀ᶠ w in 𝓝 z, ξ w = 0}
  let v : Set ℂ := {z | z ∈ Ω ∧ ¬ ∀ᶠ w in 𝓝 z, ξ w = 0}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨hz, hnot⟩ ↦ ?_
    have hne := (eventually_eq_zero_or_eventually_ne_zero_of_hasSimilarityFactorizationAt
      hΩ hξ hfac hz).resolve_left hnot
    filter_upwards [hΩ.mem_nhds hz, eventually_nhdsWithin_iff.1 hne] with w hw hwne
    refine ⟨hw, fun hw₀ ↦ ?_⟩
    rcases eq_or_ne w z with rfl | hwz
    · exact hnot hw₀
    · exact hwne hwz hw₀.self_of_nhds
  have hsub : Ω ⊆ u := hΩc.subset_left_of_subset_union hu hv
    (disjoint_left.2 fun _ hzu hzv ↦ hzv.2 hzu)
    (fun z hz ↦ (em (z ∈ u)).imp_right fun h ↦ ⟨hz, h⟩) ⟨z₀, hz₀, h₀⟩
  exact fun z hz ↦ (hsub hz).self_of_nhds

/-- **Unique continuation.** On an open preconnected `Ω`, a continuous function factoring at each
of its zeros in `Ω` and vanishing on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) {U : Set ℂ} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ hfac
    (hUΩ hz₀) (eventually_of_mem (hU.mem_nhds hz₀) h₀)

/-- **Unique continuation from a zero of infinite order.** On an open preconnected `Ω`, a
continuous function factoring at each of its zeros in `Ω` and satisfying `ξ = O(‖z - z₀‖ⁿ)` near
one point `z₀ ∈ Ω` for every `n` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have hξ₀ : ξ z₀ = 0 := by
    obtain ⟨c, hc⟩ := (h₀ 1).bound
    simpa using hc.self_of_nhds
  obtain ⟨Φ, σ, hΦ, hΦ₀, hσ, hfz⟩ := hfac z₀ hz₀ hξ₀
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ hfac hz₀
    ((analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply hΦ hΦ₀ hfz).1
      ((analyticOrderAt_eq_top_iff_forall_isBigO_of_eventually_eq_clm_apply hΦ hΦ₀ hσ hfz).2 h₀))

/-- **Isolated zeros.** On an open preconnected `Ω`, a continuous function factoring at each of
its zeros in `Ω` and not identically zero on `Ω` has no zeros in a punctured neighbourhood of any
point of `Ω`. -/
theorem eventually_ne_zero_of_hasSimilarityFactorizationAt
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) (hne : ∃ z ∈ Ω, ξ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  refine (eventually_eq_zero_or_eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hξ hfac
    hz₀).resolve_left fun h₀ ↦ ?_
  obtain ⟨z, hz, hξz⟩ := hne
  exact hξz (eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ hfac
    hz₀ h₀ hz)

/-- **Isolated zeros.** On an open preconnected `Ω`, the zeros of a continuous function factoring
at each of its zeros in `Ω` and not identically zero on `Ω` form a discrete subset of `Ω`:
their complement is codiscrete within `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  refine mem_codiscreteWithin.2 fun z₀ hz₀ ↦ ?_
  rw [disjoint_principal_right]
  filter_upwards [eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hΩc hξ hfac hne hz₀]
    with z hz hmem
  exact hmem.2 hz

/-- **Positive orders.** On an open preconnected `Ω`, let `ξ` be continuous, factoring at each of
its zeros in `Ω`, and not identically zero on `Ω`. At a zero `z₀ ∈ Ω`, every factorization
`ξ = Φ σ` has `σ` of the same finite positive analytic order `m`, and `‖ξ z‖` is comparable to
`‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContinuousOn ξ Ω)
    (hfac : ∀ z ∈ Ω, ξ z = 0 → HasSimilarityFactorizationAt ξ z) (hne : ∃ z ∈ Ω, ξ z ≠ 0)
    (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  obtain ⟨Φ, σ, hΦ, hΦ₀, hσ, hfz⟩ := hfac z₀ hz₀ hξ₀
  have htop : analyticOrderAt σ z₀ ≠ ⊤ := fun htop ↦ by
    obtain ⟨z, hz, hξz⟩ := hne
    exact hξz (eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ hfac
      hz₀ ((analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply hΦ hΦ₀ hfz).1 htop) hz)
  have hm := Nat.cast_analyticOrderNatAt htop
  refine ⟨analyticOrderNatAt σ z₀, ?_,
    (analyticOrderAt_eq_natCast_iff_isTheta_of_eventually_eq_clm_apply hΦ hΦ₀ hσ hfz).1 hm.symm,
    fun Φ' σ' hΦ' hΦ'₀ hσ' hfz' ↦
      (analyticOrderAt_eq_of_eventually_eq_clm_apply hΦ' hΦ'₀ hσ' hfz' hΦ hΦ₀ hσ hfz).trans
        hm.symm⟩
  -- `σ` vanishes at `z₀` because `Φ z₀` is injective
  have hσ₀ : σ z₀ = 0 := (injective_iff_map_eq_zero _).1
    (ContinuousLinearMap.isUnit_iff_bijective.1 hΦ₀).1 _ (hfz.self_of_nhds ▸ hξ₀)
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  rw [h0, Nat.cast_zero] at hm
  exact (hσ.analyticOrderAt_ne_zero.2 hσ₀) hm.symm

end Global

/-- **Example.** For `v ≠ 0` and any family `Φ` continuous and invertible at `0`, the function
`z ↦ Φ z (z ^ 2 • v)` has an isolated zero at `0`, comparable in size to `‖z‖ ^ 2`, and the
holomorphic factor `z ↦ z ^ 2 • v` has order `2` there. -/
theorem isTheta_clm_apply_sq_smul {v : V} (hv : v ≠ 0) (hΦ : ContinuousAt Φ 0)
    (hΦ₀ : IsUnit (Φ 0)) :
    analyticOrderAt (fun z : ℂ ↦ z ^ 2 • v) 0 = 2 ∧
      ((fun z ↦ Φ z (z ^ 2 • v)) =Θ[𝓝 0] fun z : ℂ ↦ z ^ 2) ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), Φ z (z ^ 2 • v) ≠ 0 := by
  have hσ : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2 • v) 0 := by fun_prop
  have hord : analyticOrderAt (fun z : ℂ ↦ z ^ 2 • v) 0 = 2 := by
    exact_mod_cast (hσ.analyticOrderAt_eq_natCast (n := 2)).2
      ⟨fun _ ↦ v, analyticAt_const, hv, by simp⟩
  refine ⟨hord, by simpa using (analyticOrderAt_eq_natCast_iff_isTheta_of_eventually_eq_clm_apply
    (ξ := fun z ↦ Φ z (z ^ 2 • v)) hΦ hΦ₀ hσ (by simp) (n := 2)).1 hord, ?_⟩
  refine (HasSimilarityFactorizationAt.eventually_eq_zero_or_eventually_ne_zero
    ⟨Φ, _, hΦ, hΦ₀, hσ, Eventually.of_forall fun _ ↦ rfl⟩).resolve_left fun h ↦ ?_
  have := (analyticOrderAt_eq_top_iff_of_eventually_eq_clm_apply hΦ hΦ₀
    (Eventually.of_forall fun _ ↦ rfl)).2 h
  rw [hord] at this
  exact ENat.natCast_ne_top 2 this

end TauCeti
