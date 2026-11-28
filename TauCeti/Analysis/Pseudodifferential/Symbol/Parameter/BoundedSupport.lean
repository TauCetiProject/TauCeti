/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Dilation

/-!
# Parameter-dependent symbols with bounded support

A strongly parameter-dependent symbol (`TauCeti.ParameterSymbol`) is estimated by powers of the
weight `w = 1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` of the frequency `ξ` and the spectral parameter `z`. A smooth
function whose support is bounded in `(ξ, z)` jointly satisfies the estimates of every order,
since `w` is bounded on its support: it is a smoothing parameter-dependent symbol
(`TauCeti.ParameterSymbol.ofBoundedSupport`,
`TauCeti.ParameterSymbol.isSmoothing_ofBoundedSupport`).
Such symbols are the corrections near `(ξ, z) = (0, 0)` that make the symbol of an elliptic
operator minus a spectral parameter elliptic with parameter on a neighbourhood of the negative
real axis, `z = 0` included, as in Seeley's construction of complex powers.

The estimates rest on the bound `TauCeti.norm_parameterIteratedFDeriv_le` for the dilated
derivatives: at `((x, ξ), z)`, the dilated derivative of order `k` is at most the ordinary one
times `w ^ (2 k)`.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

namespace ParameterSymbol

variable {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- On the points whose frequency and spectral parameter have norm at most `R`, the weight is at
most `1 + R + R ^ (1 / 2)`. -/
private theorem parameterWeight_le_of_norm_le {R : ℝ} {ξ : CoordinateSpace n} {z : ℂ}
    (hξ : ‖ξ‖ ≤ R) (hz : ‖z‖ ≤ R) : parameterWeight ξ z ≤ 1 + R + Real.sqrt R := by
  rw [parameterWeight_def]
  gcongr

/-- On the points whose frequency and spectral parameter have norm at most `R`,
`1 ≤ (1 + R + R ^ (1 / 2)) ^ |m| * parameterWeight ξ z ^ m`. -/
private theorem one_le_rpow_abs_mul_parameterWeight_rpow {R : ℝ} {ξ : CoordinateSpace n} {z : ℂ}
    (hξ : ‖ξ‖ ≤ R) (hz : ‖z‖ ≤ R) (m : ℝ) :
    1 ≤ (1 + R + Real.sqrt R) ^ |m| * parameterWeight ξ z ^ m := by
  have hw := one_le_parameterWeight ξ z
  have hW := parameterWeight_le_of_norm_le hξ hz
  have hW1 : 0 < 1 + R + Real.sqrt R := by linarith
  calc (1 : ℝ) = (1 + R + Real.sqrt R) ^ |m| * (1 + R + Real.sqrt R) ^ (-|m|) := by
        rw [← Real.rpow_add hW1, add_neg_cancel, Real.rpow_zero]
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (Real.rpow_le_rpow_of_nonpos (by linarith) hW (neg_nonpos.2 (abs_nonneg m))).trans
        (Real.rpow_le_rpow_of_exponent_le hw (neg_abs_le m))

open scoped Classical in
/-- A smooth function `f((x, ξ), z)` that vanishes as soon as `‖(ξ, z)‖ = max ‖ξ‖ ‖z‖` exceeds `R`,
as a parameter-dependent symbol of any order `m` on `Λ`. On its support the weight
`1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is bounded, so all the estimates hold, and the symbol is smoothing
(`TauCeti.ParameterSymbol.isSmoothing_ofBoundedSupport`). -/
def ofBoundedSupport (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, R < ‖(p.1.2, p.2)‖ → f p = 0) :
    ParameterSymbol n Λ V W m where
  coefficient p := if p.2 ∈ Λ then f p else 0
  contDiffOn_coefficient := hf.contDiffOn.congr fun p hp => by simp [SetLike.mem_coe.1 hp.2]
  coefficient_of_notMem p hp := by simp [hp]
  exists_bound K hK k := by
    set R' := max R 0
    set B := 1 + R' + Real.sqrt R'
    -- The `k`-th derivative of `f` is bounded on the compact set where it may be nonzero.
    obtain ⟨C₀, hC₀⟩ := ((hK.prod (isCompact_closedBall (0 : CoordinateSpace n) R')).prod
      (isCompact_closedBall (0 : ℂ) R')).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn
    refine ⟨max C₀ 0 * (B ^ 2) ^ k * B ^ |m|, by positivity, fun x hx ξ z hz => ?_⟩
    have hcongr : (fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ =>
        if p.2 ∈ Λ then f p else 0) =ᶠ[𝓝 ((x, ξ), z)] f := by
      filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hz] with q hq
      simp [show q.2 ∈ Λ from hq]
    rw [parameterIteratedFDeriv_congr hcongr]
    by_cases hp : R < ‖(ξ, z)‖
    · -- Beyond `R`, the function vanishes near the point.
      have hzero : f =ᶠ[𝓝 ((x, ξ), z)] 0 := by
        filter_upwards [(isOpen_lt continuous_const (by fun_prop :
          Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × ℂ =>
            ‖(q.1.2, q.2)‖)).mem_nhds hp] with q hq
        exact hR q hq
      rw [parameterIteratedFDeriv_eq_zero_of_eventuallyEq_zero hzero, norm_zero]
      have := (Real.rpow_pos_of_pos (parameterWeight_pos ξ z) m).le
      positivity
    · rw [not_lt, Prod.norm_def, max_le_iff] at hp
      have hξ : ‖ξ‖ ≤ R' := hp.1.trans (le_max_left R 0)
      have hz' : ‖z‖ ≤ R' := hp.2.trans (le_max_left R 0)
      have hw := one_le_parameterWeight ξ z
      have hwB : parameterWeight ξ z ≤ B := parameterWeight_le_of_norm_le hξ hz'
      have hmem : ((x, ξ), z) ∈ (K ×ˢ Metric.closedBall (0 : CoordinateSpace n) R') ×ˢ
          Metric.closedBall (0 : ℂ) R' :=
        Set.mk_mem_prod (Set.mk_mem_prod hx (mem_closedBall_zero_iff.2 hξ))
          (mem_closedBall_zero_iff.2 hz')
      have h0 : ‖iteratedFDeriv ℝ k f ((x, ξ), z)‖ ≤ max C₀ 0 :=
        (hC₀ _ hmem).trans (le_max_left _ _)
      calc ‖parameterIteratedFDeriv k f ((x, ξ), z)‖
          ≤ ‖iteratedFDeriv ℝ k f ((x, ξ), z)‖ * (parameterWeight ξ z ^ 2) ^ k :=
            norm_parameterIteratedFDeriv_le k f x ξ z
        _ ≤ max C₀ 0 * (B ^ 2) ^ k := by gcongr
        _ ≤ max C₀ 0 * (B ^ 2) ^ k * (B ^ |m| * parameterWeight ξ z ^ m) :=
            le_mul_of_one_le_right (by positivity)
              (one_le_rpow_abs_mul_parameterWeight_rpow hξ hz' m)
        _ = _ := by ring

@[simp]
theorem coefficient_ofBoundedSupport (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, R < ‖(p.1.2, p.2)‖ → f p = 0)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (ofBoundedSupport f hf R hR : ParameterSymbol n Λ V W m).coefficient ((x, ξ), z) =
      f ((x, ξ), z) := by
  simp [ofBoundedSupport, hz]

/-- **A symbol with bounded support in the frequency and the spectral parameter is smoothing.** -/
theorem isSmoothing_ofBoundedSupport
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, R < ‖(p.1.2, p.2)‖ → f p = 0) :
    (ofBoundedSupport f hf R hR : ParameterSymbol n Λ V W m).IsSmoothing :=
  isSmoothing_iff.2 fun _ => ⟨ofBoundedSupport f hf R hR, rfl⟩

end ParameterSymbol

end TauCeti
