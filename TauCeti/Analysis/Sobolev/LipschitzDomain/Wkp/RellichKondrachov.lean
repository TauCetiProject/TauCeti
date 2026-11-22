/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.Wkp.Compactness

/-!
# Higher-order Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E`, `1 ≤ p ≤ ∞` and every natural `k`, forgetting the
highest weak derivative is a compact operator `W^{k+1,p}(Ω) → W^{k,p}(Ω)`. Unlike the interior
statement `TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, no restriction to a compactly
contained subdomain is needed: the estimate holds up to the boundary.

The proof applies the domain-independent lifting
`TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isCompactOperator_valueL` to the first-order theorem
`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`. That lifting inducts on the order:
the lower-order component is compact by induction, and the highest retained derivative field is
compact coordinatewise, since each scalar coordinate is a `W^{1,p}(Ω)` function.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith`: compactness of
  `W^{k+1,p}(Ω) → W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith`: a bounded sequence in
  `W^{k+1,p}(Ω)` has a subsequence converging in `W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_pos_mul_norm_le_of_mem_w1p0Submodule`: **Peetre's argument**: an operator
  `T : W^{2,p}(Ω) → Lᵖ(Ω)` with `‖u‖ ≤ D (‖T u‖ + ‖u‖_{Lᵖ})` that is injective on functions with
  zero boundary values is bounded below there.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 6.3, part I; the
  higher-order statement follows by applying the first-order theorem to the weak derivatives.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **Higher-order Rellich–Kondrachov on bounded Lipschitz domains.** If `Ω` is a bounded
Lipschitz domain and `1 ≤ p ≤ ∞`, forgetting the highest weak derivative is a compact operator
`W^{k+1,p}(Ω) → W^{k,p}(Ω)` for every `k`. -/
theorem isCompactOperator_lowerOrderL_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∀ k : ℕ, IsCompactOperator (lowerOrderL (mu := volume) (Omega := Ω) (p := p) k) :=
  isCompactOperator_lowerOrderL_of_isCompactOperator_valueL
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb)

/-- On a bounded Lipschitz domain, a bounded sequence in `W^{k+1,p}(Ω)` has a subsequence whose
lower-order parts converge in `W^{k,p}(Ω)`, for `1 ≤ p ≤ ∞`. -/
theorem exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ)
    {u : ℕ → Wkp volume Ω p (k + 1)} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ w : Wkp volume Ω p k, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ lowerOrder k (u (φ n))) atTop (𝓝 w) := by
  obtain ⟨w, φ, hφ, hw⟩ :=
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith hΩ hb k).exists_subseq_tendsto hu
  refine ⟨w, φ, hφ, ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, lowerOrderL_apply k (u (φ _))] using hw

/-- **Peetre's argument on `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`.** On a bounded Lipschitz domain, an operator
`T : W^{2,p}(Ω) → Lᵖ(Ω)` with `‖u‖ ≤ D (‖T u‖ + ‖u‖_{Lᵖ})` that is injective on functions with zero
boundary values is bounded below there. -/
theorem exists_pos_mul_norm_le_of_mem_w1p0Submodule
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (T : Wkp volume Ω p 2 →L[ℝ] Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Ω))
    {D : ℝ}
    (hest : ∀ u, firstOrder 1 u ∈ w1p0Submodule volume Ω p → ‖u‖ ≤ D * (‖T u‖ + ‖value 2 u‖))
    (hinj : ∀ u, firstOrder 1 u ∈ w1p0Submodule volume Ω p → T u = 0 → u = 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ u, firstOrder 1 u ∈ w1p0Submodule volume Ω p → κ * ‖u‖ ≤ ‖T u‖ := by
  -- The closed subspace `M` of zero boundary values, a Banach space.
  let M : Submodule ℝ (Wkp volume Ω p 2) :=
    (w1p0Submodule volume Ω p).toSubmodule.comap (firstOrderL 1).toLinearMap
  have hmemM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume Ω p := fun u => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, firstOrderL_apply,
      ClosedSubmodule.mem_toSubmodule_iff]
  have : CompleteSpace M :=
    ((w1p0Submodule volume Ω p).isClosed.preimage (firstOrderL 1).continuous).completeSpace_coe
  -- On `M`, `‖u‖ ≤ D' ‖T u‖ + ‖K u‖` with `K = D' • valueL 2` compact, `D' = max D 0`.
  have hK : IsCompactOperator ((max D 0 • valueL 2).comp M.subtypeL) :=
    ((isCompactOperator_valueL_of_isCompactOperator_lowerOrderL
      (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith hΩ hb 1)).smul (max D 0)).comp_clm _
  have hbound : ∀ w : M,
      ‖w‖ ≤ max D 0 * ‖T.comp M.subtypeL w‖ + ‖(max D 0 • valueL 2).comp M.subtypeL w‖ :=
    fun w => by
      have hn := mul_le_mul_of_nonneg_right (le_max_left D 0) (add_nonneg (norm_nonneg (T w))
        (norm_nonneg (value 2 (w : Wkp volume Ω p 2))))
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, smul_apply,
        valueL_apply 2 (w : Wkp volume Ω p 2), norm_smul, Real.norm_of_nonneg (le_max_right D 0),
        ← Submodule.norm_coe]
      linarith [hest w ((hmemM _).1 w.property)]
  have hker : Disjoint (T.comp M.subtypeL).ker ⊤ := by
    rw [disjoint_top, LinearMap.ker_eq_bot']
    intro w hw
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply] at hw
    exact Subtype.ext (hinj w ((hmemM _).1 w.property) hw)
  obtain ⟨κ, hκ, hκb⟩ := (T.comp M.subtypeL).exists_pos_mul_norm_le_of_compact_estimate hK hbound
    isClosed_univ hker
  refine ⟨κ, hκ, fun u hu0 => ?_⟩
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ← Submodule.norm_coe]
    using hκb ⟨u, (hmemM u).2 hu0⟩ trivial

end Wkp

end TauCeti
