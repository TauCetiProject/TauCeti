/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension

/-!
# The trace of a bounded Lipschitz domain does not depend on the exponent

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain and `1 ≤ p ≤ q < ∞`. Since `Ω` has finite measure,
`W^{1,q}(Ω) ⊆ W^{1,p}(Ω)`, and each of the two spaces has its trace operator
`TauCeti.W1p.frontierTrace` onto the frontier. This file proves that they agree: if `u ∈ W^{1,q}(Ω)`
and `v ∈ W^{1,p}(Ω)` have the same value almost everywhere on `Ω`, then their traces agree almost
everywhere on the frontier for surface measure
(`TauCeti.W1p.frontierTrace_ae_eq_of_value_ae_eq`). Both traces are limits of the boundary values
of the same test functions, which approximate `u` in `W^{1,q}(Ω)` and hence also in `W^{1,p}(Ω)`,
and limits in measure are unique.

Since `W^{1,p}_0(Ω)` is the kernel of the trace, zero boundary values pass from the smaller
exponent to the larger one (`TauCeti.W1p.mem_w1p0Submodule_of_value_ae_eq`): if the value of
`u ∈ W^{1,q}(Ω)` is that of some `v ∈ W^{1,p}_0(Ω)`, then `u ∈ W^{1,q}_0(Ω)`. This is the form in
which boundary conditions survive the gain of integrability in regularity theory. The other
direction, from `W^{1,q}_0(Ω)` to `W^{1,p}_0(Ω)`, holds on every open set of finite measure
(`TauCeti.W1p.ofExponentLE_mem_w1p0Submodule`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorems 1 and 2 (the trace
  operator and its kernel).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Module
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **The trace does not depend on the exponent.** Let `Ω` be a bounded Lipschitz domain and
`1 ≤ p ≤ q < ∞`. If `u ∈ W^{1,q}(Ω)` and `v ∈ W^{1,p}(Ω)` have almost everywhere equal values on
`Ω`, then their traces agree almost everywhere on the frontier for surface measure. -/
theorem W1p.frontierTrace_ae_eq_of_value_ae_eq (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p ≤ q)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω q}
    {v : W1p volume Ω p}
    (huv : W1p.value v =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) :
    W1p.frontierTrace hp hΩ hb v =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))] W1p.frontierTrace hq hΩ hb u := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  -- Test functions `φₖ` whose restrictions `aₖ` tend to `u` in `W^{1,q}(Ω)`.
  obtain ⟨a, ha, hau⟩ := mem_closure_iff_seq_limit.1
    (W1p.denseRange_restrictL_ofTestFunctionₗ_top hq hΩ hb u)
  choose φ hφ using ha
  -- Lowering the exponent, the same functions tend to `v` in `W^{1,p}(Ω)`.
  have hv : W1p.ofExponentLEL hpq u = v := W1p.ext_value <| Lp.ext <| by
    rw [W1p.value_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    exact huv.symm
  have hav := ((W1p.ofExponentLEL hpq).continuous.tendsto u).comp hau
  rw [hv] at hav
  -- Both traces of `aₖ` are the restrictions of `φₖ` to the frontier.
  have hφa : ∀ k, (W1p.frontierTrace hp hΩ hb (W1p.ofExponentLEL hpq (a k)) :
      WithLp 2 (ℝ × E) → ℝ) =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] W1p.frontierTrace hq hΩ hb (a k) := fun k => by
    have hval : W1p.value (a k) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] φ k := by
      rw [← hφ k]
      exact W1p.value_restrictL_ofTestFunctionₗ_ae le_top (φ k)
    refine (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb (φ k).continuous.continuousOn ?_).trans
      (W1p.frontierTrace_ae_eq_of_continuousOn hq hΩ hb (φ k).continuous.continuousOn hval).symm
    rw [W1p.value_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    exact hval
  have hp' := tendstoInMeasure_of_tendsto_Lp
    (((W1p.frontierTrace hp hΩ hb).continuous.tendsto v).comp hav)
  have hq' := tendstoInMeasure_of_tendsto_Lp
    (((W1p.frontierTrace hq hΩ hb).continuous.tendsto u).comp hau)
  exact tendstoInMeasure_ae_unique (hp'.congr_left fun k => hφa k) hq'

/-- **Zero boundary values gain integrability.** Let `Ω` be a bounded Lipschitz domain and
`1 ≤ p ≤ q < ∞`. If `u ∈ W^{1,q}(Ω)` has almost everywhere the value of some `v ∈ W^{1,p}_0(Ω)`,
then `u ∈ W^{1,q}_0(Ω)`. -/
theorem W1p.mem_w1p0Submodule_of_value_ae_eq (hp : p ≠ ∞) (hq : q ≠ ∞) (hpq : p ≤ q)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω q}
    {v : W1p volume Ω p} (hv : v ∈ w1p0Submodule volume Ω p)
    (huv : W1p.value v =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) :
    u ∈ w1p0Submodule volume Ω q := by
  rw [W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero hq hΩ hb]
  rw [W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero hp hΩ hb] at hv
  refine Lp.ext ((W1p.frontierTrace_ae_eq_of_value_ae_eq hp hq hpq hΩ hb huv).symm.trans ?_)
  rw [hv]
  exact (Lp.coeFn_zero _ _ _).trans (Lp.coeFn_zero _ _ _).symm

end TauCeti

end
