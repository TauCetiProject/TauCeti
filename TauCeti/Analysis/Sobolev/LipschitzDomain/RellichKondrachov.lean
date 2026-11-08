/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Compactness
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `1 ≤ p < ∞`, the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. Unlike `TauCeti.W1p0.isCompactOperator_valueL`, this
concerns the whole Sobolev space, with no vanishing boundary values. The boundary regularity enters
only through the extension operator `TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the
value map factors as extension to the whole space followed by restriction to `Ω`, and the latter is
compact by local Rellich compactness (`TauCeti.W1p.isCompactOperator_valueL_restrictL`), since
`closure Ω` is compact.

Compactness then gives the Poincaré–Wirtinger inequality on bounded connected Lipschitz domains,
with a constant that is not explicit.

Compactness passes to every subcritical target exponent: if `Ω` has dimension `n`, `1 ≤ p < ∞`
and `1 ≤ q < ∞` with `1/p - 1/q < 1/n`, then `W^{1,p}(Ω) → L^q(Ω)` is compact. For `p < n` this is
the range `q < p⋆` below the Sobolev conjugate `1/p⋆ = 1/p - 1/n`, and for `p ≥ n` it is every
finite `q`. For `q ≤ p` the inclusion factors through `Lᵖ(Ω)`, as `Ω` has finite measure. For
`q > p` choose a finite `s > q` still in the subcritical range: the inclusion is bounded into
`L^s(Ω)` (`TauCeti.W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith`), and
`1/q = (1 - θ)/p + θ/s` with `0 ≤ θ < 1`, so the interpolation inequality
`‖u‖_{L^q} ≤ ‖u‖_{Lᵖ} ^ (1 - θ) ‖u‖_{L^s} ^ θ` transfers compactness from `Lᵖ(Ω)` to `L^q(Ω)`
(`IsCompactOperator.of_forall_ae_eq_of_interpolation`). The inequality `1/p - 1/q < 1/n` is
strict: at `q = p⋆` the inclusion is bounded but not compact.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`.
* `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith`: the
  Poincaré–Wirtinger inequality on a bounded connected Lipschitz domain.
* `TauCeti.W1p.exists_isCompactOperator_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → L^q(Ω)` for every subcritical `q`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.7, Theorem 1, and §5.8.1, Theorem 1.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 6.3.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich–Kondrachov on bounded Lipschitz domains.** If `Ω` is a bounded Lipschitz domain and
`1 ≤ p < ∞`, the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hK := W1p.isCompactOperator_valueL_restrictL (mu := volume) (Omega := ⊤) (V := Ω) hp
    hb.isCompact_closure (subset_univ _)
  -- The value map is the value of the restriction of the extension.
  have heq : W1p.valueL (mu := volume) (Omega := Ω) (p := p) =
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)).comp T := by
    rw [ContinuousLinearMap.comp_assoc, hT, ContinuousLinearMap.comp_id]
  rw [heq]
  exact hK.comp_clm T

/-- **The Poincaré–Wirtinger inequality on bounded connected Lipschitz domains.** Let `Ω` be a
bounded, preconnected Lipschitz domain, let `S ⊆ Ω` have positive measure, and let `1 ≤ p < ∞`.
There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at
most `C` times the `Lᵖ` norm of its weak gradient. -/
theorem W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    {S : Set (WithLp 2 (ℝ × E))} (hS : S ⊆ Ω) (hS0 : volume S ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p volume Ω p,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y) p (volume.restrict Ω) ≤
        ENNReal.ofReal C * ‖W1p.gradient u‖ₑ :=
  W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hp hΩ hb) hconn
    hb.measure_lt_top.ne hS hS0

/-- For finite exponents `1 ≤ p ≤ q` and `1 ≤ n` with `1/p - 1/q < 1/n`, there are a finite
`s ≥ 1` with `1/p - 1/s < 1/n` and `0 ≤ θ < 1` with `1/q = (1 - θ)/p + θ/s`. -/
private theorem exists_interpolation_exponent {p q n : ℝ≥0∞} (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (hq₁ : 1 ≤ q) (hq : q ≠ ∞) (hn₁ : 1 ≤ n) (hn : n ≠ ∞) (hpq : p ≤ q)
    (h : p⁻¹ < q⁻¹ + n⁻¹) :
    ∃ s : ℝ≥0∞, ∃ θ : ℝ, 1 ≤ s ∧ s ≠ ∞ ∧ p⁻¹ < s⁻¹ + n⁻¹ ∧ 0 ≤ θ ∧ θ < 1 ∧
      q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * s⁻¹ := by
  -- Work with the reciprocals `a = 1/p`, `b = 1/q`, `ν = 1/n`.
  have hinv {r : ℝ≥0∞} (hr : 1 ≤ r) (hr' : r ≠ ∞) : r⁻¹ = ENNReal.ofReal r.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos (zero_lt_one.trans_le hr).ne' hr'),
      ENNReal.ofReal_toReal hr']
  rw [hinv hp₁ hp, hinv hq₁ hq, hinv hn₁ hn] at h ⊢
  set a := p.toReal⁻¹
  set b := q.toReal⁻¹
  set ν := n.toReal⁻¹
  have hb0 : 0 < b := inv_pos.2 (ENNReal.toReal_pos (zero_lt_one.trans_le hq₁).ne' hq)
  have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hq hq₁)
  have hν0 : 0 ≤ ν := inv_nonneg.2 ENNReal.toReal_nonneg
  have hba : b ≤ a := inv_anti₀ (ENNReal.toReal_pos (zero_lt_one.trans_le hp₁).ne' hp)
    (ENNReal.toReal_mono hq hpq)
  rw [← ENNReal.ofReal_add hb0.le hν0,
    ENNReal.ofReal_lt_ofReal_iff (add_pos_of_pos_of_nonneg hb0 hν0)] at h
  -- The reciprocal `c = 1/s` lies strictly between `max (a - ν) 0` and `b`.
  set c := (b + max (a - ν) 0) / 2
  have hmb : max (a - ν) 0 < b := max_lt (by linarith) hb0
  have hc0 : 0 < c := by have := le_max_right (a - ν) 0; simp only [c]; linarith
  have hcb : c < b := by simp only [c]; linarith
  have hac : a < c + ν := by have := le_max_left (a - ν) 0; simp only [c]; linarith
  have hs : (ENNReal.ofReal c⁻¹)⁻¹ = ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hc0), inv_inv]
  have hac' : 0 < a - c := by linarith
  have hθ0 : 0 ≤ (a - b) / (a - c) := div_nonneg (by linarith) hac'.le
  have hθ1 : (a - b) / (a - c) < 1 := (div_lt_one hac').2 (by linarith)
  have hθ : (a - b) / (a - c) * (a - c) = a - b := div_mul_cancel₀ _ hac'.ne'
  refine ⟨ENNReal.ofReal c⁻¹, (a - b) / (a - c),
    ENNReal.one_le_ofReal.2 ((one_le_inv₀ hc0).2 (by linarith)), ENNReal.ofReal_ne_top, ?_,
    hθ0, hθ1, ?_⟩
  · rwa [hs, ← ENNReal.ofReal_add hc0.le hν0,
      ENNReal.ofReal_lt_ofReal_iff (add_pos_of_pos_of_nonneg hc0 hν0)]
  · rw [hs, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hθ0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hθ0 hc0.le)]
    congr 1
    linear_combination hθ

/-- **Rellich–Kondrachov for subcritical target exponents.** Let `Ω ⊆ ℝ × E` be a bounded
Lipschitz domain of dimension `n`, let `1 ≤ p < ∞`, and let `1 ≤ q < ∞` with `1/p - 1/q < 1/n`.
Then the inclusion `W^{1,p}(Ω) → L^q(Ω)` is a compact operator. For `p < n` the condition says
`q < p⋆`, where `1/p⋆ = 1/p - 1/n`; for `p ≥ n` every finite `q` is allowed. -/
theorem W1p.exists_isCompactOperator_of_isLipschitzDomainWith (hp : p ≠ ∞) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ∞)
    (hpq : p⁻¹ < q⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ S : W1p volume Ω p →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      IsCompactOperator S ∧
        ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
  obtain ⟨S, hS⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hq hpq hΩ hb)
  refine ⟨S, ?_, hS⟩
  have hK := W1p.isCompactOperator_valueL_of_isLipschitzDomainWith (p := p) hp hΩ hb
  have hS₀ (u : W1p volume Ω p) :
      ⇑(S u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] ⇑(W1p.valueL (p := p) u) := by
    rw [W1p.valueL_apply]
    exact hS u
  rcases le_total q p with hqp | hpq'
  · -- For `q ≤ p`, compactness into `Lᵖ(Ω)` passes down, as `Ω` has finite measure.
    have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
      isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
    exact hK.of_forall_ae_eq_of_le hqp hS₀
  -- For `p ≤ q`, interpolate between `Lᵖ(Ω)` and `L^s(Ω)` for a finite `s > q` in the
  -- subcritical range.
  obtain ⟨s, θ, hs₁, hs, hps, hθ0, hθ1, hrel⟩ := exists_interpolation_exponent Fact.out hp
    Fact.out hq (by exact_mod_cast Module.finrank_pos (R := ℝ) (M := WithLp 2 (ℝ × E)))
    (ENNReal.natCast_ne_top _) hpq' hpq
  have : Fact (1 ≤ s) := ⟨hs₁⟩
  obtain ⟨T, hT⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hs hps hΩ hb)
  exact hK.of_forall_ae_eq_of_interpolation T hθ0 hθ1 hrel hS₀ fun u => (hS u).trans (hT u).symm

end TauCeti

end
