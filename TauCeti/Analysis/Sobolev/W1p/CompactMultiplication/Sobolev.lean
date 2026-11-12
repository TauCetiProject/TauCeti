/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.AdmissibleExponent
public import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
public import TauCeti.Analysis.Sobolev.W1p.CompactMultiplication
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Compact multiplication by Sobolev coefficients at every exponent

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n ≥ 1`. Multiplication by `α ∈ Lʳ(Ω)` with `n < r` is compact from `W^{1,q}_0(Ω)` to `L^q(Ω)`
only for `q ≤ r` (`TauCeti.W1p0.exists_isCompactOperator_value_smul`). A coefficient of class
`W^{1,p}` with `n < p` is better: on a set whose closure is a compact subset of its domain it is
bounded (Morrey), so multiplication by it is compact `W^{1,q}_0(Ω) → L^q(Ω)` for *every*
`q ≥ 1`, including `q > p`. The same holds on all of `W^{1,q}(Ω)` for a bounded Lipschitz domain
`Ω ⊆ ℝ × E`, where `α ∈ W^{1,p}(Ω)` lies in `L^s(Ω)` for every finite `s`.

In the plane, this is the `k = 1` row of McDuff--Salamon, Lemma C.2.2: for a real
Cauchy--Riemann operator of class `W^{ℓ-1,p}`, `p > 2`, multiplication by the zeroth-order term
`α ∈ W^{ℓ-1,p}` is compact `W^{1,q} → L^q` at every admissible exponent
(`TauCeti.IsAdmissibleRealizationExponent ℓ p 1 q`). For `ℓ = 1` admissibility means `q ≤ p`
and the `Lᵖ` statement applies; for `ℓ ≥ 2` every `q > 1` is admissible and the Sobolev
coefficient statement applies.

## Main declarations

* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_memLp_top`: compact multiplication by a
  bounded coefficient on `W^{1,q}_0(Ω)` at every `q`.
* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`: the same for a `W^{1,p}`
  coefficient, `n < p`, defined on a neighbourhood of `closure Ω`.
* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_wkp`: the same for a `W^{m+1,p}`
  coefficient.
* `TauCeti.W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith` and
  `TauCeti.W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith`: the
  versions on all of `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E`.
* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_isAdmissibleRealizationExponent`: the
  planar statement for a coefficient of class `W^{ℓ-1,p}` at an admissible exponent `(1, q)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Theorem C.1.10
  and Lemma C.2.2.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

section Interior

variable [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Compact multiplication on `W^{1,q}_0(Ω)` by a coefficient `α ∈ Lʳ(Ω, G)` given as a function,
for `n < r` and `q ≤ r`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_memLp {Ω : Opens E}
    (hΩ : IsBounded (Ω : Set E)) {r : ℝ≥0} (hnr : (finrank ℝ E : ℝ≥0) < r) (hqr : q ≤ r)
    {α : E → G} (hα : MemLp α r (μ.restrict Ω)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp G q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • α x) ∧
        IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p0.exists_isCompactOperator_value_smul (μ := μ) hΩ hnr hqr (hα.toLp α)
  refine ⟨M, fun u => ?_, hMc⟩
  filter_upwards [hM u, hα.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]

/-- **Compact multiplication by bounded coefficients on `W^{1,q}_0`.** For a bounded open `Ω`
and `α ∈ L^∞(Ω, G)`, multiplication `u ↦ u α` is a compact operator `W^{1,q}_0(Ω) → L^q(Ω, G)`
for every `q ≥ 1`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_memLp_top {Ω : Opens E}
    (hΩ : IsBounded (Ω : Set E)) {α : E → G} (hα : MemLp α ∞ (μ.restrict Ω)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp G q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • α x) ∧
        IsCompactOperator M := by
  have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  exact W1p0.exists_isCompactOperator_value_smul_of_memLp (r := max q (finrank ℝ E + 1)) hΩ
    ((lt_add_one _).trans_le (le_max_right _ _)) (le_max_left _ _) (hα.mono_exponent le_top)

/-- **Compact multiplication by `W^{1,p}` coefficients on `W^{1,q}_0`, every `q`.** Let `Ω` be
a bounded open set whose closure lies in an open set `Ω'`, let `n < p < ∞` and
`α ∈ W^{1,p}(Ω')`. Then multiplication `u ↦ u α` is a compact operator
`W^{1,q}_0(Ω) → L^q(Ω)` for every `q ≥ 1`, including `q > p`: by Morrey's embedding `α` is
bounded on `Ω`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_w1p {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hnp : (finrank ℝ E : ℝ≥0) < p) (α : W1p μ Ω' p) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • W1p.value α x) ∧
        IsCompactOperator M := by
  obtain ⟨S, hS⟩ :=
    W1p.exists_lpInftyEmbeddingL_of_isCompact_closure (μ := μ) hnp hΩ.isCompact_closure hΩΩ'
  exact W1p0.exists_isCompactOperator_value_smul_of_memLp_top hΩ
    ((Lp.memLp (S α)).ae_eq (hS α))

/-- **Compact multiplication by `W^{m+1,p}` coefficients on `W^{1,q}_0`, every `q`.** The
higher-order form of `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_wkp {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hnp : (finrank ℝ E : ℝ≥0) < p) (m : ℕ)
    (α : Wkp μ Ω' p (m + 1)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x =>
        W1p.value (u : W1p μ Ω q) x • Wkp.value (m + 1) α x) ∧ IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p0.exists_isCompactOperator_value_smul_of_w1p (q := q) hΩ hΩΩ' hnp (Wkp.firstOrder m α)
  exact ⟨M, fun u => by rw [← Wkp.value_firstOrder]; exact hM u, hMc⟩

/-- **Compact multiplication at admissible exponents in the plane.** Let `Ω` be a bounded open
subset of a two-dimensional space whose closure lies in an open set `Ω'`, let `2 < p < ∞`, and
let `α ∈ W^{ℓ-1,p}(Ω')` with `ℓ = m + 1 ≥ 1`. If `(1, q)` is an admissible exponent pair for a
real Cauchy--Riemann operator of class `W^{ℓ-1,p}`, multiplication `u ↦ u α` is a compact
operator `W^{1,q}_0(Ω) → L^q(Ω)` (McDuff--Salamon, Lemma C.2.2 at `k = 1`). For `ℓ = 1`
admissibility means `q ≤ p`; for `ℓ ≥ 2` every `q > 1` is admissible. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_isAdmissibleRealizationExponent
    (hE : finrank ℝ E = 2) {Ω Ω' : Opens E} (hΩ : IsBounded (Ω : Set E))
    (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 2 < (p : ℝ))
    {m : ℕ} (hq : IsAdmissibleRealizationExponent (m + 1) p 1 q) (α : Wkp μ Ω' p m) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • Wkp.value m α x) ∧
        IsCompactOperator M := by
  have hnp : (finrank ℝ E : ℝ≥0) < p := by
    rw [hE]
    exact_mod_cast hp
  cases m with
  | zero =>
    have hqp : q ≤ p := by
      have h := ((isAdmissibleRealizationExponent_one_iff (by linarith)).1 hq).2.2
      exact_mod_cast h
    exact W1p0.exists_isCompactOperator_value_smul_of_memLp hΩ hnp hqp
      ((Lp.memLp (Wkp.value 0 α)).mono_measure
        (Measure.restrict_mono_set μ (subset_closure.trans hΩΩ')))
  | succ m => exact W1p0.exists_isCompactOperator_value_smul_of_wkp hΩ hΩΩ' hnp m α

end Interior

section LipschitzDomain

variable {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- Compact multiplication on `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` by a
coefficient `α ∈ Lʳ(Ω, G)` given as a function, for `n < r` and `q ≤ r`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_memLp_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0}
    (hnr : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < r) (hqr : q ≤ r)
    {α : WithLp 2 (ℝ × E) → G} (hα : MemLp α r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp G q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • α x) ∧ IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p.exists_isCompactOperator_value_smul_of_isLipschitzDomainWith hΩ hb hnr hqr (hα.toLp α)
  refine ⟨M, fun u => ?_, hMc⟩
  filter_upwards [hM u, hα.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]

/-- **Compact multiplication by `W^{1,p}` coefficients on bounded Lipschitz domains, every
`q`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `n = dim (ℝ × E)`, `n < p < ∞` and
`α ∈ W^{1,p}(Ω)`. Then multiplication `u ↦ u α` is a compact operator `W^{1,q}(Ω) → L^q(Ω)` for
every `q ≥ 1`, including `q > p`: `α` lies in `L^s(Ω)` for every finite `s`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p) (α : W1p volume Ω p) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • W1p.value α x) ∧ IsCompactOperator M := by
  have hps : (p : ℝ≥0∞)⁻¹ < ((max p q : ℝ≥0) : ℝ≥0∞)⁻¹ +
      (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ :=
    (ENNReal.inv_lt_inv.2 (by exact_mod_cast hnp)).trans_le le_add_self
  obtain ⟨C, hC⟩ :=
    W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith ENNReal.coe_ne_top
      hps hΩ hb
  exact W1p.exists_isCompactOperator_value_smul_of_memLp_of_isLipschitzDomainWith hΩ hb
    (hnp.trans_le (le_max_left _ _)) (le_max_right _ _)
    ((hC α).trans_lt (by finiteness))

/-- **Compact multiplication by `W^{m+1,p}` coefficients on bounded Lipschitz domains, every
`q`.** The higher-order form of
`TauCeti.W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p) (m : ℕ)
    (α : Wkp volume Ω p (m + 1)) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • Wkp.value (m + 1) α x) ∧ IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith (q := q) hΩ hb hnp
      (Wkp.firstOrder m α)
  exact ⟨M, fun u => by rw [← Wkp.value_firstOrder]; exact hM u, hMc⟩

end LipschitzDomain

end TauCeti

end
