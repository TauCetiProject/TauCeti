/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.AdmissibleExponent
public import TauCeti.Analysis.Sobolev.W1p.CompactMultiplication.Sobolev

/-!
# Compact multiplication at admissible exponents in the plane

This is the `k = 1` row of McDuff--Salamon, Lemma C.2.2: for a real Cauchy--Riemann operator of
class `W^{ℓ-1,p}` on a surface, `p > 2`, multiplication by the zeroth-order term
`α ∈ W^{ℓ-1,p}` is compact `W^{1,q} → L^q` at every admissible exponent
(`TauCeti.IsAdmissibleRealizationExponent ℓ p 1 q`). For `ℓ = 1` admissibility means `q ≤ p`
and the `Lᵖ` statement `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_memLp` applies;
for `ℓ ≥ 2` every `q > 1` is admissible and the Sobolev coefficient statement
`TauCeti.W1p0.exists_isCompactOperator_value_smul_of_wkp` applies.

## Main declarations

* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_isAdmissibleRealizationExponent`: compact
  multiplication `W^{1,q}_0(Ω) → L^q(Ω)` for a bounded open `Ω` in a two-dimensional space.
* its `_of_isLipschitzDomainWith` form in the `TauCeti.W1p` namespace: compact multiplication
  `W^{1,q}(Ω) → L^q(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` with `dim (ℝ × E) = 2`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Theorem C.1.10
  and Lemma C.2.2.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-- For `ℓ = 1` the admissible exponents `(1, q)` satisfy `q ≤ p`. -/
private theorem le_of_isAdmissibleRealizationExponent_one {p q : ℝ≥0} (hp : 2 < (p : ℝ))
    (hq : IsAdmissibleRealizationExponent 1 p 1 q) : q ≤ p := by
  have h := ((isAdmissibleRealizationExponent_one_iff (by linarith)).1 hq).2.2
  exact_mod_cast h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Compact multiplication at admissible exponents in the plane.** Let `Ω` be a bounded open
subset of a two-dimensional space whose closure lies in an open set `Ω'`, let `2 < p < ∞`, and
let `α ∈ W^{ℓ-1,p}(Ω')` with `ℓ = m + 1 ≥ 1`. If `(1, q)` is an admissible exponent pair for a
real Cauchy--Riemann operator of class `W^{ℓ-1,p}`, multiplication `u ↦ u α` is a compact
operator `W^{1,q}_0(Ω) → L^q(Ω)` (McDuff--Salamon, Lemma C.2.2 at `k = 1`). For `ℓ = 1`
admissibility means `q ≤ p`; for `ℓ ≥ 2` every `q > 1` is admissible. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_isAdmissibleRealizationExponent
    {μ : Measure E} [μ.IsAddHaarMeasure] (hE : finrank ℝ E = 2) {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') (hp : 2 < (p : ℝ))
    {m : ℕ} (hq : IsAdmissibleRealizationExponent (m + 1) p 1 q) (α : Wkp μ Ω' p m) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • Wkp.value m α x) ∧
        IsCompactOperator M := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have hnp : (finrank ℝ E : ℝ≥0) < p := by
    rw [hE]
    exact_mod_cast hp
  cases m with
  | zero =>
    have hα : MemLp (Wkp.value 0 α) p (μ.restrict Ω) :=
      (Lp.memLp (Wkp.value 0 α)).mono_measure
        (Measure.restrict_mono_set μ (subset_closure.trans hΩΩ'))
    exact W1p0.exists_isCompactOperator_value_smul_of_memLp hΩ hnp
      (le_of_isAdmissibleRealizationExponent_one hp hq) hα
  | succ m => exact W1p0.exists_isCompactOperator_value_smul_of_wkp hΩ hΩΩ' hnp.le m α

namespace W1p

/-- **Compact multiplication at admissible exponents on planar Lipschitz domains.** Let
`Ω ⊆ ℝ × E` be a bounded Lipschitz domain with `dim (ℝ × E) = 2`, let `2 < p < ∞`, and let
`α ∈ W^{ℓ-1,p}(Ω)` with `ℓ = m + 1 ≥ 1`. If `(1, q)` is an admissible exponent pair for a real
Cauchy--Riemann operator of class `W^{ℓ-1,p}`, multiplication `u ↦ u α` is a compact operator
`W^{1,q}(Ω) → L^q(Ω)`. -/
theorem
    exists_isCompactOperator_value_smul_of_isAdmissibleRealizationExponent_of_isLipschitzDomainWith
    (hE : finrank ℝ (WithLp 2 (ℝ × E)) = 2) {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (hp : 2 < (p : ℝ)) {m : ℕ}
    (hq : IsAdmissibleRealizationExponent (m + 1) p 1 q) (α : Wkp volume Ω p m) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • Wkp.value m α x) ∧ IsCompactOperator M := by
  have hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p := by
    rw [hE]
    exact_mod_cast hp
  cases m with
  | zero =>
    exact W1p.exists_isCompactOperator_value_smul_of_isLipschitzDomainWith hΩ hb hnp
      (le_of_isAdmissibleRealizationExponent_one hp hq) (Wkp.value 0 α)
  | succ m =>
    exact W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith hΩ hb m
      (hnp.le.trans (le_mul_of_one_le_left zero_le le_add_self)) α

end W1p

end TauCeti

end
