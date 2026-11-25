/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.CurvedBoundary.Regularity
public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Exponent
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.Embedding

/-!
# `W^{2,q}` regularity of strong solutions of the Dirichlet problem

Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, of dimension `n`, and let

`L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`

with `A` continuous up to the boundary and elliptic there, and `b`, `c` bounded and measurable.
This file proves Gilbarg–Trudinger's Lemma 9.16 in the form stated there: for `1 < p ≤ q < ∞`, a
solution `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` of `L u = f` with `f ∈ L^q(Ω)` lies in
`W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` (in the `TauCeti` namespace,
`exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq`).
Unlike `TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph`,
nothing is assumed about the integrability of `u` and `∇u` beyond `u ∈ W^{2,p}(Ω)`, and the
boundary condition is carried to the larger exponent.

## The argument

The integrability of `u` and `∇u` is bootstrapped. If `u` is already known to lie in
`W^{2,r'}(Ω)`, then `u` and `∇u` lie in `W^{1,r'}(Ω)` and so, by the Sobolev embedding on
the Lipschitz domain `Ω`, in `L^r(Ω)` whenever `1/r' < 1/r + 1/n`. The regularity statement with
these integrability hypotheses then places `u` in `W^{2,r}(Ω)`. Each step lowers the reciprocal
exponent by `1/(2n)`, so `2n` steps lead from `p` to `q`. Zero boundary values pass from
`W^{1,p}_0(Ω)` to `W^{1,q}_0(Ω)` since the trace does not depend on the exponent
(`TauCeti.W1p.mem_w1p0Submodule_of_value_ae_eq`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace Module
open scoped ENNReal NNReal

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  {Omega : Opens (WithLp 2 (ℝ × E))}
  {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
  {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ} {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
  {f : WithLp 2 (ℝ × E) → ℝ}

/-- One step of the bootstrap. Under the hypotheses of
`exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph`, if the value of
`u` is that of some `v' ∈ W^{2,r'}(Ω)` and `1/r' < 1/r + 1/n`, then it is that of some
`v ∈ W^{2,r}(Ω)`. -/
private theorem exists_wkp_value_ae_eq_of_wkp_value_ae_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x)
    {r r' : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ r')] (hpr : p ≤ r) (hr_top : r ≠ ⊤)
    (hf : MemLp f r (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hrr' : r'⁻¹ < r⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    {v' : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega r' 2}
    (hv' : (value 2 v' : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
      value 2 u) :
    ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega r 2,
      (value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
        value 2 u := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  -- The embedding `W^{2,r'}(Ω) → W^{1,r}(Ω)`, keeping the value and the gradient.
  obtain ⟨S, hS⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hr_top hrr' hL hΩ)
  obtain ⟨T, hT⟩ := exists_sobolevEmbeddingL_succ_of_ae_eq le_rfl S hS 0
  obtain ⟨hTv, hTg⟩ := hT v'
  have huq : MemLp (value 2 u) r (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    (Lp.memLp (value 1 (T v'))).ae_eq (hTv.trans hv')
  have hgrad : (iteratedGradient 0 (lowerOrder 1 v') : WithLp 2 (ℝ × E) → IteratedGradient _ 0)
      =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
        iteratedGradient 0 (lowerOrder 1 u) :=
    iteratedGradient_ae_eq_of_value_ae_eq 0 (by rwa [← value_succ, ← value_succ])
  have hgq : MemLp (iteratedGradient 0 (lowerOrder 1 u)) r
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    (Lp.memLp (iteratedGradient 0 (T v'))).ae_eq (hTg.trans hgrad)
  obtain ⟨v, hv, -⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph hp hp_top
      (hp.trans_le hpr) hr_top hΩ hbdry hcont hell hb hbβ hc hcγ u hu0 hf huq hgq heq
  exact ⟨v, hv⟩

omit [Fact (1 ≤ q)] in
/-- The bootstrap: under the hypotheses of
`exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph` with
`f ∈ L^q(Ω)`, the value of `u` is that of some `v ∈ W^{2,r}(Ω)` for every `p ≤ r ≤ q` with
`1/p ≤ 1/r + k/(2n)`, by induction on `k`. -/
private theorem exists_wkp_value_ae_eq_of_inv_le_inv_add_mul (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x)
    (hq_top : q ≠ ⊤) (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) :
    ∀ (k : ℕ) (r : ℝ≥0∞) [Fact (1 ≤ r)], p ≤ r → r ≤ q →
      p⁻¹ ≤ r⁻¹ + k * (2 * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞))⁻¹ →
      ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega r 2,
        (value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
          value 2 u
  | 0, r, _, hpr, _, hk => by
    obtain rfl : r = p := le_antisymm (ENNReal.inv_le_inv.1 (by simpa using hk)) hpr
    exact ⟨u, ae_eq_refl _⟩
  | k + 1, r, _, hpr, hrq, hk => by
    have : IsFiniteMeasure (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
      isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
    set n : ℝ≥0∞ := (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)
    have hn0 : n ≠ 0 := by simp [n, Module.finrank_pos.ne']
    have hntop : n ≠ ⊤ := ENNReal.natCast_ne_top _
    have hr0 : r⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne'
    have hr_top : r ≠ ⊤ := ne_top_of_le_ne_top hq_top hrq
    -- The step `1/(2n)` is below the critical gap `1/n`.
    have hstep : r⁻¹ + (2 * n)⁻¹ < r⁻¹ + n⁻¹ := by
      refine ENNReal.add_lt_add_left hr0 (ENNReal.inv_lt_inv.2 ?_)
      rw [two_mul]
      exact ENNReal.lt_add_right hntop hn0
    have hfr := hf.mono_exponent hrq
    by_cases hcase : p⁻¹ ≤ r⁻¹ + (2 * n)⁻¹
    · exact exists_wkp_value_ae_eq_of_wkp_value_ae_eq hp hp_top hΩ hbdry hcont hell hb hbβ hc hcγ
        hu0 heq hpr hr_top hfr (hcase.trans_lt hstep) (ae_eq_refl _)
    -- The previous exponent `r'`, with `1/r' = 1/r + 1/(2n) < 1/p`.
    push Not at hcase
    set r' : ℝ≥0∞ := (r⁻¹ + (2 * n)⁻¹)⁻¹
    have hr' : r'⁻¹ = r⁻¹ + (2 * n)⁻¹ := inv_inv _
    have hpr' : p ≤ r' := (ENNReal.inv_lt_inv.1 (hr' ▸ hcase)).le
    have : Fact (1 ≤ r') := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans hpr'⟩
    have hr'r : r' ≤ r := ENNReal.inv_le_inv.1 (hr' ▸ le_self_add)
    obtain ⟨v', hv'⟩ := exists_wkp_value_ae_eq_of_inv_le_inv_add_mul hp hp_top hΩ hbdry hcont
      hell hb hbβ hc hcγ hu0 heq hq_top hf k r' hpr' (hr'r.trans hrq) (by
        rw [hr', add_assoc]
        convert hk using 2
        push_cast
        ring)
    exact exists_wkp_value_ae_eq_of_wkp_value_ae_eq hp hp_top hΩ hbdry hcont hell hb hbβ hc hcγ
      hu0 heq hpr hr_top hfr (hr' ▸ hstep) hv'

/-- **`W^{2,q}` regularity of strong solutions of the Dirichlet problem** (Gilbarg–Trudinger,
Lemma 9.16). Let `1 < p ≤ q < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary.
Let `A` be continuous within `Ω` and elliptic at every point of `closure Ω`, and let `b`, `c` be
measurable and bounded. If `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `Ω` with `f ∈ L^q(Ω)`, then
`u ∈ W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)`: some `v ∈ W^{2,q}(Ω)` with zero boundary values has the value and
the weak Hessian of `u`. -/
theorem exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq
    (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x)
    (hpq : p ≤ q) (hq_top : q ≠ ⊤)
    (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) :
    ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega q 2,
      firstOrder 1 v ∈ w1p0Submodule volume Omega q ∧
      (value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
        value 2 u ∧
      (iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
        =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] iteratedGradient 1 u := by
  set n : ℝ≥0∞ := (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)
  -- `2n` steps of size `1/(2n)` lead from `p` to `q`.
  have hk : p⁻¹ ≤ q⁻¹ + ((2 * finrank ℝ (WithLp 2 (ℝ × E)) : ℕ) : ℝ≥0∞) * (2 * n)⁻¹ := by
    have hn0 : 2 * n ≠ 0 := by simp [n, Module.finrank_pos.ne']
    have hntop : 2 * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _)
    rw [Nat.cast_mul, Nat.cast_ofNat, ENNReal.mul_inv_cancel hn0 hntop]
    exact (ENNReal.inv_le_one.2 Fact.out).trans le_add_self
  obtain ⟨v, hv⟩ := exists_wkp_value_ae_eq_of_inv_le_inv_add_mul hp hp_top hΩ hbdry hcont hell hb
    hbβ hc hcγ hu0 heq hq_top hf _ q hpq le_rfl hk
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  refine ⟨v, W1p.mem_w1p0Submodule_of_value_ae_eq hp_top hq_top hpq hL hΩ hu0 ?_, hv,
    iteratedGradient_ae_eq_of_value_ae_eq 1 hv⟩
  rw [value_firstOrder, value_firstOrder]
  exact hv.symm

end TauCeti

end
