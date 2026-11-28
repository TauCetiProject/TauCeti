/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Trace
public import TauCeti.Analysis.PDE.Regularity.Hessian.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Regularity
public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Morrey
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.RellichKondrachov
public import TauCeti.Analysis.Sobolev.Wkp.Compactness
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import TauCeti.Analysis.InnerProductSpace.Positive.Definite
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.Regularity.Hessian.CurvedBoundary.Regularity
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.ContDiff
import TauCeti.Analysis.Sobolev.Wkp.Chain

/-!
# The `W^{2,p}` Dirichlet problem with continuous coefficients: estimate and uniqueness

Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary and let

`L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`

be a non-divergence-form operator whose principal coefficients `A` are continuous up to the boundary
and elliptic there, with `b` and `c` bounded and measurable. This file turns the boundary
Calderón–Zygmund estimate `‖D²u‖ ≤ C (‖L u‖ + ‖∇u‖ + ‖u‖)`
(`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`) into the
a priori estimates of the Dirichlet problem `L u = f` in `Ω`, `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`,
`1 < p < ∞`. Norms are those of `W^{2,p}(Ω)` and `Lᵖ(Ω)`.

* **Gilbarg–Trudinger, Theorem 9.14.** `‖u‖_{W^{2,p}} ≤ C (‖L u‖ + ‖u‖_{Lᵖ})`
  (`TauCeti.exists_norm_le_of_continuousWithinAt_of_contDiff_graph`). The lower-order terms are
  absorbed by Ehrling's inequality, which holds since `Ω` is a bounded Lipschitz domain
  (`TauCeti.exists_isLipschitzDomainWith_of_isBounded_of_contDiff`).
* **Uniqueness.** For `b = 0`, `c ≤ 0` and `p ≥ n = dim (ℝ × E)`, a solution of `L u = 0` in
  `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` vanishes
  (`TauCeti.eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero`). This needs neither the
  continuity of `A`, only its positive definiteness almost everywhere, nor more than a bounded
  Lipschitz domain. Some sign condition on `c` is needed: `sin x` on `(0, π)` solves `u'' + u = 0`.
  With a drift `b` the same holds for `p > n` whenever `|b|ⁿ / det S` is integrable, `S` the
  symmetric part of `A`
  (`TauCeti.eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero`). For continuous
  `A` and bounded `b` uniqueness holds for every `1 < p < ∞`
  (`TauCeti.eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero_of_contDiff_graph`):
  by Gilbarg–Trudinger's Lemma 9.16 a solution in `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` lies in
  `W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` for every finite `q ≥ p`, in particular for some `q > n`.
* **Gilbarg–Trudinger, Lemma 9.17.** For `c ≤ 0` and `1 < p < ∞`, the uniqueness removes the
  `Lᵖ` norm of `u`: `‖u‖_{W^{2,p}} ≤ C ‖L u‖`
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq`).
  For constant coefficients the constant is uniform over the class of matrices `A` with
  `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le`).

## The arguments

For uniqueness, `u ∈ W^{2,p}(Ω) ⊆ W^{2,n}(Ω)` has a representative `ū` continuous on `closure Ω`,
by Morrey's embedding on Lipschitz domains, which vanishes on `frontier Ω` since
`u ∈ W^{1,p}_0(Ω)` (`TauCeti.Wkp.exists_continuousOn_closure_ae_eq_and_eqOn_frontier`). The weak
maximum principle for strong subsolutions
(`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier`), applied to `u`
and `-u`, gives `ū = 0`. With a drift, Morrey's embedding for `p > n` makes `ū` moreover `C¹` in
`Ω`, which the weak maximum principle with a drift
(`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_nonneg_le_frontier`) asks for.
On a `C²` domain, Gilbarg–Trudinger's Lemma 9.16 (in the `TauCeti` namespace,
`exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq`)
puts a solution of `L u = 0` in `W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` with `q = max p (n + 1)`, and the case
`p > n` applies to it. There `|b|ⁿ / det S` is bounded, since `det S` is continuous up to the
compact boundary and positive on `closure Ω`.

For Lemma 9.17, `u ↦ L u` is a bounded operator `W^{2,p}(Ω) → Lᵖ(Ω)`
(`TauCeti.exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul`): `A` is bounded on `Ω` by its
continuity on the compact set `closure Ω`. On the closed subspace of `u` with zero boundary values,
Theorem 9.14 is an estimate `‖u‖ ≤ C ‖L u‖ + ‖K u‖` with `K` a multiple of the compact inclusion
`W^{2,p}(Ω) → Lᵖ(Ω)` (Rellich–Kondrachov), and `L` is injective there by uniqueness, so `L` is
bounded below there (`TauCeti.Wkp.exists_pos_mul_norm_le_of_mem_w1p0Submodule`). For constant
coefficients, `u ↦ tr (A ∘ D²u)` depends linearly, hence continuously, on `A`, and the class of
`A` is compact, so a perturbation argument over a finite cover
(`IsCompact.exists_forall_norm_le_mul_norm_apply`) makes the constant uniform in `A`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 9.14 and 9.15 and Lemmas 9.16 and 9.17.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace Filter Module
open scoped ENNReal NNReal Topology

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The global estimate for the Dirichlet problem** (Gilbarg–Trudinger, Theorem 9.14). Let
`1 < p < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, and let `b`, `c` be measurable and
bounded. Then there is `C` such that every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solving
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere satisfies
`‖u‖_{W^{2,p}(Ω)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`. -/
theorem exists_norm_le_of_continuousWithinAt_of_contDiff_graph (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
      ‖u‖ ≤ C * (‖f‖ + ‖value 2 u‖) := by
  have hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    ContinuousOn.aestronglyMeasurable (fun x hx => hcont x (subset_closure hx))
      Omega.isOpen.measurableSet
  obtain ⟨C₀, hC₀⟩ := exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph hp
    hp_top hΩ hbdry hA hcont hell hb hbβ hc hcγ
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  -- Ehrling's inequality `‖u‖_{W^{1,p}} ≤ ε ‖D²u‖ + C₁ ‖u‖_{Lᵖ}` with `2 C ε ≤ 1 / 2`.
  set C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  obtain ⟨C₁, hC₁, hE⟩ := exists_norm_lowerOrder_le_of_isCompactOperator
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith (p := p) hL hΩ 1)
    (by positivity : (0 : ℝ) < (4 * (C + 1))⁻¹)
  refine ⟨4 * C + 8 * C * C₁ + C₁, fun u f hu0 heq => ?_⟩
  have h1 := (hC₀ u f hu0 heq).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0)
    (by positivity))
  have hgrad : C * ‖iteratedGradient 0 (lowerOrder 1 u)‖ ≤ C * ‖lowerOrder 1 u‖ :=
    mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 _) hC
  have hval : ‖value 2 u‖ ≤ ‖lowerOrder 1 u‖ := by
    rw [value_succ]
    exact norm_value_le 1 _
  have hlo : C * ‖lowerOrder 1 u‖ ≤
      C * (4 * (C + 1))⁻¹ * ‖iteratedGradient 1 u‖ + C * C₁ * ‖value 2 u‖ := by
    linarith [mul_le_mul_of_nonneg_left (hE u) hC]
  have hε : C * (4 * (C + 1))⁻¹ * ‖iteratedGradient 1 u‖ ≤ 1 / 4 * ‖iteratedGradient 1 u‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [mul_inv_le_iff₀ (by positivity)]
    linarith
  have hε1 : (4 * (C + 1))⁻¹ * ‖iteratedGradient 1 u‖ ≤ ‖iteratedGradient 1 u‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by linarith))
  -- `‖D²u‖ ≤ 2 C ‖f‖ + 4 C C₁ ‖u‖_{Lᵖ}`, after absorbing the lower-order part.
  have hD : ‖iteratedGradient 1 u‖ ≤ 2 * C * ‖f‖ + 4 * C * C₁ * ‖value 2 u‖ := by
    linarith [mul_le_mul_of_nonneg_left hval hC]
  have := norm_le_norm_lowerOrder_add_norm_iteratedGradient 1 u
  linarith [hE u, mul_nonneg (mul_nonneg hC hC₁) (norm_nonneg f),
    mul_nonneg hC (norm_nonneg (value 2 u)), mul_nonneg hC₁ (norm_nonneg f)]

/-- The frame of the uniqueness theorems below. Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of
dimension `n`, let `n ≤ p < ∞` and let `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`. By Morrey's embedding `u`
has a representative `ū` continuous on `closure Ω` and vanishing on `frontier Ω`, and `u` lies in
`W^{2,n}(Ω)`, as some `v` with the same value and Hessian. If `ū ≤ 0` and `-ū ≤ 0` on `Ω` for all
such `ū` and `v`, as the weak maximum principle applied to `v` and `-v` gives, then `u = 0`. -/
private theorem eq_zero_of_forall_le_zero_and_neg_le_zero (hp_top : p ≠ ⊤)
    (hpn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≤ p) {Omega : Opens (WithLp 2 (ℝ × E))}
    {L : ℝ≥0} (hΩ : (Omega : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (h : ∀ [Fact (1 ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞))] (ū : WithLp 2 (ℝ × E) → ℝ)
      (v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega (finrank ℝ (WithLp 2 (ℝ × E))) 2),
      ContinuousOn ū (closure (Omega : Set (WithLp 2 (ℝ × E)))) →
      ⇑(value 2 u) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] ū →
      EqOn ū 0 (frontier (Omega : Set (WithLp 2 (ℝ × E)))) →
      ⇑(value 2 v) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] ⇑(value 2 u) →
      ⇑(iteratedGradient 1 v) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
        ⇑(iteratedGradient 1 u) →
      (∀ x ∈ Omega, ū x ≤ 0) ∧ ∀ x ∈ Omega, -ū x ≤ 0) :
    u = 0 := by
  obtain ⟨ū, hcont, huū, hfr⟩ :=
    exists_continuousOn_closure_ae_eq_and_eqOn_frontier hp_top (hpn.trans_lt (by
      rw [two_mul]
      exact ENNReal.lt_add_right hp_top (zero_lt_one.trans_le Fact.out).ne')) hΩ hb hu0
  -- `v = u ∈ W^{2,n}(Ω)`.
  have : Fact (1 ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)) :=
    ⟨Nat.one_le_cast.2 Module.finrank_pos⟩
  have : IsFiniteMeasure (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨hle, hge⟩ := h ū (ofExponentLEL hpn 2 u) hcont huū hfr (value_ofExponentLEL_ae hpn 2 u)
    (iteratedGradient_ofExponentLEL_ae hpn 1 u)
  refine Wkp.ext 2 (Lp.ext (huū.trans ?_ |>.trans (value_zero_ae 2).symm))
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  exact le_antisymm (hle x hx) (neg_nonpos.1 (hge x hx))

/-- **Uniqueness for the Dirichlet problem with strong solutions.** Let `Ω ⊆ ℝ × E` be a bounded
Lipschitz domain of dimension `n` and let `n ≤ p < ∞`. Let `A(x)` be positive definite,
`⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, and let `c(x) ≤ 0`, for almost every `x ∈ Ω`. If
`u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves `tr (A ∘ D²u) + c u = 0` almost everywhere on `Ω`, then
`u = 0`. -/
theorem eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero (hp_top : p ≠ ⊤)
    (hpn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≤ p) {Omega : Opens (WithLp 2 (ℝ × E))}
    {L : ℝ≥0} (hΩ : (Omega : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    {c : WithLp 2 (ℝ × E) → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) + c x * value 2 u x = 0) :
    u = 0 := by
  -- Apply the weak maximum principle to `v = u ∈ W^{2,n}(Ω)` and to `-v`.
  refine eq_zero_of_forall_le_zero_and_neg_le_zero hp_top hpn hΩ hb hu0
    fun ū v hcont huū hfr hv hD => ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier hb rfl v hcont
      (hv.trans huū) hA hc
      (by
        filter_upwards [heq, hD, hv] with y hy hDy hvy
        rw [hDy, hvy, hy]) le_rfl (fun z hz => (hfr hz).le) hx
  · exact PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier (ū := -ū) hb rfl
      (-v) hcont.neg ((value_neg_ae 2 v).trans (hv.trans huū).neg) hA hc
      (by
        filter_upwards [heq, hD, hv, value_neg_ae 2 v,
          iteratedGradient_neg_ae 1 v] with y hy hDy hvy hnv hnD
        simp only [hnD, hnv, Pi.neg_apply, hDy, hvy]
        rw [ContinuousLinearMap.comp_neg, map_neg]
        linarith)
      le_rfl (fun z hz => by simp [hfr hz]) hx

/-- **Uniqueness for the Dirichlet problem with strong solutions and a drift.** Let `Ω ⊆ ℝ × E` be a
bounded Lipschitz domain of dimension `n` and let `n < p < ∞`. Let `A(x)` be positive definite,
`⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, and `c(x) ≤ 0`, for almost every `x ∈ Ω`, and let the drift `b`
satisfy `∫_Ω |b|ⁿ / det S < ∞` for the symmetric part `S = (A + A†) / 2` of `A`. If
`u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = 0` almost everywhere on
`Ω`, then `u = 0`. -/
theorem eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero (hp_top : p ≠ ⊤)
    (hpn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) < p) {Omega : Opens (WithLp 2 (ℝ × E))}
    {L : ℝ≥0} (hΩ : (Omega : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hbA : ∫⁻ x in (Omega : Set (WithLp 2 (ℝ × E))), ENNReal.ofReal
      (‖b x‖ ^ finrank ℝ (WithLp 2 (ℝ × E)) / ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det) ≠ ∞)
    {c : WithLp 2 (ℝ × E) → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = 0) :
    u = 0 := by
  -- Apply the weak maximum principle with drift to `v = u ∈ W^{2,n}(Ω)` and to `-v`.
  refine eq_zero_of_forall_le_zero_and_neg_le_zero hp_top hpn.le hΩ hb hu0
    fun ū v hcont huū hfr hv hD => ?_
  -- By Morrey's embedding, `ū` is `C¹` in `Ω`.
  have hdiff : ContDiffOn ℝ 1 ū Omega := by
    obtain ⟨q, rfl⟩ : ∃ q : ℝ≥0, (q : ℝ≥0∞) = p := ⟨p.toNNReal, ENNReal.coe_toNNReal hp_top⟩
    exact contDiffOn_of_value_ae_eq_of_isLipschitzDomainWith_image (j := 1)
      (LinearIsometryEquiv.refl ℝ (WithLp 2 (ℝ × E))) (by simpa using hΩ) hb
      (by exact_mod_cast hpn) u (hcont.mono subset_closure) huū
  have hG : ⇑(iteratedGradient 0 (lowerOrder 1 v)) =ᵐ[volume.restrict
      (Omega : Set (WithLp 2 (ℝ × E)))] ⇑(iteratedGradient 0 (lowerOrder 1 u)) :=
    iteratedGradient_ae_eq_of_value_ae_eq 0 (by simpa only [value_succ] using hv)
  have hGneg : ⇑(iteratedGradient 0 (lowerOrder 1 (-v))) =ᵐ[volume.restrict
      (Omega : Set (WithLp 2 (ℝ × E)))] -⇑(iteratedGradient 0 (lowerOrder 1 v)) := by
    rw [← lowerOrderL_apply, map_neg, lowerOrderL_apply]
    exact iteratedGradient_neg_ae 0 _
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_nonneg_le_frontier hb rfl v
      hcont (hv.trans huū) hdiff hA hbA hc
      (by
        filter_upwards [heq, hD, hv, hG] with y hy hDy hvy hGy
        rw [hDy, hvy, hGy, hy]) le_rfl (fun z hz => (hfr hz).le) hx
  · exact PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_nonneg_le_frontier (ū := -ū) hb
      rfl (-v) hcont.neg ((value_neg_ae 2 v).trans (hv.trans huū).neg) hdiff.neg hA hbA hc
      (by
        filter_upwards [heq, hD, hv, hG, value_neg_ae 2 v, iteratedGradient_neg_ae 1 v,
          hGneg] with y hy hDy hvy hGy hnv hnD hnG
        simp only [hnD, hnv, hnG, Pi.neg_apply, hDy, hvy, hGy]
        rw [ContinuousLinearMap.comp_neg, map_neg, inner_neg_right]
        linarith)
      le_rfl (fun z hz => by simp [hfr hz]) hx

/-- On a bounded open set, if `A` is continuous within `Ω` and positive definite at every point of
`closure Ω` and the drift `b` is bounded, then `|b|ⁿ / det S` is integrable over `Ω`, for the
symmetric part `S = (A + A†) / 2` of `A`: `det S` is continuous up to the compact boundary and
positive there, so it is bounded below on `Ω`. -/
private theorem lintegral_ofReal_norm_pow_div_det_ne_top {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β) :
    ∫⁻ x in (Omega : Set (WithLp 2 (ℝ × E))), ENNReal.ofReal
      (‖b x‖ ^ finrank ℝ (WithLp 2 (ℝ × E)) / ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det) ≠ ∞ := by
  have hpos (x : WithLp 2 (ℝ × E)) (hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))) :
      0 < ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det := by
    obtain ⟨lam, hlam, h⟩ := hell x hx
    exact ContinuousLinearMap.det_two_inv_smul_add_adjoint_pos fun ξ hξ =>
      (mul_pos hlam (by positivity)).trans_le (h ξ)
  -- `(det S)⁻¹` is continuous within `Ω` up to the compact boundary, hence bounded on `Ω`.
  have hSc (x : WithLp 2 (ℝ × E)) (hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))) :
      ContinuousWithinAt (fun y => (2⁻¹ : ℝ) • (A y + (A y).adjoint)) Omega x :=
    ((hcont x hx).add ((ContinuousLinearMap.adjoint.continuous.tendsto _).comp
      (hcont x hx))).const_smul (2⁻¹ : ℝ)
  obtain ⟨U, hKU, -, hbdd⟩ :=
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
      (f := fun x => (((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det)⁻¹) hΩ.isCompact_closure
      fun x hx => (ContinuousLinearMap.continuous_det.continuousAt.comp_continuousWithinAt
        (hSc x hx)).inv₀ (hpos x hx).ne'
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hbound : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      ENNReal.ofReal (‖b x‖ ^ finrank ℝ (WithLp 2 (ℝ × E)) /
        ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det) ≤
      ENNReal.ofReal (β ^ finrank ℝ (WithLp 2 (ℝ × E)) * K) := by
    filter_upwards [hbβ, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
    have hK' := (Real.le_norm_self _).trans (hK _ ⟨x, ⟨hKU (subset_closure hxΩ), hxΩ⟩, rfl⟩)
    rw [div_eq_mul_inv]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) hK'
      (inv_nonneg.2 (hpos x (subset_closure hxΩ)).le) (pow_nonneg ((norm_nonneg _).trans hx) _))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩ.measure_lt_top.ne

/-- **Uniqueness for the Dirichlet problem with strong solutions, at every exponent.** Let
`1 < p < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, let `b` be measurable and bounded, and let
`c` be measurable, bounded and `c ≤ 0` almost everywhere. If `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`
solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = 0` almost everywhere on `Ω`, then `u = 0`. -/
theorem eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero_of_contDiff_graph
    (hp : 1 < p) (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = 0) :
    u = 0 := by
  -- By Lemma 9.16, `u ∈ W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` for `q = max p (n + 1) > n`.
  set q := max p ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) + 1)
  have : Fact (1 ≤ q) := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans (le_max_left _ _)⟩
  have hq_top : q ≠ ⊤ := max_ne_top hp_top (by simp)
  have hqn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) < q :=
    (ENNReal.lt_add_right (ENNReal.natCast_ne_top _) one_ne_zero).trans_le (le_max_right _ _)
  obtain ⟨v, hv0, hv, hvD⟩ :=
    exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq hp
      hp_top hΩ hbdry hcont hell hb hbβ hc hcγ hu0 (f := 0) (by simpa using heq) (le_max_left _ _)
      hq_top MemLp.zero
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  have hpos : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx ξ hξ
    obtain ⟨lam, hlam, hlx⟩ := hell x (subset_closure hx)
    exact (mul_pos hlam (by positivity)).trans_le (hlx ξ)
  -- The weak gradients of `u` and `v` agree, since their values do.
  have hvG : ⇑(iteratedGradient 0 (lowerOrder 1 v)) =ᵐ[volume.restrict
      (Omega : Set (WithLp 2 (ℝ × E)))] ⇑(iteratedGradient 0 (lowerOrder 1 u)) :=
    iteratedGradient_ae_eq_of_value_ae_eq 0 (by simpa only [value_succ] using hv)
  have hv' : v = 0 := eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero hq_top
    hqn hL hΩ hpos (lintegral_ofReal_norm_pow_div_det_ne_top hΩ hcont hell hbβ) hc0 hv0 (by
      filter_upwards [heq, hv, hvD, hvG] with x hx hvx hDx hGx
      rw [hvx, hDx, hGx, hx])
  rw [hv'] at hv
  exact Wkp.ext 2 (Lp.ext (hv.symm.trans (value_zero_ae 2) |>.trans (value_zero_ae 2).symm))

/-- **The operator of the Dirichlet problem is bounded.** Let `Ω ⊆ ℝ × E` be a bounded open set,
let `A` be continuous within `Ω` at every point of `closure Ω`, and let `b` and `c` be measurable
and bounded. Then `u ↦ tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u` is a continuous linear map
`W^{2,p}(Ω) → Lᵖ(Ω)`: the continuity of `A` up to the compact boundary bounds it on `Ω`. -/
theorem exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul_of_continuousWithinAt
    {Omega : Opens (WithLp 2 (ℝ × E))} (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ T : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
        Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega),
      ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        T u x = traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x := by
  -- `A` is bounded on `Ω`, by continuity up to the compact boundary.
  obtain ⟨U, hKU, -, hbdd⟩ :=
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt (f := A)
      hΩ.isCompact_closure hcont
  obtain ⟨Λ, hΛ⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hAΛ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖A x‖ ≤ Λ := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    exact hΛ _ ⟨x, ⟨hKU (subset_closure hx), hx⟩, rfl⟩
  have hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    ContinuousOn.aestronglyMeasurable (fun x hx => hcont x (subset_closure hx))
      Omega.isOpen.measurableSet
  exact exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul hA hAΛ hb hbβ hc hcγ

/-- **The a priori estimate for the Dirichlet problem** (Gilbarg–Trudinger, Lemma 9.17). Let
`Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, and let `1 < p < ∞`. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, let `b` be measurable and bounded, and let
`c` be measurable, bounded and `c ≤ 0` almost everywhere. Then there is `C` such that every
`u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solving `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost
everywhere satisfies `‖u‖_{W^{2,p}(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. -/
theorem exists_norm_le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
      ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  obtain ⟨T, hTae'⟩ :=
    exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul_of_continuousWithinAt (p := p) hΩ
      hcont hb hbβ hc hcγ
  have hT : ∀ u f, (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
      T u = f := fun u f heq => Lp.ext <| by
    filter_upwards [hTae' u, heq] with x h1 h2
    exact h1.trans h2
  -- Theorem 9.14, with a nonnegative constant `D`.
  obtain ⟨D₀, hD₀⟩ := exists_norm_le_of_continuousWithinAt_of_contDiff_graph hp hp_top hΩ hbdry
    hcont hell hb hbβ hc hcγ
  -- `T` is injective on zero boundary values by uniqueness, hence bounded below there.
  obtain ⟨κ, hκ, hκb⟩ := exists_pos_mul_norm_le_of_mem_w1p0Submodule hL hΩ T
    (fun u hu0 => hD₀ u (T u) hu0 (by
      filter_upwards [hTae' u] with x hx
      exact hx.symm))
    (fun u hu0 hTu =>
      eq_zero_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq_zero_of_contDiff_graph hp
        hp_top hΩ hbdry hcont hell hb hbβ hc hcγ hc0 hu0 (by
          filter_upwards [hTae' u, Lp.coeFn_zero ℝ p
            ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)] with x h1 h2
          rw [← h1, hTu]
          exact h2))
  refine ⟨κ⁻¹, fun u f hu0 heq => ?_⟩
  have h := hκb u hu0
  rw [hT u f heq] at h
  rw [inv_mul_eq_div, le_div_iff₀ hκ]
  linarith

/-- The constant-coefficient operator `u ↦ tr (A ∘ D²u)` from `W^{2,p}(Ω)` to `Lᵖ(Ω)`; its
values are given almost everywhere by `TauCeti.coeFn_hessianTraceL`. -/
def hessianTraceL (Omega : Opens (WithLp 2 (ℝ × E)))
    (A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
      Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega) :=
  ((traceCLM ℝ (WithLp 2 (ℝ × E))).comp (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E))
    (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A)).compLpL p _ ∘L iteratedGradientL 1

/-- `hessianTraceL Omega A` unfolded to its defining composite. It is proved by `delta` rather than
`rw [hessianTraceL]`, because the equation lemma of this unexposed definition has a type that is
slow to check. -/
private theorem hessianTraceL_eq (Omega : Opens (WithLp 2 (ℝ × E)))
    (A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    hessianTraceL (p := p) Omega A =
      ((traceCLM ℝ (WithLp 2 (ℝ × E))).comp (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E))
        (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A)).compLpL p _ ∘L iteratedGradientL 1 := by
  delta hessianTraceL
  rfl

/-- Almost everywhere on `Ω`, `hessianTraceL Omega A u` is `tr (A ∘ D²u)`. -/
theorem coeFn_hessianTraceL (Omega : Opens (WithLp 2 (ℝ × E)))
    (A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) :
    ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
      hessianTraceL Omega A u x = traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p) ((traceCLM ℝ (WithLp 2 (ℝ × E))).comp
    (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A))
    (iteratedGradient 1 u)] with x hx
  rw [hessianTraceL_eq, ContinuousLinearMap.comp_apply, iteratedGradientL_apply, hx,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

/-- The operator `u ↦ tr (A ∘ D²u)` depends continuously on `A`, since it is linear in `A` and the
coefficient matrices form a finite-dimensional space. -/
private theorem continuous_hessianTraceL (Omega : Opens (WithLp 2 (ℝ × E))) :
    Continuous fun A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (hessianTraceL (p := p) Omega A) := by
  let T : (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) →ₗ[ℝ]
      (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
        Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :=
    { toFun := fun A => hessianTraceL Omega A
      map_add' := fun A B => by
        simp only [hessianTraceL_eq, map_add, ContinuousLinearMap.comp_add,
          ContinuousLinearMap.add_compLpL, ContinuousLinearMap.add_comp]
      map_smul' := fun c A => by
        simp only [hessianTraceL_eq, map_smul, ContinuousLinearMap.comp_smul,
          ContinuousLinearMap.smul_compLpL, ContinuousLinearMap.smul_comp, RingHom.id_apply] }
  exact T.continuous_of_finiteDimensional

private theorem exists_norm_le_mul_norm_hessianTraceL (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Λ →
        ∀ u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
          firstOrder 1 u ∈ w1p0Submodule volume Omega p →
            ‖u‖ ≤ C * ‖hessianTraceL Omega A u‖ := by
  -- The class of coefficient matrices is compact.
  set K : Set (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :=
    {A | ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ} ∩ closedBall 0 Λ
  have hK : IsCompact K := by
    -- The norm of the operator space reaches `ProperSpace` through two instance paths.
    have : ProperSpace (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
      simpa +instances using
        FiniteDimensional.proper ℝ (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    refine (isCompact_closedBall 0 Λ).inter_left ?_
    simp only [ofPred_forall]
    exact isClosed_iInter fun ξ => isClosed_le continuous_const
      ((continuous_id.clm_apply continuous_const).inner continuous_const)
  -- The Banach space `M = W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` and the family `A ↦ tr (A ∘ D²·)` on it.
  set M : Submodule ℝ (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) :=
    (w1p0Submodule volume Omega p).toSubmodule.comap (firstOrderL 1).toLinearMap
  have hM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume Omega p := fun u => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, firstOrderL_apply,
      ClosedSubmodule.mem_toSubmodule_iff]
  have hLc : Continuous fun A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (hessianTraceL (p := p) Omega A).comp M.subtypeL :=
    (continuous_hessianTraceL Omega).clm_comp continuous_const
  -- Lemma 9.17 for each `A` in the class, made uniform by compactness.
  obtain ⟨C, hC⟩ := hK.exists_forall_norm_le_mul_norm_apply hLc.continuousOn fun A hA => by
    obtain ⟨hA1, -⟩ := hA
    obtain ⟨C, hC⟩ := exists_norm_le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq hp
      hp_top hΩ hbdry (A := fun _ => A) (fun _ _ => continuousWithinAt_const)
      (fun _ _ => ⟨lam, hlam, hA1⟩) (b := 0) (β := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp) (c := 0) (γ := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp) (ae_of_all _ fun _ => le_rfl)
    refine ⟨C, fun u => ?_⟩
    simpa using hC u _ ((hM u).1 u.property)
      ((coeFn_hessianTraceL Omega A (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)).mono
        fun x hx => by simp only [Pi.zero_apply, inner_zero_left, zero_mul, add_zero, hx])
  exact ⟨C, fun A hA hAΛ u hu => by
    -- `mem_closedBall_zero_iff` does not unify with the operator norm here; `dist` does.
    have hAK : A ∈ K := ⟨hA, mem_closedBall.2 ((dist_zero_right A).le.trans hAΛ)⟩
    simpa using hC A hAK ⟨u, (hM u).2 hu⟩⟩

/-- **The a priori estimate, uniformly in the coefficients** (Gilbarg–Trudinger, Lemma 9.17, for
constant coefficients). Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, `1 < p < ∞` and
`0 < λ`. There is one constant `C` such that for every constant matrix `A` with
`λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`, every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with `tr (A ∘ D²u) = f`
almost everywhere on `Ω` satisfies `‖u‖_{W^{2,p}(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. -/
theorem exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Λ →
        ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
          (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
          firstOrder 1 u ∈ w1p0Submodule volume Omega p →
          (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
            traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x) →
          ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_hessianTraceL hp hp_top hΩ hbdry hlam Λ
  refine ⟨C, fun A hA hAΛ u f hu hf => ?_⟩
  have hT : hessianTraceL Omega A u = f := Lp.ext <| by
    filter_upwards [coeFn_hessianTraceL Omega A u, hf] with x h1 h2
    rw [h1, h2]
  exact hT ▸ hC A hA hAΛ u hu

end TauCeti
