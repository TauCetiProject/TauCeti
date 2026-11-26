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
import TauCeti.Analysis.PDE.Regularity.Hessian.CurvedBoundary.Regularity

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
  For continuous `A` uniqueness holds for every `1 < p < ∞`
  (`TauCeti.eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero_of_contDiff_graph`): by
  Gilbarg–Trudinger's Lemma 9.16 a solution in `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` lies in
  `W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` for every finite `q ≥ p`, in particular for `q ≥ n`.
* **Gilbarg–Trudinger, Lemma 9.17.** For `b = 0`, `c ≤ 0` and `1 < p < ∞`, the uniqueness
  removes the `Lᵖ` norm of `u`: `‖u‖_{W^{2,p}} ≤ C ‖L u‖`
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq`).

## The arguments

For uniqueness, `u ∈ W^{2,p}(Ω) ⊆ W^{2,n}(Ω)` has a representative `ū` continuous on `closure Ω`,
by Morrey's embedding on Lipschitz domains, which vanishes on `frontier Ω` since
`u ∈ W^{1,p}_0(Ω)` (`TauCeti.Wkp.exists_continuousOn_closure_ae_eq_and_eqOn_frontier`). The weak
maximum principle for strong subsolutions
(`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier`), applied to `u`
and `-u`, gives `ū = 0`. For `p < n` on a `C²` domain, Gilbarg–Trudinger's Lemma 9.16 (in the
`TauCeti` namespace,
`exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq`)
puts a solution of `L u = 0` in `W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` with `q = max p n`, and the case
`p ≥ n` applies to it.

For Lemma 9.17, `u ↦ L u` is a bounded operator `W^{2,p}(Ω) → Lᵖ(Ω)`
(`TauCeti.exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul`): `A` is bounded on `Ω` by its
continuity on the compact set `closure Ω`. On the closed subspace of `u` with zero boundary values,
Theorem 9.14 is an estimate `‖u‖ ≤ C ‖L u‖ + ‖K u‖` with `K` a multiple of the compact inclusion
`W^{2,p}(Ω) → Lᵖ(Ω)` (Rellich–Kondrachov), and `L` is injective there by uniqueness, so `L` is
bounded below there (`TauCeti.Wkp.exists_pos_mul_norm_le_of_mem_w1p0Submodule`).

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
  obtain ⟨ū, hcont, huū, hfr⟩ :=
    exists_continuousOn_closure_ae_eq_and_eqOn_frontier hp_top (hpn.trans_lt (by
      rw [two_mul]
      exact ENNReal.lt_add_right hp_top (zero_lt_one.trans_le Fact.out).ne')) hΩ hb hu0
  -- Apply the weak maximum principle to `v = u ∈ W^{2,n}(Ω)` and to `-v`.
  have : Fact (1 ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)) :=
    ⟨Nat.one_le_cast.2 Module.finrank_pos⟩
  have : IsFiniteMeasure (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  set v := ofExponentLEL hpn 2 u
  have hv : ⇑(value 2 v) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] ⇑(value 2 u) :=
    value_ofExponentLEL_ae hpn 2 u
  have hvū := hv.trans huū
  have hD : ⇑(iteratedGradient 1 v) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
      ⇑(iteratedGradient 1 u) :=
    iteratedGradient_ofExponentLEL_ae hpn 1 u
  have hle : ∀ x ∈ Omega, ū x ≤ 0 := fun x hx =>
    PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier hb rfl v hcont hvū hA hc
      (by
        filter_upwards [heq, hD, hv] with y hy hDy hvy
        rw [hDy, hvy, hy]) le_rfl (fun z hz => (hfr hz).le) hx
  have hge : ∀ x ∈ Omega, -ū x ≤ 0 := fun x hx =>
    PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier (ū := -ū) hb rfl (-v)
      hcont.neg ((value_neg_ae 2 v).trans hvū.neg) hA hc
      (by
        filter_upwards [heq, hD, hv, value_neg_ae 2 v,
          iteratedGradient_neg_ae 1 v] with y hy hDy hvy hnv hnD
        simp only [hnD, hnv, Pi.neg_apply, hDy, hvy]
        rw [ContinuousLinearMap.comp_neg, map_neg]
        linarith)
      le_rfl (fun z hz => by simp [hfr hz]) hx
  refine valueL_injective 2 ?_
  rw [map_zero, valueL_apply]
  refine Lp.ext (huū.trans ?_ |>.trans (Lp.coeFn_zero _ _ _).symm)
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  exact le_antisymm (hle x hx) (neg_nonpos.1 (hge x hx))

/-- **Uniqueness for the Dirichlet problem with strong solutions, at every exponent.** Let
`1 < p < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, and let `c` be measurable, bounded and
`c ≤ 0` almost everywhere. If `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves `tr (A ∘ D²u) + c u = 0`
almost everywhere on `Ω`, then `u = 0`. -/
theorem eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero_of_contDiff_graph (hp : 1 < p)
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
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) + c x * value 2 u x = 0) :
    u = 0 := by
  -- By Lemma 9.16, `u ∈ W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` for `q = max p n ≥ n`.
  set q := max p (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)
  have : Fact (1 ≤ q) := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans (le_max_left _ _)⟩
  have hq_top : q ≠ ⊤ := max_ne_top hp_top (ENNReal.natCast_ne_top _)
  obtain ⟨v, hv0, hv, hvD⟩ :=
    exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq hp
      hp_top hΩ hbdry hcont hell (b := 0) (β := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp) hc hcγ hu0 (f := 0) (by simpa using heq) (le_max_left _ _)
      hq_top MemLp.zero
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  have hpos : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫_ℝ := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx ξ hξ
    obtain ⟨lam, hlam, hlx⟩ := hell x (subset_closure hx)
    exact (mul_pos hlam (by positivity)).trans_le (hlx ξ)
  have hv' : v = 0 := eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero hq_top
    (le_max_right _ _) hL hΩ hpos hc0 hv0 (by
      filter_upwards [heq, hv, hvD] with x hx hvx hDx
      rw [hvx, hDx, hx])
  refine valueL_injective 2 ?_
  rw [map_zero, valueL_apply]
  refine Lp.ext (hv.symm.trans ?_ |>.trans (Lp.coeFn_zero _ _ _).symm)
  rw [hv']
  exact value_zero_ae 2

/-- **The operator of the Dirichlet problem is bounded.** Let `Ω ⊆ ℝ × E` be a bounded open set,
let `A` be continuous within `Ω` at every point of `closure Ω`, and let `c` be measurable and
bounded. Then `u ↦ tr (A ∘ D²u) + c u` is a continuous linear map `W^{2,p}(Ω) → Lᵖ(Ω)`: the
continuity of `A` up to the compact boundary bounds it on `Ω`. -/
theorem exists_continuousLinearMap_traceCLM_comp_add_mul_of_continuousWithinAt
    {Omega : Opens (WithLp 2 (ℝ × E))} (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ T : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
        Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega),
      ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        T u x = traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          c x * value 2 u x := by
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
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul (p := p) hA hAΛ
    (b := 0) (β := 0) aestronglyMeasurable_const (ae_of_all _ fun _ => by simp) hc hcγ
  exact ⟨T, fun u => (hT u).mono fun x hx => by
    rwa [Pi.zero_apply, inner_zero_left, add_zero] at hx⟩

/-- **The a priori estimate for the Dirichlet problem** (Gilbarg–Trudinger, Lemma 9.17). Let
`Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, and let `1 < p < ∞`. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, and let `c` be measurable, bounded and
`c ≤ 0` almost everywhere. Then there is `C` such that every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`
solving `tr (A ∘ D²u) + c u = f ∈ Lᵖ(Ω)` almost everywhere
satisfies `‖u‖_{W^{2,p}(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. -/
theorem exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq (hp : 1 < p)
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
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) + c x * value 2 u x =
          f x) →
      ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  obtain ⟨T, hTae'⟩ :=
    exists_continuousLinearMap_traceCLM_comp_add_mul_of_continuousWithinAt (p := p) hΩ hcont hc hcγ
  have hT : ∀ u f, (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) + c x * value 2 u x =
        f x) → T u = f := fun u f heq => Lp.ext <| by
    filter_upwards [hTae' u, heq] with x h1 h2
    exact h1.trans h2
  -- Theorem 9.14 with `b = 0`, with a nonnegative constant `D`.
  obtain ⟨D₀, hD₀⟩ := exists_norm_le_of_continuousWithinAt_of_contDiff_graph hp hp_top hΩ hbdry
    hcont hell (b := 0) (β := 0) aestronglyMeasurable_const (ae_of_all _ fun _ => by simp) hc
    hcγ
  -- `T` is injective on zero boundary values by uniqueness, hence bounded below there.
  obtain ⟨κ, hκ, hκb⟩ := exists_pos_mul_norm_le_of_mem_w1p0Submodule hL hΩ T
    (fun u hu0 => hD₀ u (T u) hu0 (by
      filter_upwards [hTae' u] with x hx
      simp [hx]))
    (fun u hu0 hTu => eq_zero_of_traceCLM_comp_iteratedGradient_add_mul_eq_zero_of_contDiff_graph hp
      hp_top hΩ hbdry hcont hell hc hcγ hc0 hu0 (by
        filter_upwards [hTae' u, Lp.coeFn_zero ℝ p
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)] with x h1 h2
        rw [← h1, hTu]
        exact h2))
  refine ⟨κ⁻¹, fun u f hu0 heq => ?_⟩
  have h := hκb u hu0
  rw [hT u f heq] at h
  rw [inv_mul_eq_div, le_div_iff₀ hκ]
  linarith

end TauCeti
