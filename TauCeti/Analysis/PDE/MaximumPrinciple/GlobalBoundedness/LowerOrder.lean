/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic
public import TauCeti.Analysis.PDE.MaximumPrinciple.Drift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.PDE.EnergyForm.LowerOrder
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Global boundedness of weak subsolutions with a drift

Let `Ω ⊆ ℝⁿ` be open with finite measure, let `a` be measurable and uniformly elliptic on `Ω`
with constants `0 < λ ≤ Λ`, let `b ∈ L^q(Ω; ℝⁿ)` be a drift, and let `c` be bounded, measurable
and nonnegative, where `q > n` and `q > 2`. This file proves the weak maximum principle with data
for weak subsolutions of the operator with a drift (Gilbarg–Trudinger, Theorem 8.16, with the
integrability of the lower-order coefficients allowed by the remark following it): if `u ∈ H¹(Ω)`
satisfies

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` in `Ω`, with `g ∈ L^{q/2}(Ω)`, `F ∈ L^q(Ω; ℝⁿ)`,

weakly, and `u ≤ k` on `∂Ω` for a level `k ≥ 0`, then

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`

almost everywhere, with `C` depending only on `n`, `q`, a bound for `‖b‖_q |Ω| ^ (1/n - 1/q) / λ`
and the normalization of the Haar measure (`TauCeti.PDE.exists_ae_value_le_add_of_memLp_drift`).
No smallness of the drift is assumed. For a bounded drift, `‖b‖ ≤ β`, the dimensionless size is at
most `β |Ω| ^ (1/n) / λ` (`TauCeti.PDE.exists_ae_value_le_add_of_drift`). Such a bound, uniform over
a class of coefficients, is the quantitative maximum principle that comparison arguments for
divergence-form equations need. In the proof of Hopf's boundary point lemma for weak solutions by
Rosales the first-order coefficient `cⁱ ∂ᵢu` of his Lemma 3.2 is such an `L^q` drift; the zero-order
coefficient in `L^{q/2}` and the first-order coefficient in divergence form of that lemma are not
treated here. Without drift the bound is Stampacchia's bound of
`TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic`.

## The argument

* **Stampacchia's bound from an energy inequality.** If every truncation `w = (u - l)⁺`, `l ≥ k`,
  satisfies `λ ‖∇w‖² ≤ ∫ g w - ∫ ⟪F, ∇w⟫`, then Hölder's and the Sobolev inequality and
  Stampacchia's lemma bound `u`
  (`TauCeti.PDE.exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le`). This is
  Stampacchia's argument of `TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic`,
  with both kinds of data at once, and it is proved there.
* **Boundedness.** Testing against `w` leaves the drift term `∫ ‖b‖ ‖∇w‖ |w|`, which by Hölder's
  inequality with the exponents `p, 2, s`, `1/p + 1/s = 1/2`, `p ≤ q`, is at most
  `S ‖b‖_{Lᵖ({u > l})} ‖∇w‖²` for the Sobolev constant `S` of `‖w‖_s ≤ S ‖∇w‖₂`. It is absorbed
  once `‖b‖_{Lᵖ({u > l})}` is small. This happens above some level, since `|Ω| < ∞` and `p < ∞`,
  so `u` is essentially bounded above; the bound depends on `u`.
* **Removing the drift.** Let `M` bound `w = (u - k)⁺` and `κ > 0`. The transform `z = Φ(w)`,
  with `Φ' = G`, `G(t) = (A - t)/((A - t)² + κ²) - A/(A² + κ²)` and `A = M + 2κ`, satisfies
  `G' ≥ 3/4 G²` on `[0, M]`. Testing the equation of `u` against `G(w) (z - l)⁺` produces the term
  `G'(w) (z - l)⁺ ⟨a ∇w, ∇w⟩`, which absorbs the drift pointwise, and `z` satisfies the energy
  inequality of the first step without drift, with the scalar datum `‖b‖²/λ + ‖g‖/κ + ‖F‖²/(λκ²)`
  in `L^{q/2}` and the datum `G(w) F`, of size `‖F‖/κ`, in divergence form. For `κ` the size of the
  data, Stampacchia's bound gives `z ≤ C₁`, and since `Φ` grows like `log (A/κ)` near `M`, taking
  `M` to be the essential supremum of `w` gives `M ≤ C κ`.

The weak formulation with an unbounded drift is written as `a₀(u, v) + ∫_Ω ⟪b, ∇u⟫ v`, where `a₀` is
the energy form of `-∂ᵢ(aⁱʲ ∂ⱼ·) + c`, as in
`TauCeti.Analysis.PDE.MaximumPrinciple.LpDrift`; for a bounded drift it is the energy form of the
whole operator.

## Main declarations

* `TauCeti.PDE.exists_ae_value_le_add_of_memLp_drift`: the weak maximum principle with data for a
  drift in `L^q`.
* `TauCeti.PDE.exists_ae_value_le_add_of_drift`: the same for a bounded drift.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.15 and Theorem 8.16.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Lemma 3.2.
* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du second ordre à
  coefficients discontinus*, Ann. Inst. Fourier 15 (1965).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-! ### Boundedness of subsolutions with a drift -/

section Drift

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}

/-- The energy inequality of a truncation of a subsolution with a drift `b ∈ Lᵖ`, at a level where
the drift can be absorbed. Testing the subsolution inequality against `w = (u - l)⁺` gives
`λ ‖∇w‖² - ∫ ‖b‖ ‖∇w‖ |w| ≤ ∫ g w - ∫ ⟪F, ∇w⟫`, and Hölder's inequality on `A = {u > l}` with the
Sobolev inequality `‖w‖_s ≤ S ‖∇w‖₂`, `1/p + 1/s = 1/2`, bounds the drift term by
`S ‖b‖_{Lᵖ(A)} ‖∇w‖²`. Once this is at most `λ/2 ‖∇w‖²`, the truncation satisfies the energy
inequality with `λ/2` in place of `λ`. -/
private theorem half_mul_norm_gradient_posPartAbove_sq_le_of_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {p : ℝ≥0∞} (hb : MemLp b p (mu.restrict Omega)) {s S : ℝ≥0}
    (hps : p⁻¹ + (s : ℝ≥0∞)⁻¹ = 2⁻¹)
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) s (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {g : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (v : W1p mu Omega 2) x ∂mu ≤
          ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
            ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {l : ℝ} (hkl : k ≤ l)
    (hsmall : S * eLpNorm b p ((mu.restrict Omega).restrict {x | l < W1p.value u x}) ≤
      ENNReal.ofReal (lam / 2)) :
    lam / 2 * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u)‖ ^ 2 ≤
      ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hk.trans hkl) u) x⟫
          ∂mu := by
  set ν := mu.restrict Omega
  have hl : 0 ≤ l := hk.trans hkl
  set w := W1p.posPartAbove (by norm_num) hl u
  set f := W1p.value w
  set G := W1p.gradient w
  have hw0 : w ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hfs : MemLp f s ν :=
    memLp_iff.2 ((hS w hw0).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top))
  have hcoeff := h.memLp_energyIntegrand_zero_drift ha hc hc_bound
  have hc_ae : ∀ᵐ x ∂ν, 0 ≤ c x :=
    (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx ↦ hc_nonneg x hx
  -- The subsolution inequality tested against `w`, where the drift term only sees `w`.
  have htest : energyFormH1 a 0 c w w + ∫ x in Omega, ⟪b x, G x⟫ * f x ∂mu ≤
      ∫ x in Omega, g x * f x ∂mu - ∫ x in Omega, ⟪F x, G x⟫ ∂mu := by
    have h₁ := energyFormH1_posPartAbove_self_le hcoeff hc_ae hl u
    have h₂ := hu ⟨w, hw0⟩ (W1p.value_posPartAbove_nonneg_ae (by norm_num) hl u)
    rw [W1p.integral_inner_gradient_mul_value_posPartAbove (by norm_num) hl b u] at h₂
    exact (add_le_add_left h₁ _).trans h₂
  -- Ellipticity: `λ ‖∇w‖² ≤ a₀(w, w)`.
  have hlow := mul_norm_gradient_sq_sub_le_energyFormH1_self h hcoeff (beta := 0)
    (fun x _ ↦ by simp) hc_nonneg w
  -- The drift term is at most `∫ ‖b‖ ‖∇w‖ |w|`.
  have : p.HolderTriple s 2 := ⟨hps⟩
  have hint : Integrable (fun x ↦ ‖b x‖ * (‖G x‖ * ‖f x‖)) ν :=
    hb.integrable_norm_mul_norm_mul_norm (r := 2) (s := 2) (Lp.memLp G) hfs
  have hneg : -∫ x in Omega, ⟪b x, G x⟫ * f x ∂mu ≤ ∫ x, ‖b x‖ * (‖G x‖ * ‖f x‖) ∂ν :=
    neg_integral_inner_mul_le hint (ae_of_all _ fun _ ↦ le_rfl)
  -- Hölder's inequality on `A = {u > l}`, off which `∇w` vanishes, and the Sobolev inequality.
  set A := {x | l < W1p.value u x}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable
  have hgA : ∀ᵐ x ∂ν, G x ≠ 0 → x ∈ A :=
    (W1p.ae_mem_of_gradient_posPartAbove_ne_zero (by norm_num) hl u).mono fun x hx hne ↦
      (hx hne).1
  have hholder : ENNReal.ofReal (∫ x, ‖b x‖ * (‖G x‖ * ‖f x‖) ∂ν) ≤
      ENNReal.ofReal (lam / 2 * ‖G‖ ^ 2) := by
    rw [W1p.ofReal_integral_mul_norm_gradient_mul_norm_value_eq
      (ae_of_all _ fun x ↦ norm_nonneg _) hint hA hgA]
    simp only [eNorm_norm]
    calc ∫⁻ x in A, ‖b x‖ₑ * (‖G x‖ₑ * ‖f x‖ₑ) ∂ν
        ≤ S * eLpNorm b p (ν.restrict A) * ‖G‖ₑ ^ 2 :=
          W1p.lintegral_enorm_mul_enorm_gradient_mul_enorm_value_le (t := 2)
            hb.aestronglyMeasurable (hS w hw0) A
      _ ≤ ENNReal.ofReal (lam / 2) * ‖G‖ₑ ^ 2 := by gcongr
      _ = ENNReal.ofReal (lam / 2 * ‖G‖ ^ 2) := by
          rw [ENNReal.ofReal_mul (half_pos h.pos).le, ENNReal.ofReal_pow (norm_nonneg _),
            ofReal_norm]
  have hdrift := (ENNReal.ofReal_le_ofReal_iff (by have := h.pos; positivity)).1 hholder
  linarith

/-- Weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` with a drift `b ∈ L^q`, `q > n`,
`c ≥ 0` and `u ≤ k` on `∂Ω` are essentially bounded above on a set `Ω` of finite measure. At levels
`l` with `‖b‖_{L^q({u > l})}` small, which exist since `|Ω| < ∞`, the drift is absorbed
(`half_mul_norm_gradient_posPartAbove_sq_le_of_drift`), and Stampacchia's bound applies above
such a level. The bound obtained depends on `u`; the quantitative bound is
`TauCeti.PDE.exists_ae_value_le_add_of_memLp_drift`. -/
private theorem exists_ae_value_le_of_drift [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q)
    (hb : MemLp b q (mu.restrict Omega))
    {g : EuclideanSpace ℝ ι → ℝ} (hg : MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (v : W1p mu Omega 2) x ∂mu ≤
          ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
            ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2) :
    ∃ M : ℝ, ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  set n : ℕ := Fintype.card ι
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hlam := h.pos
  -- A Sobolev inequality `‖v‖_s ≤ S ‖∇v‖₂` with `1/s = 1/2 - δ` and `s (1/2 - 1/q) > 1`.
  obtain ⟨δ, hδ0, hδn, hδ2, hs, hqs⟩ := exists_sobolev_exponent (θ := (q : ℝ)⁻¹)
    (inv_nonneg.2 hq0.le) ((inv_lt_inv₀ hq0 hn0).2 hqn) ((inv_lt_inv₀ hq0 two_pos).2 hq)
  obtain ⟨K, -, hsob⟩ :=
    exists_forall_eLpNorm_value_le_toNNReal_mul_measureReal_rpow (mu := mu) hδ0 hδn hδ2
  set s : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  set S : ℝ≥0 := Real.toNNReal (K * mu.real Omega ^ ((n : ℝ)⁻¹ - δ))
  -- The drift lies in `Lᵖ` for the exponent `p = 1/δ ≤ q` dual to `s`: `1/p + 1/s = 1/2`.
  have hs0 : (0 : ℝ) < s := inv_pos.1 (by rw [hs]; linarith)
  have hqδ : (q : ℝ)⁻¹ < δ := by
    have h₁ : 2⁻¹ - (q : ℝ)⁻¹ > (s : ℝ)⁻¹ := by
      rw [gt_iff_lt, inv_lt_iff_one_lt_mul₀ hs0, mul_comm]
      exact hqs
    rw [hs] at h₁
    linarith
  set p : ℝ≥0∞ := ENNReal.ofReal δ⁻¹
  have hp1 : 1 ≤ p := ENNReal.one_le_ofReal.2 ((one_le_inv₀ hδ0).2 (by linarith))
  have hptop : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hps : p⁻¹ + (s : ℝ≥0∞)⁻¹ = 2⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hδ0), inv_inv, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_inv_of_pos hs0, hs, ← ENNReal.ofReal_add hδ0.le (by linarith),
      add_sub_cancel, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hbp : MemLp b p ν := hb.mono_exponent (ENNReal.ofReal_le_of_le_toReal (by
    rw [ENNReal.coe_toReal]
    exact (inv_le_comm₀ hδ0 hq0).2 hqδ.le))
  -- The superlevel sets `{u > j}` shrink to the empty set, so their measures tend to zero.
  set T : ℕ → Set (EuclideanSpace ℝ ι) := fun j => {x | (j : ℝ) < W1p.value u x}
  have hmeas : Tendsto (ν ∘ T) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := ν) (s := T)
      (fun j => (measurableSet_lt measurable_const
        (Lp.stronglyMeasurable (W1p.value u)).measurable).nullMeasurableSet)
      (fun i j hij x hx => show (i : ℝ) < W1p.value u x from
        lt_of_le_of_lt (by exact_mod_cast hij) hx)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ j, T j) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨j, hj⟩ := exists_nat_gt (W1p.value u x)
      exact (lt_asymm hj) (mem_iInter.1 hx j)
    rwa [hempty, measure_empty] at hlim
  -- So does the drift on them, since `p < ∞`.
  have hT : Tendsto (fun j => S * eLpNorm b p (ν.restrict (T j))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (hbp.tendsto_eLpNorm_restrict_of_tendsto_measure hp1 hptop hmeas) (Or.inr ENNReal.coe_ne_top)
  obtain ⟨j, hj⟩ := (hT.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hlam))))
    |>.exists_forall_of_atTop
  -- Above the level `l₀ = max k j` the drift is absorbed.
  set l₀ := max k (j : ℝ)
  have hl₀ : 0 ≤ l₀ := hk.trans (le_max_left _ _)
  have hboundary₀ : W1p.posPartAbove (by norm_num) hl₀ u ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk (le_max_left _ _) hboundary
  have henergy : ∀ l (hkl : l₀ ≤ l),
      lam / 2 * ‖W1p.gradient (W1p.posPartAbove (by norm_num) (hl₀.trans hkl) u)‖ ^ 2 ≤
        ∫ x in Omega, g x * W1p.value (W1p.posPartAbove (by norm_num) (hl₀.trans hkl) u) x ∂mu -
          ∫ x in Omega,
            ⟪F x, W1p.gradient (W1p.posPartAbove (by norm_num) (hl₀.trans hkl) u) x⟫ ∂mu := by
    intro l hkl
    refine half_mul_norm_gradient_posPartAbove_sq_le_of_drift h ha hc hc_bound hc_nonneg hbp hps
      (hsob hOmega) hu hk hboundary ((le_max_left _ _).trans hkl) (le_trans ?_ (hj j le_rfl))
    gcongr
    exact fun x hx ↦ lt_of_le_of_lt ((le_max_right _ _).trans hkl) hx
  exact ⟨_, ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le hOmega hq hqs
    (hsob hOmega) (half_pos hlam) hg hF hl₀ hboundary₀ henergy⟩

end Drift

/-! ### The transformation that removes the drift

For `A, κ > 0` let `G(t) = (A - t) / ((A - t)² + κ²) - A / (A² + κ²)` and let `Φ` be its primitive
with `Φ(0) = 0`. On `[0, A - 2κ]` the function `G` is nonnegative and at most `1/(2κ)`, its
derivative is at most `1/(4κ²)`, and `G' ≥ 3/4 G²`. The last inequality is what lets the second
derivative term of the chain rule absorb the drift. -/

/-- The weight `G(t) = (A - t) / ((A - t)² + κ²) - A / (A² + κ²)`. -/
private def driftWeight (A κ t : ℝ) : ℝ :=
  (A - t) / ((A - t) ^ 2 + κ ^ 2) - A / (A ^ 2 + κ ^ 2)

/-- The derivative `G'(t) = ((A - t)² - κ²) / ((A - t)² + κ²)²` of the weight. -/
private def driftWeightDeriv (A κ t : ℝ) : ℝ :=
  ((A - t) ^ 2 - κ ^ 2) / ((A - t) ^ 2 + κ ^ 2) ^ 2

/-- The primitive `Φ(t) = (log (A² + κ²) - log ((A - t)² + κ²)) / 2 - A t / (A² + κ²)` of the
weight, with `Φ(0) = 0`. -/
private def driftTransform (A κ t : ℝ) : ℝ :=
  2⁻¹ * (Real.log (A ^ 2 + κ ^ 2) - Real.log ((A - t) ^ 2 + κ ^ 2)) - A / (A ^ 2 + κ ^ 2) * t

section Transform

variable {A κ : ℝ}

private theorem sq_add_sq_pos (hκ : 0 < κ) (y : ℝ) : 0 < y ^ 2 + κ ^ 2 := by positivity

private theorem hasDerivAt_den (A κ t : ℝ) :
    HasDerivAt (fun t => (A - t) ^ 2 + κ ^ 2) (-(2 * (A - t))) t := by
  have := (((hasDerivAt_id' t).const_sub A).pow 2).add_const (κ ^ 2)
  convert this using 1
  push_cast
  ring

private theorem hasDerivAt_driftTransform (hκ : 0 < κ) (t : ℝ) :
    HasDerivAt (driftTransform A κ) (driftWeight A κ t) t := by
  have hlog := (hasDerivAt_den A κ t).log (sq_add_sq_pos hκ _).ne'
  have := (((hasDerivAt_const t (Real.log (A ^ 2 + κ ^ 2))).sub hlog).const_mul 2⁻¹).sub
    ((hasDerivAt_id' t).const_mul (A / (A ^ 2 + κ ^ 2)))
  refine this.congr_deriv ?_
  have := (sq_add_sq_pos hκ (A - t)).ne'
  simp only [driftWeight, mul_one]
  field_simp
  ring

private theorem hasDerivAt_driftWeight (hκ : 0 < κ) (t : ℝ) :
    HasDerivAt (driftWeight A κ) (driftWeightDeriv A κ t) t := by
  have := (((hasDerivAt_id' t).const_sub A).div (hasDerivAt_den A κ t)
    (sq_add_sq_pos hκ _).ne').sub_const (A / (A ^ 2 + κ ^ 2))
  refine this.congr_deriv ?_
  have := (sq_add_sq_pos hκ (A - t)).ne'
  simp only [driftWeightDeriv]
  field_simp
  ring

private theorem contDiff_driftWeight (hκ : 0 < κ) : ContDiff ℝ 1 (driftWeight A κ) :=
  ((contDiff_const.sub contDiff_id).div ((contDiff_const.sub contDiff_id).pow 2 |>.add
    contDiff_const) fun _ => (sq_add_sq_pos hκ _).ne').sub contDiff_const

private theorem contDiff_driftTransform (hκ : 0 < κ) : ContDiff ℝ 1 (driftTransform A κ) :=
  (contDiff_const.mul (contDiff_const.sub (((contDiff_const.sub contDiff_id).pow 2 |>.add
    contDiff_const).log fun _ => (sq_add_sq_pos hκ _).ne'))).sub (contDiff_const.mul contDiff_id)

private theorem deriv_driftTransform (hκ : 0 < κ) :
    deriv (driftTransform A κ) = driftWeight A κ :=
  funext fun t => (hasDerivAt_driftTransform hκ t).deriv

private theorem driftWeight_zero : driftWeight A κ 0 = 0 := by
  simp [driftWeight]

private theorem driftTransform_zero : driftTransform A κ 0 = 0 := by
  simp [driftTransform]

/-- The factored form `G(t) = t (A (A - t) - κ²) / (((A - t)² + κ²) (A² + κ²))`. -/
private theorem driftWeight_eq (hκ : 0 < κ) (t : ℝ) :
    driftWeight A κ t = t * (A * (A - t) - κ ^ 2) / (((A - t) ^ 2 + κ ^ 2) * (A ^ 2 + κ ^ 2)) := by
  have := (sq_add_sq_pos hκ (A - t)).ne'
  have := (sq_add_sq_pos hκ A).ne'
  simp only [driftWeight]
  field_simp
  ring

private theorem driftWeight_nonneg (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) (htA : t ≤ A - 2 * κ) :
    0 ≤ driftWeight A κ t := by
  rw [driftWeight_eq hκ]
  have : κ ^ 2 ≤ A * (A - t) := by nlinarith
  have := sq_add_sq_pos hκ (A - t)
  have := sq_add_sq_pos hκ A
  positivity

private theorem driftWeight_pos (hκ : 0 < κ) {t : ℝ} (ht : 0 < t) (htA : t ≤ A - 2 * κ) :
    0 < driftWeight A κ t := by
  rw [driftWeight_eq hκ]
  have : κ ^ 2 < A * (A - t) := by nlinarith
  have := sq_add_sq_pos hκ (A - t)
  have := sq_add_sq_pos hκ A
  exact div_pos (mul_pos ht (by linarith)) (by positivity)

private theorem driftWeight_le_aux (hκ : 0 < κ) (hA : 0 ≤ A) (t : ℝ) :
    driftWeight A κ t ≤ (A - t) / ((A - t) ^ 2 + κ ^ 2) := by
  have := sq_add_sq_pos hκ A
  simp only [driftWeight]
  linarith [div_nonneg hA this.le]

private theorem driftWeight_le (hκ : 0 < κ) (hA : 0 ≤ A) (t : ℝ) :
    driftWeight A κ t ≤ (2 * κ)⁻¹ := by
  refine (driftWeight_le_aux hκ hA t).trans ?_
  have := sq_add_sq_pos hκ (A - t)
  rw [div_le_iff₀ this, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (A - t - κ)]

private theorem driftWeightDeriv_le (hκ : 0 < κ) (t : ℝ) :
    driftWeightDeriv A κ t ≤ (4 * κ ^ 2)⁻¹ := by
  have := sq_add_sq_pos hκ (A - t)
  simp only [driftWeightDeriv]
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((A - t) ^ 2 - κ ^ 2), sq_nonneg κ, pow_pos hκ 4]

private theorem mul_driftWeight_sq_le_driftWeightDeriv (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t)
    (htA : t ≤ A - 2 * κ) :
    3 / 4 * driftWeight A κ t ^ 2 ≤ driftWeightDeriv A κ t := by
  have hA : 0 ≤ A := by linarith
  have hG := driftWeight_nonneg hκ ht htA
  have hGle := driftWeight_le_aux hκ hA t
  calc 3 / 4 * driftWeight A κ t ^ 2 ≤ 3 / 4 * ((A - t) / ((A - t) ^ 2 + κ ^ 2)) ^ 2 := by
        gcongr
    _ ≤ driftWeightDeriv A κ t := by
        simp only [driftWeightDeriv]
        rw [div_pow, ← mul_div_assoc]
        gcongr
        nlinarith

/-- `0 ≤ Φ(t) ≤ t/(2κ)` on `[0, A - 2κ]`, since `0 ≤ Φ' ≤ 1/(2κ)` there and `Φ(0) = 0`. -/
private theorem driftTransform_mem_Icc (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) (htA : t ≤ A - 2 * κ) :
    0 ≤ driftTransform A κ t ∧ driftTransform A κ t ≤ t / (2 * κ) := by
  have hA : 0 ≤ A := by linarith
  have hD : Convex ℝ (Icc 0 (A - 2 * κ)) := convex_Icc _ _
  have hdiff : Differentiable ℝ (driftTransform A κ) := fun t =>
    (hasDerivAt_driftTransform hκ t).differentiableAt
  have hmem : t ∈ Icc 0 (A - 2 * κ) := ⟨ht, htA⟩
  have h0 : (0 : ℝ) ∈ Icc 0 (A - 2 * κ) := ⟨le_rfl, ht.trans htA⟩
  constructor
  · have hmono := monotoneOn_of_deriv_nonneg hD hdiff.continuous.continuousOn
      hdiff.differentiableOn fun x hx => by
        rw [interior_Icc] at hx
        rw [deriv_driftTransform hκ]
        exact driftWeight_nonneg hκ hx.1.le hx.2.le
    simpa [driftTransform_zero] using hmono h0 hmem ht
  · have hdiff' : Differentiable ℝ fun t => t / (2 * κ) - driftTransform A κ t :=
      (differentiable_id.div_const _).sub hdiff
    have hmono := monotoneOn_of_deriv_nonneg hD hdiff'.continuous.continuousOn
      hdiff'.differentiableOn fun x _ => by
        have hd : HasDerivAt (fun t => t / (2 * κ) - driftTransform A κ t)
            (1 / (2 * κ) - driftWeight A κ x) x :=
          ((hasDerivAt_id' x).div_const (2 * κ)).sub (hasDerivAt_driftTransform hκ x)
        rw [hd.deriv, sub_nonneg, one_div]
        exact driftWeight_le hκ hA x
    have := hmono h0 hmem ht
    simp only [zero_div, driftTransform_zero, sub_zero, sub_nonneg] at this
    exact this

/-- Near the top of `[0, A - 2κ]` the transform is large:
`Φ(t) ≥ (log (A² + κ²) - log (8 κ²)) / 2 - 1` when `0 ≤ t ≤ A` and `(A - t)² ≤ 7κ²`. -/
private theorem le_driftTransform (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) (htA : t ≤ A)
    (hclose : (A - t) ^ 2 ≤ 7 * κ ^ 2) :
    2⁻¹ * (Real.log (A ^ 2 + κ ^ 2) - Real.log (8 * κ ^ 2)) - 1 ≤ driftTransform A κ t := by
  have hden := sq_add_sq_pos hκ A
  have hlog : Real.log ((A - t) ^ 2 + κ ^ 2) ≤ Real.log (8 * κ ^ 2) :=
    Real.log_le_log (sq_add_sq_pos hκ _) (by linarith)
  have hlin : A / (A ^ 2 + κ ^ 2) * t ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hden]
    nlinarith
  simp only [driftTransform]
  linarith

end Transform

/-- The scalar inequality behind the transformation: with `0 ≤ G ≤ 1/(2κ)`,
`3/4 G² ≤ G' ≤ 1/(4κ²)`, `|B| ≤ β e` and `|P| ≤ F e`, the drift term `B G` and the term `G' P`
coming from the datum in divergence form are absorbed by `λ G' e²` up to constants. -/
private theorem key_ineq {lam beta κ G G' e Fn g B P : ℝ} (hlam : 0 < lam) (hκ : 0 < κ)
    (hG0 : 0 ≤ G) (hG : G ≤ (2 * κ)⁻¹)
    (hGd : 3 / 4 * G ^ 2 ≤ G') (hGd' : G' ≤ (4 * κ ^ 2)⁻¹) (hB : |B| ≤ beta * e)
    (hP : |P| ≤ Fn * e) :
    0 ≤ beta ^ 2 / lam + κ⁻¹ * |g| + (lam * κ ^ 2)⁻¹ * Fn ^ 2 + lam * G' * e ^ 2 + B * G -
      g * G + G' * P := by
  have hG'0 : 0 ≤ G' := le_trans (by positivity) hGd
  -- The drift term: `β G e ≤ λ G' e² / 2 + β² / λ`.
  have h1 : beta * G * e ≤ lam * G' * e ^ 2 / 2 + beta ^ 2 / lam := by
    have : 24 * lam * (beta * G * e) ≤ 12 * lam ^ 2 * e ^ 2 * G' + 16 * beta ^ 2 := by
      nlinarith [sq_nonneg (3 * lam * e * G - 4 * beta),
        mul_le_mul_of_nonneg_left hGd (by positivity : (0 : ℝ) ≤ 12 * lam ^ 2 * e ^ 2)]
    rw [div_add_div _ _ two_ne_zero hlam.ne', le_div_iff₀ (by positivity)]
    nlinarith
  -- The divergence term: `G' F e ≤ λ G' e² / 2 + F² / (λ κ²)`.
  have h2 : G' * Fn * e ≤ lam * G' * e ^ 2 / 2 + (lam * κ ^ 2)⁻¹ * Fn ^ 2 := by
    have h2a : 2 * lam * (G' * Fn * e) ≤ lam ^ 2 * G' * e ^ 2 + G' * Fn ^ 2 := by
      nlinarith [mul_nonneg hG'0 (sq_nonneg (lam * e - Fn))]
    have h2b : G' * Fn ^ 2 ≤ κ⁻¹ ^ 2 * Fn ^ 2 := by
      refine mul_le_mul_of_nonneg_right (hGd'.trans ?_) (sq_nonneg _)
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (by nlinarith)
    have hκ' : (lam * κ ^ 2)⁻¹ * Fn ^ 2 = κ⁻¹ ^ 2 * Fn ^ 2 / lam := by
      field_simp
    rw [hκ', div_add_div _ _ two_ne_zero hlam.ne', le_div_iff₀ (by positivity)]
    nlinarith
  -- The scalar datum: `g G ≤ |g| / κ`.
  have h3 : g * G ≤ κ⁻¹ * |g| := by
    calc g * G ≤ |g| * G := mul_le_mul_of_nonneg_right (le_abs_self g) hG0
      _ ≤ |g| * κ⁻¹ := by
        refine mul_le_mul_of_nonneg_left (hG.trans (inv_anti₀ hκ (by linarith))) (abs_nonneg g)
      _ = κ⁻¹ * |g| := mul_comm _ _
  have hBG : -(beta * G * e) ≤ B * G := by
    have := mul_le_mul_of_nonneg_right ((neg_abs_le B).trans' (neg_le_neg hB)) hG0
    linarith
  have hGP : -(G' * Fn * e) ≤ G' * P := by
    have := mul_le_mul_of_nonneg_left ((neg_abs_le P).trans' (neg_le_neg hP)) hG'0
    linarith
  linarith

/-- The pointwise inequality of the transformation where `v = Φ(w) - l` is positive. With
`v = h > 0`, `0 < G ≤ 1/(2κ)`, `3/4 G² ≤ G' ≤ 1/(4κ²)`, `λ e² ≤ Q`, `|B| ≤ β e`, `|P| ≤ F e` and
`m ≥ 0`, the density `λ (G e)²` of the transformed energy is at most the transformed data tested
against `v`, plus the density of `a(u, θ)` for `θ = G h`, minus the data tested against `θ`. -/
private theorem key_ineq_density {lam beta κ G G' h e Fn g B P Q m : ℝ} (hlam : 0 < lam)
    (hκ : 0 < κ) (hG : 0 < G) (hGle : G ≤ (2 * κ)⁻¹) (hGd : 3 / 4 * G ^ 2 ≤ G')
    (hGd' : G' ≤ (4 * κ ^ 2)⁻¹) (hh : 0 < h) (hQ : lam * e ^ 2 ≤ Q) (hB : |B| ≤ beta * e)
    (hP : |P| ≤ Fn * e) (hm : 0 ≤ m) :
    lam * (G * e) ^ 2 ≤
      (beta ^ 2 / lam + κ⁻¹ * |g| + (lam * κ ^ 2)⁻¹ * Fn ^ 2) * h - G * (G * P) +
        ((G' * h + G * G) * Q + B * (G * h) + m) - (g * (G * h) - (G' * h + G * G) * P) := by
  have hkey := key_ineq (g := g) hlam hκ hG.le hGle hGd hGd' hB hP
  have hG'0 : 0 ≤ G' := le_trans (by positivity) hGd
  nlinarith [mul_nonneg hh.le hkey, mul_nonneg (mul_nonneg hG'0 hh.le) (sub_nonneg.2 hQ),
    mul_nonneg (sq_nonneg G) (sub_nonneg.2 hQ)]

omit [DecidableEq ι] in
/-- The test function `θ = (G(w) (Φ(w) - l))⁺` of the transformation, for `0 ≤ w ≤ M`,
`w ∈ H¹₀(Ω)` and `l ≥ 0`: it lies in `H¹₀(Ω)`, is bounded by `M/(4κ²)`, and its gradient is
`(G'(w) (Φ(w) - l) + G(w)²) ∇w` where `G(w) (Φ(w) - l) > 0` and zero elsewhere. -/
private theorem exists_driftTest {M κ l : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ) (hl : 0 ≤ l)
    {w : W1p mu Omega 2} (hw : w ∈ w1p0Submodule mu Omega 2)
    (hw0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value w x)
    (hwM : ∀ᵐ x ∂mu.restrict Omega, W1p.value w x ≤ M) :
    ∃ θ : W1p mu Omega 2, θ ∈ w1p0Submodule mu Omega 2 ∧
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value θ x) ∧
      (∀ᵐ x ∂mu.restrict Omega, ‖W1p.value θ x‖ ≤ (4 * κ ^ 2)⁻¹ * M) ∧
      (∀ᵐ x ∂mu.restrict Omega, W1p.value θ x =
        max (driftWeight (M + 2 * κ) κ (W1p.value w x) *
          (driftTransform (M + 2 * κ) κ (W1p.value w x) - l)) 0) ∧
      (∀ᵐ x ∂mu.restrict Omega, W1p.gradient θ x =
        if 0 < driftWeight (M + 2 * κ) κ (W1p.value w x) *
            (driftTransform (M + 2 * κ) κ (W1p.value w x) - l) then
          (driftWeightDeriv (M + 2 * κ) κ (W1p.value w x) *
              (driftTransform (M + 2 * κ) κ (W1p.value w x) - l) +
            driftWeight (M + 2 * κ) κ (W1p.value w x) *
              driftWeight (M + 2 * κ) κ (W1p.value w x)) • W1p.gradient w x
        else 0) := by
  set ν := mu.restrict Omega
  set A := M + 2 * κ
  have hA : 0 ≤ A := by positivity
  have hwA : ∀ᵐ x ∂ν, W1p.value w x ≤ A - 2 * κ := hwM.mono fun x hx => by simp only [A]; linarith
  -- `θ` is the positive part of `Ψ(w)`, `Ψ(t) = G(t) (Φ(t) - l)`.
  set Ψ : ℝ → ℝ := fun t => driftWeight A κ t * (driftTransform A κ t - l)
  have hΨ : ContDiff ℝ 1 Ψ :=
    (contDiff_driftWeight hκ).mul ((contDiff_driftTransform hκ).sub contDiff_const)
  have hΨ0 : Ψ 0 = 0 := by simp [Ψ, driftWeight_zero]
  have hdΨ : ∀ t, deriv Ψ t =
      driftWeightDeriv A κ t * (driftTransform A κ t - l) + driftWeight A κ t * driftWeight A κ t :=
    fun t => ((hasDerivAt_driftWeight hκ t).mul
      ((hasDerivAt_driftTransform hκ t).sub_const l)).deriv
  obtain ⟨θ₀, hθ₀v, hθ₀g⟩ := W1p.exists_value_gradient_ae_eq_comp_of_ae_abs_le (u := w) (M := M)
    (by norm_num) hΨ hΨ0
    (by filter_upwards [hw0, hwM] with x h₀ h₁ using abs_le.2 ⟨by linarith, h₁⟩)
  set θ := W1p.posPart (by norm_num) θ₀
  have hθv : ∀ᵐ x ∂ν, W1p.value θ x = max (W1p.value θ₀ x) 0 := by
    rw [W1p.value_posPart]
    exact Lp.coeFn_posPart _
  have hθg := W1p.gradient_posPart_ae (by norm_num) θ₀
  have hθ_nonneg : ∀ᵐ x ∂ν, 0 ≤ W1p.value θ x := hθv.mono fun x hx => hx ▸ le_max_right _ _
  -- `0 ≤ θ ≤ w / (4κ²)`, so `θ ∈ H¹₀(Ω)`.
  have hθle : ∀ᵐ x ∂ν, W1p.value θ x ≤ (4 * κ ^ 2)⁻¹ * W1p.value w x := by
    filter_upwards [hθv, hθ₀v, hw0, hwA] with x h₁ h₂ h₄ h₅
    rw [h₁, h₂]
    obtain ⟨hΦ0, hΦ⟩ := driftTransform_mem_Icc hκ h₄ h₅
    have hG0 := driftWeight_nonneg hκ h₄ h₅
    have hG := driftWeight_le hκ hA (W1p.value w x)
    refine max_le ?_ (by positivity)
    calc Ψ (W1p.value w x) ≤ driftWeight A κ (W1p.value w x) * driftTransform A κ (W1p.value w x) :=
          mul_le_mul_of_nonneg_left (by linarith) hG0
      _ ≤ (2 * κ)⁻¹ * (W1p.value w x / (2 * κ)) := mul_le_mul hG hΦ hΦ0 (by positivity)
      _ = (4 * κ ^ 2)⁻¹ * W1p.value w x := by field_simp; ring
  have hθmem : θ ∈ w1p0Submodule mu Omega 2 := by
    refine W1p.mem_w1p0Submodule_of_nonneg_of_le (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.smul_mem (4 * κ ^ 2)⁻¹ hw) hθ_nonneg ?_
    filter_upwards [hθle, W1p.value_smul_ae (4 * κ ^ 2)⁻¹ w] with x h₁ h₂
    rw [h₂, Pi.smul_apply, smul_eq_mul]
    exact h₁
  have hθbd : ∀ᵐ x ∂ν, ‖W1p.value θ x‖ ≤ (4 * κ ^ 2)⁻¹ * M := by
    filter_upwards [hθle, hθ_nonneg, hwM] with x h₁ h₂ h₃
    rw [Real.norm_of_nonneg h₂]
    exact h₁.trans (by gcongr)
  refine ⟨θ, hθmem, hθ_nonneg, hθbd, by filter_upwards [hθv, hθ₀v] with x h₁ h₂; rw [h₁, h₂], ?_⟩
  filter_upwards [hθg, hθ₀v, hθ₀g] with x h₁ h₂ h₃
  rw [h₁]
  by_cases hpos : 0 < Ψ (W1p.value w x)
  · rw [ite_eq_left hpos, indicator_of_mem (show x ∈ {y | 0 < W1p.value θ₀ y} by
      rw [Set.mem_ofPred_eq, h₂]
      exact hpos), h₃, hdΨ]
  · rw [ite_eq_right hpos, indicator_of_notMem (show x ∉ {y | 0 < W1p.value θ₀ y} by
      rw [Set.mem_ofPred_eq, h₂]
      exact hpos)]

section TransformEnergy

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ}

/-- **The transformed truncation satisfies an energy inequality without drift.** Let `u` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` with `b ∈ L²`, `c ≥ 0` and
`w = (u - k)⁺ ∈ H¹₀(Ω)`, `0 ≤ w ≤ M`, and let `z = Φ(w)` for the transform `Φ` with parameters
`A = M + 2κ` and `κ > 0`. At every level `l ≥ 0` the truncation `v = (z - l)⁺` satisfies

`λ ‖∇v‖² ≤ ∫ (‖b‖²/λ + ‖g‖/κ + ‖F‖²/(λκ²)) v - ∫ ⟪G(w) F, ∇v⟫`.

The proof tests the subsolution inequality against `θ = G(w) v`, a bounded function of `w`. Where
`v > 0`, `∇θ = (G'(w) v + G(w)²) ∇w` and `∇v = G(w) ∇w`, so the principal part of `a(u, θ)` is
that of `a(z, v)` plus `G'(w) v ⟨a ∇w, ∇w⟩`, which absorbs the drift pointwise
(`key_ineq_density`). -/
private theorem mul_norm_gradient_posPartAbove_sq_le_of_driftTransform
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hOmega : mu Omega ≠ ∞) (hb : MemLp b 2 (mu.restrict Omega)) {q : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    {g : EuclideanSpace ℝ ι → ℝ} (hg : MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (v : W1p mu Omega 2) x ∂mu ≤
          ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
            ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu)
    {k : ℝ} (hk : 0 ≤ k)
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {M κ : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ)
    (hwM : ∀ᵐ x ∂mu.restrict Omega, W1p.value (W1p.posPartAbove (by norm_num) hk u) x ≤ M)
    {z : W1p mu Omega 2}
    (hzv : ∀ᵐ x ∂mu.restrict Omega, W1p.value z x =
      driftTransform (M + 2 * κ) κ (W1p.value (W1p.posPartAbove (by norm_num) hk u) x))
    (hzg : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient z x =
      driftWeight (M + 2 * κ) κ (W1p.value (W1p.posPartAbove (by norm_num) hk u) x) •
        W1p.gradient (W1p.posPartAbove (by norm_num) hk u) x)
    {l : ℝ} (hl : 0 ≤ l) :
    lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) hl z)‖ ^ 2 ≤
      ∫ x in Omega, (‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) *
          W1p.value (W1p.posPartAbove (by norm_num) hl z) x ∂mu -
        ∫ x in Omega, ⟪driftWeight (M + 2 * κ) κ
            (W1p.value (W1p.posPartAbove (by norm_num) hk u) x) • F x,
          W1p.gradient (W1p.posPartAbove (by norm_num) hl z) x⟫ ∂mu := by
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  set A := M + 2 * κ
  set w := W1p.posPartAbove (by norm_num) hk u
  set v := W1p.posPartAbove (by norm_num) hl z
  have hlam := h.pos
  have hA : 0 ≤ A := by positivity
  -- `w` takes values in `[0, M] ⊆ [0, A - 2κ]`.
  have hwv := W1p.value_posPartAbove_ae (by norm_num) hk u
  have hw0 : ∀ᵐ x ∂ν, 0 ≤ W1p.value w x := W1p.value_posPartAbove_nonneg_ae (by norm_num) hk u
  have hwA : ∀ᵐ x ∂ν, W1p.value w x ≤ A - 2 * κ := hwM.mono fun x hx => by simp only [A]; linarith
  -- The test function `θ = G(w) (Φ(w) - l)⁺`.
  obtain ⟨θ, hθmem, hθ_nonneg, hθbd, hθv, hθg⟩ := exists_driftTest hM hκ hl hboundary hw0 hwM
  -- `0 ≤ v ≤ M / (2κ)`.
  have hvv := W1p.value_posPartAbove_ae (by norm_num) hl z
  have hvbd : ∀ᵐ x ∂ν, ‖W1p.value v x‖ ≤ M / (2 * κ) := by
    filter_upwards [hvv, hzv, hw0, hwA, hwM] with x h₁ h₂ h₃ h₄ h₅
    obtain ⟨-, hΦ⟩ := driftTransform_mem_Icc hκ h₃ h₄
    rw [h₁, Real.norm_of_nonneg (le_max_right _ _), h₂]
    refine max_le ?_ (by positivity)
    calc driftTransform A κ (W1p.value w x) - l ≤ W1p.value w x / (2 * κ) := by linarith
      _ ≤ M / (2 * κ) := by gcongr
  -- The subsolution inequality tested against `θ`.
  have htest := hu ⟨θ, hθmem⟩ hθ_nonneg
  -- Integrability of the terms. The drift term is integrable since `b, ∇u ∈ L²` and `θ` is
  -- bounded.
  have hcoeff := h.memLp_energyIntegrand_zero_drift ha hc hc_bound
  have hq2' : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ≥0) ≤ q := by exact_mod_cast hq
    exact_mod_cast this
  have hF2 : MemLp F 2 ν := hF.mono_exponent hq2'
  have hg1 : Integrable g ν := by
    refine memLp_one_iff_integrable.1 (hg.mono_exponent ?_)
    have : (1 : ℝ≥0) ≤ q / 2 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      linarith
    exact_mod_cast this
  have hGmeas : AEStronglyMeasurable (fun x => driftWeight A κ (W1p.value w x)) ν :=
    (contDiff_driftWeight hκ).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (W1p.value w))
  have hGbd : ∀ᵐ x ∂ν, ‖driftWeight A κ (W1p.value w x)‖ ≤ (2 * κ)⁻¹ := by
    filter_upwards [hw0, hwA] with x h₁ h₂
    rw [Real.norm_of_nonneg (driftWeight_nonneg hκ h₁ h₂)]
    exact driftWeight_le hκ hA _
  have hGF : MemLp (fun x => driftWeight A κ (W1p.value w x) • F x) 2 ν :=
    hF2.of_le_mul (c := (2 * κ)⁻¹) (hGmeas.smul hF.aestronglyMeasurable)
      (hGbd.mono fun x hx => by rw [norm_smul]; gcongr)
  have hg'int : Integrable
      (fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) ν :=
    ((hb.norm.integrable_sq.div_const lam).add (hg1.norm.const_mul _)).add
      (hF2.norm.integrable_sq.const_mul _)
  have hY₁ : Integrable (fun x => g x * W1p.value θ x) ν :=
    hg1.mul_bdd (Lp.aestronglyMeasurable _) hθbd
  have hY₂ := hF2.integrable_inner (𝕜 := ℝ) (Lp.memLp (W1p.gradient θ))
  have hR₁ : Integrable (fun x => (‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) *
      W1p.value v x) ν :=
    hg'int.mul_bdd (Lp.aestronglyMeasurable _) hvbd
  have hR₂ := hGF.integrable_inner (𝕜 := ℝ) (Lp.memLp (W1p.gradient v))
  have hX := integrable_energyIntegrand_jetField hcoeff u θ
  have hD : Integrable (fun x => ⟪b x, W1p.gradient u x⟫ * W1p.value θ x) ν :=
    (hb.integrable_inner (𝕜 := ℝ) (Lp.memLp (W1p.gradient u))).mul_bdd
      (Lp.aestronglyMeasurable _) hθbd
  have hP : Integrable (fun x => lam * ‖W1p.gradient v x‖ ^ 2) ν :=
    (Lp.memLp (W1p.gradient v)).norm.integrable_sq.const_mul lam
  -- The pointwise inequality.
  have hpt : ∀ᵐ x ∂ν, lam * ‖W1p.gradient v x‖ ^ 2 ≤
      ((‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) * W1p.value v x -
        ⟪driftWeight A κ (W1p.value w x) • F x, W1p.gradient v x⟫) +
      (energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x)
          (jetField u x) (jetField θ x) + ⟪b x, W1p.gradient u x⟫ * W1p.value θ x) -
      (g x * W1p.value θ x - ⟪F x, W1p.gradient θ x⟫) := by
    filter_upwards [hwv, hw0, hwA, W1p.gradient_posPartAbove_ae (by norm_num) hk u, hzv, hzg, hvv,
      W1p.gradient_posPartAbove_ae (by norm_num) hl z, hθv, hθg,
      ae_restrict_mem Omega.isOpen.measurableSet] with x hwvx hw0x hwAx hwgx hzvx hzgx hvvx hvgx
      hθvx hθgx hx
    simp only [jetField_apply, energyIntegrand_apply, driftForm_apply, massForm_apply,
      Pi.zero_apply, inner_zero_left, zero_mul, add_zero]
    rw [hvvx, hvgx, hθvx, hθgx]
    set t := W1p.value w x
    by_cases hmain : l < driftTransform A κ t ∧ 0 < t
    · obtain ⟨hΦl, ht⟩ := hmain
      -- Here `u > k`, `∇w = ∇u`, `v = Φ(t) - l` and `θ = G(t) v`.
      have hku : k < W1p.value u x := by
        rw [hwvx] at ht
        by_contra hle
        rw [max_eq_right (by linarith)] at ht
        exact lt_irrefl _ ht
      have hut : W1p.value u x = t + k := by
        rw [hwvx, max_eq_left (by linarith)]
        ring
      have hwg' : W1p.gradient w x = W1p.gradient u x := by
        rw [hwgx, indicator_of_mem (show x ∈ {y | k < W1p.value u y} from hku)]
      set G := driftWeight A κ t
      set G' := driftWeightDeriv A κ t
      set h' := driftTransform A κ t - l
      set e := W1p.gradient u x
      have hG : 0 < G := driftWeight_pos hκ ht hwAx
      have hh : 0 < h' := sub_pos.2 hΦl
      have hzl : x ∈ {y | l < W1p.value z y} := by
        rw [Set.mem_ofPred_eq, hzvx]
        exact hΦl
      rw [indicator_of_mem hzl, ite_eq_left (mul_pos hG hh), hzgx, hwg', hzvx, max_eq_left hh.le,
        max_eq_left (mul_pos hG hh).le]
      -- The scalar quantities.
      set Q := matrixBilinearForm (a x) e e
      have hQ : lam * ‖e‖ ^ 2 ≤ Q := by
        have := h.lower_bound hx e
        rw [← matrixBilinearForm_self] at this
        convert this
      have hB : |⟪b x, e⟫| ≤ ‖b x‖ * ‖e‖ := abs_real_inner_le_norm _ _
      have hPF : |⟪F x, e⟫| ≤ ‖F x‖ * ‖e‖ := abs_real_inner_le_norm _ _
      have hcu : 0 ≤ c x * W1p.value u x * (G * h') := by
        have := hc_nonneg x hx
        rw [hut]
        positivity
      have hkey := key_ineq_density (g := g x) hlam hκ hG (driftWeight_le hκ hA t)
        (mul_driftWeight_sq_le_driftWeightDeriv hκ hw0x hwAx) (driftWeightDeriv_le hκ t) hh hQ
        hB hPF hcu
      simp only [norm_smul, Real.norm_of_nonneg hG.le, real_inner_smul_left,
        real_inner_smul_right, map_smul, smul_apply, smul_eq_mul, Real.norm_eq_abs (g x)]
      linarith
    · -- Otherwise `Φ(t) ≤ l`, so `v`, `θ` and their gradients vanish at `x`.
      have hΦl : driftTransform A κ t ≤ l := by
        by_contra hlt
        refine hmain ⟨not_le.1 hlt, lt_of_le_of_ne hw0x fun h0 => ?_⟩
        rw [← h0, driftTransform_zero] at hlt
        exact hlt hl
      have hzl : x ∉ {y | l < W1p.value z y} := by
        rw [Set.mem_ofPred_eq, hzvx]
        exact not_lt.2 hΦl
      have hΨle : driftWeight A κ t * (driftTransform A κ t - l) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (driftWeight_nonneg hκ hw0x hwAx) (by linarith)
      rw [indicator_of_notMem hzl, ite_eq_right (not_lt.2 hΨle), hzvx, max_eq_right (by linarith),
        max_eq_right hΨle]
      simp
  -- Integrate.
  have hRR : Integrable (fun x => (‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) *
      W1p.value v x - ⟪driftWeight A κ (W1p.value w x) • F x, W1p.gradient v x⟫) ν := hR₁.sub hR₂
  have hXD : Integrable (fun x => energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x) (jetField u x) (jetField θ x) +
        ⟪b x, W1p.gradient u x⟫ * W1p.value θ x) ν := hX.add hD
  have hRX : Integrable (fun x => (‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) *
      W1p.value v x - ⟪driftWeight A κ (W1p.value w x) • F x, W1p.gradient v x⟫ +
        (energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x)
          (jetField u x) (jetField θ x) + ⟪b x, W1p.gradient u x⟫ * W1p.value θ x)) ν :=
    hRR.add hXD
  have hYY : Integrable (fun x => g x * W1p.value θ x - ⟪F x, W1p.gradient θ x⟫) ν := hY₁.sub hY₂
  have hint := integral_mono_ae hP (hRX.sub hYY) hpt
  simp only [Pi.sub_apply] at hint
  rw [integral_const_mul, W1p.integral_norm_gradient_sq_eq_norm_gradient_sq, integral_sub hRX hYY,
    integral_add hRR hXD, integral_sub hR₁ hR₂, integral_add hX hD, integral_sub hY₁ hY₂,
    ← energyFormH1_def] at hint
  linarith

end TransformEnergy

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The scalar datum `‖b‖²/λ + ‖g‖/κ + ‖F‖²/(λκ²)` of the transformed problem lies in `L^{q/2}`,
with `‖·‖_{q/2} ≤ ‖b‖_q²/λ + ‖g‖_{q/2}/κ + ‖F‖_q²/(λκ²)`. -/
private theorem memLp_and_toReal_eLpNorm_le_of_drift {q : ℝ≥0} (hq : 2 ≤ (q : ℝ))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hb : MemLp b q (mu.restrict Omega))
    {g : EuclideanSpace ℝ ι → ℝ} (hg : MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict Omega))
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : 0 < κ) :
    MemLp (fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2)
        (q / 2 : ℝ≥0) (mu.restrict Omega) ∧
      (eLpNorm (fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2)
          (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal ≤
        lam⁻¹ * (eLpNorm b q (mu.restrict Omega)).toReal ^ 2 +
          κ⁻¹ * (eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal +
          (lam * κ ^ 2)⁻¹ * (eLpNorm F q (mu.restrict Omega)).toReal ^ 2 := by
  set ν := mu.restrict Omega
  have hq2 : ((q / 2 : ℝ≥0) : ℝ) = q / 2 := by simp
  have hp1 : (1 : ℝ≥0∞) ≤ ((q / 2 : ℝ≥0) : ℝ≥0∞) := by
    have : (1 : ℝ≥0) ≤ q / 2 := by
      rw [← NNReal.coe_le_coe, hq2, NNReal.coe_one]
      linarith
    exact_mod_cast this
  -- The three summands, the first and the last squares of norms of `L^q` functions.
  have hb2 := hb.norm_sq
  have hnb := eLpNorm_norm_sq (q := q) hb.aestronglyMeasurable
  have hF2 := hF.norm_sq
  have hnF := eLpNorm_norm_sq (q := q) hF.aestronglyMeasurable
  have hsmul₀ (r : ℝ) (H : EuclideanSpace ℝ ι → ℝ) : (fun x => r * H x) = r • H := by
    ext x
    simp
  have hsq (r : ℝ) (hr : 0 ≤ r) {H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      (hH : MemLp H q ν) (hnH : eLpNorm (fun x => ‖H x‖ ^ 2) (q / 2 : ℝ≥0) ν =
        eLpNorm H q ν ^ (2 : ℝ)) :
      eLpNorm (fun x => r * ‖H x‖ ^ 2) (q / 2 : ℝ≥0) ν =
        ENNReal.ofReal (r * (eLpNorm H q ν).toReal ^ 2) := by
    rw [hsmul₀, eLpNorm_const_smul, hnH, Real.eNorm_of_nonneg hr, ENNReal.ofReal_mul hr,
      ← ENNReal.ofReal_toReal hH.eLpNorm_ne_top,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg zero_le_two, Real.rpow_two,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  have he1 := hsq lam⁻¹ (by positivity) hb hnb
  have he3 := hsq (lam * κ ^ 2)⁻¹ (by positivity) hF hnF
  have he2 : eLpNorm (fun x => κ⁻¹ * ‖g x‖) (q / 2 : ℝ≥0) ν =
      ENNReal.ofReal (κ⁻¹ * (eLpNorm g (q / 2 : ℝ≥0) ν).toReal) := by
    rw [hsmul₀, eLpNorm_const_smul, eLpNorm_norm _ hg.aestronglyMeasurable,
      Real.eNorm_of_nonneg (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
  have hdiv : (fun x => ‖b x‖ ^ 2 / lam) = fun x => lam⁻¹ * ‖b x‖ ^ 2 := by
    ext x
    ring
  have h1 : MemLp (fun x => ‖b x‖ ^ 2 / lam) (q / 2 : ℝ≥0) ν := hdiv ▸ hb2.const_mul lam⁻¹
  have h2 : MemLp (fun x => κ⁻¹ * ‖g x‖) (q / 2 : ℝ≥0) ν := hg.norm.const_mul κ⁻¹
  have h3 : MemLp (fun x => (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) (q / 2 : ℝ≥0) ν := hF2.const_mul _
  refine ⟨(h1.add h2).add h3, ?_⟩
  have hsum : eLpNorm (fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2)
      (q / 2 : ℝ≥0) ν ≤
      ENNReal.ofReal (lam⁻¹ * (eLpNorm b q ν).toReal ^ 2) +
        ENNReal.ofReal (κ⁻¹ * (eLpNorm g (q / 2 : ℝ≥0) ν).toReal) +
        ENNReal.ofReal ((lam * κ ^ 2)⁻¹ * (eLpNorm F q ν).toReal ^ 2) := by
    rw [← he1, ← he2, ← he3, ← hdiv]
    have hA := eLpNorm_add_le (f := fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖)
      (g := fun x => (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2) (μ := ν) hp1
    have hB := eLpNorm_add_le (f := fun x => ‖b x‖ ^ 2 / lam)
      (g := fun x => κ⁻¹ * ‖g x‖) (μ := ν) hp1
    calc _ ≤ _ := hA
      _ ≤ _ := by
        gcongr
        exact hB
  refine (ENNReal.toReal_mono (by finiteness) hsum).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
    (by finiteness), ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

/-- If the transform with parameters `A = m + 2κ` and `κ` is at most `C₁` at a point `t` with
`m - κ/2 < t ≤ m`, then `m ≤ 3 e^(C₁ + 1) κ`: the transform grows like `log (A / κ)` near the top
of its range. -/
private theorem le_mul_of_driftTransform_le {m κ C₁ t : ℝ} (hκ : 0 < κ) (ht0 : 0 ≤ t)
    (hlow : m - κ / 2 < t) (htm : t ≤ m) (hΦ : driftTransform (m + 2 * κ) κ t ≤ C₁) :
    m ≤ 3 * Real.exp (C₁ + 1) * κ := by
  set A := m + 2 * κ
  have hle := (le_driftTransform hκ ht0 (by linarith) (by nlinarith)).trans hΦ
  have h8 : 0 < 8 * κ ^ 2 := by positivity
  have hlog : Real.log (A ^ 2 + κ ^ 2) ≤ Real.log (8 * κ ^ 2) + 2 * (C₁ + 1) := by linarith
  rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, Real.exp_log h8,
    show 2 * (C₁ + 1) = (C₁ + 1) + (C₁ + 1) by ring, Real.exp_add] at hlog
  have hE := Real.exp_pos (C₁ + 1)
  nlinarith [sq_nonneg (3 * Real.exp (C₁ + 1) * κ - m), mul_pos hE hκ]

/-- **The transform of a subsolution is bounded.** For a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` with `b ∈ L^q` and `w = (u - k)⁺ ≤ M`, and `κ > 0`,
Stampacchia's bound for `z = Φ(w)` (`mul_norm_gradient_posPartAbove_sq_le_of_driftTransform`)
gives

`Φ(w) ≤ C (β̂² + a/κ + (f/κ)² + f/κ)`,

where `β̂ = ‖b‖_q |Ω| ^ (1/n - 1/q) / λ`, `a = ‖g‖_{q/2} |Ω| ^ (2/n - 2/q) / λ` and
`f = ‖F‖_q |Ω| ^ (1/n - 1/q) / λ`, with `C` depending only on `n`, `q` and `mu`. -/
private theorem exists_ae_driftTransform_le [Nonempty ι] {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k M κ : ℝ}
      (hk : 0 ≤ k), mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ Omega, ‖c x‖ ≤ gamma) → (∀ x ∈ Omega, 0 ≤ c x) → MemLp b q (mu.restrict Omega) →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 c u (v : W1p mu Omega 2) +
              ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (v : W1p mu Omega 2) x ∂mu ≤
            ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
              ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      0 ≤ M → 0 < κ →
      (∀ᵐ x ∂mu.restrict Omega, W1p.value (W1p.posPartAbove (by norm_num) hk u) x ≤ M) →
      ∀ᵐ x ∂mu.restrict Omega,
        driftTransform (M + 2 * κ) κ (W1p.value (W1p.posPartAbove (by norm_num) hk u) x) ≤
          C * (((eLpNorm b q (mu.restrict Omega)).toReal *
              mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam) ^ 2 +
            (eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
              mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) / lam / κ +
            ((eLpNorm F q (mu.restrict Omega)).toReal *
              mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam / κ) ^ 2 +
            (eLpNorm F q (mu.restrict Omega)).toReal *
              mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam / κ) := by
  obtain ⟨CS, hCS, hStamp⟩ :=
    exists_ae_value_le_add_of_forall_mul_norm_gradient_posPartAbove_sq_le (mu := mu) hq hqn
  refine ⟨CS, hCS, fun {Omega a b c lam Lam gamma g F u k M κ} hk hOmega h ha hc hc_bound
    hc_nonneg hb hg hF hu hboundary hM hκ hwM => ?_⟩
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  set n : ℕ := Fintype.card ι
  have hlam := h.pos
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    have : (2 : ℝ≥0) ≤ q := by exact_mod_cast hq.le
    exact_mod_cast this
  set w := W1p.posPartAbove (by norm_num) hk u
  have hw0 : ∀ᵐ x ∂ν, 0 ≤ W1p.value w x := W1p.value_posPartAbove_nonneg_ae (by norm_num) hk u
  have hwA : ∀ᵐ x ∂ν, W1p.value w x ≤ M + 2 * κ - 2 * κ := hwM.mono fun x hx => by linarith
  -- The transformed function `z = Φ(w)`.
  obtain ⟨z, hzv, hzg⟩ := W1p.exists_value_gradient_ae_eq_comp_of_ae_abs_le (u := w) (M := M)
    (by norm_num) (contDiff_driftTransform (A := M + 2 * κ) hκ) driftTransform_zero
    (by filter_upwards [hw0, hwM] with x h₀ h₁ using abs_le.2 ⟨by linarith, h₁⟩)
  rw [deriv_driftTransform hκ] at hzg
  -- `0 ≤ z⁺ ≤ w / (2κ)`, so `z⁺ ∈ H¹₀(Ω)`.
  have hzb : W1p.posPartAbove (by norm_num) (le_refl 0) z ∈ w1p0Submodule mu Omega 2 := by
    refine W1p.mem_w1p0Submodule_of_nonneg_of_le (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.smul_mem (2 * κ)⁻¹ hboundary)
      (W1p.value_posPartAbove_nonneg_ae (by norm_num) le_rfl z) ?_
    filter_upwards [W1p.value_posPartAbove_ae (by norm_num) (le_refl 0) z, hzv, hw0, hwA,
      W1p.value_smul_ae (2 * κ)⁻¹ w] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, h₅, Pi.smul_apply, smul_eq_mul, sub_zero]
    obtain ⟨-, hΦ⟩ := driftTransform_mem_Icc hκ h₃ h₄
    exact max_le (hΦ.trans_eq (by ring)) (by positivity)
  -- The data of the transformed problem.
  obtain ⟨hg'mem, hg'le⟩ := memLp_and_toReal_eLpNorm_le_of_drift hq.le hb hg hF hlam hκ
  have hGmeas : AEStronglyMeasurable
      (fun x => driftWeight (M + 2 * κ) κ (W1p.value w x)) ν :=
    (contDiff_driftWeight hκ).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (W1p.value w))
  have hGF : ∀ᵐ x ∂ν, ‖driftWeight (M + 2 * κ) κ (W1p.value w x) • F x‖ ≤ κ⁻¹ * ‖F x‖ := by
    filter_upwards [hw0, hwA] with x h₁ h₂
    rw [norm_smul, Real.norm_of_nonneg (driftWeight_nonneg hκ h₁ h₂)]
    exact mul_le_mul_of_nonneg_right ((driftWeight_le hκ (by positivity) _).trans
      (inv_anti₀ hκ (by linarith))) (norm_nonneg _)
  have hF'mem : MemLp (fun x => driftWeight (M + 2 * κ) κ (W1p.value w x) • F x) q ν :=
    hF.of_le_mul (hGmeas.smul hF.aestronglyMeasurable) hGF
  have hF'le : (eLpNorm (fun x => driftWeight (M + 2 * κ) κ (W1p.value w x) • F x) q ν).toReal ≤
      κ⁻¹ * (eLpNorm F q ν).toReal := by
    have := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hGmeas.smul hF.aestronglyMeasurable) hGF q
    refine (ENNReal.toReal_mono (by finiteness) this).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Stampacchia's bound for `z`.
  have hz := hStamp (u := z) le_rfl hOmega hlam hg'mem hF'mem hzb fun l hkl =>
    mul_norm_gradient_posPartAbove_sq_le_of_driftTransform h ha hc hc_bound hc_nonneg hOmega
      (hb.mono_exponent hq2) hq.le hg hF hu hk hboundary hM hκ hwM hzv hzg hkl
  filter_upwards [hz, hzv] with x hx hzx
  rw [← hzx]
  refine hx.trans ?_
  -- The powers of `|Ω|`: `|Ω| ^ (2/n - 2/q) = (|Ω| ^ (1/n - 1/q))²`.
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  have hm : 0 ≤ m := measureReal_nonneg
  have hP₁ : m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) = (m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hm]
    ring_nf
  set Bq := (eLpNorm b q ν).toReal
  set Gq := (eLpNorm g (q / 2 : ℝ≥0) ν).toReal
  set Fq := (eLpNorm F q ν).toReal
  set P₁ := m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)
  rw [zero_add]
  gcongr CS * ?_
  calc ((eLpNorm (fun x => ‖b x‖ ^ 2 / lam + κ⁻¹ * ‖g x‖ + (lam * κ ^ 2)⁻¹ * ‖F x‖ ^ 2)
          (q / 2 : ℝ≥0) ν).toReal * m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) +
        (eLpNorm (fun x => driftWeight (M + 2 * κ) κ (W1p.value w x) • F x) q ν).toReal * P₁) /
          lam
      ≤ ((lam⁻¹ * Bq ^ 2 + κ⁻¹ * Gq + (lam * κ ^ 2)⁻¹ * Fq ^ 2) *
            m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) + κ⁻¹ * Fq * P₁) / lam := by
        gcongr
    _ = (Bq * P₁ / lam) ^ 2 + Gq * m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) / lam / κ +
          (Fq * P₁ / lam / κ) ^ 2 + Fq * P₁ / lam / κ := by
        rw [hP₁]
        field_simp

/-! ### The global bound -/

/-- **Global boundedness of weak subsolutions with a drift in `L^q` and data** (Gilbarg–Trudinger,
Theorem 8.16 with the integrability of the remark following it; the drift case of Rosales,
Lemma 3.2). Let `n ≥ 1` be
the dimension, let `q > n` with `q > 2`, and let `B ≥ 0` bound the dimensionless size of the drift.
There is `C > 0`, depending only on `n`, `q`, `B` and the normalization of the additive Haar measure
`mu`, with the following property. Let `Ω` have finite measure, let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b ∈ L^q(Ω; ℝⁿ)` be a drift with
`‖b‖_q |Ω| ^ (1/n - 1/q) ≤ B λ`, let `c` be bounded, measurable and nonnegative, and let
`g ∈ L^{q/2}(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`. If `u ∈ H¹(Ω)` is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` in `Ω`,

that is `a₀(u, v) + ∫_Ω ⟪b, ∇u⟫ v ≤ ∫_Ω g v - ∫_Ω ⟪F, ∇v⟫` for every nonnegative `v ∈ H¹₀(Ω)`,
where `a₀` is the energy form of `-∂ᵢ(aⁱʲ ∂ⱼ·) + c`, and `u ≤ k` on `∂Ω` for a level `k ≥ 0`, in
the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`.

No smallness of the drift is assumed: `B` is arbitrary and only enters the constant, and the bound
is invariant under dilations of `Ω`. Since `q > n`, the drift integral converges for every
`v ∈ H¹₀(Ω)` by the Sobolev inequality, so the hypothesis is the usual weak formulation. For a
bounded drift this is `TauCeti.PDE.exists_ae_value_le_add_of_drift`, and without
drift it is `TauCeti.PDE.exists_ae_value_le_add_mul_div_mul_rpow` and its divergence-form
analogue. -/
theorem exists_ae_value_le_add_of_memLp_drift [Nonempty ι] {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma : ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ Omega, ‖c x‖ ≤ gamma) → (∀ x ∈ Omega, 0 ≤ c x) → MemLp b q (mu.restrict Omega) →
      (eLpNorm b q (mu.restrict Omega)).toReal *
        mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) ≤ B * lam →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 c u (v : W1p mu Omega 2) +
              ∫ x in Omega, ⟪b x, W1p.gradient u x⟫ * W1p.value (v : W1p mu Omega 2) x ∂mu ≤
            ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
              ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (((eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) +
          (eLpNorm F q (mu.restrict Omega)).toReal *
            mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam) := by
  obtain ⟨C₀, hC₀, hz⟩ := exists_ae_driftTransform_le (mu := mu) hq hqn
  set B' := max B 0
  set C₁ := C₀ * (B' ^ 2 + 3)
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨3 * Real.exp (C₁ + 1), by positivity, fun {Omega a b c lam Lam gamma g F u k} hk
    hOmega h ha hc hc_bound hc_nonneg hb hsmall hg hF hu hboundary => ?_⟩
  rcases eq_or_ne (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) 0 with hν | hν
  · exact ae_iff.2 (measure_mono_null (subset_univ _) (by rw [hν]; rfl))
  set ν := mu.restrict Omega
  have : (ae ν).NeBot := ae_neBot.2 hν
  have hlam := h.pos
  set n : ℕ := Fintype.card ι
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι))
  set Gq := (eLpNorm g (q / 2 : ℝ≥0) ν).toReal
  set Fq := (eLpNorm F q ν).toReal
  set κ₀ := (Gq * m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) + Fq * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam
  have ha₀ : 0 ≤ Gq * m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) / lam := by positivity
  have hf₀ : 0 ≤ Fq * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam := by positivity
  have hκ₀ : 0 ≤ κ₀ := by positivity
  -- The dimensionless size of the drift is at most `B' = max B 0`.
  have hβB : (eLpNorm b q ν).toReal * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam ≤ B' := by
    rw [div_le_iff₀ hlam]
    exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le)
  have hβ0 : 0 ≤ (eLpNorm b q ν).toReal * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam := by positivity
  -- `w = (u - k)⁺` is bounded; let `M` be its essential supremum.
  set w := W1p.posPartAbove (by norm_num) hk u
  have hw0 : ∀ᵐ x ∂ν, 0 ≤ W1p.value w x := W1p.value_posPartAbove_nonneg_ae (by norm_num) hk u
  obtain ⟨M₀, hM₀⟩ := exists_ae_value_le_of_drift h ha hc hc_bound hc_nonneg hOmega hq hqn hb hg
    hF hu hk hboundary
  have hwM₀ : ∀ᵐ x ∂ν, W1p.value w x ≤ max (M₀ - k) 0 := by
    filter_upwards [hM₀, W1p.value_posPartAbove_ae (by norm_num) hk u] with x h₁ h₂
    rw [h₂]
    exact max_le_max (by linarith) le_rfl
  set M := max (essSup (fun x => W1p.value w x) ν) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hwM : ∀ᵐ x ∂ν, W1p.value w x ≤ M :=
    (ae_le_essSup (isBoundedUnder_of_eventually_le hwM₀)).mono fun _ hx =>
      hx.trans (le_max_left _ _)
  have hnot : ∀ t, 0 ≤ t → t < M → ¬ ∀ᵐ x ∂ν, W1p.value w x ≤ t := fun t ht htM hae =>
    not_le.2 htM (max_le (essSup_le_of_ae_le t hae
      (isCoboundedUnder_le_of_eventually_le (ae ν) hw0)) ht)
  -- For every admissible `κ`, the transform bounds `M` by a multiple of `κ`.
  have hkey : ∀ κ, 0 < κ → κ₀ ≤ κ → M ≤ 3 * Real.exp (C₁ + 1) * κ := by
    intro κ hκ hκκ
    have hzκ := hz hk hOmega h ha hc hc_bound hc_nonneg hb hg hF hu hboundary hM hκ hwM
    -- The right-hand side is at most `C₁`, since `a, f ≤ κ₀ ≤ κ` and `β̂ ≤ B'`.
    have ha : Gq * m ^ (2 / (n : ℝ) - 2 / (q : ℝ)) / lam / κ ≤ 1 :=
      (div_le_one hκ).2 ((le_add_of_nonneg_right hf₀).trans (by rw [← add_div]; exact hκκ))
    have hf : Fq * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam / κ ≤ 1 :=
      (div_le_one hκ).2 ((le_add_of_nonneg_left ha₀).trans (by rw [← add_div]; exact hκκ))
    have hf0 : 0 ≤ Fq * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) / lam / κ := by positivity
    have hbound : ∀ᵐ x ∂ν, driftTransform (M + 2 * κ) κ (W1p.value w x) ≤ C₁ := by
      filter_upwards [hzκ] with x hx
      refine hx.trans (mul_le_mul_of_nonneg_left ?_ hC₀.le)
      nlinarith [pow_le_pow_left₀ hβ0 hβB 2, pow_le_one₀ (n := 2) hf0 hf]
    rcases le_or_gt M κ with hMκ | hMκ
    · nlinarith [Real.add_one_le_exp (C₁ + 1)]
    · -- Some point has `w > M - κ/2`; there the transform is large.
      have hfreq := Filter.not_eventually.1 (hnot (M - κ / 2) (by linarith) (by linarith))
      obtain ⟨x, hx₁, hx₂, hx₃, hx₄⟩ := (hfreq.and_eventually (hbound.and (hwM.and hw0))).exists
      exact le_mul_of_driftTransform_le hκ hx₄ (not_le.1 hx₁) hx₃ hx₂
  -- Letting `κ` decrease to `κ₀`.
  have hMκ₀ : M ≤ 3 * Real.exp (C₁ + 1) * κ₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hE : 0 < 3 * Real.exp (C₁ + 1) := by positivity
    have := hkey (κ₀ + ε / (3 * Real.exp (C₁ + 1))) (by positivity) (by
      linarith [div_pos hε hE])
    calc M ≤ 3 * Real.exp (C₁ + 1) * (κ₀ + ε / (3 * Real.exp (C₁ + 1))) := this
      _ = 3 * Real.exp (C₁ + 1) * κ₀ + ε := by field_simp
  filter_upwards [hwM, W1p.value_posPartAbove_ae (by norm_num) hk u] with x h₁ h₂
  rw [h₂] at h₁
  linarith [le_max_left (W1p.value u x - k) 0]

/-- **Global boundedness of weak subsolutions with a bounded drift and data** (Gilbarg–Trudinger,
Theorem 8.16, for bounded coefficients). Let `n ≥ 1` be the dimension, let `q > n` with `q > 2`,
and let `B ≥ 0` bound the dimensionless drift size. There is `C > 0`, depending only on `n`, `q`,
`B` and the normalization of the additive Haar measure `mu`, with the following property. Let `Ω`
have finite measure, let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b` be a measurable drift with `‖b‖ ≤ β` and `β |Ω| ^ (1/n) ≤ B λ`, let `c` be
bounded, measurable and nonnegative, and let `g ∈ L^{q/2}(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`. If `u ∈ H¹(Ω)`
is a weak subsolution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ g + ∂ᵢFⁱ` in `Ω`,

that is `a(u, v) ≤ ∫_Ω g v - ∫_Ω ⟪F, ∇v⟫` for every nonnegative `v ∈ H¹₀(Ω)`, and `u ≤ k` on `∂Ω`
for a level `k ≥ 0`, in the sense that `(u - k)⁺ ∈ H¹₀(Ω)`, then almost everywhere in `Ω`

`u ≤ k + C (‖g‖_{q/2} |Ω| ^ (2/n - 2/q) + ‖F‖_q |Ω| ^ (1/n - 1/q)) / λ`.

This is the case of a bounded drift of `TauCeti.PDE.exists_ae_value_le_add_of_memLp_drift`, since
`‖b‖_q ≤ β |Ω| ^ (1/q)`. -/
theorem exists_ae_value_le_add_of_drift [Nonempty ι] {q : ℝ≥0} (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ} {g : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k),
      mu Omega ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ Omega, ‖b x‖ ≤ beta) → (∀ x ∈ Omega, ‖c x‖ ≤ gamma) → (∀ x ∈ Omega, 0 ≤ c x) →
      beta * mu.real Omega ^ (Fintype.card ι : ℝ)⁻¹ ≤ B * lam →
      MemLp g (q / 2 : ℝ≥0) (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu -
              ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2 →
      ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤
        k + C * (((eLpNorm g (q / 2 : ℝ≥0) (mu.restrict Omega)).toReal *
            mu.real Omega ^ (2 / (Fintype.card ι : ℝ) - 2 / (q : ℝ)) +
          (eLpNorm F q (mu.restrict Omega)).toReal *
            mu.real Omega ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹)) / lam) := by
  obtain ⟨C, hC, hbound⟩ := exists_ae_value_le_add_of_memLp_drift (mu := mu) hq hqn (max B 0)
  refine ⟨C, hC, fun {Omega a b c lam Lam beta gamma g F u k} hk hOmega h ha hb hc hb_bound
    hc_bound hc_nonneg hsmall hg hF hu hboundary => ?_⟩
  set ν := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  set n : ℕ := Fintype.card ι
  set m := mu.real (Omega : Set (EuclideanSpace ℝ ι)) with hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hb_ae : ∀ᵐ x ∂ν, ‖b x‖ ≤ max beta 0 :=
    (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx =>
      (hb_bound x hx).trans (le_max_left _ _)
  have hc_ae : ∀ᵐ x ∂ν, ‖c x‖ ≤ gamma :=
    (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx => hc_bound x hx
  -- `‖b‖_q ≤ β |Ω| ^ (1/q)`, so the dimensionless size of the drift is at most `B`.
  have hbq : (eLpNorm b q ν).toReal ≤ max beta 0 * m ^ (q : ℝ)⁻¹ := by
    have := eLpNorm_le_of_ae_bound (p := (q : ℝ≥0∞)) hb hb_ae
    rw [Measure.restrict_apply_univ, ENNReal.coe_toReal] at this
    refine (ENNReal.toReal_mono (by finiteness) this).trans_eq ?_
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (le_max_right _ _),
      mul_comm, hm, measureReal_def]
  have hsmall' : (eLpNorm b q ν).toReal * m ^ ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) ≤ max B 0 * lam := by
    have hlam := h.pos
    rcases le_total beta 0 with hβ | hβ
    · rw [max_eq_right hβ, zero_mul] at hbq
      rw [le_antisymm hbq ENNReal.toReal_nonneg, zero_mul]
      positivity
    · rw [max_eq_left hβ] at hbq
      refine (mul_le_mul_of_nonneg_right hbq (by positivity)).trans (le_of_eq_of_le ?_
        (hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le)))
      rw [mul_assoc, ← Real.rpow_add' measureReal_nonneg (by simp [hn0.ne']), add_sub_cancel]
  have hab := h.memLp_energyIntegrand_zero_drift ha aestronglyMeasurable_zero (gamma := 0)
    fun x _ ↦ by simp
  refine hbound hk hOmega h ha hc hc_bound hc_nonneg
    (MemLp.of_bound hb (max beta 0) hb_ae) hsmall' hg hF (fun v hv => ?_) hboundary
  rw [← energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner hab
    (memLp_top_of_bound hb _ hb_ae) (memLp_top_of_bound hc _ hc_ae)]
  exact hu v hv

end TauCeti.PDE
