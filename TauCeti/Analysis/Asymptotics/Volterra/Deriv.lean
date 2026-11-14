/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Asymptotics.Volterra.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Order.OrderClosed
import TauCeti.MeasureTheory.Integral.Bochner.Tail

/-!
# Differentiation and derivative bounds for Volterra integral equations

Let `s ⊆ ℝ` be open, let `K : ℝ → ℝ → 𝕜` be continuous up to the diagonal
`{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2}` with `K x x = 0` for all `x ∈ s`, and suppose `x ↦ K x v` has
derivative `K₁ x v` for `x < v` in `s` bounded by `‖K₁ x v‖ ≤ P₁ x * Q v` with `P₁` continuous on
`s`. Then every continuous `O(P)` solution `h` of the Volterra integral equation

  `h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v)`

is differentiable on `s` with

  `deriv h x = ∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)`

and satisfies `‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` for all `x ∈ s`. Joint continuity of `K₁` is
not needed for differentiability or for the derivative bound; when `K₁` is also continuous on the
strict upper triangle `{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}`, `h` is `C¹` on `s`. When `P` is a
nonnegative constant `P₀` and `‖J v‖ ≤ ‖ψ v‖` on `s`, the sharper derivative bound
`P₀ * ‖deriv h x‖ ≤ P₁ x * (exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1)` holds.

## Main statements

* `TauCeti.hasDerivAt_volterra_solution_on` and `TauCeti.hasDerivAt_volterra_solution`:
  differentiability of Volterra solutions on an open set `s` and on `(a, ∞)`.
* `TauCeti.contDiffOn_volterra_solution_on` and `TauCeti.contDiffOn_volterra_solution`: `C¹`
  regularity when `K₁` is continuous on the strict upper triangle.
* `TauCeti.norm_deriv_volterra_solution_le_on` and `TauCeti.norm_deriv_volterra_solution_le`:
  the `P₁ Φ exp Ψ` derivative bound.
* `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on` and
  `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one`: sharper `exp (P₀ Φ) - 1` derivative
  bound when `P = P₀ ≥ 0` is constant and `‖J‖ ≤ ‖ψ‖`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted A K Peters,
  1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §§2.7–2.8, <https://dlmf.nist.gov/2.7>.
-/

public section

open MeasureTheory Filter Set Asymptotics Function
open scoped Topology

namespace TauCeti

section ParametricDeriv

/-- Strong measurability of `v ↦ K₁ x₀ v` on `s ∩ Ioi x₀`, requiring only joint continuity of `K`
on the strict upper triangle and pointwise differentiability of `x ↦ K x v` (not joint continuity
of `K₁`). -/
private lemma aestronglyMeasurable_kernel_deriv {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {s : Set ℝ} (hs_open : IsOpen s) {K K₁ : ℝ → ℝ → 𝕜}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    AEStronglyMeasurable (K₁ x₀) (volume.restrict (s ∩ Ioi x₀)) := by
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.1 hs_open x₀ hx₀
  let δn : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 2)
  have hδn_pos : ∀ n, 0 < δn n := fun n ↦ div_pos hδ_pos (by positivity)
  have hδn_lt : ∀ n, δn n < δ := fun n ↦
    div_lt_self hδ_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let tn : ℕ → ℝ → ℝ := fun n v ↦ min ((v + x₀) / 2) (x₀ + δn n)
  let fn : ℕ → ℝ → 𝕜 := fun n v ↦ (tn n v - x₀)⁻¹ • (K (tn n v) v - K x₀ v)
  have htn_mem : ∀ n, ∀ v ∈ s ∩ Ioi x₀,
      tn n v ∈ s ∧ x₀ < tn n v ∧ tn n v < v := fun n v hv ↦ by
    have hxv : x₀ < v := hv.2
    have hgt : x₀ < tn n v := lt_min (by linarith) (lt_add_of_pos_right x₀ (hδn_pos n))
    have hdist : dist (tn n v) x₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hgt)]
      linarith [min_le_right ((v + x₀) / 2) (x₀ + δn n), hδn_lt n]
    exact ⟨hδ_sub hdist, hgt, (min_le_left _ _).trans_lt (by linarith)⟩
  have hfn_meas : ∀ n, AEStronglyMeasurable (fn n) (volume.restrict (s ∩ Ioi x₀)) := fun n ↦ by
    have htn_cont : Continuous fun v ↦ tn n v :=
      ((continuous_id.add continuous_const).div_const 2).min continuous_const
    have hK₁_cont : ContinuousOn (fun v ↦ K (tn n v) v) (s ∩ Ioi x₀) :=
      ContinuousOn.comp hK (htn_cont.prodMk continuous_id).continuousOn
        fun v hv ↦ ⟨(htn_mem n v hv).1, hv.1, (htn_mem n v hv).2.2⟩
    have hK₀_cont : ContinuousOn (fun v ↦ K x₀ v) (s ∩ Ioi x₀) :=
      ContinuousOn.comp (g := uncurry K) (f := fun v ↦ (x₀, v)) hK
        (continuousOn_const.prodMk continuousOn_id) fun _ hv ↦ ⟨hx₀, hv.1, hv.2⟩
    have hinv_cont : ContinuousOn (fun v ↦ (tn n v - x₀)⁻¹) (s ∩ Ioi x₀) :=
      (htn_cont.sub continuous_const).continuousOn.inv₀
        fun v hv ↦ sub_ne_zero.2 (htn_mem n v hv).2.1.ne'
    exact (hinv_cont.smul (hK₁_cont.sub hK₀_cont)).aestronglyMeasurable
      (hs_open.measurableSet.inter measurableSet_Ioi)
  refine aestronglyMeasurable_of_tendsto_ae atTop hfn_meas
    (ae_restrict_of_forall_mem (hs_open.measurableSet.inter measurableSet_Ioi) fun v hv ↦ ?_)
  have hxv : x₀ < v := hv.2
  have hδn_tendsto : Tendsto δn atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds))
      (Eventually.of_forall hδn_pos)
  refine (((hKderiv x₀ hx₀ v hv.1 hxv).tendsto_slope_zero_right).comp hδn_tendsto).congr' ?_
  filter_upwards [(tendsto_nhds_of_tendsto_nhdsWithin hδn_tendsto).eventually
    (Iic_mem_nhds (half_pos (sub_pos.2 hxv)))] with n hn
  have : δn n ≤ (v - x₀) / 2 := hn
  have htn_eq : tn n v = x₀ + δn n := min_eq_right (by linarith)
  simp [fn, htn_eq]

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-- Lipschitz bound on `Icc α β ⊆ s` for the truncated integrand
`x ↦ if x < v then K x v • g v else 0` when `K v v = 0` and `‖K₁ x v‖ ≤ M * |Q v|`. -/
private lemma lipschitzOnWith_truncated_kernel_smul {s : Set ℝ} {α β M : ℝ}
    (hIcc : Icc α β ⊆ s) (hM0 : 0 ≤ M) {K K₁ : ℝ → ℝ → 𝕜} {Q : ℝ → ℝ} {g : ℝ → E}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hK₁le : ∀ x ∈ Icc α β, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ M * |Q v|)
    {v : ℝ} (hv : v ∈ s) :
    LipschitzOnWith (Real.nnabs (M * |Q v| * ‖g v‖))
      (fun x ↦ if x < v then K x v • g v else 0) (Icc α β) := by
  set F : ℝ → E := fun x ↦ if x < v then K x v • g v else 0
  set L : ℝ := M * |Q v| * ‖g v‖
  have hL0 : 0 ≤ L := by positivity
  have hF_cont : ContinuousOn F (Icc α β) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc α β).domRestrict F =
        fun x : Icc α β ↦ if v ≤ (x : ℝ) then (0 : E) else K (x : ℝ) v • g v := by
      ext x; simp only [domRestrict_apply, F, ← not_le]; split_ifs <;> rfl
    rw [hEq]
    refine continuous_if_le continuous_const continuous_subtype_val continuousOn_const
      ((ContinuousOn.comp (g := uncurry K) (f := fun x : Icc α β ↦ ((x : ℝ), v))
        (s := {x : Icc α β | (x : ℝ) ≤ v}) hK
        (continuous_subtype_val.prodMk continuous_const).continuousOn
        fun x hx ↦ ⟨hIcc x.2, hv, hx⟩).smul continuousOn_const) fun x hx ↦ ?_
    rw [← hx, hKdiag v hv, zero_smul]
  have hF_rderiv : ∀ x ∈ Icc α β,
      HasDerivWithinAt F (if x < v then K₁ x v • g v else 0) (Ici x) x := fun x hx ↦ by
    split_ifs with hxv
    · refine (((hKderiv x (hIcc hx) v hv hxv).smul_const (g v)).hasDerivWithinAt
        (s := Ici x)).congr_of_eventuallyEq ?_ (by simp [F, hxv])
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxv)] with y hy
      simp [F, mem_Iio.1 hy]
    · refine (hasDerivWithinAt_const x (Ici x) (0 : E)).congr (fun y hy ↦ ?_) (by simp [F, hxv])
      simp [F, not_lt.2 ((not_lt.1 hxv).trans (mem_Ici.1 hy))]
  have hF'_le : ∀ x ∈ Icc α β, ‖if x < v then K₁ x v • g v else 0‖ ≤ L := fun x hx ↦ by
    split_ifs with hxv
    · rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hK₁le x hx v hv hxv) (norm_nonneg _)
    · simpa using hL0
  have hseg : ∀ {x y}, x ∈ Icc α β → y ∈ Icc α β → x ≤ y → ‖F y - F x‖ ≤ L * (y - x) :=
    fun {x y} hx hy hxy ↦
      norm_image_sub_le_of_norm_deriv_right_le_segment
        (hF_cont.mono (Icc_subset_Icc hx.1 hy.2))
        (fun z hz ↦ hF_rderiv z ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩)
        (fun z hz ↦ hF'_le z ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩)
        y ⟨hxy, le_rfl⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm, Real.coe_nnabs, abs_of_nonneg hL0]
  rcases le_total x y with hxy | hyx
  · rw [norm_sub_rev, norm_sub_rev x y, Real.norm_of_nonneg (sub_nonneg.2 hxy)]
    exact hseg hx hy hxy
  · rw [Real.norm_of_nonneg (sub_nonneg.2 hyx)]
    exact hseg hy hx hyx

/-- Almost-everywhere Lipschitz domination on `Icc α β ⊆ s` for the indicator integrand
`(Ioi x).indicator (fun v ↦ K x v • g v) v`. -/
private lemma ae_lipschitzOnWith_indicator_kernel_smul {s : Set ℝ} (hs : MeasurableSet s)
    {α β M : ℝ} (hIcc : Icc α β ⊆ s) (hα_s : α ∈ s)
    {K K₁ : ℝ → ℝ → 𝕜} {g : ℝ → E} {P₁ Q : ℝ → ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hM : ∀ x ∈ Icc α β, ‖P₁ x‖ ≤ M)
    (B : ℝ → ℝ → ℝ) (hB_le : ∀ u ∈ s, ∀ v ∈ s ∩ Ioi u, |Q v| * ‖g v‖ ≤ B u v) :
    ∀ᵐ v ∂volume.restrict s,
      LipschitzOnWith (Real.nnabs ((Ioi α).indicator (fun u ↦ max M 0 * B α u) v))
        (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • g u) v) (Icc α β) := by
  set M' := max M 0
  set bound : ℝ → ℝ := (Ioi α).indicator fun u ↦ M' * B α u
  refine ae_restrict_of_forall_mem hs fun v hv ↦ ?_
  by_cases hαv : α < v
  · have hlip := lipschitzOnWith_truncated_kernel_smul hIcc (le_max_right M 0) hK hKdiag hKderiv
      (g := g) (fun x hx u hu hxu ↦ by
        have hP₁x : |P₁ x| ≤ M' := by
          rw [← Real.norm_eq_abs]; exact (hM x hx).trans (le_max_left M 0)
        exact (hK₁le x (hIcc hx) u hu hxu).trans
          (((le_abs_self _).trans_eq (abs_mul _ _)).trans
            (mul_le_mul_of_nonneg_right hP₁x (abs_nonneg _)))) hv
    have hind : (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • g u) v) =
        fun x ↦ if x < v then K x v • g v else 0 := by
      ext x; simp only [indicator, mem_Ioi]
    rw [hind]
    refine hlip.weaken ?_
    rw [← NNReal.coe_le_coe, Real.coe_nnabs, Real.coe_nnabs]
    have hle : M' * |Q v| * ‖g v‖ ≤ bound v := by
      simp only [bound, mem_Ioi.2 hαv, indicator_of_mem, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB_le α hα_s v ⟨hv, hαv⟩) (le_max_right M 0)
    have h0 : 0 ≤ M' * |Q v| * ‖g v‖ := by positivity
    rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans hle)]
    exact hle
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hnotx : v ∉ Ioi x := not_lt.2 ((not_lt.1 hαv).trans hx.1)
    have hnoty : v ∉ Ioi y := not_lt.2 ((not_lt.1 hαv).trans hy.1)
    simp only [indicator_of_notMem hnotx, indicator_of_notMem hnoty, dist_self]
    positivity

private lemma ae_hasDerivAt_indicator_kernel_smul {s : Set ℝ} (hs : MeasurableSet s)
    {K K₁ : ℝ → ℝ → 𝕜} {g : ℝ → E}
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    ∀ᵐ v ∂volume.restrict s,
      HasDerivAt (fun x ↦ (Ioi x).indicator (fun u ↦ K x u • g u) v)
        ((Ioi x₀).indicator (fun u ↦ K₁ x₀ u • g u) v) x₀ := by
  refine ((ae_restrict_of_ae (Measure.ae_ne volume x₀)).and (ae_restrict_mem hs)).mono
    fun v ⟨hne, hv⟩ ↦ ?_
  rcases lt_or_gt_of_ne hne with hvx₀ | hx₀v
  · simp only [mem_Ioi, not_lt.2 hvx₀.le, not_false_eq_true, indicator_of_notMem]
    refine (hasDerivAt_const x₀ (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hvx₀] with x hx
    simp [not_lt.2 (mem_Ioi.1 hx).le]
  · simp only [mem_Ioi.2 hx₀v, indicator_of_mem]
    refine ((hKderiv x₀ hx₀ v hv hx₀v).smul_const (g v)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx₀v] with x hx
    simp [mem_Ioi.2 (mem_Iio.1 hx)]

/-- Differentiation under the Volterra integral `x ↦ ∫ v in s ∩ Ioi x, K x v • g v` at `x₀ ∈ s`
whenever `|Q| * ‖g‖` is dominated by an integrable tail majorant `B` on each `s ∩ Ioi α`. -/
private lemma hasDerivAt_setIntegral_Ioi_smul_of_majorant {s : Set ℝ} (hs_open : IsOpen s)
    {K K₁ : ℝ → ℝ → 𝕜} {g : ℝ → E} {P₁ Q : ℝ → ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hg_cont : ContinuousOn g s) (hP₁ : ContinuousOn P₁ s)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s)
    (hg_int₀ : IntegrableOn (fun v ↦ K x₀ v • g v) (s ∩ Ioi x₀))
    (B : ℝ → ℝ → ℝ) (hB_int : ∀ α ∈ s, IntegrableOn (B α) (s ∩ Ioi α))
    (hB_le : ∀ α ∈ s, ∀ v ∈ s ∩ Ioi α, |Q v| * ‖g v‖ ≤ B α v) :
    IntegrableOn (fun v ↦ K₁ x₀ v • g v) (s ∩ Ioi x₀) ∧
      HasDerivAt (fun x ↦ ∫ v in s ∩ Ioi x, K x v • g v)
        (∫ v in s ∩ Ioi x₀, K₁ x₀ v • g v) x₀ := by
  have hs : MeasurableSet s := hs_open.measurableSet
  have hK_lt : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  let F : ℝ → ℝ → E := fun x v ↦ (Ioi x).indicator (fun u ↦ K x u • g u) v
  let F' : ℝ → E := (Ioi x₀).indicator fun v ↦ K₁ x₀ v • g v
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.1 hs_open x₀ hx₀
  set α := x₀ - ε / 2 with _
  set β := x₀ + ε / 2 with _
  have hIcc : Icc α β ⊆ s := fun x hx ↦ hε_sub <| by
    have hx1 : α ≤ x := hx.1; have hx2 : x ≤ β := hx.2
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  have hα_s : α ∈ s := hIcc ⟨le_rfl, by linarith⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hIcc)
  have hbound_int : Integrable ((Ioi α).indicator fun v ↦ max M 0 * B α v) (volume.restrict s) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm]
    exact (hB_int α hα_s).const_mul (max M 0)
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict s) := by
    filter_upwards [hs_open.mem_nhds hx₀] with x hx
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm]
    exact aestronglyMeasurable_volterra_smul hs hK_lt hg_cont hx
  have hF_int : Integrable (F x₀) (volume.restrict s) := by
    rwa [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm]
  have hF'_meas : AEStronglyMeasurable F' (volume.restrict s) := by
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm]
    exact (aestronglyMeasurable_kernel_deriv hs_open hK_lt hKderiv hx₀).smul
      ((hg_cont.mono inter_subset_left).aestronglyMeasurable (hs.inter measurableSet_Ioi))
  obtain ⟨hF'_int, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (Icc_mem_nhds (by linarith) (by linarith)) hF_meas hF_int hF'_meas
    (ae_lipschitzOnWith_indicator_kernel_smul hs hIcc hα_s hK hKdiag hKderiv hK₁le hM B hB_le)
    hbound_int (ae_hasDerivAt_indicator_kernel_smul hs hKderiv hx₀)
  rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi, inter_comm] at hF'_int
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_comm] at hmain
  refine ⟨hF'_int, hmain.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)⟩
  dsimp only [F]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_comm]

end ParametricDeriv

section DerivativeTheorems

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {s : Set ℝ} {K K₁ : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

/-- **Differentiation of Volterra solutions.** On an open set `s`, if `K` is continuous up to the
diagonal `{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2}` with `K x x = 0`, and `x ↦ K x v` has derivative
`K₁ x v` for `x < v` in `s` bounded by `‖K₁ x v‖ ≤ P₁ x * Q v` with `P₁` continuous on `s`, then
every continuous `O(P)` solution `h` satisfies
`HasDerivAt h (∫ v in s ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀` at every `x₀ ∈ s`. -/
theorem hasDerivAt_volterra_solution_on (hs_open : IsOpen s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP₁ : ContinuousOn P₁ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] P) {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    HasDerivAt h (∫ v in s ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀ := by
  classical
  have hs : MeasurableSet s := hs_open.measurableSet
  have hK_lt : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  choose C hC using fun α : s ↦ (hh_O α.1 α.2).bound
  have hmain := (hasDerivAt_setIntegral_Ioi_smul_of_majorant hs_open hK hKdiag hKderiv
    (hJ.add (hψ.smul hh_cont)) hP₁ hK₁le hx₀
    (integrableOn_volterra_of_isBigO_on hs hK_lt hJ hψ hKle hΦ hΨ hh_cont hx₀ (hh_O x₀ hx₀))
    (fun α v ↦ if hα : α ∈ s then
      |Q v| * ‖J v‖ + max (C ⟨α, hα⟩) 0 * (|P v| * |Q v| * ‖ψ v‖) else 0)
    (fun α hα ↦ by
      simp only [hα, ↓reduceDIte]
      have hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi α) := by
        rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΦ α hα).norm
      have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi α) := by
        rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΨ α hα).norm
      exact hΦ'.add (hΨ'.const_mul _))
    fun α hα v hv ↦ by
      simp only [hα, ↓reduceDIte]
      have hhv : ‖h v‖ ≤ max (C ⟨α, hα⟩) 0 * |P v| := by
        simpa [Real.norm_eq_abs] using (eventually_principal.1 (hC ⟨α, hα⟩) v hv).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      calc |Q v| * ‖(J + ψ • h) v‖
          ≤ |Q v| * (‖J v‖ + ‖ψ v‖ * (max (C ⟨α, hα⟩) 0 * |P v|)) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (abs_nonneg _)
            rw [Pi.smul_apply', norm_smul]; gcongr
        _ = |Q v| * ‖J v‖ + max (C ⟨α, hα⟩) 0 * (|P v| * |Q v| * ‖ψ v‖) := by ring).2
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hs_open.mem_nhds hx₀] with x hx
  exact hh_eq x hx

/-- **`C¹` regularity of Volterra solutions.** Under the hypotheses of
`hasDerivAt_volterra_solution_on`, if `K₁` is also continuous on
`{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2}`, then `ContDiffOn ℝ 1 h s`. -/
theorem contDiffOn_volterra_solution_on (hs_open : IsOpen s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hK₁ : ContinuousOn (uncurry K₁) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP₁ : ContinuousOn P₁ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] P) :
    ContDiffOn ℝ 1 h s := by
  classical
  have hd : ∀ x ∈ s, HasDerivAt h (∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) x :=
    fun x hx ↦ hasDerivAt_volterra_solution_on hs_open hK hKdiag hKderiv hJ hψ hP₁ hKle hK₁le
      hΦ hΨ hh_cont hh_eq hh_O hx
  choose C hC using fun x : s ↦ (hh_O x.1 x.2).bound
  have hd_cont : ContinuousOn (fun x ↦ ∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) s := by
    refine continuousOn_volterra_integral hs_open.measurableSet hK₁
      (hJ.add (hψ.smul hh_cont)) hP₁
      (fun u v ↦ if hu : u ∈ s then
        |Q v| * ‖J v‖ + max (C ⟨u, hu⟩) 0 * (|P v| * |Q v| * ‖ψ v‖) else 0)
      (fun u hu ↦ by
        simp only [hu, ↓reduceDIte]
        have hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi u) := by
          rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΦ u hu).norm
        have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi u) := by
          rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΨ u hu).norm
        exact hΦ'.add (hΨ'.const_mul _))
      fun u hu x hx hxge v hv ↦ ?_
    simp only [hu, ↓reduceDIte, norm_smul]
    have hhv : ‖h v‖ ≤ max (C ⟨u, hu⟩) 0 * |P v| := by
      have hv_mem : v ∈ s ∩ Ioi u := ⟨hv.1, hxge.trans_lt hv.2⟩
      simpa [Real.norm_eq_abs] using (eventually_principal.1 (hC ⟨u, hu⟩) v hv_mem).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    calc ‖K₁ x v‖ * ‖(J + ψ • h) v‖
        ≤ (|P₁ x| * |Q v|) * (‖J v‖ + ‖ψ v‖ * (max (C ⟨u, hu⟩) 0 * |P v|)) := by
          refine mul_le_mul
            ((hK₁le x hx v hv.1 hv.2).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
            ((norm_add_le _ _).trans ?_) (norm_nonneg _) (by positivity)
          rw [Pi.smul_apply', norm_smul]; gcongr
      _ = |P₁ x| * (|Q v| * ‖J v‖ + max (C ⟨u, hu⟩) 0 * (|P v| * |Q v| * ‖ψ v‖)) := by ring
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := rfl
  rw [h1, contDiffOn_succ_iff_deriv_of_isOpen hs_open]
  refine ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hd_cont.congr fun x hx ↦ (hd x hx).deriv

omit [IsScalarTower ℝ 𝕜 E] in
/-- Norm estimate for the differentiated Volterra integral
`∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)` when `h` obeys the `|P| Φ' exp Ψ'` bound. -/
private lemma norm_setIntegral_kernel_deriv_le (hs_open : IsOpen s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2})
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {x : ℝ} (hx : x ∈ s)
    (hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi x))
    (hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_le : ∀ v ∈ s ∩ Ioi x,
      ‖h v‖ ≤ |P v| * (∫ u in s ∩ Ioi v, |Q u| * ‖J u‖) *
        Real.exp (∫ u in s ∩ Ioi v, |P u| * |Q u| * ‖ψ u‖)) :
    ‖∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)‖ ≤
      |P₁ x| * (∫ v in s ∩ Ioi x, |Q v| * ‖J v‖) *
        Real.exp (∫ v in s ∩ Ioi x, |P v| * |Q v| * ‖ψ v‖) := by
  have ht : MeasurableSet (s ∩ Ioi x) := hs_open.measurableSet.inter measurableSet_Ioi
  set a : ℝ → ℝ := fun v ↦ |P v| * |Q v| * ‖ψ v‖
  set Φ : ℝ → ℝ := fun y ↦ ∫ v in s ∩ Ioi y, |Q v| * ‖J v‖
  set Ψ : ℝ → ℝ := fun y ↦ ∫ v in s ∩ Ioi y, a v
  have hEq_exp : EqOn (fun v ↦ a v * Real.exp (∫ u in (s ∩ Ioi x) ∩ Ioi v, a u))
      (fun v ↦ a v * Real.exp (Ψ v)) (s ∩ Ioi x) := fun v hv ↦ by
    dsimp only; rw [inter_assoc, Ioi_inter_Ioi, max_eq_right hv.2.le]
  have ha_exp_int : IntegrableOn (fun v ↦ a v * Real.exp (Ψ v)) (s ∩ Ioi x) :=
    hΨ'.mul_exp_setIntegral_Ioi.congr_fun hEq_exp ht
  have hpt : ∀ v ∈ s ∩ Ioi x, ‖K₁ x v • (J v + ψ v • h v)‖ ≤
      |P₁ x| * (|Q v| * ‖J v‖ + Φ x * (a v * Real.exp (Ψ v))) := fun v hv ↦ by
    have hΦ_mono : Φ v ≤ Φ x :=
      setIntegral_mono_set hΦ' (ae_of_all _ fun _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (Eventually.of_forall (inter_subset_inter_right s (Ioi_subset_Ioi hv.2.le)))
    rw [norm_smul]
    calc ‖K₁ x v‖ * ‖J v + ψ v • h v‖
        ≤ (|P₁ x| * |Q v|) * (‖J v‖ + ‖ψ v‖ * (|P v| * Φ x * Real.exp (Ψ v))) := by
          refine mul_le_mul
            ((hK₁le x hx v hv.1 hv.2).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
            ((norm_add_le _ _).trans ?_) (norm_nonneg _) (by positivity)
          rw [norm_smul]
          refine add_le_add le_rfl
            (mul_le_mul_of_nonneg_left ((hh_le v hv).trans ?_) (norm_nonneg _))
          gcongr
      _ = |P₁ x| * (|Q v| * ‖J v‖ + Φ x * (a v * Real.exp (Ψ v))) := by dsimp only [a]; ring
  have hmaj_int : IntegrableOn
      (fun v ↦ |P₁ x| * (|Q v| * ‖J v‖ + Φ x * (a v * Real.exp (Ψ v)))) (s ∩ Ioi x) :=
    (hΦ'.add (ha_exp_int.const_mul (Φ x))).const_mul |P₁ x|
  have hK₁g_int : IntegrableOn (fun v ↦ K₁ x v • (J v + ψ v • h v)) (s ∩ Ioi x) :=
    hmaj_int.mono' ((aestronglyMeasurable_kernel_deriv hs_open hK hKderiv hx).smul
      (((hJ.add (hψ.smul hh_cont)).mono inter_subset_left).aestronglyMeasurable ht))
      (ae_restrict_of_forall_mem ht hpt)
  calc ‖∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)‖
       ≤ ∫ v in s ∩ Ioi x, |P₁ x| * (|Q v| * ‖J v‖ + Φ x * (a v * Real.exp (Ψ v))) :=
        (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hK₁g_int.norm hmaj_int ht hpt)
    _ = |P₁ x| * Φ x * Real.exp (Ψ x) := by
        rw [integral_const_mul, integral_add hΦ' (ha_exp_int.const_mul _),
          integral_const_mul, setIntegral_congr_fun ht hEq_exp.symm,
          hΨ'.setIntegral_mul_exp_setIntegral_Ioi]
        dsimp only [Φ, Ψ]; ring

/-- **Volterra derivative bound.** Under the hypotheses of `hasDerivAt_volterra_solution_on` (plus
`ContinuousOn P s`), every continuous `O(P)` solution satisfies
`‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` for all `x ∈ s`. -/
theorem norm_deriv_volterra_solution_le_on (hs_open : IsOpen s)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s)
    (hP : ContinuousOn P s) (hP₁ : ContinuousOn P₁ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖J v‖) (s ∩ Ioi x))
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] P) {x : ℝ} (hx : x ∈ s) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in s ∩ Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in s ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  have hs : MeasurableSet s := hs_open.measurableSet
  have hK_lt : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  have hPQ : ∀ y ∈ s, ∀ v ∈ s, y < v → 0 ≤ P y * Q v :=
    fun y hy v hv hyv ↦ (norm_nonneg _).trans (hKle y hy v hv hyv)
  have hΦ' : IntegrableOn (fun v ↦ |Q v| * ‖J v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΦ x hx).norm
  have hΨ' : IntegrableOn (fun v ↦ |P v| * |Q v| * ‖ψ v‖) (s ∩ Ioi x) := by
    rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΨ x hx).norm
  rw [(hasDerivAt_volterra_solution_on hs_open hK hKdiag hKderiv hJ hψ hP₁ hKle hK₁le
    hΦ hΨ hh_cont hh_eq hh_O hx).deriv,
    ← volterra_bound_abs_eq hs hPQ fun v hv ↦ (norm_nonneg _).trans (hK₁le x hx v hv.1 hv.2)]
  exact norm_setIntegral_kernel_deriv_le hs_open hK_lt hKderiv hJ hψ hK₁le hx hΦ' hΨ' hh_cont
    fun v hv ↦ by
      rw [volterra_bound_abs_eq hs hPQ fun u hu ↦ hPQ v hv.1 u hu.1 hu.2]
      exact norm_volterra_solution_le_on hs hK_lt hJ hψ hP hKle hΦ hΨ hh_cont hh_eq hh_O hv.1

/-- Integrability of `K₁ x · • (J + ψ • h)` and derivative formula for `h` in the constant-`P₀`,
`‖J‖ ≤ ‖ψ‖` regime (without assuming separate integrability of `Q * ‖J‖`). -/
private lemma integrableOn_and_deriv_of_const_le (hs_open : IsOpen s) {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP₁ : ContinuousOn P₁ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hJψ : ∀ v ∈ s, ‖J v‖ ≤ ‖ψ v‖)
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] (1 : ℝ → ℝ)) {x : ℝ} (hx : x ∈ s) :
    IntegrableOn (fun v ↦ K₁ x v • (J v + ψ v • h v)) (s ∩ Ioi x) ∧
      deriv h x = ∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v) := by
  classical
  have hs : MeasurableSet s := hs_open.measurableSet
  have hK_lt : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  choose C hC using fun α : s ↦ (hh_O α.1 α.2).bound
  have hΨ_abs : ∀ α ∈ s, IntegrableOn (fun v ↦ |Q v| * ‖ψ v‖) (s ∩ Ioi α) := fun α hα ↦ by
    rw [IntegrableOn]; simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (hΨ α hα).norm
  have hg_int₀ : IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (s ∩ Ioi x) :=
    ((hΨ_abs x hx).const_mul (|P₀| * (1 + max (C ⟨x, hx⟩) 0))).mono'
      (aestronglyMeasurable_volterra_smul hs hK_lt (hJ.add (hψ.smul hh_cont)) hx)
      (ae_restrict_of_forall_mem (hs.inter measurableSet_Ioi) fun v hv ↦ by
        have hhv : ‖h v‖ ≤ max (C ⟨x, hx⟩) 0 :=
          ((eventually_principal.1 (hC ⟨x, hx⟩) v hv).trans_eq (by simp)).trans (le_max_left _ _)
        rw [norm_smul]
        calc ‖K x v‖ * ‖J v + ψ v • h v‖
            ≤ (|P₀| * |Q v|) * (‖ψ v‖ + ‖ψ v‖ * max (C ⟨x, hx⟩) 0) :=
              mul_le_mul ((hKle x hx v hv.1 hv.2).trans ((le_abs_self _).trans_eq (abs_mul _ _)))
                ((norm_add_le _ _).trans (add_le_add (hJψ v hv.1) (by rw [norm_smul]; gcongr)))
                (norm_nonneg _) (by positivity)
          _ = (|P₀| * (1 + max (C ⟨x, hx⟩) 0)) * (|Q v| * ‖ψ v‖) := by ring)
  obtain ⟨hK₁g_int, hd0⟩ := hasDerivAt_setIntegral_Ioi_smul_of_majorant hs_open hK hKdiag hKderiv
    (hJ.add (hψ.smul hh_cont)) hP₁ hK₁le hx hg_int₀
    (fun α v ↦ if hα : α ∈ s then (1 + max (C ⟨α, hα⟩) 0) * (|Q v| * ‖ψ v‖) else 0)
    (fun α hα ↦ by simp only [hα, ↓reduceDIte]; exact (hΨ_abs α hα).const_mul _)
    fun α hα v hv ↦ by
      simp only [hα, ↓reduceDIte]
      have hhv : ‖h v‖ ≤ max (C ⟨α, hα⟩) 0 :=
        ((eventually_principal.1 (hC ⟨α, hα⟩) v hv).trans_eq (by simp)).trans (le_max_left _ _)
      calc |Q v| * ‖(J + ψ • h) v‖
          ≤ |Q v| * (‖ψ v‖ + ‖ψ v‖ * max (C ⟨α, hα⟩) 0) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (abs_nonneg _)
            exact add_le_add (hJψ v hv.1) (by rw [Pi.smul_apply', norm_smul]; gcongr)
        _ = (1 + max (C ⟨α, hα⟩) 0) * (|Q v| * ‖ψ v‖) := by ring
  refine ⟨hK₁g_int, (hd0.congr_of_eventuallyEq ?_).deriv⟩
  filter_upwards [hs_open.mem_nhds hx] with y hy
  exact hh_eq y hy

/-- **Sharper Volterra derivative bound for constant `P₀ ≥ 0` and `‖J‖ ≤ ‖ψ‖`.** Under the
hypotheses of `hasDerivAt_volterra_solution_on` with `P = fun _ ↦ P₀` (`0 ≤ P₀`) and
`‖J v‖ ≤ ‖ψ v‖` on `s`, every continuous solution bounded on tails satisfies
`P₀ * ‖deriv h x‖ ≤ P₁ x * (exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one_on (hs_open : IsOpen s) {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ s, K x x = 0)
    (hKderiv : ∀ x ∈ s, ∀ v ∈ s, x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J s) (hψ : ContinuousOn ψ s) (hP₀ : 0 ≤ P₀) (hP₁ : ContinuousOn P₁ s)
    (hKle : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁le : ∀ x ∈ s, ∀ v ∈ s, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hJψ : ∀ v ∈ s, ‖J v‖ ≤ ‖ψ v‖)
    (hΨ : ∀ x ∈ s, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (s ∩ Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h s)
    (hh_eq : ∀ x ∈ s, h x = ∫ v in s ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ s, h =O[𝓟 (s ∩ Ioi x)] (1 : ℝ → ℝ)) {x : ℝ} (hx : x ∈ s) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1) := by
  rcases eq_or_lt_of_le hP₀ with rfl | hP₀_pos; · simp
  have hs : MeasurableSet s := hs_open.measurableSet
  have ht : MeasurableSet (s ∩ Ioi x) := hs.inter measurableSet_Ioi
  have hK_lt : ContinuousOn (uncurry K) {p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2} :=
    hK.mono fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.le⟩
  have hQ0 : ∀ v ∈ s ∩ Ioi x, 0 ≤ Q v := fun v hv ↦
    nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (hKle x hx v hv.1 hv.2)) hP₀_pos
  obtain ⟨hK₁g_int, hd⟩ := integrableOn_and_deriv_of_const_le hs_open hK hKdiag hKderiv hJ hψ
    hP₁ hKle hK₁le hJψ hΨ hh_cont hh_eq hh_O hx
  by_cases hQ_all0 : ∀ v ∈ s ∩ Ioi x, Q v = 0
  · have hK₁0 : EqOn (fun v ↦ K₁ x v • (J v + ψ v • h v)) 0 (s ∩ Ioi x) := fun v hv ↦ by
      simp [norm_le_zero_iff.1 (by simpa [hQ_all0 v hv] using hK₁le x hx v hv.1 hv.2)]
    have hQ0' : EqOn (fun v ↦ Q v * ‖ψ v‖) 0 (s ∩ Ioi x) := fun v hv ↦ by simp [hQ_all0 v hv]
    rw [hd, setIntegral_congr_fun ht hK₁0, setIntegral_congr_fun ht hQ0']; simp
  · push Not at hQ_all0; obtain ⟨v₀, hv₀, hQv₀⟩ := hQ_all0
    have hP₁0 : 0 ≤ P₁ x := nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hK₁le x hx v₀ hv₀.1 hv₀.2))
      (lt_of_le_of_ne (hQ0 v₀ hv₀) (Ne.symm hQv₀))
    set a : ℝ → ℝ := fun v ↦ P₀ * (Q v * ‖ψ v‖)
    have ha_int : IntegrableOn a (s ∩ Ioi x) := (hΨ x hx).const_mul P₀
    have hEq_exp : EqOn (fun v ↦ a v * Real.exp (∫ u in (s ∩ Ioi x) ∩ Ioi v, a u))
        (fun v ↦ a v * Real.exp (P₀ * ∫ u in s ∩ Ioi v, Q u * ‖ψ u‖)) (s ∩ Ioi x) := fun v hv ↦ by
      dsimp only; rw [inter_assoc, Ioi_inter_Ioi, max_eq_right hv.2.le, integral_const_mul]
    have hpt : ∀ v ∈ s ∩ Ioi x, P₀ * ‖K₁ x v • (J v + ψ v • h v)‖ ≤
        P₁ x * (a v * Real.exp (P₀ * ∫ u in s ∩ Ioi v, Q u * ‖ψ u‖)) := fun v hv ↦ by
      have hhv := norm_volterra_solution_le_exp_sub_one_on hs hK_lt hJ hψ hKle hJψ hΨ hh_cont
        hh_eq hh_O hv.1
      rw [norm_smul]
      calc P₀ * (‖K₁ x v‖ * ‖J v + ψ v • h v‖)
          ≤ P₀ * ((P₁ x * Q v) * (‖ψ v‖ + ‖ψ v‖ *
              (Real.exp (P₀ * ∫ u in s ∩ Ioi v, Q u * ‖ψ u‖) - 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hK₁le x hx v hv.1 hv.2)
              ((norm_add_le _ _).trans (add_le_add (hJψ v hv.1) (by rw [norm_smul]; gcongr)))
              (norm_nonneg _) (mul_nonneg hP₁0 (hQ0 v hv))) hP₀
        _ = P₁ x * (a v * Real.exp (P₀ * ∫ u in s ∩ Ioi v, Q u * ‖ψ u‖)) := by dsimp only [a]; ring
    rw [hd]
    calc P₀ * ‖∫ v in s ∩ Ioi x, K₁ x v • (J v + ψ v • h v)‖
        ≤ ∫ v in s ∩ Ioi x, P₀ * ‖K₁ x v • (J v + ψ v • h v)‖ := by
          rw [integral_const_mul]; gcongr; exact norm_integral_le_integral_norm _
      _ ≤ ∫ v in s ∩ Ioi x, P₁ x * (a v * Real.exp (P₀ * ∫ u in s ∩ Ioi v, Q u * ‖ψ u‖)) :=
          setIntegral_mono_on (hK₁g_int.norm.const_mul P₀)
            ((ha_int.mul_exp_setIntegral_Ioi.congr_fun hEq_exp ht).const_mul (P₁ x)) ht hpt
      _ = P₁ x * (Real.exp (P₀ * ∫ v in s ∩ Ioi x, Q v * ‖ψ v‖) - 1) := by
          rw [integral_const_mul, setIntegral_congr_fun ht hEq_exp.symm,
            ha_int.setIntegral_mul_exp_setIntegral_Ioi, integral_const_mul]

end DerivativeTheorems

section Intervals

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {a : ℝ} {K K₁ : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

private lemma Ioi_inter_of_gt' {y : ℝ} (hy : y ∈ Ioi a) : Ioi a ∩ Ioi y = Ioi y :=
  inter_eq_right.2 (Ioi_subset_Ioi hy.le)

/-- **Differentiation of Volterra solutions on `(a, ∞)`.** -/
theorem hasDerivAt_volterra_solution (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP₁ : ContinuousOn P₁ (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x v, a < x → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] P) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioi a) :
    HasDerivAt h (∫ v in Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀ := by
  simpa only [Ioi_inter_of_gt' hx₀] using hasDerivAt_volterra_solution_on (s := Ioi a) isOpen_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag (fun y hy v _ hyv ↦ hKderiv y v hy hyv) hJ hψ hP₁
    (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy v _ hyv ↦ hK₁le y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΨ y hy) hh_cont
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_O y hy) hx₀

/-- **`C¹` regularity of Volterra solutions on `(a, ∞)`.** -/
theorem contDiffOn_volterra_solution (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 < p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hP₁ : ContinuousOn P₁ (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x v, a < x → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] P) :
    ContDiffOn ℝ 1 h (Ioi a) :=
  contDiffOn_volterra_solution_on (s := Ioi a) isOpen_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag
    (fun y hy v _ hyv ↦ hKderiv y v hy hyv) (hK₁.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hJ hψ hP₁
    (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy v _ hyv ↦ hK₁le y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΨ y hy) hh_cont
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_O y hy)

/-- **Volterra derivative bound on `(a, ∞)`.** -/
theorem norm_deriv_volterra_solution_le (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hP₁ : ContinuousOn P₁ (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P x * Q v)
    (hK₁le : ∀ x v, a < x → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  simpa only [Ioi_inter_of_gt' hx] using norm_deriv_volterra_solution_le_on (s := Ioi a) isOpen_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag (fun y hy v _ hyv ↦ hKderiv y v hy hyv) hJ hψ hP
    hP₁ (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy v _ hyv ↦ hK₁le y v hy hyv)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΦ y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΨ y hy) hh_cont
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_O y hy) hx

/-- **Sharper Volterra derivative bound on `(a, ∞)` for constant `P₀ ≥ 0` and `‖J‖ ≤ ‖ψ‖`.** -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one {P₀ : ℝ}
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0)
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (K · v) (K₁ x v) x)
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP₀ : 0 ≤ P₀) (hP₁ : ContinuousOn P₁ (Ioi a))
    (hKle : ∀ x v, a < x → x < v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁le : ∀ x v, a < x → x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh_cont : ContinuousOn h (Ioi a))
    (hh_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hh_O : ∀ x ∈ Ioi a, h =O[𝓟 (Ioi x)] (1 : ℝ → ℝ)) {x : ℝ} (hx : x ∈ Ioi a) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1) := by
  simpa only [Ioi_inter_of_gt' hx] using mul_norm_deriv_volterra_solution_le_exp_sub_one_on
    (s := Ioi a) isOpen_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag
    (fun y hy v _ hyv ↦ hKderiv y v hy hyv) hJ hψ hP₀ hP₁ (fun y hy v _ hyv ↦ hKle y v hy hyv)
    (fun y hy v _ hyv ↦ hK₁le y v hy hyv) hJψ (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hΨ y hy)
    hh_cont (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_eq y hy)
    (fun y hy ↦ (Ioi_inter_of_gt' hy).symm ▸ hh_O y hy) hx

/-- Sanity check on `(0, ∞)` for the non-zero kernel `K x v = v - x` (`K x x = 0`, `K₁ x v = -1`)
with `P = 1`, `Q = id`, and `P₁ = Inv.inv`. -/
example {ψ₀ : ℝ → ℝ} (hJ : ContinuousOn J (Ioi 0)) (hψ : ContinuousOn ψ₀ (Ioi 0))
    (hΦ : ∀ x ∈ Ioi (0 : ℝ), IntegrableOn (fun v ↦ v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi (0 : ℝ), IntegrableOn (fun v ↦ (1 : ℝ) * v * ‖ψ₀ v‖) (Ioi x)) :
    ∃ h : ℝ → E, ContDiffOn ℝ 1 h (Ioi 0) ∧
      (∀ x ∈ Ioi (0 : ℝ), h x = ∫ v in Ioi x, (v - x) • (J v + ψ₀ v • h v)) ∧
      ∀ x ∈ Ioi (0 : ℝ), HasDerivAt h (∫ v in Ioi x, (-1 : ℝ) • (J v + ψ₀ v • h v)) x := by
  have hK : Continuous (uncurry fun x v : ℝ ↦ v - x) := continuous_snd.sub continuous_fst
  have hKle : ∀ x v, 0 < x → x < v → ‖v - x‖ ≤ (1 : ℝ) * v := fun x v _ hxv ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.2 hxv)]; linarith
  have hK₁le : ∀ x v, 0 < x → x < v → ‖(-1 : ℝ)‖ ≤ x⁻¹ * v := fun x v hx hxv ↦ by
    rw [norm_neg, norm_one, inv_mul_eq_div, one_le_div hx]; exact hxv.le
  have hderiv : ∀ x v : ℝ, 0 < x → x < v → HasDerivAt (fun y ↦ v - y) (-1) x :=
    fun x v _ _ ↦ by simpa using (hasDerivAt_id x).const_sub v
  have hP₁ : ContinuousOn Inv.inv (Ioi (0 : ℝ)) := continuousOn_id.inv₀ fun _ hx ↦ ne_of_gt hx
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ := exists_volterra_solution hK.continuousOn hJ hψ
    continuousOn_const hKle hΦ hΨ
  have hh_O : ∀ x ∈ Ioi (0 : ℝ), h =O[𝓟 (Ioi x)] (1 : ℝ → ℝ) := fun x hx ↦
    (isBigO_of_norm_le_volterra_bound (fun _ _ hu huv ↦ by linarith) hΦ hΨ hh_le hx).mono
      (principal_mono.2 Ioi_subset_Ici_self)
  exact ⟨h, contDiffOn_volterra_solution hK.continuousOn (fun x _ ↦ sub_self x) hderiv
    continuousOn_const hJ hψ hP₁ hKle hK₁le hΦ hΨ hh_cont hh_eq hh_O, hh_eq,
    fun x hx ↦ hasDerivAt_volterra_solution hK.continuousOn (fun y _ ↦ sub_self y) hderiv
      hJ hψ hP₁ hKle hK₁le hΦ hΨ hh_cont hh_eq hh_O hx⟩

end Intervals

end TauCeti
