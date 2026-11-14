/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InwardSemiflow.Basic
public import TauCeti.Analysis.ODE.Regularity
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Analysis.ODE.Gronwall

/-!
# Smoothness of inward forward semiflows and inward deformations of convex sets

Mathlib's local flow regularity theorem (`ODE.exists_contDiffAt_localFlow`) differentiates the
fixed-point equation of an ODE on an open neighborhood, which is unavailable at `t = 0` or along
the boundary and corners of a closed convex set `C`.

When `X` is `C^m` (`1 ≤ m`, including `m = ∞`) on `U ∩ C` and strictly inward to the closed convex
set `C`, its maximal forward semiflow `TauCeti.forwardSemiflow X (U ∩ C)` constructed in
`TauCeti/Analysis/ODE/InwardSemiflow/Basic.lean` is nevertheless jointly `C^m` on the entire
maximal domain `forwardSemiflowDomain X (U ∩ C)` — including at `t = 0` and along `∂C`:

1. **Unique derivatives from strict inwardness.** Existence of a strictly inward vector at any
   point of `C` forces `(interior C).Nonempty`, so `V ∩ C` has unique derivatives for every open
   set `V` (`Convex.uniqueDiffOn_inter_of_mem_strictInwardCone`).
2. **Joint `C¹` differentiability via the Dyson variational propagator.** Along each local
   trajectory `t ↦ Φ t y₀`, the linear time-ordered exponential
   `A(y₀, t) = dysonSeriesLeft (s ↦ fderivWithin ℝ X (U ∩ C) (Φ s y₀)) t` solves the linearized
   variational equation. Combining the uniform convex Taylor bound
   (`Convex.exists_pos_norm_sub_fderivWithin_le_of_compact`) with integral Grönwall
   (`TauCeti.le_mul_exp_of_le_add_mul_integral`) shows that the joint Fréchet derivative of
   `uncurry Φ` within `Icc 0 τ ×ˢ (ball x₀ r ∩ C)` is `(dt, dy) ↦ dt • X (Φ t y) + A(y, t) dy` up
   to `t = 0` and `∂C`.
3. **Higher `C^m` smoothness via the variational system.** For `C^{k+2}` fields, the pair
   `(Φ t y, A(y, t))` is the forward trajectory starting at `(y, 1)` of the `C^{k+1}` strictly
   inward variational field `(q, L) ↦ (X q, fderivWithin ℝ X (U ∩ C) q ∘L L)` on
   `(U ×ˢ univ) ∩ (C ×ˢ univ)`. Induction on `k` upgrades local smoothness to every finite order,
   and cocycle propagation along `[0, T]` yields `ContDiffOn ℝ m` on the entire maximal domain
   `forwardSemiflowDomain X (U ∩ C)` (`TauCeti.contDiffOn_forwardSemiflow`) as well as the local
   `C^m` semiflow package around a single inward point (`Convex.exists_contDiffOn_inwardSemiflow`).
4. **`C^m` inward deformation.** When `forwardSemiflow X C` is globally forward complete on `C`,
   its time-`1` map `r := forwardSemiflow X C 1` and quadratically reparametrized homotopy
   `H (t, x) := forwardSemiflow X C ((1 - t) ^ 2) x` deform `C` into `interior C` through `C^m`
   maps while preserving `interior C` at every time (`Convex.exists_contDiffOn_inward_deformation`).

## Main results

* `Convex.uniqueDiffOn_inter_of_mem_strictInwardCone`: `V ∩ C` has unique derivatives whenever `C`
  is convex, `V` is open, and `C` admits a strictly inward vector.
* `TauCeti.contDiffOn_forwardSemiflow_time`: each individual trajectory of `forwardSemiflow` is
  `C^(m + 1)` in time on its maximal forward interval.
* `TauCeti.contDiffOn_forwardSemiflow`: joint `C^m` smoothness (`1 ≤ m`) of
  `uncurry (forwardSemiflow X (U ∩ C))` on `forwardSemiflowDomain X (U ∩ C)`.
* `Convex.exists_contDiffOn_inwardSemiflow`: local `C^m` forward semiflow on
  `Icc 0 τ ×ˢ (ball x₀ r ∩ C)` around a single point where `X x₀ ∈ strictInwardCone C x₀`.
* `TauCeti.contDiffOn_forwardSemiflow_Ici`: global `C^m` smoothness on `Ici 0 ×ˢ C` when every
  trajectory is forward complete.
* `Convex.exists_contDiffOn_inward_deformation`: `C^m` strong inward deformation of `C` into
  `interior C` preserving `interior C`.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X (variational
  equation and smooth dependence on initial conditions).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.25–9.26.
-/

public section

open Filter Function Metric Set intervalIntegral
open scoped ContDiff NNReal Topology

/-- If a convex set `C` admits a strictly inward vector at one of its points, then `V ∩ C` has
unique derivatives for every open set `V`. -/
theorem Convex.uniqueDiffOn_inter_of_mem_strictInwardCone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C V : Set E} (hC : Convex ℝ C) (hV : IsOpen V) {x v : E} (hx : x ∈ C)
    (hv : v ∈ TauCeti.strictInwardCone C x) :
    UniqueDiffOn ℝ (V ∩ C) := by
  obtain ⟨t, _, ht⟩ := (hC.mem_strictInwardCone_iff hx).mp hv
  rw [inter_comm]
  exact (uniqueDiffOn_convex hC ⟨_, ht⟩).inter hV

namespace TauCeti

section TimeRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a locally Lipschitz `C^m` field `X` (`m : ℕ∞`) on `S`, each individual trajectory of
`forwardSemiflow X S` is `C^(m + 1)` on its maximal forward interval. -/
theorem contDiffOn_forwardSemiflow_time {m : ℕ∞} {S : Set E} {X : E → E}
    (hX_lip : LocallyLipschitzOn S X) (hX : ContDiffOn ℝ m X S) (x : E) :
    ContDiffOn ℝ (m + 1) (fun t ↦ forwardSemiflow X S t x)
      (forwardSemiflowInterval X S x) := by
  intro t ht
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  have hIco : ContDiffOn ℝ (m + 1) (fun s ↦ forwardSemiflow X S s x) (Ico 0 b) :=
    contDiffOn_succ_of_hasDerivWithinAt_comp (uniqueDiffOn_Ico 0 b) hX
      (fun s hs ↦ forwardSemiflow_mem hX_lip (hsub hs))
      (fun s hs ↦ hasDerivWithinAt_forwardSemiflow_Ico hX_lip hsub hs)
  refine (hIco t ⟨nonneg_of_mem_forwardSemiflowInterval ht, htb⟩).mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact ⟨Iio b, Iio_mem_nhds htb,
    fun s hs ↦ ⟨nonneg_of_mem_forwardSemiflowInterval hs.2, hs.1⟩⟩

end TimeRegularity

/-! ### Variational derivative and inductive `C^m` smoothness -/

section VariationalRegularity

/-- Pointwise integral inequality for the spatial linearization remainder
`w t = Φ t y - Φ t y₀ - dysonSeriesLeft (DX ∘ Φ · y₀) t (y - y₀)` on `[0, τ]`. -/
private theorem norm_sub_dysonSeriesLeft_le_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} {X : E → E}
    (hX : ContDiffOn ℝ 1 X (U ∩ C)) {x₀ y₀ y : E} {r τ CD R₀ : ℝ} (hτ : 0 < τ)
    (h2rU : ball x₀ (2 * r) ⊆ U) (hy₀ : y₀ ∈ ball x₀ r ∩ C) (hy : y ∈ ball x₀ r ∩ C)
    (hmem : ∀ z ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t z ∈ ball x₀ (2 * r) ∩ C)
    (hint : ∀ z ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t z =
        z + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s z))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    (hM₀_cont : Continuous (fun s ↦ fderivWithin ℝ X (U ∩ C)
      (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) y₀)))
    (hCD_bound : ∀ s ∈ Icc 0 τ,
      ‖fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) s y₀)‖ ≤ CD)
    (hR₀ : 0 ≤ R₀)
    (hTaylor_s : ∀ s ∈ Icc 0 τ,
      ‖X (forwardSemiflow X (U ∩ C) s y) - X (forwardSemiflow X (U ∩ C) s y₀) -
        fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) s y₀)
          (forwardSemiflow X (U ∩ C) s y - forwardSemiflow X (U ∩ C) s y₀)‖ ≤ R₀)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    let Φ := forwardSemiflow X (U ∩ C)
    let A := dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) y₀))
    let w := fun s ↦ Φ s y - Φ s y₀ - A s (y - y₀)
    ‖w t‖ ≤ R₀ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ := by
  dsimp only
  set Φ := forwardSemiflow X (U ∩ C)
  set DX := fderivWithin ℝ X (U ∩ C)
  set A := dysonSeriesLeft (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀))
  set w := fun s ↦ Φ s y - Φ s y₀ - A s (y - y₀)
  have hγ_cont {z : E} (hz : z ∈ ball x₀ r ∩ C) : ContinuousOn (fun s ↦ Φ s z) (Icc 0 τ) :=
    hcontΦ.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hz⟩
  have hX_cont {z : E} (hz : z ∈ ball x₀ r ∩ C) : ContinuousOn (fun s ↦ X (Φ s z)) (Icc 0 τ) :=
    hX.continuousOn.comp (hγ_cont hz)
      fun s hs ↦ ⟨h2rU (hmem z hz s hs).1, (hmem z hz s hs).2⟩
  have hw_cont : ContinuousOn (fun s ↦ ‖w s‖) (Icc 0 τ) :=
    ((hγ_cont hy).sub (hγ_cont hy₀) |>.sub
      ((continuous_dysonSeriesLeft hM₀_cont).clm_apply continuous_const).continuousOn).norm
  have hA_int : A t (y - y₀) - (y - y₀) =
      ∫ s in (0 : ℝ)..t, DX (Φ (projIcc 0 τ hτ.le s) y₀) (A s (y - y₀)) := by
    have hd (s : ℝ) (_ : s ∈ uIcc 0 t) := hasDerivAt_dysonSeriesLeft_apply hM₀_cont (y - y₀) s
    simpa [A, DX] using (intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hM₀_cont.clm_apply ((continuous_dysonSeriesLeft hM₀_cont).clm_apply
        continuous_const)).intervalIntegrable _ _)).symm
  have hw_eq : w t = ∫ s in (0 : ℝ)..t,
      ((X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀)) + DX (Φ s y₀) (w s)) := by
    have hw_lhs : w t = (Φ t y - y) - (Φ t y₀ - y₀) - (A t (y - y₀) - (y - y₀)) := by
      simp only [w]; abel
    rw [hw_lhs, hint y hy t ht, hint y₀ hy₀ t ht, add_sub_cancel_left, add_sub_cancel_left,
      hA_int]
    have hInt1 := ((hX_cont hy).mono
      (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
      (μ := MeasureTheory.volume)
    have hInt2 := ((hX_cont hy₀).mono
      (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
      (μ := MeasureTheory.volume)
    have hInt3 := ((hM₀_cont.clm_apply ((continuous_dysonSeriesLeft hM₀_cont).clm_apply
      (continuous_const (y := y - y₀)))).intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    rw [← intervalIntegral.integral_sub hInt1 hInt2,
      ← intervalIntegral.integral_sub (hInt1.sub hInt2) hInt3]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    have hsI : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [DX, projIcc_of_mem hτ.le hsI, w, map_sub]
    abel
  have hDX_s : ContinuousOn (fun s ↦ DX (Φ s y₀)) (Icc 0 τ) :=
    hM₀_cont.continuousOn.congr fun s hs ↦ by simp [DX, projIcc_of_mem hτ.le hs]
  have hrem_int : IntervalIntegrable
      (fun s ↦ ‖X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀)‖ + CD * ‖w s‖)
      MeasureTheory.volume 0 t :=
    ((((hX_cont hy).sub (hX_cont hy₀)).sub
      (hDX_s.clm_apply ((hγ_cont hy).sub (hγ_cont hy₀)))).norm.add
        (continuousOn_const.mul hw_cont) |>.mono
          (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
  have hw_int : IntervalIntegrable (fun s ↦ CD * ‖w s‖) MeasureTheory.volume 0 t :=
    ((continuousOn_const.mul hw_cont).mono
      (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
  suffices h : ‖w t‖ ≤ R₀ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ from h
  rw [hw_eq]
  refine (intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ hrem_int).trans ?_
  · filter_upwards with s hs
    have hsI : s ∈ Icc 0 τ := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hW : ‖DX (Φ s y₀) (w s)‖ ≤ CD * ‖w s‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hCD_bound s hsI) (norm_nonneg _))
    exact (norm_add_le _ _).trans (add_le_add_right hW _)
  · have hmono := intervalIntegral.integral_mono_on ht.1 hrem_int
      ((intervalIntegrable_const (c := R₀)).add hw_int)
      fun s hs ↦ add_le_add_left (hTaylor_s s ⟨hs.1, hs.2.trans ht.2⟩) _
    refine hmono.trans ?_
    rw [intervalIntegral.integral_add intervalIntegrable_const hw_int,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, sub_zero, smul_eq_mul]
    have ht_le : t * R₀ ≤ R₀ * τ := by
      calc t * R₀ = R₀ * t := mul_comm _ _
        _ ≤ R₀ * τ := mul_le_mul_of_nonneg_left ht.2 hR₀
    linarith

/-- Spatial Taylor remainder estimate for the variational propagator `dysonSeriesLeft`: on `[0, τ]`,
`Φ t₀ y - Φ t₀ y₀ - A y₀ t₀ (y - y₀)` is bounded by `ε / 2 * ‖y - y₀‖` for `y ∈ ball x₀ r ∩ C`
sufficiently close to `y₀`. -/
private theorem eventually_norm_sub_dysonSeriesLeft_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C))
    {x₀ y₀ : E} {r τ : ℝ} {KΦ : ℝ≥0} (hτ : 0 < τ) (h2rU : ball x₀ (2 * r) ⊆ U)
    (hy₀ : y₀ ∈ ball x₀ r ∩ C)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y =
        y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hLipΦ : ∀ t ∈ Icc 0 τ,
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    {t₀ ε : ℝ} (ht₀ : t₀ ∈ Icc 0 τ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ ball x₀ r ∩ C, dist y y₀ < δ →
      ‖forwardSemiflow X (U ∩ C) t₀ y - forwardSemiflow X (U ∩ C) t₀ y₀ -
        dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) y₀)) t₀ (y - y₀)‖ ≤
        ε / 2 * ‖y - y₀‖ := by
  set Φ := forwardSemiflow X (U ∩ C)
  set DX := fderivWithin ℝ X (U ∩ C)
  have hDX_cont : ContinuousOn DX (U ∩ C) := hX.continuousOn_fderivWithin hU_uniq le_rfl
  have hγ₀_cont : ContinuousOn (fun s ↦ Φ s y₀) (Icc 0 τ) :=
    hcontΦ.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hy₀⟩
  have hM₀_cont : Continuous (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀)) :=
    hDX_cont.comp_continuous (hγ₀_cont.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) fun s ↦ (projIcc 0 τ hτ.le s).2)
      fun s ↦ ⟨h2rU (hmem y₀ hy₀ _ (projIcc 0 τ hτ.le s).2).1,
        (hmem y₀ hy₀ _ (projIcc 0 τ hτ.le s).2).2⟩
  obtain ⟨BD, hBD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hM₀_cont.norm).continuousOn (s := Icc 0 τ))
  set CD : ℝ := max BD 0
  have hCD : 0 ≤ CD := le_max_right _ _
  have hCD_bound (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖DX (Φ s y₀)‖ ≤ CD :=
    (by simpa [projIcc_of_mem hτ.le hs] using hBD s hs : ‖DX (Φ s y₀)‖ ≤ BD).trans
      (le_max_left _ _)
  set K' : ℝ := (KΦ : ℝ) + 1 with hK'_def
  have hK' : 0 < K' := by positivity
  have hKΦ_le : (KΦ : ℝ) ≤ K' := by linarith [hK'_def]
  set η : ℝ := ε / (4 * τ * K' * Real.exp (CD * τ))
  have hη : 0 < η := by positivity
  have hKtraj : IsCompact ((fun s ↦ Φ s y₀) '' Icc 0 τ) :=
    isCompact_Icc.image_of_continuousOn hγ₀_cont
  have hKsub : (fun s ↦ Φ s y₀) '' Icc 0 τ ⊆ U ∩ C := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨h2rU (hmem y₀ hy₀ s hs).1, (hmem y₀ hy₀ s hs).2⟩
  obtain ⟨ρ, hρ, hTaylor⟩ := hC.exists_pos_norm_sub_fderivWithin_le_of_compact hU hU_uniq hX
    hKtraj hKsub hη
  refine ⟨ρ / K', by positivity, fun y hy hdist ↦ ?_⟩
  let A : ℝ → E →L[ℝ] E := dysonSeriesLeft (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀))
  let w : ℝ → E := fun t ↦ Φ t y - Φ t y₀ - A t (y - y₀)
  have hγy_cont : ContinuousOn (fun s ↦ Φ s y) (Icc 0 τ) :=
    hcontΦ.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hy⟩
  have hw_cont : ContinuousOn (fun t ↦ ‖w t‖) (Icc 0 τ) :=
    (hγy_cont.sub hγ₀_cont |>.sub
      ((continuous_dysonSeriesLeft hM₀_cont).clm_apply continuous_const).continuousOn).norm
  have hTaylor_s (s : ℝ) (hsI : s ∈ Icc 0 τ) :
      ‖X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀)‖ ≤ η * K' * ‖y - y₀‖ := by
    have hdist_s : dist (Φ s y) (Φ s y₀) < ρ := by
      calc dist (Φ s y) (Φ s y₀) ≤ (KΦ : ℝ) * dist y y₀ :=
            (hLipΦ s hsI).dist_le_mul y hy y₀ hy₀
        _ ≤ K' * dist y y₀ := mul_le_mul_of_nonneg_right hKΦ_le dist_nonneg
        _ < K' * (ρ / K') := mul_lt_mul_of_pos_left hdist hK'
        _ = ρ := mul_div_cancel₀ ρ hK'.ne'
    calc ‖X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀)‖
        ≤ η * ‖Φ s y - Φ s y₀‖ :=
          hTaylor (Φ s y₀) (mem_image_of_mem _ hsI) (Φ s y) (hmem y hy s hsI).2 hdist_s
      _ ≤ η * ((KΦ : ℝ) * ‖y - y₀‖) := by
          gcongr
          simpa [dist_eq_norm] using (hLipΦ s hsI).dist_le_mul y hy y₀ hy₀
      _ ≤ η * (K' * ‖y - y₀‖) := by gcongr
      _ = η * K' * ‖y - y₀‖ := (mul_assoc _ _ _).symm
  have hw_bound (t : ℝ) (ht : t ∈ Icc 0 τ) :
      ‖w t‖ ≤ η * K' * ‖y - y₀‖ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ :=
    norm_sub_dysonSeriesLeft_le_add_integral hX hτ h2rU hy₀ hy hmem hint hcontΦ hM₀_cont
      hCD_bound (by positivity) hTaylor_s ht
  have hgron := le_mul_exp_of_le_add_mul_integral hw_cont hCD hw_bound t₀ ht₀
  calc ‖w t₀‖ ≤ η * K' * ‖y - y₀‖ * τ * Real.exp (CD * (t₀ - 0)) := hgron
    _ ≤ η * K' * ‖y - y₀‖ * τ * Real.exp (CD * τ) := by
        gcongr
        linarith [ht₀.2]
    _ = ε / 4 * ‖y - y₀‖ := by
        have hτ_ne := hτ.ne'
        have hK'_ne := hK'.ne'
        simp only [η]
        field_simp
    _ ≤ ε / 2 * ‖y - y₀‖ := by nlinarith [norm_nonneg (y - y₀)]

/-- Joint Fréchet derivative of `uncurry (forwardSemiflow X (U ∩ C))` on
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)`, valid up to `t = 0` and `∂C`. -/
private theorem hasFDerivWithinAt_local_forwardSemiflow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C))
    {x₀ : E} {r τ : ℝ} {KΦ : ℝ≥0} (hτ : 0 < τ) (h2rU : ball x₀ (2 * r) ⊆ U)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y =
        y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hLipΦ : ∀ t ∈ Icc 0 τ,
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    {p₀ : ℝ × E} (hp₀ : p₀ ∈ Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :
    HasFDerivWithinAt (uncurry (forwardSemiflow X (U ∩ C)))
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (X (forwardSemiflow X (U ∩ C) p₀.1 p₀.2)) +
        (dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) p₀.2)) p₀.1).comp
          (ContinuousLinearMap.snd ℝ ℝ E))
      (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) p₀ := by
  set Φ := forwardSemiflow X (U ∩ C)
  set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hXΦ_cont : ContinuousOn (X ∘ uncurry Φ) S :=
    hX.continuousOn.comp hcontΦ fun p hp ↦ ⟨h2rU (hmem p.2 hp.2 p.1 hp.1).1,
      (hmem p.2 hp.2 p.1 hp.1).2⟩
  obtain ⟨δ₁, hδ₁, hcloseX⟩ := Metric.continuousWithinAt_iff.mp (hXΦ_cont p₀ hp₀)
    (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hrem⟩ := eventually_norm_sub_dysonSeriesLeft_le hC hU hU_uniq hX hτ h2rU
    hp₀.2 hmem hint hLipΦ hcontΦ hp₀.1 hε
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds p₀ (lt_min hδ₁ hδ₂)),
    self_mem_nhdsWithin] with p hpdist hpS
  rw [mem_ball] at hpdist
  have hp_d1 : dist p p₀ < δ₁ := hpdist.trans_le (min_le_left _ _)
  have hp_d2 : dist p.2 p₀.2 < δ₂ := by
    have hmax := hpdist.trans_le (min_le_right _ _)
    rw [Prod.dist_eq] at hmax
    exact (le_max_right _ _).trans_lt hmax
  -- Step 1: Bound the time increment `Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)`.
  have ht_inc : ‖Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)‖ ≤
      ε / 2 * ‖p - p₀‖ := by
    have hX_y : ContinuousOn (fun s ↦ X (Φ s p.2)) (Icc 0 τ) :=
      hXΦ_cont.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hpS.2⟩
    have hdiff_int : Φ p.1 p.2 - Φ p₀.1 p.2 = ∫ s in p₀.1..p.1, X (Φ s p.2) := by
      have hInt1 := (hX_y.mono (uIcc_of_le hp₀.1.1 ▸
        Icc_subset_Icc_right hp₀.1.2)).intervalIntegrable (μ := MeasureTheory.volume)
      have hInt2 := (hX_y.mono (uIcc_subset_Icc hp₀.1 hpS.1)).intervalIntegrable
        (μ := MeasureTheory.volume)
      rw [hint p.2 hpS.2 p.1 hpS.1, hint p.2 hpS.2 p₀.1 hp₀.1, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
      abel
    have hconst_int : (p.1 - p₀.1) • X (Φ p₀.1 p₀.2) =
        ∫ _ in p₀.1..p.1, X (Φ p₀.1 p₀.2) := by
      simp [intervalIntegral.integral_const]
    rw [hdiff_int, hconst_int,
      ← intervalIntegral.integral_sub
        (hX_y.mono (uIcc_subset_Icc hp₀.1 hpS.1)).intervalIntegrable intervalIntegrable_const]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2)
      fun s hs ↦ ?_).trans ?_
    · have hsIcc : s ∈ Icc 0 τ := uIcc_subset_Icc hp₀.1 hpS.1 (uIoc_subset_uIcc hs)
      have habs : |s - p₀.1| ≤ |p.1 - p₀.1| := by
        have hlo := neg_le_abs (p.1 - p₀.1)
        have hhi := le_abs_self (p.1 - p₀.1)
        rcases mem_uIcc.mp (uIoc_subset_uIcc hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hs_dist : dist (s, p.2) p₀ < δ₁ := by
        rw [Prod.dist_eq] at hp_d1 ⊢
        dsimp only
        refine max_lt (lt_of_le_of_lt ?_ (max_lt_iff.mp hp_d1).1) (max_lt_iff.mp hp_d1).2
        simpa [Real.dist_eq] using habs
      have hclose : ‖X (Φ s p.2) - X (Φ p₀.1 p₀.2)‖ < ε / 2 := by
        simpa only [Function.comp_apply, Function.uncurry_def, dist_eq_norm] using
          hcloseX (x := (s, p.2)) ⟨hsIcc, hpS.2⟩ hs_dist
      linarith
    · calc ε / 2 * |p.1 - p₀.1| = ε / 2 * ‖(p - p₀).1‖ := by simp [Real.norm_eq_abs]
        _ ≤ ε / 2 * ‖p - p₀‖ :=
            mul_le_mul_of_nonneg_left (norm_fst_le (p - p₀)) (half_pos hε).le
  -- Step 2: Combine with the spatial remainder estimate at fixed time `p₀.1`.
  have hsplit : uncurry Φ p - uncurry Φ p₀ -
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (X (Φ p₀.1 p₀.2)) +
        (dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2))
          p₀.1).comp (ContinuousLinearMap.snd ℝ ℝ E)) (p - p₀) =
      (Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)) +
      (Φ p₀.1 p.2 - Φ p₀.1 p₀.2 -
        dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2))
          p₀.1 (p.2 - p₀.2)) := by
    simp [uncurry]
    abel
  rw [hsplit]
  calc ‖(Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)) +
        (Φ p₀.1 p.2 - Φ p₀.1 p₀.2 -
          dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2))
            p₀.1 (p.2 - p₀.2))‖
      ≤ ‖Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)‖ +
          ‖Φ p₀.1 p.2 - Φ p₀.1 p₀.2 -
            dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2))
              p₀.1 (p.2 - p₀.2)‖ := norm_add_le _ _
    _ ≤ ε / 2 * ‖p - p₀‖ + ε / 2 * ‖p.2 - p₀.2‖ := add_le_add ht_inc (hrem p.2 hpS.2 hp_d2)
    _ ≤ ε / 2 * ‖p - p₀‖ + ε / 2 * ‖p - p₀‖ := by
        gcongr
        exact norm_snd_le (p - p₀)
    _ = ε * ‖p - p₀‖ := by ring

/-- Joint continuity of the variational propagator `dysonSeriesLeft` along `forwardSemiflow` on
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)`. -/
private theorem continuousOn_dysonSeriesLeft_forwardSemiflow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} (hU_uniq : UniqueDiffOn ℝ (U ∩ C))
    {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C)) {x₀ : E} {r τ : ℝ} (hτ : 0 < τ)
    (h2rU : ball x₀ (2 * r) ⊆ U)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C))) :
    ContinuousOn (fun p : ℝ × E ↦ dysonSeriesLeft
      (fun s ↦ fderivWithin ℝ X (U ∩ C)
        (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) p.2)) p.1)
      (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  let B := ↥(ball x₀ r ∩ C)
  let P : B → ℝ → E →L[ℝ] E := fun y s ↦
    fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) y.1)
  have hDX_cont : ContinuousOn (fderivWithin ℝ X (U ∩ C)) (U ∩ C) :=
    hX.continuousOn_fderivWithin hU_uniq le_rfl
  have hcoord : Continuous (fun q : B × ℝ ↦ ((projIcc 0 τ hτ.le q.2 : ℝ), q.1.1)) :=
    ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hΦP : Continuous (fun q : B × ℝ ↦
      uncurry (forwardSemiflow X (U ∩ C)) ((projIcc 0 τ hτ.le q.2 : ℝ), q.1.1)) :=
    hcontΦ.comp_continuous hcoord fun q ↦ ⟨(projIcc 0 τ hτ.le q.2).2, q.1.2⟩
  have hP_cont : Continuous (uncurry P) :=
    hDX_cont.comp_continuous hΦP fun q ↦
      ⟨h2rU (hmem q.1.1 q.1.2 _ (projIcc 0 τ hτ.le q.2).2).1,
        (hmem q.1.1 q.1.2 _ (projIcc 0 τ hτ.le q.2).2).2⟩
  have hDyson : Continuous (fun q : B × ℝ ↦ dysonSeriesLeft (P q.1) q.2) :=
    continuous_parametric_dysonSeriesLeft hP_cont
  rw [continuousOn_iff_continuous_domRestrict]
  exact hDyson.comp (((continuous_snd.comp continuous_subtype_val).subtype_mk fun p ↦ p.2.2).prodMk
    (continuous_fst.comp continuous_subtype_val))

/-- Identification of the variational semiflow on `E × (E →L[ℝ] E)` starting at `(y, 1)` with the
pair `(forwardSemiflow X (U ∩ C) · y, dysonSeriesLeft ·)`. -/
private theorem eq_forwardSemiflow_variational {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 2 X (U ∩ C))
    {x₀ y : E} {r₁ τ₁ b : ℝ} (hτ₁ : 0 < τ₁) (hb : 0 < b) (hb_le : b ≤ τ₁)
    (h2r₁U : ball x₀ (2 * r₁) ⊆ U)
    (hsub₁ : Ico 0 (2 * τ₁) ⊆ forwardSemiflowInterval X (U ∩ C) y)
    (hmem₁ : ∀ t ∈ Icc 0 τ₁, forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r₁) ∩ C)
    (hcont₁ : ContinuousOn (fun t ↦ forwardSemiflow X (U ∩ C) t y) (Icc 0 τ₁))
    {t : ℝ} (ht : t ∈ Ico 0 b) :
    let X' : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
      fun q ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2)
    forwardSemiflow X' ((U ×ˢ univ) ∩ (C ×ˢ univ)) t (y, (1 : E →L[ℝ] E)) =
      (forwardSemiflow X (U ∩ C) t y,
        dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) y)) t) := by
  intro X'
  have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (by norm_num)
  have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1
  have hDX : ContDiffOn ℝ 1 (fderivWithin ℝ X (U ∩ C)) (U ∩ C) :=
    hX.fderivWithin hU_uniq (by norm_num)
  let S' : Set (E × (E →L[ℝ] E)) := (U ×ˢ univ) ∩ (C ×ˢ univ)
  have hX' : ContDiffOn ℝ 1 X' S' :=
    (hX1.comp contDiffOn_fst fun q (hq : q ∈ S') ↦ ⟨hq.1.1, hq.2.1⟩).prodMk
      ((hDX.comp contDiffOn_fst fun q (hq : q ∈ S') ↦ ⟨hq.1.1, hq.2.1⟩).clm_comp contDiffOn_snd)
  have hX'_lip : LocallyLipschitzOn S' X' :=
    (hC.prod convex_univ).locallyLipschitzOn_inter_of_contDiffOn (hU.prod isOpen_univ) hX'
  let M_y : ℝ → E →L[ℝ] E := fun s ↦
    fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) y)
  have hMy_cont : Continuous M_y :=
    hDX.continuousOn.comp_continuous
      (hcont₁.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun s ↦ (projIcc 0 τ₁ hτ₁.le s).2)
      fun s ↦ ⟨h2r₁U (hmem₁ _ (projIcc 0 τ₁ hτ₁.le s).2).1,
        (hmem₁ _ (projIcc 0 τ₁ hτ₁.le s).2).2⟩
  let Γ : ℝ → E × (E →L[ℝ] E) := fun s ↦ (forwardSemiflow X (U ∩ C) s y, dysonSeriesLeft M_y s)
  have hΓ0 : Γ 0 = (y, (1 : E →L[ℝ] E)) := by
    ext1
    · exact forwardSemiflow_zero _ _ _
    · exact dysonSeriesLeft_zero _
  have hΓ_maps : MapsTo Γ (Ico 0 b) S' := fun s hs ↦ by
    have hs₁ : s ∈ Icc 0 τ₁ := ⟨hs.1, hs.2.le.trans hb_le⟩
    exact ⟨⟨h2r₁U (hmem₁ s hs₁).1, trivial⟩, ⟨(hmem₁ s hs₁).2, trivial⟩⟩
  have hΓ' : ∀ s ∈ Ico 0 b, HasDerivWithinAt Γ (X' (Γ s)) (Ico 0 b) s := fun s hs ↦ by
    have hs₁ : s ∈ Icc 0 τ₁ := ⟨hs.1, hs.2.le.trans hb_le⟩
    have hd1 := (hasDerivWithinAt_forwardSemiflow_Ico hX_lip hsub₁
      ⟨hs.1, hs.2.trans_le (by linarith)⟩).mono (Ico_subset_Ico_right (by linarith))
    have hd2 : HasDerivWithinAt (dysonSeriesLeft M_y)
        ((fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) s y)).comp
          (dysonSeriesLeft M_y s)) (Ico 0 b) s := by
      have hd := (hasDerivAt_dysonSeriesLeft hMy_cont s).hasDerivWithinAt (s := Ico 0 b)
      simpa only [M_y, projIcc_of_mem hτ₁.le hs₁, ContinuousLinearMap.mul_def] using hd
    exact hd1.prodMk hd2
  exact (eqOn_forwardSemiflow hX'_lip hb hΓ0 hΓ_maps hΓ' ht).symm

/-- Inductive short-time `C^{k+1}` regularity of `uncurry (forwardSemiflow X (U ∩ C))` on a uniform
neighborhood `Icc 0 τ ×ˢ (ball x₀ r ∩ C)`. -/
private theorem exists_local_forwardSemiflow_contDiffOn_nat.{u} (k : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U)
      {X : E → E} (hX : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C)) {x₀ : E}
      (hx₀ : x₀ ∈ U ∩ C) (hX_in : X x₀ ∈ strictInwardCone C x₀),
      ∃ r > 0, ∃ τ > 0, ball x₀ r ⊆ U ∧
        (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
        ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C)))
          (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  induction k with
  | zero =>
    -- Base case (`C¹`): combine `hasFDerivWithinAt_local_forwardSemiflow` with continuity of the
    -- Dyson propagator.
    intro E _ _ _ C U hC hC_closed hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := by simpa using hX
    have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hx₀.2 hX_in
    obtain ⟨r, hr, τ, hτ, _, _, h2rU, _, hsub, hmem, hint, hLipΦ, hcontΦ⟩ :=
      exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX_lip hx₀ hX_in
    set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
    have hS_uniq : UniqueDiffOn ℝ S :=
      (uniqueDiffOn_Icc hτ).prod (hC.uniqueDiffOn_inter_of_mem_strictInwardCone isOpen_ball
        hx₀.2 hX_in)
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith)).trans h2rU, hsub, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun p hp ↦ hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1
      hτ h2rU hmem hint hLipΦ hcontΦ hp⟩
    have hXΦ : ContinuousOn (fun p : ℝ × E ↦ X (forwardSemiflow X (U ∩ C) p.1 p.2)) S :=
      hX1.continuousOn.comp hcontΦ fun p hp ↦ ⟨h2rU (hmem p.2 hp.2 p.1 hp.1).1,
        (hmem p.2 hp.2 p.1 hp.1).2⟩
    have hA := continuousOn_dysonSeriesLeft_forwardSemiflow hU_uniq hX1 hτ h2rU hmem hcontΦ
    exact (contDiffOn_const.smulRight (contDiffOn_zero.mpr hXΦ)).add
      ((contDiffOn_zero.mpr hA).clm_comp contDiffOn_const)
  | succ k ih =>
    -- Inductive step (`C^{k+2}`): apply the `C^{k+1}` hypothesis to the variational system on
    -- `E × (E →L[ℝ] E)` to obtain `C^{k+1}` regularity of `(Φ, A)`.
    intro E _ _ _ C U hC hC_closed hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (by norm_cast; omega)
    have hX2 : ContDiffOn ℝ 2 X (U ∩ C) := hX.of_le (by norm_cast; omega)
    have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hx₀.2 hX_in
    obtain ⟨r₁, hr₁, τ₁, hτ₁, _, _, h2r₁U, _, hsub₁, hmem₁, hint₁, hLip₁, hcont₁⟩ :=
      exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX_lip hx₀ hX_in
    let F := E × (E →L[ℝ] E)
    let C' : Set F := C ×ˢ univ
    let U' : Set F := U ×ˢ univ
    let X' : F → F := fun q ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2)
    have hX' : ContDiffOn ℝ (k + 1 : ℕ) X' (U' ∩ C') :=
      ((hX.of_le (by norm_cast; omega)).comp contDiffOn_fst
        fun q (hq : q ∈ U' ∩ C') ↦ ⟨hq.1.1, hq.2.1⟩).prodMk
        (((hX.fderivWithin hU_uniq (by norm_cast)).comp contDiffOn_fst
          fun q (hq : q ∈ U' ∩ C') ↦ ⟨hq.1.1, hq.2.1⟩).clm_comp contDiffOn_snd)
    let q₀ : F := (x₀, (1 : E →L[ℝ] E))
    have hq₀ : q₀ ∈ U' ∩ C' := ⟨⟨hx₀.1, trivial⟩, ⟨hx₀.2, trivial⟩⟩
    have hX'_in : X' q₀ ∈ strictInwardCone C' q₀ := by
      obtain ⟨t, ht_pos, ht_int⟩ := (hC.mem_strictInwardCone_iff hx₀.2).mp hX_in
      refine ((hC.prod convex_univ).mem_strictInwardCone_iff hq₀.2).mpr ⟨t, ht_pos, ?_⟩
      rw [interior_prod_eq, interior_univ]
      exact ⟨ht_int, trivial⟩
    obtain ⟨r₂, hr₂, τ₂, hτ₂, _, _, hCD₂⟩ :=
      ih (hC.prod convex_univ) (hC_closed.prod isClosed_univ) (hU.prod isOpen_univ) hX' hq₀ hX'_in
    set r := min r₁ r₂
    have hr : 0 < r := lt_min hr₁ hr₂
    set τ := min (τ₁ / 2) τ₂
    have hτ : 0 < τ := lt_min (half_pos hτ₁) hτ₂
    have hτ_le₁ : 2 * τ ≤ τ₁ := by linarith [min_le_left (τ₁ / 2) τ₂]
    have hτ_le₂ : τ ≤ τ₂ := min_le_right _ _
    have hr_le₁ : r ≤ r₁ := min_le_left _ _
    have hr_le₂ : r ≤ r₂ := min_le_right _ _
    set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
    have hS_uniq : UniqueDiffOn ℝ S :=
      (uniqueDiffOn_Icc hτ).prod (hC.uniqueDiffOn_inter_of_mem_strictInwardCone isOpen_ball
        hx₀.2 hX_in)
    have hS_sub₁ : S ⊆ Icc 0 τ₁ ×ˢ (ball x₀ r₁ ∩ C) :=
      prod_mono (Icc_subset_Icc_right (by linarith))
        (inter_subset_inter_left C (ball_subset_ball hr_le₁))
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith)).trans h2r₁U,
      fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans
        (hsub₁ y ⟨ball_subset_ball hr_le₁ hy.1, hy.2⟩), ?_⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun p hp ↦
      (hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1 hτ₁ h2r₁U hmem₁ hint₁ hLip₁
        hcont₁ (hS_sub₁ hp)).mono hS_sub₁⟩
    let embed : ℝ × E → ℝ × F := fun p ↦ (p.1, (p.2, (1 : E →L[ℝ] E)))
    have hembed_cd : ContDiffOn ℝ (k + 1 : ℕ) embed S :=
      contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)
    have hembed_maps : MapsTo embed S (Icc 0 τ₂ ×ˢ (ball q₀ r₂ ∩ C')) := fun p hp ↦ by
      refine ⟨⟨hp.1.1, hp.1.2.trans hτ_le₂⟩, ?_, ⟨hp.2.2, trivial⟩⟩
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (lt_of_lt_of_le hp.2.1 hr_le₂) (by simp [embed, q₀, hr₂])
    have hΨ_cd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X' (U' ∩ C')) ∘ embed) S :=
      hCD₂.comp hembed_cd hembed_maps
    have hΨ_eq (p : ℝ × E) (hp : p ∈ S) :
        (uncurry (forwardSemiflow X' (U' ∩ C')) ∘ embed) p =
          (forwardSemiflow X (U ∩ C) p.1 p.2,
            dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
              (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) p.2)) p.1) := by
      have hy₁ : p.2 ∈ ball x₀ r₁ ∩ C := ⟨ball_subset_ball hr_le₁ hp.2.1, hp.2.2⟩
      exact eq_forwardSemiflow_variational hC hU hU_uniq hX2 hτ₁ (by positivity : 0 < 2 * τ)
        hτ_le₁ h2r₁U (hsub₁ p.2 hy₁) (hmem₁ p.2 hy₁)
        (hcont₁.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hy₁⟩)
        ⟨hp.1.1, by linarith [hp.1.2]⟩
    have hΦ_cd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C))) S :=
      (contDiffOn_fst.comp hΨ_cd (mapsTo_univ _ _)).congr fun p hp ↦
        congr_arg Prod.fst (hΨ_eq p hp).symm
    have hA_cd : ContDiffOn ℝ (k + 1 : ℕ)
        (fun p : ℝ × E ↦ dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) p.2)) p.1) S :=
      (contDiffOn_snd.comp hΨ_cd (mapsTo_univ _ _)).congr fun p hp ↦
        congr_arg Prod.snd (hΨ_eq p hp).symm
    have hXΦ_cd : ContDiffOn ℝ (k + 1 : ℕ)
        (fun p : ℝ × E ↦ X (forwardSemiflow X (U ∩ C) p.1 p.2)) S :=
      (hX.of_le (by norm_cast; omega)).comp hΦ_cd fun p hp ↦
        ⟨h2r₁U (hmem₁ p.2 (hS_sub₁ hp).2 p.1 (hS_sub₁ hp).1).1,
          (hmem₁ p.2 (hS_sub₁ hp).2 p.1 (hS_sub₁ hp).1).2⟩
    exact (contDiffOn_const.smulRight hXΦ_cd).add (hA_cd.clm_comp contDiffOn_const)

/-- Propagation of `C^{k+1}` joint regularity of `forwardSemiflow` along any forward trajectory up
to time `T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
private theorem exists_contDiffOn_Icc_of_mem_forwardSemiflowInterval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {k : ℕ} {X : E → E}
    (hX : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {x₀ : E} {T : ℝ}
    (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0,
      ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C)))
        (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  let Φ := forwardSemiflow X (U ∩ C)
  have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU (hX.of_le (by norm_cast; omega))
  obtain ⟨r₀, hr₀, δ₀, hδ₀, _, hsub₀, hcont₀⟩ :=
    exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hX_lip hX_in hx₀ hT
  let P : ℝ → Prop := fun t ↦ ∃ r > 0, ∃ δ > 0, r ≤ r₀ ∧ δ ≤ δ₀ ∧
    ContDiffOn ℝ (k + 1 : ℕ) (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C))
  have hP_ext {t r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hr0 : r ≤ r₀) (hδ0 : δ ≤ δ₀)
      (hcd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C)))
      {u : ℝ} (hu : u ≤ t + δ / 2) : P u :=
    ⟨r, hr, δ / 4, by positivity, hr0, by linarith,
      hcd.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)⟩
  by_contra hnotPT
  obtain ⟨r, hr, δ, hδ, _, _, hcd⟩ | h := em (P T)
  · exact hnotPT ⟨r, hr, δ, hδ, hcd⟩
  let B : Set ℝ := {t ∈ Icc 0 T | ¬ P t}
  have hBne : B.Nonempty := ⟨T, ⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, h⟩
  have hBbdd : BddBelow B := ⟨0, fun t ht ↦ ht.1.1⟩
  set b := sInf B
  have hb0 : 0 ≤ b := le_csInf hBne fun t ht ↦ ht.1.1
  have hbT : b ≤ T := csInf_le hBbdd ⟨⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, h⟩
  obtain ⟨r₁, hr₁, τ₁, hτ₁, _, _, hcd₁⟩ :=
    exists_local_forwardSemiflow_contDiffOn_nat k hC hC_closed hU hX hx₀ (hX_in x₀ hx₀)
  have hb_pos : 0 < b := by
    set δ₁ := min (τ₁ / 2) δ₀
    have hδ₁ : 0 < δ₁ := lt_min (half_pos hτ₁) hδ₀
    have hle : δ₁ / 2 ≤ b := le_csInf hBne fun t ht ↦ by
      by_contra hlt
      exact ht.2 (hP_ext (t := 0) (lt_min hr₁ hr₀) hδ₁ (min_le_right _ _) (min_le_right _ _)
        (hcd₁.mono (prod_mono (Icc_subset_Icc_right (by linarith [min_le_left (τ₁ / 2) δ₀]))
          (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _))))) (by linarith))
    linarith
  have hbJ : b ∈ forwardSemiflowInterval X (U ∩ C) x₀ :=
    Icc_subset_of_mem_forwardSemiflowInterval hT ⟨hb0, hbT⟩
  have hzU : Φ b x₀ ∈ U ∩ C := forwardSemiflow_mem hX_lip hbJ
  obtain ⟨rz, hrz, τz, hτz, _, hsubz, hcdz⟩ :=
    exists_local_forwardSemiflow_contDiffOn_nat k hC hC_closed hU hX hzU (hX_in _ hzU)
  obtain ⟨ηc, hηc, hclose⟩ := Metric.continuousWithinAt_iff.mp
    (hcont₀ (b, x₀) ⟨⟨hb0, by linarith⟩, mem_ball_self hr₀, hx₀.2⟩) rz hrz
  set τ' := min τz δ₀
  have : 0 < τ' := lt_min hτz hδ₀
  set η := min (b / 2) (min (ηc / 2) (τ' / 3))
  have hη : 0 < η := by positivity
  set s := b - η
  have hs_pos : 0 < s := by linarith [min_le_left (b / 2) (min (ηc / 2) (τ' / 3))]
  have hs_lt_b : s < b := sub_lt_self b hη
  have hbs_le : b - s ≤ τ' / 3 := by
    linarith [min_le_right (b / 2) (min (ηc / 2) (τ' / 3)), min_le_right (ηc / 2) (τ' / 3)]
  have hPs : P s := by
    by_contra hnotPs
    exact not_lt_of_ge (csInf_le hBbdd ⟨⟨hs_pos.le, hs_lt_b.le.trans hbT⟩, hnotPs⟩) hs_lt_b
  obtain ⟨rs, hrs, δs, hδs, hrs0, _, hcds⟩ := hPs
  set r' := min rs (ηc / 2)
  have hr' : 0 < r' := lt_min hrs (half_pos hηc)
  have hΦs_ball (y : E) (hy : y ∈ ball x₀ r' ∩ C) : Φ s y ∈ ball (Φ b x₀) rz ∩ C := by
    have hy₀ : y ∈ ball x₀ r₀ ∩ C :=
      ⟨ball_subset_ball ((min_le_left _ _).trans hrs0) hy.1, hy.2⟩
    have hdist : dist (s, y) (b, x₀) < ηc := by
      rw [Prod.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt_b)]
      refine max_lt ?_ (lt_of_lt_of_le hy.1 (by linarith [min_le_right rs (ηc / 2)]))
      linarith [min_le_right (b / 2) (min (ηc / 2) (τ' / 3)), min_le_left (ηc / 2) (τ' / 3)]
    exact ⟨hclose ⟨⟨hs_pos.le, by linarith⟩, hy₀⟩ hdist,
      (forwardSemiflow_mem hX_lip (hsub₀ y hy₀ ⟨hs_pos.le, by linarith⟩)).2⟩
  have hstep_cd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry Φ) (Icc s (s + τ') ×ˢ (ball x₀ r' ∩ C)) := by
    let stepMap : ℝ × E → ℝ × E := fun p ↦ (p.1 - s, Φ s p.2)
    have hΦs_cd : ContDiffOn ℝ (k + 1 : ℕ) (fun y ↦ Φ s y) (ball x₀ r' ∩ C) :=
      hcds.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy ↦
        ⟨⟨hs_pos.le, by linarith⟩, ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    have hstepMap_cd : ContDiffOn ℝ (k + 1 : ℕ) stepMap (Icc s (s + τ') ×ˢ (ball x₀ r' ∩ C)) :=
      (contDiffOn_fst.sub contDiffOn_const).prodMk
        (hΦs_cd.comp contDiffOn_snd fun p hp ↦ hp.2)
    have hstepMap_maps : MapsTo stepMap (Icc s (s + τ') ×ˢ (ball x₀ r' ∩ C))
        (Icc 0 τz ×ˢ (ball (Φ b x₀) rz ∩ C)) := fun p hp ↦
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2, min_le_left τz δ₀]⟩, hΦs_ball p.2 hp.2⟩
    refine (hcdz.comp hstepMap_cd hstepMap_maps).congr fun p hp ↦ ?_
    have hy₀ : p.2 ∈ ball x₀ r₀ ∩ C :=
      ⟨ball_subset_ball ((min_le_left _ _).trans hrs0) hp.2.1, hp.2.2⟩
    have hsJ : s ∈ forwardSemiflowInterval X (U ∩ C) p.2 :=
      hsub₀ p.2 hy₀ ⟨hs_pos.le, by linarith⟩
    have huJ : p.1 - s ∈ forwardSemiflowInterval X (U ∩ C) (Φ s p.2) :=
      hsubz (Φ s p.2) (hΦs_ball p.2 hp.2)
        ⟨by linarith [hp.1.1], by linarith [hp.1.2, min_le_left τz δ₀]⟩
    have heq := forwardSemiflow_add hX_lip hsJ huJ
    rw [sub_add_cancel] at heq
    exact heq
  have hglue : ContDiffOn ℝ (k + 1 : ℕ) (uncurry Φ) (Icc 0 (s + τ') ×ˢ (ball x₀ r' ∩ C)) := by
    set T₁ := min (s + δs) (s + τ')
    have hT₁ : s < T₁ := lt_min (by linarith) (by linarith)
    intro p hp
    rcases lt_or_ge p.1 T₁ with hlt | hge
    · have hp₁ : p ∈ Icc 0 (s + δs) ×ˢ (ball x₀ rs ∩ C) :=
        ⟨⟨hp.1.1, hlt.le.trans (min_le_left _ _)⟩,
          ball_subset_ball (min_le_left _ _) hp.2.1, hp.2.2⟩
      refine (hcds p hp₁).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Iio T₁ ×ˢ ball x₀ rs, (isOpen_Iio.prod isOpen_ball).mem_nhds ⟨hlt, hp₁.2.1⟩,
        fun q hq ↦ ⟨⟨hq.2.1.1, hq.1.1.le.trans (min_le_left _ _)⟩, hq.1.2, hq.2.2.2⟩⟩
    · have hgt : s < p.1 := hT₁.trans_le hge
      refine (hstep_cd p ⟨⟨hgt.le, hp.1.2⟩, hp.2⟩).mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Ioi s ×ˢ univ, (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hgt, trivial⟩,
        fun q hq ↦ ⟨⟨hq.1.1.le, hq.2.1.2⟩, hq.2.2⟩⟩
  have hb_contra : b + τ' / 6 ≤ b := le_csInf hBne fun t ht ↦ by
    by_contra hlt
    exact ht.2 (hP_ext (t := b) hr' (by positivity : 0 < τ' / 3)
      ((min_le_left _ _).trans hrs0) (by linarith [min_le_right τz δ₀])
      (hglue.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl))
      (by linarith))
  linarith

/-- **Joint `C^m` smoothness of the maximal forward semiflow.** For `1 ≤ m` (`m : ℕ∞`, including
`m = ∞`), if `X` is `C^m` on `U ∩ C` and strictly inward to the closed convex set `C` at every
point of `U ∩ C`, then `uncurry (forwardSemiflow X (U ∩ C))` is `C^m` on the entire maximal domain
`forwardSemiflowDomain X (U ∩ C)` — including at `t = 0` and along `∂C`. -/
theorem contDiffOn_forwardSemiflow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ContDiffOn ℝ m (uncurry (forwardSemiflow X (U ∩ C))) (forwardSemiflowDomain X (U ∩ C)) := by
  rw [contDiffOn_iff_forall_nat_le]
  intro j hj
  set k : ℕ := max j 1 - 1
  have hk_eq : k + 1 = max j 1 := Nat.sub_add_cancel (le_max_right j 1)
  have hkm : ((k + 1 : ℕ) : ℕ∞) ≤ m := by
    rw [hk_eq]
    exact max_le hj hm
  have hXk : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C) := hX.of_le (mod_cast hkm)
  intro p hp
  obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp hp
  obtain ⟨r, hr, δ, hδ, hcd⟩ :=
    exists_contDiffOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hXk hX_in hpU hpJ
  have hcd_p : ContDiffWithinAt ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C)))
      (forwardSemiflowDomain X (U ∩ C)) p := by
    refine (hcd p ⟨⟨nonneg_of_mem_forwardSemiflowInterval hpJ, by linarith⟩,
      mem_ball_self hr, hpU.2⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Iio (p.1 + δ) ×ˢ ball p.2 r, (isOpen_Iio.prod isOpen_ball).mem_nhds
      ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun q hq ↦
        ⟨⟨nonneg_of_mem_forwardSemiflowInterval (mem_forwardSemiflowDomain_iff.mp hq.2).2,
          hq.1.1.le⟩, hq.1.2, (mem_forwardSemiflowDomain_iff.mp hq.2).1.2⟩⟩
  exact hcd_p.of_le (by norm_cast; omega)

/-- **Global `C^m` smoothness of a forward-complete inward semiflow on `Ici 0 ×ˢ C`.** -/
theorem contDiffOn_forwardSemiflow_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C) {m : ℕ∞} (hm : 1 ≤ m)
    {X : E → E} (hX : ContDiffOn ℝ m X C) (hX_in : ∀ x ∈ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ C, forwardSemiflowInterval X C x = Ici 0) :
    ContDiffOn ℝ m (uncurry (forwardSemiflow X C)) (Ici 0 ×ˢ C) := by
  have h := contDiffOn_forwardSemiflow hC hC_closed isOpen_univ hm
    (by simpa only [univ_inter] using hX) (fun x hx ↦ hX_in x hx.2)
  simpa only [univ_inter, forwardSemiflowDomain_eq_Ici_prod hglob] using h

end VariationalRegularity

end TauCeti

/-- **Local `C^m` forward semiflow of a vector field strictly inward at a point.** If `C` is a
closed convex subset of a Banach space `E`, `U` is open, `X` is `C^m` on `U ∩ C` (`1 ≤ m`,
including `m = ∞`), and `X x₀ ∈ strictInwardCone C x₀` at `x₀ ∈ U ∩ C`, then on a neighborhood
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)` there exists a jointly `C^m` map `Φ : ℝ → E → E` integrating `X`,
mapping positive times into `interior C`, and satisfying the local semiflow cocycle law. -/
theorem Convex.exists_contDiffOn_inwardSemiflow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    {x₀ : E} (hx₀ : x₀ ∈ U ∩ C) (hX_in : X x₀ ∈ TauCeti.strictInwardCone C x₀) :
    ∃ r > 0, ∃ τ > 0, ∃ Φ : ℝ → E → E,
      ball x₀ r ⊆ U ∧
      ContDiffOn ℝ m (uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) ∧
      (∀ y ∈ ball x₀ r ∩ C, Φ 0 y = y) ∧
      MapsTo (uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) (U ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Ioc 0 τ, Φ t y ∈ interior C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        HasDerivWithinAt (fun s ↦ Φ s y) (X (Φ t y)) (Icc 0 τ) t) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → t + s ≤ τ →
        Φ s y ∈ ball x₀ r → Φ (t + s) y = Φ t (Φ s y)) := by
  have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (mod_cast hm)
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨ε, hε, δ, hδ, hev⟩ := hC.exists_uniform_ball_subset_of_mem_strictInwardCone hX_in
  have hpair_cont : ContinuousWithinAt (fun y ↦ (y, X y)) (U ∩ C) x₀ :=
    continuousWithinAt_id.prodMk (hX1.continuousOn x₀ hx₀)
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp (hpair_cont.eventually hev)
  set r₀ := min rU rI
  have hr₀ : 0 < r₀ := lt_min hrU hrI
  set U' := ball x₀ r₀
  have hU'_sub : U' ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hballU
  have hX_U' : ContDiffOn ℝ m X (U' ∩ C) := hX.mono (inter_subset_inter_left C hU'_sub)
  have hX1_U' : ContDiffOn ℝ 1 X (U' ∩ C) := hX1.mono (inter_subset_inter_left C hU'_sub)
  have hX_lip_U' : LocallyLipschitzOn (U' ∩ C) X :=
    hC.locallyLipschitzOn_inter_of_contDiffOn isOpen_ball hX1_U'
  have hX_in_U' (y : E) (hy : y ∈ U' ∩ C) : X y ∈ TauCeti.strictInwardCone C y :=
    TauCeti.mem_strictInwardCone_iff.mpr ⟨ε, hε, δ, hδ,
      hballI ⟨ball_subset_ball (min_le_right _ _) hy.1, hU'_sub hy.1, hy.2⟩ hy.2⟩
  obtain ⟨r, hr, τ, hτ, _, _, h2rU', _, hsub, _, _, _, _⟩ :=
    TauCeti.exists_local_forwardSemiflow_continuousOn hC hC_closed isOpen_ball hX_lip_U'
      ⟨mem_ball_self hr₀, hx₀.2⟩ hX_in
  have hrU' : ball x₀ r ⊆ U' := (ball_subset_ball (by linarith)).trans h2rU'
  let Φ := TauCeti.forwardSemiflow X (U' ∩ C)
  have hdom : Icc 0 τ ×ˢ (ball x₀ r ∩ C) ⊆ TauCeti.forwardSemiflowDomain X (U' ∩ C) :=
    fun p hp ↦ TauCeti.mem_forwardSemiflowDomain_iff.mpr
      ⟨⟨hrU' hp.2.1, hp.2.2⟩, hsub p.2 hp.2 ⟨hp.1.1, by linarith [hp.1.2]⟩⟩
  refine ⟨r, hr, τ, hτ, Φ, hrU'.trans hU'_sub,
    (TauCeti.contDiffOn_forwardSemiflow hC hC_closed isOpen_ball hm hX_U' hX_in_U').mono hdom,
    fun y _ ↦ TauCeti.forwardSemiflow_zero _ _ _,
    fun p hp ↦ by
      have hpJ := (TauCeti.mem_forwardSemiflowDomain_iff.mp (hdom hp)).2
      exact ⟨hU'_sub (TauCeti.forwardSemiflow_mem hX_lip_U' hpJ).1,
        (TauCeti.forwardSemiflow_mem hX_lip_U' hpJ).2⟩,
    fun y hy t ht ↦ TauCeti.forwardSemiflow_mem_interior hC inter_subset_right hX_lip_U'
      hX_in_U' (hsub y hy ⟨ht.1.le, by linarith [ht.2]⟩) ht.1,
    fun y hy t ht ↦ (TauCeti.hasDerivWithinAt_forwardSemiflow hX_lip_U'
      (hsub y hy ⟨ht.1, by linarith [ht.2]⟩)).mono
        (fun s (hs : s ∈ Icc 0 τ) ↦ hsub y hy ⟨hs.1, by linarith [hs.2]⟩),
    fun y hy t s ht hs hts hΦs ↦ ?_⟩
  have hsJ : s ∈ TauCeti.forwardSemiflowInterval X (U' ∩ C) y :=
    hsub y hy ⟨hs, by linarith⟩
  have htJ : t ∈ TauCeti.forwardSemiflowInterval X (U' ∩ C) (Φ s y) :=
    hsub (Φ s y) ⟨hΦs, (TauCeti.forwardSemiflow_mem hX_lip_U' hsJ).2⟩ ⟨ht, by linarith⟩
  exact TauCeti.forwardSemiflow_add hX_lip_U' hsJ htJ

/-- **`C^m` inward deformation of a closed convex set into its interior.** Given a `C^m` (`1 ≤ m`,
including `m = ∞`) strictly inward vector field `X` on a closed convex set `C` whose forward
semiflow is defined on `[0, ∞)` for every `x ∈ C`, the time-`1` map
`r := forwardSemiflow X C 1` and the reparametrized semiflow
`H (t, x) := forwardSemiflow X C ((1 - t) ^ 2) x` deform `C` into `interior C` while preserving
`interior C` at every time. -/
theorem Convex.exists_contDiffOn_inward_deformation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X C)
    (hX_in : ∀ x ∈ C, X x ∈ TauCeti.strictInwardCone C x)
    (hglob : ∀ x ∈ C, TauCeti.forwardSemiflowInterval X C x = Ici 0) :
    ∃ (r : E → E) (H : ℝ × E → E),
      ContDiffOn ℝ m r C ∧
      MapsTo r C (interior C) ∧
      ContDiffOn ℝ m H (Icc 0 1 ×ˢ C) ∧
      (∀ x ∈ C, H (0, x) = r x) ∧
      (∀ x ∈ C, H (1, x) = x) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ C, H (t, x) ∈ interior C) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ interior C, H (t, x) ∈ interior C) := by
  have hCD := TauCeti.contDiffOn_forwardSemiflow_Ici hC hC_closed hm hX hX_in hglob
  have hX_lip : LocallyLipschitzOn C X := (hX.of_le (mod_cast hm)).locallyLipschitzOn hC
  let r : E → E := TauCeti.forwardSemiflow X C 1
  let H : ℝ × E → E := fun p ↦ TauCeti.forwardSemiflow X C ((1 - p.1) ^ 2) p.2
  have hreparam : ContDiffOn ℝ m (fun p : ℝ × E ↦ ((1 - p.1) ^ 2, p.2)) (Icc 0 1 ×ˢ C) :=
    ((contDiffOn_const.sub contDiffOn_fst).pow 2).prodMk contDiffOn_snd
  refine ⟨r, H,
    hCD.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx ↦ ⟨zero_le_one, hx⟩),
    fun x hx ↦ ?_,
    hCD.comp hreparam (fun p hp ↦ ⟨sq_nonneg _, hp.2⟩),
    fun x _ ↦ by simp [H, r],
    fun x _ ↦ by simp [H],
    fun t ht x hx ↦ ?_,
    fun t _ x hx ↦ ?_⟩
  · have hmem : (1 : ℝ) ∈ TauCeti.forwardSemiflowInterval X C x := by
      rw [hglob x hx]; exact zero_le_one
    exact TauCeti.forwardSemiflow_mem_interior hC Subset.rfl hX_lip hX_in hmem zero_lt_one
  · have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht.2)
    have hmem : (1 - t) ^ 2 ∈ TauCeti.forwardSemiflowInterval X C x := by
      rw [hglob x hx]; exact hpos.le
    exact TauCeti.forwardSemiflow_mem_interior hC Subset.rfl hX_lip hX_in hmem hpos
  · have hmem : (1 - t) ^ 2 ∈ TauCeti.forwardSemiflowInterval X C x := by
      rw [hglob x (interior_subset hx)]; exact sq_nonneg _
    exact TauCeti.forwardSemiflow_mem_interior_of_mem_interior hC Subset.rfl hX_lip hX_in hx hmem
