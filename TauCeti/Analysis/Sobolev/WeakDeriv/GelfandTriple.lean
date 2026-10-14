/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ExtendFrom

/-!
# Time-dependent functions in a Gelfand triple are continuous into the pivot space

Let `V ↪ H ↪ V*` be a Gelfand triple, given by a continuous linear map `ι : V →L[ℝ] H` into a
real Hilbert space `H` (`ContinuousLinearMap.gelfandDual`). Let `u ∈ L²(a, b; V)`, and suppose
that `u`, viewed in `V*` through `V → H → V*`, has a weak time derivative `u' ∈ L²(a, b; V*)`.
Neither `u` nor `ι ∘ u` is assumed to have any continuity in time. This file proves:

* `ι ∘ u` agrees almost everywhere on `(a, b)` with a function `w : ℝ → H` continuous on
  `[a, b]` (`TauCeti.HasWeakLineDerivOn.exists_continuousOn_ae_eq_of_gelfandDual`);
* every such `w` satisfies the **energy identity**
  `‖w t‖² - ‖w s‖² = 2 ∫ₛᵗ u'(r)(u r) dr` for all `s, t ∈ [a, b]`
  (`TauCeti.HasWeakLineDerivOn.norm_sq_sub_norm_sq_eq_of_gelfandDual`);
* and the bound `‖w t‖² ≤ ⨍_{(a, b)} ‖ι u‖² + 2 ∫_{(a, b)} |u'(u)|`, which controls
  `sup_t ‖w t‖` by the norms of `u` in `L²(a, b; V)` and of `u'` in `L²(a, b; V*)`
  (`TauCeti.HasWeakLineDerivOn.norm_sq_le_of_gelfandDual`).

Together these are the analytic content of the embedding `L²(a, b; V) ∩ H¹(a, b; V*) ↪
C([a, b]; H)`: a continuous representative exists, and its supremum norm is controlled by the
norms of `u` and `u'`. They are stated for pointwise representatives `u`, `u'`; packaging the
domain as a normed space and the representative as a bounded linear map is not done here.

This is the setting of linear parabolic equations: a weak solution of `u' + A u = f` lies in
`L²(0, T; H¹₀(Ω))` with `u' ∈ L²(0, T; H⁻¹(Ω))`, so it has a representative in
`C([0, T]; L²(Ω))`, which gives meaning to the initial condition `u(0) = u₀`, and its energy
identity yields uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

open MeasureTheory Filter Set Metric intervalIntegral
open scoped Interval Topology InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : V →L[ℝ] H} {a b : ℝ} {u : ℝ → V}
  {u' : ℝ → StrongDual ℝ V}

/-- **The oscillation estimate.** Suppose that at `s` and `s'` the functions `‖ι u‖²` and
`ι.gelfandDual ∘ ι ∘ u` agree with primitives of `2 u'(u)` and `u'` based at `t₀ ∈ (a, b)`. If
`s, s'` lie in an interval `(α, β) ⊆ (a, b)`, then
`‖ι u s - ι u s'‖² ≤ ∫_{(α, β)} (‖u'‖² + 2 ‖u‖²) + 2 (β - α) ‖u s'‖²`. -/
private theorem norm_sub_sq_le {t₀ c₁ α β s s' : ℝ} {c₂ : StrongDual ℝ V}
    (hp : IntegrableOn (fun r ↦ u' r (u r)) (Ioo a b)) (hu'i : IntegrableOn u' (Ioo a b))
    (hg : IntegrableOn (fun r ↦ ‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2) (Ioo a b))
    (hJ : Ioo α β ⊆ Ioo a b) (ht₀ : t₀ ∈ Ioo a b) (hs : s ∈ Ioo α β) (hs' : s' ∈ Ioo α β)
    (hs₁ : ‖ι (u s)‖ ^ 2 = c₁ + ∫ r in t₀..s, 2 * u' r (u r))
    (hs₂ : ι.gelfandDual (ι (u s)) = c₂ + ∫ r in t₀..s, u' r)
    (hs'₁ : ‖ι (u s')‖ ^ 2 = c₁ + ∫ r in t₀..s', 2 * u' r (u r))
    (hs'₂ : ι.gelfandDual (ι (u s')) = c₂ + ∫ r in t₀..s', u' r) :
    ‖ι (u s) - ι (u s')‖ ^ 2 ≤
      (∫ r in Ioo α β, (‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2)) + 2 * (β - α) * ‖u s'‖ ^ 2 := by
  have hsub {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : uIcc x y ⊆ Ioo a b :=
    ordConnected_Ioo.uIcc_subset hx hy
  have hp2 : IntegrableOn (fun r ↦ 2 * u' r (u r)) (Ioo a b) := hp.const_mul 2
  have hc : IntegrableOn (fun r ↦ 2 * u' r (u s')) (Ioo a b) :=
    ((ContinuousLinearMap.apply ℝ ℝ (u s')).integrable_comp hu'i).const_mul 2
  -- Expanding the square, `‖ι u s - ι u s'‖² = ∫_{s'}^{s} 2 u'(r)(u r - u s') dr`.
  have key : ‖ι (u s) - ι (u s')‖ ^ 2 = ∫ r in s'..s, (2 * u' r (u r) - 2 * u' r (u s')) := by
    have e₁ : ‖ι (u s)‖ ^ 2 - ‖ι (u s')‖ ^ 2 = ∫ r in s'..s, 2 * u' r (u r) := by
      rw [hs₁, hs'₁, add_sub_add_left_eq_sub, integral_interval_sub_left
        ((hp2.mono_set (hsub ht₀ (hJ hs))).intervalIntegrable)
        ((hp2.mono_set (hsub ht₀ (hJ hs'))).intervalIntegrable)]
    have e₂ : ⟪ι (u s), ι (u s')⟫_ℝ - ‖ι (u s')‖ ^ 2 = ∫ r in s'..s, u' r (u s') := by
      rw [← real_inner_self_eq_norm_sq, ← ι.gelfandDual_apply, ← ι.gelfandDual_apply, hs₂, hs'₂,
        ← sub_apply, add_sub_add_left_eq_sub, integral_interval_sub_left
          ((hu'i.mono_set (hsub ht₀ (hJ hs))).intervalIntegrable)
          ((hu'i.mono_set (hsub ht₀ (hJ hs'))).intervalIntegrable),
        ContinuousLinearMap.intervalIntegral_apply (φ := u')
          ((hu'i.mono_set (hsub (hJ hs') (hJ hs))).intervalIntegrable)]
    rw [norm_sub_sq_real, intervalIntegral.integral_sub
      ((hp2.mono_set (hsub (hJ hs') (hJ hs))).intervalIntegrable)
      ((hc.mono_set (hsub (hJ hs') (hJ hs))).intervalIntegrable), ← e₁,
      intervalIntegral.integral_const_mul, ← e₂]
    ring
  -- Pointwise, `|2 u'(r)(u r - u s')| ≤ ‖u' r‖² + 2 ‖u r‖² + 2 ‖u s'‖²`.
  have hpt (r : ℝ) : ‖2 * u' r (u r) - 2 * u' r (u s')‖ ≤
      ‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2 + 2 * ‖u s'‖ ^ 2 := by
    rw [← mul_sub, ← map_sub, norm_mul, Real.norm_two]
    have h₁ := (u' r).le_opNorm (u r - u s')
    have h₂ := norm_sub_le (u r) (u s')
    nlinarith [sq_nonneg (‖u' r‖ - ‖u r - u s'‖), sq_nonneg (‖u r‖ - ‖u s'‖), norm_nonneg (u' r),
      norm_nonneg (u r - u s'), norm_nonneg (u r), norm_nonneg (u s')]
  have hαβ : α ≤ β := (hs.1.trans hs.2).le
  have hG : IntegrableOn (fun r ↦ ‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2 + 2 * ‖u s'‖ ^ 2) (Ioo α β) :=
    (hg.mono_set hJ).add (integrableOn_const measure_Ioo_lt_top.ne)
  have hΙ : Ι s' s ⊆ Ioo α β := uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hs' hs)
  calc ‖ι (u s) - ι (u s')‖ ^ 2
      ≤ ‖∫ r in s'..s, (2 * u' r (u r) - 2 * u' r (u s'))‖ := key.le.trans (le_abs_self _)
    _ ≤ ∫ r in Ι s' s, ‖2 * u' r (u r) - 2 * u' r (u s')‖ := norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in Ι s' s, (‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2 + 2 * ‖u s'‖ ^ 2) :=
        setIntegral_mono_on (((hp2.sub hc).mono_set (hΙ.trans hJ)).norm) (hG.mono_set hΙ)
          measurableSet_uIoc fun r _ ↦ hpt r
    _ ≤ ∫ r in Ioo α β, (‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2 + 2 * ‖u s'‖ ^ 2) :=
        setIntegral_mono_set hG (Eventually.of_forall fun r ↦ by positivity)
          (Eventually.of_forall hΙ)
    _ = (∫ r in Ioo α β, (‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2)) + 2 * (β - α) * ‖u s'‖ ^ 2 := by
        rw [integral_add (hg.mono_set hJ) (integrableOn_const measure_Ioo_lt_top.ne),
          setIntegral_const, Real.volume_real_Ioo_of_le hαβ, smul_eq_mul]
        ring

/-- The integral of a function integrable on `(a, b)` over `(a, b) ∩ (x - δ, x + δ)` tends to zero
with `δ`. -/
private theorem exists_pos_setIntegral_Ioo_lt {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b)) (x : ℝ)
    {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∫ r in Ioo ((x - δ) ⊔ a) ((x + δ) ⊓ b), g r < η := by
  have hT : Tendsto (fun δ ↦ ∫ r in Ioo (x - δ) (x + δ), g r ∂volume.restrict (Ioo a b)) (𝓝 0)
      (𝓝 0) := by
    refine Integrable.tendsto_setIntegral_nhds_zero hg ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun δ ↦ ENNReal.ofReal (2 * δ)) ?_ (fun _ ↦ zero_le) fun δ ↦ ?_
    · have hc : Continuous fun δ : ℝ ↦ ENNReal.ofReal (2 * δ) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
      simpa using hc.tendsto 0
    · refine (Measure.restrict_apply_le _ _).trans_eq ?_
      dsimp only
      rw [Real.volume_Ioo]
      ring_nf
  obtain ⟨δ, hδ, hδη⟩ := Metric.tendsto_nhds_nhds.1 hT η hη
  refine ⟨δ / 2, by positivity, ?_⟩
  have h := @hδη (δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  rw [Real.dist_eq, sub_zero, Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo] at h
  exact (le_abs_self _).trans_lt h

variable [CompleteSpace V]

/-- **A time-dependent function in a Gelfand triple is continuous into the pivot space.** Let
`ι : V →L[ℝ] H` with `H` a Hilbert space, let `u ∈ L²(a, b; V)`, and suppose that
`t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)` on `(a, b)`. Then `ι ∘ u`
agrees almost everywhere on `(a, b)` with a function continuous on `[a, b]`. -/
theorem HasWeakLineDerivOn.exists_continuousOn_ae_eq_of_gelfandDual [CompleteSpace H]
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b))) :
    ∃ w : ℝ → H, ContinuousOn w (Icc a b) ∧ (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨0, continuousOn_const, by simp [Ioo_eq_empty (not_lt.2 hba), EventuallyEq]⟩
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hp : IntegrableOn (fun r ↦ u' r (u r)) (Ioo a b) :=
    memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu' hu)
  have hu'i : IntegrableOn u' (Ioo a b) := hu'.integrable one_le_two
  have hu2 : IntegrableOn (fun r ↦ ‖u r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hu'2 : IntegrableOn (fun r ↦ ‖u' r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hu'.aestronglyMeasurable).1 hu'
  -- Outside a measurable null set `N`, `‖ι u‖²` and `ι.gelfandDual ∘ ι ∘ u` are primitives of
  -- `2 u'(u)` and `u'` up to constants. Call `S₀` the remaining points of `(a, b)`.
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨c₁, hc₁⟩ := (h.norm_sq_of_gelfandDual hu hu').exists_ae_eq_add_intervalIntegral ht₀
  obtain ⟨c₂, hc₂⟩ := h.exists_ae_eq_add_intervalIntegral ht₀
  set P : ℝ → Prop := fun t ↦ ‖ι (u t)‖ ^ 2 = c₁ + ∫ r in (a + b) / 2..t, 2 * u' r (u r) ∧
    ι.gelfandDual (ι (u t)) = c₂ + ∫ r in (a + b) / 2..t, u' r with hP
  set N := toMeasurable volume {t | ¬(t ∈ Ioo a b → P t)} with hN_def
  have hN : volume N = 0 := by
    rw [hN_def, measure_toMeasurable, ← ae_iff]
    exact (ae_restrict_iff' measurableSet_Ioo).1 (hc₁.and hc₂)
  set S₀ := Ioo a b \ N with hS₀_def
  have hS₀ (t : ℝ) (ht : t ∈ S₀) : P t := by
    by_contra hc
    exact ht.2 (subset_toMeasurable _ _ fun h' ↦ hc (h' ht.1))
  -- On a subinterval `(α, β)`, some `s' ∈ S₀` is close to every point of `S₀ ∩ (α, β)`.
  have hosc (α β : ℝ) (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b) : ∃ s' ∈ S₀ ∩ Ioo α β,
      ∀ s ∈ S₀ ∩ Ioo α β, ‖ι (u s) - ι (u s')‖ ^ 2 ≤
        ∫ r in Ioo α β, (‖u' r‖ ^ 2 + 4 * ‖u r‖ ^ 2) := by
    have hJ : Ioo α β ⊆ Ioo a b := Ioo_subset_Ioo haα hβb
    have hK : S₀ ∩ Ioo α β = Ioo α β \ N := by
      ext t
      exact ⟨fun ⟨⟨_, htN⟩, ht⟩ ↦ ⟨ht, htN⟩, fun ⟨ht, htN⟩ ↦ ⟨⟨hJ ht, htN⟩, ht⟩⟩
    have hμK : volume (S₀ ∩ Ioo α β) = ENNReal.ofReal (β - α) := by
      rw [hK, measure_sdiff_null hN, Real.volume_Ioo]
    -- Choose `s'` with `‖u s'‖²` at most the average of `‖u‖²` over `(α, β)`.
    obtain ⟨s', hs'K, hs'le⟩ := exists_le_setAverage (μ := volume) (f := fun r ↦ ‖u r‖ ^ 2)
      (by rw [hμK]; simpa using hαβ) (by rw [hμK]; exact ENNReal.ofReal_ne_top)
      (hu2.mono_set (inter_subset_right.trans hJ))
    have hav : (β - α) * ‖u s'‖ ^ 2 ≤ ∫ r in Ioo α β, ‖u r‖ ^ 2 := by
      rw [setAverage_eq, measureReal_def, hμK, ENNReal.toReal_ofReal (sub_nonneg.2 hαβ.le),
        smul_eq_mul, setIntegral_congr_set (hK ▸ sdiff_null_ae_eq_self hN)] at hs'le
      have hpos := sub_pos.2 hαβ
      calc (β - α) * ‖u s'‖ ^ 2 ≤ (β - α) * ((β - α)⁻¹ * ∫ r in Ioo α β, ‖u r‖ ^ 2) := by
            gcongr
        _ = ∫ r in Ioo α β, ‖u r‖ ^ 2 := by field_simp
    refine ⟨s', hs'K, fun s hsK ↦ ?_⟩
    obtain ⟨hs₁, hs₂⟩ := hS₀ s hsK.1
    obtain ⟨hs'₁, hs'₂⟩ := hS₀ s' hs'K.1
    have hest := norm_sub_sq_le (ι := ι) hp hu'i (hu'2.add (hu2.const_mul 2)) hJ ht₀ hsK.2 hs'K.2
      hs₁ hs₂ hs'₁ hs'₂
    have hsplit : ∫ r in Ioo α β, (‖u' r‖ ^ 2 + 4 * ‖u r‖ ^ 2) =
        (∫ r in Ioo α β, (‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2)) + 2 * ∫ r in Ioo α β, ‖u r‖ ^ 2 := by
      have h₁ : IntegrableOn (fun r ↦ ‖u' r‖ ^ 2 + 2 * ‖u r‖ ^ 2) (Ioo α β) :=
        IntegrableOn.mono_set (hu'2.add (hu2.const_mul 2)) hJ
      have h₂ : IntegrableOn (fun r ↦ 2 * ‖u r‖ ^ 2) (Ioo α β) :=
        IntegrableOn.mono_set (hu2.const_mul 2) hJ
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add h₁ h₂]
      congr 1 with r
      ring
    linarith
  -- The oscillation of `ι ∘ u` on `S₀` near any point of `[a, b]` is small.
  have hL4 (x : ℝ) (hx : x ∈ Icc a b) (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ s ∈ S₀, ∀ r ∈ S₀,
      dist s x < δ → dist r x < δ → dist (ι (u s)) (ι (u r)) < ε := by
    obtain ⟨δ, hδ, hsm⟩ := exists_pos_setIntegral_Ioo_lt (hu'2.add (hu2.const_mul 4)) x
      (η := (ε / 2) ^ 2) (by positivity)
    have hαβ : (x - δ) ⊔ a < (x + δ) ⊓ b :=
      sup_lt_iff.2 ⟨lt_inf_iff.2 ⟨by linarith, by linarith [hx.2]⟩,
        lt_inf_iff.2 ⟨by linarith [hx.1], hab⟩⟩
    obtain ⟨s', hs'K, hs'⟩ := hosc _ _ le_sup_right hαβ inf_le_right
    have hclose (t : ℝ) (ht : t ∈ S₀) (hd : dist t x < δ) : dist (ι (u t)) (ι (u s')) < ε / 2 := by
      rw [Real.dist_eq, abs_lt] at hd
      have htK : t ∈ S₀ ∩ Ioo ((x - δ) ⊔ a) ((x + δ) ⊓ b) :=
        ⟨ht, by rw [← Ioo_inter_Ioo]; exact ⟨⟨by linarith, by linarith⟩, ht.1⟩⟩
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) ((hs' t htK).trans_lt hsm)
    refine ⟨δ, hδ, fun s hs r hr hsd hrd ↦ ?_⟩
    calc dist (ι (u s)) (ι (u r)) ≤ dist (ι (u s)) (ι (u s')) + dist (ι (u r)) (ι (u s')) :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hclose s hs hsd) (hclose r hr hrd)
      _ = ε := add_halves ε
  -- `S₀` is dense in `[a, b]`.
  have hdense : Icc a b ⊆ closure S₀ := by
    intro x hx
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    have hαβ : (x - ε) ⊔ a < (x + ε) ⊓ b :=
      sup_lt_iff.2 ⟨lt_inf_iff.2 ⟨by linarith, by linarith [hx.2]⟩,
        lt_inf_iff.2 ⟨by linarith [hx.1], hab⟩⟩
    obtain ⟨s', ⟨hs'S, hs'K⟩, -⟩ := hosc _ _ le_sup_right hαβ inf_le_right
    rw [← Ioo_inter_Ioo] at hs'K
    refine ⟨s', hs'S, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs'K.1.1, hs'K.1.2]
  -- Hence `ι ∘ u` has a limit along `S₀` at every point of `[a, b]`; extend it from `S₀`.
  have hlim (x : ℝ) (hx : x ∈ Icc a b) : ∃ y, Tendsto (fun t ↦ ι (u t)) (𝓝[S₀] x) (𝓝 y) := by
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hx)
    refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε ↦ ?_⟩)
    obtain ⟨δ, hδ, hosc'⟩ := hL4 x hx ε hε
    refine ⟨(fun t ↦ ι (u t)) '' (S₀ ∩ ball x δ),
      image_mem_map (inter_mem_nhdsWithin _ (ball_mem_nhds x hδ)), ?_⟩
    rintro _ ⟨s, ⟨hs, hsd⟩, rfl⟩ _ ⟨r, ⟨hr, hrd⟩, rfl⟩
    exact hosc' s hs r hr hsd hrd
  refine ⟨extendFrom S₀ (fun t ↦ ι (u t)), continuousOn_extendFrom hdense hlim, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with t htN htI
  have ht : t ∈ S₀ := ⟨htI, htN⟩
  refine (extendFrom_eq (subset_closure ht) (Metric.tendsto_nhdsWithin_nhds.2 fun ε hε ↦ ?_)).symm
  obtain ⟨δ, hδ, h'⟩ := hL4 t (Ioo_subset_Icc_self htI) ε hε
  exact ⟨δ, hδ, fun r hr hrd ↦ h' r hr t ht hrd (by simpa using hδ)⟩

/-- **The energy identity in a Gelfand triple.** Let `u ∈ L²(a, b; V)` be such that
`t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)` on `(a, b)`, and let `w` be
continuous on `[a, b]` and equal to `ι ∘ u` almost everywhere on `(a, b)`. Then for all
`s, t ∈ [a, b]`, `‖w t‖² - ‖w s‖² = 2 ∫ₛᵗ u'(r)(u r) dr`. -/
theorem HasWeakLineDerivOn.norm_sq_sub_norm_sq_eq_of_gelfandDual
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    {w : ℝ → H} (hw : ContinuousOn w (Icc a b))
    (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    ‖w t‖ ^ 2 - ‖w s‖ ^ 2 = 2 * ∫ r in s..t, u' r (u r) := by
  have hp : IntegrableOn (fun r ↦ u' r (u r)) (Ioo a b) :=
    memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu' hu)
  rw [← intervalIntegral.integral_const_mul]
  exact ((h.norm_sq_of_gelfandDual hu hu').integral_eq_sub (hp.const_mul 2) (hw.norm.pow 2)
    (hae.fun_comp fun y ↦ ‖y‖ ^ 2) hs ht).symm

/-- **The `C([a, b]; H)` bound in a Gelfand triple.** Let `a < b`, let `u ∈ L²(a, b; V)` be such
that `t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)` on `(a, b)`, and let `w`
be continuous on `[a, b]` and equal to `ι ∘ u` almost everywhere on `(a, b)`. Then at every
`t ∈ [a, b]`, `‖w t‖² ≤ ⨍_{(a, b)} ‖ι u‖² + 2 ∫_{(a, b)} |u'(u)|`. -/
theorem HasWeakLineDerivOn.norm_sq_le_of_gelfandDual
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hab : a < b) (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo a b))) {w : ℝ → H} (hw : ContinuousOn w (Icc a b))
    (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖w t‖ ^ 2 ≤ (⨍ s in Ioo a b, ‖ι (u s)‖ ^ 2) + 2 * ∫ s in Ioo a b, |u' s (u s)| := by
  have hp : IntegrableOn (fun r ↦ u' r (u r)) (Ioo a b) :=
    memLp_one_iff_integrable.1 ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu' hu)
  have := (h.norm_sq_of_gelfandDual hu hu').norm_le_setAverage_add_integral hab
    (hp.const_mul 2) (hw.norm.pow 2) (hae.fun_comp fun y ↦ ‖y‖ ^ 2) ht
  simpa [MeasureTheory.integral_const_mul] using this

end TauCeti
