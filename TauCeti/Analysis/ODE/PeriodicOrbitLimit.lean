/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz

/-!
# Loops with square-integrable defect accumulate at periodic orbits

Let `X : ℝ → V → V` be a continuous time-dependent vector field on a real Banach space,
`1`-periodic in time, and let `u : ℝ × ℝ → V` be a `C¹` map on the half-cylinder `s > a`
whose loops `t ↦ u(s, t)` are `1`-periodic and stay in a compact set. Measure how far the loop at
`s` is from solving `x' = X(t, x)` by the *defect* `∂_t u(s, t) - X(t, u(s, t))`. If the square of
its norm has finite integral over the half-cylinder `(a, ∞) × [0, 1]`, then:

* there are `s_n → ∞` along which the `L²` norm of the defect over the loop tends to `0`
  (`TauCeti.exists_tendsto_integral_norm_sq_sliceDefect`);
* along any such sequence, a subsequence of the loops `t ↦ u(s_n, t)` converges uniformly to a
  `1`-periodic solution of `x' = X(t, x)`
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral`).

Together these give a periodic solution and a sequence `s_n → ∞` along which the loops converge
to it uniformly (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`).

The second statement is an application of the Arzelà–Ascoli theorem: by the Cauchy–Schwarz
inequality (`TauCeti.integral_le_sqrt_mul_sqrt_integral_sq`), once the squared defect integrals
are at most `1` the loops have the common modulus of continuity `B h + √h`, where `B` bounds `X`
on the compact set, and the integral equation `x(t) - x(0) = ∫₀ᵗ X(τ, x(τ)) dτ` passes to the limit
because the integral of the defect tends to `0`.

This is the step of the asymptotic analysis of Floer trajectories that produces the periodic orbit
at an end: for a solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a
cylindrical end, the defect is `J ∂_s u`, and its square integral is controlled by the energy.
No regularity beyond `C¹`, and no bound on the derivative of `u`, is assumed.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, the convergence of finite-energy Floer trajectories to periodic
  orbits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {X : ℝ → V → V} {u : ℝ × ℝ → V} {a : ℝ}

section Slice

/-- The `t`-slices of a map differentiable at `z` have derivative `∂_t u(z) = du(z)(0, 1)`. -/
theorem _root_.DifferentiableAt.hasDerivAt_slice_snd {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z) :
    HasDerivAt (fun t ↦ u (z.1, t)) (fderiv ℝ u z (0, 1)) z.2 := by
  have hc : HasDerivAt (fun t : ℝ ↦ (z.1, t)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact hu.hasFDerivAt.comp_hasDerivAt z.2 hc

/-- On the half-cylinder `s > a`, a `C¹` map has continuous partial derivative
`∂_t u(z) = du(z)(0, 1)`. -/
private theorem continuousOn_fderiv_apply_slice (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) :
    ContinuousOn (fun z ↦ fderiv ℝ u z (0, 1)) (Ioi a ×ˢ univ) :=
  ((hu.continuousOn_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) le_rfl).clm_apply
    continuousOn_const)

end Slice

/-- The defect `∂_t u(z) - X(t, u(z))` of a map `u` from solving the time-dependent equation
`x' = X(t, x)` along its `t`-slices, at `z = (s, t)`. -/
noncomputable def sliceDefect (X : ℝ → V → V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ u z (0, 1) - X z.2 (u z)

theorem sliceDefect_def (X : ℝ → V → V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    sliceDefect X u z = fderiv ℝ u z (0, 1) - X z.2 (u z) :=
  (rfl)

/-- The defect of a `C¹` map is continuous on the half-cylinder, for a continuous vector field. -/
theorem continuousOn_sliceDefect (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) : ContinuousOn (sliceDefect X u) (Ioi a ×ˢ univ) :=
  (continuousOn_fderiv_apply_slice hu).sub <|
    hX.comp_continuousOn (continuousOn_snd.prodMk hu.continuousOn)

/-- The squared norm of the defect along one loop is continuous in `t`. -/
theorem continuous_norm_sliceDefect_sq (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) :
    Continuous fun t ↦ ‖sliceDefect X u (s, t)‖ ^ 2 := by
  have h := (continuousOn_sliceDefect hu hX).comp_continuous
    (continuous_const.prodMk continuous_id) fun t ↦ ⟨hs, mem_univ t⟩
  exact (h.norm.pow 2)

section Selection

/-- **Loops with small defect.** If the squared defect has finite integral over the half-cylinder
`(a, ∞) × [0, 1]`, then there are `s_n → ∞`, with `s_n > a`, along which the `L²` norm of the
defect over the loop at `s_n` tends to `0`. -/
theorem exists_tendsto_integral_norm_sq_sliceDefect
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X))
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤) :
    ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
      Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0) := by
  set f : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)
  -- Tonelli: the integral over the half-cylinder is the iterated integral.
  have hmeas :
      AEMeasurable f ((volume.restrict (Ioi a)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine (ENNReal.continuous_ofReal.comp_continuousOn
      (((continuousOn_sliceDefect hu hX).norm.pow 2).mono ?_)).aemeasurable
      (measurableSet_Ioi.prod measurableSet_Icc)
    exact prod_mono le_rfl (subset_univ _)
  have hiter : ∫⁻ s in Ioi a, ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) ≠ ⊤ := by
    rwa [← lintegral_prod f hmeas, Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- The inner integral is the real integral of the squared defect over the loop.
  have hinner : ∀ s, a < s → ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
    intro s hs
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal
        ((continuous_norm_sliceDefect_sq hu hX hs).integrableOn_Icc)
        (Eventually.of_forall fun t ↦ sq_nonneg _)]
  -- For every `S` and `ε > 0` some loop beyond `S` has squared defect integral below `ε`.
  have hsel : ∀ (S ε : ℝ), 0 < ε → ∃ s, S < s ∧ a < s ∧
      ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2 < ε := by
    intro S ε hε
    by_contra! h
    refine hiter (eq_top_iff.2 ?_)
    calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ioi (max S a), ENNReal.ofReal ε := by
          rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (by simpa using hε)]
      _ ≤ ∫⁻ s in Ioi (max S a), ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ?_
          have hs' : S < s ∧ a < s := max_lt_iff.1 hs
          rw [hinner s hs'.2]
          exact ENNReal.ofReal_le_ofReal (h s hs'.1 hs'.2)
      _ ≤ ∫⁻ s in Ioi a, ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) :=
          lintegral_mono_set (Ioi_subset_Ioi (le_max_right S a))
  choose φ hφS hφa hφε using fun n : ℕ ↦ hsel n (1 / (n + 1)) Nat.one_div_pos_of_nat
  refine ⟨φ, hφa, tendsto_atTop_mono (fun n ↦ (hφS n).le) tendsto_natCast_atTop_atTop, ?_⟩
  refine squeeze_zero (fun n ↦ intervalIntegral.integral_nonneg zero_le_one
    fun t _ ↦ sq_nonneg _) (fun n ↦ (hφε n).le) tendsto_one_div_add_atTop_nhds_zero_nat

end Selection

section Modulus

/-- **A modulus of continuity for loops with small defect.** If `X` is bounded by `B` along the
loop at `s` on `[t₁, t₂]`, then
`‖u(s, t₂) - u(s, t₁)‖ ≤ B (t₂ - t₁) + √(t₂ - t₁) √(∫_{t₁}^{t₂} ‖∂_t u - X(t, u)‖²)`. -/
theorem norm_sub_le_add_sqrt_mul_sqrt_integral_sliceDefect [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s)
    {B t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (hB : ∀ t ∈ Icc t₁ t₂, ‖X t (u (s, t))‖ ≤ B) :
    ‖u (s, t₂) - u (s, t₁)‖ ≤
      B * (t₂ - t₁) + √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) := by
  have hmem : ∀ t : ℝ, (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := fun t ↦ ⟨hs, mem_univ t⟩
  have hderiv : ∀ t, HasDerivAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t := fun t ↦
    ((hu.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds (hmem t))).hasDerivAt_slice_snd
  have hcont : Continuous fun t ↦ fderiv ℝ u (s, t) (0, 1) :=
    (continuousOn_fderiv_apply_slice hu).comp_continuous
      (continuous_const.prodMk continuous_id) hmem
  have hd : Continuous fun t ↦ ‖sliceDefect X u (s, t)‖ :=
    ((continuousOn_sliceDefect hu hX).comp_continuous
      (continuous_const.prodMk continuous_id) hmem).norm
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable _ _)]
  calc ‖∫ t in t₁..t₂, fderiv ℝ u (s, t) (0, 1)‖
      ≤ ∫ t in t₁..t₂, ‖fderiv ℝ u (s, t) (0, 1)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ t in t₁..t₂, (B + ‖sliceDefect X u (s, t)‖) := by
        refine intervalIntegral.integral_mono_on ht (hcont.norm.intervalIntegrable _ _)
          (continuous_const.add hd |>.intervalIntegrable _ _) fun t htI ↦ ?_
        have h : fderiv ℝ u (s, t) (0, 1) = X t (u (s, t)) + sliceDefect X u (s, t) := by
          rw [sliceDefect_def, add_sub_cancel]
        rw [h]
        exact (norm_add_le _ _).trans (add_le_add_left (hB t htI) _)
    _ = B * (t₂ - t₁) + ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hd.intervalIntegrable _ _),
          intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ B * (t₂ - t₁) + √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) :=
        add_le_add le_rfl (integral_le_sqrt_mul_sqrt_integral_sq ht (fun t _ ↦ norm_nonneg _)
          (hd.intervalIntegrable _ _) ((hd.pow 2).intervalIntegrable _ _))

end Modulus

section Limit

/-- A `1`-periodic function takes the same value at `t` and at its fractional part. -/
theorem _root_.Function.Periodic.apply_fract {β : Type*} {f : ℝ → β} (hf : Periodic f 1)
    (t : ℝ) : f (Int.fract t) = f t := by
  simpa [Int.self_sub_floor] using hf.sub_int_mul_eq (x := t) ⌊t⌋

/-- **Loops with small defect converge to periodic orbits.** Let `X` be a continuous,
`1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`. If `s_n > a` and the `L²` norm of the defect
`∂_t u - X(t, u)` over the loop at `s_n` tends to `0`, then a subsequence of the loops
`t ↦ u(s_n, t)` converges uniformly to a `1`-periodic solution `x` of `x' = X(t, x)`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    {K : Set V} (hK : IsCompact K) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    {φ : ℕ → ℝ} (hφa : ∀ n, a < φ n)
    (hφ : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      TendstoUniformly (fun n t ↦ u (φ (ψ n), t)) x atTop := by
  have hmem : ∀ s, a < s → ∀ t : ℝ, (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) :=
    fun s hs t ↦ ⟨hs, mem_univ t⟩
  have hloop : ∀ s, a < s → Continuous fun t ↦ u (s, t) := fun s hs ↦
    hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (hmem s hs)
  -- A bound for `X` on `[0, 1] × K`.
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hX.continuousOn
  have hBu : ∀ s, a < s → ∀ t ∈ Icc (0 : ℝ) 1, ‖X t (u (s, t))‖ ≤ B := fun s hs t ht ↦
    hB (t, u (s, t)) ⟨ht, huK s hs t⟩
  -- Pass to the tail of the sequence on which the squared defect integral is at most `1`.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφ.eventually (gt_mem_nhds zero_lt_one))
  set y : ℕ → ℝ → V := fun n t ↦ u (φ (N + n), t)
  -- The loops share the modulus of continuity `h ↦ B h + √h` on `[0, 1]`.
  have hmod : ∀ n, ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1, t₁ ≤ t₂ →
      dist (y n t₂) (y n t₁) ≤ B * (t₂ - t₁) + √(t₂ - t₁) := by
    intro n t₁ ht₁ t₂ ht₂ ht
    have hs := hφa (N + n)
    rw [dist_eq_norm]
    refine (norm_sub_le_add_sqrt_mul_sqrt_integral_sliceDefect hu hX hs ht
      fun t htI ↦ hBu _ hs t ⟨ht₁.1.trans htI.1, htI.2.trans ht₂.2⟩).trans ?_
    have hle : ∫ t in t₁..t₂, ‖sliceDefect X u (φ (N + n), t)‖ ^ 2 ≤ 1 :=
      (intervalIntegral.integral_mono_interval ht₁.1 ht ht₂.2
        (Eventually.of_forall fun t ↦ sq_nonneg _)
        ((continuous_norm_sliceDefect_sq hu hX hs).intervalIntegrable _ _)).trans
        (hN _ (Nat.le_add_right N n)).le
    exact add_le_add le_rfl (mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (Real.sqrt_le_one.mpr hle))
  -- Arzelà–Ascoli on `C([0, 1], V)`.
  let G : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) 1) V := fun n ↦
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t ↦ y n t, (hloop _ (hφa (N + n))).comp continuous_subtype_val⟩
  have hGK : ∀ f x, f ∈ range G → f x ∈ K := by
    rintro _ x ⟨n, rfl⟩
    exact huK _ (hφa (N + n)) x
  have hGeq : Equicontinuous ((↑) : range G → Icc (0 : ℝ) 1 → V) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun h ↦ B * h + √h) ?_ _ ?_
    · have hb : Continuous fun h : ℝ ↦ B * h + √h :=
        (continuous_const.mul continuous_id).add Real.continuous_sqrt
      simpa using hb.tendsto 0
    · rintro t₁ t₂ ⟨_, n, rfl⟩
      rw [Subtype.dist_eq, Real.dist_eq]
      rcases le_total (t₁ : ℝ) t₂ with h | h
      · rw [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
        exact hmod n t₁ t₁.2 t₂ t₂.2 h
      · rw [abs_of_nonneg (sub_nonneg.2 h)]
        exact hmod n t₂ t₂.2 t₁ t₁.2 h
  obtain ⟨g, -, ψ', hψ', hlim⟩ :=
    (BoundedContinuousFunction.arzela_ascoli K hK (range G) hGK hGeq).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  have hunif := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hlim
  set ψ : ℕ → ℕ := fun n ↦ N + ψ' n
  have hψ : StrictMono ψ := fun m n h ↦ Nat.add_lt_add_left (hψ' h) N
  -- The limit loop, extended periodically.
  let p : ℝ → Icc (0 : ℝ) 1 := fun t ↦ ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  set x : ℝ → V := fun t ↦ g (p t)
  have hxper : Periodic x 1 := fun t ↦ by simp only [x, p, Int.fract_add_one]
  have hux : TendstoUniformly (fun n t ↦ u (φ (ψ n), t)) x atTop := by
    have heq : (fun n t ↦ u (φ (ψ n), t)) = fun n ↦ ⇑((G ∘ ψ') n) ∘ p := by
      funext n t
      exact ((hper _ (hφa _)).apply_fract t).symm
    rw [heq]
    exact hunif.comp p
  have hxcont : Continuous x :=
    hux.continuous (Frequently.of_forall fun n ↦ hloop _ (hφa _))
  have hpt : ∀ t, Tendsto (fun n ↦ u (φ (ψ n), t)) atTop (𝓝 (x t)) := hux.tendsto_at
  have hdef : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ (ψ n), t)‖ ^ 2) atTop
      (𝓝 0) := hφ.comp (tendsto_atTop_mono (fun n ↦ Nat.le_add_left _ N) hψ'.tendsto_atTop)
  -- The integral equation on `[0, 1]`.
  set Y : ℝ → V := fun t ↦ X t (x t)
  have hYcont : Continuous Y := hX.comp (continuous_id.prodMk hxcont)
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, x t - x 0 = ∫ τ in (0 : ℝ)..t, Y τ := by
    intro t ht
    -- Along the sequence, `u(s, t) - u(s, 0) = ∫₀ᵗ X(τ, u(s, τ)) dτ + ∫₀ᵗ (defect)`.
    have hsplit : ∀ n, u (φ (ψ n), t) - u (φ (ψ n), 0) =
        (∫ τ in (0 : ℝ)..t, X τ (u (φ (ψ n), τ))) +
          ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ (ψ n), τ) := by
      intro n
      have hs := hφa (ψ n)
      have hX' : Continuous fun τ ↦ X τ (u (φ (ψ n), τ)) :=
        hX.comp (continuous_id.prodMk (hloop _ hs))
      have hd : Continuous fun τ ↦ sliceDefect X u (φ (ψ n), τ) :=
        (continuousOn_sliceDefect hu hX).comp_continuous
          (continuous_const.prodMk continuous_id) (hmem _ hs)
      rw [← intervalIntegral.integral_add (hX'.intervalIntegrable _ _)
        (hd.intervalIntegrable _ _)]
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ ↦ u (φ (ψ n), τ))
        (f' := fun τ ↦ X τ (u (φ (ψ n), τ)) + sliceDefect X u (φ (ψ n), τ))
        (fun τ _ ↦ ?_) ?_).symm
      · simp only [sliceDefect_def, add_sub_cancel]
        exact ((hu.differentiableOn one_ne_zero).differentiableAt
          ((isOpen_Ioi.prod isOpen_univ).mem_nhds (hmem _ hs τ))).hasDerivAt_slice_snd
      · exact (hX'.add hd).intervalIntegrable _ _
    -- The first integral converges by dominated convergence.
    have hA : Tendsto (fun n ↦ ∫ τ in (0 : ℝ)..t, X τ (u (φ (ψ n), τ))) atTop
        (𝓝 (∫ τ in (0 : ℝ)..t, Y τ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
        (Eventually.of_forall fun n ↦ (hX.comp (continuous_id.prodMk
          (hloop _ (hφa (ψ n))))).aestronglyMeasurable)
        (Eventually.of_forall fun n ↦ Eventually.of_forall fun τ hτ ↦ ?_)
        intervalIntegrable_const
        (Eventually.of_forall fun τ _ ↦ ((hX.tendsto (τ, x τ)).comp
          (tendsto_const_nhds.prodMk_nhds (hpt τ))))
      rw [uIoc_of_le ht.1] at hτ
      exact hBu _ (hφa _) τ ⟨hτ.1.le, hτ.2.trans ht.2⟩
    -- The second integral tends to `0` by the Cauchy–Schwarz inequality.
    have hD : Tendsto (fun n ↦ ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ (ψ n), τ)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n ↦
          √(∫ τ in (0 : ℝ)..1, ‖sliceDefect X u (φ (ψ n), τ)‖ ^ 2)) atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hdef
        rw [Real.sqrt_zero] at h
        exact h
      refine squeeze_zero_norm (fun n ↦ ?_) hsq
      have hs := hφa (ψ n)
      have hd : Continuous fun τ ↦ ‖sliceDefect X u (φ (ψ n), τ)‖ :=
        ((continuousOn_sliceDefect hu hX).comp_continuous
          (continuous_const.prodMk continuous_id) (hmem _ hs)).norm
      calc ‖∫ τ in (0 : ℝ)..t, sliceDefect X u (φ (ψ n), τ)‖
          ≤ ∫ τ in (0 : ℝ)..t, ‖sliceDefect X u (φ (ψ n), τ)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.1
        _ ≤ √(t - 0) * √(∫ τ in (0 : ℝ)..t, ‖sliceDefect X u (φ (ψ n), τ)‖ ^ 2) :=
            integral_le_sqrt_mul_sqrt_integral_sq ht.1 (fun τ _ ↦ norm_nonneg _)
              (hd.intervalIntegrable _ _) ((hd.pow 2).intervalIntegrable _ _)
        _ ≤ 1 * √(∫ τ in (0 : ℝ)..1, ‖sliceDefect X u (φ (ψ n), τ)‖ ^ 2) := by
            gcongr
            · exact Real.sqrt_le_one.mpr (by linarith [ht.2])
            · exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
                (Eventually.of_forall fun τ ↦ sq_nonneg _) ((hd.pow 2).intervalIntegrable _ _)
        _ = _ := one_mul _
    have hL : Tendsto (fun n ↦ u (φ (ψ n), t) - u (φ (ψ n), 0)) atTop (𝓝 (x t - x 0)) :=
      (hpt t).sub (hpt 0)
    simp_rw [hsplit] at hL
    simpa using (tendsto_nhds_unique (hA.add hD) hL).symm
  -- The integral equation on all of `ℝ`, by periodicity.
  have hYper : Periodic Y 1 := fun t ↦ by simp only [Y, hxper t, hXper (x t) t]
  have hint1 : ∫ τ in (0 : ℝ)..1, Y τ = 0 := by
    rw [← hint 1 ⟨zero_le_one, le_rfl⟩, show (1 : ℝ) = 0 + 1 by ring, hxper 0, sub_self]
  have hall : ∀ t, x t = x 0 + ∫ τ in (0 : ℝ)..t, Y τ := by
    set Φ : ℝ → V := fun t ↦ x 0 + (∫ τ in (0 : ℝ)..t, Y τ) - x t
    have hΦper : Periodic Φ 1 := fun t ↦ by
      have h := hYper.intervalIntegral_add_eq t 0
      rw [zero_add, hint1] at h
      simp only [Φ, hxper t]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hYcont.intervalIntegrable 0 t)
        (hYcont.intervalIntegrable t (t + 1)), h, add_zero]
    intro t
    have h0 : Φ (Int.fract t) = 0 := by
      have h := hint (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
      simp only [Φ]
      rw [← h]
      abel
    rw [hΦper.apply_fract] at h0
    exact (sub_eq_zero.1 h0).symm
  refine ⟨ψ, hψ, x, hxper, fun t ↦ ?_, hux⟩
  have h := ((intervalIntegral.integral_hasDerivAt_right (hYcont.intervalIntegrable 0 t)
    (hYcont.stronglyMeasurableAtFilter _ _) hYcont.continuousAt).const_add (x 0))
  exact h.congr_of_eventuallyEq (Eventually.of_forall hall)

/-- **Loops with square-integrable defect accumulate at periodic orbits.** Let `X` be a
continuous, `1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder
`s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set. If the squared norm of the defect
`∂_t u - X(t, u)` has finite integral over `(a, ∞) × [0, 1]`, then there are a `1`-periodic
solution `x` of `x' = X(t, x)` and `s_n → ∞`, with `s_n > a`, such that the loops
`t ↦ u(s_n, t)` converge uniformly to `x` and the `L²` norms of the defect over them tend to
`0`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    {K : Set V} (hK : IsCompact K) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨φ, hφa, hφ, hdef⟩ := exists_tendsto_integral_norm_sq_sliceDefect hu hX hfin
  obtain ⟨ψ, hψ, x, hxper, hx, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral hu hper hK huK hX hXper hφa
      hdef
  exact ⟨x, hxper, hx, φ ∘ ψ, fun n ↦ hφa (ψ n), hφ.comp hψ.tendsto_atTop, hux,
    hdef.comp hψ.tendsto_atTop⟩

end Limit

end TauCeti
