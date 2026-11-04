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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
because the integral of the defect tends to `0`
(`TauCeti.sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect`).

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

/-- On the half-cylinder `s > a`, the loops `t ↦ f(s, t)` of a continuous map are continuous. -/
theorem continuous_slice_of_continuousOn {Y : Type*} [TopologicalSpace Y] {f : ℝ × ℝ → Y}
    (hf : ContinuousOn f (Ioi a ×ˢ univ)) {s : ℝ} (hs : a < s) : Continuous fun t ↦ f (s, t) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) fun t ↦ ⟨hs, mem_univ t⟩

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
  ((hu.continuousOn_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) le_rfl).clm_apply
    continuousOn_const).sub <| hX.comp_continuousOn (continuousOn_snd.prodMk hu.continuousOn)

/-- The defect along one loop of a `C¹` map is continuous in `t`. -/
theorem continuous_sliceDefect_slice (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) :
    Continuous fun t ↦ sliceDefect X u (s, t) :=
  continuous_slice_of_continuousOn (continuousOn_sliceDefect hu hX) hs

/-- The squared norm of the defect along one loop is continuous in `t`. -/
theorem continuous_norm_sliceDefect_sq (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) :
    Continuous fun t ↦ ‖sliceDefect X u (s, t)‖ ^ 2 :=
  (continuous_sliceDefect_slice hu hX hs).norm.pow 2

/-- Along the loop at `s > a`, a map differentiable on the half-cylinder has `t`-derivative
`X(t, u(s, t))` plus the defect. -/
theorem hasDerivAt_slice_add_sliceDefect (hu : DifferentiableOn ℝ u (Ioi a ×ˢ univ)) {s : ℝ}
    (hs : a < s) (t : ℝ) :
    HasDerivAt (fun t ↦ u (s, t)) (X t (u (s, t)) + sliceDefect X u (s, t)) t := by
  rw [sliceDefect_def, add_sub_cancel]
  have hmem : (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ t⟩
  exact (hu.differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)).hasDerivAt_slice_snd

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
  have hXc : Continuous fun t ↦ X t (u (s, t)) :=
    hX.comp (continuous_id.prodMk (continuous_slice_of_continuousOn hu.continuousOn hs))
  have hd := continuous_sliceDefect_slice hu hX hs
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) hs t)
    ((hXc.add hd).intervalIntegrable _ _)]
  calc ‖∫ t in t₁..t₂, (X t (u (s, t)) + sliceDefect X u (s, t))‖
      ≤ ∫ t in t₁..t₂, ‖X t (u (s, t)) + sliceDefect X u (s, t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ t in t₁..t₂, (B + ‖sliceDefect X u (s, t)‖) := by
        refine intervalIntegral.integral_mono_on ht ((hXc.add hd).norm.intervalIntegrable _ _)
          (continuous_const.add hd.norm |>.intervalIntegrable _ _) fun t htI ↦ ?_
        exact (norm_add_le _ _).trans (add_le_add_left (hB t htI) _)
    _ = B * (t₂ - t₁) + ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hd.norm.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ B * (t₂ - t₁) + √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) :=
        add_le_add le_rfl (integral_le_sqrt_mul_sqrt_integral_sq ht (fun t _ ↦ norm_nonneg _)
          ((hd.norm.pow 2).intervalIntegrable _ _))

/-- **The defect integral is controlled by its `L²` norm.** Over a subinterval `[t₁, t₂]` of
`[0, 1]`, the integral of the norm of the defect along the loop at `s > a` is at most the `L²` norm
of the defect over `[0, 1]`. -/
theorem integral_norm_sliceDefect_le_sqrt (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) {t₁ t₂ : ℝ} (h₀ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (h₁ : t₂ ≤ 1) :
    ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ≤
      √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
  have hd := continuous_norm_sliceDefect_sq hu hX hs
  calc ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖
      ≤ √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) :=
        integral_le_sqrt_mul_sqrt_integral_sq ht (fun t _ ↦ norm_nonneg _)
          (hd.intervalIntegrable _ _)
    _ ≤ 1 * √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
        gcongr
        · exact Real.sqrt_le_one.mpr (by linarith)
        · exact intervalIntegral.integral_mono_interval h₀ ht h₁
            (Eventually.of_forall fun t ↦ sq_nonneg _) (hd.intervalIntegrable _ _)
    _ = _ := one_mul _

end Modulus

section Limit

/-- **The integral equation passes to the limit.** Let `X` be continuous and let `u` be `C¹` on
the half-cylinder `s > a`, with loops in a compact set `K`. If the loops at `s_i > a` converge
pointwise to `x` and the `L²` norms of their defects tend to `0`, then
`x(t) - x(0) = ∫₀ᵗ X(τ, x(τ)) dτ` for `t ∈ [0, 1]`. -/
theorem sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) {K : Set V} (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hX : Continuous (uncurry X)) {ι : Type*}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {φ : ι → ℝ} (hφa : ∀ i, a < φ i)
    (hφ : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ i, t)‖ ^ 2) l (𝓝 0))
    {x : ℝ → V} (hx : ∀ t, Tendsto (fun i ↦ u (φ i, t)) l (𝓝 (x t))) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    x t - x 0 = ∫ τ in (0 : ℝ)..t, X τ (x τ) := by
  have hloop : ∀ i, Continuous fun τ ↦ u (φ i, τ) := fun i ↦
    continuous_slice_of_continuousOn hu.continuousOn (hφa i)
  -- Along the sequence, `u(s, t) - u(s, 0) = ∫₀ᵗ X(τ, u(s, τ)) dτ + ∫₀ᵗ (defect)`.
  have hsplit : ∀ i, u (φ i, t) - u (φ i, 0) =
      (∫ τ in (0 : ℝ)..t, X τ (u (φ i, τ))) + ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ i, τ) := by
    intro i
    have hX' : Continuous fun τ ↦ X τ (u (φ i, τ)) := hX.comp (continuous_id.prodMk (hloop i))
    have hd := continuous_sliceDefect_slice hu hX (hφa i)
    rw [← intervalIntegral.integral_add (hX'.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ _ ↦ hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) (hφa i) τ)
      ((hX'.add hd).intervalIntegrable _ _)).symm
  -- The first integral converges by dominated convergence.
  have hA : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, X τ (u (φ i, τ))) l
      (𝓝 (∫ τ in (0 : ℝ)..t, X τ (x τ))) :=
    tendsto_intervalIntegral_comp_of_tendsto (Φ := uncurry X) (y := fun i τ ↦ u (φ i, τ)) hX hK
      (fun i ↦ (hloop i).continuousOn) (fun i τ _ ↦ huK _ (hφa i) τ) fun τ _ ↦ hx τ
  -- The second integral tends to `0` by the Cauchy–Schwarz inequality.
  have hD : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ i, τ)) l (𝓝 0) := by
    have hsq : Tendsto (fun i ↦
        √(∫ τ in (0 : ℝ)..1, ‖sliceDefect X u (φ i, τ)‖ ^ 2)) l (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hφ
      rw [Real.sqrt_zero] at h
      exact h
    exact squeeze_zero_norm (fun i ↦ (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
      (integral_norm_sliceDefect_le_sqrt hu hX (hφa i) le_rfl ht.1 ht.2)) hsq
  have hL : Tendsto (fun i ↦ u (φ i, t) - u (φ i, 0)) l (𝓝 (x t - x 0)) := (hx t).sub (hx 0)
  simp_rw [hsplit] at hL
  simpa using (tendsto_nhds_unique (hA.add hD) hL).symm

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
  have hloop : ∀ s, a < s → Continuous fun t ↦ u (s, t) := fun s hs ↦
    continuous_slice_of_continuousOn hu.continuousOn hs
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
  -- The limit solves the integral equation on `[0, 1]`, hence `x' = X(t, x)` by periodicity.
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, x t - x 0 = ∫ τ in (0 : ℝ)..t, X τ (x τ) := fun t ht ↦
    sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect hu hK huK hX (fun n ↦ hφa (ψ n)) hdef
      hpt ht
  refine ⟨ψ, hψ, x, hxper, hasDerivAt_of_periodic_of_sub_eq_integral one_pos hxper
    (hX.comp (continuous_id.prodMk hxcont)) (fun t ↦ by simp only [hxper t, hXper (x t) t]) hint,
    hux⟩

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
