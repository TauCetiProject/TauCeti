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
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Topology.ContinuousMap.Ascoli

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

The second statement is an application of the Arzelà–Ascoli theorem, in the form for periodic
loops with a common modulus of continuity
(`TauCeti.exists_tendstoUniformly_subseq_of_periodic_of_modulus`): by the Cauchy–Schwarz
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
  exact hasDerivAt_slice_right (hu.differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem))

/-- **The loops solve the integral equation up to the defect.** Along the loop at `s > a` of a
`C¹` map, `u(s, t₂) - u(s, t₁) = ∫_{t₁}^{t₂} X(t, u(s, t)) dt + ∫_{t₁}^{t₂} (∂_t u - X(t, u))`. -/
theorem sub_eq_integral_add_integral_sliceDefect [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s)
    (t₁ t₂ : ℝ) :
    u (s, t₂) - u (s, t₁) =
      (∫ t in t₁..t₂, X t (u (s, t))) + ∫ t in t₁..t₂, sliceDefect X u (s, t) := by
  have hXc : Continuous fun t ↦ X t (u (s, t)) :=
    hX.comp (continuous_id.prodMk (continuous_slice_of_continuousOn hu.continuousOn hs))
  have hd := continuous_sliceDefect_slice hu hX hs
  rw [← intervalIntegral.integral_add (hXc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) hs t)
    ((hXc.add hd).intervalIntegrable _ _)).symm

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
  have hd := continuous_sliceDefect_slice hu hX hs
  rw [sub_eq_integral_add_integral_sliceDefect hu hX hs]
  calc ‖(∫ t in t₁..t₂, X t (u (s, t))) + ∫ t in t₁..t₂, sliceDefect X u (s, t)‖
      ≤ ‖∫ t in t₁..t₂, X t (u (s, t))‖ + ‖∫ t in t₁..t₂, sliceDefect X u (s, t)‖ :=
        norm_add_le _ _
    _ ≤ B * (t₂ - t₁) + ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ := by
        gcongr
        · rw [← abs_of_nonneg (sub_nonneg.2 ht)]
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun t htI ↦ hB t ?_
          rw [uIoc_of_le ht] at htI
          exact Ioc_subset_Icc_self htI
        · exact intervalIntegral.norm_integral_le_integral_norm ht
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

/-- **Vanishing defect integrals.** If the `L²` norms of the defects along the loops at `s_i > a`
tend to `0`, then so do the integrals of the norms of the defects over any subinterval
`[t₁, t₂]` of `[0, 1]`. -/
theorem tendsto_integral_norm_sliceDefect_of_tendsto_integral_norm_sq
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X)) {ι : Type*}
    {l : Filter ι} {φ : ι → ℝ} (hφa : ∀ i, a < φ i)
    (hφ : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ i, t)‖ ^ 2) l (𝓝 0))
    {t₁ t₂ : ℝ} (h₀ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (h₁ : t₂ ≤ 1) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, ‖sliceDefect X u (φ i, t)‖) l (𝓝 0) := by
  have hsq : Tendsto (fun i ↦
      √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ i, t)‖ ^ 2)) l (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hφ
    rw [Real.sqrt_zero] at h
    exact h
  exact squeeze_zero (fun i ↦ intervalIntegral.integral_nonneg ht fun t _ ↦ norm_nonneg _)
    (fun i ↦ integral_norm_sliceDefect_le_sqrt hu hX (hφa i) h₀ ht h₁) hsq

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
      (∫ τ in (0 : ℝ)..t, X τ (u (φ i, τ))) + ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ i, τ) :=
    fun i ↦ sub_eq_integral_add_integral_sliceDefect hu hX (hφa i) 0 t
  -- The first integral converges by dominated convergence.
  have hA : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, X τ (u (φ i, τ))) l
      (𝓝 (∫ τ in (0 : ℝ)..t, X τ (x τ))) :=
    tendsto_intervalIntegral_comp_of_tendsto (Φ := uncurry X) (y := fun i τ ↦ u (φ i, τ)) hX hK
      (fun i ↦ (hloop i).continuousOn) (fun i τ _ ↦ huK _ (hφa i) τ) fun τ _ ↦ hx τ
  -- The second integral tends to `0` by the Cauchy–Schwarz inequality.
  have hD : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, sliceDefect X u (φ i, τ)) l (𝓝 0) :=
    squeeze_zero_norm (fun i ↦ intervalIntegral.norm_integral_le_integral_norm ht.1)
      (tendsto_integral_norm_sliceDefect_of_tendsto_integral_norm_sq hu hX hφa hφ le_rfl ht.1
        ht.2)
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
  have hρ : Tendsto (fun h : ℝ ↦ B * h + √h) (𝓝 0) (𝓝 0) := by
    have hb : Continuous fun h : ℝ ↦ B * h + √h :=
      (continuous_const.mul continuous_id).add Real.continuous_sqrt
    simpa using hb.tendsto 0
  obtain ⟨ψ', hψ', x, hxper, hxcont, hux'⟩ :=
    exists_tendstoUniformly_subseq_of_periodic_of_modulus hK
      (fun n ↦ continuous_slice_of_continuousOn hu.continuousOn (hφa (N + n)))
      (fun n ↦ hper _ (hφa (N + n))) (fun n ↦ huK _ (hφa (N + n))) hρ hmod
  set ψ : ℕ → ℕ := fun n ↦ N + ψ' n
  have hψ : StrictMono ψ := fun m n h ↦ Nat.add_lt_add_left (hψ' h) N
  have hux : TendstoUniformly (fun n t ↦ u (φ (ψ n), t)) x atTop := hux'
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
