/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Variational
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- Private: compactly supported `C¹` maps are Lipschitz; used only inside the proof.
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Time-dependent flows near a rest point

Let `X` be a time-dependent vector field on a finite-dimensional real normed space, defined and
jointly `C^r` (`r ≥ 1`) only on `T × U`, for an open set of times `T ⊇ [0, 1]` and an open set
`U`, and suppose that `x₀ ∈ U` is a rest point: `X t x₀ = 0` for all `t ∈ T`. The orbit of `x₀` is
then constant, so the orbits of nearby points stay close to `x₀` up to time one, and the field
generates a family of maps `ψₜ` near `x₀` for `t ∈ [0, 1]`.

`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn` makes this precise. It cuts the
field off by a bump function equal to one near `[0, 1] × {x₀}`, so that the suspended field is
globally Lipschitz, and takes the global time-dependent flow `TauCeti.timeDependentFlow` from time
`0`. The resulting maps satisfy `ψ₀ = id` and `ψₜ x₀ = x₀`, the time-one map is a `C^r`
diffeomorphism of the whole space, and for every `x` near `x₀` and `t ∈ [0, 1]` the point `ψₜ x`
stays in `U`, the orbit solves `∂ₜ ψₜ x = Xₜ (ψₜ x)`, and the derivative `Dψₜ(x)` solves the
variational equation `∂ₜ Dψₜ(x) = DXₜ(ψₜ x) ∘ Dψₜ(x)`.

These are exactly the hypotheses of Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`), so this is the flow used in
Moser's deformation argument, for instance in the proof of Darboux's theorem, where the Moser field
vanishes at the centre of the chart.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (the Moser flow in the proof of Darboux's theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.48 (time-dependent flows).
-/

public section

open Set Filter Topology Metric
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A time-dependent field which is `C^r` on `T × U`, with `T ⊇ [0, 1]` and `U ∋ x₀` open, agrees
near `[0, 1] × {x₀}` with a compactly supported field which is `C^r` on all of `ℝ × E`. If the
field vanishes at `x₀`, so does the cut-off field. -/
private theorem exists_contDiff_hasCompactSupport_eq {X : ℝ → E → E} {T : Set ℝ} {U : Set E}
    {x₀ : E} {r : ℕ∞} (hT : IsOpen T) (hU : IsOpen U) (hTI : Icc 0 1 ⊆ T) (hx₀ : x₀ ∈ U)
    (hX : ContDiffOn ℝ r (fun p : ℝ × E ↦ X p.1 p.2) (T ×ˢ U)) (hX₀ : ∀ t ∈ T, X t x₀ = 0) :
    ∃ (Y : ℝ → E → E) (O : Set (ℝ × E)), ContDiff ℝ r (fun p : ℝ × E ↦ Y p.1 p.2) ∧
      HasCompactSupport (fun p : ℝ × E ↦ Y p.1 p.2) ∧ (∀ t, Y t x₀ = 0) ∧ IsOpen O ∧
      Icc 0 1 ×ˢ {x₀} ⊆ O ∧ O ⊆ T ×ˢ U ∧ ∀ q ∈ O, Y q.1 q.2 = X q.1 q.2 := by
  -- Some closed thickening `[-ε, 1 + ε]` of `[0, 1]` still lies in `T`.
  obtain ⟨ε, hε, hεT⟩ := isCompact_Icc.exists_cthickening_subset_open hT hTI
  rw [show Icc (0 : ℝ) 1 = closedBall (1 / 2) (1 / 2) by rw [Real.closedBall_eq_Icc]; norm_num,
    cthickening_closedBall hε.le (by norm_num), add_comm] at hεT
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  let b₁ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 + ε / 2, 1 / 2 + ε, by positivity, by linarith⟩
  let b₂ : ContDiffBump x₀ := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hb₁T : tsupport b₁ ⊆ T := by rw [b₁.tsupport_eq]; exact hεT
  have hb₁r : b₁.rIn = 1 / 2 + ε / 2 := rfl
  have hb₂r : b₂.rIn = ρ / 4 := rfl
  have hb₂R : b₂.rOut = ρ / 2 := rfl
  have hb₂U : tsupport b₂ ⊆ U := by
    rw [b₂.tsupport_eq, hb₂R]
    exact (closedBall_subset_ball (by linarith)).trans hρU
  refine ⟨fun t x ↦ (b₁ t * b₂ x) • X t x, ball (1 / 2 : ℝ) (1 / 2 + ε / 2) ×ˢ ball x₀ (ρ / 4),
    ?_, ?_, fun t ↦ ?_, isOpen_ball.prod isOpen_ball, ?_, ?_, ?_⟩
  · -- Inside `T × U` the cut-off field is a product of `C^r` maps, outside it vanishes nearby.
    refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
    by_cases hp : p ∈ T ×ˢ U
    · exact ((b₁.contDiff.comp contDiff_fst).mul (b₂.contDiff.comp contDiff_snd)).contDiffAt.smul
        (hX.contDiffAt ((hT.prod hU).mem_nhds hp))
    · refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
      rw [mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · filter_upwards [continuous_fst.continuousAt.eventually
          (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hp (hb₁T h))] with q hq
        simp [hq]
      · filter_upwards [continuous_snd.continuousAt.eventually
          (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hp (hb₂U h))] with q hq
        simp [hq]
  · refine HasCompactSupport.intro
      ((isCompact_closedBall (1 / 2 : ℝ) (1 / 2 + ε)).prod (isCompact_closedBall x₀ (ρ / 2)))
      fun p hp ↦ ?_
    rw [mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : b₁ p.1 = 0 := image_eq_zero_of_notMem_tsupport (by rw [b₁.tsupport_eq]; exact hp)
      simp [this]
    · have : b₂ p.2 = 0 :=
        image_eq_zero_of_notMem_tsupport (by rw [b₂.tsupport_eq, hb₂R]; exact hp)
      simp [this]
  · by_cases ht : t ∈ T
    · simp [hX₀ t ht]
    · have : b₁ t = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ ht (hb₁T h)
      simp [this]
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [mem_singleton_iff] at hx
    refine mk_mem_prod ?_ (hx ▸ mem_ball_self (by positivity))
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  · exact prod_mono (ball_subset_closedBall.trans ((closedBall_subset_closedBall
      (by linarith)).trans hεT)) ((ball_subset_ball (by linarith)).trans hρU)
  · rintro q ⟨hq₁, hq₂⟩
    rw [← hb₁r] at hq₁
    rw [← hb₂r] at hq₂
    simp [b₁.one_of_mem_closedBall (ball_subset_closedBall hq₁),
      b₂.one_of_mem_closedBall (ball_subset_closedBall hq₂)]

/-- **The local flow of a time-dependent field near a rest point.** Let `X` be a time-dependent
vector field on a finite-dimensional space, jointly `C^r` (`r ≥ 1`) on `T × U` for an open set of
times `T ⊇ [0, 1]` and an open set `U`, and vanishing at `x₀ ∈ U` for all times in `T`. Then there
is a family of maps `ψ t`, with `ψ 0 = id` and `ψ t x₀ = x₀`, whose time-one map is a `C^r`
diffeomorphism of the whole space, such that for every `x` near `x₀` and every `t ∈ [0, 1]`, the
point `ψ t x` lies in `U`, the orbit `s ↦ ψ s x` solves `x' = X(t, x)` at `t`, and the derivative
`Dψ_t(x)` solves the variational equation `∂ₜ Dψ_t(x) = DX_t(ψ_t x) ∘ Dψ_t(x)`. -/
theorem exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn {X : ℝ → E → E} {T : Set ℝ}
    {U : Set E} {x₀ : E} {r : ℕ∞} (hr : 1 ≤ r) (hT : IsOpen T) (hU : IsOpen U) (hTI : Icc 0 1 ⊆ T)
    (hx₀ : x₀ ∈ U) (hX : ContDiffOn ℝ r (fun p : ℝ × E ↦ X p.1 p.2) (T ×ˢ U))
    (hX₀ : ∀ t ∈ T, X t x₀ = 0) :
    ∃ (ψ : ℝ → E → E) (ψ' : E → E), ContDiff ℝ r (ψ 1) ∧ ContDiff ℝ r ψ' ∧
      Function.LeftInverse ψ' (ψ 1) ∧ Function.RightInverse ψ' (ψ 1) ∧
      ψ 0 = id ∧ (∀ t, ψ t x₀ = x₀) ∧
      ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc (0 : ℝ) 1, ψ t x ∈ U ∧
        HasDerivAt (fun s ↦ ψ s x) (X t (ψ t x)) t ∧
        HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
          ((fderiv ℝ (X t) (ψ t x)).comp (fderiv ℝ (ψ t) x)) t := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  obtain ⟨Y, O, hY, hYc, hYx₀, hO, hIO, hOTU, hYX⟩ :=
    exists_contDiff_hasCompactSupport_eq hT hU hTI hx₀ hX hX₀
  -- The cut-off field has a global time-dependent flow, with `C^r` time maps.
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hYc (hY.of_le hr') one_ne_zero
  have hS : LipschitzWith (max 0 C) (timeDependentSuspension Y) := by
    convert (LipschitzWith.const (1 : ℝ)).prodMk hC using 1
    funext ⟨t, x⟩
    simp
  have hsm (s t : ℝ) : ContDiff ℝ r (timeDependentFlow Y hS s t) := by
    refine contDiff_iff_forall_nat_le.2 fun m hm ↦ ?_
    have hι : ContDiff ℝ m fun x : E ↦ ((s, t), x) := contDiff_const.prodMk contDiff_id
    cases m with
    | zero => exact contDiff_zero.2 ((continuous_timeDependentFlow Y hS).comp hι.continuous)
    | succ m =>
      exact (contDiff_timeDependentFlow hS m (hY.of_le (by exact_mod_cast hm))).comp hι
  have hψx₀ (t : ℝ) : timeDependentFlow Y hS 0 t x₀ = x₀ :=
    (eq_timeDependentFlow Y hS (y := fun _ ↦ x₀)
      (fun t ↦ by rw [hYx₀]; exact hasDerivAt_const t x₀) 0 t).symm
  -- Orbits starting near `x₀` stay, up to time one, where the cut-off field is the given one.
  have hcont : Continuous fun p : ℝ × E ↦ (p.1, timeDependentFlow Y hS 0 p.1 p.2) :=
    continuous_fst.prodMk ((continuous_timeDependentFlow Y hS).comp
      (by fun_prop : Continuous fun p : ℝ × E ↦ (((0 : ℝ), p.1), p.2)))
  obtain ⟨T', U', -, hU', hIT', hxU', hsub⟩ := generalized_tube_lemma isCompact_Icc
    (isCompact_singleton (x := x₀)) (hO.preimage hcont) fun p hp ↦ by
      rw [mem_preimage, (mem_singleton_iff.1 hp.2), hψx₀]
      exact hIO (mk_mem_prod hp.1 rfl)
  refine ⟨timeDependentFlow Y hS 0, timeDependentFlow Y hS 1 0, hsm 0 1, hsm 1 0,
    leftInverse_timeDependentFlow Y hS 0 1, rightInverse_timeDependentFlow Y hS 0 1,
    funext fun x ↦ timeDependentFlow_self Y hS 0 x, hψx₀, ?_⟩
  filter_upwards [hU'.mem_nhds (hxU' rfl)] with x hx t ht
  have hmem : (t, timeDependentFlow Y hS 0 t x) ∈ O := hsub (mk_mem_prod (hIT' ht) hx)
  have hEq : Y t =ᶠ[𝓝 (timeDependentFlow Y hS 0 t x)] X t :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
      (Filter.mem_of_superset (hO.mem_nhds hmem) hYX)
  refine ⟨(hOTU hmem).2, ?_, ?_⟩
  · rw [← hEq.eq_of_nhds]
    exact hasDerivAt_timeDependentFlow Y hS 0 t x
  · rw [← hEq.fderiv_eq]
    exact hasDerivAt_fderiv_timeDependentFlow hS (hY.of_le hr') 0 t x

end TauCeti
