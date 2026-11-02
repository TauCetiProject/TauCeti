/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Variational
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
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
`0`. The resulting maps satisfy `ψ₀ = id` and fix every rest point of the field, in particular
`ψₜ x₀ = x₀`; the time-one map is a `C^r`
diffeomorphism of the whole space, and for every `x` near `x₀` and `t ∈ [0, 1]` the point `ψₜ x`
stays in `U`, the orbit solves `∂ₜ ψₜ x = Xₜ (ψₜ x)`, and the derivative `Dψₜ(x)` solves the
variational equation `∂ₜ Dψₜ(x) = DXₜ(ψₜ x) ∘ Dψₜ(x)`.

These are exactly the hypotheses of Moser's identity
(`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`), so this is the flow used in
Moser's deformation argument, for instance in the proof of Darboux's theorem, where the Moser field
vanishes at the centre of the chart. In the relative Darboux theorem the Moser field vanishes along
a whole submanifold, which the flow therefore fixes pointwise.

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
near `[0, 1] × {x₀}` with a compactly supported field which is `C^r` on all of `ℝ × E`. The cut-off
field vanishes at every point where the field vanishes for all times in `T`. -/
private theorem exists_contDiff_hasCompactSupport_eq {X : ℝ → E → E} {T : Set ℝ} {U : Set E}
    {x₀ : E} {r : ℕ∞} (hT : IsOpen T) (hU : IsOpen U) (hTI : Icc 0 1 ⊆ T) (hx₀ : x₀ ∈ U)
    (hX : ContDiffOn ℝ r (fun p : ℝ × E ↦ X p.1 p.2) (T ×ˢ U)) :
    ∃ (Y : ℝ → E → E) (O : Set (ℝ × E)), ContDiff ℝ r (fun p : ℝ × E ↦ Y p.1 p.2) ∧
      HasCompactSupport (fun p : ℝ × E ↦ Y p.1 p.2) ∧
      (∀ y, (∀ t ∈ T, X t y = 0) → ∀ t, Y t y = 0) ∧ IsOpen O ∧
      Icc 0 1 ×ˢ {x₀} ⊆ O ∧ O ⊆ T ×ˢ U ∧ ∀ q ∈ O, Y q.1 q.2 = X q.1 q.2 := by
  -- Cut the joint field off near the compact set `[0, 1] × {x₀}` of the open set `T × U`.
  obtain ⟨g, hg, hgc, hgTU, hgX, hgeq⟩ :=
    hX.exists_contDiff_eventuallyEq_on_isCompact (isCompact_Icc.prod isCompact_singleton)
      (hT.prod hU) (prod_mono hTI (singleton_subset_iff.2 hx₀))
  refine ⟨fun t x ↦ g (t, x), interior {q | g q = X q.1 q.2} ∩ T ×ˢ U, hg, hgc,
    fun y hy t ↦ ?_, isOpen_interior.inter (hT.prod hU),
    fun q hq ↦ ⟨mem_interior_iff_mem_nhds.2 (hgeq q hq),
      prod_mono hTI (singleton_subset_iff.2 hx₀) hq⟩,
    inter_subset_right, fun q hq ↦ interior_subset hq.1⟩
  -- Off `T × U` the cut-off field vanishes; on it, it vanishes wherever the field does.
  by_contra h
  exact hgX h (hy t (hgTU (subset_tsupport _ h)).1)

/-- **The local flow of a time-dependent field near a rest point.** Let `X` be a time-dependent
vector field on a finite-dimensional space, jointly `C^r` (`r ≥ 1`) on `T × U` for an open set of
times `T ⊇ [0, 1]` and an open set `U`, and vanishing at `x₀ ∈ U` for all times in `T`. Then there
is a family of maps `ψ t`, with `ψ 0 = id` and `ψ t y = y` at every point `y` where the field
vanishes for all times in `T` (in particular `ψ t x₀ = x₀`), whose time-one map is a `C^r`
diffeomorphism of the whole space, such that for every `x` near `x₀` and every `t ∈ [0, 1]`, the
point `ψ t x` lies in `U`, the orbit `s ↦ ψ s x` solves `x' = X(t, x)` at `t`, and the derivative
`Dψ_t(x)` solves the variational equation `∂ₜ Dψ_t(x) = DX_t(ψ_t x) ∘ Dψ_t(x)`. -/
theorem exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn {X : ℝ → E → E} {T : Set ℝ}
    {U : Set E} {x₀ : E} {r : ℕ∞} (hr : 1 ≤ r) (hT : IsOpen T) (hU : IsOpen U) (hTI : Icc 0 1 ⊆ T)
    (hx₀ : x₀ ∈ U) (hX : ContDiffOn ℝ r (fun p : ℝ × E ↦ X p.1 p.2) (T ×ˢ U))
    (hX₀ : ∀ t ∈ T, X t x₀ = 0) :
    ∃ (ψ : ℝ → E → E) (ψ' : E → E), ContDiff ℝ r (ψ 1) ∧ ContDiff ℝ r ψ' ∧
      Function.LeftInverse ψ' (ψ 1) ∧ Function.RightInverse ψ' (ψ 1) ∧
      ψ 0 = id ∧ (∀ y, (∀ t ∈ T, X t y = 0) → ∀ t, ψ t y = y) ∧
      ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc (0 : ℝ) 1, ψ t x ∈ U ∧
        HasDerivAt (fun s ↦ ψ s x) (X t (ψ t x)) t ∧
        HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
          ((fderiv ℝ (X t) (ψ t x)).comp (fderiv ℝ (ψ t) x)) t := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  obtain ⟨Y, O, hY, hYc, hYrest, hO, hIO, hOTU, hYX⟩ :=
    exists_contDiff_hasCompactSupport_eq hT hU hTI hx₀ hX
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
  -- Rest points of the field are rest points of the cut-off field, hence fixed by its flow.
  have hfix (y : E) (hy : ∀ t ∈ T, X t y = 0) (t : ℝ) : timeDependentFlow Y hS 0 t y = y :=
    (eq_timeDependentFlow Y hS (y := fun _ ↦ y)
      (fun t ↦ by rw [hYrest y hy]; exact hasDerivAt_const t y) 0 t).symm
  have hψx₀ (t : ℝ) : timeDependentFlow Y hS 0 t x₀ = x₀ := hfix x₀ hX₀ t
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
    funext fun x ↦ timeDependentFlow_self Y hS 0 x, hfix, ?_⟩
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
