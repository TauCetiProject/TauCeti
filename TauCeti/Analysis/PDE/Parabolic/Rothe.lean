/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.NormSq
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.WeakLimit

/-!
# Time regularity for time-dependent coefficients by Rothe's method

Let `ι : V →L[ℝ] H` give a Gelfand triple `V ↪ H ↪ V*` of real Hilbert spaces, and let
`A(t) : V →L[ℝ] V*`, `t ∈ [a, b]`, be symmetric, coercive, `α ‖v‖² ≤ A(t) v v`, and Lipschitz in
time, `‖A(t) - A(s)‖ ≤ L |t - s|`. A weak solution of `u' + A(t) u = ι* g`, `u(a) = ι v₀`, with
`g ∈ L²(a, b; H)` and `v₀ ∈ V`, has a weak time derivative `d ∈ L²(a, b; H)` of `ι ∘ u`, and with
`M = exp (L (b - a) / α) (A(a) v₀ v₀ + ∫ₐᵇ ‖g‖²)`, `∫ₐᵇ ‖d‖² ≤ M` and `A(t) u(t) u(t) ≤ M` for
almost every `t`
(`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_lipschitz`). For
`∂ₜu - ∂ᵢ(aⁱʲ(t, x) ∂ⱼu) = f` with `∂ₜa` bounded this is `∂ₜu ∈ L²(0, T; L²(Ω))` and
`u ∈ L^∞(0, T; H¹₀(Ω))`. When `A` does not depend on time,
`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm` proves these
estimates by a shifted Gelfand triple, which has no counterpart for time-dependent `A`.

## The argument

Formally, testing the equation with `u'` gives `‖u'‖² + ½ (A u u)' = ⟪g, u'⟫ + ½ A' u u` with
`‖A'‖ ≤ L`. This is carried out on the implicit Euler scheme for `N` cells of length `h`,
`ι* ι (x (k + 1) - x k) + h A(t_{k+1}) x (k + 1) = h ι* gₖ` with the cell averages `gₖ` of `g`,
a sequence of stationary problems solved by Lax–Milgram. Testing a step with `x (k + 1) - x k`
bounds the energies `A(t_k) x_k x_k` and the dissipation `∑ ‖ι (x (k + 1) - x k)‖² / h` by `M`,
uniformly in `N`. The piecewise linear interpolant `uh` of the scheme has weak derivative `D`,
`ι* ι D + A(t_{k+1}) ub = ι* G` for the piecewise constant interpolant `ub` and the cellwise
average `G` of `g`, and `∫ ‖uh - ub‖² ≤ h M / α`. The energy estimate
`TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual` for `uh - u`, whose forcing
`ι* (G - g) + A(t) (uh - ub) + (A(t) - A(t_{k+1})) ub` tends to zero since cell averages converge in
`L²`, gives `uh → u` and `ub → u` in `L²(a, b; V)`. An almost everywhere convergent subsequence
of `ub` passes the energy bound to `u`, and a weakly convergent subsequence of `ι D` in
`L²(a, b; H)` gives `d` (`TauCeti.hasWeakLineDerivOn_of_tendsto_inner_toLp`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5 (time-independent
  coefficients, by Galerkin approximation).
* J. Kačur, *Method of Rothe in Evolution Equations*, Teubner-Texte zur Mathematik **80**, Teubner,
  Leipzig, 1985, Chapter 2.
* K. Rektorys, *The Method of Discretization in Time and Partial Differential Equations*, Reidel,
  Dordrecht, 1982.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped InnerProductSpace Interval Distributions

namespace TauCeti

/-! ### The cells of a uniform partition -/

/-- The index `k` of the cell `(a + (k - 1) h, a + k h]` of the uniform partition of step `h`
starting at `a` that contains `t`. -/
private def cellIndex (a h t : ℝ) : ℕ := ⌈(t - a) / h⌉₊

private theorem cellIndex_eq {a h t : ℝ} (hh : 0 < h) {k : ℕ}
    (ht : t ∈ Ioc (a + k * h) (a + (k + 1) * h)) : cellIndex a h t = k + 1 := by
  rw [cellIndex, Nat.ceil_eq_iff (Nat.succ_ne_zero k), Nat.succ_sub_one, lt_div_iff₀ hh,
    div_le_iff₀ hh]
  push_cast
  constructor <;> linarith [ht.1, ht.2]

private theorem measurable_cellIndex (a h : ℝ) : Measurable (cellIndex a h) :=
  ((measurable_id.sub_const a).div_const h).nat_ceil

/-- On `(a, b)`, the cell index for the partition into `N` cells lies between `1` and `N`. -/
private theorem cellIndex_mem_Icc {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N) :
    cellIndex a ((b - a) / N) t - 1 < N ∧ 1 ≤ cellIndex a ((b - a) / N) t := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 (ht.1.trans ht.2)) (Nat.cast_pos.2 hN)
  have hpos : 0 < (t - a) / ((b - a) / N) := div_pos (sub_pos.2 ht.1) hh
  have hlt : (t - a) / ((b - a) / N) < N := by
    rw [div_lt_iff₀ hh, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]
    linarith [ht.2]
  refine ⟨?_, Nat.one_le_iff_ne_zero.2 fun h ↦ ?_⟩
  · have : cellIndex a ((b - a) / N) t ≤ N := Nat.ceil_le.2 hlt.le
    omega
  · rw [cellIndex, Nat.ceil_eq_zero] at h
    linarith

/-- A point of `(a, b)` lies in its cell. -/
private theorem mem_Ioc_cellIndex {a h t : ℝ} (hh : 0 < h) (ht : a < t) :
    t ∈ Ioc (a + ((cellIndex a h t - 1 : ℕ) : ℝ) * h) (a + (cellIndex a h t : ℝ) * h) := by
  have hpos : 0 < (t - a) / h := div_pos (sub_pos.2 ht) hh
  have h1 : 1 ≤ cellIndex a h t := Nat.one_le_iff_ne_zero.2 fun h ↦ by
    rw [cellIndex, Nat.ceil_eq_zero] at h
    linarith
  have hk := (Nat.ceil_eq_iff (n := cellIndex a h t) (a := (t - a) / h) (by omega)).1 rfl
  rw [lt_div_iff₀ hh, div_le_iff₀ hh] at hk
  constructor <;> linarith [hk.1, hk.2]

/-- **Integrals of cellwise constant functions.** For the partition of `(a, b)` into `N` cells of
length `h = (b - a) / N`, the integral of `t ↦ F (cellIndex a h t)` is `∑ₖ h F (k + 1)`. -/
private theorem integral_Ioo_comp_cellIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) (F : ℕ → E) :
    ∫ t in Ioo a b, F (cellIndex a ((b - a) / N) t) =
      ∑ k ∈ Finset.range N, ((b - a) / N) • F (k + 1) := by
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hae (k : ℕ) : ∀ᵐ t ∂volume, t ∈ Ι (a + (k : ℕ) * h) (a + ((k + 1 : ℕ) : ℝ) * h) →
      F (cellIndex a h t) = F (k + 1) := Eventually.of_forall fun t ht ↦ by
    rw [uIoc_of_le (by push_cast; nlinarith)] at ht
    rw [cellIndex_eq hh (by push_cast at ht ⊢; exact ht)]
  have hcell (k : ℕ) : ∫ t in (a + (k : ℕ) * h)..(a + ((k + 1 : ℕ) : ℝ) * h),
      F (cellIndex a h t) = h • F (k + 1) := by
    rw [intervalIntegral.integral_congr_ae (hae k), intervalIntegral.integral_const]
    congr 1
    push_cast
    ring
  have hint (k : ℕ) (_ : k < N) : IntervalIntegrable (fun t ↦ F (cellIndex a h t)) volume
      (a + (k : ℕ) * h) (a + ((k + 1 : ℕ) : ℝ) * h) :=
    (intervalIntegrable_const (c := F (k + 1))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 ((hae k).mono fun t ht ht' ↦ (ht ht').symm))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ a + (k : ℝ) * h) hint
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  have hbN : a + (N : ℝ) * h = b := by
    rw [hh_def, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]
    ring
  rw [hbN] at hsum
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le, ← hsum]
  exact Finset.sum_congr rfl fun k _ ↦ hcell k

/-! ### The implicit Euler scheme and its discrete energy estimate -/

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : V →L[ℝ] H}

/-- **Solvability of the implicit Euler scheme.** For `h > 0`, coercive operators `B (k + 1)` and
data `G k ∈ H`, there are `x k ∈ V` with `x 0 = v₀` and
`⟪ι (x (k + 1) - x k), ι v⟫ + h B (k + 1) (x (k + 1)) v = h ⟪G k, ι v⟫` for all `v`: each step is a
stationary problem for the coercive operator `ι* ι + h B (k + 1)`, solved by Lax–Milgram. -/
private theorem exists_rotheScheme [CompleteSpace V] {B : ℕ → V →L[ℝ] StrongDual ℝ V} {α h : ℝ}
    (hα : 0 < α) (hh : 0 < h) (hB : ∀ k v, α * ‖v‖ ^ 2 ≤ B (k + 1) v v) (G : ℕ → H) (v₀ : V) :
    ∃ x : ℕ → V, x 0 = v₀ ∧ ∀ k v,
      ⟪ι (x (k + 1) - x k), ι v⟫_ℝ + h * B (k + 1) (x (k + 1)) v = h * ⟪G k, ι v⟫_ℝ := by
  have hT (k : ℕ) : IsCoercive (ι.gelfandDual ∘L ι + h • B (k + 1)) := by
    refine ⟨h * α, mul_pos hh hα, fun v ↦ ?_⟩
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.gelfandDual_apply, smul_eq_mul,
      real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖ι v‖, mul_le_mul_of_nonneg_left (hB k v) hh.le]
  -- The step map `y ↦ x` solving `(ι* ι + h B (k + 1)) x = ι* ι y + h ι* G k`.
  let S : ℕ → V → V := fun k y ↦
    (hT k).solutionOfFunctional (ι.gelfandDual (ι y) + h • ι.gelfandDual (G k))
  let x : ℕ → V := fun k ↦ Nat.rec v₀ S k
  refine ⟨x, rfl, fun k v ↦ ?_⟩
  have := (hT k).apply_solutionOfFunctional_eq
    (ι.gelfandDual (ι (x k)) + h • ι.gelfandDual (G k)) v
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.gelfandDual_apply, smul_eq_mul] at this
  -- `x` is defined by recursion, so `x (k + 1) = S k (x k)` holds by definition.
  have hxS : x (k + 1) = S k (x k) := rfl
  rw [hxS, map_sub, inner_sub_left]
  linarith

/-- **One step of the discrete energy estimate.** If `B'` is symmetric, `B` and `B'` are coercive
and `‖B' - B‖ ≤ L h`, a step `x ↦ y` of the implicit Euler scheme tested with `y - x` gives
`‖ι (y - x)‖² / h + α ‖y - x‖² + B' y y ≤ (1 + L h / α) B x x + h ‖G‖²`. -/
private theorem rotheStep_energy {B B' : V →L[ℝ] StrongDual ℝ V} {α L h : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hh : 0 < h) (hsymm : ∀ v w, B' v w = B' w v)
    (hB : ∀ v, α * ‖v‖ ^ 2 ≤ B v v) (hB' : ∀ v, α * ‖v‖ ^ 2 ≤ B' v v) (hBB : ‖B' - B‖ ≤ L * h)
    {x y : V} {G : H}
    (hstep : ⟪ι (y - x), ι (y - x)⟫_ℝ + h * B' y (y - x) = h * ⟪G, ι (y - x)⟫_ℝ) :
    ‖ι (y - x)‖ ^ 2 / h + α * ‖y - x‖ ^ 2 + B' y y ≤
      (1 + L * h / α) * B x x + h * ‖G‖ ^ 2 := by
  set δ := y - x with hδ
  have hpol : 2 * B' y δ = B' y y - B' x x + B' δ δ := by
    have hx : x = y - δ := by rw [hδ, sub_sub_cancel]
    rw [hx]
    simp only [map_sub, sub_apply, hsymm δ y]
    ring
  have hBx : B' x x ≤ B x x + L * h * ‖x‖ ^ 2 := by
    have h1 : (B' - B) x x ≤ ‖B' - B‖ * ‖x‖ * ‖x‖ :=
      (le_abs_self _).trans ((((B' - B) x).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right ((B' - B).le_opNorm x) (norm_nonneg x)))
    simp only [sub_apply] at h1
    nlinarith [mul_le_mul_of_nonneg_right hBB (sq_nonneg ‖x‖)]
  have hx2 : L * h * ‖x‖ ^ 2 ≤ L * h / α * B x x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    nlinarith [mul_le_mul_of_nonneg_left (hB x) (mul_nonneg hL hh.le)]
  have hG : h * ⟪G, ι δ⟫_ℝ ≤ ‖ι δ‖ ^ 2 / 2 + h ^ 2 * ‖G‖ ^ 2 / 2 := by
    have := real_inner_le_norm G (ι δ)
    nlinarith [sq_nonneg (h * ‖G‖ - ‖ι δ‖), mul_le_mul_of_nonneg_left this hh.le]
  rw [real_inner_self_eq_norm_sq] at hstep
  have hδ' := hB' δ
  have hmain : h * (‖ι δ‖ ^ 2 / h + α * ‖δ‖ ^ 2 + B' y y) ≤
      h * ((1 + L * h / α) * B x x + h * ‖G‖ ^ 2) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hh.ne']
    nlinarith
  exact le_of_mul_le_mul_left hmain hh

/-- **The discrete energy estimate.** For the implicit Euler scheme with symmetric, coercive
operators `B k` that vary by at most `L h` per step,
`B k (x k) (x k) + ∑_{j < k} (‖ι (x (j + 1) - x j)‖² / h + α ‖x (j + 1) - x j‖²)` is at most
`(1 + L h / α)ᵏ (B 0 (x 0) (x 0) + ∑_{j < k} h ‖G j‖²)`. -/
private theorem rotheScheme_energy {B : ℕ → V →L[ℝ] StrongDual ℝ V} {α L h : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hh : 0 < h) {N : ℕ} (hsymm : ∀ k ≤ N, ∀ v w, B k v w = B k w v)
    (hB : ∀ k ≤ N, ∀ v, α * ‖v‖ ^ 2 ≤ B k v v) (hBB : ∀ k < N, ‖B (k + 1) - B k‖ ≤ L * h)
    {x : ℕ → V} {G : ℕ → H}
    (hx : ∀ k < N, ∀ v,
      ⟪ι (x (k + 1) - x k), ι v⟫_ℝ + h * B (k + 1) (x (k + 1)) v = h * ⟪G k, ι v⟫_ℝ)
    {k : ℕ} (hk : k ≤ N) :
    B k (x k) (x k) + ∑ j ∈ Finset.range k,
        (‖ι (x (j + 1) - x j)‖ ^ 2 / h + α * ‖x (j + 1) - x j‖ ^ 2) ≤
      (1 + L * h / α) ^ k * (B 0 (x 0) (x 0) + ∑ j ∈ Finset.range k, h * ‖G j‖ ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ihk := ih (by omega)
    have hstep := rotheStep_energy hα hL hh (hsymm (k + 1) hk) (hB k (by omega))
      (hB (k + 1) hk) (hBB k (by omega)) (hx k (by omega) _)
    set q := 1 + L * h / α
    have hq : 1 ≤ q := le_add_of_nonneg_right (by positivity)
    have hS : 0 ≤ ∑ j ∈ Finset.range k,
        (‖ι (x (j + 1) - x j)‖ ^ 2 / h + α * ‖x (j + 1) - x j‖ ^ 2) :=
      Finset.sum_nonneg fun _ _ ↦ by positivity
    have hpow : 1 ≤ q ^ k * q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) hq
    rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_succ q k]
    nlinarith [mul_le_mul_of_nonneg_left ihk (zero_le_one.trans hq),
      mul_nonneg (sub_nonneg.2 hq) hS,
      mul_nonneg (sub_nonneg.2 hpow) (mul_nonneg hh.le (sq_nonneg ‖G k‖))]

/-- The growth factor of the discrete energy estimate over at most `N` steps of length
`(b - a) / N` is at most `exp (L (b - a) / α)`. -/
private theorem one_add_pow_le_exp {α L a b : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hab : a ≤ b)
    {N k : ℕ} (hk : k ≤ N) :
    (1 + L * ((b - a) / N) / α) ^ k ≤ Real.exp (L * (b - a) / α) := by
  have hx : 0 ≤ L * ((b - a) / N) / α :=
    div_nonneg (mul_nonneg hL (div_nonneg (sub_nonneg.2 hab) N.cast_nonneg)) hα.le
  calc (1 + L * ((b - a) / N) / α) ^ k ≤ Real.exp (L * ((b - a) / N) / α) ^ k :=
        pow_le_pow_left₀ (by positivity)
          (by linarith [Real.add_one_le_exp (L * ((b - a) / N) / α)]) k
    _ = Real.exp (k * (L * ((b - a) / N) / α)) := (Real.exp_natCast_mul k _).symm
    _ ≤ Real.exp (L * (b - a) / α) := by
        refine Real.exp_le_exp.2 ?_
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · have : k = 0 := by omega
          subst this
          simpa using div_nonneg (mul_nonneg hL (sub_nonneg.2 hab)) hα.le
        · calc (k : ℝ) * (L * ((b - a) / N) / α) ≤ N * (L * ((b - a) / N) / α) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hx
            _ = L * (b - a) / α := by
                field_simp

/-! ### Cellwise constant functions and cell averages -/

/-- A cellwise constant function on `(a, b)` is in every `Lᵖ`. -/
private theorem memLp_comp_cellIndex {E : Type*} [NormedAddCommGroup E] {a b : ℝ} {N : ℕ}
    (hN : 0 < N) (F : ℕ → E) (p : ENNReal) :
    MemLp (fun t ↦ F (cellIndex a ((b - a) / N) t)) p (volume.restrict (Ioo a b)) := by
  refine MemLp.of_bound ((StronglyMeasurable.of_discrete (f := F)).comp_measurable
    (measurable_cellIndex _ _)).aestronglyMeasurable (∑ k ∈ Finset.range (N + 1), ‖F k‖) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have := cellIndex_mem_Icc ht hN
  exact Finset.single_le_sum (f := fun k ↦ ‖F k‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_range.2 (by omega))

/-- An integrable function on `(a, b)` is integrable on each cell of a uniform partition. -/
private theorem intervalIntegrable_cell {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {g : ℝ → E} (hg : IntegrableOn g (Ioo a b)) {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (hab : a ≤ b) :
    IntervalIntegrable g volume (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N)) := by
  have hh : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) N.cast_nonneg
  have hkN : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
  have hI : IntegrableOn g (Icc a b) := (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2 hg
  refine (hI.mono_set ?_).intervalIntegrable
  rw [uIcc_of_le (by nlinarith)]
  refine Icc_subset_Icc (by nlinarith) ?_
  calc a + (k + 1) * ((b - a) / N) ≤ a + N * ((b - a) / N) := by nlinarith
    _ = b := by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]; ring

/-- The average of `g` over the cell `(a + k h, a + (k + 1) h]`. -/
private def cellAverage (g : ℝ → H) (a h : ℝ) (k : ℕ) : H :=
  h⁻¹ • ∫ s in (a + k * h)..(a + (k + 1) * h), g s

/-- The cellwise average of `g`, constant on each cell `(a + (k - 1) h, a + k h]`. -/
private def stepAverage (g : ℝ → H) (a h t : ℝ) : H :=
  cellAverage g a h (cellIndex a h t - 1)

/-- **Cauchy–Schwarz on a cell.** `h ‖avg_I g‖² ≤ ∫_I ‖g‖²` for a cell `I` of length `h`. -/
private theorem mul_norm_cellAverage_sq_le {g : ℝ → H} {a h : ℝ} (hh : 0 < h) {k : ℕ}
    (hg : IntervalIntegrable g volume (a + k * h) (a + (k + 1) * h))
    (hg2 : IntervalIntegrable (fun s ↦ ‖g s‖ ^ 2) volume (a + k * h) (a + (k + 1) * h)) :
    h * ‖cellAverage g a h k‖ ^ 2 ≤ ∫ s in (a + k * h)..(a + (k + 1) * h), ‖g s‖ ^ 2 := by
  set p := a + k * h
  set q := a + (k + 1) * h
  have hpq : p ≤ q := by simp only [p, q]; nlinarith
  have hlen : q - p = h := by simp only [p, q]; ring
  set c := ∫ s in p..q, ‖g s‖
  set Q := ∫ s in p..q, ‖g s‖ ^ 2
  have hgn : IntervalIntegrable (fun s ↦ ‖g s‖) volume p q := hg.norm
  -- The variance `∫ (‖g‖ - c / h)²` is nonnegative.
  have hvar : 0 ≤ ∫ s in p..q, (‖g s‖ ^ 2 - 2 * (c / h) * ‖g s‖ + (c / h) ^ 2) := by
    refine intervalIntegral.integral_nonneg hpq fun s _ ↦ ?_
    nlinarith [sq_nonneg (‖g s‖ - c / h)]
  rw [intervalIntegral.integral_add (hg2.sub (hgn.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hgn.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, hlen, smul_eq_mul] at hvar
  have hc2 : c ^ 2 ≤ h * Q := by
    have : c ^ 2 / h ≤ Q := by
      have e : c ^ 2 / h = 2 * (c / h) * c - h * (c / h) ^ 2 := by field_simp; ring
      linarith
    rwa [div_le_iff₀ hh, mul_comm] at this
  have hnorm : ‖∫ s in p..q, g s‖ ≤ c := intervalIntegral.norm_integral_le_integral_norm hpq
  rw [cellAverage, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, mul_pow, ← mul_assoc,
    sq, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  calc h⁻¹ * ‖∫ s in p..q, g s‖ ^ 2 ≤ h⁻¹ * c ^ 2 := by gcongr
    _ ≤ Q := by rw [inv_mul_le_iff₀ hh]; exact hc2

/-- The cellwise average is a contraction in `L²(a, b)`. -/
private theorem integral_norm_stepAverage_sq_le {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / N) t‖ ^ 2 ≤ ∫ t in Ioo a b, ‖g t‖ ^ 2 := by
  have key := integral_Ioo_comp_cellIndex hab hN
    (fun n ↦ ‖cellAverage g a ((b - a) / N) (n - 1)‖ ^ 2)
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hgi : IntegrableOn g (Ioo a b) := hg.integrable one_le_two
  have hg2 : IntegrableOn (fun s ↦ ‖g s‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hint (k : ℕ) (hk : k < N) := intervalIntegrable_cell hgi hN hk hab.le
  have hint2 (k : ℕ) (hk : k < N) := intervalIntegrable_cell hg2 hN hk hab.le
  simp only [stepAverage]
  rw [key]
  simp only [Nat.add_sub_cancel, smul_eq_mul]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ a + (k : ℝ) * h) (f := fun s ↦ ‖g s‖ ^ 2) (μ := volume) (n := N)
    fun k hk ↦ by simpa [Nat.cast_succ] using hint2 k hk
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  have hbN : a + (N : ℝ) * h = b := by
    rw [hh_def, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]
    ring
  rw [hbN, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have := mul_norm_cellAverage_sq_le hh (hint k (Finset.mem_range.1 hk))
    (hint2 k (Finset.mem_range.1 hk))
  simpa [Nat.cast_succ] using this

/-- The cell of a point `t ∈ (a, b)` in the partition into `N` cells, with its endpoints. -/
private theorem cell_of_mem_Ioo {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N) :
    t ∈ Ioc (a + ((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) * ((b - a) / N))
      (a + (((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1) * ((b - a) / N)) ∧
    Ioc (a + ((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) * ((b - a) / N))
      (a + (((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1) * ((b - a) / N)) ⊆ Icc a b := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 (ht.1.trans ht.2)) (Nat.cast_pos.2 hN)
  obtain ⟨hlt, hge⟩ := cellIndex_mem_Icc ht hN
  have hcast : ((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1 = cellIndex a ((b - a) / N) t := by
    rw [Nat.cast_sub hge, Nat.cast_one, sub_add_cancel]
  have hmem := mem_Ioc_cellIndex hh ht.1
  rw [← hcast] at hmem
  refine ⟨hmem, Ioc_subset_Icc_self.trans (Icc_subset_Icc ?_ ?_)⟩
  · nlinarith [(Nat.cast_nonneg (cellIndex a ((b - a) / N) t - 1) : (0 : ℝ) ≤ _)]
  · have hkN : ((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hlt
    calc a + (((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1) * ((b - a) / N)
        ≤ a + N * ((b - a) / N) := by nlinarith
      _ = b := by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]; ring

/-- The data term of the discrete energy estimate: `∑_{j < k} h ‖avg_j g‖² ≤ ∫ ‖g‖²` for `k ≤ N`. -/
private theorem sum_mul_norm_cellAverage_sq_le {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {k : ℕ} (hk : k ≤ N) :
    ∑ j ∈ Finset.range k, (b - a) / N * ‖cellAverage g a ((b - a) / N) j‖ ^ 2 ≤
      ∫ t in Ioo a b, ‖g t‖ ^ 2 := by
  have hsum := integral_Ioo_comp_cellIndex hab hN
    (fun n ↦ ‖cellAverage g a ((b - a) / N) (n - 1)‖ ^ 2)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hsum
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
    fun _ _ _ ↦ by positivity).trans ?_
  rw [← hsum]
  exact integral_norm_stepAverage_sq_le hab hN hg

/-- If `φ` varies by at most `η` over distances at most `h` on `[a, b]`, its cellwise average on
cells of length `h` is within `η` of `φ` on `(a, b)`. -/
private theorem norm_stepAverage_sub_le [CompleteSpace H] {φ : ℝ → H} (hφ : Continuous φ)
    {a b t η : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N)
    (hη : ∀ s ∈ Icc a b, |s - t| ≤ (b - a) / N → ‖φ s - φ t‖ ≤ η) :
    ‖stepAverage φ a ((b - a) / N) t - φ t‖ ≤ η := by
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos (sub_pos.2 (ht.1.trans ht.2)) (Nat.cast_pos.2 hN)
  obtain ⟨hmem, hsub⟩ := cell_of_mem_Ioo ht hN
  rw [← hh_def] at hmem hsub
  set k := cellIndex a h t - 1
  set p := a + (k : ℝ) * h
  set q := a + ((k : ℝ) + 1) * h
  have hpq : p ≤ q := by simp only [p, q]; nlinarith
  have hlen : q - p = h := by simp only [p, q]; ring
  have hint : ∫ s in p..q, (φ s - φ t) = (∫ s in p..q, φ s) - h • φ t := by
    rw [intervalIntegral.integral_sub (hφ.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, hlen]
  have hbound : ‖∫ s in p..q, (φ s - φ t)‖ ≤ η * |q - p| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
    rw [uIoc_of_le hpq] at hs
    refine hη s (hsub hs) ?_
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, hmem.1, hmem.2]
  have heq : stepAverage φ a h t - φ t = h⁻¹ • ∫ s in p..q, (φ s - φ t) := by
    rw [hint, smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul, stepAverage, cellAverage]
  rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, hlen, abs_of_pos hh] at *
  calc h⁻¹ * ‖∫ s in p..q, (φ s - φ t)‖ ≤ h⁻¹ * (η * h) := by gcongr
    _ = η := by field_simp

/-- The cellwise average of `g - φ` is the difference of the cellwise averages on `(a, b)`. -/
private theorem stepAverage_sub {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N)
    {g φ : ℝ → H} (hg : IntegrableOn g (Ioo a b)) (hφ : IntegrableOn φ (Ioo a b)) :
    stepAverage (fun s ↦ g s - φ s) a ((b - a) / N) t =
      stepAverage g a ((b - a) / N) t - stepAverage φ a ((b - a) / N) t := by
  have hk := (cellIndex_mem_Icc ht hN).1
  simp only [stepAverage, cellAverage]
  rw [intervalIntegral.integral_sub (intervalIntegrable_cell hg hN hk (ht.1.trans ht.2).le)
    (intervalIntegrable_cell hφ hN hk (ht.1.trans ht.2).le), smul_sub]

/-- The `L²` estimate behind `tendsto_integral_norm_stepAverage_sub_sq`, for a continuous
approximation `φ` of `g` that varies by less than `η` over distances less than `δ`. -/
private theorem integral_norm_stepAverage_sub_sq_le [CompleteSpace H] {a b : ℝ} (hab : a < b)
    {N : ℕ} (hN : 0 < N)
    {g φ : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) (hφc : Continuous φ)
    (hφL : MemLp φ 2 (volume.restrict (Ioo a b))) {η δ : ℝ}
    (hδφ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist x y < δ → dist (φ x) (φ y) < η)
    (hhδ : (b - a) / N < δ) :
    ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / N) t - g t‖ ^ 2 ≤
      3 * ((∫ t in Ioo a b, ‖g t - φ t‖ ^ 2) + η ^ 2 * (b - a) +
        ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2) := by
  set h := (b - a) / N with hh_def
  set μ := volume.restrict (Ioo a b)
  have hstep (f : ℝ → H) : MemLp (stepAverage f a h) 2 μ :=
    memLp_comp_cellIndex hN (fun n ↦ cellAverage f a h (n - 1)) 2
  have hgφ : MemLp (fun t ↦ g t - φ t) 2 μ := hg.sub hφL
  have hle := integral_norm_sq_le_three_mul (μ := μ) (f := fun t ↦ stepAverage g a h t - g t)
    (hstep fun s ↦ g s - φ s) ((hstep φ).sub hφL) (hφL.sub hg) <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [stepAverage_sub ht hN (hg.integrable one_le_two) (hφL.integrable one_le_two),
        ← hh_def]
      simp only [Pi.sub_apply]
      abel
  refine hle.trans (mul_le_mul_of_nonneg_left (add_le_add_three
    (integral_norm_stepAverage_sq_le hab hN hgφ) ?_ (le_of_eq ?_)) (by norm_num))
  · have hpt : ∀ t ∈ Ioo a b, ‖stepAverage φ a h t - φ t‖ ^ 2 ≤ η ^ 2 := fun t ht ↦ by
      refine pow_le_pow_left₀ (norm_nonneg _) (norm_stepAverage_sub_le hφc ht hN
        fun s hs hst ↦ ?_) 2
      rw [← dist_eq_norm]
      exact (hδφ s hs t (Ioo_subset_Icc_self ht)
        (by rw [Real.dist_eq]; exact hst.trans_lt hhδ)).le
    calc ∫ t in Ioo a b, ‖stepAverage φ a h t - φ t‖ ^ 2 ≤ ∫ _ in Ioo a b, η ^ 2 :=
          setIntegral_mono_on ((memLp_two_iff_integrable_sq_norm
            ((hstep φ).sub hφL).aestronglyMeasurable).1 ((hstep φ).sub hφL))
            (integrableOn_const (by simp)) measurableSet_Ioo hpt
      _ = η ^ 2 * (b - a) := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.2 hab.le), mul_comm]
  · exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [Pi.sub_apply, norm_sub_rev])

/-- **Cellwise averages converge in `L²`.** For `g ∈ L²(a, b)`, the averages of `g` over the
cells of the uniform partition into `N` cells converge to `g` in `L²(a, b)` as `N → ∞`. -/
private theorem tendsto_integral_norm_stepAverage_sub_sq [CompleteSpace H] {a b : ℝ} (hab : a < b)
    {g : ℝ → H}
    (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    Tendsto (fun N : ℕ ↦ ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / N) t - g t‖ ^ 2) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Approximate `g` by a continuous `φ` in `L²(a, b)`.
  have hg' : MemLp ((Ioo a b).indicator g) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 hg
  obtain ⟨φ, -, hφε, hφc, hφL⟩ :=
    hg'.exists_hasCompactSupport_integral_rpow_sub_le two_pos (show 0 < ε / 12 by positivity)
  rw [ENNReal.ofReal_ofNat] at hφL hg'
  have hφL' : MemLp φ 2 (volume.restrict (Ioo a b)) := hφL.restrict _
  have hφε' : ∫ x, ‖(Ioo a b).indicator g x - φ x‖ ^ 2 ≤ ε / 12 := by
    simpa only [Real.rpow_two] using hφε
  have hgφ2 : ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2 ≤ ε / 12 :=
    calc ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2
        = ∫ t in Ioo a b, ‖(Ioo a b).indicator g t - φ t‖ ^ 2 :=
          setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by simp [indicator_of_mem ht]
      _ ≤ ∫ t, ‖(Ioo a b).indicator g t - φ t‖ ^ 2 :=
          setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm
            (hg'.sub hφL).aestronglyMeasurable).1 (hg'.sub hφL))
            (Eventually.of_forall fun _ ↦ by positivity)
      _ ≤ ε / 12 := hφε'
  -- Uniform continuity of `φ` on `[a, b]`.
  set η := Real.sqrt (ε / (12 * (b - a)))
  have hη : 0 < η := Real.sqrt_pos.2 (div_pos hε (by linarith))
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφc.continuousOn) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N₀ + 1, fun N hN ↦ ?_⟩
  have hN0 : 0 < N := by omega
  have hhδ : (b - a) / N < δ := by
    rw [div_lt_iff₀ (Nat.cast_pos.2 hN0)]
    rw [div_lt_iff₀ hδ] at hN₀
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    nlinarith
  have hηε : η ^ 2 * (b - a) = ε / 12 := by
    rw [Real.sq_sqrt (div_nonneg hε.le (by linarith))]
    field_simp
  have hnn : 0 ≤ ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / N) t - g t‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have := integral_norm_stepAverage_sub_sq_le hab hN0 hg hφc hφL' hδφ hhδ
  linarith

/-! ### The interpolants of the scheme -/

section Interpolant

variable (x : ℕ → V) (a h : ℝ)

/-- The difference quotients of the scheme, constant on each cell: `(x k - x (k - 1)) / h` on the
`k`-th cell. -/
private def rotheDeriv (t : ℝ) : V :=
  h⁻¹ • (x (cellIndex a h t) - x (cellIndex a h t - 1))

/-- The piecewise linear interpolant of the scheme, the primitive of `rotheDeriv` from `x 0`. -/
private def rotheInterp (t : ℝ) : V :=
  x 0 + ∫ s in a..t, rotheDeriv x a h s

variable {x a h}

/-- On a cell, the difference quotient is constant. -/
private theorem intervalIntegral_rotheDeriv_cell [CompleteSpace V] (hh : 0 < h) {k : ℕ} {s : ℝ}
    (hs : s ∈ Icc (a + k * h) (a + (k + 1) * h)) :
    IntervalIntegrable (rotheDeriv x a h) volume (a + k * h) s ∧
      ∫ r in (a + k * h)..s, rotheDeriv x a h r = ((s - (a + k * h)) / h) • (x (k + 1) - x k) := by
  have hae : ∀ᵐ r ∂volume, r ∈ Ι (a + k * h) s →
      rotheDeriv x a h r = h⁻¹ • (x (k + 1) - x k) := Eventually.of_forall fun r hr ↦ by
    rw [uIoc_of_le hs.1] at hr
    rw [rotheDeriv, cellIndex_eq hh ⟨hr.1, hr.2.trans hs.2⟩, Nat.add_sub_cancel]
  refine ⟨(intervalIntegrable_const (c := h⁻¹ • (x (k + 1) - x k))).congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).2 (hae.mono fun r hr hr' ↦ (hr hr').symm)), ?_⟩
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_smul,
    div_eq_mul_inv]

/-- The difference quotient is interval integrable from `a` to every node. -/
private theorem intervalIntegrable_rotheDeriv_node [CompleteSpace V] (hh : 0 < h) (k : ℕ) :
    IntervalIntegrable (rotheDeriv x a h) volume a (a + k * h) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := (intervalIntegral_rotheDeriv_cell (x := x) hh (k := k) (s := a + (k + 1) * h)
      ⟨by nlinarith, le_rfl⟩).1
    push_cast
    exact ih.trans hk

/-- **The interpolant on a cell.** On `[a + k h, a + (k + 1) h]`,
`rotheInterp s = x k + ((s - (a + k h)) / h) (x (k + 1) - x k)`. -/
private theorem rotheInterp_eq [CompleteSpace V] (hh : 0 < h) {k : ℕ} {s : ℝ}
    (hs : s ∈ Icc (a + k * h) (a + (k + 1) * h)) :
    rotheInterp x a h s = x k + ((s - (a + k * h)) / h) • (x (k + 1) - x k) := by
  induction k generalizing s with
  | zero =>
    have := (intervalIntegral_rotheDeriv_cell (x := x) hh (k := 0) hs).2
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, zero_add] at this ⊢
    rw [rotheInterp, this]
  | succ k ih =>
    have hnode : rotheInterp x a h (a + (k + 1 : ℕ) * h) = x (k + 1) := by
      rw [ih ⟨by push_cast; nlinarith, by push_cast; exact le_rfl⟩]
      push_cast
      rw [show (a + (k + 1) * h - (a + k * h)) / h = 1 by field_simp; ring, one_smul,
        add_sub_cancel]
    obtain ⟨hint, hval⟩ := intervalIntegral_rotheDeriv_cell (x := x) hh (k := k + 1) hs
    rw [rotheInterp, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rotheDeriv_node hh (k + 1)) hint, ← add_assoc, hval]
    rw [rotheInterp] at hnode
    rw [hnode]

/-- The interpolant takes the values of the scheme at the nodes. -/
private theorem rotheInterp_node [CompleteSpace V] (hh : 0 < h) (k : ℕ) :
    rotheInterp x a h (a + k * h) = x k := by
  rw [rotheInterp_eq hh ⟨le_rfl, by nlinarith⟩, sub_self, zero_div, zero_smul, add_zero]

/-- On `(a, b)`, the interpolant is within one step of the piecewise constant interpolant. -/
private theorem norm_rotheInterp_sub_le [CompleteSpace V] {b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ}
    (hN : 0 < N)
    (hh : h = (b - a) / N) :
    ‖rotheInterp x a h t - x (cellIndex a h t)‖ ≤
      ‖x (cellIndex a h t) - x (cellIndex a h t - 1)‖ := by
  subst hh
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 (ht.1.trans ht.2)) (Nat.cast_pos.2 hN)
  obtain ⟨hmem, -⟩ := cell_of_mem_Ioo ht hN
  set k := cellIndex a ((b - a) / N) t
  have hk : 1 ≤ k := (cellIndex_mem_Icc ht hN).2
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [rotheInterp_eq hh (Ioc_subset_Icc_self hmem), hk']
  set c := (t - (a + ((k - 1 : ℕ) : ℝ) * ((b - a) / N))) / ((b - a) / N)
  have hc0 : 0 ≤ c := div_nonneg (by linarith [hmem.1]) hh.le
  have hc1 : c ≤ 1 := by rw [div_le_one hh]; linarith [hmem.2]
  rw [show x (k - 1) + c • (x k - x (k - 1)) - x k = (1 - c) • -(x k - x (k - 1)) by
    rw [smul_neg, sub_smul, one_smul]; abel, norm_smul, norm_neg, Real.norm_of_nonneg (by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- The difference quotient of the scheme is in `L²(a, b)`. -/
private theorem memLp_rotheDeriv {b : ℝ} {N : ℕ} (hN : 0 < N) (p : ENNReal) :
    MemLp (rotheDeriv x a ((b - a) / N)) p (volume.restrict (Ioo a b)) :=
  memLp_comp_cellIndex hN (fun n ↦ ((b - a) / N)⁻¹ • (x n - x (n - 1))) p

/-- The interpolant is continuous on `[a, b]`. -/
private theorem continuousOn_rotheInterp {b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    ContinuousOn (rotheInterp x a ((b - a) / N)) (Icc a b) := by
  have hi : IntegrableOn (rotheDeriv x a ((b - a) / N)) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2
      ((memLp_rotheDeriv hN 1).integrable le_rfl)
  rw [← uIcc_of_le hab.le]
  exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval hi)

/-- The interpolant is in `L²(a, b)`. -/
private theorem memLp_rotheInterp {b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    MemLp (rotheInterp x a ((b - a) / N)) 2 (volume.restrict (Ioo a b)) := by
  have hc := continuousOn_rotheInterp (x := x) hab hN
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine MemLp.of_bound ((hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

/-- **The weak derivative of the interpolant** on `(a, b)` is the difference quotient. -/
private theorem hasWeakLineDerivOn_rotheInterp [CompleteSpace V] {b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (rotheInterp x a ((b - a) / N))
      (rotheDeriv x a ((b - a) / N)) 1 := by
  set h := (b - a) / N
  have hi : IntegrableOn (rotheDeriv x a h) (Ioo a b) := (memLp_rotheDeriv hN 1).integrable le_rfl
  have hiI : IntegrableOn (rotheDeriv x a h) (Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2 hi
  set t₀ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by simp only [t₀]; linarith, by simp only [t₀]; linarith⟩
  have hprim := hasWeakLineDerivOn_intervalIntegral hi.locallyIntegrableOn ht₀
  have hsum := (hasWeakLineDerivOn_const (μ := volume) (Ω := ⟨Ioo a b, isOpen_Ioo⟩) (v := 1)
    (x 0 + ∫ s in a..t₀, rotheDeriv x a h s)).add hprim
  refine (hsum.congr_ae ?_).congr_ae_deriv (Eventually.of_forall fun t ↦ by simp)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hint (p q : ℝ) (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
      IntervalIntegrable (rotheDeriv x a h) volume p q :=
    (hiI.mono_set (uIcc_subset_Icc hp hq)).intervalIntegrable
  simp only [Pi.add_apply, rotheInterp, add_assoc]
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hint a t₀ (left_mem_Icc.2 hab.le) (Ioo_subset_Icc_self ht₀))
    (hint t₀ t (Ioo_subset_Icc_self ht₀) (Ioo_subset_Icc_self ht))]

/-- `∫_{(a, b)} ‖ι (rotheDeriv t)‖² = ∑_{k < N} ‖ι (x (k + 1) - x k)‖² / h`. -/
private theorem integral_norm_rotheDeriv_sq {b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    ∫ t in Ioo a b, ‖ι (rotheDeriv x a ((b - a) / N) t)‖ ^ 2 =
      ∑ k ∈ Finset.range N, ‖ι (x (k + 1) - x k)‖ ^ 2 / ((b - a) / N) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have := integral_Ioo_comp_cellIndex hab hN
    (fun n ↦ ‖ι (((b - a) / N)⁻¹ • (x n - x (n - 1)))‖ ^ 2)
  simp only [rotheDeriv]
  rw [this]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Nat.add_sub_cancel, map_smul, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, smul_eq_mul]
  field_simp

/-- `∫_{(a, b)} ‖rotheInterp t - x (cellIndex t)‖² ≤ ∑_{k < N} h ‖x (k + 1) - x k‖²`. -/
private theorem integral_norm_rotheInterp_sub_sq_le [CompleteSpace V] {b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N) :
    ∫ t in Ioo a b, ‖rotheInterp x a ((b - a) / N) t - x (cellIndex a ((b - a) / N) t)‖ ^ 2 ≤
      ∑ k ∈ Finset.range N, (b - a) / N * ‖x (k + 1) - x k‖ ^ 2 := by
  have hcell := integral_Ioo_comp_cellIndex hab hN (fun n ↦ ‖x n - x (n - 1)‖ ^ 2)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hcell
  rw [← hcell]
  have hmem : MemLp (fun t ↦ rotheInterp x a ((b - a) / N) t - x (cellIndex a ((b - a) / N) t)) 2
      (volume.restrict (Ioo a b)) :=
    (memLp_rotheInterp hab hN).sub (memLp_comp_cellIndex hN x 2)
  refine setIntegral_mono_on ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem)
    ((memLp_comp_cellIndex hN (fun n ↦ ‖x n - x (n - 1)‖ ^ 2) 1).integrable le_rfl)
    measurableSet_Ioo fun t ht ↦ ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_rotheInterp_sub_le ht hN rfl) 2

end Interpolant

/-! ### The scheme for a time-dependent operator -/

section Scheme

variable [CompleteSpace V] {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α L : ℝ}

/-- The nodes `a + k (b - a) / N`, `k ≤ N`, lie in `[a, b]`. -/
private theorem node_mem_Icc (hab : a ≤ b) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    a + k * ((b - a) / N) ∈ Icc a b := by
  have hh : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) N.cast_nonneg
  refine ⟨by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], ?_⟩
  calc a + k * ((b - a) / N) ≤ a + N * ((b - a) / N) := by gcongr
    _ = b := by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]; ring

/-- **The scheme with its uniform energy bound.** For the partition of `[a, b]` into `N` cells of
length `h`, the implicit Euler scheme for `u' + A(t) u = ι* g`, `u(a) = v₀`, with the operators
frozen at the right end of each step and `g` averaged over each step, has a solution with
`A(a + k h) (x k) (x k) ≤ M` for `k ≤ N` and
`∑_{j < N} (‖ι (x (j + 1) - x j)‖² / h + α ‖x (j + 1) - x j‖²) ≤ M`, where
`M = exp (L (b - a) / α) (A a v₀ v₀ + ∫ ‖g‖²)` does not depend on `N`. -/
private theorem exists_rotheScheme_bound (hab : a < b) {N : ℕ} (hN : 0 < N)
    (hsymm : ∀ t ∈ Icc a b, ∀ v w, A t v w = A t w v) (hα : 0 < α)
    (hA : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) (v₀ : V) :
    ∃ x : ℕ → V, x 0 = v₀ ∧
      (∀ k < N, ∀ v, ⟪ι (x (k + 1) - x k), ι v⟫_ℝ +
          (b - a) / N * A (a + (k + 1 : ℕ) * ((b - a) / N)) (x (k + 1)) v =
        (b - a) / N * ⟪cellAverage g a ((b - a) / N) k, ι v⟫_ℝ) ∧
      (∀ k ≤ N, A (a + k * ((b - a) / N)) (x k) (x k) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2)) ∧
      ∑ j ∈ Finset.range N, (‖ι (x (j + 1) - x j)‖ ^ 2 / ((b - a) / N) +
          α * ‖x (j + 1) - x j‖ ^ 2) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) := by
  set h := (b - a) / N
  have hh : 0 < h := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  set B : ℕ → V →L[ℝ] StrongDual ℝ V := fun k ↦ A (a + (min k N : ℕ) * h)
  have hnode (k : ℕ) : a + (min k N : ℕ) * h ∈ Icc a b := node_mem_Icc hab.le hN (min_le_right _ _)
  have hBk (k : ℕ) (hk : k ≤ N) : B k = A (a + k * h) := by simp only [B, min_eq_left hk]
  obtain ⟨x, hx0, hx⟩ := exists_rotheScheme (ι := ι) (B := B) hα hh
    (fun k v ↦ hA _ (hnode _) v) (cellAverage g a h) v₀
  have hstep (k : ℕ) (hk : k < N) (v : V) := by
    have := hx k v
    rwa [hBk (k + 1) hk] at this
  have hE (k : ℕ) (hk : k ≤ N) := rotheScheme_energy (ι := ι) (B := B) hα hL hh
    (fun k _ ↦ hsymm _ (hnode k)) (fun k _ ↦ hA _ (hnode k))
    (fun k hk ↦ by
      rw [hBk (k + 1) hk, hBk k hk.le]
      refine (hLip _ (node_mem_Icc hab.le hN hk.le) _ (node_mem_Icc hab.le hN hk)).trans_eq ?_
      push_cast
      rw [show a + (k + 1) * h - (a + k * h) = h by ring, abs_of_pos hh])
    (fun k _ v ↦ hx k v) hk
  have hB0 : B 0 = A a := by simp [B]
  have hG (k : ℕ) (hk : k ≤ N) := sum_mul_norm_cellAverage_sq_le hab hN hg hk
  have hA0 : 0 ≤ A a v₀ v₀ := (by positivity : (0 : ℝ) ≤ α * ‖v₀‖ ^ 2).trans
    (hA a (left_mem_Icc.2 hab.le) v₀)
  have hexp (k : ℕ) (hk : k ≤ N) := one_add_pow_le_exp hα hL hab.le (a := a) (b := b) hk
  have hbound (k : ℕ) (hk : k ≤ N) :
      (1 + L * h / α) ^ k * (B 0 (x 0) (x 0) + ∑ j ∈ Finset.range k, h * ‖cellAverage g a h j‖ ^ 2)
        ≤ Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) := by
    rw [hB0, hx0]
    exact mul_le_mul (hexp k hk) (add_le_add_right (hG k hk) _)
      (add_nonneg hA0 (Finset.sum_nonneg fun _ _ ↦ by positivity)) (Real.exp_pos _).le
  refine ⟨x, hx0, hstep, fun k hk ↦ ?_, ?_⟩
  · have := hE k hk
    rw [hBk k hk] at this
    have hS : 0 ≤ ∑ j ∈ Finset.range k,
        (‖ι (x (j + 1) - x j)‖ ^ 2 / h + α * ‖x (j + 1) - x j‖ ^ 2) :=
      Finset.sum_nonneg fun _ _ ↦ by positivity
    linarith [hbound k hk]
  · have := hE N le_rfl
    rw [hBk N le_rfl] at this
    have hEN : 0 ≤ A (a + N * h) (x N) (x N) :=
      (by positivity : (0 : ℝ) ≤ α * ‖x N‖ ^ 2).trans (hA _ (node_mem_Icc hab.le hN le_rfl) _)
    linarith [hbound N le_rfl]

/-- A point of `(a, b)` is within one cell length of the right node of its cell. -/
private theorem abs_sub_node_le {t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N) :
    a + cellIndex a ((b - a) / N) t * ((b - a) / N) ∈ Icc a b ∧
      |t - (a + cellIndex a ((b - a) / N) t * ((b - a) / N))| ≤ (b - a) / N := by
  obtain ⟨hmem, hsub⟩ := cell_of_mem_Ioo ht hN
  have hge := (cellIndex_mem_Icc ht hN).2
  have hcast : ((cellIndex a ((b - a) / N) t - 1 : ℕ) : ℝ) + 1 = cellIndex a ((b - a) / N) t := by
    rw [Nat.cast_sub hge, Nat.cast_one, sub_add_cancel]
  rw [hcast] at hmem hsub
  refine ⟨hsub (right_mem_Ioc.2 (hmem.1.trans_le hmem.2)), ?_⟩
  rw [abs_sub_comm, abs_of_nonneg (by linarith [hmem.2])]
  have := hmem.1
  rw [Nat.cast_sub hge, Nat.cast_one, sub_mul, one_mul] at this
  linarith

omit [CompleteSpace V] in
/-- **The scheme as an equation on `(a, b)`.** On each cell the difference quotient and the
piecewise constant interpolant satisfy `ι* ι D + A(node) ū = ι* G`, with the operator frozen at the
right node of the cell and the cell average `G` of `g`. -/
private theorem rotheDeriv_add_eq {g : ℝ → H} {x : ℕ → V} (hab : a < b) {N : ℕ} (hN : 0 < N)
    (hx : ∀ k < N, ∀ v, ⟪ι (x (k + 1) - x k), ι v⟫_ℝ +
          (b - a) / N * A (a + (k + 1 : ℕ) * ((b - a) / N)) (x (k + 1)) v =
        (b - a) / N * ⟪cellAverage g a ((b - a) / N) k, ι v⟫_ℝ) {t : ℝ} (ht : t ∈ Ioo a b) :
    ι.gelfandDual (ι (rotheDeriv x a ((b - a) / N) t)) +
        A (a + cellIndex a ((b - a) / N) t * ((b - a) / N)) (x (cellIndex a ((b - a) / N) t)) =
      ι.gelfandDual (stepAverage g a ((b - a) / N) t) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  obtain ⟨hlt, hge⟩ := cellIndex_mem_Icc ht hN
  obtain ⟨k, hk⟩ : ∃ k, cellIndex a ((b - a) / N) t = k + 1 :=
    ⟨_, (Nat.sub_add_cancel hge).symm⟩
  rw [hk, Nat.add_sub_cancel] at hlt
  have hD : rotheDeriv x a ((b - a) / N) t = ((b - a) / N)⁻¹ • (x (k + 1) - x k) := by
    rw [rotheDeriv, hk, Nat.add_sub_cancel]
  have hG : stepAverage g a ((b - a) / N) t = cellAverage g a ((b - a) / N) k := by
    rw [stepAverage, hk, Nat.add_sub_cancel]
  rw [hD, hG, hk]
  ext v
  have := hx k hlt v
  simp only [add_apply, smul_apply, ContinuousLinearMap.gelfandDual_apply, map_smul, smul_eq_mul]
  rw [eq_sub_of_add_eq this, mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul,
    one_mul]
  ring

end Scheme

/-! ### Comparison with the weak solution -/

section Comparison

variable [CompleteSpace V] {a b α : ℝ}

omit [CompleteSpace V] in
/-- Applying operators bounded by `c` on `(a, b)` to `f ∈ L²(a, b; V)` gives an element of
`L²(a, b; V*)` with `∫ ‖B t (f t)‖² ≤ c² ∫ ‖f‖²`. -/
private theorem memLp_apply_of_norm_le {B : ℝ → V →L[ℝ] StrongDual ℝ V} {f : ℝ → V} {c : ℝ}
    (hB : AEStronglyMeasurable B (volume.restrict (Ioo a b))) (hc : ∀ t ∈ Ioo a b, ‖B t‖ ≤ c)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    MemLp (fun t ↦ B t (f t)) 2 (volume.restrict (Ioo a b)) ∧
      ∫ t in Ioo a b, ‖B t (f t)‖ ^ 2 ≤ c ^ 2 * ∫ t in Ioo a b, ‖f t‖ ^ 2 := by
  have hle : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖B t (f t)‖ ≤ c * ‖f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ((B t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hc t ht) (norm_nonneg _))
  have hm : MemLp (fun t ↦ B t (f t)) 2 (volume.restrict (Ioo a b)) :=
    hf.of_le_mul ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V)
      (F := StrongDual ℝ V)).continuous.comp_aestronglyMeasurable
        (hB.prodMk hf.aestronglyMeasurable)) hle
  exact ⟨hm, integral_norm_sq_le_sq_mul_of_norm_le hm hf hle⟩

/-- **Comparison of the weak solution with an approximate solution.** Let `u` be a weak solution
of `u' + A(t) u = ι* g`, `u(a) = v₀`, with coercive `A(t)`, and let `uh` start at `v₀` and solve
`ι* ι uh' + Ah(t) ub = ι* gh` for some `ub` and operators `Ah(t)` with `‖A(t)‖ ≤ Λ` and
`‖A(t) - Ah(t)‖ ≤ ε₁`. Then the energy estimate for `uh - u` gives
`α² ∫ ‖uh - u‖² ≤ 3 (‖ι‖² ∫ ‖gh - g‖² + Λ² ∫ ‖uh - ub‖² + ε₁² ∫ ‖ub‖²)`. -/
private theorem integral_norm_sub_sq_le_of_approx
    {A Ah : ℝ → V →L[ℝ] StrongDual ℝ V} {Λ ε₁ : ℝ} (hα : 0 < α) (hab : a ≤ b)
    (hA : ∀ t ∈ Ioo a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (hAm : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hAhm : AEStronglyMeasurable Ah (volume.restrict (Ioo a b)))
    (hΛ : ∀ t ∈ Ioo a b, ‖A t‖ ≤ Λ) (hε : ∀ t ∈ Ioo a b, ‖A t - Ah t‖ ≤ ε₁)
    {g gh : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hgh : MemLp gh 2 (volume.restrict (Ioo a b)))
    {u : ℝ → V} {u' : ℝ → StrongDual ℝ V} {w : ℝ → H} {v₀ : V}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A t (u t) = ι.gelfandDual (g t))
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a = ι v₀)
    {uh ub D : ℝ → V} (hD : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ uh D 1)
    (huh : MemLp uh 2 (volume.restrict (Ioo a b))) (hDm : MemLp D 2 (volume.restrict (Ioo a b)))
    (hub : MemLp ub 2 (volume.restrict (Ioo a b))) (huhc : ContinuousOn uh (Icc a b))
    (huh₀ : uh a = v₀)
    (hscheme : ∀ t ∈ Ioo a b, ι.gelfandDual (ι (D t)) + Ah t (ub t) = ι.gelfandDual (gh t)) :
    α ^ 2 * ∫ t in Ioo a b, ‖uh t - u t‖ ^ 2 ≤
      3 * ((‖ι‖ ^ 2 * ∫ t in Ioo a b, ‖gh t - g t‖ ^ 2) +
        (Λ ^ 2 * ∫ t in Ioo a b, ‖uh t - ub t‖ ^ 2) + ε₁ ^ 2 * ∫ t in Ioo a b, ‖ub t‖ ^ 2) := by
  set μ := volume.restrict (Ioo a b)
  have hF₁ : MemLp (fun t ↦ ι.gelfandDual (gh t - g t)) 2 μ :=
    ι.gelfandDual.comp_memLp' (hgh.sub hg)
  obtain ⟨hF₂, h₂⟩ := memLp_apply_of_norm_le hAm hΛ (huh.sub hub)
  obtain ⟨hF₃, h₃⟩ := memLp_apply_of_norm_le (hAm.sub hAhm) hε hub
  simp only [Pi.sub_apply] at hF₂ h₂ hF₃ h₃
  -- The error `uh - u` solves `e' + A(t) e = F₁ + F₂ + F₃`.
  have he : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι (uh t - u t))) (fun t ↦ ι.gelfandDual (ι (D t)) - u' t) 1 := by
    convert (hD.clm_comp (ι.gelfandDual ∘L ι)).sub h using 1 <;> ext t : 1 <;> simp
  have heq' : ∀ᵐ t ∂μ, (ι.gelfandDual (ι (D t)) - u' t) + A t (uh t - u t) =
      ι.gelfandDual (gh t - g t) + A t (uh t - ub t) + (A t - Ah t) (ub t) := by
    filter_upwards [heq, ae_restrict_mem measurableSet_Ioo] with t ht ht'
    rw [eq_sub_of_add_eq (hscheme t ht'), eq_sub_of_add_eq ht]
    simp only [map_sub, sub_apply]
    abel
  have hest := he.norm_sq_add_mul_integral_le_of_gelfandDual (A := A) (β := 0) (huh.sub hu)
    ((ι.gelfandDual.comp_memLp' (ι.comp_memLp' hDm)).sub hu') ((hF₁.add hF₂).add hF₃) hα le_rfl
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht v; simpa using hA t ht v)
    heq' (w := fun t ↦ ι (uh t) - w t) ((ι.continuous.comp_continuousOn huhc).sub hw)
    (by filter_upwards [hae] with t ht; simp [← ht]) (right_mem_Icc.2 hab)
  simp only [huh₀, h₀, sub_self, norm_zero, mul_zero, zero_mul, Real.exp_zero, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hest
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hest
  have hF := integral_norm_sq_le_three_mul (μ := μ) hF₁ hF₂ hF₃ (Eventually.of_forall fun _ ↦ rfl)
  have h₁ := integral_norm_sq_le_sq_mul_of_norm_le hF₁ (hgh.sub hg)
    (Eventually.of_forall fun t ↦ by
      simpa using ι.gelfandDual.le_opNorm (gh t - g t))
  simp only [Pi.add_apply] at hest
  simp only [Pi.sub_apply] at h₁
  have hnn : 0 ≤ ‖ι (uh b) - w b‖ ^ 2 := sq_nonneg _
  have key : α * ∫ t in Ioo a b, ‖uh t - u t‖ ^ 2 ≤
      α⁻¹ * ∫ t in Ioo a b, ‖ι.gelfandDual (gh t - g t) + A t (uh t - ub t) +
        (A t - Ah t) (ub t)‖ ^ 2 := by linarith
  have key' := mul_le_mul_of_nonneg_left key hα.le
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul, ← sq] at key'
  linarith

end Comparison

/-! ### The approximations for one partition -/

section Approx

variable [CompleteSpace V] {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α L : ℝ}

omit [CompleteSpace V] in
/-- A family of operators that is `L`-Lipschitz on `[a, b]` is continuous there. -/
private theorem continuousOn_of_norm_sub_le {L : ℝ}
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|) :
    ContinuousOn A (Icc a b) := by
  intro s hs
  refine (tendsto_iff_norm_sub_tendsto_zero (f := A) (b := A s)).2 ?_
  refine squeeze_zero' (Eventually.of_forall fun t ↦ norm_nonneg (A t - A s))
    (eventually_nhdsWithin_of_forall fun t ht ↦ hLip s hs t ht) ?_
  have : Tendsto (fun t : ℝ ↦ L * |t - s|) (𝓝 s) (𝓝 (L * |s - s|)) :=
    (continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto s
  rw [sub_self, abs_zero, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

omit [CompleteSpace V] in
/-- On `(a, b)`, operators that are `L`-Lipschitz on `[a, b]` are bounded by `‖A a‖ + L (b - a)`,
and differ by at most `L h` from their value at the right node of the cell. -/
private theorem norm_le_and_norm_sub_node_le (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖A t‖ ≤ ‖A a‖ + L * (b - a) ∧
      ‖A t - A (a + cellIndex a ((b - a) / N) t * ((b - a) / N))‖ ≤ L * ((b - a) / N) := by
  have hab : a ≤ b := (ht.1.trans ht.2).le
  obtain ⟨hn, hd⟩ := abs_sub_node_le ht hN
  refine ⟨?_, ?_⟩
  · have := hLip a (left_mem_Icc.2 hab) t (Ioo_subset_Icc_self ht)
    calc ‖A t‖ = ‖A a + (A t - A a)‖ := by rw [add_sub_cancel (A a) (A t)]
      _ ≤ ‖A a‖ + L * |t - a| := (norm_add_le (A a) (A t - A a)).trans (add_le_add_right this _)
      _ ≤ ‖A a‖ + L * (b - a) := by
          gcongr
          rw [abs_of_pos (sub_pos.2 ht.1)]
          linarith [ht.2]
  · rw [norm_sub_rev (A t) _]
    exact (hLip _ (Ioo_subset_Icc_self ht) _ hn).trans
      (by rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hd hL)

/-- The `L²` bounds on the interpolants of a scheme with energy at most `M`:
`∫ ‖uh - ub‖² ≤ h M / α` and `∫ ‖ub‖² ≤ (b - a) M / α`. -/
private theorem rotheScheme_integral_le (hab : a < b) {N : ℕ} (hN : 0 < N) (hα : 0 < α)
    (hA : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) {M : ℝ} {x : ℕ → V}
    (hE : ∀ k ≤ N, A (a + k * ((b - a) / N)) (x k) (x k) ≤ M)
    (hS : ∑ j ∈ Finset.range N, (‖ι (x (j + 1) - x j)‖ ^ 2 / ((b - a) / N) +
      α * ‖x (j + 1) - x j‖ ^ 2) ≤ M) :
    (∀ k ≤ N, ‖x k‖ ^ 2 ≤ M / α) ∧
      ∫ t in Ioo a b, ‖rotheInterp x a ((b - a) / N) t - x (cellIndex a ((b - a) / N) t)‖ ^ 2 ≤
        (b - a) / N * (M / α) ∧
      ∫ t in Ioo a b, ‖x (cellIndex a ((b - a) / N) t)‖ ^ 2 ≤ (b - a) * (M / α) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hxk (k : ℕ) (hk : k ≤ N) : ‖x k‖ ^ 2 ≤ M / α := by
    rw [le_div_iff₀ hα, mul_comm]
    exact (hA _ (node_mem_Icc hab.le hN hk) _).trans (hE k hk)
  have hδ : ∑ k ∈ Finset.range N, ‖x (k + 1) - x k‖ ^ 2 ≤ M / α := by
    rw [le_div_iff₀ hα, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) hS
    rw [mul_comm]
    exact le_add_of_nonneg_left (by positivity)
  have hdiff := integral_norm_rotheInterp_sub_sq_le (x := x) hab hN
  rw [← Finset.mul_sum] at hdiff
  refine ⟨hxk, hdiff.trans (mul_le_mul_of_nonneg_left hδ hh.le), ?_⟩
  rw [integral_Ioo_comp_cellIndex hab hN (fun n ↦ ‖x n‖ ^ 2)]
  simp only [smul_eq_mul]
  calc ∑ k ∈ Finset.range N, (b - a) / N * ‖x (k + 1)‖ ^ 2
      ≤ ∑ _k ∈ Finset.range N, (b - a) / N * (M / α) :=
        Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left
          (hxk (k + 1) (Finset.mem_range.1 hk)) hh.le
    _ = (b - a) * (M / α) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]

omit [CompleteSpace V] in
/-- The energy of the piecewise constant interpolant at a time `t ∈ (a, b)`, measured with `A t`,
is at most `(1 + L h / α) M` when the energies at the nodes are at most `M`. -/
private theorem apply_rotheScheme_le (hab : a < b) {N : ℕ} (hN : 0 < N) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|) {M : ℝ} {x : ℕ → V}
    (hE : ∀ k ≤ N, A (a + k * ((b - a) / N)) (x k) (x k) ≤ M)
    (hxk : ∀ k ≤ N, ‖x k‖ ^ 2 ≤ M / α) {t : ℝ} (ht : t ∈ Ioo a b) :
    A t (x (cellIndex a ((b - a) / N) t)) (x (cellIndex a ((b - a) / N) t)) ≤
      (1 + L * ((b - a) / N) / α) * M := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hd := (norm_le_and_norm_sub_node_le hL hLip hN ht).2
  set κ := cellIndex a ((b - a) / N) t
  have hκ : κ ≤ N := by have := (cellIndex_mem_Icc ht hN).1; omega
  set n := a + κ * ((b - a) / N)
  have h1 : (A t - A n) (x κ) (x κ) ≤ ‖(A t - A n) (x κ)‖ * ‖x κ‖ :=
    (Real.le_norm_self _).trans (((A t - A n) (x κ)).le_opNorm (x κ))
  have h2 := mul_le_mul_of_nonneg_right ((A t - A n).le_opNorm (x κ)) (norm_nonneg (x κ))
  have h3 := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖x κ‖)
  have h0 : (A t - A n) (x κ) (x κ) = A t (x κ) (x κ) - A n (x κ) (x κ) := by
    rw [sub_apply, sub_apply]
  rw [h0] at h1
  have hEκ := hE κ hκ
  have hLh : 0 ≤ L * ((b - a) / N) := mul_nonneg hL hh.le
  calc A t (x κ) (x κ) ≤ M + L * ((b - a) / N) * (M / α) := by
        nlinarith [norm_nonneg (x κ), mul_le_mul_of_nonneg_left (hxk κ hκ) hLh]
    _ = (1 + L * ((b - a) / N) / α) * M := by ring

/-- **The approximations for one partition.** For the partition of `[a, b]` into `N` cells of
length `h`, the interpolants `uh` (piecewise linear) and `ub` (piecewise constant) of the implicit
Euler scheme satisfy, with `M = exp (L (b - a) / α) (A a v₀ v₀ + ∫ ‖g‖²)`:
`uh` has weak derivative `D` with `∫ ‖ι D‖² ≤ M`; `A t (ub t) (ub t) ≤ M + L h M / α`;
`∫ ‖uh - ub‖² ≤ h M / α`; and `uh` is close to the weak solution `u`:
`α² ∫ ‖uh - u‖² ≤ 3 (‖ι‖² ∫ ‖G - g‖² + Λ² h M / α + (L h)² (b - a) M / α)` with
`Λ = ‖A a‖ + L (b - a)` and the cell averages `G` of `g`. -/
private theorem exists_rotheApprox (hab : a < b) {N : ℕ} (hN : 0 < N)
    (hsymm : ∀ t ∈ Icc a b, ∀ v w, A t v w = A t w v) (hα : 0 < α)
    (hA : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    {u : ℝ → V} {u' : ℝ → StrongDual ℝ V} {w : ℝ → H} {v₀ : V}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A t (u t) = ι.gelfandDual (g t))
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a = ι v₀) :
    ∃ uh ub D : ℝ → V,
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ uh D 1 ∧
      MemLp uh 2 (volume.restrict (Ioo a b)) ∧ MemLp ub 2 (volume.restrict (Ioo a b)) ∧
      MemLp D 2 (volume.restrict (Ioo a b)) ∧
      ∫ t in Ioo a b, ‖ι (D t)‖ ^ 2 ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) ∧
      (∀ t ∈ Ioo a b, A t (ub t) (ub t) ≤
        (1 + L * ((b - a) / N) / α) *
          (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2))) ∧
      ∫ t in Ioo a b, ‖uh t - ub t‖ ^ 2 ≤ (b - a) / N *
        (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) / α) ∧
      α ^ 2 * ∫ t in Ioo a b, ‖uh t - u t‖ ^ 2 ≤
        3 * ((‖ι‖ ^ 2 * ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / N) t - g t‖ ^ 2) +
          (‖A a‖ + L * (b - a)) ^ 2 * ((b - a) / N *
            (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) / α)) +
          (L * ((b - a) / N)) ^ 2 * ((b - a) *
            (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) / α))) := by
  set M := Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2)
  obtain ⟨x, hx0, hx, hE, hS⟩ := exists_rotheScheme_bound (ι := ι) hab hN hsymm hα hA hL hLip hg v₀
  obtain ⟨hxk, hdiff', hub⟩ := rotheScheme_integral_le (ι := ι) hab hN hα hA hE hS
  have : TopologicalSpace.PseudoMetrizableSpace (V →L[ℝ] StrongDual ℝ V) :=
    PseudoEMetricSpace.pseudoMetrizableSpace (α := V →L[ℝ] StrongDual ℝ V)
  have hcmp := integral_norm_sub_sq_le_of_approx (ι := ι) (A := A)
    (Ah := fun t ↦ A (a + cellIndex a ((b - a) / N) t * ((b - a) / N)))
    (Λ := ‖A a‖ + L * (b - a)) (ε₁ := L * ((b - a) / N)) hα hab.le
    (fun t ht ↦ hA t (Ioo_subset_Icc_self ht))
    (((continuousOn_of_norm_sub_le hLip).mono Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo)
    ((StronglyMeasurable.of_discrete (f := fun n : ℕ ↦ A (a + n * ((b - a) / N)))).comp_measurable
      (measurable_cellIndex _ _)).aestronglyMeasurable
    (fun t ht ↦ (norm_le_and_norm_sub_node_le hL hLip hN ht).1)
    (fun t ht ↦ (norm_le_and_norm_sub_node_le hL hLip hN ht).2)
    hg (memLp_comp_cellIndex hN (fun n ↦ cellAverage g a ((b - a) / N) (n - 1)) 2)
    h hu hu' heq hw hae h₀ (hasWeakLineDerivOn_rotheInterp hab hN) (memLp_rotheInterp hab hN)
    (memLp_rotheDeriv hN 2) (memLp_comp_cellIndex hN x 2) (continuousOn_rotheInterp hab hN)
    (by simp [rotheInterp, hx0]) (fun t ht ↦ rotheDeriv_add_eq hab hN hx ht)
  refine ⟨rotheInterp x a ((b - a) / N), fun t ↦ x (cellIndex a ((b - a) / N) t),
    rotheDeriv x a ((b - a) / N), hasWeakLineDerivOn_rotheInterp hab hN,
    memLp_rotheInterp hab hN, memLp_comp_cellIndex hN x 2, memLp_rotheDeriv hN 2, ?_, ?_, hdiff',
    hcmp.trans ?_⟩
  · rw [integral_norm_rotheDeriv_sq hab hN]
    exact le_trans (Finset.sum_le_sum fun k _ ↦ le_add_of_nonneg_right (by positivity)) hS
  · exact fun t ht ↦ apply_rotheScheme_le hab hN hL hLip hE hxk ht
  · exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hdiff' (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left hub (sq_nonneg _)))
      (by norm_num)

end Approx


/-! ### Time regularity for time-dependent coefficients -/

section Main

variable [CompleteSpace V] {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α L : ℝ}

omit [CompleteSpace V] in
/-- The interpolants of the schemes converge to the weak solution in `L²(a, b)`: given the bounds of
`exists_rotheApprox` for the partitions into `n + 1` cells, `∫ ‖uh n - u‖² → 0`. -/
private theorem tendsto_integral_norm_rotheApprox_sub [CompleteSpace H] {M : ℝ} (hab : a < b)
    (hα : 0 < α)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {u : ℝ → V} {uh : ℕ → ℝ → V}
    (hcmp : ∀ n : ℕ, α ^ 2 * ∫ t in Ioo a b, ‖uh n t - u t‖ ^ 2 ≤
      3 * ((‖ι‖ ^ 2 * ∫ t in Ioo a b, ‖stepAverage g a ((b - a) / (n + 1 : ℕ)) t - g t‖ ^ 2) +
        (‖A a‖ + L * (b - a)) ^ 2 * ((b - a) / (n + 1 : ℕ) * (M / α)) +
        (L * ((b - a) / (n + 1 : ℕ))) ^ 2 * ((b - a) * (M / α)))) :
    Tendsto (fun n ↦ ∫ t in Ioo a b, ‖uh n t - u t‖ ^ 2) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ ↦ (b - a) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
  have havg := (tendsto_integral_norm_stepAverage_sub_sq hab hg).comp (tendsto_add_atTop_nat 1)
  have hR := ((((havg.const_mul (‖ι‖ ^ 2)).add ((hmesh.mul_const (M / α)).const_mul
    ((‖A a‖ + L * (b - a)) ^ 2))).add (((hmesh.const_mul L).pow 2).mul_const
      ((b - a) * (M / α)))).const_mul 3).const_mul (α ^ 2)⁻¹
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hR
  refine squeeze_zero (fun n ↦ setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity)
    (fun n ↦ ?_) hR
  rw [le_inv_mul_iff₀ (by positivity)]
  exact hcmp n

omit [CompleteSpace V] in
/-- **The energy bound in the limit.** If `ub n → u` in `L²(a, b; V)` and
`A t (ub n t) (ub n t) ≤ c n` on `(a, b)` with `c n → M`, then `A t (u t) (u t) ≤ M` almost
everywhere on `(a, b)`. -/
private theorem ae_apply_le_of_tendsto {M : ℝ} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 M))
    {u : ℝ → V} {ub : ℕ → ℝ → V} (hub : ∀ n, MemLp (ub n) 2 (volume.restrict (Ioo a b)))
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hubu : Tendsto (fun n ↦ ∫ t in Ioo a b, ‖ub n t - u t‖ ^ 2) atTop (𝓝 0))
    (hE : ∀ n, ∀ t ∈ Ioo a b, A t (ub n t) (ub n t) ≤ c n) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), A t (u t) (u t) ≤ M := by
  obtain ⟨ns, hns, hlim⟩ := exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq hub hu hubu
  filter_upwards [hlim, ae_restrict_mem measurableSet_Ioo] with t ht ht'
  exact le_of_tendsto_of_tendsto' (((A t).continuous₂.tendsto (u t, u t)).comp (ht.prodMk_nhds ht))
    (hc.comp hns.tendsto_atTop) fun k ↦ hE (ns k) t ht'

omit [CompleteSpace V] in
/-- **The time derivative in the limit.** If `uh n → u` in `L²(a, b; V)` and the weak derivatives
`D n` of `uh n` satisfy `∫ ‖ι (D n)‖² ≤ M`, then `ι ∘ u` has a weak derivative `d ∈ L²(a, b; H)`
with `‖d‖ ≤ √M`: a subsequence of the `ι ∘ D n` converges weakly in `L²(a, b; H)`. -/
private theorem exists_hasWeakLineDerivOn_of_bounded [CompleteSpace H] {M : ℝ} {u : ℝ → V}
    {uh D : ℕ → ℝ → V} (hD : ∀ n, HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (uh n) (D n) 1)
    (huh : ∀ n, MemLp (uh n) 2 (volume.restrict (Ioo a b)))
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hDm : ∀ n, MemLp (D n) 2 (volume.restrict (Ioo a b)))
    (hDbd : ∀ n, ∫ t in Ioo a b, ‖ι (D n t)‖ ^ 2 ≤ M)
    (huhu : Tendsto (fun n ↦ ∫ t in Ioo a b, ‖uh n t - u t‖ ^ 2) atTop (𝓝 0)) :
    ∃ d : Lp H 2 (volume.restrict (Ioo a b)),
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι (u t)) d 1 ∧
        ‖d‖ ≤ Real.sqrt M := by
  set μ := volume.restrict (Ioo a b)
  set Dl : ℕ → Lp H 2 μ := fun n ↦ (ι.comp_memLp' (hDm n)).toLp (fun t ↦ ι (D n t))
  have hDl (n : ℕ) : ‖Dl n‖ ≤ Real.sqrt M := by
    rw [← Real.sqrt_sq (norm_nonneg _), MemLp.norm_toLp_sq]
    exact Real.sqrt_le_sqrt (hDbd n)
  have hbdd : Bornology.IsBounded (range Dl) :=
    isBounded_iff_forall_norm_le.2 ⟨Real.sqrt M, by rintro _ ⟨n, rfl⟩; exact hDl n⟩
  obtain ⟨dl, φs, hφs, hweak⟩ := tendsto_subseq_toWeakSpace_of_isBounded
    (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ)) hbdd
  have hinner (Ψ : Lp H 2 μ) : Tendsto (fun k ↦ ⟪Dl (φs k), Ψ⟫_ℝ) atTop (𝓝 ⟪dl, Ψ⟫_ℝ) := by
    have hc : Continuous fun v : WeakSpace ℝ (Lp H 2 μ) ↦
        innerSL ℝ Ψ ((toWeakSpace ℝ _).symm v) :=
      WeakBilin.eval_continuous (topDualPairing ℝ _).flip (innerSL ℝ Ψ)
    simpa [Function.comp_def, real_inner_comm] using (hc.tendsto _).comp hweak
  have hconv : Tendsto (fun k ↦ ∫ t in Ioo a b, ‖ι (uh (φs k) t) - ι (u t)‖ ^ 2) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun n ↦ setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity)
      (fun k ↦ integral_norm_sq_le_sq_mul_of_norm_le
        ((ι.comp_memLp' (huh _)).sub (ι.comp_memLp' hu)) ((huh _).sub hu)
        (Eventually.of_forall fun t ↦ by rw [← map_sub]; exact ι.le_opNorm _)) ?_
    simpa using (huhu.comp hφs.tendsto_atTop).const_mul (‖ι‖ ^ 2)
  refine ⟨dl, hasWeakLineDerivOn_of_tendsto_inner_toLp (F := fun k t ↦ ι (uh (φs k) t))
    (G := fun k t ↦ ι (D (φs k) t)) (fun k ↦ (hD (φs k)).clm_comp ι)
    (fun k ↦ ι.comp_memLp' (huh _)) (ι.comp_memLp' hu) (fun k ↦ ι.comp_memLp' (hDm _))
    hconv hinner, ?_⟩
  -- Weak lower semicontinuity of the norm.
  have h3 := le_of_tendsto' (hinner dl) fun k ↦ (real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hDl (φs k)) (norm_nonneg dl))
  rw [real_inner_self_eq_norm_sq] at h3
  nlinarith [norm_nonneg dl, Real.sqrt_nonneg M]

/-- **Time regularity of weak solutions with time-dependent coefficients.** Let `V ↪ H ↪ V*` be
given by `ι : V →L[ℝ] H`, and let `A(t) : V →L[ℝ] V*`, `t ∈ [a, b]`, be symmetric and coercive,
`α ‖v‖² ≤ A(t) v v`, and Lipschitz in time, `‖A(t) - A(s)‖ ≤ L |t - s|`. If `u` is a weak solution
of `u' + A(t) u = ι* g` with `g ∈ L²(a, b; H)` and initial value `ι v₀`, `v₀ ∈ V`, then

* `ι ∘ u` has a weak time derivative `d ∈ L²(a, b; H)`, with `u' = ι* d`, and
  `∫ₐᵇ ‖d‖² ≤ exp (L (b - a) / α) (A(a) v₀ v₀ + ∫ₐᵇ ‖g‖²)`;
* `u` is essentially bounded in `V`:
  `A(t) u(t) u(t) ≤ exp (L (b - a) / α) (A(a) v₀ v₀ + ∫ₐᵇ ‖g‖²)` for almost every `t`.

For a parabolic equation `∂ₜu - ∂ᵢ(aⁱʲ(t, x) ∂ⱼu) = f` whose coefficients have a bounded time
derivative this says `∂ₜu ∈ L²(0, T; L²(Ω))` and `u ∈ L^∞(0, T; H¹₀(Ω))` when
`f ∈ L²(0, T; L²(Ω))` and `u(0) ∈ H¹₀(Ω)` (Evans, §7.1.3, Theorem 5, for time-dependent
coefficients). For `L = 0` the bound is that of the time-independent theorem
`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm`. -/
theorem HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_lipschitz
    [CompleteSpace H] (hab : a ≤ b) (hsymm : ∀ t ∈ Icc a b, ∀ v w, A t v w = A t w v) (hα : 0 < α)
    (hA : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {v₀ : V} {u : ℝ → V}
    {u' : ℝ → StrongDual ℝ V} {w : ℝ → H}
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A t (u t) = ι.gelfandDual (g t))
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    (h₀ : w a = ι v₀) :
    ∃ d : ℝ → H, MemLp d 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι (u t)) d 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), u' t = ι.gelfandDual (d t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), A t (u t) (u t) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ s in Ioo a b, ‖g s‖ ^ 2)) ∧
      ∫ t in Ioo a b, ‖d t‖ ^ 2 ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) := by
  set M := Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2)
  have hA0 : 0 ≤ A a v₀ v₀ :=
    (by positivity : (0 : ℝ) ≤ α * ‖v₀‖ ^ 2).trans (hA a (left_mem_Icc.2 hab) v₀)
  have hM : 0 ≤ M := mul_nonneg (Real.exp_pos _).le
    (add_nonneg hA0 (setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity))
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨0, MemLp.zero, hasWeakLineDerivOn_iff_locally.2 fun x hx ↦ ?_, by simp, by simp,
      by simpa using hM⟩
    simp at hx
  set μ := volume.restrict (Ioo a b)
  -- The Lipschitz constant is nonnegative since `a < b`.
  have hL : 0 ≤ L := by
    have h₁ := (norm_nonneg (A b - A a)).trans
      (hLip a (left_mem_Icc.2 hab.le) b (right_mem_Icc.2 hab.le))
    rw [abs_of_pos (sub_pos.2 hab)] at h₁
    exact nonneg_of_mul_nonneg_left h₁ (sub_pos.2 hab)
  have happrox (n : ℕ) := exists_rotheApprox (ι := ι) hab (Nat.succ_pos n) hsymm hα hA hL hLip hg
    h hu hu' heq hw hae h₀
  choose uh ub D hD huh hub hDm hDbd hE hdiff hcmp using happrox
  have hmesh : Tendsto (fun n : ℕ ↦ (b - a) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)
  have huhu := tendsto_integral_norm_rotheApprox_sub hab hα hg hcmp
  -- The piecewise constant interpolants converge to `u` as well.
  have hubu : Tendsto (fun n ↦ ∫ t in Ioo a b, ‖ub n t - u t‖ ^ 2) atTop (𝓝 0) := by
    have hlim := ((hmesh.mul_const (M / α)).add huhu).const_mul 3
    simp only [zero_mul, zero_add, mul_zero] at hlim
    refine squeeze_zero (fun n ↦ setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity)
      (fun n ↦ ?_) hlim
    have h3 := integral_norm_sq_le_three_mul (μ := μ) (f := fun t ↦ ub n t - u t)
      ((hub n).sub (huh n)) ((huh n).sub hu) (MemLp.zero (ε := V))
      (Eventually.of_forall fun t ↦ by simp)
    simp only [Pi.zero_apply, Pi.sub_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, add_zero] at h3
    refine h3.trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (by norm_num))
    calc ∫ t in Ioo a b, ‖ub n t - uh n t‖ ^ 2 = ∫ t in Ioo a b, ‖uh n t - ub n t‖ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [norm_sub_rev])
      _ ≤ _ := hdiff n
  have hc : Tendsto (fun n : ℕ ↦ (1 + L * ((b - a) / ((n + 1 : ℕ) : ℝ)) / α) * M) atTop
      (𝓝 M) := by
    simpa using (((hmesh.const_mul L).div_const α).const_add 1).mul_const M
  obtain ⟨dl, hderiv, hdl⟩ := exists_hasWeakLineDerivOn_of_bounded hD huh hu hDm hDbd huhu
  refine ⟨dl, Lp.memLp dl, hderiv, h.ae_eq (hderiv.clm_comp ι.gelfandDual),
    ae_apply_le_of_tendsto hc hub hu hubu hE, ?_⟩
  rw [← MemLp.norm_toLp_sq (Lp.memLp dl), Lp.toLp_coeFn]
  calc ‖dl‖ ^ 2 ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdl 2
    _ = M := Real.sq_sqrt hM

end Main

end TauCeti
