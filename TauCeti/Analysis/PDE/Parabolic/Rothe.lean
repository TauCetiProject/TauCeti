/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.MeasureTheory.Function.CurveAction.Basic
import TauCeti.MeasureTheory.Function.IntervalStep.CellAverage
import TauCeti.MeasureTheory.Function.Lp.Norm
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
`∂ₜu - ∂ᵢ(aⁱʲ(t, x) ∂ⱼu) = f` with symmetric, uniformly elliptic coefficients `aⁱʲ` and `∂ₜa`
bounded, applied to `A(t)` the energy form of `a(t, ·)` on `H¹₀(Ω)`, this is
`∂ₜu ∈ L²(0, T; L²(Ω))` and `u ∈ L^∞(0, T; H¹₀(Ω))`; that instantiation is not formalized here.
When `A` does not depend on time,
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
average `G` of `g`, and `∫ ‖uh - ub‖² ≤ h M / α`. The energy estimate for `uh - u`
(`TauCeti.HasWeakLineDerivOn.sq_mul_integral_norm_sub_sq_le_of_gelfandDual`), whose forcing
`ι* (G - g) + A(t) (uh - ub) + (A(t) - A(t_{k+1})) ub` tends to zero since cell averages converge in
`L²` (`MeasureTheory.tendsto_integral_norm_intervalStepAverage_sub_sq`), gives `uh → u` and
`ub → u` in `L²(a, b; V)`. An almost everywhere convergent subsequence of `ub` passes the energy
bound to `u` (`MeasureTheory.ae_le_of_tendsto_integral_norm_sub_sq`), and a weakly convergent
subsequence of `ι D` in `L²(a, b; H)` gives `d`
(`TauCeti.exists_hasWeakLineDerivOn_and_norm_le_of_tendsto`).

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
      (le_abs_self _).trans ((B' - B).le_opNorm₂ x x)
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
  have hx : 0 ≤ L * (b - a) / α := div_nonneg (mul_nonneg hL (sub_nonneg.2 hab)) hα.le
  rw [show 1 + L * ((b - a) / N) / α = 1 + L * (b - a) / α / N by ring]
  exact (pow_le_pow_right₀ (le_add_of_nonneg_right (div_nonneg hx N.cast_nonneg)) hk).trans
    (Real.one_add_div_pow_le_exp ((neg_nonpos.2 N.cast_nonneg).trans hx))

/-! ### The interpolants of the scheme -/

section Interpolant

variable (x : ℕ → V) (a h : ℝ)

/-- The difference quotients of the scheme, constant on each cell: `(x k - x (k - 1)) / h` on the
`k`-th cell. -/
private def rotheDeriv (t : ℝ) : V :=
  h⁻¹ • (x (intervalCellIndex a h t) - x (intervalCellIndex a h t - 1))

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
    rw [rotheDeriv, intervalCellIndex_eq hh ⟨hr.1, hr.2.trans hs.2⟩, Nat.add_sub_cancel]
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
    ‖rotheInterp x a h t - x (intervalCellIndex a h t)‖ ≤
      ‖x (intervalCellIndex a h t) - x (intervalCellIndex a h t - 1)‖ := by
  subst hh
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 (ht.1.trans ht.2)) (Nat.cast_pos.2 hN)
  obtain ⟨k, -, hk, hmem⟩ := exists_intervalCellIndex_eq ht hN
  rw [hk, Nat.add_sub_cancel, rotheInterp_eq hh (Ioc_subset_Icc_self hmem)]
  set c := (t - (a + k * ((b - a) / N))) / ((b - a) / N)
  have hc0 : 0 ≤ c := div_nonneg (by linarith [hmem.1]) hh.le
  have hc1 : c ≤ 1 := by rw [div_le_one hh]; linarith [hmem.2]
  rw [show x k + c • (x (k + 1) - x k) - x (k + 1) = (1 - c) • -(x (k + 1) - x k) by
    rw [smul_neg, sub_smul, one_smul]; abel, norm_smul, norm_neg, Real.norm_of_nonneg (by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- The difference quotient of the scheme is in `L²(a, b)`. -/
private theorem memLp_rotheDeriv {b : ℝ} {N : ℕ} (hN : 0 < N) (p : ENNReal) :
    MemLp (rotheDeriv x a ((b - a) / N)) p (volume.restrict (Ioo a b)) :=
  memLp_comp_intervalCellIndex hN (fun n ↦ ((b - a) / N)⁻¹ • (x n - x (n - 1))) p

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
  have := integral_Ioo_comp_intervalCellIndex hab hN
    (fun n ↦ ‖ι (((b - a) / N)⁻¹ • (x n - x (n - 1)))‖ ^ 2)
  simp only [rotheDeriv]
  rw [this]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Nat.add_sub_cancel, map_smul, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, smul_eq_mul]
  field_simp

/-- `∫_{(a, b)} ‖rotheInterp t - x (intervalCellIndex t)‖² ≤ ∑_{k < N} h ‖x (k + 1) - x k‖²`. -/
private theorem integral_norm_rotheInterp_sub_sq_le [CompleteSpace V] {b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N) :
    ∫ t in Ioo a b,
        ‖rotheInterp x a ((b - a) / N) t - x (intervalCellIndex a ((b - a) / N) t)‖ ^ 2 ≤
      ∑ k ∈ Finset.range N, (b - a) / N * ‖x (k + 1) - x k‖ ^ 2 := by
  have hcell := integral_Ioo_comp_intervalCellIndex hab hN (fun n ↦ ‖x n - x (n - 1)‖ ^ 2)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hcell
  rw [← hcell]
  have hmem : MemLp
      (fun t ↦ rotheInterp x a ((b - a) / N) t - x (intervalCellIndex a ((b - a) / N) t)) 2
      (volume.restrict (Ioo a b)) :=
    (memLp_rotheInterp hab hN).sub (memLp_comp_intervalCellIndex hN x 2)
  refine setIntegral_mono_on ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem)
    ((memLp_comp_intervalCellIndex hN (fun n ↦ ‖x n - x (n - 1)‖ ^ 2) 1).integrable le_rfl)
    measurableSet_Ioo fun t ht ↦ ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_rotheInterp_sub_le ht hN rfl) 2

end Interpolant

/-! ### The scheme for a time-dependent operator -/

section Scheme

variable [CompleteSpace V] {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α L : ℝ}

/-- **The scheme with its uniform energy bound.** For the partition of `[a, b]` into `N` cells of
length `h`, the implicit Euler scheme for `u' + A(t) u = ι* g`, `u(a) = v₀`, with the operators
frozen at the right end of each step and `g` averaged over each step, has a solution with
`A(a + k h) (x k) (x k) ≤ M` for `k ≤ N` and
`∑_{j < N} (‖ι (x (j + 1) - x j)‖² / h + α ‖x (j + 1) - x j‖²) ≤ M`, where
`M = exp (L (b - a) / α) (A a v₀ v₀ + ∫ ‖g‖²)` does not depend on `N`. -/
private theorem exists_rotheScheme_bound [CompleteSpace H] (hab : a < b) {N : ℕ} (hN : 0 < N)
    (hsymm : ∀ t ∈ Icc a b, ∀ v w, A t v w = A t w v) (hα : 0 < α)
    (hA : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) (v₀ : V) :
    ∃ x : ℕ → V, x 0 = v₀ ∧
      (∀ k < N, ∀ v, ⟪ι (x (k + 1) - x k), ι v⟫_ℝ +
          (b - a) / N * A (a + (k + 1 : ℕ) * ((b - a) / N)) (x (k + 1)) v =
        (b - a) / N * ⟪intervalCellAverage g a ((b - a) / N) k, ι v⟫_ℝ) ∧
      (∀ k ≤ N, A (a + k * ((b - a) / N)) (x k) (x k) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2)) ∧
      ∑ j ∈ Finset.range N, (‖ι (x (j + 1) - x j)‖ ^ 2 / ((b - a) / N) +
          α * ‖x (j + 1) - x j‖ ^ 2) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) := by
  set h := (b - a) / N
  have hh : 0 < h := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  set B : ℕ → V →L[ℝ] StrongDual ℝ V := fun k ↦ A (a + (min k N : ℕ) * h)
  have hnode' (k : ℕ) (hk : k ≤ N) : a + k * h ∈ Icc a b :=
    Icc_subset_Icc_right (add_natCast_mul_sub_div_natCast_self a b hN).le
      (add_natCast_mul_mem_Icc a hh.le hk)
  have hnode (k : ℕ) : a + (min k N : ℕ) * h ∈ Icc a b := hnode' _ (min_le_right _ _)
  have hBk (k : ℕ) (hk : k ≤ N) : B k = A (a + k * h) := by simp only [B, min_eq_left hk]
  obtain ⟨x, hx0, hx⟩ := exists_rotheScheme (ι := ι) (B := B) hα hh
    (fun k v ↦ hA _ (hnode _) v) (intervalCellAverage g a h) v₀
  have hstep (k : ℕ) (hk : k < N) (v : V) := by
    have := hx k v
    rwa [hBk (k + 1) hk] at this
  have hE (k : ℕ) (hk : k ≤ N) := rotheScheme_energy (ι := ι) (B := B) hα hL hh
    (fun k _ ↦ hsymm _ (hnode k)) (fun k _ ↦ hA _ (hnode k))
    (fun k hk ↦ by
      rw [hBk (k + 1) hk, hBk k hk.le]
      refine (hLip _ (hnode' k hk.le) _ (hnode' (k + 1) hk)).trans_eq ?_
      push_cast
      rw [show a + (k + 1) * h - (a + k * h) = h by ring, abs_of_pos hh])
    (fun k _ v ↦ hx k v) hk
  have hB0 : B 0 = A a := by simp [B]
  have hG (k : ℕ) (hk : k ≤ N) := sum_mul_norm_intervalCellAverage_sq_le hab hN hg hk
  have hA0 : 0 ≤ A a v₀ v₀ := (by positivity : (0 : ℝ) ≤ α * ‖v₀‖ ^ 2).trans
    (hA a (left_mem_Icc.2 hab.le) v₀)
  have hexp (k : ℕ) (hk : k ≤ N) := one_add_pow_le_exp hα hL hab.le (a := a) (b := b) hk
  have hbound (k : ℕ) (hk : k ≤ N) :
      (1 + L * h / α) ^ k *
          (B 0 (x 0) (x 0) + ∑ j ∈ Finset.range k, h * ‖intervalCellAverage g a h j‖ ^ 2) ≤
        Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) := by
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
    have hEN : 0 ≤ A (a + N * h) (x N) (x N) := (by positivity : (0 : ℝ) ≤ α * ‖x N‖ ^ 2).trans
      (hA _ (hnode' N le_rfl) _)
    linarith [hbound N le_rfl]

omit [CompleteSpace V] in
/-- **The scheme as an equation on `(a, b)`.** On each cell the difference quotient and the
piecewise constant interpolant satisfy `ι* ι D + A(node) ū = ι* G`, with the operator frozen at the
right node of the cell and the cell average `G` of `g`. -/
private theorem rotheDeriv_add_eq {g : ℝ → H} {x : ℕ → V} (hab : a < b) {N : ℕ} (hN : 0 < N)
    (hx : ∀ k < N, ∀ v, ⟪ι (x (k + 1) - x k), ι v⟫_ℝ +
          (b - a) / N * A (a + (k + 1 : ℕ) * ((b - a) / N)) (x (k + 1)) v =
        (b - a) / N * ⟪intervalCellAverage g a ((b - a) / N) k, ι v⟫_ℝ) {t : ℝ} (ht : t ∈ Ioo a b) :
    ι.gelfandDual (ι (rotheDeriv x a ((b - a) / N) t)) +
        A (a + intervalCellIndex a ((b - a) / N) t * ((b - a) / N))
          (x (intervalCellIndex a ((b - a) / N) t)) =
      ι.gelfandDual (intervalStepAverage g a ((b - a) / N) t) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  obtain ⟨k, hlt, hk, hmem⟩ := exists_intervalCellIndex_eq ht hN
  have hD : rotheDeriv x a ((b - a) / N) t = ((b - a) / N)⁻¹ • (x (k + 1) - x k) := by
    rw [rotheDeriv, hk, Nat.add_sub_cancel]
  rw [hD, intervalStepAverage_eq g hh hmem, hk]
  ext v
  have := hx k hlt v
  simp only [add_apply, smul_apply, ContinuousLinearMap.gelfandDual_apply, map_smul, smul_eq_mul]
  rw [← mul_right_inj' hh.ne', mul_add, mul_inv_cancel_left₀ hh.ne']
  linarith

end Scheme

/-! ### The approximations for one partition -/

section Approx

variable [CompleteSpace V] {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α L : ℝ}

omit [CompleteSpace V] in
/-- On `(a, b)`, operators that are `L`-Lipschitz on `[a, b]` are bounded by `‖A a‖ + L (b - a)`,
and differ by at most `L h` from their value at the right node of the cell. -/
private theorem norm_le_and_norm_sub_node_le (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖A t - A s‖ ≤ L * |t - s|) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖A t‖ ≤ ‖A a‖ + L * (b - a) ∧
      ‖A t - A (a + intervalCellIndex a ((b - a) / N) t * ((b - a) / N))‖ ≤ L * ((b - a) / N) := by
  have hab : a ≤ b := (ht.1.trans ht.2).le
  have hn := add_intervalCellIndex_mul_mem_Icc ht hN
  have hd := abs_sub_add_intervalCellIndex_mul_le ht hN
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
      ∫ t in Ioo a b,
          ‖rotheInterp x a ((b - a) / N) t - x (intervalCellIndex a ((b - a) / N) t)‖ ^ 2 ≤
        (b - a) / N * (M / α) ∧
      ∫ t in Ioo a b, ‖x (intervalCellIndex a ((b - a) / N) t)‖ ^ 2 ≤ (b - a) * (M / α) := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hxk (k : ℕ) (hk : k ≤ N) : ‖x k‖ ^ 2 ≤ M / α := by
    rw [le_div_iff₀ hα, mul_comm]
    exact (hA _ (Icc_subset_Icc_right (add_natCast_mul_sub_div_natCast_self a b hN).le
      (add_natCast_mul_mem_Icc a hh.le hk)) _).trans (hE k hk)
  have hδ : ∑ k ∈ Finset.range N, ‖x (k + 1) - x k‖ ^ 2 ≤ M / α := by
    rw [le_div_iff₀ hα, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) hS
    rw [mul_comm]
    exact le_add_of_nonneg_left (by positivity)
  have hdiff := integral_norm_rotheInterp_sub_sq_le (x := x) hab hN
  rw [← Finset.mul_sum] at hdiff
  refine ⟨hxk, hdiff.trans (mul_le_mul_of_nonneg_left hδ hh.le), ?_⟩
  rw [integral_Ioo_comp_intervalCellIndex hab hN (fun n ↦ ‖x n‖ ^ 2)]
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
    A t (x (intervalCellIndex a ((b - a) / N) t)) (x (intervalCellIndex a ((b - a) / N) t)) ≤
      (1 + L * ((b - a) / N) / α) * M := by
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)
  have hd := (norm_le_and_norm_sub_node_le hL hLip hN ht).2
  set κ := intervalCellIndex a ((b - a) / N) t
  have hκ : κ ≤ N := (intervalCellIndex_mem_Icc ht hN).2
  set n := a + κ * ((b - a) / N)
  have h1 : (A t - A n) (x κ) (x κ) ≤ ‖A t - A n‖ * ‖x κ‖ * ‖x κ‖ :=
    (Real.le_norm_self _).trans ((A t - A n).le_opNorm₂ (x κ) (x κ))
  have h3 := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖x κ‖)
  simp only [sub_apply] at h1
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
private theorem exists_rotheApprox [CompleteSpace H] (hab : a < b) {N : ℕ} (hN : 0 < N)
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
        3 * ((‖ι‖ ^ 2 * ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / N) t - g t‖ ^ 2) +
          (‖A a‖ + L * (b - a)) ^ 2 * ((b - a) / N *
            (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) / α)) +
          (L * ((b - a) / N)) ^ 2 * ((b - a) *
            (Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2) / α))) := by
  set M := Real.exp (L * (b - a) / α) * (A a v₀ v₀ + ∫ t in Ioo a b, ‖g t‖ ^ 2)
  obtain ⟨x, hx0, hx, hE, hS⟩ := exists_rotheScheme_bound (ι := ι) hab hN hsymm hα hA hL hLip hg v₀
  obtain ⟨hxk, hdiff', hub⟩ := rotheScheme_integral_le (ι := ι) hab hN hα hA hE hS
  -- Instance synthesis does not find the pseudo-metrizable structure of `V →L[ℝ] V*`, needed for
  -- the strong measurability of `A` below, although its topology is the one of its norm.
  have : TopologicalSpace.PseudoMetrizableSpace (V →L[ℝ] StrongDual ℝ V) :=
    PseudoEMetricSpace.pseudoMetrizableSpace (α := V →L[ℝ] StrongDual ℝ V)
  have hAc : ContinuousOn A (Icc a b) :=
    (LipschitzOnWith.of_dist_le' (f := A) (K := L) fun t ht s hs ↦ by
      rw [Real.dist_eq]
      exact (dist_eq_norm (A t) (A s)).trans_le (hLip s hs t ht)).continuousOn
  have hcmp := HasWeakLineDerivOn.sq_mul_integral_norm_sub_sq_le_of_gelfandDual (ι := ι)
    (A := A) (Ah := fun t ↦ A (a + intervalCellIndex a ((b - a) / N) t * ((b - a) / N)))
    (Λ := ‖A a‖ + L * (b - a)) (ε₁ := L * ((b - a) / N)) hα hab.le
    (fun t ht ↦ hA t (Ioo_subset_Icc_self ht))
    ((hAc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    ((StronglyMeasurable.of_discrete (f := fun n : ℕ ↦ A (a + n * ((b - a) / N)))).comp_measurable
      (measurable_intervalCellIndex _ _)).aestronglyMeasurable
    (fun t ht ↦ (norm_le_and_norm_sub_node_le hL hLip hN ht).1)
    (fun t ht ↦ (norm_le_and_norm_sub_node_le hL hLip hN ht).2)
    hg (memLp_intervalStepAverage hN g 2)
    h hu hu' heq hw hae h₀ (hasWeakLineDerivOn_rotheInterp hab hN) (memLp_rotheInterp hab hN)
    (memLp_rotheDeriv hN 2) (memLp_comp_intervalCellIndex hN x 2) (continuousOn_rotheInterp hab hN)
    (by simp [rotheInterp, hx0]) (fun t ht ↦ rotheDeriv_add_eq hab hN hx ht)
  refine ⟨rotheInterp x a ((b - a) / N), fun t ↦ x (intervalCellIndex a ((b - a) / N) t),
    rotheDeriv x a ((b - a) / N), hasWeakLineDerivOn_rotheInterp hab hN,
    memLp_rotheInterp hab hN, memLp_comp_intervalCellIndex hN x 2, memLp_rotheDeriv hN 2, ?_, ?_,
    hdiff', hcmp.trans ?_⟩
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

/-- The cell length `(b - a) / (n + 1)` of the partitions into `n + 1` cells tends to `0`. -/
private theorem tendsto_sub_div_natCast_succ :
    Tendsto (fun n : ℕ ↦ (b - a) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 1)

omit [CompleteSpace V] in
/-- The interpolants of the schemes converge to the weak solution in `L²(a, b)`: given the bounds of
`exists_rotheApprox` for the partitions into `n + 1` cells, `∫ ‖uh n - u‖² → 0`. -/
private theorem tendsto_integral_norm_rotheApprox_sub [CompleteSpace H] {M : ℝ} (hab : a < b)
    (hα : 0 < α)
    {g : ℝ → H} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {u : ℝ → V} {uh : ℕ → ℝ → V}
    (hcmp : ∀ n : ℕ, α ^ 2 * ∫ t in Ioo a b, ‖uh n t - u t‖ ^ 2 ≤
      3 * ((‖ι‖ ^ 2 *
          ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / (n + 1 : ℕ)) t - g t‖ ^ 2) +
        (‖A a‖ + L * (b - a)) ^ 2 * ((b - a) / (n + 1 : ℕ) * (M / α)) +
        (L * ((b - a) / (n + 1 : ℕ))) ^ 2 * ((b - a) * (M / α)))) :
    Tendsto (fun n ↦ ∫ t in Ioo a b, ‖uh n t - u t‖ ^ 2) atTop (𝓝 0) := by
  have hmesh := tendsto_sub_div_natCast_succ (a := a) (b := b)
  have havg :=
    (tendsto_integral_norm_intervalStepAverage_sub_sq hab hg).comp (tendsto_add_atTop_nat 1)
  have hR := ((((havg.const_mul (‖ι‖ ^ 2)).add ((hmesh.mul_const (M / α)).const_mul
    ((‖A a‖ + L * (b - a)) ^ 2))).add (((hmesh.const_mul L).pow 2).mul_const
      ((b - a) * (M / α)))).const_mul 3).const_mul (α ^ 2)⁻¹
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hR
  refine squeeze_zero (fun n ↦ setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity)
    (fun n ↦ ?_) hR
  rw [le_inv_mul_iff₀ (by positivity)]
  exact hcmp n

/-- **Time regularity of weak solutions with time-dependent coefficients.** Let `V ↪ H ↪ V*` be
given by `ι : V →L[ℝ] H`, and let `A(t) : V →L[ℝ] V*`, `t ∈ [a, b]`, be symmetric and coercive,
`α ‖v‖² ≤ A(t) v v`, and Lipschitz in time, `‖A(t) - A(s)‖ ≤ L |t - s|`. If `u` is a weak solution
of `u' + A(t) u = ι* g` with `g ∈ L²(a, b; H)` and initial value `ι v₀`, `v₀ ∈ V`, then

* `ι ∘ u` has a weak time derivative `d ∈ L²(a, b; H)`, with `u' = ι* d`, and
  `∫ₐᵇ ‖d‖² ≤ exp (L (b - a) / α) (A(a) v₀ v₀ + ∫ₐᵇ ‖g‖²)`;
* `u` is essentially bounded in `V`:
  `A(t) u(t) u(t) ≤ exp (L (b - a) / α) (A(a) v₀ v₀ + ∫ₐᵇ ‖g‖²)` for almost every `t`.

For a parabolic equation `∂ₜu - ∂ᵢ(aⁱʲ(t, x) ∂ⱼu) = f` whose coefficients `aⁱʲ` are symmetric and
uniformly elliptic with a bounded time derivative, applied to `A(t)` the energy form of `a(t, ·)`
on `H¹₀(Ω)`, this says `∂ₜu ∈ L²(0, T; L²(Ω))` and `u ∈ L^∞(0, T; H¹₀(Ω))` when
`f ∈ L²(0, T; L²(Ω))` and `u(0) ∈ H¹₀(Ω)`; that instantiation is not formalized here. This is
the time-dependent counterpart of Evans, §7.1.3, Theorem 5, which treats time-independent
coefficients. For `L = 0` it recovers the bound
`A u u ≤ A v₀ v₀ + ∫ₐᵇ ‖g‖²` of the time-independent theorem
`TauCeti.HasWeakLineDerivOn.exists_memLp_hasWeakLineDerivOn_of_gelfandDual_of_symm` and sharpens
its derivative bound `∫ₐᵇ ‖d‖² ≤ 2 A v₀ v₀ + 4 ∫ₐᵇ ‖g‖²` to `∫ₐᵇ ‖d‖² ≤ A v₀ v₀ + ∫ₐᵇ ‖g‖²`,
without its assumptions that `ι` is injective and `H` separable. -/
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
  have hmesh := tendsto_sub_div_natCast_succ (a := a) (b := b)
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
  obtain ⟨dl, hderiv, hdl⟩ := exists_hasWeakLineDerivOn_and_norm_le_of_tendsto
    (F := fun n t ↦ ι (uh n t)) (G := fun n t ↦ ι (D n t)) (f := fun t ↦ ι (u t))
    (fun n ↦ (hD n).clm_comp ι) (fun n ↦ ι.comp_memLp' (huh n)) (ι.comp_memLp' hu)
    (fun n ↦ ι.comp_memLp' (hDm n)) hDbd (tendsto_integral_norm_clm_apply_sub_sq ι huh hu huhu)
  refine ⟨dl, Lp.memLp dl, hderiv, h.ae_eq (hderiv.clm_comp ι.gelfandDual),
    ae_le_of_tendsto_integral_norm_sub_sq (φ := fun t v ↦ A t v v) hub hu hubu
      (fun t ↦ by fun_prop) hc fun n ↦ (ae_restrict_mem measurableSet_Ioo).mono (hE n), ?_⟩
  calc ∫ t in Ioo a b, ‖dl t‖ ^ 2 = ‖dl‖ ^ 2 :=
        (Lp.toLp_coeFn dl (Lp.memLp dl) ▸ MemLp.norm_toLp_sq (Lp.memLp dl)).symm
    _ ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdl 2
    _ = M := Real.sq_sqrt hM

end Main

end TauCeti
