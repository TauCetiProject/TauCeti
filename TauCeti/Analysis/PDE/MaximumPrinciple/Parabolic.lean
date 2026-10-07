/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# The weak maximum principle for the heat equation

Let `K` be a compact subset of a finite-dimensional real inner product space `E` and `T` a time.
On the space-time cylinder `[0, T] × K` consider the parabolic operator

`∂ₜu - Δu - b·∇u`,

with a time-dependent drift field `b : ℝ → E → E`; for `b = 0` this is the heat operator. A
function `u : ℝ → E → ℝ` (time first, so `u t` is the spatial slice at time `t`) is a
*subsolution* when `∂ₜu ≤ Δu + b·∇u` at every point of the open cylinder `(0, T) × interior K`.
In Lean the drift term `⟪b, ∇u⟫` is spelled `fderiv ℝ (u t) x (b t x)`, as in
`TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple`.

The **parabolic boundary** of the cylinder is its bottom `{0} × K` together with its lateral
side `[0, T] × frontier K`; the top `{T} × interior K` is *not* part of it. The weak maximum
principle says that a subsolution which is continuous on the closed cylinder is bounded on the
whole cylinder by any bound it satisfies on the parabolic boundary.

The proof is the classical one. For `ε > 0` the function `u - εt` is a strict subsolution, so it
cannot attain its maximum over `[0, τ] × K` (for `τ < T`) at a point `(t₀, x₀)` with `t₀ > 0` and
`x₀ ∈ interior K`: there `Δ(u t₀) x₀ ≤ 0` and `∇(u t₀) x₀ = 0` because `x₀` is a spatial local
maximum, while `∂ₜu(t₀, x₀) ≥ ε` because `t₀` is a maximum from the left. Letting `ε → 0` gives
the bound for `t < T`, and continuity carries it to the top `t = T`. Unlike the elliptic
principle for `Δ + b·∇`, no bound on the drift is needed, because the perturbation `εt` does not
depend on the space variable.

Regularity is only required on the open cylinder `(0, T) × interior K` (`C²` in space,
differentiable in time), together with continuity on the closed cylinder `[0, T] × K`.

## Main declarations

* `TauCeti.le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary`: the **weak maximum
  principle** for `∂ₜ - Δ - b·∇`, in bound form.
* `TauCeti.le_of_deriv_le_laplacian_le_parabolicBoundary`: its case `b = 0`, the weak maximum
  principle for subsolutions of the heat equation `∂ₜu ≤ Δu`.
* `TauCeti.ge_of_laplacian_add_fderiv_le_deriv_ge_parabolicBoundary`: the weak minimum
  principle for supersolutions.
* `TauCeti.le_of_deriv_sub_laplacian_sub_fderiv_le_of_le_parabolicBoundary`: the comparison
  principle.
* `TauCeti.eqOn_of_deriv_sub_laplacian_sub_fderiv_eq_of_eqOn_parabolicBoundary`: uniqueness for
  the initial-boundary value problem `∂ₜu - Δu - b·∇u = f`, `u = g` on the parabolic boundary.
* `TauCeti.ge_of_laplacian_le_deriv_ge_parabolicBoundary`,
  `TauCeti.le_of_deriv_sub_laplacian_le_of_le_parabolicBoundary`,
  `TauCeti.eqOn_of_deriv_sub_laplacian_eq_of_eqOn_parabolicBoundary`: the minimum principle,
  comparison principle and uniqueness for the heat equation (`b = 0`).

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.3, Theorems 4 (i) and 5, and
  Section 7.1.4, Theorem 8.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Set E} {T : ℝ} {u : ℝ → E → ℝ} {b : ℝ → E → E}

/-- The perturbed bound behind the weak parabolic maximum principle: for a subsolution of
`∂ₜ - Δ - b·∇` bounded by `m` on the parabolic boundary, every `ε > 0` and every `τ < T`, the
strict subsolution `u - εt` is bounded by `m` on `[0, τ] × K`. -/
private theorem sub_mul_le_of_deriv_le_laplacian_add_fderiv (hK : IsCompact K) {m ε τ : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t ≤ Δ (u t) x + fderiv ℝ (u t) x (b t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m)
    (hε : 0 < ε) (hτ : τ < T) :
    ∀ ⦃t⦄, t ∈ Icc 0 τ → ∀ ⦃x⦄, x ∈ K → u t x - ε * t ≤ m := by
  intro t ht x hx
  set w : ℝ × E → ℝ := fun p ↦ Function.uncurry u p - ε * p.1 with hw
  have hsub' : Icc 0 τ ×ˢ K ⊆ Icc 0 T ×ˢ K := prod_mono (Icc_subset_Icc_right hτ.le) le_rfl
  have hwcont : ContinuousOn w (Icc 0 τ ×ˢ K) :=
    (hcont.mono hsub').sub (continuousOn_const.mul continuousOn_fst)
  obtain ⟨⟨t₀, x₀⟩, hmem, hmax⟩ :=
    (isCompact_Icc.prod hK).exists_isMaxOn ⟨(t, x), ht, hx⟩ hwcont
  have ht₀ : t₀ ∈ Icc 0 τ := hmem.1
  have hx₀ : x₀ ∈ K := hmem.2
  have hmax' : ∀ ⦃s⦄, s ∈ Icc 0 τ → ∀ ⦃y⦄, y ∈ K → u s y - ε * s ≤ u t₀ x₀ - ε * t₀ :=
    fun s hs y hy ↦ isMaxOn_iff.mp hmax (s, y) ⟨hs, hy⟩
  refine (hmax' ht hx).trans ?_
  -- The maximizer lies on the parabolic boundary, where `u ≤ m`.
  rcases ht₀.1.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, sub_zero]
    exact hinit hx₀
  by_cases hfr : x₀ ∈ frontier K
  · have := hlat ⟨ht₀.1, ht₀.2.trans hτ.le⟩ hfr
    nlinarith
  -- Otherwise `(t₀, x₀)` is an interior point of the open cylinder, which is impossible.
  exfalso
  have ht₀T : t₀ ∈ Ioo 0 T := ⟨hpos, ht₀.2.trans_lt hτ⟩
  have hint : x₀ ∈ interior K := by
    rw [← self_sdiff_frontier]
    exact ⟨hx₀, hfr⟩
  -- In space, `x₀` is a local maximum of `u t₀`.
  have hloc : IsLocalMax (u t₀) x₀ :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hint) fun y hy ↦ by
      linarith [hmax' ht₀ (interior_subset hy)]
  -- In time, `t₀` maximizes `s ↦ u s x₀ - ε s` from the left, so its derivative is `≥ 0`.
  have hg : HasDerivAt (fun s ↦ u s x₀ - ε * s) (deriv (fun s ↦ u s x₀) t₀ - ε) t₀ := by
    simpa using (hdiff ht₀T hint).hasDerivAt.fun_sub ((hasDerivAt_id t₀).const_mul ε)
  have hleft : IsLocalMaxOn (fun s ↦ u s x₀ - ε * s) (Iic t₀) t₀ :=
    Filter.mem_of_superset (Icc_mem_nhdsLE hpos) fun s hs ↦ hmax' ⟨hs.1, hs.2.trans ht₀.2⟩ hx₀
  -- Hence `0 < ε ≤ ∂ₜu ≤ Δu + b·∇u` at `(t₀, x₀)`, which rules out the spatial local maximum.
  refine not_isLocalMax_of_laplacian_add_fderiv_pos (v := b t₀ x₀) (hcd ht₀T hint) ?_ hloc
  linarith [hleft.hasDerivWithinAt_Iic_nonneg hg.hasDerivWithinAt, hsub ht₀T hint]

/-- **Weak maximum principle for `∂ₜ - Δ - b·∇`.**

Let `K` be compact. Suppose `u` is continuous on the closed cylinder `[0, T] × K`, is `C²` in
space and differentiable in time on the open cylinder `(0, T) × interior K`, and is a subsolution
there: `∂ₜu ≤ Δu + b·∇u`. If `u ≤ m` on the parabolic boundary, that is on the bottom `{0} × K`
and on the lateral side `[0, T] × frontier K`, then `u ≤ m` on all of `[0, T] × K`. No bound on
the drift `b` is needed. -/
theorem le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary (hK : IsCompact K) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t ≤ Δ (u t) x + fderiv ℝ (u t) x (b t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ m := by
  intro t ht x hx
  -- Below the top, let `ε → 0` in the perturbed bound `u - εt ≤ m`.
  have hlt : ∀ s ∈ Ico 0 T, u s x ≤ m := fun s hs ↦
    le_of_forall_pos_mul_le hs.1 fun ε hε ↦ by
      have := sub_mul_le_of_deriv_le_laplacian_add_fderiv hK hcont hcd hdiff hsub hinit hlat
        hε hs.2 ⟨hs.1, le_rfl⟩ hx
      linarith
  rcases ht.2.lt_or_eq with htT | rfl
  · exact hlt t ⟨ht.1, htT⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · exact h0 ▸ hinit hx
  -- At the top `t = T > 0`, pass to the limit from below by continuity.
  have hcw : ContinuousWithinAt (fun s ↦ u s x) (Ico 0 t) t :=
    ((hcont.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hx⟩) t ht).mono
      Ico_subset_Icc_self
  exact hcw.closure_le (by rw [closure_Ico hpos.ne]; exact ht) continuousWithinAt_const hlt

/-- **Weak maximum principle for the heat equation.** A subsolution `∂ₜu ≤ Δu` of the heat
equation, continuous on the closed cylinder `[0, T] × K` over a compact `K` and regular on the
open cylinder `(0, T) × interior K`, is bounded on `[0, T] × K` by any bound it satisfies on the
parabolic boundary `({0} × K) ∪ ([0, T] × frontier K)`. -/
theorem le_of_deriv_le_laplacian_le_parabolicBoundary (hK : IsCompact K) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t ≤ Δ (u t) x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ m :=
  le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary (b := 0) hK hcont hcd hdiff
    (fun t ht x hx ↦ by simpa using hsub ht hx) hinit hlat

/-- **Weak minimum principle for `∂ₜ - Δ - b·∇`.** The dual of
`le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary` for supersolutions
(`Δu + b·∇u ≤ ∂ₜu`): any lower bound on the parabolic boundary holds on all of `[0, T] × K`. -/
theorem ge_of_laplacian_add_fderiv_le_deriv_ge_parabolicBoundary (hK : IsCompact K) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      Δ (u t) x + fderiv ℝ (u t) x (b t x) ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ ⦃x⦄, x ∈ K → m ≤ u 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → m ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → m ≤ u t x := by
  intro t ht x hx
  have h := le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary (u := -u) (b := b)
    (m := -m) hK hcont.neg (fun s hs y hy ↦ (hcd hs hy).neg)
    (fun s hs y hy ↦ (hdiff hs hy).neg)
    (fun s hs y hy ↦ by
      simp only [Pi.neg_apply, deriv.fun_neg, congrFun laplacian_neg y, fderiv_neg, neg_apply]
      linarith [hsuper hs hy])
    (fun y hy ↦ neg_le_neg (hinit hy)) (fun s hs y hy ↦ neg_le_neg (hlat hs hy)) ht hx
  simp only [Pi.neg_apply] at h
  linarith

/-- **Weak minimum principle for the heat equation.** A supersolution `Δu ≤ ∂ₜu` of the heat
equation, continuous on the closed cylinder `[0, T] × K` over a compact `K` and regular on the
open cylinder `(0, T) × interior K`, satisfies on `[0, T] × K` any lower bound it satisfies on the
parabolic boundary `({0} × K) ∪ ([0, T] × frontier K)`. -/
theorem ge_of_laplacian_le_deriv_ge_parabolicBoundary (hK : IsCompact K) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → Δ (u t) x ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ ⦃x⦄, x ∈ K → m ≤ u 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → m ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → m ≤ u t x :=
  ge_of_laplacian_add_fderiv_le_deriv_ge_parabolicBoundary (b := 0) hK hcont hcd hdiff
    (fun t ht x hx ↦ by simpa using hsuper ht hx) hinit hlat

/-- **Comparison principle for `∂ₜ - Δ - b·∇`.** If `(∂ₜ - Δ - b·∇) u ≤ (∂ₜ - Δ - b·∇) v` on the
open cylinder `(0, T) × interior K` and `u ≤ v` on the parabolic boundary, then `u ≤ v` on all of
`[0, T] × K`. -/
theorem le_of_deriv_sub_laplacian_sub_fderiv_le_of_le_parabolicBoundary (hK : IsCompact K)
    {v : ℝ → E → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t - (Δ (u t) x + fderiv ℝ (u t) x (b t x)) ≤
        deriv (fun s ↦ v s x) t - (Δ (v t) x + fderiv ℝ (v t) x (b t x)))
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ v 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x := by
  intro t ht x hx
  have h := le_of_deriv_le_laplacian_add_fderiv_le_parabolicBoundary (u := u - v) (b := b)
    (m := 0) hK (hucont.sub hvcont) (fun s hs y hy ↦ (hucd hs hy).sub (hvcd hs hy))
    (fun s hs y hy ↦ (hudiff hs hy).sub (hvdiff hs hy))
    (fun s hs y hy ↦ by
      have hud : DifferentiableAt ℝ (u s) y := (hucd hs hy).differentiableAt (by norm_num)
      have hvd : DifferentiableAt ℝ (v s) y := (hvcd hs hy).differentiableAt (by norm_num)
      simp only [Pi.sub_apply, deriv_fun_sub (hudiff hs hy) (hvdiff hs hy),
        (hucd hs hy).laplacian_sub (hvcd hs hy), fderiv_sub hud hvd,
        sub_apply]
      linarith [hL hs hy])
    (fun y hy ↦ sub_nonpos.mpr (hinit hy)) (fun s hs y hy ↦ sub_nonpos.mpr (hlat hs hy)) ht hx
  exact sub_nonpos.mp h

/-- **Comparison principle for the heat equation.** If `∂ₜu - Δu ≤ ∂ₜv - Δv` on the open
cylinder `(0, T) × interior K` and `u ≤ v` on the parabolic boundary, then `u ≤ v` on all of
`[0, T] × K`. -/
theorem le_of_deriv_sub_laplacian_le_of_le_parabolicBoundary (hK : IsCompact K)
    {v : ℝ → E → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t - Δ (u t) x ≤ deriv (fun s ↦ v s x) t - Δ (v t) x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ v 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x :=
  le_of_deriv_sub_laplacian_sub_fderiv_le_of_le_parabolicBoundary (b := 0) hK hucont hvcont
    hucd hvcd hudiff hvdiff (fun t ht x hx ↦ by simpa using hL ht hx) hinit hlat

/-- **Uniqueness for the initial-boundary value problem of `∂ₜ - Δ - b·∇`.** Two functions with
equal values of `∂ₜ - Δ - b·∇` on the open cylinder `(0, T) × interior K` and equal values on the
parabolic boundary agree on all of `[0, T] × K`. -/
theorem eqOn_of_deriv_sub_laplacian_sub_fderiv_eq_of_eqOn_parabolicBoundary (hK : IsCompact K)
    {v : ℝ → E → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t - (Δ (u t) x + fderiv ℝ (u t) x (b t x)) =
        deriv (fun s ↦ v s x) t - (Δ (v t) x + fderiv ℝ (v t) x (b t x)))
    (hinit : EqOn (u 0) (v 0) K)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → EqOn (u t) (v t) (frontier K)) :
    EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ K) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  apply le_antisymm
  · exact le_of_deriv_sub_laplacian_sub_fderiv_le_of_le_parabolicBoundary hK hucont hvcont
      hucd hvcd hudiff hvdiff (fun s hs y hy ↦ (hL hs hy).le) (fun y hy ↦ (hinit hy).le)
      (fun s hs y hy ↦ (hlat hs hy).le) ht hx
  · exact le_of_deriv_sub_laplacian_sub_fderiv_le_of_le_parabolicBoundary hK hvcont hucont
      hvcd hucd hvdiff hudiff (fun s hs y hy ↦ (hL hs hy).ge) (fun y hy ↦ (hinit hy).ge)
      (fun s hs y hy ↦ (hlat hs hy).ge) ht hx

/-- **Uniqueness for the initial-boundary value problem of the heat equation.** Two functions with
equal values of `∂ₜ - Δ` on the open cylinder `(0, T) × interior K` and equal values on the
parabolic boundary agree on all of `[0, T] × K`. -/
theorem eqOn_of_deriv_sub_laplacian_eq_of_eqOn_parabolicBoundary (hK : IsCompact K)
    {v : ℝ → E → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      deriv (fun s ↦ u s x) t - Δ (u t) x = deriv (fun s ↦ v s x) t - Δ (v t) x)
    (hinit : EqOn (u 0) (v 0) K)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → EqOn (u t) (v t) (frontier K)) :
    EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ K) :=
  eqOn_of_deriv_sub_laplacian_sub_fderiv_eq_of_eqOn_parabolicBoundary (b := 0) hK hucont hvcont
    hucd hvcd hudiff hvdiff (fun t ht x hx ↦ by simpa using hL ht hx) hinit hlat

end TauCeti

end
