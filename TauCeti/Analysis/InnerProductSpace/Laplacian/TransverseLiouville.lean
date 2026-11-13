/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection
import TauCeti.Analysis.InnerProductSpace.Projection.Compact

/-!
# Liouville theorems for functions decaying in transverse directions

Let `E` be a finite-dimensional real inner product space and `K ≠ ⊥` a subspace, with orthogonal
projection `P = K.starProjection`. Split a point as `x = b + n` with `n = P x` the *transverse*
coordinate and `b ∈ Kᗮ` the *base* coordinate, as for `ℂ_base × ℂ_normal`. This file proves that
a function bounded above which is subharmonic where it is positive, and whose positive part tends
to zero as `‖P x‖ → ∞` uniformly in the base coordinate, is nonpositive
(`TauCeti.nonpos_of_eventually_comap_norm_starProjection_le_of_laplacian_nonneg`). Consequently a
bounded `C²` function with `0 ≤ f · Δ f` that tends to zero transversally vanishes identically
(`TauCeti.eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg`).

The decay is only assumed transversally: `f` need not tend to zero along the base, so the
cocompact Liouville theorem `TauCeti.eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg` does not
apply; boundedness is assumed instead. The sign condition `0 ≤ f · Δ f` holds for the difference
`f = u₁ - u₂` of two solutions of a semilinear equation `Δ u = F(x, u)` with `F` nondecreasing in
`u`. The typical instance is the logarithm `w = log |α₁|² - log |α₂|²` of the ratio of two
vortex-type sections with the same zeros over `ℂ × ℂ`, which satisfies `Δ w = c |α₂|² (e^w - 1)`
with `c ≥ 0`. When `w` is `C²` and bounded and both sections tend to the vacuum `|α| = 1` in the
normal direction, uniformly along the base, the theorem gives `w = 0`, so the two sections have the
same modulus `|α₁| = |α₂|`; identifying the sections and connections themselves up to gauge needs a
separate argument.

## Main results

* `TauCeti.nonpos_of_eventually_comap_norm_starProjection_le_of_laplacian_nonneg`: a function
  bounded above, `C²` and subharmonic where it is positive, whose positive part tends to zero
  transversally, is nonpositive.
* `TauCeti.eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg`: a bounded `C²`
  function with `0 ≤ f · Δ f` tending to zero transversally vanishes.

## Implementation notes

The Liouville theorem is proved by a maximum principle with a harmonic barrier. With `n = dim K`
and `d = dim Kᗮ`, the quadratic polynomial `n ‖b‖² - d ‖P x‖²` is harmonic, because the Laplacian
of the squared norm of an orthogonal projection is twice the rank of the projection
(`Submodule.laplacian_norm_starProjection_sq`). On the compact box where the base coordinate is at
most `L` from a point `x₀` and the transverse coordinate is at most `R`
(`Submodule.isCompact_starProjection_box`), a positive multiple of this polynomial, shifted by a
constant, dominates `f` on the whole boundary: on the transverse faces because `f` is small there,
and on the base faces because it is at least `sup f` there. The weak maximum principle gives the
bound at `x₀`, which is `O(1 / L²)` above the transverse bound, and `L → ∞` concludes.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, §3.1 (the weak maximum principle and barrier comparison).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Set Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The barrier `a + b (dim K ‖P_{Kᗮ} (z - x₀)‖² - dim Kᗮ ‖P_K (z - x₀)‖² + e)` is harmonic: by
`Submodule.laplacian_norm_starProjection_sq` the two squared norms have Laplacians `2 dim Kᗮ` and
`2 dim K`, which cancel. -/
private theorem laplacian_barrier (K : Submodule ℝ E) (x₀ : E) (a b e : ℝ) (y : E) :
    Δ (fun z ↦ a + b * (Module.finrank ℝ K * ‖Kᗮ.starProjection (z - x₀)‖ ^ 2 -
      Module.finrank ℝ Kᗮ * ‖K.starProjection (z - x₀)‖ ^ 2 + e)) y = 0 := by
  have hshift (S : Submodule ℝ E) :
      Δ (fun z ↦ ‖S.starProjection (z - x₀)‖ ^ 2) y = 2 * (Module.finrank ℝ S : ℝ) := by
    simp_rw [sub_eq_add_neg]
    rw [laplacian_comp_add_right (fun z ↦ ‖S.starProjection z‖ ^ 2) (-x₀)]
    exact S.laplacian_norm_starProjection_sq _
  have hsq (S : Submodule ℝ E) : ContDiff ℝ 2 fun z ↦ ‖S.starProjection (z - x₀)‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const))
  set A : E → ℝ := fun z ↦ ‖Kᗮ.starProjection (z - x₀)‖ ^ 2
  set B : E → ℝ := fun z ↦ ‖K.starProjection (z - x₀)‖ ^ 2
  set n : ℝ := (Module.finrank ℝ K : ℝ)
  set d : ℝ := (Module.finrank ℝ Kᗮ : ℝ)
  -- Write the barrier as a constant plus multiples of `A` and `B`, and use linearity of `Δ`.
  have hfun : (fun z ↦ a + b * (n * A z - d * B z + e)) =
      (fun _ ↦ a + b * e) + (b * n) • A - (b * d) • B := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h0 : ContDiffAt ℝ 2 (fun _ : E ↦ a + b * e) y := contDiffAt_const
  have h1 : ContDiffAt ℝ 2 ((b * n) • A) y := (hsq Kᗮ).contDiffAt.const_smul (b * n)
  have h2 : ContDiffAt ℝ 2 ((b * d) • B) y := (hsq K).contDiffAt.const_smul (b * d)
  have h01 : ContDiffAt ℝ 2 ((fun _ : E ↦ a + b * e) + (b * n) • A) y := h0.add h1
  rw [hfun, h01.laplacian_sub h2, h0.laplacian_add h1, laplacian_smul _ (hsq Kᗮ).contDiffAt,
    laplacian_smul _ (hsq K).contDiffAt, laplacian_const, Pi.zero_apply, hshift Kᗮ, hshift K,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The barrier step of the transverse Liouville theorem. If `f ≤ M` everywhere, `f ≤ ε` where
`‖P y‖ ≥ R`, and `‖P x₀‖ ≤ R`, then `f x₀ ≤ ε + M (dim Kᗮ) (2 R)² / ((dim K) L²)` for every `L > 0`:
the weak maximum principle on the box `‖P_{Kᗮ} (y - x₀)‖ ≤ L`, `‖P y‖ ≤ R` against a harmonic
quadratic barrier. -/
private theorem le_add_div_of_barrier {K : Submodule ℝ E} (hn : 0 < Module.finrank ℝ K)
    {f : E → ℝ} (hcont : Continuous f) (hcd : ∀ x, 0 < f x → ContDiffAt ℝ 2 f x)
    (hlap : ∀ x, 0 < f x → 0 ≤ Δ f x) {M ε R L : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, f y ≤ M)
    (hε : 0 < ε) (hL : 0 < L) (hR : ∀ y, R ≤ ‖K.starProjection y‖ → f y ≤ ε) {x₀ : E}
    (hx₀ : ‖K.starProjection x₀‖ ≤ R) :
    f x₀ ≤ ε + M * (Module.finrank ℝ Kᗮ * (2 * R) ^ 2) /
      (Module.finrank ℝ K * L ^ 2) := by
  obtain ⟨v, -, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hn)
  have : Nontrivial E := nontrivial_of_ne v 0 hv0
  set P := K.starProjection
  set Q := Kᗮ.starProjection
  set n : ℝ := (Module.finrank ℝ K : ℝ)
  set d : ℝ := (Module.finrank ℝ Kᗮ : ℝ)
  have hn' : 0 < n := Nat.cast_pos.2 hn
  set c : ℝ := M / (n * L ^ 2)
  -- The harmonic barrier `ψ`, compared with `f` on the box `S`.
  set ψ : E → ℝ := fun y ↦
    ε + c * (n * ‖Q (y - x₀)‖ ^ 2 - d * ‖P (y - x₀)‖ ^ 2 + d * (2 * R) ^ 2)
  have hψ : ContDiff ℝ 2 ψ := by
    have hsq (S : Submodule ℝ E) : ContDiff ℝ 2 fun z ↦ ‖S.starProjection (z - x₀)‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const))
    exact contDiff_const.add (contDiff_const.mul (((contDiff_const.mul (hsq Kᗮ)).sub
      (contDiff_const.mul (hsq K))).add contDiff_const))
  set S : Set E := {y | ‖Q (y - x₀)‖ ≤ L} ∩ {y | ‖P y‖ ≤ R}
  -- On `S` the transverse part of `y - x₀` has norm at most `2 R`, so `ψ ≥ ε + c n ‖Q (y - x₀)‖²`.
  have hnn (y : E) : 0 ≤ c * (n * ‖Q (y - x₀)‖ ^ 2) := by positivity
  have hψS {y : E} (hy : y ∈ S) : ε + c * (n * ‖Q (y - x₀)‖ ^ 2) ≤ ψ y := by
    have hPS : ‖P (y - x₀)‖ ≤ 2 * R := by
      have h := norm_sub_le (P y) (P x₀)
      rw [← map_sub] at h
      have hy2 : ‖P y‖ ≤ R := hy.2
      linarith
    have : ‖P (y - x₀)‖ ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPS 2
    have hd : 0 ≤ d := Nat.cast_nonneg _
    simp only [ψ]
    gcongr
    nlinarith
  -- The weak maximum principle for `f - ψ`, which is subharmonic where it is positive, since
  -- there `f > ψ ≥ ε > 0`.
  have hfpos {y : E} (hy : y ∈ interior S) (hpos : 0 < (f - ψ) y) : 0 < f y := by
    linarith [hψS (interior_subset hy), hnn y, Pi.sub_apply f ψ y]
  have hmax := le_of_laplacian_nonneg_of_lt_le_frontier (K.isCompact_starProjection_box x₀ L R)
    (f := f - ψ) (m := 0) (hcont.sub hψ.continuous).continuousOn
    (fun y hy hpos ↦ (hcd y (hfpos hy hpos)).sub hψ.contDiffAt)
    (fun y hy hpos ↦ by
      rw [(hcd y (hfpos hy hpos)).laplacian_sub hψ.contDiffAt, laplacian_barrier, sub_zero]
      exact hlap y (hfpos hy hpos))
    (fun y hy ↦ by
      have hlow := hψS ((K.isCompact_starProjection_box x₀ L R).isClosed.frontier_subset hy)
      rw [Pi.sub_apply, sub_nonpos]
      rcases frontier_inter_subset _ _ hy with ⟨hfr, -⟩ | ⟨-, hfr⟩
      · -- On a base face `‖Q (y - x₀)‖ = L`, the barrier is at least `M + ε`.
        have hyL : ‖Q (y - x₀)‖ = L :=
          frontier_le_subset_eq (f := fun y ↦ ‖Q (y - x₀)‖) (g := fun _ ↦ L) (by fun_prop)
            continuous_const hfr
        have hcnL : c * (n * L ^ 2) = M := by
          simp only [c]; field_simp
        rw [hyL, hcnL] at hlow
        linarith [hM y]
      · -- On a transverse face `‖P y‖ = R`, `f ≤ ε ≤ ψ`.
        have hyR : ‖P y‖ = R := frontier_le_subset_eq (f := fun y ↦ ‖P y‖) (g := fun _ ↦ R)
          (by fun_prop) continuous_const hfr
        linarith [hR y hyR.ge, hnn y])
    ⟨by simpa [Q] using hL.le, hx₀⟩
  have hψx₀ : ψ x₀ = ε + M * (d * (2 * R) ^ 2) / (n * L ^ 2) := by
    simp only [ψ, sub_self, map_zero, norm_zero, c]
    ring
  rw [Pi.sub_apply, sub_nonpos, hψx₀] at hmax
  exact hmax

/-- **Liouville theorem for transverse decay.** Let `K ≠ ⊥` be a subspace of a finite-dimensional
real inner product space. A continuous function `f` that is bounded above, `C²` and subharmonic
at the points where it is positive, and whose positive part tends to zero as the transverse
coordinate `‖K.starProjection x‖` tends to infinity, uniformly in the remaining coordinates, is
nonpositive. No decay along `Kᗮ` is assumed. -/
theorem nonpos_of_eventually_comap_norm_starProjection_le_of_laplacian_nonneg
    {K : Submodule ℝ E} (hK : K ≠ ⊥) {f : E → ℝ} (hcont : Continuous f)
    (hcd : ∀ x, 0 < f x → ContDiffAt ℝ 2 f x) (hlap : ∀ x, 0 < f x → 0 ≤ Δ f x)
    (hbdd : BddAbove (range f))
    (hdecay : ∀ ε > 0, ∀ᶠ x in comap (fun x ↦ ‖K.starProjection x‖) atTop, f x ≤ ε) (x : E) :
    f x ≤ 0 := by
  obtain ⟨M, hM⟩ := hbdd
  have hfM (y : E) : f y ≤ max M 0 := (hM ⟨y, rfl⟩).trans (le_max_left _ _)
  have hn : 0 < Module.finrank ℝ K := Submodule.one_le_finrank_iff.2 hK
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  -- Beyond the transverse radius `R`, `f ≤ ε / 2`; the barrier error is `A / L²`.
  obtain ⟨R₀, -, hR₀⟩ := (atTop_basis.comap fun x ↦ ‖K.starProjection x‖).eventually_iff.1
    (hdecay (ε / 2) (half_pos hε))
  set R := max R₀ ‖K.starProjection x‖
  have hR (y : E) (hy : R ≤ ‖K.starProjection y‖) : f y ≤ ε / 2 :=
    hR₀ ((le_max_left _ _).trans hy)
  set A := max M 0 * (Module.finrank ℝ Kᗮ * (2 * R) ^ 2) / Module.finrank ℝ K
  have hA : 0 ≤ A := by positivity
  set L := 2 * A / ε + 1
  have hL : 1 ≤ L := le_add_of_nonneg_left (by positivity)
  have hb := le_add_div_of_barrier hn hcont hcd hlap (le_max_right M 0) hfM (half_pos hε)
    (zero_lt_one.trans_le hL) hR (le_max_right _ _)
  have hAL : max M 0 * (Module.finrank ℝ Kᗮ * (2 * R) ^ 2) / (Module.finrank ℝ K * L ^ 2) =
      A / L ^ 2 := by
    rw [div_div, mul_comm (Module.finrank ℝ K : ℝ)]
  have hAε : A / L ^ 2 ≤ ε / 2 := by
    have hεL : ε / 2 * L = A + ε / 2 := by
      simp only [L]
      field_simp
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Liouville theorem for transverse decay under the sign condition `f · Δ f ≥ 0`.** Let
`K ≠ ⊥` be a subspace of a finite-dimensional real inner product space. A bounded `C²` function
with `0 ≤ f x * Δ f x` everywhere that tends to zero as `‖K.starProjection x‖ → ∞`, uniformly in
the remaining coordinates, vanishes identically. The sign condition holds for differences of
solutions of semilinear equations `Δ u = F(x, u)` with `F` nondecreasing in `u`. -/
theorem eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg
    {K : Submodule ℝ E} (hK : K ≠ ⊥) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hsign : ∀ x, 0 ≤ f x * Δ f x) (hbdd : Bornology.IsBounded (range f))
    (h : Tendsto f (comap (fun x ↦ ‖K.starProjection x‖) atTop) (𝓝 0)) : f = 0 := by
  have hev {g : E → ℝ} (hg : Tendsto g (comap (fun x ↦ ‖K.starProjection x‖) atTop) (𝓝 0)) :
      ∀ ε > 0, ∀ᶠ x in comap (fun x ↦ ‖K.starProjection x‖) atTop, g x ≤ ε :=
    fun ε hε ↦ hg.eventually (Iic_mem_nhds hε)
  obtain ⟨C, hC⟩ := hbdd.bddBelow
  funext x
  refine le_antisymm (nonpos_of_eventually_comap_norm_starProjection_le_of_laplacian_nonneg hK
    hf.continuous (fun _ _ ↦ hf.contDiffAt)
    (fun y hy ↦ (mul_nonneg_iff_of_pos_left hy).1 (hsign y)) hbdd.bddAbove (hev h) x) ?_
  have hneg := nonpos_of_eventually_comap_norm_starProjection_le_of_laplacian_nonneg (f := -f) hK
    hf.continuous.neg (fun _ _ ↦ hf.neg.contDiffAt)
    (fun y hy ↦ by
      rw [laplacian_neg, Pi.neg_apply]
      rw [Pi.neg_apply, neg_pos] at hy
      nlinarith [hsign y])
    ⟨-C, by rintro _ ⟨y, rfl⟩; simpa using hC ⟨y, rfl⟩⟩ (hev (by simpa [Pi.neg_def] using h.neg)) x
  simpa using hneg

end TauCeti
