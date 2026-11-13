/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.InnerProductSpace.Sphere.Cap
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Exponential decay of subsolutions of `-Δ + c²`

Let `u` be a subsolution of the screened operator `-Δ + c²` for some `c ≥ 0`, that is `c² u ≤ Δ u`,
on a region of a finite-dimensional real inner product space. Such a function decays exponentially
at rate `c` away from the boundary of the region. This file proves two forms of this.

**Outside a ball.** If `u` is defined on the exterior `‖x‖ ≥ R`, with `u → 0` at infinity, and
`u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then

`u x ≤ M exp (-c (‖x‖ - R))` for `‖x‖ ≥ R`.

The barrier `M exp (-c (‖x‖ - R))` is a supersolution of `-Δ + c²` away from the origin: its
Laplacian is `(c² - (dim E - 1) c / ‖x‖)` times itself (`ContDiffAt.laplacian_comp_norm`). The
comparison principle for `-Δ + c²` on the compact annuli `R ≤ ‖x‖ ≤ R'`
(`TauCeti.le_of_mul_le_laplacian_le_of_le_frontier`) and the limit at infinity, which controls the
outer sphere as `R' → ∞`, then give the bound.

**Inside a ball.** Let the space be nontrivial. If `u` is defined on the closed ball of radius
`R ≥ 0` about `x`, is a subsolution at the points where `u > 0`, and `u ≤ M` on its boundary
sphere, with `M ≥ 0`, then for every `κ < 1`

`u x ≤ N M exp (-κ c R)`,

with a constant `N` depending only on the space and `κ`, not on `c`, `R` or `u`. Here the barrier
is a sum `∑_θ cosh (c ⟪θ, y - x⟫)` of plane waves along finitely many unit vectors `θ`, an
eigenfunction of `Δ` with eigenvalue `c²` (`ContDiffAt.laplacian_comp_inner_sub`). The directions
are chosen so that every unit vector `v` has `⟪θ, v⟫ ≥ κ` for one of them, so on the boundary
sphere one plane wave is at least `exp (κ c R) / 2`, while at the centre the barrier is the number
of plane waves. The loss from the sharp rate `c` to `κ c` is the price of this finite barrier.

The exterior bound holds for subsolutions of `-Δ + V` with a variable potential `V ≥ c²`, since
the barrier is nonnegative and hence also a supersolution of `-Δ + V`. Such potentials arise for
solutions of a linear equation `Δ u = V u` of indefinite sign, to which the constant form does not
apply: both `u` and `-u` are subsolutions of `-Δ + V`, so `|u|` decays at the rate `c`. The
interior bounds only constrain `u` where it is positive, and there `V u ≤ Δ u` with `V ≥ c²`
already gives `c² u ≤ Δ u`, so they are stated for the constant potential `c²`. A constant source
`K ≥ 0`, `c² u ≤ Δ u + K` with `c > 0`, costs the additive term `K / c²` in the interior bound.

Outside a ball, a forcing of size `B exp (-c ‖x‖)` is absorbed when the potential is bounded
below by `a²` with `a > c > 0`: then `u x ≤ M exp (-c (‖x‖ - R)) + B / (a² - c²) exp (-c ‖x‖)`.
This forced version is what differentiating a screened equation produces.

This is the decay mechanism of massive fields. Outside a large disc the logarithmic modulus defect
`-log |α|²` of a plane vortex is such a subsolution for every rate `c < 1 / 2`. For the
large-parameter Seiberg–Witten equations the screening rate is of order `√r`, and the interior
bound with a source has the shape `C / r + C exp (-c √r R)` of Taubes's estimates on balls of
radius `R` missing the zeros of the spinor.

## Main declarations

* `TauCeti.le_mul_exp_of_mul_le_laplacian`: a subsolution of `-Δ + V`, `V ≥ c²`, on the exterior of
  a ball which tends to zero at infinity is bounded by `M exp (-c (‖x‖ - R))`.
* `TauCeti.le_mul_exp_of_sq_mul_le_laplacian`: the case of the constant potential `c²`.
* `TauCeti.le_mul_exp_add_div_mul_exp_of_mul_sub_le_laplacian`: the version with a forcing of
  size `B exp (-c ‖x‖)` and a potential `V ≥ a² > c²`.
* `TauCeti.exists_forall_le_mul_mul_exp_of_sq_mul_le_laplacian`: a subsolution of `-Δ + c²` on
  a ball of radius `R` is bounded at the centre by `N M exp (-κ c R)`.
* `TauCeti.exists_forall_le_div_sq_add_mul_mul_exp_of_sq_mul_le_laplacian_add`: the same with a
  constant source `K`, with the bound `K / c² + N M exp (-κ c R)`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (the maximum principle and comparison with barriers).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric Set Topology InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The barrier `A exp (-c ‖x‖) + ε` is a supersolution of `-Δ + c²` away from the origin when
`A ≥ 0`, `c ≥ 0` and `ε ≥ 0`. -/
private theorem laplacian_exp_barrier_le {A c ε : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ A * Real.exp (-(c * ‖y‖)) + ε) x ≤
      c ^ 2 * (A * Real.exp (-(c * ‖x‖)) + ε) := by
  have hF : ContDiffAt ℝ 2 (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) ‖x‖ := by fun_prop
  have hd : deriv (fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) =
      fun t ↦ -(c * (A * Real.exp (-(c * t)))) := by
    funext t
    simp (disch := fun_prop)
    ring
  have hdd : deriv (deriv fun t : ℝ ↦ A * Real.exp (-(c * t)) + ε) =
      fun t ↦ c ^ 2 * (A * Real.exp (-(c * t))) := by
    funext t
    simp (disch := fun_prop)
    ring
  rw [hF.laplacian_comp_norm hx, hdd, hd]
  dsimp only
  have hdim : (0 : ℝ) ≤ Module.finrank ℝ E - 1 := by
    have : 0 < Module.finrank ℝ E := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
    have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast this
    linarith
  have hterm : 0 ≤ (Module.finrank ℝ E - 1) * (c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖ := by
    positivity
  have hneg : (Module.finrank ℝ E - 1) * -(c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖ =
      -((Module.finrank ℝ E - 1) * (c * (A * Real.exp (-(c * ‖x‖)))) / ‖x‖) := by ring
  have hε' : 0 ≤ c ^ 2 * ε := by positivity
  rw [hneg, mul_add]
  linarith

/-- **Exponential decay of subsolutions of `-Δ + V` with `V ≥ c²`.** Let `u` be continuous on the
exterior `‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with `V u ≤ Δ u` there for a
potential `V ≥ c²`, `c ≥ 0`, and `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with
`M ≥ 0`, then `u x ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_of_mul_le_laplacian {u V : E → ℝ} {R c M : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hM : 0 ≤ M) (hcont : ContinuousOn u {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x) (hV : ∀ x, R < ‖x‖ → c ^ 2 ≤ V x)
    (hsub : ∀ x, R < ‖x‖ → V x * u x ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
  have hx₀ : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have : Nontrivial E := ⟨⟨x, 0, hx₀⟩⟩
  -- The barrier, rewritten as a radial profile with amplitude `A = M exp (c R)`.
  set A := M * Real.exp (c * R) with hA
  have hAnn : 0 ≤ A := by positivity
  have hbar : ∀ y : E, M * Real.exp (-(c * (‖y‖ - R))) = A * Real.exp (-(c * ‖y‖)) := by
    intro y
    rw [hA, exp_neg_mul_sub, mul_assoc]
  rw [hbar]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Beyond some radius `R₁`, `u ≤ ε`; compare on the annulus `R ≤ ‖y‖ ≤ max R₁ ‖x‖`.
  obtain ⟨R₁, hR₁⟩ := (hasBasis_cobounded_norm.eventually_iff).mp
    (cobounded_eq_cocompact (α := E) ▸ hlim.eventually (eventually_le_nhds hε))
  set R' := max R₁ ‖x‖
  set K := closedBall (0 : E) R' ∩ (ball 0 R)ᶜ
  have hK : IsCompact K := (isCompact_closedBall 0 R').inter_right isOpen_ball.isClosed_compl
  have hKsub : K ⊆ {y | R ≤ ‖y‖} := fun y hy ↦ by simpa using hy.2
  -- Interior points of the annulus lie outside the closed inner ball.
  have hint : ∀ ⦃y : E⦄, y ∈ interior K → R < ‖y‖ := fun y hy ↦ by
    rw [interior_inter, interior_compl, closure_ball 0 hR.ne'] at hy
    simpa using hy.2
  -- Frontier points of the annulus lie on the outer or the inner sphere.
  have hfront : ∀ ⦃y : E⦄, y ∈ frontier K → ‖y‖ = R' ∨ ‖y‖ = R := fun y hy ↦ by
    rcases frontier_closedBall_sdiff_ball_subset (0 : E) R R' (by rwa [sdiff_eq]) with hy | hy
    · exact .inl (by simpa using hy)
    · exact .inr (by simpa using hy)
  have hyne : ∀ ⦃y : E⦄, y ∈ interior K → y ≠ 0 := fun y hy ↦
    norm_pos_iff.mp (hR.trans (hint hy))
  refine le_of_mul_le_laplacian_le_of_le_frontier (c := V)
    (g := fun y ↦ A * Real.exp (-(c * ‖y‖)) + ε) hK (hcont.mono hKsub) (by fun_prop)
    (fun y hy ↦ hcd y (hint hy))
    (fun y hy ↦ (((contDiffAt_norm ℝ (hyne hy)).const_smul c).neg.exp.const_smul A).add
      contDiffAt_const)
    (fun y hy ↦ (sq_nonneg c).trans (hV y (hint hy))) (fun y hy ↦ hsub y (hint hy))
    (fun y hy ↦ (laplacian_exp_barrier_le hAnn hc hε.le (hyne hy)).trans
      (mul_le_mul_of_nonneg_right (hV y (hint hy)) (by positivity))) (fun y hy ↦ ?_)
    ⟨mem_closedBall_zero_iff.mpr (le_max_right _ _), by simpa using hx⟩
  rcases hfront hy with hy' | hy'
  · have hR₁y : R₁ ≤ ‖y‖ := hy' ▸ le_max_left _ _
    have h₁ : u y ≤ ε := hR₁.2 hR₁y
    have : 0 ≤ A * Real.exp (-(c * ‖y‖)) := by positivity
    linarith
  · have h₁ := hbdry y hy'
    rw [← hbar, hy', sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith

/-- **Exponential decay of subsolutions of `-Δ + c²`.** Let `u` be continuous on the exterior
`‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, with `c² u ≤ Δ u` there for some `c ≥ 0`
and `u → 0` at infinity. If `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then
`u x ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. -/
theorem le_mul_exp_of_sq_mul_le_laplacian {u : E → ℝ} {R c M : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hM : 0 ≤ M) (hcont : ContinuousOn u {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x) (hsub : ∀ x, R < ‖x‖ → c ^ 2 * u x ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) :=
  le_mul_exp_of_mul_le_laplacian (V := fun _ ↦ c ^ 2) hR hc hM hcont hcd (fun _ _ ↦ le_rfl) hsub
    hbdry hlim hx

/-- **Exponential decay of forced subsolutions of `-Δ + V`.** Let `u` be continuous on the exterior
`‖x‖ ≥ R` of a ball of radius `R > 0`, `C²` on `‖x‖ > R`, and `u → 0` at infinity. Suppose that
`V u - B exp (-c ‖x‖) ≤ Δ u` there for a potential `V ≥ a²` and a forcing constant `B ≥ 0`, where
`0 < c < a`. If `u ≤ M` on the sphere `‖x‖ = R`, with `M ≥ 0`, then for every `x` with `‖x‖ ≥ R`,

`u x ≤ M exp (-c (‖x‖ - R)) + B / (a² - c²) exp (-c ‖x‖)`.

The margin `a² - c²` between the potential and the rate absorbs the forcing: the barrier
`B / (a² - c²) exp (-c ‖x‖)` is a supersolution of `-Δ + V` with forcing `B exp (-c ‖x‖)`. -/
theorem le_mul_exp_add_div_mul_exp_of_mul_sub_le_laplacian {u V : E → ℝ} {R a c M B : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hca : c < a) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hcont : ContinuousOn u {x | R ≤ ‖x‖}) (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x)
    (hV : ∀ x, R < ‖x‖ → a ^ 2 ≤ V x)
    (hsub : ∀ x, R < ‖x‖ → V x * u x - B * Real.exp (-(c * ‖x‖)) ≤ Δ u x)
    (hbdry : ∀ x, ‖x‖ = R → u x ≤ M) (hlim : Tendsto u (cocompact E) (𝓝 0)) {x : E}
    (hx : R ≤ ‖x‖) :
    u x ≤ M * Real.exp (-(c * (‖x‖ - R))) + B / (a ^ 2 - c ^ 2) * Real.exp (-(c * ‖x‖)) := by
  have hgap : 0 < a ^ 2 - c ^ 2 := by nlinarith
  set A := B / (a ^ 2 - c ^ 2) with hA
  have hA₀ : 0 ≤ A := div_nonneg hB hgap.le
  -- Subtract the barrier `A exp (-c ‖x‖)`; the difference is an unforced subsolution.
  set b : E → ℝ := fun y ↦ A * Real.exp (-(c * ‖y‖)) with hb
  have hbcd : ∀ y : E, R < ‖y‖ → ContDiffAt ℝ 2 b y := fun y hy ↦ by
    have hy₀ : y ≠ 0 := norm_pos_iff.mp (hR.trans hy)
    have := (contDiffAt_norm ℝ hy₀ (n := 2))
    fun_prop
  have hle := le_mul_exp_of_mul_le_laplacian (u := u - b) (V := V) hR hc.le hM
    (hcont.sub (by fun_prop)) (fun y hy ↦ (hcd y hy).sub (hbcd y hy))
    (fun y hy ↦ (pow_le_pow_left₀ hc.le hca.le 2).trans (hV y hy)) ?_
    (fun y hy ↦ by
      have : 0 ≤ b y := by positivity
      simp only [Pi.sub_apply]
      linarith [hbdry y hy]) ?_ hx
  · simp only [hb, Pi.sub_apply] at hle
    linarith
  · intro y hy
    have hy₀ : y ≠ 0 := norm_pos_iff.mp (hR.trans hy)
    rw [(hcd y hy).laplacian_sub (hbcd y hy)]
    have hΔb : Δ b y ≤ c ^ 2 * b y := by
      simpa [hb] using laplacian_exp_barrier_le (ε := 0) hA₀ hc.le le_rfl hy₀
    have hcoef : B = A * (a ^ 2 - c ^ 2) := by
      rw [hA, div_mul_cancel₀ _ hgap.ne']
    have he : 0 ≤ Real.exp (-(c * ‖y‖)) := (Real.exp_pos _).le
    have hVy := hV y hy
    have hsuby := hsub y hy
    simp only [hb, Pi.sub_apply] at hΔb ⊢
    rw [hcoef] at hsuby
    nlinarith [mul_nonneg (mul_nonneg hA₀ he) (sub_nonneg.mpr hVy)]
  · have hexp : Tendsto b (cocompact E) (𝓝 0) := by
      simpa [hb] using (tendsto_exp_neg_mul_norm_cocompact (E := E) hc).const_mul A
    rw [Pi.sub_def]
    simpa only [sub_zero] using hlim.sub hexp

/-! ### Decay inside a ball -/

/-- The plane wave `cosh (c ⟪θ, z - x⟫)` along a unit vector `θ` is an eigenfunction of `Δ` with
eigenvalue `c²`. -/
private theorem laplacian_cosh_mul_inner_sub (c : ℝ) {θ : E} (hθ : ‖θ‖ = 1) (x y : E) :
    Δ (fun z ↦ Real.cosh (c * ⟪θ, z - x⟫_ℝ)) y = c ^ 2 * Real.cosh (c * ⟪θ, y - x⟫_ℝ) := by
  rw [ContDiffAt.laplacian_comp_inner_sub (g := (Real.cosh <| c * ·))
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).contDiffAt,
    deriv_deriv_comp_mul_left, Real.deriv_cosh, Real.deriv_sinh, hθ, one_pow, one_smul,
    smul_eq_mul]

omit [FiniteDimensional ℝ E] in
/-- On the sphere `‖y - x‖ = R`, the sum of the plane waves `cosh (c ⟪θ, y - x⟫)` over directions
`θ` as in `exists_finset_forall_exists_le_inner` is at least `exp (κ c R) / 2`. -/
private theorem exp_div_two_le_sum_cosh_mul_inner_sub {S : Finset E} {κ : ℝ}
    (hS : ∀ v : E, ‖v‖ = 1 → ∃ θ ∈ S, max κ 0 ≤ ⟪θ, v⟫_ℝ) {x y : E} {R c : ℝ} (hR : 0 < R)
    (hc : 0 ≤ c) (hy : y ∈ sphere x R) :
    Real.exp (κ * c * R) / 2 ≤ ∑ θ ∈ S, Real.cosh (c * ⟪θ, y - x⟫_ℝ) := by
  have hyR : ‖y - x‖ = R := by simpa [dist_eq_norm] using hy
  obtain ⟨θ, hθS, hθ⟩ := hS (R⁻¹ • (y - x)) (by
    rw [norm_smul, hyR, norm_inv, Real.norm_eq_abs, abs_of_pos hR, inv_mul_cancel₀ hR.ne'])
  rw [real_inner_smul_right, le_inv_mul_iff₀ hR] at hθ
  -- The plane wave along `θ` alone is at least `exp (κ c R) / 2`.
  have h1 : κ * c * R ≤ c * ⟪θ, y - x⟫_ℝ := by
    nlinarith [le_max_left κ 0, mul_nonneg hc hR.le, mul_le_mul_of_nonneg_left hθ hc]
  have h2 : Real.exp (c * ⟪θ, y - x⟫_ℝ) / 2 ≤ Real.cosh (c * ⟪θ, y - x⟫_ℝ) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(c * ⟪θ, y - x⟫_ℝ))]
  exact ((div_le_div_of_nonneg_right (Real.exp_le_exp.2 h1) zero_le_two).trans h2).trans
    (Finset.single_le_sum (f := fun θ ↦ Real.cosh (c * ⟪θ, y - x⟫_ℝ))
      (fun θ _ ↦ (Real.cosh_pos _).le) hθS)

variable [Nontrivial E]

/-- **Exponential decay inside a ball of subsolutions of `-Δ + c²`.** For every `κ < 1` there is
a constant `N`, depending only on `E` and `κ`, with the following property. Let `u` be continuous
on the closed ball of radius `R ≥ 0` about `x` and, at the points of the open ball where `u > 0`,
`C²` with `c² u ≤ Δ u`, `c ≥ 0`. If `u ≤ M` on the boundary sphere, with `M ≥ 0`, then at the
centre

`u x ≤ N M exp (-κ c R)`.

The constant does not depend on `c`, `R`, `x` or `u`, so the bound is uniform as the screening
rate `c` grows. A subsolution of `-Δ + V` with `V ≥ c²` where `u > 0` is in particular one of
`-Δ + c²` there. -/
theorem exists_forall_le_mul_mul_exp_of_sq_mul_le_laplacian {κ : ℝ} (hκ : κ < 1) :
    ∃ N : ℝ, 0 < N ∧ ∀ ⦃u : E → ℝ⦄ ⦃x : E⦄ ⦃R c M : ℝ⦄, 0 ≤ R → 0 ≤ c → 0 ≤ M →
      ContinuousOn u (closedBall x R) → (∀ y ∈ ball x R, 0 < u y → ContDiffAt ℝ 2 u y) →
      (∀ y ∈ ball x R, 0 < u y → c ^ 2 * u y ≤ Δ u y) →
      (∀ y ∈ sphere x R, u y ≤ M) → u x ≤ N * M * Real.exp (-(κ * c * R)) := by
  obtain ⟨S, hSunit, hS⟩ := exists_finset_forall_exists_le_inner (F := E) (max_lt hκ one_pos)
  refine ⟨2 * (S.card + 1), by positivity, fun u x R c M hR hc hM hcont hcd hsub hbdry ↦ ?_⟩
  rcases hR.eq_or_lt with rfl | hR
  · have := hbdry x (by simp)
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one]
    nlinarith
  -- The barrier `g = A ∑_θ cosh (c ⟪θ, y - x⟫)`, with `A = 2 M exp (-κ c R)`.
  set A := 2 * M * Real.exp (-(κ * c * R)) with hA
  have hA0 : 0 ≤ A := by positivity
  set w : E → ℝ := fun y ↦ ∑ θ ∈ S, Real.cosh (c * ⟪θ, y - x⟫_ℝ) with hw
  have hθcd (θ y : E) : ContDiffAt ℝ 2 (fun z ↦ Real.cosh (c * ⟪θ, z - x⟫_ℝ)) y :=
    (Real.contDiff_cosh.comp (contDiff_const.mul
      (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)))).contDiffAt
  have hwcd (y : E) : ContDiffAt ℝ 2 w y := ContDiffAt.sum fun θ _ ↦ hθcd θ y
  have hw0 (y : E) : 0 ≤ w y := Finset.sum_nonneg fun θ _ ↦ (Real.cosh_pos _).le
  have hlap (y : E) : Δ (A • w) y = c ^ 2 * (A • w) y := by
    rw [laplacian_smul A (hwcd y), hw, laplacian_fun_sum
      (f := fun θ z ↦ Real.cosh (c * ⟪θ, z - x⟫_ℝ)) fun θ _ ↦ hθcd θ y]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ hθ ↦ ?_
    rw [laplacian_cosh_mul_inner_sub c (hSunit θ hθ)]
    ring
  have hint : interior (closedBall x R) = ball x R := interior_closedBall x hR.ne'
  -- The maximum principle above `0` for `u - A • w`, which is positive only where `u` is.
  have hpos {y : E} (hy : 0 < (u - A • w) y) : 0 < u y := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy
    linarith [mul_nonneg hA0 (hw0 y)]
  have hle := le_of_laplacian_nonneg_of_lt_le_frontier (f := u - A • w) (m := 0)
    (isCompact_closedBall x R)
    (hcont.sub fun y _ ↦ ((hwcd y).const_smul A).continuousAt.continuousWithinAt)
    (fun y hy hy0 ↦ (hcd y (hint ▸ hy) (hpos hy0)).sub ((hwcd y).const_smul A))
    (fun y hy hy0 ↦ by
      have hy' : y ∈ ball x R := hint ▸ hy
      have h2 := mul_nonneg (sq_nonneg c) hy0.le
      rw [Pi.sub_apply, mul_sub] at h2
      have hAw : ContDiffAt ℝ 2 (A • w) y := (hwcd y).const_smul A
      rw [(hcd y hy' (hpos hy0)).laplacian_sub hAw, hlap]
      linarith [hsub y hy' (hpos hy0)])
    (fun y hy ↦ by
      rw [frontier_closedBall x hR.ne'] at hy
      rw [Pi.sub_apply, sub_nonpos]
      have hexp : Real.exp (-(κ * c * R)) * Real.exp (κ * c * R) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      calc u y ≤ M := hbdry y hy
        _ = A * (Real.exp (κ * c * R) / 2) := by
          rw [hA, show 2 * M * Real.exp (-(κ * c * R)) * (Real.exp (κ * c * R) / 2) =
            M * (Real.exp (-(κ * c * R)) * Real.exp (κ * c * R)) by ring, hexp, mul_one]
        _ ≤ (A • w) y := mul_le_mul_of_nonneg_left
          (exp_div_two_le_sum_cosh_mul_inner_sub hS hR hc hy) hA0)
    (mem_closedBall_self hR.le)
  -- At the centre every plane wave equals one.
  have hwx : w x = S.card := by simp [hw]
  rw [Pi.sub_apply, sub_nonpos, Pi.smul_apply, smul_eq_mul, hwx, hA] at hle
  have : 0 ≤ M * Real.exp (-(κ * c * R)) := by positivity
  nlinarith

/-- **Exponential decay inside a ball of subsolutions of `-Δ + c²` with a source.** For every
`κ < 1` there is a constant `N`, depending only on `E` and `κ`, with the following property. Let
`u` be continuous on the closed ball of radius `R ≥ 0` about `x` and, at the points of the open
ball where `u > K / c²`, `C²` with `c² u ≤ Δ u + K` for a constant `K ≥ 0` and `c > 0`. If
`u ≤ M` on the boundary sphere, with `M ≥ 0`, then at the centre

`u x ≤ K / c² + N M exp (-κ c R)`.

This is the form in which the bound is used for large-parameter equations, where `c` is of order
`√r`: the first term is of order `K / r` and the second decays exponentially in `√r R`. -/
theorem exists_forall_le_div_sq_add_mul_mul_exp_of_sq_mul_le_laplacian_add {κ : ℝ}
    (hκ : κ < 1) :
    ∃ N : ℝ, 0 < N ∧ ∀ ⦃u : E → ℝ⦄ ⦃x : E⦄ ⦃R c M K : ℝ⦄, 0 ≤ R → 0 < c → 0 ≤ M → 0 ≤ K →
      ContinuousOn u (closedBall x R) →
      (∀ y ∈ ball x R, K / c ^ 2 < u y → ContDiffAt ℝ 2 u y) →
      (∀ y ∈ ball x R, K / c ^ 2 < u y → c ^ 2 * u y ≤ Δ u y + K) →
      (∀ y ∈ sphere x R, u y ≤ M) → u x ≤ K / c ^ 2 + N * M * Real.exp (-(κ * c * R)) := by
  obtain ⟨N, hN0, hN⟩ := exists_forall_le_mul_mul_exp_of_sq_mul_le_laplacian (E := E) hκ
  refine ⟨N, hN0, fun u x R c M K hR hc hM hK hcont hcd hsub hbdry ↦ ?_⟩
  have hKc : 0 ≤ K / c ^ 2 := by positivity
  -- The shifted function `v = u - K / c²` is a subsolution of `-Δ + c²`.
  set v : E → ℝ := fun y ↦ u y - K / c ^ 2 with hv
  have hvu {y : E} (hy : 0 < v y) : K / c ^ 2 < u y := sub_pos.1 hy
  have hvsub (y : E) (hy : y ∈ ball x R) (hvy : 0 < v y) : c ^ 2 * v y ≤ Δ v y := by
    have hΔ : Δ v y = Δ u y := by
      have hvu' : v = u - fun _ ↦ K / c ^ 2 := by ext; simp [hv]
      rw [hvu', (hcd y hy (hvu hvy)).laplacian_sub contDiffAt_const, laplacian_const,
        Pi.zero_apply, sub_zero]
    have h1 : c ^ 2 * (K / c ^ 2) = K := by field_simp
    rw [hΔ, hv, mul_sub, h1]
    linarith [hsub y hy (hvu hvy)]
  have h := hN (u := v) hR hc.le hM (hcont.sub continuousOn_const)
    (fun y hy hvy ↦ (hcd y hy (hvu hvy)).sub contDiffAt_const) hvsub
    (fun y hy ↦ (sub_le_self _ hKc).trans (hbdry y hy))
  rw [hv] at h
  linarith

end TauCeti
