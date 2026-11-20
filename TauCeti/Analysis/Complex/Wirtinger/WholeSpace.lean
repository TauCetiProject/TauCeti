/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.PowerSeries.Polydisc
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Polydisc

/-!
# The `bar∂`-Poincaré lemma on `ℂⁿ` and holomorphic gauges

On the coordinate space `ι → ℂ` of a finite index type, write
`∂u/∂(conj z_j) = conjWirtingerDeriv u z (Pi.single j 1)`. A smooth `(0,1)`-form
`∑ j, f_j d(conj z_j)` with coefficients in a complex Banach space is `bar∂`-closed when
`∂f_j/∂(conj z_i) = ∂f_i/∂(conj z_j)` for all `i, j`. This file proves that every such form on
all of `ℂⁿ` is `bar∂`-exact: some smooth `u` has `∂u/∂(conj z_j) = f_j` for every `j`
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_single_eq`). The polydisc version
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc`) only solves the
equation on a strictly smaller polydisc.

The proof is the exhaustion argument of the Dolbeault lemma on discs
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball`), with balls of the sup norm,
which are polydiscs, in place of discs. The polydisc lemma gives local solutions `h k` on the
balls `ball 0 (k + 2)`. Consecutive ones differ by a holomorphic function
(`TauCeti.differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero`), which a partial
sum of its multivariate Cauchy expansion approximates within `2⁻ᵏ` on `closedBall 0 (k + 1)`
(`DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`). Subtracting these polynomials makes
the local solutions converge, and on each `ball 0 (m + 1)` the limit is `h m` plus a uniform limit
of holomorphic functions (`TauCeti.exists_differentiableOn_eqOn_add_tsum`).

**Holomorphic gauges.** A unitary connection `d + a` on the trivial line over `ℂⁿ` whose curvature
has no `(0,2)` part has a `bar∂`-closed `(0,1)` part `b = ∑ j, b_j d(conj z_j)`. If a section `α`
satisfies `bar∂_a α = 0`, that is `∂α/∂(conj z_j) + b_j α = 0`, choose `g` with `bar∂ g = b`;
then `exp g • α` is entire (`TauCeti.exists_contDiff_differentiable_exp_smul`). So `α` is an
entire function times the nowhere vanishing factor `exp (-g)`, and its zeros are those of an entire
function, with their multiplicities. In Taubes's analysis of Seiberg–Witten solutions near a
pseudoholomorphic curve, the rescaled limits are such pairs on `ℂ_base × ℂ_normal`, and this
complex gauge is how their zero divisors become holomorphic.

## Main results

* `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_single_eq`: the `bar∂`-Poincaré lemma for
  `(0,1)`-forms on `ℂⁿ`.
* `TauCeti.exists_contDiff_differentiable_exp_smul`: a section annihilated by `bar∂ + b` for a
  `bar∂`-closed `(0,1)`-form `b` is holomorphic in a smooth complex gauge.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 2.3.3 and §2.3 (the `bar∂` equation in polydiscs and in `ℂⁿ`).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Complex Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **The `bar∂`-Poincaré lemma on `ℂⁿ`.** A smooth `bar∂`-closed `(0,1)`-form
`∑ j, f_j d(conj z_j)` on all of `ι → ℂ`, with coefficients in a complex Banach space, is
`bar∂`-exact: some smooth `u` satisfies `∂u/∂(conj z_j) = f_j` for every `j`. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_single_eq {f : ι → (ι → ℂ) → F}
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hclosed : ∀ z i j,
      conjWirtingerDeriv (f j) z (Pi.single i 1) = conjWirtingerDeriv (f i) z (Pi.single j 1)) :
    ∃ u : (ι → ℂ) → F, ContDiff ℝ ∞ u ∧
      ∀ z j, conjWirtingerDeriv u z (Pi.single j 1) = f j z := by
  -- The exhaustion of `ι → ℂ` by the polydiscs `ball 0 (r k)`, `r k = k + 1`.
  set r : ℕ → ℝ := fun k ↦ k + 1
  have hr_pos (k : ℕ) : 0 < r k := by positivity
  have hr_mono : StrictMono r := fun i j hij ↦ by simp only [r]; exact_mod_cast Nat.succ_lt_succ hij
  -- Local solutions `h k`, smooth with `bar∂ (h k) = f` on `ball 0 (r (k + 1))`.
  have hloc (k : ℕ) : ∃ h : (ι → ℂ) → F, ContDiffOn ℝ ∞ h (ball 0 (r (k + 1))) ∧
      ∀ z ∈ ball (0 : ι → ℂ) (r (k + 1)), ∀ j,
        conjWirtingerDeriv h z (Pi.single j 1) = f j z := by
    have hpi : (univ.pi fun i ↦ ball ((0 : ι → ℂ) i) (r (k + 1))) = ball 0 (r (k + 1)) :=
      (ball_pi 0 (hr_pos (k + 1))).symm
    rw [← hpi]
    exact exists_contDiffOn_conjWirtingerDeriv_apply_single_eq_of_polydisc
      (r := fun _ ↦ r (k + 1) + 1) (fun _ ↦ lt_add_one _) (fun j ↦ (hf j).contDiffOn)
      fun z _ ↦ hclosed z
  choose h hh hh_eq using hloc
  have hdiffAt {k : ℕ} {z : ι → ℂ} (hz : z ∈ ball 0 (r (k + 1))) : DifferentiableAt ℝ (h k) z :=
    ((hh k).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  -- Consecutive local solutions differ by a holomorphic function.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (ball 0 (r (k + 1))) := fun z hz ↦ by
    have hz' : z ∈ ball (0 : ι → ℂ) (r (k + 1 + 1)) :=
      ball_subset_ball (hr_mono (k + 1).lt_succ_self).le hz
    refine ((differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero
      ((hdiffAt hz').sub (hdiffAt hz))).2 fun j ↦ ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub (hdiffAt hz') (hdiffAt hz), sub_apply,
      hh_eq (k + 1) z hz' j, hh_eq k z hz j, sub_self]
  -- Polynomial corrections `P k`, approximating the differences within `2⁻ᵏ`.
  have happrox (k : ℕ) : ∃ P : (ι → ℂ) → F, Differentiable ℂ P ∧
      ∀ z ∈ closedBall 0 (r k), ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k :=
    (hdiff k).exists_differentiable_norm_sub_lt_of_pi (hr_mono k.lt_succ_self) (by positivity)
  choose P hP hP_lt using happrox
  -- On `ball 0 (r m)`, the corrected limit is `h m` plus a holomorphic function.
  set u : (ι → ℂ) → F := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z
  have hkey (m : ℕ) : ∃ K : (ι → ℂ) → F, DifferentiableOn ℂ K (ball 0 (r m)) ∧
      EqOn u (h m + K) (ball 0 (r m)) :=
    exists_differentiableOn_eqOn_add_tsum hr_mono.monotone hP
      (fun k ↦ (hdiff k).mono (ball_subset_ball (hr_mono k.lt_succ_self).le)) hP_lt m
  -- Every point lies in some `ball 0 (r m)`, where `u` is `h m` plus a holomorphic function.
  have hglue := contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add (G := u) (U := univ)
    (v := fun j ↦ Pi.single j 1) (f := f) (n := ∞) (by simp) fun z _ ↦ by
      obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
      have hz : z ∈ ball (0 : ι → ℂ) (r m) := by
        rw [mem_ball_zero_iff]; simp only [r]; linarith
      obtain ⟨K, hK, huK⟩ := hkey m
      have hsub : ball (0 : ι → ℂ) (r m) ⊆ ball 0 (r (m + 1)) :=
        ball_subset_ball (hr_mono m.lt_succ_self).le
      exact ⟨ball 0 (r m), isOpen_ball, hz, h m, K, (hh m).mono hsub,
        fun w hw ↦ hh_eq m w (hsub hw), hK.contDiffOn_of_finiteDimensional isOpen_ball, huK⟩
  exact ⟨u, contDiffOn_univ.1 hglue.1, fun z ↦ hglue.2 z trivial⟩

omit [CompleteSpace F] in
/-- **Holomorphic gauge.** Let `b = ∑ j, b_j d(conj z_j)` be a smooth `bar∂`-closed `(0,1)`-form
on `ι → ℂ`, for instance the `(0,1)` part of a connection whose curvature has no `(0,2)` part, and
let `α` be a real-differentiable section with `bar∂ α + b α = 0`, that is
`∂α/∂(conj z_j) + b_j α = 0` for every `j`. Then some smooth `g` with `∂g/∂(conj z_j) = b_j`
makes `exp g • α` entire. -/
theorem exists_contDiff_differentiable_exp_smul {b : ι → (ι → ℂ) → ℂ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (hclosed : ∀ z i j,
      conjWirtingerDeriv (b j) z (Pi.single i 1) = conjWirtingerDeriv (b i) z (Pi.single j 1))
    {α : (ι → ℂ) → F} (hα : Differentiable ℝ α)
    (hαb : ∀ z j, conjWirtingerDeriv α z (Pi.single j 1) + b j z • α z = 0) :
    ∃ g : (ι → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
      (∀ z j, conjWirtingerDeriv g z (Pi.single j 1) = b j z) ∧
      Differentiable ℂ fun z ↦ cexp (g z) • α z := by
  obtain ⟨g, hg, hgb⟩ := exists_contDiff_conjWirtingerDeriv_apply_single_eq hb hclosed
  refine ⟨g, hg, hgb, fun z ↦ ?_⟩
  have hgd : DifferentiableAt ℝ g z := hg.differentiable (by simp) z
  have hed : DifferentiableAt ℝ (fun y ↦ cexp (g y)) z := hgd.cexp
  refine (differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero
    (hed.fun_smul (hα z))).2 fun j ↦ ?_
  -- `\bar∂ (exp g) = exp g • \bar∂ g` by the chain rule through the holomorphic `exp`.
  have hexp : conjWirtingerDeriv (fun y ↦ cexp (g y)) z (Pi.single j 1) = cexp (g z) * b j z := by
    have hcomp := conjWirtingerDeriv_comp (φ := cexp) differentiableAt_exp hgd
    rw [Function.comp_def] at hcomp
    rw [hcomp, ContinuousLinearMap.comp_apply, hgb z j, (hasDerivAt_exp (g z)).hasFDerivAt.fderiv]
    simp [mul_comm]
  rw [conjWirtingerDeriv_smul_apply hed (hα z), hexp, mul_smul, ← smul_add, hαb z j, smul_zero]

end TauCeti
