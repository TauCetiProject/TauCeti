/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Annulus.CyclicAction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Data.ZMod.Induction

/-!
# The exit set of the block of the cyclic action

Let `S_k`, `k ∈ ℤ/N`, be generating functions of a chain of twist maps `F_k` of the strip
`ℝ × [0, 1]`, in the convention `y = -∂₁ S_k(x, X)`, `Y = ∂₂ S_k(x, X)`. Along a configuration
`q : ℤ/N → ℝ` the `k`-th map has the *input momentum* `y_k = -∂₁ S_k(q_k, q_(k+1))` and the
*output momentum* `Y_k = ∂₂ S_k(q_k, q_(k+1))`. The negative gradient flow of the cyclic action
`W(q) = Σ_k S_k(q_k, q_(k+1))` moves the positions with velocities `dq_k/dt = y_k - Y_(k-1)`
(`TauCeti.isMIntegralCurve_mk_comp_neg_mgradient_quotientCyclicAction`), and the compact block of
the generating-function proof of the Poincaré–Birkhoff theorem is cut out by `0 ≤ y_k ≤ 1`. This
file determines how the trajectories of that flow cross the boundary of the block.

Call a factor *positive* when it twists positively, `∂_y X_k > 0`, so that its mixed second
derivative `∂₁∂₂ S_k = -1 / ∂_y X_k` is negative, and *negative* otherwise; the set of positive
indices is `P`, and no two cyclically consecutive factors are positive, as for a chain alternating
between negative twists and a positive shear. A momentum `y_k` is on a *face* at height
`c ∈ {0, 1}` when `y_k = c`. The hypotheses at a face are the pointwise identities of
`TauCeti.deriv_mul_fderiv_fderiv_stripBandGeneratingFunction_apply_zero_one`: the factor maps
the line `y = c` into itself, so `Y_k = c` too, and the second derivatives of `S_k` satisfy
`B_k d²S_k(v, (0, 1)) = -d²S_k(v, (1, 0))` for the derivative `B_k > 0` of the boundary graph.
Along the flow the momentum on the face then moves with velocity

`dy_k/dt = b_k (B_k (Y_(k-1) - c) + (y_(k+1) - c))`,  `b_k = -∂₁∂₂ S_k`,

which points weakly into the block for a positive factor and weakly out of it for a negative one,
strictly unless both neighbouring momenta are on the same face too
(`TauCeti.neg_fderiv_fderiv_stripBandGeneratingFunction_apply_face`). When they are, the velocity
vanishes and the second derivative decides:

`d²y_k/dt² = b_k (B_k / B_(k-1) · dy_(k-1)/dt + dy_(k+1)/dt)`.

For a negative factor whose neighbours move into the block, one of them strictly, the momentum
leaves the block at second order, both forwards and backwards in time.

Let `L` be the set of configurations of the block with the momentum of some *negative* factor on
a face. Combining the two orders along a maximal cyclic run of momenta on one face gives:

* At a point of `L`, every trajectory leaves the block immediately
  (`TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc`). A run of momenta on
  a face with a negative end leaves at first order. Otherwise, the run ends with a positive factor
  `j`, and the negative factor `j - 1` before it leaves at second order. This needs the run not to
  be the full cycle, which would make the configuration a periodic chain on a boundary line of
  the strip, excluded by the boundary twist of a Poincaré–Birkhoff lift.
* At a boundary point of the block outside `L`, all momenta on faces belong to positive factors
  and move strictly into the block: the trajectory is in the interior of the block just after
  (`TauCeti.eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo`), and outside it just
  before (`TauCeti.eventually_nhdsLT_stripGeneratingSource_snd_notMem_Icc`).
* Hence, if no face carries all the momenta, a point of the block leaves it immediately exactly
  when it lies in `L` (`TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc_iff`):
  `L` is the immediate exit set of the block. The further properties of an index pair in Conley's
  theory, such as every exit from the block passing through `L`, are not proved here.
* A critical configuration, at which `Y_(k-1) = y_k` for every `k`, has no momentum on a face
  `c` unless all momenta are on it, provided `Y_k = c` forces `y_k = c`
  (`TauCeti.stripGeneratingSource_snd_ne_of_forall_stripGeneratingTarget_eq`). So a rest point of
  the flow in the block lies in its interior unless all its momenta are on one face, the full-cycle
  case excluded above.

The statements concern solutions of `dq_k/dt = y_k - Y_(k-1)` on the configuration space, near
the time `t₀` of the boundary point; they project to the diagonal quotient, where the cut-off
gradient flow of
`TauCeti.exists_isCompleteVectorField_eventuallyEq_neg_mgradient_quotientCyclicAction` agrees
with the negative gradient flow near the block.

## Main results

* `TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc`: trajectories through
  `L` leave the block immediately.
* `TauCeti.eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo`,
  `TauCeti.eventually_nhdsLT_stripGeneratingSource_snd_notMem_Icc`: trajectories through the rest
  of the boundary enter the interior of the block.
* `TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc_iff`: if no face carries
  all the momenta, `L` is exactly the set of points of the block which leave it immediately.
* `TauCeti.stripGeneratingSource_snd_ne_of_forall_stripGeneratingTarget_eq`: critical
  configurations have no momentum on a face unless all of them are.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

open Filter Set Topology

namespace TauCeti

/-! ### The momenta along a trajectory, near a face -/

section Face

variable {N : ℕ} {P : Set (ZMod N)} {y Y a b : ZMod N → ℝ → ℝ} {Y' B : ZMod N → ℝ}
  {t₀ c ε : ℝ}

/-- The velocity `a_k (y_k - Y_(k-1)) + b_k (y_(k+1) - Y_k)` of the `k`-th input momentum along
the negative gradient flow, where `a_k = -∂₁∂₁ S_k` and `b_k = -∂₁∂₂ S_k`. -/
private def momentumVelocity (y Y a b : ZMod N → ℝ → ℝ) (k : ZMod N) (t : ℝ) : ℝ :=
  a k t * (y k t - Y (k - 1) t) + b k t * (y (k + 1) t - Y k t)

/-- The data at time `t₀` of the input momenta `y` and output momenta `Y` of a trajectory of the
negative gradient flow, near the face at height `c` of the block, which lies on the side
`0 ≤ ε (y - c)` of it. Here `Y'` is the derivative of `Y` at `t₀`, and `B_k` the derivative of
the boundary graph of the `k`-th factor at a momentum on the face. -/
private structure FaceData (y Y a b : ZMod N → ℝ → ℝ) (Y' B : ZMod N → ℝ) (t₀ c ε : ℝ) :
    Prop where
  hasDerivAt : ∀ᶠ t in 𝓝 t₀, ∀ k, HasDerivAt (y k) (momentumVelocity y Y a b k t) t
  continuousAt_left : ∀ k, ContinuousAt (a k) t₀
  continuousAt_right : ∀ k, ContinuousAt (b k) t₀
  hasDerivAt_target : ∀ k, HasDerivAt (Y k) (Y' k) t₀
  ne_zero : ε ≠ 0
  source_side : ∀ k, 0 ≤ ε * (y k t₀ - c)
  target_side : ∀ k, 0 ≤ ε * (Y k t₀ - c)
  target_eq_iff : ∀ k, Y k t₀ = c ↔ y k t₀ = c
  pos : ∀ k, y k t₀ = c → 0 < B k
  left_eq : ∀ k, y k t₀ = c → a k t₀ = -(B k * b k t₀)
  target_deriv : ∀ k, y k t₀ = c → B k * Y' k = momentumVelocity y Y a b k t₀

namespace FaceData

variable (h : FaceData y Y a b Y' B t₀ c ε)
include h

/-- The velocity of a momentum on the face is `b_k (B_k (Y_(k-1) - c) + (y_(k+1) - c))`. -/
private theorem mul_momentumVelocity {k : ZMod N} (hk : y k t₀ = c) :
    ε * momentumVelocity y Y a b k t₀ =
      b k t₀ * (B k * (ε * (Y (k - 1) t₀ - c)) + ε * (y (k + 1) t₀ - c)) := by
  have hY : Y k t₀ = c := (h.target_eq_iff k).2 hk
  simp only [momentumVelocity, h.left_eq k hk, hk, hY]
  ring

private theorem bracket_nonneg {k : ZMod N} (hk : y k t₀ = c) :
    0 ≤ B k * (ε * (Y (k - 1) t₀ - c)) + ε * (y (k + 1) t₀ - c) :=
  add_nonneg (mul_nonneg (h.pos k hk).le (h.target_side _)) (h.source_side _)

private theorem bracket_pos {k : ZMod N} (hk : y k t₀ = c)
    (hne : y (k - 1) t₀ ≠ c ∨ y (k + 1) t₀ ≠ c) :
    0 < B k * (ε * (Y (k - 1) t₀ - c)) + ε * (y (k + 1) t₀ - c) := by
  rcases hne with hne | hne
  · have hY : 0 < ε * (Y (k - 1) t₀ - c) := by
      refine (h.target_side _).lt_of_ne fun h0 ↦ ?_
      rcases mul_eq_zero.1 h0.symm with h1 | h1
      · exact h.ne_zero h1
      · exact hne ((h.target_eq_iff _).1 (sub_eq_zero.1 h1))
    exact add_pos_of_pos_of_nonneg (mul_pos (h.pos k hk) hY) (h.source_side _)
  · have hy : 0 < ε * (y (k + 1) t₀ - c) := by
      refine (h.source_side _).lt_of_ne fun h0 ↦ ?_
      rcases mul_eq_zero.1 h0.symm with h1 | h1
      · exact h.ne_zero h1
      · exact hne (sub_eq_zero.1 h1)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (h.pos k hk).le (h.target_side _)) hy

private theorem momentumVelocity_eq_zero {k : ZMod N} (hl : y (k - 1) t₀ = c)
    (hk : y k t₀ = c) (hr : y (k + 1) t₀ = c) : momentumVelocity y Y a b k t₀ = 0 := by
  simp [momentumVelocity, hk, hr, (h.target_eq_iff k).2 hk, (h.target_eq_iff _).2 hl]

private theorem mul_momentumVelocity_nonneg {k : ZMod N} (hk : y k t₀ = c) (hb : 0 < b k t₀) :
    0 ≤ ε * momentumVelocity y Y a b k t₀ := by
  rw [h.mul_momentumVelocity hk]
  exact mul_nonneg hb.le (h.bracket_nonneg hk)

private theorem mul_momentumVelocity_pos {k : ZMod N} (hk : y k t₀ = c) (hb : 0 < b k t₀)
    (hne : y (k - 1) t₀ ≠ c ∨ y (k + 1) t₀ ≠ c) : 0 < ε * momentumVelocity y Y a b k t₀ := by
  rw [h.mul_momentumVelocity hk]
  exact mul_pos hb (h.bracket_pos hk hne)

private theorem mul_momentumVelocity_neg {k : ZMod N} (hk : y k t₀ = c) (hb : b k t₀ < 0)
    (hne : y (k - 1) t₀ ≠ c ∨ y (k + 1) t₀ ≠ c) : ε * momentumVelocity y Y a b k t₀ < 0 := by
  rw [h.mul_momentumVelocity hk]
  exact mul_neg_of_neg_of_pos hb (h.bracket_pos hk hne)

private theorem hasDerivAt_mul_sub (k : ZMod N) :
    HasDerivAt (fun t ↦ ε * (y k t - c)) (ε * momentumVelocity y Y a b k t₀) t₀ :=
  ((h.hasDerivAt.self_of_nhds k).sub_const c).const_mul ε

/-- A momentum on the face moving out of the block leaves it just after `t₀`. -/
private theorem eventually_nhdsGT_mul_sub_neg {k : ZMod N} (hk : y k t₀ = c)
    (hv : ε * momentumVelocity y Y a b k t₀ < 0) :
    ∀ᶠ t in 𝓝[>] t₀, ε * (y k t - c) < 0 := by
  simpa [hk] using (h.hasDerivAt_mul_sub k).hasDerivWithinAt.eventually_lt_of_neg hv

/-- A momentum on the face moving into the block is inside it just after `t₀`. -/
private theorem eventually_nhdsGT_mul_sub_pos {k : ZMod N} (hk : y k t₀ = c)
    (hv : 0 < ε * momentumVelocity y Y a b k t₀) :
    ∀ᶠ t in 𝓝[>] t₀, 0 < ε * (y k t - c) := by
  simpa [hk] using (h.hasDerivAt_mul_sub k).hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hv

/-- A momentum on the face moving into the block is outside it just before `t₀`. -/
private theorem eventually_nhdsLT_mul_sub_neg {k : ZMod N} (hk : y k t₀ = c)
    (hv : 0 < ε * momentumVelocity y Y a b k t₀) :
    ∀ᶠ t in 𝓝[<] t₀, ε * (y k t - c) < 0 := by
  simpa [hk] using (h.hasDerivAt_mul_sub k).hasDerivWithinAt.eventually_nhdsLT_lt_of_pos hv

/-- **The second derivative of a stationary momentum.** If the momenta `y_(k-1)`, `y_k`,
`y_(k+1)` are all on the face, the velocity of `y_k` vanishes at `t₀` and has derivative
`b_k (B_k Y'_(k-1) + dy_(k+1)/dt)` there, where `B_(k-1) Y'_(k-1) = dy_(k-1)/dt`. -/
private theorem hasDerivAt_mul_momentumVelocity {k : ZMod N} (hl : y (k - 1) t₀ = c)
    (hk : y k t₀ = c) (hr : y (k + 1) t₀ = c) :
    HasDerivAt (fun t ↦ ε * momentumVelocity y Y a b k t)
      (b k t₀ * (B k * (ε * Y' (k - 1)) + ε * momentumVelocity y Y a b (k + 1) t₀)) t₀ := by
  have hYl : Y (k - 1) t₀ = c := (h.target_eq_iff _).2 hl
  have hYk : Y k t₀ = c := (h.target_eq_iff _).2 hk
  have hv := h.momentumVelocity_eq_zero hl hk hr
  -- `Y'_k = 0`, since `B_k Y'_k` is the vanishing velocity of `y_k`
  have hY'k : Y' k = 0 := by
    have := h.target_deriv k hk
    rw [hv] at this
    exact (mul_eq_zero.1 this).resolve_left (h.pos k hk).ne'
  -- each term of the velocity is a continuous coefficient times a difference vanishing at `t₀`
  have h1 := ((h.hasDerivAt.self_of_nhds k).sub (h.hasDerivAt_target (k - 1))).smul_of_eq_zero
    (h.continuousAt_left k) (by simp [hk, hYl])
  have h2 := ((h.hasDerivAt.self_of_nhds (k + 1)).sub (h.hasDerivAt_target k)).smul_of_eq_zero
    (h.continuousAt_right k) (by simp [hr, hYk])
  have hfun : (fun t ↦ ε * momentumVelocity y Y a b k t) = fun t ↦
      ε * ((y k t - Y (k - 1) t) • a k t + (y (k + 1) t - Y k t) • b k t) := by
    funext t
    simp only [momentumVelocity, smul_eq_mul]
    ring
  rw [hfun]
  convert (h1.add h2).const_mul ε using 1
  simp only [hv, hY'k, h.left_eq k hk, smul_eq_mul]
  ring

/-- **Exit at second order.** A momentum of a factor with `b_k < 0` which is on the face together
with both of its neighbours, whose velocities point weakly into the block and one of them strictly,
is outside the block at all times close to `t₀` but `t₀`. -/
private theorem eventually_nhdsNE_mul_sub_neg {k : ZMod N} (hl : y (k - 1) t₀ = c)
    (hk : y k t₀ = c) (hr : y (k + 1) t₀ = c) (hb : b k t₀ < 0)
    (hvl : 0 ≤ ε * momentumVelocity y Y a b (k - 1) t₀)
    (hvr : 0 ≤ ε * momentumVelocity y Y a b (k + 1) t₀)
    (hpos : 0 < ε * momentumVelocity y Y a b (k - 1) t₀ ∨
      0 < ε * momentumVelocity y Y a b (k + 1) t₀) :
    ∀ᶠ t in 𝓝[≠] t₀, ε * (y k t - c) < 0 := by
  have hg : deriv (fun t ↦ ε * (y k t - c)) =ᶠ[𝓝 t₀]
      fun t ↦ ε * momentumVelocity y Y a b k t := by
    filter_upwards [h.hasDerivAt] with t ht
    exact (((ht k).sub_const c).const_mul ε).deriv
  -- `ε Y'_(k-1)` has the sign of the velocity `ε dy_(k-1)/dt = B_(k-1) ε Y'_(k-1)`
  have hBl := h.pos _ hl
  have hz : B (k - 1) * (ε * Y' (k - 1)) = ε * momentumVelocity y Y a b (k - 1) t₀ := by
    rw [← h.target_deriv _ hl]
    ring
  have hzl : 0 ≤ ε * Y' (k - 1) := (mul_nonneg_iff_of_pos_left hBl).1 (hz ▸ hvl)
  have hsum : 0 < B k * (ε * Y' (k - 1)) + ε * momentumVelocity y Y a b (k + 1) t₀ := by
    rcases hpos with hpos | hpos
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (h.pos k hk) ((mul_pos_iff_of_pos_left hBl).1 (hz ▸ hpos))) hvr
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (h.pos k hk).le hzl) hpos
  have hdd : deriv (deriv fun t ↦ ε * (y k t - c)) t₀ < 0 := by
    rw [hg.deriv_eq, (h.hasDerivAt_mul_momentumVelocity hl hk hr).deriv]
    exact mul_neg_of_neg_of_pos hb hsum
  have hd : deriv (fun t ↦ ε * (y k t - c)) t₀ = 0 := by
    rw [hg.eq_of_nhds, h.momentumVelocity_eq_zero hl hk hr, mul_zero]
  simpa [hk] using eventually_gt_of_deriv_deriv_neg hdd hd
    (h.hasDerivAt_mul_sub k).continuousAt

/-- **Trajectories through a negative face leave the block.** If the momentum of a factor
`k₀ ∉ P` with `b_(k₀) < 0` is on the face, the momenta on the face are not all of them, every
negative factor on the face has `b_k < 0` and every positive one `b_k > 0`, and no two
consecutive factors are positive, then just after `t₀` some momentum is outside the block. -/
private theorem eventually_nhdsGT_exists_mul_sub_neg [NeZero N] (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hpos : ∀ k ∈ P, y k t₀ = c → 0 < b k t₀) (hneg : ∀ k ∉ P, y k t₀ = c → b k t₀ < 0)
    (hfull : ∃ j, y j t₀ ≠ c) {k₀ : ZMod N} (hk₀P : k₀ ∉ P) (hk₀ : y k₀ t₀ = c) :
    ∀ᶠ t in 𝓝[>] t₀, ∃ k, ε * (y k t - c) < 0 := by
  -- A negative factor at the end of a run of momenta on the face leaves at first order.
  by_cases hend : ∃ k ∉ P, y k t₀ = c ∧ (y (k - 1) t₀ ≠ c ∨ y (k + 1) t₀ ≠ c)
  · obtain ⟨k, hkP, hk, hne⟩ := hend
    exact (h.eventually_nhdsGT_mul_sub_neg hk (h.mul_momentumVelocity_neg hk (hneg k hkP hk)
      hne)).mono fun t ht ↦ ⟨k, ht⟩
  push Not at hend
  -- Otherwise `y_(k₀ + 1)` is on the face too. Some pair of consecutive momenta on the face is
  -- followed by a momentum off it: the run ends with `j + 1`, and `y_j` is on the face.
  obtain ⟨j, ⟨hj, hj1⟩, hj2⟩ : ∃ j, (y j t₀ = c ∧ y (j + 1) t₀ = c) ∧
      ¬(y (j + 1) t₀ = c ∧ y (j + 1 + 1) t₀ = c) := by
    by_contra! hcon
    obtain ⟨i, hi⟩ := hfull
    have hall : y (k₀ + (i - k₀)) t₀ = c ∧ y (k₀ + (i - k₀) + 1) t₀ = c :=
      ZMod.induction_on (P := fun n ↦ y (k₀ + n) t₀ = c ∧ y (k₀ + n + 1) t₀ = c) (i - k₀)
        (by rw [add_zero]; exact ⟨hk₀, (hend k₀ hk₀P hk₀).2⟩)
        fun n ih ↦ by rw [← add_assoc]; exact hcon _ ih
    rw [add_sub_cancel] at hall
    exact hi hall.1
  replace hj2 : y (j + 1 + 1) t₀ ≠ c := fun h' ↦ hj2 ⟨hj1, h'⟩
  -- The run ends with a positive factor `j + 1`, so `j` is a negative factor inside the run.
  have hj1P : j + 1 ∈ P := by
    by_contra hj1P
    exact hj2 (hend _ hj1P hj1).2
  have hjP : j ∉ P := fun h' ↦ hP _ h' hj1P
  have hj0 := (hend _ hjP hj).1
  -- `y_(j+1)` moves strictly into the block and `y_(j-1)` weakly, so `y_j` leaves at second order.
  have hvr : 0 < ε * momentumVelocity y Y a b (j + 1) t₀ :=
    h.mul_momentumVelocity_pos hj1 (hpos _ hj1P hj1) (Or.inr hj2)
  have hvl : 0 ≤ ε * momentumVelocity y Y a b (j - 1) t₀ := by
    by_cases hP2 : j - 1 ∈ P
    · exact h.mul_momentumVelocity_nonneg hj0 (hpos _ hP2 hj0)
    · obtain ⟨h3, h4⟩ := hend _ hP2 hj0
      rw [h.momentumVelocity_eq_zero h3 hj0 h4, mul_zero]
  have hexit := h.eventually_nhdsNE_mul_sub_neg hj0 hj hj1 (hneg _ hjP hj) hvl hvr.le (Or.inr hvr)
  exact (hexit.filter_mono (nhdsGT_le_nhdsNE t₀)).mono fun t ht ↦ ⟨j, ht⟩

/-- If every momentum on the face belongs to a positive factor, and no two consecutive factors are
positive, then every momentum on the face moves strictly into the block. -/
private theorem mul_momentumVelocity_pos_of_forall_mem (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hpos : ∀ k ∈ P, y k t₀ = c → 0 < b k t₀) (hall : ∀ k, y k t₀ = c → k ∈ P) {k : ZMod N}
    (hk : y k t₀ = c) : 0 < ε * momentumVelocity y Y a b k t₀ :=
  h.mul_momentumVelocity_pos hk (hpos k (hall k hk) hk)
    (Or.inr fun h1 ↦ hP k (hall k hk) (hall _ h1))

end FaceData

end Face

/-! ### Trajectories of the negative gradient flow -/

section Trajectory

variable {N : ℕ} [NeZero N] {S : ZMod N → ℝ × ℝ → ℝ} {γ : ℝ → ZMod N → ℝ} {t₀ : ℝ}
  {P : Set (ZMod N)}

/-- A point of `[0, 1]` lies on the side `0 ≤ (1 - 2c)(x - c)` of each face `c ∈ {0, 1}`. -/
private theorem mul_sub_nonneg_of_mem_Icc {c x : ℝ} (hc : c ∈ ({0, 1} : Set ℝ))
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ (1 - 2 * c) * (x - c) := by
  rcases hc with rfl | rfl <;> simp only [mem_Icc] at hx <;> nlinarith

/-- The velocity `(dγ_k/dt, dγ_(k+1)/dt) = (y_k - Y_(k-1), y_(k+1) - Y_k)` of the `k`-th edge
`(γ_k, γ_(k+1))` of a trajectory of the negative gradient flow. -/
private noncomputable def edgeVelocity (S : ZMod N → ℝ × ℝ → ℝ) (γ : ℝ → ZMod N → ℝ) (t : ℝ)
    (k : ZMod N) : ℝ × ℝ :=
  ((stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 -
      (stripGeneratingTarget (S (k - 1)) (γ t (k - 1), γ t k)).2,
    (stripGeneratingSource (S (k + 1)) (γ t (k + 1), γ t (k + 1 + 1))).2 -
      (stripGeneratingTarget (S k) (γ t k, γ t (k + 1))).2)

omit [NeZero N] in
private theorem hasDerivAt_edge {t : ℝ} (ht : HasDerivAt γ (fun i ↦
      (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
        (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (k : ZMod N) : HasDerivAt (fun s ↦ (γ s k, γ s (k + 1))) (edgeVelocity S γ t k) t := by
  have h2 := hasDerivAt_pi.1 ht (k + 1)
  simp only [add_sub_cancel_right] at h2
  exact (hasDerivAt_pi.1 ht k).prodMk h2

omit [NeZero N] in
/-- The second derivative `d²S_k(edge velocity, w)` splits along the two components
`y_k - Y_(k-1)` and `y_(k+1) - Y_k` of the edge velocity. -/
private theorem fderiv_fderiv_edgeVelocity_apply (t : ℝ) (k : ZMod N) (w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (edgeVelocity S γ t k) w =
      ((stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 -
          (stripGeneratingTarget (S (k - 1)) (γ t (k - 1), γ t k)).2) *
        fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (1, 0) w +
      ((stripGeneratingSource (S (k + 1)) (γ t (k + 1), γ t (k + 1 + 1))).2 -
          (stripGeneratingTarget (S k) (γ t k, γ t (k + 1))).2) *
        fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (0, 1) w := by
  rw [edgeVelocity, (fderiv ℝ (fderiv ℝ (S k)) _).apply_mk_eq_smul_add_smul]
  simp only [add_apply, smul_apply, smul_eq_mul]

omit [NeZero N] in
/-- Along a trajectory, the second partial derivative `∂_w S_k` at the edge `(γ_k, γ_(k+1))`
moves with velocity `d²S_k(edge velocity, w)`. -/
private theorem hasDerivAt_fderiv_apply {t : ℝ} {k : ZMod N} (ht : HasDerivAt γ (fun i ↦
      (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
        (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hd : DifferentiableAt ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1))) (w : ℝ × ℝ) :
    HasDerivAt (fun s ↦ fderiv ℝ (S k) (γ s k, γ s (k + 1)) w)
      (fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (edgeVelocity S γ t k) w) t := by
  have h := hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_edge ht k)
  simpa only [Function.comp_apply, map_zero, add_zero] using h.clm_apply (hasDerivAt_const t w)

omit [NeZero N] in
/-- Along a trajectory, the input momentum `y_k` moves with velocity
`a_k (y_k - Y_(k-1)) + b_k (y_(k+1) - Y_k)`, where `a_k = -∂₁∂₁ S_k` and `b_k = -∂₁∂₂ S_k`. -/
private theorem hasDerivAt_stripGeneratingSource_snd {t : ℝ} {k : ZMod N}
    (ht : HasDerivAt γ (fun i ↦
      (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
        (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hd : DifferentiableAt ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1))) :
    HasDerivAt (fun s ↦ (stripGeneratingSource (S k) (γ s k, γ s (k + 1))).2)
      (momentumVelocity (fun k t ↦ (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2)
        (fun k t ↦ (stripGeneratingTarget (S k) (γ t k, γ t (k + 1))).2)
        (fun k t ↦ -fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (1, 0) (1, 0))
        (fun k t ↦ -fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (0, 1) (1, 0)) k t) t := by
  simp only [stripGeneratingSource_snd]
  refine (hasDerivAt_fderiv_apply ht hd (1, 0)).neg.congr_deriv ?_
  rw [fderiv_fderiv_edgeVelocity_apply]
  simp only [momentumVelocity, stripGeneratingSource_snd, stripGeneratingTarget_snd, sub_add_cancel]
  ring

/-- The momenta along a trajectory of the negative gradient flow of the cyclic action satisfy the
face data at each face `c ∈ {0, 1}` of the block, with the side `ε = 1 - 2c`. -/
private theorem exists_faceData
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    {c : ℝ} (hc : c ∈ ({0, 1} : Set ℝ)) :
    ∃ Y' B : ZMod N → ℝ, FaceData
      (fun k t ↦ (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2)
      (fun k t ↦ (stripGeneratingTarget (S k) (γ t k, γ t (k + 1))).2)
      (fun k t ↦ -fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (1, 0) (1, 0))
      (fun k t ↦ -fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) (0, 1) (1, 0))
      Y' B t₀ c (1 - 2 * c) := by
  choose! B hB hBface using hface
  have hγ₀ := hγ.self_of_nhds
  have hcont (k : ZMod N) : ContinuousAt (fun t ↦ (γ t k, γ t (k + 1))) t₀ :=
    (hasDerivAt_edge hγ₀ k).continuousAt
  -- near `t₀` the generating functions are `C²` along the trajectory
  have hdiff : ∀ᶠ t in 𝓝 t₀, ∀ k, DifferentiableAt ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1)) := by
    refine eventually_all.2 fun k ↦ (hcont k).eventually ?_
    filter_upwards [(hS k).eventually (by simp)] with p hp
    exact (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcont2 (k : ZMod N) : ContinuousAt
      (fun t ↦ fderiv ℝ (fderiv ℝ (S k)) (γ t k, γ t (k + 1))) t₀ :=
    (((hS k).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
      |>.continuousAt).comp (x := t₀) (hcont k)
  refine ⟨fun k ↦ fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (edgeVelocity S γ t₀ k)
      (0, 1), B,
    { hasDerivAt := ?_, continuousAt_left := ?_, continuousAt_right := ?_,
      hasDerivAt_target := ?_, ne_zero := ?_,
      source_side := fun k ↦ mul_sub_nonneg_of_mem_Icc hc (hsrc k),
      target_side := fun k ↦ mul_sub_nonneg_of_mem_Icc hc (htgt k),
      target_eq_iff := fun k ↦ hiff k c hc, pos := fun k hk ↦ hB k (hk ▸ hc),
      left_eq := ?_, target_deriv := ?_ }⟩
  · filter_upwards [hγ, hdiff] with t ht hd k
    exact hasDerivAt_stripGeneratingSource_snd ht (hd k)
  · exact fun k ↦ (((hcont2 k).clm_apply continuousAt_const).clm_apply continuousAt_const).neg
  · exact fun k ↦ (((hcont2 k).clm_apply continuousAt_const).clm_apply continuousAt_const).neg
  · intro k
    simpa only [stripGeneratingTarget_snd] using
      hasDerivAt_fderiv_apply hγ₀ (hdiff.self_of_nhds k) (0, 1)
  · rcases hc with rfl | rfl <;> norm_num
  · -- `a_k = -∂₁∂₁ S_k = B_k ∂₁∂₂ S_k = -B_k b_k` by the face identity and symmetry
    intro k hk
    have := hBface k (hk ▸ hc) (1, 0)
    rw [← (hS k).isSymmSndFDerivAt (by simp) (1, 0) (0, 1)]
    linarith
  · intro k hk
    rw [hBface k (hk ▸ hc), fderiv_fderiv_edgeVelocity_apply]
    simp only [momentumVelocity, stripGeneratingSource_snd, stripGeneratingTarget_snd,
      sub_add_cancel]
    ring

/-- In the setting of `TauCeti.eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo`, a
momentum on a face `c ∈ {0, 1}` at `t₀` lies strictly on the block side `0 < (1 - 2c)(y_k - c)` of
the face just after `t₀`. -/
private theorem eventually_nhdsGT_mul_stripGeneratingSource_snd_sub_pos
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    (hpos : ∀ k ∈ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0) < 0)
    (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hall : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      k ∈ P)
    {k : ZMod N} (hk : (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ)) :
    ∀ᶠ t in 𝓝[>] t₀, 0 < (1 - 2 * (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2) *
      ((stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 -
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2) := by
  obtain ⟨Y', B, h⟩ := exists_faceData hS hγ hsrc htgt hiff hface hk
  exact h.eventually_nhdsGT_mul_sub_pos rfl (h.mul_momentumVelocity_pos_of_forall_mem hP
    (fun j hjP hj ↦ neg_pos.2 (hpos j hjP (hj ▸ hk))) (fun j hj ↦ hall j (hj ▸ hk)) rfl)

end Trajectory

end TauCeti

public section

namespace TauCeti

/-! ### The exit set of the block -/

variable {N : ℕ} [NeZero N] {S : ZMod N → ℝ × ℝ → ℝ} {γ : ℝ → ZMod N → ℝ} {t₀ : ℝ}
  {P : Set (ZMod N)}

/-- **Trajectories through the exit set leave the block immediately.** Let `γ` solve
`dγ_i/dt = y_i - Y_(i-1)` near `t₀`, for `C²` generating functions `S_k`, where
`y_k = -∂₁ S_k(γ_k, γ_(k+1))` and `Y_k = ∂₂ S_k(γ_k, γ_(k+1))`. Suppose that at `t₀` all these
momenta lie in `[0, 1]`, that `Y_k` is on a face `c ∈ {0, 1}` exactly when `y_k` is, and that at
each momentum `y_k` on a face the second derivatives of `S_k` satisfy
`B d²S_k(v, (0, 1)) = -d²S_k(v, (1, 0))` for some `B > 0`, with `∂₁∂₂ S_k < 0` for the positive
factors `k ∈ P` and `∂₁∂₂ S_k > 0` for the others. If no two consecutive factors are positive, no
face carries all the momenta, and the momentum of some negative factor is on a face, then just
after `t₀` some momentum `y_k` lies outside `[0, 1]`. -/
theorem eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    (hpos : ∀ k ∈ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0) < 0)
    (hneg : ∀ k ∉ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      0 < fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0))
    (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hfull : ∀ c ∈ ({0, 1} : Set ℝ),
      ∃ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ≠ c)
    (hk : ∃ k ∉ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ)) :
    ∀ᶠ t in 𝓝[>] t₀, ∃ k, (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 ∉ Icc (0 : ℝ) 1 := by
  obtain ⟨k₀, hk₀P, hk₀⟩ := hk
  obtain ⟨Y', B, h⟩ := exists_faceData hS hγ hsrc htgt hiff hface hk₀
  filter_upwards [h.eventually_nhdsGT_exists_mul_sub_neg hP
    (fun k hkP hk ↦ neg_pos.2 (hpos k hkP (hk ▸ hk₀)))
    (fun k hkP hk ↦ neg_lt_zero.2 (hneg k hkP (hk ▸ hk₀))) (hfull _ hk₀) hk₀P rfl]
    with t ⟨k, hk⟩
  exact ⟨k, fun hmem ↦ (mul_sub_nonneg_of_mem_Icc hk₀ hmem).not_gt hk⟩

/-- **Trajectories through the rest of the boundary enter the block.** In the setting of
`TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc`, if every momentum on a
face at `t₀` belongs to a positive factor, then just after `t₀` all momenta `y_k` lie in the open
interval `(0, 1)`. -/
theorem eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    (hpos : ∀ k ∈ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0) < 0)
    (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hall : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      k ∈ P) :
    ∀ᶠ t in 𝓝[>] t₀, ∀ k, (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 ∈ Ioo (0 : ℝ) 1 := by
  refine eventually_all.2 fun k ↦ ?_
  have hcont := (hasDerivAt_stripGeneratingSource_snd hγ.self_of_nhds
    (((hS k).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)).continuousAt
  by_cases hk : (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ)
  · -- a momentum on a face moves into the block, and stays within distance `1` of the face
    filter_upwards [eventually_nhdsGT_mul_stripGeneratingSource_snd_sub_pos hS hγ hsrc htgt hiff
      hface hpos hP hall hk, nhdsWithin_le_nhds (hcont.eventually
        (Ioo_mem_nhds (sub_one_lt _) (lt_add_one _)))] with t h1 h2
    rcases hk with h0 | h0 <;> rw [h0] at h1 h2 <;> exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · -- a momentum inside `(0, 1)` stays there
    exact nhdsWithin_le_nhds (hcont.eventually (isOpen_Ioo.mem_nhds
      ⟨(hsrc k).1.lt_of_ne fun h0 ↦ hk (Or.inl h0.symm),
        (hsrc k).2.lt_of_ne fun h1 ↦ hk (Or.inr h1)⟩))

/-- **Trajectories through the rest of the boundary come from outside the block.** In the
setting of `TauCeti.eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo`, a momentum on a
face at `t₀` lies outside `[0, 1]` just before `t₀`. -/
theorem eventually_nhdsLT_stripGeneratingSource_snd_notMem_Icc
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    (hpos : ∀ k ∈ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0) < 0)
    (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hall : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      k ∈ P)
    {k : ZMod N} (hk : (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ)) :
    ∀ᶠ t in 𝓝[<] t₀, (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 ∉ Icc (0 : ℝ) 1 := by
  obtain ⟨Y', B, h⟩ := exists_faceData hS hγ hsrc htgt hiff hface hk
  have hv := h.mul_momentumVelocity_pos_of_forall_mem hP
    (fun j hjP hj ↦ neg_pos.2 (hpos j hjP (hj ▸ hk))) (fun j hj ↦ hall j (hj ▸ hk)) rfl
  filter_upwards [h.eventually_nhdsLT_mul_sub_neg rfl hv] with t ht hmem
  exact (mul_sub_nonneg_of_mem_Icc hk hmem).not_gt ht

/-- **The exit set of the block.** In the setting of
`TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc`, a trajectory leaves the
block immediately after `t₀` exactly when at `t₀` the momentum of some negative factor is on a
face. -/
theorem eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc_iff
    (hS : ∀ k, ContDiffAt ℝ 2 (S k) (γ t₀ k, γ t₀ (k + 1)))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t)
    (hsrc : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (htgt : ∀ k, (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ Icc (0 : ℝ) 1)
    (hiff : ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
      (stripGeneratingTarget (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c ↔
        (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 = c)
    (hface : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (0, 1) =
        -fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) v (1, 0))
    (hpos : ∀ k ∈ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0) < 0)
    (hneg : ∀ k ∉ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      0 < fderiv ℝ (fderiv ℝ (S k)) (γ t₀ k, γ t₀ (k + 1)) (0, 1) (1, 0))
    (hP : ∀ k ∈ P, k + 1 ∉ P)
    (hfull : ∀ c ∈ ({0, 1} : Set ℝ),
      ∃ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ≠ c) :
    (∀ᶠ t in 𝓝[>] t₀, ∃ k, (stripGeneratingSource (S k) (γ t k, γ t (k + 1))).2 ∉ Icc (0 : ℝ) 1) ↔
      ∃ k ∉ P, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) := by
  refine ⟨fun hexit ↦ ?_, eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc hS hγ hsrc
    htgt hiff hface hpos hneg hP hfull⟩
  by_contra hno
  have hall : ∀ k, (stripGeneratingSource (S k) (γ t₀ k, γ t₀ (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      k ∈ P := fun k hk ↦ by_contra fun hkP ↦ hno ⟨k, hkP, hk⟩
  obtain ⟨t, ⟨k, hk⟩, ht⟩ := (hexit.and (eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo
    hS hγ hsrc htgt hiff hface hpos hP hall)).exists
  exact hk (Ioo_subset_Icc_self (ht k))

/-- **Critical configurations are off the faces.** If at every vertex of a configuration `q` the
target point of the `(i-1)`-th map is the source point of the `i`-th map, as at a critical point
of the cyclic action (`TauCeti.fderiv_cyclicAction_eq_zero_iff`), and each output momentum `Y_k`
equal to `c` forces the input momentum `y_k` to equal `c`, then no input momentum equals `c` unless
all of them do. -/
theorem stripGeneratingSource_snd_ne_of_forall_stripGeneratingTarget_eq {q : ZMod N → ℝ} {c : ℝ}
    (hcrit : ∀ i, stripGeneratingTarget (S (i - 1)) (q (i - 1), q i) =
      stripGeneratingSource (S i) (q i, q (i + 1)))
    (htgt : ∀ k, (stripGeneratingTarget (S k) (q k, q (k + 1))).2 = c →
      (stripGeneratingSource (S k) (q k, q (k + 1))).2 = c)
    (hfull : ∃ k, (stripGeneratingSource (S k) (q k, q (k + 1))).2 ≠ c) (k : ZMod N) :
    (stripGeneratingSource (S k) (q k, q (k + 1))).2 ≠ c := by
  obtain ⟨j, hj⟩ := hfull
  -- `y_i = c` forces `Y_(i-1) = c`, hence `y_(i-1) = c`: the face propagates backwards
  have hstep (i : ZMod N) (hi : (stripGeneratingSource (S i) (q i, q (i + 1))).2 = c) :
      (stripGeneratingSource (S (i - 1)) (q (i - 1), q (i - 1 + 1))).2 = c := by
    refine htgt (i - 1) ?_
    rw [sub_add_cancel, ← hi, hcrit i]
  -- so a momentum off the face propagates forwards, from `y_j` to every `y_k`
  have key := ZMod.induction_on
    (P := fun n ↦ (stripGeneratingSource (S (j + n)) (q (j + n), q (j + n + 1))).2 ≠ c) (k - j)
    (by rwa [add_zero])
    fun n ih h ↦ ih (by simpa only [← add_assoc, add_sub_cancel_right] using hstep _ h)
  simpa only [add_sub_cancel] using key

end TauCeti
