/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
import Mathlib.Order.PartialSups
import Mathlib.Topology.Order.IsLUB
import TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple
import TauCeti.Analysis.PDE.Harnack.Convergence
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# Perron's method: the Perron solution is harmonic

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space `E`, and let
`g : E → ℝ` be boundary data, bounded above on `frontier Ω`. The **Perron family** of `g` consists
of the functions `v`, continuous on `closure Ω` and subharmonic on `Ω`, with `v ≤ g` on
`frontier Ω`. Its pointwise supremum is the **Perron solution**

`u x = sup {v x | v in the Perron family}`.

This file proves Perron's theorem: if the Perron family is nonempty (for instance, if `g` is
bounded on `frontier Ω`), then `u` is harmonic in `Ω`, for any bounded open `Ω`, with no
regularity of `frontier Ω` and no continuity of `g`. Whether `u` attains the boundary values `g`
is a separate question, decided at each boundary point by the existence of a barrier.

## The argument

By the comparison principle every member of the Perron family is bounded by an upper bound `M`
of `g` on `frontier Ω`. The family is closed under pointwise maxima, and under **harmonic
lifting** in a ball `B` with `closure B ⊆ Ω`: replacing `v` inside `B` by the solution of the
Dirichlet problem on `B` with boundary values `v` gives a member of the family that is harmonic in
`B` and lies above `v`.

Fix a ball `B` centred at `c`. Choose members `v n` of the family with `v n c → u c`, replace them
by their running maxima, and lift each in `B`. The lifts increase, so by Harnack's convergence
theorem they converge in `B` to a harmonic function `W ≤ u` with `W c = u c`. If `W z < u z` at
some `z ∈ B`, a member `v` of the family with `W z < v z` can be added to the running maxima;
the resulting harmonic limit `W' ≥ W` agrees with `W` at the centre, so by the strong maximum
principle `W' = W` on `B`, contradicting `W' z ≥ v z > W z`. Hence `u = W` is harmonic in `B`.

## Main declarations

* `TauCeti.perronFamily`: the Perron family of subharmonic functions below the boundary data.
* `TauCeti.perronFamily_nonempty`: the Perron family is nonempty when the boundary data is
  bounded below.
* `TauCeti.sup_mem_perronFamily`: the Perron family is closed under pointwise maxima.
* `TauCeti.perronSolution`: the Perron solution, the pointwise supremum of the Perron family.
* `TauCeti.le_perronSolution`, `TauCeti.perronSolution_le`: the Perron solution lies above every
  member of the Perron family and below every upper bound of the boundary data.
* `TauCeti.perronSolution_le_of_forall_le`: the Perron solution at `x` is at most every common
  upper bound of the values at `x` of the members of a nonempty Perron family.
* `TauCeti.harmonicOnNhd_perronSolution`: **Perron's theorem**, the Perron solution of a
  nonempty Perron family is harmonic in `Ω`.

## References

* O. Perron, *Eine neue Behandlung der ersten Randwertaufgabe für Δu = 0*, Math. Z. 18 (1923).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8, Theorem 2.12.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {g v w : E → ℝ} {x c : E} {r M : ℝ}

/-! ### Harmonic lifting in a ball -/

open Classical in
/-- The harmonic lifting of `v` in `ball c r`: inside the ball, the solution of the Dirichlet
problem with boundary values `v` on `sphere c r`; outside the ball, `v` itself. -/
private def ballLift (c : E) (r : ℝ) (v : E → ℝ) : E → ℝ :=
  if hv : ContinuousOn v (sphere c r) then
    (ball c r).piecewise (exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere hv).choose
      v
  else v

open Classical in
private lemma ballLift_spec (hv : ContinuousOn v (sphere c r)) :
    ∃ H : E → ℝ, HarmonicOnNhd H (ball c r) ∧ ContinuousOn H (closedBall c r) ∧
      EqOn H v (sphere c r) ∧ ballLift c r v = (ball c r).piecewise H v := by
  obtain ⟨h₁, h₂, h₃⟩ :=
    (exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere hv).choose_spec
  exact ⟨_, h₁, h₂, h₃, by rw [ballLift, dite_eq_left hv]⟩

open Classical in
private lemma harmonicOnNhd_ballLift (hv : ContinuousOn v (sphere c r)) :
    HarmonicOnNhd (ballLift c r v) (ball c r) := by
  obtain ⟨H, hH, -, -, hlift⟩ := ballLift_spec hv
  intro x hx
  refine (harmonicAt_congr_nhds ?_).2 (hH x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [hlift]
  exact piecewise_eqOn (ball c r) H v hy

open Classical in
private lemma ballLift_eqOn_compl : EqOn (ballLift c r v) v (ball c r)ᶜ := by
  by_cases hv : ContinuousOn v (sphere c r)
  · obtain ⟨H, -, -, -, hlift⟩ := ballLift_spec hv
    intro x hx
    rw [hlift]
    exact piecewise_eqOn_compl (ball c r) H v hx
  · intro x _
    rw [ballLift, dite_eq_right hv]

/-- The harmonic lifting of a function continuous on a set `s ⊇ closedBall c r` is continuous on
`s`. -/
private lemma continuousOn_ballLift {s : Set E} (hr : 0 < r) (hv : ContinuousOn v s)
    (hs : closedBall c r ⊆ s) : ContinuousOn (ballLift c r v) s := by
  classical
  obtain ⟨H, -, hHc, hHv, hlift⟩ := ballLift_spec (hv.mono (sphere_subset_closedBall.trans hs))
  rw [hlift]
  refine ContinuousOn.piecewise (fun x hx ↦ ?_) (hHc.mono ?_) (hv.mono inter_subset_left)
  · rw [frontier_ball c hr.ne'] at hx
    exact hHv hx.2
  · rw [closure_ball c hr.ne']
    exact inter_subset_right

variable [MeasurableSpace E] [BorelSpace E]

/-- The **Perron family** of the boundary data `g` on `Ω`: the functions that are subharmonic on
`Ω`, continuous on `closure Ω`, and at most `g` on `frontier Ω`. -/
def perronFamily (Ω : Set E) (g : E → ℝ) : Set (E → ℝ) :=
  {v | SubharmonicOn v Ω ∧ ContinuousOn v (closure Ω) ∧ ∀ x ∈ frontier Ω, v x ≤ g x}

@[simp]
theorem mem_perronFamily : v ∈ perronFamily Ω g ↔
    SubharmonicOn v Ω ∧ ContinuousOn v (closure Ω) ∧ ∀ x ∈ frontier Ω, v x ≤ g x :=
  Iff.rfl

/-- If the boundary data is bounded below on `frontier Ω`, the Perron family is nonempty: it
contains the constant function at any lower bound of `g` on `frontier Ω`. -/
theorem perronFamily_nonempty (hg : BddBelow (g '' frontier Ω)) :
    (perronFamily Ω g).Nonempty := by
  obtain ⟨m, hm⟩ := hg
  exact ⟨fun _ ↦ m, (harmonicOnNhd_const m).subharmonicOn, continuousOn_const,
    fun x hx ↦ hm (mem_image_of_mem g hx)⟩

/-- The **Perron solution** of the Dirichlet problem on `Ω` with boundary data `g`: the pointwise
supremum of the Perron family `TauCeti.perronFamily Ω g`. It is harmonic in `Ω` when `Ω` is
bounded and open, `g` is bounded above on `frontier Ω` and the Perron family is nonempty
(`TauCeti.harmonicOnNhd_perronSolution`); the family is nonempty when `g` is also bounded below
on `frontier Ω` (`TauCeti.perronFamily_nonempty`).

If the family is empty, the supremum is the junk value `sSup ∅ = 0`; no result here is stated
for that case. -/
def perronSolution (Ω : Set E) (g : E → ℝ) (x : E) : ℝ :=
  sSup ((fun v ↦ v x) '' perronFamily Ω g)

theorem perronSolution_def :
    perronSolution Ω g x = sSup ((fun v ↦ v x) '' perronFamily Ω g) :=
  (rfl)

/-- The Perron family is closed under pointwise maxima. -/
theorem sup_mem_perronFamily (hΩ : IsOpen Ω) (hv : v ∈ perronFamily Ω g)
    (hw : w ∈ perronFamily Ω g) : v ⊔ w ∈ perronFamily Ω g :=
  ⟨hv.1.sup hw.1 hΩ, hv.2.1.sup hw.2.1, fun x hx ↦ sup_le (hv.2.2 x hx) (hw.2.2 x hx)⟩

/-- If the Perron family is nonempty, the Perron solution at `x` is at most any common upper bound
of the values at `x` of the members of the family. -/
theorem perronSolution_le_of_forall_le (hne : (perronFamily Ω g).Nonempty)
    (h : ∀ v ∈ perronFamily Ω g, v x ≤ M) : perronSolution Ω g x ≤ M :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

section Nontrivial

variable [Nontrivial E]

/-- Every member of the Perron family is bounded on `closure Ω` by an upper bound `M` of the
boundary data. -/
private lemma le_of_mem_perronFamily (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hM : ∀ x ∈ frontier Ω, g x ≤ M) (hv : v ∈ perronFamily Ω g) (hx : x ∈ closure Ω) :
    v x ≤ M :=
  hv.1.le_of_le_frontier hΩ hb hv.2.1 (harmonicOnNhd_const M) continuousOn_const
    (fun y hy ↦ (hv.2.2 y hy).trans (hM y hy)) x hx

/-- The Perron solution lies above every member of the Perron family on `closure Ω`. -/
theorem le_perronSolution (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : BddAbove (g '' frontier Ω)) (hv : v ∈ perronFamily Ω g) (hx : x ∈ closure Ω) :
    v x ≤ perronSolution Ω g x := by
  obtain ⟨M, hM⟩ := hg
  exact le_csSup ⟨M, forall_mem_image.2 fun w hw ↦
    le_of_mem_perronFamily hΩ hb (fun y hy ↦ hM (mem_image_of_mem g hy)) hw hx⟩
    (mem_image_of_mem _ hv)

/-- If the Perron family is nonempty, the Perron solution is bounded on `closure Ω` by every
upper bound of the boundary data. -/
theorem perronSolution_le (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : (perronFamily Ω g).Nonempty) (hM : ∀ x ∈ frontier Ω, g x ≤ M) (hx : x ∈ closure Ω) :
    perronSolution Ω g x ≤ M :=
  perronSolution_le_of_forall_le hne fun _ hv ↦ le_of_mem_perronFamily hΩ hb hM hv hx

end Nontrivial

/-- The harmonic lifting is monotone. -/
private lemma ballLift_mono [Nontrivial E] (hv : ContinuousOn v (sphere c r))
    (hw : ContinuousOn w (sphere c r)) (hvw : v ≤ w) : ballLift c r v ≤ ballLift c r w := by
  classical
  intro x
  by_cases hx : x ∈ ball c r
  · obtain ⟨H, hH, hHc, hHv, hlift⟩ := ballLift_spec hv
    obtain ⟨H', hH', hH'c, hH'w, hlift'⟩ := ballLift_spec hw
    rw [hlift, hlift', piecewise_eq_of_mem _ _ _ hx, piecewise_eq_of_mem _ _ _ hx]
    exact hH.subharmonicOn.le_of_le_sphere hHc hH' hH'c
      (fun y hy ↦ by rw [hHv hy, hH'w hy]; exact hvw y) x (ball_subset_closedBall hx)
  · rw [ballLift_eqOn_compl hx, ballLift_eqOn_compl hx]
    exact hvw x

/-- The harmonic lifting of a member of the Perron family lies above it. -/
private lemma le_ballLift [Nontrivial E] (hrΩ : closedBall c r ⊆ Ω) (hv : v ∈ perronFamily Ω g) :
    v ≤ ballLift c r v := by
  classical
  intro x
  by_cases hx : x ∈ ball c r
  · have hvc : ContinuousOn v (closedBall c r) := hv.2.1.mono (hrΩ.trans subset_closure)
    obtain ⟨H, hH, hHc, hHv, hlift⟩ := ballLift_spec (hvc.mono sphere_subset_closedBall)
    rw [hlift, piecewise_eq_of_mem _ _ _ hx]
    exact (hv.1.mono (ball_subset_closedBall.trans hrΩ)).le_of_le_sphere hvc hH hHc
      (fun y hy ↦ (hHv hy).ge) x (ball_subset_closedBall hx)
  · exact (ballLift_eqOn_compl hx).ge

/-- The harmonic lifting of a member of the Perron family is a member of the Perron family. -/
private lemma ballLift_mem_perronFamily [Nontrivial E] (hΩ : IsOpen Ω) (hr : 0 < r)
    (hrΩ : closedBall c r ⊆ Ω) (hv : v ∈ perronFamily Ω g) :
    ballLift c r v ∈ perronFamily Ω g := by
  have hvΩ : ContinuousOn v Ω := hv.1.continuousOn
  have hle := le_ballLift hrΩ hv
  have hsph : ContinuousOn v (sphere c r) := hvΩ.mono (sphere_subset_closedBall.trans hrΩ)
  refine ⟨⟨continuousOn_ballLift hr hvΩ hrΩ, fun x hx ↦ ?_⟩,
    continuousOn_ballLift hr hv.2.1 (hrΩ.trans subset_closure), fun x hx ↦ ?_⟩
  · by_cases hxb : x ∈ ball c r
    · exact (harmonicOnNhd_ballLift hsph).subharmonicOn.frequently_le_setAverage x hxb
    -- Outside the ball the lifting agrees with `v` at `x` and lies above `v` everywhere.
    exact hv.1.frequently_le_setAverage_of_le hΩ (continuousOn_ballLift hr hvΩ hrΩ)
      (fun y _ ↦ hle y) hx (ballLift_eqOn_compl hxb)
  · -- The ball lies inside `Ω`, so it misses the frontier of `Ω`.
    have hxb : x ∉ ball c r := fun hxb ↦
      (hΩ.frontier_eq ▸ hx).2 (hrΩ (ball_subset_closedBall hxb))
    exact (ballLift_eqOn_compl hxb).trans_le (hv.2.2 x hx)

/-! ### Perron's theorem -/

section Perron

variable [Nontrivial E]

/-- Lifting a monotone sequence of members of the Perron family in a ball whose closure lies in
`Ω` gives a monotone sequence of harmonic functions in the ball, bounded above; its supremum is
harmonic in the ball. -/
private lemma harmonicOnNhd_iSup_ballLift (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hM : ∀ x ∈ frontier Ω, g x ≤ M) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω)
    {w : ℕ → E → ℝ} (hw : ∀ n, w n ∈ perronFamily Ω g) (hmono : Monotone w) :
    HarmonicOnNhd (fun x ↦ ⨆ n, ballLift c r (w n) x) (ball c r) ∧
      ∀ x ∈ ball c r, BddAbove (range fun n ↦ ballLift c r (w n) x) := by
  have hbdd : ∀ x ∈ ball c r, BddAbove (range fun n ↦ ballLift c r (w n) x) := fun x hx ↦
    ⟨M, forall_mem_range.2 fun n ↦ le_of_mem_perronFamily hΩ hb hM
      (ballLift_mem_perronFamily hΩ hr hrΩ (hw n))
      (subset_closure (hrΩ (ball_subset_closedBall hx)))⟩
  have hsph : ∀ n, ContinuousOn (w n) (sphere c r) := fun n ↦
    (hw n).2.1.mono (sphere_subset_closedBall.trans (hrΩ.trans subset_closure))
  exact ⟨harmonicOnNhd_iSup_of_monotone isOpen_ball (convex_ball c r).isPreconnected
    (fun n ↦ harmonicOnNhd_ballLift (hsph n))
    (fun x _ m n hmn ↦ ballLift_mono (hsph m) (hsph n) (hmono hmn) x) (mem_ball_self hr)
    (hbdd c (mem_ball_self hr)), hbdd⟩

/-- On a ball whose closure lies in `Ω`, the Perron solution agrees with a harmonic function. -/
private lemma exists_harmonicOnNhd_eqOn_perronSolution (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hg : BddAbove (g '' frontier Ω))
    (hne : (perronFamily Ω g).Nonempty) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω) :
    ∃ W, HarmonicOnNhd W (ball c r) ∧ EqOn (perronSolution Ω g) W (ball c r) := by
  obtain ⟨M, hM⟩ := hg
  have hM' : ∀ x ∈ frontier Ω, g x ≤ M := fun x hx ↦ hM (mem_image_of_mem g hx)
  have hc : c ∈ ball c r := mem_ball_self hr
  have hball : ∀ x ∈ ball c r, x ∈ closure Ω := fun x hx ↦
    subset_closure (hrΩ (ball_subset_closedBall hx))
  have hsph : ∀ v ∈ perronFamily Ω g, ContinuousOn v (sphere c r) := fun v hv ↦
    hv.2.1.mono (sphere_subset_closedBall.trans (hrΩ.trans subset_closure))
  have hle : ∀ v ∈ perronFamily Ω g, ∀ x ∈ ball c r, v x ≤ perronSolution Ω g x :=
    fun v hv x hx ↦ le_perronSolution hΩ hb ⟨M, hM⟩ hv (hball x hx)
  -- Members `v n` of the Perron family whose values at `c` tend to the Perron solution there,
  -- and their running maxima `partialSups v n`, again members of the family.
  obtain ⟨s, -, hs, hsS⟩ := exists_seq_tendsto_sSup (hne.image fun v ↦ v c)
    ⟨M, forall_mem_image.2 fun v hv ↦
      (le_of_mem_perronFamily hΩ hb hM' hv (hball c hc) : v c ≤ M)⟩
  choose v hv hvc using hsS
  have hw : ∀ n, partialSups v n ∈ perronFamily Ω g := fun n ↦ by
    rw [partialSups_apply]
    exact Finset.sup'_induction _ _ (fun a ha b hb ↦ sup_mem_perronFamily hΩ ha hb)
      fun i _ ↦ hv i
  obtain ⟨hW, hWbdd⟩ :=
    harmonicOnNhd_iSup_ballLift hΩ hb hM' hr hrΩ hw (partialSups v).monotone
  -- `W`, the limit of the lifts of the running maxima, lies below the Perron solution on the ball
  -- and agrees with it at `c`.
  set W := fun x ↦ ⨆ n, ballLift c r (partialSups v n) x
  have hWu : ∀ x ∈ ball c r, W x ≤ perronSolution Ω g x := fun x hx ↦
    ciSup_le fun n ↦ hle _ (ballLift_mem_perronFamily hΩ hr hrΩ (hw n)) x hx
  have hWc : W c = perronSolution Ω g c := by
    refine le_antisymm (hWu c hc) (le_of_tendsto' hs fun n ↦ ?_)
    rw [← hvc n]
    exact (le_partialSups v n c).trans
      ((le_ballLift hrΩ (hw n) c).trans (le_ciSup (hWbdd c hc) n))
  refine ⟨W, hW, fun z hz ↦ ?_⟩
  by_contra hzne
  -- Otherwise some member `v'` of the Perron family has `W z < v' z`.
  obtain ⟨_, ⟨v', hv', rfl⟩, hv'z⟩ :=
    exists_lt_of_lt_csSup (hne.image _) (lt_of_le_of_ne (hWu z hz) (Ne.symm hzne))
  have hw' : ∀ n, partialSups v n ⊔ v' ∈ perronFamily Ω g := fun n ↦
    sup_mem_perronFamily hΩ (hw n) hv'
  obtain ⟨hW', hW'bdd⟩ := harmonicOnNhd_iSup_ballLift hΩ hb hM' hr hrΩ hw'
    fun m n hmn ↦ sup_le_sup_right ((partialSups v).monotone hmn) v'
  set W' := fun x ↦ ⨆ n, ballLift c r (partialSups v n ⊔ v') x
  have hWW' : ∀ x ∈ ball c r, W x ≤ W' x := fun x hx ↦
    ciSup_mono (hW'bdd x hx) fun n ↦
      ballLift_mono (hsph _ (hw n)) (hsph _ (hw' n)) (fun _ ↦ le_sup_left) x
  have hW'c : W' c ≤ perronSolution Ω g c :=
    ciSup_le fun n ↦ hle _ (ballLift_mem_perronFamily hΩ hr hrΩ (hw' n)) c hc
  -- The harmonic function `W - W' ≤ 0` vanishes at the centre, so it vanishes on the ball by the
  -- strong maximum principle; but `W' z ≥ v' z > W z`.
  have hmax : IsMaxOn (W - W') (ball c r) c := fun x hx ↦ by
    have := hWW' x hx
    simp only [mem_ofPred_eq, Pi.sub_apply]
    linarith [hWW' c hc]
  have heq := eqOn_const_of_harmonicOnNhd_of_isMaxOn_of_isOpen isOpen_ball hc
    (convex_ball c r).isPreconnected (hW.sub hW') hmax hz
  have hv'W' : v' z ≤ W' z := (le_sup_right.trans (le_ballLift hrΩ (hw' 0) z)).trans
    (le_ciSup (hW'bdd z hz) 0)
  simp only [Function.const_apply, Pi.sub_apply] at heq
  linarith [hWW' c hc]

end Perron

/-- **Perron's theorem.** Let `Ω` be a bounded open set, let `g` be bounded above on
`frontier Ω`, and suppose the Perron family of `g` is nonempty. Then the Perron solution
`TauCeti.perronSolution Ω g` is harmonic in `Ω`.

In Perron's setting of bounded boundary data the family is nonempty by
`TauCeti.perronFamily_nonempty`. -/
theorem harmonicOnNhd_perronSolution (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : BddAbove (g '' frontier Ω)) (hne : (perronFamily Ω g).Nonempty) :
    HarmonicOnNhd (perronSolution Ω g) Ω := by
  intro y hy
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space every function is constant.
    have hconst : perronSolution Ω g = fun _ ↦ perronSolution Ω g y :=
      funext fun z ↦ congrArg _ (Subsingleton.elim z y)
    rw [hconst]
    exact harmonicAt_const _
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hy)
  obtain ⟨W, hW, heq⟩ := exists_harmonicOnNhd_eqOn_perronSolution hΩ hb hg hne hr hrΩ
  exact (harmonicAt_congr_nhds (eventually_of_mem (ball_mem_nhds y hr) heq)).2
    (hW y (mem_ball_self hr))

end TauCeti
