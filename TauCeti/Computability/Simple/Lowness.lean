/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Low
public import TauCeti.Computability.Jump.Low
public import TauCeti.Computability.Approximation.Limit

/-!
# Lowness of the finite-injury simple set

The convergent diagonal stage computations in the construction of `TauCeti.lowSimpleSet`
stabilize, including their outputs and uses. Their convergence bits therefore approximate the
characteristic function of its actual Turing jump. Finite-prefix stabilization identifies the
stable runs with computations in the limit oracle; in particular, a transient computation cannot
supply a false positive after the runs have stabilized.

The Limit Lemma then proves that the constructed set is low. Since it is simple, its c.e.
degree is strictly between the computable degree and the halting degree, in Mathlib's quotient
of partial functions.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.1.1
  and Limit Lemma III.3.3.
-/

public section

open Filter TauCeti.Enumeration TauCeti.RestrainedSimple

namespace TauCeti

namespace LowSimple

open Oracle.Single.Code

/-- The computable guess for membership of `e` in the jump at stage `s`: one if the diagonal
stage computation converges, and zero otherwise. Zero use is not mistaken for divergence. -/
def jumpApproximation (s e : ℕ) : ℕ :=
  if (diagRun (stage diagUse s) s e).isSome then 1 else 0

/-- The jump approximation tests convergence, not the use of the computation. -/
@[simp]
theorem jumpApproximation_eq_one_iff {s e : ℕ} :
    jumpApproximation s e = 1 ↔ (diagRun (stage diagUse s) s e).isSome := by
  cases h : diagRun (stage diagUse s) s e <;> simp [jumpApproximation, h]

/-- A zero guess means that the diagonal stage computation failed. -/
@[simp]
theorem jumpApproximation_eq_zero_iff {s e : ℕ} :
    jumpApproximation s e = 0 ↔ diagRun (stage diagUse s) s e = none := by
  simp [jumpApproximation]

/-- The convergence bits are primitive recursive uniformly in the stage and the input. -/
theorem primrec₂_jumpApproximation : Primrec₂ jumpApproximation := by
  have hr : Primrec fun p : ℕ × ℕ => diagRun (stage diagUse p.1) p.1 p.2 :=
    (primrec_diagRun.comp (((primrec_stage primrec_diagUse).comp Primrec.fst).pair
      (Primrec.fst.pair Primrec.snd))).of_eq fun p => by simp
  exact (Primrec.cond (Primrec.option_isSome.comp hr) (Primrec.const 1)
    (Primrec.const 0)).of_eq fun p => by
      cases h : diagRun (stage diagUse p.1) p.1 p.2 <;> simp [jumpApproximation, h]

/-- After stabilization, convergence of the diagonal stage computation is exactly membership
in the jump of the limit set. -/
theorem eventually_isSome_diagRun_iff_mem_jump (e : ℕ) :
    ∀ᶠ s in atTop, (diagRun (stage diagUse s) s e).isSome ↔ e ∈ lowSimpleSet.jump := by
  classical
  obtain ⟨o, ho⟩ := exists_eventually_diagRun_eq e
  have hlim : o.isSome ↔ e ∈ lowSimpleSet.jump := by
    constructor
    · intro h
      obtain ⟨d, rfl⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨s₀, hs₀⟩ := finite_prefix_stabilizes (monotone_stage diagUse) d.use
      rw [← lowSimpleSet_eq_stageLimit] at hs₀
      obtain ⟨s, hs, hrun⟩ := ((eventually_ge_atTop s₀).and ho).exists
      rw [Set.mem_jump]
      refine Part.dom_iff_mem.2 ⟨d.output, evaln_sound (by simpa [diagRun_def] using hrun) ?_⟩
      intro z hz y hy
      have hz' : z ∈ stage diagUse s ↔ z ∈ lowSimpleSet := hs₀ s hs z hz
      simpa only [Set.oracle_apply, Part.mem_some_iff, Set.indicator_apply,
        Finset.mem_coe, hz', Pi.one_apply, Option.some.injEq] using hy.symm
    · intro h
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 (Set.mem_jump.1 h)
      obtain ⟨k, d, hd, -⟩ := exists_evaln_eq_some_of_mem_eval
        (σ := setAnswers lowSimpleSet) (by simp) hy
      obtain ⟨s₀, hs₀⟩ := finite_prefix_stabilizes (monotone_stage diagUse) d.use
      rw [← lowSimpleSet_eq_stageLimit] at hs₀
      obtain ⟨s, hsk, hss₀, hrun⟩ :=
        ((eventually_ge_atTop k).and ((eventually_ge_atTop s₀).and ho)).exists
      have hstage : diagRun (stage diagUse s) s e = some d := by
        rw [diagRun_def]
        refine evaln_eq_some_of_eqOn (evaln_mono hsk hd) fun z hz => ?_
        have hz' : z ∈ stage diagUse s ↔ z ∈ lowSimpleSet := hs₀ s hss₀ z hz
        simp [Set.indicator_apply, hz']
      rw [← hrun, hstage]
      rfl
  exact ho.mono fun s hs => by rw [hs]; exact hlim

/-- The computable convergence bits converge pointwise to the characteristic function of the
jump of the constructed set. No computable stabilization bound is asserted. -/
theorem converges_jumpApproximation :
    Approximation.Converges jumpApproximation (lowSimpleSet.jump.indicator 1) := by
  classical
  rw [Approximation.converges_iff_eventually]
  intro e
  filter_upwards [eventually_isSome_diagRun_iff_mem_jump e] with s hs
  simp only [jumpApproximation, Set.indicator_apply, Pi.one_apply]
  simp only [hs]

end LowSimple

/-- Soare's finite-injury simple set is low. -/
theorem low_lowSimpleSet : lowSimpleSet.Low :=
  Set.low_iff_jump_turingReducible.2
    (LowSimple.converges_jumpApproximation.turingReducible_jump_empty
      LowSimple.primrec₂_jumpApproximation.to_comp)

/-- The constructed c.e. degree lies strictly between the computable and halting degrees. -/
theorem degree_lowSimpleSet_mem_Ioo :
    toAntisymmetrization TuringReducible lowSimpleSet.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) := by
  refine ⟨?_, low_lowSimpleSet.degree_lt_jump_empty⟩
  rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
  exact ⟨Set.empty_turingReducible _, fun h =>
    simple_lowSimpleSet.not_computablePred ((Set.turingReducible_empty_iff _).1 h)⟩

/-- There is an ordinary partial computable program whose domain is simple and low. -/
theorem exists_simple_low_code :
    ∃ c : Nat.Partrec.Code, {x | (c.eval x).Dom}.Simple ∧ {x | (c.eval x).Dom}.Low := by
  obtain ⟨c, hc⟩ := rePred_iff_exists_code.1 rePred_mem_lowSimpleSet
  have hset : {x | (c.eval x).Dom} = lowSimpleSet := Set.ext fun x => (hc x).symm
  refine ⟨c, ?_⟩
  rw [hset]
  exact ⟨simple_lowSimpleSet, low_lowSimpleSet⟩

end TauCeti
