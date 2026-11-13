/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Basic
public import TauCeti.Computability.Jump.Low
import TauCeti.Computability.Approximation.Limit
import TauCeti.Computability.SingleOracle.Probe

/-!
# Sacks splitting with low halves

The halves of Sacks's splitting are low when both input stage sequences have computable binary
codes and the target stages increase to a noncomputable limit. Thus every c.e. set is the disjoint
union of two low c.e. sets, neither of which computes a prescribed noncomputable c.e. target.
No infinitude assumption is needed on the set being split.

The proof follows the agreement-length test of Soare [S, pp.125–126]. The probe for a diagonal
computation returns the target's limiting bit at zero and diverges at positive inputs. Its
agreement length eventually equals the characteristic function of the half's jump: finite
injury excludes transient successes when the diagonal computation diverges. The Limit Lemma
then bounds the jump by the halting set.

The limiting target bit is a fixed parameter in this existence argument. No procedure computing
it uniformly from a c.e. index is asserted.

## Main results

* `TauCeti.SacksSplitting.low_splitHalf`: both constructed halves are low.
* `TauCeti.SacksSplitting.exists_split_low_not_turingReducible`: Sacks's splitting theorem
  with low halves.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.3.2,
  pp.124–126.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority

namespace TauCeti.SacksSplitting

variable {B C : ℕ → Finset ℕ}
  (hB : Computable fun s => Finset.equivBitIndices.symm (B s)) (hCm : Monotone C)
  (hC : Computable fun s => Finset.equivBitIndices.symm (C s))
  (hnc : ¬ComputablePred (· ∈ stageLimit C))
include hB hCm hC hnc

private theorem eventually_agreementLength_diagonalProbe_eq_jump (b : Bool) (e : ℕ) :
    ∀ᶠ s in atTop,
      Oracle.Single.Code.agreementLength (Oracle.Single.Code.setAnswers (halfStage B C b s)) s
        (Oracle.Single.Code.diagonalProbe ((stageLimit C).indicator 1 0) e)
        ((C s : Set ℕ).indicator 1) = (splitHalf B C b).jump.indicator 1 e := by
  classical
  let p := Oracle.Single.Code.diagonalProbe ((stageLimit C).indicator 1 0) e
  let k := Nat.bit b (Encodable.encode p)
  have hI := finite_injurySet hB hCm hC hnc k
  have hr : ∀ᶠ s in atTop, ∃ r, restraint B C k s = some r ∧
      Oracle.Single.Code.agreementRestraint
        (Oracle.Single.Code.setAnswers (halfStage B C b s)) s p
        ((C s : Set ℕ).indicator 1) ≤ r := by
    refine Eventually.of_forall fun s => ⟨_, restraint_def k s, ?_⟩
    simpa [k, Denumerable.ofNat_encode] using (agreementRestraint_stage (B := B) (C := C) s k).ge
  simp only [k, Nat.bodd_bit] at hI
  by_cases he : e ∈ (splitHalf B C b).jump
  · have hbelow : ∀ x < 1, (stageLimit C).indicator 1 x ∈
        Oracle.Single.Code.eval (stageLimit (halfStage B C b)).oracle p x := by
      intro x hx
      have hx0 : x = 0 := by omega
      subst x
      rw [← splitHalf_def]
      exact Oracle.Single.Code.mem_eval_diagonalProbe.2 ⟨rfl, Set.mem_jump.1 he, rfl⟩
    have hne : (stageLimit C).indicator 1 1 ∉
        Oracle.Single.Code.eval (stageLimit (halfStage B C b)).oracle p 1 := by
      simp [p]
    have h := Oracle.Single.Code.eventually_agreementLength_eq_of_first_disagreement
      (monotone_halfStage B C b) hCm hr hI hbelow hne
    simpa [p, he] using h
  · have hne : (stageLimit C).indicator 1 0 ∉
        Oracle.Single.Code.eval (stageLimit (halfStage B C b)).oracle p 0 := by
      intro h
      apply he
      rw [splitHalf_def]
      exact Set.mem_jump.2 (Oracle.Single.Code.mem_eval_diagonalProbe.1 h).2.1
    have h := Oracle.Single.Code.eventually_agreementLength_eq_of_first_disagreement
      (monotone_halfStage B C b) hCm hr hI (n := 0) (by simp) hne
    simpa [p, he] using h

/-- Both halves of Sacks's splitting are low when the target has computable monotone stages
and a noncomputable limit. The stages being split need only have computable binary codes. -/
theorem low_splitHalf (b : Bool) : (splitHalf B C b).Low := by
  let v : ℕ := (stageLimit C).indicator 1 0
  let f := fun s e => Oracle.Single.Code.agreementLength
    (Oracle.Single.Code.setAnswers (halfStage B C b s)) s
    (Oracle.Single.Code.diagonalProbe v e) ((C s : Set ℕ).indicator 1)
  have hf : Computable₂ f := by
    have hargs : Computable fun q : ℕ × ℕ =>
        ((Finset.equivBitIndices.symm (halfStage B C b q.1),
          Finset.equivBitIndices.symm (C q.1)), q.1,
          Oracle.Single.Code.diagonalProbe v q.2) :=
      (((computable_halfStage hB hC b).comp Computable.fst).pair
        (hC.comp Computable.fst)).pair
        (Computable.fst.pair (Oracle.Single.Code.primrec₂_diagonalProbe.to_comp.comp
          (Computable.const v) Computable.snd))
    exact (Oracle.Single.Code.primrec_agreementLength_equivBitIndices.to_comp.comp hargs).of_eq
      fun q => by simp only [Equiv.apply_symm_apply]; rfl
  have hlim : Approximation.Converges f ((splitHalf B C b).jump.indicator 1) :=
    Approximation.converges_iff_eventually.2
      (eventually_agreementLength_diagonalProbe_eq_jump hB hCm hC hnc b)
  exact Set.low_iff_jump_turingReducible.2 (hlim.turingReducible_jump_empty hf)

omit hB hCm hC hnc

/-- **Sacks's splitting theorem with low halves** [S, VII.3.2]: every c.e. set `B` is the union
of two disjoint low c.e. sets, neither of which computes a prescribed noncomputable c.e. set `C`.
The set `B` may be empty or finite. -/
theorem exists_split_low_not_turingReducible {B C : Set ℕ} (hB : REPred (· ∈ B))
    (hC : REPred (· ∈ C)) (hnc : ¬ComputablePred (· ∈ C)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = B ∧
      A₀.Low ∧ A₁.Low ∧ ¬TuringReducible C.oracle A₀.oracle ∧
      ¬TuringReducible C.oracle A₁.oracle := by
  obtain ⟨bs, -, -, hbs, hBlim⟩ := rePred_iff_exists_stages.1 hB
  obtain ⟨cs, hcm, -, hcs, hClim⟩ := rePred_iff_exists_stages.1 hC
  simp only [Set.ofPred_mem_eq] at hBlim hClim
  rw [← hClim] at hnc ⊢
  rw [← hBlim]
  exact ⟨_, _, rePred_mem_splitHalf hbs hcs false, rePred_mem_splitHalf hbs hcs true,
    disjoint_splitHalf _ _, splitHalf_false_union_splitHalf_true _ _,
    low_splitHalf hbs hcm hcs hnc false, low_splitHalf hbs hcm hcs hnc true,
    not_turingReducible_splitHalf hbs hcm hcs hnc false,
    not_turingReducible_splitHalf hbs hcm hcs hnc true⟩

end TauCeti.SacksSplitting
