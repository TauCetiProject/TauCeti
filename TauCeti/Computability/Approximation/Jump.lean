/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Limit
public import TauCeti.Computability.SingleOracle.Relative
import TauCeti.Computability.SingleOracle.Limit

/-!
# Approximating computations in the jump

The jump of `Z` has a uniformly `Z`-computable approximation: at stage `s` ask whether the
bounded diagonal computation succeeds. Its bits converge to the jump's characteristic
function. Running a bounded computation against these approximate bits and returning zero
on failure gives a total approximation to any total function computable in `Z'`.

Together with the computation of a limit in the jump, this proves both directions of the
relativized Limit Lemma, for total natural-valued functions and for characteristic functions.
No stabilization modulus is supplied or assumed computable.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Limit Lemma III.3.3.
-/

public section

open Filter Encodable TauCeti.Oracle.Single TauCeti.Approximation

namespace Set

/-- The bounded diagonal-halting approximation to `Z'`: one for a successful run at fuel `s`,
zero otherwise. It is computable in `Z`, not necessarily computable without `Z`. -/
noncomputable def jumpApproximation (Z : Set ℕ) (s e : ℕ) : ℕ :=
  ((Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e).map fun _ => 1).getD 0

/-- Unfolding the bounded diagonal-halting approximation. -/
theorem jumpApproximation_def (Z : Set ℕ) (s e : ℕ) :
    Z.jumpApproximation s e =
      ((Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e).map fun _ => 1).getD 0 :=
  (rfl)

/-- The diagonal-halting guess is one exactly when the bounded run succeeds. -/
@[simp]
theorem jumpApproximation_eq_one_iff (Z : Set ℕ) (s e : ℕ) :
    Z.jumpApproximation s e = 1 ↔
      (Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e).isSome := by
  simp only [jumpApproximation]
  cases Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e <;> simp

/-- The diagonal-halting guess is zero exactly when the bounded run fails. -/
@[simp]
theorem jumpApproximation_eq_zero_iff (Z : Set ℕ) (s e : ℕ) :
    Z.jumpApproximation s e = 0 ↔
      Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e = none := by
  simp only [jumpApproximation]
  cases Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e <;> simp

/-- The jump guesses are computable in `Z`, uniformly in the stage and argument. -/
theorem computableIn₂_jumpApproximation (Z : Set ℕ) :
    ComputableIn₂ {Z.oracle} Z.jumpApproximation := by
  have hσ : ComputableIn₂ {Z.oracle} (fun (_ : ℕ) z => Z.indicator 1 z) :=
    Z.computableIn_indicator.comp ComputableIn.snd
  have hargs : ComputableIn {Z.oracle} (fun p : ℕ × ℕ =>
      (0, p.1, Denumerable.ofNat Code p.2, p.2)) :=
    ComputableIn.const 0 |>.pair (ComputableIn.fst.pair
      (((Primrec.ofNat Code).computableIn.comp ComputableIn.snd).pair ComputableIn.snd))
  have hr := (Code.computableIn_evaln hσ).comp hargs
  have hb : Primrec (fun o : Option Code.Halt => (o.map fun _ => 1).getD 0) :=
    Primrec.option_getD.comp (Primrec.option_map Primrec.id (Primrec.const 1).to₂)
      (Primrec.const 0)
  have hanswers : Code.setAnswers Z = fun z => some (Z.indicator 1 z) :=
    funext (Code.setAnswers_apply Z)
  exact RecursiveIn.of_eq (hb.computableIn.comp hr) fun p => by
    simp [jumpApproximation, hanswers]

/-- The bounded diagonal-halting guesses converge pointwise to the actual jump. -/
theorem converges_jumpApproximation (Z : Set ℕ) :
    Converges Z.jumpApproximation (Z.jump.indicator 1) := by
  classical
  apply converges_iff_eventually.2
  intro e
  by_cases he : e ∈ Z.jump
  · obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 (mem_jump.1 he)
    obtain ⟨k, d, hd, -⟩ := Code.exists_evaln_eq_some_of_mem_eval (σ := Code.setAnswers Z)
      (by simp) hy
    exact (eventually_ge_atTop k).mono fun s hs => by
      simp [jumpApproximation, Code.evaln_mono hs hd, he]
  · apply Eventually.of_forall
    intro s
    have hn : Code.evaln (Code.setAnswers Z) s (Denumerable.ofNat Code e) e = none := by
      apply Option.eq_none_iff_forall_ne_some.2
      intro d hd
      exact he (mem_jump.2 (Part.dom_iff_mem.2
        ⟨d.output, Code.evaln_sound hd (by simp)⟩))
    simp [jumpApproximation, hn, he]

end Set

namespace TauCeti.Approximation

/-- **Limit Lemma, approximating a computation in the jump.** Every total natural-valued
function computable in `Z'` is the pointwise eventually constant limit of a sequence of total
functions computable uniformly in `Z`. -/
theorem exists_computableIn_converges_of_computableIn_jump {Z : Set ℕ} {g : ℕ → ℕ}
    (hg : ComputableIn {Z.jump.oracle} g) :
    ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f g := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (RecursiveIn.iff_nat.1 hg)
  let f : ℕ → ℕ → ℕ := fun s x =>
    ((Code.evaln (fun z => some (Z.jumpApproximation s z)) s c x).map Code.Halt.output).getD 0
  refine ⟨f, ?_, ?_⟩
  · have hargs : ComputableIn {Z.oracle} (fun p : ℕ × ℕ => (p.1, p.1, c, p.2)) :=
      ComputableIn.fst.pair (ComputableIn.fst.pair
        ((ComputableIn.const c).pair ComputableIn.snd))
    have hr := (Code.computableIn_evaln Z.computableIn₂_jumpApproximation).comp hargs
    have hout : Primrec (fun o : Option Code.Halt => (o.map Code.Halt.output).getD 0) :=
      Primrec.option_getD.comp (Primrec.option_map Primrec.id
        (Code.Halt.primrec_output.comp Primrec.snd).to₂) (Primrec.const 0)
    exact hout.computableIn.comp hr
  · apply converges_iff_eventually.2
    intro x
    have hx : g x ∈ Code.eval Z.jump.oracle c x := by rw [hc]; simp
    have hσ : Converges (fun s z => some (Z.jumpApproximation s z))
        (Code.setAnswers Z.jump) := converges_iff_eventually.2 fun z =>
          (converges_iff_eventually.1 Z.converges_jumpApproximation z).mono
            fun _ hs => by simp [Code.setAnswers_apply, hs]
    obtain ⟨d, hd, he⟩ := Code.exists_eventually_evaln_eq_some_of_mem_eval
      (t := fun s => s) (by simp) hσ tendsto_id hx
    exact he.mono fun s hs => by simp [f, hs, hd]

/-- **The relativized Limit Lemma.** A total function is computable in `Z'` exactly when it
has a uniformly `Z`-computable pointwise eventually constant approximation. -/
theorem computableIn_jump_iff_exists_converges {Z : Set ℕ} {g : ℕ → ℕ} :
    ComputableIn {Z.jump.oracle} g ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f g :=
  ⟨exists_computableIn_converges_of_computableIn_jump,
    fun ⟨_, hf, h⟩ => h.computableIn_jump hf⟩

/-- **The relativized Limit Lemma for sets.** Reduction to `Z'` is equivalent to having a
uniformly `Z`-computable approximation to the characteristic function. -/
theorem turingReducible_jump_iff_exists_converges {Z A : Set ℕ} :
    TuringReducible A.oracle Z.jump.oracle ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f (A.indicator 1) := by
  rw [A.turingReducible_iff_computableIn_indicator, computableIn_jump_iff_exists_converges]

end TauCeti.Approximation
