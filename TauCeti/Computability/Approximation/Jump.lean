/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Limit
public import TauCeti.Computability.Hierarchy.Basic
public import TauCeti.Computability.SingleOracle.Relative
import TauCeti.Computability.Hierarchy.Post
import TauCeti.Computability.SingleOracle.Limit

/-!
# Approximating computations in the jump

The jump of `Z` has a uniformly `Z`-computable approximation: at stage `s` ask whether the
bounded diagonal computation succeeds. Its bits converge to the jump's characteristic
function. Running a bounded computation against these approximate bits and returning zero
on failure gives a total approximation to any total function computable in `Z'`.

Together with the computation of a limit in the jump, this proves both directions of the
relativized Limit Lemma, for total natural-valued functions and for characteristic functions,
and, via relativized Post's theorem, the equivalence between `Δ⁰₂(Z)` predicates and sets and
pointwise limits of uniformly `Z`-computable sequences. No stabilization modulus is supplied
or assumed computable.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Limit Lemma III.3.3
  and Theorem IV.2.1.
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

/-- **The Limit Lemma, unrelativized.** A total function is computable in the halting set `∅'`
exactly when it is the pointwise limit of a uniformly computable sequence. -/
theorem computableIn_jump_empty_iff_exists_converges {g : ℕ → ℕ} :
    ComputableIn {(∅ : Set ℕ).jump.oracle} g ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f g := by
  rw [computableIn_jump_iff_exists_converges]
  exact exists_congr fun _ => and_congr (Set.oracle_empty ▸ computableIn₂_const_iff) Iff.rfl

/-- **The Limit Lemma for sets, unrelativized.** A set is Turing reducible to the halting set
`∅'` exactly when its characteristic function is the pointwise limit of a uniformly computable
sequence. -/
theorem turingReducible_jump_empty_iff_exists_converges {A : Set ℕ} :
    TuringReducible A.oracle (∅ : Set ℕ).jump.oracle ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f (A.indicator 1) := by
  rw [turingReducible_jump_iff_exists_converges]
  exact exists_congr fun _ => and_congr (Set.oracle_empty ▸ computableIn₂_const_iff) Iff.rfl

end TauCeti.Approximation

namespace TauCeti.ArithmeticalHierarchy

/-- **The relativized Limit Lemma, `Δ⁰₂` form for sets.** A set of natural numbers is `Δ⁰₂`
relative to `Z` if and only if its characteristic function is the pointwise limit of a sequence
of total functions computable uniformly in `Z`. -/
theorem isDelta_two_mem_iff_exists_converges {Z A : Set ℕ} :
    IsDelta Z 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f (A.indicator 1) := by
  simpa using
    (isDelta_succ_mem_iff_turingReducible_iterate_jump (Z := Z) (n := 1) (C := A)).trans
      turingReducible_jump_iff_exists_converges

/-- **The Limit Lemma, `Δ⁰₂` form for sets, unrelativized.** A set of natural numbers is `Δ⁰₂`
if and only if its characteristic function is the pointwise limit of a uniformly computable
sequence. -/
theorem isDelta_two_empty_mem_iff_exists_converges {A : Set ℕ} :
    IsDelta ∅ 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f (A.indicator 1) := by
  simpa using
    (isDelta_succ_mem_iff_turingReducible_iterate_jump (Z := ∅) (n := 1) (C := A)).trans
      turingReducible_jump_empty_iff_exists_converges

/-- **The relativized Limit Lemma, `Δ⁰₂` form.** A predicate on a primitive-codable type is
`Δ⁰₂` relative to `Z` if and only if it has a uniformly `Z`-computable Boolean approximation
converging pointwise to a total deciding function. -/
theorem isDelta_two_iff_exists_converges {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta Z 2 p ↔
      ∃ f : ℕ → α → Bool, ComputableIn₂ {Z.oracle} f ∧
        ∃ g : α → Bool, Converges f g ∧ ∀ x, g x = true ↔ p x := by
  constructor
  · intro hp
    obtain ⟨g, hg, hgeq⟩ := (isDelta_succ_iff_exists_computableIn (n := 1)).1 hp
    have hg' : ComputableIn {Z.jump.oracle} g := by simpa using hg
    unfold ComputableIn RecursiveIn at hg'
    obtain ⟨c, hc⟩ := Code.exists_code.1 hg'
    let f : ℕ → α → Bool := fun s x =>
      ((Code.evaln (fun z => some (Z.jumpApproximation s z)) s c (encode x)).map
        Code.Halt.output).getD 0 == 1
    refine ⟨f, ?_, g, ?_, hgeq⟩
    · have hargs : ComputableIn {Z.oracle} (fun q : ℕ × α => (q.1, q.1, c, encode q.2)) :=
        ComputableIn.fst.pair (ComputableIn.fst.pair
          ((ComputableIn.const c).pair (Primrec.encode.computableIn.comp ComputableIn.snd)))
      have hr := (Code.computableIn_evaln Z.computableIn₂_jumpApproximation).comp hargs
      have hout : Primrec (fun o : Option Code.Halt =>
          ((o.map Code.Halt.output).getD 0 == 1)) :=
        (Primrec.beq.comp Primrec.id (Primrec.const 1)).comp <|
          Primrec.option_getD.comp (Primrec.option_map Primrec.id
            (Code.Halt.primrec_output.comp Primrec.snd).to₂) (Primrec.const 0)
      exact hout.computableIn.comp hr
    · apply converges_iff_eventually.2
      intro x
      have hx : encode (g x) ∈ Code.eval Z.jump.oracle c (encode x) := by
        rw [hc]
        simp [encodek]
      have hσ : Converges (fun s z => some (Z.jumpApproximation s z))
          (Code.setAnswers Z.jump) := converges_iff_eventually.2 fun z =>
            (converges_iff_eventually.1 Z.converges_jumpApproximation z).mono
              fun _ hs => by simp [Code.setAnswers_apply, hs]
      obtain ⟨d, hd, he⟩ := Code.exists_eventually_evaln_eq_some_of_mem_eval
        (t := fun s => s) (by simp) hσ tendsto_id hx
      refine he.mono fun s hs => ?_
      cases hgx : g x <;> simp [f, hs, hd, hgx]
  · rintro ⟨f, hf, g, hfg, hgeq⟩
    have hval (b₀ : Bool) : IsSigma Z 2 (fun x => g x = b₀) := by
      have hle : IsPi Z 0 (fun q : (α × ℕ) × ℕ => q.1.2 ≤ q.2) :=
        isPi_zero_iff.2 (isSigma_zero_iff.2 ⟨fun q => decide (q.1.2 ≤ q.2),
          Primrec.nat_le.decide.computableIn.comp
            ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd),
          fun _ => decide_eq_true_iff⟩)
      have hfb : IsSigma Z 0 (fun q : (α × ℕ) × ℕ => f q.2 q.1.1 = b₀) :=
        isSigma_zero_iff.2 ⟨fun q => f q.2 q.1.1 == b₀,
          (Primrec.beq.comp Primrec.id (Primrec.const b₀)).computableIn.comp
            (hf.comp (ComputableIn.snd.pair (ComputableIn.fst.comp ComputableIn.fst))),
          fun _ => beq_iff_eq⟩
      have hall : IsPi Z 1 (fun a : α × ℕ => ∀ s, a.2 ≤ s → f s a.1 = b₀) :=
        isPi_succ_iff.2 ⟨_, IsSigma.imp hle hfb, fun _ => Iff.rfl⟩
      refine (isSigma_succ_iff.2 ⟨_, hall, fun _ => Iff.rfl⟩).of_eq fun x => ?_
      constructor
      · rintro ⟨s₀, hs₀⟩
        obtain ⟨s, hsge, hfs⟩ :=
          ((eventually_ge_atTop s₀).and (converges_iff_eventually.1 hfg x)).exists
        exact hfs.symm.trans (hs₀ s hsge)
      · intro hgx
        obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (converges_iff_eventually.1 hfg x)
        exact ⟨s₀, fun s hs => (hs₀ s hs).trans hgx⟩
    refine isDelta_iff.2 ⟨(hval true).of_eq hgeq,
      isSigma_not_iff.1 ((hval false).of_eq fun x => ?_)⟩
    cases hgx : g x <;> simp [← hgeq x, hgx]

/-- **The Limit Lemma, `Δ⁰₂` form, unrelativized.** A predicate on a primitive-codable type is
`Δ⁰₂` if and only if it has a uniformly computable Boolean approximation converging pointwise to
a total deciding function. -/
theorem isDelta_two_empty_iff_exists_converges {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta ∅ 2 p ↔
      ∃ f : ℕ → α → Bool, Computable₂ f ∧
        ∃ g : α → Bool, Converges f g ∧ ∀ x, g x = true ↔ p x := by
  rw [isDelta_two_iff_exists_converges]
  exact exists_congr fun _ => and_congr (Set.oracle_empty ▸ computableIn₂_const_iff) Iff.rfl

end TauCeti.ArithmeticalHierarchy
