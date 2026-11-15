/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Jump.Iterate
import TauCeti.Computability.SingleOracle.Primrec

/-!
# The relativized Post theorem and strictness of the arithmetical hierarchy

Post's theorem identifies the quantifier-defined arithmetical hierarchy relative to an oracle set
`Z` with computability and computable enumerability in the finite iterates `Set.jump^[n] Z` of the
Turing jump.

At level one, a `Δ⁰₁(Z)` predicate has total `Z`-computable Boolean matrices witnessing both it and
its complement; searching for the first witness of either matrix produces a total `Z`-computable
decision procedure (`isDelta_one_iff_isSigma_zero`), relativizing Mathlib's
`ComputablePred.computable_iff_re_compl_re'`.

The inductive core is the jump-shift equivalence `isSigma_one_jump_iff_isSigma_two` between
`Σ⁰₁(Z')` and `Σ⁰₂(Z)`. A `Σ⁰₂(Z)` predicate projects a `Π⁰₁(Z)` matrix, whose complement one-one
reduces to `Z'` and is therefore decidable in `Z'`. Conversely, by the finite-use property of
single-oracle evaluation, an oracle program relative to `Z'` halts on an input iff there is a
finite oracle string `l` at fuel `l.length` on which bounded evaluation halts and whose entries
agree below `l.length` with membership and non-membership in `Z'`; bounded universal closure of
`Σ⁰₂(Z)` and contraction of the existential quantifier over `List ℕ` place this condition in
`Σ⁰₂(Z)`.

Induction on the quantifier depth lifts the jump shift to every positive level and every finite
iterate of the jump:

* `isSigma_succ_iff_exists_recursiveIn_domain`, `isSigma_succ_iff_exists_code`: `Σ⁰ₙ₊₁(Z)`
  predicates are the domains of partial functions recursive in `Z⁽ⁿ⁾`.
* `isDelta_succ_iff_isSigma_zero_iterate_jump`, `isDelta_succ_mem_iff_turingReducible_iterate_jump`:
  `Δ⁰ₙ₊₁(Z)` predicates are decidable in `Z⁽ⁿ⁾`, so for sets `C ∈ Δ⁰ₙ₊₁(Z)` iff `C ≤_T Z⁽ⁿ⁾`.
* `isSigma_succ_iff_oneOneReducible_iterate_jump`,
  `isPi_succ_iff_oneOneReducible_compl_iterate_jump`: `Z⁽ⁿ⁺¹⁾` is one-one complete for `Σ⁰ₙ₊₁(Z)`
  and `(Z⁽ⁿ⁺¹⁾)ᶜ` is one-one complete for `Π⁰ₙ₊₁(Z)` under ordinary computable reductions.
* `not_isPi_iterate_jump_succ`, `not_isDelta_iterate_jump_succ`,
  `isDelta_succ_turingJoin_iterate_jump_compl`: the relativized hierarchy does not collapse at any
  level, and `Σ⁰ₙ₊₁(Z) ∪ Π⁰ₙ₊₁(Z)` is strictly contained in `Δ⁰ₙ₊₂(Z)`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.2 and
  IV.1–2 (Theorems IV.1.13, IV.2.1, and IV.2.2).
-/

public section

open Encodable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z C : Set ℕ} {n m : ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-! ### Quantifier-free predicates and Post complementation -/

/-- At the empty oracle, `Σ⁰₀` agrees with Mathlib's `ComputablePred`. -/
theorem isSigma_zero_empty_iff_computablePred : IsSigma ∅ 0 p ↔ ComputablePred p := by
  rw [isSigma_zero_iff, ComputablePred.computable_iff]
  constructor
  · rintro ⟨b, hb, heq⟩
    have hb' : Computable b := hb.partrec_of_oracle fun g hg => by
      rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
      exact Partrec.const' _
    exact ⟨b, hb', funext fun x => propext (heq x).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb.computableIn, fun _ => Iff.rfl⟩

/-- For sets of natural numbers, `Σ⁰₀(Z)` membership is Turing reducibility to `Z`. -/
theorem isSigma_zero_mem_iff_turingReducible :
    IsSigma Z 0 (· ∈ C) ↔ TuringReducible C.oracle Z.oracle := by
  classical
  rw [isSigma_zero_iff, C.turingReducible_iff_computableIn_indicator]
  constructor
  · rintro ⟨b, hb, heq⟩
    have h01 : Primrec (fun a : Bool => cond a 1 0) := Primrec.dom_bool _
    refine (h01.computableIn.comp hb).of_eq fun x => ?_
    congr 1
    by_cases hx : x ∈ C
    · simp [hx, (heq x).2 hx]
    · simp [hx, Bool.eq_false_iff.2 (mt (heq x).1 hx)]
  · intro hχ
    refine ⟨fun x => C.indicator 1 x == 1,
      (Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp hχ, fun x => ?_⟩
    by_cases hx : x ∈ C <;> simp [hx]

/-- **Relativized Post complementation.** A predicate is `Δ⁰₁` relative to `Z` iff it is
quantifier-free (`Σ⁰₀`) relative to `Z`. For the empty oracle this is the classical equivalence of
computable predicates with predicates that are both c.e. and co-c.e.
(`ComputablePred.computable_iff_re_compl_re'`). -/
theorem isDelta_one_iff_isSigma_zero : IsDelta Z 1 p ↔ IsSigma Z 0 p := by
  classical
  refine ⟨fun hp => ?_, IsSigma.delta_succ⟩
  obtain ⟨hpS, hpP⟩ := isDelta_iff.1 hp
  obtain ⟨b₁, hb₁, heq₁⟩ := isSigma_one_iff.1 hpS
  obtain ⟨b₀, hb₀, heq₀⟩ := isSigma_one_iff.1 (isSigma_not_iff.2 hpP)
  have hboth : ComputableIn₂ {Z.oracle} (fun x y => b₁ (x, y) || b₀ (x, y)) :=
    Primrec.or.computableIn.comp (hb₁.pair hb₀)
  have hex : ∀ x, ∃ y, (b₁ (x, y) || b₀ (x, y)) = true := fun x => by
    by_cases hx : p x
    · obtain ⟨y, hy⟩ := (heq₁ x).1 hx
      exact ⟨y, by simp [hy]⟩
    · obtain ⟨y, hy⟩ := (heq₀ x).1 hx
      exact ⟨y, by simp [hy]⟩
  have hy₀ : ComputableIn {Z.oracle} (fun x => Nat.find (hex x)) :=
    ComputableIn.find hboth hex
  refine isSigma_zero_iff.2 ⟨fun x => b₁ (x, Nat.find (hex x)),
    hb₁.comp (ComputableIn.id.pair hy₀), fun x => ⟨fun h => (heq₁ x).2 ⟨_, h⟩, fun hx => ?_⟩⟩
  rcases Bool.or_eq_true_iff.1 (Nat.find_spec (hex x)) with h₁ | h₀
  · exact h₁
  · exact absurd hx ((heq₀ x).2 ⟨_, h₀⟩)

/-- At the empty oracle, `Δ⁰₁` agrees with Mathlib's `ComputablePred`. -/
theorem isDelta_one_empty_iff_computablePred : IsDelta ∅ 1 p ↔ ComputablePred p :=
  isDelta_one_iff_isSigma_zero.trans isSigma_zero_empty_iff_computablePred

/-- A set is `Δ⁰₁` relative to `Z` iff it is Turing reducible to `Z`. -/
theorem isDelta_one_mem_iff_turingReducible :
    IsDelta Z 1 (· ∈ C) ↔ TuringReducible C.oracle Z.oracle :=
  isDelta_one_iff_isSigma_zero.trans isSigma_zero_mem_iff_turingReducible

/-! ### Jump-shift equivalences -/

/-- **Single-jump shift at level one.** A predicate is `Σ⁰₁` relative to `Z'` iff it is `Σ⁰₂`
relative to `Z`. -/
theorem isSigma_one_jump_iff_isSigma_two : IsSigma Z.jump 1 p ↔ IsSigma Z 2 p := by
  classical
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    have hrun : IsSigma Z 2
        (fun a : α × List ℕ =>
          (Code.evaln (fun z => a.2[z]?) a.2.length c (encode a.1)).isSome = true) := by
      have hargs : Primrec (fun a : α × List ℕ => (a.2, a.2.length, c, encode a.1)) :=
        Primrec.snd.pair ((Primrec.list_length.comp Primrec.snd).pair
          ((Primrec.const c).pair (Primrec.encode.comp Primrec.fst)))
      exact (isSigma_zero_iff.2
        ⟨_, (Primrec.option_isSome.comp (Code.primrec_evaln_list.comp hargs)).computableIn,
          fun _ => Iff.rfl⟩).of_le (Nat.zero_le 2)
    have hget : ComputableIn {Z.oracle} (fun t : (α × List ℕ) × ℕ => List.getD t.1.2 t.2 0) :=
      (Primrec.list_getD 0).computableIn.comp
        ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd)
    have hval1 : IsSigma Z 2 (fun t : (α × List ℕ) × ℕ => List.getD t.1.2 t.2 0 = 1) :=
      (isSigma_zero_iff.2
        ⟨_, ((Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp hget),
          fun _ => beq_iff_eq⟩).of_le (Nat.zero_le 2)
    have hval0 : IsSigma Z 2 (fun t : (α × List ℕ) × ℕ => List.getD t.1.2 t.2 0 = 0) :=
      (isSigma_zero_iff.2
        ⟨_, ((Primrec.beq.comp Primrec.id (Primrec.const 0)).computableIn.comp hget),
          fun _ => beq_iff_eq⟩).of_le (Nat.zero_le 2)
    have hjump_mem : IsSigma Z 2 (fun t : (α × List ℕ) × ℕ => t.2 ∈ Z.jump) :=
      isSigma_one_jump.succ.preimage ComputableIn.snd
    have hjump_nmem : IsSigma Z 2 (fun t : (α × List ℕ) × ℕ => t.2 ∉ Z.jump) :=
      (isSigma_not_iff.2 isSigma_one_jump.pi_succ).preimage ComputableIn.snd
    have hagree : IsSigma Z 2
        (fun a : α × List ℕ => ∀ e < a.2.length,
          (List.getD a.2 e 0 = 1 ∧ e ∈ Z.jump) ∨ (List.getD a.2 e 0 = 0 ∧ e ∉ Z.jump)) :=
      ((hval1.and hjump_mem).or (hval0.and hjump_nmem)).forall_lt
        (Primrec.list_length.computableIn.comp ComputableIn.snd)
    refine ((hrun.and hagree).exists).of_eq fun x => ?_
    have hZ' : Z.jump.oracle = ((Z.jump.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) :=
      funext fun _ => by simp
    rw [hc x, hZ', Part.dom_iff_mem]
    simp only [Code.mem_eval_iff_exists_evaln_range_map, Option.isSome_iff_exists]
    constructor
    · rintro ⟨l, ⟨d, hd⟩, hl⟩
      have heq_list : l = (List.range l.length).map (Z.jump.indicator 1) := by
        refine List.ext_getElem (by simp) fun e he₁ he₂ => ?_
        have hgetD : List.getD l e 0 = l[e] := by
          simp [List.getD_eq_getElem?_getD, he₁]
        rcases hl e he₁ with ⟨h1, hmem⟩ | ⟨h0, hnmem⟩
        · rw [← hgetD, h1]
          simp [hmem]
        · rw [← hgetD, h0]
          simp [hnmem]
      exact ⟨d.output, l.length, d, heq_list ▸ hd, rfl⟩
    · rintro ⟨_, k, d, hd, _⟩
      refine ⟨(List.range k).map (Z.jump.indicator 1), ⟨d, by simpa using hd⟩, fun e he => ?_⟩
      simp only [List.length_map, List.length_range] at he
      have hgetD : List.getD ((List.range k).map (Z.jump.indicator 1)) e 0 =
          Z.jump.indicator 1 e := by
        simp [List.getD_eq_getElem?_getD, he]
      by_cases hmem : e ∈ Z.jump
      · refine Or.inl ⟨?_, hmem⟩
        rw [hgetD]
        simp [hmem]
      · refine Or.inr ⟨?_, hmem⟩
        rw [hgetD]
        simp [hmem]
  · intro hp
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hp
    obtain ⟨f, hf, -, hred⟩ := (isSigma_not_iff.2 hq).oneOneReducible_jump
    have hq' : IsPi Z.jump 0 q := by
      refine isPi_zero_iff.2 (isSigma_zero_iff.2
        ⟨fun a => Z.jump.indicator 1 (f a) == 0,
          (Primrec.beq.comp Primrec.id (Primrec.const 0)).computableIn.comp
            (Z.jump.computableIn_indicator.comp hf.computableIn),
          fun a => ?_⟩)
      by_cases ha : q a
      · have hnf : f a ∉ Z.jump := mt (hred a).2 (not_not.2 ha)
        simp [ha, Set.indicator_of_notMem hnf]
      · have hfmem : f a ∈ Z.jump := (hred a).1 ha
        simp [ha, Set.indicator_of_mem hfmem]
    exact isSigma_succ_iff.2 ⟨q, hq', heq⟩

/-- **Single-jump shift for `Σ⁰`.** Being `Σ⁰ₙ₊₁` relative to `Z'` is equivalent to being
`Σ⁰ₙ₊₂` relative to `Z`. -/
theorem isSigma_jump_succ : IsSigma Z.jump (n + 1) p ↔ IsSigma Z (n + 2) p := by
  induction n generalizing α with
  | zero => exact isSigma_one_jump_iff_isSigma_two
  | succ n ih =>
    rw [isSigma_succ_iff, isSigma_succ_iff]
    exact exists_congr fun q =>
      and_congr (isSigma_not_iff.symm.trans ((ih (p := fun a => ¬q a)).trans isSigma_not_iff))
        Iff.rfl

/-- **Single-jump shift for `Π⁰`.** Being `Π⁰ₙ₊₁` relative to `Z'` is equivalent to being
`Π⁰ₙ₊₂` relative to `Z`. -/
theorem isPi_jump_succ : IsPi Z.jump (n + 1) p ↔ IsPi Z (n + 2) p :=
  isSigma_not_iff.symm.trans ((isSigma_jump_succ (p := fun x => ¬p x)).trans isSigma_not_iff)

/-- **Single-jump shift for `Δ⁰`.** Being `Δ⁰ₙ₊₁` relative to `Z'` is equivalent to being
`Δ⁰ₙ₊₂` relative to `Z`. -/
theorem isDelta_jump_succ : IsDelta Z.jump (n + 1) p ↔ IsDelta Z (n + 2) p :=
  isDelta_iff.trans ((and_congr isSigma_jump_succ isPi_jump_succ).trans isDelta_iff.symm)

/-- **Iterated-jump shift for `Σ⁰`.** Being `Σ⁰ₘ₊₁` relative to `Z⁽ⁿ⁾` is equivalent to being
`Σ⁰ₙ₊ₘ₊₁` relative to `Z`. -/
theorem isSigma_iterate_jump_succ :
    IsSigma (Set.jump^[n] Z) (m + 1) p ↔ IsSigma Z (n + m + 1) p := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have hadd : n + (m + 1) + 1 = n + 1 + m + 1 := by omega
    rw [Function.iterate_succ_apply', isSigma_jump_succ, ih (m := m + 1), hadd]

/-- **Iterated-jump shift for `Π⁰`.** Being `Π⁰ₘ₊₁` relative to `Z⁽ⁿ⁾` is equivalent to being
`Π⁰ₙ₊ₘ₊₁` relative to `Z`. -/
theorem isPi_iterate_jump_succ :
    IsPi (Set.jump^[n] Z) (m + 1) p ↔ IsPi Z (n + m + 1) p :=
  isSigma_not_iff.symm.trans
    ((isSigma_iterate_jump_succ (p := fun x => ¬p x)).trans isSigma_not_iff)

/-- **Iterated-jump shift for `Δ⁰`.** Being `Δ⁰ₘ₊₁` relative to `Z⁽ⁿ⁾` is equivalent to being
`Δ⁰ₙ₊ₘ₊₁` relative to `Z`. -/
theorem isDelta_iterate_jump_succ :
    IsDelta (Set.jump^[n] Z) (m + 1) p ↔ IsDelta Z (n + m + 1) p :=
  isDelta_iff.trans
    ((and_congr isSigma_iterate_jump_succ isPi_iterate_jump_succ).trans isDelta_iff.symm)

/-- `Σ⁰ₙ₊₁(Z)` coincides with `Σ⁰₁(Z⁽ⁿ⁾)`. -/
theorem isSigma_succ_iff_isSigma_one_iterate_jump :
    IsSigma Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 1 p := by
  simpa using (isSigma_iterate_jump_succ (Z := Z) (n := n) (m := 0) (p := p)).symm

/-- `Π⁰ₙ₊₁(Z)` coincides with `Π⁰₁(Z⁽ⁿ⁾)`. -/
theorem isPi_succ_iff_isPi_one_iterate_jump :
    IsPi Z (n + 1) p ↔ IsPi (Set.jump^[n] Z) 1 p :=
  isSigma_not_iff.symm.trans
    ((isSigma_succ_iff_isSigma_one_iterate_jump (p := fun x => ¬p x)).trans isSigma_not_iff)

/-- `Δ⁰ₙ₊₁(Z)` coincides with `Δ⁰₁(Z⁽ⁿ⁾)`. -/
theorem isDelta_succ_iff_isDelta_one_iterate_jump :
    IsDelta Z (n + 1) p ↔ IsDelta (Set.jump^[n] Z) 1 p :=
  isDelta_iff.trans
    ((and_congr isSigma_succ_iff_isSigma_one_iterate_jump
      isPi_succ_iff_isPi_one_iterate_jump).trans isDelta_iff.symm)

/-! ### The relativized Post theorem and completeness of iterated jumps -/

/-- **Relativized Post theorem (`Σ⁰` form).** A predicate is `Σ⁰ₙ₊₁` relative to `Z` iff it is the
domain of a partial function recursive in `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_exists_recursiveIn_domain : IsSigma Z (n + 1) p ↔
    ∃ f : α →. ℕ, RecursiveIn {(Set.jump^[n] Z).oracle} f ∧ ∀ x, p x ↔ (f x).Dom :=
  isSigma_succ_iff_isSigma_one_iterate_jump.trans isSigma_one_iff_exists_recursiveIn_domain

/-- **Relativized Post theorem (program-domain form).** A predicate is `Σ⁰ₙ₊₁` relative to `Z`
iff it is the domain of a single-oracle program relative to `Z⁽ⁿ⁾` on encoded inputs. -/
theorem isSigma_succ_iff_exists_code : IsSigma Z (n + 1) p ↔
    ∃ c : Code, ∀ x, p x ↔ (Code.eval (Set.jump^[n] Z).oracle c (encode x)).Dom :=
  isSigma_succ_iff_isSigma_one_iterate_jump.trans isSigma_one_iff_exists_code

/-- For sets of natural numbers, `C ∈ Σ⁰ₙ₊₁(Z)` iff `C` is the domain of an oracle program
relative to `Z⁽ⁿ⁾` (c.e. in `Z⁽ⁿ⁾`). -/
theorem isSigma_succ_mem_iff_exists_code : IsSigma Z (n + 1) (· ∈ C) ↔
    ∃ c : Code, ∀ x, x ∈ C ↔ (Code.eval (Set.jump^[n] Z).oracle c x).Dom := by
  simpa only [encode_nat] using isSigma_succ_iff_exists_code (Z := Z) (n := n) (p := (· ∈ C))

/-- **Relativized Post theorem (`Π⁰` form).** A predicate is `Π⁰ₙ₊₁` relative to `Z` iff its
complement is the domain of a partial function recursive in `Z⁽ⁿ⁾`. -/
theorem isPi_succ_iff_exists_recursiveIn_domain_not : IsPi Z (n + 1) p ↔
    ∃ f : α →. ℕ, RecursiveIn {(Set.jump^[n] Z).oracle} f ∧ ∀ x, ¬p x ↔ (f x).Dom :=
  isSigma_not_iff.symm.trans (isSigma_succ_iff_exists_recursiveIn_domain (p := fun x => ¬p x))

/-- For sets of natural numbers, `C ∈ Π⁰ₙ₊₁(Z)` iff `Cᶜ` is the domain of an oracle program
relative to `Z⁽ⁿ⁾` (co-c.e. in `Z⁽ⁿ⁾`). -/
theorem isPi_succ_mem_iff_exists_code_compl : IsPi Z (n + 1) (· ∈ C) ↔
    ∃ c : Code, ∀ x, x ∈ Cᶜ ↔ (Code.eval (Set.jump^[n] Z).oracle c x).Dom :=
  isSigma_not_iff.symm.trans (isSigma_succ_mem_iff_exists_code (C := Cᶜ))

/-- **Relativized Post theorem (`Δ⁰` predicate form).** A predicate is `Δ⁰ₙ₊₁` relative to `Z` iff
it is quantifier-free (`Σ⁰₀`) relative to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_isSigma_zero_iterate_jump :
    IsDelta Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 0 p :=
  isDelta_succ_iff_isDelta_one_iterate_jump.trans isDelta_one_iff_isSigma_zero

/-- **Relativized Post theorem (`Δ⁰` set form).** A set `C` belongs to `Δ⁰ₙ₊₁(Z)` iff `C` is
Turing reducible to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_mem_iff_turingReducible_iterate_jump :
    IsDelta Z (n + 1) (· ∈ C) ↔ TuringReducible C.oracle (Set.jump^[n] Z).oracle :=
  isDelta_succ_iff_isSigma_zero_iterate_jump.trans isSigma_zero_mem_iff_turingReducible

/-- A set `C` belongs to `Δ⁰₂(Z)` iff `C` is Turing reducible to `Z'`. -/
theorem isDelta_two_mem_iff_turingReducible_jump :
    IsDelta Z 2 (· ∈ C) ↔ TuringReducible C.oracle Z.jump.oracle := by
  simpa using isDelta_succ_mem_iff_turingReducible_iterate_jump (Z := Z) (n := 1) (C := C)

/-- The `n`-th iterated jump `Z⁽ⁿ⁾` belongs to `Σ⁰ₙ(Z)` for every `n`. -/
theorem isSigma_iterate_jump : ∀ {n : ℕ}, IsSigma Z n (· ∈ Set.jump^[n] Z)
  | 0 => isSigma_zero_mem_iff_turingReducible.2 (TuringReducible.refl _)
  | _ + 1 => by
    rw [Function.iterate_succ_apply']
    exact isSigma_succ_iff_isSigma_one_iterate_jump.2 isSigma_one_jump

/-- The complement of `Z⁽ⁿ⁾` belongs to `Π⁰ₙ(Z)` for every `n`. -/
theorem isPi_compl_iterate_jump : IsPi Z n (· ∈ (Set.jump^[n] Z)ᶜ) := by
  classical
  exact isSigma_not_iff.1 (isSigma_iterate_jump.of_eq fun _ => by simp)

/-- **One-one completeness of `Z⁽ⁿ⁺¹⁾` for `Σ⁰ₙ₊₁(Z)`.** Every `Σ⁰ₙ₊₁(Z)` predicate one-one
reduces to `Z⁽ⁿ⁺¹⁾` by an ordinary computable injection. -/
theorem IsSigma.oneOneReducible_iterate_jump (hp : IsSigma Z (n + 1) p) :
    OneOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply']
  exact (isSigma_succ_iff_isSigma_one_iterate_jump.1 hp).oneOneReducible_jump

/-- Every `Σ⁰ₙ₊₁(Z)` predicate many-one reduces to `Z⁽ⁿ⁺¹⁾` by an ordinary computable function. -/
theorem IsSigma.manyOneReducible_iterate_jump (hp : IsSigma Z (n + 1) p) :
    ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  hp.oneOneReducible_iterate_jump.to_many_one

/-- A predicate is `Σ⁰ₙ₊₁` relative to `Z` iff it many-one reduces to `Z⁽ⁿ⁺¹⁾` by an ordinary
computable function. -/
theorem isSigma_succ_iff_manyOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨IsSigma.manyOneReducible_iterate_jump, fun ⟨_, hf, heq⟩ =>
    (isSigma_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- A predicate is `Σ⁰ₙ₊₁` relative to `Z` iff it one-one reduces to `Z⁽ⁿ⁺¹⁾` by an ordinary
computable injection. -/
theorem isSigma_succ_iff_oneOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ OneOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨IsSigma.oneOneReducible_iterate_jump,
    fun h => isSigma_succ_iff_manyOneReducible_iterate_jump.2 h.to_many_one⟩

/-- **One-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ` for `Π⁰ₙ₊₁(Z)`.** Every `Π⁰ₙ₊₁(Z)` predicate one-one
reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary computable injection. -/
theorem IsPi.oneOneReducible_compl_iterate_jump (hp : IsPi Z (n + 1) p) :
    OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  classical
  obtain ⟨f, hf, hinj, hred⟩ := (isSigma_not_iff.2 hp).oneOneReducible_iterate_jump
  exact ⟨f, hf, hinj, fun x => (not_iff_comm.1 (hred x)).symm⟩

/-- Every `Π⁰ₙ₊₁(Z)` predicate many-one reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary computable
function. -/
theorem IsPi.manyOneReducible_compl_iterate_jump (hp : IsPi Z (n + 1) p) :
    ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  hp.oneOneReducible_compl_iterate_jump.to_many_one

/-- A predicate is `Π⁰ₙ₊₁` relative to `Z` iff it many-one reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary
computable function. -/
theorem isPi_succ_iff_manyOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  ⟨IsPi.manyOneReducible_compl_iterate_jump, fun ⟨_, hf, heq⟩ =>
    (isPi_compl_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- A predicate is `Π⁰ₙ₊₁` relative to `Z` iff it one-one reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary
computable injection. -/
theorem isPi_succ_iff_oneOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  ⟨IsPi.oneOneReducible_compl_iterate_jump,
    fun h => isPi_succ_iff_manyOneReducible_compl_iterate_jump.2 h.to_many_one⟩

/-! ### Strictness of the relativized arithmetical hierarchy -/

/-- **Hierarchy theorem (`Σ⁰` vs `Π⁰`).** For every oracle `Z` and `n : ℕ`, the `(n + 1)`-st jump
`Z⁽ⁿ⁺¹⁾` belongs to `Σ⁰ₙ₊₁(Z)` but not to `Π⁰ₙ₊₁(Z)`. -/
theorem not_isPi_iterate_jump_succ :
    ¬IsPi Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := fun hpi =>
  Set.not_iterate_jump_turingReducible_of_lt Z (Nat.lt_succ_self n)
    (isDelta_succ_mem_iff_turingReducible_iterate_jump.1
      (isDelta_iff.2 ⟨isSigma_iterate_jump, hpi⟩))

/-- The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` belongs to `Π⁰ₙ₊₁(Z)` but not to `Σ⁰ₙ₊₁(Z)`. -/
theorem not_isSigma_compl_iterate_jump_succ :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_iterate_jump_succ (isSigma_not_iff.1 (h.of_eq fun _ => Iff.rfl))

/-- `Z⁽ⁿ⁺¹⁾` does not belong to `Δ⁰ₙ₊₁(Z)`. -/
theorem not_isDelta_iterate_jump_succ :
    ¬IsDelta Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := fun h =>
  not_isPi_iterate_jump_succ (isDelta_iff.1 h).2

/-- A later iterated jump `Z⁽ⁿ⁾` does not belong to `Σ⁰ₘ(Z)` for any `m < n`. -/
theorem not_isSigma_iterate_jump_of_lt (h : m < n) :
    ¬IsSigma Z m (· ∈ Set.jump^[n] Z) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  intro hm
  have hle : m + 1 ≤ m + k + 1 := by omega
  have hdelta : IsDelta Z (m + k + 1) (· ∈ Set.jump^[m + k + 1] Z) :=
    hm.delta_succ.of_le hle
  exact not_isDelta_iterate_jump_succ hdelta

/-- The complement `(Z⁽ⁿ⁾)ᶜ` does not belong to `Π⁰ₘ(Z)` for any `m < n`. -/
theorem not_isPi_compl_iterate_jump_of_lt (h : m < n) :
    ¬IsPi Z m (· ∈ (Set.jump^[n] Z)ᶜ) := by
  classical
  intro hm
  exact not_isSigma_iterate_jump_of_lt h ((isSigma_not_iff.2 hm).of_eq fun _ => not_not)

/-- The parity join `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` belongs to `Δ⁰ₙ₊₂(Z)`. -/
theorem isDelta_succ_turingJoin_iterate_jump_compl :
    IsDelta Z (n + 2) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  have hle : 1 ≤ n + 2 := Nat.succ_le_succ (Nat.zero_le (n + 1))
  have heven : IsDelta Z (n + 2) (fun x : ℕ => !x.bodd = true) :=
    (isSigma_zero_iff.2
      ⟨fun x : ℕ => !x.bodd, (Primrec.not.to_comp.comp Computable.nat_bodd).computableIn,
        fun _ => Iff.rfl⟩).delta_succ.of_le hle
  have hodd : IsDelta Z (n + 2) (fun x : ℕ => x.bodd = true) :=
    (isSigma_zero_iff.2
      ⟨Nat.bodd, Computable.nat_bodd.computableIn, fun _ => Iff.rfl⟩).delta_succ.of_le hle
  have hleft : IsDelta Z (n + 2) (fun x : ℕ => x.div2 ∈ Set.jump^[n + 1] Z) :=
    (isSigma_iterate_jump.delta_succ).preimage Primrec.nat_div2.computableIn
  have hright : IsDelta Z (n + 2) (fun x : ℕ => x.div2 ∈ (Set.jump^[n + 1] Z)ᶜ) :=
    (isPi_compl_iterate_jump.delta_succ).preimage Primrec.nat_div2.computableIn
  refine ((heven.and hleft).or (hodd.and hright)).of_eq fun x => ?_
  rw [Set.mem_turingJoin]
  cases x.bodd <;> simp

/-- The parity join `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` does not belong to `Σ⁰ₙ₊₁(Z)`. -/
theorem not_isSigma_turingJoin_iterate_jump_compl :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isSigma_compl_iterate_jump_succ
    ((h.preimage Primrec.nat_double_succ.computableIn).of_eq fun _ =>
      Set.two_mul_add_one_mem_turingJoin)

/-- The parity join `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` does not belong to `Π⁰ₙ₊₁(Z)`. Together with
`isDelta_succ_turingJoin_iterate_jump_compl` and `not_isSigma_turingJoin_iterate_jump_compl`, this
witnesses `Σ⁰ₙ₊₁(Z) ∪ Π⁰ₙ₊₁(Z) ⊊ Δ⁰ₙ₊₂(Z)`. -/
theorem not_isPi_turingJoin_iterate_jump_compl :
    ¬IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_iterate_jump_succ
    ((h.preimage Primrec.nat_double.computableIn).of_eq fun _ => Set.two_mul_mem_turingJoin)

end TauCeti.ArithmeticalHierarchy
