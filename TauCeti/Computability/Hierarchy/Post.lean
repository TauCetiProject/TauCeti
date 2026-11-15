/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.Jump.Iterate
import TauCeti.Computability.Approximation.Jump
import TauCeti.Computability.SingleOracle.Limit

/-!
# Relativized Post's theorem and strictness of the arithmetical hierarchy

This file relates the quantifier-defined arithmetical pointclasses `IsSigma`, `IsPi`, and `IsDelta`
to computability and enumerability in the finite iterates `Set.jump^[n] Z` of the Turing jump.

The core bridge is at the second level: the domain of an oracle program evaluated relative to `Z'`
is `Σ⁰₂` relative to `Z`, and conversely every `Σ⁰₂(Z)` predicate is `Σ⁰₁(Z')`. Shifting across a
single jump and across `n` iterated jumps turns `n` jumps into `n` quantifier alternations at every
positive level, while the first-level complement theorem `isDelta_one_iff` identifies `Σ⁰₀(Z⁽ⁿ⁾)`
with `Δ⁰ₙ₊₁(Z)`.

From these quantifier-shift equivalences we obtain both halves of **relativized Post's theorem**
for every oracle `Z : Set ℕ` and `n : ℕ`:

* a predicate is `Σ⁰ₙ₊₁(Z)` iff it is the domain of a partial function recursive in `Z⁽ⁿ⁾`, and
  iff it reduces one-one (or many-one) to `Z⁽ⁿ⁺¹⁾`;
* a predicate is `Δ⁰ₙ₊₁(Z)` iff it has a total Boolean decision procedure computable in `Z⁽ⁿ⁾`, so
  a set `C : Set ℕ` is `Δ⁰ₙ₊₁(Z)` iff `C ≤_T Z⁽ⁿ⁾`.

Combined with the strictness of the jump (`Z⁽ⁿ⁾ <_T Z⁽ⁿ⁺¹⁾`), Post's theorem classifies the exact
pointclass of every iterated jump and yields the strict inclusions of the arithmetical hierarchy:
`Σ⁰ₙ(Z) ⊂ Σ⁰ₙ₊₁(Z)` and `Π⁰ₙ(Z) ⊂ Π⁰ₙ₊₁(Z)` for all `n`, `Δ⁰ₙ₊₁(Z) ⊂ Δ⁰ₙ₊₂(Z)`, and
`Σ⁰ₙ₊₁(Z) ∪ Π⁰ₙ₊₁(Z) ⊂ Δ⁰ₙ₊₂(Z)` witnessed by the parity join of `Z⁽ⁿ⁺¹⁾` with its complement.

## Main results

* `TauCeti.ArithmeticalHierarchy.isSigma_jump_succ_iff`,
  `TauCeti.ArithmeticalHierarchy.isSigma_iterate_jump_succ_iff`: quantifier shifts across one jump
  and across `n` iterated jumps, together with their `IsPi` and `IsDelta` counterparts.
* `TauCeti.ArithmeticalHierarchy.isSigma_iterate_jump_zero_iff`: predicates computable in `Z⁽ⁿ⁾`
  are exactly the `Δ⁰ₙ₊₁(Z)` predicates.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_exists_recursiveIn_domain`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_exists_code`: **relativized Post's theorem** for
  `Σ⁰ₙ₊₁(Z)`.
* `TauCeti.ArithmeticalHierarchy.isDelta_succ_iff_exists_computableIn`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_mem_iff_turingReducible`: **relativized Post's
  theorem** for `Δ⁰ₙ₊₁(Z)`.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_succ_iff_of_low`: for a low set `A`, the hierarchy
  relative to `A` collapses to the unrelativized hierarchy from level `2` upward.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_oneOneReducible_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_manyOneReducible_iterate_jump`: one-one and
  many-one completeness of `Z⁽ⁿ⁺¹⁾` for `Σ⁰ₙ₊₁(Z)`.
* `TauCeti.ArithmeticalHierarchy.isSigma_iterate_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isPi_iterate_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isDelta_iterate_jump_iff`: exact level classifications of
  `Z⁽ⁿ⁺¹⁾`.
* `TauCeti.ArithmeticalHierarchy.strictMono_setOf_isSigma`,
  `TauCeti.ArithmeticalHierarchy.strictMono_setOf_isPi`,
  `TauCeti.ArithmeticalHierarchy.strictMono_setOf_isDelta_succ`,
  `TauCeti.ArithmeticalHierarchy.setOf_isSigma_union_setOf_isPi_ssubset_setOf_isDelta_succ_succ`:
  strictness of the arithmetical hierarchy relative to `Z`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.2 and
  IV.1–2, especially the Hierarchy Theorem IV.1.13 and Post's Theorem IV.2.1.
-/

public section

open Encodable Filter TauCeti.Approximation TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {n m : ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-! ### Quantifier shifts across a single jump -/

/-- Successful run decoded from a paired output and use `m : ℕ`. -/
private def haltOfNat (m : ℕ) : Code.Halt :=
  ⟨m.unpair.1, m.unpair.2⟩

/-- Matrix testing whether at stage `s + r` the bounded evaluation of `c` on `n` against
`Z.jumpApproximation (s + r)` produces the run `haltOfNat m`. -/
private noncomputable def jumpDomMatrix (Z : Set ℕ) (c : Code)
    (p : ((ℕ × ℕ) × ℕ) × ℕ) : Bool :=
  encode (Code.evaln (fun z => some (Z.jumpApproximation (p.1.2 + p.2) z))
    (p.1.2 + p.2) c p.1.1.1) == encode (some (haltOfNat p.1.1.2))

private theorem computableIn_jumpDomMatrix (Z : Set ℕ) (c : Code) :
    ComputableIn {Z.oracle} (jumpDomMatrix Z c) := by
  have hn : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2 + p.2) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hargs : ComputableIn {Z.oracle}
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (p.1.2 + p.2, p.1.2 + p.2, c, p.1.1.1)) :=
    ht.computableIn.pair (ht.computableIn.pair ((ComputableIn.const c).pair hn.computableIn))
  have hlhs : ComputableIn {Z.oracle} (fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      encode (Code.evaln (fun z => some (Z.jumpApproximation (p.1.2 + p.2) z))
        (p.1.2 + p.2) c p.1.1.1)) :=
    Primrec.encode.computableIn.comp
      ((Code.computableIn_evaln Z.computableIn₂_jumpApproximation).comp hargs)
  have hhalt : Primrec haltOfNat :=
    Code.Halt.primrec₂_mk.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hrhs : Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ => encode (some (haltOfNat p.1.1.2))) :=
    Primrec.encode.comp (Primrec.option_some.comp (hhalt.comp hm))
  have hbeq : Primrec (fun q : ℕ × ℕ => q.1 == q.2) :=
    Primrec.beq.of_eq fun _ _ => Bool.eq_iff_iff.2 (by simp)
  exact hbeq.computableIn.comp (hlhs.pair hrhs.computableIn)

private theorem jumpDomMatrix_eq_true_iff (Z : Set ℕ) (c : Code) (n m s r : ℕ) :
    jumpDomMatrix Z c (((n, m), s), r) = true ↔
      Code.evaln (fun z => some (Z.jumpApproximation (s + r) z)) (s + r) c n =
        some (haltOfNat m) := by
  simp only [jumpDomMatrix, beq_iff_eq, encode_inj]

private theorem exists_forall_jumpDomMatrix_iff (Z : Set ℕ) (c : Code) (n : ℕ) :
    (∃ m s, ∀ r, jumpDomMatrix Z c (((n, m), s), r) = true) ↔
      (Code.eval Z.jump.oracle c n).Dom := by
  have hσ : Converges (fun t z => some (Z.jumpApproximation t z)) (Code.setAnswers Z.jump) :=
    converges_iff_eventually.2 fun z =>
      (converges_iff_eventually.1 Z.converges_jumpApproximation z).mono
        fun _ ht => by simp [Code.setAnswers_apply, ht]
  constructor
  · rintro ⟨m, s, h⟩
    have hev : ∀ᶠ t in atTop,
        Code.evaln (fun z => some (Z.jumpApproximation t z)) t c n = some (haltOfNat m) :=
      eventually_atTop.2 ⟨s, fun t hst => by
        have hts : s + (t - s) = t := by omega
        simpa [hts] using (jumpDomMatrix_eq_true_iff Z c n m s (t - s)).1 (h (t - s))⟩
    exact Part.dom_iff_mem.2 ⟨(haltOfNat m).output,
      Code.mem_eval_of_eventually_evaln_eq_some (t := fun t => t) (by simp) hσ hev⟩
  · intro hdom
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨d, -, hev⟩ := Code.exists_eventually_evaln_eq_some_of_mem_eval
      (t := fun t => t) (by simp) hσ tendsto_id hy
    obtain ⟨s, hs⟩ := eventually_atTop.1 hev
    refine ⟨Nat.pair d.output d.use, s, fun r => (jumpDomMatrix_eq_true_iff Z c n _ s r).2 ?_⟩
    have hd : haltOfNat (Nat.pair d.output d.use) = d := by
      ext <;> simp [haltOfNat]
    simpa [hd] using hs (s + r) (Nat.le_add_right s r)

/-- The domain of an oracle program evaluated relative to the jump `Z'` is `Σ⁰₂` relative to
`Z`. -/
theorem isSigma_two_dom_eval_jump (c : Code) :
    IsSigma Z 2 (fun n => (Code.eval Z.jump.oracle c n).Dom) := by
  have h0 : IsSigma Z 0 (fun p => jumpDomMatrix Z c p = true) :=
    isSigma_zero_iff.2 ⟨jumpDomMatrix Z c, computableIn_jumpDomMatrix Z c, fun _ => Iff.rfl⟩
  have h1 : IsPi Z 1 (fun a : (ℕ × ℕ) × ℕ => ∀ r, jumpDomMatrix Z c (a, r) = true) :=
    isPi_succ_iff.2 ⟨_, h0, fun _ => Iff.rfl⟩
  have h2 : IsSigma Z 2 (fun b : ℕ × ℕ => ∃ s, ∀ r, jumpDomMatrix Z c ((b, s), r) = true) :=
    isSigma_succ_iff.2 ⟨_, h1, fun _ => Iff.rfl⟩
  exact h2.exists_nat.of_eq (exists_forall_jumpDomMatrix_iff Z c)

/-- **Single-jump shift for `Σ⁰`.** At every positive level, replacing `Z` by `Z'` shifts the
existential pointclass up by one quantifier. -/
theorem isSigma_jump_succ_iff : IsSigma Z.jump (n + 1) p ↔ IsSigma Z (n + 2) p := by
  induction n generalizing α with
  | zero =>
    classical
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 h
      exact ((isSigma_two_dom_eval_jump c).preimage Primrec.encode.computableIn).of_eq
        fun x => (hc x).symm
    · intro h
      obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
      obtain ⟨g, hg, -, hgq⟩ := (isSigma_not_iff.2 hq).oneOneReducible_jump
      have hb : ComputableIn {Z.jump.oracle} (fun a : α × ℕ => Z.jump.indicator 1 (g a) == 0) :=
        Primrec.beq.computableIn.comp
          ((Z.jump.computableIn_indicator.comp hg.computableIn).pair (ComputableIn.const 0))
      refine isSigma_one_iff.2 ⟨_, hb, fun x => (heq x).trans (exists_congr fun y => ?_)⟩
      by_cases hqy : q (x, y)
      · have : g (x, y) ∉ Z.jump := mt (hgq (x, y)).2 (not_not_intro hqy)
        simp [hqy, this]
      · have : g (x, y) ∈ Z.jump := (hgq (x, y)).1 hqy
        simp [hqy, this]
  | succ n ih =>
    rw [isSigma_succ_iff (n := n + 1), isSigma_succ_iff (n := n + 2)]
    refine exists_congr fun q => and_congr ?_ Iff.rfl
    rw [← isSigma_not_iff, ← isSigma_not_iff]
    exact ih

/-- **Single-jump shift for `Π⁰`.** At every positive level, replacing `Z` by `Z'` shifts the
universal pointclass up by one quantifier. -/
theorem isPi_jump_succ_iff : IsPi Z.jump (n + 1) p ↔ IsPi Z (n + 2) p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff, isSigma_jump_succ_iff]

/-- **Single-jump shift for `Δ⁰`.** At every positive level, replacing `Z` by `Z'` shifts the
ambiguous pointclass up by one level. -/
theorem isDelta_jump_succ_iff : IsDelta Z.jump (n + 1) p ↔ IsDelta Z (n + 2) p := by
  rw [isDelta_iff, isDelta_iff, isSigma_jump_succ_iff, isPi_jump_succ_iff]

/-- A predicate is `Σ⁰₀` relative to `Z'` exactly when it is `Δ⁰₂` relative to `Z`. -/
theorem isSigma_jump_zero_iff : IsSigma Z.jump 0 p ↔ IsDelta Z 2 p := by
  rw [← isDelta_one_iff, isDelta_jump_succ_iff (n := 0)]

/-! ### Quantifier shifts across finite iterates of the jump -/

/-- **Iterated-jump shift for `Σ⁰`.** Replacing `Z` by `Z⁽ⁿ⁾` at a positive level `m + 1` adds `n`
quantifiers, yielding `Σ⁰_{n + (m + 1)}(Z)`. -/
theorem isSigma_iterate_jump_succ_iff :
    IsSigma (Set.jump^[n] Z) (m + 1) p ↔ IsSigma Z (n + (m + 1)) p := by
  induction n generalizing Z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    have h1 : n + (m + 1) = n + m + 1 := by omega
    have h2 : n + 1 + (m + 1) = n + m + 2 := by omega
    rw [h1, h2, isSigma_jump_succ_iff]

/-- **Iterated-jump shift for `Π⁰`.** Replacing `Z` by `Z⁽ⁿ⁾` at a positive level `m + 1` yields
`Π⁰_{n + (m + 1)}(Z)`. -/
theorem isPi_iterate_jump_succ_iff :
    IsPi (Set.jump^[n] Z) (m + 1) p ↔ IsPi Z (n + (m + 1)) p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff, isSigma_iterate_jump_succ_iff]

/-- **Iterated-jump shift for `Δ⁰`.** Replacing `Z` by `Z⁽ⁿ⁾` at a positive level `m + 1` yields
`Δ⁰_{n + (m + 1)}(Z)`. -/
theorem isDelta_iterate_jump_succ_iff :
    IsDelta (Set.jump^[n] Z) (m + 1) p ↔ IsDelta Z (n + (m + 1)) p := by
  rw [isDelta_iff, isDelta_iff, isSigma_iterate_jump_succ_iff, isPi_iterate_jump_succ_iff]

/-- A predicate is `Σ⁰₀` relative to `Z⁽ⁿ⁾` exactly when it is `Δ⁰ₙ₊₁` relative to `Z`. -/
theorem isSigma_iterate_jump_zero_iff : IsSigma (Set.jump^[n] Z) 0 p ↔ IsDelta Z (n + 1) p := by
  rw [← isDelta_one_iff, isDelta_iterate_jump_succ_iff (m := 0)]

/-! ### Relativized Post's theorem -/

/-- **Relativized Post's theorem (`Σ⁰` form).** For every oracle `Z` and `n : ℕ`, a predicate is
`Σ⁰ₙ₊₁` relative to `Z` iff it is c.e. in `Z⁽ⁿ⁾`, that is, the domain of a partial function
recursive in `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_exists_recursiveIn_domain :
    IsSigma Z (n + 1) p ↔
      ∃ f : α →. ℕ, RecursiveIn {(Set.jump^[n] Z).oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  rw [← isSigma_iterate_jump_succ_iff (m := 0), isSigma_one_iff_exists_recursiveIn_domain]

/-- **Relativized Post's theorem (program-domain form).** A predicate is `Σ⁰ₙ₊₁` relative to `Z`
iff it is the halting domain of an oracle program evaluated relative to `Z⁽ⁿ⁾` on encoded
inputs. -/
theorem isSigma_succ_iff_exists_code :
    IsSigma Z (n + 1) p ↔
      ∃ c : Code, ∀ x, p x ↔ (Code.eval (Set.jump^[n] Z).oracle c (encode x)).Dom := by
  rw [← isSigma_iterate_jump_succ_iff (m := 0), isSigma_one_iff_exists_code]

/-- **Relativized Post's theorem (`Δ⁰` predicate form).** For every oracle `Z` and `n : ℕ`, a
predicate is `Δ⁰ₙ₊₁` relative to `Z` iff it has a total Boolean decision procedure computable in
`Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_exists_computableIn :
    IsDelta Z (n + 1) p ↔
      ∃ b : α → Bool, ComputableIn {(Set.jump^[n] Z).oracle} b ∧ ∀ x, b x = true ↔ p x := by
  rw [← isSigma_iterate_jump_zero_iff, isSigma_zero_iff]

/-- **Relativized Post's theorem (`Δ⁰` set form).** For every oracle `Z`, `n : ℕ`, and `C : Set ℕ`,
membership in `C` is `Δ⁰ₙ₊₁` relative to `Z` iff `C ≤_T Z⁽ⁿ⁾`. -/
theorem isDelta_succ_mem_iff_turingReducible {C : Set ℕ} :
    IsDelta Z (n + 1) (· ∈ C) ↔ TuringReducible C.oracle (Set.jump^[n] Z).oracle := by
  rw [← isSigma_iterate_jump_zero_iff, isSigma_zero_mem_iff_turingReducible]

/-- For a low set `A`, `Σ⁰ₙ₊₂` relative to `A` coincides with unrelativized `Σ⁰ₙ₊₂`. -/
theorem isSigma_succ_succ_iff_of_low {A : Set ℕ} (hA : A.Low) :
    IsSigma A (n + 2) p ↔ IsSigma ∅ (n + 2) p := by
  rw [← isSigma_jump_succ_iff, ← isSigma_jump_succ_iff (Z := ∅),
    isSigma_congr_oracle ((Set.low_def A).1 hA)]

/-- For a low set `A`, `Π⁰ₙ₊₂` relative to `A` coincides with unrelativized `Π⁰ₙ₊₂`. -/
theorem isPi_succ_succ_iff_of_low {A : Set ℕ} (hA : A.Low) :
    IsPi A (n + 2) p ↔ IsPi ∅ (n + 2) p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff, isSigma_succ_succ_iff_of_low hA]

/-- For a low set `A`, `Δ⁰ₙ₊₂` relative to `A` coincides with unrelativized `Δ⁰ₙ₊₂`. -/
theorem isDelta_succ_succ_iff_of_low {A : Set ℕ} (hA : A.Low) :
    IsDelta A (n + 2) p ↔ IsDelta ∅ (n + 2) p := by
  rw [isDelta_iff, isDelta_iff, isSigma_succ_succ_iff_of_low hA, isPi_succ_succ_iff_of_low hA]

/-! ### Completeness of the iterated jumps -/

/-- The `(n + 1)`-th jump `Z⁽ⁿ⁺¹⁾` belongs to `Σ⁰ₙ₊₁(Z)`. -/
theorem isSigma_succ_iterate_jump : IsSigma Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply', ← isSigma_iterate_jump_succ_iff (m := 0)]
  exact isSigma_one_jump

/-- Every `Σ⁰ₙ₊₁(Z)` predicate reduces one-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem IsSigma.oneOneReducible_iterate_jump (h : IsSigma Z (n + 1) p) :
    OneOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply']
  exact ((isSigma_iterate_jump_succ_iff (m := 0)).2 h).oneOneReducible_jump

/-- **One-one completeness of `Z⁽ⁿ⁺¹⁾` for `Σ⁰ₙ₊₁(Z)`.** A predicate is `Σ⁰ₙ₊₁` relative to `Z`
iff it reduces one-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_oneOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ OneOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨IsSigma.oneOneReducible_iterate_jump,
    fun h => isSigma_succ_iterate_jump.of_manyOneReducible h.to_many_one⟩

/-- **Many-one completeness of `Z⁽ⁿ⁺¹⁾` for `Σ⁰ₙ₊₁(Z)`.** A predicate is `Σ⁰ₙ₊₁` relative to `Z`
iff it reduces many-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_manyOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨fun h => h.oneOneReducible_iterate_jump.to_many_one,
    isSigma_succ_iterate_jump.of_manyOneReducible⟩

/-- Every `Π⁰ₙ₊₁(Z)` predicate reduces one-one to the complement of `Z⁽ⁿ⁺¹⁾`. -/
theorem IsPi.oneOneReducible_compl_iterate_jump (h : IsPi Z (n + 1) p) :
    OneOneReducible p (· ∉ Set.jump^[n + 1] Z) := by
  classical
  obtain ⟨f, hf, hinj, heq⟩ := (isSigma_not_iff.2 h).oneOneReducible_iterate_jump
  exact ⟨f, hf, hinj, fun x => by simpa using (heq x).not⟩

/-- **One-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ` for `Π⁰ₙ₊₁(Z)`.** A predicate is `Π⁰ₙ₊₁` relative to `Z`
iff it reduces one-one to the complement of `Z⁽ⁿ⁺¹⁾`. -/
theorem isPi_succ_iff_oneOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ OneOneReducible p (· ∉ Set.jump^[n + 1] Z) :=
  ⟨IsPi.oneOneReducible_compl_iterate_jump, fun h =>
    (isPi_not_iff.2 isSigma_succ_iterate_jump).of_manyOneReducible h.to_many_one⟩

/-- **Many-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ` for `Π⁰ₙ₊₁(Z)`.** A predicate is `Π⁰ₙ₊₁` relative to `Z`
iff it reduces many-one to the complement of `Z⁽ⁿ⁺¹⁾`. -/
theorem isPi_succ_iff_manyOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ ManyOneReducible p (· ∉ Set.jump^[n + 1] Z) :=
  ⟨fun h => h.oneOneReducible_compl_iterate_jump.to_many_one,
    (isPi_not_iff.2 isSigma_succ_iterate_jump).of_manyOneReducible⟩

/-! ### Exact classifications and strictness of the hierarchy -/

/-- **Non-collapse at `Z⁽ⁿ⁺¹⁾`.** The `(n + 1)`-th jump `Z⁽ⁿ⁺¹⁾` is not `Π⁰ₙ₊₁` relative to `Z`. -/
theorem not_isPi_succ_iterate_jump : ¬IsPi Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply', ← isPi_iterate_jump_succ_iff (m := 0)]
  exact not_isPi_one_jump

/-- `Z⁽ⁿ⁺¹⁾` belongs to `Σ⁰ₘ(Z)` iff `n + 1 ≤ m`. -/
theorem isSigma_iterate_jump_iff :
    IsSigma Z m (· ∈ Set.jump^[n + 1] Z) ↔ n + 1 ≤ m :=
  ⟨fun hm => not_lt.1 fun hlt =>
    not_isPi_succ_iterate_jump (isDelta_iff.1 (hm.delta_succ.of_le (by omega))).2,
    isSigma_succ_iterate_jump.of_le⟩

/-- `Z⁽ⁿ⁺¹⁾` belongs to `Π⁰ₘ(Z)` iff `n + 2 ≤ m`. -/
theorem isPi_iterate_jump_iff :
    IsPi Z m (· ∈ Set.jump^[n + 1] Z) ↔ n + 2 ≤ m :=
  ⟨fun hm => not_lt.1 fun hlt => not_isPi_succ_iterate_jump (hm.of_le (by omega)),
    isSigma_succ_iterate_jump.pi_succ.of_le⟩

/-- `Z⁽ⁿ⁺¹⁾` belongs to `Δ⁰ₘ(Z)` iff `n + 2 ≤ m`. -/
theorem isDelta_iterate_jump_iff :
    IsDelta Z m (· ∈ Set.jump^[n + 1] Z) ↔ n + 2 ≤ m := by
  rw [isDelta_iff, isSigma_iterate_jump_iff, isPi_iterate_jump_iff]
  omega

/-- `Z'` belongs to `Σ⁰ₘ(Z)` iff `1 ≤ m`. -/
theorem isSigma_jump_iff : IsSigma Z m (· ∈ Z.jump) ↔ 1 ≤ m := by
  simpa using isSigma_iterate_jump_iff (Z := Z) (n := 0) (m := m)

/-- `Z'` belongs to `Π⁰ₘ(Z)` iff `2 ≤ m`. -/
theorem isPi_jump_iff : IsPi Z m (· ∈ Z.jump) ↔ 2 ≤ m := by
  simpa using isPi_iterate_jump_iff (Z := Z) (n := 0) (m := m)

/-- `Z'` belongs to `Δ⁰ₘ(Z)` iff `2 ≤ m`. -/
theorem isDelta_jump_iff : IsDelta Z m (· ∈ Z.jump) ↔ 2 ≤ m := by
  simpa using isDelta_iterate_jump_iff (Z := Z) (n := 0) (m := m)

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement belongs to `Δ⁰ₙ₊₂(Z)`. -/
theorem isDelta_succ_succ_turingJoin_compl_iterate_jump :
    IsDelta Z (n + 2) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isDelta_succ_mem_iff_turingReducible, Set.oracle_turingJoin_turingReducible_iff]
  refine ⟨TuringReducible.refl _, isSigma_zero_mem_iff_turingReducible.1 ?_⟩
  exact (isSigma_not_iff.2
    (isPi_zero_iff.2 (isSigma_zero_mem_iff_turingReducible.2 (TuringReducible.refl _)))).of_eq
    (by simp)

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement does not belong to `Σ⁰ₙ₊₁(Z)`. -/
theorem not_isSigma_succ_turingJoin_compl_iterate_jump :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_succ_iterate_jump <| isSigma_not_iff.1 <|
    (h.preimage Primrec.nat_double_succ.computableIn).of_eq fun _ =>
      Set.two_mul_add_one_mem_turingJoin

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement does not belong to `Π⁰ₙ₊₁(Z)`. -/
theorem not_isPi_succ_turingJoin_compl_iterate_jump :
    ¬IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_succ_iterate_jump <|
    (h.preimage Primrec.nat_double.computableIn).of_eq fun _ =>
      Set.two_mul_mem_turingJoin

/-- **Arithmetical Hierarchy Theorem (`Σ⁰` strictness).** Relative to every oracle `Z`, the
sequence of `Σ⁰ₙ(Z)` pointclasses on `ℕ` is strictly increasing for all `n : ℕ`. -/
theorem strictMono_setOf_isSigma (Z : Set ℕ) :
    StrictMono fun n => {p : ℕ → Prop | IsSigma Z n p} := by
  intro n m hnm
  rw [Set.ssubset_def]
  refine ⟨fun _ hp => hp.of_le hnm.le, fun hsub => ?_⟩
  have hmem : IsSigma Z n (· ∈ Set.jump^[n + 1] Z) :=
    hsub (isSigma_iterate_jump_iff.2 hnm)
  exact (not_le_of_gt n.lt_succ_self) (isSigma_iterate_jump_iff.1 hmem)

/-- **Arithmetical Hierarchy Theorem (`Π⁰` strictness).** Relative to every oracle `Z`, the
sequence of `Π⁰ₙ(Z)` pointclasses on `ℕ` is strictly increasing for all `n : ℕ`. -/
theorem strictMono_setOf_isPi (Z : Set ℕ) :
    StrictMono fun n => {p : ℕ → Prop | IsPi Z n p} := by
  intro n m hnm
  rw [Set.ssubset_def]
  refine ⟨fun _ hp => hp.of_le hnm.le, fun hsub => ?_⟩
  have hmem : IsPi Z m (· ∉ Set.jump^[n + 1] Z) :=
    isPi_not_iff.2 (isSigma_iterate_jump_iff.2 hnm)
  have hmem' : IsSigma Z n (· ∈ Set.jump^[n + 1] Z) :=
    isPi_not_iff.1 (hsub hmem)
  exact (not_le_of_gt n.lt_succ_self) (isSigma_iterate_jump_iff.1 hmem')

/-- **Arithmetical Hierarchy Theorem (`Δ⁰` strictness).** Relative to every oracle `Z`, the
sequence of `Δ⁰ₙ₊₁(Z)` pointclasses on `ℕ` is strictly increasing in `n : ℕ`. -/
theorem strictMono_setOf_isDelta_succ (Z : Set ℕ) :
    StrictMono fun n => {p : ℕ → Prop | IsDelta Z (n + 1) p} := by
  intro n m hnm
  rw [Set.ssubset_def]
  refine ⟨fun _ hp => hp.of_le (Nat.succ_le_succ hnm.le), fun hsub => ?_⟩
  have hmem : IsDelta Z (n + 1) (· ∈ Set.jump^[n + 1] Z) :=
    hsub (isDelta_iterate_jump_iff.2 (Nat.succ_le_succ hnm))
  exact (not_le_of_gt (n + 1).lt_succ_self) (isDelta_iterate_jump_iff.1 hmem)

/-- At every positive level `n + 1`, `Δ⁰ₙ₊₁(Z)` is a proper subclass of `Σ⁰ₙ₊₁(Z)`. -/
theorem setOf_isDelta_ssubset_setOf_isSigma_succ (Z : Set ℕ) (n : ℕ) :
    {p : ℕ → Prop | IsDelta Z (n + 1) p} ⊂ {p : ℕ → Prop | IsSigma Z (n + 1) p} := by
  rw [Set.ssubset_def]
  exact ⟨fun _ hp => (isDelta_iff.1 hp).1, fun hsub =>
    not_isPi_succ_iterate_jump (isDelta_iff.1 (hsub isSigma_succ_iterate_jump)).2⟩

/-- At every positive level `n + 1`, `Δ⁰ₙ₊₁(Z)` is a proper subclass of `Π⁰ₙ₊₁(Z)`. -/
theorem setOf_isDelta_ssubset_setOf_isPi_succ (Z : Set ℕ) (n : ℕ) :
    {p : ℕ → Prop | IsDelta Z (n + 1) p} ⊂ {p : ℕ → Prop | IsPi Z (n + 1) p} := by
  rw [Set.ssubset_def]
  refine ⟨fun _ hp => (isDelta_iff.1 hp).2, fun hsub => ?_⟩
  have hcompl : IsPi Z (n + 1) (· ∉ Set.jump^[n + 1] Z) :=
    isPi_not_iff.2 isSigma_succ_iterate_jump
  exact not_isPi_succ_iterate_jump (isSigma_not_iff.1 (isDelta_iff.1 (hsub hcompl)).1)

/-- At every positive level `n + 1`, `Σ⁰ₙ₊₁(Z)` is not contained in `Π⁰ₙ₊₁(Z)`. -/
theorem not_setOf_isSigma_subset_setOf_isPi_succ (Z : Set ℕ) (n : ℕ) :
    ¬({p : ℕ → Prop | IsSigma Z (n + 1) p} ⊆ {p : ℕ → Prop | IsPi Z (n + 1) p}) :=
  fun hsub => not_isPi_succ_iterate_jump (hsub isSigma_succ_iterate_jump)

/-- At every positive level `n + 1`, `Π⁰ₙ₊₁(Z)` is not contained in `Σ⁰ₙ₊₁(Z)`. -/
theorem not_setOf_isPi_subset_setOf_isSigma_succ (Z : Set ℕ) (n : ℕ) :
    ¬({p : ℕ → Prop | IsPi Z (n + 1) p} ⊆ {p : ℕ → Prop | IsSigma Z (n + 1) p}) :=
  fun hsub =>
    not_isPi_succ_iterate_jump (isSigma_not_iff.1 (hsub (isPi_not_iff.2 isSigma_succ_iterate_jump)))

/-- At every positive level `n + 1`, `Σ⁰ₙ₊₁(Z) ∪ Π⁰ₙ₊₁(Z)` is a proper subclass of `Δ⁰ₙ₊₂(Z)`. -/
theorem setOf_isSigma_union_setOf_isPi_ssubset_setOf_isDelta_succ_succ (Z : Set ℕ) (n : ℕ) :
    {p : ℕ → Prop | IsSigma Z (n + 1) p} ∪ {p : ℕ → Prop | IsPi Z (n + 1) p} ⊂
      {p : ℕ → Prop | IsDelta Z (n + 2) p} := by
  rw [Set.ssubset_def]
  refine ⟨?_, fun hsub => ?_⟩
  · rintro p (hp | hp)
    · exact hp.delta_succ
    · exact hp.delta_succ
  · rcases hsub isDelta_succ_succ_turingJoin_compl_iterate_jump with hS | hP
    · exact not_isSigma_succ_turingJoin_compl_iterate_jump hS
    · exact not_isPi_succ_turingJoin_compl_iterate_jump hP

end TauCeti.ArithmeticalHierarchy
