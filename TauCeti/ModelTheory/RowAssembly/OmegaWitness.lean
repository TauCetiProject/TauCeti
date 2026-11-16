/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.BackAndForth
public import TauCeti.ModelTheory.Scott.Height
import TauCeti.ModelTheory.BackAndForth.PureSet
import TauCeti.GroupTheory.Perm.Basic

/-!
# A countable structure of internal Scott rank `ω` with a large level-`ω` class

This file constructs a countably infinite relational structure `OmegaWitness` in
`lang ℕ Language.empty` together with a family `OmegaCompanion z` (`z : ℕ → Bool`) of
countably infinite structures such that:

* `internalScottRank OmegaWitness = ω`: every finite tuple has finite orbit rank, because
  appending owner rows costs `n` levels, level `r + 2` pins every row of length at most `r` via
  pure-set fiber cardinalities, and slot-preserving permutations act transitively on tuples with
  matching slots and equality patterns; conversely, the staircase rows `[0, …, k]` and
  `[0, …, k, k]` are `BFEquiv k`-equivalent along their transposition yet non-automorphic, so
  orbit ranks are unbounded below `ω`.
* Every `OmegaCompanion z` is `BFEquiv ω`-equivalent to `OmegaWitness`: for each `m : ℕ`, a
  Hilbert-hotel shift of the tail prefixes of the path `companionPath z` from length `2 * m` on
  matches every fiber up to `BFEquiv m`.
* No `OmegaCompanion z` is isomorphic to `OmegaWitness`, and distinct `z ≠ z'` give
  non-isomorphic `OmegaCompanion z` and `OmegaCompanion z'`, because an isomorphism must preserve
  rows and fiber cardinalities.
* Consequently `ω < scottHeight OmegaWitness` (while `scottHeight OmegaWitness ≤ ω + ω`): the
  Scott height can strictly exceed the internal Scott rank.

## Main definitions

* `TauCeti.RowAssembly.PrefixRow`: nondecreasing finite words `p` over `ℕ` with `p[i] ≤ i`.
* `TauCeti.RowAssembly.prefixFiber` and `TauCeti.RowAssembly.OmegaWitness`: the base row assembly
  of internal Scott rank `ω`.
* `TauCeti.RowAssembly.companionPath`, `TauCeti.RowAssembly.pathPrefix`,
  `TauCeti.RowAssembly.companionFiber`, and `TauCeti.RowAssembly.OmegaCompanion`: the Cantor-space
  family of companions in the level-`ω` back-and-forth class of `OmegaWitness`.

## Main results

* `TauCeti.RowAssembly.internalScottRank_omegaWitness`: `internalScottRank OmegaWitness = ω`.
* `TauCeti.RowAssembly.bfEquiv_omega0_omegaCompanion_omegaWitness`: each `OmegaCompanion z` is
  `BFEquiv ω`-equivalent to `OmegaWitness`.
* `TauCeti.RowAssembly.isEmpty_equiv_omegaCompanion_omegaWitness` and
  `TauCeti.RowAssembly.isEmpty_equiv_omegaCompanion`: the companions are pairwise non-isomorphic
  and none is isomorphic to `OmegaWitness`.
* `TauCeti.RowAssembly.omega0_lt_scottHeight_omegaWitness`: `ω < scottHeight OmegaWitness`.
* `TauCeti.RowAssembly.exists_internalScottRank_omega_with_large_bfClass`: existential packaging
  of all properties above.

## References

Adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/ModelTheory/FiberExactOmega.lean`,
`InfinitaryLogic/ModelTheory/FiberCompanion.lean`,
`InfinitaryLogic/ModelTheory/FiberCompanionShift.lean`,
`InfinitaryLogic/ModelTheory/FiberCompanionEquiv.lean`,
`InfinitaryLogic/ModelTheory/FiberCompanionIso.lean`, and
`InfinitaryLogic/ModelTheory/FiberCantorFamily.lean` (checkpoint
`518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0).
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

/-! ### Prefix rows and the base structure -/

/-- A finite nondecreasing word `word` over `ℕ` whose `i`-th entry is at most `i`. -/
@[ext]
structure PrefixRow where
  /-- The underlying word of natural numbers. -/
  word : List ℕ
  /-- The word is nondecreasing. -/
  pairwise_le : word.Pairwise (· ≤ ·)
  /-- Each entry is bounded by its index. -/
  getElem_le : ∀ i : Fin word.length, word[i] ≤ i.1

instance : DecidableEq PrefixRow :=
  fun a b => decidable_of_iff (a.word = b.word) ⟨PrefixRow.ext, congrArg PrefixRow.word⟩

instance : Countable PrefixRow :=
  Function.Injective.countable (f := PrefixRow.word) fun _ _ h => PrefixRow.ext h

instance : Infinite PrefixRow :=
  Infinite.of_injective (fun k => ⟨List.replicate k 0,
      List.pairwise_replicate.mpr (Or.inr le_rfl), fun _ => by simp⟩)
    fun _ _ h => by simpa using congrArg (fun p : PrefixRow => p.word.length) h

/-- Every nonempty prefix `τ` of a `PrefixRow` satisfies `τ.getLast + 1 ≤ τ.length`. -/
private theorem getLast_add_one_le_length_of_prefix {p : PrefixRow} {τ : Label ℕ}
    (h : τ.1 <+: p.word) : τ.1.getLast τ.2 + 1 ≤ τ.1.length := by
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < τ.1.length := List.length_pos_of_ne_nil τ.2
  have hlen : τ.1.length - 1 < p.word.length := by rw [← ht, List.length_append]; omega
  rw [List.getLast_eq_getElem]
  have hget : τ.1[τ.1.length - 1] = p.word[τ.1.length - 1] := by
    simp only [← ht, List.getElem_append_left (by omega : τ.1.length - 1 < τ.1.length)]
  have hle : p.word[τ.1.length - 1] ≤ τ.1.length - 1 := by
    simpa only [Fin.getElem_fin] using p.getElem_le ⟨τ.1.length - 1, hlen⟩
  omega

/-- The fiber of `OmegaWitness` at row `p` and label `τ`: `Fin (last τ + 1)` when `τ` is a prefix
of `p.word`, and `ℕ` otherwise. -/
def prefixFiber (p : PrefixRow) (τ : Label ℕ) : Type :=
  if τ.1 <+: p.word then Fin (τ.1.getLast τ.2 + 1) else ℕ

instance (p : PrefixRow) (τ : Label ℕ) : Language.empty.Structure (prefixFiber p τ) :=
  Language.emptyStructure

instance (p : PrefixRow) (τ : Label ℕ) : Countable (prefixFiber p τ) := by
  unfold prefixFiber; split_ifs <;> infer_instance

private theorem enatCard_prefixFiber_of_prefix {p : PrefixRow} {τ : Label ℕ}
    (h : τ.1 <+: p.word) : ENat.card (prefixFiber p τ) = (τ.1.getLast τ.2 + 1 : ℕ) := by
  simp [prefixFiber, h]

private theorem enatCard_prefixFiber_of_not_prefix {p : PrefixRow} {τ : Label ℕ}
    (h : ¬ τ.1 <+: p.word) : ENat.card (prefixFiber p τ) = ⊤ := by
  simp [prefixFiber, h, ENat.card_eq_top_of_infinite]

/-- The base row assembly of internal Scott rank `ω`. -/
abbrev OmegaWitness : Type := Carrier PrefixRow prefixFiber

/-! ### Row pinning and the upper bound on internal Scott rank -/

/-- If two rows `p` and `q` are `BFEquiv k`-equivalent while `τ` is a prefix of `p` and not of `q`,
then `k ≤ τ.1.length`. -/
private theorem le_length_of_bfEquiv_of_prefix_of_not_prefix {p q : PrefixRow} {k : ℕ}
    (h : BFEquiv (L := lang ℕ Language.empty) (k : Ordinal.{0}) 1
      (![Carrier.row p] : Fin 1 → OmegaWitness) (![Carrier.row q] : Fin 1 → OmegaWitness))
    {τ : Label ℕ} (hp : τ.1 <+: p.word) (hq : ¬ τ.1 <+: q.word) :
    k ≤ τ.1.length := by
  have hfib := (bfEquiv_empty_elim0_natCast_iff k).mp (bfEquiv_fiber_elim0_of_bfEquiv_row h τ)
  rw [enatCard_prefixFiber_of_prefix hp, enatCard_prefixFiber_of_not_prefix hq,
    min_top_left] at hfib
  have hle : (k : ℕ∞) ≤ (τ.1.getLast τ.2 + 1 : ℕ) := hfib.symm ▸ min_le_left _ _
  exact (Nat.cast_le.mp hle).trans (getLast_add_one_le_length_of_prefix hp)

/-- If two row markers of `OmegaWitness` are `BFEquiv`-equivalent at level `p.word.length + 2`,
then they are equal. -/
theorem prefixRow_eq_of_bfEquiv {p q : PrefixRow}
    (h : BFEquiv (L := lang ℕ Language.empty) ((p.word.length + 2 : ℕ) : Ordinal.{0}) 1
      (![Carrier.row p] : Fin 1 → OmegaWitness) (![Carrier.row q] : Fin 1 → OmegaWitness)) :
    p = q := by
  have hpref : p.word <+: q.word := by
    by_cases hp : p.word = []
    · simp [hp]
    · by_contra hnp
      have hle := le_length_of_bfEquiv_of_prefix_of_not_prefix h
        (τ := ⟨p.word, hp⟩) List.prefix_rfl hnp
      dsimp only at hle; omega
  have hlen : q.word.length ≤ p.word.length := by
    by_contra hlt
    let w := q.word.take (p.word.length + 1)
    have hwlen : w.length = p.word.length + 1 := by
      simp [w, Nat.min_eq_left (Nat.succ_le_of_lt (lt_of_not_ge hlt))]
    have hle := le_length_of_bfEquiv_of_prefix_of_not_prefix h.symm
      (τ := ⟨w, List.ne_nil_of_length_pos (by omega)⟩) (List.take_prefix _ _)
      (fun hpre => by have := hpre.length_le; dsimp only at this; omega)
    dsimp only at hle; omega
  obtain ⟨t, ht⟩ := hpref
  have htlen : t.length = 0 := by have := congrArg List.length ht; simp at this; omega
  exact PrefixRow.ext (by simpa [List.eq_nil_of_length_eq_zero htlen] using ht)

/-- Every finite tuple of `OmegaWitness` has finite orbit rank. -/
theorem orbitRank_omegaWitness_lt_omega0 {n : ℕ} (a : Fin n → OmegaWitness) :
    orbitRank (L := lang ℕ Language.empty) a < Ordinal.omega0 := by
  let r : ℕ := Finset.univ.sup fun i : Fin n => (a i).ownerRow.word.length
  have hstable : ((r + 2 + n : ℕ) : Ordinal.{0}) ∈
      orbitStable (L := lang ℕ Language.empty) a := by
    rw [mem_orbitStable_iff_of_countable]
    intro b hab
    have hrow_eq (i : Fin n) : (a i).ownerRow = (b i).ownerRow := by
      have hab' : BFEquiv (L := lang ℕ Language.empty)
          (((r + 2 : ℕ) : Ordinal.{0}) + (n : ℕ)) n a b := by simpa only [Nat.cast_add] using hab
      have hri : (a i).ownerRow.word.length ≤ r :=
        Finset.le_sup (f := fun j : Fin n => (a j).ownerRow.word.length) (Finset.mem_univ i)
      exact prefixRow_eq_of_bfEquiv ((bfEquiv_ownerRow_of_bfEquiv_add hab' i).mono
        (Nat.cast_le.mpr (by omega : (a i).ownerRow.word.length + 2 ≤ r + 2)))
    have hslot (i : Fin n) : (a i).slot = (b i).slot := by
      cases hai : a i with
      | row p =>
        obtain ⟨q, hbi⟩ := (hab.sameAtomicType.rel_iff (.row : Sym ℕ Language.empty 1) ![i]).mp
          ⟨p, by simp [hai]⟩
        simp only [Function.comp_apply, Matrix.cons_val_zero] at hbi
        have hpq : p = q := by simpa [hai, hbi] using hrow_eq i
        rw [hbi, hpq]
      | pt p τ x =>
        obtain ⟨q, _, hbi⟩ := (hab.sameAtomicType.rel_iff (.lab τ : Sym ℕ Language.empty 1) ![i]).mp
          ⟨p, x, by simp [hai]⟩
        simp only [Function.comp_apply, Matrix.cons_val_zero] at hbi
        have hpq : p = q := by simpa [hai, hbi] using hrow_eq i
        simp [hbi, hpq]
    obtain ⟨σ, hσslot, hσab⟩ := exists_perm_apply_eq_of_eq_iff Carrier.slot
      (fun i j => hab.sameAtomicType.eq_iff i j) hslot
    exact ⟨equivOfSlotPerm σ hσslot,
      funext fun i => by simpa [equivOfSlotPerm_apply] using hσab i⟩
  exact (orbitRank_le a hstable).trans_lt (Ordinal.natCast_lt_omega0 _)

/-! ### Staircase rows and the lower bound on internal Scott rank -/

/-- The staircase word `[0, 1, …, k]`, of length `k + 1`. -/
private def staircaseRow (k : ℕ) : PrefixRow where
  word := List.range (k + 1)
  pairwise_le := List.pairwise_lt_range.imp fun h => h.le
  getElem_le i := by simp

/-- The extended staircase word `[0, 1, …, k, k]`, of length `k + 2`. -/
private def extendedStaircaseRow (k : ℕ) : PrefixRow where
  word := List.range (k + 1) ++ [k]
  pairwise_le := List.pairwise_append.mpr
    ⟨List.pairwise_lt_range.imp fun h => h.le, List.pairwise_singleton _ _,
      fun a ha b hb => by simp at ha hb; omega⟩
  getElem_le i := by
    dsimp only [Fin.getElem_fin]
    by_cases hi : i.1 < k + 1
    · rw [List.getElem_append_left (by simp [hi])]; simp
    · have hieq : i.1 = k + 1 := by have := i.2; simp at this; omega
      rw [List.getElem_append_right (by simp; omega)]; simp [hieq]

/-- Every proper prefix of `extendedStaircaseRow k` is a prefix of `staircaseRow k`. -/
private theorem prefix_staircaseRow_iff_of_ne (k : ℕ) {w : List ℕ}
    (hne : w ≠ (extendedStaircaseRow k).word) :
    w <+: (staircaseRow k).word ↔ w <+: (extendedStaircaseRow k).word := by
  refine ⟨fun h => h.trans (List.prefix_append _ _), fun ⟨t, ht⟩ => ?_⟩
  have hne_nil : t ≠ [] := fun hnil => hne (by simpa [hnil] using ht)
  have hlen : w.length ≤ (staircaseRow k).word.length := by
    have htpos : 0 < t.length := List.length_pos_of_ne_nil hne_nil
    have := congrArg List.length ht; simp [staircaseRow, extendedStaircaseRow] at this ⊢; omega
  have htake : w = (staircaseRow k).word.take w.length := by
    calc w = (w ++ t).take w.length := by simp
      _ = ((staircaseRow k).word ++ [k]).take w.length := by rw [ht]; rfl
      _ = (staircaseRow k).word.take w.length := List.take_append_of_le_length hlen
  exact htake ▸ List.take_prefix _ _

/-- The fibers of `staircaseRow k` and `extendedStaircaseRow k` are `BFEquiv k`-equivalent. -/
private theorem bfEquiv_staircase_fibers (k : ℕ) (τ : Label ℕ) :
    BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → prefixFiber (staircaseRow k) τ)
      (Fin.elim0 : Fin 0 → prefixFiber (extendedStaircaseRow k) τ) := by
  rw [bfEquiv_empty_elim0_natCast_iff]
  by_cases hτ : τ.1 = (extendedStaircaseRow k).word
  · have hnp : ¬ τ.1 <+: (staircaseRow k).word := fun hpre => by
      have := hpre.length_le; simp [hτ, staircaseRow, extendedStaircaseRow] at this
    have hp : τ.1 <+: (extendedStaircaseRow k).word := hτ ▸ List.prefix_rfl
    have hlast : τ.1.getLast τ.2 = k := by simp [hτ, extendedStaircaseRow]
    rw [enatCard_prefixFiber_of_not_prefix hnp, enatCard_prefixFiber_of_prefix hp, hlast,
      min_top_left, eq_comm, min_eq_right_iff]
    exact Nat.cast_le.mpr (Nat.le_succ k)
  · have hiff := prefix_staircaseRow_iff_of_ne k hτ
    by_cases hp : τ.1 <+: (staircaseRow k).word
    · rw [enatCard_prefixFiber_of_prefix hp, enatCard_prefixFiber_of_prefix (hiff.mp hp)]
    · rw [enatCard_prefixFiber_of_not_prefix hp,
        enatCard_prefixFiber_of_not_prefix (mt hiff.mpr hp)]

/-- The staircase rows `[0, …, k]` and `[0, …, k, k]` are `BFEquiv k`-equivalent in
`OmegaWitness`. -/
private theorem bfEquiv_staircaseRow (k : ℕ) :
    BFEquiv (L := lang ℕ Language.empty) (k : Ordinal.{0}) 1
      (![Carrier.row (staircaseRow k)] : Fin 1 → OmegaWitness)
      (![Carrier.row (extendedStaircaseRow k)] : Fin 1 → OmegaWitness) := by
  let eR := Equiv.swap (staircaseRow k) (extendedStaircaseRow k)
  have hF (p : PrefixRow) (τ : Label ℕ) :
      BFEquiv (L := Language.empty) (k : Ordinal.{0}) 0
        (Fin.elim0 : Fin 0 → prefixFiber p τ) (Fin.elim0 : Fin 0 → prefixFiber (eR p) τ) := by
    by_cases hp1 : p = staircaseRow k
    · subst hp1; rw [show eR _ = _ from Equiv.swap_apply_left _ _]
      exact bfEquiv_staircase_fibers k τ
    · by_cases hp2 : p = extendedStaircaseRow k
      · subst hp2; rw [show eR _ = _ from Equiv.swap_apply_right _ _]
        exact (bfEquiv_staircase_fibers k τ).symm
      · rw [show eR p = p from Equiv.swap_apply_of_ne_of_ne hp1 hp2]
  convert bfEquiv_rows_of_rowEquiv eR hF ![staircaseRow k] using 1 <;>
    (ext t; simp [Subsingleton.elim t 0, eR])

/-- No automorphism of `OmegaWitness` sends `staircaseRow k` to `extendedStaircaseRow k`. -/
private theorem not_aut_staircaseRow (k : ℕ) :
    ¬ ∃ σ : OmegaWitness ≃[lang ℕ Language.empty] OmegaWitness,
        σ ∘ (![Carrier.row (staircaseRow k)] : Fin 1 → OmegaWitness) =
          ![Carrier.row (extendedStaircaseRow k)] := by
  rintro ⟨σ, hσ⟩
  have hrow : rowEquiv σ (staircaseRow k) = extendedStaircaseRow k := by
    have h0 := congrFun hσ 0
    simpa [apply_row] using h0
  let τ : Label ℕ := ⟨(extendedStaircaseRow k).word, by simp [extendedStaircaseRow]⟩
  have hcard := ENat.card_congr (fiberEquiv σ (staircaseRow k) τ).toEquiv
  rw [hrow] at hcard
  have hnp : ¬ τ.1 <+: (staircaseRow k).word := fun hpre => by
    have := hpre.length_le; simp [τ, staircaseRow, extendedStaircaseRow] at this
  rw [enatCard_prefixFiber_of_not_prefix hnp,
    enatCard_prefixFiber_of_prefix List.prefix_rfl] at hcard
  exact ENat.natCast_ne_top _ hcard.symm

/-- The orbit rank of `staircaseRow k` in `OmegaWitness` strictly exceeds `k`. -/
private theorem k_lt_orbitRank_staircaseRow (k : ℕ) :
    (k : Ordinal.{0}) <
      orbitRank (L := lang ℕ Language.empty)
        (![Carrier.row (staircaseRow k)] : Fin 1 → OmegaWitness) :=
  lt_of_not_ge fun hle => not_aut_staircaseRow k <|
    (mem_orbitStable_iff_of_countable _ _).mp ((orbitRank_le_iff _ _).mp hle) _
      (bfEquiv_staircaseRow k)

/-- The internal Scott rank of `OmegaWitness` is `ω`. -/
theorem internalScottRank_omegaWitness :
    internalScottRank (L := lang ℕ Language.empty) OmegaWitness = Ordinal.omega0 :=
  le_antisymm
    (by rw [internalScottRank_le_iff]; exact fun _ a => orbitRank_omegaWitness_lt_omega0 a)
    (Ordinal.omega0_le.mpr fun k =>
      ((k_lt_orbitRank_staircaseRow k).trans (orbitRank_lt_internalScottRank _)).le)

/-! ### The Cantor family of companions in the level-`ω` class -/

/-- The infinite path associated to `z : ℕ → Bool`: `2 * n ↦ n` and
`2 * n + 1 ↦ n + (z n).toNat`. -/
def companionPath (z : ℕ → Bool) (i : ℕ) : ℕ :=
  i / 2 + if i % 2 = 0 then 0 else (z (i / 2)).toNat

@[simp]
theorem companionPath_two_mul (z : ℕ → Bool) (n : ℕ) : companionPath z (2 * n) = n := by
  simp [companionPath]

@[simp]
theorem companionPath_two_mul_add_one (z : ℕ → Bool) (n : ℕ) :
    companionPath z (2 * n + 1) = n + (z n).toNat := by
  unfold companionPath
  rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
  simp

/-- Every entry of `companionPath z` is bounded by its index. -/
theorem companionPath_le_self (z : ℕ → Bool) (i : ℕ) : companionPath z i ≤ i := by
  unfold companionPath; split_ifs <;> cases z (i / 2) <;> simp <;> omega

/-- `companionPath z` is nondecreasing. -/
theorem companionPath_mono (z : ℕ → Bool) : Monotone (companionPath z) := by
  intro i j hij
  unfold companionPath
  by_cases hdiv : i / 2 = j / 2
  · rw [hdiv]; split_ifs <;> omega
  · have hlt : i / 2 < j / 2 := Nat.lt_of_le_of_ne (Nat.div_le_div_right hij) hdiv
    have hb1 : (z (i / 2)).toNat ≤ 1 := by cases z (i / 2) <;> decide
    split_ifs <;> omega

/-- Distinct binary sequences induce distinct companion paths. -/
theorem companionPath_injective : Function.Injective companionPath :=
  fun z z' h => funext fun n => by
    have hval := congrFun h (2 * n + 1)
    simp only [companionPath_two_mul_add_one, add_right_inj] at hval
    cases hz : z n <;> cases hz' : z' n <;> simp_all

/-- The length-`k` initial prefix of `companionPath z`, as a `PrefixRow`. -/
def pathPrefix (z : ℕ → Bool) (k : ℕ) : PrefixRow where
  word := List.ofFn fun i : Fin k => companionPath z i.1
  pairwise_le := List.pairwise_iff_getElem.mpr fun _ _ _ _ hij => by
    simp only [List.getElem_ofFn]; exact companionPath_mono z hij.le
  getElem_le i := by
    simp only [Fin.getElem_fin, List.getElem_ofFn]
    exact companionPath_le_self z i.1

@[simp]
theorem pathPrefix_length (z : ℕ → Bool) (k : ℕ) : (pathPrefix z k).word.length = k := by
  simp [pathPrefix]

@[simp]
theorem pathPrefix_getElem (z : ℕ → Bool) (k i : ℕ) (hi : i < (pathPrefix z k).word.length) :
    (pathPrefix z k).word[i] = companionPath z i := by
  simp [pathPrefix]

private theorem isPrefix_pathPrefix_iff (z : ℕ → Bool) (w : List ℕ) (k : ℕ) :
    w <+: (pathPrefix z k).word ↔ w.length ≤ k ∧ w = (pathPrefix z w.length).word := by
  refine ⟨fun ⟨t, ht⟩ => ?_, fun ⟨hlen, hw⟩ => ?_⟩
  · have hlen : w.length ≤ k := by have := congrArg List.length ht; simp at this; omega
    refine ⟨hlen, List.ext_getElem (by simp) fun i hi₁ _ => ?_⟩
    have hget : w[i] = (pathPrefix z k).word[i]'(by simp; omega) := by
      simp only [← ht, List.getElem_append_left hi₁]
    simp [hget]
  · have htake : (pathPrefix z w.length).word = (pathPrefix z k).word.take w.length :=
      List.ext_getElem (by simp [Nat.min_eq_left hlen]) fun i _ _ => by simp [List.getElem_take]
    exact hw ▸ htake ▸ List.take_prefix _ _

private theorem getLast_pathPrefix (z : ℕ → Bool) {τ : Label ℕ}
    (h : τ.1 = (pathPrefix z τ.1.length).word) :
    τ.1.getLast τ.2 = companionPath z (τ.1.length - 1) := by
  have hpos : 0 < τ.1.length := List.length_pos_of_ne_nil τ.2
  rw [List.getLast_eq_getElem]
  have hlt : τ.1.length - 1 < (pathPrefix z τ.1.length).word.length := by simp; omega
  have hget := congrArg (fun l : List ℕ => l[τ.1.length - 1]?) h
  simp only [List.getElem?_eq_getElem (by omega : τ.1.length - 1 < τ.1.length),
    List.getElem?_eq_getElem hlt, pathPrefix_getElem, Option.some.injEq] at hget
  exact hget

/-- The fiber family for `OmegaCompanion z`: each `some p` keeps `prefixFiber p`, while the extra
row `none` follows the infinite path `companionPath z`. -/
def companionFiber (z : ℕ → Bool) : Option PrefixRow → Label ℕ → Type
  | some p, τ => prefixFiber p τ
  | none, τ =>
      if τ.1 = (pathPrefix z τ.1.length).word then Fin (τ.1.getLast τ.2 + 1) else ℕ

instance (z : ℕ → Bool) (r : Option PrefixRow) (τ : Label ℕ) :
    Language.empty.Structure (companionFiber z r τ) :=
  Language.emptyStructure

instance (z : ℕ → Bool) (r : Option PrefixRow) (τ : Label ℕ) :
    Countable (companionFiber z r τ) := by
  cases r with
  | some p => exact inferInstanceAs (Countable (prefixFiber p τ))
  | none => dsimp only [companionFiber]; split_ifs <;> infer_instance

private theorem enatCard_companionFiber_none_of_eq {z : ℕ → Bool} {τ : Label ℕ}
    (h : τ.1 = (pathPrefix z τ.1.length).word) :
    ENat.card (companionFiber z none τ) = (τ.1.getLast τ.2 + 1 : ℕ) := by
  dsimp only [companionFiber]; split_ifs; simp

private theorem enatCard_companionFiber_none_of_ne {z : ℕ → Bool} {τ : Label ℕ}
    (h : τ.1 ≠ (pathPrefix z τ.1.length).word) :
    ENat.card (companionFiber z none τ) = ⊤ := by
  simp [companionFiber, h, ENat.card_eq_top_of_infinite]

/-- The companion row assembly associated to `z : ℕ → Bool`. -/
abbrev OmegaCompanion (z : ℕ → Bool) : Type := Carrier (Option PrefixRow) (companionFiber z)

/-! ### Hilbert-hotel shift and level-`ω` equivalence -/

/-- Forward map of the Hilbert-hotel row bijection shifting the tail of `pathPrefix z` from
length `2 * m` onward. -/
private def shiftFun (z : ℕ → Bool) (m : ℕ) : Option PrefixRow → PrefixRow
  | none => pathPrefix z (2 * m)
  | some p =>
      if 2 * m ≤ p.word.length ∧ p = pathPrefix z p.word.length then
        pathPrefix z (p.word.length + 1)
      else p

/-- Inverse map of `shiftFun`. -/
private def shiftInv (z : ℕ → Bool) (m : ℕ) (p : PrefixRow) : Option PrefixRow :=
  if 2 * m ≤ p.word.length ∧ p = pathPrefix z p.word.length then
    if p.word.length = 2 * m then none else some (pathPrefix z (p.word.length - 1))
  else some p

/-- Hilbert-hotel bijection between `Option PrefixRow` and `PrefixRow` shifting the tail of
`pathPrefix z` from length `2 * m` onward. -/
private def shiftEquiv (z : ℕ → Bool) (m : ℕ) : Option PrefixRow ≃ PrefixRow where
  toFun := shiftFun z m
  invFun := shiftInv z m
  left_inv
    | none => by simp [shiftFun, shiftInv]
    | some p => by
      dsimp only [shiftFun, shiftInv]
      split_ifs with h1 h2 h3
      · simp only [pathPrefix_length] at h3; omega
      · simpa only [pathPrefix_length, Nat.add_sub_cancel] using congrArg some h1.2.symm
      · exact (h2 ⟨by simp; omega, by simp⟩).elim
      · rfl
  right_inv p := by
    dsimp only [shiftFun, shiftInv]
    split_ifs with h1 h2
    · simpa only [← h2] using h1.2.symm
    · dsimp only; split_ifs with hcond
      · simpa only [pathPrefix_length, show p.word.length - 1 + 1 = p.word.length by omega] using
          h1.2.symm
      · exact (hcond ⟨by simp; omega, by simp⟩).elim
    · dsimp only; split_ifs; rfl

/-- Every prefix of `companionPath z` of length strictly greater than `2 * m` has last entry at
least `m`. -/
private theorem le_getLast_add_one_of_two_mul_lt (z : ℕ → Bool) {m : ℕ} {τ : Label ℕ}
    (hτ : τ.1 = (pathPrefix z τ.1.length).word) (hlen : 2 * m < τ.1.length) :
    m ≤ τ.1.getLast τ.2 + 1 := by
  rw [getLast_pathPrefix z hτ]
  have hmono := companionPath_mono z (by omega : 2 * m ≤ τ.1.length - 1)
  rw [companionPath_two_mul] at hmono; omega

/-- Fiber matching at the extra path row `none` under `shiftEquiv z m`. -/
private theorem bfEquiv_shiftEquiv_fibers_none (z : ℕ → Bool) (m : ℕ) (τ : Label ℕ) :
    min (ENat.card (companionFiber z none τ)) (m : ℕ∞) =
      min (ENat.card (prefixFiber (pathPrefix z (2 * m)) τ)) (m : ℕ∞) := by
  by_cases hτ : τ.1 = (pathPrefix z τ.1.length).word
  · by_cases hlen : τ.1.length ≤ 2 * m
    · rw [enatCard_companionFiber_none_of_eq hτ,
        enatCard_prefixFiber_of_prefix ((isPrefix_pathPrefix_iff z τ.1 (2 * m)).mpr ⟨hlen, hτ⟩)]
    · have hnp : ¬ τ.1 <+: (pathPrefix z (2 * m)).word := by
        rw [isPrefix_pathPrefix_iff]; exact fun ⟨h1, _⟩ => hlen h1
      rw [enatCard_companionFiber_none_of_eq hτ, enatCard_prefixFiber_of_not_prefix hnp,
        min_top_left, min_eq_right_iff]
      exact Nat.cast_le.mpr (le_getLast_add_one_of_two_mul_lt z hτ (by omega))
  · have hnp : ¬ τ.1 <+: (pathPrefix z (2 * m)).word := by
      rw [isPrefix_pathPrefix_iff]; exact fun ⟨_, h2⟩ => hτ h2
    rw [enatCard_companionFiber_none_of_ne hτ, enatCard_prefixFiber_of_not_prefix hnp]

/-- Fiber matching along shifted tail prefixes `pathPrefix z k ↦ pathPrefix z (k + 1)` for
`2 * m ≤ k`. -/
private theorem bfEquiv_shiftEquiv_fibers_tail (z : ℕ → Bool) {m k : ℕ} (hlen : 2 * m ≤ k)
    (τ : Label ℕ) :
    min (ENat.card (prefixFiber (pathPrefix z k) τ)) (m : ℕ∞) =
      min (ENat.card (prefixFiber (pathPrefix z (k + 1)) τ)) (m : ℕ∞) := by
  by_cases hmatch : τ.1.length = k + 1 ∧ τ.1 = (pathPrefix z τ.1.length).word
  · have hnp : ¬ τ.1 <+: (pathPrefix z k).word := by rw [isPrefix_pathPrefix_iff]; omega
    have hpr : τ.1 <+: (pathPrefix z (k + 1)).word :=
      (isPrefix_pathPrefix_iff z τ.1 (k + 1)).mpr ⟨by omega, hmatch.2⟩
    rw [enatCard_prefixFiber_of_not_prefix hnp, enatCard_prefixFiber_of_prefix hpr,
      min_top_left, eq_comm, min_eq_right_iff]
    exact Nat.cast_le.mpr (le_getLast_add_one_of_two_mul_lt z hmatch.2 (by omega))
  · have hiff : τ.1 <+: (pathPrefix z k).word ↔ τ.1 <+: (pathPrefix z (k + 1)).word := by
      simp only [isPrefix_pathPrefix_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.le_succ_of_le h1, h2⟩, fun ⟨h1, h2⟩ =>
        ⟨Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h1 fun heq => hmatch ⟨heq, h2⟩), h2⟩⟩
    by_cases hpr : τ.1 <+: (pathPrefix z k).word
    · rw [enatCard_prefixFiber_of_prefix hpr, enatCard_prefixFiber_of_prefix (hiff.mp hpr)]
    · rw [enatCard_prefixFiber_of_not_prefix hpr,
        enatCard_prefixFiber_of_not_prefix (mt hiff.mpr hpr)]

/-- Along `shiftEquiv z m`, every corresponding pair of fibers is `BFEquiv m`-equivalent. -/
private theorem bfEquiv_shiftEquiv_fibers (z : ℕ → Bool) (m : ℕ)
    (r : Option PrefixRow) (τ : Label ℕ) :
    BFEquiv (L := Language.empty) (m : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → companionFiber z r τ)
      (Fin.elim0 : Fin 0 → prefixFiber (shiftEquiv z m r) τ) := by
  rw [bfEquiv_empty_elim0_natCast_iff]
  cases r with
  | none => exact bfEquiv_shiftEquiv_fibers_none z m τ
  | some p =>
    dsimp only [shiftEquiv, Equiv.coe_fn_mk, shiftFun]
    split_ifs with hp
    · rcases hp with ⟨hlen, hpeq⟩
      rw [show companionFiber z (some p) τ = prefixFiber (pathPrefix z p.word.length) τ from
        congrArg (fun r => prefixFiber r τ) hpeq]
      exact bfEquiv_shiftEquiv_fibers_tail z hlen τ
    · rfl

/-- Every companion `OmegaCompanion z` is `BFEquiv ω`-equivalent to `OmegaWitness`. -/
theorem bfEquiv_omega0_omegaCompanion_omegaWitness (z : ℕ → Bool) :
    BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
      (Fin.elim0 : Fin 0 → OmegaCompanion z) (Fin.elim0 : Fin 0 → OmegaWitness) := by
  refine (BFEquiv.limit Ordinal.isSuccLimit_omega0 _ _).mpr fun β hβ => ?_
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact bfEquiv_elim0_of_rowEquiv (shiftEquiv z m) (bfEquiv_shiftEquiv_fibers z m)

/-! ### Non-isomorphism and Scott height separation -/

/-- No finite row `p : PrefixRow` can match the path row `none` of `OmegaCompanion z` fiberwise. -/
private theorem false_of_fiberEquiv_none_some (z : ℕ → Bool) (p : PrefixRow)
    (hF : ∀ τ,
      Nonempty (companionFiber z none τ ≃[Language.empty] prefixFiber p τ)) : False := by
  let τ : Label ℕ := ⟨(pathPrefix z (p.word.length + 1)).word, List.ne_nil_of_length_pos (by simp)⟩
  have hτnp : ¬ τ.1 <+: p.word := fun hpre => by have := hpre.length_le; simp [τ] at this
  obtain ⟨e⟩ := hF τ
  have hcard := ENat.card_congr e.toEquiv
  rw [enatCard_companionFiber_none_of_eq (by simp [τ]),
    enatCard_prefixFiber_of_not_prefix hτnp] at hcard
  exact ENat.natCast_ne_top _ hcard

/-- No companion `OmegaCompanion z` is isomorphic to `OmegaWitness`. -/
theorem isEmpty_equiv_omegaCompanion_omegaWitness (z : ℕ → Bool) :
    IsEmpty (OmegaCompanion z ≃[lang ℕ Language.empty] OmegaWitness) :=
  ⟨fun e => false_of_fiberEquiv_none_some z (rowEquiv e none) fun τ => ⟨fiberEquiv e none τ⟩⟩

/-- Distinct sequences `z ≠ z'` produce non-isomorphic companions. -/
theorem isEmpty_equiv_omegaCompanion {z z' : ℕ → Bool} (hz : z ≠ z') :
    IsEmpty (OmegaCompanion z ≃[lang ℕ Language.empty] OmegaCompanion z') := ⟨fun e => by
  cases hrow : rowEquiv e none with
  | some p =>
    exact false_of_fiberEquiv_none_some z p fun τ => by
      have he := fiberEquiv e none τ; rw [hrow] at he; exact ⟨he⟩
  | none =>
    obtain ⟨n, hn⟩ := Function.ne_iff.mp (companionPath_injective.ne hz)
    let τ : Label ℕ := ⟨(pathPrefix z (n + 1)).word, List.ne_nil_of_length_pos (by simp)⟩
    have hτz' : τ.1 ≠ (pathPrefix z' τ.1.length).word := fun heq => by
      have hget := congrArg (fun l : List ℕ => l[n]?) heq
      simp only [τ, pathPrefix_length,
        List.getElem?_eq_getElem (by simp : n < (pathPrefix z (n + 1)).word.length),
        List.getElem?_eq_getElem (by simp : n < (pathPrefix z' (n + 1)).word.length),
        pathPrefix_getElem, Option.some.injEq] at hget
      exact hn hget
    have he := fiberEquiv e none τ
    rw [hrow] at he
    have hcard := ENat.card_congr he.toEquiv
    rw [enatCard_companionFiber_none_of_eq (by simp [τ]),
      enatCard_companionFiber_none_of_ne hτz'] at hcard
    exact ENat.natCast_ne_top _ hcard⟩

/-- The Scott height of `OmegaWitness` strictly exceeds `ω`, even though its internal Scott rank
is `ω`. -/
theorem omega0_lt_scottHeight_omegaWitness :
    Ordinal.omega0 < scottHeight (L := lang ℕ Language.empty) OmegaWitness :=
  lt_of_not_ge fun hle =>
    let ⟨e⟩ := nonempty_equiv_of_bfEquiv_of_scottHeight_le hle
      (bfEquiv_omega0_omegaCompanion_omegaWitness (fun _ => false)).symm
    (isEmpty_equiv_omegaCompanion_omegaWitness (fun _ => false)).false e.symm

/-- The Scott height of `OmegaWitness` is at most `ω + ω`. -/
theorem scottHeight_omegaWitness_le :
    scottHeight (L := lang ℕ Language.empty) OmegaWitness ≤
      Ordinal.omega0 + Ordinal.omega0 := by
  simpa only [internalScottRank_omegaWitness] using
    scottHeight_le_internalScottRank_add_omega0 (L := lang ℕ Language.empty) OmegaWitness

/-- **A countable structure of internal Scott rank `ω` with a Cantor-sized level-`ω` class.**
There is a countable structure of internal Scott rank `ω` whose Scott height exceeds `ω`, together
with a Cantor-space family of countable structures that are pairwise non-isomorphic, none
isomorphic to it, and all `BFEquiv ω`-equivalent to it. -/
theorem exists_internalScottRank_omega_with_large_bfClass :
    ∃ (M : Type) (_ : (lang ℕ Language.empty).Structure M) (_ : Countable M)
      (N : (ℕ → Bool) → Type) (_ : ∀ z, (lang ℕ Language.empty).Structure (N z))
      (_ : ∀ z, Countable (N z)),
      internalScottRank (L := lang ℕ Language.empty) M = Ordinal.omega0 ∧
      Ordinal.omega0 < scottHeight (L := lang ℕ Language.empty) M ∧
      (∀ z, BFEquiv (L := lang ℕ Language.empty) Ordinal.omega0.{0} 0
        (Fin.elim0 : Fin 0 → N z) (Fin.elim0 : Fin 0 → M)) ∧
      (∀ z, IsEmpty (N z ≃[lang ℕ Language.empty] M)) ∧
      (∀ z z', z ≠ z' → IsEmpty (N z ≃[lang ℕ Language.empty] N z')) :=
  ⟨OmegaWitness, inferInstance, inferInstance, OmegaCompanion, fun _ => inferInstance,
    fun _ => inferInstance, internalScottRank_omegaWitness, omega0_lt_scottHeight_omegaWitness,
    bfEquiv_omega0_omegaCompanion_omegaWitness, isEmpty_equiv_omegaCompanion_omegaWitness,
    fun _ _ h => isEmpty_equiv_omegaCompanion h⟩

end TauCeti.RowAssembly
