/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Hierarchy.One
import Mathlib.Order.Interval.Finset.Nat
import TauCeti.Computability.SingleOracle.Padding
import TauCeti.Computability.SingleOracle.Prefix
import TauCeti.Computability.SingleOracle.Recursion

/-!
# The finite-domain and infinite-domain index sets

For an oracle `Z : Set ℕ`, `finiteDomain Z` (`FIN` relative to `Z`) is the set of program numbers
`e` whose computation relative to `Z.oracle` halts on only finitely many inputs, and
`infiniteDomain Z` (`INF` relative to `Z`) is its complement, the set of program numbers whose
domain relative to `Z.oracle` is infinite.

We establish the exact arithmetical classifications and completeness properties of both index sets
(Soare, Theorem IV.3.2):
* `finiteDomain Z` is Σ⁰₂ relative to `Z` (`isSigma_two_finiteDomain`), because a subset of `ℕ` is
  finite precisely when some strict upper bound excludes every halting input at or above it, and
  bounded-versus-divergent matrix membership is Π⁰₁ relative to `Z` via the universal oracle
  program.
* `infiniteDomain Z` is Π⁰₂ relative to `Z` (`isPi_two_infiniteDomain`).
* Every predicate in Σ⁰₂ relative to `Z` on any primitive-codable type reduces one-one (by an
  ordinary primitive recursive injection, independently of the computability of `Z`) to
  `finiteDomain Z` (`IsSigma.oneOneReducible_finiteDomain`), using `Code.prefixDom` and
  `Code.curry` to turn existential Π⁰₁ witnesses into finite initial-segment domains.
* Every predicate in Π⁰₂ relative to `Z` reduces one-one to `infiniteDomain Z`
  (`IsPi.oneOneReducible_infiniteDomain`), characterizing Σ⁰₂ and Π⁰₂ relative to `Z` by both
  many-one and one-one reducibility.
* By Rogers' fixed-point theorem (`Code.fixed_point`), neither index set reduces many-one to the
  other (`not_manyOneReducible_infiniteDomain_finiteDomain`). Consequently `finiteDomain Z` is not
  Π⁰₂ relative to `Z`, `infiniteDomain Z` is not Σ⁰₂ relative to `Z`, neither is Δ⁰₂, Σ⁰₁, or
  Π⁰₁, and neither reduces many-one to `Z.jump`.
* At the empty oracle, `finiteDomain ∅` and `infiniteDomain ∅` are one-one equivalent to the
  finite-domain and infinite-domain predicates on ordinary `Nat.Partrec.Code` programs.

## Main definitions

* `TauCeti.ArithmeticalHierarchy.finiteDomain`: the index set `FIN` of oracle programs with finite
  domain relative to `Z`.
* `TauCeti.ArithmeticalHierarchy.infiniteDomain`: the index set `INF` of oracle programs with
  infinite domain relative to `Z`.

## Main results

* `TauCeti.ArithmeticalHierarchy.isSigma_two_finiteDomain`,
  `TauCeti.ArithmeticalHierarchy.isPi_two_infiniteDomain`: upper classifications in Σ⁰₂ and Π⁰₂.
* `TauCeti.ArithmeticalHierarchy.IsSigma.oneOneReducible_finiteDomain`,
  `TauCeti.ArithmeticalHierarchy.isSigma_two_iff_manyOneReducible_finiteDomain`,
  `TauCeti.ArithmeticalHierarchy.isSigma_two_iff_oneOneReducible_finiteDomain`: one-one and
  many-one Σ⁰₂-completeness of `finiteDomain Z`.
* `TauCeti.ArithmeticalHierarchy.IsPi.oneOneReducible_infiniteDomain`,
  `TauCeti.ArithmeticalHierarchy.isPi_two_iff_manyOneReducible_infiniteDomain`,
  `TauCeti.ArithmeticalHierarchy.isPi_two_iff_oneOneReducible_infiniteDomain`: one-one and
  many-one Π⁰₂-completeness of `infiniteDomain Z`.
* `TauCeti.ArithmeticalHierarchy.not_isPi_two_finiteDomain`,
  `TauCeti.ArithmeticalHierarchy.not_isSigma_two_infiniteDomain`,
  `TauCeti.ArithmeticalHierarchy.not_manyOneReducible_finiteDomain_jump`,
  `TauCeti.ArithmeticalHierarchy.not_manyOneReducible_infiniteDomain_jump`: exactness and
  strictness above `Z.jump`.
* `TauCeti.ArithmeticalHierarchy.oneOneEquiv_finite_dom_eval_finiteDomain_empty`,
  `TauCeti.ArithmeticalHierarchy.oneOneEquiv_infinite_dom_eval_infiniteDomain_empty`: one-one
  equivalence with the ordinary `Nat.Partrec.Code` index sets at `Z = ∅`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.3
  (Theorem IV.3.2).
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-! ### Index-set definitions, complements, extensionality, and witnesses -/

/-- The **finite-domain index set** (`FIN` relative to `Z`): the numbers `e` of single-oracle
programs whose domain relative to `Z.oracle` is finite. -/
def finiteDomain (Z : Set ℕ) : Set ℕ :=
  {e | {x | (Code.eval Z.oracle (ofNat Code e) x).Dom}.Finite}

/-- The **infinite-domain index set** (`INF` relative to `Z`): the numbers `e` of single-oracle
programs whose domain relative to `Z.oracle` is infinite. -/
def infiniteDomain (Z : Set ℕ) : Set ℕ :=
  {e | {x | (Code.eval Z.oracle (ofNat Code e) x).Dom}.Infinite}

/-- A number belongs to `finiteDomain Z` precisely when the numbered program halts on finitely many
inputs relative to `Z`. -/
@[simp]
theorem mem_finiteDomain {e : ℕ} :
    e ∈ finiteDomain Z ↔ {x | (Code.eval Z.oracle (ofNat Code e) x).Dom}.Finite :=
  Iff.rfl

/-- A number belongs to `infiniteDomain Z` precisely when the numbered program halts on infinitely
many inputs relative to `Z`. -/
@[simp]
theorem mem_infiniteDomain {e : ℕ} :
    e ∈ infiniteDomain Z ↔ {x | (Code.eval Z.oracle (ofNat Code e) x).Dom}.Infinite :=
  Iff.rfl

/-- Non-membership in `finiteDomain Z` is membership in `infiniteDomain Z`. -/
theorem notMem_finiteDomain {e : ℕ} : e ∉ finiteDomain Z ↔ e ∈ infiniteDomain Z :=
  Iff.rfl

/-- Non-membership in `infiniteDomain Z` is membership in `finiteDomain Z`. -/
theorem notMem_infiniteDomain {e : ℕ} : e ∉ infiniteDomain Z ↔ e ∈ finiteDomain Z := by
  classical
  exact not_not

/-- The complement of `finiteDomain Z` is `infiniteDomain Z`. -/
@[simp]
theorem compl_finiteDomain (Z : Set ℕ) : (finiteDomain Z)ᶜ = infiniteDomain Z :=
  Set.ext fun _ => notMem_finiteDomain

/-- The complement of `infiniteDomain Z` is `finiteDomain Z`. -/
@[simp]
theorem compl_infiniteDomain (Z : Set ℕ) : (infiniteDomain Z)ᶜ = finiteDomain Z :=
  Set.ext fun _ => notMem_infiniteDomain

/-- `finiteDomain Z` and `infiniteDomain Z` are disjoint. -/
theorem disjoint_finiteDomain_infiniteDomain (Z : Set ℕ) :
    Disjoint (finiteDomain Z) (infiniteDomain Z) :=
  Set.disjoint_left.2 fun _ hfin hinf => hinf hfin

/-- A program number lies in `finiteDomain Z` if and only if its halting domain is bounded above
in `ℕ`. -/
theorem mem_finiteDomain_iff_bddAbove {e : ℕ} :
    e ∈ finiteDomain Z ↔ BddAbove {x | (Code.eval Z.oracle (ofNat Code e) x).Dom} :=
  Set.finite_iff_bddAbove

/-- A program number lies in `finiteDomain Z` if and only if the program diverges on every input
from some threshold onward. -/
theorem mem_finiteDomain_iff_exists_bound {e : ℕ} :
    e ∈ finiteDomain Z ↔
      ∃ b, ∀ x, b ≤ x → ¬(Code.eval Z.oracle (ofNat Code e) x).Dom := by
  rw [mem_finiteDomain_iff_bddAbove, bddAbove_def]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, fun x hbx hdom => by have := hm x hdom; omega⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, fun x hdom => ?_⟩
    by_contra hlt
    exact hb x (by omega) hdom

/-- A program number lies in `infiniteDomain Z` if and only if the program halts on arbitrarily
large inputs. -/
theorem mem_infiniteDomain_iff_forall_exists_ge {e : ℕ} :
    e ∈ infiniteDomain Z ↔
      ∀ b, ∃ x, b ≤ x ∧ (Code.eval Z.oracle (ofNat Code e) x).Dom := by
  classical
  rw [← notMem_finiteDomain, mem_finiteDomain_iff_exists_bound]
  push Not
  rfl

/-- Membership in `finiteDomain Z` depends only on the domain of the evaluated program. -/
theorem mem_finiteDomain_congr {d e : ℕ}
    (h : ∀ x, (Code.eval Z.oracle (ofNat Code d) x).Dom ↔
      (Code.eval Z.oracle (ofNat Code e) x).Dom) :
    d ∈ finiteDomain Z ↔ e ∈ finiteDomain Z := by
  have hset : {x | (Code.eval Z.oracle (ofNat Code d) x).Dom} =
      {x | (Code.eval Z.oracle (ofNat Code e) x).Dom} :=
    Set.ext h
  simp [mem_finiteDomain, hset]

/-- Membership in `infiniteDomain Z` depends only on the domain of the evaluated program. -/
theorem mem_infiniteDomain_congr {d e : ℕ}
    (h : ∀ x, (Code.eval Z.oracle (ofNat Code d) x).Dom ↔
      (Code.eval Z.oracle (ofNat Code e) x).Dom) :
    d ∈ infiniteDomain Z ↔ e ∈ infiniteDomain Z := by
  rw [← notMem_finiteDomain, ← notMem_finiteDomain, mem_finiteDomain_congr h]

/-- Query-free codes retain their finite-domain property under any oracle `Z`. -/
theorem encode_toSingleOracleCode_mem_finiteDomain_iff (Z : Set ℕ) (c : Nat.Partrec.Code) :
    encode c.toSingleOracleCode ∈ finiteDomain Z ↔ {x | (c.eval x).Dom}.Finite := by
  simp

/-- Query-free codes retain their infinite-domain property under any oracle `Z`. -/
theorem encode_toSingleOracleCode_mem_infiniteDomain_iff (Z : Set ℕ) (c : Nat.Partrec.Code) :
    encode c.toSingleOracleCode ∈ infiniteDomain Z ↔ {x | (c.eval x).Dom}.Infinite := by
  simp

/-- The basic `zero` program halts on every input, witnessing nonemptiness of `infiniteDomain Z`. -/
theorem encode_zero_mem_infiniteDomain (Z : Set ℕ) :
    encode Code.zero ∈ infiniteDomain Z := by
  simpa [mem_infiniteDomain] using Set.infinite_univ

/-- The everywhere-divergent search program `rfind' (comp succ zero)` has empty domain, witnessing
nonemptiness of `finiteDomain Z`. -/
theorem encode_rfind'_succ_zero_mem_finiteDomain (Z : Set ℕ) :
    encode (Code.rfind' (Code.comp Code.succ Code.zero)) ∈ finiteDomain Z := by
  have hs : Code.eval Z.oracle Code.succ = fun n => Part.some (n + 1) := funext Code.eval_succ
  rw [mem_finiteDomain, ofNat_encode]
  refine Set.finite_empty.subset fun x hx => ?_
  rw [Set.mem_ofPred, ← Nat.pair_unpair x, Code.eval_rfind'] at hx
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hx
  obtain ⟨k, hk, -⟩ := (Part.mem_map_iff _).1 hy
  have hspec := Nat.rfind_spec hk
  simp [hs] at hspec

/-- `finiteDomain Z` contains infinitely many distinct program indices. -/
theorem infinite_finiteDomain (Z : Set ℕ) : (finiteDomain Z).Infinite := by
  let c₀ := Code.rfind' (Code.comp Code.succ Code.zero)
  refine Set.infinite_of_injective_forall_mem
      (f := fun n => encode (Code.pad c₀ n)) ?_ fun n => ?_
  · intro m n h
    exact (Code.pad_inj.1 (encode_injective h)).2
  · exact (mem_finiteDomain_congr fun x => by simp [c₀]).2
      (encode_rfind'_succ_zero_mem_finiteDomain Z)

/-- `infiniteDomain Z` contains infinitely many distinct program indices. -/
theorem infinite_infiniteDomain (Z : Set ℕ) : (infiniteDomain Z).Infinite := by
  refine Set.infinite_of_injective_forall_mem
      (f := fun n => encode (Code.pad Code.zero n)) ?_ fun n => ?_
  · intro m n h
    exact (Code.pad_inj.1 (encode_injective h)).2
  · exact (mem_infiniteDomain_congr fun x => by simp).2 (encode_zero_mem_infiniteDomain Z)

/-! ### Upper classifications in the arithmetical hierarchy -/

/-- **Upper classification of `FIN`.** The finite-domain index set relative to `Z` is Σ⁰₂ relative
to `Z`. -/
theorem isSigma_two_finiteDomain : IsSigma Z 2 (· ∈ finiteDomain Z) := by
  have hlt : IsPi Z 1 (fun a : (ℕ × ℕ) × ℕ => a.2 < a.1.2) := by
    refine (isPi_zero_iff.2 (isSigma_zero_iff.2
      ⟨fun a : (ℕ × ℕ) × ℕ => decide (a.2 < a.1.2), ?_,
        fun a => decide_eq_true_iff⟩)).succ
    exact (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide.computableIn
  have hnotdom : IsPi Z 1
      (fun a : (ℕ × ℕ) × ℕ => ¬(Code.eval Z.oracle (ofNat Code a.1.1) a.2).Dom) := by
    rw [isPi_not_iff]
    have hpair : Primrec fun a : (ℕ × ℕ) × ℕ => Nat.pair a.1.1 a.2 :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    refine ((isSigma_one_dom_eval Code.universal).preimage hpair.computableIn).of_eq fun a => ?_
    rw [Z.oracle_eq_indicator, Code.eval_universal]
  refine isSigma_succ_iff.2
    ⟨fun p => ∀ x, x < p.2 ∨ ¬(Code.eval Z.oracle (ofNat Code p.1) x).Dom,
      (hlt.or hnotdom).forall_nat, fun e => ?_⟩
  rw [mem_finiteDomain_iff_exists_bound]
  exact exists_congr fun b => forall_congr' fun x => by
    rcases lt_or_ge x b with hxb | hbx
    · simp [hxb, not_le.2 hxb]
    · simp [not_lt.2 hbx, hbx]

/-- **Upper classification of `INF`.** The infinite-domain index set relative to `Z` is Π⁰₂
relative to `Z`. -/
theorem isPi_two_infiniteDomain : IsPi Z 2 (· ∈ infiniteDomain Z) :=
  (isPi_not_iff.2 isSigma_two_finiteDomain).of_eq fun _ => notMem_finiteDomain

/-! ### One-one and many-one completeness -/

/-- **One-one Σ⁰₂-completeness of `FIN`** (Soare, Theorem IV.3.2). Every predicate in Σ⁰₂ relative
to `Z` on any primitive-codable type reduces one-one to `finiteDomain Z` by an ordinary computable
injection. -/
theorem IsSigma.oneOneReducible_finiteDomain (hp : IsSigma Z 2 p) :
    OneOneReducible p (· ∈ finiteDomain Z) := by
  classical
  obtain ⟨q, hq, hpq⟩ := isSigma_succ_iff.1 hp
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 (isSigma_not_iff.2 hq)
  let f : α → ℕ := fun x => encode (Code.prefixDom (Code.curry c (encode x)))
  have hf : Primrec f :=
    Primrec.encode.comp
      (Code.primrec_prefixDom.comp (Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode))
  refine ⟨f, hf.to_comp, ?_, fun x => ?_⟩
  · intro x₁ x₂ h
    have hcur := Code.prefixDom_inj.1 (encode_injective h)
    exact encode_injective (Code.curry_inj.1 hcur).2
  · rw [hpq x]
    simp only [f, mem_finiteDomain, ofNat_encode, Code.finite_dom_eval_prefixDom_iff,
      Code.eval_curry]
    refine exists_congr fun y => ?_
    have hcy := hc (x, y)
    simp only [encode_prod_val, encode_nat] at hcy
    exact (not_iff_comm.1 hcy).symm

/-- Every Σ⁰₂ predicate relative to `Z` reduces many-one to `finiteDomain Z`. -/
theorem IsSigma.manyOneReducible_finiteDomain (hp : IsSigma Z 2 p) :
    ManyOneReducible p (· ∈ finiteDomain Z) :=
  hp.oneOneReducible_finiteDomain.to_many_one

/-- Many-one reducibility to `finiteDomain Z` characterizes Σ⁰₂ membership relative to `Z`. -/
theorem isSigma_two_iff_manyOneReducible_finiteDomain :
    IsSigma Z 2 p ↔ ManyOneReducible p (· ∈ finiteDomain Z) := by
  refine ⟨IsSigma.manyOneReducible_finiteDomain, ?_⟩
  rintro ⟨f, hf, hpf⟩
  exact (isSigma_two_finiteDomain.preimage hf.computableIn).of_eq fun x => (hpf x).symm

/-- One-one reducibility to `finiteDomain Z` characterizes Σ⁰₂ membership relative to `Z`. -/
theorem isSigma_two_iff_oneOneReducible_finiteDomain :
    IsSigma Z 2 p ↔ OneOneReducible p (· ∈ finiteDomain Z) :=
  ⟨IsSigma.oneOneReducible_finiteDomain,
    fun h => isSigma_two_iff_manyOneReducible_finiteDomain.2 h.to_many_one⟩

/-- **One-one Π⁰₂-completeness of `INF`** (Soare, Theorem IV.3.2). Every predicate in Π⁰₂ relative
to `Z` on any primitive-codable type reduces one-one to `infiniteDomain Z` by an ordinary
computable injection. -/
theorem IsPi.oneOneReducible_infiniteDomain (hp : IsPi Z 2 p) :
    OneOneReducible p (· ∈ infiniteDomain Z) := by
  classical
  obtain ⟨f, hf, hinj, hiff⟩ := (isSigma_not_iff.2 hp).oneOneReducible_finiteDomain
  refine ⟨f, hf, hinj, fun x => ?_⟩
  dsimp only at hiff ⊢
  rw [← notMem_finiteDomain, ← hiff x, not_not]

/-- Every Π⁰₂ predicate relative to `Z` reduces many-one to `infiniteDomain Z`. -/
theorem IsPi.manyOneReducible_infiniteDomain (hp : IsPi Z 2 p) :
    ManyOneReducible p (· ∈ infiniteDomain Z) :=
  hp.oneOneReducible_infiniteDomain.to_many_one

/-- Many-one reducibility to `infiniteDomain Z` characterizes Π⁰₂ membership relative to `Z`. -/
theorem isPi_two_iff_manyOneReducible_infiniteDomain :
    IsPi Z 2 p ↔ ManyOneReducible p (· ∈ infiniteDomain Z) := by
  refine ⟨IsPi.manyOneReducible_infiniteDomain, ?_⟩
  rintro ⟨f, hf, hpf⟩
  exact (isPi_two_infiniteDomain.preimage hf.computableIn).of_eq fun x => (hpf x).symm

/-- One-one reducibility to `infiniteDomain Z` characterizes Π⁰₂ membership relative to `Z`. -/
theorem isPi_two_iff_oneOneReducible_infiniteDomain :
    IsPi Z 2 p ↔ OneOneReducible p (· ∈ infiniteDomain Z) :=
  ⟨IsPi.oneOneReducible_infiniteDomain,
    fun h => isPi_two_iff_manyOneReducible_infiniteDomain.2 h.to_many_one⟩

/-! ### Exactness, non-self-duality, and strictness above the halting set -/

/-- `infiniteDomain Z` does not reduce many-one to `finiteDomain Z`: a computable reduction would
induce a program transformation contradicting Rogers' fixed-point theorem. -/
theorem not_manyOneReducible_infiniteDomain_finiteDomain :
    ¬ManyOneReducible (· ∈ infiniteDomain Z) (· ∈ finiteDomain Z) := by
  rintro ⟨f, hf, hiff⟩
  have hg : Computable fun c : Code => ofNat Code (f (encode c)) :=
    (Computable.ofNat Code).comp (hf.comp Computable.encode)
  obtain ⟨c, hc⟩ := Code.fixed_point hg
  have heval : Code.eval Z.oracle (ofNat Code (f (encode c))) =
      Code.eval Z.oracle (ofNat Code (encode c)) := by
    rw [Z.oracle_eq_indicator, ofNat_encode]
    exact hc (Z.indicator 1)
  have hsame : f (encode c) ∈ finiteDomain Z ↔ encode c ∈ finiteDomain Z :=
    mem_finiteDomain_congr fun x => by rw [heval]
  exact not_iff_self ((notMem_finiteDomain.trans (hiff (encode c))).trans hsame)

/-- `finiteDomain Z` does not reduce many-one to `infiniteDomain Z`. -/
theorem not_manyOneReducible_finiteDomain_infiniteDomain :
    ¬ManyOneReducible (· ∈ finiteDomain Z) (· ∈ infiniteDomain Z) := by
  rintro ⟨f, hf, hiff⟩
  refine not_manyOneReducible_infiniteDomain_finiteDomain (Z := Z) ⟨f, hf, fun e => ?_⟩
  classical
  dsimp only at hiff ⊢
  rw [← notMem_finiteDomain, hiff e, notMem_infiniteDomain]

/-- **Exactness for `FIN`.** `finiteDomain Z` does not belong to Π⁰₂ relative to `Z`. -/
theorem not_isPi_two_finiteDomain : ¬IsPi Z 2 (· ∈ finiteDomain Z) := by
  intro h
  have hinf : IsSigma Z 2 (· ∈ infiniteDomain Z) :=
    (isSigma_not_iff.2 h).of_eq fun _ => notMem_finiteDomain
  exact not_manyOneReducible_infiniteDomain_finiteDomain hinf.manyOneReducible_finiteDomain

/-- **Exactness for `INF`.** `infiniteDomain Z` does not belong to Σ⁰₂ relative to `Z`. -/
theorem not_isSigma_two_infiniteDomain : ¬IsSigma Z 2 (· ∈ infiniteDomain Z) :=
  fun h => not_manyOneReducible_infiniteDomain_finiteDomain h.manyOneReducible_finiteDomain

/-- `finiteDomain Z` does not belong to Δ⁰₂ relative to `Z`. -/
theorem not_isDelta_two_finiteDomain : ¬IsDelta Z 2 (· ∈ finiteDomain Z) :=
  fun h => not_isPi_two_finiteDomain (isDelta_iff.1 h).2

/-- `infiniteDomain Z` does not belong to Δ⁰₂ relative to `Z`. -/
theorem not_isDelta_two_infiniteDomain : ¬IsDelta Z 2 (· ∈ infiniteDomain Z) :=
  fun h => not_isSigma_two_infiniteDomain (isDelta_iff.1 h).1

/-- `finiteDomain Z` does not belong to Σ⁰₁ relative to `Z`. -/
theorem not_isSigma_one_finiteDomain : ¬IsSigma Z 1 (· ∈ finiteDomain Z) :=
  fun h => not_isPi_two_finiteDomain h.pi_succ

/-- `finiteDomain Z` does not belong to Π⁰₁ relative to `Z`. -/
theorem not_isPi_one_finiteDomain : ¬IsPi Z 1 (· ∈ finiteDomain Z) :=
  fun h => not_isPi_two_finiteDomain h.succ

/-- `infiniteDomain Z` does not belong to Σ⁰₁ relative to `Z`. -/
theorem not_isSigma_one_infiniteDomain : ¬IsSigma Z 1 (· ∈ infiniteDomain Z) :=
  fun h => not_isSigma_two_infiniteDomain h.succ

/-- `infiniteDomain Z` does not belong to Π⁰₁ relative to `Z`. -/
theorem not_isPi_one_infiniteDomain : ¬IsPi Z 1 (· ∈ infiniteDomain Z) :=
  fun h => not_isSigma_two_infiniteDomain h.sigma_succ

/-- The relative jump `Z.jump` reduces one-one to `finiteDomain Z`. -/
theorem oneOneReducible_jump_finiteDomain (Z : Set ℕ) :
    OneOneReducible (· ∈ Z.jump) (· ∈ finiteDomain Z) :=
  isSigma_one_jump.succ.oneOneReducible_finiteDomain

/-- The relative jump `Z.jump` reduces one-one to `infiniteDomain Z`. -/
theorem oneOneReducible_jump_infiniteDomain (Z : Set ℕ) :
    OneOneReducible (· ∈ Z.jump) (· ∈ infiniteDomain Z) :=
  isSigma_one_jump.pi_succ.oneOneReducible_infiniteDomain

/-- `finiteDomain Z` does not reduce many-one to the relative jump `Z.jump`. -/
theorem not_manyOneReducible_finiteDomain_jump :
    ¬ManyOneReducible (· ∈ finiteDomain Z) (· ∈ Z.jump) := by
  rintro ⟨f, hf, hiff⟩
  exact not_isSigma_one_finiteDomain
    ((isSigma_one_jump.preimage hf.computableIn).of_eq fun e => (hiff e).symm)

/-- `infiniteDomain Z` does not reduce many-one to the relative jump `Z.jump`. -/
theorem not_manyOneReducible_infiniteDomain_jump :
    ¬ManyOneReducible (· ∈ infiniteDomain Z) (· ∈ Z.jump) := by
  rintro ⟨f, hf, hiff⟩
  exact not_isSigma_one_infiniteDomain
    ((isSigma_one_jump.preimage hf.computableIn).of_eq fun e => (hiff e).symm)

/-- At the empty oracle, `finiteDomain ∅` is not recursively enumerable. -/
theorem not_rePred_mem_finiteDomain : ¬REPred (· ∈ finiteDomain ∅) :=
  fun h => not_isSigma_one_finiteDomain (isSigma_one_empty_iff_rePred.2 h)

/-- At the empty oracle, `infiniteDomain ∅` is not recursively enumerable. -/
theorem not_rePred_mem_infiniteDomain : ¬REPred (· ∈ infiniteDomain ∅) :=
  fun h => not_isSigma_one_infiniteDomain (isSigma_one_empty_iff_rePred.2 h)

/-- At the empty oracle, membership in `finiteDomain ∅` is not computable. -/
theorem not_computablePred_mem_finiteDomain : ¬ComputablePred (· ∈ finiteDomain ∅) :=
  fun h => not_rePred_mem_finiteDomain h.to_re

/-- At the empty oracle, membership in `infiniteDomain ∅` is not computable. -/
theorem not_computablePred_mem_infiniteDomain : ¬ComputablePred (· ∈ infiniteDomain ∅) :=
  fun h => not_rePred_mem_infiniteDomain h.to_re

/-! ### Ordinary partial recursive codes at the empty oracle -/

/-- Every unrelativized Σ⁰₂ predicate reduces one-one to the finite-domain predicate on ordinary
`Nat.Partrec.Code` programs. -/
theorem IsSigma.oneOneReducible_finite_dom_eval (hp : IsSigma ∅ 2 p) :
    OneOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite) := by
  classical
  obtain ⟨q, hq, hpq⟩ := isSigma_succ_iff.1 hp
  have hre : REPred (fun a : α × ℕ => ¬q a) :=
    isSigma_one_empty_iff_rePred.1 (isSigma_not_iff.2 hq)
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.1 hre
  let f : α → Nat.Partrec.Code := fun x => (d.curry (encode x)).prefixDom
  have hf : Primrec f :=
    Nat.Partrec.Code.primrec_prefixDom.comp
      (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const d) Primrec.encode)
  refine ⟨f, hf.to_comp, ?_, fun x => ?_⟩
  · intro x₁ x₂ h
    exact encode_injective
      (Nat.Partrec.Code.curry_inj (Nat.Partrec.Code.prefixDom_inj.1 h)).2
  · rw [hpq x]
    simp only [f, Nat.Partrec.Code.finite_dom_eval_prefixDom_iff, Nat.Partrec.Code.eval_curry]
    refine exists_congr fun y => ?_
    have hdy := congrFun hd (encode (x, y))
    rw [encodek, encode_prod_val, encode_nat] at hdy
    have hdom : (d.eval (Nat.pair (encode x) y)).Dom ↔ ¬q (x, y) := by
      simp [hdy, Part.assert]
    exact (not_iff_comm.1 hdom.symm).symm

/-- The finite-domain predicate on ordinary `Nat.Partrec.Code` programs is one-one equivalent to
`finiteDomain ∅`. -/
theorem oneOneEquiv_finite_dom_eval_finiteDomain_empty :
    OneOneEquiv (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite)
      (· ∈ finiteDomain ∅) := by
  refine ⟨⟨fun c => encode c.toSingleOracleCode,
    (Primrec.encode.comp Nat.Partrec.Code.primrec_toSingleOracleCode).to_comp,
    encode_injective.comp Nat.Partrec.Code.toSingleOracleCode_injective,
    fun c => (encode_toSingleOracleCode_mem_finiteDomain_iff ∅ c).symm⟩,
    isSigma_two_finiteDomain.oneOneReducible_finite_dom_eval⟩

/-- Unrelativized Σ⁰₂ predicates are characterized by many-one reducibility to the finite-domain
predicate on ordinary `Nat.Partrec.Code` programs. -/
theorem isSigma_two_empty_iff_manyOneReducible_finite_dom_eval :
    IsSigma ∅ 2 p ↔
      ManyOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite) :=
  ⟨fun hp => hp.oneOneReducible_finite_dom_eval.to_many_one,
    fun h => isSigma_two_iff_manyOneReducible_finiteDomain.2
      (h.trans oneOneEquiv_finite_dom_eval_finiteDomain_empty.1.to_many_one)⟩

/-- Unrelativized Σ⁰₂ predicates are characterized by one-one reducibility to the finite-domain
predicate on ordinary `Nat.Partrec.Code` programs. -/
theorem isSigma_two_empty_iff_oneOneReducible_finite_dom_eval :
    IsSigma ∅ 2 p ↔
      OneOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite) :=
  ⟨IsSigma.oneOneReducible_finite_dom_eval,
    fun h => isSigma_two_empty_iff_manyOneReducible_finite_dom_eval.2 h.to_many_one⟩

/-- Every unrelativized Π⁰₂ predicate reduces one-one to the infinite-domain predicate on ordinary
`Nat.Partrec.Code` programs. -/
theorem IsPi.oneOneReducible_infinite_dom_eval (hp : IsPi ∅ 2 p) :
    OneOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite) := by
  classical
  obtain ⟨f, hf, hinj, hiff⟩ := (isSigma_not_iff.2 hp).oneOneReducible_finite_dom_eval
  refine ⟨f, hf, hinj, fun x => ?_⟩
  dsimp only at hiff ⊢
  rw [Set.Infinite, ← hiff x, not_not]

/-- The infinite-domain predicate on ordinary `Nat.Partrec.Code` programs is one-one equivalent to
`infiniteDomain ∅`. -/
theorem oneOneEquiv_infinite_dom_eval_infiniteDomain_empty :
    OneOneEquiv (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite)
      (· ∈ infiniteDomain ∅) := by
  refine ⟨⟨fun c => encode c.toSingleOracleCode,
    (Primrec.encode.comp Nat.Partrec.Code.primrec_toSingleOracleCode).to_comp,
    encode_injective.comp Nat.Partrec.Code.toSingleOracleCode_injective,
    fun c => (encode_toSingleOracleCode_mem_infiniteDomain_iff ∅ c).symm⟩,
    isPi_two_infiniteDomain.oneOneReducible_infinite_dom_eval⟩

/-- Unrelativized Π⁰₂ predicates are characterized by many-one reducibility to the infinite-domain
predicate on ordinary `Nat.Partrec.Code` programs. -/
theorem isPi_two_empty_iff_manyOneReducible_infinite_dom_eval :
    IsPi ∅ 2 p ↔
      ManyOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite) :=
  ⟨fun hp => hp.oneOneReducible_infinite_dom_eval.to_many_one,
    fun h => isPi_two_iff_manyOneReducible_infiniteDomain.2
      (h.trans oneOneEquiv_infinite_dom_eval_infiniteDomain_empty.1.to_many_one)⟩

/-- Unrelativized Π⁰₂ predicates are characterized by one-one reducibility to the infinite-domain
predicate on ordinary `Nat.Partrec.Code` programs. -/
theorem isPi_two_empty_iff_oneOneReducible_infinite_dom_eval :
    IsPi ∅ 2 p ↔
      OneOneReducible p (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite) :=
  ⟨IsPi.oneOneReducible_infinite_dom_eval,
    fun h => isPi_two_empty_iff_manyOneReducible_infinite_dom_eval.2 h.to_many_one⟩

/-- The finite-domain predicate on ordinary `Nat.Partrec.Code` programs is not recursively
enumerable. -/
theorem not_rePred_finite_dom_eval :
    ¬REPred (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite) := by
  intro h
  have hsigma : IsSigma ∅ 1 (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Finite) :=
    isSigma_one_empty_iff_rePred.2 h
  obtain ⟨f, hf, -, hiff⟩ := oneOneEquiv_finite_dom_eval_finiteDomain_empty.2
  exact not_isSigma_one_finiteDomain
    ((hsigma.preimage hf.computableIn).of_eq fun e => (hiff e).symm)

/-- The infinite-domain predicate on ordinary `Nat.Partrec.Code` programs is not recursively
enumerable. -/
theorem not_rePred_infinite_dom_eval :
    ¬REPred (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite) := by
  intro h
  have hsigma : IsSigma ∅ 1 (fun c : Nat.Partrec.Code => {x | (c.eval x).Dom}.Infinite) :=
    isSigma_one_empty_iff_rePred.2 h
  obtain ⟨f, hf, -, hiff⟩ := oneOneEquiv_infinite_dom_eval_infiniteDomain_empty.2
  exact not_isSigma_one_infiniteDomain
    ((hsigma.preimage hf.computableIn).of_eq fun e => (hiff e).symm)

end TauCeti.ArithmeticalHierarchy
