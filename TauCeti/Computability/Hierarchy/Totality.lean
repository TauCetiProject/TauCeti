/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.SingleOracle.Recursion

/-!
# The totality index set

`totality Z` consists of the indices of oracle programs defined on every natural input relative
to `Z`. It is Π⁰₂-complete relative to `Z` under ordinary computable one-one and many-one
reductions, even when `Z` is noncomputable. The reduction specializes a single program for a
Σ⁰₁ matrix relative to `Z`; it does not use an oracle to transform indices.

A diagonal argument proves that totality is not Σ⁰₂ relative to `Z`. Consequently it is
neither c.e. nor co-c.e. for any oracle, and neither it nor its complement many-one reduces to
relative halting.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.3
  (arithmetical index sets and completeness).
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

/-- The indices of programs total relative to `Z`, in the single-oracle numbering. -/
def totality (Z : Set ℕ) : Set ℕ :=
  {e | ∀ x, (Code.eval Z.oracle (ofNat Code e) x).Dom}

/-- An index belongs to totality exactly when its program halts on every input. -/
@[simp]
theorem mem_totality {Z : Set ℕ} {e : ℕ} :
    e ∈ totality Z ↔ ∀ x, (Code.eval Z.oracle (ofNat Code e) x).Dom := Iff.rfl

variable {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-- Totality is Π⁰₂ relative to its oracle. -/
theorem isPi_two_totality : IsPi Z 2 (· ∈ totality Z) := by
  have hdom : IsSigma Z 1 (fun a : ℕ × ℕ =>
      (Code.eval Z.oracle (ofNat Code a.1) a.2).Dom) := by
    have h := (isSigma_one_dom_eval (Z := Z) Code.universal).preimage
      Primrec₂.natPair.computableIn
    exact h.of_eq fun a => by
      have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
      rw [hZ, Code.eval_universal]
  exact isPi_succ_iff.2 ⟨_, hdom, fun _ => mem_totality⟩

/-- Every Π⁰₂ predicate relative to `Z` one-one reduces to relative totality. The translating
function is ordinary computable, even for a noncomputable oracle. -/
theorem IsPi.oneOneReducible_totality (hp : IsPi Z 2 p) :
    OneOneReducible p (· ∈ totality Z) := by
  obtain ⟨q, hq, heq⟩ := isPi_succ_iff.1 hp
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hq
  refine ⟨fun x => encode (Code.curry c (encode x)),
    Computable.encode.comp (Code.primrec₂_curry.to_comp.comp
      (Computable.const c) Computable.encode),
    fun _ _ h => encode_injective (Code.curry_inj (encode_injective h)).2, fun x => ?_⟩
  simpa only [mem_totality, ofNat_encode, Code.eval_curry, encode_prod_val, encode_nat] using
    (heq x).trans (forall_congr' fun y => hc (x, y))

/-- Every Π⁰₂ predicate relative to `Z` many-one reduces to relative totality by an ordinary
computable function. -/
theorem IsPi.manyOneReducible_totality (hp : IsPi Z 2 p) :
    ManyOneReducible p (· ∈ totality Z) :=
  hp.oneOneReducible_totality.to_many_one

/-- A predicate is Π⁰₂ relative to `Z` exactly when it many-one reduces to relative totality
by an ordinary computable function. -/
theorem isPi_two_iff_manyOneReducible_totality :
    IsPi Z 2 p ↔ ManyOneReducible p (· ∈ totality Z) := by
  refine ⟨IsPi.manyOneReducible_totality, fun ⟨f, hf, heq⟩ => ?_⟩
  exact (isPi_two_totality.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- A predicate is Π⁰₂ relative to `Z` exactly when it one-one reduces to relative totality
by an ordinary computable function. -/
theorem isPi_two_iff_oneOneReducible_totality :
    IsPi Z 2 p ↔ OneOneReducible p (· ∈ totality Z) :=
  ⟨IsPi.oneOneReducible_totality,
    fun h => isPi_two_iff_manyOneReducible_totality.2 h.to_many_one⟩

/-- Totality is not Σ⁰₂ relative to its oracle. -/
theorem not_isSigma_two_totality : ¬IsSigma Z 2 (· ∈ totality Z) := by
  intro h
  obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 (isSigma_not_iff.2 hq)
  let d := Code.fixedPoint c
  have hrow : (∀ x, (Code.eval Z.oracle c (Nat.pair (encode d) x)).Dom) ↔
      ¬encode d ∈ totality Z := by
    rw [heq (encode d)]
    simp only [not_exists]
    apply forall_congr'
    intro x
    simpa only [encode_prod_val, encode_nat] using (hc (encode d, x)).symm
  have hdiag : encode d ∈ totality Z ↔ ¬encode d ∈ totality Z := by
    simpa only [d, mem_totality, ofNat_encode, Code.eval_fixedPoint] using hrow
  exact iff_not_self hdiag

/-- Relative totality does not many-one reduce to the relative halting set. -/
theorem not_manyOneReducible_totality_jump :
    ¬ManyOneReducible (· ∈ totality Z) (· ∈ Z.jump) := by
  rintro ⟨f, hf, heq⟩
  exact not_isSigma_two_totality
    (((isSigma_one_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm).succ)

/-- The totality index set relative to any oracle is not computably enumerable. -/
theorem not_rePred_mem_totality : ¬REPred (· ∈ totality Z) := by
  intro h
  exact not_manyOneReducible_totality_jump (Z.oneOneReducible_jump_of_rePred h).to_many_one

/-- The complement of relative totality does not many-one reduce to the relative halting set. -/
theorem not_manyOneReducible_compl_totality_jump :
    ¬ManyOneReducible (· ∈ (totality Z)ᶜ) (· ∈ Z.jump) := by
  rintro ⟨f, hf, heq⟩
  have hpi : IsPi Z 1 (· ∈ totality Z) :=
    isSigma_not_iff.1 ((isSigma_one_jump.preimage hf.computableIn).of_eq
      fun x => (heq x).symm)
  exact not_isSigma_two_totality hpi.sigma_succ

/-- The complement of totality relative to any oracle is not computably enumerable. -/
theorem not_rePred_mem_compl_totality : ¬REPred (· ∈ (totality Z)ᶜ) := fun h =>
  not_manyOneReducible_compl_totality_jump (Z.oneOneReducible_jump_of_rePred h).to_many_one

end TauCeti.ArithmeticalHierarchy
