/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code
public import TauCeti.Computability.TuringDegree

/-!
# The Turing jump of a set

A set `Z ⊆ ℕ` is used as an oracle through its characteristic function, the total partial function
`Z.oracle`. The **jump** `Z.jump` is the relative diagonal halting set
`Z' = {e | Φ_e^Z(e)↓}`, where `Φ_e^Z` is the program numbered `e` of
`TauCeti.Oracle.Single.Code`, evaluated relative to `Z.oracle`. The **paired jump**
`Z.pairedJump` is the relative paired halting set `K₀^Z = {⟨x, e⟩ | Φ_e^Z(x)↓}`, with the input in
the first coordinate of `Nat.pair`.

The main results are that the jump is a strict upper bound in the Turing order and that every set
c.e. in `Z` reduces to it. These reductions are one-one reductions in the sense of Mathlib's
`OneOneReducible`, and descend to Turing reducibility of the set oracles.

## Main definitions

* `Set.jump`: the jump `Z'` of a set `Z`.
* `Set.pairedJump`: the paired halting set `K₀^Z` relative to a set `Z`.

## Main results

* `Set.oneOneReducible_jump_of_recursiveIn`: every set c.e. in `Z`, that is, the domain of a
  partial function recursive in `Z.oracle`, reduces one-one to the jump.
* `Set.oneOneEquiv_jump_pairedJump`: the diagonal and paired halting sets relative to `Z` are
  one-one equivalent.
* `Set.oneOneReducible_jump`, `Set.turingReducible_jump`: `Z` reduces to its jump.
* `Set.not_jump_turingReducible`: the jump of `Z` is not computable relative to `Z`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2.
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace Set

variable (Z : Set ℕ)

/-- The **jump** `Z'` of a set `Z`: the indices `e` for which the program numbered `e` halts on
input `e` relative to the oracle of `Z`. -/
def jump : Set ℕ :=
  {e | (Code.eval Z.oracle (ofNat Code e) e).Dom}

/-- The **paired jump** `K₀^Z` of a set `Z`: the numbers `Nat.pair x e` for which the program
numbered `e` halts on input `x` relative to the oracle of `Z`. -/
def pairedJump : Set ℕ :=
  {n | (Code.eval Z.oracle (ofNat Code n.unpair.2) n.unpair.1).Dom}

variable {Z}

/-- `e ∈ Z'` when the program numbered `e` halts on input `e` relative to `Z`. -/
@[simp]
theorem mem_jump {e : ℕ} : e ∈ Z.jump ↔ (Code.eval Z.oracle (ofNat Code e) e).Dom :=
  Iff.rfl

/-- `n ∈ K₀^Z` when the program numbered by the second coordinate of `n` halts on the first
coordinate relative to `Z`. -/
@[simp]
theorem mem_pairedJump {n : ℕ} :
    n ∈ Z.pairedJump ↔ (Code.eval Z.oracle (ofNat Code n.unpair.2) n.unpair.1).Dom :=
  Iff.rfl

/-- `Nat.pair x e ∈ K₀^Z` when the program numbered `e` halts on input `x` relative to `Z`. -/
theorem pair_mem_pairedJump {x e : ℕ} :
    Nat.pair x e ∈ Z.pairedJump ↔ (Code.eval Z.oracle (ofNat Code e) x).Dom := by
  simp

variable (Z)

/-- Halting relative to `Z` reduces one-one to the jump of `Z`, uniformly in the program: the
program `c` halts on `x` exactly when the program that ignores its input and runs `c` on `x` halts
on its own number. -/
theorem oneOneReducible_dom_eval_jump :
    OneOneReducible (fun p : Code × ℕ => (Code.eval Z.oracle p.1 p.2).Dom) (· ∈ Z.jump) := by
  -- hard-wire the input `x` into the program `c`
  let r : Code × ℕ → Code := fun p => .comp p.1 (Nat.Partrec.Code.const p.2).toSingleOracleCode
  have hr : Primrec r := Code.primrec₂_comp.comp Primrec.fst <|
    Nat.Partrec.Code.primrec_toSingleOracleCode.comp <|
      Nat.Partrec.Code.primrec_const.comp Primrec.snd
  refine ⟨fun p => encode (r p), (Primrec.encode.comp hr).to_comp, ?_, fun p => ?_⟩
  · rintro ⟨c, x⟩ ⟨d, y⟩ h
    simp only [r, encode_inj, Code.comp.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Nat.Partrec.Code.const_inj (Nat.Partrec.Code.toSingleOracleCode_injective h)]
  · simp only [r, mem_jump, ofNat_encode, Code.eval_comp, Code.eval_toSingleOracleCode,
      Nat.Partrec.Code.eval_const]
    exact Iff.of_eq (congrArg Part.Dom (Part.bind_some _ _)).symm

/-- **Every set c.e. in `Z` reduces one-one to the jump of `Z`:** the domain of every partial
function recursive in the oracle of `Z` reduces one-one to `Z'`. -/
theorem oneOneReducible_jump_of_recursiveIn {f : ℕ →. ℕ} (hf : Nat.RecursiveIn {Z.oracle} f) :
    OneOneReducible (fun x => (f x).Dom) (· ∈ Z.jump) := by
  obtain ⟨c, rfl⟩ := Code.exists_code.1 hf
  exact (OneOneReducible.mk _ ((Computable.const c).pair Computable.id)
    fun _ _ h => (Prod.ext_iff.1 h).2).trans (oneOneReducible_dom_eval_jump Z)

/-- **The diagonal and paired halting sets are one-one equivalent**, relative to every set `Z`. -/
theorem oneOneEquiv_jump_pairedJump : OneOneEquiv (· ∈ Z.jump) (· ∈ Z.pairedJump) := by
  refine ⟨⟨fun e => Nat.pair e e, (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp,
    fun e e' h => (Nat.pair_eq_pair.1 h).1, fun e => by simp [mem_jump]⟩, ?_⟩
  -- read `Nat.pair x e` as the program numbered `e` and the input `x`
  refine (OneOneReducible.mk _ (f := fun n : ℕ => (ofNat Code n.unpair.2, n.unpair.1))
    ((Computable.ofNat Code).comp (Computable.snd.comp Computable.unpair) |>.pair
      (Computable.fst.comp Computable.unpair)) fun n n' h => ?_).trans
    (oneOneReducible_dom_eval_jump Z)
  simp only [Prod.mk.injEq] at h
  have h₂ := congrArg encode h.1
  simp only [encode_ofNat] at h₂
  rw [← Nat.pair_unpair n, ← Nat.pair_unpair n', h.2, h₂]

/-- The diagonal and paired halting sets relative to `Z` have Turing equivalent oracles. -/
theorem turingEquivalent_jump_pairedJump : TuringEquivalent Z.jump.oracle Z.pairedJump.oracle :=
  ⟨(oneOneEquiv_jump_pairedJump Z).1.to_many_one.turingReducible_oracle,
    (oneOneEquiv_jump_pairedJump Z).2.to_many_one.turingReducible_oracle⟩

/-- A set reduces one-one to its jump. -/
theorem oneOneReducible_jump : OneOneReducible (· ∈ Z) (· ∈ Z.jump) := by
  -- `n ∈ Z` exactly when the predecessor of the oracle's answer at `n` is defined
  have h : Nat.RecursiveIn {Z.oracle} fun n => Z.oracle n >>= fun m => (Nat.ppred m : Part ℕ) :=
    Nat.Partrec.ppred.recursiveIn.comp (.oracle _ rfl)
  have hZ : (fun n => (Z.oracle n >>= fun m => (Nat.ppred m : Part ℕ)).Dom) = (· ∈ Z) :=
    funext fun n => by
      by_cases hn : n ∈ Z <;> simp [hn, Option.isSome_iff_exists, Nat.ppred_eq_some]
  exact hZ ▸ oneOneReducible_jump_of_recursiveIn Z h

/-- A set is Turing reducible to its jump. -/
theorem turingReducible_jump : TuringReducible Z.oracle Z.jump.oracle :=
  (oneOneReducible_jump Z).to_many_one.turingReducible_oracle

/-- **The jump is not computable relative to `Z`:** the oracle of `Z'` is not Turing reducible to
the oracle of `Z`. -/
theorem not_jump_turingReducible : ¬TuringReducible Z.jump.oracle Z.oracle := by
  -- diagonalize: the program halting on `e` exactly when `e ∉ Z'` would halt on its own number
  -- exactly when it does not
  intro h
  -- `1 - m` has a defined predecessor exactly when `m = 0`
  have hg : Nat.Partrec fun m => (Nat.ppred (1 - m) : Part ℕ) :=
    (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primrec.nat_iff.1 <|
      Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).of_eq fun m => by simp
  obtain ⟨c, hc⟩ := Code.exists_code.1 <|
    hg.recursiveIn.comp (RecursiveIn.iff_nat.1 h)
  have := mem_jump (Z := Z) (e := encode c)
  rw [ofNat_encode, hc] at this
  by_cases he : encode c ∈ Z.jump <;> simp [he, Part.bind_eq_bind] at this

end Set
