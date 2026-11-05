/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.RecursiveIn

/-!
# Closure properties of oracle-relative computability

Mathlib's `Nat.RecursiveIn O` is the inductive closure of the basic functions and the oracles in
`O` under pairing, composition, primitive recursion and unbounded search starting at zero. This file
derives further closure properties from those constructors:

* `Nat.RecursiveIn.comp_primrec`, `Nat.RecursiveIn.map_primrec`: composition with a primitive
  recursive function on either side;
* `Nat.RecursiveIn.rfind'`: unbounded search starting at a given value, the oracle-relative form of
  `Nat.Partrec.rfind'`;
* `Nat.RecursiveIn.cond`: a conditional with a guard computable in `O`, which evaluates only the
  selected branch.

The search `rfind'` is the closure property needed to evaluate the search instruction of a code,
whose search starts at the second component of its input rather than at zero. The conditional is
needed to combine two reductions according to a decidable property of the input, as in the Turing
join of two oracles.

Mathlib's `ComputableIn₂` expresses computability of binary total functions in terms of
encodings; `ComputableIn₂.iff_nat` restates it for functions on `ℕ` as a `Nat.RecursiveIn`
statement on codes `Nat.pair a b` of pairs. Total oracle-computable functions are closed under
composition, pairing, primitive recursion, and forming finite initial segments of a sequence.
These closure proofs adapt Mathlib's `Computable.comp`, `Computable.pair`, and
`Computable.nat_rec` in `Mathlib.Computability.Partrec` to `Nat.RecursiveIn`.
-/

public section

namespace Nat.RecursiveIn

variable {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}

/-- Precomposition with a primitive recursive function preserves recursiveness in `O`. -/
theorem comp_primrec {g : ℕ → ℕ} (hf : Nat.RecursiveIn O f) (hg : Nat.Primrec g) :
    Nat.RecursiveIn O fun n => f (g n) :=
  (hf.comp hg.recursiveIn).of_eq fun _ => Part.bind_some _ _

/-- Postcomposition with a primitive recursive function preserves recursiveness in `O`. -/
theorem map_primrec {g : ℕ → ℕ} (hf : Nat.RecursiveIn O f) (hg : Nat.Primrec g) :
    Nat.RecursiveIn O fun n => (f n).map g :=
  (hg.recursiveIn.comp hf).of_eq fun n => by simp [Part.bind_some_eq_map]

/-- **Search from a given start.** If `f` is recursive in `O`, so is the function sending
`Nat.pair a m` to the least `n ≥ m` with `f (Nat.pair a n) = 0`, provided `f (Nat.pair a k)` is
defined for every `k` from `m` to `n`. This is the oracle-relative form of `Nat.Partrec.rfind'`. -/
theorem rfind' (hf : Nat.RecursiveIn O f) :
    Nat.RecursiveIn O
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) := by
  -- shift the search: `Nat.pair (Nat.pair a m) n` is sent to `Nat.pair a (n + m)`
  have hk : Nat.Primrec fun q : ℕ =>
      Nat.pair q.unpair.1.unpair.1 (q.unpair.2 + q.unpair.1.unpair.2) :=
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair)
        (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair))
  -- read off `n + m` from `Nat.pair (Nat.pair a m) n`
  have hj : Nat.Primrec fun p : ℕ => p.unpair.2 + p.unpair.1.unpair.2 :=
    Primrec.nat_iff.1 <| Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  have hs := ((Nat.Primrec.id.recursiveIn (O := O)).pair (hf.comp_primrec hk).rfind).map_primrec hj
  refine hs.of_eq fun x => ?_
  simp [Seq.seq, Part.map_map, Function.comp_def]

/-- A conditional whose fallback value is part of the input: `Nat.pair n v` is sent to `f n` when
`c n` holds and to `v` otherwise. Primitive recursion on the code of `c n`, with base case `v`, only
evaluates its step function `f` in the first case. -/
private theorem cond_unpair {c : ℕ → Bool}
    (hc : Nat.RecursiveIn O fun n => Part.some (cond (c n) 1 0)) (hf : Nat.RecursiveIn O f) :
    Nat.RecursiveIn O fun p => bif c p.unpair.1 then f p.unpair.1 else Part.some p.unpair.2 := by
  -- the step function reads `n` off `Nat.pair (Nat.pair n v) (Nat.pair y i)`
  have hb : Nat.Primrec fun q : ℕ => q.unpair.1.unpair.1 :=
    Primrec.nat_iff.1 <| Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair
  -- the recursion runs on `Nat.pair p 1` when `c n` holds and on `Nat.pair p 0` otherwise
  have hk : Nat.RecursiveIn O fun p => Part.some (Nat.pair p (cond (c p.unpair.1) 1 0)) :=
    ((Nat.Primrec.id.recursiveIn (O := O)).pair (hc.comp_primrec Nat.Primrec.left)).of_eq
      fun p => by simp [Seq.seq]
  refine ((Nat.RecursiveIn.prec Nat.RecursiveIn.right (hf.comp_primrec hb)).comp hk).of_eq
    fun p => ?_
  cases c p.unpair.1 <;> simp

/-- **Conditionals.** If the guard `c` is computable in `O` and `f` and `g` are recursive in `O`,
then so is the function which agrees with `f` where `c` holds and with `g` elsewhere. Only the
selected branch is evaluated, so the conditional is defined at `n` exactly when the selected branch
is. -/
protected theorem cond {c : ℕ → Bool} (hc : ComputableIn O c) (hf : Nat.RecursiveIn O f)
    {g : ℕ →. ℕ} (hg : Nat.RecursiveIn O g) :
    Nat.RecursiveIn O fun n => bif c n then f n else g n := by
  -- the guard and its negation, as `1`/`0`-valued functions on `ℕ`
  unfold ComputableIn RecursiveIn at hc
  have hc₁ : Nat.RecursiveIn O fun n => Part.some (cond (c n) 1 0) :=
    hc.of_eq fun n => by cases h : c n <;> simp [h]
  have hc₀ : Nat.RecursiveIn O fun n => Part.some (cond (!c n) 1 0) :=
    (hc₁.map_primrec <| Primrec.nat_iff.1 <|
      Primrec.nat_sub.comp (_root_.Primrec.const 1) _root_.Primrec.id).of_eq
      fun n => by cases c n <;> simp
  -- first evaluate `g n`, or `0` where `c n` holds, and pass that value as the fallback for `f`
  have hg₀ := (cond_unpair hc₀ hg).comp_primrec
    (Primrec.nat_iff.1 <| Primrec₂.natPair.comp _root_.Primrec.id (_root_.Primrec.const 0))
  have hs := Nat.RecursiveIn.pair (Nat.Primrec.id.recursiveIn (O := O)) hg₀
  refine ((cond_unpair hc₁ hf).comp hs).of_eq fun n => ?_
  cases h : c n <;> simp [h, Seq.seq]

end Nat.RecursiveIn

namespace ComputableIn₂

variable {O : Set (ℕ →. ℕ)}

/-- A binary total function on `ℕ` is computable in `O` exactly when it is recursive in `O` as a
function of the code `Nat.pair a b` of its arguments. -/
theorem iff_nat {f : ℕ → ℕ → ℕ} :
    ComputableIn₂ O f ↔ Nat.RecursiveIn O fun n => Part.some (f n.unpair.1 n.unpair.2) := by
  -- `ComputableIn₂` is recursiveness of the function on encodings, which `simp` unpairs
  unfold ComputableIn₂ ComputableIn RecursiveIn
  exact ⟨fun h => h.of_eq fun n => by simp, fun h => h.of_eq fun n => by simp⟩

end ComputableIn₂

namespace ComputableIn

open Encodable

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
variable {O : Set (ℕ →. ℕ)}

/-- Composition of total oracle-computable functions. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f (g a)) := by
  exact (Nat.RecursiveIn.comp hf hg).of_eq fun n => by
    cases decode (α := α) n <;> simp [Encodable.encodek]

/-- Pairing total oracle-computable functions. -/
theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => (f a, g a)) := by
  exact (Nat.RecursiveIn.pair hf hg).of_eq fun n => by
    cases decode (α := α) n <;> simp [Seq.seq]

/-- Primitive recursion of total oracle-computable functions. The recursion counter is allowed
to depend on the parameter. -/
theorem nat_rec {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : ComputableIn O f) (hg : ComputableIn O g)
    (hh : ComputableIn₂ O h) :
    ComputableIn O (fun a => Nat.rec (motive := fun _ => β) (g a)
      (fun n b => h a (n, b)) (f a)) := by
  have hr := (Nat.RecursiveIn.prec hg hh).comp (Nat.RecursiveIn.pair
    (Nat.Primrec.id.recursiveIn (O := O)) hf)
  refine hr.of_eq fun n => ?_
  cases e : decode (α := α) n with
  | none => simp [Seq.seq]
  | some a =>
    simp only [Seq.seq, e, id_eq, Part.coe_some, Part.map_eq_map, Part.map_some, encode_nat,
      Part.bind_some, decode_prod_val, Nat.unpair_pair, decode_nat, Option.bind_some,
      Option.map_map, Part.bind_eq_bind]
    generalize f a = k
    induction k with
    | zero => rfl
    | succ k ih => simp [ih]

end ComputableIn

namespace ComputableIn₂

variable {α β : Type*} [Primcodable α] [Primcodable β] {O : Set (ℕ →. ℕ)}

/-- A finite initial segment of an oracle-computable sequence can be computed uniformly in its
length and in the sequence parameter. -/
theorem list_range_map {f : α → ℕ → β} (hf : ComputableIn₂ O f) :
    ComputableIn₂ O (fun a n => (List.range n).map (f a)) := by
  have hstep : ComputableIn₂ O (fun p : α × ℕ => fun q : ℕ × List β =>
      q.2 ++ [f p.1 q.1]) :=
    Primrec.list_concat.computableIn.comp <|
      ComputableIn.snd.comp ComputableIn.snd |>.pair
        (hf.comp ((ComputableIn.fst.comp ComputableIn.fst).pair
          (ComputableIn.fst.comp ComputableIn.snd)))
  refine RecursiveIn.of_eq
    (ComputableIn.nat_rec ComputableIn.snd (ComputableIn.const []) hstep) ?_
  rintro ⟨a, n⟩
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, ih]

end ComputableIn₂
