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
  `Nat.Partrec.rfind'`.

The last one is the closure property needed to evaluate the search instruction of a code, whose
search starts at the second component of its input rather than at zero.
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

end Nat.RecursiveIn
