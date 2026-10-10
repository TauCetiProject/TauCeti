/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Tables.Checks

/-! # Polynomial-time parameter substitution for permutation-table machines -/

@[expose] public section

namespace TauCeti.PermutationTables

open Computability BitEncoding Turing

variable {α : Type} [Primcodable α] [BitEncoding α]

@[fun_prop] theorem polyTime_lookup_comp
    {n x : α → ℕ} {t : α → Table}
    (hn : PolyTime n) (ht : PolyTime t) (hx : PolyTime x) :
    PolyTime (fun a => lookup (n a) (t a) (x a)) :=
  PolyTime.comp (f := fun a => (n a, t a, x a))
    polyTime_lookup (PolyTime.pair hn (PolyTime.pair ht hx))

@[fun_prop] theorem polyTime_mul_comp
    {n : α → ℕ} {t u : α → Table}
    (hn : PolyTime n) (ht : PolyTime t) (hu : PolyTime u) :
    PolyTime (fun a => mul (n a) (t a) (u a)) :=
  PolyTime.comp (f := fun a => (n a, t a, u a))
    polyTime_mul (PolyTime.pair hn (PolyTime.pair ht hu))

@[fun_prop] theorem polyTime_inv_comp
    {n : α → ℕ} {t : α → Table} (hn : PolyTime n) (ht : PolyTime t) :
    PolyTime (fun a => inv (n a) (t a)) :=
  PolyTime.comp (f := fun a => (n a, t a)) polyTime_inv (PolyTime.pair hn ht)

@[fun_prop] theorem polyTime_letter_comp
    {n : α → ℕ} {gs : α → List Table} {l : α → ℕ × Bool}
    (hn : PolyTime n) (hg : PolyTime gs) (hl : PolyTime l) :
    PolyTime (fun a => letter (n a) (gs a) (l a)) :=
  PolyTime.comp (f := fun a => ((n a, gs a), l a))
    polyTime_letter (PolyTime.pair (PolyTime.pair hn hg) hl)

@[fun_prop] theorem polyTime_word_comp
    {n : α → ℕ} {gs : α → List Table} {w : α → Word}
    (hn : PolyTime n) (hg : PolyTime gs) (hw : PolyTime w) :
    PolyTime (fun a => word (n a) (gs a) (w a)) :=
  PolyTime.comp (f := fun a => ((n a, gs a), w a))
    polyTime_word (PolyTime.pair (PolyTime.pair hn hg) hw)

@[fun_prop] theorem polyTime_member_comp
    {s : α → PointSet} {x : α → ℕ} (hs : PolyTime s) (hx : PolyTime x) :
    PolyTime (fun a => member (s a) (x a)) :=
  PolyTime.comp (f := fun a => (s a, x a)) polyTime_member (PolyTime.pair hs hx)

@[fun_prop] theorem polyTime_primitive_comp
    {n a : α → ℕ} {gs : α → List Table}
    (hn : PolyTime n) (hg : PolyTime gs) (ha : PolyTime a) :
    PolyTime (fun x => primitive (n x) (gs x) (a x)) :=
  PolyTime.comp (f := fun x => ((n x, gs x), a x))
    polyTime_primitive (PolyTime.pair (PolyTime.pair hn hg) ha)

@[fun_prop] theorem polyTime_cycleCheck_comp
    {n : α → ℕ} {t : α → Table} (hn : PolyTime n) (ht : PolyTime t) :
    PolyTime (fun a => cycleCheck (n a) (t a)) :=
  PolyTime.comp (f := fun a => (n a, t a)) polyTime_cycleCheck (PolyTime.pair hn ht)

@[fun_prop] theorem polyTime_supportCount_comp
    {n : α → ℕ} {t : α → Table} (hn : PolyTime n) (ht : PolyTime t) :
    PolyTime (fun a => supportCount (n a) (t a)) :=
  PolyTime.comp (f := fun a => (n a, t a)) polyTime_supportCount (PolyTime.pair hn ht)

@[fun_prop] theorem polyTime_even_comp
    {n : α → ℕ} {t : α → Table} (hn : PolyTime n) (ht : PolyTime t) :
    PolyTime (fun a => even (n a) (t a)) :=
  PolyTime.comp (f := fun a => (n a, t a)) polyTime_even (PolyTime.pair hn ht)

end TauCeti.PermutationTables
