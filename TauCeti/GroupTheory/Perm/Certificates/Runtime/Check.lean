/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Runtime.Wire.Basic
public import TauCeti.GroupTheory.Perm.Certificates.Tables.Combinators

/-!
# Uniform finite-control machines for all certificate checks

The degree, generator tables, and certificate data are inputs to one machine.
Every loop scans a list or uses a unary clock with a proved size bound.
The semantic correspondence with the dependent checker is proved separately.
-/

@[expose] public section

namespace TauCeti.CertificateRuntime

open Computability BitEncoding Turing PermutationTables

/-- Evaluate each subgroup generator word in the ambient tables. -/
def decodedTables (n : ℕ) (gs : List Table) (words : List PermutationTables.Word) :
    List Table := words.map (word n gs)

/-- Enumerate points not selected by the fixed-point mask. -/
def complementPoints (n : ℕ) (mask : List Bool) : List ℕ :=
  (List.range n).filter fun x => !member mask x

/-- Count the fixed points selected by the mask. -/
def fixedCount (n : ℕ) (mask : List Bool) : ℕ :=
  (List.range n).countP (member mask)

/-- Check that every subgroup generator fixes every masked point. -/
def fixes (n : ℕ) (hs : List Table) (mask : List Bool) : Bool :=
  hs.all fun h => (List.range n).all fun x =>
    !member mask x || decide (lookup n h x = x)

/-- Check that the supplied subgroup words carry the base to each complementary point. -/
def reaches (n : ℕ) (hs : List Table) (mask : List Bool) (base : ℕ)
    (words : List PermutationTables.Word) : Bool :=
  let points := complementPoints n mask
  (List.range points.length).all fun i =>
    decide (lookup n (word n hs (words[i]?.getD [])) base = points[i]?.getD 0)

/-- Evaluate a conjugated subgroup generator in ambient point tables. -/
def factor (n : ℕ) (gs hs : List Table) (f : Factor) : Table :=
  let u := word n gs f.1
  mul n (mul n u (letter n hs f.2)) (inv n u)

/-- Multiply the supplied conjugated factors to obtain the proposed prime cycle. -/
def cycleTable (n : ℕ) (gs hs : List Table) (factors : List Factor) : Table :=
  factors.foldl (fun t f => mul n t (factor n gs hs f)) (List.range n)

/-- Check primitivity, the fixed set, the complementary base, and all orbit witnesses. -/
def baseCheck (n : ℕ) (gs hs : List Table) (mask : List Bool) (base : ℕ)
    (words : List PermutationTables.Word) : Bool :=
  primitive n gs base &&
    decide (0 < fixedCount n mask) &&
    decide (fixedCount n mask + 1 < n) &&
    !member mask base && fixes n hs mask && reaches n hs mask base words

/-- Check the prime-cycle support and degree hypotheses required by Jordan's theorem. -/
def cycleValid (n : ℕ) (t : Table) : Bool :=
  cycleCheck n t && decide (supportCount n t).Prime && decide (supportCount n t + 3 ≤ n)

/-- Check the cycle and parity obligations associated with a recognized claim tag. -/
def claimCheck (n : ℕ) (gs hs : List Table) (tag : ℕ) (factors : List Factor) : Bool :=
  bif decide (tag = 0) then true
  else bif decide (tag = 1) then
    cycleValid n (cycleTable n gs hs factors) && hs.all (even n)
  else bif decide (tag = 2) then
    cycleValid n (cycleTable n gs hs factors) && hs.any (fun h => !even n h)
  else false

/-- Run the proof-erased certificate checks on the decoded ambient and subgroup tables. -/
def check (n : ℕ) (gs : List Table) (c : Certificate) : Bool :=
  let hs := decodedTables n gs c.2.1
  baseCheck n gs hs c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 &&
    claimCheck n gs hs c.1 c.2.2.2.2.2

@[fun_prop] theorem polyTime_decodedTables :
    PolyTime (fun p : (ℕ × List Table) × List PermutationTables.Word =>
      decodedTables p.1.1 p.1.2 p.2) := by
  unfold decodedTables
  fun_prop

@[fun_prop] theorem polyTime_complementPoints :
    PolyTime (fun p : ℕ × List Bool => complementPoints p.1 p.2) := by
  unfold complementPoints
  fun_prop

@[fun_prop] theorem polyTime_fixedCount :
    PolyTime (fun p : ℕ × List Bool => fixedCount p.1 p.2) := by
  unfold fixedCount
  fun_prop

@[fun_prop] theorem polyTime_fixes :
    PolyTime (fun p : ℕ × List Table × List Bool => fixes p.1 p.2.1 p.2.2) := by
  unfold fixes
  fun_prop

@[fun_prop] theorem polyTime_reaches :
    PolyTime (fun p : ℕ × List Table × List Bool × ℕ × List PermutationTables.Word =>
      reaches p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold reaches
  fun_prop

@[fun_prop] theorem polyTime_factor :
    PolyTime (fun p : (ℕ × List Table × List Table) × Factor =>
      factor p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold factor
  fun_prop

variable {α : Type} [Primcodable α] [BitEncoding α]

@[fun_prop] theorem polyTime_factor_comp
    {n : α → ℕ} {gs hs : α → List Table} {f : α → Factor}
    (hn : PolyTime n) (hg : PolyTime gs) (hh : PolyTime hs) (hf : PolyTime f) :
    PolyTime (fun a => factor (n a) (gs a) (hs a) (f a)) :=
  PolyTime.comp (f := fun a => ((n a, gs a, hs a), f a))
    polyTime_factor (PolyTime.pair (PolyTime.pair hn (PolyTime.pair hg hh)) hf)

@[fun_prop] theorem polyTime_cycleTable :
    PolyTime (fun p : (ℕ × List Table × List Table) × List Factor =>
      cycleTable p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hs : PolyTime (fun p : (ℕ × List Table × List Table) × Table × Factor =>
      mul p.1.1 p.2.1 (factor p.1.1 p.1.2.1 p.1.2.2 p.2.2)) := by
    fun_prop
  have hf := PolyTime.foldl
    (g := fun p : ℕ × List Table × List Table => fun t f =>
      mul p.1 t (factor p.1 p.2.1 p.2.2 f)) hs 3 fun p t f => by
      have h := length_enc_table_le
        (le_of_eq (length_mul p.1 t (factor p.1 p.2.1 p.2.2 f)))
        (mul_entry_le p.1 t (factor p.1 p.2.1 p.2.2 f))
      have hn : p.1 ≤ (enc p).length := by rw [length_enc_prod, length_enc_nat]; omega
      have hp := Nat.pow_le_pow_left (by omega : p.1 + 2 ≤ (enc p).length + 2) 3
      omega
  exact PolyTime.comp
    (f := fun p : (ℕ × List Table × List Table) × List Factor =>
      (p.1, List.range p.1.1, p.2)) hf (by fun_prop)

@[fun_prop] theorem polyTime_cycleTable_comp
    {n : α → ℕ} {gs hs : α → List Table} {f : α → List Factor}
    (hn : PolyTime n) (hg : PolyTime gs) (hh : PolyTime hs) (hf : PolyTime f) :
    PolyTime (fun a => cycleTable (n a) (gs a) (hs a) (f a)) :=
  PolyTime.comp (f := fun a => ((n a, gs a, hs a), f a))
    polyTime_cycleTable (PolyTime.pair (PolyTime.pair hn (PolyTime.pair hg hh)) hf)

@[fun_prop] theorem polyTime_baseCheck :
    PolyTime (fun p :
      ℕ × List Table × List Table × List Bool × ℕ × List PermutationTables.Word =>
        baseCheck p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold baseCheck
  fun_prop

@[fun_prop] theorem polyTime_cycleValid :
    PolyTime (fun p : ℕ × Table => cycleValid p.1 p.2) := by
  unfold cycleValid
  have hp : PolyTime (fun p : ℕ × Table => decide (supportCount p.1 p.2).Prime) :=
    PolyTime.comp (f := fun p : ℕ × Table => supportCount p.1 p.2)
      PolyTime.prime polyTime_supportCount
  exact PolyTime.comp
    (g := fun p : Bool × Bool => p.1 && p.2)
    (f := fun p : ℕ × Table =>
      (cycleCheck p.1 p.2 && decide (supportCount p.1 p.2).Prime,
        decide (supportCount p.1 p.2 + 3 ≤ p.1))) PolyTime.and (by fun_prop)

@[fun_prop] theorem polyTime_cycleValid_comp
    {n : α → ℕ} {t : α → Table} (hn : PolyTime n) (ht : PolyTime t) :
    PolyTime (fun a => cycleValid (n a) (t a)) :=
  PolyTime.comp (f := fun a => (n a, t a)) polyTime_cycleValid (PolyTime.pair hn ht)

@[fun_prop] theorem polyTime_claimCheck :
    PolyTime (fun p : ℕ × List Table × List Table × ℕ × List Factor =>
      claimCheck p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold claimCheck
  fun_prop

@[fun_prop] theorem polyTime_decodedTables_comp
    {n : α → ℕ} {gs : α → List Table} {w : α → List PermutationTables.Word}
    (hn : PolyTime n) (hg : PolyTime gs) (hw : PolyTime w) :
    PolyTime (fun a => decodedTables (n a) (gs a) (w a)) :=
  PolyTime.comp (f := fun a => ((n a, gs a), w a))
    polyTime_decodedTables (PolyTime.pair (PolyTime.pair hn hg) hw)

@[fun_prop] theorem polyTime_baseCheck_comp
    {n b : α → ℕ} {gs hs : α → List Table} {m : α → List Bool}
    {w : α → List PermutationTables.Word}
    (hn : PolyTime n) (hg : PolyTime gs) (hh : PolyTime hs)
    (hm : PolyTime m) (hb : PolyTime b) (hw : PolyTime w) :
    PolyTime (fun a => baseCheck (n a) (gs a) (hs a) (m a) (b a) (w a)) :=
  PolyTime.comp (f := fun a => (n a, gs a, hs a, m a, b a, w a))
    polyTime_baseCheck
    (PolyTime.pair hn (PolyTime.pair hg (PolyTime.pair hh
      (PolyTime.pair hm (PolyTime.pair hb hw)))))

@[fun_prop] theorem polyTime_claimCheck_comp
    {n tag : α → ℕ} {gs hs : α → List Table} {f : α → List Factor}
    (hn : PolyTime n) (hg : PolyTime gs) (hh : PolyTime hs)
    (ht : PolyTime tag) (hf : PolyTime f) :
    PolyTime (fun a => claimCheck (n a) (gs a) (hs a) (tag a) (f a)) :=
  PolyTime.comp (f := fun a => (n a, gs a, hs a, tag a, f a))
    polyTime_claimCheck
    (PolyTime.pair hn (PolyTime.pair hg (PolyTime.pair hh (PolyTime.pair ht hf))))

@[fun_prop] theorem polyTime_check :
    PolyTime (fun p : (ℕ × List Table) × Certificate => check p.1.1 p.1.2 p.2) := by
  unfold check
  fun_prop

end TauCeti.CertificateRuntime
