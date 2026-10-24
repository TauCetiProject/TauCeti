/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Option.Basic

/-!
# Coherent colors on ordered distinct pairs

A `PairColorSystem` colors ordered pairs of distinct vertices. Its palette carries an
involution describing how colors change when the vertices are exchanged. This permits both
symmetric colors and genuinely oriented colors in the lower skeleton of a hypergraph complex.

`PairColorSystem.colorOfPair` extends the coloring to all vertex pairs with values in `Option`:
only diagonal pairs have color `none`. `PairColorSystem.ofRaw` makes any directed coloring
coherent by recording its colors in both orientations, using the product palette.
`coordPair` extracts the ordered distinct pair of two coordinates of an injective tuple.
-/

public section

namespace TauCeti

/-- A coloring of ordered distinct pairs, coherent with an involution of the palette. -/
structure PairColorSystem (κ : Type*) (V : Type*) where
  /-- The color of an ordered distinct pair. -/
  color : {p : V × V // p.1 ≠ p.2} → κ
  /-- Palette reversal. -/
  rev : κ → κ
  /-- Reversing a color twice recovers it. -/
  rev_involutive : Function.Involutive rev
  /-- Exchanging the vertices reverses their color. -/
  color_rev : ∀ p, color ⟨p.val.swap, p.property.symm⟩ = rev (color p)

namespace PairColorSystem

variable {κ V : Type*}

/-- Pair-color systems are determined by their coloring and palette reversal. -/
@[ext]
theorem ext {S T : PairColorSystem κ V} (hcolor : ∀ p, S.color p = T.color p)
    (hrev : ∀ c, S.rev c = T.rev c) : S = T := by
  cases S
  cases T
  congr <;> exact funext ‹_›

@[simp]
theorem rev_rev (S : PairColorSystem κ V) (c : κ) : S.rev (S.rev c) = c :=
  S.rev_involutive c

/-- The total pair color, with `none` exactly on the diagonal. -/
noncomputable def colorOfPair (S : PairColorSystem κ V) (u v : V) : Option κ := by
  classical
  exact if h : u ≠ v then some (S.color ⟨(u, v), h⟩) else none

@[simp]
theorem colorOfPair_self (S : PairColorSystem κ V) (u : V) :
    S.colorOfPair u u = none := by
  simp [colorOfPair]

/-- Off the diagonal, the total color is the original color. -/
@[simp]
theorem colorOfPair_of_ne (S : PairColorSystem κ V) {u v : V} (h : u ≠ v) :
    S.colorOfPair u v = some (S.color ⟨(u, v), h⟩) := by
  simp [colorOfPair, h]

@[simp]
theorem colorOfPair_eq_none_iff (S : PairColorSystem κ V) (u v : V) :
    S.colorOfPair u v = none ↔ u = v := by
  classical
  simp [colorOfPair]

/-- A prescribed pair color implies distinctness and identifies the underlying color. -/
theorem colorOfPair_eq_some_iff (S : PairColorSystem κ V) (u v : V) (c : κ) :
    S.colorOfPair u v = some c ↔ ∃ h : u ≠ v, S.color ⟨(u, v), h⟩ = c := by
  classical
  by_cases h : u ≠ v <;> simp [colorOfPair, h]

/-- Exchanging vertices applies palette reversal to the total color. -/
theorem colorOfPair_swap (S : PairColorSystem κ V) (u v : V) :
    S.colorOfPair v u = (S.colorOfPair u v).map S.rev := by
  by_cases h : u ≠ v
  · rw [S.colorOfPair_of_ne h, S.colorOfPair_of_ne h.symm, Option.map_some]
    exact congrArg some (S.color_rev ⟨(u, v), h⟩)
  · obtain rfl := not_ne_iff.mp h
    simp

/-- A reversed pair has the reversed color exactly when the original pair has that color. -/
theorem colorOfPair_swap_eq_some_iff (S : PairColorSystem κ V) (u v : V) (c : κ) :
    S.colorOfPair v u = some (S.rev c) ↔ S.colorOfPair u v = some c := by
  rw [S.colorOfPair_swap]
  simpa only [Option.map_some] using
    (Option.map_injective S.rev_involutive.injective).eq_iff
      (a := S.colorOfPair u v) (b := some c)

/-- Make a directed coloring coherent by retaining the colors in both orientations.
The palette is `κ × κ`, and reversal exchanges the coordinates. -/
def ofRaw (color : {p : V × V // p.1 ≠ p.2} → κ) : PairColorSystem (κ × κ) V where
  color p := (color p, color ⟨p.val.swap, p.property.symm⟩)
  rev := Prod.swap
  rev_involutive := Prod.swap_swap
  color_rev _ := rfl

@[simp]
theorem ofRaw_color (color : {p : V × V // p.1 ≠ p.2} → κ)
    (p : {p : V × V // p.1 ≠ p.2}) :
    (ofRaw color).color p = (color p, color ⟨p.val.swap, p.property.symm⟩) := (rfl)

@[simp]
theorem ofRaw_rev (color : {p : V × V // p.1 ≠ p.2} → κ) (c : κ × κ) :
    (ofRaw color).rev c = c.swap := (rfl)

end PairColorSystem

/-- The ordered distinct pair formed by two coordinates of an injective tuple. -/
def coordPair {ι V : Type*} (x : {x : ι → V // Function.Injective x}) (i j : ι)
    (hij : i ≠ j) : {p : V × V // p.1 ≠ p.2} :=
  ⟨(x.1 i, x.1 j), fun h ↦ hij (x.2 h)⟩

/-- The underlying pair of `coordPair x i j hij` consists of the `i`th and `j`th coordinates. -/
@[simp]
theorem coe_coordPair {ι V : Type*} (x : {x : ι → V // Function.Injective x}) (i j : ι)
    (hij : i ≠ j) : (coordPair x i j hij : V × V) = (x.1 i, x.1 j) := (rfl)

/-- The color of a coordinate pair is the total pair color of the two coordinates. -/
theorem PairColorSystem.color_coordPair_eq_iff {ι κ V : Type*} (C : PairColorSystem κ V)
    {x : {x : ι → V // Function.Injective x}} {i j : ι} (hij : i ≠ j) {k : κ} :
    C.color (coordPair x i j hij) = k ↔ C.colorOfPair (x.1 i) (x.1 j) = some k := by
  rw [C.colorOfPair_of_ne (fun h ↦ hij (x.2 h)), Option.some_inj]
  rfl

end TauCeti
