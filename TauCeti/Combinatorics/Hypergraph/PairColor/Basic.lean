/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod

/-!
# Coherent colors on ordered distinct pairs

A `PairColorSystem` colors ordered pairs of distinct vertices. Its palette carries an
involution describing how colors change when the vertices are exchanged. This permits both
symmetric colors and genuinely oriented colors in the lower skeleton of a hypergraph complex.

`PairColorSystem.colorOfPair` extends the coloring to all vertex pairs with values in `Option`:
only diagonal pairs have color `none`. `PairColorSystem.ofRaw` makes any directed coloring
coherent by recording its colors in both orientations, using the product palette.
`PairColorSystem.relabel` renames the palette along an equivalence.
`PairColorSystem.split` refines a coloring by a symmetric labelling of the unordered pairs.
`PairColorSystem.comap` restricts a coloring along a vertex embedding, preserving the palette.
`coordPair` extracts the ordered distinct pair of two coordinates of an injective tuple, and
`card_filter_coordPair_mem_le` counts the injective triples with a coordinate pair in a given set.
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

/-- Rename the palette of a coherent coloring along an equivalence, conjugating the reversal. -/
def relabel {κ' : Type*} (S : PairColorSystem κ V) (e : κ ≃ κ') : PairColorSystem κ' V where
  color p := e (S.color p)
  rev c := e (S.rev (e.symm c))
  rev_involutive c := by simp [S.rev_rev]
  color_rev p := by simp [S.color_rev]

@[simp]
theorem relabel_color {κ' : Type*} (S : PairColorSystem κ V) (e : κ ≃ κ')
    (p : {p : V × V // p.1 ≠ p.2}) : (S.relabel e).color p = e (S.color p) := (rfl)

@[simp]
theorem relabel_rev {κ' : Type*} (S : PairColorSystem κ V) (e : κ ≃ κ') (c : κ') :
    (S.relabel e).rev c = e (S.rev (e.symm c)) := (rfl)

variable {ι : Type*}

/-- Split a coherent pair coloring by a symmetric labelling of the unordered vertex pairs: the
color of an ordered distinct pair `(u, v)` becomes its original color together with the label
of `s(u, v)`. Reversal reverses the original color and keeps the label. -/
def split (S : PairColorSystem κ V) (f : Sym2 V → ι) : PairColorSystem (κ × ι) V where
  color p := (S.color p, f s(p.1.1, p.1.2))
  rev c := (S.rev c.1, c.2)
  rev_involutive c := by simp
  color_rev p := by simp [S.color_rev, Sym2.eq_swap]

@[simp]
theorem split_color (S : PairColorSystem κ V) (f : Sym2 V → ι) (p : {p : V × V // p.1 ≠ p.2}) :
    (S.split f).color p = (S.color p, f s(p.1.1, p.1.2)) := (rfl)

@[simp]
theorem split_rev (S : PairColorSystem κ V) (f : Sym2 V → ι) (c : κ × ι) :
    (S.split f).rev c = (S.rev c.1, c.2) := (rfl)

/-- The total split color is the total original color together with the label of the pair. -/
theorem colorOfPair_split (S : PairColorSystem κ V) (f : Sym2 V → ι) (u v : V) :
    (S.split f).colorOfPair u v = (S.colorOfPair u v).map fun c ↦ (c, f s(u, v)) := by
  by_cases h : u = v
  · subst h
    simp
  · simp [h]

@[simp]
theorem colorOfPair_split_eq_some_iff (S : PairColorSystem κ V) (f : Sym2 V → ι) (u v : V)
    (c : κ) (i : ι) :
    (S.split f).colorOfPair u v = some (c, i) ↔ S.colorOfPair u v = some c ∧ f s(u, v) = i := by
  rw [colorOfPair_split]
  cases S.colorOfPair u v <;> simp

/-- Restrict a coherent pair coloring along a vertex embedding. The palette and its
reversal are unchanged. -/
def comap {W : Type*} (S : PairColorSystem κ W) (f : V ↪ W) : PairColorSystem κ V where
  color p := S.color ⟨(f p.1.1, f p.1.2), f.injective.ne p.2⟩
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev p := S.color_rev ⟨(f p.1.1, f p.1.2), f.injective.ne p.2⟩

@[simp]
theorem comap_color {W : Type*} (S : PairColorSystem κ W) (f : V ↪ W)
    (p : {p : V × V // p.1 ≠ p.2}) :
    (S.comap f).color p = S.color ⟨(f p.1.1, f p.1.2), f.injective.ne p.2⟩ := (rfl)

@[simp]
theorem comap_rev {W : Type*} (S : PairColorSystem κ W) (f : V ↪ W) (c : κ) :
    (S.comap f).rev c = S.rev c := (rfl)

@[simp]
theorem colorOfPair_comap {W : Type*} (S : PairColorSystem κ W) (f : V ↪ W) (u v : V) :
    (S.comap f).colorOfPair u v = S.colorOfPair (f u) (f v) := by
  by_cases h : u = v
  · subst h
    simp
  · simp [h, f.injective.ne h]

@[simp]
theorem comap_refl (S : PairColorSystem κ V) : S.comap (.refl V) = S := by
  ext <;> rfl

@[simp]
theorem comap_comap {W U : Type*} (S : PairColorSystem κ U) (g : W ↪ U) (f : V ↪ W) :
    (S.comap g).comap f = S.comap (f.trans g) := by
  ext <;> rfl

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

open Finset in
/-- The injective triples whose coordinate pair on the roles `i` and `j` lies in `E` are at most
`|E| |V|` many: such a triple is determined by that pair and its third coordinate `k`. -/
theorem card_filter_coordPair_mem_le {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset {p : V × V // p.1 ≠ p.2}) {i j k : Fin 3} (hij : i ≠ j)
    (hl : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) :
    #{x : {x : Fin 3 → V // Function.Injective x} | coordPair x i j hij ∈ E} ≤
      #E * Fintype.card V := by
  rw [← card_univ (α := V), ← card_product]
  refine card_le_card_of_injOn (fun x ↦ (coordPair x i j hij, x.1 k))
    (fun x hx ↦ mem_product.2 ⟨(mem_filter.1 hx).2, mem_univ _⟩) fun x _ y _ hxy ↦ ?_
  simp only [Prod.mk.injEq, Subtype.ext_iff, coe_coordPair] at hxy
  obtain ⟨⟨hi, hj⟩, hk⟩ := hxy
  refine Subtype.ext (funext fun l ↦ ?_)
  obtain rfl | rfl | rfl := hl l
  exacts [hi, hj, hk]

end TauCeti
