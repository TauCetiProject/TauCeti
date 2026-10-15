/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Relational configurations

A **relational configuration** of a one-sorted relational signature `L` on a vertex type `V` is a
truth value for every atom `R(v₁, …, vₙ)`: an `n`-ary relation symbol of `L` together with an
`n`-tuple of vertices. Tuple entries may repeat, so a configuration also records the value of
`R(v, v)` and the like; nothing here assumes distinct coordinates.

Configurations carry the product σ-algebra, with one Boolean coordinate per atom. Pulling a
configuration back along a map of vertex types `f : V → W` reads each atom of `V` at its image
atom of `W`. This **restriction** is measurable and functorial: restriction along the identity is
the identity, and restriction along a composite is the composite of the restrictions in the
opposite order.

The function symbols of `L` play no role. A structure of `L` determines a configuration by
deciding its relations (`ofStructure`).

## Main definitions

* `TauCeti.RelationalConfiguration.Atom L V` — a relation symbol of `L` with a tuple of vertices;
* `TauCeti.RelationalConfiguration L V` — a truth value for every atom;
* `TauCeti.RelationalConfiguration.restrict` — pulling a configuration back along a vertex map;
* `TauCeti.RelationalConfiguration.ofStructure` — the configuration of an `L`-structure.

## Main results

* `TauCeti.RelationalConfiguration.measurable_iff` — a map into configurations is measurable
  exactly when each atom coordinate is;
* `TauCeti.RelationalConfiguration.measurable_restrict` — restriction is measurable;
* `TauCeti.RelationalConfiguration.restrict_id` and
  `TauCeti.RelationalConfiguration.restrict_comp` — restriction is functorial.
-/

public section

open MeasureTheory

namespace TauCeti

open _root_.FirstOrder (Language)

/-- An atom of the signature `L` over the vertex type `V`: an `n`-ary relation symbol together with
an `n`-tuple of vertices, whose entries may repeat. -/
@[expose] def RelationalConfiguration.Atom (L : Language) (V : Type*) : Type _ :=
  Σ n, L.Relations n × (Fin n → V)

/-- A **relational configuration** of `L` on `V`: a truth value for every atom. -/
@[expose] def RelationalConfiguration (L : Language) (V : Type*) : Type _ :=
  RelationalConfiguration.Atom L V → Bool

namespace RelationalConfiguration

variable {L : Language} {V W X : Type*}

/-! ### Atoms -/

/-- The atom with relation symbol `R` and argument tuple `x`. -/
def atom {n : ℕ} (R : L.Relations n) (x : Fin n → V) : Atom L V := ⟨n, R, x⟩

/-- Every atom is `atom R x` for its relation symbol and tuple. -/
@[elab_as_elim]
theorem Atom.rec_atom {motive : Atom L V → Prop}
    (h : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → V), motive (atom R x)) (a : Atom L V) :
    motive a := by
  obtain ⟨n, R, x⟩ := a
  exact h R x

/-- Relabel the arguments of an atom along a vertex map. -/
def Atom.map (f : V → W) (a : Atom L V) : Atom L W := ⟨a.1, a.2.1, f ∘ a.2.2⟩

@[simp]
theorem Atom.map_atom (f : V → W) {n : ℕ} (R : L.Relations n) (x : Fin n → V) :
    (atom R x).map f = atom R (f ∘ x) := (rfl)

@[simp]
theorem Atom.map_id (a : Atom L V) : a.map id = a := (rfl)

theorem Atom.map_comp (g : W → X) (f : V → W) (a : Atom L V) :
    a.map (g ∘ f) = (a.map f).map g := (rfl)

/-! ### Configurations -/

/-- The value of a configuration at the atom `R(x)`. -/
def eval (c : RelationalConfiguration L V) (a : Atom L V) : Bool := c a

/-- Build a configuration from its value at every atom. -/
def mk (c : Atom L V → Bool) : RelationalConfiguration L V := c

@[simp]
theorem eval_mk (c : Atom L V → Bool) (a : Atom L V) : (mk c).eval a = c a := (rfl)

/-- Configurations are determined by their values at atoms. -/
@[ext]
theorem ext {c d : RelationalConfiguration L V} (h : ∀ a, c.eval a = d.eval a) : c = d :=
  funext h

/-- Configurations carry the product σ-algebra, one Boolean coordinate per atom. -/
instance : MeasurableSpace (RelationalConfiguration L V) :=
  inferInstanceAs (MeasurableSpace (Atom L V → Bool))

/-- Reading off one atom is measurable. -/
@[fun_prop]
theorem measurable_eval (a : Atom L V) :
    Measurable fun c : RelationalConfiguration L V => c.eval a :=
  measurable_pi_apply (X := fun _ : Atom L V => Bool) a

/-- A map into configurations is measurable exactly when each atom coordinate is. -/
theorem measurable_iff {Ω : Type*} [MeasurableSpace Ω] {F : Ω → RelationalConfiguration L V} :
    Measurable F ↔ ∀ a, Measurable fun ω => (F ω).eval a :=
  measurable_pi_iff (X := fun _ : Atom L V => Bool)

/-! ### Restriction -/

/-- Pull a configuration back along a vertex map: the atom `R(x)` of `V` takes the value of the
atom `R(f ∘ x)` of `W`. -/
def restrict (f : V → W) (c : RelationalConfiguration L W) : RelationalConfiguration L V :=
  mk fun a => c.eval (a.map f)

@[simp]
theorem eval_restrict (f : V → W) (c : RelationalConfiguration L W) (a : Atom L V) :
    (c.restrict f).eval a = c.eval (a.map f) := (rfl)

@[simp]
theorem restrict_id (c : RelationalConfiguration L V) : c.restrict id = c := (rfl)

/-- Restriction along a composite is the composite of the restrictions, in the opposite order. -/
theorem restrict_comp (g : W → X) (f : V → W) (c : RelationalConfiguration L X) :
    c.restrict (g ∘ f) = (c.restrict g).restrict f := (rfl)

/-- Restriction is measurable: each atom coordinate of the restriction is an atom coordinate of
the source. -/
@[fun_prop]
theorem measurable_restrict (f : V → W) :
    Measurable (restrict (L := L) f) :=
  measurable_iff.2 fun a => by simpa using measurable_eval (a.map f)

/-! ### Configurations of structures -/

open Classical in
/-- The configuration of an `L`-structure: an atom holds exactly when its relation does. -/
noncomputable def ofStructure (L : Language) (V : Type*) [L.Structure V] :
    RelationalConfiguration L V :=
  mk fun a => decide (Language.Structure.RelMap a.2.1 a.2.2)

open Classical in
@[simp]
theorem eval_ofStructure [L.Structure V] {n : ℕ} (R : L.Relations n) (x : Fin n → V) :
    (ofStructure L V).eval (atom R x) = decide (Language.Structure.RelMap R x) := (rfl)

end RelationalConfiguration

end TauCeti
