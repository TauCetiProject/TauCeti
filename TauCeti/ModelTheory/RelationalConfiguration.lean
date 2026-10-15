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

A **relational configuration** on a vertex type `V` interprets the relational part of a
one-sorted first-order language `L`: it is a truth value for every atom `R(v₁, …, vₙ)`, an `n`-ary
relation symbol of `L` together with an `n`-tuple of vertices. Tuple entries may repeat, so a
configuration also records the value of `R(v, v)` and the like; nothing here assumes distinct
coordinates.

Configurations carry the product σ-algebra, with one Boolean coordinate per atom. Pulling a
configuration back along a map of vertex types `f : V → W` reads each atom of `V` at its image
atom of `W`. This **restriction** is measurable and functorial: restriction along the identity is
the identity, and restriction along a composite is the composite of the restrictions in the
opposite order.

The function symbols of `L` are permitted and play no role. A structure of `L` determines a
configuration by deciding its relations (`ofStructure`).

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

/-- An atom of the language `L` over the vertex type `V`: an `n`-ary relation symbol together with
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
theorem Atom.induction_atom {motive : Atom L V → Prop}
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

/-- The atoms relabelled from `Fin m` are relabelled from `Fin n` for every `n ≥ m`. -/
private theorem Atom.exists_map_val_of_le {m n : ℕ} (hmn : m ≤ n) {a : Atom L ℕ}
    (ha : ∃ b : Atom L (Fin m), b.map Fin.val = a) : ∃ b : Atom L (Fin n), b.map Fin.val = a := by
  obtain ⟨b, rfl⟩ := ha
  -- `Fin.val ∘ Fin.castLE hmn` is `Fin.val` by definition; no rewrite lemma states it.
  exact ⟨b.map (Fin.castLE hmn), by rw [← Atom.map_comp]; rfl⟩

/-- Every finite set of atoms over `ℕ` has its vertices below some bound `n`, so its atoms are
relabelled from atoms of `Fin n`. -/
theorem Atom.exists_forall_map_val (J : Finset (Atom L ℕ)) :
    ∃ n, ∀ a ∈ J, ∃ b : Atom L (Fin n), b.map Fin.val = a := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a J _ ih =>
    obtain ⟨m, hm⟩ := ih
    -- The single atom `a` has its finitely many vertices below some bound `k`.
    obtain ⟨k, hk⟩ : ∃ k, ∃ b : Atom L (Fin k), b.map Fin.val = a := by
      induction a using Atom.induction_atom with
      | h R x =>
        obtain ⟨k, hk⟩ := Finset.exists_nat_subset_range (Finset.univ.image x)
        exact ⟨k, atom R fun i => ⟨x i, Finset.mem_range.1 (hk (Finset.mem_image_of_mem _
          (Finset.mem_univ i)))⟩, by rw [Atom.map_atom]; rfl⟩
    refine ⟨max k m, fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact exists_map_val_of_le (le_max_left k m) hk
    · exact exists_map_val_of_le (le_max_right k m) (hm b hb)

/-! ### Configurations -/

/-- The value of a configuration at the atom `R(x)`. -/
def eval (c : RelationalConfiguration L V) (a : Atom L V) : Bool := c a

/-- Build a configuration from its value at every atom. A bare function on atoms only unfolds to a
configuration, so this gives it the configuration type, with `eval_mk` to rewrite with. -/
def mk (c : Atom L V → Bool) : RelationalConfiguration L V := c

@[simp]
theorem eval_mk (c : Atom L V → Bool) (a : Atom L V) : (mk c).eval a = c a := (rfl)

/-- Configurations are determined by their values at atoms. -/
@[ext]
theorem ext {c d : RelationalConfiguration L V} (h : ∀ a, c.eval a = d.eval a) : c = d :=
  funext h

/-- A language with countably many relation symbols of each arity has countably many atoms over a
countable vertex type. -/
instance [∀ n, Countable (L.Relations n)] [Countable V] : Countable (Atom L V) :=
  inferInstanceAs (Countable (Σ n, L.Relations n × (Fin n → V)))

/-- Configurations carry the product σ-algebra, one Boolean coordinate per atom. -/
instance : MeasurableSpace (RelationalConfiguration L V) :=
  inferInstanceAs (MeasurableSpace (Atom L V → Bool))

/-- Reading off one atom is measurable. -/
@[fun_prop]
theorem measurable_eval (a : Atom L V) :
    Measurable fun c : RelationalConfiguration L V => c.eval a :=
  measurable_pi_apply (X := fun _ : Atom L V => Bool) a

/-- Building a configuration from its values at atoms is measurable. -/
@[fun_prop]
theorem measurable_mk : Measurable (mk : (Atom L V → Bool) → RelationalConfiguration L V) :=
  measurable_id

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

/-! ### Extension by `false` -/

/-- Relabelling atoms along an injective vertex map is injective. -/
theorem Atom.map_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (Atom.map (L := L) f) := by
  rintro ⟨n, R, x⟩ ⟨m, S, y⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  obtain ⟨rfl, h⟩ := Prod.mk.inj (eq_of_heq h)
  cases hf.comp_left h
  rfl

/-- Extend a configuration along a vertex map `f : V → W`: an atom of `W` relabelled from an atom
of `V` takes the value of such an atom, and every other atom is false. Along an injective map the
relabelled atom is unique (`eval_extend_map`), so restriction undoes extension
(`restrict_extend`). -/
noncomputable def extend (f : V → W) (c : RelationalConfiguration L V) :
    RelationalConfiguration L W :=
  mk (Function.extend (Atom.map f) c.eval fun _ => false)

/-- The value of an extension at an atom, through `Function.extend`. -/
theorem eval_extend (f : V → W) (c : RelationalConfiguration L V) (a : Atom L W) :
    (c.extend f).eval a = Function.extend (Atom.map f) c.eval (fun _ => false) a := (rfl)

/-- Along an injective map, the relabelled atom `R(f ∘ x)` of the extension takes the value of the
atom `R(x)`. -/
@[simp]
theorem eval_extend_map {f : V → W} (hf : Function.Injective f) (c : RelationalConfiguration L V)
    (a : Atom L V) : (c.extend f).eval (a.map f) = c.eval a := by
  rw [eval_extend, (Atom.map_injective hf).extend_apply]

/-- An atom of `W` that is not relabelled from an atom of `V` is false in the extension. -/
theorem eval_extend_of_forall_ne {f : V → W} (c : RelationalConfiguration L V) {a : Atom L W}
    (ha : ∀ b : Atom L V, b.map f ≠ a) : (c.extend f).eval a = false := by
  rw [eval_extend, Function.extend_apply' _ _ a fun ⟨b, hb⟩ => ha b hb]

/-- Along an injective map, restriction undoes extension. -/
@[simp]
theorem restrict_extend {f : V → W} (hf : Function.Injective f)
    (c : RelationalConfiguration L V) : (c.extend f).restrict f = c :=
  ext fun a => by rw [eval_restrict, eval_extend_map hf]

/-- Extension is measurable: each atom coordinate of the extension is an atom coordinate of the
source or constantly false. -/
@[fun_prop]
theorem measurable_extend (f : V → W) : Measurable (extend (L := L) f) := by
  refine measurable_iff.2 fun a => ?_
  classical
  by_cases ha : ∃ b : Atom L V, b.map f = a
  · simpa only [eval_extend, Function.extend_def, ha, ↓reduceDIte] using measurable_eval _
  · simpa only [eval_extend, Function.extend_def, ha, ↓reduceDIte] using measurable_const

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
