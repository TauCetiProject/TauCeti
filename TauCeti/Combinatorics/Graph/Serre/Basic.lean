/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Graphs with edge reversal

A Serre graph has directed edges paired by a fixed-point-free reversal. In particular, a loop
still has two distinct directions, and parallel edges remain distinct. The quiver associated to
a Serre graph keeps those directed edge identities, so its paths can be used for reduced paths,
graph groups, and labelled-graph arguments.

The simple-graph construction takes its edge set from Mathlib's darts. It provides the familiar
loopless example while retaining the reversal structure used for general graphs.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v w x y z

namespace TauCeti

/-- A graph in Serre's sense: every directed edge has a distinct reverse edge. Loops and parallel
edges are permitted. -/
structure SerreGraph where
  /-- Vertices. -/
  V : Type u
  /-- Directed edges, or darts. -/
  E : Type v
  /-- Initial vertex of a dart. -/
  src : E → V
  /-- Reverse dart. -/
  rev : E → E
  /-- Reversing twice does nothing. -/
  rev_rev : ∀ e, rev (rev e) = e
  /-- A dart differs from its reverse, even when it is a loop. -/
  rev_ne : ∀ e, rev e ≠ e

namespace SerreGraph

variable (Γ : SerreGraph.{u, v})

/-- Terminal vertex of a dart. -/
def tgt (e : Γ.E) : Γ.V := Γ.src (Γ.rev e)

/-- A dart ends where its reverse starts. -/
theorem tgt_def (e : Γ.E) : Γ.tgt e = Γ.src (Γ.rev e) := (rfl)

@[simp] theorem src_rev (e : Γ.E) : Γ.src (Γ.rev e) = Γ.tgt e := by
  simp only [tgt]

@[simp] theorem tgt_rev (e : Γ.E) : Γ.tgt (Γ.rev e) = Γ.src e := by
  simp only [tgt, Γ.rev_rev]

theorem rev_injective : Function.Injective Γ.rev := by
  intro e f h
  simpa only [Γ.rev_rev] using congrArg Γ.rev h

/-- An orientation chooses one dart from each reverse pair. -/
def IsOrientation (O : Set Γ.E) : Prop := ∀ e, e ∈ O ↔ Γ.rev e ∉ O

theorem isOrientation_iff (O : Set Γ.E) :
    Γ.IsOrientation O ↔ ∀ e, e ∈ O ↔ Γ.rev e ∉ O := Iff.rfl

theorem IsOrientation.mem_rev_iff {O : Set Γ.E} (hO : Γ.IsOrientation O) (e : Γ.E) :
    Γ.rev e ∈ O ↔ e ∉ O := by
  simpa only [Γ.rev_rev] using hO (Γ.rev e)

theorem IsOrientation.rev_notMem_of_mem {O : Set Γ.E} (hO : Γ.IsOrientation O)
    (e : Γ.E) (he : e ∈ O) : Γ.rev e ∉ O :=
  (hO e).mp he

/-- The quiver whose arrows are the actual darts from their source to their target. -/
@[expose, instance_reducible] def toQuiver : Quiver Γ.V where
  Hom a b := {e : Γ.E // Γ.src e = a ∧ Γ.tgt e = b}

attribute [instance] toQuiver

/-- Reversal on the quiver associated to a Serre graph. -/
@[instance_reducible] def toQuiverHasInvolutiveReverse :
    @Quiver.HasInvolutiveReverse Γ.V Γ.toQuiver := by
  letI : Quiver Γ.V := Γ.toQuiver
  exact {
    reverse' := fun {a b} e =>
      ⟨Γ.rev e.1, ⟨(Γ.src_rev e.1).trans e.2.2,
        by simpa only [tgt_rev] using e.2.1⟩⟩
    inv' := by
      intro a b e
      apply Subtype.ext
      exact Γ.rev_rev e.1 }

attribute [instance] toQuiverHasInvolutiveReverse

@[simp] theorem reverse_val {a b : Γ.V}
    (f : Quiver.Hom a b) :
    (Quiver.reverse f).1 = Γ.rev f.1 := (rfl)

/-- A dart as an arrow of the associated quiver. -/
def dart (e : Γ.E) : Quiver.Hom (Γ.src e) (Γ.tgt e) :=
  ⟨e, rfl, rfl⟩

@[simp] theorem dart_val (e : Γ.E) : (Γ.dart e).1 = e := by
  simp only [dart]

/-- An indexed path in a Serre graph is a path of its associated quiver. -/
abbrev Path (a b : Γ.V) : Type (max u v) := Quiver.Path a b

attribute [simp] SerreGraph.rev_rev

/-- A morphism of Serre graphs maps vertices and darts and preserves incidence and reversal. -/
structure Hom (Δ : SerreGraph.{w, x}) where
  /-- Vertex map. -/
  mapV : Γ.V → Δ.V
  /-- Dart map. -/
  mapE : Γ.E → Δ.E
  /-- Sources are preserved. -/
  map_src : ∀ e, Δ.src (mapE e) = mapV (Γ.src e)
  /-- Reversal is preserved. -/
  map_rev : ∀ e, mapE (Γ.rev e) = Δ.rev (mapE e)

attribute [simp] Hom.map_src Hom.map_rev

@[ext] theorem Hom.ext {Δ : SerreGraph.{w, x}} {f g : Γ.Hom Δ}
    (hV : f.mapV = g.mapV) (hE : f.mapE = g.mapE) : f = g := by
  cases f
  cases g
  congr

@[simp] theorem Hom.map_tgt {Δ : SerreGraph.{w, x}} (f : Γ.Hom Δ) (e : Γ.E) :
    Δ.tgt (f.mapE e) = f.mapV (Γ.tgt e) := by
  simp only [tgt, ← f.map_rev, f.map_src]

/-- The quiver prefunctor underlying a Serre-graph morphism. -/
@[expose] def Hom.toPrefunctor {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) : Γ.V ⥤q Δ.V where
  obj := f.mapV
  map := fun e => ⟨f.mapE e.1,
    by simpa only [f.map_src] using congrArg f.mapV e.2.1,
    by simpa only [f.map_tgt] using congrArg f.mapV e.2.2⟩

@[simp] theorem Hom.toPrefunctor_obj {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) (a : Γ.V) : f.toPrefunctor.obj a = f.mapV a := rfl

@[simp] theorem Hom.toPrefunctor_map_val {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) {a b : Γ.V} (e : Quiver.Hom a b) :
    (f.toPrefunctor.map e).1 = f.mapE e.1 := rfl

/-- Identity morphism of a Serre graph. -/
def Hom.id : Γ.Hom Γ where
  mapV := _root_.id
  mapE := _root_.id
  map_src := by intros; rfl
  map_rev := by intros; rfl

@[simp] theorem Hom.id_mapV : (Hom.id Γ).mapV = _root_.id := by
  simp only [Hom.id]
@[simp] theorem Hom.id_mapE : (Hom.id Γ).mapE = _root_.id := by
  simp only [Hom.id]

/-- Compose Serre-graph morphisms. -/
def Hom.comp {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}
    (g : Δ.Hom Θ) (f : Γ.Hom Δ) : Γ.Hom Θ where
  mapV := g.mapV ∘ f.mapV
  mapE := g.mapE ∘ f.mapE
  map_src := by intro e; simp [g.map_src, f.map_src]
  map_rev := by intro e; simp [g.map_rev, f.map_rev]

@[simp] theorem Hom.comp_mapV {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}
    (g : Δ.Hom Θ) (f : Γ.Hom Δ) : (Hom.comp g f).mapV = g.mapV ∘ f.mapV := by
  simp only [Hom.comp]

@[simp] theorem Hom.comp_mapE {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}
    (g : Δ.Hom Θ) (f : Γ.Hom Δ) : (Hom.comp g f).mapE = g.mapE ∘ f.mapE := by
  simp only [Hom.comp]

@[simp] theorem Hom.id_comp {Δ : SerreGraph.{w, x}} (f : Γ.Hom Δ) :
    Hom.comp (Hom.id Δ) f = f := by
  apply Hom.ext <;> rfl

@[simp] theorem Hom.comp_id {Δ : SerreGraph.{w, x}} (f : Γ.Hom Δ) :
    Hom.comp f (Hom.id Γ) = f := by
  apply Hom.ext <;> rfl

theorem Hom.comp_assoc {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}
    {Ξ : SerreGraph} (f : Γ.Hom Δ) (g : Δ.Hom Θ) (h : Θ.Hom Ξ) :
    Hom.comp h (Hom.comp g f) = Hom.comp (Hom.comp h g) f := by
  apply Hom.ext <;> rfl

@[simp] theorem Hom.toPrefunctor_id :
    (Hom.id Γ).toPrefunctor = Prefunctor.id Γ.V := by
  unfold Hom.id Hom.toPrefunctor Prefunctor.id
  rfl

@[simp] theorem Hom.toPrefunctor_comp {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}
    (g : Δ.Hom Θ) (f : Γ.Hom Δ) :
    (Hom.comp g f).toPrefunctor = f.toPrefunctor.comp g.toPrefunctor := by
  unfold Hom.comp Hom.toPrefunctor Prefunctor.comp
  rfl

instance Hom.toPrefunctor_mapReverse {Δ : SerreGraph.{w, x}} (f : Γ.Hom Δ) :
    f.toPrefunctor.MapReverse where
  map_reverse' e := by
    apply Subtype.ext
    simp only [Hom.toPrefunctor_map_val, Γ.reverse_val, Δ.reverse_val, f.map_rev]

/-- The rose on a type of petals. Each petal is a loop with two distinct darts. -/
@[expose] def rose (α : Type w) : SerreGraph.{0, w} where
  V := PUnit
  E := α × Bool
  src := fun _ => PUnit.unit
  rev := fun e => (e.1, !e.2)
  rev_rev := by intro ⟨a, b⟩; cases b <;> rfl
  rev_ne := by intro ⟨a, b⟩; cases b <;> simp

@[simp] theorem rose_src (α : Type w) (e : α × Bool) :
    (rose α).src e = PUnit.unit := rfl

@[simp] theorem rose_rev (α : Type w) (e : α × Bool) :
    (rose α).rev e = (e.1, !e.2) := rfl

/-- Each dart of a rose is a loop. -/
@[simp] theorem rose_tgt (α : Type w) (e : α × Bool) :
    (rose α).tgt e = PUnit.unit := rfl

/-- Positive darts form an orientation of a rose. -/
theorem rose_isOrientation (α : Type w) :
    (rose α).IsOrientation {e | e.2 = true} := by
  intro ⟨a, b⟩
  -- The carrier `(rose α).E` reduces definitionally to `α × Bool` here.
  change (b = true) ↔ ¬(!b = true)
  cases b <;> decide

end SerreGraph

end TauCeti

namespace SimpleGraph

/-- The Serre graph of a simple graph has its darts as directed edges. -/
@[expose] def toSerreGraph {V : Type u} (G : SimpleGraph V) : TauCeti.SerreGraph.{u, u} where
  V := V
  E := G.Dart
  src := fun e => e.fst
  rev := SimpleGraph.Dart.symm
  rev_rev := SimpleGraph.Dart.symm_symm
  rev_ne := SimpleGraph.Dart.symm_ne

@[simp] theorem toSerreGraph_src {V : Type u} (G : SimpleGraph V) (e : G.Dart) :
    (toSerreGraph G).src e = e.fst := rfl

@[simp] theorem toSerreGraph_rev {V : Type u} (G : SimpleGraph V) (e : G.Dart) :
    (toSerreGraph G).rev e = e.symm := rfl

@[simp] theorem toSerreGraph_tgt {V : Type u} (G : SimpleGraph V) (e : G.Dart) :
    (toSerreGraph G).tgt e = e.snd := by
  exact (TauCeti.SerreGraph.tgt_def (toSerreGraph G) e).trans rfl

end SimpleGraph
