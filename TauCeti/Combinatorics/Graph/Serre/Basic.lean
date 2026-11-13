/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Graphs with edge reversal

A Serre graph has directed edges paired by a fixed-point-free reversal. In particular, a loop
still has two distinct directions, and parallel edges remain distinct. The quiver associated to
a Serre graph keeps those directed edge identities, so its paths can be used for reduced paths,
graph groups, and labelled-graph arguments.

The geometric edges of a Serre graph are the reversal pairs `{e, rev e}`; data attached to an
unoriented edge, such as the edge groups of a graph of groups, is indexed by them, and
`GeomEdge.out` chooses a dart representing each of them.

For a reversal-closed set `S` of darts, the subgraph `Γ.restrict S hS` keeps every vertex of `Γ`
and the darts in `S`.

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

/-- Terminal vertex of a dart. The body is exposed so that families indexed by vertices, such as
the vertex groups of a graph of groups, can be evaluated at `Γ.tgt e` without a cast. -/
@[expose] def tgt (e : Γ.E) : Γ.V := Γ.src (Γ.rev e)

/-- A dart ends where its reverse starts. -/
theorem tgt_def (e : Γ.E) : Γ.tgt e = Γ.src (Γ.rev e) := (rfl)

@[simp] theorem src_rev (e : Γ.E) : Γ.src (Γ.rev e) = Γ.tgt e := by
  simp only [tgt]

@[simp] theorem tgt_rev (e : Γ.E) : Γ.tgt (Γ.rev e) = Γ.src e := by
  simp only [tgt, Γ.rev_rev]

theorem rev_injective : Function.Injective Γ.rev := by
  intro e f h
  simpa only [Γ.rev_rev] using congrArg Γ.rev h

/-- The geometric edges of a Serre graph: the pairs `{e, rev e}` of mutually reverse darts. -/
def GeomEdge : Type v := Quot fun e f : Γ.E => f = Γ.rev e

/-- The geometric edge underlying a dart. -/
def toGeomEdge (e : Γ.E) : Γ.GeomEdge := Quot.mk _ e

/-- A dart and its reverse have the same underlying geometric edge. -/
@[simp] theorem toGeomEdge_rev (e : Γ.E) : Γ.toGeomEdge (Γ.rev e) = Γ.toGeomEdge e :=
  Quot.sound (Γ.rev_rev e).symm

theorem toGeomEdge_surjective : Function.Surjective Γ.toGeomEdge :=
  Quot.mk_surjective

/-- Two darts have the same geometric edge exactly when they are equal or mutually reverse. -/
theorem toGeomEdge_eq_toGeomEdge_iff {e f : Γ.E} :
    Γ.toGeomEdge e = Γ.toGeomEdge f ↔ f = e ∨ f = Γ.rev e := by
  refine ⟨fun h => ?_, ?_⟩
  · have hequiv : Equivalence fun e f : Γ.E => f = e ∨ f = Γ.rev e :=
      { refl := fun _ => Or.inl rfl
        symm := by
          rintro e f (rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr (Γ.rev_rev e).symm
        trans := by
          rintro e f g (rfl | rfl) (rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inr rfl
          · exact Or.inl (Γ.rev_rev e) }
    exact hequiv.eqvGen_iff.mp ((Quot.eqvGen_exact h).mono fun _ _ => Or.inr)
  · rintro (rfl | rfl)
    · rfl
    · exact (Γ.toGeomEdge_rev e).symm

/-- A function on darts taking the same value on mutually reverse darts descends to geometric
edges. -/
def GeomEdge.lift {β : Sort*} (f : Γ.E → β) (hf : ∀ e, f (Γ.rev e) = f e) :
    Γ.GeomEdge → β :=
  Quot.lift f fun e _ h => h ▸ (hf e).symm

@[simp] theorem GeomEdge.lift_toGeomEdge {β : Sort*} (f : Γ.E → β)
    (hf : ∀ e, f (Γ.rev e) = f e) (e : Γ.E) : GeomEdge.lift Γ f hf (Γ.toGeomEdge e) = f e :=
  (rfl)

/-- A chosen dart representing a geometric edge. -/
noncomputable def GeomEdge.out (y : Γ.GeomEdge) : Γ.E :=
  Quot.out y

/-- The chosen dart of a geometric edge lies on it. -/
@[simp] theorem toGeomEdge_out (y : Γ.GeomEdge) : Γ.toGeomEdge (GeomEdge.out Γ y) = y :=
  Quot.out_eq y

/-- Distinct geometric edges have distinct chosen darts. -/
theorem GeomEdge.out_injective : Function.Injective (GeomEdge.out Γ) :=
  Function.LeftInverse.injective Γ.toGeomEdge_out

@[simp] theorem GeomEdge.out_inj {x y : Γ.GeomEdge} :
    GeomEdge.out Γ x = GeomEdge.out Γ y ↔ x = y :=
  (GeomEdge.out_injective Γ).eq_iff

/-- The dart representing the geometric edge of a dart `e` is `e` or its reverse. -/
theorem GeomEdge.out_toGeomEdge_eq_or_eq_rev (e : Γ.E) :
    GeomEdge.out Γ (Γ.toGeomEdge e) = e ∨ GeomEdge.out Γ (Γ.toGeomEdge e) = Γ.rev e :=
  Γ.toGeomEdge_eq_toGeomEdge_iff.mp (Γ.toGeomEdge_out _).symm

/-- A bijection of darts commuting with reversal induces a bijection of geometric edges. -/
def GeomEdge.congr {Δ : SerreGraph.{w, x}} (f : Γ.E ≃ Δ.E)
    (hf : ∀ e, f (Γ.rev e) = Δ.rev (f e)) : Γ.GeomEdge ≃ Δ.GeomEdge :=
  Quot.congr f fun e e' => by rw [← hf, f.apply_eq_iff_eq]

@[simp] theorem GeomEdge.congr_toGeomEdge {Δ : SerreGraph.{w, x}} (f : Γ.E ≃ Δ.E)
    (hf : ∀ e, f (Γ.rev e) = Δ.rev (f e)) (e : Γ.E) :
    GeomEdge.congr Γ f hf (Γ.toGeomEdge e) = Δ.toGeomEdge (f e) :=
  Quot.congr_mk ..

@[simp] theorem GeomEdge.congr_symm_toGeomEdge {Δ : SerreGraph.{w, x}} (f : Γ.E ≃ Δ.E)
    (hf : ∀ e, f (Γ.rev e) = Δ.rev (f e)) (e : Δ.E) :
    (GeomEdge.congr Γ f hf).symm (Δ.toGeomEdge e) = Γ.toGeomEdge (f.symm e) := by
  rw [Equiv.symm_apply_eq, GeomEdge.congr_toGeomEdge, Equiv.apply_symm_apply]

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

variable {Γ} in
/-- An orientation contains a dart or its reverse. -/
theorem IsOrientation.mem_or_rev_mem {O : Set Γ.E} (hO : Γ.IsOrientation O) (e : Γ.E) :
    e ∈ O ∨ Γ.rev e ∈ O :=
  or_iff_not_imp_left.mpr (IsOrientation.mem_rev_iff Γ hO e).mpr

/-- An orientation contains exactly one dart above each geometric edge. -/
theorem IsOrientation.bijective_toGeomEdge {O : Set Γ.E} (hO : Γ.IsOrientation O) :
    Function.Bijective fun e : O => Γ.toGeomEdge e := by
  refine ⟨fun e f h => Subtype.ext ?_, fun g => ?_⟩
  · rcases Γ.toGeomEdge_eq_toGeomEdge_iff.mp h with hf | hf
    · exact hf.symm
    · exact absurd (hf ▸ f.2) (hO.rev_notMem_of_mem Γ e e.2)
  · obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective g
    by_cases he : e ∈ O
    · exact ⟨⟨e, he⟩, rfl⟩
    · exact ⟨⟨Γ.rev e, (hO.mem_rev_iff Γ e).mpr he⟩, Γ.toGeomEdge_rev e⟩

/-- Every Serre graph has an orientation: choose one dart above each geometric edge. -/
theorem exists_isOrientation : ∃ O : Set Γ.E, Γ.IsOrientation O := by
  choose out hout using Γ.toGeomEdge_surjective
  have hmem (e : Γ.E) : e ∈ Set.range out ↔ out (Γ.toGeomEdge e) = e :=
    ⟨by rintro ⟨g, rfl⟩; rw [hout], fun h => ⟨_, h⟩⟩
  refine ⟨Set.range out, fun e => ?_⟩
  rw [hmem, hmem, toGeomEdge_rev]
  rcases Γ.toGeomEdge_eq_toGeomEdge_iff.mp (hout (Γ.toGeomEdge e)).symm with h | h
  · simpa [h] using (Γ.rev_ne e).symm
  · simpa [h] using Γ.rev_ne e

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

theorem dart_def (e : Γ.E) : Γ.dart e = ⟨e, rfl, rfl⟩ :=
  (rfl)

/-- If the dart of `e : a ⟶ b` is the reverse of the dart of `f : c ⟶ d`, then `e` starts where
`f` ends. -/
theorem src_eq_tgt_of_val_eq_rev {a b c d : Γ.V} {e : Quiver.Hom a b} {f : Quiver.Hom c d}
    (h : e.1 = Γ.rev f.1) : a = d := by
  rw [← e.2.1, h, src_rev, f.2.2]

/-- If the dart of `e : a ⟶ b` is the reverse of the dart of `f : c ⟶ d`, then `e` ends where
`f` starts. -/
theorem tgt_eq_src_of_val_eq_rev {a b c d : Γ.V} {e : Quiver.Hom a b} {f : Quiver.Hom c d}
    (h : e.1 = Γ.rev f.1) : b = c := by
  rw [← e.2.2, h, tgt_rev, f.2.1]

/-- An arrow `e : b ⟶ a` whose dart is the reverse of the dart of `f : a ⟶ b` is the reverse
of `f`. -/
theorem eq_reverse_of_val_eq_rev {a b : Γ.V} {e : Quiver.Hom b a} {f : Quiver.Hom a b}
    (h : e.1 = Γ.rev f.1) : e = Quiver.reverse f :=
  Subtype.ext (h.trans (Γ.reverse_val f).symm)

/-- An indexed path in a Serre graph is a path of its associated quiver. -/
abbrev Path (a b : Γ.V) : Type (max u v) := Quiver.Path a b

/-- A Serre graph is preconnected when any two vertices are joined by a path. -/
def Preconnected : Prop := Quiver.IsStronglyConnected Γ.V

/-- Preconnectivity is pairwise Serre path reachability. -/
theorem preconnected_iff : Γ.Preconnected ↔ ∀ a b, Nonempty (Γ.Path a b) :=
  Quiver.isStronglyConnected_iff Γ.V

/-- A Serre graph is preconnected as soon as one vertex is joined by a path to every vertex:
paths can be reversed. -/
theorem preconnected_of_forall_nonempty_path (a : Γ.V) (h : ∀ b, Nonempty (Γ.Path a b)) :
    Γ.Preconnected :=
  (preconnected_iff Γ).2 fun b c => ⟨(h b).some.reverse.comp (h c).some⟩

/-- In a Serre graph all of whose darts are loops, a path never leaves its starting vertex. -/
theorem eq_of_path_of_forall_src_eq_tgt (h : ∀ e, Γ.src e = Γ.tgt e) {a b : Γ.V}
    (p : Γ.Path a b) : a = b := by
  induction p with
  | nil => rfl
  | cons _ e ih => exact ih.trans (e.2.1.symm.trans ((h e.1).trans e.2.2))

/-- A Serre graph is connected when it is nonempty and path-connected. -/
def Connected : Prop := Nonempty Γ.V ∧ Γ.Preconnected

/-- Connectedness requires a vertex as well as preconnectivity. -/
theorem connected_iff : Γ.Connected ↔ Nonempty Γ.V ∧ Γ.Preconnected := Iff.rfl

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

/-- A morphism of Serre graphs sends darts with the same geometric edge to darts with the same
geometric edge. -/
theorem Hom.toGeomEdge_mapE_congr {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}} (f : Γ.Hom Δ)
    {e e' : Γ.E} (h : Γ.toGeomEdge e = Γ.toGeomEdge e') :
    Δ.toGeomEdge (f.mapE e) = Δ.toGeomEdge (f.mapE e') := by
  obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 h
  · rfl
  · rw [f.map_rev, Δ.toGeomEdge_rev]

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

/-- A vertex-surjective graph morphism carries preconnectedness to its target. -/
theorem Hom.preconnected_of_surjective {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) (hf : Function.Surjective f.mapV)
    (hΓ : Γ.Preconnected) : Δ.Preconnected := by
  apply (preconnected_iff Δ).2
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  obtain ⟨p⟩ := (preconnected_iff Γ).1 hΓ x y
  exact ⟨f.toPrefunctor.mapPath p⟩

/-- A vertex-surjective graph morphism carries connectedness to its target. -/
theorem Hom.connected_of_surjective {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) (hf : Function.Surjective f.mapV)
    (hΓ : Γ.Connected) : Δ.Connected := by
  obtain ⟨⟨x⟩, hpre⟩ := (connected_iff Γ).1 hΓ
  exact (connected_iff Δ).2 ⟨⟨f.mapV x⟩, f.preconnected_of_surjective hf hpre⟩

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

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The subgraph of `Γ` with all vertices of `Γ` and the darts of a reversal-closed set `S`. The
vertex type reduces to that of `Γ`, so vertices of `Γ` are vertices of the subgraph. -/
abbrev restrict : SerreGraph.{u, v} where
  V := Γ.V
  E := S
  src e := Γ.src e.1
  rev e := ⟨Γ.rev e.1, hS e.1 e.2⟩
  rev_rev e := Subtype.ext (Γ.rev_rev e.1)
  rev_ne e he := Γ.rev_ne e.1 (congrArg Subtype.val he)

@[simp] theorem restrict_src (e : (Γ.restrict S hS).E) :
    (Γ.restrict S hS).src e = Γ.src e.1 := (rfl)

@[simp] theorem restrict_rev_val (e : (Γ.restrict S hS).E) :
    ((Γ.restrict S hS).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem restrict_tgt (e : (Γ.restrict S hS).E) :
    (Γ.restrict S hS).tgt e = Γ.tgt e.1 := (rfl)

/-- The inclusion of a restriction into the ambient graph. -/
@[expose] def restrictInclusion : (Γ.restrict S hS).Hom Γ where
  mapV := id
  mapE := Subtype.val
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem restrictInclusion_mapV (a : (Γ.restrict S hS).V) :
    (Γ.restrictInclusion S hS).mapV a = a := (rfl)

@[simp] theorem restrictInclusion_mapE (e : (Γ.restrict S hS).E) :
    (Γ.restrictInclusion S hS).mapE e = e.1 := (rfl)

end Restrict

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

/-- The Serre graph with one vertex and no edges. -/
abbrev point : SerreGraph.{u, v} where
  V := PUnit
  E := PEmpty
  src := PEmpty.elim
  rev := PEmpty.elim
  rev_rev := by intro e; exact e.elim
  rev_ne := by intro e; exact e.elim

/-- A rose has a single vertex. -/
instance (α : Type w) : Unique (rose α).V := inferInstanceAs (Unique PUnit)

/-- The darts of a rose, being pairs of a petal and a direction, have decidable equality when
the petals do. -/
instance (α : Type w) [DecidableEq α] : DecidableEq (rose α).E :=
  inferInstanceAs (DecidableEq (α × Bool))

/-- The geometric edges of a rose are its petals. -/
def roseGeomEdgeEquiv (α : Type w) : (rose α).GeomEdge ≃ α where
  toFun := GeomEdge.lift (rose α) Prod.fst fun _ => rfl
  invFun a := (rose α).toGeomEdge (a, true)
  left_inv x := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (rose α).toGeomEdge_surjective x
    refine ((rose α).toGeomEdge_eq_toGeomEdge_iff).2 ?_
    cases b
    · exact .inr rfl
    · exact .inl rfl
  right_inv _ := rfl

@[simp] theorem roseGeomEdgeEquiv_toGeomEdge (α : Type w) (e : α × Bool) :
    roseGeomEdgeEquiv α ((rose α).toGeomEdge e) = e.1 := (rfl)

/-- Every rose is connected, including the rose without petals. -/
theorem rose_connected (α : Type*) : (rose α).Connected := by
  rw [(rose α).connected_iff]
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  rw [(rose α).preconnected_iff]
  intro u v
  cases u
  cases v
  exact ⟨Quiver.Path.nil⟩

/-- Positive darts form an orientation of a rose. -/
theorem rose_isOrientation (α : Type w) :
    (rose α).IsOrientation {e | e.2 = true} := by
  intro ⟨a, b⟩
  -- The carrier `(rose α).E` reduces definitionally to `α × Bool` here.
  change (b = true) ↔ ¬(!b = true)
  cases b <;> decide

/-- The segment: two vertices joined by a single pair of darts. The dart `b` runs from the
vertex `b` to the vertex `!b`. -/
@[expose] def segment : SerreGraph.{0, 0} where
  V := Bool
  E := Bool
  src := id
  rev := not
  rev_rev := Bool.not_not
  rev_ne := Bool.not_ne_self

@[simp] theorem segment_src (b : Bool) : segment.src b = b := rfl

/-- Every vertex of the segment is the source of a dart: the dart with the same Boolean label. -/
theorem segment_src_surjective : Function.Surjective segment.src := fun b => ⟨b, segment_src b⟩

@[simp] theorem segment_rev (b : Bool) : segment.rev b = !b := rfl

@[simp] theorem segment_tgt (b : Bool) : segment.tgt b = !b := rfl

/-- The vertices of the segment are the Booleans. -/
def segmentVEquiv : segment.V ≃ Bool := Equiv.refl Bool

/-- The darts of the segment, being Booleans, have decidable equality. -/
instance : DecidableEq segment.E := inferInstanceAs (DecidableEq Bool)

/-- The segment has a single geometric edge. -/
instance : Unique segment.GeomEdge where
  default := segment.toGeomEdge true
  uniq x := by
    obtain ⟨b, rfl⟩ := segment.toGeomEdge_surjective x
    refine (segment.toGeomEdge_eq_toGeomEdge_iff).2 ?_
    cases b
    · exact .inr rfl
    · exact .inl rfl

end SerreGraph

end TauCeti

namespace SimpleGraph

/-- The Serre graph of a simple graph has its darts as directed edges. The definition unfolds at
instance transparency, so that a vertex or a dart of the simple graph is accepted as a vertex or a
dart of its Serre graph by rewriting and simplification. -/
@[expose, instance_reducible] def toSerreGraph {V : Type u} (G : SimpleGraph V) :
    TauCeti.SerreGraph.{u, u} where
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
