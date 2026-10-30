/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path

/-!
# Based cores of Serre graphs

The core at a vertex consists of the darts occurring in reduced loops at that vertex,
together with their endpoints and the base vertex itself. It retains the stem from a base
vertex to a circuit. Every reduced based loop lifts to the core, and every core vertex is
reachable from the base within the core. Finite graphs have finite cores.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Definition 3.5 and Lemma 3.7.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (v : Γ.V)

/-- The darts occurring in reduced loops at the specified base vertex. -/
def coreDarts : Set Γ.E :=
  {e | ∃ p : Γ.Path v v, Path.IsReduced Γ p ∧ e ∈ Path.darts Γ p}

/-- Membership in the core is witnessed by a reduced based loop. -/
theorem mem_coreDarts_iff (e : Γ.E) :
    e ∈ Γ.coreDarts v ↔ ∃ p : Γ.Path v v, Path.IsReduced Γ p ∧ e ∈ Path.darts Γ p :=
  Iff.rfl

/-- The dart set of a based core is closed under reversal. -/
@[simp] theorem rev_mem_coreDarts_iff (e : Γ.E) :
    Γ.rev e ∈ Γ.coreDarts v ↔ e ∈ Γ.coreDarts v := by
  suffices h : ∀ e ∈ Γ.coreDarts v, Γ.rev e ∈ Γ.coreDarts v from
    ⟨fun he => by simpa using h (Γ.rev e) he, h e⟩
  rintro e ⟨p, hp, he⟩
  exact ⟨p.reverse, (Path.isReduced_reverse Γ p).mpr hp,
    by simpa using List.mem_map_of_mem (f := Γ.rev) (List.mem_reverse.mpr he)⟩

/-- The vertices of the based core, including an isolated base vertex. -/
def coreVertices : Set Γ.V :=
  {a | a = v ∨ ∃ e ∈ Γ.coreDarts v, Γ.src e = a}

@[simp] theorem mem_coreVertices_iff (a : Γ.V) :
    a ∈ Γ.coreVertices v ↔ a = v ∨ ∃ e ∈ Γ.coreDarts v, Γ.src e = a := Iff.rfl

/-- Both endpoints of a retained dart are retained vertices. -/
theorem src_mem_coreVertices {e : Γ.E} (he : e ∈ Γ.coreDarts v) :
    Γ.src e ∈ Γ.coreVertices v := Or.inr ⟨e, he, rfl⟩

theorem tgt_mem_coreVertices {e : Γ.E} (he : e ∈ Γ.coreDarts v) :
    Γ.tgt e ∈ Γ.coreVertices v := by
  simpa only [Γ.src_rev] using
    Γ.src_mem_coreVertices v ((Γ.rev_mem_coreDarts_iff v e).mpr he)

/-- The union of reduced loops at a base vertex, retaining the base even when there are no
nonempty reduced loops. The carrier subtypes compute so paths can be lifted through them. -/
@[expose] def core : SerreGraph where
  V := Γ.coreVertices v
  E := Γ.coreDarts v
  src := fun e => ⟨Γ.src e.1, Γ.src_mem_coreVertices v e.2⟩
  rev := fun e => ⟨Γ.rev e.1, (Γ.rev_mem_coreDarts_iff v e.1).mpr e.2⟩
  rev_rev := by intro e; exact Subtype.ext (Γ.rev_rev e.1)
  rev_ne := by intro e he; exact Γ.rev_ne e.1 (congrArg Subtype.val he)

/-- The distinguished vertex in a based core. It computes to the ambient base, so paths
mapped by the inclusion have the corresponding ambient endpoints. -/
@[expose] def coreBase : (Γ.core v).V := ⟨v, by simp⟩

/-- Inclusion of the based core into the ambient graph. -/
@[expose] def coreInclusion : (Γ.core v).Hom Γ where
  mapV := Subtype.val
  mapE := Subtype.val
  map_src := by intro e; rfl
  map_rev := by intro e; rfl

@[simp] theorem coreInclusion_mapV (a : (Γ.core v).V) :
    (Γ.coreInclusion v).mapV a = a.1 := (rfl)

@[simp] theorem coreInclusion_mapE (e : (Γ.core v).E) :
    (Γ.coreInclusion v).mapE e = e.1 := (rfl)

@[simp] theorem coreBase_val : (Γ.coreBase v).1 = v := (rfl)

@[simp] theorem core_src_val (e : (Γ.core v).E) :
    ((Γ.core v).src e).1 = Γ.src e.1 := (rfl)

@[simp] theorem core_rev_val (e : (Γ.core v).E) :
    ((Γ.core v).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem core_tgt_val (e : (Γ.core v).E) :
    ((Γ.core v).tgt e).1 = Γ.tgt e.1 := by
  rw [(Γ.core v).tgt_def, Γ.tgt_def]
  rfl

instance [Finite Γ.V] : Finite (Γ.core v).V := inferInstanceAs (Finite (Γ.coreVertices v))
instance [Finite Γ.E] : Finite (Γ.core v).E := inferInstanceAs (Finite (Γ.coreDarts v))

/-- A path all of whose darts belong to the core lifts through its inclusion. -/
theorem exists_core_path {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ Γ.coreDarts v)
    (ha : a ∈ Γ.coreVertices v) (hb : b ∈ Γ.coreVertices v) :
    ∃ q : (Γ.core v).Path ⟨a, ha⟩ ⟨b, hb⟩,
      (Γ.coreInclusion v).toPrefunctor.mapPath q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons b c p e ih =>
    have he : e.1 ∈ Γ.coreDarts v := hp e.1 (by simp)
    have hprev : b ∈ Γ.coreVertices v := by
      simpa only [e.2.1] using Γ.src_mem_coreVertices v he
    obtain ⟨q, hq⟩ := ih (fun f hf => hp f (by simp [hf])) hprev
    let f : @Quiver.Hom (Γ.core v).V (Γ.core v).toQuiver ⟨b, hprev⟩ ⟨c, hb⟩ :=
      ⟨⟨e.1, he⟩, Subtype.ext e.2.1,
        Subtype.ext ((Γ.core_tgt_val v ⟨e.1, he⟩).trans e.2.2)⟩
    refine ⟨q.cons f, ?_⟩
    exact congrArg (fun t => t.cons e) hq

/-- Every reduced loop based at the chosen vertex is a loop in its core. -/
theorem exists_core_loop (p : Γ.Path v v) (hp : Path.IsReduced Γ p) :
    ∃ q : (Γ.core v).Path (Γ.coreBase v) (Γ.coreBase v),
      (Γ.coreInclusion v).toPrefunctor.mapPath q = p :=
  Γ.exists_core_path v p (fun _ he => ⟨p, hp, he⟩) _ _

/-- Every core vertex is reached from its base by a path entirely inside the core. -/
theorem core_reachable (a : (Γ.core v).V) :
    Nonempty ((Γ.core v).Path (Γ.coreBase v) a) := by
  rcases a with ⟨a, ha⟩
  rcases (Γ.mem_coreVertices_iff v a).mp ha with rfl | ⟨e, he, rfl⟩
  · exact ⟨.nil⟩
  · obtain ⟨p, hp, he⟩ := he
    obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
    obtain ⟨q', _⟩ := Γ.exists_core_path v q
      (fun f hf => ⟨_, hp, by simp [hf]⟩) (by simp) ha
    exact ⟨q'⟩

/-- A graph is a core at `v` if every vertex is reachable from `v` and every dart lies on a
reduced loop based at `v`. The base vertex may be isolated or have degree one. -/
def IsCore : Prop :=
  (∀ a : Γ.V, Nonempty (Γ.Path v a)) ∧
    ∀ e : Γ.E, ∃ p : Γ.Path v v, Path.IsReduced Γ p ∧ e ∈ Path.darts Γ p

/-- Characterization of a based core by reachability and reduced-loop coverage. -/
theorem isCore_iff : Γ.IsCore v ↔
    (∀ a : Γ.V, Nonempty (Γ.Path v a)) ∧
      ∀ e : Γ.E, ∃ p : Γ.Path v v, Path.IsReduced Γ p ∧ e ∈ Path.darts Γ p := Iff.rfl

/-- A based core is connected, including when its base is an isolated vertex. -/
theorem IsCore.connected (hΓ : Γ.IsCore v) : Γ.Connected := by
  apply Γ.connected_iff.mpr
  refine ⟨⟨v⟩, ?_⟩
  rw [Γ.preconnected_iff]
  intro a b
  obtain ⟨p⟩ := hΓ.1 a
  obtain ⟨q⟩ := hΓ.1 b
  exact ⟨p.reverse.comp q⟩

/-- The union of reduced based loops is itself a based core. -/
theorem core_isCore : (Γ.core v).IsCore (Γ.coreBase v) := by
  refine ⟨Γ.core_reachable v, ?_⟩
  intro e
  obtain ⟨p, hp, he⟩ := e.2
  obtain ⟨q, hq⟩ := Γ.exists_core_loop v p hp
  subst p
  refine ⟨q, ?_, ?_⟩
  · exact ((Γ.coreInclusion v).isReduced_mapPath_iff _ Subtype.val_injective q).mp hp
  · have hd := Hom.darts_mapPath (Γ.core v) (Γ.coreInclusion v) q
    have hm := Eq.mp (congrArg (fun l => e.1 ∈ l) hd) he
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
    have : f = e := Subtype.ext hfe
    exact this ▸ hf

/-- At any vertex other than the base, an outgoing dart of a core has a different outgoing
dart. Thus the base is the only possible degree-one vertex, even for an infinite core. -/
theorem IsCore.exists_outgoing_ne (hΓ : Γ.IsCore v) (e : Γ.E) (he : Γ.src e ≠ v) :
    ∃ f : Γ.E, Γ.src f = Γ.src e ∧ f ≠ e := by
  obtain ⟨p, hp, he'⟩ := hΓ.2 e
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he'
  have hq := hp.of_comp_left Γ
  cases q with
  | nil => exact False.elim (he rfl)
  | cons q f =>
    refine ⟨Γ.rev f.1, ?_, ?_⟩
    · simpa only [Γ.src_rev] using f.2.2
    · have hn := ((Path.isReduced_cons_cons Γ q f (Γ.dart e)).mp hq).2
      simpa only [Γ.dart_val, ne_eq, eq_comm] using hn

end TauCeti.SerreGraph
