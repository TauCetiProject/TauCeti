/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Basic

import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# Based cores of Serre graphs

A set of vertices together with a reversal-closed set of darts starting at those vertices forms
a subgraph (`SerreGraph.subgraph`), through whose inclusion every path with darts in the subgraph
lifts. The core at a vertex is the subgraph consisting of the darts occurring in reduced loops at
that vertex, together with their endpoints and the base vertex itself. It retains the stem from a
base vertex to a circuit. Every reduced based loop lifts to the core, and every core vertex is
reachable from the base within the core. Finite graphs have finite cores. Moving the base vertex
back along a path keeps every dart of the core that the path does not traverse
(`SerreGraph.mem_coreDarts_or_mem_darts`).

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 3, Definition 3.5 and Lemma 3.7, and the proof of Lemma 7.5.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (v : Γ.V)

section Subgraph

variable (A : Set Γ.V) (D : Set Γ.E) (hsrc : ∀ e ∈ D, Γ.src e ∈ A)
  (hrev : ∀ e ∈ D, Γ.rev e ∈ D)

/-- The subgraph of `Γ` on a set `A` of vertices and a reversal-closed set `D` of darts starting
in `A`. Its carriers compute to these subtypes so that paths can be lifted through them. -/
@[expose] def subgraph : SerreGraph where
  V := A
  E := D
  src e := ⟨Γ.src e.1, hsrc e.1 e.2⟩
  rev e := ⟨Γ.rev e.1, hrev e.1 e.2⟩
  rev_rev e := Subtype.ext (Γ.rev_rev e.1)
  rev_ne e he := Γ.rev_ne e.1 (congrArg Subtype.val he)

@[simp] theorem subgraph_src_val (e : (Γ.subgraph A D hsrc hrev).E) :
    ((Γ.subgraph A D hsrc hrev).src e).1 = Γ.src e.1 := (rfl)

@[simp] theorem subgraph_rev_val (e : (Γ.subgraph A D hsrc hrev).E) :
    ((Γ.subgraph A D hsrc hrev).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem subgraph_tgt_val (e : (Γ.subgraph A D hsrc hrev).E) :
    ((Γ.subgraph A D hsrc hrev).tgt e).1 = Γ.tgt e.1 := by
  rw [(Γ.subgraph A D hsrc hrev).tgt_def, Γ.tgt_def]
  rfl

instance [Finite Γ.V] : Finite (Γ.subgraph A D hsrc hrev).V := inferInstanceAs (Finite A)
instance [Finite Γ.E] : Finite (Γ.subgraph A D hsrc hrev).E := inferInstanceAs (Finite D)

/-- Inclusion of a subgraph into the ambient graph. -/
@[expose] def subgraphInclusion : (Γ.subgraph A D hsrc hrev).Hom Γ where
  mapV := Subtype.val
  mapE := Subtype.val
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem subgraphInclusion_mapV (a : (Γ.subgraph A D hsrc hrev).V) :
    (Γ.subgraphInclusion A D hsrc hrev).mapV a = a.1 := (rfl)

@[simp] theorem subgraphInclusion_mapE (e : (Γ.subgraph A D hsrc hrev).E) :
    (Γ.subgraphInclusion A D hsrc hrev).mapE e = e.1 := (rfl)

/-- A path between vertices of `A` all of whose darts lie in `D` lifts through the inclusion of
the subgraph. -/
theorem exists_subgraph_path {a b : Γ.V} (p : Γ.Path a b) (hp : ∀ e ∈ Path.darts Γ p, e ∈ D)
    (ha : a ∈ A) (hb : b ∈ A) :
    ∃ q : (Γ.subgraph A D hsrc hrev).Path ⟨a, ha⟩ ⟨b, hb⟩,
      (Γ.subgraphInclusion A D hsrc hrev).toPrefunctor.mapPath q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons b c p e ih =>
    have he : e.1 ∈ D := hp e.1 (by simp)
    have hprev : b ∈ A := e.2.1 ▸ hsrc e.1 he
    obtain ⟨q, hq⟩ := ih (fun f hf => hp f (by simp [hf])) hprev
    let f : @Quiver.Hom (Γ.subgraph A D hsrc hrev).V (Γ.subgraph A D hsrc hrev).toQuiver
        ⟨b, hprev⟩ ⟨c, hb⟩ :=
      ⟨⟨e.1, he⟩, Subtype.ext e.2.1, Subtype.ext ((Γ.subgraph_tgt_val A D hsrc hrev _).trans e.2.2)⟩
    exact ⟨q.cons f, congrArg (fun t => t.cons e) hq⟩

end Subgraph

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
nonempty reduced loops. -/
abbrev core : SerreGraph :=
  Γ.subgraph (Γ.coreVertices v) (Γ.coreDarts v) (fun _ => Γ.src_mem_coreVertices v)
    fun e => (Γ.rev_mem_coreDarts_iff v e).mpr

/-- The distinguished vertex in a based core. It computes to the ambient base, so paths
mapped by the inclusion have the corresponding ambient endpoints. -/
@[expose] def coreBase : (Γ.core v).V := ⟨v, by simp⟩

/-- Inclusion of the based core into the ambient graph. -/
abbrev coreInclusion : (Γ.core v).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

@[simp] theorem coreBase_val : (Γ.coreBase v).1 = v := (rfl)

/-- Every reduced loop based at the chosen vertex is a loop in its core. -/
theorem exists_core_loop (p : Γ.Path v v) (hp : Path.IsReduced Γ p) :
    ∃ q : (Γ.core v).Path (Γ.coreBase v) (Γ.coreBase v),
      (Γ.coreInclusion v).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path (Γ.coreVertices v) (Γ.coreDarts v) _ _ p (fun _ he => ⟨p, hp, he⟩) _ _

/-- Every core vertex is reached from its base by a path entirely inside the core. -/
theorem core_reachable (a : (Γ.core v).V) :
    Nonempty ((Γ.core v).Path (Γ.coreBase v) a) := by
  rcases a with ⟨a, ha⟩
  rcases (Γ.mem_coreVertices_iff v a).mp ha with rfl | ⟨e, he, rfl⟩
  · exact ⟨.nil⟩
  · obtain ⟨p, hp, he⟩ := he
    obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
    obtain ⟨q', -⟩ : ∃ q' : (Γ.core v).Path (Γ.coreBase v) ⟨_, ha⟩, _ :=
      Γ.exists_subgraph_path (Γ.coreVertices v) (Γ.coreDarts v) _ _ q
        (fun f hf => ⟨_, hp, by simp [hf]⟩) _ ha
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

/-! ### Moving the base vertex -/

/-- A dart in the based core at the terminus of a dart `d`, other than `d` and its reverse, is
in the based core at the origin of `d`. -/
theorem mem_coreDarts_src {d e : Γ.E} (he : e ∈ Γ.coreDarts (Γ.tgt d)) (hd : e ≠ d)
    (hd' : e ≠ Γ.rev d) : e ∈ Γ.coreDarts (Γ.src d) := by
  obtain ⟨c, hc, he⟩ := (Γ.mem_coreDarts_iff _ e).mp he
  -- Go back along `d`, around `c` and forward along `d`, cancelling backtracks.
  let r : Quiver.Hom (Γ.tgt d) (Γ.src d) := ⟨Γ.rev d, Γ.src_rev d, Γ.tgt_rev d⟩
  have h₁ : e ∈ Path.darts Γ (Path.reduce Γ (c.cons r)) := Path.mem_darts_reduce_cons Γ c r
    (by rwa [Path.reduce_eq_self_of_isReduced Γ c hc]) (by simpa [r] using hd)
  have h₂ := Path.mem_darts_reduce_cons Γ (Path.reduce Γ (c.cons r)).reverse r
    (e := Γ.rev e) (by simpa using ⟨e, h₁, rfl⟩) fun h => hd' (Γ.rev_injective h)
  rw [← Γ.rev_mem_coreDarts_iff, Γ.mem_coreDarts_iff]
  exact ⟨_, Path.isReduced_reduce Γ _, h₂⟩

/-- Moving the base vertex of a based core back along a path keeps every dart of the core other
than the darts of the path and their reverses. -/
theorem mem_coreDarts_or_mem_darts {v w : Γ.V} (p : Γ.Path v w) {e : Γ.E} (he : e ∈ Γ.coreDarts w) :
    e ∈ Γ.coreDarts v ∨ e ∈ Path.darts Γ p ∨ Γ.rev e ∈ Path.darts Γ p := by
  induction p with
  | nil => exact Or.inl he
  | cons p d ih =>
    obtain ⟨d, rfl, rfl⟩ := d
    by_cases h₁ : e = d
    · simp [h₁]
    by_cases h₂ : e = Γ.rev d
    · simp [h₂]
    rcases ih (Γ.mem_coreDarts_src he h₁ h₂) with h | h | h <;> simp [h]

end TauCeti.SerreGraph
