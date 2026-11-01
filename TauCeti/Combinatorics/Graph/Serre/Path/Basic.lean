/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Combinatorics.Quiver.Path.Decomposition
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Paths without immediate reversal in a Serre graph

A path in the quiver of a Serre graph is reduced when no consecutive darts cancel. This
condition retains the distinction between a loop and its reversed dart, and between parallel
edges. It is the local normal-form condition used for graph path groups and Stallings graphs.
The ordered dart list is obtained from Mathlib's `Quiver.Path.weight` in the free monoid;
its decomposition and mapping lemmas support subgraph and based-core constructions. The paths of
a restriction `Γ.restrict S hS` are the paths of `Γ` whose darts lie in `S`, and a path leaving a
vertex set crosses its boundary along one of its darts.
-/

public section

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph)

/-- The ordered list of darts traversed by a path. -/
def Path.darts {a b : Γ.V} (p : Γ.Path a b) : List Γ.E :=
  (p.weight fun {i j} (e : @Quiver.Hom Γ.V Γ.toQuiver i j) =>
    FreeMonoid.of e.1).toList

@[simp] theorem Path.darts_nil (a : Γ.V) :
    Path.darts Γ (Quiver.Path.nil : Γ.Path a a) = [] := by simp [Path.darts]

@[simp] theorem Path.darts_cons {a b c : Γ.V} (p : Γ.Path a b)
    (e : Quiver.Hom b c) : Path.darts Γ (p.cons e) = Path.darts Γ p ++ [e.1] := by
  simp [Path.darts]

@[simp] theorem Path.darts_toPath {a b : Γ.V} (e : Quiver.Hom a b) :
    Path.darts Γ e.toPath = [e.1] := by simp [Quiver.Hom.toPath]

@[simp] theorem Path.darts_comp {a b c : Γ.V} (p : Γ.Path a b) (q : Γ.Path b c) :
    Path.darts Γ (p.comp q) = Path.darts Γ p ++ Path.darts Γ q := by
  simp [Path.darts]

@[simp] theorem Path.darts_reverse {a b : Γ.V} (p : Γ.Path a b) :
    Path.darts Γ p.reverse = ((Path.darts Γ p).reverse.map Γ.rev) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [Quiver.Path.reverse, Quiver.Hom.toPath, ih]

/-- A path traverses as many darts as its length. -/
@[simp] theorem Path.length_darts {a b : Γ.V} (p : Γ.Path a b) :
    (Path.darts Γ p).length = p.length := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

/-- A traversed dart separates a path into a prefix, that dart, and a suffix. -/
theorem Path.exists_eq_cons_comp_of_mem_darts {a b : Γ.V} (p : Γ.Path a b)
    {e : Γ.E} (he : e ∈ Path.darts Γ p) :
    ∃ (q : Γ.Path a (Γ.src e)) (r : Γ.Path (Γ.tgt e) b),
      p = (q.cons (Γ.dart e)).comp r := by
  induction p with
  | nil => simp at he
  | @cons c b p f ih =>
    simp only [Path.darts_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨q, r, rfl⟩ := ih he
      exact ⟨q, r.cons f, rfl⟩
    · rcases f with ⟨f, hs, ht⟩
      subst c
      subst b
      refine ⟨p, .nil, ?_⟩
      simp only [Quiver.Path.comp_nil]
      congr 1
      apply Subtype.ext
      simp

/-- A Serre path has no consecutive pair of mutually reversed darts. -/
def Path.IsReduced {a : Γ.V} : ∀ {b : Γ.V}, Γ.Path a b → Prop
  | _, .nil => True
  | _, .cons .nil _ => True
  | _, .cons (.cons p e) f =>
      Path.IsReduced (.cons p e) ∧ f.1 ≠ Γ.rev e.1

@[simp] theorem Path.isReduced_nil (a : Γ.V) :
    Path.IsReduced Γ (Quiver.Path.nil : Γ.Path a a) := trivial

@[simp] theorem Path.isReduced_toPath {a b : Γ.V} (e : Quiver.Hom a b) :
    Path.IsReduced Γ e.toPath := trivial

/-- The reducedness test for a newly appended dart only examines the preceding dart. -/
@[simp] theorem Path.isReduced_cons_cons {a b c d : Γ.V}
    (p : Γ.Path a b) (e : Quiver.Hom b c)
    (f : Quiver.Hom c d) :
    Path.IsReduced Γ ((p.cons e).cons f) ↔
      Path.IsReduced Γ (p.cons e) ∧ f.1 ≠ Γ.rev e.1 := Iff.rfl

/-- Every prefix obtained by removing the final dart of a reduced path is reduced. -/
theorem Path.IsReduced.of_cons {a b c : Γ.V} {p : Γ.Path a b} {e : Quiver.Hom b c}
    (hp : Path.IsReduced Γ (p.cons e)) : Path.IsReduced Γ p := by
  cases p with
  | nil => simp
  | cons p f => exact hp.1

/-- A prefix of a reduced concatenation is reduced. -/
theorem Path.IsReduced.of_comp_left {a b c : Γ.V} {p : Γ.Path a b} {q : Γ.Path b c}
    (hp : Path.IsReduced Γ (p.comp q)) : Path.IsReduced Γ p := by
  induction q with
  | nil => exact hp
  | cons q e ih => exact ih (hp.of_cons Γ)

/-- Mapping a path maps its dart list pointwise. -/
@[simp] theorem Hom.darts_mapPath {Δ : SerreGraph} (f : Γ.Hom Δ)
    {a b : Γ.V} (p : Γ.Path a b) :
    Path.darts Δ (f.toPrefunctor.mapPath p) = (Path.darts Γ p).map f.mapE := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, Path.darts_cons Δ, ih]
    simp

/-- A morphism injective on darts preserves and reflects reduced paths. -/
theorem Hom.isReduced_mapPath_iff {Δ : SerreGraph} (f : Γ.Hom Δ)
    (hf : Function.Injective f.mapE) {a b : Γ.V} (p : Γ.Path a b) :
    Path.IsReduced Δ (f.toPrefunctor.mapPath p) ↔ Path.IsReduced Γ p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    cases p with
    | nil => simp [Path.IsReduced]
    | cons p k =>
      simp only [Prefunctor.mapPath_cons, Path.isReduced_cons_cons,
        Hom.toPrefunctor_map_val, ← f.map_rev, ne_eq, hf.eq_iff] at ih ⊢
      exact and_congr ih Iff.rfl

private theorem isReduced_pair_comp {a b c d : Γ.V}
    (e : Quiver.Hom a b) (f : Quiver.Hom b c) (p : Γ.Path c d) :
    Path.IsReduced Γ ((e.toPath.comp f.toPath).comp p) ↔
      f.1 ≠ Γ.rev e.1 ∧ Path.IsReduced Γ (f.toPath.comp p) := by
  induction p with
  | nil => simp [Quiver.Path.comp, Quiver.Hom.toPath, Path.IsReduced]
  | cons p k ih =>
    cases p with
    | nil => simp [Quiver.Path.comp, Quiver.Hom.toPath, Path.IsReduced]
    | cons p l =>
      simp only [Quiver.Path.comp_cons, Path.IsReduced] at ih ⊢
      rw [← and_assoc, ← ih]

/-- Reversing a path preserves the absence of immediate backtracking. -/
@[simp] theorem Path.isReduced_reverse {a b : Γ.V} (p : Γ.Path a b) :
    Path.IsReduced Γ p.reverse ↔ Path.IsReduced Γ p := by
  induction p with
  | nil => simp [Path.IsReduced]
  | cons p e ih =>
    cases p with
    | nil => simp [Quiver.Path.reverse, Path.IsReduced]
    | cons p f =>
      rw [Quiver.Path.reverse, Quiver.Path.reverse, ← Quiver.Path.comp_assoc,
        isReduced_pair_comp]
      simp only [reverse_val, Γ.rev_rev, Path.isReduced_cons_cons]
      exact (and_congr (ne_comm : Γ.rev f.1 ≠ e.1 ↔ e.1 ≠ Γ.rev f.1) ih).trans and_comm

/-- A suffix of a reduced concatenation is reduced. -/
theorem Path.IsReduced.of_comp_right {a b c : Γ.V} {p : Γ.Path a b} {q : Γ.Path b c}
    (hp : Path.IsReduced Γ (p.comp q)) : Path.IsReduced Γ q := by
  rw [← Path.isReduced_reverse, Quiver.Path.reverse_comp] at hp
  exact (Path.isReduced_reverse Γ q).mp (hp.of_comp_left Γ)

/-- Paths in a set of darts that preserves a vertex set `R` start in `R` exactly when they end
in `R`. -/
theorem Path.mem_iff_mem_of_forall_mem_darts {S : Set Γ.E} {R : Set Γ.V}
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) (hR : ∀ e ∈ S, Γ.src e ∈ R → Γ.tgt e ∈ R)
    {a b : Γ.V} (p : Γ.Path a b) (hp : ∀ e ∈ Path.darts Γ p, e ∈ S) : a ∈ R ↔ b ∈ R := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    have he : e ∈ S := hp e (by simp)
    rw [ih fun f hf => hp f (by simp [hf])]
    exact ⟨hR e he, fun h => by simpa using hR _ (hS e he) (by simpa using h)⟩

/-- A path from a vertex set `R` to its complement has a dart from `R` to its complement. -/
theorem Path.exists_boundary_dart {a b : Γ.V} (p : Γ.Path a b) (R : Set Γ.V)
    (ha : a ∈ R) (hb : b ∉ R) : ∃ e ∈ Path.darts Γ p, Γ.src e ∈ R ∧ Γ.tgt e ∉ R := by
  obtain ⟨u, hu, v, hv, e, p₁, p₂, rfl⟩ :=
    Quiver.Path.exists_mem_notMem_hom_path_path_of_notMem_mem p R ha hb
  exact ⟨e.1, by simp, by rwa [e.2.1], by rwa [e.2.2]⟩

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- A path all of whose darts lie in `S` lifts through the inclusion of the restriction. -/
theorem exists_restrict_path {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ S) :
    ∃ q : (Γ.restrict S hS).Path a b,
      (Γ.restrictInclusion S hS).toPrefunctor.mapPath q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq⟩ := ih fun f hf => hp f (by simp [hf])
    refine ⟨q.cons ⟨⟨e.1, hp e.1 (by simp)⟩, e.2⟩, ?_⟩
    subst hq
    rfl

/-- The darts of a path in the restriction lie in `S`. -/
theorem mem_of_mem_darts_mapPath {a b : (Γ.restrict S hS).V}
    (q : (Γ.restrict S hS).Path a b) {e : Γ.E}
    (he : e ∈ Path.darts Γ ((Γ.restrictInclusion S hS).toPrefunctor.mapPath q)) : e ∈ S := by
  rw [Hom.darts_mapPath] at he
  obtain ⟨f, -, rfl⟩ := List.mem_map.mp he
  exact f.2

/-- A path in the restriction is reduced exactly when it is reduced in the ambient graph. -/
@[simp] theorem isReduced_restrictInclusion_mapPath_iff {a b : (Γ.restrict S hS).V}
    (q : (Γ.restrict S hS).Path a b) :
    Path.IsReduced Γ ((Γ.restrictInclusion S hS).toPrefunctor.mapPath q) ↔
      Path.IsReduced (Γ.restrict S hS) q :=
  Hom.isReduced_mapPath_iff _ (Γ.restrictInclusion S hS) Subtype.val_injective q

/-- The restriction is preconnected exactly when any two vertices are joined by a path of `Γ`
whose darts lie in `S`. -/
theorem preconnected_restrict_iff : (Γ.restrict S hS).Preconnected ↔
    ∀ a b : Γ.V, ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S := by
  rw [preconnected_iff]
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · obtain ⟨q⟩ := h a b
    exact ⟨_, fun e he => Γ.mem_of_mem_darts_mapPath S hS q he⟩
  · obtain ⟨p, hp⟩ := h a b
    exact ⟨(Γ.exists_restrict_path S hS p hp).choose⟩

end Restrict

/-- Traversing a rose petal and then its reverse is a backtrack. -/
theorem rose_not_isReduced_backtrack {α : Type*} (a : α) :
    ¬ Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (a, false))) := by
  simp [Path.IsReduced, rose]

/-- Traversing one rose petal and then the reverse of a different petal is reduced. -/
theorem rose_isReduced_of_ne {α : Type*} {a b : α} (hab : a ≠ b) :
    Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (b, false))) := by
  simpa [Path.IsReduced, rose] using hab.symm

/-- A rose petal is a closed path of length one. -/
def rosePetal {α : Type*} (a : α) : (rose α).Path PUnit.unit PUnit.unit :=
  ((rose α).dart (a, true)).toPath

/-- A rose petal is the path consisting of its positive dart. -/
theorem rosePetal_eq_toPath {α : Type*} (a : α) :
    rosePetal a = ((rose α).dart (a, true)).toPath := (rfl)

@[simp] theorem rosePetal_length {α : Type*} (a : α) :
    (rosePetal a).length = 1 := by
  rw [rosePetal_eq_toPath]
  exact Quiver.Path.length_toPath _

/-- A rose petal is reduced. -/
theorem rosePetal_isReduced {α : Type*} (a : α) :
    Path.IsReduced (rose α) (rosePetal a) := by
  exact Path.isReduced_toPath _ _

end SerreGraph

end TauCeti
