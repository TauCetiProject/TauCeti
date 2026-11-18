/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import TauCeti.Combinatorics.Graph.Serre.Card
import Mathlib.Basic.Finite.Sum

/-!
# Barycentric subdivision of a Serre graph

The barycentric subdivision of a Serre graph `Γ` inserts a new vertex in the middle of every
geometric edge. Its vertices are the vertices of `Γ` together with the geometric edges of `Γ`,
the midpoints, and each dart `e` of `Γ` gives two mutually reverse darts: the half
`Γ.barycentricDart e true` of `e` running from the source of `e` to the midpoint of `e`, and its
reverse `Γ.barycentricDart e false`.

Every automorphism of `Γ` induces an automorphism of the subdivision, and the induced
automorphism never maps a dart to its reverse: an automorphism inverting an edge of `Γ` fixes
the midpoint of that edge instead. This is how an action with inversions is replaced by an
action without inversions.

Subdivision preserves connectedness and acyclicity, so the subdivision of a tree is a tree. The
subdivision of a finite graph is finite, with one new vertex for each geometric edge, and with
twice as many darts and twice as many geometric edges as the graph.

## Main declarations

* `TauCeti.SerreGraph.barycentricSubdivision`: the barycentric subdivision.
* `TauCeti.SerreGraph.Aut.barycentricSubdivision`: the induced automorphisms of the subdivision,
  with `TauCeti.SerreGraph.Aut.barycentricSubdivision_smul_ne_rev`: they have no inversions.
* `TauCeti.SerreGraph.IsTree.barycentricSubdivision`: the subdivision of a tree is a tree.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 and §3.1.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph.{u, v})

/-- The barycentric subdivision of a Serre graph: a new vertex, the midpoint, is inserted in
every geometric edge. Its vertices are `Γ.barycentricVertex v` and `Γ.barycentricMidpoint m`,
and its darts are the two halves `Γ.barycentricDart e b` of each dart `e`. The body is exposed
because the compiler needs the vertex and dart types to compile these three embeddings. -/
@[expose] def barycentricSubdivision : SerreGraph.{max u v, v} where
  V := Γ.V ⊕ Γ.GeomEdge
  E := Γ.E × Bool
  src x := cond x.2 (.inl (Γ.src x.1)) (.inr (Γ.toGeomEdge x.1))
  rev x := (x.1, !x.2)
  rev_rev x := by simp
  rev_ne x := by simp [Prod.ext_iff]

/-- A vertex of a Serre graph, as a vertex of its barycentric subdivision. -/
def barycentricVertex (v : Γ.V) : Γ.barycentricSubdivision.V := Sum.inl v

/-- The midpoint of a geometric edge, as a vertex of the barycentric subdivision. -/
def barycentricMidpoint (m : Γ.GeomEdge) : Γ.barycentricSubdivision.V := Sum.inr m

/-- A half of a dart `e`, as a dart of the barycentric subdivision: `Γ.barycentricDart e true`
runs from the source of `e` to the midpoint of `e`, and `Γ.barycentricDart e false` is its
reverse. -/
def barycentricDart (e : Γ.E) (b : Bool) : Γ.barycentricSubdivision.E := (e, b)

theorem barycentricVertex_injective : Function.Injective Γ.barycentricVertex :=
  Sum.inl_injective

theorem barycentricMidpoint_injective : Function.Injective Γ.barycentricMidpoint :=
  Sum.inr_injective

@[simp] theorem barycentricVertex_inj {v w : Γ.V} :
    Γ.barycentricVertex v = Γ.barycentricVertex w ↔ v = w :=
  Γ.barycentricVertex_injective.eq_iff

@[simp] theorem barycentricMidpoint_inj {m n : Γ.GeomEdge} :
    Γ.barycentricMidpoint m = Γ.barycentricMidpoint n ↔ m = n :=
  Γ.barycentricMidpoint_injective.eq_iff

/-- A vertex of the graph is not a midpoint. -/
@[simp] theorem barycentricVertex_ne_barycentricMidpoint (v : Γ.V) (m : Γ.GeomEdge) :
    Γ.barycentricVertex v ≠ Γ.barycentricMidpoint m :=
  Sum.inl_ne_inr

/-- A midpoint is not a vertex of the graph. -/
@[simp] theorem barycentricMidpoint_ne_barycentricVertex (m : Γ.GeomEdge) (v : Γ.V) :
    Γ.barycentricMidpoint m ≠ Γ.barycentricVertex v :=
  Sum.inr_ne_inl

@[simp] theorem barycentricDart_inj {e f : Γ.E} {b c : Bool} :
    Γ.barycentricDart e b = Γ.barycentricDart f c ↔ e = f ∧ b = c :=
  Prod.mk_inj

variable {Γ} in
/-- Every vertex of the barycentric subdivision is a vertex of the graph or a midpoint. -/
@[elab_as_elim]
theorem barycentricSubdivision_vertex_cases {motive : Γ.barycentricSubdivision.V → Prop}
    (vertex : ∀ v, motive (Γ.barycentricVertex v))
    (midpoint : ∀ m, motive (Γ.barycentricMidpoint m)) (x : Γ.barycentricSubdivision.V) :
    motive x :=
  Sum.rec vertex midpoint x

variable {Γ} in
/-- Every dart of the barycentric subdivision is a half of a dart of the graph. -/
@[elab_as_elim]
theorem barycentricSubdivision_dart_cases {motive : Γ.barycentricSubdivision.E → Prop}
    (dart : ∀ e b, motive (Γ.barycentricDart e b)) (x : Γ.barycentricSubdivision.E) :
    motive x :=
  dart x.1 x.2

/-- The outgoing half of a dart starts at the source of the dart. -/
@[simp] theorem barycentricSubdivision_src_true (e : Γ.E) :
    Γ.barycentricSubdivision.src (Γ.barycentricDart e true) = Γ.barycentricVertex (Γ.src e) :=
  (rfl)

/-- The reverse of the outgoing half of a dart starts at the midpoint of the dart. -/
@[simp] theorem barycentricSubdivision_src_false (e : Γ.E) :
    Γ.barycentricSubdivision.src (Γ.barycentricDart e false) =
      Γ.barycentricMidpoint (Γ.toGeomEdge e) := (rfl)

/-- The two halves of a dart are mutually reverse. -/
@[simp] theorem barycentricSubdivision_rev (e : Γ.E) (b : Bool) :
    Γ.barycentricSubdivision.rev (Γ.barycentricDart e b) = Γ.barycentricDart e !b := (rfl)

/-- The outgoing half of a dart ends at the midpoint of the dart. -/
@[simp] theorem barycentricSubdivision_tgt_true (e : Γ.E) :
    Γ.barycentricSubdivision.tgt (Γ.barycentricDart e true) =
      Γ.barycentricMidpoint (Γ.toGeomEdge e) := (rfl)

/-- The reverse of the outgoing half of a dart ends at the source of the dart. -/
@[simp] theorem barycentricSubdivision_tgt_false (e : Γ.E) :
    Γ.barycentricSubdivision.tgt (Γ.barycentricDart e false) = Γ.barycentricVertex (Γ.src e) :=
  (rfl)

/-! ### Finiteness -/

/-- The barycentric subdivision of a graph with finitely many vertices and geometric edges has
finitely many vertices. -/
instance [Finite Γ.V] [Finite Γ.GeomEdge] : Finite Γ.barycentricSubdivision.V :=
  inferInstanceAs (Finite (Γ.V ⊕ Γ.GeomEdge))

/-- The barycentric subdivision of a graph with finitely many darts has finitely many darts. -/
instance [Finite Γ.E] : Finite Γ.barycentricSubdivision.E :=
  inferInstanceAs (Finite (Γ.E × Bool))

/-- The vertices of the barycentric subdivision are the vertices and the midpoints of the
geometric edges of the graph. -/
@[simp] theorem card_barycentricSubdivision_V [Finite Γ.V] [Finite Γ.GeomEdge] :
    Nat.card Γ.barycentricSubdivision.V = Nat.card Γ.V + Nat.card Γ.GeomEdge :=
  Nat.card_sum

/-- Each dart of the graph has two halves in the barycentric subdivision. -/
@[simp] theorem card_barycentricSubdivision_E :
    Nat.card Γ.barycentricSubdivision.E = 2 * Nat.card Γ.E :=
  (Nat.card_prod Γ.E Bool).trans <| by simp [mul_comm]

/-- Each geometric edge of the graph has two halves in the barycentric subdivision. -/
@[simp] theorem card_barycentricSubdivision_geomEdge :
    Nat.card Γ.barycentricSubdivision.GeomEdge = 2 * Nat.card Γ.GeomEdge := by
  have h := Γ.barycentricSubdivision.card_E_eq_two_mul_card_geomEdge
  rw [card_barycentricSubdivision_E, card_E_eq_two_mul_card_geomEdge] at h
  omega

/-! ### Induced automorphisms -/

namespace Aut

variable {Γ}

/-- The automorphism of the barycentric subdivision induced by an automorphism of the graph. -/
private def barycentricSubdivisionFun (φ : Γ.Aut) : Γ.barycentricSubdivision.Aut where
  equivV := Equiv.sumCongr (MulAction.toPerm φ) (MulAction.toPerm φ)
  equivE := Equiv.prodCongr (MulAction.toPerm φ) (Equiv.refl Bool)
  map_src := by
    rintro ⟨e, _ | _⟩
    · exact congrArg Sum.inr (smul_toGeomEdge φ e).symm
    · exact congrArg Sum.inl (src_smul φ e)
  map_rev := by rintro ⟨e, b⟩; rfl

private theorem barycentricSubdivisionFun_smul_barycentricVertex (φ : Γ.Aut) (v : Γ.V) :
    barycentricSubdivisionFun φ • Γ.barycentricVertex v = Γ.barycentricVertex (φ • v) :=
  (smul_vertex_def _ _).trans rfl

private theorem barycentricSubdivisionFun_smul_barycentricMidpoint (φ : Γ.Aut)
    (m : Γ.GeomEdge) :
    barycentricSubdivisionFun φ • Γ.barycentricMidpoint m = Γ.barycentricMidpoint (φ • m) :=
  (smul_vertex_def _ _).trans rfl

private theorem barycentricSubdivisionFun_smul_barycentricDart (φ : Γ.Aut) (e : Γ.E)
    (b : Bool) :
    barycentricSubdivisionFun φ • Γ.barycentricDart e b = Γ.barycentricDart (φ • e) b :=
  (smul_dart_def _ _).trans rfl

/-- The automorphism of the barycentric subdivision induced by an automorphism of the graph, as
a group homomorphism. -/
def barycentricSubdivision : Γ.Aut →* Γ.barycentricSubdivision.Aut where
  toFun := barycentricSubdivisionFun
  map_one' := by
    ext x
    · simp only [← smul_vertex_def]
      induction x using barycentricSubdivision_vertex_cases <;>
        simp [barycentricSubdivisionFun_smul_barycentricVertex,
          barycentricSubdivisionFun_smul_barycentricMidpoint]
    · simp only [← smul_dart_def]
      induction x using barycentricSubdivision_dart_cases
      simp [barycentricSubdivisionFun_smul_barycentricDart]
  map_mul' φ ψ := by
    ext x
    · simp only [← smul_vertex_def]
      induction x using barycentricSubdivision_vertex_cases <;>
        simp [mul_smul, barycentricSubdivisionFun_smul_barycentricVertex,
          barycentricSubdivisionFun_smul_barycentricMidpoint]
    · simp only [← smul_dart_def]
      induction x using barycentricSubdivision_dart_cases
      simp [mul_smul, barycentricSubdivisionFun_smul_barycentricDart]

@[simp] theorem barycentricSubdivision_smul_barycentricVertex (φ : Γ.Aut) (v : Γ.V) :
    barycentricSubdivision φ • Γ.barycentricVertex v = Γ.barycentricVertex (φ • v) :=
  barycentricSubdivisionFun_smul_barycentricVertex φ v

@[simp] theorem barycentricSubdivision_smul_barycentricMidpoint (φ : Γ.Aut) (m : Γ.GeomEdge) :
    barycentricSubdivision φ • Γ.barycentricMidpoint m = Γ.barycentricMidpoint (φ • m) :=
  barycentricSubdivisionFun_smul_barycentricMidpoint φ m

@[simp] theorem barycentricSubdivision_smul_barycentricDart (φ : Γ.Aut) (e : Γ.E) (b : Bool) :
    barycentricSubdivision φ • Γ.barycentricDart e b = Γ.barycentricDart (φ • e) b :=
  barycentricSubdivisionFun_smul_barycentricDart φ e b

/-- The automorphisms of the barycentric subdivision induced by automorphisms of the graph have
no inversions. -/
theorem barycentricSubdivision_smul_ne_rev (φ : Γ.Aut) (x : Γ.barycentricSubdivision.E) :
    barycentricSubdivision φ • x ≠ Γ.barycentricSubdivision.rev x := by
  induction x using barycentricSubdivision_dart_cases
  simp

/-- Distinct automorphisms induce distinct automorphisms of the barycentric subdivision. -/
theorem barycentricSubdivision_injective :
    Function.Injective (barycentricSubdivision : Γ.Aut → Γ.barycentricSubdivision.Aut) := by
  intro φ ψ h
  ext x
  · rw [← smul_vertex_def, ← smul_vertex_def]
    exact Γ.barycentricVertex_injective
      (by simpa using congrArg (· • Γ.barycentricVertex x) h)
  · rw [← smul_dart_def, ← smul_dart_def]
    simpa using congrArg (· • Γ.barycentricDart x true) h

/-- An induced automorphism fixes the midpoint of a dart exactly when the automorphism fixes or
inverts the dart. -/
theorem barycentricSubdivision_smul_barycentricMidpoint_eq_iff (φ : Γ.Aut) (e : Γ.E) :
    barycentricSubdivision φ • Γ.barycentricMidpoint (Γ.toGeomEdge e) =
      Γ.barycentricMidpoint (Γ.toGeomEdge e) ↔ φ • e = e ∨ φ • e = Γ.rev e := by
  rw [barycentricSubdivision_smul_barycentricMidpoint, barycentricMidpoint_inj, smul_toGeomEdge,
    eq_comm, toGeomEdge_eq_toGeomEdge_iff]

end Aut

/-! ### Paths in the subdivision -/

/-- A path of the graph gives a path of the barycentric subdivision with the same endpoints. -/
theorem nonempty_barycentricSubdivision_path {a b : Γ.V} (p : Γ.Path a b) :
    Nonempty (Γ.barycentricSubdivision.Path (Γ.barycentricVertex a) (Γ.barycentricVertex b)) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | cons _ e ih =>
    obtain ⟨q⟩ := ih
    obtain ⟨e, rfl, rfl⟩ := e
    have e₁ : Γ.barycentricVertex (Γ.src e) ⟶ Γ.barycentricMidpoint (Γ.toGeomEdge e) :=
      ⟨Γ.barycentricDart e true, by simp, by simp⟩
    have e₂ : Γ.barycentricMidpoint (Γ.toGeomEdge e) ⟶ Γ.barycentricVertex (Γ.tgt e) :=
      ⟨Γ.barycentricDart (Γ.rev e) false, by simp, by simp⟩
    exact ⟨(q.cons e₁).cons e₂⟩

/-- Every vertex of the barycentric subdivision is joined by a path to a vertex of the graph. -/
theorem exists_nonempty_barycentricSubdivision_path (x : Γ.barycentricSubdivision.V) :
    ∃ a : Γ.V, Nonempty (Γ.barycentricSubdivision.Path x (Γ.barycentricVertex a)) := by
  induction x using barycentricSubdivision_vertex_cases with
  | vertex v => exact ⟨v, ⟨.nil⟩⟩
  | midpoint m =>
    obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective m
    have e₁ : Γ.barycentricMidpoint (Γ.toGeomEdge e) ⟶ Γ.barycentricVertex (Γ.src e) :=
      ⟨Γ.barycentricDart e false, by simp, by simp⟩
    exact ⟨Γ.src e, ⟨e₁.toPath⟩⟩

variable {Γ}

/-- The barycentric subdivision of a preconnected graph is preconnected. -/
theorem Preconnected.barycentricSubdivision (h : Γ.Preconnected) :
    Γ.barycentricSubdivision.Preconnected := by
  refine (preconnected_iff _).mpr fun x y => ?_
  obtain ⟨a, ⟨p⟩⟩ := Γ.exists_nonempty_barycentricSubdivision_path x
  obtain ⟨b, ⟨q⟩⟩ := Γ.exists_nonempty_barycentricSubdivision_path y
  obtain ⟨r⟩ := Γ.nonempty_barycentricSubdivision_path (Γ.preconnected_iff.mp h a b).some
  exact ⟨(p.comp r).comp q.reverse⟩

/-- The barycentric subdivision of a connected graph is connected. -/
theorem Connected.barycentricSubdivision (h : Γ.Connected) :
    Γ.barycentricSubdivision.Connected :=
  (connected_iff _).mpr ⟨(Γ.connected_iff.mp h).1.map Γ.barycentricVertex,
    (Γ.connected_iff.mp h).2.barycentricSubdivision⟩

variable (Γ) in
/-- The two halves replacing a dart in the barycentric subdivision. -/
private def barycentricHalves (e : Γ.E) : List Γ.barycentricSubdivision.E :=
  [Γ.barycentricDart e true, Γ.barycentricDart (Γ.rev e) false]

/-- Appending a dart to a reduced path of the graph gives a reduced path as soon as the outgoing
half of the dart does not reverse the last of the halves of the path. -/
private theorem isReduced_cons_dart {a : Γ.V} {e : Γ.E} (q : Γ.Path a (Γ.src e))
    (hq : Path.IsReduced Γ q)
    (h : ∀ x ∈ ((Path.darts Γ q).flatMap Γ.barycentricHalves).getLast?,
      Γ.barycentricDart e true ≠ Γ.barycentricSubdivision.rev x) :
    Path.IsReduced Γ (q.cons (Γ.dart e)) := by
  cases q with
  | nil => exact Path.isReduced_toPath Γ (Γ.dart e)
  | cons q d =>
    refine (Path.isReduced_cons_cons Γ q d _).mpr ⟨hq, fun he => ?_⟩
    have hne : e ≠ Γ.rev d.1 := by
      simpa using h (Γ.barycentricDart (Γ.rev d.1) false) (by simp [barycentricHalves])
    exact hne (by simpa using he)

/-- Two darts `e` and `f` with the same midpoint are mutually reverse as soon as the reverse of
the outgoing half of `e` does not reverse the outgoing half of `f`. -/
private theorem eq_rev_of_toGeomEdge_eq {e f : Γ.E} (hf : Γ.toGeomEdge f = Γ.toGeomEdge e)
    (h : Γ.barycentricDart e false ≠
      Γ.barycentricSubdivision.rev (Γ.barycentricDart f true)) : e = Γ.rev f :=
  (Γ.toGeomEdge_eq_toGeomEdge_iff.mp hf).resolve_left fun he => h (by simp [he])

/-- A reduced path of the barycentric subdivision starting at a vertex of the graph follows the
halves of a reduced path of the graph, and when it ends at a midpoint it ends with the outgoing
half of a dart continuing that path. -/
private theorem exists_darts_eq_of_isReduced {a : Γ.V} {y : Γ.barycentricSubdivision.V}
    (p : Γ.barycentricSubdivision.Path (Γ.barycentricVertex a) y)
    (hp : Path.IsReduced _ p) :
    (∀ b, y = Γ.barycentricVertex b → ∃ q : Γ.Path a b, Path.IsReduced Γ q ∧
      Path.darts _ p = (Path.darts Γ q).flatMap Γ.barycentricHalves) ∧
    (∀ m, y = Γ.barycentricMidpoint m → ∃ (b c : Γ.V) (q : Γ.Path a b) (f : b ⟶ c),
      Γ.toGeomEdge f.1 = m ∧ Path.IsReduced Γ (q.cons f) ∧
      Path.darts _ p =
        (Path.darts Γ q).flatMap Γ.barycentricHalves ++ [Γ.barycentricDart f.1 true]) := by
  induction p with
  | nil =>
    refine ⟨fun b hb => ?_, fun m hm => by simp at hm⟩
    obtain rfl := Γ.barycentricVertex_injective hb
    exact ⟨.nil, Path.isReduced_nil Γ a, by simp⟩
  | cons p g ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (Path.IsReduced.of_cons _ hp)
    have hlast := ((Path.isReduced_comp_iff _ p g.toPath).mp hp).2.2
    obtain ⟨x, hs, ht⟩ := g
    induction x using barycentricSubdivision_dart_cases with | dart e bo
    cases bo
    · -- The last dart reverses an outgoing half: the path ends at a vertex of the graph.
      rw [barycentricSubdivision_src_false] at hs
      rw [barycentricSubdivision_tgt_false] at ht
      refine ⟨fun b hb => ?_, fun m hm => by simp [← ht] at hm⟩
      obtain rfl := Γ.barycentricVertex_injective (ht.trans hb)
      obtain ⟨b', c', q, ⟨f, hfs, hft⟩, hf, hq, hd⟩ := ih₂ _ hs.symm
      obtain rfl : e = Γ.rev f := eq_rev_of_toGeomEdge_eq hf
        (hlast (Γ.barycentricDart f true) (by simp [hd]) (Γ.barycentricDart e false) (by simp))
      subst hft
      exact ⟨q.cons ⟨f, hfs, rfl⟩, hq, by simp [hd, barycentricHalves]⟩
    · -- The last dart is an outgoing half: the path ends at a midpoint.
      rw [barycentricSubdivision_src_true] at hs
      rw [barycentricSubdivision_tgt_true] at ht
      refine ⟨fun b hb => by simp [← ht] at hb, fun m hm => ?_⟩
      obtain rfl := Γ.barycentricMidpoint_injective (ht.trans hm)
      obtain ⟨q, hq, hd⟩ := ih₁ _ hs.symm
      exact ⟨_, _, q, Γ.dart e, by simp, isReduced_cons_dart q hq fun x hx =>
        hlast x (hd ▸ hx) (Γ.barycentricDart e true) (by simp), by simp [hd]⟩

/-- In the barycentric subdivision of an acyclic graph, no nonempty reduced path returns to the
midpoint it started from. -/
private theorem not_isReduced_cons_of_isAcyclic (h : Γ.IsAcyclic) {m : Γ.GeomEdge}
    {y : Γ.barycentricSubdivision.V}
    (p : Γ.barycentricSubdivision.Path (Γ.barycentricMidpoint m) y)
    (g : y ⟶ Γ.barycentricMidpoint m) : ¬Path.IsReduced _ (p.cons g) := by
  intro hp
  have hlast := ((Path.isReduced_comp_iff _ p g.toPath).mp hp).2.2
  obtain ⟨x, hs, ht⟩ := g
  induction x using barycentricSubdivision_dart_cases with | dart e bo
  cases bo
  · simp at ht
  rw [barycentricSubdivision_src_true] at hs
  rw [barycentricSubdivision_tgt_true] at ht
  subst hs
  obtain rfl := Γ.barycentricMidpoint_injective ht
  -- Read backwards, the path before the last dart starts at a vertex of the graph.
  obtain ⟨b, c, q, ⟨f, hfs, hft⟩, hf, hq, hd⟩ := (exists_darts_eq_of_isReduced p.reverse
    ((Path.isReduced_reverse _ p).mpr (Path.IsReduced.of_cons _ hp))).2 _ rfl
  have hd' : Path.darts _ p = (((Path.darts Γ q).flatMap Γ.barycentricHalves ++
      [Γ.barycentricDart f true]).reverse).map Γ.barycentricSubdivision.rev := by
    rw [← hd, ← Path.darts_reverse, Quiver.Path.reverse_reverse]
  rcases Γ.toGeomEdge_eq_toGeomEdge_iff.mp hf with rfl | rfl
  · -- The path leaves and re-enters the midpoint through the same half-edge.
    subst hfs
    rw [Γ.isAcyclic_iff.mp h _ q (Path.IsReduced.of_cons _ hq)] at hd'
    simpa using hlast (Γ.barycentricDart e false) (by simp [hd'])
      (Γ.barycentricDart e true) (by simp)
  · -- The path projects to a nonempty reduced closed path of the graph.
    subst hft
    exact Nat.succ_ne_zero _
      (congrArg Quiver.Path.length (Γ.isAcyclic_iff.mp h (Γ.tgt f) (q.cons ⟨f, hfs, rfl⟩) hq))

/-- The barycentric subdivision of an acyclic graph is acyclic. -/
theorem IsAcyclic.barycentricSubdivision (h : Γ.IsAcyclic) :
    Γ.barycentricSubdivision.IsAcyclic := by
  refine (isAcyclic_iff _).mpr fun u p hp => ?_
  induction u using barycentricSubdivision_vertex_cases with
  | vertex a =>
    obtain ⟨q, hq, hd⟩ := (exists_darts_eq_of_isReduced p hp).1 a rfl
    rw [Γ.isAcyclic_iff.mp h a q hq] at hd
    exact Quiver.Path.eq_nil_of_length_zero p (by rw [← Path.length_darts, hd]; simp)
  | midpoint m =>
    cases p with
    | nil => rfl
    | cons p g => exact (not_isReduced_cons_of_isAcyclic h p g hp).elim

/-- The barycentric subdivision of a tree is a tree. -/
theorem IsTree.barycentricSubdivision (h : Γ.IsTree) : Γ.barycentricSubdivision.IsTree :=
  (isTree_iff _).mpr ⟨(IsTree.connected _ h).barycentricSubdivision,
    (IsTree.isAcyclic _ h).barycentricSubdivision⟩

end SerreGraph
end TauCeti
