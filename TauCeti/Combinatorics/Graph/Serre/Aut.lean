/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Convex
public import TauCeti.Combinatorics.Graph.Serre.Dist
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Combinatorics.Quiver.Cast

/-!
# Automorphisms of Serre graphs

An automorphism of a Serre graph is a pair of bijections of its vertices and darts commuting with
the source and reversal maps. Automorphisms form a group, `SerreGraph.Aut Γ`, acting on the
vertices and on the darts. A group action on a Serre graph is then a homomorphism into this
group, as in Serre's *Trees*.

Automorphisms preserve reduced paths and distances. In an acyclic graph an automorphism fixing
two vertices fixes every dart of the reduced path between them, so the fixed vertices of an
automorphism form a convex set.

The segment carries the automorphism exchanging its two vertices; it maps the edge to its
reverse, which is the kind of inversion excluded from actions on trees.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1, §3.1 and §6.1.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- An automorphism of a Serre graph: bijections of the vertices and of the darts preserving
sources and reversal. -/
structure Aut where
  /-- The bijection of vertices. -/
  equivV : Γ.V ≃ Γ.V
  /-- The bijection of darts. -/
  equivE : Γ.E ≃ Γ.E
  /-- Sources are preserved. -/
  map_src : ∀ e, Γ.src (equivE e) = equivV (Γ.src e)
  /-- Reversal is preserved. -/
  map_rev : ∀ e, equivE (Γ.rev e) = Γ.rev (equivE e)

namespace Aut

variable {Γ}

@[ext] theorem ext {φ ψ : Γ.Aut} (hV : ∀ v, φ.equivV v = ψ.equivV v)
    (hE : ∀ e, φ.equivE e = ψ.equivE e) : φ = ψ := by
  obtain ⟨φV, φE, _, _⟩ := φ
  obtain ⟨ψV, ψE, _, _⟩ := ψ
  obtain rfl : φV = ψV := Equiv.ext hV
  obtain rfl : φE = ψE := Equiv.ext hE
  rfl

/-- Automorphisms form a group under composition, with `φ * ψ` acting as `ψ` followed by `φ`. -/
instance : Group Γ.Aut where
  mul φ ψ :=
    { equivV := ψ.equivV.trans φ.equivV
      equivE := ψ.equivE.trans φ.equivE
      map_src e := by simp only [Equiv.trans_apply, φ.map_src, ψ.map_src]
      map_rev e := by simp only [Equiv.trans_apply, φ.map_rev, ψ.map_rev] }
  one :=
    { equivV := Equiv.refl _
      equivE := Equiv.refl _
      map_src _ := rfl
      map_rev _ := rfl }
  inv φ :=
    { equivV := φ.equivV.symm
      equivE := φ.equivE.symm
      map_src e := by rw [Equiv.eq_symm_apply, ← φ.map_src, Equiv.apply_symm_apply]
      map_rev e := by rw [Equiv.symm_apply_eq, φ.map_rev, Equiv.apply_symm_apply] }
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel φ := ext (fun v => φ.equivV.symm_apply_apply v)
    (fun e => φ.equivE.symm_apply_apply e)

/-- Automorphisms act on vertices. -/
instance : MulAction Γ.Aut Γ.V where
  smul φ v := φ.equivV v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Automorphisms act on darts. -/
instance : MulAction Γ.Aut Γ.E where
  smul φ e := φ.equivE e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_vertex_def (φ : Γ.Aut) (v : Γ.V) : φ • v = φ.equivV v := (rfl)

theorem smul_dart_def (φ : Γ.Aut) (e : Γ.E) : φ • e = φ.equivE e := (rfl)

@[simp] theorem src_smul (φ : Γ.Aut) (e : Γ.E) : Γ.src (φ • e) = φ • Γ.src e :=
  φ.map_src e

@[simp] theorem rev_smul (φ : Γ.Aut) (e : Γ.E) : Γ.rev (φ • e) = φ • Γ.rev e :=
  (φ.map_rev e).symm

@[simp] theorem tgt_smul (φ : Γ.Aut) (e : Γ.E) : Γ.tgt (φ • e) = φ • Γ.tgt e := by
  rw [tgt, rev_smul, src_smul, src_rev]

/-- The graph morphism underlying an automorphism. -/
def toHom (φ : Γ.Aut) : Γ.Hom Γ where
  mapV v := φ • v
  mapE e := φ • e
  map_src := src_smul φ
  map_rev e := (rev_smul φ e).symm

@[simp] theorem toHom_mapV (φ : Γ.Aut) (v : Γ.V) : φ.toHom.mapV v = φ • v := (rfl)

@[simp] theorem toHom_mapE (φ : Γ.Aut) (e : Γ.E) : φ.toHom.mapE e = φ • e := (rfl)

theorem toHom_mapE_injective (φ : Γ.Aut) : Function.Injective φ.toHom.mapE :=
  φ.equivE.injective

/-- Automorphisms preserve distances. -/
@[simp] theorem dist_smul (φ : Γ.Aut) (a b : Γ.V) : Γ.dist (φ • a) (φ • b) = Γ.dist a b := by
  -- Each automorphism maps paths to paths of the same length, and so does its inverse.
  have key : ∀ (ψ : Γ.Aut) (a b : Γ.V), Γ.dist (ψ • a) (ψ • b) ≤ Γ.dist a b := by
    intro ψ a b
    rcases isEmpty_or_nonempty (Γ.Path a b) with hab | hab
    · have : IsEmpty (Γ.Path (ψ • a) (ψ • b)) := ⟨fun p =>
        hab.false ((ψ⁻¹.toHom.toPrefunctor.mapPath p).cast (inv_smul_smul ψ a)
          (inv_smul_smul ψ b))⟩
      rw [dist_of_isEmpty this, dist_of_isEmpty hab]
    · exact ψ.toHom.dist_le hab
  refine (key φ a b).antisymm ?_
  simpa only [inv_smul_smul] using key φ⁻¹ (φ • a) (φ • b)

/-- An automorphism translates a path to a path whose darts are the translates of the darts of
the original path, and which is reduced exactly when the original path is. -/
theorem exists_path_darts_eq_map_smul (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    ∃ q : Γ.Path (φ • a) (φ • b), Path.darts Γ q = (Path.darts Γ p).map (φ • ·) ∧
      (Path.IsReduced Γ q ↔ Path.IsReduced Γ p) :=
  ⟨φ.toHom.toPrefunctor.mapPath p, Hom.darts_mapPath Γ φ.toHom p,
    Hom.isReduced_mapPath_iff Γ φ.toHom φ.toHom_mapE_injective p⟩

/-! ### Fixed points in acyclic graphs -/

/-- In an acyclic graph, an automorphism fixing two vertices fixes every dart of a reduced path
joining them. -/
theorem smul_eq_of_mem_darts (h : Γ.IsAcyclic) (φ : Γ.Aut) {a b : Γ.V} (ha : φ • a = a)
    (hb : φ • b = b) {p : Γ.Path a b} (hp : Path.IsReduced Γ p) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : φ • e = e := by
  -- The image path, transported to the original endpoints, is another reduced path.
  have hq : Path.IsReduced Γ ((φ.toHom.toPrefunctor.mapPath p).cast ha hb) :=
    (Path.isReduced_cast Γ ha hb _).mpr
      ((Hom.isReduced_mapPath_iff Γ φ.toHom φ.toHom_mapE_injective p).mpr hp)
  have hdarts : (Path.darts Γ p).map (φ • ·) = (Path.darts Γ p).map id := by
    rw [List.map_id]
    calc (Path.darts Γ p).map (φ • ·) = Path.darts Γ (φ.toHom.toPrefunctor.mapPath p) :=
          (Hom.darts_mapPath Γ φ.toHom p).symm
      _ = Path.darts Γ ((φ.toHom.toPrefunctor.mapPath p).cast ha hb) :=
          (Path.darts_cast Γ ha hb _).symm
      _ = Path.darts Γ p := congrArg (Path.darts Γ) (h.eq_of_isReduced hq hp)
  exact List.map_inj_left.mp hdarts e he

/-- In an acyclic graph, the vertices fixed by an automorphism form a convex set. -/
theorem isConvex_fixedBy (h : Γ.IsAcyclic) (φ : Γ.Aut) :
    Γ.IsConvex (MulAction.fixedBy Γ.V φ) := isConvex_iff.mpr fun _ ha _ hb _ hp e he => by
  rw [MulAction.mem_fixedBy, ← src_smul,
    smul_eq_of_mem_darts h φ (MulAction.mem_fixedBy.mp ha) (MulAction.mem_fixedBy.mp hb) hp he]

end Aut

/-- The automorphism of the segment exchanging its two vertices. -/
def segmentSwap : segment.Aut where
  equivV := Function.Involutive.toPerm not Bool.not_not
  equivE := Function.Involutive.toPerm not Bool.not_not
  map_src _ := rfl
  map_rev _ := rfl

/-- Exchanging the vertices of the segment inverts its edge. -/
theorem segmentSwap_smul (e : segment.E) : segmentSwap • e = segment.rev e := by
  rw [Aut.smul_dart_def]
  rfl

end SerreGraph
end TauCeti
