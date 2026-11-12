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
public import Mathlib.Data.ZMod.Basic

/-!
# Automorphisms of Serre graphs

An automorphism of a Serre graph is a pair of bijections of its vertices and darts commuting with
the source and reversal maps. Automorphisms form a group, `SerreGraph.Aut Γ`, acting on the
vertices, on the darts and on the geometric edges. A group action on a Serre graph is then a
homomorphism into this group, as in Serre's *Trees*.

Automorphisms preserve reduced paths and distances. In an acyclic graph an automorphism fixing
two vertices fixes every dart of the reduced path between them, so the fixed vertices of an
automorphism form a convex set.

The segment carries the automorphism exchanging its two vertices; it maps the edge to its
reverse, which is the kind of inversion excluded from actions on trees. It is an involution, so
the group of order two acts on the segment, `SerreGraph.segmentSwapHom`.
An inversion admits no invariant morphism of Serre graphs, so in particular no morphism out of
the segment is invariant under the exchange of its two vertices.

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

/-- Automorphisms act on geometric edges. -/
instance : SMul Γ.Aut Γ.GeomEdge where
  smul φ := GeomEdge.lift Γ (fun e => Γ.toGeomEdge (φ • e)) fun e => by
    rw [← rev_smul, toGeomEdge_rev]

@[simp] theorem smul_toGeomEdge (φ : Γ.Aut) (e : Γ.E) :
    φ • Γ.toGeomEdge e = Γ.toGeomEdge (φ • e) :=
  GeomEdge.lift_toGeomEdge Γ _ _ e

/-- Automorphisms act on geometric edges. -/
instance : MulAction Γ.Aut Γ.GeomEdge where
  one_smul x := by
    obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective x
    rw [smul_toGeomEdge, one_smul]
  mul_smul φ ψ x := by
    obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective x
    simp only [smul_toGeomEdge, mul_smul]

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

/-- A morphism of Serre graphs invariant under an automorphism forces that automorphism to map no
dart to its reverse. -/
theorem smul_ne_rev_of_comp_toHom_eq {Δ : SerreGraph} (f : Γ.Hom Δ) (φ : Γ.Aut)
    (h : Hom.comp f φ.toHom = f) (e : Γ.E) : φ • e ≠ Γ.rev e := by
  intro he
  have h₁ : f.mapE (φ • e) = f.mapE e := by
    simpa using congrArg (fun k : Γ.Hom Δ => k.mapE e) h
  rw [he, f.map_rev] at h₁
  exact Δ.rev_ne _ h₁

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

/-- The trivial action of a monoid on a Serre graph maps no dart to its reverse. -/
theorem one_apply_smul_ne_rev (M : Type*) [MulOneClass M] (g : M) (e : Γ.E) :
    (1 : M →* Γ.Aut) g • e ≠ Γ.rev e := by
  simpa using (Γ.rev_ne e).symm

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

/-- Exchanging the vertices of the segment maps the source of a dart to its target. -/
theorem segmentSwap_smul_src (e : segment.E) : segmentSwap • segment.src e = segment.tgt e := by
  rw [← Aut.src_smul, segmentSwap_smul, src_rev]

/-- Exchanging the vertices of the segment maps the target of a dart to its source. -/
theorem segmentSwap_smul_tgt (e : segment.E) : segmentSwap • segment.tgt e = segment.src e := by
  rw [← Aut.tgt_smul, segmentSwap_smul, tgt_rev]

/-- The exchange automorphism of the segment is an involution. -/
@[simp] theorem segmentSwap_mul_self : segmentSwap * segmentSwap = 1 := by
  ext x
  · obtain ⟨e, rfl⟩ := segment_src_surjective x
    rw [← Aut.smul_vertex_def, ← Aut.smul_vertex_def, mul_smul, one_smul, segmentSwap_smul_src,
      segmentSwap_smul_tgt]
  · rw [← Aut.smul_dart_def, ← Aut.smul_dart_def, mul_smul, one_smul, segmentSwap_smul,
      segmentSwap_smul, rev_rev]

private theorem zmultiplesHom_segmentSwap_two :
    zmultiplesHom (Additive segment.Aut) (Additive.ofMul segmentSwap) 2 = 0 := by
  rw [zmultiplesHom_apply, two_zsmul, ← ofMul_mul, segmentSwap_mul_self, ofMul_one]

/-- The action of the group of order two on the segment in which the generator exchanges the two
vertices. -/
def segmentSwapHom : Multiplicative (ZMod 2) →* segment.Aut :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨_, zmultiplesHom_segmentSwap_two⟩)

@[simp] theorem segmentSwapHom_ofAdd_one :
    segmentSwapHom (Multiplicative.ofAdd 1) = segmentSwap := by
  have h := ZMod.lift_coe 2 ⟨_, zmultiplesHom_segmentSwap_two⟩ 1
  rw [Int.cast_one] at h
  simpa [segmentSwapHom] using congrArg Additive.toMul h

/-- The generator of the group of order two inverts the edge of the segment. -/
theorem segmentSwapHom_ofAdd_one_smul (e : segment.E) :
    segmentSwapHom (Multiplicative.ofAdd 1) • e = segment.rev e := by
  rw [segmentSwapHom_ofAdd_one, segmentSwap_smul]

/-- No morphism out of the segment is invariant under the exchange of its two vertices. -/
theorem segment_comp_segmentSwap_toHom_ne {Δ : SerreGraph} (f : segment.Hom Δ) :
    Hom.comp f segmentSwap.toHom ≠ f := fun h =>
  Aut.smul_ne_rev_of_comp_toHom_eq f segmentSwap h true (segmentSwap_smul true)

end SerreGraph
end TauCeti
