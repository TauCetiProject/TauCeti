/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Convex
public import TauCeti.Combinatorics.Graph.Serre.Dist
public import TauCeti.Combinatorics.Graph.Serre.Iso
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Data.ZMod.Basic

/-!
# Automorphisms of Serre graphs

An automorphism of a Serre graph is an isomorphism of the graph with itself, that is, a pair of
bijections of its vertices and darts commuting with the source and reversal maps. Automorphisms
form a group, `SerreGraph.Aut Γ`, under composition of isomorphisms, acting on the vertices, on the
darts and on the geometric edges. A group action on a Serre graph is then a homomorphism into this
group, as in Serre's *Trees*.

An automorphism translates a path to a path of the same length through the translated darts,
reduced exactly when the original path is; translation of paths commutes with concatenation and
reversal and is compatible with the group law. Hence automorphisms preserve distances, and the
`n`-th power of an automorphism moves a vertex joined to its image by at most `|n|` times as
much as the automorphism. In an acyclic graph an automorphism fixing two vertices fixes every
dart of the reduced path between them, so the fixed vertices of an automorphism form a convex set.

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

/-- The automorphisms of a Serre graph: its isomorphisms with itself, that is, bijections of the
vertices and of the darts preserving sources and reversal. -/
abbrev Aut : Type _ := Γ.Iso Γ

namespace Aut

variable {Γ}

/-- Automorphisms form a group under composition, with `φ * ψ` acting as `ψ` followed by `φ`. -/
instance : Group Γ.Aut where
  one := Iso.refl Γ
  mul φ ψ := ψ.trans φ
  inv φ := φ.symm
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_trans_symm

theorem one_def : (1 : Γ.Aut) = Iso.refl Γ := (rfl)

theorem mul_def (φ ψ : Γ.Aut) : φ * ψ = ψ.trans φ := (rfl)

theorem inv_def (φ : Γ.Aut) : φ⁻¹ = φ.symm := (rfl)

@[simp] theorem one_equivV : (1 : Γ.Aut).equivV = Equiv.refl Γ.V := Iso.refl_equivV Γ

@[simp] theorem one_equivE : (1 : Γ.Aut).equivE = Equiv.refl Γ.E := Iso.refl_equivE Γ

@[simp] theorem mul_equivV (φ ψ : Γ.Aut) : (φ * ψ).equivV = ψ.equivV.trans φ.equivV :=
  Iso.trans_equivV ψ φ

@[simp] theorem mul_equivE (φ ψ : Γ.Aut) : (φ * ψ).equivE = ψ.equivE.trans φ.equivE :=
  Iso.trans_equivE ψ φ

@[simp] theorem inv_equivV (φ : Γ.Aut) : φ⁻¹.equivV = φ.equivV.symm := Iso.symm_equivV φ

@[simp] theorem inv_equivE (φ : Γ.Aut) : φ⁻¹.equivE = φ.equivE.symm := Iso.symm_equivE φ

/-- Automorphisms act on vertices. -/
instance : MulAction Γ.Aut Γ.V where
  smul φ v := φ.equivV v
  one_smul v := congrArg (· v) one_equivV
  mul_smul φ ψ v := congrArg (· v) (mul_equivV φ ψ)

/-- Automorphisms act on darts. -/
instance : MulAction Γ.Aut Γ.E where
  smul φ e := φ.equivE e
  one_smul e := congrArg (· e) one_equivE
  mul_smul φ ψ e := congrArg (· e) (mul_equivE φ ψ)

theorem smul_vertex_def (φ : Γ.Aut) (v : Γ.V) : φ • v = φ.equivV v := (rfl)

theorem smul_dart_def (φ : Γ.Aut) (e : Γ.E) : φ • e = φ.equivE e := (rfl)

@[simp] theorem src_smul (φ : Γ.Aut) (e : Γ.E) : Γ.src (φ • e) = φ • Γ.src e :=
  φ.map_src e

@[simp] theorem rev_smul (φ : Γ.Aut) (e : Γ.E) : Γ.rev (φ • e) = φ • Γ.rev e :=
  (φ.map_rev e).symm

@[simp] theorem tgt_smul (φ : Γ.Aut) (e : Γ.E) : Γ.tgt (φ • e) = φ • Γ.tgt e := by
  rw [tgt, rev_smul, src_smul, src_rev]

/-- Automorphisms act on geometric edges, through the induced bijection of geometric edges. -/
instance : MulAction Γ.Aut Γ.GeomEdge where
  smul φ := φ.geomEdgeEquiv
  one_smul x := congrArg (· x) (Iso.geomEdgeEquiv_refl Γ)
  mul_smul φ ψ x := congrArg (· x) (Iso.geomEdgeEquiv_trans ψ φ)

theorem smul_geomEdge_def (φ : Γ.Aut) (x : Γ.GeomEdge) : φ • x = φ.geomEdgeEquiv x := (rfl)

@[simp] theorem smul_toGeomEdge (φ : Γ.Aut) (e : Γ.E) :
    φ • Γ.toGeomEdge e = Γ.toGeomEdge (φ • e) :=
  Iso.geomEdgeEquiv_toGeomEdge φ e

/-- A morphism of Serre graphs invariant under an automorphism forces that automorphism to map no
dart to its reverse. -/
theorem smul_ne_rev_of_comp_toHom_eq {Δ : SerreGraph} (f : Γ.Hom Δ) (φ : Γ.Aut)
    (h : Hom.comp f φ.toHom = f) (e : Γ.E) : φ • e ≠ Γ.rev e := by
  intro he
  have h₁ : f.mapE (φ • e) = f.mapE e := by
    simpa [smul_dart_def] using congrArg (fun k : Γ.Hom Δ => k.mapE e) h
  rw [he, f.map_rev] at h₁
  exact Δ.rev_ne _ h₁

/-! ### Translates of paths -/

/-- The translate of a path by an automorphism: the path through the translates of its darts. -/
def smulPath (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) : Γ.Path (φ • a) (φ • b) :=
  φ.toHom.toPrefunctor.mapPath p

/-- The translate of a path is its image under the graph morphism underlying the automorphism. -/
theorem smulPath_def (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    φ.smulPath p = φ.toHom.toPrefunctor.mapPath p := (rfl)

/-- The translate of the empty path is empty. -/
@[simp] theorem smulPath_nil (φ : Γ.Aut) (a : Γ.V) :
    φ.smulPath (Quiver.Path.nil : Γ.Path a a) = Quiver.Path.nil := (rfl)

/-- The translate of a path extended by a dart is the translate extended by the translated
dart. -/
@[simp] theorem smulPath_cons (φ : Γ.Aut) {a b c : Γ.V} (p : Γ.Path a b) (e : Quiver.Hom b c) :
    φ.smulPath (p.cons e) =
      (φ.smulPath p).cons ⟨φ • e.1, by rw [src_smul, e.2.1], by rw [tgt_smul, e.2.2]⟩ :=
  (rfl)

/-- The translate of a one-dart path is the one-dart path through the translated dart. -/
@[simp] theorem smulPath_toPath (φ : Γ.Aut) {a b : Γ.V} (e : Quiver.Hom a b) :
    φ.smulPath e.toPath =
      Quiver.Hom.toPath (⟨φ • e.1, by rw [src_smul, e.2.1], by rw [tgt_smul, e.2.2]⟩ :
        Quiver.Hom (φ • a) (φ • b)) :=
  (rfl)

/-- The translate of a concatenation is the concatenation of the translates. -/
@[simp] theorem smulPath_comp (φ : Γ.Aut) {a b c : Γ.V} (p : Γ.Path a b) (q : Γ.Path b c) :
    φ.smulPath (p.comp q) = (φ.smulPath p).comp (φ.smulPath q) :=
  Prefunctor.mapPath_comp _ p q

/-- The translate of a reversed path is the reverse of the translate. -/
@[simp] theorem smulPath_reverse (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    φ.smulPath p.reverse = (φ.smulPath p).reverse :=
  Prefunctor.mapPath_reverse _ p

/-- The translate of a path passes through the translates of its vertices. -/
@[simp] theorem vertices_smulPath (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    (φ.smulPath p).vertices = p.vertices.map (φ • ·) :=
  Prefunctor.vertices_mapPath _ p

/-- The identity automorphism translates every path to itself. -/
@[simp] theorem one_smulPath {a b : Γ.V} (p : Γ.Path a b) : (1 : Γ.Aut).smulPath p = p :=
  Prefunctor.mapPath_id p

/-- Translating by a product of automorphisms is translating by each factor in turn. -/
theorem mul_smulPath (φ ψ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    (φ * ψ).smulPath p = φ.smulPath (ψ.smulPath p) :=
  Prefunctor.mapPath_comp_apply ψ.toHom.toPrefunctor φ.toHom.toPrefunctor p

/-- The translate of a path traverses the translates of its darts. -/
@[simp] theorem darts_smulPath (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    Path.darts Γ (φ.smulPath p) = (Path.darts Γ p).map (φ • ·) :=
  Hom.darts_mapPath Γ φ.toHom p

/-- The translate of a path is reduced exactly when the path is. -/
@[simp] theorem isReduced_smulPath (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    Path.IsReduced Γ (φ.smulPath p) ↔ Path.IsReduced Γ p :=
  Hom.isReduced_mapPath_iff Γ φ.toHom φ.toHom_mapE_injective p

/-- The translate of a path has the same length as the path. -/
@[simp] theorem length_smulPath (φ : Γ.Aut) {a b : Γ.V} (p : Γ.Path a b) :
    (φ.smulPath p).length = p.length :=
  Prefunctor.length_mapPath φ.toHom.toPrefunctor p

/-- Automorphisms preserve distances. -/
@[simp] theorem dist_smul (φ : Γ.Aut) (a b : Γ.V) : Γ.dist (φ • a) (φ • b) = Γ.dist a b := by
  -- Each automorphism maps paths to paths of the same length, and so does its inverse.
  have key : ∀ (ψ : Γ.Aut) (a b : Γ.V), Γ.dist (ψ • a) (ψ • b) ≤ Γ.dist a b := by
    intro ψ a b
    rcases isEmpty_or_nonempty (Γ.Path a b) with hab | hab
    · have : IsEmpty (Γ.Path (ψ • a) (ψ • b)) := ⟨fun p =>
        hab.false ((ψ⁻¹.smulPath p).cast (inv_smul_smul ψ a) (inv_smul_smul ψ b))⟩
      rw [dist_of_isEmpty this, dist_of_isEmpty hab]
    · simpa only [smul_vertex_def, Iso.toHom_mapV] using ψ.toHom.dist_le hab
  refine (key φ a b).antisymm ?_
  simpa only [inv_smul_smul] using key φ⁻¹ (φ • a) (φ • b)

/-- The `n`-th power of an automorphism moves a vertex by at most `n` times as much as the
automorphism, provided that the vertex is joined to its image. -/
theorem dist_pow_smul_le (φ : Γ.Aut) {v : Γ.V} (h : Nonempty (Γ.Path v (φ • v))) (n : ℕ) :
    Γ.dist v (φ ^ n • v) ≤ n * Γ.dist v (φ • v) := by
  obtain ⟨p⟩ := h
  -- Follow a path from `v` to `φⁿ • v` by the translate of `p` under `φⁿ`.
  have key : ∀ n : ℕ, Nonempty (Γ.Path v (φ ^ n • v)) ∧
      Γ.dist v (φ ^ n • v) ≤ n * Γ.dist v (φ • v) := by
    intro n
    induction n with
    | zero => exact ⟨⟨(Quiver.Path.nil).cast rfl (by rw [pow_zero, one_smul])⟩, by simp⟩
    | succ n ih =>
      obtain ⟨⟨q⟩, hq⟩ := ih
      have htri := dist_triangle ⟨q⟩ ⟨(φ ^ n).smulPath p⟩
      rw [dist_smul] at htri
      rw [pow_succ, mul_smul, Nat.succ_mul]
      exact ⟨⟨q.comp ((φ ^ n).smulPath p)⟩, by omega⟩
  exact (key n).2

/-- The `n`-th power of an automorphism, for an integer `n`, moves a vertex by at most `|n|` times
as much as the automorphism, provided that the vertex is joined to its image. -/
theorem dist_zpow_smul_le (φ : Γ.Aut) {v : Γ.V} (h : Nonempty (Γ.Path v (φ • v))) (n : ℤ) :
    Γ.dist v (φ ^ n • v) ≤ n.natAbs * Γ.dist v (φ • v) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, Int.natAbs_natCast]
    exact φ.dist_pow_smul_le h k
  · rw [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← dist_smul (φ ^ k),
      smul_inv_smul, dist_comm]
    exact φ.dist_pow_smul_le h k

/-! ### Fixed points in acyclic graphs -/

/-- In an acyclic graph, an automorphism fixing two vertices fixes every dart of a reduced path
joining them. -/
theorem smul_eq_of_mem_darts (h : Γ.IsAcyclic) (φ : Γ.Aut) {a b : Γ.V} (ha : φ • a = a)
    (hb : φ • b = b) {p : Γ.Path a b} (hp : Path.IsReduced Γ p) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : φ • e = e := by
  -- The translate of `p`, transported to the original endpoints, is another reduced path.
  have hq : Path.IsReduced Γ ((φ.smulPath p).cast ha hb) := by
    rwa [Path.isReduced_cast, isReduced_smulPath]
  have hdarts : (Path.darts Γ p).map (φ • ·) = (Path.darts Γ p).map id := by
    rw [List.map_id, ← darts_smulPath, ← Path.darts_cast Γ ha hb, h.eq_of_isReduced hq hp]
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
