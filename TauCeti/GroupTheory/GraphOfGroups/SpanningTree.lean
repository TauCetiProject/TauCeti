/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Path
public import TauCeti.Combinatorics.Graph.Serre.Path.SpanningTree
public import TauCeti.Combinatorics.Quiver.Symmetric

/-!
# The fundamental group of a graph of groups via a spanning tree

Let `𝔸` be a graph of groups over a Serre graph `Γ`, let `v₀` be a vertex and let `T` be a
spanning tree of `Γ`, with tree paths `[a, b]_T`. The two models of the fundamental group of `𝔸`
agree: reading the letters of closed `𝔸`-paths at `v₀` is an isomorphism
`π₁(𝔸, v₀) ≃* π₁(𝔸, T)`. Its inverse sends `g ∈ A_v` to the class of `[v₀, v]_T g [v, v₀]_T` and
the generator of a dart `e` to the class of the loop `[v₀, src e]_T e [tgt e, v₀]_T`; these
classes generate `π₁(𝔸, v₀)`. More generally, reading the letters of an `𝔸`-path `p` from `a` to
`b` gives an element of `π₁(𝔸, T)`, which the inverse sends to the class of
`[v₀, a]_T p [b, v₀]_T`.

## Main definitions

* `TauCeti.GraphOfGroups.π₁Equiv`: the isomorphism `π₁(𝔸, v₀) ≃* π₁(𝔸, T)`.

## Main results

* `TauCeti.GraphOfGroups.π₁Equiv_symm_of`, `TauCeti.GraphOfGroups.π₁Equiv_symm_edge`: the
  inverse on the generators of `π₁(𝔸, T)`.
* `TauCeti.GraphOfGroups.π₁Equiv_symm_toπ₁Tree`: the inverse sends the element of `π₁(𝔸, T)`
  read off an `𝔸`-path `p` from `a` to `b` to the class of `[v₀, a]_T p [b, v₀]_T`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definitions 2.2–2.3 and Proposition 2.4(3).
* J.-P. Serre, *Trees*, Chapter I, §5.1.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

open SerreGraph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
  (T : Γ.SpanningTree)

/-! ### Basing `𝔸`-paths along the tree -/

/-- The tree path from `b` to `a`, as an `𝔸`-path, is the reverse of the tree path from `a`
to `b`. -/
private theorem mapPath_path_eq_reverse (a b : Γ.V) :
    (dartPrefunctor 𝔸).mapPath (T.path b a) =
      ((dartPrefunctor 𝔸).mapPath (T.path a b)).reverse := by
  rw [← Prefunctor.mapPath_reverse, T.reverse_path]

/-- The class in `π₁(𝔸, v₀)` of the loop `[v₀, a]_T p [b, v₀]_T`, for an `𝔸`-path `p` from `a`
to `b`. -/
private noncomputable def based {x y : 𝔸.LetterVertex} (p : 𝔸.Path x y) : π₁ 𝔸 v₀ :=
  π₁.mk ((((dartPrefunctor 𝔸).mapPath (T.path v₀ x.as)).comp p).comp
    ((dartPrefunctor 𝔸).mapPath (T.path y.as v₀)))

private theorem based_congr {x y : 𝔸.LetterVertex} {p q : 𝔸.Path x y} (h : p.Homotopic q) :
    based 𝔸 v₀ T p = based 𝔸 v₀ T q :=
  π₁.mk_eq_mk_iff.2 ((h.comp_left _).comp_right _)

private theorem based_nil (x : 𝔸.LetterVertex) :
    based 𝔸 v₀ T (Quiver.Path.nil : 𝔸.Path x x) = 1 := by
  rw [based, Quiver.Path.comp_nil, mapPath_path_eq_reverse 𝔸 T v₀ x.as, ← π₁.mk_nil,
    π₁.mk_eq_mk_iff]
  exact Path.Homotopic.comp_reverse _

private theorem based_comp {x y z : 𝔸.LetterVertex} (p : 𝔸.Path x y) (q : 𝔸.Path y z) :
    based 𝔸 v₀ T (p.comp q) = based 𝔸 v₀ T p * based 𝔸 v₀ T q := by
  rw [based, based, based, ← π₁.mk_comp, π₁.mk_eq_mk_iff, mapPath_path_eq_reverse 𝔸 T v₀ y.as]
  -- Cancel the tree path to `y` and its reverse in the middle.
  simpa only [Quiver.Path.comp_assoc] using (Path.Homotopic.comp_reverse_comp_comp
    (((dartPrefunctor 𝔸).mapPath (T.path v₀ x.as)).comp p)
    ((dartPrefunctor 𝔸).mapPath (T.path v₀ y.as))
    (q.comp ((dartPrefunctor 𝔸).mapPath (T.path z.as v₀)))).symm

private theorem based_reverse {x y : 𝔸.LetterVertex} (p : 𝔸.Path x y) :
    based 𝔸 v₀ T p.reverse = (based 𝔸 v₀ T p)⁻¹ := by
  simp [based, ← π₁.mk_reverse, ← Prefunctor.mapPath_reverse, Quiver.Path.comp_assoc]

private theorem based_ofVertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    based 𝔸 v₀ T (Path.ofVertex g) = π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ a)) g := by
  rw [based, π₁.vertexHom_apply, mapPath_path_eq_reverse 𝔸 T v₀ a]

private theorem based_ofDart (e : Γ.E) :
    based 𝔸 v₀ T (Path.ofDart (Γ.dart e)) = π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e) := by
  simp [based, SpanningTree.loop_def]

/-! ### The inverse of the reading map -/

/-- The defining relation of a dart holds for the based tree loops. -/
private theorem based_rel (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e) *
        π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ (Γ.tgt e))) (𝔸.ω e c) *
        (π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e))⁻¹ =
      π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ (Γ.src e))) (𝔸.α e c) := by
  rw [← based_ofDart, ← based_ofVertex, ← based_ofVertex, ← based_reverse, ← based_comp,
    ← based_comp]
  apply based_congr
  rw [Path.reverse_ofDart, Path.comp_ofVertex, Path.comp_ofDart, Path.ofDart_def,
    Path.ofVertex_def]
  exact ((Path.Homotopic.dart_ω e c _).cons _).trans (.dart_reverse _ _)

/-- The inverse of `π₁Equiv`, from the universal property of `π₁(𝔸, T)`. -/
private noncomputable def ofπ₁Tree : π₁Tree 𝔸 T.darts →* π₁ 𝔸 v₀ :=
  π₁Tree.lift (fun v => π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ v)))
    (fun e => π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e))
    (fun e he => by simp [he]) (fun e => by simp)
    (based_rel 𝔸 v₀ T)

/-- The inverse sends the element of `π₁(𝔸, T)` read off an `𝔸`-path to the class of the path
based along the tree. -/
private theorem ofπ₁Tree_toπ₁Tree {x y : 𝔸.LetterVertex} (p : 𝔸.Path x y) :
    ofπ₁Tree 𝔸 v₀ T (Path.toπ₁Tree T.darts p) = based 𝔸 v₀ T p := by
  induction p with
  | nil => rw [Path.toπ₁Tree_nil, map_one, based_nil]
  | cons p l ih =>
    rw [Path.toπ₁Tree_cons, map_mul, ih, ← Quiver.Path.comp_toPath_eq_cons, based_comp]
    congr 1
    cases l with
    | vertex g => simp [ofπ₁Tree, ← Path.ofVertex_def, based_ofVertex]
    | dart e =>
      obtain ⟨e, rfl, rfl⟩ := e
      have hd : Letter.dart (𝔸 := 𝔸) ⟨e, rfl, rfl⟩ = Letter.dart (Γ.dart e) :=
        congrArg _ (Subtype.ext (Γ.dart_val e).symm)
      rw [hd, ← Path.ofDart_def, based_ofDart]
      simp [ofπ₁Tree]

/-- The dart generators of `π₁(𝔸, T)` along a tree path multiply to `1`. -/
@[simp] theorem π₁Tree.weight_path_edge_eq_one (a b : Γ.V) :
    (T.path a b).weight (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge (𝔸 := 𝔸) T.darts e.1) = 1 :=
  T.weight_path_eq_one (fun _ => π₁Tree.edge_eq_one) a b

private theorem toπ₁Tree_comp_ofπ₁Tree :
    (π₁.toπ₁Tree 𝔸 v₀ T.darts).comp (ofπ₁Tree 𝔸 v₀ T) = MonoidHom.id _ := by
  -- Tree paths read as `1` in `π₁(𝔸, T)`, so each generator is sent back to itself.
  refine π₁Tree.hom_ext (fun v => MonoidHom.ext fun g => ?_) fun e => ?_ <;>
    simp [ofπ₁Tree, SpanningTree.loop_def]

/-! ### The isomorphism -/

/-- **The two models of the fundamental group of a graph of groups agree.** For a spanning tree
`T` of `Γ`, reading the letters of closed `𝔸`-paths at `v₀` is an isomorphism
`π₁(𝔸, v₀) ≃* π₁(𝔸, T)`. -/
noncomputable def π₁Equiv : π₁ 𝔸 v₀ ≃* π₁Tree 𝔸 T.darts :=
  MonoidHom.toMulEquiv (π₁.toπ₁Tree 𝔸 v₀ T.darts) (ofπ₁Tree 𝔸 v₀ T)
    (MonoidHom.ext fun g => π₁.induction_on g fun p => by
      simpa [based] using ofπ₁Tree_toπ₁Tree 𝔸 v₀ T p)
    (toπ₁Tree_comp_ofπ₁Tree 𝔸 v₀ T)

theorem π₁Equiv_apply (g : π₁ 𝔸 v₀) : π₁Equiv 𝔸 v₀ T g = π₁.toπ₁Tree 𝔸 v₀ T.darts g :=
  (rfl)

@[simp] theorem π₁Equiv_mk (p : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁Equiv 𝔸 v₀ T (π₁.mk p) = p.toπ₁Tree T.darts := by
  rw [π₁Equiv_apply, π₁.toπ₁Tree_mk]

/-- The inverse of `π₁Equiv` sends `g ∈ A_v` to the class of `[v₀, v]_T g [v, v₀]_T`. -/
@[simp] theorem π₁Equiv_symm_of (v : Γ.V) (g : 𝔸.vertexGroup v) :
    (π₁Equiv 𝔸 v₀ T).symm (π₁Tree.of T.darts v g) =
      π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ v)) g :=
  π₁Tree.lift_of ..

/-- The inverse of `π₁Equiv` sends the generator of a dart `e` to the class of the loop
`[v₀, src e]_T e [tgt e, v₀]_T`. -/
@[simp] theorem π₁Equiv_symm_edge (e : Γ.E) :
    (π₁Equiv 𝔸 v₀ T).symm (π₁Tree.edge T.darts e) = π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e) :=
  π₁Tree.lift_edge ..

/-- `π₁Equiv` sends the class of `[v₀, v]_T g [v, v₀]_T` to `g ∈ A_v`. -/
@[simp] theorem π₁Equiv_vertexHom_mapPath_path (v : Γ.V) (g : 𝔸.vertexGroup v) :
    π₁Equiv 𝔸 v₀ T (π₁.vertexHom ((dartPrefunctor 𝔸).mapPath (T.path v₀ v)) g) =
      π₁Tree.of T.darts v g := by
  rw [← π₁Equiv_symm_of, MulEquiv.apply_symm_apply]

/-- `π₁Equiv` sends the class of the loop `[v₀, src e]_T e [tgt e, v₀]_T` to the generator of
the dart `e`. -/
@[simp] theorem π₁Equiv_ofPathGroup_loop (e : Γ.E) :
    π₁Equiv 𝔸 v₀ T (π₁.ofPathGroup 𝔸 v₀ (T.loop v₀ e)) = π₁Tree.edge T.darts e := by
  rw [← π₁Equiv_symm_edge, MulEquiv.apply_symm_apply]

/-- The inverse of `π₁Equiv` sends the element of `π₁(𝔸, T)` read off an `𝔸`-path `p` from `a`
to `b` to the class of the loop `[v₀, a]_T p [b, v₀]_T`. -/
@[simp] theorem π₁Equiv_symm_toπ₁Tree {a b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (π₁Equiv 𝔸 v₀ T).symm (p.toπ₁Tree T.darts) =
      π₁.mk ((((dartPrefunctor 𝔸).mapPath (T.path v₀ a)).comp p).comp
        ((dartPrefunctor 𝔸).mapPath (T.path b v₀))) :=
  ofπ₁Tree_toπ₁Tree 𝔸 v₀ T p

end TauCeti.GraphOfGroups
