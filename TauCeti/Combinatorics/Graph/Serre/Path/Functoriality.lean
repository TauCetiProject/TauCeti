/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Core
public import TauCeti.Combinatorics.Graph.Serre.Path.SpanningTree
public import TauCeti.Combinatorics.Quiver.Prefunctor
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Functoriality of the reduced path group

A morphism of Serre graphs `f : Γ.Hom Δ` sends closed paths at `v` to closed paths at
`f.mapV v`, and backtrack-homotopic paths to backtrack-homotopic paths. It therefore induces a
homomorphism `PathGroup.map f` of reduced path groups, functorially in `f`. A morphism injective
on darts sends reduced paths to reduced paths, so the induced homomorphism is injective; in
particular the reduced path group of a subgraph embeds in that of the ambient graph, with image
the reduced loops all of whose darts lie in the subgraph. Every reduced loop at `v` comes from the
based core at `v`, and lies in a finite connected based subgraph.

A path `p` from `v` to `w` gives the change of base vertex `PathGroup.mulEquivOfPath p`,
`g ↦ p⁻¹ g p`, which is natural in the graph.

For spanning trees `T` of `Γ` and `T'` of `Δ` such that `f.mapE` carries the darts of `T` into
`T'`, the induced homomorphism sends the tree loop of a dart `e` to the tree loop of `f.mapE e`;
in particular the inclusion of a subgraph containing a spanning tree sends the tree loops of the
restricted tree to the tree loops of the tree. Changing the base vertex along a tree path sends
tree loops to tree loops.

## Main definitions

* `TauCeti.SerreGraph.PathGroup.map`: the homomorphism of reduced path groups induced by a
  morphism of Serre graphs.
* `TauCeti.SerreGraph.PathGroup.mulEquivOfPath`: the change of base vertex along a path.

## Main results

* `TauCeti.SerreGraph.PathGroup.map_id`, `TauCeti.SerreGraph.PathGroup.map_comp`: functoriality.
* `TauCeti.SerreGraph.PathGroup.map_injective`: a morphism injective on darts induces an
  injective homomorphism.
* `TauCeti.SerreGraph.PathGroup.mem_range_map_restrictInclusion_iff`: the image of the reduced
  path group of a subgraph.
* `TauCeti.SerreGraph.PathGroup.exists_finite_connected_mem_range_map`: every reduced loop lies in
  a finite connected based subgraph.
* `TauCeti.SerreGraph.PathGroup.map_mulEquivOfPath`: induced homomorphisms commute with the
  change of base vertex.
* `TauCeti.SerreGraph.SpanningTree.map_loop`: induced homomorphisms send tree loops to tree
  loops.

## References

* A. Hatcher, *Algebraic Topology*, §1.1 (induced homomorphisms; change of basepoint,
  Proposition 1.5) and §1.A, Proposition 1A.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §3,
  Definition 3.5 and Lemma 3.7 (core graphs), §4, Lemma 4.1, and §6, Lemma 6.1.
* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
-/

public section

namespace TauCeti.SerreGraph

universe u w u' w' u'' w''

variable {Γ : SerreGraph.{u, w}} {Δ : SerreGraph.{u', w'}} {Θ : SerreGraph.{u'', w''}}

noncomputable section

namespace PathGroup

/-! ### The induced homomorphism -/

/-- The homomorphism of reduced path groups induced by a morphism of Serre graphs: the class of
a closed path at `v` is sent to the class of its image, a closed path at `f.mapV v`. The base
vertex `w` of the target is a parameter equal to `f.mapV v`, so that identities and composites of
morphisms can be compared without transporting along equalities of vertices. -/
def map (f : Γ.Hom Δ) {v : Γ.V} {w : Δ.V} (h : f.mapV v = w) :
    PathGroup Γ v →* PathGroup Δ w where
  toFun g := ofPath ((f.toPrefunctor.mapPath g.toPath).cast
    ((f.toPrefunctor_obj v).trans h) ((f.toPrefunctor_obj v).trans h))
  map_one' := by
    -- Substitute `w` by the endpoint of the image path, so that the transport disappears.
    have h' : f.toPrefunctor.obj v = w := h
    subst h'
    rw [toPath_one, Prefunctor.mapPath_nil, Quiver.Path.cast_rfl_rfl, ofPath_nil]
  map_mul' a b := by
    have h' : f.toPrefunctor.obj v = w := h
    subst h'
    rw [← ofPath_comp, ofPath_eq_iff_homotopic, toPath_mul, Quiver.Path.cast_rfl_rfl,
      Quiver.Path.cast_rfl_rfl, Quiver.Path.cast_rfl_rfl, ← Prefunctor.mapPath_comp]
    exact (Path.homotopic_reduce Γ _).symm.mapPath Γ f

theorem map_apply (f : Γ.Hom Δ) {v : Γ.V} {w : Δ.V} (h : f.mapV v = w) (g : PathGroup Γ v) :
    map f h g = ofPath ((f.toPrefunctor.mapPath g.toPath).cast
      ((f.toPrefunctor_obj v).trans h) ((f.toPrefunctor_obj v).trans h)) := (rfl)

/-- The induced homomorphism sends the class of a closed path to the class of its image. -/
@[simp] theorem map_ofPath (f : Γ.Hom Δ) {v : Γ.V} {w : Δ.V} (h : f.mapV v = w)
    (p : Γ.Path v v) :
    map f h (ofPath p) = ofPath ((f.toPrefunctor.mapPath p).cast
      ((f.toPrefunctor_obj v).trans h) ((f.toPrefunctor_obj v).trans h)) := by
  have h' : f.toPrefunctor.obj v = w := h
  subst h'
  rw [map_apply, ofPath_eq_iff_homotopic, toPath_ofPath, Quiver.Path.cast_rfl_rfl]
  exact (Path.homotopic_reduce Γ p).symm.mapPath Γ f

/-- The identity morphism induces the identity homomorphism. -/
@[simp] theorem map_id {v : Γ.V} (h : (Hom.id Γ).mapV v = v) :
    map (Hom.id Γ) h = MonoidHom.id (PathGroup Γ v) := by
  refine MonoidHom.ext fun g => ?_
  have key : ((Hom.id Γ).toPrefunctor.mapPath g.toPath).cast
      (((Hom.id Γ).toPrefunctor_obj v).trans h) (((Hom.id Γ).toPrefunctor_obj v).trans h) =
        g.toPath :=
    (Prefunctor.cast_mapPath_eq_of_eq (Hom.toPrefunctor_id Γ) g.toPath).trans
      (Prefunctor.mapPath_id g.toPath)
  rw [MonoidHom.id_apply, map_apply, key, ofPath_toPath]

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (g : Δ.Hom Θ) (f : Γ.Hom Δ) {v : Γ.V} {w : Δ.V} {x : Θ.V}
    (hf : f.mapV v = w) (hg : g.mapV w = x) :
    map (g.comp f) (by rw [Hom.comp_mapV, Function.comp_apply, hf, hg]) =
      (map g hg).comp (map f hf) := by
  have hf' : f.toPrefunctor.obj v = w := hf
  subst hf'
  have hg' : g.toPrefunctor.obj (f.toPrefunctor.obj v) = x := hg
  subst hg'
  refine MonoidHom.ext fun a => ?_
  have key (hc : (g.comp f).toPrefunctor.obj v = g.toPrefunctor.obj (f.toPrefunctor.obj v)) :
      ((g.comp f).toPrefunctor.mapPath a.toPath).cast hc hc =
        g.toPrefunctor.mapPath (f.toPrefunctor.mapPath a.toPath) :=
    (Prefunctor.cast_mapPath_eq_of_eq (Hom.toPrefunctor_comp Γ g f) a.toPath).trans
      (Prefunctor.mapPath_comp_apply _ _ _)
  apply ext
  rw [MonoidHom.comp_apply, map_apply, map_apply, map_apply, toPath_ofPath, toPath_ofPath,
    toPath_ofPath, Quiver.Path.cast_rfl_rfl, Quiver.Path.cast_rfl_rfl,
    Path.reduce_mapPath_reduce]
  exact congrArg (Path.reduce Θ) (key _)

/-- Applying two induced homomorphisms in succession applies the homomorphism induced by the
composite. -/
@[simp] theorem map_map (g : Δ.Hom Θ) (f : Γ.Hom Δ) {v : Γ.V} {w : Δ.V} {x : Θ.V}
    (hf : f.mapV v = w) (hg : g.mapV w = x) (a : PathGroup Γ v) :
    map g hg (map f hf a) =
      map (g.comp f) (by rw [Hom.comp_mapV, Function.comp_apply, hf, hg]) a := by
  rw [map_comp g f hf hg, MonoidHom.comp_apply]

/-! ### Morphisms injective on darts -/

/-- A morphism injective on darts sends a reduced closed path to its image, which is again
reduced. -/
theorem toPath_map_of_injective (f : Γ.Hom Δ) (hf : Function.Injective f.mapE) {v : Γ.V}
    {w : Δ.V} (h : f.mapV v = w) (g : PathGroup Γ v) :
    (map f h g).toPath = (f.toPrefunctor.mapPath g.toPath).cast
      ((f.toPrefunctor_obj v).trans h) ((f.toPrefunctor_obj v).trans h) := by
  have h' : f.toPrefunctor.obj v = w := h
  subst h'
  rw [map_apply, toPath_ofPath, Quiver.Path.cast_rfl_rfl]
  exact Path.reduce_eq_self_of_isReduced Δ _ ((f.isReduced_mapPath_iff Γ hf _).mpr g.isReduced)

/-- A morphism of Serre graphs injective on darts induces an injective homomorphism of reduced
path groups. -/
theorem map_injective (f : Γ.Hom Δ) (hf : Function.Injective f.mapE) {v : Γ.V} {w : Δ.V}
    (h : f.mapV v = w) : Function.Injective (map f h) := by
  have h' : f.toPrefunctor.obj v = w := h
  subst h'
  refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
  have hlen := congrArg Quiver.Path.length (congrArg toPath hg)
  rw [toPath_map_of_injective f hf, Quiver.Path.cast_rfl_rfl, Prefunctor.length_mapPath,
    toPath_one, Quiver.Path.length_nil] at hlen
  exact ext ((Quiver.Path.eq_nil_of_length_zero _ hlen).trans toPath_one.symm)

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S) {v w : Γ.V}
  (h : (Γ.restrictInclusion S hS).mapV v = w)

/-- The reduced path group of a subgraph embeds in the reduced path group of the ambient
graph. -/
theorem map_restrictInclusion_injective :
    Function.Injective (map (Γ.restrictInclusion S hS) h) :=
  map_injective _ Subtype.val_injective _

/-- The image of the reduced path group of a subgraph consists of the reduced loops all of
whose darts lie in the subgraph. -/
theorem mem_range_map_restrictInclusion_iff (g : PathGroup Γ w) :
    g ∈ (map (Γ.restrictInclusion S hS) h).range ↔ ∀ e ∈ Path.darts Γ g.toPath, e ∈ S := by
  have h' : v = w := (Γ.restrictInclusion_mapV S hS v).symm.trans h
  subst h'
  constructor
  · rintro ⟨a, rfl⟩ e he
    rw [toPath_map_of_injective (Γ.restrictInclusion S hS) Subtype.val_injective,
      Path.darts_cast] at he
    exact Γ.mem_of_mem_darts_mapPath S hS a.toPath he
  · intro hg
    obtain ⟨q, hq⟩ := Γ.exists_restrict_path S hS g.toPath hg
    have hv := ((Γ.restrictInclusion S hS).toPrefunctor_obj v).trans h
    have hc := (Quiver.Path.cast_eq_iff_heq hv hv _ _).mpr (heq_of_eq hq)
    exact ⟨ofPath q, (map_ofPath _ h q).trans ((congrArg ofPath hc).trans (ofPath_toPath g))⟩

end Restrict

/-- Every reduced loop at the base vertex comes from a reduced loop of the based core. -/
theorem mem_range_map_coreInclusion {v : Γ.V} (g : PathGroup Γ v) :
    g ∈ (map (Γ.coreInclusion v)
      ((Γ.subgraphInclusion_mapV _ _ _ _ (Γ.coreBase v)).trans (Γ.coreBase_val v))).range := by
  obtain ⟨q, hq⟩ := Γ.exists_core_loop v g.toPath g.isReduced
  have h := (Γ.subgraphInclusion_mapV _ _ _ _ (Γ.coreBase v)).trans (Γ.coreBase_val v)
  have hv := ((Γ.coreInclusion v).toPrefunctor_obj (Γ.coreBase v)).trans h
  have hc := (Quiver.Path.cast_eq_iff_heq hv hv _ _).mpr (heq_of_eq hq)
  exact ⟨ofPath q, (map_ofPath _ h q).trans ((congrArg ofPath hc).trans (ofPath_toPath g))⟩

/-- Every reduced loop lies in a finite connected based subgraph: there are a finite connected
Serre graph `Δ`, a morphism `f` from `Δ` to `Γ` injective on vertices and on darts, and a vertex
of `Δ` over the base vertex, such that the loop is in the image of the induced homomorphism. -/
theorem exists_finite_connected_mem_range_map {v : Γ.V} (g : PathGroup Γ v) :
    ∃ (Δ : SerreGraph.{u, w}) (f : Δ.Hom Γ) (v' : Δ.V) (h : f.mapV v' = v),
      Finite Δ.V ∧ Finite Δ.E ∧ Δ.Connected ∧ Function.Injective f.mapV ∧
        Function.Injective f.mapE ∧ g ∈ (map f h).range := by
  -- The based core of the subgraph spanned by the darts of the loop and their reverses.
  let D : Set Γ.E := {e | e ∈ Path.darts Γ g.toPath} ∪ Γ.rev '' {e | e ∈ Path.darts Γ g.toPath}
  have hD : ∀ e ∈ D, Γ.rev e ∈ D := by
    rintro e (he | ⟨d, hd, rfl⟩)
    · exact Or.inr ⟨e, he, rfl⟩
    · exact Or.inl (by rwa [Γ.rev_rev])
  have : Finite (Γ.restrict D hD).E :=
    ((List.finite_toSet _).union ((List.finite_toSet _).image _)).to_subtype
  obtain ⟨g', hg'⟩ := (mem_range_map_restrictInclusion_iff D hD
    (Γ.restrictInclusion_mapV D hD v) g).mpr fun e he => Or.inl he
  obtain ⟨g'', hg''⟩ := mem_range_map_coreInclusion g'
  refine ⟨_, (Γ.restrictInclusion D hD).comp ((Γ.restrict D hD).coreInclusion v), _, by simp,
    inferInstance, inferInstance, ((Γ.restrict D hD).core_isCore v).connected, ?_, ?_, g'',
    (map_map _ _ _ _ g'').symm.trans ((congrArg _ hg'').trans hg')⟩
  · rw [Hom.comp_mapV]
    exact Function.injective_id.comp Subtype.val_injective
  · rw [Hom.comp_mapE]
    exact Subtype.val_injective.comp Subtype.val_injective

/-! ### Change of base vertex -/

/-- Conjugating by a path and then by its reverse returns the original closed path, up to
backtrack homotopy. -/
private theorem homotopic_conj_conj {v w : Γ.V} (p : Γ.Path v w) (a : Γ.Path v v) :
    Path.Homotopic Γ ((p.comp ((p.reverse.comp a).comp p)).comp p.reverse) a := by
  have h := (Path.Homotopic.comp_reverse Γ p).comp Γ
    ((Path.Homotopic.refl a).comp Γ (Path.Homotopic.comp_reverse Γ p))
  simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp, Quiver.Path.comp_nil] using h

/-- Conjugation by a path carries concatenation to concatenation, up to backtrack homotopy. -/
private theorem homotopic_conj_comp {v w : Γ.V} (p : Γ.Path v w) (a b : Γ.Path v v) :
    Path.Homotopic Γ ((p.reverse.comp (a.comp b)).comp p)
      (((p.reverse.comp a).comp p).comp ((p.reverse.comp b).comp p)) := by
  have h := (Path.Homotopic.refl (p.reverse.comp a)).comp Γ
    ((Path.Homotopic.comp_reverse Γ p).comp Γ (Path.Homotopic.refl (b.comp p)))
  simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] using h.symm

/-- A reduced representative between two paths can be replaced by any representative of its
class. -/
private theorem ofPath_comp_toPath_ofPath_comp {v w : Γ.V} (p : Γ.Path v w) (a : Γ.Path w w)
    (q : Γ.Path w v) :
    ofPath ((p.comp (ofPath a).toPath).comp q) = ofPath ((p.comp a).comp q) := by
  rw [ofPath_eq_iff_homotopic, toPath_ofPath]
  exact ((Path.homotopic_reduce Γ a).symm.comp_left Γ p).comp_right Γ q

/-- The change of base vertex along a path `p` from `v` to `w`: the class of a closed path `a`
at `v` is sent to the class of `p⁻¹ a p`, a closed path at `w`. -/
def mulEquivOfPath {v w : Γ.V} (p : Γ.Path v w) : PathGroup Γ v ≃* PathGroup Γ w where
  toFun g := ofPath ((p.reverse.comp g.toPath).comp p)
  invFun g := ofPath ((p.comp g.toPath).comp p.reverse)
  left_inv g := by
    beta_reduce
    rw [ofPath_comp_toPath_ofPath_comp]
    exact ((ofPath_eq_iff_homotopic _ _).mpr (homotopic_conj_conj p g.toPath)).trans
      (ofPath_toPath g)
  right_inv g := by
    beta_reduce
    rw [ofPath_comp_toPath_ofPath_comp]
    refine ((ofPath_eq_iff_homotopic _ _).mpr ?_).trans (ofPath_toPath g)
    simpa only [Quiver.Path.reverse_reverse] using homotopic_conj_conj p.reverse g.toPath
  map_mul' a b := by
    have hab : a * b = ofPath (a.toPath.comp b.toPath) := by
      rw [ofPath_comp, ofPath_toPath, ofPath_toPath]
    rw [hab, ofPath_comp_toPath_ofPath_comp, ← ofPath_comp]
    exact (ofPath_eq_iff_homotopic _ _).mpr (homotopic_conj_comp p a.toPath b.toPath)

theorem mulEquivOfPath_apply {v w : Γ.V} (p : Γ.Path v w) (g : PathGroup Γ v) :
    mulEquivOfPath p g = ofPath ((p.reverse.comp g.toPath).comp p) := (rfl)

/-- The change of base vertex can be computed on any closed path representing a class. -/
@[simp] theorem mulEquivOfPath_ofPath {v w : Γ.V} (p : Γ.Path v w) (a : Γ.Path v v) :
    mulEquivOfPath p (ofPath a) = ofPath ((p.reverse.comp a).comp p) := by
  rw [mulEquivOfPath_apply, ofPath_comp_toPath_ofPath_comp]

/-- The change of base vertex along `p` sends the class of `a` to the class of `b` exactly when
`a p` and `p b` are backtrack homotopic. -/
theorem mulEquivOfPath_ofPath_eq_iff {v w : Γ.V} (p : Γ.Path v w) (a : Γ.Path v v)
    (b : Γ.Path w w) :
    mulEquivOfPath p (ofPath a) = ofPath b ↔ Path.Homotopic Γ (a.comp p) (p.comp b) := by
  rw [mulEquivOfPath_ofPath, ofPath_eq_iff_homotopic]
  constructor
  · intro h
    have h₁ := ((Path.Homotopic.comp_reverse Γ p).comp_right Γ (a.comp p)).symm
    have h₂ := h.comp_left Γ p
    simp only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] at h₁ h₂
    exact h₁.trans h₂
  · intro h
    have h₁ := h.comp_left Γ p.reverse
    have h₂ := (Path.Homotopic.reverse_comp Γ p).comp_right Γ b
    simp only [← Quiver.Path.comp_assoc, Quiver.Path.nil_comp] at h₁ h₂
    exact h₁.trans h₂

/-- The inverse of the change of base vertex along a path is the change of base vertex along the
reversed path. -/
@[simp] theorem mulEquivOfPath_symm {v w : Γ.V} (p : Γ.Path v w) :
    (mulEquivOfPath p).symm = mulEquivOfPath p.reverse := by
  refine MulEquiv.ext fun g => ?_
  rw [mulEquivOfPath_apply, Quiver.Path.reverse_reverse]
  rfl

/-- Backtrack-homotopic paths give the same change of base vertex. -/
theorem mulEquivOfPath_eq_of_homotopic {v w : Γ.V} {p q : Γ.Path v w}
    (h : Path.Homotopic Γ p q) : mulEquivOfPath p = mulEquivOfPath q := by
  refine MulEquiv.ext fun g => ?_
  rw [mulEquivOfPath_apply, mulEquivOfPath_apply, ofPath_eq_iff_homotopic]
  exact ((h.reverse Γ).comp_right Γ g.toPath).comp Γ h

/-- The change of base vertex along the empty path is the identity. -/
@[simp] theorem mulEquivOfPath_nil (v : Γ.V) :
    mulEquivOfPath (Quiver.Path.nil : Γ.Path v v) = MulEquiv.refl (PathGroup Γ v) := by
  refine MulEquiv.ext fun g => ?_
  simp [mulEquivOfPath_apply]

/-- The change of base vertex along a concatenation is the composite of the changes of base
vertex. -/
theorem mulEquivOfPath_comp {v w x : Γ.V} (p : Γ.Path v w) (q : Γ.Path w x) :
    mulEquivOfPath (p.comp q) = (mulEquivOfPath p).trans (mulEquivOfPath q) := by
  refine MulEquiv.ext fun g => ?_
  rw [MulEquiv.trans_apply, mulEquivOfPath_apply p, mulEquivOfPath_ofPath, mulEquivOfPath_apply,
    Quiver.Path.reverse_comp]
  simp only [Quiver.Path.comp_assoc]

/-- The change of base vertex along a closed path is conjugation by the inverse of its class. -/
theorem mulEquivOfPath_eq_conj {v : Γ.V} (p : Γ.Path v v) :
    mulEquivOfPath p = MulAut.conj (ofPath p)⁻¹ := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.conj_apply, inv_inv, ← ofPath_reverse, ← ofPath_toPath g, mulEquivOfPath_ofPath,
    ofPath_comp, ofPath_comp]

/-- Induced homomorphisms commute with the change of base vertex. -/
theorem map_mulEquivOfPath (f : Γ.Hom Δ) {v w : Γ.V} {v' w' : Δ.V} (hv : f.mapV v = v')
    (hw : f.mapV w = w') (p : Γ.Path v w) (g : PathGroup Γ v) :
    map f hw (mulEquivOfPath p g) =
      mulEquivOfPath ((f.toPrefunctor.mapPath p).cast
        ((f.toPrefunctor_obj v).trans hv) ((f.toPrefunctor_obj w).trans hw)) (map f hv g) := by
  have hv' : f.toPrefunctor.obj v = v' := hv
  subst hv'
  have hw' : f.toPrefunctor.obj w = w' := hw
  subst hw'
  induction g using induction_on with | h a
  have h := ((mulEquivOfPath_ofPath_eq_iff p a _).mp (mulEquivOfPath_ofPath p a)).mapPath Γ f
  rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp] at h
  rw [mulEquivOfPath_ofPath, map_ofPath, map_ofPath, Quiver.Path.cast_rfl_rfl,
    Quiver.Path.cast_rfl_rfl, Quiver.Path.cast_rfl_rfl]
  exact ((mulEquivOfPath_ofPath_eq_iff _ _ _).mpr h).symm

end PathGroup

/-! ### Spanning trees -/

namespace SpanningTree

variable (T : Γ.SpanningTree) (v : Γ.V)

/-- Changing the base vertex along a tree path carries based classes to based classes. -/
@[simp] theorem mulEquivOfPath_path_basedPath (w : Γ.V) {a b : Γ.V} (p : Γ.Path a b) :
    PathGroup.mulEquivOfPath (T.path v w) (T.basedPath v p) = T.basedPath w p := by
  rw [basedPath_def, basedPath_def, PathGroup.mulEquivOfPath_ofPath_eq_iff]
  have h₁ := (T.homotopic_path_comp_path b v w).comp_left Γ ((T.path v a).comp p)
  have h₂ := (((T.homotopic_path_comp_path v w a).symm.comp_right Γ p).comp_right Γ
    (T.path b w))
  simpa only [Quiver.Path.comp_assoc] using h₁.trans h₂

/-- Changing the base vertex along a tree path carries tree loops to tree loops. -/
@[simp] theorem mulEquivOfPath_path_loop (w : Γ.V) (e : Γ.E) :
    PathGroup.mulEquivOfPath (T.path v w) (T.loop v e) = T.loop w e := by
  simpa using T.mulEquivOfPath_path_basedPath v w (Γ.dart e).toPath

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'` sends
based classes relative to `T` to based classes relative to `T'`. -/
theorem map_basedPath (f : Γ.Hom Δ) (T' : Δ.SpanningTree)
    (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts) {w : Δ.V} (h : f.mapV v = w) {a b : Γ.V}
    (p : Γ.Path a b) :
    PathGroup.map f h (T.basedPath v p) = T'.basedPath w (f.toPrefunctor.mapPath p) := by
  have h' : f.toPrefunctor.obj v = w := h
  subst h'
  rw [basedPath_def, basedPath_def, PathGroup.map_ofPath, Quiver.Path.cast_rfl_rfl,
    PathGroup.ofPath_eq_iff_homotopic, Prefunctor.mapPath_comp, Prefunctor.mapPath_comp]
  exact ((T.homotopic_mapPath_path f T' hT v a).comp Δ (.refl _)).comp Δ
    (T.homotopic_mapPath_path f T' hT b v)

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'` sends the
tree loop of a dart to the tree loop of its image. -/
theorem map_loop (f : Γ.Hom Δ) (T' : Δ.SpanningTree)
    (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts) {w : Δ.V} (h : f.mapV v = w) (e : Γ.E) :
    PathGroup.map f h (T.loop v e) = T'.loop w (f.mapE e) := by
  have h' := T.map_basedPath v f T' hT h (Γ.dart e).toPath
  rwa [Prefunctor.mapPath_toPath, basedPath_toPath, basedPath_toPath, Hom.toPrefunctor_map_val,
    dart_val] at h'

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The inclusion of a subgraph containing a spanning tree sends the tree loops of the
restricted tree to the tree loops of the tree. -/
@[simp] theorem map_restrictInclusion_loop (hTS : T.darts ⊆ S) {w : Γ.V}
    (h : (Γ.restrictInclusion S hS).mapV v = w) (e : (Γ.restrict S hS).E) :
    PathGroup.map (Γ.restrictInclusion S hS) h ((T.restrict S hS hTS).loop v e) =
      T.loop w e.1 := by
  simpa using (T.restrict S hS hTS).map_loop v (Γ.restrictInclusion S hS) T
    (fun _ he => (T.mem_restrict_darts S hS hTS).mp he) h e

end Restrict

end SpanningTree

end

end TauCeti.SerreGraph
