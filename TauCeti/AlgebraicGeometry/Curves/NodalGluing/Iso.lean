/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Basic
public import TauCeti.Geometry.Manifold.Instances.Sigma
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Isomorphisms of nodal curves presented by flag-pair data

A nodal curve presented by flag-pair data `d : FlagPairData ι Flag X` is the quotient of the
disjoint union `Σ i, X i` of its normalization components by the flag pairs.  An isomorphism of
two such curves is given on the normalizations: it is a diffeomorphism of the disjoint unions of
the components which carries the two points of a flag pair exactly to the two points of a flag
pair.  For complex curves (`𝕜 = ℂ` and `n = ∞`) the diffeomorphism is a biholomorphism, so an
isomorphism consists of component biholomorphisms together with the compatible maps of the dual
graph.

This file defines these isomorphisms, extracts the combinatorial maps they induce, descends them
to the glued curves and assembles the automorphism group.

## Main definitions

* `NodalGluing.Iso I n d d'`: a `C^n` diffeomorphism `(Σ i, X i) ≃ₘ^n⟮I, I⟯ (Σ i, X' i)` such that
  two points are the two points of a flag pair of `d'` exactly when their preimages are the two
  points of a flag pair of `d`.
* `NodalGluing.Iso.branchEquiv`: the induced bijection of branches `Flag × Bool ≃ Flag' × Bool`,
  characterized by `flagPoint d' (e.branchEquiv p) = e (flagPoint d p)`.  It commutes with
  exchanging the two branches of a node (`branchEquiv_swap`), so it may interchange them.
* `NodalGluing.Iso.edgeEquiv`: the induced bijection of nodes `Flag ≃ Flag'`.
* `NodalGluing.Iso.vertexEquiv`: for connected components, the induced bijection of components
  `ι ≃ ι'`, compatible with the branches (`fst_flagPoint_branchEquiv`).
* `NodalGluing.Iso.gluedCurveHomeomorph`: the descended homeomorphism of glued curves.
* `NodalGluing.Aut I n d`: the automorphism group, with its actions on branches
  (`Aut.branchPerm`), nodes (`Aut.edgePerm`), components (`Aut.vertexPerm`) and the glued curve
  (`Aut.toGluedCurveHomeomorph`).

## Main results

* `NodalGluing.Iso.gluedCurveHomeomorph_mk`, `gluedCurveHomeomorph_nodeOfFlag`: descent commutes
  with the quotient maps and sends the node of `f` to the node of `e.edgeEquiv f`; in particular
  it preserves the node set (`image_gluedCurveHomeomorph_nodeSet`).
* `NodalGluing.Iso.gluedCurveHomeomorph_injective`: descent is faithful as soon as the points
  which are not flag points are dense in the normalization, as they are for curves.  So an
  isomorphism of normalizations is determined by the map of glued curves it induces.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699: a nodal Riemann surface is a surface with a set of
  unordered pairs of distinct points, and an isomorphism is a biholomorphism of the surfaces
  carrying the nodal pairs exactly to the nodal pairs.
* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II*, Chapter X, for the dual graph of a nodal curve and the action of automorphisms on it.
-/

public noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)]
  {ι'' Flag'' : Type*} {X'' : ι'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'} {d'' : FlagPairData ι'' Flag'' X''}

variable (I n) in
/-- **An isomorphism of nodal curves presented by flag-pair data.**  A `C^n` diffeomorphism of the
disjoint unions of the normalization components which carries the two points of a flag pair of
`d` exactly to the two points of a flag pair of `d'`.  Over `ℂ` with `n = ∞` this is a
biholomorphism of the normalizations matching the nodes. -/
structure Iso (d : FlagPairData ι Flag X) (d' : FlagPairData ι' Flag' X') where
  /-- The diffeomorphism of the normalizations. -/
  toDiffeomorph : (Σ i, X i) ≃ₘ^n⟮I, I⟯ (Σ i, X' i)
  /-- Two points are the two points of a flag pair of `d` exactly when their images are the two
  points of a flag pair of `d'`. -/
  flagRel_apply_iff' (x y : Σ i, X i) :
    flagRel d' (toDiffeomorph x) (toDiffeomorph y) ↔ flagRel d x y

namespace Iso

instance : EquivLike (Iso I n d d') (Σ i, X i) (Σ i, X' i) where
  coe e := e.toDiffeomorph
  inv e := e.toDiffeomorph.symm
  left_inv e := e.toDiffeomorph.symm_apply_apply
  right_inv e := e.toDiffeomorph.apply_symm_apply
  coe_injective' e e' h _ := by
    cases e
    cases e'
    congr 1
    exact Diffeomorph.ext (congrFun h)

/-- The underlying diffeomorphism of an isomorphism acts as the isomorphism. -/
@[simp] theorem coe_toDiffeomorph (e : Iso I n d d') : ⇑e.toDiffeomorph = e :=
  (rfl)

/-- An isomorphism built from a diffeomorphism acts as that diffeomorphism. -/
@[simp] theorem coe_mk (f : (Σ i, X i) ≃ₘ^n⟮I, I⟯ (Σ i, X' i))
    (hf : ∀ x y, flagRel d' (f x) (f y) ↔ flagRel d x y) : ⇑(⟨f, hf⟩ : Iso I n d d') = f :=
  (rfl)

/-- Two isomorphisms agreeing at every point of the normalization are equal. -/
@[ext] theorem ext {e e' : Iso I n d d'} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/-- An isomorphism carries the two points of a flag pair exactly to the two points of a flag
pair. -/
@[simp] theorem flagRel_apply_iff (e : Iso I n d d') (x y : Σ i, X i) :
    flagRel d' (e x) (e y) ↔ flagRel d x y :=
  e.flagRel_apply_iff' x y

/-- An isomorphism is continuous on the normalizations. -/
protected theorem continuous (e : Iso I n d d') : Continuous e :=
  e.toDiffeomorph.continuous

variable (I n d) in
/-- The identity isomorphism. -/
protected def refl : Iso I n d d where
  toDiffeomorph := Diffeomorph.refl I _ n
  flagRel_apply_iff' _ _ := Iff.rfl

/-- The identity isomorphism fixes every point. -/
@[simp] theorem refl_apply (x : Σ i, X i) : Iso.refl I n d x = x :=
  (rfl)

/-- The underlying diffeomorphism of the identity isomorphism is the identity. -/
@[simp] theorem refl_toDiffeomorph :
    (Iso.refl I n d).toDiffeomorph = Diffeomorph.refl I (Σ i, X i) n :=
  (rfl)

/-- The inverse isomorphism. -/
protected def symm (e : Iso I n d d') : Iso I n d' d where
  toDiffeomorph := e.toDiffeomorph.symm
  flagRel_apply_iff' x y := by
    conv_rhs => rw [← e.toDiffeomorph.apply_symm_apply x, ← e.toDiffeomorph.apply_symm_apply y]
    exact (e.flagRel_apply_iff' _ _).symm

/-- The inverse isomorphism undoes the isomorphism. -/
@[simp] theorem symm_apply_apply (e : Iso I n d d') (x : Σ i, X i) : e.symm (e x) = x :=
  e.toDiffeomorph.symm_apply_apply x

/-- The isomorphism undoes its inverse. -/
@[simp] theorem apply_symm_apply (e : Iso I n d d') (y : Σ i, X' i) : e (e.symm y) = y :=
  e.toDiffeomorph.apply_symm_apply y

/-- The inverse of the inverse is the original isomorphism. -/
@[simp] theorem symm_symm (e : Iso I n d d') : e.symm.symm = e :=
  ext fun _ ↦ rfl

/-- The underlying diffeomorphism of the inverse is the inverse diffeomorphism. -/
@[simp] theorem symm_toDiffeomorph (e : Iso I n d d') :
    e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  (rfl)

/-- The inverse of the identity isomorphism is the identity. -/
@[simp] theorem symm_refl : (Iso.refl I n d).symm = Iso.refl I n d :=
  ext fun _ ↦ rfl

/-- The inverse isomorphism sends `y` to `x` exactly when the isomorphism sends `x` to `y`. -/
theorem symm_apply_eq (e : Iso I n d d') {x : Σ i, X i} {y : Σ i, X' i} :
    e.symm y = x ↔ y = e x :=
  ⟨fun h ↦ by rw [← h, apply_symm_apply], fun h ↦ by rw [h, symm_apply_apply]⟩

/-- The isomorphism sends `x` to `y` exactly when the inverse sends `y` to `x`. -/
theorem eq_symm_apply (e : Iso I n d d') {x : Σ i, X i} {y : Σ i, X' i} :
    x = e.symm y ↔ e x = y :=
  eq_comm.trans <| e.symm_apply_eq.trans eq_comm

/-- The composite of two isomorphisms. -/
protected def trans (e : Iso I n d d') (e' : Iso I n d' d'') : Iso I n d d'' where
  toDiffeomorph := e.toDiffeomorph.trans e'.toDiffeomorph
  flagRel_apply_iff' x y := (e'.flagRel_apply_iff' _ _).trans (e.flagRel_apply_iff' x y)

/-- The composite acts by applying the first isomorphism, then the second. -/
@[simp] theorem trans_apply (e : Iso I n d d') (e' : Iso I n d' d'') (x : Σ i, X i) :
    e.trans e' x = e' (e x) :=
  (rfl)

/-- The underlying diffeomorphism of a composite is the composite of the diffeomorphisms. -/
@[simp] theorem trans_toDiffeomorph (e : Iso I n d d') (e' : Iso I n d' d'') :
    (e.trans e').toDiffeomorph = e.toDiffeomorph.trans e'.toDiffeomorph :=
  (rfl)

/-- The inverse of a composite is the composite of the inverses in the opposite order. -/
@[simp] theorem symm_trans (e : Iso I n d d') (e' : Iso I n d' d'') :
    (e.trans e').symm = e'.symm.trans e.symm :=
  ext fun _ ↦ rfl

/-- An isomorphism followed by its inverse is the identity. -/
@[simp] theorem self_trans_symm (e : Iso I n d d') : e.trans e.symm = Iso.refl I n d :=
  ext e.symm_apply_apply

/-- The inverse of an isomorphism followed by it is the identity. -/
@[simp] theorem symm_trans_self (e : Iso I n d d') : e.symm.trans e = Iso.refl I n d' :=
  ext e.apply_symm_apply

/-- Composing with the identity on the right does nothing. -/
@[simp] theorem trans_refl (e : Iso I n d d') : e.trans (Iso.refl I n d') = e :=
  ext fun _ ↦ rfl

/-- Composing with the identity on the left does nothing. -/
@[simp] theorem refl_trans (e : Iso I n d d') : (Iso.refl I n d).trans e = e :=
  ext fun _ ↦ rfl

/-- Composition of isomorphisms is associative. -/
theorem trans_assoc {ι₃ Flag₃ : Type*} {X₃ : ι₃ → Type*} [∀ i, TopologicalSpace (X₃ i)]
    [∀ i, ChartedSpace H (X₃ i)] {d₃ : FlagPairData ι₃ Flag₃ X₃}
    (e : Iso I n d d') (e' : Iso I n d' d'') (e'' : Iso I n d'' d₃) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  ext fun _ ↦ rfl

-- High priority, so that `simp` removes the isomorphism before `mem_flagPointSet` unfolds the
-- membership into an existential that no longer mentions `flagPointSet`.
/-- An isomorphism maps flag points exactly to flag points. -/
@[simp high] theorem apply_mem_flagPointSet_iff (e : Iso I n d d') (x : Σ i, X i) :
    e x ∈ flagPointSet d' ↔ x ∈ flagPointSet d := by
  rw [mem_flagPointSet_iff_exists_flagRel, mem_flagPointSet_iff_exists_flagRel]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, (e.flagRel_apply_iff _ _).mp (by rwa [apply_symm_apply])⟩
  · rintro ⟨y, hy⟩
    exact ⟨e y, (e.flagRel_apply_iff _ _).mpr hy⟩

/-- An isomorphism respects the equivalence relation generated by the flag pairs. -/
@[simp] theorem gluedRel_apply_iff (e : Iso I n d d') (x y : Σ i, X i) :
    gluedRel d' (e x) (e y) ↔ gluedRel d x y := by
  rw [gluedRel_def, gluedRel_def, EquivLike.apply_eq_iff_eq, e.flagRel_apply_iff]

/-! ### Branches, nodes and components -/

private theorem apply_flagPoint_mem_range (e : Iso I n d d') (p : Flag × Bool) :
    e (flagPoint d p) ∈ range (flagPoint d') := by
  rw [← flagPointSet_eq_range, e.apply_mem_flagPointSet_iff, flagPointSet_eq_range]
  exact mem_range_self p

/-- **The branch map.**  The bijection of branches induced by an isomorphism: the flag point
selected by `p` is carried to the flag point selected by `e.branchEquiv p`. -/
def branchEquiv (e : Iso I n d d') : Flag × Bool ≃ Flag' × Bool where
  toFun p := (Equiv.ofInjective _ (flagPoint_injective d')).symm
    ⟨e (flagPoint d p), e.apply_flagPoint_mem_range p⟩
  invFun q := (Equiv.ofInjective _ (flagPoint_injective d)).symm
    ⟨e.symm (flagPoint d' q), e.symm.apply_flagPoint_mem_range q⟩
  left_inv p := flagPoint_injective d <| by
    simp only [Equiv.apply_ofInjective_symm, symm_apply_apply]
  right_inv q := flagPoint_injective d' <| by
    simp only [Equiv.apply_ofInjective_symm, apply_symm_apply]

/-- The characteristic property of the branch map. -/
@[simp] theorem flagPoint_branchEquiv (e : Iso I n d d') (p : Flag × Bool) :
    flagPoint d' (e.branchEquiv p) = e (flagPoint d p) :=
  Equiv.apply_ofInjective_symm (flagPoint_injective d') _

/-- The branch map sends `p` to `q` exactly when the isomorphism sends the flag point of `p`
to the flag point of `q`. -/
theorem branchEquiv_apply_eq_iff (e : Iso I n d d') (p : Flag × Bool) (q : Flag' × Bool) :
    e.branchEquiv p = q ↔ e (flagPoint d p) = flagPoint d' q := by
  rw [← flagPoint_branchEquiv, (flagPoint_injective d').eq_iff]

/-- The identity isomorphism fixes every branch. -/
@[simp] theorem branchEquiv_refl : (Iso.refl I n d).branchEquiv = Equiv.refl _ :=
  Equiv.ext fun p ↦ by rw [branchEquiv_apply_eq_iff, refl_apply, Equiv.refl_apply]

/-- The branch map of the inverse is the inverse of the branch map. -/
@[simp] theorem branchEquiv_symm (e : Iso I n d d') : e.symm.branchEquiv = e.branchEquiv.symm :=
  Equiv.ext fun q ↦ (Equiv.eq_symm_apply _).mpr <| (e.branchEquiv_apply_eq_iff _ _).mpr <| by
    rw [flagPoint_branchEquiv, apply_symm_apply]

/-- The branch map of a composite is the composite of the branch maps. -/
@[simp] theorem branchEquiv_trans (e : Iso I n d d') (e' : Iso I n d' d'') :
    (e.trans e').branchEquiv = e.branchEquiv.trans e'.branchEquiv :=
  Equiv.ext fun p ↦ by
    rw [branchEquiv_apply_eq_iff, Equiv.trans_apply, flagPoint_branchEquiv,
      flagPoint_branchEquiv, trans_apply]

/-- **The branch map respects the nodes.**  The two branches of a node are carried to the two
branches of a node: exchanging the branches commutes with the branch map. -/
theorem branchEquiv_swap (e : Iso I n d d') (p : Flag × Bool) :
    e.branchEquiv (p.1, !p.2) = ((e.branchEquiv p).1, !(e.branchEquiv p).2) := by
  rw [← flagRel_flagPoint_iff d', flagPoint_branchEquiv, flagPoint_branchEquiv,
    e.flagRel_apply_iff, flagRel_flagPoint_iff]

private theorem fst_branchEquiv_eq (e : Iso I n d d') (f : Flag) (b c : Bool) :
    (e.branchEquiv (f, b)).1 = (e.branchEquiv (f, c)).1 := by
  have h := congrArg Prod.fst (e.branchEquiv_swap (f, false))
  cases b <;> cases c <;> simp_all

private theorem fst_symm_branchEquiv_fst (e : Iso I n d d') (f : Flag) :
    (e.symm.branchEquiv ((e.branchEquiv (f, false)).1, false)).1 = f := by
  rw [e.symm.fst_branchEquiv_eq _ false (e.branchEquiv (f, false)).2, Prod.mk.eta,
    branchEquiv_symm, Equiv.symm_apply_apply]

/-- **The node map.**  The bijection of nodes (flag pairs) induced by an isomorphism. -/
def edgeEquiv (e : Iso I n d d') : Flag ≃ Flag' where
  toFun f := (e.branchEquiv (f, false)).1
  invFun g := (e.symm.branchEquiv (g, false)).1
  left_inv f := e.fst_symm_branchEquiv_fst f
  right_inv g := by simpa only [symm_symm] using e.symm.fst_symm_branchEquiv_fst g

/-- The branch map lies over the node map. -/
@[simp] theorem fst_branchEquiv (e : Iso I n d d') (p : Flag × Bool) :
    (e.branchEquiv p).1 = e.edgeEquiv p.1 :=
  e.fst_branchEquiv_eq p.1 p.2 false

/-- The node map sends a node to the node of the image of either of its branches. -/
theorem edgeEquiv_apply (e : Iso I n d d') (f : Flag) (b : Bool) :
    e.edgeEquiv f = (e.branchEquiv (f, b)).1 :=
  (e.fst_branchEquiv (f, b)).symm

/-- The identity isomorphism fixes every node. -/
@[simp] theorem edgeEquiv_refl : (Iso.refl I n d).edgeEquiv = Equiv.refl _ :=
  Equiv.ext fun f ↦ by
    rw [edgeEquiv_apply _ f false, branchEquiv_refl, Equiv.refl_apply, Equiv.refl_apply]

/-- The node map of a composite is the composite of the node maps. -/
@[simp] theorem edgeEquiv_trans (e : Iso I n d d') (e' : Iso I n d' d'') :
    (e.trans e').edgeEquiv = e.edgeEquiv.trans e'.edgeEquiv :=
  Equiv.ext fun f ↦ by
    rw [edgeEquiv_apply _ f false, branchEquiv_trans, Equiv.trans_apply, fst_branchEquiv,
      fst_branchEquiv, Equiv.trans_apply]

/-- The node map of the inverse is the inverse of the node map. -/
@[simp] theorem edgeEquiv_symm (e : Iso I n d d') : e.symm.edgeEquiv = e.edgeEquiv.symm :=
  Equiv.ext fun g ↦ (Equiv.eq_symm_apply _).mpr <| by
    rw [← Equiv.trans_apply, ← edgeEquiv_trans, symm_trans_self, edgeEquiv_refl,
      Equiv.refl_apply]

section Vertex

/-- An isomorphism maps each connected component of the normalization into a single component. -/
theorem fst_apply_eq_fst_apply [∀ i, PreconnectedSpace (X i)] (e : Iso I n d d')
    {x y : Σ i, X i} (h : x.1 = y.1) : (e x).1 = (e y).1 := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  subst h
  have hconn : IsPreconnected (e '' range (Sigma.mk i)) := by
    rw [← image_univ]
    exact (isPreconnected_univ.image _ continuous_sigmaMk.continuousOn).image _
      e.continuous.continuousOn
  have hsub := hconn.subset_isClopen (isClopen_range_sigmaMk (i := (e ⟨i, a⟩).1))
    ⟨e ⟨i, a⟩, mem_image_of_mem _ (mem_range_self a), ⟨_, rfl⟩⟩
  obtain ⟨c, hc⟩ := hsub (mem_image_of_mem _ (mem_range_self b))
  rw [← hc]

variable [∀ i, ConnectedSpace (X i)] [∀ i, ConnectedSpace (X' i)]

/-- **The component map.**  For connected components, the bijection of components induced by an
isomorphism: the component `i` is carried onto the component `e.vertexEquiv i`. -/
def vertexEquiv (e : Iso I n d d') : ι ≃ ι' where
  toFun i := (e ⟨i, Classical.arbitrary (X i)⟩).1
  invFun j := (e.symm ⟨j, Classical.arbitrary (X' j)⟩).1
  left_inv i := by
    simp only
    rw [e.symm.fst_apply_eq_fst_apply (x := ⟨_, Classical.arbitrary _⟩)
      (y := e ⟨i, Classical.arbitrary (X i)⟩) rfl, symm_apply_apply]
  right_inv j := by
    simp only
    rw [e.fst_apply_eq_fst_apply (x := ⟨_, Classical.arbitrary _⟩)
      (y := e.symm ⟨j, Classical.arbitrary (X' j)⟩) rfl, apply_symm_apply]

/-- The characteristic property of the component map. -/
@[simp] theorem fst_apply (e : Iso I n d d') (x : Σ i, X i) : (e x).1 = e.vertexEquiv x.1 :=
  e.fst_apply_eq_fst_apply rfl

/-- **The graph maps are compatible.**  The component carrying the image of a branch is the image
of the component carrying that branch. -/
theorem fst_flagPoint_branchEquiv (e : Iso I n d d') (p : Flag × Bool) :
    (flagPoint d' (e.branchEquiv p)).1 = e.vertexEquiv (flagPoint d p).1 := by
  rw [flagPoint_branchEquiv, fst_apply]

/-- The component map sends `i` to `j` exactly when some point of the component `i` is sent
into the component `j`. -/
theorem vertexEquiv_apply_eq_iff (e : Iso I n d d') (i : ι) (j : ι') :
    e.vertexEquiv i = j ↔ ∃ x : X i, (e ⟨i, x⟩).1 = j :=
  ⟨fun h ↦ ⟨Classical.arbitrary _, h⟩, fun ⟨x, hx⟩ ↦ (e.fst_apply ⟨i, x⟩).symm.trans hx⟩

/-- The identity isomorphism fixes every component. -/
@[simp] theorem vertexEquiv_refl : (Iso.refl I n d).vertexEquiv = Equiv.refl _ :=
  Equiv.ext fun i ↦ by
    rw [vertexEquiv_apply_eq_iff]
    exact ⟨Classical.arbitrary _, rfl⟩

/-- The component map of a composite is the composite of the component maps. -/
@[simp] theorem vertexEquiv_trans [∀ i, ConnectedSpace (X'' i)] (e : Iso I n d d')
    (e' : Iso I n d' d'') : (e.trans e').vertexEquiv = e.vertexEquiv.trans e'.vertexEquiv :=
  Equiv.ext fun i ↦ by
    rw [vertexEquiv_apply_eq_iff]
    refine ⟨Classical.arbitrary _, ?_⟩
    rw [trans_apply, fst_apply, fst_apply, Equiv.trans_apply]

/-- The component map of the inverse is the inverse of the component map. -/
@[simp] theorem vertexEquiv_symm (e : Iso I n d d') : e.symm.vertexEquiv = e.vertexEquiv.symm :=
  Equiv.ext fun j ↦ (Equiv.eq_symm_apply _).mpr <| by
    have h₁ := e.symm.fst_apply ⟨j, Classical.arbitrary (X' j)⟩
    have h₂ := e.fst_apply (e.symm ⟨j, Classical.arbitrary (X' j)⟩)
    rw [apply_symm_apply] at h₂
    rw [← h₁, ← h₂]

end Vertex

/-! ### Descent to the glued curves -/

/-- **Descent.**  The homeomorphism of glued curves induced by an isomorphism of nodal curves. -/
def gluedCurveHomeomorph (e : Iso I n d d') : GluedCurve d ≃ₜ GluedCurve d' :=
  Homeomorph.Quotient.congr e.toDiffeomorph.toHomeomorph fun x y ↦ by
    rw [gluedRelSetoid_r, gluedRelSetoid_r, Diffeomorph.coe_toHomeomorph, coe_toDiffeomorph,
      e.gluedRel_apply_iff]

/-- The descended homeomorphism commutes with the quotient maps. -/
@[simp] theorem gluedCurveHomeomorph_mk (e : Iso I n d d') (x : Σ i, X i) :
    e.gluedCurveHomeomorph (Quotient.mk _ x) = Quotient.mk _ (e x) :=
  (rfl)

/-- The descended homeomorphism sends the node of `f` to the node of `e.edgeEquiv f`. -/
@[simp] theorem gluedCurveHomeomorph_nodeOfFlag (e : Iso I n d d') (f : Flag) :
    e.gluedCurveHomeomorph (nodeOfFlag d f) = nodeOfFlag d' (e.edgeEquiv f) := by
  have h := congrArg e.gluedCurveHomeomorph (mk_flagPoint d (f, false))
  rw [gluedCurveHomeomorph_mk, ← flagPoint_branchEquiv, mk_flagPoint, fst_branchEquiv] at h
  exact h.symm

-- High priority, so that `simp` removes the homeomorphism before `mem_nodeSet` unfolds the
-- membership into an existential.
/-- The descended homeomorphism maps nodes exactly to nodes. -/
@[simp high] theorem gluedCurveHomeomorph_mem_nodeSet_iff (e : Iso I n d d') (q : GluedCurve d) :
    e.gluedCurveHomeomorph q ∈ nodeSet d' ↔ q ∈ nodeSet d := by
  rw [nodeSet_eq_range_nodeOfFlag, nodeSet_eq_range_nodeOfFlag]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.edgeEquiv.symm g, e.gluedCurveHomeomorph.injective ?_⟩
    rw [gluedCurveHomeomorph_nodeOfFlag, Equiv.apply_symm_apply, hg]
  · rintro ⟨f, rfl⟩
    exact ⟨e.edgeEquiv f, (e.gluedCurveHomeomorph_nodeOfFlag f).symm⟩

/-- The descended homeomorphism maps the node set onto the node set. -/
theorem image_gluedCurveHomeomorph_nodeSet (e : Iso I n d d') :
    e.gluedCurveHomeomorph '' nodeSet d = nodeSet d' := by
  ext q
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (e.gluedCurveHomeomorph_mem_nodeSet_iff q).mpr hq
  · intro hq
    refine ⟨e.gluedCurveHomeomorph.symm q, ?_, e.gluedCurveHomeomorph.apply_symm_apply q⟩
    rwa [← e.gluedCurveHomeomorph_mem_nodeSet_iff, Homeomorph.apply_symm_apply]

/-- Descent sends the identity to the identity. -/
@[simp] theorem gluedCurveHomeomorph_refl :
    (Iso.refl I n d).gluedCurveHomeomorph = Homeomorph.refl _ :=
  Homeomorph.ext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

/-- Descent sends a composite to the composite of the descended homeomorphisms. -/
@[simp] theorem gluedCurveHomeomorph_trans (e : Iso I n d d') (e' : Iso I n d' d'') :
    (e.trans e').gluedCurveHomeomorph = e.gluedCurveHomeomorph.trans e'.gluedCurveHomeomorph :=
  Homeomorph.ext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

/-- Descent sends the inverse to the inverse homeomorphism. -/
@[simp] theorem gluedCurveHomeomorph_symm (e : Iso I n d d') :
    e.symm.gluedCurveHomeomorph = e.gluedCurveHomeomorph.symm :=
  Homeomorph.ext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

/-- **Descent is faithful.**  If the points of the normalization which are not flag points are
dense, then an isomorphism of nodal curves is determined by the homeomorphism of glued curves it
induces.  The density hypothesis holds for curves, whose components have no isolated points, by
`Dense.sdiff_finite`. -/
theorem gluedCurveHomeomorph_injective [∀ i, T2Space (X' i)] (hd : Dense (flagPointSet d)ᶜ) :
    Function.Injective (gluedCurveHomeomorph : Iso I n d d' → GluedCurve d ≃ₜ GluedCurve d') := by
  intro e e' h
  -- Off the flag points the two maps agree, because the quotient map is injective there.
  have hagree : EqOn e e' (flagPointSet d)ᶜ := by
    intro x hx
    have hmk := DFunLike.congr_fun h (Quotient.mk _ x)
    rw [gluedCurveHomeomorph_mk, gluedCurveHomeomorph_mk] at hmk
    rcases eq_or_mem_flagPointSet_of_gluedRel d'
        ((gluedRelSetoid_r d' _ _).mp (Quotient.exact hmk)) with heq | ⟨hx', -⟩
    · exact heq
    · exact absurd ((e.apply_mem_flagPointSet_iff x).mp hx') hx
  exact ext (congrFun (e.continuous.ext_on hd e'.continuous hagree))

end Iso

variable (I n d) in
/-- **The automorphism group** of a nodal curve presented by flag-pair data: its isomorphisms
with itself, with composition as multiplication. -/
abbrev Aut : Type _ := Iso I n d d

namespace Aut

instance : One (Aut I n d) := ⟨Iso.refl I n d⟩

instance : Mul (Aut I n d) := ⟨fun e e' ↦ e'.trans e⟩

instance : Inv (Aut I n d) := ⟨Iso.symm⟩

instance : Group (Aut I n d) where
  mul_assoc e e' e'' := (Iso.trans_assoc e'' e' e).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_trans_symm

/-- Multiplication of automorphisms is composition, the right factor acting first. -/
theorem mul_def (e e' : Aut I n d) : e * e' = e'.trans e :=
  (rfl)

/-- The unit automorphism is the identity. -/
theorem one_def : (1 : Aut I n d) = Iso.refl I n d :=
  (rfl)

/-- The inverse automorphism is the inverse isomorphism. -/
theorem inv_def (e : Aut I n d) : e⁻¹ = e.symm :=
  (rfl)

/-- A product of automorphisms acts by composition. -/
@[simp] theorem mul_apply (e e' : Aut I n d) (x : Σ i, X i) : (e * e') x = e (e' x) :=
  (rfl)

/-- The unit automorphism fixes every point. -/
@[simp] theorem one_apply (x : Σ i, X i) : (1 : Aut I n d) x = x :=
  (rfl)

/-- The inverse automorphism acts as the inverse isomorphism. -/
@[simp] theorem inv_apply (e : Aut I n d) (x : Σ i, X i) : e⁻¹ x = e.symm x :=
  (rfl)

/-- **The branch action** of the automorphism group: its action on the branches at the nodes. -/
def branchPerm : Aut I n d →* Equiv.Perm (Flag × Bool) where
  toFun e := e.branchEquiv
  map_one' := Iso.branchEquiv_refl
  map_mul' e e' := Iso.branchEquiv_trans e' e

/-- The branch action of an automorphism is its branch map. -/
@[simp] theorem branchPerm_apply (e : Aut I n d) : branchPerm e = e.branchEquiv :=
  (rfl)

/-- The action of the automorphism group on the nodes. -/
def edgePerm : Aut I n d →* Equiv.Perm Flag where
  toFun e := e.edgeEquiv
  map_one' := Iso.edgeEquiv_refl
  map_mul' e e' := Iso.edgeEquiv_trans e' e

/-- The node action of an automorphism is its node map. -/
@[simp] theorem edgePerm_apply (e : Aut I n d) : edgePerm e = e.edgeEquiv :=
  (rfl)

/-- The action of the automorphism group on the components, when they are connected. -/
def vertexPerm [∀ i, ConnectedSpace (X i)] : Aut I n d →* Equiv.Perm ι where
  toFun e := e.vertexEquiv
  map_one' := Iso.vertexEquiv_refl
  map_mul' e e' := Iso.vertexEquiv_trans e' e

/-- The component action of an automorphism is its component map. -/
@[simp] theorem vertexPerm_apply [∀ i, ConnectedSpace (X i)] (e : Aut I n d) :
    vertexPerm e = e.vertexEquiv :=
  (rfl)

/-- The action of the automorphism group on the glued curve, by descent. -/
def toGluedCurveHomeomorph : Aut I n d →* (GluedCurve d ≃ₜ GluedCurve d) where
  toFun e := e.gluedCurveHomeomorph
  map_one' := Iso.gluedCurveHomeomorph_refl
  map_mul' e e' := Iso.gluedCurveHomeomorph_trans e' e

/-- An automorphism acts on the glued curve by its descended homeomorphism. -/
@[simp] theorem toGluedCurveHomeomorph_apply (e : Aut I n d) :
    toGluedCurveHomeomorph e = e.gluedCurveHomeomorph :=
  (rfl)

/-- The automorphism group acts faithfully on the glued curve when the points which are not flag
points are dense in the normalization. -/
theorem toGluedCurveHomeomorph_injective [∀ i, T2Space (X i)] (hd : Dense (flagPointSet d)ᶜ) :
    Function.Injective (toGluedCurveHomeomorph : Aut I n d →* (GluedCurve d ≃ₜ GluedCurve d)) :=
  Iso.gluedCurveHomeomorph_injective hd

end Aut

end NodalGluing

end TauCeti
