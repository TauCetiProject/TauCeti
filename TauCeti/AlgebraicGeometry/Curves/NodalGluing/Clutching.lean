/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Clutching
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.DualGraph
public import TauCeti.Geometry.Manifold.Diffeomorph.Sigma

/-!
# Clutching glued nodal curves

Pointed nodal curves are glued along marks by Knudsen's two clutching operations. In
**self-clutching**, a curve with marks labelled by `L ⊕ Fin 2` is glued to itself by identifying
the marks `.inr 0` and `.inr 1`, which become the two branches of a new node; the result carries
the marks `L`. In **external clutching**, curves with marks labelled by `Option L₁` and
`Option L₂` are glued by identifying their two marks `none`; the result carries the marks
`L₁ ⊕ L₂`. This file performs both operations on nodal curves presented by flag-pair data, and
compares them with the clutching of dual graphs in
`TauCeti.AlgebraicGeometry.Curves.DualGraph.Clutching`.

The normalization of a clutched curve is the normalization of the original curve (for external
clutching, of the disjoint union of the two curves), and the new flag pair is `none`. So the
clutched curve is a curve with one more node. This file clutches individual curves only; a family
formed by clutching along sections would carry this node in every fibre, but no such family is
constructed here.

## Main definitions

* `NodalGluing.FlagPairData.selfClutch d m`, `NodalGluing.Marking.selfClutch m`: the
  self-clutching of the curve `d` at the marks `m.point (.inr 0)` and `m.point (.inr 1)`, and its
  remaining marks.
* `NodalGluing.selfClutchMap d m`: the map from a glued curve to its self-clutching.
* `NodalGluing.FlagPairData.sum d₁ d₂`: the disjoint union of two curves whose components form one
  family indexed by `ι₁ ⊕ ι₂`.
* `NodalGluing.FlagPairData.clutch d₁ d₂ m₁ m₂`, `NodalGluing.Marking.clutch m₁ m₂`: the external
  clutching of `d₁` and `d₂` at their marks `none`, defined as the self-clutching of the disjoint
  union, and its remaining marks.
* `NodalGluing.inlClutchMap`, `NodalGluing.inrClutchMap`: the maps of the two curves to their
  external clutching.
* `NodalGluing.dualGraphSelfClutchIso`, `NodalGluing.dualGraphClutchIso`: the dual graph of a
  clutched curve is the clutched dual graph.
* `NodalGluing.Iso.selfClutch`, `NodalGluing.Iso.clutch`: isomorphisms of curves which carry the
  glued marks to the glued marks induce isomorphisms of the clutched curves.
* `NodalGluing.Iso.ofSelfClutch`: an isomorphism of self-clutched curves fixing the new node comes
  from an isomorphism of the original curves.

## Main results

* `NodalGluing.isQuotientMap_selfClutchMap` and `NodalGluing.selfClutchMap_eq_selfClutchMap_iff`:
  the self-clutching is the quotient of the curve identifying exactly the two glued marks.
* `NodalGluing.inlClutchMap_injective`, `NodalGluing.inrClutchMap_injective` and
  `NodalGluing.range_inlClutchMap_inter_range_inrClutchMap`: the two curves map injectively into
  their external clutching and meet exactly at the new node.
* `NodalGluing.isQuotientMap_sumElim_inlClutchMap_inrClutchMap`,
  `NodalGluing.isEmbedding_inlClutchMap` and `NodalGluing.isEmbedding_inrClutchMap`: the external
  clutching is the quotient of the disjoint union of the two curves, and each curve embeds in it.
* `NodalGluing.Marking.specialPoints_selfClutch`: self-clutching preserves the special points of
  every component, since the glued marks become node branches.
* `NodalGluing.connectedSpace_gluedCurve_selfClutch` and
  `NodalGluing.connectedSpace_gluedCurve_clutch`: clutching connected curves gives a connected
  curve.
* `NodalGluing.arithmeticGenus_dualGraph_selfClutch` and
  `NodalGluing.arithmeticGenus_dualGraph_clutch`: for dual graphs with given component genera,
  self-clutching raises the arithmetic genus by one, and external clutching adds the genera.
* `NodalGluing.isStable_dualGraph_selfClutch_iff`, `NodalGluing.isStable_dualGraph_clutch_iff`:
  for dual graphs with given component genera, the dual graph of a clutched curve is stable
  exactly when the dual graphs of the curves it is glued from are.
* `NodalGluing.Iso.selfClutchEquiv`: isomorphisms of curves carrying the glued marks to the glued
  marks correspond exactly to isomorphisms of the self-clutchings fixing the new node.
* `NodalGluing.Iso.edgeEquiv_selfClutch_none`, `NodalGluing.Iso.edgeEquiv_clutch_none`, with
  `selfClutch_trans` and `clutch_trans`: clutched isomorphisms fix the new node and clutching is
  compatible with identities and composition.
* `NodalGluing.Iso.gluedCurveHomeomorph_selfClutch_selfClutchMap`,
  `NodalGluing.Iso.gluedCurveHomeomorph_clutch_inlClutchMap` and
  `NodalGluing.Iso.gluedCurveHomeomorph_clutch_inrClutchMap`: the homeomorphisms induced by
  clutched isomorphisms commute with the clutching maps.

## Implementation notes

For external clutching the components of the two curves form one family `X` indexed by
`ι₁ ⊕ ι₂`, and the two curves are presented on its restrictions `fun i ↦ X (.inl i)` and
`fun i ↦ X (.inr i)`. Topological and manifold structures on the components are then instances
for both the curves and their union. `FlagPairData.clutch` and `Marking.clutch` are abbreviations
for a self-clutching of the disjoint union, so that the self-clutching API applies to them
directly. In particular the simp lemmas for self-clutching and disjoint unions already normalize
the flags and marks of an external clutching, so the stated normal forms such as
`FlagPairData.fst_clutch_some_inl` and `Marking.point_clutch_inl` are not simp lemmas.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §3, for the clutching morphisms.
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*
  (Grundlehren der mathematischen Wissenschaften 331, Springer, 2011), Chapter X, for pointed
  nodal curves and their dual graphs.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for nodal Riemann surfaces presented by their nodal pairs.
-/

public noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

/-! ### Self-clutching -/

section SelfClutch

variable {ι Flag : Type*} {X : ι → Type*} {L : Type*}

namespace FlagPairData

variable (d : FlagPairData ι Flag X) (m : Marking d (L ⊕ Fin 2))

/-- **Self-clutching.** The flag-pair data obtained from `d` by gluing the two marks
`m.point (.inr 0)` and `m.point (.inr 1)` to each other. The new flag pair is `none`; its first
point is the mark `.inr 0` and its second point the mark `.inr 1`. The old flag pairs are kept as
`some f`. -/
def selfClutch : FlagPairData ι (Option Flag) X where
  fst
    | none => (m.point (.inr 0)).1
    | some f => d.fst f
  snd
    | none => (m.point (.inr 1)).1
    | some f => d.snd f
  fstPt
    | none => (m.point (.inr 0)).2
    | some f => d.fstPt f
  sndPt
    | none => (m.point (.inr 1)).2
    | some f => d.sndPt f
  flagPointOf_injective' := by
    have hd := flagPoint_injective d
    have hm := m.point_injective
    have hn := m.point_notMem_flagPointSet
    rintro ⟨_ | f, _ | _⟩ ⟨_ | g, _ | _⟩ h <;>
      simp only [flagPointOf_false, flagPointOf_true, Sigma.eta, ← fstPoint_def, ← sndPoint_def,
        ← flagPoint_false, ← flagPoint_true] at h
    all_goals first
      | rfl
      | exact absurd (hm h) (by simp)
      | exact (hn _ (by rw [flagPointSet_eq_range]; exact ⟨_, h.symm⟩)).elim
      | exact (hn _ (by rw [flagPointSet_eq_range]; exact ⟨_, h⟩)).elim
      | simpa using hd h

end FlagPairData

variable {d : FlagPairData ι Flag X} {m : Marking d (L ⊕ Fin 2)}

/-- The new flag pair of a self-clutching starts on the component of the mark `.inr 0`. -/
@[simp]
theorem FlagPairData.fst_selfClutch_none : (d.selfClutch m).fst none = (m.point (.inr 0)).1 :=
  (rfl)

/-- The new flag pair of a self-clutching ends on the component of the mark `.inr 1`. -/
@[simp]
theorem FlagPairData.snd_selfClutch_none : (d.selfClutch m).snd none = (m.point (.inr 1)).1 :=
  (rfl)

/-- The old flag pairs keep their first components under self-clutching. -/
@[simp]
theorem FlagPairData.fst_selfClutch_some (f : Flag) : (d.selfClutch m).fst (some f) = d.fst f :=
  (rfl)

/-- The old flag pairs keep their second components under self-clutching. -/
@[simp]
theorem FlagPairData.snd_selfClutch_some (f : Flag) : (d.selfClutch m).snd (some f) = d.snd f :=
  (rfl)

/-- The first point of the new flag pair of a self-clutching is the mark `.inr 0`. -/
@[simp]
theorem fstPoint_selfClutch_none : fstPoint (d.selfClutch m) none = m.point (.inr 0) := by
  rw [fstPoint_def]
  rfl

/-- The second point of the new flag pair of a self-clutching is the mark `.inr 1`. -/
@[simp]
theorem sndPoint_selfClutch_none : sndPoint (d.selfClutch m) none = m.point (.inr 1) := by
  rw [sndPoint_def]
  rfl

/-- The old flag pairs keep their first points under self-clutching. -/
@[simp]
theorem fstPoint_selfClutch_some (f : Flag) :
    fstPoint (d.selfClutch m) (some f) = fstPoint d f := by
  rw [fstPoint_def, fstPoint_def]
  rfl

/-- The old flag pairs keep their second points under self-clutching. -/
@[simp]
theorem sndPoint_selfClutch_some (f : Flag) :
    sndPoint (d.selfClutch m) (some f) = sndPoint d f := by
  rw [sndPoint_def, sndPoint_def]
  rfl

/-- The old flag pairs keep their flag points under self-clutching. -/
@[simp]
theorem flagPoint_selfClutch_some (f : Flag) (b : Bool) :
    flagPoint (d.selfClutch m) (some f, b) = flagPoint d (f, b) := by
  cases b <;> simp

/-- **The flag points of a self-clutching** are the old flag points and the two glued marks. -/
theorem flagPointSet_selfClutch :
    flagPointSet (d.selfClutch m) = flagPointSet d ∪ {m.point (.inr 0), m.point (.inr 1)} := by
  ext x
  simp only [mem_flagPointSet, Option.exists, fstPoint_selfClutch_none, sndPoint_selfClutch_none,
    fstPoint_selfClutch_some, sndPoint_selfClutch_some, mem_union, mem_insert_iff,
    mem_singleton_iff]
  exact or_comm

/-- **The generating relation of a self-clutching** relates the points related by `d` and the two
glued marks, in either order. -/
theorem flagRel_selfClutch_iff (x y : Σ i, X i) :
    flagRel (d.selfClutch m) x y ↔
      flagRel d x y ∨ s(x, y) = s(m.point (.inr 0), m.point (.inr 1)) := by
  simp only [flagRel_def, Option.exists, fstPoint_selfClutch_none, sndPoint_selfClutch_none,
    fstPoint_selfClutch_some, sndPoint_selfClutch_some, Sym2.eq_iff]
  exact or_comm

/-- A pair related by `d` is never the pair of glued marks. -/
private theorem not_flagRel_of_sym2_eq {x y : Σ i, X i}
    (h : s(x, y) = s(m.point (.inr 0), m.point (.inr 1))) : ¬ flagRel d x y := by
  intro hxy
  have hx : x ∈ flagPointSet d := (mem_flagPointSet_iff_exists_flagRel d x).mpr ⟨y, hxy⟩
  rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [m.point_notMem_flagPointSet _ hx, m.point_notMem_flagPointSet _ hx]

/-- A mark which is not glued, viewed as a mark of a self-clutching. -/
def Marking.selfClutch (m : Marking d (L ⊕ Fin 2)) : Marking (d.selfClutch m) L where
  point l := m.point (.inl l)
  point_injective _ _ h := Sum.inl_injective (m.point_injective h)
  point_notMem_flagPointSet l := by
    rw [flagPointSet_selfClutch]
    rintro (h | h | h)
    · exact m.point_notMem_flagPointSet _ h
    · exact Sum.inl_ne_inr (m.point_injective h)
    · exact Sum.inl_ne_inr (m.point_injective h)

/-- The marks of a self-clutching are the marks `.inl l` of the original curve. -/
@[simp]
theorem Marking.point_selfClutch (l : L) : m.selfClutch.point l = m.point (.inl l) :=
  (rfl)

/-- **Self-clutching preserves the special points of every component**: the two glued marks become
the two branches of the new node, so they remain special. -/
@[simp]
theorem Marking.specialPoints_selfClutch (i : ι) :
    m.selfClutch.specialPoints i = m.specialPoints i := by
  ext x
  simp only [Marking.mem_specialPoints_iff, flagPointSet_selfClutch, Marking.point_selfClutch,
    mem_union, mem_insert_iff, mem_singleton_iff, Sum.exists, Fin.exists_fin_two]
  tauto

variable (d m) in
/-- **The clutching map.** The map from a glued curve to its self-clutching, sending a point to its
class; it identifies the two glued marks, which become the new node. It is continuous by
`continuous_selfClutchMap`. -/
def selfClutchMap : GluedCurve d → GluedCurve (d.selfClutch m) :=
  GluedCurve.lift d (Quotient.mk _) fun f ↦ by
    rw [← fstPoint_selfClutch_some (m := m), ← sndPoint_selfClutch_some (m := m), mk_fstPoint,
      mk_sndPoint]

/-- The clutching map sends the class of a point to its class. -/
@[simp]
theorem selfClutchMap_mk (x : Σ i, X i) :
    selfClutchMap d m (Quotient.mk _ x) = Quotient.mk (gluedRelSetoid (d.selfClutch m)) x :=
  GluedCurve.lift_mk _ _ _ x

/-- The clutching map is continuous. -/
theorem continuous_selfClutchMap [∀ i, TopologicalSpace (X i)] :
    Continuous (selfClutchMap d m) :=
  GluedCurve.continuous_lift _ _ _ continuous_quotient_mk'

/-- **The self-clutching is a quotient of the curve**: the clutching map is a quotient map. -/
theorem isQuotientMap_selfClutchMap [∀ i, TopologicalSpace (X i)] :
    IsQuotientMap (selfClutchMap d m) := by
  refine .of_comp continuous_quotient_mk' continuous_selfClutchMap ?_
  convert isQuotientMap_quotient_mk' (s := gluedRelSetoid (d.selfClutch m))
  exact funext selfClutchMap_mk

/-- Each of the two glued marks is a branch of the new node of the self-clutching. -/
@[simp]
theorem mk_point_inr_selfClutch (k : Fin 2) :
    Quotient.mk (gluedRelSetoid (d.selfClutch m)) (m.point (.inr k)) =
      nodeOfFlag (d.selfClutch m) none := by
  rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with rfl | rfl
  · rw [← fstPoint_selfClutch_none, mk_fstPoint]
  · rw [← sndPoint_selfClutch_none, mk_sndPoint]

/-- **The clutching map glues exactly the two marks**: two points of the curve have the same image
exactly when they are equal or are the classes of the two glued marks. -/
theorem selfClutchMap_eq_selfClutchMap_iff (a b : GluedCurve d) :
    selfClutchMap d m a = selfClutchMap d m b ↔
      a = b ∨ s(a, b) = s(Quotient.mk _ (m.point (.inr 0)), Quotient.mk _ (m.point (.inr 1))) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  simp only [selfClutchMap_mk, Quotient.eq, gluedRelSetoid_r, gluedRel_def, flagRel_selfClutch_iff,
    Sym2.eq_iff, m.mk_eq_mk_point_iff]
  tauto

/-- **Self-clutching of a connected curve is connected.** -/
instance connectedSpace_gluedCurve_selfClutch [∀ i, TopologicalSpace (X i)]
    [ConnectedSpace (GluedCurve d)] : ConnectedSpace (GluedCurve (d.selfClutch m)) :=
  isQuotientMap_selfClutchMap.surjective.connectedSpace continuous_selfClutchMap

/-- A pair related by a self-clutching is related by the original data exactly when it is not the
pair of glued marks. -/
theorem flagRel_iff_flagRel_selfClutch_and_ne (x y : Σ i, X i) :
    flagRel d x y ↔
      flagRel (d.selfClutch m) x y ∧ s(x, y) ≠ s(m.point (.inr 0), m.point (.inr 1)) := by
  rw [flagRel_selfClutch_iff]
  exact ⟨fun h ↦ ⟨.inl h, fun h' ↦ not_flagRel_of_sym2_eq h' h⟩,
    fun ⟨h, hne⟩ ↦ h.resolve_right hne⟩

end SelfClutch

/-! ### The dual graph of a self-clutching -/

section SelfClutchDualGraph

universe u

variable {ι Flag : Type u} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, ConnectedSpace (X i)] {d : FlagPairData ι Flag X} [ConnectedSpace (GluedCurve d)]
  [Fintype ι] [DecidableEq ι] [Fintype Flag] [DecidableEq Flag] {L : Type*}
  (g : ι → ℕ) (m : Marking d (L ⊕ Fin 2))

/-- **The dual graph of a self-clutching is the self-clutching of the dual graph.** The
isomorphism is the identity on components and on flag pairs; the new flag pair `none` is the new
edge of `DualGraph.selfClutch`. -/
def dualGraphSelfClutchIso : (dualGraph g m.selfClutch).Iso (dualGraph g m).selfClutch where
  vertexEquiv := .refl ι
  edgeEquiv := .refl (Option Flag)
  ends_edgeEquiv e := by
    cases e <;> simp [DualGraph.ends_def]
  genus_vertexEquiv _ := rfl
  vertexEquiv_marking _ := rfl

/-- The comparison of dual graphs is the identity on components. -/
@[simp]
theorem dualGraphSelfClutchIso_vertexEquiv :
    (dualGraphSelfClutchIso g m).vertexEquiv = .refl ι :=
  (rfl)

/-- The comparison of dual graphs is the identity on flag pairs. -/
@[simp]
theorem dualGraphSelfClutchIso_edgeEquiv :
    (dualGraphSelfClutchIso g m).edgeEquiv = .refl (Option Flag) :=
  (rfl)

/-- **Self-clutching raises the arithmetic genus by one**: with the component genera `g`, the
dual graph of the self-clutching has arithmetic genus one more than the dual graph of the curve. -/
theorem arithmeticGenus_dualGraph_selfClutch :
    (dualGraph g m.selfClutch).arithmeticGenus = (dualGraph g m).arithmeticGenus + 1 := by
  rw [(dualGraphSelfClutchIso g m).arithmeticGenus_eq, DualGraph.arithmeticGenus_selfClutch]

/-- **Self-clutching preserves stability**: with the component genera `g`, the dual graph of the
self-clutching is stable exactly when the dual graph of the curve with the two glued marks is. -/
theorem isStable_dualGraph_selfClutch_iff [Fintype L] :
    (dualGraph g m.selfClutch).IsStable ↔ (dualGraph g m).IsStable := by
  rw [(dualGraphSelfClutchIso g m).isStable_iff, DualGraph.isStable_selfClutch_iff]

end SelfClutchDualGraph

/-! ### Isomorphisms of self-clutchings -/

section SelfClutchIso

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)]
  {ι'' Flag'' : Type*} {X'' : ι'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'} {d'' : FlagPairData ι'' Flag'' X''}
  {L : Type*} {m : Marking d (L ⊕ Fin 2)} {m' : Marking d' (L ⊕ Fin 2)}
  {m'' : Marking d'' (L ⊕ Fin 2)}

namespace Iso

/-- **Isomorphisms clutch.** An isomorphism of nodal curves carrying the two glued marks of `m` to
the two glued marks of `m'`, in either order, is an isomorphism of the self-clutchings. The
underlying map of normalizations is unchanged. -/
def selfClutch (e : Iso I n d d')
    (he : s(e (m.point (.inr 0)), e (m.point (.inr 1))) =
      s(m'.point (.inr 0), m'.point (.inr 1))) :
    Iso I n (d.selfClutch m) (d'.selfClutch m') where
  toDiffeomorph := e.toDiffeomorph
  flagRel_apply_iff' x y := by
    rw [flagRel_selfClutch_iff, flagRel_selfClutch_iff, coe_toDiffeomorph, e.flagRel_apply_iff,
      ← he, ← Sym2.map_mk, ← Sym2.map_mk, (Sym2.map.injective (EquivLike.injective e)).eq_iff]

variable (e : Iso I n d d')
  (he : s(e (m.point (.inr 0)), e (m.point (.inr 1))) = s(m'.point (.inr 0), m'.point (.inr 1)))

/-- The clutched isomorphism acts as the original one on the normalizations. -/
@[simp]
theorem selfClutch_apply (x : Σ i, X i) : e.selfClutch he x = e x :=
  (rfl)

/-- The clutched isomorphism acts on the old branches as the original one. -/
@[simp]
theorem branchEquiv_selfClutch_some (f : Flag) (b : Bool) :
    (e.selfClutch he).branchEquiv (some f, b) =
      (some (e.branchEquiv (f, b)).1, (e.branchEquiv (f, b)).2) := by
  rw [branchEquiv_apply_eq_iff, selfClutch_apply, flagPoint_selfClutch_some,
    flagPoint_selfClutch_some, Prod.mk.eta, flagPoint_branchEquiv]

/-- The clutched isomorphism acts on the old nodes as the original one. -/
@[simp]
theorem edgeEquiv_selfClutch_some (f : Flag) :
    (e.selfClutch he).edgeEquiv (some f) = some (e.edgeEquiv f) := by
  rw [edgeEquiv_apply _ _ false, edgeEquiv_apply _ _ false, branchEquiv_selfClutch_some]

/-- **The clutched isomorphism fixes the new node.** -/
@[simp]
theorem edgeEquiv_selfClutch_none : (e.selfClutch he).edgeEquiv none = none := by
  rcases h : (e.selfClutch he).edgeEquiv none with _ | f'
  · rfl
  · obtain ⟨f, rfl⟩ := e.edgeEquiv.surjective f'
    rw [← edgeEquiv_selfClutch_some e he] at h
    exact absurd ((e.selfClutch he).edgeEquiv.injective h) (by simp)

/-- Clutching the identity gives the identity. -/
@[simp]
theorem selfClutch_refl
    (he : s((Iso.refl I n d) (m.point (.inr 0)), (Iso.refl I n d) (m.point (.inr 1))) =
      s(m.point (.inr 0), m.point (.inr 1))) :
    (Iso.refl I n d).selfClutch he = Iso.refl I n (d.selfClutch m) :=
  ext fun _ ↦ by simp

/-- Clutching commutes with composition. -/
theorem selfClutch_trans (e' : Iso I n d' d'')
    (he' : s(e' (m'.point (.inr 0)), e' (m'.point (.inr 1))) =
      s(m''.point (.inr 0), m''.point (.inr 1)))
    (he'' : s((e.trans e') (m.point (.inr 0)), (e.trans e') (m.point (.inr 1))) =
      s(m''.point (.inr 0), m''.point (.inr 1))) :
    (e.trans e').selfClutch he'' = (e.selfClutch he).trans (e'.selfClutch he') :=
  ext fun _ ↦ by simp

/-- Clutching commutes with inverses. -/
theorem selfClutch_symm
    (he' : s(e.symm (m'.point (.inr 0)), e.symm (m'.point (.inr 1))) =
      s(m.point (.inr 0), m.point (.inr 1))) :
    e.symm.selfClutch he' = (e.selfClutch he).symm :=
  ext fun _ ↦ ((e.selfClutch he).symm_apply_eq.mpr (by simp)).symm

/-- **Clutching is natural**: the homeomorphism of self-clutchings induced by a clutched
isomorphism commutes with the clutching maps. -/
@[simp]
theorem gluedCurveHomeomorph_selfClutch_selfClutchMap (a : GluedCurve d) :
    (e.selfClutch he).gluedCurveHomeomorph (selfClutchMap d m a) =
      selfClutchMap d' m' (e.gluedCurveHomeomorph a) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  simp only [selfClutchMap_mk, gluedCurveHomeomorph_mk, selfClutch_apply]

/-- An isomorphism of self-clutchings fixing the new node carries the two glued marks to the two
glued marks, possibly exchanging them. -/
theorem sym2_apply_point_inr_of_edgeEquiv_none (e : Iso I n (d.selfClutch m) (d'.selfClutch m'))
    (he : e.edgeEquiv none = none) :
    s(e (m.point (.inr 0)), e (m.point (.inr 1))) = s(m'.point (.inr 0), m'.point (.inr 1)) := by
  have h₀ := e.flagPoint_branchEquiv (none, false)
  have h₁ := e.flagPoint_branchEquiv (none, true)
  have hswap := e.branchEquiv_swap (none, false)
  rcases hb : e.branchEquiv (none, false) with ⟨f, b⟩
  have hf : f = none := by rw [← he, edgeEquiv_apply _ _ false, hb]
  subst hf
  rw [hb] at h₀ hswap
  rw [Bool.not_false] at hswap
  rw [hswap] at h₁
  simp only [flagPoint_false, flagPoint_true, fstPoint_selfClutch_none,
    sndPoint_selfClutch_none] at h₀ h₁
  rw [← h₀, ← h₁]
  cases b <;> simp [Sym2.eq_swap]

/-- **Isomorphisms fixing the new node unclutch.** An isomorphism of self-clutchings fixing the
new node is an isomorphism of the original curves, with the same map of normalizations. -/
def ofSelfClutch (e : Iso I n (d.selfClutch m) (d'.selfClutch m')) (he : e.edgeEquiv none = none) :
    Iso I n d d' where
  toDiffeomorph := e.toDiffeomorph
  flagRel_apply_iff' x y := by
    rw [flagRel_iff_flagRel_selfClutch_and_ne (m := m'),
      flagRel_iff_flagRel_selfClutch_and_ne (m := m),
      coe_toDiffeomorph, e.flagRel_apply_iff, ← sym2_apply_point_inr_of_edgeEquiv_none e he,
      ← Sym2.map_mk, ← Sym2.map_mk, (Sym2.map.injective (EquivLike.injective e)).ne_iff]

/-- The unclutched isomorphism acts as the original one on the normalizations. -/
@[simp]
theorem ofSelfClutch_apply (e : Iso I n (d.selfClutch m) (d'.selfClutch m'))
    (he : e.edgeEquiv none = none) (x : Σ i, X i) : e.ofSelfClutch he x = e x :=
  (rfl)

/-- **Clutching is fully faithful on isomorphisms**: isomorphisms of the curves carrying the glued
marks to the glued marks correspond to isomorphisms of the self-clutchings fixing the new node. -/
def selfClutchEquiv :
    {e : Iso I n d d' //
      s(e (m.point (.inr 0)), e (m.point (.inr 1))) = s(m'.point (.inr 0), m'.point (.inr 1))} ≃
    {e : Iso I n (d.selfClutch m) (d'.selfClutch m') // e.edgeEquiv none = none} where
  toFun e := ⟨e.val.selfClutch e.property, edgeEquiv_selfClutch_none _ _⟩
  invFun e := ⟨e.val.ofSelfClutch e.property,
    sym2_apply_point_inr_of_edgeEquiv_none e.val e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The correspondence `selfClutchEquiv` keeps the map of normalizations. -/
@[simp]
theorem selfClutchEquiv_apply_apply
    (e : {e : Iso I n d d' //
      s(e (m.point (.inr 0)), e (m.point (.inr 1))) = s(m'.point (.inr 0), m'.point (.inr 1))})
    (x : Σ i, X i) : (selfClutchEquiv e).val x = e.val x :=
  (rfl)

/-- The inverse correspondence `selfClutchEquiv.symm` keeps the map of normalizations. -/
@[simp]
theorem selfClutchEquiv_symm_apply_apply
    (e : {e : Iso I n (d.selfClutch m) (d'.selfClutch m') // e.edgeEquiv none = none})
    (x : Σ i, X i) : (selfClutchEquiv.symm e).val x = e.val x :=
  (rfl)

end Iso

end SelfClutchIso

/-! ### Disjoint unions and external clutching -/

section External

variable {ι₁ ι₂ Flag₁ Flag₂ L₁ L₂ : Type*} {X : ι₁ ⊕ ι₂ → Type*}

namespace FlagPairData

/-- **The disjoint union of two nodal curves.** Its normalization components are those of `d₁`
and those of `d₂`, indexed by `ι₁ ⊕ ι₂`, and its flag pairs are those of `d₁` and those of `d₂`.
The components are given as one family `X` on `ι₁ ⊕ ι₂`, so that structures on them are
instances for the union. -/
def sum (d₁ : FlagPairData ι₁ Flag₁ fun i ↦ X (.inl i))
    (d₂ : FlagPairData ι₂ Flag₂ fun i ↦ X (.inr i)) : FlagPairData (ι₁ ⊕ ι₂) (Flag₁ ⊕ Flag₂) X where
  fst := Sum.map d₁.fst d₂.fst
  snd := Sum.map d₁.snd d₂.snd
  fstPt
    | .inl f => d₁.fstPt f
    | .inr f => d₂.fstPt f
  sndPt
    | .inl f => d₁.sndPt f
    | .inr f => d₂.sndPt f
  flagPointOf_injective' := by
    have h₁ := flagPoint_injective d₁
    have h₂ := flagPoint_injective d₂
    rintro ⟨f | f, _ | _⟩ ⟨g | g, _ | _⟩ h <;>
      have h := congrArg (Equiv.sumSigmaDistrib X) h <;>
      simp only [flagPointOf_false, flagPointOf_true, Equiv.sumSigmaDistrib_apply, Sum.map_inl,
        Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ← fstPoint_def, ← sndPoint_def,
        ← flagPoint_false, ← flagPoint_true] at h
    all_goals first
      | simpa using h₁ h
      | simpa using h₂ h

end FlagPairData

variable {d₁ : FlagPairData ι₁ Flag₁ fun i ↦ X (.inl i)}
  {d₂ : FlagPairData ι₂ Flag₂ fun i ↦ X (.inr i)}

private theorem sigmaMap_inl_injective :
    Function.Injective (Sigma.map Sum.inl (fun _ ↦ id) : (Σ i, X (.inl i)) → Σ i, X i) :=
  Sum.inl_injective.sigma_map fun _ ↦ Function.injective_id

private theorem sigmaMap_inr_injective :
    Function.Injective (Sigma.map Sum.inr (fun _ ↦ id) : (Σ i, X (.inr i)) → Σ i, X i) :=
  Sum.inr_injective.sigma_map fun _ ↦ Function.injective_id

private theorem sigmaMap_inl_ne_sigmaMap_inr (x : Σ i, X (.inl i)) (y : Σ i, X (.inr i)) :
    Sigma.map Sum.inl (fun _ ↦ id) x ≠ Sigma.map Sum.inr (fun _ ↦ id) y :=
  fun h ↦ Sum.inl_ne_inr (congrArg Sigma.fst h)

/-- The flag pairs of a disjoint union start on the components of the two curves. -/
@[simp]
theorem FlagPairData.fst_sum : (d₁.sum d₂).fst = Sum.map d₁.fst d₂.fst :=
  (rfl)

/-- The flag pairs of a disjoint union end on the components of the two curves. -/
@[simp]
theorem FlagPairData.snd_sum : (d₁.sum d₂).snd = Sum.map d₁.snd d₂.snd :=
  (rfl)

/-- The flag points of the first curve are flag points of the disjoint union. -/
@[simp]
theorem flagPoint_sum_inl (f : Flag₁) (b : Bool) :
    flagPoint (d₁.sum d₂) (.inl f, b) = Sigma.map Sum.inl (fun _ ↦ id) (flagPoint d₁ (f, b)) := by
  cases b <;> simp only [flagPoint_false, flagPoint_true, fstPoint_def, sndPoint_def] <;> rfl

/-- The flag points of the second curve are flag points of the disjoint union. -/
@[simp]
theorem flagPoint_sum_inr (f : Flag₂) (b : Bool) :
    flagPoint (d₁.sum d₂) (.inr f, b) = Sigma.map Sum.inr (fun _ ↦ id) (flagPoint d₂ (f, b)) := by
  cases b <;> simp only [flagPoint_false, flagPoint_true, fstPoint_def, sndPoint_def] <;> rfl

/-- Points of the first curve are related in the disjoint union exactly when they are related in
the first curve. -/
@[simp]
theorem flagRel_sum_inl_inl (x y : Σ i, X (.inl i)) :
    flagRel (d₁.sum d₂) (Sigma.map Sum.inl (fun _ ↦ id) x) (Sigma.map Sum.inl (fun _ ↦ id) y) ↔
      flagRel d₁ x y := by
  simp only [flagRel_def, Sum.exists, ← flagPoint_false, ← flagPoint_true, flagPoint_sum_inl,
    flagPoint_sum_inr, sigmaMap_inl_injective.eq_iff, sigmaMap_inl_ne_sigmaMap_inr, and_false,
    or_false, exists_false]

/-- Points of the second curve are related in the disjoint union exactly when they are related in
the second curve. -/
@[simp]
theorem flagRel_sum_inr_inr (x y : Σ i, X (.inr i)) :
    flagRel (d₁.sum d₂) (Sigma.map Sum.inr (fun _ ↦ id) x) (Sigma.map Sum.inr (fun _ ↦ id) y) ↔
      flagRel d₂ x y := by
  simp only [flagRel_def, Sum.exists, ← flagPoint_false, ← flagPoint_true, flagPoint_sum_inl,
    flagPoint_sum_inr, sigmaMap_inr_injective.eq_iff, (sigmaMap_inl_ne_sigmaMap_inr _ _).symm,
    and_false, or_false, exists_false, false_or]

/-- A point of the first curve is never related to a point of the second curve in their disjoint
union. -/
@[simp]
theorem not_flagRel_sum_inl_inr (x : Σ i, X (.inl i)) (y : Σ i, X (.inr i)) :
    ¬ flagRel (d₁.sum d₂) (Sigma.map Sum.inl (fun _ ↦ id) x)
      (Sigma.map Sum.inr (fun _ ↦ id) y) := by
  simp only [flagRel_def, Sum.exists, ← flagPoint_false, ← flagPoint_true, flagPoint_sum_inl,
    flagPoint_sum_inr, sigmaMap_inl_ne_sigmaMap_inr, (sigmaMap_inl_ne_sigmaMap_inr _ _).symm,
    and_false, false_and, or_false, exists_false, not_false_eq_true]

/-- A point of the second curve is never related to a point of the first curve in their disjoint
union. -/
@[simp]
theorem not_flagRel_sum_inr_inl (x : Σ i, X (.inr i)) (y : Σ i, X (.inl i)) :
    ¬ flagRel (d₁.sum d₂) (Sigma.map Sum.inr (fun _ ↦ id) x) (Sigma.map Sum.inl (fun _ ↦ id) y) :=
  fun h ↦ not_flagRel_sum_inl_inr y x (flagRel_symm _ h)

/-- **The flag points of a disjoint union** are those of its two curves. -/
theorem flagPointSet_sum :
    flagPointSet (d₁.sum d₂) = Sigma.map Sum.inl (fun _ ↦ id) '' flagPointSet d₁ ∪
      Sigma.map Sum.inr (fun _ ↦ id) '' flagPointSet d₂ := by
  simp only [flagPointSet_eq_range, ← range_comp]
  ext x
  simp only [mem_range, mem_union, Prod.exists, Sum.exists, Function.comp_apply,
    flagPoint_sum_inl, flagPoint_sum_inr]

variable (m₁ : Marking d₁ (Option L₁)) (m₂ : Marking d₂ (Option L₂))

/-- The marks of a disjoint union prepared for external clutching. The mark `.inl (.inl l)` is
the mark `some l` of the first curve, `.inl (.inr l)` is the mark `some l` of the second curve,
and the two marks to be glued are `.inr 0`, the mark `none` of the first curve, and `.inr 1`, the
mark `none` of the second curve. -/
def Marking.sumClutch : Marking (d₁.sum d₂) ((L₁ ⊕ L₂) ⊕ Fin 2) where
  point := Sum.elim
    (Sum.elim (fun l ↦ Sigma.map Sum.inl (fun _ ↦ id) (m₁.point (some l)))
      (fun l ↦ Sigma.map Sum.inr (fun _ ↦ id) (m₂.point (some l))))
    ![Sigma.map Sum.inl (fun _ ↦ id) (m₁.point none),
      Sigma.map Sum.inr (fun _ ↦ id) (m₂.point none)]
  point_injective := by
    have hl := sigmaMap_inl_injective (X := X)
    have hr := sigmaMap_inr_injective (X := X)
    have h₁ := m₁.point_injective
    have h₂ := m₂.point_injective
    have hlr := sigmaMap_inl_ne_sigmaMap_inr (X := X)
    rintro ((l | l) | k) ((l' | l') | k') h <;> (try fin_cases k) <;> (try fin_cases k') <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    all_goals first
      | rfl
      | exact absurd h (hlr _ _)
      | exact absurd h.symm (hlr _ _)
      | simpa using h₁ (hl h)
      | simpa using h₂ (hr h)
  point_notMem_flagPointSet := by
    have hl := sigmaMap_inl_injective (X := X)
    have hr := sigmaMap_inr_injective (X := X)
    have hlr := sigmaMap_inl_ne_sigmaMap_inr (X := X)
    rw [flagPointSet_sum]
    rintro ((l | l) | k) <;> (try fin_cases k) <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    all_goals first
      | exact m₁.point_notMem_flagPointSet _ (hl h ▸ hx)
      | exact m₂.point_notMem_flagPointSet _ (hr h ▸ hx)
      | exact hlr _ _ h
      | exact hlr _ _ h.symm

/-- The marks `.inl (.inl l)` of `Marking.sumClutch` are the marks `some l` of the first curve. -/
@[simp]
theorem Marking.point_sumClutch_inl_inl (l : L₁) :
    (m₁.sumClutch m₂).point (.inl (.inl l)) = Sigma.map Sum.inl (fun _ ↦ id) (m₁.point (some l)) :=
  (rfl)

/-- The marks `.inl (.inr l)` of `Marking.sumClutch` are the marks `some l` of the second curve. -/
@[simp]
theorem Marking.point_sumClutch_inl_inr (l : L₂) :
    (m₁.sumClutch m₂).point (.inl (.inr l)) = Sigma.map Sum.inr (fun _ ↦ id) (m₂.point (some l)) :=
  (rfl)

/-- The first mark to be glued is the mark `none` of the first curve. -/
@[simp]
theorem Marking.point_sumClutch_inr_zero :
    (m₁.sumClutch m₂).point (.inr 0) = Sigma.map Sum.inl (fun _ ↦ id) (m₁.point none) :=
  (rfl)

/-- The second mark to be glued is the mark `none` of the second curve. -/
@[simp]
theorem Marking.point_sumClutch_inr_one :
    (m₁.sumClutch m₂).point (.inr 1) = Sigma.map Sum.inr (fun _ ↦ id) (m₂.point none) :=
  (rfl)

/-- **External clutching.** The flag-pair data obtained from the disjoint union of `d₁` and `d₂`
by gluing the mark `none` of the first curve to the mark `none` of the second; the new flag pair is
`none`. -/
abbrev FlagPairData.clutch (d₁ : FlagPairData ι₁ Flag₁ fun i ↦ X (.inl i))
    (d₂ : FlagPairData ι₂ Flag₂ fun i ↦ X (.inr i)) (m₁ : Marking d₁ (Option L₁))
    (m₂ : Marking d₂ (Option L₂)) : FlagPairData (ι₁ ⊕ ι₂) (Option (Flag₁ ⊕ Flag₂)) X :=
  (d₁.sum d₂).selfClutch (m₁.sumClutch m₂)

/-- The marks of an external clutching: the marks `some l` of the two curves. -/
abbrev Marking.clutch : Marking (d₁.clutch d₂ m₁ m₂) (L₁ ⊕ L₂) :=
  (m₁.sumClutch m₂).selfClutch

/-- The new flag pair of an external clutching starts on the component of the first glued mark. -/
theorem FlagPairData.fst_clutch_none :
    (d₁.clutch d₂ m₁ m₂).fst none = .inl (m₁.point none).1 :=
  (rfl)

/-- The new flag pair of an external clutching ends on the component of the second glued mark. -/
theorem FlagPairData.snd_clutch_none :
    (d₁.clutch d₂ m₁ m₂).snd none = .inr (m₂.point none).1 :=
  (rfl)

/-- The flag pairs of the first curve keep their first components under external clutching. -/
theorem FlagPairData.fst_clutch_some_inl (f : Flag₁) :
    (d₁.clutch d₂ m₁ m₂).fst (some (.inl f)) = .inl (d₁.fst f) :=
  (rfl)

/-- The flag pairs of the first curve keep their second components under external clutching. -/
theorem FlagPairData.snd_clutch_some_inl (f : Flag₁) :
    (d₁.clutch d₂ m₁ m₂).snd (some (.inl f)) = .inl (d₁.snd f) :=
  (rfl)

/-- The flag pairs of the second curve keep their first components under external clutching. -/
theorem FlagPairData.fst_clutch_some_inr (f : Flag₂) :
    (d₁.clutch d₂ m₁ m₂).fst (some (.inr f)) = .inr (d₂.fst f) :=
  (rfl)

/-- The flag pairs of the second curve keep their second components under external clutching. -/
theorem FlagPairData.snd_clutch_some_inr (f : Flag₂) :
    (d₁.clutch d₂ m₁ m₂).snd (some (.inr f)) = .inr (d₂.snd f) :=
  (rfl)

/-- The flag points of the first curve are flag points of its external clutching. -/
theorem flagPoint_clutch_some_inl (f : Flag₁) (b : Bool) :
    flagPoint (d₁.clutch d₂ m₁ m₂) (some (.inl f), b) =
      Sigma.map Sum.inl (fun _ ↦ id) (flagPoint d₁ (f, b)) := by
  rw [flagPoint_selfClutch_some, flagPoint_sum_inl]

/-- The flag points of the second curve are flag points of its external clutching. -/
theorem flagPoint_clutch_some_inr (f : Flag₂) (b : Bool) :
    flagPoint (d₁.clutch d₂ m₁ m₂) (some (.inr f), b) =
      Sigma.map Sum.inr (fun _ ↦ id) (flagPoint d₂ (f, b)) := by
  rw [flagPoint_selfClutch_some, flagPoint_sum_inr]

/-- The marks `.inl l` of an external clutching are the marks `some l` of the first curve. -/
theorem Marking.point_clutch_inl (l : L₁) :
    (m₁.clutch m₂).point (.inl l) = Sigma.map Sum.inl (fun _ ↦ id) (m₁.point (some l)) :=
  (rfl)

/-- The marks `.inr l` of an external clutching are the marks `some l` of the second curve. -/
theorem Marking.point_clutch_inr (l : L₂) :
    (m₁.clutch m₂).point (.inr l) = Sigma.map Sum.inr (fun _ ↦ id) (m₂.point (some l)) :=
  (rfl)

variable (d₂) in
/-- The inclusion of the first curve into an external clutching. -/
def inlClutchMap : GluedCurve d₁ → GluedCurve (d₁.clutch d₂ m₁ m₂) :=
  GluedCurve.lift d₁ (fun x ↦ Quotient.mk _ (Sigma.map Sum.inl (fun _ ↦ id) x)) fun f ↦ by
    simp only [← flagPoint_false, ← flagPoint_true, ← flagPoint_sum_inl (d₂ := d₂),
      ← flagPoint_selfClutch_some (m := m₁.sumClutch m₂), mk_flagPoint]

variable (d₁) in
/-- The inclusion of the second curve into an external clutching. -/
def inrClutchMap : GluedCurve d₂ → GluedCurve (d₁.clutch d₂ m₁ m₂) :=
  GluedCurve.lift d₂ (fun x ↦ Quotient.mk _ (Sigma.map Sum.inr (fun _ ↦ id) x)) fun f ↦ by
    simp only [← flagPoint_false, ← flagPoint_true, ← flagPoint_sum_inr (d₁ := d₁),
      ← flagPoint_selfClutch_some (m := m₁.sumClutch m₂), mk_flagPoint]

variable {m₁ m₂}

/-- The inclusion of the first curve sends the class of a point to its class. -/
@[simp]
theorem inlClutchMap_mk (x : Σ i, X (.inl i)) :
    inlClutchMap d₂ m₁ m₂ (Quotient.mk _ x) = Quotient.mk _ (Sigma.map Sum.inl (fun _ ↦ id) x) :=
  GluedCurve.lift_mk _ _ _ x

/-- The inclusion of the second curve sends the class of a point to its class. -/
@[simp]
theorem inrClutchMap_mk (x : Σ i, X (.inr i)) :
    inrClutchMap d₁ m₁ m₂ (Quotient.mk _ x) = Quotient.mk _ (Sigma.map Sum.inr (fun _ ↦ id) x) :=
  GluedCurve.lift_mk _ _ _ x

/-- The glued mark of the first curve is a branch of the new node of an external clutching. -/
@[simp]
theorem mk_sigmaMap_inl_point_none_clutch :
    Quotient.mk (gluedRelSetoid (d₁.clutch d₂ m₁ m₂))
        (Sigma.map Sum.inl (fun _ ↦ id) (m₁.point none)) =
      nodeOfFlag (d₁.clutch d₂ m₁ m₂) none :=
  mk_point_inr_selfClutch 0

/-- The glued mark of the second curve is a branch of the new node of an external clutching. -/
@[simp]
theorem mk_sigmaMap_inr_point_none_clutch :
    Quotient.mk (gluedRelSetoid (d₁.clutch d₂ m₁ m₂))
        (Sigma.map Sum.inr (fun _ ↦ id) (m₂.point none)) =
      nodeOfFlag (d₁.clutch d₂ m₁ m₂) none :=
  mk_point_inr_selfClutch 1

/-- The inclusion of the first curve sends its glued mark to the new node. -/
theorem inlClutchMap_mk_point_none :
    inlClutchMap d₂ m₁ m₂ (Quotient.mk _ (m₁.point none)) =
      nodeOfFlag (d₁.clutch d₂ m₁ m₂) none := by
  rw [inlClutchMap_mk, mk_sigmaMap_inl_point_none_clutch]

/-- The inclusion of the second curve sends its glued mark to the new node. -/
theorem inrClutchMap_mk_point_none :
    inrClutchMap d₁ m₁ m₂ (Quotient.mk _ (m₂.point none)) =
      nodeOfFlag (d₁.clutch d₂ m₁ m₂) none := by
  rw [inrClutchMap_mk, mk_sigmaMap_inr_point_none_clutch]

/-- **The two curves cover their external clutching.** -/
theorem range_inlClutchMap_union_range_inrClutchMap :
    range (inlClutchMap d₂ m₁ m₂) ∪ range (inrClutchMap d₁ m₁ m₂) = univ := by
  refine eq_univ_of_forall fun q ↦ ?_
  induction q using Quotient.inductionOn with | _ x => ?_
  obtain ⟨i | i, x⟩ := x
  exacts [.inl ⟨Quotient.mk _ ⟨i, x⟩, inlClutchMap_mk _⟩,
    .inr ⟨Quotient.mk _ ⟨i, x⟩, inrClutchMap_mk _⟩]

/-- The inclusion of the first curve into an external clutching is injective. -/
theorem inlClutchMap_injective : Function.Injective (inlClutchMap d₂ m₁ m₂) := by
  intro a b h
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  simpa [Quotient.eq, gluedRel_def, flagRel_selfClutch_iff, sigmaMap_inl_injective.eq_iff,
    sigmaMap_inl_ne_sigmaMap_inr, Sym2.eq_iff] using h

/-- The inclusion of the second curve into an external clutching is injective. -/
theorem inrClutchMap_injective : Function.Injective (inrClutchMap d₁ m₁ m₂) := by
  intro a b h
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  simpa [Quotient.eq, gluedRel_def, flagRel_selfClutch_iff, sigmaMap_inr_injective.eq_iff,
    (sigmaMap_inl_ne_sigmaMap_inr _ _).symm, Sym2.eq_iff] using h

/-- **The two curves meet only at their glued marks**: a point of the first curve and a point of
the second have the same image in the external clutching exactly when they are the two glued
marks. -/
theorem inlClutchMap_eq_inrClutchMap_iff (a : GluedCurve d₁) (b : GluedCurve d₂) :
    inlClutchMap d₂ m₁ m₂ a = inrClutchMap d₁ m₁ m₂ b ↔
      a = Quotient.mk _ (m₁.point none) ∧ b = Quotient.mk _ (m₂.point none) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  simp [m₁.mk_eq_mk_point_iff, m₂.mk_eq_mk_point_iff, Quotient.eq, gluedRel_def,
    flagRel_selfClutch_iff, sigmaMap_inl_ne_sigmaMap_inr, (sigmaMap_inl_ne_sigmaMap_inr _ _).symm,
    sigmaMap_inl_injective.eq_iff, sigmaMap_inr_injective.eq_iff]

/-- **The two curves of an external clutching meet exactly at the new node.** -/
theorem range_inlClutchMap_inter_range_inrClutchMap :
    range (inlClutchMap d₂ m₁ m₂) ∩ range (inrClutchMap d₁ m₁ m₂) =
      {nodeOfFlag (d₁.clutch d₂ m₁ m₂) none} := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨a, rfl⟩, b, hb⟩
    obtain ⟨rfl, -⟩ := (inlClutchMap_eq_inrClutchMap_iff a b).mp hb.symm
    exact inlClutchMap_mk_point_none
  · rintro _ rfl
    exact ⟨⟨_, inlClutchMap_mk_point_none⟩, _, inrClutchMap_mk_point_none⟩

variable [∀ i, TopologicalSpace (X i)]

/-- The inclusion of the first curve into an external clutching is continuous. -/
theorem continuous_inlClutchMap : Continuous (inlClutchMap d₂ m₁ m₂) :=
  GluedCurve.continuous_lift _ _ _
    (continuous_quotient_mk'.comp (continuous_sigma_map.mpr fun _ ↦ continuous_id))

/-- The inclusion of the second curve into an external clutching is continuous. -/
theorem continuous_inrClutchMap : Continuous (inrClutchMap d₁ m₁ m₂) :=
  GluedCurve.continuous_lift _ _ _
    (continuous_quotient_mk'.comp (continuous_sigma_map.mpr fun _ ↦ continuous_id))

/-- **The external clutching is a quotient of the two curves**: together, the inclusions of the
two curves form a quotient map from their disjoint union. -/
theorem isQuotientMap_sumElim_inlClutchMap_inrClutchMap :
    IsQuotientMap (Sum.elim (inlClutchMap d₂ m₁ m₂) (inrClutchMap d₁ m₁ m₂)) := by
  have hf : Continuous (Sum.map (Quotient.mk (gluedRelSetoid d₁))
      (Quotient.mk (gluedRelSetoid d₂)) ∘ Equiv.sumSigmaDistrib X) :=
    continuous_sigma fun
      | .inl _ => continuous_inl.comp (continuous_quotient_mk'.comp continuous_sigmaMk)
      | .inr _ => continuous_inr.comp (continuous_quotient_mk'.comp continuous_sigmaMk)
  refine .of_comp hf (continuous_inlClutchMap.sumElim continuous_inrClutchMap) ?_
  convert isQuotientMap_quotient_mk' (s := gluedRelSetoid (d₁.clutch d₂ m₁ m₂))
  funext x
  rcases x with ⟨i | i, x⟩
  exacts [inlClutchMap_mk ⟨i, x⟩, inrClutchMap_mk ⟨i, x⟩]

/-- The retraction of an external clutching onto the first curve, collapsing the second curve to
the glued mark of the first. -/
private def inlClutchRetraction : GluedCurve (d₁.clutch d₂ m₁ m₂) → GluedCurve d₁ :=
  GluedCurve.lift _ (fun x ↦ Sum.elim (Quotient.mk _) (fun _ ↦ Quotient.mk _ (m₁.point none))
      (Equiv.sumSigmaDistrib X x)) fun f ↦ by
    rcases f with _ | f | f
    · simp only [fstPoint_selfClutch_none, sndPoint_selfClutch_none,
        Marking.point_sumClutch_inr_zero, Marking.point_sumClutch_inr_one,
        Equiv.sumSigmaDistrib_apply_sigmaMap_inl, Equiv.sumSigmaDistrib_apply_sigmaMap_inr,
        Sum.elim_inl, Sum.elim_inr]
    all_goals simp only [← flagPoint_false, ← flagPoint_true, flagPoint_clutch_some_inl,
      flagPoint_clutch_some_inr, Equiv.sumSigmaDistrib_apply_sigmaMap_inl,
      Equiv.sumSigmaDistrib_apply_sigmaMap_inr, Sum.elim_inl, Sum.elim_inr, mk_flagPoint]

/-- The retraction of an external clutching onto the second curve, collapsing the first curve to
the glued mark of the second. -/
private def inrClutchRetraction : GluedCurve (d₁.clutch d₂ m₁ m₂) → GluedCurve d₂ :=
  GluedCurve.lift _ (fun x ↦ Sum.elim (fun _ ↦ Quotient.mk _ (m₂.point none)) (Quotient.mk _)
      (Equiv.sumSigmaDistrib X x)) fun f ↦ by
    rcases f with _ | f | f
    · simp only [fstPoint_selfClutch_none, sndPoint_selfClutch_none,
        Marking.point_sumClutch_inr_zero, Marking.point_sumClutch_inr_one,
        Equiv.sumSigmaDistrib_apply_sigmaMap_inl, Equiv.sumSigmaDistrib_apply_sigmaMap_inr,
        Sum.elim_inl, Sum.elim_inr]
    all_goals simp only [← flagPoint_false, ← flagPoint_true, flagPoint_clutch_some_inl,
      flagPoint_clutch_some_inr, Equiv.sumSigmaDistrib_apply_sigmaMap_inl,
      Equiv.sumSigmaDistrib_apply_sigmaMap_inr, Sum.elim_inl, Sum.elim_inr, mk_flagPoint]

/-- **The first curve embeds in an external clutching.** -/
theorem isEmbedding_inlClutchMap : IsEmbedding (inlClutchMap d₂ m₁ m₂) :=
  .of_leftInverse (f := inlClutchRetraction) (fun a ↦ Quotient.inductionOn a fun _ ↦ by
      simp only [inlClutchRetraction, inlClutchMap_mk, GluedCurve.lift_mk,
        Equiv.sumSigmaDistrib_apply_sigmaMap_inl, Sum.elim_inl])
    (GluedCurve.continuous_lift _ _ _ <| continuous_sigma fun
      | .inl _ => continuous_quotient_mk'.comp continuous_sigmaMk
      | .inr _ => continuous_const)
    continuous_inlClutchMap

/-- **The second curve embeds in an external clutching.** -/
theorem isEmbedding_inrClutchMap : IsEmbedding (inrClutchMap d₁ m₁ m₂) :=
  .of_leftInverse (f := inrClutchRetraction) (fun a ↦ Quotient.inductionOn a fun _ ↦ by
      simp only [inrClutchRetraction, inrClutchMap_mk, GluedCurve.lift_mk,
        Equiv.sumSigmaDistrib_apply_sigmaMap_inr, Sum.elim_inr])
    (GluedCurve.continuous_lift _ _ _ <| continuous_sigma fun
      | .inl _ => continuous_const
      | .inr _ => continuous_quotient_mk'.comp continuous_sigmaMk)
    continuous_inrClutchMap

/-- **External clutching of connected curves is connected**: the two curves meet at the new
node. -/
instance connectedSpace_gluedCurve_clutch [ConnectedSpace (GluedCurve d₁)]
    [ConnectedSpace (GluedCurve d₂)] : ConnectedSpace (GluedCurve (d₁.clutch d₂ m₁ m₂)) := by
  rw [connectedSpace_iff_univ, ← range_inlClutchMap_union_range_inrClutchMap]
  refine (isConnected_range continuous_inlClutchMap).union ?_
    (isConnected_range continuous_inrClutchMap)
  exact ⟨_, ⟨_, inlClutchMap_mk_point_none⟩, ⟨_, inrClutchMap_mk_point_none⟩⟩

end External

/-! ### The dual graph of an external clutching -/

section ExternalDualGraph

universe u

variable {ι₁ ι₂ Flag₁ Flag₂ : Type u} {X : ι₁ ⊕ ι₂ → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, ConnectedSpace (X i)] {d₁ : FlagPairData ι₁ Flag₁ fun i ↦ X (.inl i)}
  {d₂ : FlagPairData ι₂ Flag₂ fun i ↦ X (.inr i)} [ConnectedSpace (GluedCurve d₁)]
  [ConnectedSpace (GluedCurve d₂)] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype Flag₁] [DecidableEq Flag₁] [Fintype Flag₂] [DecidableEq Flag₂] {L₁ L₂ : Type*}
  (g₁ : ι₁ → ℕ) (g₂ : ι₂ → ℕ) (m₁ : Marking d₁ (Option L₁)) (m₂ : Marking d₂ (Option L₂))

/-- **The dual graph of an external clutching is the clutching of the dual graphs.** The
isomorphism is the identity on components and on flag pairs; the new flag pair `none` is the new
edge of `DualGraph.clutch`. -/
def dualGraphClutchIso :
    (dualGraph (Sum.elim g₁ g₂) (m₁.clutch m₂)).Iso
      ((dualGraph g₁ m₁).clutch (dualGraph g₂ m₂)) where
  vertexEquiv := .refl (ι₁ ⊕ ι₂)
  edgeEquiv := .refl (Option (Flag₁ ⊕ Flag₂))
  ends_edgeEquiv e := by
    rw [Equiv.refl_apply, Equiv.coe_refl, Sym2.map_id, id_eq, DualGraph.ends_def,
      DualGraph.ends_def]
    rcases e with _ | f | f <;> rfl
  genus_vertexEquiv _ := rfl
  vertexEquiv_marking l := by
    rcases l with l | l <;> rfl

/-- The comparison of dual graphs is the identity on components. -/
@[simp]
theorem dualGraphClutchIso_vertexEquiv :
    (dualGraphClutchIso g₁ g₂ m₁ m₂).vertexEquiv = .refl (ι₁ ⊕ ι₂) :=
  (rfl)

/-- The comparison of dual graphs is the identity on flag pairs. -/
@[simp]
theorem dualGraphClutchIso_edgeEquiv :
    (dualGraphClutchIso g₁ g₂ m₁ m₂).edgeEquiv = .refl (Option (Flag₁ ⊕ Flag₂)) :=
  (rfl)

/-- **External clutching adds the arithmetic genera**: with the component genera `g₁` and `g₂`,
the arithmetic genus of the dual graph of the external clutching is the sum of those of the dual
graphs of the two curves. -/
theorem arithmeticGenus_dualGraph_clutch :
    (dualGraph (Sum.elim g₁ g₂) (m₁.clutch m₂)).arithmeticGenus =
      (dualGraph g₁ m₁).arithmeticGenus + (dualGraph g₂ m₂).arithmeticGenus := by
  rw [(dualGraphClutchIso g₁ g₂ m₁ m₂).arithmeticGenus_eq, DualGraph.arithmeticGenus_clutch]

/-- **External clutching preserves stability**: with the component genera `g₁` and `g₂`, the dual
graph of the external clutching is stable exactly when the dual graphs of both curves are. -/
theorem isStable_dualGraph_clutch_iff [Fintype L₁] [Fintype L₂] :
    (dualGraph (Sum.elim g₁ g₂) (m₁.clutch m₂)).IsStable ↔
      (dualGraph g₁ m₁).IsStable ∧ (dualGraph g₂ m₂).IsStable := by
  rw [(dualGraphClutchIso g₁ g₂ m₁ m₂).isStable_iff, DualGraph.isStable_clutch_iff]

end ExternalDualGraph

/-! ### Isomorphisms of external clutchings -/

section ExternalIso

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι₁ ι₂ Flag₁ Flag₂ : Type*} {X : ι₁ ⊕ ι₂ → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace H (X i)]
  {ι₁' ι₂' Flag₁' Flag₂' : Type*} {X' : ι₁' ⊕ ι₂' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)]
  {ι₁'' ι₂'' Flag₁'' Flag₂'' : Type*} {X'' : ι₁'' ⊕ ι₂'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)]
  {d₁ : FlagPairData ι₁ Flag₁ fun i ↦ X (.inl i)} {d₂ : FlagPairData ι₂ Flag₂ fun i ↦ X (.inr i)}
  {d₁' : FlagPairData ι₁' Flag₁' fun i ↦ X' (.inl i)}
  {d₂' : FlagPairData ι₂' Flag₂' fun i ↦ X' (.inr i)}
  {d₁'' : FlagPairData ι₁'' Flag₁'' fun i ↦ X'' (.inl i)}
  {d₂'' : FlagPairData ι₂'' Flag₂'' fun i ↦ X'' (.inr i)}

namespace Iso

/-- **The disjoint union of two isomorphisms** of nodal curves, an isomorphism of the disjoint
unions. -/
def sum (e₁ : Iso I n d₁ d₁') (e₂ : Iso I n d₂ d₂') : Iso I n (d₁.sum d₂) (d₁'.sum d₂') where
  toDiffeomorph := (Diffeomorph.sumSigmaDistrib I n X).trans
    ((e₁.toDiffeomorph.sumCongr e₂.toDiffeomorph).trans (Diffeomorph.sumSigmaDistrib I n X').symm)
  flagRel_apply_iff' x y := by
    obtain ⟨x | x, rfl⟩ := (Diffeomorph.sumSigmaDistrib I n X).symm.surjective x <;>
    obtain ⟨y | y, rfl⟩ := (Diffeomorph.sumSigmaDistrib I n X).symm.surjective y <;>
    simp only [Diffeomorph.coe_toEquiv, Diffeomorph.coe_trans, Function.comp_apply,
      Diffeomorph.apply_symm_apply, Diffeomorph.sumCongr_coe, Sum.map_inl, Sum.map_inr] <;>
    simp only [Diffeomorph.sumSigmaDistrib_symm_apply_inl,
      Diffeomorph.sumSigmaDistrib_symm_apply_inr, coe_toDiffeomorph, flagRel_sum_inl_inl,
      flagRel_sum_inr_inr, not_flagRel_sum_inl_inr, not_flagRel_sum_inr_inl, flagRel_apply_iff]

variable (e₁ : Iso I n d₁ d₁') (e₂ : Iso I n d₂ d₂')

/-- The disjoint union of two isomorphisms acts on the first curve as the first one. -/
@[simp]
theorem sum_apply_inl (x : Σ i, X (.inl i)) :
    e₁.sum e₂ (Sigma.map Sum.inl (fun _ ↦ id) x) = Sigma.map Sum.inl (fun _ ↦ id) (e₁ x) := by
  obtain ⟨i, x⟩ := x
  simp only [← coe_toDiffeomorph, sum, Diffeomorph.coe_trans, Function.comp_apply, Sigma.map_mk,
    Diffeomorph.sumSigmaDistrib_apply_inl, Diffeomorph.sumCongr_coe, Sum.map_inl,
    Diffeomorph.sumSigmaDistrib_symm_apply_inl, id]

/-- The disjoint union of two isomorphisms acts on the second curve as the second one. -/
@[simp]
theorem sum_apply_inr (x : Σ i, X (.inr i)) :
    e₁.sum e₂ (Sigma.map Sum.inr (fun _ ↦ id) x) = Sigma.map Sum.inr (fun _ ↦ id) (e₂ x) := by
  obtain ⟨i, x⟩ := x
  simp only [← coe_toDiffeomorph, sum, Diffeomorph.coe_trans, Function.comp_apply, Sigma.map_mk,
    Diffeomorph.sumSigmaDistrib_apply_inr, Diffeomorph.sumCongr_coe, Sum.map_inr,
    Diffeomorph.sumSigmaDistrib_symm_apply_inr, id]

/-- Isomorphisms of disjoint unions agree when they agree on both curves. -/
private theorem ext_sum {e e' : Iso I n (d₁.sum d₂) (d₁'.sum d₂')}
    (h₁ : ∀ x, e (Sigma.map Sum.inl (fun _ ↦ id) x) = e' (Sigma.map Sum.inl (fun _ ↦ id) x))
    (h₂ : ∀ x, e (Sigma.map Sum.inr (fun _ ↦ id) x) = e' (Sigma.map Sum.inr (fun _ ↦ id) x)) :
    e = e' :=
  ext fun x ↦ by
    obtain ⟨x | x, rfl⟩ := (Diffeomorph.sumSigmaDistrib I n X).symm.surjective x
    · simpa only [Diffeomorph.coe_toEquiv, Diffeomorph.sumSigmaDistrib_symm_apply_inl] using h₁ x
    · simpa only [Diffeomorph.coe_toEquiv, Diffeomorph.sumSigmaDistrib_symm_apply_inr] using h₂ x

/-- The disjoint union of two identities is the identity. -/
@[simp]
theorem sum_refl : (Iso.refl I n d₁).sum (Iso.refl I n d₂) = Iso.refl I n (d₁.sum d₂) :=
  ext_sum (fun _ ↦ by simp) fun _ ↦ by simp

/-- The disjoint union of composites is the composite of the disjoint unions. -/
theorem sum_trans (e₁' : Iso I n d₁' d₁'') (e₂' : Iso I n d₂' d₂'') :
    (e₁.trans e₁').sum (e₂.trans e₂') = (e₁.sum e₂).trans (e₁'.sum e₂') :=
  ext_sum (fun _ ↦ by simp) fun _ ↦ by simp

/-- The disjoint union of inverses is the inverse of the disjoint union. -/
theorem sum_symm : e₁.symm.sum e₂.symm = (e₁.sum e₂).symm :=
  ext_sum (fun _ ↦ ((e₁.sum e₂).symm_apply_eq.mpr (by simp)).symm)
    fun _ ↦ ((e₁.sum e₂).symm_apply_eq.mpr (by simp)).symm

variable {L₁ L₂ : Type*} {m₁ : Marking d₁ (Option L₁)} {m₂ : Marking d₂ (Option L₂)}
  {m₁' : Marking d₁' (Option L₁)} {m₂' : Marking d₂' (Option L₂)}
  {m₁'' : Marking d₁'' (Option L₁)} {m₂'' : Marking d₂'' (Option L₂)}

/-- **Isomorphisms clutch externally.** Two isomorphisms of nodal curves, each carrying the glued
mark `none` to the glued mark `none`, give an isomorphism of the external clutchings. -/
def clutch (h₁ : e₁ (m₁.point none) = m₁'.point none) (h₂ : e₂ (m₂.point none) = m₂'.point none) :
    Iso I n (d₁.clutch d₂ m₁ m₂) (d₁'.clutch d₂' m₁' m₂') :=
  (e₁.sum e₂).selfClutch <| by
    simp only [Marking.point_sumClutch_inr_zero, Marking.point_sumClutch_inr_one, sum_apply_inl,
      sum_apply_inr, h₁, h₂]

variable (h₁ : e₁ (m₁.point none) = m₁'.point none) (h₂ : e₂ (m₂.point none) = m₂'.point none)

/-- The clutched isomorphism acts on the first curve as the first isomorphism. -/
@[simp]
theorem clutch_apply_inl (x : Σ i, X (.inl i)) :
    e₁.clutch e₂ h₁ h₂ (Sigma.map Sum.inl (fun _ ↦ id) x) = Sigma.map Sum.inl (fun _ ↦ id) (e₁ x) :=
  sum_apply_inl e₁ e₂ x

/-- The clutched isomorphism acts on the second curve as the second isomorphism. -/
@[simp]
theorem clutch_apply_inr (x : Σ i, X (.inr i)) :
    e₁.clutch e₂ h₁ h₂ (Sigma.map Sum.inr (fun _ ↦ id) x) = Sigma.map Sum.inr (fun _ ↦ id) (e₂ x) :=
  sum_apply_inr e₁ e₂ x

/-- **External clutching is natural on the first curve**: the homeomorphism of external
clutchings induced by a clutched isomorphism commutes with the inclusions of the first curves. -/
@[simp]
theorem gluedCurveHomeomorph_clutch_inlClutchMap (a : GluedCurve d₁) :
    (e₁.clutch e₂ h₁ h₂).gluedCurveHomeomorph (inlClutchMap d₂ m₁ m₂ a) =
      inlClutchMap d₂' m₁' m₂' (e₁.gluedCurveHomeomorph a) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  simp only [inlClutchMap_mk, gluedCurveHomeomorph_mk, clutch_apply_inl]

/-- **External clutching is natural on the second curve**: the homeomorphism of external
clutchings induced by a clutched isomorphism commutes with the inclusions of the second curves. -/
@[simp]
theorem gluedCurveHomeomorph_clutch_inrClutchMap (a : GluedCurve d₂) :
    (e₁.clutch e₂ h₁ h₂).gluedCurveHomeomorph (inrClutchMap d₁ m₁ m₂ a) =
      inrClutchMap d₁' m₁' m₂' (e₂.gluedCurveHomeomorph a) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  simp only [inrClutchMap_mk, gluedCurveHomeomorph_mk, clutch_apply_inr]

/-- **The clutched isomorphism fixes the new node.** -/
@[simp]
theorem edgeEquiv_clutch_none : (e₁.clutch e₂ h₁ h₂).edgeEquiv none = none :=
  edgeEquiv_selfClutch_none _ _

/-- Isomorphisms preserving every mark clutch to an isomorphism preserving every mark. -/
theorem clutch_apply_point (hm₁ : ∀ l, e₁ (m₁.point l) = m₁'.point l)
    (hm₂ : ∀ l, e₂ (m₂.point l) = m₂'.point l) (l : L₁ ⊕ L₂) :
    e₁.clutch e₂ h₁ h₂ ((m₁.clutch m₂).point l) = (m₁'.clutch m₂').point l := by
  rcases l with l | l <;>
    simp [Marking.clutch, hm₁, hm₂]

/-- Clutching the identities gives the identity. -/
@[simp]
theorem clutch_refl (h₁ : Iso.refl I n d₁ (m₁.point none) = m₁.point none)
    (h₂ : Iso.refl I n d₂ (m₂.point none) = m₂.point none) :
    (Iso.refl I n d₁).clutch (Iso.refl I n d₂) h₁ h₂ = Iso.refl I n (d₁.clutch d₂ m₁ m₂) :=
  ext fun _ ↦ by simp [clutch]

/-- Clutching commutes with composition. -/
theorem clutch_trans (e₁' : Iso I n d₁' d₁'') (e₂' : Iso I n d₂' d₂'')
    (h₁' : e₁' (m₁'.point none) = m₁''.point none) (h₂' : e₂' (m₂'.point none) = m₂''.point none)
    (h₁'' : e₁.trans e₁' (m₁.point none) = m₁''.point none)
    (h₂'' : e₂.trans e₂' (m₂.point none) = m₂''.point none) :
    (e₁.trans e₁').clutch (e₂.trans e₂') h₁'' h₂'' =
      (e₁.clutch e₂ h₁ h₂).trans (e₁'.clutch e₂' h₁' h₂') :=
  ext fun _ ↦ by simp [clutch, sum_trans]

/-- Clutching commutes with inverses. -/
theorem clutch_symm (h₁' : e₁.symm (m₁'.point none) = m₁.point none)
    (h₂' : e₂.symm (m₂'.point none) = m₂.point none) :
    e₁.symm.clutch e₂.symm h₁' h₂' = (e₁.clutch e₂ h₁ h₂).symm :=
  ext fun _ ↦ ((e₁.clutch e₂ h₁ h₂).symm_apply_eq.mpr (by simp [clutch, sum_symm])).symm

end Iso

end ExternalIso

end NodalGluing

end TauCeti
