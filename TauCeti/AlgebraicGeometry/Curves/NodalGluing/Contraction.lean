/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Forget
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.DualGraph

/-!
# Forgetting a mark and contracting a tail of a glued nodal curve

Knudsen's forgetful map from `(n + 1)`-pointed to `n`-pointed stable curves forgets a mark and then
contracts the components that become unstable: a rational tail carrying at most one of the
remaining marks, or an unmarked rational bridge. This file performs the first of these
contractions on a nodal curve presented by flag-pair data `d : FlagPairData ι Flag X`.

A **tail** of `d` is a component `X v` carrying exactly one flag point, the branch `p₀` of a node
(`∀ p, (flagPoint d p).1 = v ↔ p = p₀`). The other branch of that node, the *attaching point*
`flagPoint d (p₀.1, !p₀.2)`, lies on another component.
Contracting the tail removes the component `X v` and its node:

* `FlagPairData.deleteComponent d v` is the flag-pair data on the components other than `v`, with
  the flag pairs having no branch on `v`. The attaching point is not a flag point of it, so in the
  contracted curve it is not a node.
* `Marking.contractTail` moves a mark lying on the tail to the attaching point and keeps the other
  marks. At most one mark may lie on the tail, as for a rational tail which becomes unstable after
  forgetting a mark.
* `contractTailMap` is the continuous map from the glued curve to the contracted curve that
  collapses the whole tail onto the attaching point and is the identity elsewhere.

This file treats only the flag-pair data, the topological quotient `GluedCurve` and the dual
graph, not the complex structure sheaf. The normalization of the contracted curve is the
normalization of `d` with the component `X v` removed. The genus labels of the components are an
input, as in `NodalGluing.dualGraph`; the contraction is the stabilization step when the tail is
labelled by genus zero.

Forgetting the mark `none` of marks labelled by `Option L` is relabelling them along
`Function.Embedding.some` (`Marking.reindex`); on dual graphs it is `DualGraph.reindex`
(`dualGraph_reindex`).

## Main definitions

* `NodalGluing.FlagPairData.deleteComponent`: the flag-pair data with one component and all its
  nodes removed.
* `NodalGluing.Marking.contractTail`: the marks of the contracted curve.
* `NodalGluing.contractTailMap`: the contraction of a tail.
* `NodalGluing.dualGraphContractTailIso`: the dual graph of the contracted curve is the contraction
  `DualGraph.contractTail` of the dual graph.

## Main results

* `NodalGluing.gluedRel_deleteComponent_iff`: removing a component does not change how the
  remaining points are glued.
* `NodalGluing.contractTailMap_eq_contractTailMap_iff`: the contraction identifies two points
  exactly when they are equal or both lie on the tail.
* `NodalGluing.isQuotientMap_contractTailMap`: the contracted curve is the quotient of the curve
  collapsing the tail.
* `NodalGluing.contractTailMap_mk_point`: the contraction carries the marks to the marks.
* `NodalGluing.mk_attachPoint_notMem_nodeSet_deleteComponent`: the image of the tail is not a node
  of the contracted curve.
* `NodalGluing.arithmeticGenus_dualGraph_contractTail`: contracting a tail lowers the arithmetic
  genus by the genus of the tail.
* `NodalGluing.isStable_dualGraph_contractTail_reindex_some`: if the dual graph is stable,
  forgetting the mark `none` and contracting a genus-zero tail carrying at most one remaining mark
  gives a curve with stable dual graph.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §§1–2, for forgetting a mark and contracting
  the components which become unstable.
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*
  (Grundlehren der mathematischen Wissenschaften 331, Springer, 2011), Chapter X, for the
  stabilization of pointed nodal curves.
* [Stacks, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N), contracting rational tails.
-/

public noncomputable section

open Set Topology

namespace TauCeti

namespace NodalGluing

variable {ι Flag : Type*} {X : ι → Type*}

/-! ### Deleting a component -/

section Delete

variable (d : FlagPairData ι Flag X) (v : ι)

namespace FlagPairData

/-- **Deleting a component.** The flag-pair data on the components other than `X v`, keeping
exactly the flag pairs with no branch on `X v`. A flag point of `d` whose partner lies on `X v` is
not a flag point of the result. -/
def deleteComponent :
    FlagPairData {i // i ≠ v} {f : Flag // d.fst f ≠ v ∧ d.snd f ≠ v} (fun i ↦ X i) where
  fst f := ⟨d.fst f, f.property.1⟩
  snd f := ⟨d.snd f, f.property.2⟩
  fstPt f := d.fstPt f
  sndPt f := d.sndPt f
  flagPointOf_injective' := by
    rintro ⟨⟨f, hf⟩, b⟩ ⟨⟨f', hf'⟩, b'⟩ h
    replace h := congrArg (Sigma.map Subtype.val fun _ ↦ id) h
    have h' : flagPoint d (f, b) = flagPoint d (f', b') := by
      cases b <;> cases b' <;> simp only [flagPointOf_false, flagPointOf_true] at h <;>
        simpa [Sigma.map, fstPoint_def, sndPoint_def] using h
    simpa using flagPoint_injective d h'

end FlagPairData

variable {d v}

/-- The components of the deleted data are the components of `d` other than `X v`, and its flag
pairs keep their first components. -/
@[simp]
theorem FlagPairData.fst_deleteComponent (f : {f : Flag // d.fst f ≠ v ∧ d.snd f ≠ v}) :
    (d.deleteComponent v).fst f = ⟨d.fst f, f.property.1⟩ :=
  (rfl)

/-- The flag pairs of the deleted data keep their second components. -/
@[simp]
theorem FlagPairData.snd_deleteComponent (f : {f : Flag // d.fst f ≠ v ∧ d.snd f ≠ v}) :
    (d.deleteComponent v).snd f = ⟨d.snd f, f.property.2⟩ :=
  (rfl)

/-- The normalization of the deleted data is a part of the normalization of `d`. -/
private theorem sigmaMap_val_injective (v : ι) :
    Function.Injective (Sigma.map Subtype.val fun (i : {i // i ≠ v}) ↦ (id : X i → X i)) :=
  Subtype.val_injective.sigma_map fun _ ↦ Function.injective_id

/-- The flag points of the deleted data are flag points of `d`. -/
@[simp]
theorem sigmaMap_flagPoint_deleteComponent
    (p : {f : Flag // d.fst f ≠ v ∧ d.snd f ≠ v} × Bool) :
    Sigma.map Subtype.val (fun _ ↦ id) (flagPoint (d.deleteComponent v) p) =
      flagPoint d (p.1.val, p.2) := by
  obtain ⟨f, _ | _⟩ := p
  · rw [flagPoint_false, flagPoint_false, fstPoint_def, fstPoint_def]
    rfl
  · rw [flagPoint_true, flagPoint_true, sndPoint_def, sndPoint_def]
    rfl

/-- **Deleting a component does not change the gluing of the other points.** Two points off
`X v` are the two points of a flag pair of the deleted data exactly when they are the two points
of a flag pair of `d`. -/
theorem flagRel_deleteComponent_iff (x y : Σ i : {i // i ≠ v}, X i) :
    flagRel (d.deleteComponent v) x y ↔
      flagRel d (Sigma.map Subtype.val (fun _ ↦ id) x)
        (Sigma.map Subtype.val (fun _ ↦ id) y) := by
  have hinj := sigmaMap_val_injective (X := X) v
  have hoff (z : Σ i : {i // i ≠ v}, X i) (w : Σ i, X i)
      (h : Sigma.map Subtype.val (fun _ ↦ id) z = w) : w.1 ≠ v := by
    subst h
    exact z.1.property
  rw [flagRel_def, flagRel_def]
  constructor
  · rintro ⟨f, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨f.val, Or.inl ⟨by simpa using sigmaMap_flagPoint_deleteComponent (f, false),
        by simpa using sigmaMap_flagPoint_deleteComponent (f, true)⟩⟩
    · exact ⟨f.val, Or.inr ⟨by simpa using sigmaMap_flagPoint_deleteComponent (f, true),
        by simpa using sigmaMap_flagPoint_deleteComponent (f, false)⟩⟩
  · rintro ⟨f, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · have hf : d.fst f ≠ v ∧ d.snd f ≠ v :=
        ⟨by simpa [fstPoint_def] using hoff x _ hx, by simpa [sndPoint_def] using hoff y _ hy⟩
      refine ⟨⟨f, hf⟩, Or.inl ⟨hinj ?_, hinj ?_⟩⟩
      · simpa [← flagPoint_false] using hx
      · simpa [← flagPoint_true] using hy
    · have hf : d.fst f ≠ v ∧ d.snd f ≠ v :=
        ⟨by simpa [fstPoint_def] using hoff y _ hy, by simpa [sndPoint_def] using hoff x _ hx⟩
      refine ⟨⟨f, hf⟩, Or.inr ⟨hinj ?_, hinj ?_⟩⟩
      · simpa [← flagPoint_true] using hx
      · simpa [← flagPoint_false] using hy

/-- **Deleting a component does not change the gluing of the other points**, for the generated
relation. -/
theorem gluedRel_deleteComponent_iff (x y : Σ i : {i // i ≠ v}, X i) :
    gluedRel (d.deleteComponent v) x y ↔
      gluedRel d (Sigma.map Subtype.val (fun _ ↦ id) x)
        (Sigma.map Subtype.val (fun _ ↦ id) y) := by
  rw [gluedRel_def, gluedRel_def, flagRel_deleteComponent_iff,
    (sigmaMap_val_injective (X := X) v).eq_iff]

end Delete

/-! ### Tails -/

section Tail

variable {d : FlagPairData ι Flag X} {v : ι} {p₀ : Flag × Bool}

/-- The attaching point of a tail lies off the tail. -/
theorem fst_flagPoint_ne_of_tail (htail : ∀ p, (flagPoint d p).1 = v ↔ p = p₀) :
    (flagPoint d (p₀.1, !p₀.2)).1 ≠ v := by
  intro h
  have := congrArg Prod.snd ((htail _).mp h)
  cases hb : p₀.2 <;> simp_all

/-- A flag pair has no branch on a tail exactly when it is not the node of the tail. -/
theorem fst_ne_and_snd_ne_iff_of_tail (htail : ∀ p, (flagPoint d p).1 = v ↔ p = p₀)
    (f : Flag) :
    d.fst f ≠ v ∧ d.snd f ≠ v ↔ f ≠ p₀.1 := by
  have hp₀ := (htail p₀).mpr rfl
  constructor
  · rintro ⟨h₁, h₂⟩ rfl
    obtain ⟨f, _ | _⟩ := p₀
    · exact h₁ (by simpa [fstPoint_def] using hp₀)
    · exact h₂ (by simpa [sndPoint_def] using hp₀)
  · intro hf
    refine ⟨fun h ↦ hf ?_, fun h ↦ hf ?_⟩
    · exact congrArg Prod.fst ((htail (f, false)).mp (by simpa [fstPoint_def] using h))
    · exact congrArg Prod.fst ((htail (f, true)).mp (by simpa [sndPoint_def] using h))

/-- The attaching point of a tail, as a point of the normalization of the contracted curve. -/
def attachPoint (d : FlagPairData ι Flag X) (htail : ∀ p, (flagPoint d p).1 = v ↔ p = p₀) :
    Σ i : {i // i ≠ v}, X i :=
  ⟨⟨(flagPoint d (p₀.1, !p₀.2)).1, fst_flagPoint_ne_of_tail htail⟩,
    (flagPoint d (p₀.1, !p₀.2)).2⟩

variable (htail : ∀ p, (flagPoint d p).1 = v ↔ p = p₀)

/-- The attaching point of the contracted curve is the attaching point of the tail. -/
@[simp]
theorem sigmaMap_attachPoint :
    Sigma.map Subtype.val (fun _ ↦ id) (attachPoint d htail) = flagPoint d (p₀.1, !p₀.2) :=
  (rfl)

/-- The attaching point lies on the component of the other branch of the node of the tail. -/
@[simp]
theorem fst_attachPoint :
    (attachPoint d htail).1 = ⟨(flagPoint d (p₀.1, !p₀.2)).1, fst_flagPoint_ne_of_tail htail⟩ :=
  (rfl)

/-- **The node of a tail disappears.** The attaching point is not a flag point of the contracted
curve. -/
theorem attachPoint_notMem_flagPointSet_deleteComponent :
    attachPoint d htail ∉ flagPointSet (d.deleteComponent v) := by
  rw [flagPointSet_eq_range]
  rintro ⟨p, hp⟩
  have h := congrArg (Sigma.map Subtype.val fun _ ↦ id) hp
  rw [sigmaMap_flagPoint_deleteComponent, sigmaMap_attachPoint] at h
  have := congrArg Prod.fst (flagPoint_injective d h)
  exact (fst_ne_and_snd_ne_iff_of_tail htail p.1.val).mp p.1.property this

open scoped Classical in
/-- The point of the contracted normalization to which a point of `d` is sent: the attaching point
for a point of the tail, and the point itself otherwise. -/
private def collapse (x : Σ i, X i) : Σ i : {i // i ≠ v}, X i :=
  if h : x.1 = v then attachPoint d htail else ⟨⟨x.1, h⟩, x.2⟩

private theorem collapse_of_fst_eq {x : Σ i, X i} (hx : x.1 = v) :
    collapse htail x = attachPoint d htail :=
  dite_eq_left hx

private theorem collapse_sigmaMap (y : Σ i : {i // i ≠ v}, X i) :
    collapse htail (Sigma.map Subtype.val (fun _ ↦ id) y) = y :=
  dite_eq_right y.1.property

private theorem sigmaMap_collapse_of_fst_eq {x : Σ i, X i} (hx : x.1 = v) :
    Sigma.map Subtype.val (fun _ ↦ id) (collapse htail x) = flagPoint d (p₀.1, !p₀.2) := by
  rw [collapse_of_fst_eq htail hx, sigmaMap_attachPoint]

private theorem sigmaMap_collapse_of_fst_ne {x : Σ i, X i} (hx : x.1 ≠ v) :
    Sigma.map Subtype.val (fun _ ↦ id) (collapse htail x) = x := by
  rw [collapse, dite_eq_right hx]
  rfl

private theorem continuous_collapse [∀ i, TopologicalSpace (X i)] :
    Continuous (collapse htail) := by
  refine continuous_sigma_iff.mpr fun i ↦ ?_
  by_cases hi : i = v
  · subst hi
    have : (fun x : X i ↦ collapse htail ⟨i, x⟩) = fun _ ↦ attachPoint d htail :=
      funext fun _ ↦ collapse_of_fst_eq htail rfl
    rw [this]
    exact continuous_const
  · have : (fun x : X i ↦ collapse htail ⟨i, x⟩) =
        Sigma.mk (β := fun i : {i // i ≠ v} ↦ X i) ⟨i, hi⟩ :=
      funext fun x ↦ collapse_sigmaMap htail ⟨⟨i, hi⟩, x⟩
    rw [this]
    exact continuous_sigmaMk

/-- `collapse` sends the two points of every flag pair to glued points. -/
private theorem mk_collapse_fstPoint_eq (f : Flag) :
    Quotient.mk (gluedRelSetoid (d.deleteComponent v)) (collapse htail (fstPoint d f)) =
      Quotient.mk _ (collapse htail (sndPoint d f)) := by
  have hp₀ := (htail p₀).mpr rfl
  by_cases hf : f = p₀.1
  · -- The node of the tail: one branch is on the tail and the other is the attaching point.
    subst hf
    obtain ⟨f, b⟩ := p₀
    have hq : collapse htail (flagPoint d (f, !b)) = attachPoint d htail := by
      rw [← sigmaMap_attachPoint htail, collapse_sigmaMap]
    cases b
    · simp only [Bool.not_false, flagPoint_true] at hq
      rw [hq, collapse_of_fst_eq htail (by simpa using hp₀)]
    · simp only [Bool.not_true, flagPoint_false] at hq
      rw [hq, collapse_of_fst_eq htail (by simpa using hp₀)]
  · -- Any other node is a node of the contracted curve.
    have hf' := (fst_ne_and_snd_ne_iff_of_tail htail f).mpr hf
    have h₁ : collapse htail (fstPoint d f) = fstPoint (d.deleteComponent v) ⟨f, hf'⟩ := by
      rw [← flagPoint_false, ← flagPoint_false, ← collapse_sigmaMap htail (flagPoint _ _),
        sigmaMap_flagPoint_deleteComponent]
    have h₂ : collapse htail (sndPoint d f) = sndPoint (d.deleteComponent v) ⟨f, hf'⟩ := by
      rw [← flagPoint_true, ← flagPoint_true, ← collapse_sigmaMap htail (flagPoint _ _),
        sigmaMap_flagPoint_deleteComponent]
    rw [h₁, h₂, mk_fstPoint, mk_sndPoint]

variable (d) in
/-- **Contracting a tail.** The map from the glued curve `d` to the glued curve with the tail `X v`
deleted, collapsing the whole tail onto its attaching point and the identity on the other
points. -/
def contractTailMap : GluedCurve d → GluedCurve (d.deleteComponent v) :=
  GluedCurve.lift d (fun x ↦ Quotient.mk _ (collapse htail x))
    (mk_collapse_fstPoint_eq htail)

/-- The contraction is the identity off the tail. -/
@[simp]
theorem contractTailMap_mk_sigmaMap (y : Σ i : {i // i ≠ v}, X i) :
    contractTailMap d htail (Quotient.mk _ (Sigma.map Subtype.val (fun _ ↦ id) y)) =
      Quotient.mk _ y := by
  rw [contractTailMap, GluedCurve.lift_mk, collapse_sigmaMap]

/-- The contraction sends every point of the tail to the attaching point. -/
@[simp]
theorem contractTailMap_mk_of_fst_eq {x : Σ i, X i} (hx : x.1 = v) :
    contractTailMap d htail (Quotient.mk _ x) = Quotient.mk _ (attachPoint d htail) := by
  rw [contractTailMap, GluedCurve.lift_mk, collapse_of_fst_eq htail hx]

/-- The contraction is continuous. -/
theorem continuous_contractTailMap [∀ i, TopologicalSpace (X i)] :
    Continuous (contractTailMap d htail) :=
  GluedCurve.continuous_lift _ _ _ (continuous_quotient_mk'.comp (continuous_collapse htail))

/-- The contraction is surjective. -/
theorem contractTailMap_surjective : Function.Surjective (contractTailMap d htail) := by
  rintro ⟨y⟩
  exact ⟨Quotient.mk _ (Sigma.map Subtype.val (fun _ ↦ id) y),
    contractTailMap_mk_sigmaMap htail y⟩

/-- **The node of a tail disappears.** The image of the tail is not a node of the contracted
curve. -/
theorem mk_attachPoint_notMem_nodeSet_deleteComponent :
    Quotient.mk _ (attachPoint d htail) ∉ nodeSet (d.deleteComponent v) := by
  rw [← mem_preimage, preimage_nodeSet]
  exact attachPoint_notMem_flagPointSet_deleteComponent htail

include htail in
/-- **Contracting a tail of a connected curve gives a connected curve.** -/
theorem connectedSpace_gluedCurve_deleteComponent_of_tail [∀ i, TopologicalSpace (X i)]
    [ConnectedSpace (GluedCurve d)] : ConnectedSpace (GluedCurve (d.deleteComponent v)) :=
  (contractTailMap_surjective htail).connectedSpace (continuous_contractTailMap htail)

include htail in
/-- A point of the normalization lies over the image of the tail in the glued curve exactly when
it lies on the tail or is the attaching point. -/
theorem mk_mem_range_iff_of_tail (x : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d) x ∈ range (fun y : X v ↦ Quotient.mk _ ⟨v, y⟩) ↔
      x.1 = v ∨ x = flagPoint d (p₀.1, !p₀.2) := by
  have hp₀ := (htail p₀).mpr rfl
  have hmem (z : Σ i, X i) (hz : z.1 = v) :
      Quotient.mk (gluedRelSetoid d) z ∈ range (fun y : X v ↦ Quotient.mk _ ⟨v, y⟩) := by
    obtain ⟨i, z⟩ := z
    subst hz
    exact ⟨z, rfl⟩
  constructor
  · rintro ⟨y, hy⟩
    rcases (gluedRel_def d _ _).mp ((gluedRelSetoid_r d _ _).mp (Quotient.exact hy)) with h | h
    · exact .inl (congrArg Sigma.fst h).symm
    · -- A point glued to a point of the tail is the attaching point.
      have hv := (mem_flagPointSet_iff_exists_flagRel d _).mpr ⟨x, h⟩
      rw [flagPointSet_eq_range] at hv
      obtain ⟨p, hp⟩ := hv
      obtain rfl := (htail p).mp (by rw [hp])
      rw [← hp] at h
      have hx := (mem_flagPointSet_iff_exists_flagRel d _).mpr ⟨_, flagRel_symm d h⟩
      rw [flagPointSet_eq_range] at hx
      obtain ⟨q, rfl⟩ := hx
      exact .inr (by rw [(flagRel_flagPoint_iff d _ _).mp h])
  · rintro (h | rfl)
    · exact hmem x h
    · simpa only [mk_flagPoint] using hmem (flagPoint d p₀) hp₀

/-- A point lies over the image of the tail exactly when `collapse` sends it to the attaching
point. -/
private theorem mk_mem_range_iff_sigmaMap_collapse (z : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d) z ∈ range (fun y : X v ↦ Quotient.mk _ ⟨v, y⟩) ↔
      Sigma.map Subtype.val (fun _ ↦ id) (collapse htail z) = flagPoint d (p₀.1, !p₀.2) := by
  rw [mk_mem_range_iff_of_tail htail]
  by_cases h : z.1 = v
  · simp [h, sigmaMap_collapse_of_fst_eq htail h]
  · simp [h, sigmaMap_collapse_of_fst_ne htail h]

/-- **The contraction collapses exactly the tail.** Two points of the glued curve have the same
image exactly when they are equal or both lie on the tail. -/
theorem contractTailMap_eq_contractTailMap_iff (a b : GluedCurve d) :
    contractTailMap d htail a = contractTailMap d htail b ↔
      a = b ∨ (a ∈ range (fun y : X v ↦ Quotient.mk _ ⟨v, y⟩) ∧
        b ∈ range (fun y : X v ↦ Quotient.mk _ ⟨v, y⟩)) := by
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  set K := range (fun y : X v ↦ Quotient.mk (gluedRelSetoid d) ⟨v, y⟩)
  have hK := mk_mem_range_iff_sigmaMap_collapse htail
  have hoff (z : Σ i, X i) (hz : Quotient.mk _ z ∉ K) :
      Sigma.map Subtype.val (fun _ ↦ id) (collapse htail z) = z :=
    sigmaMap_collapse_of_fst_ne htail fun h ↦ hz ((mk_mem_range_iff_of_tail htail z).mpr (.inl h))
  have hatt : Quotient.mk (gluedRelSetoid d) (flagPoint d (p₀.1, !p₀.2)) ∈ K :=
    (mk_mem_range_iff_of_tail htail _).mpr (.inr rfl)
  rw [contractTailMap, GluedCurve.lift_mk, GluedCurve.lift_mk, Quotient.eq, gluedRelSetoid_r,
    gluedRel_deleteComponent_iff, ← gluedRelSetoid_r, ← Quotient.eq]
  by_cases hx : Quotient.mk (gluedRelSetoid d) x ∈ K <;>
    by_cases hy : Quotient.mk (gluedRelSetoid d) y ∈ K
  · simp [(hK x).mp hx, (hK y).mp hy, hx, hy]
  · -- Only `x` lies over the tail: `y` is not glued to the attaching point.
    rw [(hK x).mp hx, hoff y hy]
    exact iff_of_false (fun h ↦ hy (h ▸ hatt)) fun h ↦ h.elim (fun h ↦ hy (h ▸ hx)) fun h ↦ hy h.2
  · -- Only `y` lies over the tail.
    rw [(hK y).mp hy, hoff x hx]
    exact iff_of_false (fun h ↦ hx (h ▸ hatt)) fun h ↦ h.elim (fun h ↦ hx (h ▸ hy)) fun h ↦ hx h.1
  · rw [hoff x hx, hoff y hy]
    simp [hx]

/-- **The contracted curve is the quotient collapsing the tail.** The contraction is a quotient
map. -/
theorem isQuotientMap_contractTailMap [∀ i, TopologicalSpace (X i)] :
    IsQuotientMap (contractTailMap d htail) := by
  refine .of_comp (f := Quotient.mk _ ∘ Sigma.map Subtype.val fun (i : {i // i ≠ v}) ↦
      (id : X i → X i)) (continuous_quotient_mk'.comp (Continuous.sigma_map fun _ ↦ continuous_id))
    (continuous_contractTailMap htail) ?_
  convert isQuotientMap_quotient_mk' (s := gluedRelSetoid (d.deleteComponent v))
  exact funext (contractTailMap_mk_sigmaMap htail)

/-! ### Moving the marks -/

variable {L : Type*} (m : Marking d L)

/-- **The marks of the contracted curve.** A mark on the tail moves to the attaching point, and the
other marks stay where they are. At most one mark may lie on the tail. -/
def Marking.contractTail (hm : {l | (m.point l).1 = v}.Subsingleton) :
    Marking (d.deleteComponent v) L where
  point l := collapse htail (m.point l)
  point_injective l l' h := by
    have h' := congrArg (Sigma.map Subtype.val fun _ ↦ id) h
    have hq (l : L) : m.point l ≠ flagPoint d (p₀.1, !p₀.2) := fun h ↦
      m.point_notMem_flagPointSet l (by rw [flagPointSet_eq_range]; exact ⟨_, h.symm⟩)
    by_cases hl : (m.point l).1 = v <;> by_cases hl' : (m.point l').1 = v
    · exact hm hl hl'
    · rw [sigmaMap_collapse_of_fst_eq htail hl, sigmaMap_collapse_of_fst_ne htail hl'] at h'
      exact absurd h'.symm (hq l')
    · rw [sigmaMap_collapse_of_fst_ne htail hl, sigmaMap_collapse_of_fst_eq htail hl'] at h'
      exact absurd h' (hq l)
    · rw [sigmaMap_collapse_of_fst_ne htail hl, sigmaMap_collapse_of_fst_ne htail hl'] at h'
      exact m.point_injective h'
  point_notMem_flagPointSet l := by
    by_cases hl : (m.point l).1 = v
    · rw [collapse_of_fst_eq htail hl]
      exact attachPoint_notMem_flagPointSet_deleteComponent htail
    · rw [flagPointSet_eq_range]
      rintro ⟨p, hp⟩
      have h := congrArg (Sigma.map Subtype.val fun _ ↦ id) hp
      rw [sigmaMap_flagPoint_deleteComponent, sigmaMap_collapse_of_fst_ne htail hl] at h
      exact m.point_notMem_flagPointSet l (by rw [flagPointSet_eq_range]; exact ⟨_, h⟩)

variable (hm : {l | (m.point l).1 = v}.Subsingleton)

/-- The marks of the contracted curve are the images of the marks under `collapse`. -/
private theorem point_contractTail (l : L) :
    (m.contractTail htail hm).point l = collapse htail (m.point l) :=
  rfl

/-- A mark on the tail moves to the attaching point. -/
@[simp]
theorem Marking.point_contractTail_of_fst_eq {l : L} (hl : (m.point l).1 = v) :
    (m.contractTail htail hm).point l = attachPoint d htail := by
  rw [point_contractTail, collapse_of_fst_eq htail hl]

/-- A mark off the tail stays where it is. -/
@[simp]
theorem Marking.sigmaMap_point_contractTail_of_fst_ne {l : L} (hl : (m.point l).1 ≠ v) :
    Sigma.map Subtype.val (fun _ ↦ id) ((m.contractTail htail hm).point l) = m.point l := by
  rw [point_contractTail, sigmaMap_collapse_of_fst_ne htail hl]

/-- A mark off the tail stays where it is, as a point of the contracted normalization. -/
theorem Marking.point_contractTail_of_fst_ne {l : L} (hl : (m.point l).1 ≠ v) :
    (m.contractTail htail hm).point l = ⟨⟨(m.point l).1, hl⟩, (m.point l).2⟩ := by
  rw [point_contractTail, collapse, dite_eq_right hl]

/-- **The contraction carries the marks to the marks.** -/
@[simp]
theorem contractTailMap_mk_point (l : L) :
    contractTailMap d htail (Quotient.mk _ (m.point l)) =
      Quotient.mk _ ((m.contractTail htail hm).point l) := by
  rw [contractTailMap, GluedCurve.lift_mk, point_contractTail]

end Tail

/-! ### The dual graph of the contracted curve -/

section DualGraph

universe u

variable {ι Flag : Type u} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, ConnectedSpace (X i)] {d : FlagPairData ι Flag X} [ConnectedSpace (GluedCurve d)]
  [Fintype ι] [DecidableEq ι] [Fintype Flag] [DecidableEq Flag] {L : Type*}
  (g : ι → ℕ) (m : Marking d L)

variable {v : ι} {p₀ : Flag × Bool} (htail : ∀ p, (flagPoint d p).1 = v ↔ p = p₀)

include htail in
/-- **A tail has valence one** in the dual graph. -/
theorem valence_dualGraph_of_tail : (dualGraph g m).valence v = 1 := by
  rw [valence_dualGraph, flagPointSet_eq_range,
    ncard_preimage_sigmaMk_range (flagPoint_injective d)]
  simp [htail]

/-- The tail is the endpoint of its node selected by its branch, and the attaching point lies on
the other endpoint. -/
theorem attachment_dualGraph_of_tail :
    (dualGraph g m).attachment (valence_dualGraph_of_tail g m htail) =
      (flagPoint d (p₀.1, !p₀.2)).1 := by
  have hp₀ := (htail p₀).mpr rfl
  obtain ⟨f, b⟩ := p₀
  cases b
  · refine (DualGraph.endpoint_rev_eq_attachment (e := f) (i := 0) _ ?_).symm.trans
      (by simp [sndPoint_def])
    simpa [fstPoint_def] using hp₀
  · refine (DualGraph.endpoint_rev_eq_attachment (e := f) (i := 1) _ ?_).symm.trans
      (by simp [fstPoint_def])
    simpa [sndPoint_def] using hp₀

/-- **The dual graph of the contracted curve is the contracted dual graph.** The isomorphism is
the identity on the remaining components and on the remaining flag pairs. -/
def dualGraphContractTailIso (hm : {l | (m.point l).1 = v}.Subsingleton) :
    (haveI := connectedSpace_gluedCurve_deleteComponent_of_tail htail;
      dualGraph (fun i : {i // i ≠ v} ↦ g i) (m.contractTail htail hm)).Iso
      ((dualGraph g m).contractTail (valence_dualGraph_of_tail g m htail)) where
  vertexEquiv := .refl _
  edgeEquiv := Equiv.subtypeEquivRight fun f ↦ by simp [Fin.forall_fin_two]
  ends_edgeEquiv e := by
    simp [DualGraph.ends_def]
  genus_vertexEquiv _ := rfl
  vertexEquiv_marking l := by
    have := connectedSpace_gluedCurve_deleteComponent_of_tail htail
    rw [Equiv.refl_apply, DualGraph.marking_contractTail, marking_dualGraph, marking_dualGraph]
    by_cases hl : (m.point l).1 = v
    · rw [dite_eq_left hl, Marking.point_contractTail_of_fst_eq htail m hm hl]
      exact Subtype.ext (attachment_dualGraph_of_tail g m htail).symm
    · rw [dite_eq_right hl]
      exact Subtype.ext (congrArg Sigma.fst
        (Marking.sigmaMap_point_contractTail_of_fst_ne htail m hm hl))

/-- The comparison of dual graphs is the identity on the remaining components. -/
@[simp]
theorem dualGraphContractTailIso_vertexEquiv (hm : {l | (m.point l).1 = v}.Subsingleton) :
    (dualGraphContractTailIso g m htail hm).vertexEquiv = .refl _ :=
  (rfl)

/-- The comparison of dual graphs is the identity on the remaining flag pairs. -/
@[simp]
theorem coe_dualGraphContractTailIso_edgeEquiv_apply (hm : {l | (m.point l).1 = v}.Subsingleton)
    (f : {f : Flag // d.fst f ≠ v ∧ d.snd f ≠ v}) :
    ((dualGraphContractTailIso g m htail hm).edgeEquiv f : Flag) = f :=
  (rfl)

/-- The inverse comparison of dual graphs is the identity on the remaining flag pairs. -/
@[simp]
theorem coe_dualGraphContractTailIso_edgeEquiv_symm_apply
    (hm : {l | (m.point l).1 = v}.Subsingleton)
    (e : ((dualGraph g m).contractTail (valence_dualGraph_of_tail g m htail)).Edge) :
    ((dualGraphContractTailIso g m htail hm).edgeEquiv.symm e : Flag) = e :=
  (rfl)

/-- **Contracting a tail lowers the arithmetic genus by the genus of the tail.** -/
theorem arithmeticGenus_dualGraph_contractTail (hm : {l | (m.point l).1 = v}.Subsingleton) :
    (haveI := connectedSpace_gluedCurve_deleteComponent_of_tail htail;
      dualGraph (fun i : {i // i ≠ v} ↦ g i) (m.contractTail htail hm)).arithmeticGenus +
        g v = (dualGraph g m).arithmeticGenus := by
  rw [(dualGraphContractTailIso g m htail hm).arithmeticGenus_eq]
  exact DualGraph.arithmeticGenus_contractTail _

/-- **Forgetting a mark and contracting a rational tail preserves stability.** If the dual graph of
the curve with marks labelled by `Option L` is stable, forgetting the mark `none` and contracting a
tail of genus label zero carrying at most one of the remaining marks gives a curve whose dual graph,
with the restricted genus labels, is stable. -/
theorem isStable_dualGraph_contractTail_reindex_some [Fintype L] {m : Marking d (Option L)}
    (hG : (dualGraph g m).IsStable) (hg : g v = 0)
    (hm : {l | ((m.reindex .some).point l).1 = v}.Subsingleton) :
    (haveI := connectedSpace_gluedCurve_deleteComponent_of_tail htail;
      dualGraph (fun i : {i // i ≠ v} ↦ g i)
        ((m.reindex .some).contractTail htail hm)).IsStable := by
  rw [(dualGraphContractTailIso g _ htail hm).isStable_iff]
  have hnum : ((dualGraph g m).reindex .some).numMarkings v ≤ 1 := by
    rw [DualGraph.numMarkings_def]
    exact Finset.card_le_one.mpr fun a ha b hb ↦ hm (by simpa using ha) (by simpa using hb)
  have hv : ((dualGraph g m).reindex .some).IsRationalTail v :=
    (DualGraph.isRationalTail_iff _).mpr ⟨hg, by simpa using valence_dualGraph_of_tail g m htail⟩
  -- The dual graph of the curve with `none` forgotten is the dual graph with `none` forgotten.
  convert hG.isStable_of_stabilizationStep_reindex_some (.contractTail _ hv hnum) using 2
  rw [dualGraph_reindex, Function.Embedding.some_apply]

end DualGraph

end NodalGluing

end TauCeti
