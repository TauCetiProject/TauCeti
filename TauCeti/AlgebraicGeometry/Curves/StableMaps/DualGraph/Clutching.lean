/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Clutching
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Basic

/-!
# Gluing degree-decorated dual graphs

Stable maps to a common target are glued along markings with equal evaluations, in the same two
ways as pointed curves. **External gluing** identifies a marking `a` of a map of type
`(g₁, I ⊔ {a}, d₁)` with a marking `b` of a map of type `(g₂, J ⊔ {b}, d₂)`, giving a map of type
`(g₁ + g₂, I ⊔ J, d₁ + d₂)`. **Self-gluing** identifies two markings of a map of type
`(g, I ⊔ {a, b}, d)`, giving a map of type `(g + 1, I, d)`. In both cases the glued map restricts
to the input maps on the components of the input curves, so the component degrees are unchanged.

This file describes the effect of both operations on dual graphs decorated by component degrees.
The underlying graphs are glued by `TauCeti.DualGraph.clutch` and `TauCeti.DualGraph.selfClutch`,
and the decorations are carried along unchanged. Since clutching also preserves every
log-canonical degree, it preserves every weighted log-canonical degree, so a glued decorated graph
is stable exactly when its inputs are. Every decoration of a clutched graph arises from a unique
decoration of its inputs.

## Main definitions

* `TauCeti.DualGraph.DegreeDecoration.clutch`: the decoration of an externally clutched graph
  that restricts to given decorations on both halves.
* `TauCeti.DualGraph.DegreeDecoration.selfClutch`: the decoration of a self-clutched graph with
  the same component degrees.
* `TauCeti.DualGraph.DegreeDecoration.clutchAddEquiv` and
  `TauCeti.DualGraph.DegreeDecoration.selfClutchAddEquiv`: decorations of a clutched graph are
  decorations of its inputs.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.totalDegree_clutch`: external gluing adds the total
  degrees.
* `TauCeti.DualGraph.DegreeDecoration.totalDegree_selfClutch`: self-gluing preserves the total
  degree.
* `TauCeti.DualGraph.DegreeDecoration.isStable_clutch_iff` and
  `TauCeti.DualGraph.DegreeDecoration.isStable_selfClutch_iff`: a glued decorated graph is stable
  exactly when its inputs are.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov--Witten invariants*, Duke Math. J.
  85 (1996), 1--60, Sections 1 and 2, for modular graphs of stable maps and their gluing.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161--199, §3, for the clutching morphisms.
-/

public section

namespace TauCeti

namespace DualGraph

namespace DegreeDecoration

universe u u₁ u₂ v w

variable {ι : Type v} {κ : Type w}

/-! ### External gluing -/

section External

variable {G₁ : DualGraph.{u₁} (Option ι)} {G₂ : DualGraph.{u₂} (Option κ)}
  (D₁ D₁' : G₁.DegreeDecoration) (D₂ D₂' : G₂.DegreeDecoration)

/-- The degree decoration of an externally clutched graph whose component degrees are those of
`D₁` on the components of `G₁` and those of `D₂` on the components of `G₂`. -/
def clutch : (G₁.clutch G₂).DegreeDecoration :=
  ⟨Sum.elim D₁.componentDegree D₂.componentDegree⟩

@[simp]
lemma componentDegree_clutch_inl (v : G₁.Vertex) :
    (D₁.clutch D₂).componentDegree (.inl v) = D₁.componentDegree v :=
  (rfl)

@[simp]
lemma componentDegree_clutch_inr (v : G₂.Vertex) :
    (D₁.clutch D₂).componentDegree (.inr v) = D₂.componentDegree v :=
  (rfl)

/-- A decoration of an externally clutched graph is determined by its restrictions to the two
halves. -/
@[simp]
theorem clutch_inj : D₁.clutch D₂ = D₁'.clutch D₂' ↔ D₁ = D₁' ∧ D₂ = D₂' := by
  simp only [DegreeDecoration.ext_iff, funext_iff, Sum.forall, componentDegree_clutch_inl,
    componentDegree_clutch_inr]

/-- Gluing two constant maps gives a constant map. -/
@[simp]
lemma clutch_zero : (0 : G₁.DegreeDecoration).clutch (0 : G₂.DegreeDecoration) = 0 :=
  DegreeDecoration.ext <| funext <| Sum.rec (fun _ ↦ rfl) fun _ ↦ rfl

@[simp]
lemma clutch_add : (D₁ + D₁').clutch (D₂ + D₂') = D₁.clutch D₂ + D₁'.clutch D₂' :=
  DegreeDecoration.ext <| funext <| Sum.rec (fun _ ↦ rfl) fun _ ↦ rfl

@[simp]
lemma clutch_smul (m : ℕ) : (m • D₁).clutch (m • D₂) = m • D₁.clutch D₂ :=
  DegreeDecoration.ext <| funext <| Sum.rec (fun _ ↦ rfl) fun _ ↦ rfl

variable (G₁ G₂) in
/-- Decorations of an externally clutched graph are exactly pairs of decorations of the two
halves. -/
def clutchAddEquiv :
    G₁.DegreeDecoration × G₂.DegreeDecoration ≃+ (G₁.clutch G₂).DegreeDecoration where
  toFun D := D.1.clutch D.2
  invFun D := (⟨fun v ↦ D.componentDegree (.inl v)⟩, ⟨fun v ↦ D.componentDegree (.inr v)⟩)
  left_inv _ := rfl
  right_inv _ := DegreeDecoration.ext <| funext <| Sum.rec (fun _ ↦ rfl) fun _ ↦ rfl
  map_add' D D' := clutch_add D.1 D'.1 D.2 D'.2

@[simp]
lemma clutchAddEquiv_apply (D : G₁.DegreeDecoration × G₂.DegreeDecoration) :
    clutchAddEquiv G₁ G₂ D = D.1.clutch D.2 :=
  (rfl)

@[simp]
lemma componentDegree_clutchAddEquiv_symm_apply_fst (D : (G₁.clutch G₂).DegreeDecoration)
    (v : G₁.Vertex) :
    ((clutchAddEquiv G₁ G₂).symm D).1.componentDegree v = D.componentDegree (.inl v) :=
  (rfl)

@[simp]
lemma componentDegree_clutchAddEquiv_symm_apply_snd (D : (G₁.clutch G₂).DegreeDecoration)
    (v : G₂.Vertex) :
    ((clutchAddEquiv G₁ G₂).symm D).2.componentDegree v = D.componentDegree (.inr v) :=
  (rfl)

/-- External gluing adds the total degrees. -/
@[simp]
theorem totalDegree_clutch : (D₁.clutch D₂).totalDegree = D₁.totalDegree + D₂.totalDegree := by
  simp only [totalDegree_def, Fintype.sum_sum_type, componentDegree_clutch_inl,
    componentDegree_clutch_inr]

variable [Fintype ι] [Fintype κ]

/-- External gluing preserves the weighted log-canonical degree of every component of the first
input. -/
@[simp]
theorem weightedLogCanonicalDegree_clutch_inl (v : G₁.Vertex) :
    (D₁.clutch D₂).weightedLogCanonicalDegree (.inl v) = D₁.weightedLogCanonicalDegree v := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_clutch_inl, componentDegree_clutch_inl]

/-- External gluing preserves the weighted log-canonical degree of every component of the second
input. -/
@[simp]
theorem weightedLogCanonicalDegree_clutch_inr (v : G₂.Vertex) :
    (D₁.clutch D₂).weightedLogCanonicalDegree (.inr v) = D₂.weightedLogCanonicalDegree v := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_clutch_inr, componentDegree_clutch_inr]

/-- An externally glued decorated graph is stable exactly when both of its inputs are. -/
@[simp]
theorem isStable_clutch_iff : (D₁.clutch D₂).IsStable ↔ D₁.IsStable ∧ D₂.IsStable := by
  simp only [isStable_iff_weightedLogCanonicalDegree_pos, Sum.forall,
    weightedLogCanonicalDegree_clutch_inl, weightedLogCanonicalDegree_clutch_inr]

end External

/-! ### Self-gluing -/

section Self

variable {G : DualGraph.{u} (ι ⊕ Fin 2)} (D D' : G.DegreeDecoration)

/-- The degree decoration of a self-clutched graph with the same component degrees as `D`. -/
def selfClutch : G.selfClutch.DegreeDecoration :=
  ⟨D.componentDegree⟩

@[simp]
lemma componentDegree_selfClutch (v : G.Vertex) :
    D.selfClutch.componentDegree v = D.componentDegree v :=
  (rfl)

/-- A decoration of a self-clutched graph is determined by the component degrees of its input. -/
@[simp]
theorem selfClutch_inj : D.selfClutch = D'.selfClutch ↔ D = D' := by
  simp only [DegreeDecoration.ext_iff, funext_iff, componentDegree_selfClutch]

/-- Self-gluing a constant map gives a constant map. -/
@[simp]
lemma selfClutch_zero : (0 : G.DegreeDecoration).selfClutch = 0 :=
  (rfl)

@[simp]
lemma selfClutch_add : (D + D').selfClutch = D.selfClutch + D'.selfClutch :=
  (rfl)

@[simp]
lemma selfClutch_smul (m : ℕ) : (m • D).selfClutch = m • D.selfClutch :=
  (rfl)

variable (G) in
/-- Decorations of a self-clutched graph are exactly decorations of its input. -/
def selfClutchAddEquiv : G.DegreeDecoration ≃+ G.selfClutch.DegreeDecoration where
  toFun D := D.selfClutch
  invFun D := ⟨D.componentDegree⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := selfClutch_add

@[simp]
lemma selfClutchAddEquiv_apply : selfClutchAddEquiv G D = D.selfClutch :=
  (rfl)

@[simp]
lemma componentDegree_selfClutchAddEquiv_symm_apply (D : G.selfClutch.DegreeDecoration)
    (v : G.Vertex) :
    ((selfClutchAddEquiv G).symm D).componentDegree v = D.componentDegree v :=
  (rfl)

/-- Self-gluing preserves the total degree. -/
@[simp]
theorem totalDegree_selfClutch : D.selfClutch.totalDegree = D.totalDegree := by
  simp only [totalDegree_def, componentDegree_selfClutch]

variable [Fintype ι]

/-- Self-gluing preserves every weighted log-canonical degree. -/
@[simp]
theorem weightedLogCanonicalDegree_selfClutch (v : G.Vertex) :
    D.selfClutch.weightedLogCanonicalDegree v = D.weightedLogCanonicalDegree v := by
  rw [weightedLogCanonicalDegree_def, weightedLogCanonicalDegree_def,
    logCanonicalDegree_selfClutch, componentDegree_selfClutch]

/-- A self-glued decorated graph is stable exactly when its input is. -/
@[simp]
theorem isStable_selfClutch_iff : D.selfClutch.IsStable ↔ D.IsStable := by
  simp only [isStable_iff_weightedLogCanonicalDegree_pos, weightedLogCanonicalDegree_selfClutch]

end Self

end DegreeDecoration

end DualGraph

end TauCeti
