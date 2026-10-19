/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.Combinatorics.Brauer.LoopCount

/-!
# Labellings of Brauer diagrams that are constant on arcs

Label the boundary points of a Brauer diagram `D` on `k` strands by elements of a type `ι`: a
bottom labelling `u : Fin k → ι` and a top labelling `v : Fin k → ι`, assembled into
`Sum.elim u v`. The labelling is **constant on arcs** (`TauCeti.BrauerDiagram.IsConstantOnArcs`)
when the two endpoints of every arc carry the same label. These are the matrix entries of the
action of the Brauer algebra on the tensor power of `V = ι → R` with its standard symmetric form:
the coefficient of the output basis tensor `v` in the image of the input basis tensor `u` under `D`
is `1` when `Sum.elim u v` is constant on the arcs of `D`, and `0` otherwise. A cap of `D`
contracts two input slots through the form, which pairs equal coordinates; a cup expands two
output slots through the copairing `∑ c, e_c ⊗ e_c`; and a through strand copies a coordinate.

The point of this file is that these entries multiply according to the loop rule of the Brauer
algebra. Stack `D₁` above `D₂`, with bottom labels `u` and top labels `v`, and count the labellings
`m` of the middle boundary for which both `Sum.elim m v` is constant on the arcs of `D₁` and
`Sum.elim u m` on the arcs of `D₂`. There is such a middle labelling only if `Sum.elim u v` is
constant on the arcs of the composite `TauCeti.composeDiagram D₁ D₂`, since a label is carried
unchanged along each strand of the stack (`TauCeti.BrauerDiagram.IsConstantOnArcs.composeDiagram`).
Conversely, when it is, the middle labels on the strands are forced while the label on each closed
middle loop is free, so there are exactly `|ι| ^ c` of them with `c = TauCeti.middleLoopCount D₁ D₂`
(`TauCeti.BrauerDiagram.natCard_middleLabelling`). That is the identity
`M(D₁) * M(D₂) = |ι| ^ c • M(D₁ ∘ D₂)` for the matrices of the action, which makes it an action of
the Brauer algebra `B_k(|ι|)`.

## Main definitions

* `TauCeti.BrauerDiagram.IsConstantOnArcs`: a labelling of the boundary points is constant on the
  arcs of a diagram.

## Main results

* `TauCeti.BrauerDiagram.isConstantOnArcs_permToBrauer_iff`: the labellings constant on the arcs
  of a permutation diagram are those whose top labels are the bottom labels moved along the
  permutation.
* `TauCeti.BrauerDiagram.isConstantOnArcs_capCup_iff`: the labellings constant on the arcs of a
  cap-cup diagram.
* `TauCeti.BrauerDiagram.IsConstantOnArcs.composeDiagram`: a labelling of a stack constant on the
  arcs of both diagrams restricts to the outer boundary as a labelling constant on the arcs of the
  composite.
* `TauCeti.BrauerDiagram.natCard_middleLabelling`: **the loop rule for labellings**; given a
  labelling of the outer boundary constant on the arcs of the composite, its extensions to the
  middle boundary number `|ι| ^ middleLoopCount D₁ D₂`.

## Implementation notes

The count is proved by restricting a middle labelling to the least points of the closed middle
loops, the points counted by `TauCeti.middleLoopCount`. That restriction is injective because every
middle point off the loops is joined in the middle graph to a point carrying a through strand of
one of the two diagrams, whose label is the label of an outer point. It is surjective because those
forced labels are consistent: the middle points joined to the through strand at an outer point `y`
all lie on the strand of the stack that starts at `y`, so the outer points whose labels they are
forced to carry are `y` and the far end of that strand, which carry the same label once the outer
labelling is constant on the arcs of the composite. The strand is followed with
`TauCeti.stackStart` and `TauCeti.stackStep`, the walk through which
`TauCeti.composeDiagram_val_eq_iff` describes the composite.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

variable {k : ℕ} {ι : Type*}

namespace BrauerDiagram

/-- A labelling `ℓ` of the boundary points of the Brauer diagram `D` is **constant on arcs** when
the two endpoints of every arc of `D` carry the same label. -/
def IsConstantOnArcs (D : BrauerDiagram k) (ℓ : Fin k ⊕ Fin k → ι) : Prop :=
  ∀ x, ℓ (D.val x) = ℓ x

/-- A labelling is constant on arcs when it takes the same value at the two endpoints of every
arc. -/
theorem isConstantOnArcs_def (D : BrauerDiagram k) (ℓ : Fin k ⊕ Fin k → ι) :
    D.IsConstantOnArcs ℓ ↔ ∀ x, ℓ (D.val x) = ℓ x := Iff.rfl

instance [DecidableEq ι] (D : BrauerDiagram k) (ℓ : Fin k ⊕ Fin k → ι) :
    Decidable (D.IsConstantOnArcs ℓ) :=
  inferInstanceAs (Decidable (∀ x, ℓ (D.val x) = ℓ x))

/-- **Labellings of a permutation diagram.** A labelling is constant on the arcs of the diagram of
`σ` exactly when the top point `σ i` carries the label of the bottom point `i`. -/
theorem isConstantOnArcs_permToBrauer_iff (σ : Equiv.Perm (Fin k)) (u v : Fin k → ι) :
    (permToBrauer σ).IsConstantOnArcs (Sum.elim u v) ↔ ∀ i, v (σ i) = u i := by
  refine ⟨fun h i => by simpa using h (Sum.inl i), fun h x => ?_⟩
  rcases x with i | j
  · simpa using h i
  · simpa using (h (σ.symm j)).symm

/-- **Labellings of a cap-cup diagram.** A labelling is constant on the arcs of `capCup a b`
exactly when the two capped bottom points carry the same label, the two cupped top points carry
the same label, and every other top point carries the label of the bottom point below it. -/
theorem isConstantOnArcs_capCup_iff {a b : Fin k} (hab : a ≠ b) (u v : Fin k → ι) :
    (capCup a b).IsConstantOnArcs (Sum.elim u v) ↔
      u a = u b ∧ v a = v b ∧ ∀ i, i ≠ a → i ≠ b → v i = u i := by
  refine ⟨fun h => ⟨?_, ?_, fun i hia hib => ?_⟩, fun ⟨hu, hv, h⟩ x => ?_⟩
  · simpa [capCup_val_inl_left hab] using (h (Sum.inl a)).symm
  · simpa [capCup_val_inr_left hab] using (h (Sum.inr a)).symm
  · simpa [capCup_val_inl_of_ne hia hib] using h (Sum.inl i)
  · rcases x with i | i
    · rcases eq_or_ne i a with rfl | hia
      · simpa [capCup_val_inl_left hab] using hu.symm
      rcases eq_or_ne i b with rfl | hib
      · simpa [capCup_val_inl_right hab] using hu
      · simpa [capCup_val_inl_of_ne hia hib] using h i hia hib
    · rcases eq_or_ne i a with rfl | hia
      · simpa [capCup_val_inr_left hab] using hv.symm
      rcases eq_or_ne i b with rfl | hib
      · simpa [capCup_val_inr_right hab] using hv
      · simpa [capCup_val_inr_of_ne hia hib] using (h i hia hib).symm

/-! ### Labels are carried along the strands of a stack -/

section Stack

variable {D₁ D₂ : BrauerDiagram k} {u v m : Fin k → ι}

/-- The label of a point reached by `TauCeti.stackStart` or `TauCeti.stackStep`: an outer point
carries its outer label, and a middle state carries the label of its middle point. -/
private def stateLabel (u v m : Fin k → ι) : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → ι :=
  Sum.elim (Sum.elim u v) fun s => m (middlePoint s)

/-- The first arc of a strand carries the label of the outer point it starts at. -/
private theorem stateLabel_stackStart (h₁ : D₁.IsConstantOnArcs (Sum.elim m v))
    (h₂ : D₂.IsConstantOnArcs (Sum.elim u m)) (x : Fin k ⊕ Fin k) :
    stateLabel u v m (stackStart D₁ D₂ x) = Sum.elim u v x := by
  rcases x with i | j
  · have h := h₂ (Sum.inl i)
    rcases hD : D₂.val (Sum.inl i) with i' | a <;> simp_all [stateLabel]
  · have h := h₁ (Sum.inr j)
    rcases hD : D₁.val (Sum.inr j) with a | j' <;> simp_all [stateLabel]

/-- A later arc of a strand carries the label of the middle point it continues from. -/
private theorem stateLabel_stackStep (h₁ : D₁.IsConstantOnArcs (Sum.elim m v))
    (h₂ : D₂.IsConstantOnArcs (Sum.elim u m)) (s : Fin k ⊕ Fin k) :
    stateLabel u v m (stackStep D₁ D₂ s) = m (middlePoint s) := by
  rcases s with a | a
  · have h := h₁ (Sum.inl a)
    rcases hD : D₁.val (Sum.inl a) with a' | j <;> simp_all [stateLabel]
  · have h := h₂ (Sum.inr a)
    rcases hD : D₂.val (Sum.inr a) with i | a' <;> simp_all [stateLabel]

/-- **Labels are carried along strands.** If a labelling of the stack of `D₁` above `D₂` is
constant on the arcs of both diagrams, its restriction to the outer boundary is constant on the
arcs of the composite `TauCeti.composeDiagram D₁ D₂`: each strand carries one label from end to
end. -/
theorem IsConstantOnArcs.composeDiagram (h₁ : D₁.IsConstantOnArcs (Sum.elim m v))
    (h₂ : D₂.IsConstantOnArcs (Sum.elim u m)) :
    (composeDiagram D₁ D₂).IsConstantOnArcs (Sum.elim u v) := by
  intro x
  have hx := stateLabel_stackStart h₁ h₂ x
  rcases (composeDiagram_val_eq_iff D₁ D₂ (x := x)).mp rfl with h | ⟨s, t, hs, hst, ht⟩
  · rw [h] at hx
    exact hx
  · rw [hs] at hx
    have hmid : ∀ t, Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t →
        m (middlePoint t) = m (middlePoint s) := fun t hst => by
      induction hst with
      | refl => rfl
      | @tail b c _ hstep ih =>
        have := stateLabel_stackStep h₁ h₂ b
        rw [hstep] at this
        exact this.trans ih
    have hy := stateLabel_stackStep h₁ h₂ t
    rw [ht] at hy
    exact hy.trans ((hmid t hst).trans hx)

/-! ### Middle points with a through strand -/

/-- The outer point `z` is reached from the middle point `b` along a through strand: of `D₁` up
to the top point `z`, or of `D₂` down to the bottom point `z`. -/
private def IsAttach (D₁ D₂ : BrauerDiagram k) (b : Fin k) (z : Fin k ⊕ Fin k) : Prop :=
  (z.isRight ∧ D₁.val (Sum.inl b) = z) ∨ (z.isLeft ∧ D₂.val (Sum.inr b) = z)

/-- A middle point that does not keep both of its arcs in the middle has a through strand. -/
private theorem exists_isAttach {b : Fin k} (hb : ¬IsMiddleVertex D₁ D₂ b) :
    ∃ z, IsAttach D₁ D₂ b z := by
  rw [isMiddleVertex_def, isCap_def, isCup_def] at hb
  by_cases h : (D₁.val (Sum.inl b)).isLeft
  · refine ⟨D₂.val (Sum.inr b), Or.inr ⟨?_, rfl⟩⟩
    simpa [h] using hb
  · exact ⟨D₁.val (Sum.inl b), Or.inl ⟨by simpa using h, rfl⟩⟩

/-- A middle point with a through strand does not lie on a closed middle loop. -/
private theorem not_onMiddleLoop_of_isAttach {b : Fin k} {z : Fin k ⊕ Fin k}
    (hz : IsAttach D₁ D₂ b z) : ¬OnMiddleLoop D₁ D₂ b := by
  rcases hz with ⟨hz, h⟩ | ⟨hz, h⟩
  · exact not_onMiddleLoop_of_isThrough_left (by rcases z <;> simp_all [isThrough_def])
  · exact not_onMiddleLoop_of_isThrough_right (by rcases z <;> simp_all [isThrough_def])

/-- The strand of the stack that starts at the outer end `y` of a through strand at the middle
point `a` crosses the middle boundary at `a`. -/
private theorem exists_stackStart_eq_inr {a : Fin k} {y : Fin k ⊕ Fin k}
    (hy : IsAttach D₁ D₂ a y) : ∃ s, stackStart D₁ D₂ y = Sum.inr s ∧ middlePoint s = a := by
  rcases hy with ⟨hy, h⟩ | ⟨hy, h⟩
  · rcases y with i | j
    · simp at hy
    · exact ⟨Sum.inr a, by simp [D₁.apply_eq_of_apply_eq h], middlePoint_inr a⟩
  · rcases y with i | j
    · exact ⟨Sum.inl a, by simp [D₂.apply_eq_of_apply_eq h], middlePoint_inl a⟩
    · simp at hy

/-- The relation of following a strand from one middle state to the next. -/
private abbrev StackRel (D₁ D₂ : BrauerDiagram k) (s t : Fin k ⊕ Fin k) : Prop :=
  stackStep D₁ D₂ s = Sum.inr t

/-- **The ends of a strand.** A through strand at a middle point visited by the strand of the
stack starting at the outer point `y` leads back to `y` or on to the far end of that strand. -/
private theorem eq_or_composeDiagram_val_eq_of_isAttach {y : Fin k ⊕ Fin k}
    {s₀ s : Fin k ⊕ Fin k} (h₀ : stackStart D₁ D₂ y = Sum.inr s₀)
    (hs : Relation.ReflTransGen (StackRel D₁ D₂) s₀ s) {z : Fin k ⊕ Fin k}
    (hz : IsAttach D₁ D₂ (middlePoint s) z) : z = y ∨ (composeDiagram D₁ D₂).val y = z := by
  rcases hz with ⟨hz, h⟩ | ⟨hz, h⟩ <;> rcases z with i | j <;> simp at hz
  · exact eq_or_composeDiagram_val_eq_inr_of_reflTransGen_stackStep h₀ hs h
  · exact eq_or_composeDiagram_val_eq_inl_of_reflTransGen_stackStep h₀ hs h

/-- **The forced labels are consistent.** If the outer labelling is constant on the arcs of the
composite, then two through strands at middle points joined in the middle graph end at outer
points with the same label. -/
private theorem label_eq_of_isAttach (hC : (composeDiagram D₁ D₂).IsConstantOnArcs (Sum.elim u v))
    {a b : Fin k} (hab : Relation.ReflTransGen (MiddleAdj D₁ D₂) a b) {y z : Fin k ⊕ Fin k}
    (hy : IsAttach D₁ D₂ a y) (hz : IsAttach D₁ D₂ b z) : Sum.elim u v y = Sum.elim u v z := by
  obtain ⟨s₀, h₀, hs₀⟩ := exists_stackStart_eq_inr hy
  have hreach : ∀ b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b →
      ∃ s, Relation.ReflTransGen (StackRel D₁ D₂) s₀ s ∧ middlePoint s = b := fun b hab => by
    induction hab with
    | refl => exact ⟨s₀, .refl, hs₀⟩
    | tail _ hadj ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      exact exists_reflTransGen_stackStep_of_middleAdj h₀ hs hadj
  obtain ⟨s, hs, rfl⟩ := hreach b hab
  rcases eq_or_composeDiagram_val_eq_of_isAttach h₀ hs hz with rfl | hyz
  · rfl
  · rw [← hyz]
    exact (hC y).symm

/-! ### The count -/

/-- A labelling constant on the arcs of both diagrams is constant along the middle graph. -/
private theorem eq_of_reflTransGen (h₁ : D₁.IsConstantOnArcs (Sum.elim m v))
    (h₂ : D₂.IsConstantOnArcs (Sum.elim u m)) {a b : Fin k}
    (hab : Relation.ReflTransGen (MiddleAdj D₁ D₂) a b) : m a = m b := by
  induction hab with
  | refl => rfl
  | @tail b c _ hadj ih =>
    refine ih.trans ?_
    rcases (middleAdj_def D₁ D₂ b c).mp hadj with h | h
    · simpa [h] using (h₁ (Sum.inl b)).symm
    · simpa [h] using (h₂ (Sum.inr b)).symm

/-- A labelling constant on the arcs of both diagrams gives a middle point with a through strand
the label of the outer end of that strand. -/
private theorem eq_of_isAttach (h₁ : D₁.IsConstantOnArcs (Sum.elim m v))
    (h₂ : D₂.IsConstantOnArcs (Sum.elim u m)) {b : Fin k} {z : Fin k ⊕ Fin k}
    (hz : IsAttach D₁ D₂ b z) : m b = Sum.elim u v z := by
  rcases hz with ⟨hz, h⟩ | ⟨hz, h⟩ <;> rcases z with i | j <;> simp at hz
  · simpa [h] using (h₁ (Sum.inl b)).symm
  · simpa [h] using (h₂ (Sum.inr b)).symm

/-- Conversely, a middle labelling is constant on the arcs of both diagrams once it is constant
along the middle graph and gives every through strand the label of its outer end, provided the
outer labelling is constant on the arcs of the composite. -/
private theorem isConstantOnArcs_of_forall
    (hC : (composeDiagram D₁ D₂).IsConstantOnArcs (Sum.elim u v))
    (hadj : ∀ a b, MiddleAdj D₁ D₂ a b → m a = m b)
    (hatt : ∀ b z, IsAttach D₁ D₂ b z → m b = Sum.elim u v z) :
    D₁.IsConstantOnArcs (Sum.elim m v) ∧ D₂.IsConstantOnArcs (Sum.elim u m) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rcases x with a | j
    · rcases hD : D₁.val (Sum.inl a) with b | j
      · exact (hadj a b ((middleAdj_def D₁ D₂ a b).mpr (Or.inl hD))).symm
      · exact (hatt a _ (Or.inl ⟨rfl, hD⟩)).symm
    · rcases hD : D₁.val (Sum.inr j) with a | j'
      · exact hatt a _ (Or.inl ⟨rfl, D₁.apply_eq_of_apply_eq hD⟩)
      · simpa [composeDiagram_val_inr_eq_inr_of_cup_upper D₁ D₂ hD] using hC (Sum.inr j)
  · rcases x with i | a
    · rcases hD : D₂.val (Sum.inl i) with i' | a
      · simpa [composeDiagram_val_inl_eq_inl_of_cap_lower D₁ D₂ hD] using hC (Sum.inl i)
      · exact hatt a _ (Or.inr ⟨rfl, D₂.apply_eq_of_apply_eq hD⟩)
    · rcases hD : D₂.val (Sum.inr a) with i | b
      · exact (hatt a _ (Or.inr ⟨rfl, hD⟩)).symm
      · exact (hadj a b ((middleAdj_def D₁ D₂ a b).mpr (Or.inr hD))).symm

/-- A middle point off the closed loops is joined in the middle graph to a through strand. -/
private theorem exists_isAttach_of_not_onMiddleLoop {a : Fin k} (ha : ¬OnMiddleLoop D₁ D₂ a) :
    ∃ z b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b ∧ IsAttach D₁ D₂ b z := by
  rw [onMiddleLoop_def, not_forall] at ha
  obtain ⟨b, hb⟩ := ha
  rw [not_imp] at hb
  obtain ⟨hab, hb⟩ := hb
  obtain ⟨z, hz⟩ := exists_isAttach hb
  exact ⟨z, b, hab, hz⟩

variable (D₁ D₂ u v) in
/-- Restricting a middle labelling to the least points of the closed middle loops. -/
private def restrictLoopMin
    (m : {m : Fin k → ι // D₁.IsConstantOnArcs (Sum.elim m v) ∧
      D₂.IsConstantOnArcs (Sum.elim u m)}) :
    {a : Fin k // IsMiddleLoopMin D₁ D₂ a} → ι :=
  fun p => m.1 p.1

/-- A middle labelling is determined by its labels on the least points of the closed loops. -/
private theorem restrictLoopMin_injective : Function.Injective (restrictLoopMin D₁ D₂ u v) := by
  rintro ⟨m, h₁, h₂⟩ ⟨m', h₁', h₂'⟩ h
  refine Subtype.ext (funext fun a => ?_)
  dsimp only
  by_cases ha : OnMiddleLoop D₁ D₂ a
  · obtain ⟨p, hp, hap⟩ := ha.exists_isMiddleLoopMin
    rw [eq_of_reflTransGen h₁ h₂ hap, eq_of_reflTransGen h₁' h₂' hap]
    exact congrFun h ⟨p, hp⟩
  · obtain ⟨z, b, hab, hz⟩ := exists_isAttach_of_not_onMiddleLoop ha
    rw [eq_of_reflTransGen h₁ h₂ hab, eq_of_reflTransGen h₁' h₂' hab, eq_of_isAttach h₁ h₂ hz,
      eq_of_isAttach h₁' h₂' hz]

open Classical in
/-- Every labelling of the least points of the closed middle loops extends to a middle labelling,
once the outer labelling is constant on the arcs of the composite: label each loop by the label of
its least point, and every other middle point by the label its through strands force. -/
private theorem restrictLoopMin_surjective
    (hC : (composeDiagram D₁ D₂).IsConstantOnArcs (Sum.elim u v)) :
    Function.Surjective (restrictLoopMin D₁ D₂ u v) := by
  intro g
  let m : Fin k → ι := fun a =>
    if ha : OnMiddleLoop D₁ D₂ a then g ⟨_, ha.exists_isMiddleLoopMin.choose_spec.1⟩
    else Sum.elim u v (exists_isAttach_of_not_onMiddleLoop ha).choose
  have hloop {a : Fin k} (ha : OnMiddleLoop D₁ D₂ a) {p : Fin k} (hp : IsMiddleLoopMin D₁ D₂ p)
      (hap : Relation.ReflTransGen (MiddleAdj D₁ D₂) a p) : m a = g ⟨p, hp⟩ := by
    have hspec := ha.exists_isMiddleLoopMin.choose_spec
    simp only [m, ha, ↓reduceDIte]
    congr 2
    exact hspec.1.eq_of_reflTransGen hp ((MiddleAdj.reflTransGen_symm hspec.2).trans hap)
  have hoff {a : Fin k} (ha : ¬OnMiddleLoop D₁ D₂ a) {b : Fin k} {z : Fin k ⊕ Fin k}
      (hab : Relation.ReflTransGen (MiddleAdj D₁ D₂) a b) (hz : IsAttach D₁ D₂ b z) :
      m a = Sum.elim u v z := by
    obtain ⟨b', hab', hz'⟩ := (exists_isAttach_of_not_onMiddleLoop ha).choose_spec
    simp only [m, ha, ↓reduceDIte]
    exact label_eq_of_isAttach hC ((MiddleAdj.reflTransGen_symm hab').trans hab) hz' hz
  have hm := isConstantOnArcs_of_forall (m := m) hC
    (fun a b hadj => by
      by_cases ha : OnMiddleLoop D₁ D₂ a
      · obtain ⟨p, hp, hap⟩ := ha.exists_isMiddleLoopMin
        have hb := ha.reflTransGen (.single hadj)
        have hbp : Relation.ReflTransGen (MiddleAdj D₁ D₂) b p :=
          (MiddleAdj.reflTransGen_symm (.single hadj)).trans hap
        rw [hloop ha hp hap, hloop hb hp hbp]
      · obtain ⟨z, c, hac, hz⟩ := exists_isAttach_of_not_onMiddleLoop ha
        have hb : ¬OnMiddleLoop D₁ D₂ b := fun hb =>
          ha (hb.reflTransGen (MiddleAdj.reflTransGen_symm (.single hadj)))
        rw [hoff ha hac hz,
          hoff hb ((MiddleAdj.reflTransGen_symm (.single hadj)).trans hac) hz])
    (fun b z hz => hoff (not_onMiddleLoop_of_isAttach hz) .refl hz)
  exact ⟨⟨m, hm⟩, funext fun p => hloop ((isMiddleLoopMin_def D₁ D₂ _).mp p.2).1 p.2 .refl⟩

/-- **The loop rule for labellings.** Stack `D₁` above `D₂` and label the outer boundary by
`Sum.elim u v`, constant on the arcs of the composite `TauCeti.composeDiagram D₁ D₂`. Its
extensions by a labelling `m` of the middle boundary, constant on the arcs of both diagrams, number
`|ι| ^ c` with `c = TauCeti.middleLoopCount D₁ D₂`: the labels on the strands are forced, and the
label of each closed middle loop is free. No finiteness of `ι` is needed: for an infinite `ι` both
sides are `1` when there is no loop and `0` (the value of `Nat.card` on infinite types) when there
is one. -/
theorem natCard_middleLabelling (hC : (composeDiagram D₁ D₂).IsConstantOnArcs (Sum.elim u v)) :
    Nat.card {m : Fin k → ι // D₁.IsConstantOnArcs (Sum.elim m v) ∧
      D₂.IsConstantOnArcs (Sum.elim u m)} = Nat.card ι ^ middleLoopCount D₁ D₂ := by
  rw [Nat.card_congr (Equiv.ofBijective _
    ⟨restrictLoopMin_injective, restrictLoopMin_surjective hC⟩), Nat.card_fun,
    middleLoopCount_def, ← Nat.card_coe_set_eq, Set.coe_ofPred]

end Stack

end BrauerDiagram

end TauCeti
