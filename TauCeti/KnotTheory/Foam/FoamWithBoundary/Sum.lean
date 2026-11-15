/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.FoamWithBoundary.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Disjoint union and symmetric monoidal structure on unlabelled prefoams

This file constructs the disjoint union `F.sum G : FoamWithBoundary (W₁.sum W₂)` of two unlabelled
prefoams together with the symmetric monoidal coherence isomorphisms (`emptySum`, `sumEmpty`,
`sumComm`, `sumAssoc`) and functoriality on isomorphisms (`IsoOver.sum`) lying over the
corresponding operations on `ClosedWeb`.

## Main definitions

* `TauCeti.FoamWithBoundary.sum`: disjoint union of prefoams over `ClosedWeb.sum`.
* `TauCeti.FoamWithBoundary.emptySum`, `sumEmpty`, `sumComm`, `sumAssoc`: left/right unitors,
  braiding, and associator isomorphisms over their `ClosedWeb` counterparts.
* `TauCeti.FoamWithBoundary.IsoOver.sum`: disjoint union of prefoam isomorphisms.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definition 2.4.
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1.
-/

public section

namespace TauCeti

universe u v w

namespace FoamWithBoundary

/-- Seam-end pairing equivalence on the disjoint union `F.sum G`. -/
def sumSeamEnds {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) :
    ((F.Vertex ⊕ G.Vertex) × Fin 4) ⊕ (W₁.sum W₂).Vertex ≃ (F.Seam ⊕ G.Seam) × Bool :=
  (((Equiv.sumProdDistrib F.Vertex G.Vertex (Fin 4)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)).trans
      ((F.seamEnds.sumCongr G.seamEnds).trans (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm)

@[simp] theorem sumSeamEnds_inl_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (v : F.Vertex) (k : Fin 4) :
    sumSeamEnds F G (Sum.inl (Sum.inl v, k)) =
      Prod.map Sum.inl id (F.seamEnds (Sum.inl (v, k))) := by
  change (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm (Sum.inl (F.seamEnds (Sum.inl (v, k)))) =
    Prod.map Sum.inl id (F.seamEnds (Sum.inl (v, k)))
  rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
  rfl

@[simp] theorem sumSeamEnds_inl_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (v : G.Vertex) (k : Fin 4) :
    sumSeamEnds F G (Sum.inl (Sum.inr v, k)) =
      Prod.map Sum.inr id (G.seamEnds (Sum.inl (v, k))) := by
  change (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm (Sum.inr (G.seamEnds (Sum.inl (v, k)))) =
    Prod.map Sum.inr id (G.seamEnds (Sum.inl (v, k)))
  rcases G.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
  rfl

@[simp] theorem sumSeamEnds_inr_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (w : W₁.Vertex) :
    sumSeamEnds F G (Sum.inr (Sum.inl w)) = Prod.map Sum.inl id (F.seamEnds (Sum.inr w)) := by
  change (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm (Sum.inl (F.seamEnds (Sum.inr w))) =
    Prod.map Sum.inl id (F.seamEnds (Sum.inr w))
  rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
  rfl

@[simp] theorem sumSeamEnds_inr_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (w : W₂.Vertex) :
    sumSeamEnds F G (Sum.inr (Sum.inr w)) = Prod.map Sum.inr id (G.seamEnds (Sum.inr w)) := by
  change (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm (Sum.inr (G.seamEnds (Sum.inr w))) =
    Prod.map Sum.inr id (G.seamEnds (Sum.inr w))
  rcases G.seamEnds (Sum.inr w) with ⟨s, b⟩
  rfl

/-- Equivalence redistributing the segmented sides of `F.sum G` into `F.Side ⊕ G.Side`. -/
def sumSideEquiv {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) :
    (((F.Seam ⊕ G.Seam) × Fin 3) ⊕ (W₁.sum W₂).Edge) ≃ F.Side ⊕ G.Side :=
  ((Equiv.sumProdDistrib F.Seam G.Seam (Fin 3)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)

@[simp] theorem sumSideEquiv_inl_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (s : F.Seam) (i : Fin 3) :
    sumSideEquiv F G (Sum.inl (Sum.inl s, i)) = Sum.inl (Sum.inl (s, i)) := (rfl)

@[simp] theorem sumSideEquiv_inl_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (s : G.Seam) (i : Fin 3) :
    sumSideEquiv F G (Sum.inl (Sum.inr s, i)) = Sum.inr (Sum.inl (s, i)) := (rfl)

@[simp] theorem sumSideEquiv_inr_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (e : W₁.Edge) :
    sumSideEquiv F G (Sum.inr (Sum.inl e)) = Sum.inl (Sum.inr e) := (rfl)

@[simp] theorem sumSideEquiv_inr_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (e : W₂.Edge) :
    sumSideEquiv F G (Sum.inr (Sum.inr e)) = Sum.inr (Sum.inr e) := (rfl)

@[simp] theorem sumSideEquiv_symm_inl_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (s : F.Seam) (i : Fin 3) :
    (sumSideEquiv F G).symm (Sum.inl (Sum.inl (s, i))) = Sum.inl (Sum.inl s, i) := (rfl)

@[simp] theorem sumSideEquiv_symm_inl_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (e : W₁.Edge) :
    (sumSideEquiv F G).symm (Sum.inl (Sum.inr e)) = Sum.inr (Sum.inl e) := (rfl)

@[simp] theorem sumSideEquiv_symm_inr_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (s : G.Seam) (i : Fin 3) :
    (sumSideEquiv F G).symm (Sum.inr (Sum.inl (s, i))) = Sum.inl (Sum.inr s, i) := (rfl)

@[simp] theorem sumSideEquiv_symm_inr_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (e : W₂.Edge) :
    (sumSideEquiv F G).symm (Sum.inr (Sum.inr e)) = Sum.inr (Sum.inr e) := (rfl)

/-- Equivalence redistributing the circle sides of `F.sum G` into `F.CircleSide ⊕ G.CircleSide`. -/
def sumCircleSideEquiv {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) :
    (((F.SeamCircle ⊕ G.SeamCircle) × Fin 3) ⊕ (W₁.sum W₂).Circle) ≃
      F.CircleSide ⊕ G.CircleSide :=
  ((Equiv.sumProdDistrib F.SeamCircle G.SeamCircle (Fin 3)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)

@[simp] theorem sumCircleSideEquiv_inl_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (c : F.SeamCircle) (i : Fin 3) :
    sumCircleSideEquiv F G (Sum.inl (Sum.inl c, i)) = Sum.inl (Sum.inl (c, i)) := (rfl)

@[simp] theorem sumCircleSideEquiv_inl_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (c : G.SeamCircle) (i : Fin 3) :
    sumCircleSideEquiv F G (Sum.inl (Sum.inr c, i)) = Sum.inr (Sum.inl (c, i)) := (rfl)

@[simp] theorem sumCircleSideEquiv_inr_inl {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (c : W₁.Circle) :
    sumCircleSideEquiv F G (Sum.inr (Sum.inl c)) = Sum.inl (Sum.inr c) := (rfl)

@[simp] theorem sumCircleSideEquiv_inr_inr {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) (c : W₂.Circle) :
    sumCircleSideEquiv F G (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c) := (rfl)

private def sumCornerEquiv {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) :
    (((F.Vertex ⊕ G.Vertex) × Fin 6) ⊕ ((W₁.sum W₂).Vertex × Fin 3)) ≃ F.Corner ⊕ G.Corner :=
  ((Equiv.sumProdDistrib F.Vertex G.Vertex (Fin 6)).sumCongr
    (Equiv.sumProdDistrib W₁.Vertex W₂.Vertex (Fin 3))).trans (Equiv.sumSumSumComm _ _ _ _)

private theorem sum_cornerIncomingEquiv {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂)
    (h_inl : ∀ (v : F.Vertex ⊕ G.Vertex) k,
      (sumSeamEnds F G (Sum.inl (v, k))).2 =
        !((ClosedWeb.tetWeb (Sum.elim F.chirality G.chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w : (W₁.sum W₂).Vertex,
      (sumSeamEnds F G (Sum.inr w)).2 = ((W₁.sum W₂).ends (w, 0)).2)
    (c : ((F.Vertex ⊕ G.Vertex) × Fin 6) ⊕ ((W₁.sum W₂).Vertex × Fin 3)) :
    cornerIncomingEquiv (W := W₁.sum W₂) (Sum.elim F.chirality G.chirality)
        (sumSeamEnds F G) h_inl h_inr c =
      (sumSideEquiv F G).symm ((F.cornerIncoming.sumCongr G.cornerIncoming)
        (sumCornerEquiv F G c)) := by
  rcases c with ⟨v | v, e⟩ | ⟨w | w, i⟩
  · have hc : sumCornerEquiv F G (Sum.inl (Sum.inl v, e)) = Sum.inl (Sum.inl (v, e)) := rfl
    rw [hc, cornerIncomingEquiv_inl]
    dsimp only [Sum.elim_inl]
    rw [sumSeamEnds_inl_inl]
    simp [F.cornerIncoming_def, sumSideEquiv]
  · have hc : sumCornerEquiv F G (Sum.inl (Sum.inr v, e)) = Sum.inr (Sum.inl (v, e)) := rfl
    rw [hc, cornerIncomingEquiv_inl]
    dsimp only [Sum.elim_inr]
    rw [sumSeamEnds_inl_inr]
    simp [G.cornerIncoming_def, sumSideEquiv]
  · have hc : sumCornerEquiv F G (Sum.inr (Sum.inl w, i)) = Sum.inl (Sum.inr (w, i)) := rfl
    rw [hc, cornerIncomingEquiv_inr, ClosedWeb.sum_ends_apply_inl, sumSeamEnds_inr_inl]
    simp only [Equiv.sumCongr_apply, Sum.map_inl, F.cornerIncoming_def, cornerIncomingEquiv_inr]
    rcases W₁.ends (w, i) with ⟨e, _ | _⟩ <;> rfl
  · have hc : sumCornerEquiv F G (Sum.inr (Sum.inr w, i)) = Sum.inr (Sum.inr (w, i)) := rfl
    rw [hc, cornerIncomingEquiv_inr, ClosedWeb.sum_ends_apply_inr, sumSeamEnds_inr_inr]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, G.cornerIncoming_def, cornerIncomingEquiv_inr]
    rcases W₂.ends (w, i) with ⟨e, _ | _⟩ <;> rfl

private theorem sum_cornerOutgoingEquiv {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂)
    (h_inl : ∀ (v : F.Vertex ⊕ G.Vertex) k,
      (sumSeamEnds F G (Sum.inl (v, k))).2 =
        !((ClosedWeb.tetWeb (Sum.elim F.chirality G.chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w : (W₁.sum W₂).Vertex,
      (sumSeamEnds F G (Sum.inr w)).2 = ((W₁.sum W₂).ends (w, 0)).2)
    (c : ((F.Vertex ⊕ G.Vertex) × Fin 6) ⊕ ((W₁.sum W₂).Vertex × Fin 3)) :
    cornerOutgoingEquiv (W := W₁.sum W₂) (Sum.elim F.chirality G.chirality)
        (sumSeamEnds F G) h_inl h_inr c =
      (sumSideEquiv F G).symm ((F.cornerOutgoing.sumCongr G.cornerOutgoing)
        (sumCornerEquiv F G c)) := by
  rcases c with ⟨v | v, e⟩ | ⟨w | w, i⟩
  · have hc : sumCornerEquiv F G (Sum.inl (Sum.inl v, e)) = Sum.inl (Sum.inl (v, e)) := rfl
    rw [hc, cornerOutgoingEquiv_inl]
    dsimp only [Sum.elim_inl]
    rw [sumSeamEnds_inl_inl]
    simp [F.cornerOutgoing_def, sumSideEquiv]
  · have hc : sumCornerEquiv F G (Sum.inl (Sum.inr v, e)) = Sum.inr (Sum.inl (v, e)) := rfl
    rw [hc, cornerOutgoingEquiv_inl]
    dsimp only [Sum.elim_inr]
    rw [sumSeamEnds_inl_inr]
    simp [G.cornerOutgoing_def, sumSideEquiv]
  · have hc : sumCornerEquiv F G (Sum.inr (Sum.inl w, i)) = Sum.inl (Sum.inr (w, i)) := rfl
    rw [hc, cornerOutgoingEquiv_inr, ClosedWeb.sum_ends_apply_inl, sumSeamEnds_inr_inl]
    simp only [Equiv.sumCongr_apply, Sum.map_inl, F.cornerOutgoing_def, cornerOutgoingEquiv_inr]
    rcases W₁.ends (w, i) with ⟨e, _ | _⟩ <;> rfl
  · have hc : sumCornerEquiv F G (Sum.inr (Sum.inr w, i)) = Sum.inr (Sum.inr (w, i)) := rfl
    rw [hc, cornerOutgoingEquiv_inr, ClosedWeb.sum_ends_apply_inr, sumSeamEnds_inr_inr]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, G.cornerOutgoing_def, cornerOutgoingEquiv_inr]
    rcases W₂.ends (w, i) with ⟨e, _ | _⟩ <;> rfl

private theorem sum_nextSidePerm {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂)
    (h_inl : ∀ (v : F.Vertex ⊕ G.Vertex) k,
      (sumSeamEnds F G (Sum.inl (v, k))).2 =
        !((ClosedWeb.tetWeb (Sum.elim F.chirality G.chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w : (W₁.sum W₂).Vertex,
      (sumSeamEnds F G (Sum.inr w)).2 = ((W₁.sum W₂).ends (w, 0)).2) :
    nextSidePerm (W := W₁.sum W₂) (Sum.elim F.chirality G.chirality) (sumSeamEnds F G) h_inl h_inr =
      (sumSideEquiv F G).symm.permCongr (Equiv.Perm.sumCongr F.nextSide G.nextSide) := by
  ext y
  obtain ⟨c, rfl⟩ :=
    (cornerIncomingEquiv (W := W₁.sum W₂) (Sum.elim F.chirality G.chirality)
      (sumSeamEnds F G) h_inl h_inr).surjective y
  rw [nextSidePerm_apply, Equiv.symm_apply_apply,
    sum_cornerOutgoingEquiv F G h_inl h_inr c, sum_cornerIncomingEquiv F G h_inl h_inr c,
    Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rcases sumCornerEquiv F G c with c₁ | c₂ <;> simp [nextSide_apply]

/-- Disjoint union of two prefoams `F : FoamWithBoundary W₁` and `G : FoamWithBoundary W₂`. -/
abbrev sum {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
    (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂) :
    FoamWithBoundary (W₁.sum W₂) where
  Vertex := F.Vertex ⊕ G.Vertex
  Seam := F.Seam ⊕ G.Seam
  SeamCircle := F.SeamCircle ⊕ G.SeamCircle
  Facet := F.Facet ⊕ G.Facet
  Boundary := F.Boundary ⊕ G.Boundary
  chirality := Sum.elim F.chirality G.chirality
  seamEnds := sumSeamEnds F G
  seamEnds_inl_snd := by
    rintro (v | v) k
    · rw [sumSeamEnds_inl_inl]
      exact F.seamEnds_inl_snd v k
    · rw [sumSeamEnds_inl_inr]
      exact G.seamEnds_inl_snd v k
  seamEnds_inr_snd := by
    rintro (w | w)
    · rw [sumSeamEnds_inr_inl, ClosedWeb.sum_ends_apply_inl]
      exact F.seamEnds_inr_snd w
    · rw [sumSeamEnds_inr_inr, ClosedWeb.sum_ends_apply_inr]
      exact G.seamEnds_inr_snd w
  genus := Sum.elim F.genus G.genus
  boundaryFacet := Sum.map F.boundaryFacet G.boundaryFacet
  sideBoundary := Sum.map F.sideBoundary G.sideBoundary ∘ sumSideEquiv F G
  circleBoundary := Sum.map F.circleBoundary G.circleBoundary ∘ sumCircleSideEquiv F G
  sideBoundary_eq_iff x y := by
    rw [sum_nextSidePerm F G,
      Equiv.Perm.sameCycle_permCongr_iff (σ := Equiv.Perm.sumCongr F.nextSide G.nextSide)
        (sumSideEquiv F G).symm]
    dsimp only [Function.comp_apply, Equiv.symm_symm]
    rcases sumSideEquiv F G x with x₁ | x₂ <;> rcases sumSideEquiv F G y with y₁ | y₂
    · simp [F.sideBoundary_eq_iff, ← F.nextSide_def, Equiv.Perm.sameCycle_sumCongr_inl]
    · simp [Equiv.Perm.not_sameCycle_sumCongr_inl_inr]
    · constructor
      · intro h
        cases h
      · intro h
        exact (Equiv.Perm.not_sameCycle_sumCongr_inl_inr _ _ _ _ h.symm).elim
    · simp [G.sideBoundary_eq_iff, ← G.nextSide_def, Equiv.Perm.sameCycle_sumCongr_inr]
  circleBoundary_injective :=
    (F.circleBoundary_injective.sumMap G.circleBoundary_injective).comp
      (sumCircleSideEquiv F G).injective
  sideBoundary_ne_circleBoundary x z h := by
    dsimp only [Function.comp_apply] at h
    rcases hx : sumSideEquiv F G x with x₁ | x₂ <;>
      rcases hz : sumCircleSideEquiv F G z with z₁ | z₂ <;>
      rw [hx, hz] at h
    · exact F.sideBoundary_ne_circleBoundary x₁ z₁ (Sum.inl.inj h)
    · cases h
    · cases h
    · exact G.sideBoundary_ne_circleBoundary x₂ z₂ (Sum.inr.inj h)
  boundary_surjective := by
    rintro (b₁ | b₂)
    · rcases F.boundary_surjective b₁ with ⟨x₁, rfl⟩ | ⟨z₁, rfl⟩
      · exact Or.inl ⟨(sumSideEquiv F G).symm (Sum.inl x₁), by simp⟩
      · exact Or.inr ⟨(sumCircleSideEquiv F G).symm (Sum.inl z₁), by simp⟩
    · rcases G.boundary_surjective b₂ with ⟨x₂, rfl⟩ | ⟨z₂, rfl⟩
      · exact Or.inl ⟨(sumSideEquiv F G).symm (Sum.inr x₂), by simp⟩
      · exact Or.inr ⟨(sumCircleSideEquiv F G).symm (Sum.inr z₂), by simp⟩

/-- Left unit isomorphism for disjoint union of prefoams. -/
def emptySum {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (empty.{v}.sum F).IsoOver W.emptySum F where
  vertex := Equiv.emptySum _ _
  seam := Equiv.emptySum _ _
  seamCircle := Equiv.emptySum _ _
  facet := Equiv.emptySum _ _
  boundary := Equiv.emptySum _ _
  map_chirality := by
    rintro (v | v)
    · exact v.elim
    · rfl
  map_seamEnds := by
    rintro (⟨v | v, k⟩ | (w | w))
    · exact v.elim
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.emptySum_apply_inr, id_eq]
      rw [sumSeamEnds_inl_inr]
      rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · exact w.elim
    · simp only [Sum.map_inr, ClosedWeb.emptySum_vertex, Equiv.emptySum_apply_inr]
      rw [sumSeamEnds_inr_inr]
      rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
  map_genus := by
    rintro (f | f)
    · exact f.elim
    · rfl
  map_boundaryFacet := by
    rintro (b | b)
    · exact b.elim
    · rfl
  map_sideBoundary := by
    rintro (⟨s | s, i⟩ | (e | e))
    · exact s.elim
    · rfl
    · exact e.elim
    · simp [sum, sumSideEquiv]
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · exact c.elim
    · rfl
    · exact c.elim
    · simp [sum, sumCircleSideEquiv]

/-- Right unit isomorphism for disjoint union of prefoams. -/
def sumEmpty {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (F.sum empty.{v}).IsoOver W.sumEmpty F where
  vertex := Equiv.sumEmpty _ _
  seam := Equiv.sumEmpty _ _
  seamCircle := Equiv.sumEmpty _ _
  facet := Equiv.sumEmpty _ _
  boundary := Equiv.sumEmpty _ _
  map_chirality := by
    rintro (v | v)
    · rfl
    · exact v.elim
  map_seamEnds := by
    rintro (⟨v | v, k⟩ | (w | w))
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumEmpty_apply_inl, id_eq]
      rw [sumSeamEnds_inl_inl]
      rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · exact v.elim
    · simp only [Sum.map_inr, ClosedWeb.sumEmpty_vertex, Equiv.sumEmpty_apply_inl]
      rw [sumSeamEnds_inr_inl]
      rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
    · exact w.elim
  map_genus := by
    rintro (f | f)
    · rfl
    · exact f.elim
  map_boundaryFacet := by
    rintro (b | b)
    · rfl
    · exact b.elim
  map_sideBoundary := by
    rintro (⟨s | s, i⟩ | (e | e))
    · rfl
    · exact s.elim
    · simp [sum, sumSideEquiv]
    · exact e.elim
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · rfl
    · exact c.elim
    · simp [sum, sumCircleSideEquiv]
    · exact c.elim

/-- Symmetry isomorphism exchanging two disjoint prefoam components. -/
def sumComm {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (F.sum G).IsoOver (W.sumComm V) (G.sum F) where
  vertex := Equiv.sumComm _ _
  seam := Equiv.sumComm _ _
  seamCircle := Equiv.sumComm _ _
  facet := Equiv.sumComm _ _
  boundary := Equiv.sumComm _ _
  map_chirality := by rintro (v | v) <;> rfl
  map_seamEnds := by
    rintro (⟨v | v, k⟩ | (w | w))
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumComm_apply, Sum.swap_inl, id_eq]
      rw [sumSeamEnds_inl_inr, sumSeamEnds_inl_inl]
      rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumComm_apply, Sum.swap_inr, id_eq]
      rw [sumSeamEnds_inl_inl, sumSeamEnds_inl_inr]
      rcases G.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inr, ClosedWeb.sumComm_vertex, Equiv.sumComm_apply, Sum.swap_inl]
      rw [sumSeamEnds_inr_inr, sumSeamEnds_inr_inl]
      rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inr, ClosedWeb.sumComm_vertex, Equiv.sumComm_apply, Sum.swap_inr]
      rw [sumSeamEnds_inr_inl, sumSeamEnds_inr_inr]
      rcases G.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
  map_genus := by rintro (f | f) <;> rfl
  map_boundaryFacet := by rintro (b | b) <;> rfl
  map_sideBoundary := by rintro (⟨s | s, i⟩ | (e | e)) <;> simp [sum, sumSideEquiv]
  map_circleBoundary := by rintro (⟨c | c, i⟩ | (c | c)) <;> simp [sum, sumCircleSideEquiv]

/-- Associativity isomorphism for disjoint union of prefoams. -/
def sumAssoc {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    ((F.sum G).sum H).IsoOver (W.sumAssoc V U) (F.sum (G.sum H)) where
  vertex := Equiv.sumAssoc _ _ _
  seam := Equiv.sumAssoc _ _ _
  seamCircle := Equiv.sumAssoc _ _ _
  facet := Equiv.sumAssoc _ _ _
  boundary := Equiv.sumAssoc _ _ _
  map_chirality := by rintro ((v | v) | v) <;> rfl
  map_seamEnds := by
    rintro (⟨(v | v) | v, k⟩ | ((w | w) | w))
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumAssoc_apply_inl_inl, id_eq]
      rw [sumSeamEnds_inl_inl, sumSeamEnds_inl_inl, sumSeamEnds_inl_inl]
      rcases F.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumAssoc_apply_inl_inr, id_eq]
      rw [sumSeamEnds_inl_inr, sumSeamEnds_inl_inl, sumSeamEnds_inl_inl, sumSeamEnds_inl_inr]
      rcases G.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inl, Prod.map_apply, Equiv.sumAssoc_apply_inr, id_eq]
      rw [sumSeamEnds_inl_inr, sumSeamEnds_inl_inr, sumSeamEnds_inl_inr]
      rcases H.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inr, ClosedWeb.sumAssoc_vertex, Equiv.sumAssoc_apply_inl_inl]
      rw [sumSeamEnds_inr_inl, sumSeamEnds_inr_inl, sumSeamEnds_inr_inl]
      rcases F.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inr, ClosedWeb.sumAssoc_vertex, Equiv.sumAssoc_apply_inl_inr]
      rw [sumSeamEnds_inr_inr, sumSeamEnds_inr_inl, sumSeamEnds_inr_inl, sumSeamEnds_inr_inr]
      rcases G.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
    · simp only [Sum.map_inr, ClosedWeb.sumAssoc_vertex, Equiv.sumAssoc_apply_inr]
      rw [sumSeamEnds_inr_inr, sumSeamEnds_inr_inr, sumSeamEnds_inr_inr]
      rcases H.seamEnds (Sum.inr w) with ⟨s, b⟩
      rfl
  map_genus := by rintro ((f | f) | f) <;> rfl
  map_boundaryFacet := by rintro ((b | b) | b) <;> rfl
  map_sideBoundary := by rintro (⟨(s | s) | s, i⟩ | ((e | e) | e)) <;> simp [sum, sumSideEquiv]
  map_circleBoundary := by
    rintro (⟨(c | c) | c, i⟩ | ((c | c) | c)) <;> simp [sum, sumCircleSideEquiv]

private theorem sum_map_seamEnds {W₁ : ClosedWeb.{u}} {V₁ : ClosedWeb.{v}} {W₂ U₂ : ClosedWeb}
    {φ₁ : W₁.Iso V₁} {φ₂ : W₂.Iso U₂}
    {F₁ : FoamWithBoundary W₁} {G₁ : FoamWithBoundary V₁}
    {F₂ : FoamWithBoundary W₂} {G₂ : FoamWithBoundary U₂}
    (ψ₁ : F₁.IsoOver φ₁ G₁) (ψ₂ : F₂.IsoOver φ₂ G₂)
    (x : ((F₁.Vertex ⊕ F₂.Vertex) × Fin 4) ⊕ (W₁.sum W₂).Vertex) :
    sumSeamEnds G₁ G₂
        (Sum.map (Prod.map (ψ₁.vertex.sumCongr ψ₂.vertex) id) (φ₁.sum φ₂).vertex x) =
      Prod.map (ψ₁.seam.sumCongr ψ₂.seam) id (sumSeamEnds F₁ F₂ x) := by
  rcases x with ⟨v | v, k⟩ | (w | w)
  · have h := ψ₁.map_seamEnds (Sum.inl (v, k))
    dsimp only [Sum.map_inl, Prod.map_apply, id_eq] at h
    simp only [Sum.map_inl, Prod.map_apply, Equiv.sumCongr_apply, id_eq]
    rw [sumSeamEnds_inl_inl, sumSeamEnds_inl_inl, h]
    rcases F₁.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
    rfl
  · have h := ψ₂.map_seamEnds (Sum.inl (v, k))
    dsimp only [Sum.map_inl, Prod.map_apply, id_eq] at h
    simp only [Sum.map_inl, Prod.map_apply, Equiv.sumCongr_apply, Sum.map_inr, id_eq]
    rw [sumSeamEnds_inl_inr, sumSeamEnds_inl_inr, h]
    rcases F₂.seamEnds (Sum.inl (v, k)) with ⟨s, b⟩
    rfl
  · have h := ψ₁.map_seamEnds (Sum.inr w)
    dsimp only [Sum.map_inr] at h
    simp only [Sum.map_inr, ClosedWeb.Iso.sum_vertex, Equiv.sumCongr_apply, Sum.map_inl]
    rw [sumSeamEnds_inr_inl, sumSeamEnds_inr_inl, h]
    rcases F₁.seamEnds (Sum.inr w) with ⟨s, b⟩
    rfl
  · have h := ψ₂.map_seamEnds (Sum.inr w)
    dsimp only [Sum.map_inr] at h
    simp only [Sum.map_inr, ClosedWeb.Iso.sum_vertex, Equiv.sumCongr_apply]
    rw [sumSeamEnds_inr_inr, sumSeamEnds_inr_inr, h]
    rcases F₂.seamEnds (Sum.inr w) with ⟨s, b⟩
    rfl

/-- Functoriality of disjoint union on prefoam isomorphisms. -/
def IsoOver.sum {W₁ : ClosedWeb.{u}} {V₁ : ClosedWeb.{v}} {W₂ U₂ : ClosedWeb}
    {φ₁ : W₁.Iso V₁} {φ₂ : W₂.Iso U₂}
    {F₁ : FoamWithBoundary W₁} {G₁ : FoamWithBoundary V₁}
    {F₂ : FoamWithBoundary W₂} {G₂ : FoamWithBoundary U₂}
    (ψ₁ : F₁.IsoOver φ₁ G₁) (ψ₂ : F₂.IsoOver φ₂ G₂) :
    (F₁.sum F₂).IsoOver (φ₁.sum φ₂) (G₁.sum G₂) where
  vertex := ψ₁.vertex.sumCongr ψ₂.vertex
  seam := ψ₁.seam.sumCongr ψ₂.seam
  seamCircle := ψ₁.seamCircle.sumCongr ψ₂.seamCircle
  facet := ψ₁.facet.sumCongr ψ₂.facet
  boundary := ψ₁.boundary.sumCongr ψ₂.boundary
  map_chirality := by
    rintro (v | v)
    · exact ψ₁.map_chirality v
    · exact ψ₂.map_chirality v
  map_seamEnds := sum_map_seamEnds ψ₁ ψ₂
  map_genus := by
    rintro (f | f)
    · exact ψ₁.map_genus f
    · exact ψ₂.map_genus f
  map_boundaryFacet := by
    rintro (b | b)
    · exact congrArg Sum.inl (ψ₁.map_boundaryFacet b)
    · exact congrArg Sum.inr (ψ₂.map_boundaryFacet b)
  map_sideBoundary := by
    rintro (⟨s | s, i⟩ | (e | e))
    · exact congrArg Sum.inl (ψ₁.map_sideBoundary (Sum.inl (s, i)))
    · exact congrArg Sum.inr (ψ₂.map_sideBoundary (Sum.inl (s, i)))
    · simp only [FoamWithBoundary.sum, Sum.map_inr, ClosedWeb.Iso.sum_edge, Equiv.sumCongr_apply,
        Sum.map_inl, Function.comp_apply, sumSideEquiv]
      exact congrArg Sum.inl (ψ₁.map_sideBoundary (Sum.inr e))
    · simp only [FoamWithBoundary.sum, Sum.map_inr, ClosedWeb.Iso.sum_edge, Equiv.sumCongr_apply,
        Sum.map_inr, Function.comp_apply, sumSideEquiv]
      exact congrArg Sum.inr (ψ₂.map_sideBoundary (Sum.inr e))
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · exact congrArg Sum.inl (ψ₁.map_circleBoundary (Sum.inl (c, i)))
    · exact congrArg Sum.inr (ψ₂.map_circleBoundary (Sum.inl (c, i)))
    · simp only [FoamWithBoundary.sum, Sum.map_inr, ClosedWeb.Iso.sum_circle, Equiv.sumCongr_apply,
        Sum.map_inl, Function.comp_apply, sumCircleSideEquiv]
      exact congrArg Sum.inl (ψ₁.map_circleBoundary (Sum.inr c))
    · simp only [FoamWithBoundary.sum, Sum.map_inr, ClosedWeb.Iso.sum_circle, Equiv.sumCongr_apply,
        Sum.map_inr, Function.comp_apply, sumCircleSideEquiv]
      exact congrArg Sum.inr (ψ₂.map_circleBoundary (Sum.inr c))

end FoamWithBoundary

end TauCeti
