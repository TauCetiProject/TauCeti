/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.FoamWithBoundary.Iso
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Disjoint union and structural isomorphisms on unlabelled prefoams

This file constructs the disjoint union `F.sum G : FoamWithBoundary (W₁.sum W₂)` of two unlabelled
prefoams together with the structural unit, symmetry, and associativity isomorphisms (`emptySum`,
`sumEmpty`, `sumComm`, `sumAssoc`) and functoriality on isomorphisms (`IsoOver.sum`) lying over the
corresponding operations on `ClosedWeb`.

## Main definitions

* `TauCeti.FoamWithBoundary.sum`: disjoint union of prefoams over `ClosedWeb.sum`.
* `TauCeti.FoamWithBoundary.emptySum`, `sumEmpty`, `sumComm`, `sumAssoc`: left/right unitors,
  symmetry, and associativity isomorphisms over their `ClosedWeb` counterparts.
* `TauCeti.FoamWithBoundary.IsoOver.sum`: disjoint union of prefoam isomorphisms.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definitions 2.1 and 3.1.
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
    ((F.Vertex ⊕ G.Vertex) × Fin 4) ⊕ (W₁.Vertex ⊕ W₂.Vertex) ≃ (F.Seam ⊕ G.Seam) × Bool :=
  (((Equiv.sumProdDistrib F.Vertex G.Vertex (Fin 4)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)).trans
      ((F.seamEnds.sumCongr G.seamEnds).trans (Equiv.sumProdDistrib F.Seam G.Seam Bool).symm)

section SumEquiv

variable {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
  (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂)

@[simp] theorem sumSeamEnds_inl_inl (v : F.Vertex) (k : Fin 4) :
    sumSeamEnds F G (Sum.inl (Sum.inl v, k)) =
      Prod.map Sum.inl id (F.seamEnds (Sum.inl (v, k))) := by
  simp [sumSeamEnds, Prod.map]

@[simp] theorem sumSeamEnds_inl_inr (v : G.Vertex) (k : Fin 4) :
    sumSeamEnds F G (Sum.inl (Sum.inr v, k)) =
      Prod.map Sum.inr id (G.seamEnds (Sum.inl (v, k))) := by
  simp [sumSeamEnds, Prod.map]

@[simp] theorem sumSeamEnds_inr_inl (w : W₁.Vertex) :
    sumSeamEnds F G (Sum.inr (Sum.inl w)) = Prod.map Sum.inl id (F.seamEnds (Sum.inr w)) := by
  simp [sumSeamEnds, Prod.map]

@[simp] theorem sumSeamEnds_inr_inr (w : W₂.Vertex) :
    sumSeamEnds F G (Sum.inr (Sum.inr w)) = Prod.map Sum.inr id (G.seamEnds (Sum.inr w)) := by
  simp [sumSeamEnds, Prod.map]

/-- Equivalence redistributing the segmented sides of `F.sum G` into `F.Side ⊕ G.Side`. -/
def sumSideEquiv :
    (((F.Seam ⊕ G.Seam) × Fin 3) ⊕ (W₁.Edge ⊕ W₂.Edge)) ≃ F.Side ⊕ G.Side :=
  ((Equiv.sumProdDistrib F.Seam G.Seam (Fin 3)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)

@[simp] theorem sumSideEquiv_inl_inl (s : F.Seam) (i : Fin 3) :
    sumSideEquiv F G (Sum.inl (Sum.inl s, i)) = Sum.inl (Sum.inl (s, i)) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_inl_inr (s : G.Seam) (i : Fin 3) :
    sumSideEquiv F G (Sum.inl (Sum.inr s, i)) = Sum.inr (Sum.inl (s, i)) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_inr_inl (e : W₁.Edge) :
    sumSideEquiv F G (Sum.inr (Sum.inl e)) = Sum.inl (Sum.inr e) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_inr_inr (e : W₂.Edge) :
    sumSideEquiv F G (Sum.inr (Sum.inr e)) = Sum.inr (Sum.inr e) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_symm_inl_inl (s : F.Seam) (i : Fin 3) :
    (sumSideEquiv F G).symm (Sum.inl (Sum.inl (s, i))) = Sum.inl (Sum.inl s, i) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_symm_inl_inr (e : W₁.Edge) :
    (sumSideEquiv F G).symm (Sum.inl (Sum.inr e)) = Sum.inr (Sum.inl e) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_symm_inr_inl (s : G.Seam) (i : Fin 3) :
    (sumSideEquiv F G).symm (Sum.inr (Sum.inl (s, i))) = Sum.inl (Sum.inr s, i) := by
  simp [sumSideEquiv]

@[simp] theorem sumSideEquiv_symm_inr_inr (e : W₂.Edge) :
    (sumSideEquiv F G).symm (Sum.inr (Sum.inr e)) = Sum.inr (Sum.inr e) := by
  simp [sumSideEquiv]

/-- Equivalence redistributing the circle sides of `F.sum G` into `F.CircleSide ⊕ G.CircleSide`. -/
def sumCircleSideEquiv :
    (((F.SeamCircle ⊕ G.SeamCircle) × Fin 3) ⊕ (W₁.Circle ⊕ W₂.Circle)) ≃
      F.CircleSide ⊕ G.CircleSide :=
  ((Equiv.sumProdDistrib F.SeamCircle G.SeamCircle (Fin 3)).sumCongr (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)

@[simp] theorem sumCircleSideEquiv_inl_inl (c : F.SeamCircle) (i : Fin 3) :
    sumCircleSideEquiv F G (Sum.inl (Sum.inl c, i)) = Sum.inl (Sum.inl (c, i)) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_inl_inr (c : G.SeamCircle) (i : Fin 3) :
    sumCircleSideEquiv F G (Sum.inl (Sum.inr c, i)) = Sum.inr (Sum.inl (c, i)) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_inr_inl (c : W₁.Circle) :
    sumCircleSideEquiv F G (Sum.inr (Sum.inl c)) = Sum.inl (Sum.inr c) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_inr_inr (c : W₂.Circle) :
    sumCircleSideEquiv F G (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_symm_inl_inl (c : F.SeamCircle) (i : Fin 3) :
    (sumCircleSideEquiv F G).symm (Sum.inl (Sum.inl (c, i))) = Sum.inl (Sum.inl c, i) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_symm_inl_inr (c : W₁.Circle) :
    (sumCircleSideEquiv F G).symm (Sum.inl (Sum.inr c)) = Sum.inr (Sum.inl c) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_symm_inr_inl (c : G.SeamCircle) (i : Fin 3) :
    (sumCircleSideEquiv F G).symm (Sum.inr (Sum.inl (c, i))) = Sum.inl (Sum.inr c, i) := by
  simp [sumCircleSideEquiv]

@[simp] theorem sumCircleSideEquiv_symm_inr_inr (c : W₂.Circle) :
    (sumCircleSideEquiv F G).symm (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c) := by
  simp [sumCircleSideEquiv]

private def sumCornerEquiv :
    (((F.Vertex ⊕ G.Vertex) × Fin 6) ⊕ ((W₁.Vertex ⊕ W₂.Vertex) × Fin 3)) ≃
      F.Corner ⊕ G.Corner :=
  ((Equiv.sumProdDistrib F.Vertex G.Vertex (Fin 6)).sumCongr
    (Equiv.sumProdDistrib W₁.Vertex W₂.Vertex (Fin 3))).trans (Equiv.sumSumSumComm _ _ _ _)

@[simp] private theorem sumCornerEquiv_inl_inl (v : F.Vertex) (e : Fin 6) :
    sumCornerEquiv F G (Sum.inl (Sum.inl v, e)) = Sum.inl (Sum.inl (v, e)) := by
  simp [sumCornerEquiv]

@[simp] private theorem sumCornerEquiv_inl_inr (v : G.Vertex) (e : Fin 6) :
    sumCornerEquiv F G (Sum.inl (Sum.inr v, e)) = Sum.inr (Sum.inl (v, e)) := by
  simp [sumCornerEquiv]

@[simp] private theorem sumCornerEquiv_inr_inl (w : W₁.Vertex) (i : Fin 3) :
    sumCornerEquiv F G (Sum.inr (Sum.inl w, i)) = Sum.inl (Sum.inr (w, i)) := by
  simp [sumCornerEquiv]

@[simp] private theorem sumCornerEquiv_inr_inr (w : W₂.Vertex) (i : Fin 3) :
    sumCornerEquiv F G (Sum.inr (Sum.inr w, i)) = Sum.inr (Sum.inr (w, i)) := by
  simp [sumCornerEquiv]

private theorem sum_cornerSideEquiv (dir : Bool)
    (h_inl : ∀ (v : F.Vertex ⊕ G.Vertex) k,
      (sumSeamEnds F G (Sum.inl (v, k))).2 =
        !((ClosedWeb.tetWeb (Sum.elim F.chirality G.chirality v)).ends (k, 0)).2)
    (h_inr : ∀ w : (W₁.sum W₂).Vertex,
      (sumSeamEnds F G (Sum.inr w)).2 = ((W₁.sum W₂).ends (w, 0)).2)
    (c : ((F.Vertex ⊕ G.Vertex) × Fin 6) ⊕ ((W₁.sum W₂).Vertex × Fin 3)) :
    cornerSideEquiv dir (W := W₁.sum W₂) (Sum.elim F.chirality G.chirality)
        (sumSeamEnds F G) h_inl h_inr c =
      (sumSideEquiv F G).symm (((F.cornerSide dir).sumCongr (G.cornerSide dir))
        (sumCornerEquiv F G c)) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · rw [cornerSideEquiv_inl]
    rcases v with v | v
    · cases hc : F.chirality v <;> simp [F.cornerSide_def, hc]
    · cases hc : G.chirality v <;> simp [G.cornerSide_def, hc]
  · rw [cornerSideEquiv_inr]
    rcases w with w | w
    · rw [ClosedWeb.sum_ends_apply_inl]
      by_cases hb : (W₁.ends (w, i)).2 = dir <;> simp [F.cornerSide_def, hb]
    · rw [ClosedWeb.sum_ends_apply_inr]
      by_cases hb : (W₂.ends (w, i)).2 = dir <;> simp [G.cornerSide_def, hb]

private theorem sum_nextSidePerm
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
    sum_cornerSideEquiv F G false h_inl h_inr c, sum_cornerSideEquiv F G true h_inl h_inr c,
    Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rcases sumCornerEquiv F G c with c₁ | c₂ <;> simp [nextSide_apply]

end SumEquiv

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

section SumAPI

variable {W₁ : ClosedWeb.{u}} {W₂ : ClosedWeb.{v}}
  (F : FoamWithBoundary W₁) (G : FoamWithBoundary W₂)

/-- The boundary-walk permutation on `F.sum G` is conjugate via `sumSideEquiv` to the sum of
`F.nextSide` and `G.nextSide`. -/
theorem nextSide_sum :
    (F.sum G).nextSide =
      (sumSideEquiv F G).symm.permCongr (Equiv.Perm.sumCongr F.nextSide G.nextSide) :=
  (F.sum G).nextSide_def.trans
    (sum_nextSidePerm F G (F.sum G).seamEnds_inl_snd (F.sum G).seamEnds_inr_snd)

@[simp] theorem numBoundaryComponents_sum_inl (f : F.Facet) :
    (F.sum G).numBoundaryComponents (Sum.inl f) = F.numBoundaryComponents f := by
  rw [numBoundaryComponents_def, numBoundaryComponents_def,
    Nat.card_congr (Equiv.subtypeSum (p := fun b ↦ (F.sum G).boundaryFacet b = Sum.inl f)),
    Nat.card_sum]
  simp [FacetBoundary]

@[simp] theorem numBoundaryComponents_sum_inr (g : G.Facet) :
    (F.sum G).numBoundaryComponents (Sum.inr g) = G.numBoundaryComponents g := by
  rw [numBoundaryComponents_def, numBoundaryComponents_def,
    Nat.card_congr (Equiv.subtypeSum (p := fun b ↦ (F.sum G).boundaryFacet b = Sum.inr g)),
    Nat.card_sum]
  simp [FacetBoundary]

@[simp] theorem facetEulerChar_sum_inl (f : F.Facet) :
    (F.sum G).facetEulerChar (Sum.inl f) = F.facetEulerChar f := by
  simp [facetEulerChar_def]

@[simp] theorem facetEulerChar_sum_inr (g : G.Facet) :
    (F.sum G).facetEulerChar (Sum.inr g) = G.facetEulerChar g := by
  simp [facetEulerChar_def]

@[simp] theorem isNilvalent_sum_iff :
    (F.sum G).IsNilvalent ↔ F.IsNilvalent ∧ G.IsNilvalent := by
  simp only [isNilvalent_def, isEmpty_sum]
  tauto

end SumAPI

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
    · simp [sumSeamEnds, Prod.map]
    · exact w.elim
    · simp [sumSeamEnds, Prod.map]
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
    · simp [sumSideEquiv]
    · exact e.elim
    · simp [sumSideEquiv]
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · exact c.elim
    · simp [sumCircleSideEquiv]
    · exact c.elim
    · simp [sumCircleSideEquiv]

@[simp] theorem emptySum_vertex {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (emptySum.{u, v} F).vertex = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_seam {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (emptySum.{u, v} F).seam = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_seamCircle {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (emptySum.{u, v} F).seamCircle = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_facet {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (emptySum.{u, v} F).facet = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_boundary {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (emptySum.{u, v} F).boundary = Equiv.emptySum _ _ := (rfl)

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
    · simp [sumSeamEnds, Prod.map]
    · exact v.elim
    · simp [sumSeamEnds, Prod.map]
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
    · simp [sumSideEquiv]
    · exact s.elim
    · simp [sumSideEquiv]
    · exact e.elim
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · simp [sumCircleSideEquiv]
    · exact c.elim
    · simp [sumCircleSideEquiv]
    · exact c.elim

@[simp] theorem sumEmpty_vertex {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (sumEmpty.{u, v} F).vertex = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_seam {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (sumEmpty.{u, v} F).seam = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_seamCircle {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (sumEmpty.{u, v} F).seamCircle = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_facet {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (sumEmpty.{u, v} F).facet = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_boundary {W : ClosedWeb.{u}} (F : FoamWithBoundary W) :
    (sumEmpty.{u, v} F).boundary = Equiv.sumEmpty _ _ := (rfl)

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
  map_seamEnds := by rintro (⟨v | v, k⟩ | (w | w)) <;> simp [Prod.map]
  map_genus := by rintro (f | f) <;> rfl
  map_boundaryFacet := by rintro (b | b) <;> rfl
  map_sideBoundary := by rintro (⟨s | s, i⟩ | (e | e)) <;> simp
  map_circleBoundary := by rintro (⟨c | c, i⟩ | (c | c)) <;> simp

@[simp] theorem sumComm_vertex {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (sumComm F G).vertex = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_seam {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (sumComm F G).seam = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_seamCircle {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (sumComm F G).seamCircle = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_facet {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (sumComm F G).facet = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_boundary {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) :
    (sumComm F G).boundary = Equiv.sumComm _ _ := (rfl)

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
  map_seamEnds := by rintro (⟨(v | v) | v, k⟩ | ((w | w) | w)) <;> simp [sumSeamEnds, Prod.map]
  map_genus := by rintro ((f | f) | f) <;> rfl
  map_boundaryFacet := by rintro ((b | b) | b) <;> rfl
  map_sideBoundary := by rintro (⟨(s | s) | s, i⟩ | ((e | e) | e)) <;> simp [sumSideEquiv]
  map_circleBoundary := by rintro (⟨(c | c) | c, i⟩ | ((c | c) | c)) <;> simp [sumCircleSideEquiv]

@[simp] theorem sumAssoc_vertex {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    (sumAssoc F G H).vertex = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_seam {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    (sumAssoc F G H).seam = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_seamCircle {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    (sumAssoc F G H).seamCircle = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_facet {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    (sumAssoc F G H).facet = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_boundary {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}}
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) (H : FoamWithBoundary U) :
    (sumAssoc F G H).boundary = Equiv.sumAssoc _ _ _ := (rfl)

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
    simp only [Sum.map_inl, Prod.map_apply, id_eq] at h
    simp [h, Prod.map]
  · have h := ψ₂.map_seamEnds (Sum.inl (v, k))
    simp only [Sum.map_inl, Prod.map_apply, id_eq] at h
    simp [h, Prod.map]
  · have h := ψ₁.map_seamEnds (Sum.inr w)
    simp only [Sum.map_inr] at h
    simp [h, Prod.map]
  · have h := ψ₂.map_seamEnds (Sum.inr w)
    simp only [Sum.map_inr] at h
    simp [h, Prod.map]

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
  map_chirality := by rintro (v | v) <;> simp
  map_seamEnds := sum_map_seamEnds ψ₁ ψ₂
  map_genus := by rintro (f | f) <;> simp
  map_boundaryFacet := by rintro (b | b) <;> simp
  map_sideBoundary := by
    rintro (⟨s | s, i⟩ | (e | e))
    · simpa using ψ₁.map_sideBoundary (Sum.inl (s, i))
    · simpa using ψ₂.map_sideBoundary (Sum.inl (s, i))
    · simpa using ψ₁.map_sideBoundary (Sum.inr e)
    · simpa using ψ₂.map_sideBoundary (Sum.inr e)
  map_circleBoundary := by
    rintro (⟨c | c, i⟩ | (c | c))
    · simpa using ψ₁.map_circleBoundary (Sum.inl (c, i))
    · simpa using ψ₂.map_circleBoundary (Sum.inl (c, i))
    · simpa using ψ₁.map_circleBoundary (Sum.inr c)
    · simpa using ψ₂.map_circleBoundary (Sum.inr c)

section IsoOverSumSimp

variable {W₁ : ClosedWeb.{u}} {V₁ : ClosedWeb.{v}} {W₂ U₂ : ClosedWeb}
  {φ₁ : W₁.Iso V₁} {φ₂ : W₂.Iso U₂}
  {F₁ : FoamWithBoundary W₁} {G₁ : FoamWithBoundary V₁}
  {F₂ : FoamWithBoundary W₂} {G₂ : FoamWithBoundary U₂}
  (ψ₁ : F₁.IsoOver φ₁ G₁) (ψ₂ : F₂.IsoOver φ₂ G₂)

@[simp] theorem IsoOver.sum_vertex : (ψ₁.sum ψ₂).vertex = ψ₁.vertex.sumCongr ψ₂.vertex := (rfl)
@[simp] theorem IsoOver.sum_seam : (ψ₁.sum ψ₂).seam = ψ₁.seam.sumCongr ψ₂.seam := (rfl)
@[simp] theorem IsoOver.sum_seamCircle :
    (ψ₁.sum ψ₂).seamCircle = ψ₁.seamCircle.sumCongr ψ₂.seamCircle := (rfl)
@[simp] theorem IsoOver.sum_facet : (ψ₁.sum ψ₂).facet = ψ₁.facet.sumCongr ψ₂.facet := (rfl)
@[simp] theorem IsoOver.sum_boundary :
    (ψ₁.sum ψ₂).boundary = ψ₁.boundary.sumCongr ψ₂.boundary := (rfl)

end IsoOverSumSimp

end FoamWithBoundary

end TauCeti
