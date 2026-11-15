/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.FoamWithBoundary.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Concrete examples of unlabelled prefoams and signed cyclic boundary words

This file constructs standard closed and bounded prefoams and verifies their facet counts, Euler
characteristics, local seam-sheet multiplicities, and signed cyclic boundary word orientations:

* `Cycle.reverseSigned`: orientation reversal on signed cyclic words `Cycle (α × Bool)`, reversing
  cyclic order while negating every orientation bit, with `coe_signed_three_ne_reverseSigned`
  distinguishing `[+s, +t, -u]` from its orientation reversal `[+u, -t, -s]`.
* `TauCeti.FoamWithBoundary.closedSurface`, `sphere`, `torus`: closed orientable surfaces of genus
  `g` as nilvalent closed prefoams with `χ = 2 - 2g`.
* `TauCeti.FoamWithBoundary.disk`, `annulus`: nilvalent prefoams bounding `ClosedWeb.circle` and
  `ClosedWeb.circles Bool` with `χ = 1` and `χ = 0`.
* `TauCeti.FoamWithBoundary.annulusSeamDisk`: a closed prefoam with one circular seam and two
  facets (an annulus occupying sheet slots `0, 2` and a disk occupying sheet slot `1`),
  demonstrating that distinct local sheet occurrences around a seam can belong to the same global
  facet.
* `TauCeti.FoamWithBoundary.thetaCup`: three half-disk facets glued along one interval seam with
  boundary `ClosedWeb.theta`.
* `TauCeti.FoamWithBoundary.tetrahedralBall`: the cone prefoam over `ClosedWeb.tetWeb c` with one
  interior singular vertex of chirality `c`, four radial seams, and six triangular disk facets.
* `TauCeti.FoamWithBoundary.tetrahedralPillow`: a closed prefoam with two opposite-chirality
  singular tetrahedral vertices, four interval seams, and six digon disk facets.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definition 2.4 and Remark 2.5.
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1 and Remark 2.2.
-/

public section

namespace Cycle

/-- Reverse the orientation of a signed cyclic word by reversing cyclic order and negating every
sign bit. -/
def reverseSigned {α : Type*} (w : Cycle (α × Bool)) : Cycle (α × Bool) :=
  w.reverse.map (Prod.map id Bool.not)

@[simp] theorem reverseSigned_coe {α : Type*} (l : List (α × Bool)) :
    (l : Cycle (α × Bool)).reverseSigned = l.reverse.map (Prod.map id Bool.not) := by
  simp [reverseSigned]

@[simp] theorem reverseSigned_reverseSigned {α : Type*} (w : Cycle (α × Bool)) :
    w.reverseSigned.reverseSigned = w := by
  induction w using Quotient.inductionOn' with | h l =>
  have hmap : (Prod.map (id : α → α) Bool.not ∘ Prod.map id Bool.not) = id := by
    funext ⟨_, b⟩
    simp
  simp [reverseSigned, List.map_reverse, hmap]

/-- Cyclic rotation preserves a signed cyclic word. -/
theorem coe_signed_three_rotate {α : Type*} (s t u : α) :
    ([(s, true), (t, true), (u, false)] : Cycle (α × Bool)) =
      ([(t, true), (u, false), (s, true)] : Cycle (α × Bool)) :=
  Cycle.coe_eq_coe.mpr ⟨1, rfl⟩

/-- Reversing `[+s, +t, -u]` yields `[+u, -t, -s]`. -/
theorem reverseSigned_coe_three {α : Type*} (s t u : α) :
    (([(s, true), (t, true), (u, false)] : Cycle (α × Bool))).reverseSigned =
      ([(u, true), (t, false), (s, false)] : Cycle (α × Bool)) := by
  simp [reverseSigned]

/-- A signed cyclic word `[+s, +t, -u]` is distinct from its orientation reversal `[+u, -t, -s]`
for all `s, t, u : α`. -/
theorem coe_signed_three_ne_reverseSigned {α : Type*} (s t u : α) :
    ([(s, true), (t, true), (u, false)] : Cycle (α × Bool)) ≠
      ([(u, true), (t, false), (s, false)] : Cycle (α × Bool)) := by
  intro h
  have hm :=
    congrArg (fun c : Cycle (α × Bool) ↦ Multiset.count true (c.toMultiset.map Prod.snd)) h
  simp only [Cycle.coe_toMultiset, Multiset.map_coe, List.map_cons, List.map_nil] at hm
  exact absurd hm (by decide)

end Cycle

namespace TauCeti

universe u

namespace FoamWithBoundary

/-! ### Closed orientable surfaces and nilvalent cobordisms -/

/-- A closed connected orientable surface of genus `g`, viewed as a nilvalent closed prefoam. -/
abbrev closedSurface (g : ℕ) : ClosedFoam.{u} where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PEmpty
  Facet := PUnit
  Boundary := PEmpty
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus _ := g
  boundaryFacet := PEmpty.elim
  sideBoundary := isEmptyElim
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective b := b.elim

/-- The 2-sphere as a closed genus-`0` prefoam. -/
abbrev sphere : ClosedFoam.{u} := closedSurface 0

/-- The 2-torus as a closed genus-`1` prefoam. -/
abbrev torus : ClosedFoam.{u} := closedSurface 1

theorem isNilvalent_closedSurface (g : ℕ) : (closedSurface.{u} g).IsNilvalent := by
  rw [isNilvalent_def]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

@[simp] theorem numBoundaryComponents_closedSurface (g : ℕ) :
    (closedSurface.{u} g).numBoundaryComponents PUnit.unit = 0 := by
  simp [numBoundaryComponents_def]

@[simp] theorem facetEulerChar_closedSurface (g : ℕ) :
    (closedSurface.{u} g).facetEulerChar PUnit.unit = 2 - 2 * (g : ℤ) := by
  simp [facetEulerChar_def]

theorem facetEulerChar_sphere : (sphere.{u}).facetEulerChar PUnit.unit = 2 := by
  simp [sphere]

theorem facetEulerChar_torus : (torus.{u}).facetEulerChar PUnit.unit = 0 := by
  simp [torus]

/-- A genus-`0` disk prefoam bounding `ClosedWeb.circle`. -/
abbrev disk : FoamWithBoundary ClosedWeb.circle.{u} where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PEmpty
  Facet := PUnit
  Boundary := PUnit
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus _ := 0
  boundaryFacet _ := PUnit.unit
  sideBoundary := isEmptyElim
  circleBoundary := Sum.elim (fun x ↦ x.1.elim) id
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective := by
    rintro (⟨x, _⟩ | ⟨⟩) (⟨y, _⟩ | ⟨⟩)
    · exact x.elim
    · exact x.elim
    · exact y.elim
    · intro _
      rfl
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective := by
    rintro ⟨⟩
    exact Or.inr ⟨Sum.inr PUnit.unit, rfl⟩

theorem isNilvalent_disk : (disk.{u}).IsNilvalent := by
  rw [isNilvalent_def]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

@[simp] theorem numBoundaryComponents_disk :
    (disk.{u}).numBoundaryComponents PUnit.unit = 1 := by
  rw [numBoundaryComponents_def]
  exact Nat.card_unique

@[simp] theorem facetEulerChar_disk : (disk.{u}).facetEulerChar PUnit.unit = 1 := by
  simp [facetEulerChar_def]

/-- A genus-`0` annulus prefoam bounding two vertex-free circles `ClosedWeb.circles Bool`. -/
abbrev annulus : FoamWithBoundary (ClosedWeb.circles Bool) where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PEmpty
  Facet := PUnit
  Boundary := Bool
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus _ := 0
  boundaryFacet _ := PUnit.unit
  sideBoundary := isEmptyElim
  circleBoundary := Sum.elim (fun x ↦ x.1.elim) id
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective := by
    rintro (⟨x, _⟩ | b₁) (⟨y, _⟩ | b₂)
    · exact x.elim
    · exact x.elim
    · exact y.elim
    · intro h
      exact congrArg Sum.inr h
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective b := Or.inr ⟨Sum.inr b, rfl⟩

theorem isNilvalent_annulus : annulus.IsNilvalent := by
  rw [isNilvalent_def]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

@[simp] theorem numBoundaryComponents_annulus :
    annulus.numBoundaryComponents PUnit.unit = 2 := by
  rw [numBoundaryComponents_def]
  have e : annulus.FacetBoundary PUnit.unit ≃ Bool := Equiv.subtypeUnivEquiv fun _ ↦ rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_bool]

@[simp] theorem facetEulerChar_annulus : annulus.facetEulerChar PUnit.unit = 0 := by
  simp [facetEulerChar_def]

/-! ### Circular seam with repeated global facet in local sheet slots -/

/-- Closed prefoam with one circular seam and two facets: an annulus (`false`) meeting the seam
along sheet slots `0` and `2`, and a disk (`true`) meeting the seam along sheet slot `1`. -/
abbrev annulusSeamDisk : ClosedFoam.{0} where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PUnit
  Facet := Bool
  Boundary := Fin 3
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus _ := 0
  boundaryFacet i := decide (i = 1)
  sideBoundary := isEmptyElim
  circleBoundary := Sum.elim Prod.snd PEmpty.elim
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective := by
    rintro (⟨⟨⟩, i⟩ | c) (⟨⟨⟩, j⟩ | d)
    · intro h
      exact congrArg (fun k ↦ Sum.inl (PUnit.unit, k)) h
    · exact d.elim
    · exact c.elim
    · exact c.elim
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective i := Or.inr ⟨Sum.inl (PUnit.unit, i), rfl⟩

/-- Sheet slots `0` and `2` around the circular seam of `annulusSeamDisk` belong to the same global
annulus facet, distinct from the disk facet in slot `1`. -/
theorem annulusSeamDisk_seamCircleSheetFacet :
    annulusSeamDisk.seamCircleSheetFacet PUnit.unit 0 = false ∧
      annulusSeamDisk.seamCircleSheetFacet PUnit.unit 1 = true ∧
      annulusSeamDisk.seamCircleSheetFacet PUnit.unit 2 = false := by
  simp

@[simp] theorem numBoundaryComponents_annulusSeamDisk_false :
    annulusSeamDisk.numBoundaryComponents false = 2 := by
  rw [numBoundaryComponents_def,
    Nat.card_eq_fintype_card (α := annulusSeamDisk.FacetBoundary false)]
  decide

@[simp] theorem numBoundaryComponents_annulusSeamDisk_true :
    annulusSeamDisk.numBoundaryComponents true = 1 := by
  rw [numBoundaryComponents_def,
    Nat.card_eq_fintype_card (α := annulusSeamDisk.FacetBoundary true)]
  decide

@[simp] theorem facetEulerChar_annulusSeamDisk_false :
    annulusSeamDisk.facetEulerChar false = 0 := by
  simp [facetEulerChar_def]

@[simp] theorem facetEulerChar_annulusSeamDisk_true :
    annulusSeamDisk.facetEulerChar true = 1 := by
  simp [facetEulerChar_def]

/-! ### Singular prefoams with interval seams and tetrahedral vertices -/

/-- Cup prefoam bounding `ClosedWeb.theta`: three half-disk facets glued along a single interval
seam from the merge vertex `false` to the split vertex `true`. -/
abbrev thetaCup : FoamWithBoundary ClosedWeb.theta where
  Vertex := PEmpty
  Seam := PUnit
  SeamCircle := PEmpty
  Facet := Fin 3
  Boundary := Fin 3
  chirality := PEmpty.elim
  seamEnds := (Equiv.emptySum (PEmpty × Fin 4) Bool).trans (Equiv.punitProd Bool).symm
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := by cases w <;> rfl
  genus _ := 0
  boundaryFacet := id
  sideBoundary := Sum.elim Prod.snd id
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x y := by revert x y; decide
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary _ z := isEmptyElim z
  boundary_surjective i := Or.inl ⟨Sum.inr i, rfl⟩

@[simp] theorem numBoundaryComponents_thetaCup (i : Fin 3) :
    thetaCup.numBoundaryComponents i = 1 := by
  rw [numBoundaryComponents_def, Nat.card_eq_fintype_card (α := thetaCup.FacetBoundary i)]
  revert i
  decide

@[simp] theorem facetEulerChar_thetaCup (i : Fin 3) :
    thetaCup.facetEulerChar i = 1 := by
  simp [facetEulerChar_def]

/-- Seam-end pairing for `tetrahedralBall`: radial seam `k : Fin 4` connects interior branch `k` of
the central vertex to boundary vertex `k` of `ClosedWeb.tetWeb c`. -/
@[expose] def tetrahedralBallSeamEnds (c : Bool) :
    (PUnit.{1} × Fin 4) ⊕ (ClosedWeb.tetWeb c).Vertex ≃ Fin 4 × Bool where
  toFun x := match x with
    | Sum.inl (_, k) => (k, !((ClosedWeb.tetWeb c).ends (k, 0)).2)
    | Sum.inr k => (k, ((ClosedWeb.tetWeb c).ends (k, 0)).2)
  invFun kb :=
    if kb.2 = ((ClosedWeb.tetWeb c).ends (kb.1, 0)).2 then Sum.inr kb.1
    else Sum.inl (PUnit.unit, kb.1)
  left_inv x := by revert c x; decide
  right_inv kb := by revert c kb; decide

/-- Cone prefoam over `ClosedWeb.tetWeb c` with one interior tetrahedral vertex of chirality `c`,
four radial seams, and six triangular disk facets. -/
abbrev tetrahedralBall (c : Bool) : FoamWithBoundary (ClosedWeb.tetWeb c) where
  Vertex := PUnit.{1}
  Seam := Fin 4
  SeamCircle := PEmpty
  Facet := Fin 6
  Boundary := Fin 6
  chirality _ := c
  seamEnds := tetrahedralBallSeamEnds c
  seamEnds_inl_snd _ _ := rfl
  seamEnds_inr_snd _ := rfl
  genus _ := 0
  boundaryFacet := id
  sideBoundary x := match x with
    | Sum.inl (k, i) => ((ClosedWeb.tetWeb c).ends (k, i)).1
    | Sum.inr e => e
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x y := by revert c x y; decide
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary _ z := isEmptyElim z
  boundary_surjective e := Or.inl ⟨Sum.inr e, rfl⟩

@[simp] theorem numBoundaryComponents_tetrahedralBall (c : Bool) (e : Fin 6) :
    (tetrahedralBall c).numBoundaryComponents e = 1 := by
  rw [numBoundaryComponents_def,
    Nat.card_eq_fintype_card (α := (tetrahedralBall c).FacetBoundary e)]
  revert c e
  decide

@[simp] theorem facetEulerChar_tetrahedralBall (c : Bool) (e : Fin 6) :
    (tetrahedralBall c).facetEulerChar e = 1 := by
  simp [facetEulerChar_def]

/-- Seam-end pairing for `tetrahedralPillow`, gluing a positive tetrahedral vertex (`true`) and a
negative tetrahedral vertex (`false`) along `ClosedWeb.tetRevVertexEquiv`. -/
@[expose] def tetrahedralPillowSeamEnds :
    (Bool × Fin 4) ⊕ PEmpty.{1} ≃ Fin 4 × Bool where
  toFun x := match x with
    | Sum.inl (false, k) => (k, !(ClosedWeb.tetrahedronNeg.ends (k, 0)).2)
    | Sum.inl (true, k) =>
      (ClosedWeb.tetRevVertexEquiv k, !(ClosedWeb.tetrahedronPos.ends (k, 0)).2)
    | Sum.inr w => w.elim
  invFun sb :=
    if sb.2 = !(ClosedWeb.tetrahedronNeg.ends (sb.1, 0)).2 then Sum.inl (false, sb.1)
    else Sum.inl (true, ClosedWeb.tetRevVertexEquiv.symm sb.1)
  left_inv x := by revert x; decide
  right_inv sb := by revert sb; decide

/-- Closed prefoam obtained by gluing two opposite-chirality singular tetrahedral vertices along
four interval seams and six digon disk facets. -/
abbrev tetrahedralPillow : ClosedFoam.{0} where
  Vertex := Bool
  Seam := Fin 4
  SeamCircle := PEmpty
  Facet := Fin 6
  Boundary := Fin 6
  chirality := id
  seamEnds := tetrahedralPillowSeamEnds
  seamEnds_inl_snd b k := by revert b k; decide
  seamEnds_inr_snd w := w.elim
  genus _ := 0
  boundaryFacet := id
  sideBoundary x := match x with
    | Sum.inl (s, i) => (ClosedWeb.tetrahedronNeg.ends (s, i)).1
    | Sum.inr e => e.elim
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x y := by revert x y; decide
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary _ z := isEmptyElim z
  boundary_surjective e := by
    obtain ⟨⟨s, i⟩, h⟩ := ClosedWeb.tetrahedronNeg.ends.surjective (e, false)
    exact Or.inl ⟨Sum.inl (s, i), congrArg Prod.fst h⟩

@[simp] theorem numBoundaryComponents_tetrahedralPillow (e : Fin 6) :
    tetrahedralPillow.numBoundaryComponents e = 1 := by
  rw [numBoundaryComponents_def,
    Nat.card_eq_fintype_card (α := tetrahedralPillow.FacetBoundary e)]
  revert e
  decide

@[simp] theorem facetEulerChar_tetrahedralPillow (e : Fin 6) :
    tetrahedralPillow.facetEulerChar e = 1 := by
  simp [facetEulerChar_def]

end FoamWithBoundary

end TauCeti
