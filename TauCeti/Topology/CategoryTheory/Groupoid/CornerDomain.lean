/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Topology.Algebra.Ring.Real
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

/-!
# Corner domains of groupoids

Let `ρ : ι → C → ℝ` be a family of functions on the objects of a category `C`; for an orbifold
presentation these are finitely many smooth functions on the object manifold. The corner domain
`TauCeti.cornerDomain ρ` is the property `0 ≤ ρ i x` for every label `i`. For a set `s` of labels,
the labelled face `TauCeti.cornerFace ρ s` is the part of the corner domain on which `ρ i`
vanishes for every `i ∈ s`, and the boundary `TauCeti.cornerBoundary ρ` is the union of the faces
with a single label. The faces of two label sets intersect in the face of their union
(`TauCeti.cornerFace_union`), the face of no labels is the whole domain, and the points of the
domain off the boundary are those where every `ρ i` is positive.

When every `ρ i` is invariant under isomorphisms (in a groupoid, under every arrow), these
properties are closed under isomorphisms
(`TauCeti.isClosedUnderIsomorphisms_cornerDomain` and its face and boundary versions). When
every `ρ i` is continuous, they cut out closed sets of objects; for the boundary this needs
finitely many labels. The full restriction of a topological groupoid to such a closed saturated
property is the global corner groupoid of the presentation: its objects are the domain and its
arrows are all ambient arrows between them, so every isotropy arrow is retained. The general
theory of full restrictions then applies:

* source and target remain local homeomorphisms
  (`TauCeti.isLocalHomeomorph_source_fullSubcategory_of_isClosedUnderIsomorphisms`), and the
  source-target map remains proper (`TauCeti.isProperMap_source_target_fullSubcategory`);
* the objects and arrows of the restriction are closed subspaces
  (`TauCeti.isClosedEmbedding_obj_fullSubcategory`,
  `TauCeti.isClosedEmbedding_total_fullSubcategory`), and composition is inherited
  (`TauCeti.IsTopologicalGroupoid.fullSubcategory`);
* its coarse space and its fat classifying space are the closed subspaces over the image of the
  domain (`CategoryTheory.ObjectProperty.isClosedEmbedding_isomorphismClasses_map_ι`,
  `CategoryTheory.ObjectProperty.isClosedEmbedding_fatClassifyingSpaceMap_ι`).

These apply equally to every labelled face and to the boundary union, which is a closed union
of faces rather than a single smooth object chart. Each face is labelled individually: an arrow
preserves each `ρ i` separately, so no arrow exchanges two faces.

Products of corner domains are corner domains. Pulling families on `C` and `D` back along the two
projections gives a family on `C × D` labelled by `ι ⊕ κ`, whose domain, faces and boundary are
described by those of the factors (`TauCeti.cornerDomain_sumElim`, `TauCeti.cornerFace_sumElim`
and `TauCeti.cornerBoundary_sumElim`). The cube `[0, 1]^κ` is the corner domain of the
continuous functions `TauCeti.boxFunctions κ` on the unit groupoid of `κ → ℝ`, with the lower
face of the coordinate `j` labelled `Sum.inl j` and its upper face labelled `Sum.inr j`. So a
product of a presentation with an ordered box, with its individually labelled faces, is again a
corner domain.

Only the topology and the combinatorics of labels are treated here. Linear independence of the
active differentials, quadrant charts and compatible collars are additional smooth data on a
corner domain.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

section Basic

variable {C : Type*} [Category C] {ι : Type*} (ρ : ι → C → ℝ)

/-- The corner domain of a family of functions `ρ`: the objects at which every `ρ i` is
nonnegative. -/
def cornerDomain : ObjectProperty C := fun x ↦ ∀ i, 0 ≤ ρ i x

/-- The labelled face of a set `s` of labels: the points of the corner domain at which `ρ i`
vanishes for every `i ∈ s`. -/
def cornerFace (s : Set ι) : ObjectProperty C := fun x ↦ cornerDomain ρ x ∧ ∀ i ∈ s, ρ i x = 0

/-- The boundary of the corner domain: the points of the corner domain at which some `ρ i`
vanishes. It is the union of the faces with one label (`TauCeti.cornerBoundary_eq_iSup`). -/
def cornerBoundary : ObjectProperty C := fun x ↦ cornerDomain ρ x ∧ ∃ i, ρ i x = 0

variable {ρ}

/-- Membership in the corner domain. -/
@[simp]
theorem cornerDomain_iff {x : C} : cornerDomain ρ x ↔ ∀ i, 0 ≤ ρ i x := Iff.rfl

/-- Membership in a labelled face. -/
@[simp]
theorem cornerFace_iff {s : Set ι} {x : C} :
    cornerFace ρ s x ↔ cornerDomain ρ x ∧ ∀ i ∈ s, ρ i x = 0 := Iff.rfl

/-- Membership in the boundary. -/
@[simp]
theorem cornerBoundary_iff {x : C} :
    cornerBoundary ρ x ↔ cornerDomain ρ x ∧ ∃ i, ρ i x = 0 := Iff.rfl

variable (ρ)

/-- The face of the empty set of labels is the whole corner domain. -/
@[simp]
theorem cornerFace_empty : cornerFace ρ ∅ = cornerDomain ρ := by
  ext x
  simp

/-- **Intersection of labelled faces.** The face of a union of label sets is the intersection
of their faces. -/
theorem cornerFace_union (s t : Set ι) :
    cornerFace ρ (s ∪ t) = cornerFace ρ s ⊓ cornerFace ρ t := by
  ext x
  simp only [cornerFace_iff, mem_union, ObjectProperty.prop_inf_iff]
  grind

/-- Adding labels shrinks the face. -/
theorem cornerFace_antitone : Antitone (cornerFace ρ) :=
  fun _ _ hst _ hx ↦ ⟨hx.1, fun i hi ↦ hx.2 i (hst hi)⟩

/-- Every face lies in the corner domain. -/
theorem cornerFace_le_cornerDomain (s : Set ι) : cornerFace ρ s ≤ cornerDomain ρ :=
  fun _ hx ↦ hx.1

/-- The boundary is the union of the faces with one label. -/
theorem cornerBoundary_eq_iSup : cornerBoundary ρ = ⨆ i, cornerFace ρ {i} := by
  ext x
  simp only [cornerBoundary_iff, ObjectProperty.prop_iSup_iff, cornerFace_iff, mem_singleton_iff,
    forall_eq]
  exact ⟨fun ⟨hx, i, hi⟩ ↦ ⟨i, hx, hi⟩, fun ⟨i, hx, hi⟩ ↦ ⟨hx, i, hi⟩⟩

/-- The boundary lies in the corner domain. -/
theorem cornerBoundary_le_cornerDomain : cornerBoundary ρ ≤ cornerDomain ρ :=
  fun _ hx ↦ hx.1

variable {ρ} in
/-- The points of the corner domain off its boundary are those at which every `ρ i` is
positive. -/
theorem cornerDomain_and_not_cornerBoundary_iff {x : C} :
    cornerDomain ρ x ∧ ¬cornerBoundary ρ x ↔ ∀ i, 0 < ρ i x := by
  simp only [cornerDomain_iff, cornerBoundary_iff, not_and, not_exists]
  exact ⟨fun ⟨h0, h⟩ i ↦ (h0 i).lt_of_ne' (h h0 i),
    fun h ↦ ⟨fun i ↦ (h i).le, fun _ i ↦ (h i).ne'⟩⟩

/-- Pulling the defining functions back along a functor pulls back the corner domain. For the
inclusion of an open full subgroupoid, this is the restriction of the corner domain. -/
theorem cornerDomain_comp_obj {D : Type*} [Category D] (F : D ⥤ C) :
    cornerDomain (fun i ↦ ρ i ∘ F.obj) = (cornerDomain ρ).inverseImage F := (rfl)

/-- Pulling the defining functions back along a functor pulls back each labelled face. -/
theorem cornerFace_comp_obj {D : Type*} [Category D] (F : D ⥤ C) (s : Set ι) :
    cornerFace (fun i ↦ ρ i ∘ F.obj) s = (cornerFace ρ s).inverseImage F := (rfl)

/-- Pulling the defining functions back along a functor pulls back the boundary. -/
theorem cornerBoundary_comp_obj {D : Type*} [Category D] (F : D ⥤ C) :
    cornerBoundary (fun i ↦ ρ i ∘ F.obj) = (cornerBoundary ρ).inverseImage F := (rfl)

end Basic

section Saturation

variable {C : Type*} [Category C] {ι : Type*} {ρ : ι → C → ℝ}

/-- For isomorphism-invariant defining functions, the corner domain is closed under
isomorphisms. -/
theorem isClosedUnderIsomorphisms_cornerDomain
    (hρ : ∀ i ⦃x y : C⦄, (x ≅ y) → ρ i x = ρ i y) :
    (cornerDomain ρ).IsClosedUnderIsomorphisms where
  of_iso e hx i := hρ i e ▸ hx i

/-- For isomorphism-invariant defining functions, every labelled face is closed under
isomorphisms. -/
theorem isClosedUnderIsomorphisms_cornerFace
    (hρ : ∀ i ⦃x y : C⦄, (x ≅ y) → ρ i x = ρ i y) (s : Set ι) :
    (cornerFace ρ s).IsClosedUnderIsomorphisms where
  of_iso e hx := ⟨fun i ↦ hρ i e ▸ hx.1 i, fun i hi ↦ hρ i e ▸ hx.2 i hi⟩

/-- For isomorphism-invariant defining functions, the boundary is closed under isomorphisms. -/
theorem isClosedUnderIsomorphisms_cornerBoundary
    (hρ : ∀ i ⦃x y : C⦄, (x ≅ y) → ρ i x = ρ i y) :
    (cornerBoundary ρ).IsClosedUnderIsomorphisms where
  of_iso e hx := ⟨fun i ↦ hρ i e ▸ hx.1 i, hx.2.imp fun i hi ↦ hρ i e ▸ hi⟩

end Saturation

section Topology

variable {C : Type*} [Category C] [TopologicalSpace C] {ι : Type*} {ρ : ι → C → ℝ}

/-- For continuous defining functions, the corner domain is closed. -/
theorem isClosed_cornerDomain (hρ : ∀ i, Continuous (ρ i)) :
    IsClosed {x | cornerDomain ρ x} := by
  simp only [cornerDomain_iff, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const (hρ i)

/-- For continuous defining functions, every labelled face is closed. -/
theorem isClosed_cornerFace (hρ : ∀ i, Continuous (ρ i)) (s : Set ι) :
    IsClosed {x | cornerFace ρ s x} := by
  simp only [cornerFace_iff, ofPred_and, ofPred_forall]
  exact (isClosed_cornerDomain hρ).inter
    (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ isClosed_eq (hρ i) continuous_const)

/-- For finitely many continuous defining functions, the boundary, a finite union of faces, is
closed. -/
theorem isClosed_cornerBoundary [Finite ι] (hρ : ∀ i, Continuous (ρ i)) :
    IsClosed {x | cornerBoundary ρ x} := by
  rw [cornerBoundary_eq_iSup]
  simp only [ObjectProperty.prop_iSup_iff, ofPred_exists]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_cornerFace hρ {i}

end Topology

section Prod

variable {C D : Type*} [Category C] [Category D] {ι κ : Type*} (ρ : ι → C → ℝ) (σ : κ → D → ℝ)

/-- The corner domain of the family on `C × D` pulled back from both factors is the product of
the corner domains. -/
theorem cornerDomain_sumElim {p : C × D} :
    cornerDomain (Sum.elim (fun i (p : C × D) ↦ ρ i p.1) fun j p ↦ σ j p.2) p ↔
      cornerDomain ρ p.1 ∧ cornerDomain σ p.2 := by
  simp [Sum.forall]

/-- The face of the family on `C × D` labelled by `s` on the first factor and `t` on the second
is the product of the two faces. -/
theorem cornerFace_sumElim (s : Set ι) (t : Set κ) {p : C × D} :
    cornerFace (Sum.elim (fun i (p : C × D) ↦ ρ i p.1) fun j p ↦ σ j p.2)
        (Sum.inl '' s ∪ Sum.inr '' t) p ↔
      cornerFace ρ s p.1 ∧ cornerFace σ t p.2 := by
  simp only [cornerFace_iff, cornerDomain_sumElim, mem_union, mem_image]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h⟩
    exact ⟨⟨h₁, fun i hi ↦ h (.inl i) (.inl ⟨i, hi, rfl⟩)⟩,
      ⟨h₂, fun j hj ↦ h (.inr j) (.inr ⟨j, hj, rfl⟩)⟩⟩
  · rintro ⟨⟨h₁, hs⟩, ⟨h₂, ht⟩⟩
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    rintro _ (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    exacts [hs i hi, ht j hj]

/-- The boundary of a product of corner domains is the union of the boundary of the first factor
times the second domain and the first domain times the boundary of the second factor. -/
theorem cornerBoundary_sumElim {p : C × D} :
    cornerBoundary (Sum.elim (fun i (p : C × D) ↦ ρ i p.1) fun j p ↦ σ j p.2) p ↔
      cornerBoundary ρ p.1 ∧ cornerDomain σ p.2 ∨ cornerDomain ρ p.1 ∧ cornerBoundary σ p.2 := by
  simp only [cornerBoundary_iff, cornerDomain_sumElim, Sum.exists, Sum.elim_inl, Sum.elim_inr]
  tauto

end Prod

section Box

variable (κ : Type*)

/-- The defining functions of the cube `[0, 1]^κ` on the unit groupoid of `κ → ℝ`: the
coordinate `t ↦ t j`, labelled `Sum.inl j`, cuts out the lower face of the coordinate `j`, and
`t ↦ 1 - t j`, labelled `Sum.inr j`, cuts out its upper face. -/
def boxFunctions : κ ⊕ κ → Discrete (κ → ℝ) → ℝ :=
  Sum.elim (fun j t ↦ t.as j) fun j t ↦ 1 - t.as j

@[simp]
theorem boxFunctions_inl (j : κ) (t : Discrete (κ → ℝ)) :
    boxFunctions κ (.inl j) t = t.as j := (rfl)

@[simp]
theorem boxFunctions_inr (j : κ) (t : Discrete (κ → ℝ)) :
    boxFunctions κ (.inr j) t = 1 - t.as j := (rfl)

variable {κ}

/-- The defining functions of the cube are continuous for the topology of `κ → ℝ`. -/
theorem continuous_boxFunctions (l : κ ⊕ κ) : Continuous (boxFunctions κ l) := by
  have h : Continuous (Discrete.as : Discrete (κ → ℝ) → κ → ℝ) := continuous_induced_dom
  cases l with
  | inl j => exact (continuous_apply j).comp h
  | inr j => exact continuous_const.sub ((continuous_apply j).comp h)

/-- The defining functions of the cube are invariant under the arrows of the unit groupoid. -/
theorem boxFunctions_eq_of_hom (l : κ ⊕ κ) {t u : Discrete (κ → ℝ)} (f : t ⟶ u) :
    boxFunctions κ l t = boxFunctions κ l u := by
  rw [Discrete.ext (Discrete.eq_of_hom f)]

/-- The corner domain of the defining functions of the cube is the cube `[0, 1]^κ`. -/
theorem cornerDomain_boxFunctions {t : Discrete (κ → ℝ)} :
    cornerDomain (boxFunctions κ) t ↔ t.as ∈ Icc 0 1 := by
  simp only [cornerDomain_iff, Sum.forall, boxFunctions_inl, boxFunctions_inr, sub_nonneg,
    mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]

/-- The face labelled `Sum.inl j` is the lower face `t j = 0` of the cube. -/
theorem cornerFace_boxFunctions_inl {j : κ} {t : Discrete (κ → ℝ)} :
    cornerFace (boxFunctions κ) {.inl j} t ↔ t.as ∈ Icc 0 1 ∧ t.as j = 0 := by
  rw [cornerFace_iff, cornerDomain_boxFunctions]
  simp only [mem_singleton_iff, forall_eq, boxFunctions_inl]

/-- The face labelled `Sum.inr j` is the upper face `t j = 1` of the cube. -/
theorem cornerFace_boxFunctions_inr {j : κ} {t : Discrete (κ → ℝ)} :
    cornerFace (boxFunctions κ) {.inr j} t ↔ t.as ∈ Icc 0 1 ∧ t.as j = 1 := by
  rw [cornerFace_iff, cornerDomain_boxFunctions]
  simp only [mem_singleton_iff, forall_eq, boxFunctions_inr, sub_eq_zero, eq_comm (a := (1 : ℝ))]

/-- The lower and upper faces of the same coordinate do not meet. -/
theorem cornerFace_boxFunctions_inl_inr (j : κ) :
    cornerFace (boxFunctions κ) {.inl j, .inr j} = ⊥ := by
  refine le_bot_iff.mp fun t ⟨_, h⟩ ↦ ?_
  have h₀ := h (.inl j) (by simp)
  have h₁ := h (.inr j) (by simp)
  rw [boxFunctions_inl] at h₀
  rw [boxFunctions_inr, h₀, sub_zero] at h₁
  exact absurd h₁ one_ne_zero

end Box

end TauCeti
