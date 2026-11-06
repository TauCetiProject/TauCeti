/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.RegionBetween
public import TauCeti.Analysis.Convex.SimplicialComplex.Restrict
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier
import TauCeti.Data.Set.Prod
import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision

/-!
# Triangulating rectilinear cells over a simplicial complex

Let `K` be a geometric simplicial complex in a finite-dimensional real normed space `E`. A
*section* over a face `s` of `K` is a continuous affine function `a : E → ℝ`, considered on the
simplex `convexHull ℝ s` only; it is recorded as the pair `(s, a)`. Given a family `S` of sections,
the *rectilinear cells* of `S` (`TauCeti.rectilinearCells S`) are the convex polytopes in `E × ℝ`

* the graphs `(convexHull ℝ s).graphOn a` of the sections `(s, a) ∈ S`
  (`TauCeti.rectilinearGraphs S`), and
* the closed bands `TauCeti.closedRegionBetween a b (convexHull ℝ s)` between two sections over
  the same face which are *consecutive*: `a ≤ b` on `s`, `a < b` somewhere on `s`, and every
  section over `s` between `a` and `b` agrees with one of them on `s`
  (`TauCeti.IsConsecutiveSections`, `TauCeti.rectilinearBands S`).

These are the rectilinear cells of Łojasiewicz's triangulation of semianalytic sets, obtained by
replacing the graphs of a prismatic family over a base triangulation by the affine functions with
the same heights at the vertices. Suppose that the faces of a section graph are again section
graphs (`(s, a) ∈ S` and `t ⊆ s` give `(t, a) ∈ S`), that the sections over each face are totally
ordered on its vertices (`TauCeti.IsTotalOnVertices`), that the section graphs form a locally
finite family and that `K` is locally finite. Then the rectilinear cells have a simplicial
subdivision: a locally finite complex `L` in `E × ℝ` with `|L| = ⋃₀ rectilinearCells S`,
triangulating every cell by finitely many of its simplices
(`TauCeti.exists_subdivision_rectilinearCells`). If the sections over every face are
unbounded above and below, the cells cover the whole cylinder `|K| × ℝ`
(`TauCeti.sUnion_rectilinearCells`).

The proof checks the hypotheses of the subdivision of a locally finite family of compact convex
cells (`Geometry.SimplicialComplex.exists_subdivision`).

* The intrinsic interior of a graph or a band lies over the open simplex of its base face
  (`ContinuousAffineMap.intrinsicInterior_graphOn`, `TauCeti.intrinsicInterior_closedRegionBetween`)
  and open simplices of distinct faces are disjoint. Over a single open simplex an affine
  inequality `a ≤ b` between ordered sections is strict unless `a = b` on the whole face
  (`TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior`), so distinct cells have disjoint
  intrinsic interiors: two bands between consecutive sections over a face coincide or lie one
  above the other.
* A point of a band between ordered sections lies in the intrinsic interior of a smaller cell:
  over the face carrying its base point, the finitely many sections between the two bounds have a
  largest value below the point and a smallest value above it. Those two sections are consecutive,
  and the point lies on one of their graphs or in the band between them. Applied to the intrinsic
  frontier of a cell, this covers it by strictly smaller cells.
* Only finitely many cells meet a ball. A band meeting it either has a bounding graph meeting it,
  which determines the band, or crosses the ball; over each face at most one band crosses it, since
  the upper section of the lower of two such bands would meet the ball.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §2, Lemma 15, and §4.
-/

public section

open Set Filter Topology Metric Geometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sections over each face of a family `S` are totally ordered on the vertices of the face:
for `(s, a), (s, b) ∈ S`, either `a ≤ b` or `b ≤ a` on `s`. -/
def IsTotalOnVertices (S : Set (Finset E × (E →ᴬ[ℝ] ℝ))) : Prop :=
  ∀ s a b, (s, a) ∈ S → (s, b) ∈ S → (∀ x ∈ s, a x ≤ b x) ∨ ∀ x ∈ s, b x ≤ a x

/-- Two sections `a, b` over a face `s` are consecutive in the family `S`: `a ≤ b` on `s`, with
`a < b` somewhere on `s`, and every section of `S` over `s` between `a` and `b` agrees on `s` with
one of them. -/
structure IsConsecutiveSections (S : Set (Finset E × (E →ᴬ[ℝ] ℝ))) (s : Finset E)
    (a b : E →ᴬ[ℝ] ℝ) : Prop where
  /-- The lower section lies below the upper one on the vertices. -/
  le : ∀ x ∈ s, a x ≤ b x
  /-- The lower section lies strictly below the upper one at some vertex. -/
  exists_lt : ∃ x ∈ s, a x < b x
  /-- Every section over `s` between the two agrees on `s` with one of them. -/
  eq_or_eq : ∀ c, (s, c) ∈ S → (∀ x ∈ s, a x ≤ c x) → (∀ x ∈ s, c x ≤ b x) →
    (∀ x ∈ s, c x = a x) ∨ ∀ x ∈ s, c x = b x

/-- The graph cells of a family of sections `S`: the graphs of the affine functions `a` over the
simplices `convexHull ℝ s`, for `(s, a) ∈ S`. -/
def rectilinearGraphs (S : Set (Finset E × (E →ᴬ[ℝ] ℝ))) : Set (Set (E × ℝ)) :=
  (fun p ↦ (convexHull ℝ (p.1 : Set E)).graphOn p.2) '' S

/-- The band cells of a family of sections `S`: the closed bands over `convexHull ℝ s` between
two sections `(s, a), (s, b) ∈ S` which are consecutive over `s`. -/
def rectilinearBands (S : Set (Finset E × (E →ᴬ[ℝ] ℝ))) : Set (Set (E × ℝ)) :=
  {C | ∃ s a b, (s, a) ∈ S ∧ (s, b) ∈ S ∧ IsConsecutiveSections S s a b ∧
    closedRegionBetween a b (convexHull ℝ (s : Set E)) = C}

/-- The rectilinear cells of a family of sections `S`: its graph cells and its band cells. -/
def rectilinearCells (S : Set (Finset E × (E →ᴬ[ℝ] ℝ))) : Set (Set (E × ℝ)) :=
  rectilinearGraphs S ∪ rectilinearBands S

variable {S : Set (Finset E × (E →ᴬ[ℝ] ℝ))} {C : Set (E × ℝ)}

@[simp]
theorem mem_rectilinearGraphs :
    C ∈ rectilinearGraphs S ↔ ∃ p ∈ S, (convexHull ℝ (p.1 : Set E)).graphOn p.2 = C :=
  Iff.rfl

@[simp]
theorem mem_rectilinearBands :
    C ∈ rectilinearBands S ↔ ∃ s a b, (s, a) ∈ S ∧ (s, b) ∈ S ∧ IsConsecutiveSections S s a b ∧
      closedRegionBetween a b (convexHull ℝ (s : Set E)) = C :=
  Iff.rfl

@[simp]
theorem mem_rectilinearCells :
    C ∈ rectilinearCells S ↔ C ∈ rectilinearGraphs S ∨ C ∈ rectilinearBands S :=
  Iff.rfl

/-! ### Ordered sections over a face -/

section Ordered

variable {s : Finset E} {a b c a₁ b₁ a₂ b₂ : E →ᴬ[ℝ] ℝ} {x : E}

/-- Ordered sections which agree at an intrinsic interior point of a simplex agree on the whole
simplex. -/
private theorem eq_of_eq (hSle : IsTotalOnVertices S) (ha : (s, a) ∈ S) (hb : (s, b) ∈ S)
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) (h : a x = b x) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E)) : a y = b y := by
  rcases hSle s a b ha hb with hab | hba
  · exact eq_of_le_of_mem_intrinsicInterior hab hx h hy
  · exact (eq_of_le_of_mem_intrinsicInterior hba hx h.symm hy).symm

/-- A section which is smaller than another at a point of the simplex is smaller on all of it. -/
private theorem le_of_lt (hSle : IsTotalOnVertices S) (ha : (s, a) ∈ S) (hb : (s, b) ∈ S)
    (hx : x ∈ convexHull ℝ (s : Set E)) (h : a x < b x) : ∀ y ∈ s, a y ≤ b y :=
  (hSle s a b ha hb).resolve_right fun hba ↦ (le_of_forall_le_of_mem_convexHull hba hx).not_gt h

/-- No section lies strictly between two consecutive sections at any point of the simplex. -/
private theorem not_lt_of_lt (hSle : IsTotalOnVertices S) (ha : (s, a) ∈ S) (hb : (s, b) ∈ S)
    (hab : IsConsecutiveSections S s a b) (hc : (s, c) ∈ S) (hx : x ∈ convexHull ℝ (s : Set E))
    (h₁ : a x < c x) : ¬c x < b x := by
  intro h₂
  rcases hab.eq_or_eq c hc (le_of_lt hSle ha hc hx h₁) (le_of_lt hSle hc hb hx h₂) with he | he
  · exact h₁.not_ge (le_of_forall_le_of_mem_convexHull (fun v hv ↦ (he v hv).le) hx)
  · exact h₂.not_ge (le_of_forall_le_of_mem_convexHull (fun v hv ↦ (he v hv).ge) hx)

/-- Two bands between consecutive sections over the same face, with the lower section of the
first below that of the second, coincide or lie one above the other. -/
private theorem band_trichotomy_of_le (hSle : IsTotalOnVertices S) (hb₁ : (s, b₁) ∈ S)
    (h₁ : IsConsecutiveSections S s a₁ b₁) (ha₂ : (s, a₂) ∈ S) (hb₂ : (s, b₂) ∈ S)
    (h₂ : IsConsecutiveSections S s a₂ b₂) (h : ∀ x ∈ s, a₁ x ≤ a₂ x) :
    ((∀ x ∈ s, a₁ x = a₂ x) ∧ ∀ x ∈ s, b₁ x = b₂ x) ∨ (∀ x ∈ s, b₁ x ≤ a₂ x) ∨
      ∀ x ∈ s, b₂ x ≤ a₁ x := by
  rcases hSle s a₂ b₁ ha₂ hb₁ with h₃ | h₃
  · rcases h₁.eq_or_eq a₂ ha₂ h h₃ with he | he
    · -- the lower sections agree; then so do the upper ones
      rcases hSle s b₁ b₂ hb₁ hb₂ with h₄ | h₄
      · rcases h₂.eq_or_eq b₁ hb₁ (fun x hx ↦ (he x hx).trans_le (h₁.le x hx)) h₄ with he' | he'
        · obtain ⟨x, hx, hlt⟩ := h₁.exists_lt
          exact absurd hlt (by rw [he' x hx, he x hx]; exact lt_irrefl _)
        · exact .inl ⟨fun x hx ↦ (he x hx).symm, he'⟩
      · rcases h₁.eq_or_eq b₂ hb₂ (fun x hx ↦ (he x hx).symm.trans_le (h₂.le x hx)) h₄ with
          he' | he'
        · obtain ⟨x, hx, hlt⟩ := h₂.exists_lt
          exact absurd hlt (by rw [he' x hx, ← he x hx]; exact lt_irrefl _)
        · exact .inl ⟨fun x hx ↦ (he x hx).symm, fun x hx ↦ (he' x hx).symm⟩
    · exact .inr (.inl fun x hx ↦ (he x hx).ge)
  · exact .inr (.inl h₃)

/-- Two bands between consecutive sections over the same face coincide or lie one above the
other. -/
private theorem band_trichotomy (hSle : IsTotalOnVertices S) (ha₁ : (s, a₁) ∈ S)
    (hb₁ : (s, b₁) ∈ S) (h₁ : IsConsecutiveSections S s a₁ b₁) (ha₂ : (s, a₂) ∈ S)
    (hb₂ : (s, b₂) ∈ S) (h₂ : IsConsecutiveSections S s a₂ b₂) :
    closedRegionBetween a₁ b₁ (convexHull ℝ (s : Set E)) =
        closedRegionBetween a₂ b₂ (convexHull ℝ (s : Set E)) ∨
      (∀ x ∈ s, b₁ x ≤ a₂ x) ∨ ∀ x ∈ s, b₂ x ≤ a₁ x := by
  -- sections agreeing on the vertices agree on the simplex
  have hcongr : ∀ {f g : E →ᴬ[ℝ] ℝ}, (∀ x ∈ s, f x = g x) → EqOn f g (convexHull ℝ (s : Set E)) :=
    fun {f g} h ↦ (AffineMap.eqOn_affineSpan (f := (f : E →ᵃ[ℝ] ℝ)) (g := g) h).mono
      (convexHull_subset_affineSpan _)
  rcases hSle s a₁ a₂ ha₁ ha₂ with h | h
  · rcases band_trichotomy_of_le hSle hb₁ h₁ ha₂ hb₂ h₂ h with ⟨he, he'⟩ | h'
    · exact .inl (closedRegionBetween_congr (hcongr he) (hcongr he'))
    · exact .inr h'
  · rcases band_trichotomy_of_le hSle hb₂ h₂ ha₁ hb₁ h₁ h with ⟨he, he'⟩ | h'
    · exact .inl (closedRegionBetween_congr (hcongr he) (hcongr he')).symm
    · exact .inr h'.symm

end Ordered

/-! ### The cells -/

section Cells

variable {K : SimplicialComplex ℝ E}

/-- Every rectilinear cell is a closed band between ordered sections over a face; a graph is a
degenerate band. -/
private theorem exists_eq_closedRegionBetween (hC : C ∈ rectilinearCells S) :
    ∃ s a b, (s, a) ∈ S ∧ (s, b) ∈ S ∧ (∀ x ∈ s, a x ≤ b x) ∧
      closedRegionBetween a b (convexHull ℝ (s : Set E)) = C := by
  rcases hC with ⟨⟨s, a⟩, ha, rfl⟩ | ⟨s, a, b, ha, hb, hab, rfl⟩
  · exact ⟨s, a, a, ha, ha, fun _ _ ↦ le_rfl, closedRegionBetween_self _ _⟩
  · exact ⟨s, a, b, ha, hb, hab.le, rfl⟩

/-- The cells are compact. -/
private theorem isCompact_of_mem_rectilinearCells (hC : C ∈ rectilinearCells S) : IsCompact C := by
  obtain ⟨s, a, b, -, -, hab, rfl⟩ := exists_eq_closedRegionBetween hC
  exact isCompact_closedRegionBetween_convexHull (a := (a : E →ᵃ[ℝ] ℝ)) (b := b) s.finite_toSet hab

/-- The cells are convex. -/
private theorem convex_of_mem_rectilinearCells (hC : C ∈ rectilinearCells S) : Convex ℝ C := by
  obtain ⟨s, a, b, -, -, hab, rfl⟩ := exists_eq_closedRegionBetween hC
  have h : closedRegionBetween a b (convexHull ℝ (s : Set E)) =
      convexHull ℝ ((s : Set E).graphOn a ∪ (s : Set E).graphOn b) :=
    closedRegionBetween_convexHull (a := (a : E →ᵃ[ℝ] ℝ)) (b := b) hab
  rw [h]
  exact convex_convexHull ℝ _

/-- The cells are nonempty. -/
private theorem nonempty_of_mem_rectilinearCells (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hC : C ∈ rectilinearCells S) : C.Nonempty := by
  obtain ⟨s, a, b, ha, -, hab, rfl⟩ := exists_eq_closedRegionBetween hC
  obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces (hS _ ha)
  exact ⟨(x, a x), mem_closedRegionBetween.2 ⟨subset_convexHull ℝ _ hx, le_rfl, hab x hx⟩⟩

/-- The intrinsic interior of a band between consecutive sections lies strictly between them
over the open simplex. -/
private theorem mem_intrinsicInterior_band {s : Finset E} {a b : E →ᴬ[ℝ] ℝ}
    (hab : ∀ x ∈ s, a x ≤ b x) (hlt : ∃ x ∈ s, a x < b x) {z : E × ℝ}
    (hz : z ∈ intrinsicInterior ℝ (closedRegionBetween a b (convexHull ℝ (s : Set E)))) :
    z.1 ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧ a z.1 < z.2 ∧ z.2 < b z.1 := by
  obtain ⟨x, hx, hxlt⟩ := hlt
  rw [intrinsicInterior_closedRegionBetween (fun y hy ↦ le_of_forall_le_of_mem_convexHull hab hy)
    ⟨x, subset_convexHull ℝ _ hx, hxlt⟩] at hz
  exact ⟨hz.1, hz.2.1, hz.2.2⟩

/-- A graph cell and a band cell have disjoint intrinsic interiors. -/
private theorem notMem_intrinsicInterior_band (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSle : IsTotalOnVertices S) {s t : Finset E} {c a b : E →ᴬ[ℝ] ℝ} (hc : (s, c) ∈ S)
    (ha : (t, a) ∈ S) (hb : (t, b) ∈ S) (hab : IsConsecutiveSections S t a b) {z : E × ℝ}
    (hz : z ∈ intrinsicInterior ℝ ((convexHull ℝ (s : Set E)).graphOn c)) :
    z ∉ intrinsicInterior ℝ (closedRegionBetween a b (convexHull ℝ (t : Set E))) := by
  intro hz'
  rw [ContinuousAffineMap.intrinsicInterior_graphOn, mem_graphOn] at hz
  obtain ⟨hzt, h₁, h₂⟩ := mem_intrinsicInterior_band hab.le hab.exists_lt hz'
  obtain rfl := SimplicialComplex.eq_of_mem_intrinsicInterior (hS _ hc) (hS _ ha) hz.1 hzt
  rw [← hz.2] at h₁ h₂
  exact not_lt_of_lt hSle ha hb hab hc (intrinsicInterior_subset hz.1) h₁ h₂

/-- **Distinct cells have disjoint intrinsic interiors.** -/
private theorem eq_of_mem_intrinsicInterior_rectilinearCells (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSle : IsTotalOnVertices S)
    {D : Set (E × ℝ)} (hC : C ∈ rectilinearCells S) (hD : D ∈ rectilinearCells S) {z : E × ℝ}
    (hzC : z ∈ intrinsicInterior ℝ C) (hzD : z ∈ intrinsicInterior ℝ D) : C = D := by
  rcases hC with ⟨⟨s, a⟩, ha, rfl⟩ | ⟨s, a₁, b₁, ha₁, hb₁, h₁, rfl⟩ <;>
    rcases hD with ⟨⟨t, c⟩, hc, rfl⟩ | ⟨t, a₂, b₂, ha₂, hb₂, h₂, rfl⟩
  · -- two graphs
    rw [ContinuousAffineMap.intrinsicInterior_graphOn, mem_graphOn] at hzC hzD
    obtain rfl := SimplicialComplex.eq_of_mem_intrinsicInterior (hS _ ha) (hS _ hc) hzC.1 hzD.1
    have h := fun y (hy : y ∈ convexHull ℝ (s : Set E)) ↦
      eq_of_eq hSle ha hc hzC.1 (hzC.2.trans hzD.2.symm) hy
    dsimp only
    rw [← closedRegionBetween_self, ← closedRegionBetween_self]
    exact closedRegionBetween_congr h h
  · exact (notMem_intrinsicInterior_band hS hSle ha ha₂ hb₂ h₂ hzC hzD).elim
  · exact (notMem_intrinsicInterior_band hS hSle hc ha₁ hb₁ h₁ hzD hzC).elim
  · -- two bands
    obtain ⟨hzs, hz₁, hz₂⟩ := mem_intrinsicInterior_band h₁.le h₁.exists_lt hzC
    obtain ⟨hzt, hz₃, hz₄⟩ := mem_intrinsicInterior_band h₂.le h₂.exists_lt hzD
    obtain rfl := SimplicialComplex.eq_of_mem_intrinsicInterior (hS _ ha₁) (hS _ ha₂) hzs hzt
    have hz := intrinsicInterior_subset hzs
    rcases band_trichotomy hSle ha₁ hb₁ h₁ ha₂ hb₂ h₂ with h | h | h
    · exact h
    all_goals
      have h' := le_of_forall_le_of_mem_convexHull (s := (s : Set E)) h hz
      simp only [ContinuousAffineMap.coe_toAffineMap] at h'
      linarith

/-- Above a point of a simplex, the sections over it lying between two ordered sections take only
finitely many values, since their graphs meet a compact band. -/
private theorem finite_image_apply
    (hSlf : LocallyFinite fun C : rectilinearGraphs S ↦ (C : Set (E × ℝ)))
    {t : Finset E} {a b : E →ᴬ[ℝ] ℝ} (hab : ∀ v ∈ t, a v ≤ b v) {x : E}
    (hx : x ∈ convexHull ℝ (t : Set E)) :
    ((fun c : E →ᴬ[ℝ] ℝ ↦ c x) ''
      {c | (t, c) ∈ S ∧ (∀ v ∈ t, a v ≤ c v) ∧ ∀ v ∈ t, c v ≤ b v}).Finite := by
  -- each graph meeting the band contributes at most one value above `x`
  refine ((hSlf.finite_nonempty_inter_compact (isCompact_closedRegionBetween_convexHull
    (a := (a : E →ᵃ[ℝ] ℝ)) (b := b) t.finite_toSet hab)).biUnion
    fun D _ ↦ (show {q : ℝ | (x, q) ∈ (D : Set (E × ℝ))}.Subsingleton from ?_).finite).subset ?_
  · obtain ⟨⟨u, c⟩, -, hD⟩ := D.2
    intro q₁ hq₁ q₂ hq₂
    simp only [mem_ofPred_eq, ← hD, mem_graphOn] at hq₁ hq₂
    exact hq₁.2.symm.trans hq₂.2
  · rintro _ ⟨c, hc, rfl⟩
    exact mem_iUnion₂.2 ⟨⟨_, ⟨(t, c), hc.1, rfl⟩⟩, ⟨(x, c x), mem_graphOn.2 ⟨hx, rfl⟩,
      mem_closedRegionBetween.2 ⟨hx, le_of_forall_le_of_mem_convexHull hc.2.1 hx,
        le_of_forall_le_of_mem_convexHull hc.2.2 hx⟩⟩, mem_graphOn.2 ⟨hx, rfl⟩⟩

/-- **Covering a band by smaller cells.** Every point of the closed band between two ordered
sections over a face lies in the intrinsic interior of a cell contained in that band. -/
private theorem exists_mem_intrinsicInterior (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSface : ∀ p ∈ S, ∀ t ⊆ p.1, t.Nonempty → (t, p.2) ∈ S)
    (hSle : IsTotalOnVertices S)
    (hSlf : LocallyFinite fun C : rectilinearGraphs S ↦ (C : Set (E × ℝ)))
    {s : Finset E} {a b : E →ᴬ[ℝ] ℝ} (ha : (s, a) ∈ S) (hb : (s, b) ∈ S)
    (hab : ∀ x ∈ s, a x ≤ b x) {z : E × ℝ}
    (hz : z ∈ closedRegionBetween a b (convexHull ℝ (s : Set E))) :
    ∃ D ∈ rectilinearCells S, z ∈ intrinsicInterior ℝ D ∧
      D ⊆ closedRegionBetween a b (convexHull ℝ (s : Set E)) := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hx, hay, hyb⟩ := mem_closedRegionBetween.1 hz
  -- work over the face `t` whose open simplex carries `x`
  obtain ⟨t, ht, hts, hxt⟩ :=
    SimplicialComplex.exists_mem_faces_subset_mem_intrinsicInterior (hS _ ha) hx
  have htne := K.nonempty_of_mem_faces ht
  have hxt' : x ∈ convexHull ℝ (t : Set E) := intrinsicInterior_subset hxt
  have hts' : convexHull ℝ (t : Set E) ⊆ convexHull ℝ (s : Set E) :=
    convexHull_mono (Finset.coe_subset.2 hts)
  have habt : ∀ v ∈ t, a v ≤ b v := fun v hv ↦ hab v (hts hv)
  -- the sections over `t` between `a` and `b`
  set T := {c : E →ᴬ[ℝ] ℝ | (t, c) ∈ S ∧ (∀ v ∈ t, a v ≤ c v) ∧ ∀ v ∈ t, c v ≤ b v}
  have hsub : ∀ {c d : E →ᴬ[ℝ] ℝ}, c ∈ T → d ∈ T →
      closedRegionBetween c d (convexHull ℝ (t : Set E)) ⊆
        closedRegionBetween a b (convexHull ℝ (s : Set E)) := by
    rintro c d hc hd ⟨p, q⟩ hpq
    obtain ⟨hp, hcq, hqd⟩ := mem_closedRegionBetween.1 hpq
    exact mem_closedRegionBetween.2 ⟨hts' hp,
      (le_of_forall_le_of_mem_convexHull hc.2.1 hp).trans hcq,
      hqd.trans (le_of_forall_le_of_mem_convexHull hd.2.2 hp)⟩
  -- their values at `x` form a finite set
  have hV : ((fun c : E →ᴬ[ℝ] ℝ ↦ c x) '' T).Finite := finite_image_apply hSlf habt hxt'
  -- the largest value at most `y` and the smallest value at least `y`
  obtain ⟨_, ⟨⟨c₀, hT₀, rfl⟩, h₀⟩, hmax⟩ := exists_max_image ((fun c ↦ c x) '' T ∩ Iic y) id
    (hV.inter_of_left _) ⟨a x, ⟨a, ⟨hSface _ ha t hts htne, fun _ _ ↦ le_rfl, habt⟩, rfl⟩, hay⟩
  obtain ⟨_, ⟨⟨c₁, hT₁, rfl⟩, h₁⟩, hmin⟩ := exists_min_image ((fun c ↦ c x) '' T ∩ Ici y) id
    (hV.inter_of_left _) ⟨b x, ⟨b, ⟨hSface _ hb t hts htne, habt, fun _ _ ↦ le_rfl⟩, rfl⟩, hyb⟩
  replace h₀ : c₀ x ≤ y := h₀
  replace h₁ : y ≤ c₁ x := h₁
  -- if one of them takes the value `y`, the point lies in the open part of its graph
  have hgraph : ∀ {c : E →ᴬ[ℝ] ℝ}, c ∈ T → c x = y → ∃ D ∈ rectilinearCells S,
      (x, y) ∈ intrinsicInterior ℝ D ∧ D ⊆ closedRegionBetween a b (convexHull ℝ (s : Set E)) := by
    intro c hc hcy
    refine ⟨(convexHull ℝ (t : Set E)).graphOn c, .inl ⟨(t, c), hc.1, rfl⟩, ?_, ?_⟩
    · rw [ContinuousAffineMap.intrinsicInterior_graphOn]
      exact mem_graphOn.2 ⟨hxt, hcy⟩
    · rw [← closedRegionBetween_self]
      exact hsub hc hc
  rcases h₀.eq_or_lt with h₀ | h₀
  · exact hgraph hT₀ h₀
  rcases h₁.eq_or_lt with h₁ | h₁
  · exact hgraph hT₁ h₁.symm
  -- otherwise the two sections are consecutive and the point lies in the open band between them
  have hle : ∀ v ∈ t, c₀ v ≤ c₁ v := le_of_lt hSle hT₀.1 hT₁.1 hxt' (h₀.trans h₁)
  have hlt : ∃ v ∈ t, c₀ v < c₁ v := by
    by_contra! hne
    exact (le_of_forall_le_of_mem_convexHull hne hxt').not_gt (h₀.trans h₁)
  have hcons : IsConsecutiveSections S t c₀ c₁ := by
    refine ⟨hle, hlt, fun c hc h₀c hc₁ ↦ ?_⟩
    have hcT : c ∈ T := ⟨hc, fun v hv ↦ (hT₀.2.1 v hv).trans (h₀c v hv),
      fun v hv ↦ (hc₁ v hv).trans (hT₁.2.2 v hv)⟩
    rcases le_total (c x) y with hcy | hcy
    · have hcx : c₀ x = c x :=
        (le_of_forall_le_of_mem_convexHull h₀c hxt').antisymm (hmax (c x) ⟨⟨c, hcT, rfl⟩, hcy⟩)
      exact .inl fun v hv ↦
        (eq_of_le_of_mem_intrinsicInterior h₀c hxt hcx (subset_convexHull ℝ _ hv)).symm
    · have hcx : c x = c₁ x :=
        (le_of_forall_le_of_mem_convexHull hc₁ hxt').antisymm (hmin (c x) ⟨⟨c, hcT, rfl⟩, hcy⟩)
      exact .inr fun v hv ↦ eq_of_le_of_mem_intrinsicInterior hc₁ hxt hcx (subset_convexHull ℝ _ hv)
  refine ⟨closedRegionBetween c₀ c₁ (convexHull ℝ (t : Set E)),
    .inr ⟨t, c₀, c₁, hT₀.1, hT₁.1, hcons, rfl⟩, ?_, hsub hT₀ hT₁⟩
  rw [intrinsicInterior_closedRegionBetween (fun v hv ↦ le_of_forall_le_of_mem_convexHull hle hv)
    ⟨x, hxt', h₀.trans h₁⟩]
  exact ⟨hxt, h₀, h₁⟩

/-- **Covering by the cells.** If the sections over every face are unbounded above and below, the
rectilinear cells cover the cylinder `|K| × ℝ`. -/
theorem sUnion_rectilinearCells (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSface : ∀ p ∈ S, ∀ t ⊆ p.1, t.Nonempty → (t, p.2) ∈ S)
    (hSle : IsTotalOnVertices S)
    (hSlf : LocallyFinite fun C : rectilinearGraphs S ↦ (C : Set (E × ℝ)))
    (hbelow : ∀ s ∈ K.faces, ∀ y : ℝ, ∃ a, (s, a) ∈ S ∧ ∀ x ∈ s, a x ≤ y)
    (habove : ∀ s ∈ K.faces, ∀ y : ℝ, ∃ b, (s, b) ∈ S ∧ ∀ x ∈ s, y ≤ b x) :
    ⋃₀ rectilinearCells S = K.space ×ˢ univ := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨C, hC, hz⟩
    obtain ⟨s, a, b, ha, -, -, rfl⟩ := exists_eq_closedRegionBetween hC
    exact ⟨SimplicialComplex.mem_space_iff.2 ⟨s, hS _ ha, (mem_closedRegionBetween.1 hz).1⟩,
      mem_univ _⟩
  · rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.1 hx
    obtain ⟨a, ha, hay⟩ := hbelow s hs y
    obtain ⟨b, hb, hyb⟩ := habove s hs y
    have hay' : a x ≤ y := by
      simpa using le_of_forall_le_of_mem_convexHull (a := (a : E →ᵃ[ℝ] ℝ))
        (b := AffineMap.const ℝ E y) (by simpa using hay) hxs
    have hyb' : y ≤ b x := by
      simpa using le_of_forall_le_of_mem_convexHull (a := AffineMap.const ℝ E y)
        (b := (b : E →ᵃ[ℝ] ℝ)) (by simpa using hyb) hxs
    obtain ⟨D, hD, hzD, -⟩ := exists_mem_intrinsicInterior hS hSface hSle hSlf ha hb
      (fun v hv ↦ (hay v hv).trans (hyb v hv)) (z := (x, y))
      (mem_closedRegionBetween.2 ⟨hxs, hay', hyb'⟩)
    exact ⟨D, hD, intrinsicInterior_subset hzD⟩

/-- Over a face, at most one band between consecutive sections meets a box `B ×ˢ Icc l r` over a
convex set `B` while both of its bounding graphs miss it: two such bands would be ordered, and the
upper section of the lower band would cross the box. -/
private theorem band_eq_of_not_nonempty (hSle : IsTotalOnVertices S) {s : Finset E}
    {a₁ b₁ a₂ b₂ : E →ᴬ[ℝ] ℝ} {B : Set E} (hB : Convex ℝ B) {l r : ℝ}
    (ha₁ : (s, a₁) ∈ S) (hb₁ : (s, b₁) ∈ S) (h₁ : IsConsecutiveSections S s a₁ b₁)
    (hU₁ : (closedRegionBetween a₁ b₁ (convexHull ℝ (s : Set E)) ∩ B ×ˢ Icc l r).Nonempty)
    (hna₁ : ¬((convexHull ℝ (s : Set E)).graphOn a₁ ∩ B ×ˢ Icc l r).Nonempty)
    (hnb₁ : ¬((convexHull ℝ (s : Set E)).graphOn b₁ ∩ B ×ˢ Icc l r).Nonempty)
    (ha₂ : (s, a₂) ∈ S) (hb₂ : (s, b₂) ∈ S) (h₂ : IsConsecutiveSections S s a₂ b₂)
    (hU₂ : (closedRegionBetween a₂ b₂ (convexHull ℝ (s : Set E)) ∩ B ×ˢ Icc l r).Nonempty)
    (hna₂ : ¬((convexHull ℝ (s : Set E)).graphOn a₂ ∩ B ×ˢ Icc l r).Nonempty)
    (hnb₂ : ¬((convexHull ℝ (s : Set E)).graphOn b₂ ∩ B ×ˢ Icc l r).Nonempty) :
    closedRegionBetween a₁ b₁ (convexHull ℝ (s : Set E)) =
      closedRegionBetween a₂ b₂ (convexHull ℝ (s : Set E)) := by
  have hconv := convex_convexHull ℝ (s : Set E)
  rcases band_trichotomy hSle ha₁ hb₁ h₁ ha₂ hb₂ h₂ with h | h | h
  · exact h
  · exact (hnb₁ (graphOn_inter_prod_nonempty_of_le hconv hB b₁.continuous.continuousOn
      (fun _ hx ↦ le_of_forall_le_of_mem_convexHull h hx) hU₁ hU₂ hna₂)).elim
  · exact (hnb₂ (graphOn_inter_prod_nonempty_of_le hconv hB b₂.continuous.continuousOn
      (fun _ hx ↦ le_of_forall_le_of_mem_convexHull h hx) hU₂ hU₁ hna₁)).elim

/-- A band between consecutive sections is determined by the graph of its lower section, and also
by the graph of its upper section. -/
private theorem band_eq_of_graphOn_eq (hS : ∀ p ∈ S, p.1 ∈ K.faces) (hSle : IsTotalOnVertices S)
    {s₁ s₂ : Finset E} {a₁ b₁ a₂ b₂ : E →ᴬ[ℝ] ℝ}
    (ha₁ : (s₁, a₁) ∈ S) (hb₁ : (s₁, b₁) ∈ S) (h₁ : IsConsecutiveSections S s₁ a₁ b₁)
    (ha₂ : (s₂, a₂) ∈ S) (hb₂ : (s₂, b₂) ∈ S) (h₂ : IsConsecutiveSections S s₂ a₂ b₂)
    (h : (convexHull ℝ (s₁ : Set E)).graphOn a₁ = (convexHull ℝ (s₂ : Set E)).graphOn a₂ ∨
      (convexHull ℝ (s₁ : Set E)).graphOn b₁ = (convexHull ℝ (s₂ : Set E)).graphOn b₂) :
    closedRegionBetween a₁ b₁ (convexHull ℝ (s₁ : Set E)) =
      closedRegionBetween a₂ b₂ (convexHull ℝ (s₂ : Set E)) := by
  -- the two bands lie over the same face
  have hs : convexHull ℝ (s₁ : Set E) = convexHull ℝ (s₂ : Set E) := by
    rcases h with h | h <;> simpa only [image_fst_graphOn] using congrArg (Prod.fst '' ·) h
  obtain rfl := ((K.face_subset_face_iff (hS _ ha₁) (hS _ ha₂)).1 hs.le).antisymm
    ((K.face_subset_face_iff (hS _ ha₂) (hS _ ha₁)).1 hs.ge)
  -- and the given graphs are equal as functions on the vertices
  have hgr : ∀ {f g : E →ᴬ[ℝ] ℝ}, (convexHull ℝ (s₁ : Set E)).graphOn f =
      (convexHull ℝ (s₁ : Set E)).graphOn g → ∀ x ∈ s₁, f x = g x := fun hfg x hx ↦
    graphOn_inj.mp hfg (subset_convexHull ℝ _ hx)
  obtain ⟨v₁, hv₁, hlt₁⟩ := h₁.exists_lt
  obtain ⟨v₂, hv₂, hlt₂⟩ := h₂.exists_lt
  rcases band_trichotomy hSle ha₁ hb₁ h₁ ha₂ hb₂ h₂ with h' | h' | h'
  · exact h'
  all_goals rcases h with h | h <;>
    linarith [h' v₁ hv₁, h' v₂ hv₂, hgr h v₁ hv₁, hgr h v₂ hv₂]

/-! ### Constant sections at integer heights -/

/-- The constant sections at integer heights over the faces of `K`. -/
private abbrev integerSections (K : SimplicialComplex ℝ E) : Set (Finset E × (E →ᴬ[ℝ] ℝ)) :=
  {p | p.1 ∈ K.faces ∧ ∃ n : ℤ, p.2 = ContinuousAffineMap.const ℝ E (n : ℝ)}

/-- The constant sections at integer heights over a face are totally ordered. -/
private theorem isTotalOnVertices_integerSections : IsTotalOnVertices (integerSections K) := by
  rintro s _ _ ⟨-, n, rfl⟩ ⟨-, m, rfl⟩
  rcases le_total n m with h | h
  · exact .inl fun x _ ↦ by simpa using h
  · exact .inr fun x _ ↦ by simpa using h

/-- The graphs of the constant sections at integer heights are locally finite: near a point they
lie over finitely many faces and heights. -/
private theorem locallyFinite_rectilinearGraphs_integerSections
    (hK : LocallyFinite fun s : K.faces ↦ convexHull ℝ (s : Set E)) :
    LocallyFinite fun C : rectilinearGraphs (integerSections K) ↦ (C : Set (E × ℝ)) := by
  intro z
  obtain ⟨V, hV, hVf⟩ := hK z.1
  refine ⟨V ×ˢ Ioo (z.2 - 1) (z.2 + 1), prod_mem_nhds hV (Ioo_mem_nhds (by linarith)
    (by linarith)), ?_⟩
  have hN : {n : ℤ | (n : ℝ) ∈ Ioo (z.2 - 1) (z.2 + 1)}.Finite :=
    (finite_Ioo ⌊z.2 - 1⌋ ⌈z.2 + 1⌉).subset fun n hn ↦
      ⟨Int.floor_lt.2 hn.1, Int.lt_ceil.2 hn.2⟩
  refine (((hVf.prod hN).image fun q ↦
    convexHull ℝ ((q.1 : Finset E) : Set E) ×ˢ {((q.2 : ℤ) : ℝ)}).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨_, ⟨s, a⟩, ⟨hs, n, hn⟩, rfl⟩ ⟨⟨x, y⟩, hxy, hxV, hy⟩
  obtain rfl : a = _ := hn
  simp only [ContinuousAffineMap.coe_const, graphOn_const] at hxy ⊢
  obtain ⟨hx, rfl⟩ : x ∈ convexHull ℝ (s : Set E) ∧ y = n := by simpa using hxy
  exact ⟨(⟨s, hs⟩, n), ⟨⟨x, hx, hxV⟩, hy⟩, rfl⟩

/-- Each prism `convexHull ℝ s ×ˢ Icc n (n + 1)` over a face is the band between the consecutive
constant sections at heights `n` and `n + 1`. -/
private theorem prod_Icc_mem_rectilinearCells {s : Finset E} (hs : s ∈ K.faces) (n : ℤ) :
    convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1) ∈ rectilinearCells (integerSections K) := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  refine .inr ⟨s, ContinuousAffineMap.const ℝ E (n : ℝ),
    ContinuousAffineMap.const ℝ E ((n + 1 : ℤ) : ℝ), ⟨hs, n, rfl⟩, ⟨hs, n + 1, rfl⟩,
    ⟨fun x _ ↦ by simp, ⟨v, hv, by simp⟩, ?_⟩, by simp⟩
  rintro _ ⟨-, m, rfl⟩ hnm hmn
  have h₁ : n ≤ m := by exact_mod_cast (show (n : ℝ) ≤ m by simpa using hnm v hv)
  have h₂ : m ≤ n + 1 := by
    exact_mod_cast (show (m : ℝ) ≤ ((n + 1 : ℤ) : ℝ) by simpa using hmn v hv)
  rcases (show m = n ∨ m = n + 1 by omega) with rfl | rfl
  · exact .inl fun _ _ ↦ rfl
  · exact .inr fun _ _ ↦ rfl

/-- Every cell of the constant sections at integer heights lies in a prism
`convexHull ℝ s ×ˢ Icc n (n + 1)` over a face. -/
private theorem exists_subset_prod_Icc (hC : C ∈ rectilinearCells (integerSections K)) :
    ∃ s ∈ K.faces, ∃ n : ℤ, C ⊆ convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1) := by
  rcases hC with ⟨⟨s, a⟩, ⟨hs, n, hn⟩, rfl⟩ |
    ⟨s, _, _, ⟨hs, n, rfl⟩, ⟨-, m, rfl⟩, ⟨-, ⟨v, hv, -⟩, hcons⟩, rfl⟩
  · obtain rfl : a = _ := hn
    refine ⟨s, hs, n, ?_⟩
    simp only [ContinuousAffineMap.coe_const, graphOn_const]
    exact prod_mono le_rfl (singleton_subset_iff.2 ⟨le_rfl, by linarith⟩)
  · refine ⟨s, hs, n, ?_⟩
    simp only [ContinuousAffineMap.coe_const, closedRegionBetween_const]
    refine prod_mono le_rfl (Icc_subset_Icc le_rfl ?_)
    -- the constant section at height `n + 1` cannot lie strictly between `n` and `m`
    by_contra! hm
    have hm' : n + 1 < m := by exact_mod_cast hm
    rcases hcons (ContinuousAffineMap.const ℝ E ((n + 1 : ℤ) : ℝ)) ⟨hs, n + 1, rfl⟩
        (fun x _ ↦ by simp)
        (fun x _ ↦ by simpa using (show ((n + 1 : ℤ) : ℝ) ≤ m by exact_mod_cast hm'.le))
      with h | h
    · have := h v hv
      simp at this
    · have := h v hv
      simp only [ContinuousAffineMap.coe_const, Function.const_apply] at this
      exact hm'.ne (by exact_mod_cast this)

/-! ### Local finiteness and the subdivision -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Local finiteness of the cells.** Near a point `z`, take a compact box around it. Only finitely
many section graphs meet it, and a band meeting it either has a bounding graph meeting it, which
determines the band, or crosses it; over each of the finitely many faces whose simplex meets the
base of the box at most one band crosses it. -/
private theorem locallyFinite_rectilinearCells
    (hK : LocallyFinite fun s : K.faces ↦ convexHull ℝ (s : Set E))
    (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSle : IsTotalOnVertices S)
    (hSlf : LocallyFinite fun C : rectilinearGraphs S ↦ (C : Set (E × ℝ))) :
    LocallyFinite fun C : rectilinearCells S ↦ (C : Set (E × ℝ)) := by
  intro z
  set U := closedBall z.1 1 ×ˢ Icc (z.2 - 1) (z.2 + 1)
  refine ⟨U, prod_mem_nhds (closedBall_mem_nhds _ one_pos)
    (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  -- the graphs meeting the box
  set G := {D | D ∈ rectilinearGraphs S ∧ (D ∩ U).Nonempty}
  have hG : G.Finite := by
    refine ((hSlf.finite_nonempty_inter_compact
      ((isCompact_closedBall z.1 1).prod (isCompact_Icc (a := z.2 - 1) (b := z.2 + 1)))).image
      Subtype.val).subset ?_
    rintro D ⟨hD, hDU⟩
    exact ⟨⟨D, hD⟩, hDU, rfl⟩
  -- the faces whose simplex meets the base of the box
  have hF := hK.finite_nonempty_inter_compact (isCompact_closedBall z.1 1)
  -- the bands with a given lower or upper graph, and the bands crossing the box over a face
  let bandWith := fun (lower : Bool) (D : Set (E × ℝ)) ↦ {C | ∃ s a b, (s, a) ∈ S ∧ (s, b) ∈ S ∧
    IsConsecutiveSections S s a b ∧ closedRegionBetween a b (convexHull ℝ (s : Set E)) = C ∧
    (convexHull ℝ (s : Set E)).graphOn (if lower then a else b) = D}
  let crossing := fun s : K.faces ↦ {C | ∃ a b, ((s : Finset E), a) ∈ S ∧
    ((s : Finset E), b) ∈ S ∧ IsConsecutiveSections S s a b ∧
    closedRegionBetween a b (convexHull ℝ ((s : Finset E) : Set E)) = C ∧
    (C ∩ U).Nonempty ∧ ¬((convexHull ℝ ((s : Finset E) : Set E)).graphOn a ∩ U).Nonempty ∧
    ¬((convexHull ℝ ((s : Finset E) : Set E)).graphOn b ∩ U).Nonempty}
  have hB : {D | D ∈ rectilinearBands S ∧ (D ∩ U).Nonempty}.Finite := by
    refine (((hG.biUnion fun D _ ↦ Subsingleton.finite (s := bandWith true D) ?_).union
      (hG.biUnion fun D _ ↦ Subsingleton.finite (s := bandWith false D) ?_)).union
      (hF.biUnion fun s _ ↦ Subsingleton.finite (s := crossing s) ?_)).subset ?_
    · rintro _ ⟨s₁, a₁, b₁, ha₁, hb₁, h₁, rfl, hD₁⟩ _ ⟨s₂, a₂, b₂, ha₂, hb₂, h₂, rfl, hD₂⟩
      exact band_eq_of_graphOn_eq hS hSle ha₁ hb₁ h₁ ha₂ hb₂ h₂
        (.inl (hD₁.trans hD₂.symm))
    · rintro _ ⟨s₁, a₁, b₁, ha₁, hb₁, h₁, rfl, hD₁⟩ _ ⟨s₂, a₂, b₂, ha₂, hb₂, h₂, rfl, hD₂⟩
      exact band_eq_of_graphOn_eq hS hSle ha₁ hb₁ h₁ ha₂ hb₂ h₂
        (.inr (hD₁.trans hD₂.symm))
    · rintro _ ⟨a₁, b₁, ha₁, hb₁, h₁, rfl, hU₁, hna₁, hnb₁⟩
        _ ⟨a₂, b₂, ha₂, hb₂, h₂, rfl, hU₂, hna₂, hnb₂⟩
      exact band_eq_of_not_nonempty hSle (convex_closedBall z.1 1) ha₁ hb₁ h₁ hU₁ hna₁ hnb₁
        ha₂ hb₂ h₂ hU₂ hna₂ hnb₂
    · rintro D ⟨⟨s, a, b, ha, hb, hab, rfl⟩, p, hp, hpU⟩
      by_cases hna : ((convexHull ℝ (s : Set E)).graphOn a ∩ U).Nonempty
      · exact .inl (.inl (mem_biUnion (x := (convexHull ℝ (s : Set E)).graphOn a)
          ⟨⟨(s, a), ha, rfl⟩, hna⟩ ⟨s, a, b, ha, hb, hab, rfl, rfl⟩))
      by_cases hnb : ((convexHull ℝ (s : Set E)).graphOn b ∩ U).Nonempty
      · exact .inl (.inr (mem_biUnion (x := (convexHull ℝ (s : Set E)).graphOn b)
          ⟨⟨(s, b), hb, rfl⟩, hnb⟩ ⟨s, a, b, ha, hb, hab, rfl, rfl⟩))
      exact .inr (mem_biUnion (x := ⟨s, hS _ ha⟩)
        ⟨p.1, (mem_closedRegionBetween.1 hp).1, hpU.1⟩
        ⟨a, b, ha, hb, hab, rfl, ⟨p, hp, hpU⟩, hna, hnb⟩)
  refine ((hG.union hB).preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨D, hD | hD⟩ hDU
  · exact .inl ⟨hD, hDU⟩
  · exact .inr ⟨hD, hDU⟩

/-- **Łojasiewicz's Lemma 15: triangulating the rectilinear cells.** Let `K` be a locally finite
simplicial complex in a finite-dimensional real normed space `E`, and let `S` be a family of
sections over the faces of `K` such that

* every face of a section graph is a section graph: if `(s, a) ∈ S` and `t ⊆ s` is nonempty, then
  `(t, a) ∈ S`;
* the sections over each face are totally ordered on its vertices; and
* the section graphs form a locally finite family.

Then there is a locally finite simplicial complex `L` in `E × ℝ` whose underlying space is the
union of the rectilinear cells, which triangulates every cell by finitely many of its simplices,
and each of whose simplices lies in a cell. -/
theorem exists_subdivision_rectilinearCells
    (hK : LocallyFinite fun s : K.faces ↦ convexHull ℝ (s : Set E))
    (hS : ∀ p ∈ S, p.1 ∈ K.faces)
    (hSface : ∀ p ∈ S, ∀ t ⊆ p.1, t.Nonempty → (t, p.2) ∈ S)
    (hSle : IsTotalOnVertices S)
    (hSlf : LocallyFinite fun C : rectilinearGraphs S ↦ (C : Set (E × ℝ))) :
    ∃ L : SimplicialComplex ℝ (E × ℝ), L.space = ⋃₀ rectilinearCells S ∧
      (∀ C ∈ rectilinearCells S, (L.restrict C).space = C ∧ (L.restrict C).faces.Finite) ∧
      (∀ t ∈ L.faces, ∃ C ∈ rectilinearCells S, (t : Set (E × ℝ)) ⊆ C) ∧
      LocallyFinite fun t : L.faces ↦ convexHull ℝ (t : Set (E × ℝ)) := by
  have hne : ∀ C : rectilinearCells S, (intrinsicInterior ℝ (C : Set (E × ℝ))).Nonempty :=
    fun C ↦ Set.Nonempty.intrinsicInterior (convex_of_mem_rectilinearCells C.2)
      (nonempty_of_mem_rectilinearCells hS C.2)
  obtain ⟨L, hLs, hLP, hLf, hLlf⟩ := SimplicialComplex.exists_subdivision
    (fun C : rectilinearCells S ↦ (C : Set (E × ℝ)))
    (fun C ↦ isCompact_of_mem_rectilinearCells C.2) (fun C ↦ convex_of_mem_rectilinearCells C.2)
    (fun C ↦ (hne C).some) (fun C ↦ (hne C).some_mem)
    (locallyFinite_rectilinearCells hK hS hSle hSlf)
    (fun C D hCD ↦ Set.disjoint_left.2 fun _ hzC hzD ↦ hCD (Subtype.ext
      (eq_of_mem_intrinsicInterior_rectilinearCells hS hSle C.2 D.2 hzC hzD)))
    (fun C z hz ↦ by
      -- a point of the intrinsic frontier lies in the intrinsic interior of a smaller cell
      obtain ⟨s, a, b, ha, hb, hab, hC⟩ := exists_eq_closedRegionBetween C.2
      have hzC : z ∈ (C : Set (E × ℝ)) :=
        intrinsicFrontier_subset (isCompact_of_mem_rectilinearCells C.2).isClosed hz
      rw [← hC] at hzC
      obtain ⟨D, hD, hzD, hDC⟩ := exists_mem_intrinsicInterior hS hSface hSle hSlf ha hb hab hzC
      have hzi : z ∉ intrinsicInterior ℝ (C : Set (E × ℝ)) := by
        rw [← intrinsicClosure_sdiff_intrinsicInterior] at hz
        exact hz.2
      refine mem_iUnion₂.2 ⟨⟨D, hD⟩, ⟨fun h ↦ hzi ?_, hC ▸ hDC⟩, intrinsicInterior_subset hzD⟩
      rw [← h]
      exact hzD)
  refine ⟨L, by rw [hLs, sUnion_eq_iUnion], fun C hC ↦ hLP ⟨C, hC⟩, fun t ht ↦ ?_, hLlf⟩
  obtain ⟨C, -, htC⟩ := hLf t ht
  exact ⟨C, C.2, htC⟩

/-- **Triangulating a cylinder over a simplicial complex.** For a locally finite simplicial complex
`K` in a finite-dimensional real normed space `E`, the cylinder `|K| × ℝ` has a locally finite
triangulation which triangulates every prism `convexHull ℝ s ×ˢ Icc n (n + 1)`, for a face `s` of
`K` and an integer `n`, by finitely many of its simplices, and each of whose simplices lies in such
a prism. These prisms are the band cells of the constant sections at integer heights; the
remaining cells are the slices `convexHull ℝ s ×ˢ {n}` they contain. -/
theorem exists_simplicialComplex_space_eq_prod_univ
    (hK : LocallyFinite fun s : K.faces ↦ convexHull ℝ (s : Set E)) :
    ∃ L : SimplicialComplex ℝ (E × ℝ), L.space = K.space ×ˢ univ ∧
      (∀ s ∈ K.faces, ∀ n : ℤ,
        (L.restrict (convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1))).space =
          convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1) ∧
        (L.restrict (convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1))).faces.Finite) ∧
      (∀ t ∈ L.faces, ∃ s ∈ K.faces, ∃ n : ℤ,
        (t : Set (E × ℝ)) ⊆ convexHull ℝ (s : Set E) ×ˢ Icc (n : ℝ) (n + 1)) ∧
      LocallyFinite fun t : L.faces ↦ convexHull ℝ (t : Set (E × ℝ)) := by
  have hS : ∀ p ∈ integerSections K, p.1 ∈ K.faces := fun _ hp ↦ hp.1
  have hSface : ∀ p ∈ integerSections K, ∀ t ⊆ p.1, t.Nonempty → (t, p.2) ∈ integerSections K :=
    fun _ hp t hts htne ↦ ⟨K.down_closed hp.1 hts htne, hp.2⟩
  have hSlf := locallyFinite_rectilinearGraphs_integerSections hK
  obtain ⟨L, hLs, hLC, hLf, hLlf⟩ :=
    exists_subdivision_rectilinearCells hK hS hSface isTotalOnVertices_integerSections hSlf
  have hsp := sUnion_rectilinearCells hS hSface isTotalOnVertices_integerSections hSlf
    (fun s hs y ↦ ⟨ContinuousAffineMap.const ℝ E (⌊y⌋ : ℝ), ⟨hs, ⌊y⌋, rfl⟩,
      fun x _ ↦ by simpa using Int.floor_le y⟩)
    (fun s hs y ↦ ⟨ContinuousAffineMap.const ℝ E (⌈y⌉ : ℝ), ⟨hs, ⌈y⌉, rfl⟩,
      fun x _ ↦ by simpa using Int.le_ceil y⟩)
  refine ⟨L, hLs.trans hsp, fun s hs n ↦ hLC _ (prod_Icc_mem_rectilinearCells hs n),
    fun t ht ↦ ?_, hLlf⟩
  obtain ⟨C, hC, htC⟩ := hLf t ht
  obtain ⟨s, hs, n, hCs⟩ := exists_subset_prod_Icc hC
  exact ⟨s, hs, n, htC.trans hCs⟩

end FiniteDimensional

end Cells

end TauCeti
