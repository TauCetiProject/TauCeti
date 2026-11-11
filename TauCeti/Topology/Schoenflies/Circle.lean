/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
public import TauCeti.Topology.ConnectedComponents
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import TauCeti.Topology.Circle.Schoenflies

/-!
# Brown's generalized Schoenflies theorem in dimension one

Let `σ` be an injective map from the unit sphere `S⁰` of a real normed space `E` of dimension `1`
into the unit sphere `S¹` of a real normed space `F` of dimension `2`. Its image `Σ` is a
pair of points of the circle, and by the Jordan–Brouwer separation theorem
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`) the complement `S¹ ∖ Σ` has
exactly two connected components. This file proves the other clauses of M. Brown's generalized
Schoenflies theorem in this dimension.

* The closure of each component `U` of `S¹ ∖ Σ` is `U ∪ Σ`, and its frontier is `Σ`
  (`TauCeti.closure_connectedComponentIn_compl_range_of_finrank_eq_one`,
  `TauCeti.frontier_connectedComponentIn_compl_range_of_finrank_eq_one`).
* The closure of each component is a closed `1`-cell: it is homeomorphic to the closed unit ball
  `D¹` of `E`, by a homeomorphism which inverts `σ` on `Σ` and carries exactly `Σ` onto the
  boundary sphere `S⁰` of `D¹`
  (`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one`).
* For a bicollar `b` of `σ`, the two collar arcs at each point `σ x`, the points `b (x, t)` with
  `t > 0` and those with `t < 0`, lie in different components
  (`TauCeti.IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one`).

In dimension one the first two statements hold for every injective `σ`, with no bicollar. The last
statement is the form that the collar clause takes here. In higher dimensions each side of a
bicollar is connected and lies in one component. Here each side consists of two arcs, one at each
point of `Σ`, and these two arcs may lie in the same component: on the unit circle, with `Σ` the
points at angles `0` and `π`, a bicollar whose angle increases with `t` at the first point and
decreases with `t` at the second has both positive arcs in the upper half of the circle.

## Proof

The two open arcs between the points of `Σ`, their closures and their closed `1`-cell structures
are those of `TauCeti.exists_closure_homeomorph_closedBall_sphere`. Being open, preconnected and
disjoint, the two arcs are the components of `S¹ ∖ Σ`
(`IsPreconnected.connectedComponentIn_union_eq_left`). A homeomorphism of a closed arc onto `D¹`
carrying `Σ` onto `S⁰` either inverts `σ` or does so after composing with the negation of `D¹`.
For the collar clause, the slice of a bicollar through a point of the discrete domain `S⁰` is an
open neighbourhood of a point of `Σ`, and so meets both components.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

namespace TauCeti

open Metric Module Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- An open set `A` of the circle which is one of the two complementary arcs of the image of
`σ`: it is preconnected, its closure adds the image of `σ`, and the closure is a closed `1`-cell
by a homeomorphism inverting `σ` on its boundary. -/
private def IsComplementaryArc (σ : sphere (0 : E) 1 → sphere (0 : F) 1)
    (A : Set (sphere (0 : F) 1)) : Prop :=
  IsOpen A ∧ IsPreconnected A ∧ closure A = A ∪ range σ ∧
    ∃ h : closure A ≃ₜ closedBall (0 : E) 1,
      ∀ (z : closure A) x, (z : sphere (0 : F) 1) = σ x → (h z : E) = x

/-- The complement of the image of an injective map from the unit sphere of a space of dimension
`1` into the unit sphere of a space of dimension `2` is the union of two disjoint complementary
arcs. These are the arcs of `TauCeti.exists_closure_homeomorph_closedBall_sphere`. -/
private theorem exists_isComplementaryArc (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) :
    ∃ A₁ A₂ : Set (sphere (0 : F) 1), (range σ)ᶜ = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧
      IsComplementaryArc σ A₁ ∧ IsComplementaryArc σ A₂ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- The image of `σ` is the pair `{σ u, σ (-u)}`.
  have hrange : range σ = {σ u, σ (-u)} := by
    rw [← image_univ, ← image_pair]
    congr 1
    refine (eq_univ_of_forall fun x ↦ ?_).symm
    have hx : (x : E) ∈ ({(u : E), -(u : E)} : Set E) :=
      sphere_eq_pair_of_finrank_eq_one hE u.2 ▸ x.2
    rcases hx with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_closure_homeomorph_closedBall_sphere hE (by rw [hEF, hE])
      (hσ.ne (ne_neg_of_mem_unit_sphere ℝ u))
  rw [← hrange] at hunion hAcl hBcl heA heB
  have hsub {S : Set (sphere (0 : F) 1)} (hS : closure S = S ∪ range σ) : range σ ⊆ closure S :=
    hS ▸ subset_union_right
  obtain ⟨hA, hhA⟩ := exists_homeomorph_apply_eq_of_finrank_eq_one hE hσ (hsub hAcl) eA heA
  obtain ⟨hB, hhB⟩ := exists_homeomorph_apply_eq_of_finrank_eq_one hE hσ (hsub hBcl) eB heB
  exact ⟨A, B, hunion.symm, hdisj, ⟨hAo, hAc.isPreconnected, hAcl, hA, hhA⟩,
    ⟨hBo, hBc.isPreconnected, hBcl, hB, hhB⟩⟩

/-- The connected component of a point `y` off the image of `σ` is one of the two complementary
arcs, and the other arc is the rest of the complement. -/
private theorem exists_connectedComponentIn_eq (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ A A' : Set (sphere (0 : F) 1), connectedComponentIn (range σ)ᶜ y = A ∧
      (range σ)ᶜ = A ∪ A' ∧ Disjoint A A' ∧ IsComplementaryArc σ A ∧
      IsComplementaryArc σ A' := by
  obtain ⟨A₁, A₂, hcompl, hdisj, h₁, h₂⟩ := exists_isComplementaryArc hEF hE hσ
  have hy' : y ∈ A₁ ∪ A₂ := hcompl ▸ hy
  rcases hy' with hy' | hy'
  · exact ⟨A₁, A₂, by rw [hcompl, h₁.2.1.connectedComponentIn_union_eq_left h₁.1 h₂.1 hdisj hy'],
      hcompl, hdisj, h₁, h₂⟩
  · rw [union_comm] at hcompl
    exact ⟨A₂, A₁, by
      rw [hcompl, h₂.2.1.connectedComponentIn_union_eq_left h₂.1 h₁.1 hdisj.symm hy'], hcompl,
      hdisj.symm, h₂, h₁⟩

/-- **The closure of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1`, a pair of points, into the unit
sphere of a real normed space of dimension `2`. The closure of each connected component of
the complement of its image `Σ` adds exactly `Σ`. -/
theorem closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  obtain ⟨A, -, hA, -, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  exact hA'.2.2.1

/-- **The frontier of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1` into the unit sphere of a real
normed space of dimension `2`. Each connected component of the complement of its image `Σ`
has frontier `Σ`. -/
theorem frontier_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  obtain ⟨A, A', hA, hcompl, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  have hsub : A ⊆ (range σ)ᶜ := hcompl ▸ subset_union_left
  rw [hA, hA'.1.frontier_eq, hA'.2.2.1, union_sdiff_left]
  exact (subset_compl_iff_disjoint_left.1 hsub).sdiff_eq_left

/-- **Brown's generalized Schoenflies theorem in dimension `1`.** Let `σ` be an injective map from
the unit sphere `S⁰` of a real normed space `E` of dimension `1` into the unit sphere `S¹` of a
real normed space of dimension `2`, with image `Σ`. The closure of each connected component
of `S¹ ∖ Σ` is homeomorphic to the closed unit ball `D¹` of `E`, by a homeomorphism `h` which
inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere `S⁰` of `D¹`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  obtain ⟨A, -, hA, -, -, ⟨-, -, hcl, h, hh⟩, -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  refine ⟨h, hh, fun z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · -- A point sent to the boundary sphere is the image under `σ` of its image.
    let x : sphere (0 : E) 1 := ⟨h z, hz⟩
    have hx : σ x ∈ closure A := hcl ▸ Or.inr (mem_range_self x)
    have : (⟨σ x, hx⟩ : closure A) = z := h.injective (Subtype.ext (hh _ x rfl))
    exact ⟨x, congrArg Subtype.val this⟩
  · rintro ⟨x, hx⟩
    rw [hh z x hx.symm]
    exact x.2

/-- **The collar arcs at a point of a pair in a circle.** Let `b` be a bicollar of a map `σ` from
the unit sphere `S⁰` of a real normed space of dimension `1` into the unit sphere `S¹` of a real
normed space of dimension `2`. At each point `σ x`, a point `b (x, s)` with `s > 0` and a
point `b (x, t)` with `t < 0` lie in different components of the complement of the image of `σ`.

Each collar arc at `σ x` lies in a single component
(`TauCeti.IsBicollar.image_singleton_prod_subset_connectedComponentIn`), and there are exactly
two components (`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`), so each
component contains exactly one of the two arcs at `σ x`. -/
theorem IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one
    {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1} (h : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (x : sphere (0 : E) 1)
    {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    connectedComponentIn (range σ)ᶜ (b (x, s)) ≠ connectedComponentIn (range σ)ᶜ (b (x, t)) := by
  intro heq
  have hbs : b (x, s) ∉ range σ := fun hmem ↦ by
    have : (x, s) ∈ b ⁻¹' range σ := hmem
    rw [h.preimage_range] at this
    exact hs.ne' this.2
  obtain ⟨A, A', hA, hcompl, hdisj, -, hA'⟩ :=
    exists_connectedComponentIn_eq hEF hE h.injective hbs
  -- Both collar arcs at `σ x` lie in `A`.
  have hpos := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Ioi
    (lt_irrefl 0) (mem_Ioi.2 hs)
  have hneg := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Iio
    (lt_irrefl 0) (mem_Iio.2 ht)
  rw [hA] at hpos
  rw [← heq, hA] at hneg
  -- The domain is a pair of points, so the slice of `b` through `x` is an open neighbourhood of
  -- `σ x`; it meets the other arc `A'`, whose closure contains `σ x`.
  have := discreteTopology_sphere_of_finrank_eq_one hE (0 : E) 1
  have hW : IsOpen (b '' ({x} ×ˢ univ)) :=
    h.isOpenEmbedding.isOpenMap _ ((isOpen_discrete _).prod isOpen_univ)
  have hσx : σ x ∈ closure A' := hA'.2.2.1 ▸ Or.inr (mem_range_self x)
  obtain ⟨_, ⟨⟨x', r⟩, ⟨hx', -⟩, rfl⟩, hrA'⟩ :=
    mem_closure_iff.1 hσx _ hW ⟨(x, 0), ⟨rfl, trivial⟩, h.apply_zero x⟩
  rw [mem_singleton_iff] at hx'
  subst hx'
  have hA'sub : A' ⊆ (range σ)ᶜ := hcompl ▸ subset_union_right
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact disjoint_left.1 hdisj (hneg ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'
  · rw [h.apply_zero] at hrA'
    exact hA'sub hrA' (mem_range_self x')
  · exact disjoint_left.1 hdisj (hpos ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'

end TauCeti
