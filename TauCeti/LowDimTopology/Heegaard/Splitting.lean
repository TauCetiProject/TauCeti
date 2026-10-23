/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import TauCeti.LowDimTopology.Handlebody.Basic

/-!
# Heegaard splittings and Heegaard genus

A Heegaard splitting of genus `g` of a closed orientable `3`-manifold `M` writes `M` as the union
of two handlebodies of genus `g` meeting in their common boundary, a closed surface of genus `g`.
The Heegaard genus of `M` is the least genus of a Heegaard splitting.

Here a splitting is recorded inside `M`, without gluing: `TauCeti.HeegaardSplitting M` consists of
two subsets `left` and `right` of `M` covering it, each homeomorphic to the standard handlebody
`TauCeti.handlebody genus`, whose intersection is the frontier of each. The definition makes sense
for any topological space. When `M` is a `3`-manifold without boundary, invariance of domain
identifies the frontier of each piece with the image of the manifold boundary of the handlebody,
so the two pieces meet exactly in their common boundary surface
(`TauCeti.HeegaardSplitting.coe_mem_right_iff`). The standard handlebodies are
orientable, so these are the splittings of orientable manifolds.

The Heegaard genus `TauCeti.heegaardGenus M` is defined only under
`[Nonempty (HeegaardSplitting M)]`, as the least genus of a splitting, so it never silently takes
a junk value. The unit sphere of a
four-dimensional real inner product space, split into two closed hemispheres along the equator,
has a splitting of genus zero, so its Heegaard genus is zero.

## Main definitions

* `TauCeti.HeegaardSplitting M`: a Heegaard splitting of a space `M`.
* `TauCeti.HeegaardSplitting.symm`: the splitting with its two sides exchanged.
* `TauCeti.HeegaardSplitting.transHomeomorph`: transport of a splitting along a homeomorphism.
* `TauCeti.heegaardGenus M`: the least genus of a Heegaard splitting of `M`.
* `TauCeti.hemisphereHeegaardSplitting p`: the splitting of the `3`-sphere into the closed
  hemispheres around `p` and `-p`.

## Main results

* `TauCeti.heegaardGenus_le` and `TauCeti.exists_genus_eq_heegaardGenus`: the Heegaard genus is
  the least genus of a splitting.
* `TauCeti.heegaardGenus_congr`: homeomorphic spaces have the same Heegaard genus.
* `TauCeti.heegaardGenus_sphere`: the `3`-sphere has Heegaard genus zero.

## References

* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Chapter 2.
-/

public section

noncomputable section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

/-- A Heegaard splitting of genus `genus` of a space `M`: two subsets `left` and `right` covering
`M`, each homeomorphic to the standard handlebody of genus `genus`, whose intersection is the
frontier of each of them. In a `3`-manifold without boundary this intersection is the common
boundary surface of the two handlebodies. -/
@[ext]
structure HeegaardSplitting (M : Type*) [TopologicalSpace M] where
  /-- The genus of the splitting. -/
  genus : ℕ
  /-- The first handlebody. -/
  left : Set M
  /-- The second handlebody. -/
  right : Set M
  /-- The two handlebodies cover the space. -/
  union_eq_univ : left ∪ right = univ
  /-- The two handlebodies meet in the frontier of the first. -/
  inter_eq_frontier_left : left ∩ right = frontier left
  /-- The two handlebodies meet in the frontier of the second. -/
  inter_eq_frontier_right : left ∩ right = frontier right
  /-- The first piece is a handlebody of genus `genus`. -/
  nonempty_homeomorph_left : Nonempty (left ≃ₜ handlebody genus)
  /-- The second piece is a handlebody of genus `genus`. -/
  nonempty_homeomorph_right : Nonempty (right ≃ₜ handlebody genus)

namespace HeegaardSplitting

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] (s : HeegaardSplitting M)

/-- The first handlebody of a Heegaard splitting is closed. -/
theorem isClosed_left : IsClosed s.left :=
  frontier_subset_iff_isClosed.1 (s.inter_eq_frontier_left ▸ inter_subset_left)

/-- The second handlebody of a Heegaard splitting is closed. -/
theorem isClosed_right : IsClosed s.right :=
  frontier_subset_iff_isClosed.1 (s.inter_eq_frontier_right ▸ inter_subset_right)

/-- The Heegaard splitting with its two handlebodies exchanged. -/
def symm : HeegaardSplitting M where
  genus := s.genus
  left := s.right
  right := s.left
  union_eq_univ := union_comm s.left s.right ▸ s.union_eq_univ
  inter_eq_frontier_left := inter_comm s.left s.right ▸ s.inter_eq_frontier_right
  inter_eq_frontier_right := inter_comm s.left s.right ▸ s.inter_eq_frontier_left
  nonempty_homeomorph_left := s.nonempty_homeomorph_right
  nonempty_homeomorph_right := s.nonempty_homeomorph_left

@[simp] theorem symm_genus : s.symm.genus = s.genus := (rfl)
@[simp] theorem symm_left : s.symm.left = s.right := (rfl)
@[simp] theorem symm_right : s.symm.right = s.left := (rfl)
@[simp] theorem symm_symm : s.symm.symm = s := (rfl)

/-- The image of a Heegaard splitting under a homeomorphism. -/
def transHomeomorph (e : M ≃ₜ N) : HeegaardSplitting N where
  genus := s.genus
  left := e '' s.left
  right := e '' s.right
  union_eq_univ := by rw [← image_union, s.union_eq_univ, image_univ, e.range_coe]
  inter_eq_frontier_left := by
    rw [← image_inter e.injective, s.inter_eq_frontier_left, e.image_frontier]
  inter_eq_frontier_right := by
    rw [← image_inter e.injective, s.inter_eq_frontier_right, e.image_frontier]
  nonempty_homeomorph_left := s.nonempty_homeomorph_left.map (e.image s.left).symm.trans
  nonempty_homeomorph_right := s.nonempty_homeomorph_right.map (e.image s.right).symm.trans

@[simp] theorem transHomeomorph_genus (e : M ≃ₜ N) : (s.transHomeomorph e).genus = s.genus := (rfl)
@[simp] theorem transHomeomorph_left (e : M ≃ₜ N) : (s.transHomeomorph e).left = e '' s.left :=
  (rfl)
@[simp] theorem transHomeomorph_right (e : M ≃ₜ N) :
    (s.transHomeomorph e).right = e '' s.right :=
  (rfl)

end HeegaardSplitting

/-! ### Heegaard genus -/

section HeegaardGenus

variable (M : Type*) [TopologicalSpace M] [h : Nonempty (HeegaardSplitting M)]

open Classical in
/-- The Heegaard genus of a space admitting a Heegaard splitting: the least genus of its Heegaard
splittings. -/
def heegaardGenus : ℕ :=
  Nat.find (⟨h.some.genus, h.some, rfl⟩ : ∃ g, ∃ s : HeegaardSplitting M, s.genus = g)

/-- Some Heegaard splitting realizes the Heegaard genus. -/
theorem exists_genus_eq_heegaardGenus : ∃ s : HeegaardSplitting M, s.genus = heegaardGenus M := by
  classical
  exact Nat.find_spec (⟨h.some.genus, h.some, rfl⟩ : ∃ g, ∃ s : HeegaardSplitting M, s.genus = g)

variable {M}

/-- The Heegaard genus is at most the genus of any Heegaard splitting. -/
theorem heegaardGenus_le (s : HeegaardSplitting M) : heegaardGenus M ≤ s.genus := by
  classical
  exact Nat.find_min' _ ⟨s, rfl⟩

/-- A lower bound for the Heegaard genus is a lower bound for the genus of every splitting. -/
theorem le_heegaardGenus_iff {n : ℕ} :
    n ≤ heegaardGenus M ↔ ∀ s : HeegaardSplitting M, n ≤ s.genus := by
  refine ⟨fun hn s ↦ hn.trans (heegaardGenus_le s), fun hn ↦ ?_⟩
  obtain ⟨s, hs⟩ := exists_genus_eq_heegaardGenus M
  exact hs ▸ hn s

/-- The Heegaard genus vanishes exactly when there is a splitting of genus zero. -/
theorem heegaardGenus_eq_zero_iff :
    heegaardGenus M = 0 ↔ ∃ s : HeegaardSplitting M, s.genus = 0 := by
  refine ⟨fun h0 ↦ h0 ▸ exists_genus_eq_heegaardGenus M, fun ⟨s, hs⟩ ↦ ?_⟩
  exact Nat.eq_zero_of_le_zero (hs ▸ heegaardGenus_le s)

/-- **The Heegaard genus is a topological invariant.** -/
theorem heegaardGenus_congr {N : Type*} [TopologicalSpace N] [Nonempty (HeegaardSplitting N)]
    (e : M ≃ₜ N) : heegaardGenus M = heegaardGenus N := by
  refine le_antisymm ?_ ?_
  · obtain ⟨s, hs⟩ := exists_genus_eq_heegaardGenus N
    simpa [hs] using heegaardGenus_le (s.transHomeomorph e.symm)
  · obtain ⟨s, hs⟩ := exists_genus_eq_heegaardGenus M
    simpa [hs] using heegaardGenus_le (s.transHomeomorph e)

end HeegaardGenus

/-! ### The genus-zero splitting of the `3`-sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 4)]

/-- A closed hemisphere of the unit sphere in four dimensions is a genus-zero handlebody. -/
private theorem nonempty_homeomorph_hemisphere_handlebody_zero (p : sphere (0 : E) 1) :
    Nonempty ({x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫} ≃ₜ handlebody 0) := by
  have : Fact (Module.finrank ℝ E = 3 + 1) := ‹_›
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 3
  have hF : Module.finrank ℝ (ℝ ∙ (p : E))ᗮ = 3 :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
  obtain ⟨e⟩ := nonempty_homeomorph_handlebody_zero hF
  exact ⟨(hemisphereHomeomorph p).trans e⟩

/-- The genus-zero Heegaard splitting of the unit sphere of a four-dimensional real inner product
space into the closed hemispheres around `p` and `-p`, meeting along the equator. -/
def hemisphereHeegaardSplitting (p : sphere (0 : E) 1) : HeegaardSplitting (sphere (0 : E) 1) where
  genus := 0
  left := {x | 0 ≤ ⟪(x : E), (p : E)⟫}
  right := {x | 0 ≤ ⟪(x : E), ((-p : sphere (0 : E) 1) : E)⟫}
  union_eq_univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    simpa [inner_neg_right] using le_total 0 ⟪(x : E), (p : E)⟫
  inter_eq_frontier_left := by
    rw [frontier_setOf_inner_nonneg, range_equatorInclusion]
    simp only [coe_neg_sphere]
  inter_eq_frontier_right := by
    rw [frontier_setOf_inner_nonneg, range_equatorInclusion]
    simp only [coe_neg_sphere, neg_neg, inter_comm]
  nonempty_homeomorph_left := nonempty_homeomorph_hemisphere_handlebody_zero p
  nonempty_homeomorph_right := nonempty_homeomorph_hemisphere_handlebody_zero (-p)

@[simp]
theorem hemisphereHeegaardSplitting_genus (p : sphere (0 : E) 1) :
    (hemisphereHeegaardSplitting p).genus = 0 :=
  (rfl)

@[simp]
theorem hemisphereHeegaardSplitting_left (p : sphere (0 : E) 1) :
    (hemisphereHeegaardSplitting p).left = {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫} :=
  (rfl)

@[simp]
theorem hemisphereHeegaardSplitting_right (p : sphere (0 : E) 1) :
    (hemisphereHeegaardSplitting p).right = {x : sphere (0 : E) 1 | ⟪(x : E), (p : E)⟫ ≤ 0} := by
  ext x
  simp [hemisphereHeegaardSplitting, inner_neg_right]

instance : Nonempty (HeegaardSplitting (sphere (0 : E) 1)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : Module.finrank ℝ E = 4)
  exact ((NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one).to_subtype.map
    hemisphereHeegaardSplitting

/-- **The `3`-sphere has Heegaard genus zero.** -/
theorem heegaardGenus_sphere : heegaardGenus (sphere (0 : E) 1) = 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : Module.finrank ℝ E = 4)
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
  exact heegaardGenus_eq_zero_iff.2
    ⟨hemisphereHeegaardSplitting ⟨p, hp⟩, hemisphereHeegaardSplitting_genus _⟩

end Sphere

end TauCeti
