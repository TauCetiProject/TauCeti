/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.TangentCone
public import TauCeti.Analysis.Convex.Polyhedron.Boundary
public import TauCeti.Analysis.Convex.Polyhedron.Direction
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.LinearAlgebra.AffineSpace.Span

/-!
# Faces of Delzant polytopes

Let `Δ = {x ∈ V* | c j ≤ ⟨x, u j⟩ for every j}` be the polyhedron of a facet presentation
`(u, c)` in an integral lattice `i : N →+ V`. For a set `s` of facets, the *face cut out by `s`*
is the set of points of `Δ` lying on every facet in `s`,

`F_s = {x ∈ Δ | ⟨x, u j⟩ = c j for every j ∈ s}`

(`TauCeti.Toric.facetFace i u c s`). These are exactly the faces of `Δ`: each `F_s` is an exposed
subset of `Δ` (`TauCeti.Toric.isExposed_facetFace`), and every nonempty convex extreme subset of
`Δ` is of this form (`TauCeti.Toric.exists_facetFace_eq_of_isExtreme`). In general different sets
of facets can cut out the same face.

For a Delzant polytope the sets of facets give a faithful dictionary of the faces, which is the
combinatorial input to the local models of symplectic toric manifolds over the faces of their
moment polytopes. The key fact is that a Delzant polytope is *simple*: the normals of the facets
through any point of `Δ` are among the normals at a vertex, so they are linearly independent
over `ℤ` (`TauCeti.Toric.IsDelzant.linearIndepOn_activeSet`). Consequently, for every set `s` of
facets with `F_s` nonempty:

* the normals `u j`, `j ∈ s`, are linearly independent, and their real span, the Lie algebra of
  the isotropy subtorus over the face, has dimension `#s`
  (`TauCeti.Toric.IsDelzant.finrank_span_image_of_nonempty`);
* some point of `Δ` lies on exactly the facets in `s`
  (`TauCeti.Toric.IsDelzant.exists_activeSet_eq`): starting from any point of `F_s`, move
  off the other facets through it along the edge basis of a vertex;
* `F_s` determines `s`: `F_s ⊆ F_t` exactly when `t ⊆ s`
  (`TauCeti.Toric.IsDelzant.facetFace_subset_facetFace_iff`), so every nonempty face of `Δ` is
  `F_s` for a unique set `s` (`TauCeti.Toric.IsDelzant.existsUnique_facetFace_eq`);
* `F_s` has codimension `#s`: its direction is the common kernel of the pairings with the normals
  in `s` (`TauCeti.Toric.IsDelzant.vectorSpan_facetFace`), of dimension `dim V - #s`
  (`TauCeti.Toric.IsDelzant.finrank_vectorSpan_facetFace_add_ncard`);
* the relative interior of `F_s` is the set of points of `Δ` lying on exactly the facets in `s`
  (`TauCeti.Toric.IsDelzant.mem_intrinsicInterior_facetFace_iff`). So the relative interiors of
  the faces partition `Δ`, each point lying in the relative interior of the face cut out by its
  active facets.

In particular the vertices of a Delzant polytope are exactly its points lying on `dim V` facets
(`TauCeti.Toric.IsDelzant.mem_extremePoints_iff_ncard_activeSet`).

## Main definitions

* `TauCeti.Toric.facetFace i u c s`: the face of the facet polyhedron cut out by the facets in
  `s`.

## Main results

* `TauCeti.Toric.isExposed_facetFace`, `TauCeti.Toric.exists_facetFace_eq_of_isExtreme`: the
  sets `F_s` are the faces of the facet polyhedron.
* `TauCeti.Toric.IsDelzant.linearIndepOn_activeSet`: a Delzant polytope is simple.
  `TauCeti.Toric.IsDelzant.linearIndepOn_real_activeSet` is the same over `ℝ`, for the real
  vectors `i (u j)` of an integral lattice.
* `TauCeti.Toric.IsDelzant.exists_activeSet_eq`: a nonempty face `F_s` has a point lying on
  exactly the facets in `s`.
* `TauCeti.Toric.IsDelzant.facetFace_subset_facetFace_iff`,
  `TauCeti.Toric.IsDelzant.existsUnique_facetFace_eq`: faces correspond to the sets of facets
  with nonempty intersection, reversing inclusion.
* `TauCeti.Toric.IsDelzant.finrank_vectorSpan_facetFace_add_ncard`: the face `F_s` has
  codimension `#s`.
* `TauCeti.Toric.IsDelzant.mem_intrinsicInterior_facetFace_iff`: the relative interior of `F_s`
  consists of the points on exactly the facets in `s`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
* G. M. Ziegler, *Lectures on Polytopes*, Graduate Texts in Mathematics 152, Springer, 1995,
  Section 2.5 (simple polytopes).
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} {s t : Set ι} {x : StrongDual ℝ V}

/-! ### The face cut out by a set of facets -/

variable (i u c) in
/-- The face of the facet polyhedron cut out by a set `s` of facets: the points of the
polyhedron lying on every facet in `s`. -/
def facetFace (s : Set ι) : Set (StrongDual ℝ V) :=
  facetPolyhedron i u c ∩ {x | s ⊆ activeSet (facetPairing i u) c x}

theorem facetFace_def (s : Set ι) :
    facetFace i u c s = facetPolyhedron i u c ∩ {x | s ⊆ activeSet (facetPairing i u) c x} :=
  (rfl)

@[simp]
theorem mem_facetFace :
    x ∈ facetFace i u c s ↔ x ∈ facetPolyhedron i u c ∧ ∀ j ∈ s, x (i (u j)) = c j := by
  simp [facetFace, subset_def]

@[simp]
theorem facetFace_empty : facetFace i u c ∅ = facetPolyhedron i u c := by
  ext
  simp

theorem facetFace_union (s t : Set ι) :
    facetFace i u c (s ∪ t) = facetFace i u c s ∩ facetFace i u c t := by
  ext
  simp only [mem_facetFace, mem_union, or_imp, forall_and, mem_inter_iff]
  tauto

theorem facetFace_antitone : Antitone (facetFace i u c) :=
  fun _ _ hst _ hx ↦ ⟨hx.1, hst.trans hx.2⟩

theorem facetFace_subset_facetPolyhedron (s : Set ι) :
    facetFace i u c s ⊆ facetPolyhedron i u c :=
  inter_subset_left

/-- Every point of the polyhedron lies on the face cut out by its active facets. -/
theorem mem_facetFace_activeSet (hx : x ∈ facetPolyhedron i u c) :
    x ∈ facetFace i u c (activeSet (facetPairing i u) c x) :=
  ⟨hx, Subset.rfl⟩

theorem isExtreme_facetFace (s : Set ι) :
    IsExtreme ℝ (facetPolyhedron i u c) (facetFace i u c s) := by
  rw [facetFace_def, facetPolyhedron_eq_polyhedron]
  exact isExtreme_polyhedron_inter_setOf_subset_activeSet s

theorem convex_facetFace (s : Set ι) : Convex ℝ (facetFace i u c s) := by
  intro x hx y hy a b ha hb hab
  refine mem_facetFace.2 ⟨convex_facetPolyhedron (mem_facetFace.1 hx).1 (mem_facetFace.1 hy).1
    ha hb hab, fun j hj ↦ ?_⟩
  simp [(mem_facetFace.1 hx).2 j hj, (mem_facetFace.1 hy).2 j hj, ← add_mul, hab]

theorem isClosed_facetFace (s : Set ι) : IsClosed (facetFace i u c s) := by
  have : {x : StrongDual ℝ V | s ⊆ activeSet (facetPairing i u) c x} =
      ⋂ j ∈ s, {x | facetPairing i u j x = c j} := by
    ext
    simp [subset_def]
  rw [facetFace_def, this]
  exact isClosed_facetPolyhedron.inter (isClosed_biInter fun j _ ↦
    isClosed_eq (continuous_facetPairing i u j) continuous_const)

/-! ### Faces of the polyhedron -/

variable (i u c) in
/-- The facet constraint `c j ≤ ⟨x, u j⟩` written as `c j - ⟨x, u j⟩ ≤ 0`, for the general
polyhedron API stated with nonpositive affine rows. -/
private def facetRow (j : ι) : StrongDual ℝ V →ᴬ[ℝ] ℝ :=
  ContinuousAffineMap.const ℝ (StrongDual ℝ V) (c j) -
    (ContinuousLinearMap.apply ℝ ℝ (i (u j))).toContinuousAffineMap

private theorem facetRow_apply (j : ι) (x : StrongDual ℝ V) :
    facetRow i u c j x = c j - x (i (u j)) :=
  (rfl)

private theorem facetPolyhedron_eq_setOf_facetRow :
    facetPolyhedron i u c = {x | ∀ j, facetRow i u c j x ≤ 0} := by
  ext
  simp [facetRow_apply]

private theorem facetFace_eq_setOf_facetRow (s : Set ι) :
    facetFace i u c s =
      {x | (∀ j, facetRow i u c j x ≤ 0) ∧ ∀ j ∈ s, facetRow i u c j x = 0} := by
  ext
  simp only [mem_facetFace, mem_facetPolyhedron, mem_ofPred_eq, facetRow_apply, sub_nonpos,
    sub_eq_zero]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ eq_comm

/-- A facet not through a point of the polyhedron is strictly satisfied there: the general
`lt_of_mem_polyhedron_of_notMem_activeSet` with the facet pairings evaluated. -/
private theorem lt_of_notMem_activeSet (hx : x ∈ facetPolyhedron i u c) {j : ι}
    (hj : j ∉ activeSet (facetPairing i u) c x) : c j < x (i (u j)) :=
  facetPairing_apply i u j x ▸
    lt_of_mem_polyhedron_of_notMem_activeSet (facetPolyhedron_eq_polyhedron i u c ▸ hx) hj

/-- The face cut out by any set of facets is an exposed subset of the polyhedron. -/
theorem isExposed_facetFace [Finite ι] (s : Set ι) :
    IsExposed ℝ (facetPolyhedron i u c) (facetFace i u c s) := by
  have hs : s = ↑(toFinite s).toFinset := (Finite.coe_toFinset _).symm
  rw [hs, facetFace_eq_setOf_facetRow, facetPolyhedron_eq_setOf_facetRow]
  exact isExposed_setOf_active _ _

/-- **Faces are cut out by facets.** Every nonempty convex extreme subset of a facet polyhedron,
in particular every nonempty face, is the face cut out by some set of facets. -/
theorem exists_facetFace_eq_of_isExtreme [Finite ι] {F : Set (StrongDual ℝ V)}
    (hF : IsExtreme ℝ (facetPolyhedron i u c) F) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ s, F = facetFace i u c s := by
  rw [facetPolyhedron_eq_setOf_facetRow] at hF
  obtain ⟨I, rfl⟩ := hF.eq_setOf_active (fun j ↦ (facetRow i u c j).toAffineMap) hconv hne
  exact ⟨I, (facetFace_eq_setOf_facetRow (I : Set ι)).symm⟩

/-! ### Simplicity of Delzant polytopes -/

namespace IsDelzant

variable (hΔ : IsDelzant i u c)
include hΔ

/-- **Delzant polytopes are simple.** The normals of the facets through a point of a Delzant
polytope are linearly independent: they are among the normals at a vertex. -/
theorem linearIndepOn_activeSet [FiniteDimensional ℝ V] (hx : x ∈ facetPolyhedron i u c) :
    LinearIndepOn ℤ u (activeSet (facetPairing i u) c x) := by
  obtain ⟨v, hvs, hsub⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hx
  exact (isSmoothVertex_iff_linearIndepOn.1 hvs).1.mono hsub

/-- The real vectors `i (u j)` given by the normals of the facets through a point of a Delzant
polytope in an integral lattice are linearly independent over `ℝ`. -/
theorem linearIndepOn_real_activeSet (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) :
    LinearIndepOn ℝ (fun j ↦ i (u j)) (activeSet (facetPairing i u) c x) := by
  have := hi.finiteDimensional
  exact (linearIndependent_comp_iff_of_liftBaseChange_injective
    hi.isBaseChange.liftBaseChange_injective).2 (hΔ.linearIndepOn_activeSet hx)

/-- The normals of the facets cutting out a nonempty face are linearly independent. -/
theorem linearIndepOn_of_nonempty [FiniteDimensional ℝ V] (hs : (facetFace i u c s).Nonempty) :
    LinearIndepOn ℤ u s := by
  obtain ⟨x, hx, hxs⟩ := hs
  exact (hΔ.linearIndepOn_activeSet hx).mono hxs

/-- At most `rank N` facets meet at a point of a Delzant polytope. -/
theorem ncard_activeSet_le [Finite ι] [FiniteDimensional ℝ V]
    (hx : x ∈ facetPolyhedron i u c) :
    (activeSet (facetPairing i u) c x).ncard ≤ Module.finrank ℤ N := by
  obtain ⟨v, hvs, hsub⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hx
  exact (ncard_le_ncard hsub (toFinite _)).trans hvs.ncard_activeSet.le

/-- The real span of the normals of the facets cutting out a nonempty face has dimension the
number of these facets. Its image in `V / 2π i(N)` is the face subtorus
`TauCeti.Toric.faceSubtorus i u (2 * π) s`, the isotropy subtorus of a symplectic toric manifold
over the relative interior of that face. -/
theorem finrank_span_image_of_nonempty [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    Module.finrank ℝ (Submodule.span ℝ ((fun j ↦ i (u j)) '' s)) = s.ncard := by
  have := hi.finiteDimensional
  have := Fintype.ofFinite s
  obtain ⟨y, hy, hys⟩ := hs
  obtain ⟨v, hvs, hsub⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hy
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hvs
  -- The normals at `v` are the images of an integral basis, hence linearly independent over `ℝ`.
  have hli : LinearIndependent ℝ fun j : s ↦ i (u j) := by
    have := (hi.linearIndependent_basis b).comp (inclusion (hys.trans hsub))
      (inclusion_injective _)
    simpa [Function.comp_def, hb] using this
  rw [image_eq_range, finrank_span_eq_card hli, Fintype.card_eq_nat_card, Nat.card_coe_set_eq]

/-- **Moving off the other facets.** A nonempty face `F_s` of a Delzant polytope has a point lying
on exactly the facets in `s`. -/
theorem exists_activeSet_eq [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    ∃ x ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c x = s := by
  classical
  have := hi.finiteDimensional
  obtain ⟨y, hy, hys⟩ := hs
  obtain ⟨v, hvs, hsub⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hy
  -- In the edge coordinates of the vertex `v`, the direction `w` pairs to `0` with the normals in
  -- `s` and to `1` with the other normals at `v`.
  set w : StrongDual ℝ V := (hvs.edgeBasis hi).equivFun.symm fun k ↦ if (k : ι) ∈ s then 0 else 1
  have hw (k : activeSet (facetPairing i u) c v) :
      w (i (u k)) = if (k : ι) ∈ s then 0 else 1 :=
    hvs.edgeBasis_equivFun_symm_apply hi _ k
  have hw₀ : ∀ j ∈ activeSet (facetPairing i u) c y, 0 ≤ w (i (u j)) := fun j hj ↦ by
    rw [hw ⟨j, hsub hj⟩]
    split_ifs <;> norm_num
  obtain ⟨r, hr, hmove⟩ := exists_pos_forall_add_smul_mem_polyhedron
    (facetPolyhedron_eq_polyhedron (i := i) (u := u) (c := c) ▸ hy) w
  have hmem (a : ℝ) (ha₀ : 0 ≤ a) (har : a ≤ r) : y + a • w ∈ facetPolyhedron i u c := by
    rw [facetPolyhedron_eq_polyhedron]
    exact hmove a (by rwa [abs_of_nonneg ha₀]) fun j hj ↦ mul_nonneg ha₀ (by simpa using hw₀ j hj)
  refine ⟨y + (r / 2) • w, hmem _ (by positivity) (by linarith), ?_⟩
  ext j
  have hval (a : ℝ) : (y + a • w) (i (u j)) = y (i (u j)) + a * w (i (u j)) := by simp
  rw [mem_activeSet, facetPairing_apply, hval]
  by_cases hj : j ∈ activeSet (facetPairing i u) c y
  · -- On a facet through `y`, the move keeps exactly the facets in `s`.
    rw [(by simpa using hj : y (i (u j)) = c j), hw ⟨j, hsub hj⟩]
    split_ifs with hjs <;> simp [hjs, hr.ne']
  · -- Off the facets through `y`, the midpoint of `y` and `y + r • w` keeps some slack.
    have hjs : j ∉ s := fun h ↦ hj (hys h)
    have hlt := lt_of_notMem_activeSet hy hj
    have hle := mem_facetPolyhedron.1 (hmem r hr.le le_rfl) j
    rw [hval] at hle
    simp only [hjs, iff_false]
    intro h
    linarith

/-- **Faces determine their facets.** For a nonempty face `F_s` of a Delzant polytope,
`F_s ⊆ F_t` exactly when `t ⊆ s`. -/
theorem facetFace_subset_facetFace_iff [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    facetFace i u c s ⊆ facetFace i u c t ↔ t ⊆ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ facetFace_antitone h⟩
  obtain ⟨x, hx, hxs⟩ := hΔ.exists_activeSet_eq hi hs
  exact hxs ▸ (h (hxs ▸ mem_facetFace_activeSet hx)).2

/-- Distinct sets of facets with nonempty intersection cut out distinct faces. -/
theorem injOn_facetFace [Finite ι] (hi : IsIntegralLattice i) :
    InjOn (facetFace i u c) {s | (facetFace i u c s).Nonempty} := fun _ hs _ ht hst ↦
  ((hΔ.facetFace_subset_facetFace_iff hi ht).1 hst.ge).antisymm
    ((hΔ.facetFace_subset_facetFace_iff hi hs).1 hst.le)

/-- **The face dictionary.** Every nonempty convex extreme subset of a Delzant polytope, in
particular every nonempty face, is cut out by a unique set of facets. -/
theorem existsUnique_facetFace_eq [Finite ι] (hi : IsIntegralLattice i)
    {F : Set (StrongDual ℝ V)} (hF : IsExtreme ℝ (facetPolyhedron i u c) F)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃! s, F = facetFace i u c s := by
  obtain ⟨s, rfl⟩ := exists_facetFace_eq_of_isExtreme hF hconv hne
  exact ⟨s, rfl, fun t ht ↦
    hΔ.injOn_facetFace hi (ht ▸ hne : (facetFace i u c t).Nonempty) hne ht.symm⟩

/-! ### Dimension and relative interior of a face -/

/-- **The direction of a face.** The direction of a nonempty face `F_s` of a Delzant polytope is
the common kernel of the pairings with the normals in `s`. -/
theorem vectorSpan_facetFace [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    vectorSpan ℝ (facetFace i u c s) = ⨅ j ∈ s, LinearMap.ker (facetPairing i u j) := by
  obtain ⟨x, hx, hxs⟩ := hΔ.exists_activeSet_eq hi hs
  set g : ι → (StrongDual ℝ V →ᵃ[ℝ] ℝ) := fun j ↦ (facetRow i u c j).toAffineMap
  have hg (j : ι) (y : StrongDual ℝ V) : g j y = c j - y (i (u j)) := facetRow_apply j y
  have hlin (j : ι) : LinearMap.ker (g j).linear = LinearMap.ker (facetPairing i u j) := by
    ext w
    have hw : (g j).linear w = g j w - g j 0 := by simpa using (g j).linear_apply_vsub w 0
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hw, hg, hg]
    simp
  have hface : {y | y ∈ (⊤ : AffineSubspace ℝ (StrongDual ℝ V)) ∧ (∀ l, g l y ≤ 0) ∧
      ∀ l ∈ s, g l y = 0} = facetFace i u c s := by
    simpa [g] using (facetFace_eq_setOf_facetRow s).symm
  have h := vectorSpan_setOf_active_eq g ⊤ s (AffineSubspace.mem_top ℝ _ x)
    (fun j hj ↦ by
      rw [hg, sub_eq_zero]
      rw [← hxs] at hj
      exact (by simpa using hj : x (i (u j)) = c j).symm)
    (fun j hj ↦ by
      rw [hg, sub_neg]
      exact lt_of_notMem_activeSet hx (hxs ▸ hj))
  rw [hface] at h
  simp only [h, AffineSubspace.direction_top, top_inf_eq, hlin]

/-- **Faces of a Delzant polytope have the expected codimension.** A nonempty face `F_s` of a
Delzant polytope has dimension `dim V - #s`. -/
theorem finrank_vectorSpan_facetFace_add_ncard [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (facetFace i u c s)) + s.ncard = Module.finrank ℝ V := by
  classical
  have := hi.finiteDimensional
  have := Fintype.ofFinite s
  obtain ⟨y, hy, hys⟩ := hs
  obtain ⟨v, hvs, hsub⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hy
  -- The pairings with the normals in `s` form a surjective map `V* → ℝ^s`, through the edge
  -- coordinates at the vertex `v`; its kernel is the direction of the face.
  set Φ : StrongDual ℝ V →ₗ[ℝ] s → ℝ := LinearMap.pi fun j : s ↦ facetPairing i u j
  have hΦ : Function.Surjective Φ := fun f ↦ by
    refine ⟨(hvs.edgeBasis hi).equivFun.symm fun k ↦ if h : (k : ι) ∈ s then f ⟨k, h⟩ else 0,
      funext fun j ↦ ?_⟩
    have := hvs.edgeBasis_equivFun_symm_apply hi
      (fun k ↦ if h : (k : ι) ∈ s then f ⟨k, h⟩ else 0) ⟨j, hsub (hys j.property)⟩
    simp only [j.property, dite_true] at this
    simpa only [Φ, LinearMap.pi_apply, facetPairing_apply] using this
  have hker : LinearMap.ker Φ = vectorSpan ℝ (facetFace i u c s) := by
    rw [hΔ.vectorSpan_facetFace hi ⟨y, hy, hys⟩, LinearMap.ker_pi]
    ext w
    simp [Submodule.mem_iInf]
  rw [← hker, ← ContinuousLinearMap.dual_finrank_eq, ← LinearMap.finrank_range_add_finrank_ker Φ,
    LinearMap.range_eq_top.2 hΦ, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_eq_nat_card, Nat.card_coe_set_eq, add_comm]

/-- **Vertices of a Delzant polytope.** A point of a Delzant polytope is a vertex exactly when it
lies on `dim V` facets. -/
theorem mem_extremePoints_iff_ncard_activeSet [Finite ι] (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) :
    x ∈ (facetPolyhedron i u c).extremePoints ℝ ↔
      (activeSet (facetPairing i u) c x).ncard = Module.finrank ℝ V := by
  have := hi.finiteDimensional
  rw [mem_extremePoints_facetPolyhedron_iff_span_eq_top, and_iff_right hx,
    ← hΔ.finrank_span_image_of_nonempty hi ⟨x, mem_facetFace_activeSet hx⟩]
  exact ⟨fun h ↦ by rw [h, finrank_top], Submodule.eq_top_of_finrank_eq⟩

/-- **The relative interior of a face.** The relative interior of a nonempty face `F_s` of a
Delzant polytope consists of the points of the polytope lying on exactly the facets in `s`. -/
theorem mem_intrinsicInterior_facetFace_iff [Finite ι] (hi : IsIntegralLattice i)
    (hs : (facetFace i u c s).Nonempty) :
    x ∈ intrinsicInterior ℝ (facetFace i u c s) ↔
      x ∈ facetPolyhedron i u c ∧ activeSet (facetPairing i u) c x = s := by
  obtain ⟨p, hp, hps⟩ := hΔ.exists_activeSet_eq hi hs
  -- Present the face by the facet rows together with the negated rows of the facets in `s`.
  set g : ι ⊕ s → (StrongDual ℝ V →ᴬ[ℝ] ℝ) :=
    Sum.elim (facetRow i u c) fun j ↦ -facetRow i u c j
  have hP : facetFace i u c s = {y | ∀ r, g r y ≤ 0} := by
    rw [facetFace_eq_setOf_facetRow]
    ext y
    simp only [mem_ofPred_eq, Sum.forall, g, Sum.elim_inl, Sum.elim_inr,
      ContinuousAffineMap.coe_neg, Pi.neg_apply, neg_nonpos, Subtype.forall]
    exact and_congr_right fun h ↦ forall₂_congr fun j _ ↦ ⟨ge_of_eq, (h j).antisymm⟩
  rw [mem_intrinsicInterior_iff_forall_lt g (eq_setOf_mem_affineSpan_and hP)]
  constructor
  · rintro ⟨hx, hlt⟩
    refine ⟨hx.1, subset_antisymm (fun j hj ↦ ?_) hx.2⟩
    -- A facet through `x` outside `s` would be strict at `p` but not at `x`.
    by_contra hjs
    have hpj := lt_of_notMem_activeSet hp (hps ▸ hjs)
    have := hlt (.inl j) ⟨p, hps ▸ mem_facetFace_activeSet hp, by
      simpa [g, facetRow_apply] using hpj⟩
    simp only [g, Sum.elim_inl, facetRow_apply, sub_neg] at this
    exact this.ne' (by simpa using mem_activeSet.1 hj)
  · rintro ⟨hx, rfl⟩
    refine ⟨mem_facetFace_activeSet hx, ?_⟩
    rintro (j | ⟨j, hj⟩) ⟨q, hq, hlt⟩
    · simp only [g, Sum.elim_inl, facetRow_apply, sub_neg] at hlt ⊢
      exact lt_of_notMem_activeSet hx fun hj ↦ hlt.ne' ((mem_facetFace.1 hq).2 j hj)
    · simp only [g, Sum.elim_inr, ContinuousAffineMap.coe_neg, Pi.neg_apply, facetRow_apply,
        neg_neg_iff_pos, sub_pos] at hlt
      exact absurd ((mem_facetFace.1 hq).2 j hj) hlt.ne

/-- Each point of a Delzant polytope lies in the relative interior of the face cut out by its
active facets. -/
theorem mem_intrinsicInterior_facetFace_activeSet [Finite ι] (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) :
    x ∈ intrinsicInterior ℝ (facetFace i u c (activeSet (facetPairing i u) c x)) :=
  (hΔ.mem_intrinsicInterior_facetFace_iff hi ⟨x, mem_facetFace_activeSet hx⟩).2 ⟨hx, rfl⟩

end IsDelzant

end TauCeti.Toric
