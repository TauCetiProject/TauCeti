/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

import TauCeti.LinearAlgebra.LinearIndependent.Basic

/-!
# Products of Delzant polytopes

The product of two symplectic toric manifolds is a symplectic toric manifold for the product
torus, and its moment polytope is the product `Δ × Δ'` of the two moment polytopes. This file
describes that product at the level of facet presentations.

Let `i : N →+ V` and `i' : N' →+ V'` be lattices with facet presentations `(u, c)` and
`(u', c')`. The product lattice is `i × i' : N × N' →+ V × V'` (`AddMonoidHom.prodMap`). Its facet
normals are indexed by `ι ⊕ ι'`: they are `(u j, 0)` and `(0, u' j')`
(`TauCeti.Toric.prodNormal u u'`), with support constants `Sum.elim c c'`. A point of the dual
`(V × V')*` is a pair of points `y ∈ V*`, `y' ∈ V'*`, by `ContinuousLinearMap.coprod`, and

* it lies in the product polyhedron exactly when `y ∈ Δ` and `y' ∈ Δ'`
  (`TauCeti.Toric.coprod_mem_facetPolyhedron_prod_iff`), so the product polyhedron is the image
  of `Δ × Δ'` (`TauCeti.Toric.facetPolyhedron_prod`);
* its active constraints are those of `y`, tagged by `Sum.inl`, together with those of `y'`,
  tagged by `Sum.inr` (`TauCeti.Toric.activeSet_prod`);
* it is a vertex exactly when both `y` and `y'` are vertices
  (`TauCeti.Toric.coprod_mem_extremePoints_facetPolyhedron_prod_iff`), and a smooth vertex exactly
  when both are smooth vertices (`TauCeti.Toric.isSmoothVertex_prod_iff`): a lattice basis of
  `N × N'` made of active normals splits into lattice bases of `N` and of `N'`.

For nonempty factors, the product polyhedron is bounded exactly when both factors are
(`TauCeti.Toric.isBounded_facetPolyhedron_prod_iff`). Consequently, for finite-dimensional
spaces, the factors of a Delzant product presentation are Delzant
(`TauCeti.Toric.IsDelzant.of_prod`). Conversely, for injective lattice maps and finitely many
facets, the product of Delzant presentations is Delzant (`TauCeti.Toric.IsDelzant.prod`).
Irredundancy of a facet `(u j, 0)` of the product uses a point of `Δ'` on no facet of `Δ'`, which a
Delzant polytope has (`TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`). Together these give
`TauCeti.Toric.isDelzant_prod_iff`.

## Main definitions

* `TauCeti.Toric.prodNormal u u'`: the facet normals `(u j, 0)` and `(0, u' j')` of `Δ × Δ'`.

## Main results

* `TauCeti.Toric.facetPolyhedron_prod`: the product polyhedron is `Δ × Δ'`.
* `TauCeti.Toric.activeSet_prod`: the active constraints of the product.
* `TauCeti.Toric.isSmoothVertex_prod_iff`: smooth vertices of the product.
* `TauCeti.Toric.isBounded_facetPolyhedron_prod_iff`: for nonempty factors, the product is bounded
  exactly when both factors are.
* `TauCeti.Toric.IsDelzant.of_prod`: for finite-dimensional spaces, the factors of a Delzant
  product are Delzant.
* `TauCeti.Toric.IsDelzant.prod`: for injective lattice maps into finite-dimensional spaces and
  finitely many facets, the product of Delzant polytopes is Delzant.
* `TauCeti.Toric.isDelzant_prod_iff`: under the hypotheses of `TauCeti.Toric.IsDelzant.prod`, the
  product is Delzant exactly when both factors are.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {ι ι' N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {u : ι → N} {u' : ι' → N'} {c : ι → ℝ} {c' : ι' → ℝ}

variable (u u') in
/-- The facet normals of the product of two polytopes: `(u j, 0)` for the facets of the first
factor and `(0, u' j')` for those of the second. -/
def prodNormal : ι ⊕ ι' → N × N' :=
  Sum.elim (fun j ↦ (u j, 0)) fun j ↦ (0, u' j)

@[simp]
theorem prodNormal_inl (j : ι) : prodNormal u u' (.inl j) = (u j, 0) :=
  (rfl)

@[simp]
theorem prodNormal_inr (j : ι') : prodNormal u u' (.inr j) = (0, u' j) :=
  (rfl)

/-- The point `y.coprod y'` of the product lies in the product polyhedron exactly when `y` and
`y'` lie in the factors. -/
theorem coprod_mem_facetPolyhedron_prod_iff (y : StrongDual ℝ V) (y' : StrongDual ℝ V') :
    y.coprod y' ∈ facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c') ↔
      y ∈ facetPolyhedron i u c ∧ y' ∈ facetPolyhedron i' u' c' := by
  simp [Sum.forall]

/-- The product polyhedron is the image of `Δ × Δ'` under the identification
`V* × V'* ≃ (V × V')*`. -/
theorem facetPolyhedron_prod :
    facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c') =
      ContinuousLinearMap.coprodEquivL ℝ '' facetPolyhedron i u c ×ˢ facetPolyhedron i' u' c' := by
  ext x
  simp [ContinuousLinearEquiv.image_eq_preimage_symm]

/-- The constraints active at `y.coprod y'` are those active at `y` and those active at `y'`. -/
@[simp]
theorem activeSet_prod (y : StrongDual ℝ V) (y' : StrongDual ℝ V') :
    activeSet (facetPairing (i.prodMap i') (prodNormal u u')) (Sum.elim c c') (y.coprod y') =
      Sum.inl '' activeSet (facetPairing i u) c y ∪
        Sum.inr '' activeSet (facetPairing i' u') c' y' := by
  ext (j | j) <;> simp [eq_comm]

/-- The point `y.coprod y'` is a vertex of the product polyhedron exactly when `y` and `y'` are
vertices of the factors. -/
@[simp]
theorem coprod_mem_extremePoints_facetPolyhedron_prod_iff (y : StrongDual ℝ V)
    (y' : StrongDual ℝ V') :
    y.coprod y' ∈ (facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c')).extremePoints ℝ
      ↔ y ∈ (facetPolyhedron i u c).extremePoints ℝ ∧
        y' ∈ (facetPolyhedron i' u' c').extremePoints ℝ := by
  rw [facetPolyhedron_prod, ← image_extremePoints, extremePoints_prod]
  simp [ContinuousLinearEquiv.image_eq_preimage_symm]

/-- The family of normals `(u j, 0)`, `(0, u' j')` is linearly independent on
`Sum.inl '' s ∪ Sum.inr '' t` exactly when `u` is on `s` and `u'` is on `t`. -/
private theorem linearIndepOn_prodNormal_iff {s : Set ι} {t : Set ι'} :
    LinearIndepOn ℤ (prodNormal u u') (Sum.inl '' s ∪ Sum.inr '' t) ↔
      LinearIndepOn ℤ u s ∧ LinearIndepOn ℤ u' t := by
  have hl : prodNormal u u' ∘ Sum.inl = LinearMap.inl ℤ N N' ∘ u := funext fun j ↦ by simp
  have hr : prodNormal u u' ∘ Sum.inr = LinearMap.inr ℤ N N' ∘ u' := funext fun j ↦ by simp
  have hdisj : Disjoint (Submodule.span ℤ (prodNormal u u' '' (Sum.inl '' s)))
      (Submodule.span ℤ (prodNormal u u' '' (Sum.inr '' t))) := by
    refine (LinearMap.disjoint_inl_inr (R := ℤ) (M := N) (M₂ := N')).mono ?_ ?_ <;>
      refine Submodule.span_le.2 ?_ <;> rintro _ ⟨_, ⟨j, -, rfl⟩, rfl⟩ <;> simp
  rw [linearIndepOn_union_iff disjoint_image_inl_image_inr, and_iff_left hdisj]
  refine and_congr ?_ ?_
  · rw [linearIndepOn_image_iff _ Sum.inl_injective.injOn, hl]
    exact LinearMap.linearIndepOn_iff_of_injOn _ LinearMap.inl_injective.injOn
  · rw [linearIndepOn_image_iff _ Sum.inr_injective.injOn, hr]
    exact LinearMap.linearIndepOn_iff_of_injOn _ LinearMap.inr_injective.injOn

/-- The normals `(u j, 0)`, `(0, u' j')` indexed by `Sum.inl '' s ∪ Sum.inr '' t` generate
`N × N'` exactly when `u` generates `N` on `s` and `u'` generates `N'` on `t`. -/
private theorem span_prodNormal_eq_top_iff {s : Set ι} {t : Set ι'} :
    Submodule.span ℤ (prodNormal u u' '' (Sum.inl '' s ∪ Sum.inr '' t)) = ⊤ ↔
      Submodule.span ℤ (u '' s) = ⊤ ∧ Submodule.span ℤ (u' '' t) = ⊤ := by
  rw [image_union, image_image, image_image, Submodule.span_union]
  have hl : (fun j ↦ prodNormal u u' (Sum.inl j)) '' s = LinearMap.inl ℤ N N' '' (u '' s) := by
    simp [image_image]
  have hr : (fun j ↦ prodNormal u u' (Sum.inr j)) '' t = LinearMap.inr ℤ N N' '' (u' '' t) := by
    simp [image_image]
  rw [hl, hr, Submodule.span_image, Submodule.span_image, Submodule.map_inl, Submodule.map_inr,
    Submodule.prod_sup_prod, sup_bot_eq, bot_sup_eq, Submodule.prod_eq_top_iff]

/-- **Smooth vertices of a product.** The point `y.coprod y'` is a smooth vertex of the product
presentation exactly when `y` and `y'` are smooth vertices of the factors. -/
@[simp]
theorem isSmoothVertex_prod_iff (y : StrongDual ℝ V) (y' : StrongDual ℝ V') :
    IsSmoothVertex (i.prodMap i') (prodNormal u u') (Sum.elim c c') (y.coprod y') ↔
      IsSmoothVertex i u c y ∧ IsSmoothVertex i' u' c' y' := by
  rw [isSmoothVertex_iff_linearIndepOn, isSmoothVertex_iff_linearIndepOn,
    isSmoothVertex_iff_linearIndepOn, activeSet_prod, linearIndepOn_prodNormal_iff,
    span_prodNormal_eq_top_iff]
  tauto

/-- For nonempty factors, the product polyhedron is bounded exactly when both factors are. -/
theorem isBounded_facetPolyhedron_prod_iff (hne : (facetPolyhedron i u c).Nonempty)
    (hne' : (facetPolyhedron i' u' c').Nonempty) :
    Bornology.IsBounded (facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c')) ↔
      Bornology.IsBounded (facetPolyhedron i u c) ∧
        Bornology.IsBounded (facetPolyhedron i' u' c') := by
  let e := ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := V) (F := V') (G := ℝ) ℝ
  rw [facetPolyhedron_prod, ← Bornology.isBounded_prod_of_nonempty (hne.prod hne')]
  refine ⟨fun h ↦ ?_, fun h ↦ (e : StrongDual ℝ V × StrongDual ℝ V' →L[ℝ] StrongDual ℝ (V × V')
    ).lipschitzWith.isBounded_image h⟩
  simpa [e] using (e.symm : StrongDual ℝ (V × V') →L[ℝ] StrongDual ℝ V × StrongDual ℝ V'
    ).lipschitzWith.isBounded_image h

namespace IsDelzant

/-- **Factors of a Delzant product.** For finite-dimensional spaces, if the product presentation
`(prodNormal u u', Sum.elim c c')` is Delzant, then so are both factors. -/
theorem of_prod [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
    (h : IsDelzant (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    IsDelzant i u c ∧ IsDelzant i' u' c' := by
  -- The factors are the projections of the nonempty bounded product.
  obtain ⟨x, hx⟩ := h.nonempty
  rw [← ContinuousLinearMap.coprod_comp_inl_inr x, coprod_mem_facetPolyhedron_prod_iff] at hx
  obtain ⟨hbdd₁, hbdd₂⟩ := (isBounded_facetPolyhedron_prod_iff ⟨_, hx.1⟩ ⟨_, hx.2⟩).1 h.isBounded
  obtain ⟨z, hz⟩ := (Metric.isCompact_of_isClosed_isBounded isClosed_facetPolyhedron
    hbdd₁).extremePoints_nonempty ⟨_, hx.1⟩
  obtain ⟨z', hz'⟩ := (Metric.isCompact_of_isClosed_isBounded isClosed_facetPolyhedron
    hbdd₂).extremePoints_nonempty ⟨_, hx.2⟩
  -- An irredundancy witness of the product restricts to one of each factor.
  have hirr (k : ι ⊕ ι') : ∃ y₁ ∈ facetPolyhedron i u c, ∃ y₂ ∈ facetPolyhedron i' u' c',
      Sum.inl '' activeSet (facetPairing i u) c y₁ ∪
        Sum.inr '' activeSet (facetPairing i' u') c' y₂ = {k} := by
    obtain ⟨x, hx, hxk⟩ := h.irredundant k
    rw [← ContinuousLinearMap.coprod_comp_inl_inr x, coprod_mem_facetPolyhedron_prod_iff] at hx
    rw [← ContinuousLinearMap.coprod_comp_inl_inr x, activeSet_prod] at hxk
    exact ⟨_, hx.1, _, hx.2, hxk⟩
  refine ⟨⟨hbdd₁, fun y hy ↦ ?_, fun j ↦ ?_⟩, ⟨hbdd₂, fun y' hy' ↦ ?_, fun j ↦ ?_⟩⟩
  · exact ((isSmoothVertex_prod_iff y z').1 (h.isSmoothVertex _
      ((coprod_mem_extremePoints_facetPolyhedron_prod_iff y z').2 ⟨hy, hz'⟩))).1
  · obtain ⟨y₁, hy₁, _, _, hk⟩ := hirr (.inl j)
    exact ⟨y₁, hy₁, ext fun j' ↦ by simpa using Set.ext_iff.1 hk (.inl j')⟩
  · exact ((isSmoothVertex_prod_iff z y').1 (h.isSmoothVertex _
      ((coprod_mem_extremePoints_facetPolyhedron_prod_iff z y').2 ⟨hz, hy'⟩))).2
  · obtain ⟨_, _, y₂, hy₂, hk⟩ := hirr (.inr j)
    exact ⟨y₂, hy₂, ext fun j' ↦ by simpa using Set.ext_iff.1 hk (.inr j')⟩

/-- **Products of Delzant polytopes.** For injective lattice maps into finite-dimensional spaces
and finitely many facets, the product presentation `(prodNormal u u', Sum.elim c c')` of two
Delzant presentations is Delzant. -/
theorem prod [Finite ι] [Finite ι'] [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
    (hi : Function.Injective i) (hi' : Function.Injective i') (h : IsDelzant i u c)
    (h' : IsDelzant i' u' c') : IsDelzant (i.prodMap i') (prodNormal u u') (Sum.elim c c') := by
  -- A point on no facet of the other factor serves as the irredundancy witness's partner.
  obtain ⟨z, hz, hz₀⟩ := h.exists_activeSet_eq_empty hi
  obtain ⟨z', hz', hz₀'⟩ := h'.exists_activeSet_eq_empty hi'
  refine ⟨(isBounded_facetPolyhedron_prod_iff ⟨z, hz⟩ ⟨z', hz'⟩).2 ⟨h.isBounded, h'.isBounded⟩,
    fun x hx ↦ ?_, ?_⟩
  · rw [← ContinuousLinearMap.coprod_comp_inl_inr x] at hx ⊢
    rw [coprod_mem_extremePoints_facetPolyhedron_prod_iff] at hx
    exact (isSmoothVertex_prod_iff _ _).2 ⟨h.isSmoothVertex _ hx.1, h'.isSmoothVertex _ hx.2⟩
  · rintro (j | j)
    · obtain ⟨y, hy, hyj⟩ := h.irredundant j
      exact ⟨y.coprod z', (coprod_mem_facetPolyhedron_prod_iff _ _).2 ⟨hy, hz'⟩, by
        rw [activeSet_prod, hyj, hz₀', image_empty, union_empty, image_singleton]⟩
    · obtain ⟨y', hy', hyj'⟩ := h'.irredundant j
      exact ⟨z.coprod y', (coprod_mem_facetPolyhedron_prod_iff _ _).2 ⟨hz, hy'⟩, by
        rw [activeSet_prod, hz₀, hyj', image_empty, empty_union, image_singleton]⟩

end IsDelzant

/-- **Products of Delzant polytopes.** For injective lattice maps into finite-dimensional spaces
and finitely many facets, the product presentation `(prodNormal u u', Sum.elim c c')` is Delzant
exactly when both factors are. -/
theorem isDelzant_prod_iff [Finite ι] [Finite ι'] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ V'] (hi : Function.Injective i) (hi' : Function.Injective i') :
    IsDelzant (i.prodMap i') (prodNormal u u') (Sum.elim c c') ↔
      IsDelzant i u c ∧ IsDelzant i' u' c' :=
  ⟨IsDelzant.of_prod, fun h ↦ h.1.prod hi hi' h.2⟩

end TauCeti.Toric
