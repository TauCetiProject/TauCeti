/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

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

Consequently, for injective lattice maps into finite-dimensional spaces and finitely many facets,
the product presentation is Delzant exactly when both factors are
(`TauCeti.Toric.isDelzant_prod_iff`). Irredundancy of a facet `(u j, 0)` of the product uses a
point of `Δ'` on no facet of `Δ'`, which a Delzant polytope has
(`TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`).

## Main definitions

* `TauCeti.Toric.prodNormal u u'`: the facet normals `(u j, 0)` and `(0, u' j')` of `Δ × Δ'`.

## Main results

* `TauCeti.Toric.facetPolyhedron_prod`: the product polyhedron is `Δ × Δ'`.
* `TauCeti.Toric.activeSet_prod`: the active constraints of the product.
* `TauCeti.Toric.isSmoothVertex_prod_iff`: smooth vertices of the product.
* `TauCeti.Toric.isDelzant_prod_iff`: the product of Delzant polytopes is Delzant, and conversely.

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
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage,
    ContinuousLinearMap.coprodEquivL_symm_apply, mem_prod,
    ← coprod_mem_facetPolyhedron_prod_iff, ContinuousLinearMap.coprod_comp_inl_inr]

/-- The constraints active at `y.coprod y'` are those active at `y` and those active at `y'`. -/
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
  rw [facetPolyhedron_prod, ← image_extremePoints, extremePoints_prod,
    ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage,
    ContinuousLinearMap.coprodEquivL_symm_apply, ContinuousLinearMap.coprod_comp_inl,
    ContinuousLinearMap.coprod_comp_inr, mem_prod]

/-- The family of normals `(u j, 0)`, `(0, u' j')` is linearly independent on
`Sum.inl '' s ∪ Sum.inr '' t` exactly when `u` is on `s` and `u'` is on `t`. -/
private theorem linearIndepOn_prodNormal_iff {s : Set ι} {t : Set ι'} :
    LinearIndepOn ℤ (prodNormal u u') (Sum.inl '' s ∪ Sum.inr '' t) ↔
      LinearIndepOn ℤ u s ∧ LinearIndepOn ℤ u' t := by
  have hl : prodNormal u u' ∘ Sum.inl = LinearMap.inl ℤ N N' ∘ u := (rfl)
  have hr : prodNormal u u' ∘ Sum.inr = LinearMap.inr ℤ N N' ∘ u' := (rfl)
  have hdisj : Disjoint (Submodule.span ℤ (prodNormal u u' '' (Sum.inl '' s)))
      (Submodule.span ℤ (prodNormal u u' '' (Sum.inr '' t))) := by
    refine (LinearMap.disjoint_inl_inr (R := ℤ) (M := N) (M₂ := N')).mono ?_ ?_ <;>
      refine Submodule.span_le.2 ?_ <;> rintro _ ⟨_, ⟨j, -, rfl⟩, rfl⟩ <;> simp
  rw [linearIndepOn_union_iff disjoint_image_inl_image_inr, and_iff_left hdisj]
  refine and_congr ?_ ?_
  · rw [show LinearIndepOn ℤ (prodNormal u u') (Sum.inl '' s) ↔
        LinearIndepOn ℤ (prodNormal u u' ∘ Sum.inl) s from
      ⟨fun h ↦ h.comp_of_image Sum.inl_injective.injOn, LinearIndepOn.image_of_comp _ _⟩, hl]
    exact LinearMap.linearIndepOn_iff_of_injOn _ LinearMap.inl_injective.injOn
  · rw [show LinearIndepOn ℤ (prodNormal u u') (Sum.inr '' t) ↔
        LinearIndepOn ℤ (prodNormal u u' ∘ Sum.inr) t from
      ⟨fun h ↦ h.comp_of_image Sum.inr_injective.injOn, LinearIndepOn.image_of_comp _ _⟩, hr]
    exact LinearMap.linearIndepOn_iff_of_injOn _ LinearMap.inr_injective.injOn

/-- The normals `(u j, 0)`, `(0, u' j')` indexed by `Sum.inl '' s ∪ Sum.inr '' t` generate
`N × N'` exactly when `u` generates `N` on `s` and `u'` generates `N'` on `t`. -/
private theorem span_prodNormal_eq_top_iff {s : Set ι} {t : Set ι'} :
    Submodule.span ℤ (prodNormal u u' '' (Sum.inl '' s ∪ Sum.inr '' t)) = ⊤ ↔
      Submodule.span ℤ (u '' s) = ⊤ ∧ Submodule.span ℤ (u' '' t) = ⊤ := by
  rw [image_union, image_image, image_image, Submodule.span_union]
  have hl : (fun j ↦ prodNormal u u' (Sum.inl j)) '' s = LinearMap.inl ℤ N N' '' (u '' s) := by
    rw [image_image]; rfl
  have hr : (fun j ↦ prodNormal u u' (Sum.inr j)) '' t = LinearMap.inr ℤ N N' '' (u' '' t) := by
    rw [image_image]; rfl
  rw [hl, hr, Submodule.span_image, Submodule.span_image, Submodule.map_inl, Submodule.map_inr,
    Submodule.prod_sup_prod, sup_bot_eq, bot_sup_eq, Submodule.prod_eq_top_iff]

/-- **Smooth vertices of a product.** The point `y.coprod y'` is a smooth vertex of the product
presentation exactly when `y` and `y'` are smooth vertices of the factors. -/
theorem isSmoothVertex_prod_iff (y : StrongDual ℝ V) (y' : StrongDual ℝ V') :
    IsSmoothVertex (i.prodMap i') (prodNormal u u') (Sum.elim c c') (y.coprod y') ↔
      IsSmoothVertex i u c y ∧ IsSmoothVertex i' u' c' y' := by
  rw [isSmoothVertex_iff_linearIndepOn, isSmoothVertex_iff_linearIndepOn,
    isSmoothVertex_iff_linearIndepOn, activeSet_prod, linearIndepOn_prodNormal_iff,
    span_prodNormal_eq_top_iff]
  tauto

/-- **Products of Delzant polytopes.** For injective lattice maps into finite-dimensional spaces
and finitely many facets, the product presentation `(prodNormal u u', Sum.elim c c')` is Delzant
exactly when both factors are. -/
theorem isDelzant_prod_iff [Finite ι] [Finite ι'] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ V'] (hi : Function.Injective i) (hi' : Function.Injective i') :
    IsDelzant (i.prodMap i') (prodNormal u u') (Sum.elim c c') ↔
      IsDelzant i u c ∧ IsDelzant i' u' c' := by
  refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ ?_⟩
  · -- The factors are the projections of the nonempty bounded product.
    have hbdd : Bornology.IsBounded (facetPolyhedron i u c ×ˢ facetPolyhedron i' u' c') := by
      have := ((ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := V) (F := V') (G := ℝ) ℝ).symm :
        StrongDual ℝ (V × V') →L[ℝ] StrongDual ℝ V × StrongDual ℝ V').lipschitzWith.isBounded_image
        h.isBounded
      rwa [facetPolyhedron_prod, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_image_image] at this
    obtain ⟨x, hx⟩ := h.nonempty
    rw [facetPolyhedron_prod] at hx
    obtain ⟨⟨y, y'⟩, ⟨hy, hy'⟩, -⟩ := hx
    have hbdd₁ := hbdd.fst_of_prod ⟨y', hy'⟩
    have hbdd₂ := hbdd.snd_of_prod ⟨y, hy⟩
    have hcpt₁ : IsCompact (facetPolyhedron i u c) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_facetPolyhedron hbdd₁
    have hcpt₂ : IsCompact (facetPolyhedron i' u' c') :=
      Metric.isCompact_of_isClosed_isBounded isClosed_facetPolyhedron hbdd₂
    obtain ⟨z, hz⟩ := hcpt₁.extremePoints_nonempty ⟨y, hy⟩
    obtain ⟨z', hz'⟩ := hcpt₂.extremePoints_nonempty ⟨y', hy'⟩
    -- An irredundancy witness of the product restricts to one of a factor.
    have hirr : ∀ k : ι ⊕ ι', ∃ y₁ : StrongDual ℝ V, ∃ y₂ : StrongDual ℝ V',
        y₁ ∈ facetPolyhedron i u c ∧ y₂ ∈ facetPolyhedron i' u' c' ∧
        Sum.inl '' activeSet (facetPairing i u) c y₁ ∪
          Sum.inr '' activeSet (facetPairing i' u') c' y₂ = {k} := fun k ↦ by
      obtain ⟨x, hx, hxk⟩ := h.irredundant k
      rw [← ContinuousLinearMap.coprod_comp_inl_inr x] at hx hxk
      rw [activeSet_prod] at hxk
      exact ⟨_, _, ((coprod_mem_facetPolyhedron_prod_iff _ _).1 hx).1,
        ((coprod_mem_facetPolyhedron_prod_iff _ _).1 hx).2, hxk⟩
    refine ⟨⟨hbdd₁, fun y hy ↦ ?_, fun j ↦ ?_⟩, ⟨hbdd₂, fun y' hy' ↦ ?_, fun j ↦ ?_⟩⟩
    · exact ((isSmoothVertex_prod_iff y z').1 (h.isSmoothVertex _
        ((coprod_mem_extremePoints_facetPolyhedron_prod_iff y z').2 ⟨hy, hz'⟩))).1
    · obtain ⟨y₁, y₂, hy₁, -, hk⟩ := hirr (.inl j)
      refine ⟨y₁, hy₁, ?_⟩
      have hj : Sum.inl ⁻¹' ({.inl j} : Set (ι ⊕ ι')) = {j} := by ext; simp
      simpa [preimage_union, preimage_image_eq _ Sum.inl_injective, hj] using
        congrArg (Sum.inl ⁻¹' ·) hk
    · exact ((isSmoothVertex_prod_iff z y').1 (h.isSmoothVertex _
        ((coprod_mem_extremePoints_facetPolyhedron_prod_iff z y').2 ⟨hz, hy'⟩))).2
    · obtain ⟨y₁, y₂, -, hy₂, hk⟩ := hirr (.inr j)
      refine ⟨y₂, hy₂, ?_⟩
      have hj : Sum.inr ⁻¹' ({.inr j} : Set (ι ⊕ ι')) = {j} := by ext; simp
      simpa [preimage_union, preimage_image_eq _ Sum.inr_injective, hj] using
        congrArg (Sum.inr ⁻¹' ·) hk
  · -- The product of the factors, with a point on no facet of the other factor as witness.
    obtain ⟨z, hz, hz₀⟩ := h.exists_activeSet_eq_empty hi
    obtain ⟨z', hz', hz₀'⟩ := h'.exists_activeSet_eq_empty hi'
    refine ⟨?_, fun x hx ↦ ?_, ?_⟩
    · rw [facetPolyhedron_prod]
      exact ((ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := V) (F := V') (G := ℝ) ℝ :
        StrongDual ℝ V × StrongDual ℝ V' →L[ℝ] StrongDual ℝ (V × V')).lipschitzWith.isBounded_image
        (h.isBounded.prod h'.isBounded))
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

end TauCeti.Toric
