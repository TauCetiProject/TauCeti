/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

/-!
# Relabelling facets and changing the lattice of a Delzant presentation

A facet presentation `(u, c)` in a lattice `i : N →+ V` (`TauCeti.Toric.facetPolyhedron`)
involves two choices besides the polytope it describes: the order in which the facets are listed,
and the lattice of integral vectors the normals live in. Relabelling the facets keeps the polytope,
and an isomorphism of lattices transports it; neither changes whether the presentation is
Delzant.

**Facet permutations.** Listing the facets along a surjection `e : ι' → ι` gives the same
polyhedron (`TauCeti.Toric.facetPolyhedron_comp`), and the facets active at a point are the
preimages of the old ones (`TauCeti.Toric.activeSet_facetPairing_comp`). Along a bijection
`e : ι' ≃ ι` a smooth vertex stays a smooth vertex (`TauCeti.Toric.isSmoothVertex_comp_equiv_iff`)
and a Delzant presentation stays Delzant (`TauCeti.Toric.isDelzant_comp_equiv_iff`).

**Lattice maps.** Let `f : N → N'` and `g : V →L[ℝ] V'` satisfy `g (i n) = i' (f n)`. The map `g`
acts dually on points, sending `y ∈ V'*` to `y ∘ g ∈ V*`, and this preserves the pairings with the
normals: `y` pairs with `f (u j)` as `y ∘ g` pairs with `u j`. Hence a point `y` lies in the
polyhedron of `(f ∘ u, c)` exactly when `y ∘ g` lies in that of `(u, c)`
(`TauCeti.Toric.comp_mem_facetPolyhedron_iff`), with the same active facets
(`TauCeti.Toric.activeSet_facetPairing_comp_left`). When `f` is an isomorphism, smooth vertices
correspond (`TauCeti.Toric.isSmoothVertex_comp_iff`), since `f` carries lattice bases of `N` to
lattice bases of `N'`. When moreover `g` is an isomorphism, `y ↦ y ∘ g` is a linear isomorphism of
the dual spaces, so it matches the vertices
(`TauCeti.Toric.comp_mem_extremePoints_facetPolyhedron_iff`) and bounded polyhedra, and the Delzant
property transfers (`TauCeti.Toric.IsDelzant.map`, `TauCeti.Toric.isDelzant_congr`). This
is the action of integral basis changes, `GL(n, ℤ)`, on Delzant polytopes. Combined with the
translations of `TauCeti.Toric.isDelzant_add_iff` it gives invariance under integral affine
changes of coordinates.

## Main results

* `TauCeti.Toric.facetPolyhedron_comp`, `TauCeti.Toric.isDelzant_comp_equiv_iff`: relabelling
  the facets.
* `TauCeti.Toric.comp_mem_facetPolyhedron_iff`, `TauCeti.Toric.isSmoothVertex_comp_iff`,
  `TauCeti.Toric.isDelzant_congr`: transport along an isomorphism of lattices.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

open Set

namespace TauCeti.Toric

variable {ι ι' N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {u : ι → N} {c : ι → ℝ}

/-! ### Facet permutations -/

section Relabel

/-- Listing the facets along `e` composes the pairings with `e`. -/
theorem facetPairing_comp (e : ι' → ι) : facetPairing i (u ∘ e) = facetPairing i u ∘ e := by
  ext j x
  simp

/-- Listing the facets along `e` pulls the active facets back along `e`. -/
@[simp]
theorem activeSet_facetPairing_comp (e : ι' → ι) (x : StrongDual ℝ V) :
    activeSet (facetPairing i (u ∘ e)) (c ∘ e) x = e ⁻¹' activeSet (facetPairing i u) c x := by
  rw [facetPairing_comp, activeSet_comp]

/-- Listing the facets along a surjection `e` does not change the polyhedron. -/
theorem facetPolyhedron_comp {e : ι' → ι} (he : Function.Surjective e) :
    facetPolyhedron i (u ∘ e) (c ∘ e) = facetPolyhedron i u c := by
  ext x
  simp only [mem_facetPolyhedron, Function.comp_apply]
  exact ⟨fun h j ↦ by obtain ⟨j', rfl⟩ := he j; exact h j', fun h j' ↦ h (e j')⟩

/-- Relabelling the facets along a bijection preserves smooth vertices. -/
@[simp]
theorem isSmoothVertex_comp_equiv_iff (e : ι' ≃ ι) {x : StrongDual ℝ V} :
    IsSmoothVertex i (u ∘ e) (c ∘ e) x ↔ IsSmoothVertex i u c x := by
  -- `e` restricts to a bijection between the two sets of active facets.
  let σ : activeSet (facetPairing i (u ∘ e)) (c ∘ e) x ≃ activeSet (facetPairing i u) c x :=
    e.subtypeEquiv fun j ↦ by simp
  rw [isSmoothVertex_def, isSmoothVertex_def]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.reindex σ, fun j ↦ ?_⟩
    rw [Module.Basis.reindex_apply, hb]
    simp [σ]
  · rintro ⟨b, hb⟩
    exact ⟨b.reindex σ.symm, fun j ↦ by simp [σ, hb]⟩

/-- Relabelling the facets along a bijection preserves the Delzant property. -/
theorem IsDelzant.comp_equiv (hΔ : IsDelzant i u c) (e : ι' ≃ ι) :
    IsDelzant i (u ∘ e) (c ∘ e) := by
  have hP : facetPolyhedron i (u ∘ e) (c ∘ e) = facetPolyhedron i u c :=
    facetPolyhedron_comp e.surjective
  refine ⟨by rw [hP]; exact hΔ.isBounded, fun x hx ↦ ?_, fun j ↦ ?_⟩
  · rw [hP] at hx
    exact (isSmoothVertex_comp_equiv_iff e).2 (hΔ.isSmoothVertex x hx)
  obtain ⟨x, hx, hxj⟩ := hΔ.irredundant (e j)
  refine ⟨x, by rwa [hP], ?_⟩
  rw [activeSet_facetPairing_comp, hxj, ← image_singleton, e.preimage_image]

/-- Relabelling the facets along a bijection does not change whether the presentation is
Delzant. -/
@[simp]
theorem isDelzant_comp_equiv_iff (e : ι' ≃ ι) :
    IsDelzant i (u ∘ e) (c ∘ e) ↔ IsDelzant i u c :=
  ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

end Relabel

/-! ### Lattice maps -/

section LatticeMap

variable {f : N → N'} {g : V →L[ℝ] V'}

/-- A compatible pair of lattice and real-linear maps identifies the facets active at `y` for the
mapped normals with those active at `y ∘ g` for the original normals. -/
theorem activeSet_facetPairing_comp_left (hfg : ∀ n, g (i n) = i' (f n))
    (y : StrongDual ℝ V') :
    activeSet (facetPairing i' (f ∘ u)) c y = activeSet (facetPairing i u) c (y.comp g) := by
  ext j
  simp [hfg]

/-- A point `y` lies in the polyhedron of the mapped normals exactly when `y ∘ g` lies in the
polyhedron of the original normals. -/
theorem comp_mem_facetPolyhedron_iff (hfg : ∀ n, g (i n) = i' (f n)) {y : StrongDual ℝ V'} :
    y.comp g ∈ facetPolyhedron i u c ↔ y ∈ facetPolyhedron i' (f ∘ u) c := by
  simp [hfg]

/-- For a lattice isomorphism `f`, a point `y` is a smooth vertex for the mapped normals exactly
when `y ∘ g` is one for the original normals: `f` carries lattice bases to lattice bases. -/
theorem isSmoothVertex_comp_iff (f : N ≃+ N') (hfg : ∀ n, g (i n) = i' (f n))
    {y : StrongDual ℝ V'} :
    IsSmoothVertex i u c (y.comp g) ↔ IsSmoothVertex i' (f ∘ u) c y := by
  rw [isSmoothVertex_def, isSmoothVertex_def,
    activeSet_facetPairing_comp_left (f := ⇑f) hfg]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.map f.toIntLinearEquiv, fun j ↦ by simp [hb]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.map f.symm.toIntLinearEquiv, fun j ↦ by simp [hb]⟩

end LatticeMap

section LatticeEquiv

variable {f : N → N'} (g : V ≃L[ℝ] V')

/-- The dual of a real-linear isomorphism `g`, sending `y ∈ V'*` to `y ∘ g`, matches the vertices
of the polyhedron of the mapped normals with those of the original polyhedron. -/
theorem comp_mem_extremePoints_facetPolyhedron_iff (hfg : ∀ n, g (i n) = i' (f n))
    {y : StrongDual ℝ V'} :
    y.comp (g : V →L[ℝ] V') ∈ (facetPolyhedron i u c).extremePoints ℝ ↔
      y ∈ (facetPolyhedron i' (f ∘ u) c).extremePoints ℝ := by
  -- `Φ` is the dual isomorphism `y ↦ y ∘ g`; it maps the new polyhedron onto the old one.
  set Φ : StrongDual ℝ V' ≃L[ℝ] StrongDual ℝ V := g.symm.arrowCongr (.refl ℝ ℝ)
  have hΦ : ∀ y, Φ y = y.comp (g : V →L[ℝ] V') := fun y ↦ by ext; simp [Φ]
  have himage : Φ '' facetPolyhedron i' (f ∘ u) c = facetPolyhedron i u c := by
    ext x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    rw [Φ.injective.mem_set_image, hΦ, comp_mem_facetPolyhedron_iff (g := (g : V →L[ℝ] V')) hfg]
  rw [← hΦ, ← himage, ← image_extremePoints, Φ.injective.mem_set_image]

/-- **Delzant presentations under lattice isomorphisms.** For an isomorphism `f : N ≃+ N'` of
lattices and a compatible real-linear isomorphism `g : V ≃L[ℝ] V'`, the presentation `(f ∘ u, c)`
is Delzant when `(u, c)` is. -/
theorem IsDelzant.map (hΔ : IsDelzant i u c) (f : N ≃+ N') (hfg : ∀ n, g (i n) = i' (f n)) :
    IsDelzant i' (f ∘ u) c := by
  -- `Φ` is the dual isomorphism `y ↦ y ∘ g`, pulling the new polyhedron back to the old one.
  set Φ : StrongDual ℝ V' ≃L[ℝ] StrongDual ℝ V := g.symm.arrowCongr (.refl ℝ ℝ)
  have hΦ : ∀ y, Φ y = y.comp (g : V →L[ℝ] V') := fun y ↦ by ext; simp [Φ]
  have hpre : facetPolyhedron i' (f ∘ u) c = Φ ⁻¹' facetPolyhedron i u c := by
    ext y
    rw [mem_preimage, hΦ, comp_mem_facetPolyhedron_iff (f := ⇑f) hfg]
  refine ⟨?_, fun y hy ↦ ?_, fun j ↦ ?_⟩
  · rw [hpre, ← Φ.image_symm_eq_preimage]
    exact (Φ.symm : StrongDual ℝ V →L[ℝ] StrongDual ℝ V').lipschitzWith.isBounded_image
      hΔ.isBounded
  · rw [← isSmoothVertex_comp_iff (g := (g : V →L[ℝ] V')) f hfg]
    exact hΔ.isSmoothVertex _ ((comp_mem_extremePoints_facetPolyhedron_iff (f := ⇑f) g hfg).2 hy)
  · obtain ⟨x, hx, hxj⟩ := hΔ.irredundant j
    obtain ⟨y, rfl⟩ := Φ.surjective x
    refine ⟨y, by rwa [hpre], ?_⟩
    rw [activeSet_facetPairing_comp_left (f := ⇑f) (g := (g : V →L[ℝ] V')) hfg, ← hΦ, hxj]

/-- For an isomorphism `f : N ≃+ N'` of lattices and a compatible real-linear isomorphism
`g : V ≃L[ℝ] V'`, the presentation `(u, c)` is Delzant exactly when `(f ∘ u, c)` is. -/
theorem isDelzant_congr (f : N ≃+ N') (hfg : ∀ n, g (i n) = i' (f n)) :
    IsDelzant i u c ↔ IsDelzant i' (f ∘ u) c := by
  refine ⟨fun h ↦ h.map g f hfg, fun h ↦ ?_⟩
  have hfg' : ∀ n, g.symm (i' n) = i (f.symm n) := fun n ↦ by
    rw [g.symm_apply_eq, hfg, AddEquiv.apply_symm_apply]
  have := h.map g.symm f.symm hfg'
  rwa [← Function.comp_assoc, AddEquiv.symm_comp_self, Function.id_comp] at this

end LatticeEquiv

end TauCeti.Toric
