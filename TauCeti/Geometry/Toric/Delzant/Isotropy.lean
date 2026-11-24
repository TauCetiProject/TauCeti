/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Geometry.Toric.Delzant.Free

import TauCeti.Algebra.AddCircle

/-!
# Isotropy groups of labelled Delzant presentations

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`, and attach a positive integer label `m j` to each
facet. In the sense of Lerman and Tolman, the labelled polytope `(Δ, m)` describes the toric
orbifold obtained from Delzant's construction for the labelled normals `m j • u j` and support
constants `m j * c j`: the quotient of the zero level `Z_m ⊆ ℂ^ι`
(`TauCeti.Toric.delzantLevel`) by the kernel torus `N_m ⊆ (ℝ / 2πℤ)^ι` of
`TauCeti.Toric.facetTorusHom`. In this construction the local group at the orbit of `x ∈ Z_m` is
the isotropy group of `N_m` at `x`, the subgroup `N_m ⊓ Stab(x)` of `(ℝ / 2πℤ)^ι`. The labelled
presentation describes the same polytope with the same active facets
(`TauCeti.Toric.facetPolyhedron_nsmul`, `TauCeti.Toric.activeSet_nsmul`), and this file computes
these isotropy groups when the normals active at the image of `x` are part of a lattice basis, as
they are at every point of a Delzant polytope.

Let `x` lie over `y ∈ Δ` and let `A` be the set of facets active at `y`.

* **The isotropy group.** An angle `θ` lies in `N_m` and fixes `x` exactly when `θ j = 0` off
  `A` and `m j • θ j = 0` on `A`
  (`TauCeti.Toric.mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff`). So the isotropy group is the
  product over the active facets of the cyclic groups of order `m j`: restriction to `A` is an
  isomorphism onto `∏_(j ∈ A) (ℝ / 2πℤ)[m j]` (`TauCeti.Toric.labelledIsotropyAddEquiv`), and the
  isotropy group has `∏_(j ∈ A) m j` elements
  (`TauCeti.Toric.natCard_ker_facetTorusHom_nsmul_inf_stabilizer`).
* **Interior, facets and vertices.** Over the interior of `Δ` the product is empty and the
  isotropy group is trivial. Over a point lying on the single facet `j` it is cyclic of order
  `m j`
  (`TauCeti.Toric.isAddCyclic_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton`,
  `TauCeti.Toric.natCard_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton`), and
  over a vertex its order is the product of the labels of the facets meeting there.
* **The labels are the facet isotropy orders.** Every facet `j` of a Delzant polytope contains a
  point lying on no other facet, and the label `m j` is the order of the isotropy group at a point
  of the level over it
  (`TauCeti.Toric.IsDelzant.exists_natCard_ker_facetTorusHom_nsmul_inf_stabilizer_eq`). So each
  label can be read off from the isotropy groups over its own facet. This refines
  `TauCeti.Toric.IsDelzant.forall_eq_zero_of_vadd_eq_self_nsmul_iff`, which says only that these
  isotropy groups are all trivial exactly for unit labels.

## Main results

* `TauCeti.Toric.mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff`: the isotropy group of the
  labelled kernel torus.
* `TauCeti.Toric.labelledIsotropyAddEquiv`: its isomorphism with `∏_(j ∈ A) (ℝ / 2πℤ)[m j]`.
* `TauCeti.Toric.natCard_ker_facetTorusHom_nsmul_inf_stabilizer`: its order `∏_(j ∈ A) m j`.
* `TauCeti.Toric.IsDelzant.exists_natCard_ker_facetTorusHom_nsmul_inf_stabilizer_eq`: each label
  is the order of an isotropy group over a point lying on its facet alone.

## References

* E. Lerman, S. Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric varieties*,
  Trans. Amer. Math. Soc. 349 (1997), 4201–4230, Sections 5 and 8.
* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
-/

public section

noncomputable section

open Set Real AddSubgroup

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} {m : ι → ℕ}
  {x : delzantLevel i (fun j ↦ m j • u j) (fun j ↦ m j * c j)} {y : StrongDual ℝ V}

/-! ### The isotropy group over a point -/

/-- **Isotropy of a labelled kernel torus.** Let `x` be a point of the level of the labelled
normals `m j • u j`, with moment value over `y`, and suppose that the normals of the facets active
at `y` are part of a lattice basis. An angle `θ` lies in the labelled kernel torus and fixes `x`
exactly when `θ j = 0` for every facet `j` not active at `y` and `m j • θ j = 0` for every facet
`j` active at `y`. -/
theorem mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff (hi : IsIntegralLattice i)
    (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) {θ : ι → AddCircle (2 * π)} :
    θ ∈ (facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
        AddAction.stabilizer (ι → AddCircle (2 * π)) x ↔
      (∀ j ∉ activeSet (facetPairing i u) c y, θ j = 0) ∧
        ∀ j ∈ activeSet (facetPairing i u) c y, m j • θ j = 0 := by
  rw [mem_inf, AddAction.mem_stabilizer_iff, vadd_eq_self_iff_of_forall_eq hy, activeSet_nsmul hm]
  refine and_comm.trans (and_congr_right fun h0 ↦ ?_)
  rw [mem_ker_facetTorusHom_nsmul_iff hi hs m fun j hj ↦ h0 j fun h ↦ hj (hys h)]
  refine ⟨fun h j _ ↦ h j, fun h j ↦ ?_⟩
  by_cases hj : j ∈ activeSet (facetPairing i u) c y
  · exact h j hj
  · rw [h0 j hj, smul_zero]

open Classical in
/-- **The isotropy group of a labelled kernel torus is a product of cyclic groups.** Let `x` be a
point of the level of the labelled normals `m j • u j`, with moment value over `y`, and suppose
that the normals of the facets active at `y` are part of a lattice basis. Restricting angles to
the facets active at `y` identifies the isotropy group of the labelled kernel torus at `x` with
the product over these facets `j` of the `m j`-torsion of the circle `ℝ / 2πℤ`. -/
def labelledIsotropyAddEquiv (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) :
    ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
        AddAction.stabilizer (ι → AddCircle (2 * π)) x : AddSubgroup (ι → AddCircle (2 * π))) ≃+
      ∀ j : activeSet (facetPairing i u) c y, (AddCircle (2 * π))[(m j : ℤ)] where
  toFun θ j := ⟨(θ : ι → AddCircle (2 * π)) j, torsionBy.nsmul_iff.2
    (((mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff hi hm hy hys hs).1 θ.property).2 j
      j.property)⟩
  invFun φ := ⟨fun j ↦ if h : j ∈ activeSet (facetPairing i u) c y then φ ⟨j, h⟩ else 0,
    (mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff hi hm hy hys hs).2
      ⟨fun j hj ↦ dite_eq_right hj, fun j hj ↦ by
        rw [dite_eq_left hj]
        exact torsionBy.nsmul_iff.1 (φ ⟨j, hj⟩).property⟩⟩
  left_inv θ := Subtype.ext <| funext fun j ↦ by
    by_cases hj : j ∈ activeSet (facetPairing i u) c y
    · simp [hj]
    · simp only [hj, dite_false]
      exact (((mem_ker_facetTorusHom_nsmul_inf_stabilizer_iff hi hm hy hys hs).1
        θ.property).1 j hj).symm
  right_inv φ := funext fun j ↦ Subtype.ext (by simp [j.property])
  map_add' _ _ := (rfl)

/-- The isomorphism `TauCeti.Toric.labelledIsotropyAddEquiv` restricts angles to the facets active
over `x`. -/
@[simp]
theorem coe_labelledIsotropyAddEquiv_apply (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j)
    (θ : ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
      AddAction.stabilizer (ι → AddCircle (2 * π)) x : AddSubgroup (ι → AddCircle (2 * π))))
    (j : activeSet (facetPairing i u) c y) :
    (labelledIsotropyAddEquiv hi hm hy hys hs θ j : AddCircle (2 * π)) =
      (θ : ι → AddCircle (2 * π)) j :=
  (rfl)

/-- The inverse of `TauCeti.Toric.labelledIsotropyAddEquiv` extends angles on the facets active
over `x` by zero. -/
theorem coe_labelledIsotropyAddEquiv_symm_apply_of_mem (hi : IsIntegralLattice i)
    (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j)
    (φ : ∀ j : activeSet (facetPairing i u) c y, (AddCircle (2 * π))[(m j : ℤ)]) {j : ι}
    (hj : j ∈ activeSet (facetPairing i u) c y) :
    ((labelledIsotropyAddEquiv hi hm hy hys hs).symm φ : ι → AddCircle (2 * π)) j = φ ⟨j, hj⟩ :=
  dite_eq_left hj

/-- The inverse of `TauCeti.Toric.labelledIsotropyAddEquiv` vanishes on the facets not active over
`x`. -/
theorem coe_labelledIsotropyAddEquiv_symm_apply_of_notMem (hi : IsIntegralLattice i)
    (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j)
    (φ : ∀ j : activeSet (facetPairing i u) c y, (AddCircle (2 * π))[(m j : ℤ)]) {j : ι}
    (hj : j ∉ activeSet (facetPairing i u) c y) :
    ((labelledIsotropyAddEquiv hi hm hy hys hs).symm φ : ι → AddCircle (2 * π)) j = 0 :=
  dite_eq_right hj

/-- **The order of the isotropy group of a labelled kernel torus.** Let `x` be a point of the level
of the labelled normals `m j • u j`, with moment value over `y`, and suppose that the normals of
the facets active at `y` are part of a lattice basis. The isotropy group of the labelled kernel
torus at `x` has `∏ m j` elements, the product over the facets `j` active at `y`. -/
theorem natCard_ker_facetTorusHom_nsmul_inf_stabilizer (hi : IsIntegralLattice i)
    (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) :
    Nat.card ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
        AddAction.stabilizer (ι → AddCircle (2 * π)) x : AddSubgroup (ι → AddCircle (2 * π))) =
      ∏ᶠ j ∈ activeSet (facetPairing i u) c y, m j := by
  classical
  have : NeZero (2 * π) := ⟨two_pi_pos.ne'⟩
  rw [Nat.card_congr (labelledIsotropyAddEquiv hi hm hy hys hs).toEquiv, Nat.card_pi,
    ← finprod_subtype_eq_finprod_cond, finprod_eq_prod_of_fintype]
  exact Finset.prod_congr rfl fun j _ ↦ AddCircle.natCard_torsionBy _

/-! ### Facets and labels -/

/-- **Over a facet the isotropy group has the order of its label.** If `x` lies over a point `y`
lying on the single facet `j`, and the normal `u j` is part of a lattice basis, the isotropy group
of `x` in the labelled kernel torus has `m j` elements. -/
theorem natCard_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton
    (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) {j : ι}
    (hA : activeSet (facetPairing i u) c y = {j}) :
    Nat.card ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
        AddAction.stabilizer (ι → AddCircle (2 * π)) x : AddSubgroup (ι → AddCircle (2 * π))) =
      m j := by
  rw [natCard_ker_facetTorusHom_nsmul_inf_stabilizer hi hm hy hys hs, hA, finprod_mem_singleton]

/-- **Over a facet the isotropy group is cyclic.** If `x` lies over a point `y` lying on the
single facet `j`, and the normal `u j` is part of a lattice basis, the isotropy group of `x` in
the labelled kernel torus is cyclic, of order `m j` by
`TauCeti.Toric.natCard_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton`. -/
theorem isAddCyclic_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton
    (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0)
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + m j * c j = y (i (m j • u j)))
    {s : Set ι} (hys : activeSet (facetPairing i u) c y ⊆ s)
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) {j : ι}
    (hA : activeSet (facetPairing i u) c y = {j}) :
    IsAddCyclic ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
        AddAction.stabilizer (ι → AddCircle (2 * π)) x : AddSubgroup (ι → AddCircle (2 * π))) := by
  have : Unique (activeSet (facetPairing i u) c y) := hA ▸ Set.uniqueSingleton j
  have := AddCircle.isAddCyclic_torsionBy (2 * π)
    (Nat.cast_ne_zero.2 (hm (default : activeSet (facetPairing i u) c y)))
  let e := (labelledIsotropyAddEquiv hi hm hy hys hs).trans (AddEquiv.piUnique fun j :
    activeSet (facetPairing i u) c y ↦ (AddCircle (2 * π))[(m j : ℤ)])
  exact isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective

/-- **The labels of a Delzant polytope are the facet isotropy orders.** For a Delzant polytope
with positive labels `m`, every facet `j` contains a point `y` lying on no other facet, and over
`y` there is a point `x` of the level of the labelled normals whose isotropy group in the labelled
kernel torus has exactly `m j` elements. -/
theorem IsDelzant.exists_natCard_ker_facetTorusHom_nsmul_inf_stabilizer_eq
    (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0) (j : ι) :
    ∃ x : delzantLevel i (fun j ↦ m j • u j) (fun j ↦ m j * c j), ∃ y : StrongDual ℝ V,
      (∀ k, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 k ^ 2 +
        (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 k ^ 2) / 2 + m k * c k =
          y (i (m k • u k))) ∧
      activeSet (facetPairing i u) c y = {j} ∧
      Nat.card ((facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker ⊓
          AddAction.stabilizer (ι → AddCircle (2 * π)) x :
        AddSubgroup (ι → AddCircle (2 * π))) = m j := by
  have := hi.finiteDimensional
  obtain ⟨y, hyΔ, hA⟩ := hΔ.irredundant j
  -- The labelled presentation describes the same polytope, so some point of its level lies over
  -- `y`.
  obtain ⟨x, hx, hxy⟩ : y ∈ {y : StrongDual ℝ V | ∃ x ∈ delzantLevel i (fun j ↦ m j • u j)
      (fun j ↦ m j * c j), ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + m j * c j = y (i (m j • u j))} := by
    rwa [setOf_exists_mem_delzantLevel, facetPolyhedron_nsmul hm]
  obtain ⟨v, hv, hyv⟩ := hΔ.exists_isSmoothVertex_activeSet_subset hyΔ
  exact ⟨⟨x, hx⟩, y, hxy, hA,
    natCard_ker_facetTorusHom_nsmul_inf_stabilizer_of_activeSet_eq_singleton (x := ⟨x, hx⟩) hi hm
      hxy hyv (isSmoothVertex_def.1 hv) hA⟩

end TauCeti.Toric
