/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Geometry.Toric.Delzant.CornerChop
public import TauCeti.Geometry.Toric.Delzant.Simplex

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Lebesgue.SimplexVolume.Basic

/-!
# Lattice-normalized volumes of Delzant polytopes

Let `i : N →+ V` be an integral lattice. The moment polytope `Δ ⊆ V*` of a symplectic toric
manifold is measured with the Lebesgue measure on `V*` for which the dual lattice
`{x ∈ V* | ⟨x, n⟩ ∈ ℤ for every n ∈ N}` has covolume one; with this normalization the symplectic
volume of the toric manifold is `(2π)ⁿ vol(Δ)`. This file computes that measure in coordinates
and evaluates it on the simplex and on corner chops.

A basis `b` of the lattice `N` gives *lattice coordinates* `x ↦ (⟨x, b k⟩)_k` on `V*`
(`TauCeti.Toric.latticeCoord i b`), a linear isomorphism `V* ≃ ℝ^κ`
(`TauCeti.Toric.IsIntegralLattice.bijective_latticeCoord`) carrying the dual lattice onto `ℤ^κ`
(`TauCeti.Toric.forall_apply_mem_range_intCast_iff`). The normalized volume of a set `S ⊆ V*` is
the Lebesgue volume of its image in these coordinates. It does not depend on the basis: two bases
of `N` differ by an integral matrix with integral inverse, whose determinant is `±1`
(`TauCeti.Toric.volume_image_latticeCoord_congr`). In lattice coordinates a facet polyhedron is
the polyhedron cut out by the coordinates of the normals
(`TauCeti.Toric.IsIntegralLattice.image_latticeCoord_facetPolyhedron`).

* **The simplex.** The standard simplex of size `a ≥ 0` in `ℝ^κ`, the moment polytope of `ℂPⁿ`,
  has normalized volume `aⁿ / n!` for `n = #κ`
  (`TauCeti.Toric.volume_image_latticeCoord_facetPolyhedron_simplex`). For `n = 0` this is `1`,
  the volume of the one-point polytope.
* **Corner chops.** Chopping a smooth vertex `v` off a facet polyhedron at a small depth `ε > 0`
  removes exactly `εⁿ / n!` of normalized volume
  (`TauCeti.Toric.IsSmoothVertex.eventually_volume_image_latticeCoord_cornerChop`). In the
  coordinates `y j = ⟨x, u j⟩ - c j` given by the normals at `v`, which form a basis of `N`, the
  removed corner is the simplex `{y ≥ 0, ∑ j, y j < ε}`, once `ε` is too small for the facets not
  through `v` to meet it. On the symplectic side this is the volume `(2π)ⁿ εⁿ / n!` of the ball
  removed by the toric blowup at the fixed point over `v`.

## Main definitions

* `TauCeti.Toric.latticeCoord i b`: the coordinates `x ↦ (⟨x, b k⟩)_k` of `V*` in a lattice basis.

## Main results

* `TauCeti.Toric.volume_image_latticeCoord_congr`: the volume in lattice coordinates does not
  depend on the lattice basis.
* `TauCeti.Toric.IsIntegralLattice.image_latticeCoord_facetPolyhedron`: a facet polyhedron in
  lattice coordinates.
* `TauCeti.Toric.volume_image_latticeCoord_facetPolyhedron_simplex`: the simplex of size `a`
  has normalized volume `aⁿ / n!`.
* `TauCeti.Toric.IsSmoothVertex.eventually_volume_image_latticeCoord_cornerChop`: a small corner
  chop at depth `ε` removes normalized volume `εⁿ / n!`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28 and 30.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 2.
-/

public section

noncomputable section

open Set MeasureTheory Filter Topology

namespace TauCeti.Toric

variable {ι κ κ' N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-! ### Lattice coordinates -/

variable (i) in
/-- The *lattice coordinates* `x ↦ (⟨x, b k⟩)_k` of a point `x` of `V*` in a basis `b` of the
lattice `N`. -/
def latticeCoord (b : Module.Basis κ ℤ N) : StrongDual ℝ V →L[ℝ] κ → ℝ :=
  ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.apply ℝ ℝ (i (b k))

@[simp]
theorem latticeCoord_apply (b : Module.Basis κ ℤ N) (x : StrongDual ℝ V) (k : κ) :
    latticeCoord i b x k = x (i (b k)) :=
  (rfl)

/-- The value of a point of `V*` on a lattice vector `n` is the combination of its lattice
coordinates with the coordinates of `n`. -/
theorem apply_eq_sum_latticeCoord [Fintype κ] (b : Module.Basis κ ℤ N) (x : StrongDual ℝ V)
    (n : N) : x (i n) = ∑ k, (b.repr n k : ℝ) * latticeCoord i b x k := by
  conv_lhs => rw [← b.sum_repr n]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, latticeCoord_apply]

/-- **Change of lattice basis.** The lattice coordinates in a basis `b'` are obtained from those in
`b` by the transpose of the integral change-of-basis matrix. -/
theorem latticeCoord_eq_mulVec [Fintype κ] (b : Module.Basis κ ℤ N) (b' : Module.Basis κ' ℤ N)
    (x : StrongDual ℝ V) :
    latticeCoord i b' x =
      ((b.toMatrix b').transpose.map ((↑) : ℤ → ℝ)).mulVec (latticeCoord i b x) := by
  funext k'
  rw [latticeCoord_apply, apply_eq_sum_latticeCoord b x (b' k')]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
    Module.Basis.toMatrix_apply]

/-- **The dual lattice in lattice coordinates.** A point of `V*` takes integer values on the
lattice exactly when its lattice coordinates are integers. So the lattice coordinates carry the
dual lattice onto `ℤ^κ`, and Lebesgue measure in these coordinates gives it covolume one. -/
theorem forall_apply_mem_range_intCast_iff [Finite κ] (b : Module.Basis κ ℤ N)
    (x : StrongDual ℝ V) :
    (∀ n, x (i n) ∈ range ((↑) : ℤ → ℝ)) ↔ ∀ k, latticeCoord i b x k ∈ range ((↑) : ℤ → ℝ) := by
  have := Fintype.ofFinite κ
  refine ⟨fun h k ↦ h (b k), fun h n ↦ ?_⟩
  choose m hm using h
  exact ⟨∑ k, b.repr n k * m k, by simp [apply_eq_sum_latticeCoord b x n, hm]⟩

/-- For an integral lattice, the lattice coordinates in any basis are a linear isomorphism
`V* ≃ ℝ^κ`: the images `i (b k)` of a lattice basis form a real basis of `V`. -/
theorem IsIntegralLattice.bijective_latticeCoord [Finite κ] (hi : IsIntegralLattice i)
    (b : Module.Basis κ ℤ N) : Function.Bijective (latticeCoord i b) := by
  let B := hi.isBaseChange.basis b
  have hB (k : κ) : B k = i (b k) := by simpa using hi.isBaseChange.basis_apply b k
  refine ⟨fun x y hxy ↦ ContinuousLinearMap.coe_injective (B.ext fun k ↦ ?_), fun y ↦ ?_⟩
  · simpa [hB] using congrFun hxy k
  · have := Module.Finite.of_basis B
    refine ⟨LinearMap.toContinuousLinearMap (B.constr ℝ y), funext fun k ↦ ?_⟩
    simp [← hB, Module.Basis.constr_basis]

/-- **A facet polyhedron in lattice coordinates.** In the coordinates of a lattice basis `b`, the
polyhedron `{x | c j ≤ ⟨x, u j⟩}` is cut out by the coordinates of the normals `u j` in `b`. -/
theorem IsIntegralLattice.image_latticeCoord_facetPolyhedron [Fintype κ]
    (hi : IsIntegralLattice i) (b : Module.Basis κ ℤ N) (u : ι → N) (c : ι → ℝ) :
    latticeCoord i b '' facetPolyhedron i u c =
      {y | ∀ j, c j ≤ ∑ k, (b.repr (u j) k : ℝ) * y k} := by
  ext y
  obtain ⟨x, rfl⟩ := (hi.bijective_latticeCoord b).2 y
  rw [(hi.bijective_latticeCoord b).1.mem_set_image]
  simp only [mem_facetPolyhedron, mem_ofPred_eq]
  exact forall_congr' fun j ↦ by rw [apply_eq_sum_latticeCoord b x (u j)]

/-! ### Independence of the lattice basis -/

/-- The volume in lattice coordinates is the same for two bases indexed by the same type: the
change of coordinates is an integral matrix with integral inverse, of determinant `±1`. -/
private theorem volume_image_latticeCoord_congr_of_index [Fintype κ]
    (b b' : Module.Basis κ ℤ N) (s : Set (StrongDual ℝ V)) :
    volume (latticeCoord i b' '' s) = volume (latticeCoord i b '' s) := by
  classical
  set A := (b.toMatrix b').transpose.map ((↑) : ℤ → ℝ) with hA
  have himage : latticeCoord i b' '' s = Matrix.toLin' A '' (latticeCoord i b '' s) := by
    rw [image_image]
    exact image_congr fun x _ ↦ by rw [Matrix.toLin'_apply, latticeCoord_eq_mulVec b]
  -- The integral determinant is a unit of `ℤ`.
  have hunit : (b.toMatrix b').det * (b'.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hdet : |LinearMap.det (Matrix.toLin' A)| = 1 := by
    rw [LinearMap.det_toLin', hA, ← Matrix.det_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, ← Int.cast_det]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h <;> simp [h]
  rw [himage, Measure.addHaar_image_linearMap, hdet, ENNReal.ofReal_one, one_mul]

/-- **The volume in lattice coordinates does not depend on the lattice basis.** For any two bases
`b` and `b'` of the lattice `N`, the images of a set `s ⊆ V*` in the two lattice coordinate systems
have the same Lebesgue volume. -/
theorem volume_image_latticeCoord_congr [Fintype κ] [Fintype κ'] (b : Module.Basis κ ℤ N)
    (b' : Module.Basis κ' ℤ N) (s : Set (StrongDual ℝ V)) :
    volume (latticeCoord i b' '' s) = volume (latticeCoord i b '' s) := by
  classical
  -- Reindex `b'` by `κ`, which permutes the coordinates.
  let e : κ' ≃ κ := b'.indexEquiv b
  let F := MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℝ)
  have hF (y : κ → ℝ) (k' : κ') : F y k' = y (e k') := by
    simp [F, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  have himage : latticeCoord i b' '' s = F '' (latticeCoord i (b'.reindex e) '' s) := by
    rw [image_image]
    exact image_congr fun x _ ↦ funext fun k' ↦ by simp [hF]
  have hp := volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  rw [himage, MeasurableEquiv.image_eq_preimage_symm, hp.symm.measure_preimage_equiv,
    volume_image_latticeCoord_congr_of_index b]

/-! ### The simplex -/

/-- **The volume of the simplex.** For `a ≥ 0`, the standard simplex
`{x | 0 ≤ ⟨x, e k⟩, ∑ k, ⟨x, e k⟩ ≤ a}` of size `a` in `(ℝ^κ)*`, the moment polytope of `ℂPⁿ` for
`n = #κ`, has lattice-normalized volume `aⁿ / n!`: its image in the coordinates of any basis of
`ℤ^κ` has this Lebesgue volume. -/
theorem volume_image_latticeCoord_facetPolyhedron_simplex [Fintype κ] [DecidableEq κ]
    [Fintype κ'] (b : Module.Basis κ' ℤ (κ → ℤ)) {a : ℝ} (ha : 0 ≤ a) :
    volume (latticeCoord ((Int.castAddHom ℝ).compLeft κ) b ''
      facetPolyhedron ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a)) =
        ENNReal.ofReal (a ^ Fintype.card κ / (Fintype.card κ).factorial) := by
  have hi : IsIntegralLattice ((Int.castAddHom ℝ).compLeft κ) :=
    isIntegralLattice_of_basis (Pi.basisFun ℤ κ) (Pi.basisFun ℝ κ) fun j ↦ by
      ext k
      simp [Pi.basisFun_apply, Pi.single_apply, apply_ite]
  rw [volume_image_latticeCoord_congr (Pi.basisFun ℤ κ) b,
    hi.image_latticeCoord_facetPolyhedron, ← volume_setOf_nonneg_sum_le κ ha]
  congr 1
  ext y
  simp [Option.forall, Pi.single_apply, and_comm]

/-! ### Corner chops -/

/-- **A small corner chop removes the volume of a small simplex.** Let `v` be a smooth vertex of
the facet polyhedron `Δ` of an integral lattice of rank `n`, at which the facets indexed by `s`
meet. For every sufficiently small `ε > 0`, chopping the corner `v` off `Δ` at depth `ε` removes
lattice-normalized volume `εⁿ / n!`: in the coordinates of any lattice basis `b`,
`vol(Δ) = vol(Δ_ε) + εⁿ / n!`. -/
theorem IsSmoothVertex.eventually_volume_image_latticeCoord_cornerChop [Finite ι] [Fintype κ]
    {u : ι → N} {c : ι → ℝ} {s : Finset ι} {v : StrongDual ℝ V}
    (hi : IsIntegralLattice i) (hvΔ : v ∈ facetPolyhedron i u c) (hv : IsSmoothVertex i u c v)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) (b : Module.Basis κ ℤ N) :
    ∀ᶠ ε in 𝓝[>] 0, volume (latticeCoord i b '' facetPolyhedron i u c) =
      volume (latticeCoord i b ''
        facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)) +
        ENNReal.ofReal (ε ^ Fintype.card κ / (Fintype.card κ).factorial) := by
  classical
  obtain ⟨w, -, hx⟩ := hv.exists_coord hi hs
  have hsA (j) : j ∈ s ↔ v (i (u j)) = c j := by
    rw [← Finset.mem_coe, hs, mem_activeSet, facetPairing_apply]
  -- The constraints inactive at the corner have positive slack there.
  have hslack (k) (hk : k ∉ s) : 0 < v (i (u k)) - c k :=
    sub_pos.2 ((mem_facetPolyhedron.1 hvΔ k).lt_of_ne fun h ↦ hk ((hsA k).2 h.symm))
  filter_upwards [self_mem_nhdsWithin, eventually_forall_notMem_mul_sum_abs_lt w hslack]
    with ε (hε0 : 0 < ε) hε
  -- The vertex basis `u j`, `j ∈ s`, of the lattice.
  obtain ⟨b₀, hb₀⟩ := isSmoothVertex_def.1 hv
  let bv : Module.Basis s ℤ N := b₀.reindex (Equiv.subtypeEquivRight fun j ↦ by
    rw [← hs, Finset.mem_coe])
  have hbv (j : s) : bv j = u j := by simp [bv, hb₀]
  -- The corner removed by the chop: the points with nonnegative coordinates `⟨x, u j⟩ - c j`,
  -- `j ∈ s`, of sum less than `ε`. The facets not through `v` do not meet it.
  set C := {x : StrongDual ℝ V | (∀ j ∈ s, c j ≤ x (i (u j))) ∧ ∑ j ∈ s, (x (i (u j)) - c j) < ε}
  have hsplit : facetPolyhedron i u c =
      facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε) ∪ C := by
    refine Subset.antisymm (fun x hxΔ ↦ ?_) (union_subset facetPolyhedron_cornerChop_subset ?_)
    · by_cases hxε : ε ≤ ∑ j ∈ s, (x (i (u j)) - c j)
      · exact Or.inl (mem_facetPolyhedron_cornerChop_iff.2 ⟨hxΔ, hxε⟩)
      · exact Or.inr ⟨fun j _ ↦ mem_facetPolyhedron.1 hxΔ j, not_le.1 hxε⟩
    · rintro x ⟨hxs, hxε⟩
      refine mem_facetPolyhedron.2 fun k ↦ ?_
      by_cases hk : k ∈ s
      · exact hxs k hk
      · exact (lt_apply_of_sum_le hx hε hxs hxε.le hk).le
  have hdisj : Disjoint (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)) C :=
    disjoint_left.2 fun x hx' hxC ↦
      (mem_facetPolyhedron_cornerChop_iff.1 hx').2.not_gt hxC.2
  -- The chopped polyhedron is measurable in lattice coordinates.
  have hmeas : MeasurableSet
      (latticeCoord i b '' facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)) := by
    rw [hi.image_latticeCoord_facetPolyhedron, ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ measurableSet_le measurable_const (by fun_prop)
  -- In the coordinates of the vertex basis, the corner is a translate of the simplex
  -- `{y ≥ 0, ∑ j, y j < ε}`.
  have hcorner : latticeCoord i bv '' C =
      (· + -fun j : s ↦ c j) ⁻¹' {y : s → ℝ | (∀ j, 0 ≤ y j) ∧ ∑ j, y j < ε} := by
    ext y
    obtain ⟨x, rfl⟩ := (hi.bijective_latticeCoord bv).2 y
    rw [(hi.bijective_latticeCoord bv).1.mem_set_image]
    simp only [C, mem_preimage, mem_ofPred_eq, ← sub_eq_add_neg, Pi.sub_apply, latticeCoord_apply,
      hbv, sub_nonneg, Subtype.forall]
    rw [Finset.sum_coe_sort s fun j ↦ x (i (u j)) - c j]
  have hcard : Fintype.card s = Fintype.card κ := Fintype.card_congr (bv.indexEquiv b)
  rw [hsplit, image_union,
    measure_union' ((disjoint_image_iff (hi.bijective_latticeCoord b).1).2 hdisj) hmeas,
    volume_image_latticeCoord_congr bv b C, hcorner, measure_preimage_add_right,
    volume_setOf_nonneg_sum_lt s hε0, hcard]

end TauCeti.Toric
