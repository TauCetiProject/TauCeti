/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Level

/-!
# Orbits and stabilizers of the residual torus on the Delzant level

Let `i : N →+ V` be an integral lattice and `(u, c)` a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`. Delzant's construction reduces `ℂ^ι` by the kernel
torus `N_Δ` of the homomorphism `π : (ℝ / 2πℤ)^ι → V / 2π i(N)`
(`TauCeti.Toric.facetTorusHom`), acting by `z_j ↦ exp(-i θ_j) z_j`, at the zero level `Z` of its
moment map (`TauCeti.Toric.delzantLevel`). The *residual torus* `V / 2π i(N)`, the image of `π`,
then acts on `Z / N_Δ`: the class `π [θ]` sends the `N_Δ`-orbit of `x` to that of the rotation of
`x` by `-θ`. This file describes the orbits and the stabilizers of this action in terms of the
faces of `Δ`, without constructing the quotient `Z / N_Δ` itself.

For a set `s` of facets, the *face subtorus* `TauCeti.Toric.faceSubtorus i u p s` is the image
in `V / p i(N)` of the real span of the normals `i (u j)`, `j ∈ s`; equivalently, it is the image
under `π` of the coordinate subtorus of the angles supported on `s`
(`TauCeti.Toric.mem_faceSubtorus_iff_exists_facetTorusHom_eq`). The face subtori and their basic
properties are in `TauCeti.Geometry.Toric.Delzant.Torus`.

* **Stabilizers.** Rotating `x` by `-θ` lands in the `N_Δ`-orbit of `x` exactly when `π [θ]`
  lies in the face subtorus of the facets `j` with `z_j = 0`
  (`TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus`). This needs no
  hypothesis on `x` or on the presentation. For a point of the level with moment value `y ∈ Δ`
  these are the facets active at `y`, so the residual stabilizer of a point over `y` is the
  face subtorus of the face of `Δ` containing `y` in its relative interior.
* **Free over the interior, fixed over the vertices.** The face subtorus is trivial exactly when
  the normals are zero, and is everything exactly when the normals span `V`
  (`TauCeti.Toric.faceSubtorus_eq_bot_iff`, `TauCeti.Toric.faceSubtorus_eq_top_iff`). Both use
  that the lattice is countable while every nonzero real line is not. Hence, when the normals
  are nonzero, the residual torus acts freely on the orbit over `y` exactly when `y` lies on no
  facet; when the normals span `V`, it fixes that orbit exactly when `y` is a vertex of `Δ`.
* **Fibres.** The points of `ℂ^ι` with moment value `y` form a single orbit of `(ℝ / 2πℤ)^ι`
  (`TauCeti.Toric.setOf_forall_eq_eq_range_weightRotation_neg`), so the fibre of the residual
  moment map over each `y ∈ Δ` is a single orbit of the residual torus.
* **Effectiveness.** A Delzant polytope has a point lying on no facet
  (`TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`), so some point of the level has trivial
  residual stabilizer and the residual torus acts effectively.

## Main results

* `TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus`,
  `TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet`: the
  residual stabilizer is the face subtorus of the active facets.
* `TauCeti.Toric.forall_exists_weightRotation_neg_apply_eq_iff_eq_zero_iff_activeSet_eq_empty`: the
  residual torus acts freely exactly over the points of `Δ` lying on no facet.
* `TauCeti.Toric.forall_exists_weightRotation_neg_apply_eq_iff_mem_extremePoints`: the residual
  torus fixes the orbit over `y` exactly when `y` is a vertex of `Δ`.
* `TauCeti.Toric.setOf_forall_eq_eq_range_weightRotation_neg`: the moment fibres are single
  torus orbits.
* `TauCeti.Toric.IsDelzant.exists_mem_delzantLevel_forall_exists_weightRotation_neg_apply_eq_iff`:
  some point of the level has trivial residual stabilizer.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28 and 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real Filter Topology

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {u : ι → N}

/-! ### Stabilizers of the residual torus -/

/-- **The residual stabilizer.** The rotation of `x` by `-θ` lies in the orbit of `x` under the
kernel torus `N_Δ` of `facetTorusHom` exactly when the class of `θ` in the residual torus
`V / 2π i(N)` lies in the face subtorus of the facets `j` with `z_j = 0`. -/
theorem exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ι → ℝ) :
    (∃ t : ι → ℝ, (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
        weightRotation (-θ) x = weightRotation (-t) x) ↔
      facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) ∈
        faceSubtorus i u (2 * π) {j | x.1 j = 0 ∧ x.2 j = 0} := by
  classical
  have hsub (a b : ι → ℝ) : facetTorusHom i u (2 * π) (fun j ↦ ((a j - b j : ℝ) : AddCircle _)) =
      facetTorusHom i u (2 * π) (fun j ↦ (a j : AddCircle _)) -
        facetTorusHom i u (2 * π) (fun j ↦ (b j : AddCircle _)) := by
    rw [← map_sub]
    exact congrArg _ (funext fun j ↦ by simp only [Pi.sub_apply, AddCircle.coe_sub])
  simp_rw [weightRotation_neg_apply_eq_iff, mem_faceSubtorus_iff_exists_facetTorusHom_eq,
    AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨t, ht, h⟩
    -- Keep the coordinates of `θ - t` along the vanishing coordinates of `x`.
    refine ⟨fun j ↦ if x.1 j = 0 ∧ x.2 j = 0 then θ j - t j else 0,
      fun j hj ↦ ite_eq_right hj, ?_⟩
    rw [← sub_zero (facetTorusHom i u (2 * π) fun j ↦ (θ j : AddCircle (2 * π))), ← ht, ← hsub]
    congr 1
    funext j
    dsimp only
    split_ifs with hj
    · rfl
    · rw [AddCircle.coe_zero]
      exact (h j (not_and_or.1 hj)).symm
  · rintro ⟨s, hs, hsθ⟩
    refine ⟨θ - s, ?_, fun j hj ↦ ?_⟩
    · simp only [Pi.sub_apply, hsub, hsθ, sub_self]
    · simp [hs j (not_and_or.2 hj)]

section Level

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V} {c : ι → ℝ}
  {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {y : StrongDual ℝ V}

/-- **The residual stabilizer over a point of `Δ`.** If `μ(x) = β_ℝ^* y`, the rotation of `x` by
`-θ` lies in the orbit of `x` under the kernel torus exactly when the class of `θ` in the residual
torus lies in the face subtorus of the facets active at `y`. -/
theorem exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) (θ : ι → ℝ) :
    (∃ t : ι → ℝ, (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
        weightRotation (-θ) x = weightRotation (-t) x) ↔
      facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) ∈
        faceSubtorus i u (2 * π) (activeSet (facetPairing i u) c y) := by
  rw [activeSet_eq_of_forall_eq hy]
  exact exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus x θ

/-- **The residual torus acts freely exactly over the facet-free points.** Suppose that the
normals are nonzero. If `μ(x) = β_ℝ^* y`, the only element of the residual torus moving `x` within
its orbit under the kernel torus is `0` exactly when `y` lies on no facet of `Δ`. -/
theorem forall_exists_weightRotation_neg_apply_eq_iff_eq_zero_iff_activeSet_eq_empty
    (hi : IsIntegralLattice i) (hu₀ : ∀ j, u j ≠ 0)
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    (∀ θ : ι → ℝ, (∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
        facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) = 0) ↔
      activeSet (facetPairing i u) c y = ∅ := by
  have := hi.finite
  have := Countable.of_moduleFinite (R := ℤ) (M := N)
  simp_rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hy]
  -- Both sides say that the face subtorus of the active facets is trivial.
  trans faceSubtorus i u (2 * π) (activeSet (facetPairing i u) c y) = ⊥
  · refine ⟨fun h ↦ eq_bot_iff.2 fun q hq ↦ ?_, fun h θ ↦ by rw [h, AddSubgroup.mem_bot]⟩
    obtain ⟨θ, -, rfl⟩ := mem_faceSubtorus_iff_exists_facetTorusHom_eq.1 hq
    exact (h θ).1 hq
  · rw [faceSubtorus_eq_bot_iff, eq_empty_iff_forall_notMem]
    exact forall₂_congr fun j _ ↦ by simpa using hu₀ j ∘ (map_eq_zero_iff i hi.injective).1

/-- **The residual torus fixes exactly the orbits over the vertices.** Suppose that the normals
span `V`. If `μ(x) = β_ℝ^* y`, every element of the residual torus moves `x`
within its orbit under the kernel torus exactly when `y` is a vertex of `Δ`. -/
theorem forall_exists_weightRotation_neg_apply_eq_iff_mem_extremePoints
    (hi : IsIntegralLattice i) (hu : Submodule.span ℝ (Set.range fun j ↦ i (u j)) = ⊤)
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    (∀ θ : ι → ℝ, ∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
      y ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  have := hi.finite
  have := Countable.of_moduleFinite (R := ℤ) (M := N)
  have := hi.finiteDimensional
  simp_rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hy]
  rw [mem_extremePoints_facetPolyhedron_iff_span_eq_top, ← faceSubtorus_eq_top_iff (p := 2 * π),
    and_iff_right (mem_facetPolyhedron_of_forall_eq c hy), eq_top_iff]
  refine ⟨fun h q _ ↦ ?_, fun h θ ↦ h (AddSubgroup.mem_top _)⟩
  obtain ⟨θ, rfl⟩ := exists_facetTorusHom_eq hu q
  exact h θ

/-- **Moment fibres are torus orbits.** If `μ(x) = β_ℝ^* y`, the points `x'` of `ℂ^ι` with
`μ(x') = β_ℝ^* y` are exactly the rotations of `x` by the torus `(ℝ / 2πℤ)^ι`. In particular they
lie on the level, and they form a single orbit of the residual torus modulo the kernel torus. -/
theorem setOf_forall_eq_eq_range_weightRotation_neg
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    {x' : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι |
        ∀ j, (x'.1 j ^ 2 + x'.2 j ^ 2) / 2 + c j = y (i (u j))} =
      range fun θ : ι → ℝ ↦ weightRotation (-θ) x := by
  ext x'
  have hneg : (∃ θ : ι → ℝ, weightRotation (-θ) x = x') ↔ ∃ θ, weightRotation θ x = x' :=
    ⟨fun ⟨θ, h⟩ ↦ ⟨-θ, h⟩, fun ⟨θ, h⟩ ↦ ⟨-θ, by rwa [neg_neg]⟩⟩
  rw [mem_ofPred_eq, mem_range, hneg, exists_weightRotation_apply_eq_iff]
  exact forall_congr' fun j ↦ ⟨fun h ↦ by linarith [hy j], fun h ↦ by linarith [hy j]⟩

end Level

/-! ### Delzant polytopes -/

namespace IsDelzant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {c : ι → ℝ} (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **The residual torus acts effectively.** Some point of the level of a Delzant polytope has
trivial residual stabilizer: the only element of the residual torus moving it within its orbit
under the kernel torus is `0`. -/
theorem exists_mem_delzantLevel_forall_exists_weightRotation_neg_apply_eq_iff :
    ∃ x ∈ delzantLevel i u c, ∀ θ : ι → ℝ, (∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
        facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) = 0 := by
  have := hi.finiteDimensional
  obtain ⟨y, hy, hA⟩ := hΔ.exists_activeSet_eq_empty hi.injective
  rw [← setOf_exists_mem_delzantLevel i u c] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨x, hx, fun θ ↦ ?_⟩
  rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hxy, hA,
    faceSubtorus_empty, AddSubgroup.mem_bot]

end IsDelzant

end TauCeti.Toric
