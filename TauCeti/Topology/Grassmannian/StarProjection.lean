/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# The Grassmannian of a Euclidean space in projection form

For a real inner product space `E` and `k : ℕ`, `Euclidean.grassmannian E k` is the set of
continuous linear maps `P : E → E` that are self-adjoint idempotents (`IsStarProjection`)
whose range has rank `k` (`Module.rank`, so the range is finite-dimensional), with the topology
and the operator-norm metric of `E →L[ℝ] E`. Each `k`-plane of `E` is recorded by its orthogonal
projection: when `E` is finite-dimensional, `S ↦ S.starProjection` is a bijection from the
`k`-dimensional subspaces of `E` onto `Euclidean.grassmannian E k`, with inverse `P ↦ P.range`
(`Euclidean.grassmannian.submoduleEquiv`), by Mathlib's
`isStarProjection_iff_eq_starProjection_range`.

For a surjective linear isometry `e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)`, sending a point `S` of
Tau Ceti's finite Grassmannian `TauCeti.finiteGrassmannian ℝ k N` to `e⁻¹ P_S e`, where `P_S` is
the orthogonal projection onto `S.toEuclidean`, is a homeomorphism onto
`Euclidean.grassmannian E k` (`Euclidean.grassmannian.finiteGrassmannianHomeomorph`). It is a
continuous bijection (`TauCeti.finiteGrassmannian.continuous_starProjection_toEuclidean`) from a
compact space to a Hausdorff space. In particular `Euclidean.grassmannian E k` is compact for
finite-dimensional `E`. Every element has operator norm at most `1`
(`Euclidean.grassmannian.norm_le_one`).

This is the Grassmannian `G(E, k)` that carries the varifolds of a Euclidean space
(L. Simon, *Lectures on Geometric Measure Theory*, §38).

## Main definitions

* `Euclidean.grassmannian E k`: the orthogonal projections of `E` with range of rank `k`.
* `Euclidean.grassmannian.submoduleEquiv`: the bijection with the `k`-dimensional subspaces.
* `Euclidean.grassmannian.finiteGrassmannianHomeomorph`: the homeomorphism from
  `TauCeti.finiteGrassmannian ℝ k N` induced by a linear isometry
  `E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)`.

## Main results

* `Euclidean.isCompact_grassmannian`: `Euclidean.grassmannian E k` is compact.
-/

public section

open Module

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

section CompleteSpace

variable [CompleteSpace E]

variable (E) in
/-- The **Grassmannian** `G(E, k)` of a real inner product space in projection form: the
self-adjoint idempotent continuous linear maps of `E` whose range has rank `k`, that is, the
orthogonal projections onto the `k`-dimensional subspaces of `E` (L. Simon, *Lectures on
Geometric Measure Theory*, §38). The rank is the cardinal `Module.rank`, so that an
infinite-rank projection of an infinite-dimensional `E` is not a point of `G(E, 0)`. -/
def grassmannian (k : ℕ) : Set (E →L[ℝ] E) :=
  {P | IsStarProjection P ∧ Module.rank ℝ P.range = k}

/-- Membership in the Grassmannian unfolds to its defining conditions. -/
theorem mem_grassmannian {P : E →L[ℝ] E} :
    P ∈ grassmannian E k ↔ IsStarProjection P ∧ Module.rank ℝ P.range = k :=
  Iff.rfl

namespace grassmannian

/-- A point of the Grassmannian is a star projection. -/
theorem isStarProjection {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k) : IsStarProjection P :=
  hP.1

/-- The range of a point of `G(E, k)` is finite-dimensional. -/
theorem finiteDimensional_range {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k) :
    FiniteDimensional ℝ P.range :=
  Module.finite_of_rank_eq_nat hP.2

/-- The range of a point of `G(E, k)` has dimension `k`. -/
theorem finrank_range {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k) : finrank ℝ P.range = k :=
  finrank_eq_of_rank_eq hP.2

/-- A point of the Grassmannian has operator norm at most `1`. -/
theorem norm_le_one {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k) :
    ‖P‖ ≤ 1 :=
  hP.1.norm_le

/-- The orthogonal projection onto a `k`-dimensional subspace is a point of `G(E, k)`. -/
theorem starProjection_mem {S : Submodule ℝ E} [FiniteDimensional ℝ S]
    (hS : finrank ℝ S = k) : S.starProjection ∈ grassmannian E k :=
  ⟨isStarProjection_starProjection, by
    rw [Submodule.range_starProjection, ← Module.finrank_eq_rank, hS]⟩

/-- A point of the Grassmannian is the orthogonal projection onto its range. -/
theorem eq_starProjection_range {P : E →L[ℝ] E}
    (hP : P ∈ grassmannian E k) :
    ∃ (_ : P.range.HasOrthogonalProjection), P = P.range.starProjection :=
  isStarProjection_iff_eq_starProjection_range.1 hP.1

section FiniteGrassmannian

open TauCeti

variable {N : ℕ}

/-- For `S` in the finite Grassmannian, `e⁻¹ P_S e` lies in `G(E, k)`, where `P_S` is the
orthogonal projection onto `S.toEuclidean`. -/
private theorem conj_starProjection_toEuclidean_mem (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (S : finiteGrassmannian ℝ k N) :
    e.symm.conjStarAlgEquiv S.toEuclidean.starProjection ∈ grassmannian E k := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_starProjection]
  exact starProjection_mem <| (e.symm.toLinearEquiv.finrank_map_eq _).trans S.finrank_toEuclidean

/-- The map `S ↦ e⁻¹ P_S e` is a bijection from the finite Grassmannian onto `G(E, k)`. -/
private theorem bijective_conj_starProjection_toEuclidean
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    Function.Bijective fun S : finiteGrassmannian ℝ k N ↦
      (⟨_, conj_starProjection_toEuclidean_mem e S⟩ : grassmannian E k) := by
  refine ⟨fun S T h ↦ finiteGrassmannian.toEuclidean_injective ?_, fun P ↦ ?_⟩
  · have h := congrArg (fun P : grassmannian E k ↦ P.val.range) h
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_starProjection,
      Submodule.range_starProjection] at h
    exact Submodule.map_injective_of_injective e.symm.injective h
  · let W := P.val.range.map (e.toLinearEquiv : E →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    let L := (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm
    have hS : finrank ℝ (W.comap L.toLinearMap) = k := by
      rw [Submodule.comap_equiv_eq_map_symm, L.symm.finrank_map_eq,
        e.toLinearEquiv.finrank_map_eq, finrank_range P.property]
    let S : finiteGrassmannian ℝ k N := ⟨W.comap L.toLinearMap, hS⟩
    have hSW : S.toEuclidean = W := by
      ext x
      simp [S, L]
    refine ⟨S, Subtype.ext <| ContinuousLinearMap.IsStarProjection.ext
      (conj_starProjection_toEuclidean_mem e S).1 P.property.1 ?_⟩
    dsimp only
    rw [LinearIsometryEquiv.conjStarAlgEquiv_starProjection, Submodule.range_starProjection, hSW,
      LinearIsometryEquiv.toLinearEquiv_symm, Submodule.map_symm_eq_iff]

variable (k) in
/-- A linear isometry `e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` induces the homeomorphism
`S ↦ e⁻¹ P_S e` from Tau Ceti's finite Grassmannian `TauCeti.finiteGrassmannian ℝ k N` onto
`G(E, k)`, where `P_S` is the orthogonal projection onto `S.toEuclidean`. Its inverse sends `P` to
the subspace `e(range P)` read in coordinates (`toEuclidean_finiteGrassmannianHomeomorph_symm`). -/
noncomputable def finiteGrassmannianHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    finiteGrassmannian ℝ k N ≃ₜ grassmannian E k :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (bijective_conj_starProjection_toEuclidean e)) <| by
    refine Continuous.subtype_mk ?_ _
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    fun_prop

/-- `finiteGrassmannianHomeomorph k e` sends `S` to `e⁻¹ P_S e`. -/
@[simp]
theorem coe_finiteGrassmannianHomeomorph_apply (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (S : finiteGrassmannian ℝ k N) :
    (finiteGrassmannianHomeomorph k e S : E →L[ℝ] E) =
      e.symm.conjStarAlgEquiv S.toEuclidean.starProjection :=
  (rfl)

/-- The inverse of `finiteGrassmannianHomeomorph k e` sends `P` to the subspace `e(range P)`,
read in the coordinates of `EuclideanSpace ℝ (Fin N)`. -/
theorem toEuclidean_finiteGrassmannianHomeomorph_symm (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (P : grassmannian E k) :
    ((finiteGrassmannianHomeomorph k e).symm P).toEuclidean =
      P.val.range.map (e.toLinearEquiv : E →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
  set S := (finiteGrassmannianHomeomorph k e).symm P
  have h : (finiteGrassmannianHomeomorph k e S : E →L[ℝ] E).range = P.val.range := by
    rw [Homeomorph.apply_symm_apply]
  rw [coe_finiteGrassmannianHomeomorph_apply, LinearIsometryEquiv.conjStarAlgEquiv_starProjection,
    Submodule.range_starProjection, LinearIsometryEquiv.toLinearEquiv_symm,
    Submodule.map_symm_eq_iff] at h
  exact h.symm

end FiniteGrassmannian

end grassmannian

end CompleteSpace

namespace grassmannian

variable [FiniteDimensional ℝ E]

variable (E k) in
/-- The bijection `S ↦ S.starProjection` from the `k`-dimensional subspaces of `E` onto the
Grassmannian `G(E, k)`, with inverse `P ↦ P.range`. -/
noncomputable def submoduleEquiv :
    {S : Submodule ℝ E // finrank ℝ S = k} ≃ grassmannian E k where
  toFun S := ⟨S.val.starProjection, starProjection_mem S.property⟩
  invFun P := ⟨P.val.range, finrank_range P.property⟩
  left_inv S := Subtype.ext S.val.range_starProjection
  right_inv P := Subtype.ext (eq_starProjection_range P.property).2.symm

/-- `submoduleEquiv` sends a subspace to its orthogonal projection. -/
@[simp]
theorem coe_submoduleEquiv_apply (S : {S : Submodule ℝ E // finrank ℝ S = k}) :
    (submoduleEquiv E k S : E →L[ℝ] E) = S.val.starProjection :=
  (rfl)

/-- The inverse of `submoduleEquiv` sends a projection to its range. -/
@[simp]
theorem coe_submoduleEquiv_symm_apply (P : grassmannian E k) :
    ((submoduleEquiv E k).symm P : Submodule ℝ E) = P.val.range :=
  (rfl)

end grassmannian

/-- The Grassmannian `G(E, k)` of a finite-dimensional real inner product space is compact: it is
the image of the compact finite Grassmannian under `grassmannian.finiteGrassmannianHomeomorph`. -/
theorem isCompact_grassmannian [FiniteDimensional ℝ E] : IsCompact (grassmannian E k) := by
  let h := grassmannian.finiteGrassmannianHomeomorph k (stdOrthonormalBasis ℝ E).repr
  simpa [Set.range_comp, h.surjective.range_eq] using
    isCompact_range (continuous_subtypeVal.comp h.continuous)

/-- The Grassmannian of a finite-dimensional real inner product space is a compact space. -/
instance grassmannian.instCompactSpace [FiniteDimensional ℝ E] : CompactSpace (grassmannian E k) :=
  isCompact_iff_compactSpace.1 isCompact_grassmannian

end Euclidean
