/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Projection.Trace
public import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
public import TauCeti.Topology.Grassmannian.Tautological
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.Trace

/-!
# The Grassmannian of an inner product space in projection form

For an inner product space `E` over `𝕜 = ℝ` or `ℂ` and `k : ℕ`, `Euclidean.grassmannian 𝕜 E k` is
the set of continuous linear maps `P : E → E` that are self-adjoint idempotents
(`IsStarProjection`) whose range has rank `k` (`Module.rank`, so the range is finite-dimensional),
with the topology and the operator-norm metric of `E →L[𝕜] E`. Each `k`-plane of `E` is recorded
by its orthogonal projection: when `E` is finite-dimensional, `S ↦ S.starProjection` is a
bijection from the `k`-dimensional subspaces of `E` onto `Euclidean.grassmannian 𝕜 E k`, with
inverse `P ↦ P.range` (`Euclidean.grassmannian.submoduleEquiv`), by Mathlib's
`isStarProjection_iff_eq_starProjection_range`. Recording planes by their projections lets one
state the tangential trace `tr (P ∘ A)` of an endomorphism `A` along a plane, and distances
between planes, directly in terms of `P`.

For a surjective linear isometry `e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)`, sending a point `S` of
Tau Ceti's finite Grassmannian `TauCeti.finiteGrassmannian 𝕜 k N` to `e⁻¹ P_S e`, where `P_S` is
the orthogonal projection onto `S.toEuclidean`, is a homeomorphism onto
`Euclidean.grassmannian 𝕜 E k` (`Euclidean.grassmannian.finiteGrassmannianHomeomorph`). It is a
continuous bijection (`TauCeti.finiteGrassmannian.continuous_starProjection_toEuclidean`) from a
compact space to a Hausdorff space. In particular `Euclidean.grassmannian 𝕜 E k` is compact for
finite-dimensional `E`. Every element has operator norm at most `1`
(`Euclidean.grassmannian.norm_le_one`), equal to `1` when `k ≠ 0`.

This is the Grassmannian `G(E, k)` that carries the varifolds of a Euclidean space
(L. Simon, *Lectures on Geometric Measure Theory*, §38).

## Main definitions

* `Euclidean.grassmannian 𝕜 E k`: the orthogonal projections of `E` with range of rank `k`.
* `Euclidean.grassmannian.submoduleEquiv`: the bijection with the `k`-dimensional subspaces.
* `Euclidean.grassmannian.finiteGrassmannianHomeomorph`: the homeomorphism from
  `TauCeti.finiteGrassmannian 𝕜 k N` induced by a linear isometry
  `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)`.
* `Euclidean.grassmannianOrthogonalHomeomorph`: the passage `P ↦ 1 - P` to orthogonal
  complements, a homeomorphism `G(E, k) ≃ₜ G(E, l)` when `k + l = dim E`.
* `LinearIsometryEquiv.grassmannianCongr`: the homeomorphism `P ↦ U P U⁻¹` of `G(E, k)` onto
  `G(F, k)` induced by a linear isometry equivalence `U : E ≃ₗᵢ[𝕜] F`.

## Main results

* `Euclidean.mem_grassmannian_iff_exists_starProjection`: the points of `G(E, k)` are exactly the
  orthogonal projections `U.starProjection` onto the `k`-dimensional subspaces `U`.
* `Euclidean.mem_grassmannian_iff_trace`: among orthogonal projections, the points of `G(E, k)`
  are those of trace `k`.
* `Euclidean.isClosed_grassmannian`, `Euclidean.isCompact_grassmannian`: `G(E, k)` is closed and
  compact.
* `Euclidean.grassmannian.norm_trace_comp_le`: the tangential trace satisfies
  `‖tr (P ∘ A)‖ ≤ k ‖A‖` for `P ∈ G(E, k)`, and `Euclidean.grassmannian.continuous_trace_comp`:
  it is continuous in `P`.
* `Euclidean.grassmannian.forall_range_le_iff_eq_top`: for `1 ≤ k ≤ rank E` (the rank may be
  infinite), a subspace containing the plane of every point of `G(E, k)` is all of `E`. For a
  linear map `f : E → F`, for instance a linear isometry, the planes of `G(F, k)` all lie in
  `range f` exactly when `f` is surjective (`LinearMap.forall_range_le_range_iff_surjective`).
  For `k = 0` this fails: `G(F, 0)` is `{0}`, whose plane lies in every subspace.
* `Euclidean.grassmannian.finiteGrassmannianHomeomorph_trans_apply` and
  `Euclidean.grassmannian.finiteGrassmannianHomeomorph_trans_symm_apply`: changing the
  coordinates `e` to `O ∘ e` precomposes `finiteGrassmannianHomeomorph` with `S ↦ O⁻¹(S)` and
  postcomposes its inverse with `S ↦ O(S)`, where `TauCeti.finiteGrassmannian.mapEuclidean`
  moves a point of the finite Grassmannian by a linear automorphism of
  `EuclideanSpace 𝕜 (Fin N)`.
* `Euclidean.grassmannian_zero`, `Euclidean.grassmannian_finrank` and
  `Euclidean.grassmannian_eq_empty`: `G(E, 0) = {0}`, `G(E, dim E) = {1}`, and `G(E, k)` is
  empty for `k > dim E`.

## Implementation notes

The rank condition is stated with `Module.rank`, so that the definition is meaningful in every
complete inner product space, and an infinite-rank projection of an infinite-dimensional `E` is
not a point of `G(E, 0)`; in finite dimension it is equivalent to the condition on
`Module.finrank` (`Euclidean.mem_grassmannian_iff_finrank`). Self-adjointness is
`IsStarProjection` for the adjoint as the star operation on `E →L[𝕜] E`, which requires `E` to be
complete. Requiring only `P ∘ P = P` would admit the non-self-adjoint idempotents of the plane,
`[[1, t], [0, 0]]` for `t` real, which form an unbounded family.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proc. Centre Math. Anal. Austral. Nat. Univ. 3
  (1983), §38, where `k`-planes of `ℝⁿ` are identified with orthogonal projections.
-/

public section

open Module Set TauCeti

namespace Euclidean

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {k l : ℕ}

section CompleteSpace

variable [CompleteSpace E]

variable (𝕜 E) in
/-- The **Grassmannian** `G(E, k)` of an inner product space in projection form: the
self-adjoint idempotent continuous linear maps of `E` whose range has rank `k`, that is, the
orthogonal projections onto the `k`-dimensional subspaces of `E` (L. Simon, *Lectures on
Geometric Measure Theory*, §38). The rank is the cardinal `Module.rank`, so that an
infinite-rank projection of an infinite-dimensional `E` is not a point of `G(E, 0)`. -/
def grassmannian (k : ℕ) : Set (E →L[𝕜] E) :=
  {P | IsStarProjection P ∧ Module.rank 𝕜 P.range = k}

/-- Membership in the Grassmannian unfolds to its defining conditions. -/
theorem mem_grassmannian {P : E →L[𝕜] E} :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ Module.rank 𝕜 P.range = k :=
  Iff.rfl

namespace grassmannian

/-- A point of the Grassmannian is a star projection. -/
theorem isStarProjection {P : E →L[𝕜] E} (hP : P ∈ grassmannian 𝕜 E k) : IsStarProjection P :=
  hP.1

/-- The range of a point of `G(E, k)` is finite-dimensional. -/
theorem finiteDimensional_range {P : E →L[𝕜] E} (hP : P ∈ grassmannian 𝕜 E k) :
    FiniteDimensional 𝕜 P.range :=
  Module.finite_of_rank_eq_nat hP.2

/-- The range of a point of `G(E, k)` has dimension `k`. -/
theorem finrank_range {P : E →L[𝕜] E} (hP : P ∈ grassmannian 𝕜 E k) :
    finrank 𝕜 P.range = k :=
  finrank_eq_of_rank_eq hP.2

/-- A point of the Grassmannian has operator norm at most `1`. -/
theorem norm_le_one {P : E →L[𝕜] E} (hP : P ∈ grassmannian 𝕜 E k) :
    ‖P‖ ≤ 1 :=
  hP.1.norm_le

/-- A point of `G(E, k)` with `k ≠ 0` has operator norm `1`. -/
theorem norm_eq_one {P : E →L[𝕜] E} (hP : P ∈ grassmannian 𝕜 E k) (hk : k ≠ 0) :
    ‖P‖ = 1 :=
  hP.1.norm_eq_one fun h ↦ hk <| by
    have := hP.2
    rwa [h, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, rank_bot, eq_comm,
      Nat.cast_eq_zero] at this

/-- The orthogonal projection onto a `k`-dimensional subspace is a point of `G(E, k)`. -/
theorem starProjection_mem {S : Submodule 𝕜 E} [FiniteDimensional 𝕜 S]
    (hS : finrank 𝕜 S = k) : S.starProjection ∈ grassmannian 𝕜 E k :=
  ⟨isStarProjection_starProjection, by
    rw [Submodule.range_starProjection, ← Module.finrank_eq_rank, hS]⟩

/-- A point of the Grassmannian is the orthogonal projection onto its range. -/
theorem eq_starProjection_range {P : E →L[𝕜] E}
    (hP : P ∈ grassmannian 𝕜 E k) :
    ∃ (_ : P.range.HasOrthogonalProjection), P = P.range.starProjection :=
  isStarProjection_iff_eq_starProjection_range.1 hP.1

section FiniteGrassmannian

variable {N : ℕ}

/-- For `S` in the finite Grassmannian, `e⁻¹ P_S e` lies in `G(E, k)`, where `P_S` is the
orthogonal projection onto `S.toEuclidean`. -/
private theorem conj_starProjection_toEuclidean_mem (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (S : finiteGrassmannian 𝕜 k N) :
    e.symm.conjStarAlgEquiv S.toEuclidean.starProjection ∈ grassmannian 𝕜 E k := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_starProjection]
  exact starProjection_mem <| (e.symm.toLinearEquiv.finrank_map_eq _).trans S.finrank_toEuclidean

/-- The map `S ↦ e⁻¹ P_S e` is a bijection from the finite Grassmannian onto `G(E, k)`. -/
private theorem bijective_conj_starProjection_toEuclidean
    (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)) :
    Function.Bijective fun S : finiteGrassmannian 𝕜 k N ↦
      (⟨_, conj_starProjection_toEuclidean_mem e S⟩ : grassmannian 𝕜 E k) := by
  refine ⟨fun S T h ↦ finiteGrassmannian.toEuclidean_injective ?_, fun P ↦ ?_⟩
  · have h := congrArg (fun P : grassmannian 𝕜 E k ↦ P.val.range) h
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_starProjection,
      Submodule.range_starProjection] at h
    exact Submodule.map_injective_of_injective e.symm.injective h
  · let W := P.val.range.map (e.toLinearEquiv : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin N))
    let L := (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm
    have hS : finrank 𝕜 (W.comap L.toLinearMap) = k := by
      rw [Submodule.comap_equiv_eq_map_symm, L.symm.finrank_map_eq,
        e.toLinearEquiv.finrank_map_eq, finrank_range P.property]
    let S : finiteGrassmannian 𝕜 k N := ⟨W.comap L.toLinearMap, hS⟩
    have hSW : S.toEuclidean = W := by
      ext x
      simp [S, L]
    refine ⟨S, Subtype.ext <| ContinuousLinearMap.IsStarProjection.ext
      (conj_starProjection_toEuclidean_mem e S).1 P.property.1 ?_⟩
    dsimp only
    rw [LinearIsometryEquiv.conjStarAlgEquiv_starProjection, Submodule.range_starProjection, hSW,
      LinearIsometryEquiv.toLinearEquiv_symm, Submodule.map_symm_eq_iff]

variable (k) in
/-- A linear isometry `e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)` induces the homeomorphism
`S ↦ e⁻¹ P_S e` from Tau Ceti's finite Grassmannian `TauCeti.finiteGrassmannian 𝕜 k N` onto
`G(E, k)`, where `P_S` is the orthogonal projection onto `S.toEuclidean`. Its inverse sends `P` to
the subspace `e(range P)` read in coordinates (`toEuclidean_finiteGrassmannianHomeomorph_symm`). -/
noncomputable def finiteGrassmannianHomeomorph (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)) :
    finiteGrassmannian 𝕜 k N ≃ₜ grassmannian 𝕜 E k :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (bijective_conj_starProjection_toEuclidean e)) <| by
    refine Continuous.subtype_mk ?_ _
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    fun_prop

/-- `finiteGrassmannianHomeomorph k e` sends `S` to `e⁻¹ P_S e`. -/
@[simp]
theorem coe_finiteGrassmannianHomeomorph_apply (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (S : finiteGrassmannian 𝕜 k N) :
    (finiteGrassmannianHomeomorph k e S : E →L[𝕜] E) =
      e.symm.conjStarAlgEquiv S.toEuclidean.starProjection :=
  (rfl)

/-- The inverse of `finiteGrassmannianHomeomorph k e` sends `P` to the subspace `e(range P)`,
read in the coordinates of `EuclideanSpace 𝕜 (Fin N)`. -/
theorem toEuclidean_finiteGrassmannianHomeomorph_symm (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (P : grassmannian 𝕜 E k) :
    ((finiteGrassmannianHomeomorph k e).symm P).toEuclidean =
      P.val.range.map (e.toLinearEquiv : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin N)) := by
  set S := (finiteGrassmannianHomeomorph k e).symm P
  have h : (finiteGrassmannianHomeomorph k e S : E →L[𝕜] E).range = P.val.range := by
    rw [Homeomorph.apply_symm_apply]
  rw [coe_finiteGrassmannianHomeomorph_apply, LinearIsometryEquiv.conjStarAlgEquiv_starProjection,
    Submodule.range_starProjection, LinearIsometryEquiv.toLinearEquiv_symm,
    Submodule.map_symm_eq_iff] at h
  exact h.symm

/-- Changing the coordinates `e` to `O ∘ e`, for a linear isometry `O` of
`EuclideanSpace 𝕜 (Fin N)`, postcomposes the inverse of `finiteGrassmannianHomeomorph k e` with
`S ↦ O(S)`. -/
theorem finiteGrassmannianHomeomorph_trans_symm_apply
    (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (O : EuclideanSpace 𝕜 (Fin N) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)) (P : grassmannian 𝕜 E k) :
    (finiteGrassmannianHomeomorph k (e.trans O)).symm P =
      ((finiteGrassmannianHomeomorph k e).symm P).mapEuclidean O.toLinearEquiv :=
  finiteGrassmannian.toEuclidean_injective <| by
    simp [toEuclidean_finiteGrassmannianHomeomorph_symm, ← Submodule.map_comp]

/-- Changing the coordinates `e` to `O ∘ e`, for a linear isometry `O` of
`EuclideanSpace 𝕜 (Fin N)`, precomposes `finiteGrassmannianHomeomorph k e` with `S ↦ O⁻¹(S)`. -/
theorem finiteGrassmannianHomeomorph_trans_apply (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (O : EuclideanSpace 𝕜 (Fin N) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N))
    (S : finiteGrassmannian 𝕜 k N) :
    finiteGrassmannianHomeomorph k (e.trans O) S =
      finiteGrassmannianHomeomorph k e (S.mapEuclidean O.toLinearEquiv.symm) := by
  apply (finiteGrassmannianHomeomorph k (e.trans O)).symm.injective
  rw [Homeomorph.symm_apply_apply, finiteGrassmannianHomeomorph_trans_symm_apply,
    Homeomorph.symm_apply_apply, finiteGrassmannian.mapEuclidean_mapEuclidean_symm]

end FiniteGrassmannian

/-- For `1 ≤ k ≤ rank E`, a subspace `S` of `E` contains the plane of every point of `G(E, k)`
only when `S` is all of `E`. The rank of `E` may be infinite. -/
theorem forall_range_le_iff_eq_top {S : Submodule 𝕜 E} (hk : k ≠ 0)
    (hkE : (k : Cardinal) ≤ Module.rank 𝕜 E) :
    (∀ Q : grassmannian 𝕜 E k, (Q : E →L[𝕜] E).range ≤ S) ↔ S = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ h ▸ le_top⟩
  by_contra hS
  obtain ⟨v, -, hvS⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hS)
  obtain ⟨T, hvT, hT⟩ := Submodule.exists_mem_rank_eq v hk hkE
  have : FiniteDimensional 𝕜 T := Module.finite_of_rank_eq_nat hT
  refine hvS <| h ⟨T.starProjection, starProjection_mem (finrank_eq_of_rank_eq hT)⟩ ?_
  rwa [Submodule.range_starProjection]

/-- For an endomorphism `A` of `E`, the tangential trace `P ↦ tr (P ∘ A)` is continuous on
`G(E, k)`; it is the restriction of a linear functional of `P`. When `E` is
infinite-dimensional, `LinearMap.trace` is the zero map, so this expression is the tangential
trace along `range P` only for finite-dimensional `E`. -/
theorem continuous_trace_comp (A : E →L[𝕜] E) :
    Continuous fun P : grassmannian 𝕜 E k ↦
      LinearMap.trace 𝕜 E ((P : E →L[𝕜] E) ∘L A : E →L[𝕜] E) :=
  continuous_trace.comp (continuous_subtypeVal.clm_comp continuous_const)

end grassmannian

/-- The range of the complementary projection `1 - P` of a point `P` of `G(E, k)` is the orthogonal
complement of the range of `P`. -/
@[simp]
theorem range_one_sub_coe_grassmannian (P : grassmannian 𝕜 E k) :
    LinearMap.range (1 - ((P : E →L[𝕜] E) : E →ₗ[𝕜] E)) = (P : E →L[𝕜] E).rangeᗮ :=
  P.property.1.range_one_sub

/-- `G(E, 0) = {0}`: the only projection of rank zero is `0`. -/
@[simp]
theorem grassmannian_zero : grassmannian 𝕜 E 0 = {0} := by
  ext P
  rw [mem_grassmannian, mem_singleton_iff, Nat.cast_zero, Submodule.rank_eq_zero,
    LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero,
    ContinuousLinearMap.coe_inj]
  exact ⟨And.right, fun h ↦ ⟨h ▸ IsStarProjection.zero _, h⟩⟩

/-- The orthogonal projection onto a finite-dimensional subspace `U` lies in `G(E, k)` exactly
when `U` has dimension `k`. -/
@[simp]
theorem starProjection_mem_grassmannian_iff {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U] :
    U.starProjection ∈ grassmannian 𝕜 E k ↔ finrank 𝕜 U = k := by
  rw [mem_grassmannian, Submodule.range_starProjection, ← Module.finrank_eq_rank, Nat.cast_inj]
  exact and_iff_right isStarProjection_starProjection

end CompleteSpace

section FiniteDimensional

variable [CompleteSpace E] [FiniteDimensional 𝕜 E] {P : E →L[𝕜] E}

/-- In finite dimension, the rank condition defining `G(E, k)` is a condition on `finrank`. -/
theorem mem_grassmannian_iff_finrank :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ finrank 𝕜 P.range = k := by
  rw [mem_grassmannian, ← Module.finrank_eq_rank, Nat.cast_inj]

/-- The points of `G(E, k)` are exactly the orthogonal projections onto the `k`-dimensional
subspaces of `E`. -/
theorem mem_grassmannian_iff_exists_starProjection :
    P ∈ grassmannian 𝕜 E k ↔ ∃ U : Submodule 𝕜 E, finrank 𝕜 U = k ∧ P = U.starProjection := by
  refine ⟨fun hP ↦ ⟨P.range, grassmannian.finrank_range hP,
    (grassmannian.eq_starProjection_range hP).2⟩, ?_⟩
  rintro ⟨U, rfl, rfl⟩
  exact grassmannian.starProjection_mem rfl

/-- Among orthogonal projections, the points of `G(E, k)` are those of trace `k`. -/
theorem mem_grassmannian_iff_trace :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ LinearMap.trace 𝕜 E P = k := by
  rw [mem_grassmannian_iff_finrank]
  refine and_congr_right fun hP ↦ ?_
  rw [(isStarProjection_iff_eq_starProjection_range.mp hP).2, Submodule.range_starProjection,
    Submodule.trace_starProjection, Nat.cast_inj]

/-- The trace of a point of `G(E, k)` is `k`. -/
theorem grassmannian.trace_eq (hP : P ∈ grassmannian 𝕜 E k) :
    LinearMap.trace 𝕜 E P = k :=
  (mem_grassmannian_iff_trace.mp hP).2

/-- The Grassmannian is closed in the space of operators. -/
theorem isClosed_grassmannian : IsClosed (grassmannian 𝕜 E k) := by
  have : grassmannian 𝕜 E k = {P : E →L[𝕜] E | P * P = P} ∩ {P | IsSelfAdjoint P} ∩
      {P | traceCLM 𝕜 E P = k} := by
    ext P
    simp only [mem_grassmannian_iff_trace, isStarProjection_iff, IsIdempotentElem,
      traceCLM_apply, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [this]
  exact ((isClosed_eq (continuous_id.mul continuous_id) continuous_id).inter
    isClosed_setOfPred_isSelfAdjoint).inter
      (isClosed_eq (traceCLM 𝕜 E).continuous continuous_const)

/-- The Grassmannian `G(E, k)` of a finite-dimensional inner product space is compact: it is the
image of the compact finite Grassmannian under `grassmannian.finiteGrassmannianHomeomorph`. -/
theorem isCompact_grassmannian : IsCompact (grassmannian 𝕜 E k) := by
  let h := grassmannian.finiteGrassmannianHomeomorph k (stdOrthonormalBasis 𝕜 E).repr
  simpa [Set.range_comp, h.surjective.range_eq] using
    isCompact_range (continuous_subtypeVal.comp h.continuous)

/-- The Grassmannian of a finite-dimensional inner product space is a compact space. -/
instance grassmannian.instCompactSpace : CompactSpace (grassmannian 𝕜 E k) :=
  isCompact_iff_compactSpace.1 isCompact_grassmannian

/-- The tangential trace of an operator `A` along a plane `P ∈ G(E, k)` is bounded by `k ‖A‖`. -/
theorem grassmannian.norm_trace_comp_le (hP : P ∈ grassmannian 𝕜 E k) (A : E →L[𝕜] E) :
    ‖LinearMap.trace 𝕜 E (P ∘L A : E →L[𝕜] E)‖ ≤ k * ‖A‖ := by
  rw [← traceCLM_apply]
  refine (P ∘L A).norm_traceCLM_le_finrank_range_mul.trans
    (mul_le_mul ?_ ?_ (norm_nonneg _) (Nat.cast_nonneg _))
  · rw [← grassmannian.finrank_range hP]
    exact_mod_cast Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  · exact (P.opNorm_comp_le A).trans
      (mul_le_of_le_one_left (norm_nonneg _) (grassmannian.norm_le_one hP))

/-- The passage to the orthogonal complement: `P ∈ G(E, k)` gives `1 - P ∈ G(E, l)` when
`k + l = dim E`. -/
theorem grassmannian.one_sub_mem (hP : P ∈ grassmannian 𝕜 E k) (hkl : k + l = finrank 𝕜 E) :
    1 - P ∈ grassmannian 𝕜 E l := by
  rw [mem_grassmannian_iff_trace] at hP ⊢
  refine ⟨hP.1.one_sub, ?_⟩
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one, map_sub,
    LinearMap.trace_one, hP.2, ← hkl, Nat.cast_add]
  ring

theorem one_sub_mem_grassmannian_iff (hkl : k + l = finrank 𝕜 E) :
    1 - P ∈ grassmannian 𝕜 E l ↔ P ∈ grassmannian 𝕜 E k :=
  ⟨fun h ↦ by simpa using grassmannian.one_sub_mem h (l := k) (by omega),
    fun h ↦ grassmannian.one_sub_mem h hkl⟩

/-- The passage to orthogonal complements `P ↦ 1 - P`, a homeomorphism from `G(E, k)` onto
`G(E, l)` when `k + l = dim E`: if `P` projects onto `S`, then `1 - P` projects onto `Sᗮ`
(Mathlib's `Submodule.starProjection_orthogonal'`). -/
noncomputable def grassmannianOrthogonalHomeomorph (hkl : k + l = finrank 𝕜 E) :
    grassmannian 𝕜 E k ≃ₜ grassmannian 𝕜 E l where
  toFun P := ⟨1 - P, grassmannian.one_sub_mem P.property hkl⟩
  invFun Q := ⟨1 - Q, grassmannian.one_sub_mem Q.property (by omega)⟩
  left_inv P := Subtype.ext (sub_sub_cancel 1 P.val)
  right_inv Q := Subtype.ext (sub_sub_cancel 1 Q.val)
  continuous_toFun := (continuous_const.sub continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_const.sub continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_grassmannianOrthogonalHomeomorph (hkl : k + l = finrank 𝕜 E)
    (P : grassmannian 𝕜 E k) : (grassmannianOrthogonalHomeomorph hkl P : E →L[𝕜] E) = 1 - P :=
  (rfl)

/-- The plane of the orthogonal complement `1 - P` is the orthogonal complement of the plane of
`P`. -/
theorem range_coe_grassmannianOrthogonalHomeomorph (hkl : k + l = finrank 𝕜 E)
    (P : grassmannian 𝕜 E k) :
    (grassmannianOrthogonalHomeomorph hkl P : E →L[𝕜] E).range = (P : E →L[𝕜] E).rangeᗮ := by
  simp

@[simp]
theorem grassmannianOrthogonalHomeomorph_symm (hkl : k + l = finrank 𝕜 E) :
    (grassmannianOrthogonalHomeomorph hkl).symm =
      grassmannianOrthogonalHomeomorph (𝕜 := 𝕜) (E := E) (by omega : l + k = finrank 𝕜 E) :=
  (rfl)

/-- `G(E, dim E) = {1}`: the only projection of full rank is the identity. -/
@[simp]
theorem grassmannian_finrank : grassmannian 𝕜 E (finrank 𝕜 E) = {1} := by
  ext P
  rw [mem_singleton_iff, ← one_sub_mem_grassmannian_iff (l := 0) (add_zero _), grassmannian_zero,
    mem_singleton_iff, sub_eq_zero, eq_comm]

/-- `G(E, k)` is empty for `k > dim E`: no subspace has dimension larger than `E`. -/
theorem grassmannian_eq_empty (hk : finrank 𝕜 E < k) : grassmannian 𝕜 E k = ∅ :=
  eq_empty_of_forall_notMem fun _ hP ↦ (grassmannian.finrank_range hP ▸
    Submodule.finrank_le _).not_gt hk

namespace grassmannian

variable (𝕜 E k) in
/-- The bijection `S ↦ S.starProjection` from the `k`-dimensional subspaces of `E` onto the
Grassmannian `G(E, k)`, with inverse `P ↦ P.range`. -/
noncomputable def submoduleEquiv :
    {S : Submodule 𝕜 E // finrank 𝕜 S = k} ≃ grassmannian 𝕜 E k where
  toFun S := ⟨S.val.starProjection, starProjection_mem S.property⟩
  invFun P := ⟨P.val.range, finrank_range P.property⟩
  left_inv S := Subtype.ext S.val.range_starProjection
  right_inv P := Subtype.ext (eq_starProjection_range P.property).2.symm

/-- `submoduleEquiv` sends a subspace to its orthogonal projection. -/
@[simp]
theorem coe_submoduleEquiv_apply (S : {S : Submodule 𝕜 E // finrank 𝕜 S = k}) :
    (submoduleEquiv 𝕜 E k S : E →L[𝕜] E) = S.val.starProjection :=
  (rfl)

/-- The inverse of `submoduleEquiv` sends a projection to its range. -/
@[simp]
theorem coe_submoduleEquiv_symm_apply (P : grassmannian 𝕜 E k) :
    ((submoduleEquiv 𝕜 E k).symm P : Submodule 𝕜 E) = P.val.range :=
  (rfl)

end grassmannian

end FiniteDimensional

end Euclidean

namespace LinearIsometryEquiv

open Euclidean

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  {k : ℕ} {P : E →L[𝕜] E}

/-- Conjugating a point of `G(E, k)` by a linear isometry equivalence `U : E ≃ₗᵢ[𝕜] F` gives a
point of `G(F, k)`. -/
theorem conjStarAlgEquiv_mem_grassmannian (U : E ≃ₗᵢ[𝕜] F) (hP : P ∈ grassmannian 𝕜 E k) :
    U.conjStarAlgEquiv P ∈ grassmannian 𝕜 F k := by
  refine ⟨hP.1.map U.conjStarAlgEquiv, ?_⟩
  have h := U.toLinearEquiv.lift_rank_map_eq P.range
  rw [← range_conjStarAlgEquiv, hP.2, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff] at h
  exact h

@[simp]
theorem conjStarAlgEquiv_mem_grassmannian_iff (U : E ≃ₗᵢ[𝕜] F) :
    U.conjStarAlgEquiv P ∈ grassmannian 𝕜 F k ↔ P ∈ grassmannian 𝕜 E k :=
  ⟨fun h ↦ by
    simpa [← symm_conjStarAlgEquiv] using U.symm.conjStarAlgEquiv_mem_grassmannian h,
    U.conjStarAlgEquiv_mem_grassmannian⟩

variable (k) in
/-- The homeomorphism `P ↦ U P U⁻¹` of `G(E, k)` onto `G(F, k)` induced by a linear isometry
equivalence `U : E ≃ₗᵢ[𝕜] F`. -/
noncomputable def grassmannianCongr (U : E ≃ₗᵢ[𝕜] F) :
    grassmannian 𝕜 E k ≃ₜ grassmannian 𝕜 F k where
  toFun P := ⟨U.conjStarAlgEquiv P, U.conjStarAlgEquiv_mem_grassmannian P.property⟩
  invFun Q := ⟨U.conjStarAlgEquiv.symm Q, U.symm.conjStarAlgEquiv_mem_grassmannian Q.property⟩
  left_inv P := Subtype.ext (U.conjStarAlgEquiv.symm_apply_apply P)
  right_inv Q := Subtype.ext (U.conjStarAlgEquiv.apply_symm_apply Q)
  continuous_toFun := (U.continuous_conjStarAlgEquiv.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (U.symm.continuous_conjStarAlgEquiv.comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_grassmannianCongr_apply (U : E ≃ₗᵢ[𝕜] F) (P : grassmannian 𝕜 E k) :
    (U.grassmannianCongr k P : F →L[𝕜] F) = U.conjStarAlgEquiv P :=
  (rfl)

/-- The plane of `U P U⁻¹` is the image under `U` of the plane of `P`. -/
theorem range_coe_grassmannianCongr_apply (U : E ≃ₗᵢ[𝕜] F) (P : grassmannian 𝕜 E k) :
    (U.grassmannianCongr k P : F →L[𝕜] F).range =
      (P : E →L[𝕜] E).range.map (U.toLinearEquiv : E →ₗ[𝕜] F) :=
  U.range_conjStarAlgEquiv P

@[simp]
theorem grassmannianCongr_symm (U : E ≃ₗᵢ[𝕜] F) :
    (U.grassmannianCongr k).symm = U.symm.grassmannianCongr k := by
  ext Q : 2
  simp [grassmannianCongr]

@[simp]
theorem grassmannianCongr_refl :
    (LinearIsometryEquiv.refl 𝕜 E).grassmannianCongr k = Homeomorph.refl _ := by
  ext P : 2
  simp [grassmannianCongr]

theorem grassmannianCongr_trans (U : E ≃ₗᵢ[𝕜] F) (V : F ≃ₗᵢ[𝕜] G) :
    (U.trans V).grassmannianCongr k = (U.grassmannianCongr k).trans (V.grassmannianCongr k) := by
  ext P : 2
  simp [grassmannianCongr, conjStarAlgEquiv_trans]

end LinearIsometryEquiv

namespace LinearMap

open Euclidean

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] {k : ℕ}

/-- For `1 ≤ k ≤ rank F` and a linear map `f : E → F`, the plane of every point of `G(F, k)` lies
in `range f` exactly when `f` is surjective. The rank of `F` may be infinite. For a linear
isometry `U`, apply it to `U.toLinearMap`. -/
theorem forall_range_le_range_iff_surjective (f : E →ₗ[𝕜] F) (hk : k ≠ 0)
    (hkF : (k : Cardinal) ≤ Module.rank 𝕜 F) :
    (∀ Q : grassmannian 𝕜 F k, (Q : F →L[𝕜] F).range ≤ LinearMap.range f) ↔
      Function.Surjective f := by
  rw [grassmannian.forall_range_le_iff_eq_top hk hkF, LinearMap.range_eq_top]

end LinearMap
