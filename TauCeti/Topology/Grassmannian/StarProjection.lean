/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Trace
public import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# The Grassmannian of an inner product space as a space of orthogonal projections

A `k`-dimensional subspace `S` of a finite-dimensional inner product space `E` over `𝕜 = ℝ` or
`ℂ` is recorded by its orthogonal projection `P_S`, a self-adjoint idempotent operator of rank
`k`. This file studies the set `TauCeti.Euclidean.grassmannian 𝕜 E k` of such operators, with the
subspace topology and the operator-norm metric of `E →L[𝕜] E`. It is the fibre of the Grassmann
bundle over which varifolds are measures, and recording planes by their projections lets one
state the tangential trace `tr (P ∘ A)` of an endomorphism `A` along a plane, and distances between
planes, directly in terms of `P`.

## Main definitions

* `TauCeti.Euclidean.grassmannian 𝕜 E k`: the self-adjoint idempotents of `E →L[𝕜] E` whose range
  has dimension `k`.
* `TauCeti.Euclidean.grassmannianOrthogonalHomeomorph`: the passage `P ↦ 1 - P` to orthogonal
  complements, a homeomorphism `G(E, k) ≃ₜ G(E, l)` when `k + l = dim E`.
* `LinearIsometryEquiv.grassmannianCongr`: the homeomorphism `P ↦ U P U⁻¹` of `G(E, k)` onto
  `G(F, k)` induced by a linear isometry equivalence `U : E ≃ₗᵢ[𝕜] F`.
* `TauCeti.finiteGrassmannian.starProjectionHomeomorph`: the finite Grassmannian
  `TauCeti.finiteGrassmannian 𝕜 k N`, a quotient of the space of frames, is homeomorphic to
  `G(EuclideanSpace 𝕜 (Fin N), k)` by sending a subspace to its orthogonal projection, so both
  carriers describe the same space of planes.

## Main results

* `TauCeti.Euclidean.mem_grassmannian_iff_exists_starProjection`: the points of `G(E, k)` are
  exactly the orthogonal projections `U.starProjection` onto the `k`-dimensional subspaces `U`.
* `TauCeti.Euclidean.mem_grassmannian_iff_trace`: among orthogonal projections, the points of
  `G(E, k)` are those of trace `k`.
* `TauCeti.Euclidean.isCompact_grassmannian`: `G(E, k)` is compact; it is closed, and every point
  has norm at most one (`TauCeti.Euclidean.norm_le_one_of_mem_grassmannian`), equal to one when
  `k ≠ 0`.
* `TauCeti.Euclidean.norm_trace_comp_le_of_mem_grassmannian`: the tangential trace satisfies
  `‖tr (P ∘ A)‖ ≤ k ‖A‖` for `P ∈ G(E, k)`.
* `TauCeti.Euclidean.grassmannian_zero`, `TauCeti.Euclidean.grassmannian_finrank` and
  `TauCeti.Euclidean.grassmannian_eq_empty`: `G(E, 0) = {0}`, `G(E, dim E) = {1}`, and `G(E, k)` is
  empty for `k > dim E`.

## Implementation notes

The rank condition is stated with `Module.rank`, so that the definition is meaningful in every
complete inner product space; in finite dimension it is equivalent to the condition on
`Module.finrank` (`TauCeti.Euclidean.mem_grassmannian_iff_finrank`), which is how it is used.
Self-adjointness is `IsStarProjection` for the adjoint as the star operation on `E →L[𝕜] E`, which
requires `E` to be complete. Requiring only `P ∘ P = P` would admit the non-self-adjoint
idempotents of the plane, `[[1, t], [0, 0]]` for `t` real, which form an unbounded family.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proc. Centre Math. Anal. Austral. Nat. Univ. 3
  (1983), §38, where `k`-planes of `ℝⁿ` are identified with orthogonal projections.
-/

public section

open Module Set Topology

namespace TauCeti

namespace Euclidean

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable (𝕜 E) in
/-- The **Grassmannian** `G(E, k)` of an inner product space `E`, presented by orthogonal
projections: the self-adjoint idempotent operators on `E` whose range has dimension `k`, that is,
the orthogonal projections onto the `k`-dimensional subspaces of `E`. -/
def grassmannian (k : ℕ) : Set (E →L[𝕜] E) :=
  {P | IsStarProjection P ∧ Module.rank 𝕜 P.range = k}

variable {k l : ℕ} {P : E →L[𝕜] E}

theorem mem_grassmannian :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ Module.rank 𝕜 P.range = k :=
  Iff.rfl

theorem isStarProjection_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) :
    IsStarProjection P :=
  hP.1

variable [FiniteDimensional 𝕜 E]

/-- In finite dimension, the rank condition defining `G(E, k)` is a condition on `finrank`. -/
theorem mem_grassmannian_iff_finrank :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ finrank 𝕜 P.range = k := by
  rw [mem_grassmannian, ← Module.finrank_eq_rank, Nat.cast_inj]

theorem finrank_range_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) :
    finrank 𝕜 P.range = k :=
  (mem_grassmannian_iff_finrank.mp hP).2

/-- The orthogonal projection onto a subspace `U` lies in `G(E, k)` exactly when `U` has
dimension `k`. -/
@[simp]
theorem starProjection_mem_grassmannian_iff {U : Submodule 𝕜 E} :
    U.starProjection ∈ grassmannian 𝕜 E k ↔ finrank 𝕜 U = k := by
  rw [mem_grassmannian_iff_finrank, Submodule.range_starProjection]
  exact and_iff_right isStarProjection_starProjection

/-- The orthogonal projection onto a subspace `U` lies in the Grassmannian of planes of
dimension `finrank U`. -/
theorem starProjection_mem_grassmannian (U : Submodule 𝕜 E) :
    U.starProjection ∈ grassmannian 𝕜 E (finrank 𝕜 U) :=
  starProjection_mem_grassmannian_iff.mpr rfl

/-- A point of the Grassmannian is the orthogonal projection onto its range. -/
theorem eq_starProjection_range_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) :
    P = P.range.starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp hP.1).2

/-- The points of `G(E, k)` are exactly the orthogonal projections onto the `k`-dimensional
subspaces of `E`. -/
theorem mem_grassmannian_iff_exists_starProjection :
    P ∈ grassmannian 𝕜 E k ↔ ∃ U : Submodule 𝕜 E, finrank 𝕜 U = k ∧ P = U.starProjection := by
  refine ⟨fun hP ↦ ⟨P.range, finrank_range_of_mem_grassmannian hP,
    eq_starProjection_range_of_mem_grassmannian hP⟩, ?_⟩
  rintro ⟨U, rfl, rfl⟩
  exact starProjection_mem_grassmannian U

/-- Among orthogonal projections, the points of `G(E, k)` are those of trace `k`. -/
theorem mem_grassmannian_iff_trace :
    P ∈ grassmannian 𝕜 E k ↔ IsStarProjection P ∧ LinearMap.trace 𝕜 E P = k := by
  rw [mem_grassmannian_iff_finrank]
  refine and_congr_right fun hP ↦ ?_
  rw [(isStarProjection_iff_eq_starProjection_range.mp hP).2, Submodule.range_starProjection,
    Submodule.trace_starProjection, Nat.cast_inj]

/-- The trace of a point of `G(E, k)` is `k`. -/
theorem trace_eq_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) :
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

omit [FiniteDimensional 𝕜 E] in
/-- An operator in the Grassmannian has norm at most one. -/
theorem norm_le_one_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) : ‖P‖ ≤ 1 :=
  hP.1.norm_le P

omit [FiniteDimensional 𝕜 E] in
/-- An operator in `G(E, k)` with `k ≠ 0` has norm one. -/
theorem norm_eq_one_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) (hk : k ≠ 0) :
    ‖P‖ = 1 := by
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp hP.1
  rw [h]
  refine Submodule.norm_starProjection _ fun hb ↦ hk ?_
  have := hP.2
  rwa [hb, rank_bot, eq_comm, Nat.cast_eq_zero] at this

/-- The Grassmannian is compact. -/
theorem isCompact_grassmannian : IsCompact (grassmannian 𝕜 E k) :=
  haveI := FiniteDimensional.proper 𝕜 (E →L[𝕜] E)
  (isCompact_closedBall 0 1).of_isClosed_subset isClosed_grassmannian
    fun _ hP ↦ mem_closedBall_zero_iff.mpr (norm_le_one_of_mem_grassmannian hP)

instance : CompactSpace (grassmannian 𝕜 E k) :=
  isCompact_iff_compactSpace.mp isCompact_grassmannian

/-- The tangential trace of an operator `A` along a plane `P ∈ G(E, k)` is bounded by `k ‖A‖`. -/
theorem norm_trace_comp_le_of_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k)
    (A : E →L[𝕜] E) : ‖LinearMap.trace 𝕜 E (P ∘L A : E →L[𝕜] E)‖ ≤ k * ‖A‖ := by
  rw [← traceCLM_apply]
  refine (P ∘L A).norm_traceCLM_le_finrank_range_mul.trans
    (mul_le_mul ?_ ?_ (norm_nonneg _) (Nat.cast_nonneg _))
  · rw [← finrank_range_of_mem_grassmannian hP]
    exact_mod_cast Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  · exact (P.opNorm_comp_le A).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_grassmannian hP))

/-- The passage to the orthogonal complement: `P ∈ G(E, k)` gives `1 - P ∈ G(E, l)` when
`k + l = dim E`. -/
theorem one_sub_mem_grassmannian (hP : P ∈ grassmannian 𝕜 E k) (hkl : k + l = finrank 𝕜 E) :
    1 - P ∈ grassmannian 𝕜 E l := by
  rw [mem_grassmannian_iff_trace] at hP ⊢
  refine ⟨hP.1.one_sub, ?_⟩
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one, map_sub,
    LinearMap.trace_one, hP.2, ← hkl, Nat.cast_add]
  ring

theorem one_sub_mem_grassmannian_iff (hkl : k + l = finrank 𝕜 E) :
    1 - P ∈ grassmannian 𝕜 E l ↔ P ∈ grassmannian 𝕜 E k :=
  ⟨fun h ↦ by simpa using one_sub_mem_grassmannian h (l := k) (by omega),
    fun h ↦ one_sub_mem_grassmannian h hkl⟩

omit [FiniteDimensional 𝕜 E] in
/-- The range of the complementary projection `1 - P` of a point `P` of `G(E, k)` is the orthogonal
complement of the range of `P`. -/
@[simp]
theorem range_one_sub_coe_grassmannian (P : grassmannian 𝕜 E k) :
    LinearMap.range (1 - ((P : E →L[𝕜] E) : E →ₗ[𝕜] E)) = (P : E →L[𝕜] E).rangeᗮ := by
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp P.2.1
  rw [h, Submodule.range_one_sub_starProjection, Submodule.range_starProjection]

/-- The passage to orthogonal complements `P ↦ 1 - P`, a homeomorphism from `G(E, k)` onto
`G(E, l)` when `k + l = dim E`: if `P` projects onto `S`, then `1 - P` projects onto `Sᗮ`
(Mathlib's `Submodule.starProjection_orthogonal'`). -/
noncomputable def grassmannianOrthogonalHomeomorph (hkl : k + l = finrank 𝕜 E) :
    grassmannian 𝕜 E k ≃ₜ grassmannian 𝕜 E l where
  toFun P := ⟨1 - P, one_sub_mem_grassmannian P.2 hkl⟩
  invFun Q := ⟨1 - Q, one_sub_mem_grassmannian Q.2 (by omega)⟩
  left_inv P := Subtype.ext (sub_sub_cancel 1 P.1)
  right_inv Q := Subtype.ext (sub_sub_cancel 1 Q.1)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.sub continuous_subtype_val).subtype_mk _

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

/-- `G(E, 0) = {0}`: the only projection of rank zero is `0`. -/
@[simp]
theorem grassmannian_zero : grassmannian 𝕜 E 0 = {0} := by
  ext P
  simp only [mem_singleton_iff, mem_grassmannian_iff_exists_starProjection,
    Submodule.finrank_eq_zero]
  constructor
  · rintro ⟨U, rfl, rfl⟩
    exact Submodule.starProjection_bot
  · rintro rfl
    exact ⟨⊥, rfl, Submodule.starProjection_bot.symm⟩

/-- `G(E, dim E) = {1}`: the only projection of full rank is the identity. -/
@[simp]
theorem grassmannian_finrank : grassmannian 𝕜 E (finrank 𝕜 E) = {1} := by
  ext P
  rw [mem_singleton_iff, ← one_sub_mem_grassmannian_iff (l := 0) (add_zero _), grassmannian_zero,
    mem_singleton_iff, sub_eq_zero, eq_comm]

/-- `G(E, k)` is empty for `k > dim E`: no subspace has dimension larger than `E`. -/
theorem grassmannian_eq_empty (hk : finrank 𝕜 E < k) : grassmannian 𝕜 E k = ∅ :=
  eq_empty_of_forall_notMem fun _ hP ↦ (finrank_range_of_mem_grassmannian hP ▸
    Submodule.finrank_le _).not_gt hk

end Euclidean

end TauCeti

namespace LinearIsometryEquiv

open TauCeti.Euclidean

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
  toFun P := ⟨U.conjStarAlgEquiv P, U.conjStarAlgEquiv_mem_grassmannian P.2⟩
  invFun Q := ⟨U.conjStarAlgEquiv.symm Q, U.symm.conjStarAlgEquiv_mem_grassmannian Q.2⟩
  left_inv P := Subtype.ext (U.conjStarAlgEquiv.symm_apply_apply P)
  right_inv Q := Subtype.ext (U.conjStarAlgEquiv.apply_symm_apply Q)
  continuous_toFun := (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
    continuous_subtype_val).subtype_mk _

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

namespace TauCeti

namespace finiteGrassmannian

open Euclidean

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-- The orthogonal projection onto a point of the finite Grassmannian, read in
`EuclideanSpace 𝕜 (Fin N)`, is a point of the projection Grassmannian. -/
theorem starProjection_toEuclidean_mem_grassmannian (V : finiteGrassmannian 𝕜 r N) :
    V.toEuclidean.starProjection ∈ grassmannian 𝕜 (EuclideanSpace 𝕜 (Fin N)) r := by
  simp

/-- Sending a subspace to its orthogonal projection is a bijection from the finite Grassmannian
onto the projection Grassmannian of `EuclideanSpace 𝕜 (Fin N)`. -/
theorem starProjection_toEuclidean_bijective :
    Function.Bijective fun V : finiteGrassmannian 𝕜 r N ↦
      (⟨V.toEuclidean.starProjection, V.starProjection_toEuclidean_mem_grassmannian⟩ :
        grassmannian 𝕜 (EuclideanSpace 𝕜 (Fin N)) r) := by
  refine ⟨fun V W h ↦ toEuclidean_injective ?_, fun P ↦ ?_⟩
  · simpa using congrArg (fun P : grassmannian 𝕜 (EuclideanSpace 𝕜 (Fin N)) r ↦
      (P : EuclideanSpace 𝕜 (Fin N) →L[𝕜] EuclideanSpace 𝕜 (Fin N)).range) h
  -- The preimage of `P` is its range, read in the coordinates `Fin N → 𝕜`.
  let V : finiteGrassmannian 𝕜 r N :=
    ⟨P.1.range.map (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, finrank_range_of_mem_grassmannian P.2]⟩
  have hV : V.toEuclidean = P.1.range := by
    ext x
    simp [V, Submodule.mem_map_equiv]
  refine ⟨V, Subtype.ext ?_⟩
  rw [ContinuousLinearMap.IsStarProjection.ext_iff isStarProjection_starProjection
    (isStarProjection_of_mem_grassmannian P.2), Submodule.range_starProjection, hV]

variable (𝕜 r N) in
/-- The finite Grassmannian `TauCeti.finiteGrassmannian 𝕜 r N` is homeomorphic to the projection
Grassmannian of `EuclideanSpace 𝕜 (Fin N)`, by sending a subspace to its orthogonal projection.
Composing with `LinearIsometryEquiv.grassmannianCongr` for a linear isometry equivalence
`e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin N)` identifies it with `G(E, r)` by `V ↦ e⁻¹ P_V e`. -/
noncomputable def starProjectionHomeomorph :
    finiteGrassmannian 𝕜 r N ≃ₜ grassmannian 𝕜 (EuclideanSpace 𝕜 (Fin N)) r :=
  -- A continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ starProjection_toEuclidean_bijective)
    (continuous_starProjection_toEuclidean.subtype_mk _)

@[simp]
theorem coe_starProjectionHomeomorph_apply (V : finiteGrassmannian 𝕜 r N) :
    (starProjectionHomeomorph 𝕜 r N V :
      EuclideanSpace 𝕜 (Fin N) →L[𝕜] EuclideanSpace 𝕜 (Fin N)) = V.toEuclidean.starProjection :=
  (rfl)

/-- The inverse of `TauCeti.finiteGrassmannian.starProjectionHomeomorph` sends a projection to
its range. -/
@[simp]
theorem toEuclidean_starProjectionHomeomorph_symm_apply
    (P : grassmannian 𝕜 (EuclideanSpace 𝕜 (Fin N)) r) :
    ((starProjectionHomeomorph 𝕜 r N).symm P).toEuclidean =
      (P : EuclideanSpace 𝕜 (Fin N) →L[𝕜] EuclideanSpace 𝕜 (Fin N)).range := by
  conv_rhs => rw [← (starProjectionHomeomorph 𝕜 r N).apply_symm_apply P]
  rw [coe_starProjectionHomeomorph_apply, Submodule.range_starProjection]

end finiteGrassmannian

end TauCeti
