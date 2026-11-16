/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.GDelta.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Smul
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.LinearAlgebra.Eigenspace.Det

/-!
# Generic operators have no power with the eigenvalue one

Let `E` be a finite-dimensional normed space over a complete nontrivially normed field `𝕜`, such
as `ℝ` or `ℂ`, and fix a continuous linear map `N : E → E`. This file shows that for generic
`G` no positive power of `N * G` has the eigenvalue `1`. For `N = 1` this is a statement about
generic operators `G`.

* For a fixed bound `k`, the maps `G` such that no power `(N * G) ^ m` with `0 < m ≤ k` has the
  eigenvalue `1` form an open dense set
  (`ContinuousLinearMap.isOpen_setOf_forall_le_not_hasEigenvalue_one_pow_mul`,
  `ContinuousLinearMap.dense_setOf_forall_le_not_hasEigenvalue_one_pow_mul`).
* The maps `G` such that no positive power of `N * G` has the eigenvalue `1` form a dense `Gδ`
  set, hence a residual one
  (`ContinuousLinearMap.dense_setOf_forall_not_hasEigenvalue_one_pow_mul`,
  `ContinuousLinearMap.isGδ_setOf_forall_not_hasEigenvalue_one_pow_mul`,
  `ContinuousLinearMap.setOf_forall_not_hasEigenvalue_one_pow_mul_mem_residual`).

Openness holds because a map has the eigenvalue `μ` exactly when `det (A - μ • 1) = 0`, and the
determinant is continuous. Density uses only rescalings: `N * (c • G) = c • (N * G)`, and by
`Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul` only countably many `c` give
`c • (N * G)` a positive power with the eigenvalue `1`. A countable subset of `𝕜` has dense
complement, so `G` is a limit of such rescalings `c • G` with `c → 1`.

This is the linear step of the Kupka–Smale theorem for closed orbits of vector fields. If `N` is
the linearized return map of a periodic orbit and a perturbation of the vector field in a flow box
along the orbit replaces it by `N * G`, the `m`-fold cover of the orbit is nondegenerate when
`(N * G) ^ m` has no eigenvalue `1`. Treating every cover is necessary: for `N = -1` no
eigenvalue is `1`, but `N ^ 2 = 1`. A perturbation of the vector field that dilates the
directions transverse to the orbit realizes the rescalings `G = c • 1`, and already for these
every cover becomes nondegenerate for all but countably many `c`.

## Main results

* `ContinuousLinearMap.isOpen_setOf_not_hasEigenvalue`: the maps without the eigenvalue `μ` form
  an open set.
* `ContinuousLinearMap.isOpen_setOf_forall_le_not_hasEigenvalue_one_pow_mul` and
  `ContinuousLinearMap.dense_setOf_forall_le_not_hasEigenvalue_one_pow_mul`: up to a bound on the
  power, the condition is open and dense.
* `ContinuousLinearMap.dense_setOf_forall_not_hasEigenvalue_one_pow_mul`,
  `ContinuousLinearMap.isGδ_setOf_forall_not_hasEigenvalue_one_pow_mul` and
  `ContinuousLinearMap.setOf_forall_not_hasEigenvalue_one_pow_mul_mem_residual`: for all powers,
  the condition is dense, `Gδ` and residual.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 3, §3.
-/

public section

open Module

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The continuous linear maps of a finite-dimensional space without the eigenvalue `μ` form an
open set. -/
theorem isOpen_setOf_not_hasEigenvalue (μ : 𝕜) :
    IsOpen {A : E →L[𝕜] E | ¬End.HasEigenvalue (A : E →ₗ[𝕜] E) μ} := by
  have h (A : E →L[𝕜] E) : End.HasEigenvalue (A : E →ₗ[𝕜] E) μ ↔ (A - μ • 1).det = 0 := by
    simp [End.hasEigenvalue_iff_det_sub_eq_zero, det]
  simp only [h]
  exact isOpen_ne_fun (continuous_det.comp (continuous_id.sub continuous_const)) continuous_const

/-- For a fixed `N` and a bound `k`, the continuous linear maps `G` such that no power
`(N * G) ^ m` with `0 < m ≤ k` has the eigenvalue `1` form an open set. -/
theorem isOpen_setOf_forall_le_not_hasEigenvalue_one_pow_mul (N : E →L[𝕜] E) (k : ℕ) :
    IsOpen {G : E →L[𝕜] E | ∀ m ≠ 0, m ≤ k →
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} := by
  have h : {G : E →L[𝕜] E | ∀ m ≠ 0, m ≤ k →
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} =
      ⋂ m ∈ Finset.range (k + 1), {G : E →L[𝕜] E | m ≠ 0 →
        ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} := by
    ext G
    simp only [Set.mem_ofPred, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
    exact forall_congr' fun m ↦ ⟨fun h hk hm ↦ h hm hk, fun h hm hk ↦ h hk hm⟩
  rw [h]
  refine isOpen_biInter_finset fun m _ ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simpa [hm] using (isOpen_setOf_not_hasEigenvalue (E := E) (1 : 𝕜)).preimage
      ((continuous_const.mul continuous_id).pow m)

/-- **Generic operators have no power with the eigenvalue one.** For a fixed continuous linear
map `N` of a finite-dimensional space over a complete field, the continuous linear maps `G` such
that no positive power of `N * G` has the eigenvalue `1` are dense. For every `G`, already the
rescalings `c • G` with this property accumulate at `G` as `c → 1`. -/
theorem dense_setOf_forall_not_hasEigenvalue_one_pow_mul (N : E →L[𝕜] E) :
    Dense {G : E →L[𝕜] E | ∀ m ≠ 0,
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} := by
  intro G
  -- Only countably many rescalings `c • (N * G) = N * (c • G)` are bad, so good ones accumulate
  -- at `c = 1`.
  have hB := End.countable_setOf_exists_hasEigenvalue_one_pow_smul
    ((N * G : E →L[𝕜] E) : E →ₗ[𝕜] E)
  have h1 : (1 : 𝕜) ∈ closure _ := hB.dense_compl 𝕜 1
  rw [← one_smul 𝕜 G]
  refine map_mem_closure (f := fun c : 𝕜 ↦ c • G) (by fun_prop) h1 fun c hc m hm h ↦
    hc ⟨m, hm, ?_⟩
  rwa [mul_smul_comm, toLinearMap_pow, toLinearMap_smul] at h

/-- For a fixed `N` and a bound `k`, the continuous linear maps `G` such that no power
`(N * G) ^ m` with `0 < m ≤ k` has the eigenvalue `1` are dense. -/
theorem dense_setOf_forall_le_not_hasEigenvalue_one_pow_mul (N : E →L[𝕜] E) (k : ℕ) :
    Dense {G : E →L[𝕜] E | ∀ m ≠ 0, m ≤ k →
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} :=
  Dense.mono (s₁ := {G : E →L[𝕜] E | ∀ m ≠ 0,
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1}) (fun _ hG m hm _ ↦ hG m hm)
    (dense_setOf_forall_not_hasEigenvalue_one_pow_mul N)

/-- For a fixed `N`, the continuous linear maps `G` such that no positive power of `N * G` has the
eigenvalue `1` form a `Gδ` set. -/
theorem isGδ_setOf_forall_not_hasEigenvalue_one_pow_mul (N : E →L[𝕜] E) :
    IsGδ {G : E →L[𝕜] E | ∀ m ≠ 0,
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} := by
  have h : {G : E →L[𝕜] E | ∀ m ≠ 0,
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} =
      ⋂ k, {G : E →L[𝕜] E | ∀ m ≠ 0, m ≤ k →
        ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} := by
    ext G
    simp only [Set.mem_ofPred, Set.mem_iInter]
    exact ⟨fun h _ m hm _ ↦ h m hm, fun h m hm ↦ h m m hm le_rfl⟩
  rw [h]
  exact .iInter_of_isOpen fun k ↦ isOpen_setOf_forall_le_not_hasEigenvalue_one_pow_mul N k

/-- For a fixed continuous linear map `N` of a finite-dimensional space over a complete field, a
generic continuous linear map `G`, in the sense of Baire category, makes no positive power of
`N * G` have the eigenvalue `1`. -/
theorem setOf_forall_not_hasEigenvalue_one_pow_mul_mem_residual (N : E →L[𝕜] E) :
    {G : E →L[𝕜] E | ∀ m ≠ 0,
      ¬End.HasEigenvalue (((N * G) ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) 1} ∈ residual (E →L[𝕜] E) :=
  residual_of_dense_Gδ (isGδ_setOf_forall_not_hasEigenvalue_one_pow_mul N)
    (dense_setOf_forall_not_hasEigenvalue_one_pow_mul N)

end ContinuousLinearMap
