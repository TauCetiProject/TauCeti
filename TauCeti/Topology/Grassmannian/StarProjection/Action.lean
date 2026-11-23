/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Topology.Algebra.Module.Trace
public import TauCeti.Topology.Grassmannian.StarProjection.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Symmetries of the projection-form Grassmannian

This file collects symmetry, continuity and coordinate statements about the Grassmannian
`G(E, k) = Euclidean.grassmannian E k` of a real inner product space, in its projection form.
They are what a theory of varifolds, measures on `E × G(E, k)`, needs from `G(E, k)`: the
orthogonal group moves varifolds by acting on both factors, the tangential trace `tr (P ∘ A)` is
the integrand of the first variation, so its continuity makes the first variation a continuous
functional of the varifold, and orthonormal coordinates may be changed without changing the
topology of `G(E, k)`.

* The orthogonal group of `E`, as the unitary group `unitary (E →L[ℝ] E)`, acts on `G(E, k)` by
  `u • P = u P u*`, and the action is jointly continuous
  (`Euclidean.grassmannian.instMulActionUnitary`,
  `Euclidean.grassmannian.instContinuousSMulUnitary`). The plane of `u • P` is `u (range P)`.
* For an endomorphism `A` of `E`, the tangential trace `P ↦ tr (P ∘ A)` is
  continuous on `G(E, k)` (`Euclidean.grassmannian.continuous_trace_comp`).
* For `1 ≤ k ≤ rank F` (the rank may be infinite), a subspace `S` of `F` contains the plane of
  every point of `G(F, k)` only when `S = F`
  (`Euclidean.grassmannian.forall_range_le_iff_eq_top`). For a linear isometry `U : E → F`, the
  points of `G(F, k)` whose plane lies in `range U` are therefore all of `G(F, k)` exactly when
  `U` is surjective (`LinearIsometry.forall_range_le_range_iff_surjective`). For `k = 0` this
  fails: `G(F, 0)` is `{0}`, whose plane lies in every subspace.
* Changing the coordinates `e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` to `O ∘ e`, for an orthogonal
  map `O` of `EuclideanSpace ℝ (Fin N)`, precomposes the comparison homeomorphism
  `Euclidean.grassmannian.finiteGrassmannianHomeomorph` with `S ↦ O⁻¹(S)`
  (`Euclidean.grassmannian.finiteGrassmannianHomeomorph_trans_apply`) and postcomposes its
  inverse with `S ↦ O(S)`
  (`Euclidean.grassmannian.toEuclidean_finiteGrassmannianHomeomorph_trans_symm`).

The `k`-planes of `E` as orthogonal projections follow L. Simon, *Lectures on Geometric Measure
Theory*, §38.
-/

public section

open Module

namespace Euclidean

namespace grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

section Unitary

variable [CompleteSpace E]

/-- Conjugating a point `P` of `G(E, k)` by a unitary `u` gives the point `u P u*` of `G(E, k)`. -/
theorem mul_mul_star_mem {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k)
    (u : unitary (E →L[ℝ] E)) : (u : E →L[ℝ] E) * P * star (u : E →L[ℝ] E) ∈ grassmannian E k := by
  rw [← Unitary.conjStarAlgAut_apply (S := ℝ),
    ← Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv]
  refine mem_grassmannian.2 ⟨(isStarProjection hP).map _, ?_⟩
  rw [LinearIsometryEquiv.range_conjStarAlgEquiv,
    rank_map_eq (LinearEquiv.injective _), (mem_grassmannian.1 hP).2]

/-- A unitary `u` of `E →L[ℝ] E` moves a point `P` of `G(E, k)` to its conjugate `u P u*`. -/
noncomputable instance instSMulUnitary : SMul (unitary (E →L[ℝ] E)) (grassmannian E k) where
  smul u P := ⟨(u : E →L[ℝ] E) * P * star (u : E →L[ℝ] E), mul_mul_star_mem P.property u⟩

/-- The action of a unitary `u` on `G(E, k)` is conjugation, `u • P = u P u*`. -/
@[simp]
theorem coe_smul (u : unitary (E →L[ℝ] E)) (P : grassmannian E k) :
    ((u • P : grassmannian E k) : E →L[ℝ] E) =
      (u : E →L[ℝ] E) * P * star (u : E →L[ℝ] E) :=
  (rfl)

/-- The orthogonal group of `E`, as the unitary group of `E →L[ℝ] E`, acts on `G(E, k)` by
conjugation, `u • P = u P u*`. -/
noncomputable instance instMulActionUnitary :
    MulAction (unitary (E →L[ℝ] E)) (grassmannian E k) where
  one_smul P := Subtype.ext <| by simp
  mul_smul u v P := Subtype.ext <| by simp [star_mul, mul_assoc]

/-- The plane of `u • P` is the image of the plane of `P` under `u`. -/
theorem range_coe_smul (u : unitary (E →L[ℝ] E)) (P : grassmannian E k) :
    ((u • P : grassmannian E k) : E →L[ℝ] E).range =
      (P : E →L[ℝ] E).range.map (u : E →L[ℝ] E).toLinearMap := by
  rw [coe_smul, ← Unitary.conjStarAlgAut_apply (S := ℝ),
    ← Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv,
    LinearIsometryEquiv.range_conjStarAlgEquiv]
  exact congrArg (Submodule.map · _) <| LinearMap.ext fun x ↦
    DFunLike.congr_fun (Unitary.coe_linearIsometryEquiv_apply u) x

/-- The orthogonal group of `E` acts continuously on `G(E, k)`: the conjugation
`(u, P) ↦ u P u*` is jointly continuous. -/
instance instContinuousSMulUnitary :
    ContinuousSMul (unitary (E →L[ℝ] E)) (grassmannian E k) where
  continuous_smul := by
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, coe_smul]
    fun_prop

end Unitary

/-- For an endomorphism `A` of `E`, the tangential trace `P ↦ tr (P ∘ A)` is continuous on
`G(E, k)`; it is the restriction of a linear functional of `P`. When `E` is
infinite-dimensional, `LinearMap.trace` is the zero map. -/
theorem continuous_trace_comp [CompleteSpace E] (A : E →L[ℝ] E) :
    Continuous fun P : grassmannian E k ↦
      LinearMap.trace ℝ E ((P : E →L[ℝ] E) ∘L A : E →L[ℝ] E) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact ((TauCeti.traceCLM ℝ E).continuous.comp
      (continuous_subtypeVal.clm_comp continuous_const)).congr fun _ ↦ TauCeti.traceCLM_apply _
  · simpa only [TauCeti.LinearMap.trace_eq_zero_of_not_finite hE, LinearMap.zero_apply] using
      continuous_const

section RangeLe

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- For `1 ≤ k ≤ rank F`, a subspace `S` of `F` contains the plane of every point of `G(F, k)`
only when `S` is all of `F`. The rank of `F` may be infinite. -/
theorem forall_range_le_iff_eq_top [CompleteSpace F] {S : Submodule ℝ F} (hk : k ≠ 0)
    (hkF : (k : Cardinal) ≤ Module.rank ℝ F) :
    (∀ Q : grassmannian F k, (Q : F →L[ℝ] F).range ≤ S) ↔ S = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ h ▸ le_top⟩
  by_contra hS
  obtain ⟨v, -, hvS⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hS)
  have hv : v ≠ 0 := fun hv ↦ hvS (hv ▸ S.zero_mem)
  obtain ⟨T, hvT, hT⟩ := Submodule.exists_mem_rank_eq hv hk hkF
  have : FiniteDimensional ℝ T := Module.finite_of_rank_eq_nat hT
  refine hvS <| h ⟨T.starProjection, starProjection_mem (finrank_eq_of_rank_eq hT)⟩ ?_
  rwa [Submodule.range_starProjection]

end RangeLe

section ChangeOfCoordinates

open TauCeti

variable [CompleteSpace E] {N : ℕ}

/-- Changing the coordinates `e` to `O ∘ e`, for a linear isometry `O` of
`EuclideanSpace ℝ (Fin N)`, postcomposes the inverse of `finiteGrassmannianHomeomorph k e` with
`S ↦ O(S)`, read in coordinates. -/
theorem toEuclidean_finiteGrassmannianHomeomorph_trans_symm
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (O : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) (P : grassmannian E k) :
    ((finiteGrassmannianHomeomorph k (e.trans O)).symm P).toEuclidean =
      ((finiteGrassmannianHomeomorph k e).symm P).toEuclidean.map
        (O.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
  rw [toEuclidean_finiteGrassmannianHomeomorph_symm, toEuclidean_finiteGrassmannianHomeomorph_symm,
    ← Submodule.map_comp, LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.coe_trans]

/-- Changing the coordinates `e` to `O ∘ e`, for a linear isometry `O` of
`EuclideanSpace ℝ (Fin N)`, precomposes `finiteGrassmannianHomeomorph k e` with `S ↦ O⁻¹(S)`,
read in coordinates: if `T` is the plane `O⁻¹(S)`, then the two homeomorphisms send `S` and `T`
to the same point. -/
theorem finiteGrassmannianHomeomorph_trans_apply (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (O : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    {S T : finiteGrassmannian ℝ k N}
    (h : T.toEuclidean = S.toEuclidean.map
      (O.symm.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) :
    finiteGrassmannianHomeomorph k (e.trans O) S = finiteGrassmannianHomeomorph k e T := by
  set X := finiteGrassmannianHomeomorph k (e.trans O) S
  rw [← (finiteGrassmannianHomeomorph k e).apply_symm_apply X]
  refine congrArg _ (finiteGrassmannian.toEuclidean_injective ?_)
  rw [eq_comm, h, LinearIsometryEquiv.toLinearEquiv_symm, Submodule.map_symm_eq_iff,
    ← toEuclidean_finiteGrassmannianHomeomorph_trans_symm, Homeomorph.symm_apply_apply]

end ChangeOfCoordinates

end grassmannian

end Euclidean

namespace LinearIsometry

open Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- For `1 ≤ k ≤ rank F` and a linear isometry `U : E → F`, the plane of every point of
`G(F, k)` lies in `range U` exactly when `U` is surjective. The rank of `F` may be infinite. -/
theorem forall_range_le_range_iff_surjective (U : E →ₗᵢ[ℝ] F) (hk : k ≠ 0)
    (hkF : (k : Cardinal) ≤ Module.rank ℝ F) :
    (∀ Q : grassmannian F k, (Q : F →L[ℝ] F).range ≤ LinearMap.range U.toLinearMap) ↔
      Function.Surjective U := by
  rw [grassmannian.forall_range_le_iff_eq_top hk hkF, LinearMap.range_eq_top,
    LinearIsometry.coe_toLinearMap]

end LinearIsometry
