/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Topology.Algebra.Module.Trace
public import TauCeti.Topology.Grassmannian.StarProjection

/-!
# Symmetries of the projection-form Grassmannian

This file collects the symmetry and coordinate statements about the Grassmannian
`G(E, k) = Euclidean.grassmannian E k` of a real inner product space, in its projection form,
that the Varifolds roadmap (`TauCetiRoadmap/Varifolds/README.md`, 1.1) records next to its
definition.

* The orthogonal group of `E`, as the unitary group `unitary (E →L[ℝ] E)`, acts on `G(E, k)` by
  `u • P = u P u*`, and the action is jointly continuous
  (`Euclidean.grassmannian.instMulActionUnitary`,
  `Euclidean.grassmannian.instContinuousSMulUnitary`). The plane of `u • P` is `u (range P)`.
* For an endomorphism `A` of `E`, the tangential trace `P ↦ tr (P ∘ A)` is
  continuous on `G(E, k)` (`Euclidean.grassmannian.continuous_trace_comp`).
* For `1 ≤ k ≤ dim F`, a subspace `S` of `F` contains the plane of every point of `G(F, k)` only
  when `S = F` (`Euclidean.grassmannian.forall_range_le_iff_eq_top`). For a linear isometry
  `U : E → F`, the points of `G(F, k)` whose plane lies in `range U` are therefore all of
  `G(F, k)` exactly when `U` is surjective
  (`LinearIsometry.forall_range_le_range_iff_surjective`). For `k = 0` this fails: `G(F, 0)` is
  `{0}`, whose plane lies in every subspace.
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
  rfl

/-- The orthogonal group of `E` acts continuously on `G(E, k)`: the conjugation
`(u, P) ↦ u P u*` is jointly continuous. -/
instance instContinuousSMulUnitary :
    ContinuousSMul (unitary (E →L[ℝ] E)) (grassmannian E k) where
  continuous_smul := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun p : unitary (E →L[ℝ] E) × grassmannian E k ↦
      (p.1 : E →L[ℝ] E) * p.2 * star (p.1 : E →L[ℝ] E)
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
  · have h : LinearMap.trace ℝ E = 0 := by
      rw [LinearMap.trace, dite_eq_right]
      rintro ⟨s, ⟨b⟩⟩
      exact hE (Module.Finite.of_basis b)
    simpa only [h, LinearMap.zero_apply] using continuous_const

section RangeLe

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- In a finite-dimensional space, a nonzero vector `v` lies in a `k`-dimensional subspace for
each `1 ≤ k ≤ dim F`. -/
private theorem exists_finrank_eq_and_mem [FiniteDimensional ℝ F] {v : F} (hv : v ≠ 0) (hk : k ≠ 0)
    (hkF : k ≤ finrank ℝ F) : ∃ S : Submodule ℝ F, finrank ℝ S = k ∧ v ∈ S := by
  set W := (ℝ ∙ v)ᗮ
  have hW : finrank ℝ W + 1 = finrank ℝ F := by
    rw [← (ℝ ∙ v).finrank_add_finrank_orthogonal, finrank_span_singleton hv, add_comm]
  have hle : k - 1 ≤ finrank ℝ W := by omega
  let b := Module.finBasis ℝ W
  let f : Fin (k - 1) → F := fun i ↦ b (Fin.castLE hle i)
  have hf : LinearIndependent ℝ f :=
    (b.linearIndependent.comp _ (Fin.castLE_injective hle)).map' W.subtype W.ker_subtype
  set T := Submodule.span ℝ (Set.range f)
  have hT : finrank ℝ T = k - 1 := by
    rw [finrank_span_eq_card hf, Fintype.card_fin]
  have hTW : T ≤ W := Submodule.span_le.2 <| Set.range_subset_iff.2 fun i ↦ (b _).property
  have hinf : (ℝ ∙ v) ⊓ T = ⊥ :=
    eq_bot_iff.2 <| (inf_le_inf_left _ hTW).trans (ℝ ∙ v).inf_orthogonal_eq_bot.le
  refine ⟨(ℝ ∙ v) ⊔ T, ?_, Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ v) T
  rw [hinf, finrank_bot, finrank_span_singleton hv, hT] at h
  omega

/-- For `1 ≤ k ≤ dim F`, a subspace `S` of `F` contains the plane of every point of `G(F, k)`
only when `S` is all of `F`. -/
theorem forall_range_le_iff_eq_top [CompleteSpace F] {S : Submodule ℝ F} (hk : k ≠ 0)
    (hkF : k ≤ finrank ℝ F) :
    (∀ Q : grassmannian F k, (Q : F →L[ℝ] F).range ≤ S) ↔ S = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ h ▸ le_top⟩
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  by_contra hS
  obtain ⟨v, -, hvS⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hS)
  have hv : v ≠ 0 := fun hv ↦ hvS (hv ▸ S.zero_mem)
  obtain ⟨T, hT, hvT⟩ := exists_finrank_eq_and_mem hv hk hkF
  refine hvS <| h ⟨T.starProjection, starProjection_mem hT⟩ ?_
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
    ← Submodule.map_comp]
  rfl

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
  have hS : S.toEuclidean =
      (X : E →L[ℝ] E).range.map ((e.trans O).toLinearEquiv : E →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
    rw [← toEuclidean_finiteGrassmannianHomeomorph_symm, Homeomorph.symm_apply_apply]
  rw [← (finiteGrassmannianHomeomorph k e).apply_symm_apply X]
  refine congrArg _ (finiteGrassmannian.toEuclidean_injective ?_)
  rw [h, hS, toEuclidean_finiteGrassmannianHomeomorph_symm, ← Submodule.map_comp]
  congr 1
  ext x
  simp

end ChangeOfCoordinates

end grassmannian

end Euclidean

namespace LinearIsometry

open Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- For `1 ≤ k ≤ dim F` and a linear isometry `U : E → F`, the plane of every point of
`G(F, k)` lies in `range U` exactly when `U` is surjective. -/
theorem forall_range_le_range_iff_surjective (U : E →ₗᵢ[ℝ] F) (hk : k ≠ 0)
    (hkF : k ≤ finrank ℝ F) :
    (∀ Q : grassmannian F k, (Q : F →L[ℝ] F).range ≤ LinearMap.range U.toLinearMap) ↔
      Function.Surjective U := by
  rw [grassmannian.forall_range_le_iff_eq_top hk hkF, LinearMap.range_eq_top]
  rfl

end LinearIsometry
