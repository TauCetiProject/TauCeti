/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.SpecialLinear.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.Stabilizer
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.NilpotentOrbitFinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Coadjoint orbits of the real special linear group

Let `G = SL(n, ℝ)` with its native Lie group structure and tangent Lie algebra
`𝔤 = GroupLieAlgebra 𝓘(ℝ, Model n ℝ) G`. The differential at the identity of the matrix inclusion
identifies `𝔤` with the trace-zero matrices
(`Matrix.SpecialLinearGroup.range_mvfderiv_subtypeVal_one`) and carries the adjoint action to
conjugation (`Matrix.SpecialLinearGroup.mvfderiv_subtypeVal_adjointContinuousLinearMap`).

Pairing through the trace form, a matrix `Y` gives the covector `ν_Y(ξ) = tr(Y X_ξ)` on `𝔤`,
where `X_ξ` is the matrix of `ξ` (`Matrix.SpecialLinearGroup.tracePairing`). The trace form is
invariant, so the coadjoint action becomes conjugation as well, `Ad*_g ν_Y = ν_(g Y g⁻¹)`
(`Matrix.SpecialLinearGroup.coadjointRepresentation_tracePairing`), and the trace form is
nondegenerate on trace-zero matrices, since `tr(Y Yᵀ)` is the sum of the squares of the entries of
`Y`. So `Y ↦ ν_Y` identifies the trace-zero matrices with `𝔤*`
(`Matrix.SpecialLinearGroup.tracePairingEquiv`), and every coadjoint orbit is the image of an orbit
of conjugation (`Matrix.SpecialLinearGroup.range_orbitMap_coadjointRepresentation_tracePairing`).

For `SL(2, ℝ)` and the nilpotent matrix `E = [[0, 1], [0, 0]]` (`Matrix.single 0 1 1`), the
conjugation orbit of `E` is one half of the punctured nilpotent cone
`{Y | tr Y = 0, det Y = 0, Y ≠ 0}`, the half with `Y₀₁ ≥ 0 ≥ Y₁₀`
(`Matrix.SpecialLinearGroup.range_coe_mul_single_mul_coe_inv`), and the orbit of `-E` is the
other half. Accordingly the coadjoint orbits of `ν_E` and of `-ν_E` are disjoint and
their union is the image of the punctured nilpotent cone
(`Matrix.SpecialLinearGroup.range_orbitMap_coadjointRepresentation_tracePairing_single_union`,
`Matrix.SpecialLinearGroup.disjoint_range_orbitMap_coadjointRepresentation_tracePairing_single`).

The coadjoint orbit of `ν_E` is not closed. Conjugation by `diag(t, t⁻¹)` scales `E` by `t²`, so
`t² ν_E` lies on the orbit for every `t ≠ 0` and tends to `0` as `t → 0`, while `0` does not lie on
the orbit. Reading covectors in the continuous dual `StrongDual ℝ 𝔤`, the image of the orbit map
`ι_ν : G ⧸ G_ν → 𝔤*` of `ν = ν_E` has `0` in its closure and is not closed. So, for a noncompact
group, the injective orbit map `ι_ν` need not have closed image.

## Main definitions

All declarations are in the namespace `Matrix.SpecialLinearGroup`.

* `tracePairing`: the covector `ξ ↦ tr(Y X_ξ)` of a matrix `Y`.
* `tracePairingEquiv`: the trace form identifies the trace-zero matrices with `𝔤*`.

## Main results

* `coadjointRepresentation_tracePairing`: `Ad*_g ν_Y = ν_(g Y g⁻¹)`.
* `range_orbitMap_coadjointRepresentation_tracePairing_single`: the coadjoint orbit of `ν_E` in
  `SL(2, ℝ)` is the image of one half of the punctured nilpotent cone.
* `not_isClosed_range_orbitMap_coadjointRepresentation_tracePairing_single`: the coadjoint orbit
  of `ν_E` is not closed in `𝔤*`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

noncomputable section

open Filter Matrix Manifold Topology TauCeti TauCeti.Lie
open scoped Manifold ContDiff MatrixGroups Matrix.Norms.Operator

namespace Matrix.SpecialLinearGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-! ### The trace form -/

section TracePairing

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "𝔤" n => GroupLieAlgebra 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ)

variable (n) in
/-- The covector `ξ ↦ tr(Y X_ξ)` on the Lie algebra of `SL(n, ℝ)` given by a matrix `Y`, where
`X_ξ` is the matrix of `ξ` under the differential of the matrix inclusion at the identity. -/
def tracePairing : Matrix n n ℝ →ₗ[ℝ] Module.Dual ℝ (𝔤 n) :=
  ((LinearMap.mul ℝ (Matrix n n ℝ)).compr₂ (traceLinearMap n ℝ ℝ)).compl₂
    (mvfderiv 𝓘(ℝ, Model n ℝ) (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1 :
      (𝔤 n) →ₗ[ℝ] Matrix n n ℝ)

@[simp]
theorem tracePairing_apply (Y : Matrix n n ℝ) (ξ : 𝔤 n) :
    tracePairing n Y ξ = (Y * mvfderiv 𝓘(ℝ, Model n ℝ)
      (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1 ξ).trace :=
  (rfl)

/-- **The trace form is invariant**: the coadjoint action on `ν_Y` is conjugation of `Y`,
`Ad*_g ν_Y = ν_(g Y g⁻¹)`. -/
@[simp]
theorem coadjointRepresentation_tracePairing (g : SpecialLinearGroup n ℝ) (Y : Matrix n n ℝ) :
    coadjointRepresentation ℝ 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ) g (tracePairing n Y) =
      tracePairing n
        ((g : Matrix n n ℝ) * Y * ((g⁻¹ : SpecialLinearGroup n ℝ) : Matrix n n ℝ)) := by
  ext ξ
  rw [coadjointRepresentation_apply, tracePairing_apply, tracePairing_apply,
    mvfderiv_subtypeVal_adjointContinuousLinearMap, inv_inv]
  -- Cyclicity of the trace: `tr(g (Y g⁻¹ X)) = tr((Y g⁻¹ X) g)`.
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm (g : Matrix n n ℝ)]
  simp only [Matrix.mul_assoc]

/-- The trace form is nondegenerate on trace-zero matrices: such a matrix `Y` gives the zero
covector only when `Y = 0`. -/
theorem tracePairing_eq_zero_iff {Y : Matrix n n ℝ} (hY : Y.trace = 0) :
    tracePairing n Y = 0 ↔ Y = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  -- Pair `Y` with the matrix of a Lie algebra element whose matrix is `Yᵀ`.
  obtain ⟨ξ, hξ⟩ : Yᵀ ∈ (mvfderiv 𝓘(ℝ, Model n ℝ)
      (fun A : SpecialLinearGroup n ℝ ↦ (A : Matrix n n ℝ)) 1).range := by
    rw [range_mvfderiv_subtypeVal_one]
    simpa using hY
  have hYY := LinearMap.congr_fun h ξ
  rw [ContinuousLinearMap.coe_coe] at hξ
  rw [tracePairing_apply, hξ, LinearMap.zero_apply, ← conjTranspose_eq_transpose_of_trivial] at hYY
  exact trace_mul_conjTranspose_self_eq_zero_iff.mp hYY

/-- Distinct trace-zero matrices give distinct covectors. -/
theorem injOn_tracePairing : Set.InjOn (tracePairing n) {Y | Y.trace = 0} := by
  intro Y hY Y' hY' h
  rw [← sub_eq_zero, ← tracePairing_eq_zero_iff (by simp [trace_sub, hY.out, hY'.out]), map_sub, h,
    sub_self]

variable (n) in
/-- The trace form identifies the trace-zero matrices with the dual of the Lie algebra of
`SL(n, ℝ)`, by `Y ↦ (ξ ↦ tr(Y X_ξ))`. -/
def tracePairingEquiv : LinearMap.ker (traceLinearMap n ℝ ℝ) ≃ₗ[ℝ] Module.Dual ℝ (𝔤 n) :=
  LinearEquiv.ofBijective ((tracePairing n).domRestrict _) <| by
    have hinj : Function.Injective
        ((tracePairing n).domRestrict (LinearMap.ker (traceLinearMap n ℝ ℝ))) := fun Y Y' h ↦
      Subtype.ext (injOn_tracePairing (LinearMap.mem_ker.mp Y.property)
        (LinearMap.mem_ker.mp Y'.property) h)
    refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
    rw [Subspace.dual_finrank_eq, ← range_mvfderiv_subtypeVal_one,
      LinearMap.finrank_range_of_inj (injective_mvfderiv_subtypeVal 1)]

@[simp]
theorem tracePairingEquiv_apply (Y : LinearMap.ker (traceLinearMap n ℝ ℝ)) :
    tracePairingEquiv n Y = tracePairing n Y :=
  (rfl)

/-- The coadjoint orbit of `ν_(Y₀)` is the image of the conjugation orbit of `Y₀`. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing (Y₀ : Matrix n n ℝ) :
    Set.range (Representation.orbitMap
        (coadjointRepresentation ℝ 𝓘(ℝ, Model n ℝ) (SpecialLinearGroup n ℝ)) (tracePairing n Y₀)) =
      tracePairing n '' Set.range (fun g : SpecialLinearGroup n ℝ ↦
        (g : Matrix n n ℝ) * Y₀ * ((g⁻¹ : SpecialLinearGroup n ℝ) : Matrix n n ℝ)) := by
  rw [Representation.range_orbitMap, ← Set.range_comp]
  exact congrArg Set.range (funext fun g ↦ coadjointRepresentation_tracePairing g Y₀)

end TracePairing

/-! ### The nilpotent orbits of `SL(2, ℝ)` -/

section Nilpotent

local notation "𝔰𝔩₂" => GroupLieAlgebra 𝓘(ℝ, Model (Fin 2) ℝ) SL(2, ℝ)
local notation "Ad*" => coadjointRepresentation ℝ 𝓘(ℝ, Model (Fin 2) ℝ) SL(2, ℝ)

/-- **The coadjoint orbit of `ν_E` in `SL(2, ℝ)`**, for `E = [[0, 1], [0, 0]]`, is the image of one
half of the punctured nilpotent cone under the trace form. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing_single :
    Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0} := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing, range_coe_mul_single_mul_coe_inv]

/-- The coadjoint orbit of `-ν_E` in `SL(2, ℝ)` is the image of the other half of the punctured
nilpotent cone. -/
theorem range_orbitMap_coadjointRepresentation_neg_tracePairing_single :
    Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  rw [← map_neg, range_orbitMap_coadjointRepresentation_tracePairing,
    range_coe_mul_neg_single_mul_coe_inv]

/-- The coadjoint orbits of `ν_E` and `-ν_E` in `SL(2, ℝ)` together make up the image of the
punctured nilpotent cone under the trace form. -/
theorem range_orbitMap_coadjointRepresentation_tracePairing_single_union :
    Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) ∪
        Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1))) =
      tracePairing (Fin 2) '' {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0} := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single,
    range_orbitMap_coadjointRepresentation_neg_tracePairing_single, ← Set.image_union,
    setOf_trace_eq_zero_det_eq_zero_ne_zero_eq_union]

/-- The coadjoint orbits of `ν_E` and `-ν_E` in `SL(2, ℝ)` are disjoint: each is one half of the
punctured nilpotent cone. -/
theorem disjoint_range_orbitMap_coadjointRepresentation_tracePairing_single :
    Disjoint (Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))))
      (Set.range (Representation.orbitMap Ad* (-tracePairing (Fin 2) (single 0 1 1)))) := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single,
    range_orbitMap_coadjointRepresentation_neg_tracePairing_single]
  exact disjoint_setOf_trace_eq_zero_det_eq_zero_ne_zero.image injOn_tracePairing (fun Y hY ↦ hY.1)
    fun Y hY ↦ hY.1

/-- The zero covector does not lie on the coadjoint orbit of `ν_E` in `SL(2, ℝ)`. -/
theorem zero_notMem_range_orbitMap_coadjointRepresentation_tracePairing_single :
    0 ∉ Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) := by
  rw [range_orbitMap_coadjointRepresentation_tracePairing_single]
  rintro ⟨Y, hY, h0⟩
  exact hY.2.2.1 ((tracePairing_eq_zero_iff hY.1).mp h0)

/-- The zero covector lies in the closure of the coadjoint orbit of `ν_E` in `SL(2, ℝ)`, read in
the continuous dual: the orbit contains `t² ν_E` for every `t ≠ 0`. -/
theorem zero_mem_closure_range_orbitMap_coadjointRepresentation_tracePairing_single :
    (0 : StrongDual ℝ 𝔰𝔩₂) ∈ closure (LinearMap.toContinuousLinearMap ''
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1)))) := by
  have hmem (t : ℝ) (ht : t ≠ 0) : t ^ 2 • tracePairing (Fin 2) (single 0 1 1) ∈
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) := by
    rw [range_orbitMap_coadjointRepresentation_tracePairing_single, ← map_smul]
    refine Set.mem_image_of_mem _ ⟨by simp, by simp [det_fin_two], ?_, by simp [sq_nonneg],
      by simp⟩
    exact fun h ↦ pow_ne_zero 2 ht (by simpa using congrFun (congrFun h 0) 1)
  refine mem_closure_of_tendsto (b := 𝓝[≠] (0 : ℝ))
    (f := fun t : ℝ ↦ t ^ 2 • LinearMap.toContinuousLinearMap (tracePairing (Fin 2) (single 0 1 1)))
    ?_ ?_
  · have hc : Continuous fun t : ℝ ↦
        t ^ 2 • LinearMap.toContinuousLinearMap (tracePairing (Fin 2) (single 0 1 1)) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨_, hmem t ht, map_smul _ _ _⟩

/-- **The coadjoint orbit of `ν_E` in `SL(2, ℝ)` is not closed**, for `E = [[0, 1], [0, 0]]`.
The image of the orbit map `G ⧸ G_ν → 𝔤*` of `ν = ν_E`, read in the continuous dual, is not
closed. -/
theorem not_isClosed_range_orbitMap_coadjointRepresentation_tracePairing_single :
    ¬ IsClosed (LinearMap.toContinuousLinearMap ''
      Set.range (Representation.orbitMap Ad* (tracePairing (Fin 2) (single 0 1 1))) :
        Set (StrongDual ℝ 𝔰𝔩₂)) := by
  intro h
  obtain ⟨ν, hν, h0⟩ := h.closure_eq ▸
    zero_mem_closure_range_orbitMap_coadjointRepresentation_tracePairing_single
  rw [LinearEquiv.map_eq_zero_iff] at h0
  exact zero_notMem_range_orbitMap_coadjointRepresentation_tracePairing_single (h0 ▸ hν)

end Nilpotent

end Matrix.SpecialLinearGroup
