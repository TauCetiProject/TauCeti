/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# Changing the inner product by the inverse square root

Let `E` be a real Hilbert space with inner product `⟪·, ·⟫`, and let `h : E →L[ℝ] E →L[ℝ] ℝ` be a
second inner product on `E`, given as a bounded bilinear form, as the fibrewise inner products of a
Riemannian vector bundle are. The Riesz representation turns `h` into the operator
`H = InnerProductSpace.continuousLinearMapOfBilin h`, characterized by `⟪H u, v⟫ = h u v`. When
`H` is strictly positive (in finite dimension: exactly when `h` is symmetric and positive definite)
the inverse square root

`h.metricChangeTransport = H ^ (-(1 / 2))`

of the continuous functional calculus is an isometry from `(E, ⟪·, ·⟫)` to `(E, h)`. It therefore
carries orthonormal frames for the original inner product to orthonormal frames for `h`, and its
inverse, the square root `CFC.sqrt H`, carries `h`-orthonormal frames back.

Unlike the eigenbasis construction of `TauCeti.exists_continuousLinearEquiv_inner_map_map`, this
transport involves no choice. It is characterized as the unique positive operator `S` with
`S * H * S = 1`, and it is natural: pulling `h` back along a linear isometry equivalence `e`
conjugates the transport by `e`. When `E` is finite-dimensional, every other isometry from
`(E, ⟪·, ·⟫)` to `(E, h)` is the transport composed with an orthogonal automorphism of `E`. This
classification is the tool for comparing the composite of the transports of two successive changes
of inner product with the transport of the composite change; that comparison is not formalized
here, since every result in this file is relative to the fixed inner product of `E`.

## Main declarations

* `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff`: in finite dimension,
  the Riesz operator of `h` is strictly positive exactly when `h` is symmetric and positive
  definite.
* `ContinuousLinearMap.metricChangeTransport`: the inverse square root of the Riesz operator.
* `ContinuousLinearMap.metricChangeTransport_eq_iff`: it is the unique positive `S` with
  `S * H * S = 1`.
* `ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport`: it is an isometry from
  `⟪·, ·⟫` to `h`; `ContinuousLinearMap.apply_metricChangeTransport_of_orthonormal` is the frame
  version.
* `ContinuousLinearMap.inner_sqrt_apply_sqrt_apply`, `ContinuousLinearMap.orthonormal_sqrt_apply`:
  the inverse transport `CFC.sqrt H` is an isometry from `h` back to `⟪·, ·⟫`.
* `ContinuousLinearMap.metricChangeTransport_bilinearComp`: naturality under linear isometry
  equivalences.
* `ContinuousLinearMap.forall_apply_apply_eq_inner_iff_exists_linearIsometryEquiv`: in finite
  dimension, the isometries from `⟪·, ·⟫` to `h` are exactly the transport composed with
  orthogonal automorphisms.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles and their orthonormal frames).
-/

public section

open InnerProductSpace
open scoped InnerProductSpace

/-- The Riesz operator of a real bilinear form, written as Mathlib's `InnerProductSpace.Dual`
writes it. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-- The **metric change transport** of a second inner product `h` on a real Hilbert space: the
inverse square root `H ^ (-(1 / 2))` of its Riesz operator `H`, characterized by
`⟪H u, v⟫ = h u v`. When `H` is strictly positive it is an isometry from the original inner
product to `h` (`ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport`). -/
noncomputable def metricChangeTransport (h : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  h♯ ^ (-(1 / 2) : ℝ)

theorem metricChangeTransport_def (h : E →L[ℝ] E →L[ℝ] ℝ) :
    h.metricChangeTransport = h♯ ^ (-(1 / 2) : ℝ) := (rfl)

variable {h : E →L[ℝ] E →L[ℝ] ℝ}

/-- The metric change transport is strictly positive. -/
theorem isStrictlyPositive_metricChangeTransport (hH : IsStrictlyPositive h♯) :
    IsStrictlyPositive h.metricChangeTransport :=
  metricChangeTransport_def h ▸ IsStrictlyPositive.rpow _ _ hH

/-- The defining identity of the metric change transport `T`: `T * H * T = 1` for the Riesz
operator `H` of `h`. -/
theorem metricChangeTransport_mul_mul_self (hH : IsStrictlyPositive h♯) :
    h.metricChangeTransport * h♯ * h.metricChangeTransport = 1 := by
  have hTH : h.metricChangeTransport * h♯ = h♯ ^ (1 / 2 : ℝ) := by
    conv_lhs => rhs; rw [← CFC.rpow_one h♯ hH.nonneg]
    rw [metricChangeTransport_def, ← CFC.rpow_add hH.isUnit]
    norm_num
  rw [hTH, metricChangeTransport_def, CFC.rpow_mul_rpow_neg]

/-- The metric change transport is the unique positive operator `S` with `S * H * S = 1`, for the
Riesz operator `H` of `h`. -/
theorem metricChangeTransport_eq_iff (hH : IsStrictlyPositive h♯) {S : E →L[ℝ] E} :
    h.metricChangeTransport = S ↔ 0 ≤ S ∧ S * h♯ * S = 1 := by
  refine ⟨fun hT ↦ hT ▸ ⟨(isStrictlyPositive_metricChangeTransport hH).nonneg,
    metricChangeTransport_mul_mul_self hH⟩, fun ⟨hS, hSHS⟩ ↦ ?_⟩
  -- `S * h♯` is a left and `h♯ * S` a right inverse of `S`, so they agree, and then `S * S` is
  -- a right inverse of `h♯`; the square of the transport is its left inverse `h♯ ^ (-1)`.
  have hcomm : S * h♯ = h♯ * S := left_inv_eq_right_inv hSHS (by rw [← mul_assoc, hSHS])
  have hTT : h.metricChangeTransport * h.metricChangeTransport * h♯ = 1 := by
    conv_lhs => rhs; rw [← CFC.rpow_one h♯ hH.nonneg]
    rw [metricChangeTransport_def, ← CFC.rpow_add hH.isUnit, ← CFC.rpow_add hH.isUnit]
    norm_num [CFC.rpow_zero h♯ hH.nonneg]
  refine (CFC.mul_self_eq_mul_self_iff _ _
    (isStrictlyPositive_metricChangeTransport hH).nonneg hS).mp ?_
  exact left_inv_eq_right_inv hTT (by rw [← mul_assoc, ← hcomm, hSHS])

/-- The metric change transport is an isometry from the original inner product to `h`. -/
@[simp]
theorem apply_metricChangeTransport_metricChangeTransport (hH : IsStrictlyPositive h♯) (u v : E) :
    h (h.metricChangeTransport u) (h.metricChangeTransport v) = ⟪u, v⟫_ℝ := by
  have hT := nonneg_iff_isPositive.mp (isStrictlyPositive_metricChangeTransport hH).nonneg
  have h1 := congr($(metricChangeTransport_mul_mul_self hH) u)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at h1
  rw [← continuousLinearMapOfBilin_apply (𝕜 := ℝ) h, ← hT.inner_left_eq_inner_right, h1]

/-- The metric change transport carries an orthonormal family for the original inner product to
a family that is orthonormal for `h`. -/
theorem apply_metricChangeTransport_of_orthonormal (hH : IsStrictlyPositive h♯) {ι : Type*}
    [DecidableEq ι] {b : ι → E} (hb : Orthonormal ℝ b) (i j : ι) :
    h (h.metricChangeTransport (b i)) (h.metricChangeTransport (b j)) = if i = j then 1 else 0 := by
  rw [apply_metricChangeTransport_metricChangeTransport hH, orthonormal_iff_ite.mp hb]

/-- The inverse transport `CFC.sqrt H` is a left inverse of the metric change transport. -/
theorem sqrt_mul_metricChangeTransport (hH : IsStrictlyPositive h♯) :
    CFC.sqrt h♯ * h.metricChangeTransport = 1 := by
  rw [CFC.sqrt_eq_rpow, metricChangeTransport_def, CFC.rpow_mul_rpow_neg]

/-- The inverse transport `CFC.sqrt H` is a right inverse of the metric change transport. -/
theorem metricChangeTransport_mul_sqrt (hH : IsStrictlyPositive h♯) :
    h.metricChangeTransport * CFC.sqrt h♯ = 1 := by
  rw [CFC.sqrt_eq_rpow, metricChangeTransport_def, CFC.rpow_neg_mul_rpow]

/-- The square root of a positive Riesz operator `H` of `h` is an isometry from `h` to the
original inner product. -/
@[simp]
theorem inner_sqrt_apply_sqrt_apply (hH : 0 ≤ h♯) (u v : E) :
    ⟪CFC.sqrt h♯ u, CFC.sqrt h♯ v⟫_ℝ = h u v := by
  rw [← (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg h♯)).inner_left_eq_inner_right,
    ← mul_apply_eq_comp (CFC.sqrt h♯), CFC.sqrt_mul_sqrt_self _ hH,
    continuousLinearMapOfBilin_apply]

/-- The square root of a positive Riesz operator `H` of `h` carries a family that is orthonormal
for `h` to an orthonormal family for the original inner product. -/
theorem orthonormal_sqrt_apply (hH : 0 ≤ h♯) {ι : Type*} [DecidableEq ι] {f : ι → E}
    (hf : ∀ i j, h (f i) (f j) = if i = j then 1 else 0) :
    Orthonormal ℝ fun i ↦ CFC.sqrt h♯ (f i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_sqrt_apply_sqrt_apply hH, hf]

/-- The original inner product has trivial metric change transport. -/
@[simp]
theorem metricChangeTransport_innerSL :
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricChangeTransport = 1 := by
  have : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)♯ = 1 := by
    ext v
    refine ext_inner_right ℝ fun w ↦ ?_
    simp
  rw [metricChangeTransport_def, this, CFC.one_rpow]

/-- **Naturality of the metric change transport.** Pulling an inner product `k` on `F` back along
a linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` conjugates its metric change transport by `e`. -/
theorem metricChangeTransport_bilinearComp (e : E ≃ₗᵢ[ℝ] F) {k : F →L[ℝ] F →L[ℝ] ℝ}
    (hK : IsStrictlyPositive k♯) (x : E) :
    (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeTransport x =
      e.symm (k.metricChangeTransport (e x)) := by
  -- Pulling back along `e` conjugates the Riesz operator by the `⋆`-algebra equivalence induced by
  -- `e`, and that equivalence preserves the characterization `metricChangeTransport_eq_iff`.
  have hk : (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))♯ = e.symm.conjStarAlgEquiv k♯ := by
    ext v
    refine ext_inner_right ℝ fun w ↦ ?_
    rw [continuousLinearMapOfBilin_apply, bilinearComp_apply,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
      ← LinearIsometryEquiv.inner_map_map e, e.apply_symm_apply, continuousLinearMapOfBilin_apply]
    -- Only the coercion of `e` to a continuous linear map remains to be unfolded.
    simp
  have hK' : IsStrictlyPositive (e.symm.conjStarAlgEquiv k♯) :=
    IsStrictlyPositive.iff_of_unital.mpr
      ⟨map_nonneg e.symm.conjStarAlgEquiv hK.nonneg, hK.isUnit.map e.symm.conjStarAlgEquiv⟩
  suffices (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeTransport =
      e.symm.conjStarAlgEquiv k.metricChangeTransport from congr($this x)
  rw [metricChangeTransport_eq_iff (hk ▸ hK'), hk, ← map_mul, ← map_mul,
    metricChangeTransport_mul_mul_self hK, map_one]
  exact ⟨map_nonneg _ (isStrictlyPositive_metricChangeTransport hK).nonneg, rfl⟩

/-- **Isometries onto a second inner product.** On a finite-dimensional space, the linear maps
`S` that are isometries from the original inner product to `h` are exactly the composites of the
metric change transport with an orthogonal automorphism. In particular any two such isometries
differ by an orthogonal automorphism. -/
theorem forall_apply_apply_eq_inner_iff_exists_linearIsometryEquiv [FiniteDimensional ℝ E]
    (hH : IsStrictlyPositive h♯) {S : E →L[ℝ] E} :
    (∀ u v, h (S u) (S v) = ⟪u, v⟫_ℝ) ↔
      ∃ Q : E ≃ₗᵢ[ℝ] E, ∀ x, S x = h.metricChangeTransport (Q x) := by
  refine ⟨fun hS ↦ ?_, fun ⟨Q, hQ⟩ u v ↦ ?_⟩
  · -- The orthogonal automorphism is `CFC.sqrt h♯ ∘ S`, an isometry of the original inner product.
    have hQ : ∀ u v, ⟪(CFC.sqrt h♯ * S) u, (CFC.sqrt h♯ * S) v⟫_ℝ = ⟪u, v⟫_ℝ := fun u v ↦ by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, inner_sqrt_apply_sqrt_apply hH.nonneg, hS]
    refine ⟨(LinearMap.isometryOfInner (CFC.sqrt h♯ * S : E →L[ℝ] E).toLinearMap
      hQ).toLinearIsometryEquiv rfl, fun x ↦ ?_⟩
    simp only [LinearIsometry.coe_toLinearIsometryEquiv, LinearMap.coe_isometryOfInner, coe_coe]
    rw [← mul_apply_eq_comp h.metricChangeTransport, ← mul_assoc, metricChangeTransport_mul_sqrt hH,
      one_mul]
  · rw [hQ, hQ, apply_metricChangeTransport_metricChangeTransport hH,
      LinearIsometryEquiv.inner_map_map]

end ContinuousLinearMap

namespace InnerProductSpace

/-- The Riesz operator of a real bilinear form `h` on a finite-dimensional inner product space is
strictly positive exactly when `h` is symmetric and positive definite, that is, when `h` is an
inner product. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin_iff [FiniteDimensional ℝ E]
    {h : E →L[ℝ] E →L[ℝ] ℝ} :
    IsStrictlyPositive h♯ ↔ (∀ u v, h u v = h v u) ∧ ∀ v, v ≠ 0 → 0 < h v v := by
  have := FiniteDimensional.complete ℝ E
  have hinner : ∀ u v, ⟪u, h♯ v⟫_ℝ = h v u := fun u v ↦ by
    rw [real_inner_comm, continuousLinearMapOfBilin_apply]
  rw [IsStrictlyPositive.iff_of_unital, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff]
  have hsymm_iff : (h♯ : E →ₗ[ℝ] E).IsSymmetric ↔ ∀ u v, h u v = h v u :=
    forall₂_congr fun u v ↦ by
      rw [ContinuousLinearMap.coe_coe, continuousLinearMapOfBilin_apply, hinner]
  have hnonneg_iff : (∀ x, 0 ≤ ⟪h♯ x, x⟫_ℝ) ↔ ∀ x, 0 ≤ h x x :=
    forall_congr' fun x ↦ by rw [continuousLinearMapOfBilin_apply]
  rw [hsymm_iff, hnonneg_iff]
  refine ⟨fun ⟨⟨hsymm, hnonneg⟩, hunit⟩ ↦ ⟨hsymm, fun v hv ↦ (hnonneg v).lt_of_ne fun h0 ↦ hv ?_⟩,
    fun ⟨hsymm, hpos⟩ ↦ ⟨⟨hsymm, fun v ↦ ?_⟩, ?_⟩⟩
  · -- A vector with `h v v = 0` is killed by `CFC.sqrt h♯`, hence by the injective `h♯`.
    have hH : 0 ≤ h♯ := ContinuousLinearMap.nonneg_iff_isPositive.mpr <|
      (ContinuousLinearMap.isPositive_iff _).mpr ⟨hsymm_iff.mpr hsymm, hnonneg_iff.mpr hnonneg⟩
    have hsqrt : CFC.sqrt h♯ v = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ), ContinuousLinearMap.inner_sqrt_apply_sqrt_apply hH, h0]
    refine (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1 ?_
    rw [map_zero, ← CFC.sqrt_mul_sqrt_self _ hH, mul_apply_eq_comp, hsqrt, map_zero]
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos v hv).le
  · rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinj : Function.Injective h♯ := (injective_iff_map_eq_zero _).mpr fun v hv ↦ by
      by_contra hne
      refine (hpos v hne).ne' ?_
      rw [← continuousLinearMapOfBilin_apply (𝕜 := ℝ) h, hv, inner_zero_left]
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (h♯ : E →ₗ[ℝ] E))).mp hinj⟩

end InnerProductSpace
