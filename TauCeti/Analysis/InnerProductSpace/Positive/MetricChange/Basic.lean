/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Convex.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

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
conjugates the transport by `e`, and likewise its inverse. The transport and its inverse depend
continuously on `h`, because the real continuous functional calculus is isometric. When `E` is
finite-dimensional, every other isometry from `(E, ⟪·, ·⟫)` to `(E, h)` is the transport composed
with an orthogonal automorphism of `E`. This classification is the tool for comparing the
composite of the transports of two successive changes of inner product with the transport of the
composite change; that comparison is not formalized here, since every result in this file is
relative to the fixed inner product of `E`.

## Main declarations

* `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff`: in finite dimension,
  the Riesz operator of `h` is strictly positive exactly when `h` is symmetric and positive
  definite; `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_of_injective`: in
  particular for an inner product pulled back along an injective linear map.
* `ContinuousLinearMap.metricChangeTransport`: the inverse square root of the Riesz operator.
* `ContinuousLinearMap.metricChangeEquiv`: the same transport as a continuous linear equivalence,
  with the positive square root as inverse.
* `ContinuousLinearMap.metricChangeTransport_eq_iff`: it is the unique positive `S` with
  `S * H * S = 1`.
* `ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport`: it is an isometry from
  `⟪·, ·⟫` to `h`; `ContinuousLinearMap.apply_metricChangeTransport_of_orthonormal` is the frame
  version.
* `ContinuousLinearMap.inner_sqrt_apply_sqrt_apply`, `ContinuousLinearMap.orthonormal_sqrt_apply`:
  the inverse transport `CFC.sqrt H` is an isometry from `h` back to `⟪·, ·⟫`.
* `ContinuousLinearMap.metricChangeTransport_bilinearComp`,
  `ContinuousLinearMap.sqrt_continuousLinearMapOfBilin_bilinearComp`: naturality of the transport
  and of its inverse under linear isometry equivalences.
* `ContinuousLinearMap.continuousOn_metricChangeTransport`,
  `ContinuousLinearMap.continuousOn_sqrt_continuousLinearMapOfBilin`: the transport and its inverse
  depend continuously on `h`.
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

/-- Pointwise left-inverse equation for the metric change transport. -/
@[simp]
theorem sqrt_apply_metricChangeTransport_apply (hH : IsStrictlyPositive h♯) (x : E) :
    CFC.sqrt h♯ (h.metricChangeTransport x) = x := by
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congr($(sqrt_mul_metricChangeTransport hH) x)

/-- Pointwise right-inverse equation for the metric change transport. -/
@[simp]
theorem metricChangeTransport_apply_sqrt_apply (hH : IsStrictlyPositive h♯) (x : E) :
    h.metricChangeTransport (CFC.sqrt h♯ x) = x := by
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congr($(metricChangeTransport_mul_sqrt hH) x)

/-- The canonical metric transport as a continuous linear equivalence, with inverse the
positive square root of the Riesz operator. This equivalence is linear on the underlying space;
its isometry property compares the original inner product with `h`. -/
noncomputable def metricChangeEquiv (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit
    ⟨h.metricChangeTransport, CFC.sqrt h♯, metricChangeTransport_mul_sqrt hH,
      sqrt_mul_metricChangeTransport hH⟩

/-- The underlying operator of the canonical metric equivalence is the inverse square root. -/
@[simp]
theorem coe_metricChangeEquiv (hH : IsStrictlyPositive h♯) :
    (h.metricChangeEquiv hH : E →L[ℝ] E) = h.metricChangeTransport :=
  (rfl)

/-- The inverse metric equivalence has the positive square root as its underlying operator. -/
@[simp]
theorem coe_metricChangeEquiv_symm (hH : IsStrictlyPositive h♯) :
    ((h.metricChangeEquiv hH).symm : E →L[ℝ] E) = CFC.sqrt h♯ :=
  (rfl)

/-- Evaluation of the canonical metric equivalence. -/
@[simp]
theorem metricChangeEquiv_apply (hH : IsStrictlyPositive h♯) (x : E) :
    h.metricChangeEquiv hH x = h.metricChangeTransport x :=
  (rfl)

/-- Evaluation of the inverse metric equivalence. -/
@[simp]
theorem metricChangeEquiv_symm_apply (hH : IsStrictlyPositive h♯) (x : E) :
    (h.metricChangeEquiv hH).symm x = CFC.sqrt h♯ x :=
  (rfl)

/-- The square root of a positive Riesz operator `H` of `h` is an isometry from `h` to the
original inner product. -/
@[simp]
theorem inner_sqrt_apply_sqrt_apply (hH : 0 ≤ h♯) (u v : E) :
    ⟪CFC.sqrt h♯ u, CFC.sqrt h♯ v⟫_ℝ = h u v := by
  rw [inner_sqrt_apply_sqrt_apply_eq_inner hH, continuousLinearMapOfBilin_apply]

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
  rw [metricChangeTransport_def, continuousLinearMapOfBilin_innerSL, CFC.one_rpow]

/-- The canonical metric equivalence for the original inner product is the identity. -/
@[simp]
theorem metricChangeEquiv_innerSL
    (hR : IsStrictlyPositive (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)♯) :
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricChangeEquiv hR =
      ContinuousLinearEquiv.refl ℝ E := by
  ext x
  simp

/-- **Naturality of the metric change transport.** Pulling an inner product `k` on `F` back along
a linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` conjugates its metric change transport by `e`. -/
theorem metricChangeTransport_bilinearComp (e : E ≃ₗᵢ[ℝ] F) {k : F →L[ℝ] F →L[ℝ] ℝ}
    (hK : IsStrictlyPositive k♯) (x : E) :
    (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeTransport x =
      e.symm (k.metricChangeTransport (e x)) := by
  -- Pulling back along `e` conjugates the Riesz operator by the `⋆`-algebra equivalence induced by
  -- `e`, and that equivalence preserves the characterization `metricChangeTransport_eq_iff`.
  have hk := continuousLinearMapOfBilin_bilinearComp e k
  have hK' : IsStrictlyPositive (e.symm.conjStarAlgEquiv k♯) :=
    IsStrictlyPositive.iff_of_unital.mpr
      ⟨map_nonneg e.symm.conjStarAlgEquiv hK.nonneg, hK.isUnit.map e.symm.conjStarAlgEquiv⟩
  suffices (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeTransport =
      e.symm.conjStarAlgEquiv k.metricChangeTransport from congr($this x)
  rw [metricChangeTransport_eq_iff (hk ▸ hK'), hk, ← map_mul, ← map_mul,
    metricChangeTransport_mul_mul_self hK, map_one]
  exact ⟨map_nonneg _ (isStrictlyPositive_metricChangeTransport hK).nonneg, rfl⟩

/-- **Naturality of the inverse transport.** Pulling a bilinear form `k` on `F` with positive Riesz
operator back along a linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` conjugates the square root of
its Riesz operator by `e`. -/
theorem sqrt_continuousLinearMapOfBilin_bilinearComp (e : E ≃ₗᵢ[ℝ] F) {k : F →L[ℝ] F →L[ℝ] ℝ}
    (hK : 0 ≤ k♯) (x : E) :
    CFC.sqrt (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))♯ x =
      e.symm (CFC.sqrt k♯ (e x)) := by
  suffices CFC.sqrt (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))♯ =
      e.symm.conjStarAlgEquiv (CFC.sqrt k♯) from congr($this x)
  rw [continuousLinearMapOfBilin_bilinearComp, CFC.sqrt_eq_iff _ _ (map_nonneg _ hK)
    (map_nonneg _ (CFC.sqrt_nonneg _)), ← map_mul, CFC.sqrt_mul_sqrt_self _ hK]

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

/-- The inner product of `F` pulled back along an injective linear map `K : E → F` has strictly
positive Riesz operator. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin_of_injective [FiniteDimensional ℝ E]
    {K : E →ₗ[ℝ] F} (hK : Function.Injective K) {h : E →L[ℝ] E →L[ℝ] ℝ}
    (hh : ∀ u v, h u v = ⟪K u, K v⟫_ℝ) : IsStrictlyPositive h♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    ⟨fun u v ↦ by rw [hh, hh, real_inner_comm], fun v hv ↦ by
      rw [hh]
      exact real_inner_self_pos.2 fun h0 ↦ hv (hK (h0.trans K.map_zero.symm))⟩

end InnerProductSpace

namespace ContinuousLinearMap

/-- Real bilinear forms with strictly positive Riesz operators form a convex set. -/
theorem convex_setOf_isStrictlyPositive_continuousLinearMapOfBilin [CompleteSpace E] :
    Convex ℝ {h : E →L[ℝ] E →L[ℝ] ℝ | IsStrictlyPositive h♯} := by
  intro h hh k hk a b ha hb hab
  have heq : (a • h + b • k)♯ = a • h♯ + b • k♯ := by
    ext u
    apply ext_inner_right ℝ
    intro v
    simp [inner_add_left, inner_smul_left, continuousLinearMapOfBilin_apply]
  rw [Set.mem_ofPred_eq, heq]
  rcases lt_or_eq_of_le ha with ha | rfl
  · have hp : 0 ≤ a • h♯ + b • k♯ :=
      add_nonneg (smul_nonneg ha.le hh.nonneg) (smul_nonneg hb hk.nonneg)
    -- Mathlib's strict-positivity addition lemma is for complex C⋆-algebras;
    -- complexification preserves the spectrum of our self-adjoint real operator.
    let Φ := complexifyL2StarAlgHom E
    have hΦ : IsStrictlyPositive (Φ (a • h♯ + b • k♯)) := by
      rw [map_add]
      exact ((IsStrictlyPositive.smul ha hh).isUnit.map Φ |>.isStrictlyPositive
        (map_nonneg Φ (smul_nonneg ha.le hh.nonneg))).add_nonneg
          (map_nonneg Φ (smul_nonneg hb hk.nonneg))
    refine IsStrictlyPositive.iff_of_unital.mpr ⟨hp, ?_⟩
    rw [← spectrum.zero_notMem_iff ℝ, ← spectrum_complexifyL2 hp.isSelfAdjoint]
    simpa only [Φ, complexifyL2StarAlgHom_apply] using
      (spectrum.zero_notMem_iff ℝ).mpr hΦ.isUnit
  · have hb1 : b = 1 := by simpa using hab
    simpa [hb1] using hk

/-- The affine interpolation of positive metrics remains positive, including at its endpoints. -/
theorem isStrictlyPositive_lineMap [CompleteSpace E] (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsStrictlyPositive (AffineMap.lineMap h k t)♯ := by
  rw [AffineMap.lineMap_apply_module]
  exact convex_setOf_isStrictlyPositive_continuousLinearMapOfBilin hH hK
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

/-- Pullback of a positive metric by a continuous linear equivalence of real Hilbert spaces
is positive. No preservation of the reference inner products is needed. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
    [CompleteSpace E] [CompleteSpace F]
    (h : F →L[ℝ] F →L[ℝ] ℝ) (e : E ≃L[ℝ] F) (hH : IsStrictlyPositive h♯) :
    IsStrictlyPositive (h.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))♯ := by
  have heq : (h.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))♯ =
      (e : E →L[ℝ] F).adjoint ∘L h♯ ∘L (e : E →L[ℝ] F) := by
    ext u
    apply ext_inner_right ℝ
    intro v
    rw [continuousLinearMapOfBilin_apply, bilinearComp_apply, comp_apply, comp_apply,
      adjoint_inner_left, continuousLinearMapOfBilin_apply]
  have hleft (x : E) :
      (e : E →L[ℝ] F).adjoint ((e.symm : F →L[ℝ] E).adjoint x) = x := by
    rw [← comp_apply, ← adjoint_comp]
    simp [adjoint_id]
  have hright (x : F) :
      (e.symm : F →L[ℝ] E).adjoint ((e : E →L[ℝ] F).adjoint x) = x := by
    rw [← comp_apply, ← adjoint_comp]
    simp [adjoint_id]
  obtain ⟨u, hu⟩ := hH.isUnit
  rw [heq, IsStrictlyPositive.iff_of_unital]
  refine ⟨nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hH.nonneg).adjoint_conj _), ?_⟩
  refine ⟨⟨(e : E →L[ℝ] F).adjoint ∘L h♯ ∘L (e : E →L[ℝ] F),
    (e.symm : F →L[ℝ] E) ∘L (↑u⁻¹ : F →L[ℝ] F) ∘L
      (e.symm : F →L[ℝ] E).adjoint, ?_, ?_⟩, rfl⟩
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ← hu]
    simp only [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self, hleft]
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, ← hu, hright]
    simp only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- Pullback of a positive metric on a real Hilbert space by an injective linear map from a
finite-dimensional space is positive. No preservation of the reference inner products is needed. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp
    [FiniteDimensional ℝ E] [CompleteSpace F]
    (h : F →L[ℝ] F →L[ℝ] ℝ) (f : E →L[ℝ] F) (hH : IsStrictlyPositive h♯)
    (hf : Function.Injective f) : IsStrictlyPositive (h.bilinearComp f f)♯ := by
  have hP := nonneg_iff_isPositive.mp hH.nonneg
  refine isStrictlyPositive_continuousLinearMapOfBilin_iff.2 ⟨fun u v ↦ ?_, fun u hu ↦ ?_⟩
  · simp only [bilinearComp_apply]
    rw [← continuousLinearMapOfBilin_apply (𝕜 := ℝ) h, hP.inner_left_eq_inner_right,
      real_inner_comm, continuousLinearMapOfBilin_apply]
  · rw [bilinearComp_apply, ← inner_sqrt_apply_sqrt_apply hH.nonneg]
    apply real_inner_self_pos.mpr
    intro hzero
    apply (hf.ne hu : f u ≠ f 0)
    have hinv := metricChangeTransport_apply_sqrt_apply hH (f u)
    simpa only [hzero, map_zero] using hinv.symm

variable [CompleteSpace E]

/-- **Continuity of the metric change transport.** The metric change transport depends
continuously on the inner product `h`, among the bilinear forms with strictly positive Riesz
operator. -/
theorem continuousOn_metricChangeTransport :
    ContinuousOn (fun h : E →L[ℝ] E →L[ℝ] ℝ ↦ h.metricChangeTransport)
      {h | IsStrictlyPositive h♯} := by
  simp_rw [metricChangeTransport_def]
  exact (CFC.continuousOn_rpow _).comp continuous_continuousLinearMapOfBilin.continuousOn
    fun _ hH ↦ hH

/-- The inverse transport `CFC.sqrt h♯` depends continuously on the bilinear form `h`, among those
with positive Riesz operator. -/
theorem continuousOn_sqrt_continuousLinearMapOfBilin :
    ContinuousOn (fun h : E →L[ℝ] E →L[ℝ] ℝ ↦ CFC.sqrt h♯) {h | 0 ≤ h♯} :=
  CFC.continuousOn_sqrt.comp continuous_continuousLinearMapOfBilin.continuousOn fun _ hH ↦ hH

end ContinuousLinearMap
