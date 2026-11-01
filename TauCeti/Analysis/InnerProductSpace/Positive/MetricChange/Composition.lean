/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic

/-!
# Composition of metric-change transports

For positive inner products `h` and `k` on a finite-dimensional real inner-product space,
`h.metricChangeBetween k` is the canonical positive, `h`-self-adjoint isometry from `h` to `k`.
It is constructed by expressing `k` in the `h`-orthonormal coordinates supplied by
`h.metricChangeTransport`, applying the native inverse square root there, and conjugating back.

The successive transport from the reference inner product to `h` and then to `k` need not be
the direct transport to `k`. `metricChangeCompositionCorrection` constructs their explicit
orthogonal discrepancy. `metricChangeBetween_mul_metricChangeTransport` gives the comparison,
and `metricChangeCompositionCorrection_eq_iff` characterizes the correction uniquely.
These are pointwise statements; no parameter regularity is asserted here.

The construction uses `ContinuousLinearMap.metricChangeTransport` and its inverse square root
identities. See R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007,
Chapter 1, for positive square roots and congruences of inner products.
-/

public section

open InnerProductSpace
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- Expressing a positive metric in the orthonormal coordinates of another positive metric
preserves strict positivity of its Riesz operator. -/
theorem isStrictlyPositive_bilinearComp_metricChangeTransport
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    IsStrictlyPositive
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ := by
  rw [isStrictlyPositive_continuousLinearMapOfBilin_iff] at hK ⊢
  refine ⟨fun u v ↦ ?_, fun v hv ↦ ?_⟩
  · simpa only [bilinearComp_apply] using hK.1 (h.metricChangeTransport u)
      (h.metricChangeTransport v)
  · have hne : h.metricChangeTransport v ≠ 0 := by
      intro hz
      have heq := congr($(sqrt_mul_metricChangeTransport hH) v)
      simp only [mul_apply_eq_comp, one_apply_eq_self, hz, map_zero] at heq
      exact hv heq.symm
    simpa only [bilinearComp_apply] using hK.2 (h.metricChangeTransport v) hne

/-- The canonical metric transport from `h` to `k`, expressed on the original vector space.
For positive metrics it is positive and self-adjoint with respect to `h` and preserves the
inner products from `h` to `k`. -/
noncomputable def metricChangeBetween (h k : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  h.metricChangeTransport *
    (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport *
      CFC.sqrt h♯

/-- The formula for transport between two metrics in the reference inner-product coordinates. -/
theorem metricChangeBetween_def (h k : E →L[ℝ] E →L[ℝ] ℝ) :
    h.metricChangeBetween k = h.metricChangeTransport *
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport *
        CFC.sqrt h♯ := (rfl)

/-- In `h`-orthonormal coordinates, transport from `h` to `k` is the inverse square root of
the pulled-back metric. -/
theorem sqrt_mul_metricChangeBetween (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) :
    CFC.sqrt h♯ * h.metricChangeBetween k =
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport *
        CFC.sqrt h♯ := by
  simp [metricChangeBetween_def, ← mul_assoc, sqrt_mul_metricChangeTransport hH]

/-- Transport between metrics preserves their inner products. -/
@[simp]
theorem apply_metricChangeBetween_metricChangeBetween
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) (u v : E) :
    k (h.metricChangeBetween k u) (h.metricChangeBetween k v) = h u v := by
  have hP := isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK
  have heq := apply_metricChangeTransport_metricChangeTransport hP
    (CFC.sqrt h♯ u) (CFC.sqrt h♯ v)
  simpa only [metricChangeBetween_def, mul_apply_eq_comp, bilinearComp_apply,
    inner_sqrt_apply_sqrt_apply hH.nonneg] using heq

/-- Transport from `h` to `k` is self-adjoint for `h`, not generally for the reference
inner product. -/
theorem metricChangeBetween_selfAdjoint (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (u v : E) :
    h (h.metricChangeBetween k u) v = h u (h.metricChangeBetween k v) := by
  have hP := isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK
  have hT := nonneg_iff_isPositive.mp (isStrictlyPositive_metricChangeTransport hP).nonneg
  have heq (x : E) := congr($(sqrt_mul_metricChangeBetween h k hH) x)
  simp only [mul_apply_eq_comp] at heq
  simp only [← inner_sqrt_apply_sqrt_apply hH.nonneg, heq]
  exact hT.inner_left_eq_inner_right _ _

/-- Transport from `h` to `k` is strictly positive for `h`. -/
theorem metricChangeBetween_pos (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) {x : E} (hx : x ≠ 0) :
    0 < h (h.metricChangeBetween k x) x := by
  let T := (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport
  have hT := isStrictlyPositive_metricChangeTransport
    (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK)
  have hinjT := (isUnit_iff_bijective.mp
    (CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hT)).1
  have hinjH := (isUnit_iff_bijective.mp
    (CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hH)).1
  have hne : CFC.sqrt T (CFC.sqrt h♯ x) ≠ 0 := by
    intro hz
    apply hx
    apply hinjH
    apply hinjT
    simpa only [map_zero] using hz
  have heq := congr($(sqrt_mul_metricChangeBetween h k hH) x)
  simp only [mul_apply_eq_comp] at heq
  rw [← inner_sqrt_apply_sqrt_apply hH.nonneg, heq]
  have hs : ∀ y, ⟪CFC.sqrt T y, CFC.sqrt T y⟫_ℝ = ⟪T y, y⟫_ℝ := by
    intro y
    rw [← (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).inner_left_eq_inner_right,
      ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self T hT.nonneg]
  exact (hs _).symm ▸ real_inner_self_pos.mpr hne

/-- The transport between metrics is the unique nonnegative `h`-self-adjoint isometry
from `h` to `k`. Nonnegative, rather than strictly positive, suffices for uniqueness. -/
theorem metricChangeBetween_eq_iff (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (S : E →L[ℝ] E) :
    h.metricChangeBetween k = S ↔
      (∀ u v, h (S u) v = h u (S v)) ∧ (∀ u, 0 ≤ h (S u) u) ∧
        ∀ u v, k (S u) (S v) = h u v := by
  refine ⟨fun heq ↦ ?_, fun ⟨hsym, hpos, hiso⟩ ↦ ?_⟩
  · subst S
    refine ⟨metricChangeBetween_selfAdjoint h k hH hK, fun u ↦ ?_,
      apply_metricChangeBetween_metricChangeBetween h k hH hK⟩
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (metricChangeBetween_pos h k hH hK hu).le
  · -- In orthonormal coordinates, positivity and the isometry equation characterize
    -- the existing inverse-square-root transport.
    let P := CFC.sqrt h♯ * S * h.metricChangeTransport
    have hinv (u : E) := congr($(metricChangeTransport_mul_sqrt hH) u)
    simp only [mul_apply_eq_comp, one_apply_eq_self] at hinv
    have hinv' (u : E) := congr($(sqrt_mul_metricChangeTransport hH) u)
    simp only [mul_apply_eq_comp, one_apply_eq_self] at hinv'
    have hsymh := (isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hH).1
    have hp (u v : E) : ⟪P u, v⟫_ℝ =
        h (S (h.metricChangeTransport u)) (h.metricChangeTransport v) := by
      rw [← inner_sqrt_apply_sqrt_apply hH.nonneg]
      simp only [P, mul_apply_eq_comp, hinv']
    have hP : P.IsPositive := (isPositive_iff P).mpr ⟨fun u v ↦ by
      simp only [coe_coe]
      rw [hp, hsym, hsymh, ← hp, real_inner_comm], fun u ↦ by
        simpa only [RCLike.re_to_real, ← hp] using hpos (h.metricChangeTransport u)⟩
    have hnorm : metricChangeTransport
        (k.bilinearComp h.metricChangeTransport h.metricChangeTransport) = P := by
      rw [metricChangeTransport_eq_iff
        (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK)]
      refine ⟨nonneg_iff_isPositive.mpr hP, ?_⟩
      ext u
      apply ext_inner_right ℝ
      intro v
      rw [mul_apply_eq_comp, mul_apply_eq_comp, one_apply_eq_self,
        hP.inner_left_eq_inner_right, continuousLinearMapOfBilin_apply, bilinearComp_apply]
      simp only [P, mul_apply_eq_comp, hinv]
      rw [hiso, apply_metricChangeTransport_metricChangeTransport hH]
    rw [metricChangeBetween_def, hnorm]
    ext u
    simp only [P, mul_apply_eq_comp, hinv]

/-- Transporting a metric to itself is the identity. -/
@[simp]
theorem metricChangeBetween_self (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) : h.metricChangeBetween h = 1 := by
  have heq : h.bilinearComp h.metricChangeTransport h.metricChangeTransport = innerSL ℝ := by
    ext u v
    simpa only [bilinearComp_apply, apply_metricChangeTransport_metricChangeTransport hH]
      using (innerSL_apply_apply ℝ u v).symm
  simp [metricChangeBetween_def, heq, metricChangeTransport_mul_sqrt hH]

/-- Transport from the reference inner product, regarded as a metric, agrees with the
original inverse-square-root transport. -/
@[simp]
theorem metricChangeBetween_innerSL (k : E →L[ℝ] E →L[ℝ] ℝ) :
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricChangeBetween k = k.metricChangeTransport := by
  have hR : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)♯ = 1 := by
    ext v
    exact ext_inner_right ℝ fun w ↦ by simp
  have hP : k.bilinearComp (1 : E →L[ℝ] E) (1 : E →L[ℝ] E) = k := by
    ext u v
    simp
  simp [metricChangeBetween_def, hR, hP]

/-- The explicit orthogonal correction comparing successive metric changes through `h`
with direct transport to `k`. Its matrix is `sqrt K * T_h * T_(T_h* k)`. -/
noncomputable def metricChangeCompositionCorrection
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) : E ≃ₗᵢ[ℝ] E :=
  let T := (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport
  (LinearMap.isometryOfInner
    (CFC.sqrt k♯ * h.metricChangeTransport * T).toLinearMap
    (fun u v ↦ by
      have heq := apply_metricChangeTransport_metricChangeTransport
        (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK) u v
      simpa only [mul_apply_eq_comp, coe_coe, inner_sqrt_apply_sqrt_apply hK.nonneg,
        bilinearComp_apply] using heq)).toLinearIsometryEquiv rfl

/-- Evaluation of the orthogonal composition correction. -/
@[simp]
theorem metricChangeCompositionCorrection_apply
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) (x : E) :
    h.metricChangeCompositionCorrection k hH hK x =
      CFC.sqrt k♯
        (h.metricChangeTransport
          (metricChangeTransport
            (k.bilinearComp h.metricChangeTransport h.metricChangeTransport) x)) :=
  (rfl)

/-- Evaluation of the inverse composition correction, using the three inverse transports. -/
@[simp]
theorem metricChangeCompositionCorrection_symm_apply
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) (x : E) :
    (h.metricChangeCompositionCorrection k hH hK).symm x =
      CFC.sqrt (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
        (CFC.sqrt h♯ (k.metricChangeTransport x)) := by
  apply (h.metricChangeCompositionCorrection k hH hK).injective
  rw [LinearIsometryEquiv.apply_symm_apply, metricChangeCompositionCorrection_apply]
  have hP := isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK
  have hi (y : E) := congr($(metricChangeTransport_mul_sqrt hP) y)
  have hj (y : E) := congr($(metricChangeTransport_mul_sqrt hH) y)
  have hk (y : E) := congr($(sqrt_mul_metricChangeTransport hK) y)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hi hj hk
  rw [hi, hj, hk]

/-- Two successive canonical metric changes equal the direct change followed by the explicit
orthogonal correction. The correction acts first, on the reference inner-product space. -/
theorem metricChangeBetween_mul_metricChangeTransport
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    h.metricChangeBetween k * h.metricChangeTransport =
      k.metricChangeTransport *
        (h.metricChangeCompositionCorrection k hH hK : E →L[ℝ] E) := by
  ext x
  simp only [metricChangeBetween_def, mul_apply_eq_comp, LinearIsometryEquiv.coe_coe'',
    metricChangeCompositionCorrection_apply]
  have hi := congr($(sqrt_mul_metricChangeTransport hH) x)
  have hk (y : E) := congr($(metricChangeTransport_mul_sqrt hK) y)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hi hk
  rw [hi, hk]

/-- The displayed composition equation determines the orthogonal correction uniquely. -/
theorem metricChangeCompositionCorrection_eq_iff
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) (Q : E ≃ₗᵢ[ℝ] E) :
    h.metricChangeCompositionCorrection k hH hK = Q ↔
      h.metricChangeBetween k * h.metricChangeTransport =
        k.metricChangeTransport * (Q : E →L[ℝ] E) := by
  refine ⟨fun heq ↦ heq ▸ metricChangeBetween_mul_metricChangeTransport h k hH hK, fun heq ↦ ?_⟩
  have hc := metricChangeBetween_mul_metricChangeTransport h k hH hK
  ext x
  have he := congrArg (fun S : E →L[ℝ] E ↦ (CFC.sqrt k♯ * S) x) (hc.symm.trans heq)
  simpa only [← mul_assoc, sqrt_mul_metricChangeTransport hK, one_mul,
    LinearIsometryEquiv.coe_coe''] using he

/-- The composition correction is trivial when the intermediate and final metrics agree. -/
@[simp]
theorem metricChangeCompositionCorrection_self
    (h : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯) :
    h.metricChangeCompositionCorrection h hH hH = LinearIsometryEquiv.refl ℝ E := by
  rw [metricChangeCompositionCorrection_eq_iff]
  ext x
  simp [hH]

end ContinuousLinearMap
