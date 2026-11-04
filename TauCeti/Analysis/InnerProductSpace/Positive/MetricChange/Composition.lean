/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic

/-!
# Composition of metric-change transports

For inner products `h` and `k` with strictly positive Riesz operators on a real Hilbert space,
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
  [CompleteSpace E]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- Expressing a positive metric in the orthonormal coordinates of another positive metric
preserves strict positivity of its Riesz operator. -/
theorem isStrictlyPositive_bilinearComp_metricChangeTransport
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    IsStrictlyPositive
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ := by
  have hT := isStrictlyPositive_metricChangeTransport hH
  have heq : (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ =
      h.metricChangeTransport * k♯ * h.metricChangeTransport := by
    ext u
    apply ext_inner_right ℝ
    intro v
    rw [continuousLinearMapOfBilin_apply, bilinearComp_apply, mul_apply_eq_comp,
      mul_apply_eq_comp, (nonneg_iff_isPositive.mp hT.nonneg).inner_left_eq_inner_right,
      continuousLinearMapOfBilin_apply]
  rw [heq, IsStrictlyPositive.iff_of_unital]
  exact ⟨conjugate_nonneg_of_nonneg hK.nonneg hT.nonneg, hT.isUnit.mul hK.isUnit |>.mul hT.isUnit⟩

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

/-- Pointwise form of the transport equation in `h`-orthonormal coordinates. -/
@[simp]
theorem sqrt_apply_metricChangeBetween_apply (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (x : E) :
    CFC.sqrt h♯ (h.metricChangeBetween k x) =
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport
        (CFC.sqrt h♯ x) := by
  simpa only [mul_apply_eq_comp] using congr($(sqrt_mul_metricChangeBetween h k hH) x)

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
theorem apply_metricChangeBetween_left_eq_right (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (u v : E) :
    h (h.metricChangeBetween k u) v = h u (h.metricChangeBetween k v) := by
  have hT : (metricChangeTransport
      (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)).IsPositive := by
    apply nonneg_iff_isPositive.mp
    rw [metricChangeTransport_def]
    exact CFC.rpow_nonneg
  simp only [← inner_sqrt_apply_sqrt_apply hH.nonneg,
    sqrt_apply_metricChangeBetween_apply h k hH]
  exact hT.inner_left_eq_inner_right _ _

/-- Transport from `h` to `k` is strictly positive for `h`. -/
theorem apply_metricChangeBetween_pos (h k : E →L[ℝ] E →L[ℝ] ℝ)
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
  rw [← inner_sqrt_apply_sqrt_apply hH.nonneg, sqrt_apply_metricChangeBetween_apply h k hH]
  exact (inner_sqrt_apply_sqrt_apply_eq_inner hT.nonneg _ _).symm ▸
    real_inner_self_pos.mpr hne

/-- The transport between metrics is the unique nonnegative `h`-self-adjoint isometry
from `h` to `k`. Nonnegative, rather than strictly positive, suffices for uniqueness. -/
theorem metricChangeBetween_eq_iff (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (S : E →L[ℝ] E) :
    h.metricChangeBetween k = S ↔
      (∀ u v, h (S u) v = h u (S v)) ∧ (∀ u, 0 ≤ h (S u) u) ∧
        ∀ u v, k (S u) (S v) = h u v := by
  refine ⟨fun heq ↦ ?_, fun ⟨hsym, hpos, hiso⟩ ↦ ?_⟩
  · subst S
    refine ⟨apply_metricChangeBetween_left_eq_right h k hH, fun u ↦ ?_,
      apply_metricChangeBetween_metricChangeBetween h k hH hK⟩
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (apply_metricChangeBetween_pos h k hH hK hu).le
  · -- Express `S` in `h`-orthonormal coordinates as `P`.
    let P := CFC.sqrt h♯ * S * h.metricChangeTransport
    have hsymh (u v : E) : h u v = h v u := by
      rw [← continuousLinearMapOfBilin_apply (𝕜 := ℝ) h,
        (nonneg_iff_isPositive.mp hH.nonneg).inner_left_eq_inner_right,
        real_inner_comm, continuousLinearMapOfBilin_apply]
    have hp (u v : E) : ⟪P u, v⟫_ℝ =
        h (S (h.metricChangeTransport u)) (h.metricChangeTransport v) := by
      rw [← inner_sqrt_apply_sqrt_apply hH.nonneg]
      simp only [P, mul_apply_eq_comp, sqrt_apply_metricChangeTransport_apply hH]
    -- Source-metric symmetry and nonnegativity become ordinary positivity of `P`.
    have hP : P.IsPositive := (isPositive_iff P).mpr ⟨fun u v ↦ by
      simp only [coe_coe]
      rw [hp, hsym, hsymh, ← hp, real_inner_comm], fun u ↦ by
        simpa only [RCLike.re_to_real, ← hp] using hpos (h.metricChangeTransport u)⟩
    -- The isometry equation identifies `P` with the existing inverse-square-root transport.
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
      simp only [P, mul_apply_eq_comp, metricChangeTransport_apply_sqrt_apply hH]
      rw [hiso, apply_metricChangeTransport_metricChangeTransport hH]
    -- Conjugate back to the original coordinates.
    rw [metricChangeBetween_def, hnorm]
    ext u
    simp only [P, mul_apply_eq_comp, metricChangeTransport_apply_sqrt_apply hH]

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
  have hP : k.bilinearComp (1 : E →L[ℝ] E) (1 : E →L[ℝ] E) = k := by
    ext u v
    simp
  simp [metricChangeBetween_def, hP]

/-- The explicit orthogonal correction comparing successive metric changes through `h`
with direct transport to `k`. Its operator is
`CFC.sqrt k♯ * h.metricChangeTransport *
(k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport`,
where `k♯` is the Riesz operator of `k`. -/
noncomputable def metricChangeCompositionCorrection
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) : E ≃ₗᵢ[ℝ] E :=
  let T := (k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeTransport
  LinearIsometryEquiv.ofSurjective (LinearMap.isometryOfInner
    (CFC.sqrt k♯ * h.metricChangeTransport * T).toLinearMap
    (fun u v ↦ by
      have heq := apply_metricChangeTransport_metricChangeTransport
        (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK) u v
      simpa only [mul_apply_eq_comp, coe_coe, inner_sqrt_apply_sqrt_apply hK.nonneg,
        bilinearComp_apply] using heq)) (by
    -- The three inverse transports give a preimage in every Hilbert-space dimension.
    intro x
    refine ⟨CFC.sqrt (k.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
      (CFC.sqrt h♯ (k.metricChangeTransport x)), ?_⟩
    simp only [LinearMap.coe_isometryOfInner, coe_coe, mul_apply_eq_comp, T,
      metricChangeTransport_apply_sqrt_apply
        (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK),
      metricChangeTransport_apply_sqrt_apply hH, sqrt_apply_metricChangeTransport_apply hK])

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
  rw [metricChangeTransport_apply_sqrt_apply hP, metricChangeTransport_apply_sqrt_apply hH,
    sqrt_apply_metricChangeTransport_apply hK]

/-- Two successive canonical metric changes equal the explicit orthogonal correction,
acting on the reference inner-product space, followed by the direct change to `k`. -/
theorem metricChangeBetween_mul_metricChangeTransport
    (h k : E →L[ℝ] E →L[ℝ] ℝ) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    h.metricChangeBetween k * h.metricChangeTransport =
      k.metricChangeTransport *
        (h.metricChangeCompositionCorrection k hH hK : E →L[ℝ] E) := by
  ext x
  simp only [metricChangeBetween_def, mul_apply_eq_comp, LinearIsometryEquiv.coe_coe'',
    metricChangeCompositionCorrection_apply]
  rw [sqrt_apply_metricChangeTransport_apply hH, metricChangeTransport_apply_sqrt_apply hK]

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

/-- The correction is trivial when the intermediate metric is the reference inner product. -/
@[simp]
theorem metricChangeCompositionCorrection_innerSL
    (k : E →L[ℝ] E →L[ℝ] ℝ)
    (hR : IsStrictlyPositive (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)♯)
    (hK : IsStrictlyPositive k♯) :
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricChangeCompositionCorrection k hR hK =
      LinearIsometryEquiv.refl ℝ E := by
  rw [metricChangeCompositionCorrection_eq_iff]
  ext x
  simp

end ContinuousLinearMap
