/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.RelativeProjection
import TauCeti.Algebra.Algebra.StrictPositivity
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Commute

/-!
# Normalizing a nondegenerate form relative to a metric

Let `q` be a symmetric nondegenerate bilinear form on a finite-dimensional real inner product space
`E` and let `h` be a second inner product on `E`, given as a positive definite bilinear form. The
negative spectral projection `P = q.negativeSpectralProjection h` splits each vector as
`u = P u + (u - P u)`, orthogonally for both `h` and `q`, with `q` negative definite on the range
of `P` and positive definite on its kernel. This file constructs the canonical linear change of
variables `N` which carries `q` to the difference of the two halves of `h`:

`q (N u) (N u) = h (u - P u) (u - P u) - h (P u) (P u)`.

So in the variable `w = N⁻¹ v`, the value `q v v` reads as `‖w⁺‖² - ‖w⁻‖²` in the norm of `h`,
which is Sylvester's normal form without any choice of basis. For a field of nondegenerate forms on
a vector bundle with a fibre metric, such as the normal Hessian of a Morse–Bott critical
submanifold, it carries the form to its positive-minus-negative fibre quadratic form.

The operator is `N = |K|^(-1/2)` for the operator `K = h⁻¹ q`, defined by `h (K u) v = q u v`,
which is self-adjoint for `h`. It is computed with the metric change transport `T` of `h`
(`ContinuousLinearMap.metricChangeTransport`), an isometry from the inner product of `E` to `h`:
if `A` is the Riesz operator of the pulled-back form `q (T ·) (T ·)`, then
`N = T (A * A) ^ (-(1 / 4)) T⁻¹` (`ContinuousLinearMap.normalizingTransport`). Then
`(A * A) ^ (-(1 / 4))` commutes with `A` (`Commute.rpow_left`) and conjugates it to the difference
of the positive and negative orthogonal spectral projections of `A`
(`ContinuousLinearMap.mul_self_rpow_mul_mul_mul_self_rpow`).

No choice enters: `N` is the unique operator that is self-adjoint and positive semidefinite for
`h`, self-adjoint for `q`, and normalizes `q` as above
(`ContinuousLinearMap.eq_normalizingTransport_iff`).
Consequently it does not depend on the inner product of `E`, and it is natural under linear
equivalences (`ContinuousLinearMap.normalizingTransport_bilinearComp`): normalizations computed in
two local trivializations of a vector bundle agree under the transition. It also depends smoothly,
even real analytically, on the pair `(q, h)` (`ContDiffOn.normalizingTransport`), and so does the
corresponding operator on a finite-dimensional normed space without a chosen inner product
(`TauCeti.exists_contDiffOn_apply_eq_of_mem_relativeSpectralSubspace`).

## Main declarations

* `ContinuousLinearMap.normalizingTransport q h`: the normalizing transport of `q` relative to
  `h`.
* `ContinuousLinearMap.apply_normalizingTransport_normalizingTransport`: the normalization identity
  `q (N u) (N v) = h u v - 2 * h (P u) (P v)`.
* `ContinuousLinearMap.commute_normalizingTransport_negativeSpectralProjection`: `N` commutes with
  `P`, so it preserves the negative and positive spectral subspaces.
* `ContinuousLinearMap.normalizingTransport_apply_mem_relativeSpectralSubspace_Iio` and
  `apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio`, with their
  `Ioi` counterparts: `N` preserves the relative spectral subspaces and carries `q` to `-h` on the
  negative one and to `h` on the positive one.
* `ContinuousLinearMap.isUnit_normalizingTransport`: `N` is invertible.
* `ContinuousLinearMap.metric_apply_normalizingTransport_left_eq_right`,
  `ContinuousLinearMap.metric_apply_normalizingTransport_self_pos` and
  `ContinuousLinearMap.apply_normalizingTransport_left_eq_right`: `N` is self-adjoint and positive
  definite for `h`, and self-adjoint for `q`.
* `ContinuousLinearMap.eq_normalizingTransport_iff`: the characterization.
* `ContinuousLinearMap.eq_normalizingTransport_of_mem_relativeSpectralSubspace`: uniqueness, with
  the normalization identity read on the relative spectral subspaces.
* `ContinuousLinearMap.normalizingTransport_bilinearComp`: naturality.
* `ContinuousLinearMap.contDiffOn_normalizingTransport`: smooth dependence on `(q, h)`.
* `TauCeti.exists_contDiffOn_apply_eq_of_mem_relativeSpectralSubspace`: the normalization on a
  finite-dimensional normed space, read through the relative spectral subspaces and determined by
  its listed properties.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.1.
-/

public section

noncomputable section

open InnerProductSpace Set
open scoped InnerProductSpace ContDiff

/-- The Riesz operator of a real bilinear form, written as Mathlib's `InnerProductSpace.Dual`
writes it. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The normalizing transport -/

/-- The **normalizing transport** of a bilinear form `q` relative to a second inner product `h`:
when `q` is symmetric and nondegenerate and `h` is positive definite, the operator `|h⁻¹ q|^(-1/2)`,
which carries `q` to `h` on the positive spectral subspace of `h⁻¹ q` and to `-h` on the negative
one (`ContinuousLinearMap.apply_normalizingTransport_normalizingTransport`).

It is `(A * A) ^ (-(1 / 4))` for the Riesz operator `A` of the pulled-back form `q (T ·) (T ·)`,
conjugated by the metric change transport `T` of `h`. -/
def normalizingTransport (q h : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  h.metricChangeTransport *
    ((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ *
      (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯) ^ (-(1 / 4) : ℝ) *
    CFC.sqrt h♯

theorem normalizingTransport_def (q h : E →L[ℝ] E →L[ℝ] ℝ) :
    q.normalizingTransport h =
      h.metricChangeTransport *
        ((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ *
          (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯) ^ (-(1 / 4) : ℝ) *
        CFC.sqrt h♯ :=
  (rfl)

/-- The normalizing transport of `-q` is that of `q`. -/
@[simp]
theorem normalizingTransport_neg (q h : E →L[ℝ] E →L[ℝ] ℝ) :
    (-q).normalizingTransport h = q.normalizingTransport h := by
  have hneg : ((-q).bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ =
      -(q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ := by
    ext x
    refine ext_inner_right ℝ fun y ↦ ?_
    simp only [continuousLinearMapOfBilin_apply, neg_apply, inner_neg_left, bilinearComp_apply]
  rw [normalizingTransport_def, normalizingTransport_def, hneg, neg_mul_neg]

/-- The normalizing transport of a positive definite `h` relative to itself is the identity. -/
@[simp]
theorem normalizingTransport_self {h : E →L[ℝ] E →L[ℝ] ℝ} (hh : IsStrictlyPositive h♯) :
    h.normalizingTransport h = 1 := by
  have hone : (h.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ = 1 := by
    ext x
    refine ext_inner_right ℝ fun y ↦ ?_
    rw [continuousLinearMapOfBilin_apply, bilinearComp_apply,
      apply_metricChangeTransport_metricChangeTransport hh, one_apply_eq_self]
  rw [normalizingTransport_def, hone, one_mul, CFC.one_rpow, mul_one,
    metricChangeTransport_mul_sqrt hh]

/-! ### The normalization identity -/

variable {q h : E →L[ℝ] E →L[ℝ] ℝ}

/-- The square of the Riesz operator of the pullback of a symmetric nondegenerate form along the
transport of a positive definite `h` is strictly positive. -/
private theorem isStrictlyPositive_mul_self_continuousLinearMapOfBilin_bilinearComp
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    IsStrictlyPositive ((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ *
      (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯) := by
  have hA : IsSelfAdjoint (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ :=
    isSelfAdjoint_continuousLinearMapOfBilin fun _ _ ↦ hq _ _
  exact hA.isStrictlyPositive_mul_self
    (isUnit_continuousLinearMapOfBilin_bilinearComp_metricChangeTransport hh hq')

/-- **The normalization identity.** The normalizing transport `N` of `q` relative to `h` carries
`q` to `h` minus twice `h` on the negative spectral subspace:
`q (N u) (N v) = h u v - 2 * h (P u) (P v)` for the negative spectral projection `P`. -/
theorem apply_normalizingTransport_normalizingTransport (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) (u v : E) :
    q (q.normalizingTransport h u) (q.normalizingTransport h v) =
      h u v - 2 * h (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h v) := by
  have hTR (x : E) : h.metricChangeTransport (CFC.sqrt h♯ x) = x :=
    metricChangeTransport_apply_sqrt_apply hh x
  have hRT (x : E) : CFC.sqrt h♯ (h.metricChangeTransport x) = x :=
    sqrt_apply_metricChangeTransport_apply hh x
  -- Read both sides through the transport `T`, with `u = T x` and `v = T y`.
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u := ⟨_, hTR u⟩
  obtain ⟨y, rfl⟩ : ∃ y, h.metricChangeTransport y = v := ⟨_, hTR v⟩
  rw [normalizingTransport_def, negativeSpectralProjection_def]
  set T := h.metricChangeTransport
  set A := (q.bilinearComp T T)♯
  have hA : IsSelfAdjoint A := isSelfAdjoint_continuousLinearMapOfBilin fun _ _ ↦ hq _ _
  have hunit : IsUnit A :=
    isUnit_continuousLinearMapOfBilin_bilinearComp_metricChangeTransport hh hq'
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  set B := (A * A) ^ (-(1 / 4) : ℝ)
  have hB := isSelfAdjoint_iff_isSymmetric.mp
    (CFC.rpow_nonneg (a := A * A) (y := (-(1 / 4) : ℝ))).isSelfAdjoint
  simp only [mul_apply_eq_comp, hRT]
  rw [← bilinearComp_apply q T T (B x) (B y), ← continuousLinearMapOfBilin_apply (𝕜 := ℝ)]
  have h₁ := hB (A (B x)) y
  simp only [coe_coe] at h₁
  rw [← h₁, ← mul_apply_eq_comp A, ← mul_apply_eq_comp B, ← mul_assoc,
    mul_self_rpow_mul_mul_mul_self_rpow A hA hunit,
    apply_metricChangeTransport_metricChangeTransport hh,
    apply_metricChangeTransport_metricChangeTransport hh]
  simp only [sub_apply, one_apply_eq_self, smul_apply, inner_sub_left, real_inner_smul_left]
  rw [← Submodule.inner_starProjection_left_eq_right, ← mul_apply_eq_comp W.starProjection,
    (Submodule.isIdempotentElem_starProjection W).eq]

/-- **The normalized form of a vector.** The normalizing transport `N` of `q` relative to `h`
carries `q` to the difference of `h` on the positive and the negative components:
`q (N u) (N u) = h (u - P u) (u - P u) - h (P u) (P u)` for the negative spectral projection
`P`. -/
theorem apply_normalizingTransport_normalizingTransport_self (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) (u : E) :
    q (q.normalizingTransport h u) (q.normalizingTransport h u) =
      h (u - q.negativeSpectralProjection h u) (u - q.negativeSpectralProjection h u) -
        h (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h u) := by
  set P := q.negativeSpectralProjection h
  have h₁ := metric_apply_negativeSpectralProjection_apply_sub_eq_zero (q := q) hh u u
  have hsymm := (isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hh).1
  rw [apply_normalizingTransport_normalizingTransport hh hq hq']
  -- Expand `h u u` along `u = P u + (u - P u)`; the cross terms vanish.
  have hu : h u u = h (P u) (P u) + h (u - P u) (u - P u) := by
    conv_lhs => rw [show u = P u + (u - P u) by abel]
    simp only [map_add, add_apply]
    rw [h₁, hsymm (u - P u) (P u), h₁]
    ring
  rw [hu]
  ring

/-- **The normalizing transport commutes with the negative spectral projection.** So it maps the
negative and the positive spectral subspaces of `q` relative to `h` into themselves. -/
theorem commute_normalizingTransport_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    Commute (q.normalizingTransport h) (q.negativeSpectralProjection h) := by
  have hA : IsSelfAdjoint (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ :=
    isSelfAdjoint_continuousLinearMapOfBilin fun _ _ ↦ hq _ _
  have hunit := isUnit_continuousLinearMapOfBilin_bilinearComp_metricChangeTransport hh hq'
  have hRT : CFC.sqrt h♯ * h.metricChangeTransport = 1 := sqrt_mul_metricChangeTransport hh
  -- Both operators are conjugates by the transport, so they commute because their cores do.
  have hconj (X Y : E →L[ℝ] E) :
      h.metricChangeTransport * X * CFC.sqrt h♯ * (h.metricChangeTransport * Y * CFC.sqrt h♯) =
        h.metricChangeTransport * (X * Y) * CFC.sqrt h♯ := by
    simp only [mul_assoc]
    rw [← mul_assoc (CFC.sqrt h♯), hRT, one_mul]
  rw [Commute, SemiconjBy, normalizingTransport_def, negativeSpectralProjection_def, hconj, hconj,
    (commute_mul_self_rpow_starProjection _ hA hunit (-(1 / 4))).eq]

/-- The normalizing transport maps the range of the negative spectral projection into itself. -/
theorem negativeSpectralProjection_normalizingTransport_eq_self
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q)
    {u : E} (hu : q.negativeSpectralProjection h u = u) :
    q.negativeSpectralProjection h (q.normalizingTransport h u) = q.normalizingTransport h u := by
  rw [← mul_apply_eq_comp, ← (commute_normalizingTransport_negativeSpectralProjection hh hq hq').eq,
    mul_apply_eq_comp, hu]

/-- The normalizing transport maps the kernel of the negative spectral projection into itself. -/
theorem negativeSpectralProjection_normalizingTransport_eq_zero
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q)
    {u : E} (hu : q.negativeSpectralProjection h u = 0) :
    q.negativeSpectralProjection h (q.normalizingTransport h u) = 0 := by
  rw [← mul_apply_eq_comp, ← (commute_normalizingTransport_negativeSpectralProjection hh hq hq').eq,
    mul_apply_eq_comp, hu, map_zero]

/-- The normalizing transport maps the negative relative spectral subspace into itself. -/
theorem normalizingTransport_apply_mem_relativeSpectralSubspace_Iio (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E}
    (hu : u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0)) :
    q.normalizingTransport h u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) := by
  rw [← negativeSpectralProjection_apply_eq_self_iff hh hq] at hu ⊢
  exact negativeSpectralProjection_normalizingTransport_eq_self hh hq hq' hu

/-- The normalizing transport maps the positive relative spectral subspace into itself. -/
theorem normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E}
    (hu : u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0)) :
    q.normalizingTransport h u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) := by
  rw [← negativeSpectralProjection_apply_eq_zero_iff hh hq hq'] at hu ⊢
  exact negativeSpectralProjection_normalizingTransport_eq_zero hh hq hq' hu

/-- On the negative relative spectral subspace, the normalizing transport carries `q` to `-h`. -/
theorem apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E}
    (hu : u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0)) :
    q (q.normalizingTransport h u) (q.normalizingTransport h u) = -h u u := by
  rw [apply_normalizingTransport_normalizingTransport hh hq hq',
    (negativeSpectralProjection_apply_eq_self_iff hh hq).mpr hu]
  ring

/-- On the positive relative spectral subspace, the normalizing transport carries `q` to `h`. -/
theorem apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Ioi
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E}
    (hu : u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0)) :
    q (q.normalizingTransport h u) (q.normalizingTransport h u) = h u u := by
  rw [apply_normalizingTransport_normalizingTransport hh hq hq',
    (negativeSpectralProjection_apply_eq_zero_iff hh hq hq').mpr hu, map_zero]
  ring

/-- **The normalizing transport is invertible.** -/
theorem isUnit_normalizingTransport (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u)
    (hq' : Function.Injective q) : IsUnit (q.normalizingTransport h) :=
  ((isStrictlyPositive_metricChangeTransport hh).isUnit.mul (IsStrictlyPositive.rpow _ _
    (isStrictlyPositive_mul_self_continuousLinearMapOfBilin_bilinearComp hh hq hq')).isUnit).mul
    hh.isUnit_cfcSqrt

/-- The normalizing transport read through the metric change transport `T`: it sends `T x` to
`T ((A * A) ^ (-(1 / 4)) x)`. -/
private theorem normalizingTransport_apply_metricChangeTransport (hh : IsStrictlyPositive h♯)
    (x : E) :
    q.normalizingTransport h (h.metricChangeTransport x) =
      h.metricChangeTransport
        ((((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ *
          (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯) ^
            (-(1 / 4) : ℝ)) x) := by
  rw [normalizingTransport_def]
  simp only [mul_apply_eq_comp, sqrt_apply_metricChangeTransport_apply hh]

/-- **The normalizing transport is self-adjoint for `h`.** -/
theorem metric_apply_normalizingTransport_left_eq_right (hh : IsStrictlyPositive h♯) (u v : E) :
    h (q.normalizingTransport h u) v = h u (q.normalizingTransport h v) := by
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh u⟩
  obtain ⟨y, rfl⟩ : ∃ y, h.metricChangeTransport y = v :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh v⟩
  rw [normalizingTransport_apply_metricChangeTransport hh,
    normalizingTransport_apply_metricChangeTransport hh,
    apply_metricChangeTransport_metricChangeTransport hh,
    apply_metricChangeTransport_metricChangeTransport hh]
  exact isSelfAdjoint_iff_isSymmetric.mp (CFC.rpow_nonneg (a := _ * _) (y := _)).isSelfAdjoint x y

/-- **The normalizing transport is positive definite for `h`.** -/
theorem metric_apply_normalizingTransport_self_pos (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E} (hu : u ≠ 0) :
    0 < h (q.normalizingTransport h u) u := by
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh u⟩
  have hx : x ≠ 0 := by rintro rfl; exact hu (map_zero _)
  rw [normalizingTransport_apply_metricChangeTransport hh,
    apply_metricChangeTransport_metricChangeTransport hh]
  exact (IsStrictlyPositive.rpow _ _
    (isStrictlyPositive_mul_self_continuousLinearMapOfBilin_bilinearComp hh hq hq')).inner_pos_left
      hx

/-- **The normalizing transport is self-adjoint for `q`.** -/
theorem apply_normalizingTransport_left_eq_right (hh : IsStrictlyPositive h♯) (u v : E) :
    q (q.normalizingTransport h u) v = q u (q.normalizingTransport h v) := by
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh u⟩
  obtain ⟨y, rfl⟩ : ∃ y, h.metricChangeTransport y = v :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh v⟩
  set T := h.metricChangeTransport
  set A := (q.bilinearComp T T)♯
  rw [normalizingTransport_apply_metricChangeTransport hh,
    normalizingTransport_apply_metricChangeTransport hh, ← bilinearComp_apply q T T,
    ← bilinearComp_apply q T T, ← continuousLinearMapOfBilin_apply (𝕜 := ℝ),
    ← continuousLinearMapOfBilin_apply (𝕜 := ℝ), ← mul_apply_eq_comp,
    ← (Commute.rpow_left ((Commute.refl A).mul_left (Commute.refl A)) _).eq, mul_apply_eq_comp]
  exact isSelfAdjoint_iff_isSymmetric.mp (CFC.rpow_nonneg (a := _ * _) (y := _)).isSelfAdjoint _ y

/-! ### Characterization and naturality -/

/-- **Characterization of the normalizing transport.** For a symmetric nondegenerate form `q` and
a positive definite `h`, an operator `S` is the normalizing transport of `q` relative to `h` exactly
when it is self-adjoint and positive semidefinite for `h`, self-adjoint for `q`, and satisfies the
normalization identity `q (S u) (S v) = h u v - 2 * h (P u) (P v)` for the negative spectral
projection `P`. In particular the normalizing transport does not depend on the inner product of
`E`. -/
theorem eq_normalizingTransport_iff (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u)
    (hq' : Function.Injective q) {S : E →L[ℝ] E} :
    S = q.normalizingTransport h ↔
      (∀ u v, h (S u) v = h u (S v)) ∧ (∀ u, 0 ≤ h (S u) u) ∧
        (∀ u v, q (S u) v = q u (S v)) ∧
        ∀ u v, q (S u) (S v) =
          h u v - 2 * h (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h v) := by
  refine ⟨fun hS ↦ hS ▸ ⟨metric_apply_normalizingTransport_left_eq_right hh,
    fun u ↦ (eq_or_ne u 0).elim (fun hu ↦ by simp [hu])
      fun hu ↦ (metric_apply_normalizingTransport_self_pos hh hq hq' hu).le,
    apply_normalizingTransport_left_eq_right hh,
    apply_normalizingTransport_normalizingTransport hh hq hq'⟩, ?_⟩
  rintro ⟨hhS, hpos, hqS, hnorm⟩
  set T := h.metricChangeTransport
  set A := (q.bilinearComp T T)♯
  have hunit : IsUnit A :=
    isUnit_continuousLinearMapOfBilin_bilinearComp_metricChangeTransport hh hq'
  set B := (A * A) ^ (-(1 / 4) : ℝ)
  have hBA : Commute B A := Commute.rpow_left ((Commute.refl A).mul_left (Commute.refl A)) _
  have hB := isSelfAdjoint_iff_isSymmetric.mp
    (CFC.rpow_nonneg (a := A * A) (y := (-(1 / 4) : ℝ))).isSelfAdjoint
  have hTR (x : E) : T (CFC.sqrt h♯ x) = x := metricChangeTransport_apply_sqrt_apply hh x
  have hTB (x : E) : T (B x) = q.normalizingTransport h (T x) :=
    (normalizingTransport_apply_metricChangeTransport hh x).symm
  -- Read `S` through the transport `T`, an isometry from the inner product of `E` to `h`.
  set S' : E →L[ℝ] E := CFC.sqrt h♯ * S * T
  have hTS' (x : E) : T (S' x) = S (T x) := by simp [S', hTR]
  clear_value S'
  have hsym (x y : E) : ⟪S' x, y⟫_ℝ = ⟪x, S' y⟫_ℝ := by
    rw [← apply_metricChangeTransport_metricChangeTransport hh,
      ← apply_metricChangeTransport_metricChangeTransport hh, hTS', hTS', hhS]
  -- `S'` is positive, commutes with `A`, and conjugates `A` as `B` does.
  have hS' : 0 ≤ S' := by
    refine nonneg_iff_isPositive.mpr ((isPositive_iff _).mpr ⟨hsym, fun x ↦ ?_⟩)
    rw [← apply_metricChangeTransport_metricChangeTransport hh, hTS']
    exact hpos _
  have hcomm : A * S' = S' * A := by
    refine ContinuousLinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hsym, continuousLinearMapOfBilin_apply,
      continuousLinearMapOfBilin_apply, bilinearComp_apply, bilinearComp_apply, hTS', hTS', hqS]
  -- Both `S` and the normalizing transport satisfy the normalization identity.
  have hconj : S' * A * S' = B * A * B := by
    refine ContinuousLinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hsym, mul_apply_eq_comp, mul_apply_eq_comp,
      ← coe_coe B, hB, coe_coe, continuousLinearMapOfBilin_apply,
      continuousLinearMapOfBilin_apply, bilinearComp_apply, bilinearComp_apply, hTS', hTS', hnorm,
      hTB, hTB, apply_normalizingTransport_normalizingTransport hh hq hq']
  -- Both `S'` and `B` commute with `A`, so `S' * S' * A = B * B * A`, and `A` is invertible.
  have hS'B : S' = B := (CFC.mul_self_eq_mul_self_iff S' B hS' CFC.rpow_nonneg).mp <|
    hunit.mul_left_inj.mp <| by
      rw [mul_assoc, ← hcomm, ← mul_assoc, hconj, mul_assoc, ← hBA.eq, ← mul_assoc]
  ext u
  rw [← hTR u, ← hTB, ← hTS', hS'B]

/-- **Uniqueness of the normalizing transport, through the relative spectral subspaces.** For a
symmetric nondegenerate form `q` and a positive definite `h`, an operator `S` which is self-adjoint
and positive semidefinite for `h`, self-adjoint for `q`, maps the negative and the positive
relative spectral subspaces into themselves, and carries `q` to `-h` on the first and to `h` on
the second, is the normalizing transport of `q` relative to `h`. -/
theorem eq_normalizingTransport_of_mem_relativeSpectralSubspace (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {S : E →L[ℝ] E}
    (hhS : ∀ u v, h (S u) v = h u (S v)) (hpos : ∀ u, 0 ≤ h (S u) u)
    (hqS : ∀ u v, q (S u) v = q u (S v))
    (hneg : ∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0),
      S u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) ∧
        q (S u) (S u) = -h u u)
    (hposS : ∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0),
      S u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) ∧
        q (S u) (S u) = h u u) :
    S = q.normalizingTransport h := by
  refine (eq_normalizingTransport_iff hh hq hq').mpr ⟨hhS, hpos, hqS, fun u v ↦ ?_⟩
  set P := q.negativeSpectralProjection h
  have hsymm := (isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hh).1
  have hP (w : E) : P (P w) = P w := by
    rw [← mul_apply_eq_comp, (isIdempotentElem_negativeSpectralProjection (q := q) hh).eq]
  have hIio (w : E) : P w ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) :=
    (negativeSpectralProjection_apply_eq_self_iff hh hq).mp (hP w)
  have hIoi (w : E) : w - P w ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) :=
    (negativeSpectralProjection_apply_eq_zero_iff hh hq hq').mp (by rw [map_sub, hP, sub_self])
  -- `S` carries the two subspaces to `q`-orthogonal ones.
  have hcross (w w' : E) : q (S (P w)) (S (w' - P w')) = 0 := by
    have h₁ := (negativeSpectralProjection_apply_eq_self_iff hh hq).mpr (hneg _ (hIio w)).1
    have h₂ := (negativeSpectralProjection_apply_eq_zero_iff hh hq hq').mpr (hposS _ (hIoi w')).1
    have := apply_negativeSpectralProjection_apply_sub_eq_zero (q := q) hh (S (P w)) (S (w' - P w'))
    change q (P (S (P w))) (S (w' - P w') - P (S (w' - P w'))) = 0 at this
    rwa [h₁, h₂, sub_zero] at this
  -- On each subspace, polarize the identity for `q (S x) (S x)`.
  have hpol {M : Submodule ℝ E} {ε : ℝ} (hM : ∀ x ∈ M, q (S x) (S x) = ε * h x x) {x y : E}
      (hx : x ∈ M) (hy : y ∈ M) : q (S x) (S y) = ε * h x y := by
    have := hM _ (M.add_mem hx hy)
    simp only [map_add, add_apply, hM x hx, hM y hy, hq (S y) (S x), hsymm y x] at this
    linear_combination this / 2
  have e₁ := hpol (ε := -1) (fun x hx ↦ by rw [(hneg x hx).2]; ring) (hIio u) (hIio v)
  have e₂ := hpol (ε := 1) (fun x hx ↦ by rw [(hposS x hx).2]; ring) (hIoi u) (hIoi v)
  -- Split `u` and `v` along the two subspaces; the cross terms vanish for `q` and for `h`.
  have hsplit {B : E →L[ℝ] E →L[ℝ] ℝ} (x y : E) : B x y =
      B (P x) (P y) + B (P x) (y - P y) + B (x - P x) (P y) + B (x - P x) (y - P y) := by
    conv_lhs => rw [show x = P x + (x - P x) by abel, show y = P y + (y - P y) by abel]
    simp only [map_add, add_apply]
    ring
  have hSP (w : E) : S w = S (P w) + S (w - P w) := by rw [← map_add, add_sub_cancel]
  rw [hSP u, hSP v, hsplit (B := h) u v]
  simp only [map_add, add_apply]
  rw [hq (S (u - P u)) (S (P v)), hcross, hcross, e₁, e₂,
    metric_apply_negativeSpectralProjection_apply_sub_eq_zero (q := q) hh,
    hsymm (u - P u) (P v), metric_apply_negativeSpectralProjection_apply_sub_eq_zero (q := q) hh]
  ring

/-- **Naturality of the normalizing transport.** Pulling the form and the metric back along a
linear equivalence `e` conjugates the normalizing transport by `e`. -/
theorem normalizingTransport_bilinearComp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F ≃L[ℝ] E) (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    (q.bilinearComp (e : F →L[ℝ] E) (e : F →L[ℝ] E)).normalizingTransport
        (h.bilinearComp (e : F →L[ℝ] E) (e : F →L[ℝ] E)) =
      (e.symm : E →L[ℝ] F) ∘L q.normalizingTransport h ∘L (e : F →L[ℝ] E) := by
  obtain ⟨hhN, hposN, hqN, hnormN⟩ := (eq_normalizingTransport_iff hh hq hq').mp rfl
  refine ((eq_normalizingTransport_iff
    (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv h e hh)
    (fun u v ↦ hq _ _) (injective_bilinearComp hq' e.bijective)).mpr
    ⟨fun u v ↦ ?_, fun u ↦ ?_, fun u v ↦ ?_, fun u v ↦ ?_⟩).symm <;>
  simp only [negativeSpectralProjection_bilinearComp e hh hq hq', coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, bilinearComp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  · exact hhN _ _
  · exact hposN _
  · exact hqN _ _
  · exact hnormN _ _

/-! ### Smooth dependence -/

/-- **The normalizing transport depends smoothly on the form and the metric**, including real
analytically, as long as the form stays symmetric and nondegenerate and the metric positive
definite. Smoothness is within this set of pairs, not on an open subset of all pairs of forms. -/
theorem contDiffOn_normalizingTransport {n : ℕ∞ω} :
    ContDiffOn ℝ n
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.normalizingTransport p.2)
      {p | (∀ u v, p.1 u v = p.1 v u) ∧ Function.Injective p.1 ∧ IsStrictlyPositive p.2♯} := by
  set U := {p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) |
    (∀ u v, p.1 u v = p.1 v u) ∧ Function.Injective p.1 ∧ IsStrictlyPositive p.2♯}
  have hT : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      p.2.metricChangeTransport) U :=
    contDiff_snd.contDiffOn.metricChangeTransport fun p hp ↦ hp.2.2
  have hS : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      CFC.sqrt p.2♯) U :=
    contDiff_snd.contDiffOn.sqrt_continuousLinearMapOfBilin fun p hp ↦ hp.2.2
  -- The Riesz operator of the pulled-back form is smooth in the pair, and its square stays
  -- strictly positive.
  have hA : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      (p.1.bilinearComp p.2.metricChangeTransport p.2.metricChangeTransport)♯) U :=
    contDiff_continuousLinearMapOfBilin.comp_contDiffOn
      (contDiff_fst.contDiffOn.clm_bilinearComp hT hT)
  have hB := (contDiffOn_rpow (E := E) (n := n) (-(1 / 4))).comp (hA.mul hA) fun p hp ↦
    isStrictlyPositive_mul_self_continuousLinearMapOfBilin_bilinearComp hp.2.2 hp.1 hp.2.1
  exact (hT.mul hB).mul hS

/-- **A smooth family of nondegenerate forms and positive definite metrics has a smooth family
of normalizing transports.** -/
theorem _root_.ContDiffOn.normalizingTransport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ∞ω} {s : Set F} {q h : F → E →L[ℝ] E →L[ℝ] ℝ}
    (hqd : ContDiffOn ℝ n q s) (hhd : ContDiffOn ℝ n h s) (hq : ∀ x ∈ s, ∀ u v, q x u v = q x v u)
    (hq' : ∀ x ∈ s, Function.Injective (q x)) (hh : ∀ x ∈ s, IsStrictlyPositive (h x)♯) :
    ContDiffOn ℝ n (fun x ↦ (q x).normalizingTransport (h x)) s :=
  contDiffOn_normalizingTransport.comp (hqd.prodMk hhd) fun x hx ↦ ⟨hq x hx, hq' x hx, hh x hx⟩

end ContinuousLinearMap

/-! ### Finite-dimensional normed spaces -/

namespace TauCeti

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

open ContinuousLinearMap in
/-- **Smooth normalization of nondegenerate forms on a finite-dimensional normed space.** There is
a family `Ψ` of invertible operators of `P`, indexed by the pairs `(q, h)` of a symmetric
nondegenerate bilinear form `q` and a positive definite symmetric bilinear form `h`, which depends
real analytically on the pair, is self-adjoint and positive definite for `h` and self-adjoint for
`q`, maps the negative and the positive relative spectral subspaces of `q` with respect to `h` into
themselves, and carries `q` to `-h` on the negative one and to `h` on the positive one. As these
subspaces are complementary and orthogonal for both `q` and `h`, `Ψ` carries `q` to
`h (u⁺, u⁺) - h (u⁻, u⁻)` for `u = u⁻ + u⁺`. These properties determine `Ψ (q, h)` uniquely, even
with positive definiteness weakened to positive semidefiniteness: any operator with them is
`Ψ (q, h)`. So `Ψ (q, h)` is the normalizing transport `ContinuousLinearMap.normalizingTransport`
for any inner product on `P`
(`ContinuousLinearMap.eq_normalizingTransport_of_mem_relativeSpectralSubspace`), but no inner
product on `P` is needed. -/
theorem exists_contDiffOn_apply_eq_of_mem_relativeSpectralSubspace :
    ∃ Ψ : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) → P →L[ℝ] P,
      ContDiffOn ℝ ω Ψ {x | (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧
        (∀ u v, x.2 u v = x.2 v u) ∧ ∀ u, u ≠ 0 → 0 < x.2 u u} ∧
      ∀ q h : P →L[ℝ] P →L[ℝ] ℝ, (∀ u v, q u v = q v u) → Function.Injective q →
        (∀ u v, h u v = h v u) → (∀ u, u ≠ 0 → 0 < h u u) →
        IsUnit (Ψ (q, h)) ∧
        (∀ u v, h (Ψ (q, h) u) v = h u (Ψ (q, h) v)) ∧
        (∀ u, u ≠ 0 → 0 < h (Ψ (q, h) u) u) ∧
        (∀ u v, q (Ψ (q, h) u) v = q u (Ψ (q, h) v)) ∧
        (∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0),
          Ψ (q, h) u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) ∧
            q (Ψ (q, h) u) (Ψ (q, h) u) = -h u u) ∧
        (∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0),
          Ψ (q, h) u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) ∧
            q (Ψ (q, h) u) (Ψ (q, h) u) = h u u) ∧
        ∀ S : P →L[ℝ] P, (∀ u v, h (S u) v = h u (S v)) → (∀ u, 0 ≤ h (S u) u) →
          (∀ u v, q (S u) v = q u (S v)) →
          (∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0),
            S u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) ∧
              q (S u) (S u) = -h u u) →
          (∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0),
            S u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) ∧
              q (S u) (S u) = h u u) →
          S = Ψ (q, h) := by
  set W := EuclideanSpace ℝ (Fin (Module.finrank ℝ P))
  let T : P ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq (by simp [W])
  set Ts : W →L[ℝ] P := (T.symm : W →L[ℝ] P)
  refine ⟨fun x ↦ Ts ∘L (x.1.bilinearComp Ts Ts).normalizingTransport
    (x.2.bilinearComp Ts Ts) ∘L (T : P →L[ℝ] W),
    contDiffOn_conj_bilinearComp T ContinuousLinearMap.contDiffOn_normalizingTransport,
    fun q h hq hq' hh hh' ↦ ?_⟩
  -- Pulled back to `W`, a nondegenerate form and a metric on `P` stay so.
  obtain ⟨hqs, hqi, hhp⟩ : (∀ u v, q.bilinearComp Ts Ts u v = q.bilinearComp Ts Ts v u) ∧
      Function.Injective (q.bilinearComp Ts Ts) ∧
      IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (h.bilinearComp Ts Ts)) :=
    mapsTo_bilinearComp_symm T (x := (q, h)) ⟨hq, hq', hh, hh'⟩
  set N := (q.bilinearComp Ts Ts).normalizingTransport (h.bilinearComp Ts Ts)
  have hTsT (u : P) : Ts (T u) = u := T.symm_apply_apply u
  -- A vector of `P` lies in a relative spectral subspace exactly when its image in `W` lies in the
  -- relative spectral subspace of the pulled-back pair.
  have hmem {Ω : Set ℝ} {w : W} : w ∈ (h.bilinearComp Ts Ts).toBilinForm.relativeSpectralSubspace
      (q.bilinearComp Ts Ts).toBilinForm Ω ↔
        Ts w ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm Ω :=
    ContinuousLinearMap.mem_relativeSpectralSubspace_bilinearComp_iff T.symm
  dsimp only
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  refine ⟨?_, fun u v ↦ ?_, fun u hu ↦ ?_, fun u v ↦ ?_, fun u hu ↦ ⟨?_, ?_⟩, fun u hu ↦ ⟨?_, ?_⟩,
    fun S hhS hpos hqS hneg hposS ↦ ?_⟩
  · refine ContinuousLinearMap.isUnit_iff_bijective.mpr ?_
    rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact T.symm.bijective.comp ((ContinuousLinearMap.isUnit_iff_bijective.mp
      (ContinuousLinearMap.isUnit_normalizingTransport hhp hqs hqi)).comp T.bijective)
  · simpa [hTsT] using
      ContinuousLinearMap.metric_apply_normalizingTransport_left_eq_right hhp (T u) (T v)
  · simpa [hTsT] using ContinuousLinearMap.metric_apply_normalizingTransport_self_pos hhp hqs hqi
      ((map_ne_zero_iff _ T.injective).mpr hu)
  · simpa [hTsT] using
      ContinuousLinearMap.apply_normalizingTransport_left_eq_right (q := q.bilinearComp Ts Ts) hhp
        (T u) (T v)
  -- On the relative spectral subspaces, read the normalizing transport of the pulled-back pair.
  · exact hmem.mp (ContinuousLinearMap.normalizingTransport_apply_mem_relativeSpectralSubspace_Iio
      hhp hqs hqi (hmem.mpr (by rwa [hTsT])))
  · simpa [hTsT] using
      apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio
        hhp hqs hqi (u := T u) (hmem.mpr (by rwa [hTsT]))
  · exact hmem.mp (ContinuousLinearMap.normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi
      hhp hqs hqi (hmem.mpr (by rwa [hTsT])))
  · simpa [hTsT] using
      apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Ioi
        hhp hqs hqi (u := T u) (hmem.mpr (by rwa [hTsT]))
  -- Uniqueness: read `S` on `W`, where it is the normalizing transport of the pulled-back pair.
  · have hS := eq_normalizingTransport_of_mem_relativeSpectralSubspace
      (S := (T : P →L[ℝ] W) ∘L S ∘L Ts) hhp hqs hqi
      (fun x y ↦ by simpa [Ts] using hhS (Ts x) (Ts y)) (fun x ↦ by simpa [Ts] using hpos (Ts x))
      (fun x y ↦ by simpa [Ts] using hqS (Ts x) (Ts y))
      (fun x hx ↦ ⟨hmem.mpr (by simpa [Ts] using (hneg _ (hmem.mp hx)).1),
        by simpa [Ts] using (hneg _ (hmem.mp hx)).2⟩)
      (fun x hx ↦ ⟨hmem.mpr (by simpa [Ts] using (hposS _ (hmem.mp hx)).1),
        by simpa [Ts] using (hposS _ (hmem.mp hx)).2⟩)
    ext u
    simpa [Ts] using congr(Ts ($hS (T u)))

end TauCeti
