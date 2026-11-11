/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.RelativeProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Topology.Algebra.Module.BilinearForm

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
`(A * A) ^ (-(1 / 4))` commutes with `A`, and `A * (A * A) ^ (-(1 / 2))` is the difference of the
positive and negative orthogonal spectral projections of `A`
(`ContinuousLinearMap.starProjection_pointSpectralSubspace_Iio_zero_eq`).

No choice enters: `N` is the unique operator that is self-adjoint and positive definite for `h`,
self-adjoint for `q`, and normalizes `q` as above
(`ContinuousLinearMap.eq_normalizingTransport_iff`).
Consequently it does not depend on the inner product of `E`, and it is natural under linear
equivalences (`ContinuousLinearMap.normalizingTransport_bilinearComp`): normalizations computed in
two local trivializations of a vector bundle agree under the transition. It also depends smoothly,
even real analytically, on the pair `(q, h)` (`ContDiffOn.normalizingTransport`), and so does the
corresponding operator on a finite-dimensional normed space without a chosen inner product
(`TauCeti.exists_contDiffOn_normalization`).

## Main declarations

* `ContinuousLinearMap.normalizingTransport q h`: the normalizing transport of `q` relative to
  `h`.
* `ContinuousLinearMap.apply_normalizingTransport_normalizingTransport`: the normalization identity
  `q (N u) (N v) = h u v - 2 * h (P u) (P v)`.
* `ContinuousLinearMap.commute_normalizingTransport_negativeSpectralProjection`: `N` commutes with
  `P`, so it preserves the negative and positive spectral subspaces.
* `ContinuousLinearMap.isUnit_normalizingTransport`: `N` is invertible.
* `ContinuousLinearMap.eq_normalizingTransport_iff`: the characterization.
* `ContinuousLinearMap.normalizingTransport_bilinearComp`: naturality.
* `ContinuousLinearMap.contDiffOn_normalizingTransport`: smooth dependence on `(q, h)`.
* `TauCeti.exists_contDiffOn_normalization`: the normalization on a finite-dimensional normed
  space, read through the relative spectral subspaces.

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

/-! ### Operators of the construction -/

section Operator

variable {A : E →L[ℝ] E}

/-- The square of a self-adjoint invertible operator is strictly positive. -/
private theorem isStrictlyPositive_mul_self (hA : IsSelfAdjoint A) (hunit : IsUnit A) :
    IsStrictlyPositive (A * A) :=
  (hunit.mul hunit).isStrictlyPositive (by simpa only [hA.star_eq] using star_mul_self_nonneg A)

/-- A real power of `A * A` commutes with `A`. -/
private theorem commute_rpow_mul_self (s : ℝ) : Commute ((A * A) ^ s) A := by
  rw [CFC.rpow_def]
  exact Commute.cfc_nnreal (a := A * A) ((Commute.refl A).mul_left (Commute.refl A)) _

/-- `(A * A) ^ (-(1 / 4))` conjugates `A` to the difference `1 - 2 Π` of the orthogonal spectral
projections, where `Π` projects onto the negative spectral subspace. -/
private theorem rpow_mul_mul_rpow (hA : IsSelfAdjoint A) (hunit : IsUnit A) :
    (A * A) ^ (-(1 / 4) : ℝ) * A * (A * A) ^ (-(1 / 4) : ℝ) =
      1 - (2 : ℝ) • (Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection := by
  have hpos := isStrictlyPositive_mul_self hA hunit
  rw [starProjection_pointSpectralSubspace_Iio_zero_eq A hA hunit, smul_smul,
    mul_assoc, ← (commute_rpow_mul_self _).eq, ← mul_assoc, ← CFC.rpow_add hpos.isUnit,
    (commute_rpow_mul_self _).eq]
  norm_num

/-- `(A * A) ^ (-(1 / 4))` commutes with the orthogonal projection onto the negative spectral
subspace of `A`. -/
private theorem commute_rpow_starProjection (hA : IsSelfAdjoint A) (hunit : IsUnit A) (s : ℝ) :
    Commute ((A * A) ^ s)
      (Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection := by
  rw [starProjection_pointSpectralSubspace_Iio_zero_eq A hA hunit]
  refine ((Commute.one_right _).sub_right ((commute_rpow_mul_self s).mul_right ?_)).smul_right _
  rw [CFC.rpow_def, CFC.rpow_def]
  exact cfc_commute_cfc _ _ _

end Operator

/-! ### The normalization identity -/

variable {q h : E →L[ℝ] E →L[ℝ] ℝ}

/-- The Riesz operator of the pullback of a symmetric nondegenerate form along the transport of a
positive definite `h` is self-adjoint and invertible. -/
private theorem isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp
    (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    IsSelfAdjoint (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ ∧
      IsUnit (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ :=
  ⟨isSelfAdjoint_iff_isSymmetric.mpr (isSymmetric_continuousLinearMapOfBilin_bilinearComp hq),
    isUnit_iff_isUnit_toLinearMap.mpr ((LinearMap.isUnit_iff_ker_eq_bot _).mpr
      (ker_continuousLinearMapOfBilin_bilinearComp hh hq'))⟩

/-- **The normalization identity.** The normalizing transport `N` of `q` relative to `h` carries
`q` to `h` minus twice `h` on the negative spectral subspace:
`q (N u) (N v) = h u v - 2 * h (P u) (P v)` for the negative spectral projection `P`. -/
theorem apply_normalizingTransport_normalizingTransport (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) (u v : E) :
    q (q.normalizingTransport h u) (q.normalizingTransport h v) =
      h u v - 2 * h (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h v) := by
  obtain ⟨hA, hunit⟩ := isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hh hq hq'
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
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  set B := (A * A) ^ (-(1 / 4) : ℝ)
  have hB := isSelfAdjoint_iff_isSymmetric.mp
    (CFC.rpow_nonneg (a := A * A) (y := (-(1 / 4) : ℝ))).isSelfAdjoint
  simp only [mul_apply_eq_comp, hRT]
  rw [← inner_continuousLinearMapOfBilin_bilinearComp_apply]
  have h₁ := hB (A (B x)) y
  simp only [coe_coe] at h₁
  rw [← h₁, ← mul_apply_eq_comp A, ← mul_apply_eq_comp B, ← mul_assoc,
    rpow_mul_mul_rpow hA hunit, apply_metricChangeTransport_metricChangeTransport hh,
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
  obtain ⟨hA, hunit⟩ := isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hh hq hq'
  have hRT : CFC.sqrt h♯ * h.metricChangeTransport = 1 := sqrt_mul_metricChangeTransport hh
  -- Both operators are conjugates by the transport, so they commute because their cores do.
  have hconj (X Y : E →L[ℝ] E) :
      h.metricChangeTransport * X * CFC.sqrt h♯ * (h.metricChangeTransport * Y * CFC.sqrt h♯) =
        h.metricChangeTransport * (X * Y) * CFC.sqrt h♯ := by
    simp only [mul_assoc]
    rw [← mul_assoc (CFC.sqrt h♯), hRT, one_mul]
  rw [Commute, SemiconjBy, normalizingTransport_def, negativeSpectralProjection_def, hconj, hconj,
    (commute_rpow_starProjection hA hunit (-(1 / 4))).eq]

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

/-- **The normalizing transport is invertible.** -/
theorem isUnit_normalizingTransport (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u)
    (hq' : Function.Injective q) : IsUnit (q.normalizingTransport h) := by
  obtain ⟨hA, hunit⟩ := isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hh hq hq'
  exact ((isStrictlyPositive_metricChangeTransport hh).isUnit.mul
    (IsStrictlyPositive.rpow _ _ (isStrictlyPositive_mul_self hA hunit)).isUnit).mul
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
theorem metric_apply_normalizingTransport (hh : IsStrictlyPositive h♯) (u v : E) :
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
  obtain ⟨hA, hunit⟩ := isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hh hq hq'
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh u⟩
  have hx : x ≠ 0 := by rintro rfl; exact hu (map_zero _)
  rw [normalizingTransport_apply_metricChangeTransport hh,
    apply_metricChangeTransport_metricChangeTransport hh]
  exact (IsStrictlyPositive.rpow _ _ (isStrictlyPositive_mul_self hA hunit)).inner_pos_left hx

/-- **The normalizing transport is self-adjoint for `q`.** -/
theorem apply_normalizingTransport_apply (hh : IsStrictlyPositive h♯) (u v : E) :
    q (q.normalizingTransport h u) v = q u (q.normalizingTransport h v) := by
  obtain ⟨x, rfl⟩ : ∃ x, h.metricChangeTransport x = u :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh u⟩
  obtain ⟨y, rfl⟩ : ∃ y, h.metricChangeTransport y = v :=
    ⟨_, metricChangeTransport_apply_sqrt_apply hh v⟩
  rw [normalizingTransport_apply_metricChangeTransport hh,
    normalizingTransport_apply_metricChangeTransport hh,
    ← inner_continuousLinearMapOfBilin_bilinearComp_apply,
    ← inner_continuousLinearMapOfBilin_bilinearComp_apply, ← mul_apply_eq_comp,
    ← (commute_rpow_mul_self _).eq, mul_apply_eq_comp]
  exact isSelfAdjoint_iff_isSymmetric.mp (CFC.rpow_nonneg (a := _ * _) (y := _)).isSelfAdjoint _ y

/-- The negative spectral projection read through the metric change transport `T`: it sends
`T x` to `T (Π x)` for the orthogonal projection `Π` onto the negative spectral subspace of the
pulled-back form. -/
private theorem negativeSpectralProjection_apply_metricChangeTransport
    (hh : IsStrictlyPositive h♯) (x : E) :
    q.negativeSpectralProjection h (h.metricChangeTransport x) =
      h.metricChangeTransport
        ((Module.End.pointSpectralSubspace
          (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯.toLinearMap
            (Iio 0)).starProjection x) := by
  rw [negativeSpectralProjection_def]
  simp only [mul_apply_eq_comp, sqrt_apply_metricChangeTransport_apply hh]

/-! ### Characterization and naturality -/

/-- **Characterization of the normalizing transport.** For a symmetric nondegenerate form `q` and
a positive definite `h`, an operator `S` is the normalizing transport of `q` relative to `h` exactly
when it is self-adjoint and positive definite for `h`, self-adjoint for `q`, and satisfies the
normalization identity `q (S u) (S v) = h u v - 2 * h (P u) (P v)` for the negative spectral
projection `P`. In particular the normalizing transport does not depend on the inner product of
`E`. -/
theorem eq_normalizingTransport_iff (hh : IsStrictlyPositive h♯) (hq : ∀ u v, q u v = q v u)
    (hq' : Function.Injective q) {S : E →L[ℝ] E} :
    S = q.normalizingTransport h ↔
      (∀ u v, h (S u) v = h u (S v)) ∧ (∀ u, u ≠ 0 → 0 < h (S u) u) ∧
        (∀ u v, q (S u) v = q u (S v)) ∧
        ∀ u v, q (S u) (S v) =
          h u v - 2 * h (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h v) := by
  constructor
  · rintro rfl
    exact ⟨metric_apply_normalizingTransport hh, fun u hu ↦
      metric_apply_normalizingTransport_self_pos hh hq hq' hu, apply_normalizingTransport_apply hh,
      apply_normalizingTransport_normalizingTransport hh hq hq'⟩
  rintro ⟨hhS, hpos, hqS, hnorm⟩
  obtain ⟨hA, hunit⟩ := isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hh hq hq'
  set T := h.metricChangeTransport
  set R := CFC.sqrt h♯
  set A := (q.bilinearComp T T)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  set B := (A * A) ^ (-(1 / 4) : ℝ)
  have hTR (x : E) : T (R x) = x := metricChangeTransport_apply_sqrt_apply hh x
  -- Read `S` through the transport `T`, an isometry from the inner product of `E` to `h`.
  set S' : E →L[ℝ] E := R * S * T
  have hTS' (x : E) : T (S' x) = S (T x) := by simp [S', hTR]
  clear_value S'
  have hsym (x y : E) : ⟪S' x, y⟫_ℝ = ⟪x, S' y⟫_ℝ := by
    rw [← apply_metricChangeTransport_metricChangeTransport hh,
      ← apply_metricChangeTransport_metricChangeTransport hh, hTS', hTS', hhS]
  -- `S'` is positive, commutes with `A`, and conjugates `A` to `1 - 2 Π`, as `B` does.
  have hS' : 0 ≤ S' := by
    refine nonneg_iff_isPositive.mpr ((isPositive_iff _).mpr ⟨hsym, fun x ↦ ?_⟩)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [← apply_metricChangeTransport_metricChangeTransport hh, hTS']
    exact (hpos _ fun h0 ↦ hx (by
      rw [← sqrt_apply_metricChangeTransport_apply hh x, h0, map_zero])).le
  have hcomm : A * S' = S' * A := by
    ext x
    refine ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hsym,
      inner_continuousLinearMapOfBilin_bilinearComp_apply,
      inner_continuousLinearMapOfBilin_bilinearComp_apply, hTS', hTS', hqS]
  have hconj : S' * A * S' = B * A * B := by
    rw [rpow_mul_mul_rpow hA hunit]
    ext x
    refine ext_inner_right ℝ fun y ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hsym,
      inner_continuousLinearMapOfBilin_bilinearComp_apply,
      hTS', hTS', hnorm, negativeSpectralProjection_apply_metricChangeTransport hh,
      negativeSpectralProjection_apply_metricChangeTransport hh,
      apply_metricChangeTransport_metricChangeTransport hh,
      apply_metricChangeTransport_metricChangeTransport hh]
    simp only [sub_apply, one_apply_eq_self, smul_apply, inner_sub_left, real_inner_smul_left]
    rw [← Submodule.inner_starProjection_left_eq_right, ← mul_apply_eq_comp W.starProjection,
      (Submodule.isIdempotentElem_starProjection W).eq]
  -- Both `S'` and `B` commute with `A`, so `S' * S' * A = B * B * A`, and `A` is invertible.
  have hsq : S' * S' = B * B := by
    refine hunit.mul_left_inj.mp ?_
    calc S' * S' * A = S' * A * S' :=
          (mul_assoc _ _ _).trans ((congrArg (S' * ·) hcomm.symm).trans (mul_assoc _ _ _).symm)
      _ = B * A * B := hconj
      _ = B * B * A := by
        rw [mul_assoc, ← (commute_rpow_mul_self (A := A) (-(1 / 4))).eq, ← mul_assoc]
  have hS'B : S' = B := (CFC.mul_self_eq_mul_self_iff S' B hS' CFC.rpow_nonneg).mp hsq
  ext u
  rw [← hTR u, normalizingTransport_apply_metricChangeTransport hh, ← hTS', hS'B]

/-- **Naturality of the normalizing transport.** Pulling the form and the metric back along a
linear equivalence `e` conjugates the normalizing transport by `e`. -/
theorem normalizingTransport_bilinearComp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F ≃L[ℝ] E) (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    (q.bilinearComp (e : F →L[ℝ] E) (e : F →L[ℝ] E)).normalizingTransport
        (h.bilinearComp (e : F →L[ℝ] E) (e : F →L[ℝ] E)) =
      (e.symm : E →L[ℝ] F) ∘L q.normalizingTransport h ∘L (e : F →L[ℝ] E) := by
  refine ((eq_normalizingTransport_iff
    (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv h e hh)
    (fun u v ↦ hq _ _) (injective_bilinearComp hq' e.bijective)).mpr
    ⟨fun u v ↦ ?_, fun u hu ↦ ?_, fun u v ↦ ?_, fun u v ↦ ?_⟩).symm <;>
  simp only [negativeSpectralProjection_bilinearComp e hh hq hq', coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, bilinearComp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  · exact metric_apply_normalizingTransport hh _ _
  · exact metric_apply_normalizingTransport_self_pos hh hq hq'
      ((map_ne_zero_iff _ e.injective).mpr hu)
  · exact apply_normalizingTransport_apply hh _ _
  · exact apply_normalizingTransport_normalizingTransport hh hq hq' _ _

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
  have hB := (contDiffOn_rpow (E := E) (n := n) (-(1 / 4))).comp (hA.mul hA) fun p hp ↦ by
    obtain ⟨hA', hunit⟩ :=
      isSelfAdjoint_isUnit_continuousLinearMapOfBilin_bilinearComp hp.2.2 hp.1 hp.2.1
    exact isStrictlyPositive_mul_self hA' hunit
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

/-- **Smooth normalization of nondegenerate forms on a finite-dimensional normed space.** There is
a family `Ψ` of invertible operators of `P`, indexed by the pairs `(q, h)` of a symmetric
nondegenerate bilinear form `q` and a positive definite symmetric bilinear form `h`, which depends
real analytically on the pair, maps the negative and the positive relative spectral subspaces of
`q` with respect to `h` into themselves, and carries `q` to `-h` on the negative one and to `h` on
the positive one. As these subspaces are complementary and orthogonal for both `q` and `h`, `Ψ`
carries `q` to `h (u⁺, u⁺) - h (u⁻, u⁻)` for `u = u⁻ + u⁺`. No inner product on `P` is needed. -/
theorem exists_contDiffOn_normalization :
    ∃ Ψ : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) → P →L[ℝ] P,
      ContDiffOn ℝ ω Ψ {x | (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧
        (∀ u v, x.2 u v = x.2 v u) ∧ ∀ u, u ≠ 0 → 0 < x.2 u u} ∧
      ∀ q h : P →L[ℝ] P →L[ℝ] ℝ, (∀ u v, q u v = q v u) → Function.Injective q →
        (∀ u v, h u v = h v u) → (∀ u, u ≠ 0 → 0 < h u u) →
        IsUnit (Ψ (q, h)) ∧
        (∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0),
          Ψ (q, h) u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) ∧
            q (Ψ (q, h) u) (Ψ (q, h) u) = -h u u) ∧
        ∀ u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0),
          Ψ (q, h) u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) ∧
            q (Ψ (q, h) u) (Ψ (q, h) u) = h u u := by
  set W := EuclideanSpace ℝ (Fin (Module.finrank ℝ P))
  let T : P ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq (by simp [W])
  set Ts : W →L[ℝ] P := (T.symm : W →L[ℝ] P)
  -- Pulled back to `W`, a nondegenerate form and a metric on `P` stay so.
  have hpull {q h : P →L[ℝ] P →L[ℝ] ℝ} (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q)
      (hh : ∀ u v, h u v = h v u) (hh' : ∀ u, u ≠ 0 → 0 < h u u) :
      (∀ u v, q.bilinearComp Ts Ts u v = q.bilinearComp Ts Ts v u) ∧
        Function.Injective (q.bilinearComp Ts Ts) ∧
        IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (h.bilinearComp Ts Ts)) :=
    ⟨fun u v ↦ hq _ _, ContinuousLinearMap.injective_bilinearComp hq' T.symm.bijective,
      isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr ⟨fun u v ↦ hh _ _,
        fun u hu ↦ hh' _ ((map_ne_zero_iff _ T.symm.injective).mpr hu)⟩⟩
  refine ⟨fun x ↦ Ts ∘L (x.1.bilinearComp Ts Ts).normalizingTransport
    (x.2.bilinearComp Ts Ts) ∘L (T : P →L[ℝ] W), ?_, fun q h hq hq' hh hh' ↦ ?_⟩
  · have hc : ContDiff ℝ ω fun x : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) ↦
        (x.1.bilinearComp Ts Ts, x.2.bilinearComp Ts Ts) :=
      contDiffOn_univ.mp ((contDiff_fst.contDiffOn.clm_bilinearComp contDiffOn_const
        contDiffOn_const).prodMk (contDiff_snd.contDiffOn.clm_bilinearComp contDiffOn_const
        contDiffOn_const))
    exact contDiffOn_const.clm_comp
      ((ContinuousLinearMap.contDiffOn_normalizingTransport.comp hc.contDiffOn
        fun x (hx : x ∈ {x : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) |
          (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧ (∀ u v, x.2 u v = x.2 v u) ∧
            ∀ u, u ≠ 0 → 0 < x.2 u u}) ↦
          hpull hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).clm_comp contDiffOn_const)
  obtain ⟨hqs, hqi, hhp⟩ := hpull hq hq' hh hh'
  set N := (q.bilinearComp Ts Ts).normalizingTransport (h.bilinearComp Ts Ts)
  set Q := (q.bilinearComp Ts Ts).negativeSpectralProjection (h.bilinearComp Ts Ts)
  have hTsT (u : P) : Ts (T u) = u := T.symm_apply_apply u
  -- A vector of `P` lies in a relative spectral subspace exactly when its image in `W` lies in the
  -- relative spectral subspace of the pulled-back pair, which is the range or the kernel of `Q`.
  have hmem {Ω : Set ℝ} {u : P} : u ∈ h.toBilinForm.relativeSpectralSubspace q.toBilinForm Ω ↔
      T u ∈ (h.bilinearComp Ts Ts).toBilinForm.relativeSpectralSubspace
        (q.bilinearComp Ts Ts).toBilinForm Ω := by
    rw [ContinuousLinearMap.mem_relativeSpectralSubspace_bilinearComp_iff T.symm]
    simp
  have hrange {w : W} : w ∈ (h.bilinearComp Ts Ts).toBilinForm.relativeSpectralSubspace
      (q.bilinearComp Ts Ts).toBilinForm (Iio 0) ↔ Q w = w := by
    rw [← ContinuousLinearMap.range_negativeSpectralProjection hhp hqs]
    exact LinearMap.IsIdempotentElem.mem_range_iff
      congr(($(ContinuousLinearMap.isIdempotentElem_negativeSpectralProjection
        (q := q.bilinearComp Ts Ts) hhp) : W →ₗ[ℝ] W))
  have hker {w : W} : w ∈ (h.bilinearComp Ts Ts).toBilinForm.relativeSpectralSubspace
      (q.bilinearComp Ts Ts).toBilinForm (Ioi 0) ↔ Q w = 0 := by
    rw [← ContinuousLinearMap.ker_negativeSpectralProjection hhp hqs hqi]
    rfl
  have hval (u : P) : q (Ts (N (T u))) (Ts (N (T u))) =
      h u u - 2 * h (Ts (Q (T u))) (Ts (Q (T u))) := by
    have := ContinuousLinearMap.apply_normalizingTransport_normalizingTransport hhp hqs hqi
      (T u) (T u)
    simpa [hTsT] using this
  have hTTs (w : W) : T (Ts w) = w := T.apply_symm_apply w
  dsimp only
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  refine ⟨?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
  · refine ContinuousLinearMap.isUnit_iff_bijective.mpr ?_
    rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact T.symm.bijective.comp ((ContinuousLinearMap.isUnit_iff_bijective.mp
      (ContinuousLinearMap.isUnit_normalizingTransport hhp hqs hqi)).comp T.bijective)
  · -- On the negative subspace `Q` is the identity, so `N` stays there and `q` becomes `-h`.
    have hQ : Q (T u) = T u := hrange.mp (hmem.mp hu)
    refine ⟨hmem.mpr ?_, ?_⟩
    · rw [hTTs, hrange]
      exact ContinuousLinearMap.negativeSpectralProjection_normalizingTransport_eq_self hhp hqs hqi
        hQ
    · rw [hval, hQ, hTsT]
      ring
  · -- On the positive subspace `Q` vanishes, so `N` stays there and `q` becomes `h`.
    have hQ : Q (T u) = 0 := hker.mp (hmem.mp hu)
    refine ⟨hmem.mpr ?_, ?_⟩
    · rw [hTTs, hker]
      exact ContinuousLinearMap.negativeSpectralProjection_normalizingTransport_eq_zero
        hhp hqs hqi hQ
    · rw [hval, hQ, map_zero, map_zero]
      ring

end TauCeti
