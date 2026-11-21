/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Euclidean pairing and coordinatewise mixed-space scaling on Minkowski space

The mixed space `mixedSpace K = ℝ^r₁ × ℂ^r₂` of a number field `K` carries Mathlib's product sup
norm, so it is not an inner product space. This file fixes the Euclidean pairing on it once:

`mixedInner K x y = ∑_{w real} x_w y_w + ∑_{w complex} Re (x_w * conj y_w)`,

in which a complex coordinate counts once. It is the inner product of Mathlib's Euclidean model
`NumberField.mixedEmbedding.euclidean.mixedSpace K`, carried to the mixed space by the continuous
linear equivalence `euclidean.toMixed` (`mixedInner_toMixed`).

On the ambient Euclidean product `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`, coordinatewise
multiplication by `c : mixedSpace K` defines an `ℝ`-linear endomorphism
`TauCeti.NumberField.mixedEmbedding.mulMixedAmbient c`, transported from `LinearMap.piMap` through
`WithLp.linearEquiv` and `NumberField.mixedEmbedding.euclidean.toMixed K`.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.mixedInner`: the Euclidean pairing of the mixed space.
* `TauCeti.NumberField.mixedEmbedding.mixedInnerBilin`: the same pairing as a bilinear form.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient c`: coordinatewise multiplication by
  `c : mixedSpace K` on `PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.mixedInner_def`: the coordinate formula for `mixedInner`.
* `TauCeti.NumberField.mixedEmbedding.mixedInner_eq_sum_stdBasis_repr`: `mixedInner` is the
  standard dot product in the coordinates of `NumberField.mixedEmbedding.stdBasis K`.
* `TauCeti.NumberField.mixedEmbedding.mixedInner_toMixed`: `euclidean.toMixed` carries the inner
  product to `mixedInner`.
* `TauCeti.NumberField.mixedEmbedding.eq_of_forall_mixedInner_eq`: a point of the mixed space is
  determined by its pairings against a basis.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_apply`: coordinatewise evaluation
  formula.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_one`: multiplying by `1` is the identity.
* `TauCeti.NumberField.mixedEmbedding.mulMixedAmbient_mul`: `mulMixedAmbient` is multiplicative in
  the scaling element `c : mixedSpace K`.
-/

public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real RealInnerProductSpace

namespace TauCeti.NumberField.mixedEmbedding

section MixedInner

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The Euclidean pairing of the mixed space,
`∑_{w real} x_w y_w + ∑_{w complex} Re (x_w * conj y_w)`, in which a complex coordinate counts
once. It is the inner product of Mathlib's Euclidean model of the mixed space
(`mixedInner_toMixed`). -/
def mixedInner (x y : mixedSpace K) : ℝ :=
  ∑ w : {w : InfinitePlace K // w.IsReal}, x.1 w * y.1 w +
    ∑ w : {w : InfinitePlace K // w.IsComplex}, (x.2 w * (starRingEnd ℂ) (y.2 w)).re

open scoped Classical in
/-- The coordinate formula for the Euclidean pairing: the sum of the products of the real
coordinates plus the sum of the real parts `Re (x_w * conj y_w)` over the complex coordinates. -/
theorem mixedInner_def (x y : mixedSpace K) :
    mixedInner K x y = ∑ w : {w : InfinitePlace K // w.IsReal}, x.1 w * y.1 w +
      ∑ w : {w : InfinitePlace K // w.IsComplex}, (x.2 w * (starRingEnd ℂ) (y.2 w)).re := by
  rw [mixedInner]

open scoped Classical in
/-- In the coordinates of `NumberField.mixedEmbedding.stdBasis K`, the Euclidean pairing
`mixedInner` is the standard dot product. -/
theorem mixedInner_eq_sum_stdBasis_repr (x y : mixedSpace K) :
    mixedInner K x y = ∑ c : index K, (stdBasis K).repr x c * (stdBasis K).repr y c := by
  rw [mixedInner_def, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Fin.sum_univ_two, stdBasis_apply_isComplex_fst, stdBasis_apply_isComplex_fst,
    stdBasis_apply_isComplex_snd, stdBasis_apply_isComplex_snd, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The Euclidean pairing is symmetric. -/
theorem mixedInner_comm (x y : mixedSpace K) : mixedInner K x y = mixedInner K y x := by
  simp only [mixedInner, mul_comm (x.1 _), Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Multiplication by a point with real coordinates, `mixedSpaceOfRealSpace r`, is symmetric for
the Euclidean pairing: its coordinates are fixed by complex conjugation. -/
theorem mixedInner_mixedSpaceOfRealSpace_mul (r : realSpace K) (x y : mixedSpace K) :
    mixedInner K (mixedSpaceOfRealSpace r * x) y =
      mixedInner K x (mixedSpaceOfRealSpace r * y) := by
  simp only [mixedInner, mixedSpaceOfRealSpace_apply, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    map_mul, Complex.conj_ofReal]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ ↦ by ring
  · exact Finset.sum_congr rfl fun _ _ ↦ by ring_nf

/-- The squared Euclidean length is the sum of the squared absolute values at the infinite
places, each complex place counted once. -/
theorem mixedInner_self_eq_sum (x : mixedSpace K) :
    mixedInner K x x = ∑ w, normAtPlace w x ^ 2 := by
  classical
  rw [mixedInner_def,
    ← Equiv.sum_comp (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)),
    ← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K ↦ w.IsReal)]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    rw [normAtPlace_apply_of_isReal w.prop, Real.norm_eq_abs, sq_abs]
    ring
  · apply Finset.sum_congr rfl
    intro w _
    rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp w.prop)]
    simp only [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    -- The subtype equivalence preserves the place; subtype eta identifies its complex coordinate.
    rfl

open scoped Classical in
/-- The squared sup norm is at most the Euclidean squared length, since the sup norm
is the maximum of the absolute values at the infinite places. -/
theorem norm_sq_le_mixedInner_self (x : mixedSpace K) : ‖x‖ ^ 2 ≤ mixedInner K x x := by
  classical
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun w ↦ normAtPlace w x)
  rw [norm_eq_sup'_normAtPlace, hw, mixedInner_self_eq_sum]
  exact Finset.single_le_sum (fun v _ ↦ sq_nonneg (normAtPlace v x)) (Finset.mem_univ w)

open scoped Classical in
/-- The squared Euclidean length of a mixed-space vector is nonnegative. -/
theorem mixedInner_self_nonneg (x : mixedSpace K) : 0 ≤ mixedInner K x x :=
  (sq_nonneg ‖x‖).trans (norm_sq_le_mixedInner_self K x)

open scoped Classical in
/-- A nonzero mixed-space vector has positive squared Euclidean length. -/
theorem mixedInner_self_pos {x : mixedSpace K} (hx : x ≠ 0) : 0 < mixedInner K x x :=
  (sq_pos_of_pos (norm_pos_iff.mpr hx)).trans_le (norm_sq_le_mixedInner_self K x)

variable {K} in
/-- Nonzero vectors of a discrete lattice have uniformly positive squared Euclidean length
in the mixed embedding. The assertion also applies to the zero lattice. -/
theorem exists_pos_le_mixedInner (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] :
    ∃ δ > 0, ∀ x : L, x ≠ 0 → δ ≤ mixedInner K x x := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set L)) 0 (by simp)
  refine ⟨ε ^ 2, sq_pos_of_pos hε, fun x hx ↦ ?_⟩
  have hεx : ε ≤ ‖x‖ := le_of_not_gt fun h ↦ hx <| by
    have := hball (by simpa using h)
    simpa using this
  rw [← Submodule.norm_coe] at hεx
  exact (pow_le_pow_left₀ hε.le hεx 2).trans (norm_sq_le_mixedInner_self K x)

open scoped Classical in
/-- **The Euclidean model carries `mixedInner`**: Mathlib's continuous linear equivalence
`euclidean.toMixed` carries the inner product of `euclidean.mixedSpace K` to `mixedInner`. -/
@[simp]
theorem mixedInner_toMixed (x y : euclidean.mixedSpace K) :
    mixedInner K (euclidean.toMixed K x) (euclidean.toMixed K y) = ⟪x, y⟫ := by
  -- `euclidean.toMixed` only forgets the `WithLp` wrappers of the Euclidean model.
  have h (z : euclidean.mixedSpace K) :
      euclidean.toMixed K z = ((WithLp.ofLp z).1.ofLp, (WithLp.ofLp z).2.ofLp) := rfl
  simp only [mixedInner, h, WithLp.prod_inner_apply, PiLp.inner_apply, real_inner_eq_re_inner ℂ,
    RCLike.inner_apply, conj_trivial, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring

open scoped Classical in
/-- The Euclidean pairing `mixedInner` as a bilinear form: the inner product of Mathlib's
Euclidean model of the mixed space, read through `euclidean.toMixed`. -/
def mixedInnerBilin : mixedSpace K →ₗ[ℝ] mixedSpace K →ₗ[ℝ] ℝ :=
  (innerₗ (euclidean.mixedSpace K)).compl₁₂ (euclidean.toMixed K).symm.toLinearMap
    (euclidean.toMixed K).symm.toLinearMap

@[simp]
theorem mixedInnerBilin_apply (x y : mixedSpace K) :
    mixedInnerBilin K x y = mixedInner K x y := by
  classical
  obtain ⟨x, rfl⟩ := (euclidean.toMixed K).surjective x
  obtain ⟨y, rfl⟩ := (euclidean.toMixed K).surjective y
  simp [mixedInnerBilin]

/-- Two points of the mixed space with the same Euclidean pairing against every vector of a basis
are equal. -/
theorem eq_of_forall_mixedInner_eq {ι : Type*} (b : Module.Basis ι ℝ (mixedSpace K))
    {u v : mixedSpace K} (h : ∀ i, mixedInner K (b i) u = mixedInner K (b i) v) : u = v := by
  classical
  have hf : (mixedInnerBilin K).flip (u - v) = 0 :=
    b.ext fun i ↦ by simp [map_sub, h]
  have h0 : mixedInner K (u - v) (u - v) = 0 := by
    rw [← mixedInnerBilin_apply, ← LinearMap.flip_apply, hf, LinearMap.zero_apply]
  obtain ⟨z, hz⟩ := (euclidean.toMixed K).surjective (u - v)
  rw [← hz, mixedInner_toMixed, inner_self_eq_zero] at h0
  rw [← sub_eq_zero, ← hz, h0, map_zero]

end MixedInner

section MulMixedAmbient

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

open Classical in
/-- Coordinatewise multiplication by `c : mixedSpace K` on the ambient Euclidean Minkowski space. -/
def mulMixedAmbient (c : mixedSpace K) :
    (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ]
      (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :=
  ((WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).trans
      (LinearEquiv.piCongrRight fun _ : ι ↦ (euclidean.toMixed K).toLinearEquiv)).symm.conj
    (LinearMap.piMap fun _ : ι ↦ Algebra.lmul ℝ (mixedSpace K) c)

/-- Coordinatewise formula for `mulMixedAmbient`. -/
@[simp]
theorem mulMixedAmbient_apply (c : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) (i : ι) :
    mulMixedAmbient c x i = (euclidean.toMixed K).symm (c * euclidean.toMixed K (x i)) := by
  simp [mulMixedAmbient, LinearEquiv.conj_apply]

/-- Multiplying by `1 : mixedSpace K` acts as the identity on the ambient Euclidean Minkowski
space. -/
@[simp]
theorem mulMixedAmbient_one :
    (mulMixedAmbient (1 : mixedSpace K) :
        (PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) →ₗ[ℝ] _) = LinearMap.id := by
  ext1 x
  ext1 i
  apply (euclidean.toMixed K).injective
  simp

/-- `mulMixedAmbient` is multiplicative in the scaling element of `mixedSpace K`. -/
theorem mulMixedAmbient_mul (c₁ c₂ : mixedSpace K)
    (x : PiLp 2 fun _ : ι ↦ euclidean.mixedSpace K) :
    mulMixedAmbient (c₁ * c₂) x = mulMixedAmbient c₁ (mulMixedAmbient c₂ x) := by
  ext1 i
  apply (euclidean.toMixed K).injective
  simp [mul_assoc]

end MulMixedAmbient

end TauCeti.NumberField.mixedEmbedding

end
