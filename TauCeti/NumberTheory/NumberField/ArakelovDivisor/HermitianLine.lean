/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.Basic
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree

/-!
# The hermitian line of an Arakelov divisor

An Arakelov divisor `D = (𝔞, λ)` of a number field `K` defines the hermitian line
`O(D) = (𝔞⁻¹, ‖x‖_v = e^{-λ_v / mult(v)} |x|_v)` over `Spec 𝓞 K`
(`TauCeti.ArakelovDivisor.hermitianMetric`). Its Arakelov degree, computed with any nonzero
section, is the degree `log N(𝔞) + Σ_v λ_v` of `D`
(`TauCeti.ArakelovDivisor.sectionDegree_hermitianMetric`).

Changing `D` by a principal divisor does not change `O(D)` up to isometry: multiplication by `f`
is an isometry `O(D + (f)) ≃ O(D)` (`TauCeti.ArakelovDivisor.isometryEquivAddPrincipal`). For
`D = 0` this says that `O((f))`, the line `f⁻¹ 𝓞 K` with the norms `|f|_v |x|_v`, is trivialized
isometrically by its section `f⁻¹`, not `f`
(`TauCeti.ArakelovDivisor.placeNorm_hermitianMetric_principal_inv`). Consequently `D ↦ O(D)`
descends to isometry classes on the compactified Picard group, compatibly with the degree.

## Main definitions

* `TauCeti.ArakelovDivisor.hermitianMetric`: the hermitian line `O(D)` on `𝔞⁻¹`.
* `TauCeti.ArakelovDivisor.isometryEquivAddPrincipal`: the isometry `O(D + (f)) ≃ O(D)`,
  `x ↦ f x`.

## Main results

* `TauCeti.ArakelovDivisor.placeNorm_hermitianMetric`: `‖x‖_v = e^{-λ_v / mult(v)} |x|_v`.
* `TauCeti.ArakelovDivisor.sectionDegree_hermitianMetric`: the Arakelov degree of `O(D)` is the
  degree of `D`.
* `TauCeti.ArakelovDivisor.placeNorm_hermitianMetric_principal_inv`: the section `f⁻¹` of
  `O((f))` has norm one at every infinite place.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.1–1.2,
  Proposition 1.1 and Corollaire.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace FractionalIdeal
open scoped nonZeroDivisors TensorProduct ComplexConjugate

namespace TauCeti.ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- The **hermitian line `O(D)` of an Arakelov divisor** `D = (𝔞, λ)`: the fractional ideal
`𝔞⁻¹` with the norms `‖x‖_v = e^{-λ_v / mult(v)} |x|_v` at the infinite places. -/
def hermitianMetric (D : ArakelovDivisor K) :
    HermitianMetric K ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) :=
  HermitianMetric.fractionalIdeal _ (Units.ne_zero _) fun v ↦ D.infinitePart v / v.mult

/-- The norms of `O(D)`: `‖x‖_v = e^{-λ_v / mult(v)} |x|_v`. -/
@[simp]
theorem placeNorm_hermitianMetric (D : ArakelovDivisor K) (v : InfinitePlace K)
    (x : ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    D.hermitianMetric.placeNorm v x = Real.exp (-(D.infinitePart v / v.mult)) * v x :=
  HermitianMetric.placeNorm_fractionalIdeal _ _ v x

/-- **The Arakelov degree of `O(D)` is the degree of `D`**: computed with any nonzero section,
the degree of the hermitian line `O(D)` is `log N(𝔞) + Σ_v λ_v`. -/
theorem sectionDegree_hermitianMetric (D : ArakelovDivisor K)
    {s : (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)}
    (hs : s ≠ 0) : D.hermitianMetric.sectionDegree s = degree K D := by
  rw [hermitianMetric, HermitianMetric.sectionDegree_fractionalIdeal _ _ hs, degree_apply,
    Units.val_inv_eq_inv_val, map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]
  congr 1
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  field_simp

/-- The finite part of `-(D + (f))` is `f⁻¹` times that of `-D`. -/
theorem coe_finitePart_add_principal_inv (D : ArakelovDivisor K) (f : Kˣ) :
    (((D + principal K (Additive.ofMul f)).finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton _ (f : K)⁻¹ * ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [finitePart_add, finitePart_principal, toMul_ofMul, mul_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, coe_toPrincipalIdeal, spanSingleton_inv, mul_comm]

/-- The underlying module of `O(D + (f))` is `f⁻¹` times that of `O(D)`. -/
theorem mem_finitePart_add_principal_inv_iff (D : ArakelovDivisor K) (f : Kˣ) {x : K} :
    x ∈ (((D + principal K (Additive.ofMul f)).finitePart⁻¹ :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ↔
      (f : K) * x ∈ ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_finitePart_add_principal_inv, mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, mul_inv_cancel₀ f.ne_zero, one_mul]
  · exact fun h ↦ ⟨_, h, by rw [← mul_assoc, inv_mul_cancel₀ f.ne_zero, one_mul]⟩

/-- **Principal divisors give isometric lines**: multiplication by `f` is an isometry
`O(D + (f)) ≃ O(D)`. The module of `O(D + (f))` is `f⁻¹ 𝔞⁻¹`, and its norm at `v` is
`e^{-λ_v / mult(v)} |f|_v |x|_v`, the norm of `f x` in `O(D)`. -/
def isometryEquivAddPrincipal (D : ArakelovDivisor K) (f : Kˣ) :
    HermitianMetric.IsometryEquiv (D + principal K (Additive.ofMul f)).hermitianMetric
      D.hermitianMetric where
  toFun x := ⟨f * x, (mem_finitePart_add_principal_inv_iff D f).mp x.property⟩
  invFun y := ⟨(f⁻¹ : Kˣ) * y, (mem_finitePart_add_principal_inv_iff D f).mpr (by
    rw [← mul_assoc, Units.mul_inv, one_mul]; exact y.property)⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_left_comm _ _ _)
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  form_tmul σ x y := by
    simp only [hermitianMetric, HermitianMetric.fractionalIdeal_def,
      HermitianMetric.ofIsBaseChange_form_tmul, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.subtype_apply, infinitePart_add, Pi.add_apply,
      infinitePart_principal, toMul_ofMul, apply, map_mul]
    have hm : ((InfinitePlace.mk σ).mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    have hf : 0 < ‖σ f‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr f.ne_zero)
    have key : Real.exp (-2 * ((D.infinitePart (InfinitePlace.mk σ) +
        -((InfinitePlace.mk σ).mult * Real.log ‖σ f‖)) / (InfinitePlace.mk σ).mult)) =
        Real.exp (-2 * (D.infinitePart (InfinitePlace.mk σ) / (InfinitePlace.mk σ).mult)) *
          ‖σ f‖ ^ 2 := by
      rw [show -2 * ((D.infinitePart (InfinitePlace.mk σ) +
          -((InfinitePlace.mk σ).mult * Real.log ‖σ f‖)) / (InfinitePlace.mk σ).mult) =
          -2 * (D.infinitePart (InfinitePlace.mk σ) / (InfinitePlace.mk σ).mult) +
            Real.log (‖σ f‖ ^ 2) by rw [Real.log_pow]; field_simp; ring,
        Real.exp_add, Real.exp_log (by positivity)]
    have hn : conj (σ f) * σ f = (‖σ f‖ : ℂ) ^ 2 := Complex.conj_mul' _
    rw [key, Complex.ofReal_mul, Complex.ofReal_pow]
    linear_combination (Real.exp (-2 * (D.infinitePart (InfinitePlace.mk σ) /
      (InfinitePlace.mk σ).mult)) : ℂ) * (conj (σ x) * σ y) * hn

@[simp]
theorem coe_isometryEquivAddPrincipal_apply (D : ArakelovDivisor K) (f : Kˣ)
    (x : (((D + principal K (Additive.ofMul f)).finitePart⁻¹ :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    (isometryEquivAddPrincipal D f x : K) = f * x :=
  (rfl)

/-- **The section `f⁻¹` trivializes `O((f))`**: the line `O((f))` is `f⁻¹ 𝓞 K` with the norms
`|f|_v |x|_v`, and its section `f⁻¹` has norm one at every infinite place. -/
theorem placeNorm_hermitianMetric_principal_inv (f : Kˣ) (v : InfinitePlace K) :
    (principal K (Additive.ofMul f)).hermitianMetric.placeNorm v
      ⟨(f : K)⁻¹, by
        rw [finitePart_principal, toMul_ofMul, Units.val_inv_eq_inv_val, coe_toPrincipalIdeal,
          spanSingleton_inv]
        exact mem_spanSingleton_self _ _⟩ = 1 := by
  have hm : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  have hf : 0 < v (f : K) := pos_iff.mpr f.ne_zero
  rw [placeNorm_hermitianMetric, infinitePart_principal, toMul_ofMul, neg_div, neg_neg,
    mul_div_cancel_left₀ _ hm, Real.exp_log hf, map_inv₀, mul_inv_cancel₀ hf.ne']

end TauCeti.ArakelovDivisor
