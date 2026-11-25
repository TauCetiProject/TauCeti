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

theorem hermitianMetric_def (D : ArakelovDivisor K) :
    D.hermitianMetric =
      HermitianMetric.fractionalIdeal _ (Units.ne_zero _) fun v ↦ D.infinitePart v / v.mult :=
  (rfl)

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
  rw [hermitianMetric_def, HermitianMetric.sectionDegree_fractionalIdeal _ _ hs, degree_apply]
  simp [mul_div_cancel₀]

/-- The finite part of `-(D + (f))` is `f⁻¹` times that of `-D`. -/
theorem coe_finitePart_add_principal_inv (D : ArakelovDivisor K) (f : Kˣ) :
    (((D + principal K (Additive.ofMul f)).finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton _ (f : K)⁻¹ * ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [finitePart_add, finitePart_principal, toMul_ofMul, mul_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, coe_toPrincipalIdeal, spanSingleton_inv, mul_comm]

/-- **Principal divisors give isometric lines**: multiplication by `f` is an isometry
`O(D + (f)) ≃ O(D)`. The module of `O(D + (f))` is `f⁻¹ 𝔞⁻¹`, and its norm at `v` is
`e^{-λ_v / mult(v)} |f|_v |x|_v`, the norm of `f x` in `O(D)`. -/
def isometryEquivAddPrincipal (D : ArakelovDivisor K) (f : Kˣ) :
    HermitianMetric.IsometryEquiv (D + principal K (Additive.ofMul f)).hermitianMetric
      D.hermitianMetric :=
  HermitianMetric.isometryEquivFractionalIdealMul _ _ f (coe_finitePart_add_principal_inv D f)
    fun v ↦ by
      rw [infinitePart_add, Pi.add_apply, add_div, infinitePart_principal_div_mult, toMul_ofMul,
        sub_eq_add_neg]

@[simp]
theorem coe_isometryEquivAddPrincipal_apply (D : ArakelovDivisor K) (f : Kˣ)
    (x : (((D + principal K (Additive.ofMul f)).finitePart⁻¹ :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    (isometryEquivAddPrincipal D f x : K) = f * x :=
  HermitianMetric.coe_isometryEquivFractionalIdealMul_apply _ _ _ _ _ x

@[simp]
theorem coe_isometryEquivAddPrincipal_symm_apply (D : ArakelovDivisor K) (f : Kˣ)
    (y : ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    ((isometryEquivAddPrincipal D f).symm y : K) = (f : K)⁻¹ * y :=
  HermitianMetric.coe_isometryEquivFractionalIdealMul_symm_apply _ _ _ _ _ y

/-- **The section `f⁻¹` trivializes `O((f))`**: the line `O((f))` is `f⁻¹ 𝓞 K` with the norms
`|f|_v |x|_v`, and its section `f⁻¹` has norm one at every infinite place. -/
theorem placeNorm_hermitianMetric_principal_inv (f : Kˣ) (v : InfinitePlace K) :
    (principal K (Additive.ofMul f)).hermitianMetric.placeNorm v
      ⟨(f : K)⁻¹, by
        simp only [finitePart_principal, toMul_ofMul, Units.val_inv_eq_inv_val,
          coe_toPrincipalIdeal, spanSingleton_inv, mem_coeToSubmodule,
          mem_spanSingleton_self]⟩ = 1 := by
  have hf : 0 < v (f : K) := pos_iff.mpr f.ne_zero
  rw [placeNorm_hermitianMetric, infinitePart_principal_div_mult, toMul_ofMul, neg_neg,
    Real.exp_log hf]
  simp [hf.ne']

end TauCeti.ArakelovDivisor
