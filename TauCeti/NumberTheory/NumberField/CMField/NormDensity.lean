/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.SelfAdjointFiniteAdele
public import TauCeti.NumberTheory.NumberField.Global.Adeles.StandardFiniteAdeleHaar
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.NumberTheory.NumberField.Countable

/-!
# The density of a function on the finite adeles at a norm

Let `E` be a CM field with finite adeles `𝔸_f`, standard finite character `ψ_f`
(`TauCeti.GlobalNumberFields.finiteAdeleAddChar`) and self-adjoint finite adeles `𝔸_f⁺`, carrying
the Haar measure `TauCeti.selfAdjointFiniteAdeleHaar` that gives the dual lattice
`{z ∈ 𝔸_f⁺ : ψ_f(zÔ) = 1}` measure one. For a finite type `ι`, a function `Φ₀` on `𝔸_f^ι`, a
measure `μ` on `𝔸_f` and `α ∈ 𝔸_f`, the *density of `Φ₀` at the norm `α`* is the iterated
Fourier integral

`δ(Φ₀, α) = ∫_{z ∈ 𝔸_f⁺} ∫_{x ∈ 𝔸_f^ι} Φ₀(x) · ψ_f(z (x*x − α) / 2) dμ^ι(x) dz`

(`TauCeti.normDensity`), where `x*x = ∑ i, star (x i) * x i` is the standard hermitian norm.
It is the finite-adelic integral that plays the part of the singular series in Siegel's formula
for the vectors of a given norm in a definite hermitian lattice (Siegel, Weil).

The kernel depends on `α` only through its self-adjoint part, since `ψ_f(z β) = 1` for self-adjoint
`z` and `β` with `star β = −β`. Heuristically, for self-adjoint `α` and integrable data, Fourier
inversion on `𝔸_f⁺`, with the Haar measure dual to that of `z`, identifies `δ(Φ₀, α)` with the
density at `α` of the push-forward of `Φ₀ dμ^ι` under the map `x ↦ x*x` into `𝔸_f⁺`. This
interpretation is not formalised here.

The measure `μ` is a parameter: the density scales by `c ^ |ι|` when `μ` is scaled by `c`
(`MeasureTheory.Measure.normDensity_smul_measure`). The density of the roadmap uses the standard
Haar measure `TauCeti.GlobalNumberFields.standardFiniteAdeleHaar` of `𝔸_f`, for which `Ô` has
volume `vol(Ô) = 2^{r₂}/√|d_E|` in each coordinate; this is `TauCeti.standardNormDensity`. The
integrals are Bochner integrals; `δ` is the iterated integral, with no claim of absolute
convergence of the double integral.

## Main declarations

* `TauCeti.normDensity`: the density `δ(Φ₀, α)` for a measure `μ` on `𝔸_f`.
* `TauCeti.standardNormDensity`: the density `δ(Φ₀, α)` for the standard Haar measure of `𝔸_f`,
  which is `vol(Ô) ^ |ι|` times the density for the Haar measure giving `Ô` volume one
  (`TauCeti.standardNormDensity_eq_volIntegralAdeles_pow_mul`).
* `MeasureTheory.Measure.normDensity_smul`: `δ` is homogeneous in `Φ₀`.
* `MeasureTheory.Measure.normDensity_smul_measure`: scaling `μ` by `c` scales `δ` by `c ^ |ι|`.
* `MeasureTheory.Measure.conj_normDensity`: the complex conjugate of `δ(Φ₀, α)` is
  `δ(conj ∘ Φ₀, α)`; so `δ(Φ₀, α)` is real for real `Φ₀`
  (`MeasureTheory.Measure.im_normDensity_ofReal`).

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935),
  527–606.
* A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113
  (1965), 1–87.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
  MeasureTheory MeasureTheory.Measure TauCeti.GlobalNumberFields
open scoped NumberField.AdeleRing ComplexConjugate NNReal

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]

/-- The **density of `Φ₀` at the norm `α`**: the iterated Fourier integral
`δ(Φ₀, α) = ∫_{z ∈ 𝔸_f⁺} ∫_{x ∈ 𝔸_f^ι} Φ₀(x) · ψ_f(z (x*x − α) / 2) dμ^ι(x) dz`, where `z` runs over
the self-adjoint finite adeles of the CM field `E` with the Haar measure
`selfAdjointFiniteAdeleHaar E`, `x` over `𝔸_f^ι` with the product measure of `μ`, and
`x*x = star x ⬝ᵥ x` is the standard hermitian norm. -/
def normDensity (μ : Measure 𝔸ᶠ[E]) (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) : ℂ :=
  ∫ z, ∫ x, Φ₀ x * finiteAdeleAddChar E ((2 : E)⁻¹ • ((z : 𝔸ᶠ[E]) * (star x ⬝ᵥ x - α)))
    ∂Measure.pi (fun _ ↦ μ) ∂selfAdjointFiniteAdeleHaar E

/-- The **density of `Φ₀` at the norm `α`** for the standard Haar measure of the finite adeles:
the density `normDensity E (standardFiniteAdeleHaar E) Φ₀ α`, in which `x` runs over `𝔸_f^ι` with
the Haar measure for which `Ô` has volume `vol(Ô) = 2^{r₂}/√|d_E|` in each coordinate, and `z` over
the self-adjoint finite adeles with the Haar measure giving the dual lattice volume one. -/
def standardNormDensity (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) : ℂ :=
  normDensity E (standardFiniteAdeleHaar E) Φ₀ α

end TauCeti

open TauCeti

namespace MeasureTheory.Measure

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]

/-- Unfolding `normDensity` into its iterated integral. -/
theorem normDensity_def (μ : Measure 𝔸ᶠ[E]) (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) :
    normDensity E μ Φ₀ α =
      ∫ z, ∫ x, Φ₀ x * finiteAdeleAddChar E ((2 : E)⁻¹ • ((z : 𝔸ᶠ[E]) * (star x ⬝ᵥ x - α)))
        ∂Measure.pi (fun _ ↦ μ) ∂selfAdjointFiniteAdeleHaar E :=
  (rfl)

/-- The density of a constant multiple of `Φ₀` is the multiple of its density. -/
theorem normDensity_smul (μ : Measure 𝔸ᶠ[E]) (c : ℂ) (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) :
    normDensity E μ (c • Φ₀) α = c * normDensity E μ Φ₀ α := by
  simp only [normDensity_def, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

/-- The density of the zero function vanishes. -/
@[simp]
theorem normDensity_zero (μ : Measure 𝔸ᶠ[E]) (α : 𝔸ᶠ[E]) :
    normDensity E μ (0 : (ι → 𝔸ᶠ[E]) → ℂ) α = 0 := by
  simpa using normDensity_smul μ 0 0 α

/-- Scaling the measure `μ` on `𝔸_f` by `c` scales the density by `c ^ |ι|`. -/
theorem normDensity_smul_measure (μ : Measure 𝔸ᶠ[E]) [SigmaFinite μ] (c : ℝ≥0)
    (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) :
    normDensity E (c • μ) Φ₀ α = (c : ℂ) ^ Fintype.card ι * normDensity E μ Φ₀ α := by
  simp only [normDensity_def, Measure.pi_smul (fun _ : ι ↦ c) (fun _ ↦ μ),
    integral_smul_nnreal_measure, Finset.prod_const, Finset.card_univ, NNReal.smul_def,
    Complex.real_smul, NNReal.coe_pow, Complex.ofReal_pow, integral_const_mul]

/-- The density for the standard Haar measure of `𝔸_f` is `vol(Ô) ^ |ι|` times the density for
the Haar measure giving the integral finite adeles `Ô` volume one. -/
theorem _root_.TauCeti.standardNormDensity_eq_volIntegralAdeles_pow_mul
    (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) :
    standardNormDensity E Φ₀ α = (volIntegralAdeles E : ℂ) ^ Fintype.card ι *
      normDensity E (addHaarMeasure (integralAdelesPositiveCompacts (𝓞 E) E)) Φ₀ α := by
  rw [standardNormDensity, standardFiniteAdeleHaar_def]
  exact normDensity_smul_measure _ _ _ _

/-- The complex conjugate of the density of `Φ₀` is the density of the conjugate of `Φ₀`: the
conjugate of `ψ_f(z (x*x − α) / 2)` is its value at `−z`, and the Haar measure of the self-adjoint
finite adeles is invariant under `z ↦ −z`. -/
theorem conj_normDensity (μ : Measure 𝔸ᶠ[E]) (Φ₀ : (ι → 𝔸ᶠ[E]) → ℂ) (α : 𝔸ᶠ[E]) :
    conj (normDensity E μ Φ₀ α) = normDensity E μ (fun x ↦ conj (Φ₀ x)) α := by
  set π := Measure.pi fun _ : ι ↦ μ
  -- the inner integral of the density of `conj ∘ Φ₀`, as a function of `z`
  set G : selfAdjoint 𝔸ᶠ[E] → ℂ := fun z ↦ ∫ x, conj (Φ₀ x) *
    finiteAdeleAddChar E ((2 : E)⁻¹ • ((z : 𝔸ᶠ[E]) * (star x ⬝ᵥ x - α))) ∂π
  have hconj (z : selfAdjoint 𝔸ᶠ[E]) : conj (∫ x, Φ₀ x *
      finiteAdeleAddChar E ((2 : E)⁻¹ • ((z : 𝔸ᶠ[E]) * (star x ⬝ᵥ x - α))) ∂π) = G (-z) := by
    rw [← integral_conj]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    rw [map_mul, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, NegMemClass.coe_neg,
      neg_mul, smul_neg]
  calc conj (normDensity E μ Φ₀ α) = ∫ z, G (-z) ∂selfAdjointFiniteAdeleHaar E := by
        rw [normDensity_def, ← integral_conj]
        exact integral_congr_ae (.of_forall hconj)
    _ = normDensity E μ (fun x ↦ conj (Φ₀ x)) α :=
        integral_neg_eq_self G (selfAdjointFiniteAdeleHaar E)

/-- The density of a real-valued function is real. -/
theorem im_normDensity_ofReal (μ : Measure 𝔸ᶠ[E]) (Φ₀ : (ι → 𝔸ᶠ[E]) → ℝ) (α : 𝔸ᶠ[E]) :
    (normDensity E μ (fun x ↦ (Φ₀ x : ℂ)) α).im = 0 := by
  rw [← Complex.conj_eq_iff_im, conj_normDensity]
  simp

end MeasureTheory.Measure
