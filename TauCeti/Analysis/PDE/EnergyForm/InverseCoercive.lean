/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.InverseCoercive
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# Normalizing inverse-coercive coefficients in the `H¹` energy form

Let `a` be a measurable coefficient field which is uniformly elliptic on `Ω` in the
almost-everywhere inverse-coercive sense (`TauCeti.PDE.IsUniformlyEllipticAE`) with constants
`λ, Λ`. Dividing `a` by `λ` multiplies the energy form `a(u, v)` on `H¹(Ω)` by `λ⁻¹` and
normalizes the constants to `(1, Λ / λ)`; changing the result on a null set gives a field
satisfying the pointwise operator-bound predicate `TauCeti.PDE.UniformlyEllipticOn` everywhere
on `Ω`, without changing the energy form. This lets estimates proved for the operator-bound
predicate be applied to inverse-coercive coefficients, with constants depending only on `Λ / λ`.

* `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq`: the normalized
  field, with constants `1` and any bound `ratio` for `Λ / λ`, and the identity
  `a'(u, v) = λ⁻¹ a(u, v)`.
* `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq_zero`: a weak
  solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` is a weak solution for a measurable field satisfying the
  operator bound with constants `1` and any bound `ratio` for `Λ / λ`.
* `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_nonpos` and
  `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_nonneg`: the same for
  weak subsolutions and supersolutions.
* `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq_divergence`: a
  weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` solves the normalized equation with datum `λ⁻¹ F`.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

namespace IsUniformlyEllipticAE

/-- **Normalizing an inverse-coercive coefficient field.** For a measurable field `a` which is
inverse-coercive on `Ω` with constants `λ, Λ`, and any `ratio` with `Λ ≤ ratio · λ` (for instance
`ratio = Λ / λ`), there is a measurable field `a'` satisfying the pointwise operator-bound
predicate on `Ω` with constants `1` and `ratio` and with `a'(u, v) = λ⁻¹ a(u, v)` on `H¹(Ω)`, so
`a` and `a'` have the same weak solutions. (The construction takes `a'` equal to `λ⁻¹ a` almost
everywhere on `Ω`.) -/
theorem exists_uniformlyEllipticOn_energyFormH1_eq
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega)) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ u v : W1p mu Omega 2, energyFormH1 a' 0 0 u v = lam⁻¹ * energyFormH1 a 0 0 u v := by
  obtain ⟨a', haa', h'⟩ := (h.const_smul (inv_pos.2 h.pos)).exists_ae_eq_uniformlyEllipticOn
  rw [inv_mul_cancel₀ h.pos.ne', inv_mul_eq_div] at h'
  refine ⟨a', (h'.mono_set (subset_univ _)).mono_constants one_pos le_rfl
    ((div_le_iff₀ h.pos).2 hratio), (ha.const_smul lam⁻¹).congr haa', fun u v => ?_⟩
  rw [← energyFormH1_smul_coefficients, smul_zero, smul_zero]
  exact energyFormH1_congr_ae haa'.symm .rfl .rfl u v

/-- **Weak solutions for a normalized coefficient field.** Let `a` be measurable and
inverse-coercive on `Ω` with constants `λ, Λ`, `Λ ≤ ratio · λ`. A weak solution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, is also a weak solution for a
measurable field `a'` satisfying the pointwise operator-bound predicate on `Ω` with constants
`1` and `ratio`. -/
theorem exists_uniformlyEllipticOn_energyFormH1_eq_zero
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a' 0 0 u (v : W1p mu Omega 2) = 0 := by
  obtain ⟨a', h', ha', heq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq hratio ha
  exact ⟨a', h', ha', fun v => by rw [heq, hu v, mul_zero]⟩

/-- **Weak subsolutions for a normalized coefficient field.** Let `a` be measurable and
inverse-coercive on `Ω` with constants `λ, Λ`, `Λ ≤ ratio · λ`. A weak subsolution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, is also a weak
subsolution for a measurable field `a'` satisfying the pointwise operator-bound predicate on `Ω`
with constants `1` and `ratio`. -/
theorem exists_uniformlyEllipticOn_energyFormH1_nonpos
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a' 0 0 u (v : W1p mu Omega 2) ≤ 0 := by
  obtain ⟨a', h', ha', heq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq hratio ha
  exact ⟨a', h', ha', fun v hv => by
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 h.pos.le) (hu v hv)⟩

/-- **Weak supersolutions for a normalized coefficient field.** Let `a` be measurable and
inverse-coercive on `Ω` with constants `λ, Λ`, `Λ ≤ ratio · λ`. A weak supersolution
`u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, is
also a weak supersolution for a measurable field `a'` satisfying the pointwise operator-bound
predicate on `Ω` with constants `1` and `ratio`. -/
theorem exists_uniformlyEllipticOn_energyFormH1_nonneg
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a' 0 0 u (v : W1p mu Omega 2) := by
  obtain ⟨a', h', ha', heq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq hratio ha
  exact ⟨a', h', ha', fun v hv => by
    rw [heq]
    exact mul_nonneg (inv_nonneg.2 h.pos.le) (hu v hv)⟩

/-- **Divergence-form equations for a normalized coefficient field.** Let `a` be measurable and
inverse-coercive on `Ω` with constants `λ, Λ`, `Λ ≤ ratio · λ`. A weak solution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, is a weak
solution of `-∂ᵢ(a'ⁱʲ ∂ⱼu) = ∂ᵢ(λ⁻¹ F)ⁱ` for a measurable field `a'` satisfying the pointwise
operator-bound predicate on `Ω` with constants `1` and `ratio`. -/
theorem exists_uniformlyEllipticOn_energyFormH1_eq_divergence
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a' 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪lam⁻¹ • F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
  obtain ⟨a', h', ha', heq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq hratio ha
  refine ⟨a', h', ha', fun v => ?_⟩
  simp only [heq, hu v, inner_smul_left, RCLike.conj_to_real, integral_const_mul, mul_neg]

end IsUniformlyEllipticAE

end TauCeti.PDE
