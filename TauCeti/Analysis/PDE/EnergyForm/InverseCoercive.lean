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
* `TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq_add_divergence`:
  the same for `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, with both data divided by `λ`.

The normalization transfers the drift-free diagonal lower bounds to inverse-coercive `a`, for a
drift vanishing almost everywhere and almost everywhere bounds on the mass coefficient:

* `TauCeti.PDE.IsUniformlyEllipticAE.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift`:
  `λ/(P² + 1) ‖u‖²_{H¹} ≤ a(u, u)` when `c ≥ 0`, under a Poincaré inequality `‖u‖ ≤ P ‖∇u‖`;
* `TauCeti.PDE.IsUniformlyEllipticAE.min_mul_norm_sq_le_energyFormH1_self_of_zero_drift`:
  `min λ δ ‖u‖²_{H¹} ≤ a(u, u)` when `c ≥ δ`.
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

/-- **Weak solutions with a right-hand side for a normalized coefficient field.** Let `a` be
measurable and inverse-coercive on `Ω` with constants `λ, Λ`, `Λ ≤ ratio · λ`. A weak solution
`u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is `a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`, is a weak solution of `-∂ᵢ(a'ⁱʲ ∂ⱼu) = λ⁻¹ f + ∂ᵢ(λ⁻¹ Fⁱ)` for a measurable field
`a'` satisfying the pointwise operator-bound predicate on `Ω` with constants `1` and `ratio`. -/
theorem exists_uniformlyEllipticOn_energyFormH1_eq_add_divergence
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {ratio : ℝ}
    (hratio : Lam ≤ ratio * lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {u : W1p mu Omega 2} {f : EuclideanSpace ℝ ι → ℝ}
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a' 1 ratio ∧
      AEStronglyMeasurable a' (mu.restrict Omega) ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a' 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, (lam⁻¹ • f) x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪(lam⁻¹ • F) x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu := by
  obtain ⟨a', h', ha', heq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq hratio ha
  refine ⟨a', h', ha', fun v => ?_⟩
  simp only [heq, hu v, Pi.smul_apply, smul_eq_mul, real_inner_smul_left, mul_assoc,
    integral_const_mul, mul_sub]

/-! ### Diagonal lower bounds without drift -/

variable {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- The drift-free energy dominates the Dirichlet energy: `λ ‖∇u‖²_{L²} ≤ a(u, u)` for every
`u ∈ H¹(Ω)`, under the hypotheses of the two bounds below. -/
private theorem mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (hb : b =ᵐ[mu.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x) (u : W1p mu Omega 2) :
    lam * ‖W1p.gradient u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  -- Normalize `a` to a pointwise uniformly elliptic field `a'` with constant `1` and
  -- `a'(u, v) = λ⁻¹ a(u, v)`.
  obtain ⟨a', ha', ha'm, ha'eq⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq
    (ratio := Lam / lam) (by rw [div_mul_cancel₀ _ h.pos.ne']) ha
  have hgrad := ha'.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (b := 0) (c := 0)
    (gamma := 0) ha'm aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp)
    (fun _ _ => le_rfl) u
  rw [ha'eq, one_mul, ← energyFormH1_congr_ae .rfl hb .rfl u u] at hgrad
  calc lam * ‖W1p.gradient u‖ ^ 2 ≤ lam * (lam⁻¹ * energyFormH1 a b 0 u u) :=
        mul_le_mul_of_nonneg_left hgrad h.pos.le
    _ = energyFormH1 a b 0 u u := mul_inv_cancel_left₀ h.pos.ne' _
    _ ≤ energyFormH1 a b c u u :=
        energyFormH1_le_energyFormH1_of_mass_nonneg_ae hcoeff hc hc_nonneg u

/-- **An `H¹`-norm lower bound from a Poincaré inequality, for an inverse-coercive principal
coefficient.** For a measurable inverse-coercive principal coefficient `a` with lower constant
`λ`, a drift vanishing almost everywhere on `Ω` and an essentially bounded mass coefficient
`c ≥ 0` almost everywhere on `Ω`, if `‖u‖_{L²} ≤ P ‖∇u‖_{L²}`, then

`λ/(P² + 1) · ‖u‖²_{H¹} ≤ a(u, u)`. -/
theorem div_mul_norm_sq_le_energyFormH1_self_of_zero_drift {P : ℝ}
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (hb : b =ᵐ[mu.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    lam / (P ^ 2 + 1) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have key := h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hcoeff hc hb
    hc_nonneg u
  simpa using mul_norm_sq_le_of_gradient_sub_value_bound (P := P) (by simpa using h.pos.le)
    (A := lam) (B := 0) (by simpa using key) hu

/-- **An `H¹`-norm lower bound from a mass floor, for an inverse-coercive principal
coefficient.** For a measurable inverse-coercive principal coefficient `a` with lower constant
`λ`, a drift vanishing almost everywhere on `Ω` and an essentially bounded mass coefficient with
`δ ≤ c` almost everywhere on `Ω`,

`min λ δ · ‖u‖²_{H¹} ≤ a(u, u)`

for every `u ∈ H¹(Ω)`: the ellipticity floor controls the gradient and the mass floor controls
the value. For `δ > 0` this is coercivity on all of `H¹(Ω)`, with no Poincaré inequality and no
boundary condition. -/
theorem min_mul_norm_sq_le_energyFormH1_self_of_zero_drift {delta : ℝ}
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (hb : b =ᵐ[mu.restrict Omega] 0)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, delta ≤ c x) (u : W1p mu Omega 2) :
    min lam delta * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  -- Split off the mass floor: `a(u, u) = a_{c - δ}(u, u) + δ ‖u‖²_{L²}`, where the shifted mass
  -- `c - δ` is nonnegative almost everywhere, so the shifted form dominates `λ ‖∇u‖²`.
  have hgrad := h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha
    (memLp_energyIntegrand_mass_sub_const hcoeff delta) (hc.sub (memLp_top_const delta)) hb
    (hc_lower.mono fun x hx => sub_nonneg.2 hx) u
  rw [energyFormH1_mass_sub_const hcoeff delta, real_inner_self_eq_norm_sq] at hgrad
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [min_le_left lam delta, min_le_right lam delta, sq_nonneg ‖W1p.value u‖,
    sq_nonneg ‖W1p.gradient u‖]

end IsUniformlyEllipticAE

end TauCeti.PDE
