/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatWeitzenbock

/-!
# The projected Weitzenböck equations in a flat chart

Let `χ` be the normalized spinor of a solution of Taubes's large-parameter Seiberg–Witten equations
on a flat chart of an oriented four-space `V`, a `C²` field of positive half-spinors solving the
Dirac equation `D χ = 0` for the connection `d + i b`, whose real curvature `F = -db` satisfies

`F + ⋆F = (r / 4) ω - r q(χ) - η`

at the point `x`, with `ω` self-dual of norm `√2`. Taubes splits `χ = φ + β` along the two
eigenlines of the Clifford action of `ω`, `φ = P_α χ` and `β = P_β χ`, where `P_α` is
`TauCeti.SeibergWitten.cliffordProjection o ρ ω` and `P_β = 1 - P_α` is
`cliffordProjection o ρ (-ω)`. In the flat chart both projections are constant, so they commute with
the covariant derivative, and projecting the forced Weitzenböck equation
`∇*∇χ + (r / 4) (|χ|² - 1) χ + (r / 2) β + C(iη) χ / 2 = 0`
(`TauCeti.SeibergWitten.sum_covariantDeriv_eq_of_add_hodgeStar_eq`) gives the two projected
equations, with `∑ₖ ∇_{eₖ} ∇_{eₖ} = -∇*∇` in an orthonormal basis `(eₖ)`:

`∑ₖ ∇_{eₖ} ∇_{eₖ} φ = (r / 4) (|χ|² - 1) φ + P_α C(iη) χ / 2`
(`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`),
`∑ₖ ∇_{eₖ} ∇_{eₖ} β = (r / 4) (|χ|² + 1) β + P_β C(iη) χ / 2`
(`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_neg_eq_of_add_hodgeStar_eq`).

The term `(r / 2) β` drops out of the first equation and doubles the constant of the second: this is
where the asymmetry between the two lines of `W⁺` enters. Pairing with `φ` and `β`, with
`Δ |σ|² / 2 = Re ⟪σ, ∑ₖ ∇_{eₖ} ∇_{eₖ} σ⟫ + ∑ₖ |∇_{eₖ} σ|²`
(`TauCeti.SeibergWitten.laplacian_norm_sq_eq`) for the Euclidean Laplacian `Δ = div ∘ grad`, gives
the exact identities

`Δ |φ|² / 2 = ∑ₖ |∇_{eₖ} φ|² + (r / 4) (|χ|² - 1) |φ|² + Re ⟪φ, C(iη) χ⟫ / 2`,
`Δ |β|² / 2 = ∑ₖ |∇_{eₖ} β|² + (r / 4) (|χ|² + 1) |β|² + Re ⟪β, C(iη) χ⟫ / 2`,

and, since `|χ|² = |φ|² + |β|²` and `|Re ⟪σ, C(iη) χ⟫| ≤ √2 |η| |χ| |σ|`
(`TauCeti.SeibergWitten.abs_re_inner_cliffordRestriction_apply_le`), Taubes's two projected
inequalities, with a constant `√2 |η| / 2` independent of `r`:

`|-Δ |φ|² / 2 + ∑ₖ |∇_{eₖ} φ|² + (r / 4) (|φ|² + |β|² - 1) |φ|²| ≤ (√2 / 2) |η| |φ| (|φ| + |β|)`,
`|-Δ |β|² / 2 + ∑ₖ |∇_{eₖ} β|² + (r / 4) (|φ|² + |β|² + 1) |β|²| ≤ (√2 / 2) |η| |β| (|φ| + |β|)`.

These are the inequalities that the coarse bounds take as hypotheses, here derived from the
equations in a flat chart. In the Euclidean setting of the vacuum decay estimate
`TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`, the inequality for `φ` gives its hypothesis
`hW` with `a = |φ|`, `b = |β|` and `da² = ∑ₖ |∇_{eₖ} φ|²` (for `φ = α u₀` with `u₀` a constant unit
spinor, `∑ₖ |∇_{eₖ} φ|² = ∑ₖ |∇_{eₖ} α|²`), any `db ≥ 0` and any constant `C ≥ √2 |η| / 2`.
On a curved manifold the projections are not parallel and their derivatives couple the two
equations; that case, starting from the vector equation, is
`TauCeti.Analysis.PDE.SeibergWitten.LargeParameter.ProjectedWeitzenbock`.

## Main results

All in the namespace `TauCeti.SeibergWitten`:

* `sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`,
  `sum_covariantDeriv_cliffordProjection_neg_eq_of_add_hodgeStar_eq`: the projected equations for
  `φ` and `β`.
* `laplacian_norm_sq_cliffordProjection_eq_of_add_hodgeStar_eq`,
  `laplacian_norm_sq_cliffordProjection_neg_eq_of_add_hodgeStar_eq`: the identities for `Δ |φ|²`
  and `Δ |β|²`.
* `abs_neg_laplacian_norm_sq_div_two_add_le_canonical`,
  `abs_neg_laplacian_norm_sq_div_two_add_le_complement`: Taubes's projected inequalities.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, §1(d) and Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex
open InnerProductSpace Laplacian Filter
open scoped RealInnerProductSpace InnerProductSpace Topology

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  {ω : ⋀[ℝ]^2 V} (hω : o.hodgeStar hkl ω = ω) (hω₂ : ‖ω‖ ^ 2 = 2)
  {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {χ : V → positiveHalfSpinors o ρ} {x : V}

/-! ### The rough Laplacian of a field of positive spinors -/

include hQ hρ h₂ in
/-- The forced Weitzenböck equation for a field of positive half-spinors, as an identity in `W⁺`:
`∑ₖ ∇_{eₖ} ∇_{eₖ} χ = (r / 4) (|χ|² - 1) χ + (r / 2) P_β χ + C(iη) χ / 2`. -/
private theorem sum_covariantDeriv_eq_of_add_hodgeStar_eq_positiveHalfSpinors
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    ∑ k, covariantDeriv b (fun y ↦ covariantDeriv b χ y (e k)) x (e k) =
      (r / 4 * (‖χ x‖ ^ 2 - 1)) • χ x + (r / 2) • cliffordProjection o ρ (-ω) (χ x) +
        (2⁻¹ : ℝ) • cliffordRestriction o ρ η (χ x) := by
  -- Commute the sum past the inclusion `W⁺ → W`, normalized to the coercion `Subtype.val`.
  have hι := sum_covariantDeriv_covariantDeriv_continuousLinearMap_comp
    (positiveHalfSpinors o ρ).subtypeL hχ hb e
  simp only [Submodule.subtypeL_apply] at hι
  have hψ : ContDiffAt ℝ 2 (fun y ↦ (χ y : W)) x := by
    simpa [Function.comp_def] using
      hχ.continuousLinearMap_comp ((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ)
  apply Subtype.val_injective
  rw [← sum_covariantDeriv_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hψ hb hD rfl hF e, hι]

/-! ### The projected equations -/

include hQ hρ h₂ hω hω₂ in
/-- **The projected Weitzenböck equation for the canonical component.** Let `χ` be a `C²` field of
positive half-spinors solving the Dirac equation near `x`, whose curvature `F = -db` satisfies
`F + ⋆F = (r / 4) ω - r q(χ) - η` at `x`, with `ω` self-dual of norm `√2`. Then its component
`φ = P_α χ` on the canonical line satisfies, at `x`, in any orthonormal basis,

`∑ₖ ∇_{eₖ} ∇_{eₖ} φ = (r / 4) (|χ|² - 1) φ + P_α C(iη) χ / 2`. -/
theorem sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    ∑ k, covariantDeriv b
        (fun y ↦ covariantDeriv b (fun z ↦ cliffordProjection o ρ ω (χ z)) y (e k)) x (e k) =
      (r / 4 * (‖χ x‖ ^ 2 - 1)) • cliffordProjection o ρ ω (χ x) +
        (2⁻¹ : ℝ) • cliffordProjection o ρ ω (cliffordRestriction o ρ η (χ x)) := by
  rw [sum_covariantDeriv_covariantDeriv_continuousLinearMap_comp _ hχ hb e,
    sum_covariantDeriv_eq_of_add_hodgeStar_eq_positiveHalfSpinors o hQ hkl hρ h₂ hχ hb hD hF e]
  simp only [map_add, ContinuousLinearMap.map_smul_of_tower,
    cliffordProjection_cliffordProjection_neg_apply o ρ hQ hkl hω hω₂, smul_zero, add_zero]

include hQ hρ h₂ hω hω₂ in
/-- **The projected Weitzenböck equation for the complementary component.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`, the component
`β = P_β χ` of `χ` on the complementary line satisfies, at `x`, in any orthonormal basis,

`∑ₖ ∇_{eₖ} ∇_{eₖ} β = (r / 4) (|χ|² + 1) β + P_β C(iη) χ / 2`. -/
theorem sum_covariantDeriv_cliffordProjection_neg_eq_of_add_hodgeStar_eq
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    ∑ k, covariantDeriv b
        (fun y ↦ covariantDeriv b (fun z ↦ cliffordProjection o ρ (-ω) (χ z)) y (e k)) x (e k) =
      (r / 4 * (‖χ x‖ ^ 2 + 1)) • cliffordProjection o ρ (-ω) (χ x) +
        (2⁻¹ : ℝ) • cliffordProjection o ρ (-ω) (cliffordRestriction o ρ η (χ x)) := by
  rw [sum_covariantDeriv_covariantDeriv_continuousLinearMap_comp _ hχ hb e,
    sum_covariantDeriv_eq_of_add_hodgeStar_eq_positiveHalfSpinors o hQ hkl hρ h₂ hχ hb hD hF e]
  simp only [map_add, ContinuousLinearMap.map_smul_of_tower,
    cliffordProjection_neg_cliffordProjection_neg_apply o ρ hQ hkl hω hω₂]
  module

/-! ### The Laplacians of `|φ|²` and `|β|²` -/

include hρ in
/-- Pairing the projected equation with its own component: for a projection `P` fixing `σ = P ψ`,
self-adjoint by `hρ`, `Re ⟪σ, c σ + P z / 2⟫ = c |σ|² + Re ⟪σ, z⟫ / 2`. -/
private theorem re_inner_smul_add_smul_cliffordProjection {ω' : ⋀[ℝ]^2 V}
    {σ : positiveHalfSpinors o ρ} (hσ : cliffordProjection o ρ ω' σ = σ) (c : ℝ)
    (z : positiveHalfSpinors o ρ) :
    (⟪σ, c • σ + (2⁻¹ : ℝ) • cliffordProjection o ρ ω' z⟫_ℂ).re =
      c * ‖σ‖ ^ 2 + (⟪σ, z⟫_ℂ).re / 2 := by
  have hsym := (isSelfAdjoint_cliffordProjection o ω' hρ).isSymmetric σ z
  simp only [ContinuousLinearMap.coe_coe, hσ] at hsym
  have hσσ : (⟪σ, σ⟫_ℂ).re = ‖σ‖ ^ 2 := by
    rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [inner_add_right, inner_smul_right_eq_smul, inner_smul_right_eq_smul, ← hsym]
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hσσ]
  ring

include hQ hρ h₂ hω hω₂ in
/-- **The Laplacian of `|φ|²` for the canonical component.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`, the component
`φ = P_α χ` satisfies, at `x`, in any orthonormal basis,

`Δ |φ|² / 2 = ∑ₖ |∇_{eₖ} φ|² + (r / 4) (|χ|² - 1) |φ|² + Re ⟪φ, C(iη) χ⟫ / 2`. -/
theorem laplacian_norm_sq_cliffordProjection_eq_of_add_hodgeStar_eq
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    Δ (fun y ↦ ‖cliffordProjection o ρ ω (χ y)‖ ^ 2) x / 2 =
      ∑ k, ‖covariantDeriv b (fun y ↦ cliffordProjection o ρ ω (χ y)) x (e k)‖ ^ 2 +
        r / 4 * (‖χ x‖ ^ 2 - 1) * ‖cliffordProjection o ρ ω (χ x)‖ ^ 2 +
        (⟪cliffordProjection o ρ ω (χ x), cliffordRestriction o ρ η (χ x)⟫_ℂ).re / 2 := by
  have hφ : ContDiffAt ℝ 2 (fun y ↦ cliffordProjection o ρ ω (χ y)) x :=
    hχ.continuousLinearMap_comp ((cliffordProjection o ρ ω).restrictScalars ℝ)
  rw [laplacian_norm_sq_eq hφ hb e, Finset.sum_add_distrib, ← Complex.re_sum, ← inner_sum,
    sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hω hω₂ hχ hb hD hF
      e,
    re_inner_smul_add_smul_cliffordProjection o hρ
      (cliffordProjection_cliffordProjection_apply o ρ hQ hkl hω hω₂ (χ x))]
  ring

include hQ hρ h₂ hω hω₂ in
/-- **The Laplacian of `|β|²` for the complementary component.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`, the component
`β = P_β χ` satisfies, at `x`, in any orthonormal basis,

`Δ |β|² / 2 = ∑ₖ |∇_{eₖ} β|² + (r / 4) (|χ|² + 1) |β|² + Re ⟪β, C(iη) χ⟫ / 2`. -/
theorem laplacian_norm_sq_cliffordProjection_neg_eq_of_add_hodgeStar_eq
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    Δ (fun y ↦ ‖cliffordProjection o ρ (-ω) (χ y)‖ ^ 2) x / 2 =
      ∑ k, ‖covariantDeriv b (fun y ↦ cliffordProjection o ρ (-ω) (χ y)) x (e k)‖ ^ 2 +
        r / 4 * (‖χ x‖ ^ 2 + 1) * ‖cliffordProjection o ρ (-ω) (χ x)‖ ^ 2 +
        (⟪cliffordProjection o ρ (-ω) (χ x), cliffordRestriction o ρ η (χ x)⟫_ℂ).re / 2 := by
  have hβ : ContDiffAt ℝ 2 (fun y ↦ cliffordProjection o ρ (-ω) (χ y)) x :=
    hχ.continuousLinearMap_comp ((cliffordProjection o ρ (-ω)).restrictScalars ℝ)
  rw [laplacian_norm_sq_eq hβ hb e, Finset.sum_add_distrib, ← Complex.re_sum, ← inner_sum,
    sum_covariantDeriv_cliffordProjection_neg_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hω hω₂ hχ hb
      hD hF e,
    re_inner_smul_add_smul_cliffordProjection o hρ
      (cliffordProjection_neg_cliffordProjection_neg_apply o ρ hQ hkl hω hω₂ (χ x))]
  ring

/-! ### Taubes's projected inequalities -/

include hQ hρ in
/-- From a projected identity to a projected inequality: if
`L / 2 = S + c |σ|² + Re ⟪σ, C(iη) ψ⟫ / 2`, then, since `|ψ| ≤ |P_α ψ| + |P_β ψ|`,
`|-L / 2 + S + c |σ|²| ≤ (√2 / 2) |η| |σ| (|P_α ψ| + |P_β ψ|)`. -/
private theorem abs_neg_div_two_add_le_of_eq {L S c : ℝ} {η : ⋀[ℝ]^2 V}
    {σ ψ : positiveHalfSpinors o ρ}
    (h : L / 2 = S + c * ‖σ‖ ^ 2 + (⟪σ, cliffordRestriction o ρ η ψ⟫_ℂ).re / 2) :
    |-L / 2 + S + c * ‖σ‖ ^ 2| ≤
      √2 / 2 * ‖η‖ * ‖σ‖ * (‖cliffordProjection o ρ ω ψ‖ + ‖cliffordProjection o ρ (-ω) ψ‖) := by
  have hs := norm_add_le (cliffordProjection o ρ ω ψ) (cliffordProjection o ρ (-ω) ψ)
  rw [cliffordProjection_apply_add_cliffordProjection_neg_apply] at hs
  have hre := abs_re_inner_cliffordRestriction_apply_le o hQ hρ η ψ σ
  have hmono : √2 * ‖η‖ * ‖ψ‖ * ‖σ‖ ≤
      √2 * ‖η‖ * ‖σ‖ * (‖cliffordProjection o ρ ω ψ‖ + ‖cliffordProjection o ρ (-ω) ψ‖) := by
    rw [mul_right_comm (√2 * ‖η‖)]
    gcongr
  have hL : -L / 2 + S + c * ‖σ‖ ^ 2 = -((⟪σ, cliffordRestriction o ρ η ψ⟫_ℂ).re / 2) := by
    rw [neg_div, h]
    ring
  rw [hL, abs_neg, abs_div, abs_two]
  linarith

include hQ hρ h₂ hω hω₂ in
/-- **Taubes's projected inequality for the canonical component.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`, the
components `φ = P_α χ` and `β = P_β χ` satisfy, at `x`, in any orthonormal basis,

`|-Δ |φ|² / 2 + ∑ₖ |∇_{eₖ} φ|² + (r / 4) (|φ|² + |β|² - 1) |φ|²| ≤ (√2 / 2) |η| |φ| (|φ| + |β|)`.

The constant `√2 |η| / 2` does not depend on `r`. -/
theorem abs_neg_laplacian_norm_sq_div_two_add_le_canonical
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    |-Δ (fun y ↦ ‖cliffordProjection o ρ ω (χ y)‖ ^ 2) x / 2 +
        ∑ k, ‖covariantDeriv b (fun y ↦ cliffordProjection o ρ ω (χ y)) x (e k)‖ ^ 2 +
        r / 4 * (‖cliffordProjection o ρ ω (χ x)‖ ^ 2 +
          ‖cliffordProjection o ρ (-ω) (χ x)‖ ^ 2 - 1) * ‖cliffordProjection o ρ ω (χ x)‖ ^ 2| ≤
      √2 / 2 * ‖η‖ * ‖cliffordProjection o ρ ω (χ x)‖ *
        (‖cliffordProjection o ρ ω (χ x)‖ + ‖cliffordProjection o ρ (-ω) (χ x)‖) := by
  rw [← norm_sq_eq_add_norm_sq_cliffordProjection o hQ hkl hω hω₂ hρ (χ x)]
  exact abs_neg_div_two_add_le_of_eq o hQ hρ
    (laplacian_norm_sq_cliffordProjection_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hω hω₂ hχ hb hD hF
      e)

include hQ hρ h₂ hω hω₂ in
/-- **Taubes's projected inequality for the complementary component.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_covariantDeriv_cliffordProjection_eq_of_add_hodgeStar_eq`, the
components `φ = P_α χ` and `β = P_β χ` satisfy, at `x`, in any orthonormal basis,

`|-Δ |β|² / 2 + ∑ₖ |∇_{eₖ} β|² + (r / 4) (|φ|² + |β|² + 1) |β|²| ≤ (√2 / 2) |η| |β| (|φ| + |β|)`.

The constant `√2 |η| / 2` does not depend on `r`. -/
theorem abs_neg_laplacian_norm_sq_div_two_add_le_complement
    (hχ : ContDiffAt ℝ 2 χ x) (hb : DifferentiableAt ℝ b x)
    (hD : flatDirac ρ b (fun y ↦ (χ y : W)) =ᶠ[𝓝 x] 0) {r : ℝ} {η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl (χ x) : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    |-Δ (fun y ↦ ‖cliffordProjection o ρ (-ω) (χ y)‖ ^ 2) x / 2 +
        ∑ k, ‖covariantDeriv b (fun y ↦ cliffordProjection o ρ (-ω) (χ y)) x (e k)‖ ^ 2 +
        r / 4 * (‖cliffordProjection o ρ ω (χ x)‖ ^ 2 +
          ‖cliffordProjection o ρ (-ω) (χ x)‖ ^ 2 + 1) *
          ‖cliffordProjection o ρ (-ω) (χ x)‖ ^ 2| ≤
      √2 / 2 * ‖η‖ * ‖cliffordProjection o ρ (-ω) (χ x)‖ *
        (‖cliffordProjection o ρ ω (χ x)‖ + ‖cliffordProjection o ρ (-ω) (χ x)‖) := by
  rw [← norm_sq_eq_add_norm_sq_cliffordProjection o hQ hkl hω hω₂ hρ (χ x)]
  exact abs_neg_div_two_add_le_of_eq o hQ hρ
    (laplacian_norm_sq_cliffordProjection_neg_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hω hω₂ hχ hb hD
      hF e)

end TauCeti.SeibergWitten
