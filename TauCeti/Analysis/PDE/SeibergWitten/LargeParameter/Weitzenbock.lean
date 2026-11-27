/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting

/-!
# The curvature term of the Weitzenböck formula at large parameter

The Dirac operator of a `Spinᶜ` connection with determinant connection `A` satisfies the
Weitzenböck formula `D_A² Ψ = ∇_A*∇_A Ψ + (s / 4) Ψ + (1 / 2) F_A⁺ · Ψ`, where `s` is the scalar
curvature and the self-dual curvature acts by Clifford multiplication. On a symplectic
four-manifold Taubes perturbs the curvature equation to

`F_A⁺ = q(Ψ) + F_{A₀}⁺ - i r ω / 4 + η`,  `Ψ = √r χ`,  `χ = α u₀ + β`,

with `ω` the symplectic form, normalized by `|ω| = √2`, `u₀` a unit spinor of the `-2i`-eigenline
of Clifford multiplication by `ω`, and `β` in the complementary line. As elsewhere, imaginary
forms `i x` are indexed by real forms `x`, so that `F_A⁺` is indexed by
`q(Ψ) - (r / 4) ω + μ`, where `μ` indexes the bounded background term `F_{A₀}⁺ + η`, and the
Clifford action of `i x` is `C(ix)` (`TauCeti.SeibergWitten.cliffordRestriction`).

This file computes the Clifford action of that curvature on `χ`, which is the zeroth-order part
of the Weitzenböck formula for the normalized spinor. Write `χ = φ + β` with `P_α φ = φ` and
`P_α β = 0`, where `P_α` is the projection onto the `2`-eigenspace of `C(iω)`
(`TauCeti.SeibergWitten.cliffordProjection`). Since `C(i q(χ)) χ = (|χ|² / 2) χ`
(`TauCeti.SeibergWitten.cliffordRestriction_quadraticTwoForm_apply_self`) while `C(iω)` acts by
`2` on `φ` and by `-2` on `β`,

`C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (|χ|² - 1) χ + r β`.

The first term is the potential of a Ginzburg–Landau equation and the second is where the
asymmetry between the two summands of `W⁺` enters. Projecting onto the two lines,

`P_α C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (|χ|² - 1) φ`,
`P_β C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (|χ|² + 1) β`,

and pairing with `φ` and `β` gives `(r / 2) (|φ|² + |β|² - 1) |φ|²` and
`(r / 2) (|φ|² + |β|² + 1) |β|²`. With `φ = α u₀` and half of the curvature, these are the
potential terms `(r / 4) (|α|² + |β|² - 1) |α|²` and `(r / 4) (|α|² + |β|² + 1) |β|²` of the
projected Weitzenböck inequalities, taken as hypotheses in
`TauCeti.Analysis.PDE.SeibergWitten.GradientBound` and
`TauCeti.Analysis.PDE.SeibergWitten.L2Bounds`.

With the background term, half of the curvature acting on `χ` is
`(r / 4) (|χ|² - 1) χ + τ`, where `τ = (r / 2) β + (1 / 2) C(iμ) χ` satisfies
`Re ⟪χ, τ⟫ ≥ -(√2 / 2) |μ| |χ|²` for every two-form `μ`, independently of `r ≥ 0`. This is the
form `∇*∇χ + c (|χ|² - 1) χ + τ = 0` with `⟪τ, χ⟫ ≥ -K |χ|²` in which the maximum principle
`CovariantDerivative.IsMetricCompatible.norm_sq_le_max_of_roughLaplacian_add_eq_zero` gives
Taubes's bound `|α|² + |β|² ≤ 1 + C / r`, with `c = r / 4` and `K` bounded by the background
curvature and the scalar curvature.

Everything here is pointwise algebra on one Hermitian Clifford module; the bundles, the canonical
connection `A₀` and the Weitzenböck formula itself are not constructed here.

## Main results

All in the namespace `TauCeti.SeibergWitten`:

* `cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply`:
  `C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (|χ|² - 1) χ + r β`.
* `cliffordProjection_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply` and
  `cliffordProjection_neg_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply`: the
  projections onto the two lines.
* `re_inner_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply_canonical` and
  `re_inner_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply_complement`: the
  pairings with `φ` and `β`.
* `inv_two_smul_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_add_apply`: the
  Ginzburg–Landau form of half the perturbed curvature acting on `χ`, and
  `neg_le_re_inner_smul_add_inv_two_smul_cliffordRestriction_apply`: the lower bound on the
  pairing of its remainder with `χ`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, Section 5.1.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {ω : ⋀[ℝ]^2 V} {φ β : positiveHalfSpinors o ρ}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### The curvature term -/

section Curvature

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
include hQ hρ h₂

/-- **The curvature term of the large-parameter equations.** For `χ = φ + β` with `P_α φ = φ`
and `P_α β = 0`, the Clifford action of `i (q(√r χ) - (r / 4) ω)`, which indexes
`F_A⁺ - F_{A₀}⁺ - η` under Taubes's curvature equation, is

`C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (‖χ‖² - 1) χ + r β`. -/
theorem cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) :
    cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω)
        (φ + β) =
      (r / 2 * (‖φ + β‖ ^ 2 - 1)) • (φ + β) + r • β := by
  rw [map_sub, sub_apply, quadraticTwoForm_sqrt_smul o ρ hkl hr]
  simp only [Submodule.coe_smul, map_smul, smul_apply,
    cliffordRestriction_quadraticTwoForm_apply_self o hQ hkl hρ h₂,
    cliffordRestriction_apply_add_of_cliffordProjection o ρ hφ hβ, ← Complex.coe_smul, smul_smul]
  push_cast
  module

/-- **The curvature term on the line `P_α W⁺`.** For `χ = φ + β` with `P_α φ = φ` and
`P_α β = 0`, `P_α C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (‖χ‖² - 1) φ`: the component along the
canonical line is the Ginzburg–Landau potential. -/
theorem cliffordProjection_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) :
    cliffordProjection o ρ ω (cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω)
        (φ + β)) =
      (r / 2 * (‖φ + β‖ ^ 2 - 1)) • φ := by
  rw [cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ h₂ hφ hβ hr]
  simp [hφ, hβ]

/-- **The curvature term on the complementary line `P_β W⁺`.** For `χ = φ + β` with `P_α φ = φ`
and `P_α β = 0`, `P_β C(i (q(√r χ) - (r / 4) ω)) χ = (r / 2) (‖χ‖² + 1) β`: the potential of
`β` has the opposite sign of the constant term, so that `β` is pushed to zero at large `r`. -/
theorem cliffordProjection_neg_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) :
    cliffordProjection o ρ (-ω) (cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω)
        (φ + β)) =
      (r / 2 * (‖φ + β‖ ^ 2 + 1)) • β := by
  rw [cliffordProjection_neg_apply,
    cliffordProjection_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ
      h₂ hφ hβ hr,
    cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ h₂ hφ hβ hr]
  module

/-- **The potential of `φ`.** For `χ = φ + β` with `P_α φ = φ` and `P_α β = 0`,
`Re ⟪φ, C(i (q(√r χ) - (r / 4) ω)) χ⟫ = (r / 2) (‖φ‖² + ‖β‖² - 1) ‖φ‖²`. With `φ = α u₀` for a
unit spinor `u₀`, half of it is the term `(r / 4) (|α|² + |β|² - 1) |α|²` of the projected
Weitzenböck inequality for `|α|²`. -/
theorem re_inner_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply_canonical
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) :
    (⟪φ, cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω)
        (φ + β)⟫_ℂ).re =
      r / 2 * (‖φ‖ ^ 2 + ‖β‖ ^ 2 - 1) * ‖φ‖ ^ 2 := by
  rw [cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ h₂ hφ hβ hr,
    norm_add_sq_of_cliffordProjection o hρ hφ hβ]
  simp [inner_add_right, inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
    inner_eq_zero_of_cliffordProjection o hρ hφ hβ, ← Complex.ofReal_pow]

/-- **The potential of `β`.** For `χ = φ + β` with `P_α φ = φ` and `P_α β = 0`,
`Re ⟪β, C(i (q(√r χ) - (r / 4) ω)) χ⟫ = (r / 2) (‖φ‖² + ‖β‖² + 1) ‖β‖²`. Half of it is the term
`(r / 4) (|α|² + |β|² + 1) |β|²` of the projected Weitzenböck inequality for `|β|²`. -/
theorem re_inner_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply_complement
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) :
    (⟪β, cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω)
        (φ + β)⟫_ℂ).re =
      r / 2 * (‖φ‖ ^ 2 + ‖β‖ ^ 2 + 1) * ‖β‖ ^ 2 := by
  rw [cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ h₂ hφ hβ hr,
    norm_add_sq_of_cliffordProjection o hρ hφ hβ]
  simp [inner_add_right, inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
    inner_eq_zero_symm.1 (inner_eq_zero_of_cliffordProjection o hρ hφ hβ), ← Complex.ofReal_pow]
  ring

/-- **The Ginzburg–Landau form of the curvature term.** For `χ = φ + β` with `P_α φ = φ` and
`P_α β = 0`, and any two-form `μ`, half of the Clifford action of `i (q(√r χ) - (r / 4) ω + μ)`,
which indexes `F_A⁺` when `μ` indexes `F_{A₀}⁺ + η`, is

`(1 / 2) C(i (q(√r χ) - (r / 4) ω + μ)) χ = (r / 4) (‖χ‖² - 1) χ + τ`,
`τ = (r / 2) β + (1 / 2) C(iμ) χ`.

The remainder `τ` pairs with `χ` to at least `-(√2 / 2) ‖μ‖ ‖χ‖²`
(`neg_le_re_inner_smul_add_inv_two_smul_cliffordRestriction_apply`). -/
theorem inv_two_smul_cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_add_apply
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) (μ : ⋀[ℝ]^2 V) :
    (2⁻¹ : ℝ) • cliffordRestriction o ρ
        ((quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - (r / 4) • ω + μ)
        (φ + β) =
      (r / 4 * (‖φ + β‖ ^ 2 - 1)) • (φ + β) +
        ((r / 2) • β + (2⁻¹ : ℝ) • cliffordRestriction o ρ μ (φ + β)) := by
  rw [(cliffordRestriction o ρ).map_add, add_apply,
    cliffordRestriction_quadraticTwoForm_sqrt_smul_sub_smul_apply o hQ hkl hρ h₂ hφ hβ hr]
  module

omit h₂ in
/-- **The remainder of the Ginzburg–Landau form is bounded below.** For `χ = φ + β` with
`P_α φ = φ` and `P_α β = 0`, `r ≥ 0` and any two-form `μ`, the remainder
`τ = (r / 2) β + (1 / 2) C(iμ) χ` satisfies `Re ⟪χ, τ⟫ ≥ -(√2 / 2) ‖μ‖ ‖χ‖²`. The bound does not
depend on `r`: the term `(r / 2) β` pairs with `χ` to `(r / 2) ‖β‖² ≥ 0`, and the bound on the
`μ` term is `abs_re_inner_cliffordRestriction_apply_self_le`. -/
theorem neg_le_re_inner_smul_add_inv_two_smul_cliffordRestriction_apply
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
    (hr : 0 ≤ r) (μ : ⋀[ℝ]^2 V) :
    -(√2 / 2 * ‖μ‖ * ‖φ + β‖ ^ 2) ≤
      (⟪φ + β, (r / 2) • β + (2⁻¹ : ℝ) • cliffordRestriction o ρ μ (φ + β)⟫_ℂ).re := by
  -- The `β` term pairs to `(r / 2) ‖β‖²`.
  have hββ : (⟪φ + β, β⟫_ℂ).re = ‖β‖ ^ 2 := by
    rw [inner_add_left, inner_eq_zero_of_cliffordProjection o hρ hφ hβ, zero_add,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  -- The `μ` term pairs to `2 ⟪q(χ), μ⟫`, at least `-(√2 / 2) ‖μ‖ ‖χ‖²`.
  have hμ := neg_le_of_abs_le
    (abs_re_inner_cliffordRestriction_apply_self_le o hQ hρ μ (φ + β))
  simp only [inner_add_right, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re,
    smul_eq_mul, hββ]
  have hβ0 : 0 ≤ r / 2 * ‖β‖ ^ 2 := by positivity
  linarith

end Curvature

end TauCeti.SeibergWitten
