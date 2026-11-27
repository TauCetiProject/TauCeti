/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.PositiveCone
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
import TauCeti.Analysis.Normed.Module.Basic

/-!
# Pointwise curvature bounds for the large-parameter Seiberg–Witten equations

On a symplectic four-manifold Taubes perturbs the Seiberg–Witten curvature equation by a large
multiple `r` of the symplectic form `ω`, normalized so that `|ω| = √2`:

`F_A⁺ = q(Ψ) + F_{A₀}⁺ - i r ω / 4 + η`,  `Ψ = √r (α u₀ + β)`,  `A = A₀ + 2 a`.

Here `u₀` is a unit spinor in the `-2i`-eigenline of Clifford multiplication by `ω`, `β` lies in
the complementary line, and `η` is a self-dual perturbation. This file draws the pointwise
consequences of this equation for the curvature `F_a = (F_A - F_{A₀}) / 2` of the connection `a`
on the line `E`, at one point of the manifold. Everything is phrased in terms of the real two-form
`F = i F_a`. As in `TauCeti.SeibergWitten.quadraticTwoForm`, an imaginary form `i x` is indexed by
the real form `x`, so the perturbation is indexed by a real form `η` and the curvature equation
says exactly

`F + ⋆F = (r / 4) ω - q(Ψ) - η`,

where `q(Ψ)` is the real self-dual form `TauCeti.SeibergWitten.quadraticTwoForm` of `Ψ`. We
write `φ = α u₀`, so `‖φ‖ = |α|`, and `w₊ = max (1 - |α|²) 0` for the vacuum defect. The results
are:

* **The `ω`-component.** `c = ⟪ω, F⟫ / 2 = (r / 8) (1 - |α|² + |β|²) - ⟪ω, η⟫ / 4`
  (`inner_div_two_eq_of_add_hodgeStar_eq`). This is the coefficient `c` of the metric in the
  Hermitian part `B(v, w) = (F(v, J w) + F(w, J v)) / 2` of `F`
  (`TauCeti.AlmostComplexStructure.hermitianForm_apply_eq`). Under Taubes's bounds
  `|α|² + |β|² ≤ 1 + K / r` and `|β|² ≤ (K / r) w₊ + K / r²` it satisfies
  `c = r w₊ / 8 + O(1)` (`abs_inner_div_two_sub_le`).
* **The self-dual part.** `‖2 F⁺ + η‖² ≤ (r² / 8) ((1 - |α|² + |β|²)² + 4 |α|² |β|²)`
  (`norm_add_hodgeStar_add_sq_le`), because the cross term `q'(α u₀, β)` of `q(Ψ)` is orthogonal
  to `ω`. Under the same two bounds this gives
  `|F⁺| ≤ (r / (4 √2)) w₊ + (K + 1) / (2 √2) + |η| / 2` (`norm_smul_add_hodgeStar_le`). The
  coefficient `r / (4 √2)` of `w₊` cannot be lowered: at `α = β = 0` and `η = 0` the self-dual
  part is exactly `(r / 8) ω`, of norm `r / (4 √2)`.
* **The anti-self-dual part.** If the Hermitian part of `F` is bounded below, `B ≥ -C g`, then
  `|F⁻| ≤ √2 (c + C)` (`TauCeti.AlmostComplexStructure.forall_le_hermitianForm_apply_self_iff`),
  and the formula for `c` turns this into
  `|F⁻| ≤ (r / (4 √2)) (1 - |α|² + |β|²) - ⟪ω, η⟫ / (2 √2) + √2 C`
  (`norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm`), hence into the refined bound
  `|F⁻| ≤ (r / (4 √2)) w₊ + K / (2 √2) + |η| / 2 + √2 C` (`norm_smul_sub_hodgeStar_le`).
* **The full curvature.** Adding the two bounds, `F = F⁺ + F⁻` satisfies
  `|F| ≤ (r / (2 √2)) w₊ + (2 K + 1) / (2 √2) + |η| + √2 C` (`norm_le_of_add_hodgeStar_eq`), so
  `F` is bounded independently of `r` where `w₊ = O(1 / r)`, provided `K`, `C` and `η` are
  bounded. Under the coarse anti-self-dual bound instead, the curvature is bounded by the defect
  density `δ = (r / 4) |1 - |α|² - |β|²|`: `|F| ≤ (2 + C) δ + (2 + C) (K + 1) + |η|`
  (`norm_le_of_add_hodgeStar_eq_of_norm_smul_sub_hodgeStar_le`).
* **The anti-`J`-invariant part.** The anti-self-dual part of `F` and `ω` are `J`-invariant, so
  the anti-`J`-invariant part of `F` comes from the cross term `q'(φ, β)` and from `η`:
  `D_J² F = 2 r q'(φ, β) - D_J² η / 2`, where `-D_J² / 4` is the projection onto the
  anti-`J`-invariant forms (`lieMap_lieMap_eq_of_add_hodgeStar_eq`).
* **The distance to the positive cone.** Under the coarse anti-self-dual bound
  `|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, the Hermitian part of `F` is only bounded below by
  `-(C √r w₊ / 8 + O(1)) g`, and `F` is at distance at most
  `r |α| |β| / (2 √2) + C √r w₊ / (4 √2) + C + K / (2 √2) + |η|` from the cone of positive
  `(1,1)`-forms (`infDist_positiveCone_le_of_add_hodgeStar_eq`).
* **The defect density.** The density `δ = (r / 4) |1 - |α|² - |β|²|` of Taubes's defect energy
  is bounded by the `ω`-component, `δ ≤ ⟪ω, F⟫ + K / 2 + √2 |η| / 2`
  (`div_mul_abs_one_sub_sub_le_inner_add`, from the real inequality
  `r |1 - s - t| ≤ r (1 - s + t) + 2 K` of `mul_abs_one_sub_sub_le`), and, under the coarse
  anti-self-dual bound, it bounds the Hermitian part from above,
  `B(v, v) ≤ ((1 + C / √r) δ + (1 + C) K + √2 |η| / 2 + C) |v|²`
  (`hermitianForm_apply_self_le_of_add_hodgeStar_eq`). These are the two pointwise inputs of
  Taubes's monotonicity inequality for the defect energy, with its factor `1 + C r^(-1/2)`.

The analytic inputs (the bounds on `|α|² + |β|²` and on `|β|²`, and the lower bound on the
Hermitian part or the coarse anti-self-dual bound) are hypotheses here; they come from the maximum
principle and the coupled curvature estimates for the large-parameter equations. The constants in
the conclusions depend only on the constants in these hypotheses and on the perturbation `η`, so
they are uniform in `r` and in the solution.

The anti-self-dual statements take a positively oriented orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex orientation of `J`,
and use the Kähler two-vector `ω = J.kahlerForm`, which is then self-dual of norm `√2`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Metric
open scoped RealInnerProductSpace InnerProductSpace

/-- A bound `b ≤ (K / r) m + K / r²` with `0 ≤ b`, `0 < r` and `0 ≤ m` forces `0 ≤ K`, since the
right side is `K` times a positive number. -/
private theorem nonneg_of_le_div_mul_add_div {b r K m : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hm : 0 ≤ m)
    (h : b ≤ K / r * m + K / r ^ 2) : 0 ≤ K := by
  have hpos : 0 < m / r + 1 / r ^ 2 := by positivity
  refine (mul_nonneg_iff_of_pos_right hpos).1 ?_
  calc (0 : ℝ) ≤ b := hb
    _ ≤ K / r * m + K / r ^ 2 := h
    _ = K * (m / r + 1 / r ^ 2) := by ring

/-- With `s = |φ|²` and `b = |β|²`, the bound `b ≤ (K / r) max (1 - s) 0 + K / r²` with `r ≥ 1`
gives `r b ≤ 2 K`, since `max (1 - s) 0 ≤ 1` and `K / r ≤ K`. -/
private theorem mul_le_two_mul_of_le_div_mul_add_div {s b r K : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (h : b ≤ K / r * max (1 - s) 0 + K / r ^ 2) : r * b ≤ 2 * K := by
  have hr0 : 0 < r := by linarith
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div hb hr0 (le_max_right _ _) h
  have hm : max (1 - s) 0 ≤ 1 := max_le (by linarith) zero_le_one
  have h1 : r * b ≤ r * (K / r * max (1 - s) 0 + K / r ^ 2) := by gcongr
  have h2 : r * (K / r * max (1 - s) 0 + K / r ^ 2) = K * max (1 - s) 0 + K / r := by
    field_simp
  have h3 : K / r ≤ K := div_le_self hK hr
  nlinarith

/-- The coarse anti-self-dual bound `x ≤ (r / (4 √2)) (1 + C / √r) w + C`, divided by `√2`, reads
`x / √2 ≤ r w / 8 + C √r w / 8 + C / √2`. -/
private theorem div_sqrt_two_le_of_le_mul_add {x r C w : ℝ} (hr : 0 < r)
    (h : x ≤ r / (4 * √2) * (1 + C / √r) * w + C) :
    x / √2 ≤ r / 8 * w + C * √r * w / 8 + C / √2 := by
  have hs2 : 0 < √2 := Real.sqrt_pos.2 two_pos
  have hs2sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have hsr0 : √r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  rw [div_le_iff₀ hs2]
  have hexp : r / (4 * √2) * (1 + C / √r) * w + C =
      (r / 8 * w + C * √r * w / 8 + C / √2) * √2 := by
    clear h
    grind
  exact hexp ▸ h

/-- With `s = |φ|²` and `t = |β|²`, the vacuum defect is controlled by the spinor defect:
`(r / 4) max (1 - s) 0 ≤ (r / 4) |1 - s - t| + r t / 4`. -/
private theorem div_mul_max_le_div_mul_abs_add {s t r : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    r / 4 * max (1 - s) 0 ≤ r / 4 * |1 - s - t| + r * t / 4 := by
  have h1 := le_abs_self (1 - s - t)
  have h0 := abs_nonneg (1 - s - t)
  rcases le_total (1 - s) 0 with h | h
  · rw [max_eq_right h, mul_zero]
    nlinarith [mul_nonneg hr ht, mul_nonneg hr h0]
  · rw [max_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left h1 hr]

/-- A vector `ω` with `‖ω‖² = 2`, such as a Kähler two-vector, pairs with `η` to at most
`√2 ‖η‖`: `|⟪ω, η⟫| ≤ √2 ‖η‖`. -/
private theorem abs_inner_le_sqrt_two_mul_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ω : E} (hω₂ : ‖ω‖ ^ 2 = 2) (η : E) : |⟪ω, η⟫| ≤ √2 * ‖η‖ := by
  rw [← hω₂, Real.sqrt_sq (norm_nonneg ω)]
  exact abs_real_inner_le_norm ω η

/-- The real inequality behind the self-dual curvature bound. With `s = |α|²`, `b = |β|²` and
`u = 1 / r`, the bounds `b ≤ K u max (1 - s) 0 + K u²` and `s + b ≤ 1 + K u` give
`(1 - s + b)² + 4 s b ≤ (max (1 - s) 0 + 2 (K + 1) u)²`. -/
private theorem sq_add_mul_le_sq_max_add {s b r K : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) (hr : 1 ≤ r)
    (hbK : b ≤ K / r * max (1 - s) 0 + K / r ^ 2) (hsb : s + b ≤ 1 + K / r) :
    (1 - s + b) ^ 2 + 4 * s * b ≤ (max (1 - s) 0 + 2 * (K + 1) / r) ^ 2 := by
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div hb (by linarith) (le_max_right _ _) hbK
  set u := r⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 (by linarith)
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hr
  rw [div_eq_mul_inv] at hsb ⊢
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow] at hbK
  rw [← hu] at hbK hsb ⊢
  -- In both cases the left side is `(w - b)² + 4 b` with `w = 1 - s`.
  rcases le_total s 1 with h | h
  · rw [max_eq_left (by linarith)] at hbK ⊢
    -- Here `b ≤ K u (w + u) ≤ 2 K u`, so `b² ≤ 4 K² u²` and `4 b ≤ 4 K u w + 4 K u²`.
    have hb2 : b ≤ 2 * K * u := by nlinarith
    have hbb : b ^ 2 ≤ (2 * K * u) ^ 2 := pow_le_pow_left₀ hb hb2 2
    nlinarith [mul_nonneg (sub_nonneg.2 h) hb]
  · rw [max_eq_right (by linarith)] at hbK ⊢
    -- Here `0 ≤ s - 1 + b ≤ K u` and `b ≤ K u²`.
    have h1 : (s - 1 + b) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith

/-- **The spinor defect is controlled by the `ω`-component.** If `0 ≤ t`, `0 ≤ C` and
`s + t ≤ 1 + C / r` with `r > 0`, then `r |1 - s - t| ≤ r (1 - s + t) + 2 C`. With `s = |α|²` and
`t = |β|²`, the right side is the `ω`-component of the large-parameter curvature equation up to
the constant `2 C`. -/
theorem mul_abs_one_sub_sub_le {s t r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hst : s + t ≤ 1 + C / r) :
    r * |1 - s - t| ≤ r * (1 - s + t) + 2 * C := by
  have h : r * (s + t) ≤ r + C := by
    calc r * (s + t) ≤ r * (1 + C / r) := mul_le_mul_of_nonneg_left hst hr.le
      _ = r + C := by field_simp
  rcases abs_cases (1 - s - t) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> nlinarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### The `ω`-component and the self-dual part -/

section SelfDual

variable {ω : ⋀[ℝ]^2 V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hω : o.hodgeStar hkl ω = ω) (hω₂ : ‖ω‖ ^ 2 = 2) {φ β : positiveHalfSpinors o ρ}
  (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
  {F η : ⋀[ℝ]^2 V}

include hQ hω hω₂ hφ hβ

/-- **The `ω`-component of the curvature**: if `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`, the
large-parameter curvature equation for `F = i F_a`, then
`⟪ω, F⟫ / 2 = (r / 8) (1 - ‖φ‖² + ‖β‖²) - ⟪ω, η⟫ / 4`. -/
theorem inner_div_two_eq_of_add_hodgeStar_eq (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    ⟪ω, F⟫ / 2 = r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪ω, η⟫ / 4 := by
  have h := congrArg (⟪ω, ·⟫) hF
  have hq := inner_quadraticTwoForm_sqrt_smul_add_sub_smul o hQ hkl hω₂ hφ hβ hr
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl hω] at h
  rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hω₂] at hq
  rw [real_inner_self_eq_norm_sq, hω₂] at h
  rw [real_inner_comm] at hq
  simp only [RCLike.conj_to_real] at hq
  linarith

/-- **The self-dual curvature, squared**: if `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`, then
`‖F + ⋆F + η‖² ≤ (r² / 8) ((1 - ‖φ‖² + ‖β‖²)² + 4 ‖φ‖² ‖β‖²)`. The first term is the square of
the `ω`-component and the second bounds the cross term `r q'(φ, β)`, which is orthogonal to `ω`. -/
theorem norm_add_hodgeStar_add_sq_le (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    ‖F + o.hodgeStar hkl F + η‖ ^ 2 ≤
      r ^ 2 / 8 * ((1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) ^ 2 + 4 * ‖φ‖ ^ 2 * ‖β‖ ^ 2) := by
  set X : ⋀[ℝ]^2 V := (quadraticTwoFormPolar o ρ hkl φ β : ⋀[ℝ]^2 V)
  have hX : ⟪(r / 4 * (‖φ‖ ^ 2 - ‖β‖ ^ 2 - 1)) • ω, r • X⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      inner_quadraticTwoFormPolar_of_cliffordProjection o hQ hkl hω hρ hφ hβ, mul_zero, mul_zero]
  have hsum : F + o.hodgeStar hkl F + η =
      -((r / 4 * (‖φ‖ ^ 2 - ‖β‖ ^ 2 - 1)) • ω + r • X) := by
    rw [hF, ← coe_quadraticTwoForm_sqrt_smul_add_sub_smul o hQ hkl hω hρ h₂ hφ hβ hr]
    abel
  have hXle : ‖r • X‖ ^ 2 ≤ r ^ 2 * (‖φ‖ ^ 2 * ‖β‖ ^ 2 / 2) := by
    have h := norm_quadraticTwoFormPolar_le o hQ hkl hρ φ β
    rw [norm_smul, Real.norm_of_nonneg hr, mul_pow]
    gcongr
    calc ‖X‖ ^ 2 ≤ (‖φ‖ * ‖β‖ / √2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ‖φ‖ ^ 2 * ‖β‖ ^ 2 / 2 := by rw [div_pow, Real.sq_sqrt zero_le_two, mul_pow]
  rw [hsum, norm_neg, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real hX, ← sq, ← sq, norm_smul,
    mul_pow, hω₂, Real.norm_eq_abs, sq_abs]
  nlinarith

/-- **The self-dual curvature bound**: if `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` with `r ≥ 1`,
`‖φ‖² + ‖β‖² ≤ 1 + K / r` and `‖β‖² ≤ (K / r) w₊ + K / r²`, where `w₊ = max (1 - ‖φ‖²) 0`, then
the self-dual part `F⁺ = (F + ⋆F) / 2` satisfies
`‖F⁺‖ ≤ (r / (4 √2)) w₊ + (K + 1) / (2 √2) + ‖η‖ / 2`. -/
theorem norm_smul_add_hodgeStar_le (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    ‖(2⁻¹ : ℝ) • (F + o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * max (1 - ‖φ‖ ^ 2) 0 + (K + 1) / (2 * √2) + ‖η‖ / 2 := by
  have hr0 : 0 ≤ r := by linarith
  set m := max (1 - ‖φ‖ ^ 2) 0
  have hm : 0 ≤ m := le_max_right _ _
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div (sq_nonneg _) (by linarith) hm hβK
  -- `‖2 F⁺ + η‖ ≤ (r / (2 √2)) (w₊ + 2 (K + 1) / r)`, from the squared estimate.
  have hmain : ‖F + o.hodgeStar hkl F + η‖ ≤ r / (2 * √2) * (m + 2 * (K + 1) / r) := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    refine (norm_add_hodgeStar_add_sq_le hQ hkl hω hω₂ hφ hβ hρ h₂ hr0 hF).trans ?_
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt zero_le_two]
    have h := sq_add_mul_le_sq_max_add (sq_nonneg ‖φ‖) (sq_nonneg ‖β‖) hr hβK hφβ
    calc r ^ 2 / 8 * ((1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) ^ 2 + 4 * ‖φ‖ ^ 2 * ‖β‖ ^ 2)
        ≤ r ^ 2 / 8 * (m + 2 * (K + 1) / r) ^ 2 := by gcongr
      _ = r ^ 2 / (2 ^ 2 * 2) * (m + 2 * (K + 1) / r) ^ 2 := by norm_num
  have heq : r / (2 * √2) * (m + 2 * (K + 1) / r) = r / (2 * √2) * m + (K + 1) / √2 := by
    field_simp
  have htri : ‖F + o.hodgeStar hkl F‖ ≤ ‖F + o.hodgeStar hkl F + η‖ + ‖η‖ := by
    simpa using norm_sub_le (F + o.hodgeStar hkl F + η) η
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  calc 2⁻¹ * ‖F + o.hodgeStar hkl F‖
      ≤ 2⁻¹ * (r / (2 * √2) * m + (K + 1) / √2 + ‖η‖) := by
        gcongr
        linarith
    _ = r / (4 * √2) * m + (K + 1) / (2 * √2) + ‖η‖ / 2 := by ring

/-- **The `ω`-component is `r w₊ / 8` up to a bounded error**: if
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` with `r ≥ 1`, `‖φ‖² + ‖β‖² ≤ 1 + K / r` and
`‖β‖² ≤ (K / r) w₊ + K / r²`, where `w₊ = max (1 - ‖φ‖²) 0`, then
`|⟪ω, F⟫ / 2 - r w₊ / 8| ≤ K / 4 + √2 ‖η‖ / 4`. -/
theorem abs_inner_div_two_sub_le (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    |⟪ω, F⟫ / 2 - r / 8 * max (1 - ‖φ‖ ^ 2) 0| ≤ K / 4 + √2 * ‖η‖ / 4 := by
  have hr0 : 0 < r := by linarith
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div (sq_nonneg _) hr0 (le_max_right _ _) hβK
  rw [inner_div_two_eq_of_add_hodgeStar_eq hQ hkl hω hω₂ hφ hβ hr0.le hF]
  have hωη := abs_inner_le_sqrt_two_mul_norm hω₂ η
  -- The defect part `r (1 - ‖φ‖² + ‖β‖² - w₊) / 8` lies in `[-K / 4, K / 4]`.
  have hdef : |r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - r / 8 * max (1 - ‖φ‖ ^ 2) 0| ≤ K / 4 := by
    have hKr : K / r ≤ K := div_le_self hK hr
    have hKr2 : K / r ^ 2 ≤ K / r := div_le_div_of_nonneg_left hK hr0 (by nlinarith)
    have hb := sq_nonneg ‖β‖
    have hrb : r * (K / r) = K := mul_div_cancel₀ K hr0.ne'
    have h1 : r * ‖β‖ ^ 2 ≤ 2 * K :=
      mul_le_two_mul_of_le_div_mul_add_div (sq_nonneg _) (sq_nonneg _) hr hβK
    rw [abs_le]
    rcases le_total (‖φ‖ ^ 2) 1 with h | h
    · rw [max_eq_left (by linarith)] at hβK ⊢
      constructor <;> nlinarith
    · rw [max_eq_right (by linarith)] at hβK ⊢
      have h2 : r * (‖φ‖ ^ 2 - 1 - ‖β‖ ^ 2) ≤ K := by nlinarith
      constructor <;> nlinarith
  calc |r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪ω, η⟫ / 4 - r / 8 * max (1 - ‖φ‖ ^ 2) 0|
      ≤ |r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - r / 8 * max (1 - ‖φ‖ ^ 2) 0| + |⟪ω, η⟫| / 4 := by
        rw [show r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪ω, η⟫ / 4 - r / 8 * max (1 - ‖φ‖ ^ 2) 0 =
          (r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - r / 8 * max (1 - ‖φ‖ ^ 2) 0) + -(⟪ω, η⟫ / 4) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ K / 4 + √2 * ‖η‖ / 4 := by linarith

/-- **The defect density is bounded by the `ω`-component**: if
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` with `r > 0`, `K ≥ 0` and `‖φ‖² + ‖β‖² ≤ 1 + K / r`,
then the defect density `δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|` satisfies
`δ ≤ ⟪ω, F⟫ + K / 2 + √2 ‖η‖ / 2`. Where `‖φ‖² + ‖β‖² ≤ 1` this is the formula for `⟪ω, F⟫` with
the nonnegative term `(r / 2) ‖β‖²` dropped; elsewhere `δ ≤ K / 4` and
`⟪ω, F⟫ ≥ -K / 4 - √2 ‖η‖ / 2`. This bounds the defect density by the Kähler component of `F`, as
Taubes's monotonicity inequality for the defect energy requires. -/
theorem div_mul_abs_one_sub_sub_le_inner_add (hr : 0 < r) {K : ℝ} (hK : 0 ≤ K)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| ≤ ⟪ω, F⟫ + K / 2 + √2 * ‖η‖ / 2 := by
  have h := inner_div_two_eq_of_add_hodgeStar_eq hQ hkl hω hω₂ hφ hβ hr.le hF
  have hωη : ⟪ω, η⟫ ≤ √2 * ‖η‖ := (le_abs_self _).trans (abs_inner_le_sqrt_two_mul_norm hω₂ η)
  have := mul_abs_one_sub_sub_le hr hK (sq_nonneg ‖β‖) hφβ
  linarith

end SelfDual

/-! ### The anti-self-dual part -/

section AntiSelfDual

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) {φ β : positiveHalfSpinors o ρ}
  (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
  (hβ : cliffordProjection o ρ J.kahlerForm β = 0) {r : ℝ} {F η : ⋀[ℝ]^2 V}

include h₀ h₂₃ hQ he hφ hβ

/-- **The refined anti-self-dual curvature bound, exact form**: if
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, and the Hermitian
part `B(v, w) = (F(v, J w) + F(w, J v)) / 2` of `F` satisfies `B ≥ -C g`, then the anti-self-dual
part `F⁻ = (F - ⋆F) / 2` satisfies
`‖F⁻‖ ≤ (r / (4 √2)) (1 - ‖φ‖² + ‖β‖²) - ⟪ω, η⟫ / (2 √2) + √2 C`. -/
theorem norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪J.kahlerForm, η⟫ / (2 * √2) + √2 * C := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)
  have h := AlmostComplexStructure.norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self
    h₀ h₂₃ hkl he F hC
  rw [inner_div_two_eq_of_add_hodgeStar_eq hQ hkl hω hω₂ hφ hβ hr hF] at h
  calc ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖
      ≤ √2 * (r / 8 * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪J.kahlerForm, η⟫ / 4 + C) := h
    _ = r / (4 * √2) * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) - ⟪J.kahlerForm, η⟫ / (2 * √2) + √2 * C := by
        field_simp
        rw [Real.sq_sqrt zero_le_two]
        ring

/-- **The refined anti-self-dual curvature bound**: if `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`
for the Kähler two-vector `ω` of `J`, with `r ≥ 1` and `‖β‖² ≤ (K / r) w₊ + K / r²`, where
`w₊ = max (1 - ‖φ‖²) 0`, and the Hermitian part of `F` satisfies `B ≥ -C g`, then the
anti-self-dual part `F⁻ = (F - ⋆F) / 2` satisfies
`‖F⁻‖ ≤ (r / (4 √2)) w₊ + K / (2 √2) + ‖η‖ / 2 + √2 C`. -/
theorem norm_smul_sub_hodgeStar_le (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * max (1 - ‖φ‖ ^ 2) 0 + K / (2 * √2) + ‖η‖ / 2 + √2 * C := by
  have hr0 : 0 < r := by linarith
  have h := norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm h₀ h₂₃ hQ hkl he hφ hβ hr0.le
    hF hC
  set m := max (1 - ‖φ‖ ^ 2) 0
  -- `1 - ‖φ‖² ≤ w₊` and `r ‖β‖² ≤ K w₊ + K / r ≤ 2 K`.
  have hm1 : 1 - ‖φ‖ ^ 2 ≤ m := le_max_left _ _
  have hrb : r * ‖β‖ ^ 2 ≤ 2 * K :=
    mul_le_two_mul_of_le_div_mul_add_div (sq_nonneg _) (sq_nonneg _) hr hβK
  -- `-⟪ω, η⟫ ≤ ‖ω‖ ‖η‖ = √2 ‖η‖`.
  have hωη : -⟪J.kahlerForm, η⟫ ≤ √2 * ‖η‖ :=
    (neg_le_abs _).trans <| abs_inner_le_sqrt_two_mul_norm
      (AlmostComplexStructure.norm_kahlerForm_sq_eq_two
        (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)) η
  have hA : r / (4 * √2) * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) ≤ r / (4 * √2) * m + K / (2 * √2) := by
    have : r / (4 * √2) * (1 - ‖φ‖ ^ 2 + ‖β‖ ^ 2) =
        r / (4 * √2) * (1 - ‖φ‖ ^ 2) + r * ‖β‖ ^ 2 / (4 * √2) := by ring
    rw [this]
    have h4 : r * ‖β‖ ^ 2 / (4 * √2) ≤ 2 * K / (4 * √2) := by gcongr
    have h5 : 2 * K / (4 * √2) = K / (2 * √2) := by field_simp; ring
    have h6 : r / (4 * √2) * (1 - ‖φ‖ ^ 2) ≤ r / (4 * √2) * m := by gcongr
    linarith
  have hB : -⟪J.kahlerForm, η⟫ / (2 * √2) ≤ ‖η‖ / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2)]
  linarith [neg_div (2 * √2) ⟪J.kahlerForm, η⟫]

/-- **The Hermitian part is bounded above by the defect density**: if
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, with `r ≥ 1`,
`‖β‖² ≤ (K / r) w₊ + K / r²`, where `w₊ = max (1 - ‖φ‖²) 0`, and Taubes's coarse anti-self-dual
bound `‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C` with `C ≥ 0`, where `F⁻ = (F - ⋆F) / 2`, then the
Hermitian part `B(v, v) = F(v, J v)` of `F` satisfies

`B(v, v) ≤ ((1 + C / √r) δ + (1 + C) K + √2 ‖η‖ / 2 + C) ‖v‖²`,  `δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|`.

The largest value of `B` on the unit sphere is `c + ‖F⁻‖ / √2` with `c = ⟪ω, F⟫ / 2`
(`TauCeti.AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le`), the formula for `c` bounds
`c` by `r w₊ / 8 + O(1)`, the coarse bound bounds `‖F⁻‖ / √2` by
`(1 + C / √r) r w₊ / 8 + C / √2`, and `r w₊ / 4 ≤ δ + K / 2`. This is the bound on the Hermitian
part in Taubes's monotonicity inequality for the defect energy, with the factor
`1 + κ = 1 + C r^(-1/2)`. -/
theorem hermitianForm_apply_self_le_of_add_hodgeStar_eq (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : 0 ≤ C)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C) (v : V) :
    J.hermitianForm F v v ≤
      ((1 + C / √r) * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) + (1 + C) * K + √2 * ‖η‖ / 2 + C) *
        ‖v‖ ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div (sq_nonneg _) hr0 (le_max_right _ _) hβK
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  have hc := inner_div_two_eq_of_add_hodgeStar_eq hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hω₂ hφ hβ hr0.le hF
  -- The largest value of `B` on vectors of length `‖v‖` is `(c + ‖F⁻‖ / √2) ‖v‖²`.
  have hB : J.hermitianForm F v v ≤
      (⟪J.kahlerForm, F⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) * ‖v‖ ^ 2 := by
    have h := (abs_le.1 (AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le
      h₀ h₂₃ hkl he F v)).2
    linarith
  have hFm' := div_sqrt_two_le_of_le_mul_add hr0 hFm
  have hrb : r * ‖β‖ ^ 2 ≤ 2 * K :=
    mul_le_two_mul_of_le_div_mul_add_div (sq_nonneg _) (sq_nonneg _) hr hβK
  have hωη : -⟪J.kahlerForm, η⟫ ≤ √2 * ‖η‖ :=
    (neg_le_abs _).trans (abs_inner_le_sqrt_two_mul_norm hω₂ η)
  -- `1 - ‖φ‖² ≤ w₊` and `r w₊ / 4 ≤ δ + r ‖β‖² / 4`.
  have hm1 : r / 8 * (1 - ‖φ‖ ^ 2) ≤ r / 8 * max (1 - ‖φ‖ ^ 2) 0 := by
    gcongr
    exact le_max_left _ _
  have hw : r / 4 * max (1 - ‖φ‖ ^ 2) 0 ≤
      r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2| + r * ‖β‖ ^ 2 / 4 :=
    div_mul_max_le_div_mul_abs_add hr0.le (sq_nonneg _)
  -- The excess `C √r w₊ / 8 = (C / √r) (r w₊ / 4) / 2` of the coarse bound is `O(C / √r) δ`.
  have hCr : 0 ≤ C / √r := by positivity
  have hCr1 : C / √r ≤ C := div_le_self hC (Real.one_le_sqrt.2 hr)
  have hCw : C * √r * max (1 - ‖φ‖ ^ 2) 0 / 8 ≤
      C / √r * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) / 2 + C * K / 4 := by
    have hsr : C * √r = C / √r * r := by rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
    rw [hsr]
    have h1 := mul_le_mul_of_nonneg_left hw hCr
    have h2 : C / √r * (r * ‖β‖ ^ 2 / 4) ≤ C * (2 * K / 4) :=
      mul_le_mul hCr1 (by linarith) (by positivity) hC
    linarith
  have hδ : 0 ≤ C / √r * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) := by positivity
  have hC2 : C / √2 ≤ C := div_le_self hC (Real.one_le_sqrt.2 one_le_two)
  have hη : 0 ≤ √2 * ‖η‖ := by positivity
  refine hB.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  nlinarith [mul_nonneg hC hK]

/-- **The full curvature bound**: if `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler
two-vector `ω` of `J`, with `r ≥ 1`, `‖φ‖² + ‖β‖² ≤ 1 + K / r` and
`‖β‖² ≤ (K / r) w₊ + K / r²`, where `w₊ = max (1 - ‖φ‖²) 0`, and the Hermitian part of `F`
satisfies `B ≥ -C g`, then
`‖F‖ ≤ (r / (2 √2)) w₊ + (2 K + 1) / (2 √2) + ‖η‖ + √2 C`.
This is the sum of the self-dual and anti-self-dual bounds, since `F = F⁺ + F⁻`. Thus, for
bounded `K`, `C` and `η`, `F` is bounded independently of `r` where `w₊ = O(1 / r)`, and is of
size `r` only where `w₊` is not small. -/
theorem norm_le_of_add_hodgeStar_eq (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖F‖ ≤ r / (2 * √2) * max (1 - ‖φ‖ ^ 2) 0 + (2 * K + 1) / (2 * √2) + ‖η‖ + √2 * C := by
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)
  have hplus := norm_smul_add_hodgeStar_le hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hω₂ hφ hβ hρ h₂ hr hβK hφβ hF
  have hminus := norm_smul_sub_hodgeStar_le h₀ h₂₃ hQ hkl he hφ hβ hr hβK hF hC
  calc ‖F‖ ≤ ‖(2⁻¹ : ℝ) • (F + o.hodgeStar hkl F)‖ + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ :=
        norm_le_norm_inv_two_smul_add_add_norm_inv_two_smul_sub (R := ℝ) F (o.hodgeStar hkl F)
    _ ≤ (r / (4 * √2) * max (1 - ‖φ‖ ^ 2) 0 + (K + 1) / (2 * √2) + ‖η‖ / 2) +
          (r / (4 * √2) * max (1 - ‖φ‖ ^ 2) 0 + K / (2 * √2) + ‖η‖ / 2 + √2 * C) :=
        add_le_add hplus hminus
    _ = _ := by
        field_simp
        ring

/-- **The full curvature bound by the defect density**: if
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, with `r ≥ 1`,
`‖φ‖² + ‖β‖² ≤ 1 + K / r` and `‖β‖² ≤ (K / r) w₊ + K / r²`, where `w₊ = max (1 - ‖φ‖²) 0`, and
Taubes's coarse anti-self-dual bound `‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C` holds with
`C ≥ 0`, where `F⁻ = (F - ⋆F) / 2`, then

`‖F‖ ≤ (2 + C) δ + (2 + C) (K + 1) + ‖η‖`,  `δ = (r / 4) |1 - ‖φ‖² - ‖β‖²|`.

So the whole curvature, not only its Hermitian part, is bounded by a fixed multiple of the defect
density up to a constant. This is the form in which the curvature enters when the almost complex
structure of a Darboux chart is replaced by its value at a point. -/
theorem norm_le_of_add_hodgeStar_eq_of_norm_smul_sub_hodgeStar_le
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : 0 ≤ C)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C) :
    ‖F‖ ≤ (2 + C) * (r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|) + (2 + C) * (K + 1) + ‖η‖ := by
  have hr0 : 0 < r := by linarith
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div (sq_nonneg _) hr0 (le_max_right _ _) hβK
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)
  have hplus := norm_smul_add_hodgeStar_le hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hω₂ hφ hβ hρ h₂ hr hβK hφβ hF
  have htri :=
    norm_le_norm_inv_two_smul_add_add_norm_inv_two_smul_sub (R := ℝ) F (o.hodgeStar hkl F)
  -- Both parts are at most a multiple of `r w₊ / 4`, and `r w₊ / 4 ≤ δ + K / 2`.
  have hw₀ := div_mul_max_le_div_mul_abs_add (s := ‖φ‖ ^ 2) hr0.le (sq_nonneg ‖β‖)
  set m := max (1 - ‖φ‖ ^ 2) 0
  set δ := r / 4 * |1 - ‖φ‖ ^ 2 - ‖β‖ ^ 2|
  have hm : 0 ≤ m := le_max_right _ _
  have hrb : r * ‖β‖ ^ 2 ≤ 2 * K :=
    mul_le_two_mul_of_le_div_mul_add_div (sq_nonneg _) (sq_nonneg _) hr hβK
  have hw : r / 4 * m ≤ δ + K / 2 := by linarith
  have hs2 : 1 ≤ √2 := Real.one_le_sqrt.2 one_le_two
  have hrm : r / (4 * √2) * m ≤ r / 4 * m :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hr0.le (by norm_num) (by linarith)) hm
  have hCr : C / √r ≤ C := div_le_self hC (Real.one_le_sqrt.2 hr)
  have hrmC : r / (4 * √2) * (1 + C / √r) * m ≤ (1 + C) * (r / 4 * m) := by
    calc r / (4 * √2) * (1 + C / √r) * m = (1 + C / √r) * (r / (4 * √2) * m) := by ring
      _ ≤ (1 + C) * (r / 4 * m) := by
        exact mul_le_mul (by linarith) hrm (mul_nonneg (div_nonneg hr0.le (by positivity)) hm)
          (by linarith)
  have hK1 : (K + 1) / (2 * √2) ≤ (K + 1) / 2 := by
    gcongr
    linarith
  have hδ : 0 ≤ δ := mul_nonneg (by linarith) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hw hC, norm_nonneg η, hδ]

/-- **The anti-`J`-invariant part of the curvature is the cross term.** If
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, then

`D_J² F = 2 r q'(φ, β) - D_J² η / 2`,

where `-D_J² / 4` is the projection onto the anti-`J`-invariant two-forms. Indeed the
anti-self-dual part of `F` is `J`-invariant, `q(√r (φ + β))` differs from `r q'(φ, β)` by a multiple
of `ω`, which is `J`-invariant, and `D_J² = -4` on the self-dual forms orthogonal to `ω`. -/
theorem lieMap_lieMap_eq_of_add_hodgeStar_eq
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap F) =
      (2 * r) • (quadraticTwoFormPolar o ρ hkl φ β : ⋀[ℝ]^2 V) -
        (2⁻¹ : ℝ) •
          exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap η) := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  set D := exteriorPower.lieMap 2 J.toLinearMap
  set X : ⋀[ℝ]^2 V := (quadraticTwoFormPolar o ρ hkl φ β : ⋀[ℝ]^2 V)
  -- `F + ⋆F = -c ω - r X - η` for a scalar `c`.
  have hsum : F + o.hodgeStar hkl F =
      -((r / 4 * (‖φ‖ ^ 2 - ‖β‖ ^ 2 - 1)) • J.kahlerForm) - r • X - η := by
    have h := coe_quadraticTwoForm_sqrt_smul_add_sub_smul o hQ hkl hω hρ h₂ hφ hβ hr
    rw [hF]
    linear_combination (norm := module) -h
  -- The anti-self-dual part of `F` is `J`-invariant.
  have hASD : D ((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)) = 0 :=
    AlmostComplexStructure.lieMap_of_hodgeStar_eq_neg h₀ h₂₃ hkl he
      (o.hodgeStar_smul_sub_hodgeStar even_two hkl F)
  -- `D_J² X = -4 X`, since `X` is self-dual and orthogonal to `ω`.
  have hX : D (D X) = -(4 : ℝ) • X := by
    have hXsd : o.hodgeStar hkl X = X :=
      (Module.End.mem_eigenspace_iff.1 (quadraticTwoFormPolar o ρ hkl φ β).property).trans
          (one_smul ℝ _)
    have hXω : ⟪J.kahlerForm, X⟫ = 0 := by
      rw [real_inner_comm]
      exact inner_quadraticTwoFormPolar_of_cliffordProjection o hQ hkl hω hρ hφ hβ
    rw [AlmostComplexStructure.lieMap_lieMap_of_hodgeStar_eq_self h₀ h₂₃ hkl he hXsd, hXω,
      mul_zero, zero_smul, zero_sub, neg_smul]
  have hDω : D J.kahlerForm = 0 := AlmostComplexStructure.lieMap_kahlerForm J
  have hsplit :
      F = (2⁻¹ : ℝ) • (F + o.hodgeStar hkl F) + (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F) := by
    module
  rw [hsplit, map_add, hASD, add_zero, map_smul, map_smul, hsum]
  simp only [map_sub, map_neg, map_smul, hDω, hX, smul_zero, neg_zero, zero_sub]
  module

/-- **The coarse lower bound on the Hermitian part of the curvature.** Let
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, with `r ≥ 1`, and
suppose Taubes's coarse bounds `‖φ‖² + ‖β‖² ≤ 1 + K / r`, `‖β‖² ≤ (K / r) w₊ + K / r²` and
`‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where `w₊ = max (1 - ‖φ‖²) 0` and
`F⁻ = (F - ⋆F) / 2`. Then the Hermitian form `B(v, v) = F(v, J v)` satisfies

`B(v, v) ≥ -(C √r w₊ / 8 + C / √2 + K / 4 + √2 ‖η‖ / 4) ‖v‖²`.

Indeed the smallest eigenvalue of `B` is `⟪ω, F⟫ / 2 - ‖F⁻‖ / √2`
(`TauCeti.AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le`), and
`⟪ω, F⟫ / 2 = r w₊ / 8 + O(1)` (`abs_inner_div_two_sub_le`), so the coarse anti-self-dual bound
only allows a negative part of size `O(√r)`. -/
theorem neg_mul_norm_sq_le_inner_ιMulti_of_add_hodgeStar_eq (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C) (v : V) :
    -((C * √r * max (1 - ‖φ‖ ^ 2) 0 / 8 + C / √2 + K / 4 + √2 * ‖η‖ / 4) * ‖v‖ ^ 2) ≤
      ⟪F, exteriorPower.ιMulti ℝ 2 ![v, J v]⟫ := by
  have hr0 : 0 < r := by linarith
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  set w := max (1 - ‖φ‖ ^ 2) 0
  set Fm := ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖
  set s := C * √r * w / 8 + C / √2 + K / 4 + √2 * ‖η‖ / 4 with hs_def
  have hc := abs_inner_div_two_sub_le hQ hkl hω hω₂ hφ hβ hr hβK hφβ hF
  -- `⟪ω, F⟫ / 2 - ‖F⁻‖ / √2 ≥ -s`.
  have hmin : -s ≤ ⟪J.kahlerForm, F⟫ / 2 - Fm / √2 := by
    have hFm' : Fm / √2 ≤ r / 8 * w + C * √r * w / 8 + C / √2 :=
      div_sqrt_two_le_of_le_mul_add hr0 hFm
    have := (abs_le.1 hc).1
    linarith
  rw [← AlmostComplexStructure.hermitianForm_apply_self]
  have h : -(Fm / √2 * ‖v‖ ^ 2) ≤ J.hermitianForm F v v - ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 :=
    (abs_le.1 (AlmostComplexStructure.abs_hermitianForm_apply_self_sub_le h₀ h₂₃ hkl he F v)).1
  nlinarith [mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖v‖)]

/-- **The coarse distance of the curvature to the positive cone.** Let
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for the Kähler two-vector `ω` of `J`, with `r ≥ 1`, and
suppose Taubes's coarse bounds `‖φ‖² + ‖β‖² ≤ 1 + K / r`, `‖β‖² ≤ (K / r) w₊ + K / r²` and
`‖F⁻‖ ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where `w₊ = max (1 - ‖φ‖²) 0`,
`F⁻ = (F - ⋆F) / 2` and `C ≥ 0`. Then the distance from `F` to the cone of positive
`(1,1)`-forms satisfies

`dist(F, positiveCone) ≤ r ‖φ‖ ‖β‖ / (2 √2) + C √r w₊ / (4 √2) + C + K / (2 √2) + ‖η‖`.

The first term bounds the anti-`J`-invariant part, which is `r q'(φ, β)` up to `η`
(`lieMap_lieMap_eq_of_add_hodgeStar_eq`); the second is the negative part `O(√r)` of the
Hermitian form `B(v, v) = F(v, J v)` allowed by the coarse anti-self-dual bound
(`neg_mul_norm_sq_le_inner_ιMulti_of_add_hodgeStar_eq`). Both are large only where `|α|` is
small. -/
theorem infDist_positiveCone_le_of_add_hodgeStar_eq
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (hr : 1 ≤ r) {K : ℝ}
    (hβK : ‖β‖ ^ 2 ≤ K / r * max (1 - ‖φ‖ ^ 2) 0 + K / r ^ 2)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + K / r)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    {C : ℝ} (hC : 0 ≤ C)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C) :
    infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      r * ‖φ‖ * ‖β‖ / (2 * √2) + C * √r * max (1 - ‖φ‖ ^ 2) 0 / (4 * √2) + C +
        K / (2 * √2) + ‖η‖ := by
  have hr0 : 0 < r := by linarith
  have hK : 0 ≤ K := nonneg_of_le_div_mul_add_div (sq_nonneg _) hr0 (le_max_right _ _) hβK
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  have hω' : ‖J.kahlerForm‖ = √2 := by rw [← hω₂, Real.sqrt_sq (norm_nonneg _)]
  have hs2 : √2 ≠ 0 := by positivity
  have hs2sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hs : 0 ≤ C * √r * max (1 - ‖φ‖ ^ 2) 0 / 8 + C / √2 + K / 4 + √2 * ‖η‖ / 4 := by
    have := le_max_right (1 - ‖φ‖ ^ 2) 0
    positivity
  refine (AlmostComplexStructure.infDist_positiveCone_le hJ hs
    (neg_mul_norm_sq_le_inner_ιMulti_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hφ hβ hr hβK hφβ hF
      hFm)).trans ?_
  -- The anti-`J`-invariant part.
  have hD : ‖exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap F)‖ ≤
      2 * r * (‖φ‖ * ‖β‖ / √2) + 2 * ‖η‖ := by
    rw [lieMap_lieMap_eq_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he hφ hβ hρ h₂ hr0.le hF]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by norm_num)]
    have h1 : ‖(quadraticTwoFormPolar o ρ hkl φ β : ⋀[ℝ]^2 V)‖ ≤ ‖φ‖ * ‖β‖ / √2 :=
      norm_quadraticTwoFormPolar_le o hQ hkl hρ φ β
    have h2 := AlmostComplexStructure.norm_lieMap_lieMap_le hJ η
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * r)
    linarith
  rw [hω']
  have heq : (2 * r * (‖φ‖ * ‖β‖ / √2) + 2 * ‖η‖) / 4 +
        (C * √r * max (1 - ‖φ‖ ^ 2) 0 / 8 + C / √2 + K / 4 + √2 * ‖η‖ / 4) * √2 =
      r * ‖φ‖ * ‖β‖ / (2 * √2) + C * √r * max (1 - ‖φ‖ ^ 2) 0 / (4 * √2) + C +
        K / (2 * √2) + ‖η‖ := by
    clear * - hs2 hs2sq
    grind
  rw [← heq]
  gcongr

end AntiSelfDual

end TauCeti.SeibergWitten
