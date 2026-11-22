/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
import TauCeti.Analysis.PDE.Caccioppoli.Divergence
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The interior Schauder estimate for divergence-form equations in scaled form

Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in an open set
`Ω ⊆ ℝ^{n+1}`, and let `B(x₀, 2r) ⊆ Ω`. Write `d = n + 1` for the dimension. Suppose that `a` is
uniformly elliptic with constants `λ`, `Λ` on `B(x₀, 2r)`, that `a` and `G` are `α`-Hölder there
with constants `K_a` and `K_G`, where `r^α K_a ≤ M`, and that `f ∈ L^q(B(x₀, 2r))` with `q ≥ 2`.
For `0 < β < 1` with `β ≤ α` and `β ≤ 1 - d/q`, this file proves the interior `C^{1,β}` estimate
on the concentric ball of half the radius in its scaled form,

`r^{1+β} [∇u]_{β; B(x₀, r)} + r ‖∇u‖_{∞; B(x₀, r)}`
`  ≤ C (r^{-d/2} ‖u‖_{L²(B(x₀, 2r))} + r^{2-d/q} ‖f‖_{L^q(B(x₀, 2r))} + r^{1+α} K_G)`,

for the precise representative of `∇u`
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le`), with `C`
depending only on `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`. Every term scales like `u`, so the
estimate is invariant under `u ↦ u(x₀ + r ·)`, and only `r^α K_a` enters among the coefficient
parameters. Since `r^{-d/2} ‖u‖_{L²(B(x₀, 2r))}` is at most a dimensional multiple of the
essential supremum of `|u|` on `B(x₀, 2r)`, the same holds with that supremum in place of the
`L²` term
(`exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le_of_ae_abs_le`).
The field `G` enters through its Hölder seminorm only, not its size: `G` and `G - G x₀` define the
same equation.

## The argument

The estimate on the thickening
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`),
applied to the restriction of `u` to `B(x₀, 3r/2)` with `S = B(x₀, r)` and thickening radius
`r/2`, bounds `[∇u]_{β; B(x₀, r)}` by the data and `r^{-d/2-β} ‖∇u‖_{L²(B(x₀, 3r/2))}`. The
Caccioppoli inequality for the datum `f + div (G x₀ - G)`
(`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_add_divergence`) bounds this gradient
norm by `u` on `B(x₀, 2r)`: with `|G - G x₀| ≤ K_G (2r)^α`, Young's inequality on the term `f u`
and Hölder's inequality for `f`,

`∫_{B(x₀, 3r/2)} ‖∇u‖² ≤ K r^{d-2} (r^{-d/2} ‖u‖_{L²} + r^{2-d/q} ‖f‖_{L^q} + r^{1+α} K_G)²`.

For the supremum, some point `y ∈ B(x₀, r)` has `‖∇u(y)‖²` at most the mean of `‖∇u‖²` over
`B(x₀, r)`, which this bound controls, and the Hölder estimate carries the bound from `y` to every
point of `B(x₀, r)`.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le`: the scaled interior
  `C^{1,β}` estimate with the `L²` norm of `u`.
* `exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le_of_ae_abs_le`: the
  same with the essential supremum of `|u|`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.32 (the interior `C^{1,α}` estimate with `sup |u|` on the right-hand side).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The `L²` pairings of the weak equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` on `B`, with a constant `c`
subtracted from `G`, written as integrals: the equation is `L u = f + div (c - G)`. -/
private theorem inner_toLp_add_inner_toLp_eq_sub {B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (v : W1p volume B 2) :
    ⟪hGc.toLp, W1p.gradient v⟫_ℝ + ⟪hf.toLp, W1p.value v⟫_ℝ =
      (∫ x in B, f x * W1p.value v x) - ∫ x in B, ⟪c - G x, W1p.gradient v x⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def, sub_eq_add_neg, ← integral_neg, add_comm]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]
  · refine integral_congr_ae ?_
    filter_upwards [hGc.coeFn_toLp] with x hx
    rw [hx, ← inner_neg_left, neg_sub]

/-- The `L²` pairings of the weak equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` on `B`, with a constant
subtracted from `G`, tested against a test function `φ` on `B`, are the original pairings. -/
private theorem inner_toLp_add_inner_toLp_ofTestFunctionₗ
    {B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (φ : 𝓓(B, ℝ)) :
    ⟪hGc.toLp, W1p.gradient (W1p.ofTestFunctionₗ volume B 2 φ)⟫_ℝ +
        ⟪hf.toLp, W1p.value (W1p.ofTestFunctionₗ volume B 2 φ)⟫_ℝ =
      (∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in B, f x * φ x := by
  rw [inner_toLp_gradient_ofTestFunctionₗ hGc φ, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ]
    with x hx hφx
  rw [hx, hφx]
  simp [RCLike.inner_apply, mul_comm]

/-- On an open `B ⊆ Ω` inside a ball `B(x₀, ρ)` on which `a` and `G` are `α`-Hölder, with `a`
uniformly elliptic on `B`, the weak equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` on `Ω`, tested against
test functions, holds for the restriction of `u` against all of `H¹₀(B)`, in the form
`L u = f + div (G x₀ - G)`. -/
private theorem energyFormH1_restrictL_eq_sub_of_holderOnWith
    {Omega B : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hB : B ≤ Omega)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hBρ : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball x₀ ρ)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    {α : ℝ≥0} (hα : 0 < α) {Ka KG : ℝ≥0}
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ ρ))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ ρ)) {u : W1p volume Omega 2}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    (v : W1p0 volume B 2) :
    energyFormH1 a 0 0 (W1p.restrictL hB u) (v : W1p volume B 2) =
      (∫ x in B, f x * W1p.value (v : W1p volume B 2) x) -
        ∫ x in B, ⟪G x₀ - G x, W1p.gradient (v : W1p volume B 2) x⟫_ℝ := by
  have hcoeff := memLp_energyIntegrand_of_holderOnWith (mu := volume) hBρ h hα haK
  have hGc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) B.isOpen.measurableSet hBρ hα hGK
  exact (forall_energyFormH1_restrictL_eq_inner_add_inner hB hcoeff hu hGc hf v).trans
    (inner_toLp_add_inner_toLp_eq_sub hGc hf _)

/-- **Restricting a weak solution.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on
`Ω`, tested against test functions. On an open `B ⊆ Ω` inside a ball `B(x₀, ρ)` on which `a` and `G`
are `α`-Hölder, with `a` uniformly elliptic on `B` and `f ∈ L²(B)`, the restriction of `u` to `B`
solves the same equation on `B`, tested against test functions on `B`. -/
theorem energyFormH1_restrictL_ofTestFunctionₗ_of_holderOnWith
    {Omega B : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hB : B ≤ Omega)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hBρ : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball x₀ ρ)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    {α : ℝ≥0} (hα : 0 < α) {Ka KG : ℝ≥0}
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ ρ))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ ρ)) {u : W1p volume Omega 2}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    (φ : 𝓓(B, ℝ)) :
    energyFormH1 a 0 0 (W1p.restrictL hB u) (W1p.ofTestFunctionₗ volume B 2 φ) =
      (∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in B, f x * φ x := by
  have hcoeff := memLp_energyIntegrand_of_holderOnWith (mu := volume) hBρ h hα haK
  have hGc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) B.isOpen.measurableSet hBρ hα hGK
  exact (forall_energyFormH1_restrictL_eq_inner_add_inner hB hcoeff hu hGc hf
    ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans
    (inner_toLp_add_inner_toLp_ofTestFunctionₗ hGc hf φ)

/-- The scaling of the three terms of the Caccioppoli bound: with `d = n + 1`, `a₁ = r^{-d/2} √U`,
`a₂ = r^{2-d/t} F` and `a₃ = r^{1+α} K`, the term `U / r²` is `r^{d-2} a₁²`, the term
`(2r)^d (K (2r)^α)²` is `2^{d+2α} r^{d-2} a₃²`, and `r² F² (2r)^{d(1-2/t)}` is
`2^{d(1-2/t)} r^{d-2} a₂²`. The sum of multiples of these terms is therefore at most
`r^{d-2} (a₁ + a₂ + a₃)²` times the sum of the multiples. -/
private theorem add_add_le_mul_rpow_mul_sq {r U F K α t c₁ c₂ c₃ : ℝ} (hr : 0 < r) (hU : 0 ≤ U)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) :
    c₁ * ((r ^ 2)⁻¹ * U) + c₂ * ((2 * r) ^ (n + 1) * (K * (2 * r) ^ α) ^ 2) +
        c₃ * (r ^ 2 * (F ^ 2 * (2 * r) ^ (((n : ℝ) + 1) * (1 - 2 / t)))) ≤
      (c₁ + c₂ * 2 ^ ((n : ℝ) + 1 + 2 * α) + c₃ * 2 ^ (((n : ℝ) + 1) * (1 - 2 / t))) *
        r ^ ((n : ℝ) - 1) * (r ^ (-(((n : ℝ) + 1) / 2)) * √U +
          r ^ (2 - ((n : ℝ) + 1) / t) * F + r ^ (1 + α) * K) ^ 2 := by
  -- The three identities below are exponent arithmetic for real powers of `2` and of `r`.
  have hpow : ∀ {b : ℝ}, 0 < b → ∀ x y z : ℝ, x + y = z → b ^ x * b ^ y = b ^ z :=
    fun hb x y z h => h ▸ (Real.rpow_add hb x y).symm
  have hsq : ∀ {b : ℝ}, 0 < b → ∀ x : ℝ, (b ^ x) ^ 2 = b ^ (2 * x) := fun hb x => by
    rw [← Real.rpow_mul_natCast hb.le, mul_comm, Nat.cast_ofNat]
  have e₁ : (r ^ 2)⁻¹ * U = r ^ ((n : ℝ) - 1) * (r ^ (-(((n : ℝ) + 1) / 2)) * √U) ^ 2 := by
    have h : (r ^ 2)⁻¹ = r ^ ((n : ℝ) - 1) * r ^ (2 * -(((n : ℝ) + 1) / 2)) := by
      rw [hpow hr _ _ (-2) (by ring), Real.rpow_neg hr.le, Real.rpow_two]
    rw [h, mul_pow, Real.sq_sqrt hU, hsq hr]
    ring
  have e₃ : (2 * r) ^ (n + 1) * (K * (2 * r) ^ α) ^ 2 =
      2 ^ ((n : ℝ) + 1 + 2 * α) * r ^ ((n : ℝ) - 1) * (r ^ (1 + α) * K) ^ 2 := by
    have h2 : (2 : ℝ) ^ ((n : ℝ) + 1) * 2 ^ (2 * α) = 2 ^ ((n : ℝ) + 1 + 2 * α) :=
      hpow two_pos _ _ _ rfl
    have hr2 : r ^ ((n : ℝ) + 1) * r ^ (2 * α) = r ^ ((n : ℝ) - 1) * r ^ (2 * (1 + α)) := by
      rw [hpow hr _ _ _ rfl, hpow hr _ _ ((n : ℝ) + 1 + 2 * α) (by ring)]
    rw [← Real.rpow_natCast (2 * r) (n + 1), Nat.cast_add_one, Real.mul_rpow zero_le_two hr.le,
      Real.mul_rpow zero_le_two hr.le, mul_pow, mul_pow, mul_pow, hsq two_pos, hsq hr, hsq hr]
    linear_combination K ^ 2 * 2 ^ ((n : ℝ) + 1) * 2 ^ (2 * α) * hr2 +
      K ^ 2 * r ^ ((n : ℝ) - 1) * r ^ (2 * (1 + α)) * h2
  have e₂ : r ^ 2 * (F ^ 2 * (2 * r) ^ (((n : ℝ) + 1) * (1 - 2 / t))) =
      2 ^ (((n : ℝ) + 1) * (1 - 2 / t)) * r ^ ((n : ℝ) - 1) *
        (r ^ (2 - ((n : ℝ) + 1) / t) * F) ^ 2 := by
    have hr2 : r ^ 2 * r ^ (((n : ℝ) + 1) * (1 - 2 / t)) =
        r ^ ((n : ℝ) - 1) * r ^ (2 * (2 - ((n : ℝ) + 1) / t)) := by
      rw [← Real.rpow_two, hpow hr _ _ _ rfl,
        hpow hr _ _ (2 + ((n : ℝ) + 1) * (1 - 2 / t)) (by ring)]
    rw [Real.mul_rpow zero_le_two hr.le, mul_pow, hsq hr]
    linear_combination 2 ^ (((n : ℝ) + 1) * (1 - 2 / t)) * F ^ 2 * hr2
  rw [e₁, e₂, e₃]
  set a₁ := r ^ (-(((n : ℝ) + 1) / 2)) * √U
  set a₂ := r ^ (2 - ((n : ℝ) + 1) / t) * F
  set a₃ := r ^ (1 + α) * K
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₂ : 0 ≤ a₂ := by positivity
  have ha₃ : 0 ≤ a₃ := by positivity
  have hQ₁ : a₁ ^ 2 ≤ (a₁ + a₂ + a₃) ^ 2 := pow_le_pow_left₀ ha₁ (by linarith) 2
  have hQ₂ : a₂ ^ 2 ≤ (a₁ + a₂ + a₃) ^ 2 := pow_le_pow_left₀ ha₂ (by linarith) 2
  have hQ₃ : a₃ ^ 2 ≤ (a₁ + a₂ + a₃) ^ 2 := pow_le_pow_left₀ ha₃ (by linarith) 2
  calc c₁ * (r ^ ((n : ℝ) - 1) * a₁ ^ 2) +
          c₂ * (2 ^ ((n : ℝ) + 1 + 2 * α) * r ^ ((n : ℝ) - 1) * a₃ ^ 2) +
          c₃ * (2 ^ (((n : ℝ) + 1) * (1 - 2 / t)) * r ^ ((n : ℝ) - 1) * a₂ ^ 2)
      = r ^ ((n : ℝ) - 1) * (c₁ * a₁ ^ 2 + c₂ * 2 ^ ((n : ℝ) + 1 + 2 * α) * a₃ ^ 2 +
          c₃ * 2 ^ (((n : ℝ) + 1) * (1 - 2 / t)) * a₂ ^ 2) := by ring
    _ ≤ r ^ ((n : ℝ) - 1) * (c₁ * (a₁ + a₂ + a₃) ^ 2 +
          c₂ * 2 ^ ((n : ℝ) + 1 + 2 * α) * (a₁ + a₂ + a₃) ^ 2 +
          c₃ * 2 ^ (((n : ℝ) + 1) * (1 - 2 / t)) * (a₁ + a₂ + a₃) ^ 2) := by gcongr
    _ = _ := by ring

/-- Young's inequality for the product term of the Caccioppoli inequality, integrated over a set
`s`: `(4/λ) ∫_s |f g| ≤ (1/r²) ∫_s g² + (4 r²/λ²) ∫_s f²` for square-integrable `f` and `g`, by
`(4/λ) |f g| = 2 (|g|/r) (2r |f|/λ)`. -/
private theorem four_div_mul_setIntegral_abs_mul_le {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hf : MemLp f 2 (volume.restrict s)) (hg : MemLp g 2 (volume.restrict s)) :
    4 / lam * ∫ x in s, |f x * g x| ≤
      (r ^ 2)⁻¹ * (∫ x in s, g x ^ 2) + 4 * r ^ 2 / lam ^ 2 * ∫ x in s, f x ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.integrable_sq.const_mul _) (hf.integrable_sq.const_mul _)]
  refine integral_mono ((hf.integrable_mul hg).abs.const_mul _)
    ((hg.integrable_sq.const_mul _).add (hf.integrable_sq.const_mul _)) fun x => ?_
  have hY := two_mul_le_add_sq (|g x| / r) (2 * r * |f x| / lam)
  rw [abs_mul]
  calc 4 / lam * (|f x| * |g x|) = 2 * (|g x| / r) * (2 * r * |f x| / lam) := by
        field_simp
        ring
    _ ≤ (|g x| / r) ^ 2 + (2 * r * |f x| / lam) ^ 2 := hY
    _ = (r ^ 2)⁻¹ * g x ^ 2 + 4 * r ^ 2 / lam ^ 2 * f x ^ 2 := by
        rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs, sq_abs]
        field_simp
        ring

/-- **The Caccioppoli step.** There is a constant `C₁`, depending only on the dimension, such
that the following holds. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on
`Ω ⊆ ℝ^{n+1}`, tested against test functions, let `B(x₀, 2r) ⊆ Ω`, let `a` be uniformly elliptic
on `B(x₀, 2r)`, let `a` and `G` be `α`-Hölder there, and let `f ∈ L²(B(x₀, 2r))`. Then, with
`A = 2 ((2Λ/λ)² + 1)`,

`∫_{B(x₀, 3r/2)} ‖∇u‖² ≤ 4 A C₁² r^{-2} ∫_{B(x₀, 2r)} u² + (12/λ²) ∫_{B(x₀, 2r)} ‖G x₀ - G‖²`
`  + (4/λ) ∫_{B(x₀, 2r)} |f u|`. -/
private theorem exists_setIntegral_ball_norm_gradient_sq_le_of_holderOnWith {α : ℝ≥0}
    (hα : 0 < α) :
    ∃ C₁ : ℝ, ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r lam Lam : ℝ},
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ (2 * r)) →
      HolderOnWith KG α G (ball x₀ (2 * r)) →
      MemLp f 2 (volume.restrict (ball x₀ (2 * r))) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < r → ball x₀ (2 * r) ⊆ Omega →
      ∫ x in ball x₀ (r / 2 + r), ‖W1p.gradient u x‖ ^ 2 ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (4 * C₁ ^ 2 * (r ^ 2)⁻¹) *
            (∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
          12 / lam ^ 2 * (∫ x in ball x₀ (2 * r), ‖G x₀ - G x‖ ^ 2) +
          4 / lam * ∫ x in ball x₀ (2 * r), |f x * W1p.value u x| := by
  obtain ⟨C₁, -, hcacc⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_divergence
    (ι := Fin (n + 1))
  refine ⟨C₁, fun {Omega u a G f Ka KG x₀ r lam Lam} h haK hGK hf2 hu hr hball => ?_⟩
  let B₂ : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ (2 * r), isOpen_ball⟩
  have hB₂ : B₂ ≤ Omega := hball
  have ha := aestronglyMeasurable_of_holderOnWith_matrixBilinearForm (mu := volume)
    measurableSet_ball subset_rfl hα haK
  have hGc := memLp_sub_of_holderOnWith (μ := volume) (p := 2) measurableSet_ball subset_rfl hα hGK
  have hF : MemLp (fun x => G x₀ - G x) 2 (volume.restrict (ball x₀ (2 * r))) :=
    hGc.neg.ae_eq (ae_of_all _ fun x => by simp)
  -- The restriction of `u` to `B(x₀, 2r)` solves `L u = f + div (G x₀ - G)` against `H¹₀`.
  have hc := hcacc (mu := volume) (Omega := B₂) (u := W1p.restrictL hB₂ u) (x₀ := x₀)
    (r := r / 2 + r) (R := 2 * r) h ha hf2 hF
    (energyFormH1_restrictL_eq_sub_of_holderOnWith hB₂ subset_rfl h hα haK hGK hf2 hu)
    (by linarith) subset_rfl
  -- On `B(x₀, 2r)` the restriction has the value and gradient of `u`.
  have hval := W1p.value_restrictL_ae hB₂ u
  have e₁ : ∫ x in ball x₀ (r / 2 + r), ‖W1p.gradient (W1p.restrictL hB₂ u) x‖ ^ 2 =
      ∫ x in ball x₀ (r / 2 + r), ‖W1p.gradient u x‖ ^ 2 :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith))
      ((W1p.gradient_restrictL_ae hB₂ u).mono fun x hx => by simp only [hx]))
  have e₂ : ∫ x in ball x₀ (2 * r), W1p.value (W1p.restrictL hB₂ u) x ^ 2 =
      ∫ x in ball x₀ (2 * r), W1p.value u x ^ 2 :=
    integral_congr_ae (hval.mono fun x hx => by simp only [hx])
  have e₃ : ∫ x in ball x₀ (2 * r), |f x * W1p.value (W1p.restrictL hB₂ u) x| =
      ∫ x in ball x₀ (2 * r), |f x * W1p.value u x| :=
    integral_congr_ae (hval.mono fun x hx => by simp only [hx])
  have hC : (C₁ / (2 * r - (r / 2 + r))) ^ 2 = 4 * C₁ ^ 2 * (r ^ 2)⁻¹ := by
    field_simp
    ring
  rw [e₁, e₂, e₃, hC] at hc
  beta_reduce at hc
  exact hc

/-- **The gradient bound from the Caccioppoli inequality.** For `α > 0` and `q ≥ 2` there is a
constant `K`, depending only on `n`, `α`, `q`, `λ` and `Λ`, such that the following holds. Let
`u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `Ω ⊆ ℝ^{n+1}`, tested against test
functions, let `B(x₀, 2r) ⊆ Ω`, let `a` be uniformly elliptic on `B(x₀, 2r)`, let `a` and `G` be
`α`-Hölder there, `G` with constant `K_G`, and let `f ∈ L^q(B(x₀, 2r))`. Then, with `d = n + 1`,
`∫_{B(x₀, 3r/2)} ‖∇u‖² ≤ K r^{d-2} Q²`, where
`Q = r^{-d/2} ‖u‖_{L²(B(x₀, 2r))} + r^{2-d/q} ‖f‖_{L^q(B(x₀, 2r))} + r^{1+α} K_G`. -/
private theorem exists_setIntegral_ball_norm_gradient_sq_le_mul_rpow_mul_sq {α : ℝ≥0}
    (hα : 0 < α) {q : ℝ≥0∞} (hq : 2 ≤ q) (lam Lam : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ},
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ (2 * r)) →
      HolderOnWith KG α G (ball x₀ (2 * r)) →
      MemLp f q (volume.restrict (ball x₀ (2 * r))) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < r → ball x₀ (2 * r) ⊆ Omega →
      ∫ x in ball x₀ (r / 2 + r), ‖W1p.gradient u x‖ ^ 2 ≤
        K * r ^ ((n : ℝ) - 1) * (r ^ (-(((n : ℝ) + 1) / 2)) *
            √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
          r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG) ^ 2 := by
  obtain ⟨C₁, hcacc⟩ := exists_setIntegral_ball_norm_gradient_sq_le_of_holderOnWith (n := n) hα
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hω : 0 ≤ ω := hωdef ▸ measureReal_nonneg
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = 4 * (2 * ((2 * Lam / lam) ^ 2 + 1)) * C₁ ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = 12 / lam ^ 2 * ω := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c, c = 4 / lam ^ 2 * ω ^ (1 - 2 / q.toReal) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := hc₁ ▸ by positivity
  have hc₂0 : 0 ≤ c₂ := hc₂ ▸ by positivity
  have hc₃0 : 0 ≤ c₃ := hc₃ ▸ by positivity
  refine ⟨c₁ + c₂ * 2 ^ ((n : ℝ) + 1 + 2 * α) + c₃ * 2 ^ (((n : ℝ) + 1) * (1 - 2 / q.toReal)),
    by positivity, ?_⟩
  intro Omega u a G f Ka KG x₀ r h haK hGK hf hu hr hball
  have hlam := h.pos
  have : IsFiniteMeasure (volume.restrict (ball x₀ (2 * r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hf2 : MemLp f 2 (volume.restrict (ball x₀ (2 * r))) := hf.mono_exponent hq
  have hc := hcacc h haK hGK hf2 hu hr hball
  have hb₁ := setIntegral_ball_norm_sub_sq_le_of_holderOnWith (μ := volume) hα hGK
  rw [Measure.addHaar_real_ball_of_pos volume x₀ (by positivity : 0 < 2 * r),
    finrank_euclideanSpace_fin, ← hωdef] at hb₁
  -- Young's inequality for `f u`, and Hölder's inequality for `f`.
  have hb₂ := four_div_mul_setIntegral_abs_mul_le hlam hr hf2
    ((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl))
  have hb₃ := hf.setIntegral_ball_norm_sq_le_eLpNorm_sq_mul_rpow hq (by positivity : 0 < 2 * r)
    subset_rfl
  simp only [Real.norm_eq_abs, sq_abs, finrank_euclideanSpace_fin, ← hωdef] at hb₃
  push_cast at hb₃
  have key := add_add_le_mul_rpow_mul_sq (n := n) (α := α) (t := q.toReal)
    (U := ∫ x in ball x₀ (2 * r), W1p.value u x ^ 2)
    (F := (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal) hr
    (setIntegral_nonneg measurableSet_ball fun x _ => sq_nonneg (W1p.value u x))
    ENNReal.toReal_nonneg KG.coe_nonneg hc₁0 hc₂0 hc₃0
  refine hc.trans (le_trans ?_ key)
  refine le_trans (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hb₁ (by positivity)))
    (hb₂.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb₃ (by positivity)))))
    (le_of_eq ?_)
  rw [hc₁, hc₂, hc₃]
  ring

/-- A power `(r/2)^e` with `e ≥ 0` is at most `r^e = r^{-(1+β)} r^s`, where `s = e + 1 + β`. -/
private theorem half_rpow_mul_le {r e s β c : ℝ} (hr : 0 < r) (he : 0 ≤ e) (hc : 0 ≤ c)
    (hs : s = e + 1 + β) : (r / 2) ^ e * c ≤ r ^ (-(1 + β)) * (r ^ s * c) := by
  rw [← mul_assoc, ← Real.rpow_add hr, hs, show -(1 + β) + (e + 1 + β) = e by ring]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) (by linarith) he) hc

/-- If `X² ≤ K r^{n-1} Q²` then `(r/2)^{-(d/2+β)} X ≤ 2^{d/2+β} √K r^{-(1+β)} Q`, where
`d = n + 1`. -/
private theorem half_rpow_neg_mul_le {r X K Q β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hX : 0 ≤ X) (hXsq : X ^ 2 ≤ K * r ^ ((n : ℝ) - 1) * Q ^ 2) :
    (r / 2) ^ (-(((n : ℝ) + 1) / 2 + β)) * X ≤
      2 ^ (((n : ℝ) + 1) / 2 + β) * √K * r ^ (-(1 + β)) * Q := by
  have hXle : X ≤ √K * r ^ (((n : ℝ) - 1) / 2) * Q := by
    refine (pow_le_pow_iff_left₀ hX (by positivity) two_ne_zero).1 (hXsq.trans_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hK, ← Real.rpow_mul_natCast hr.le]
    congr 3
    push_cast
    ring
  rw [Real.div_rpow hr.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul]
  calc r ^ (-(((n : ℝ) + 1) / 2 + β)) * 2 ^ (((n : ℝ) + 1) / 2 + β) * X
      ≤ r ^ (-(((n : ℝ) + 1) / 2 + β)) * 2 ^ (((n : ℝ) + 1) / 2 + β) *
          (√K * r ^ (((n : ℝ) - 1) / 2) * Q) := by gcongr
    _ = 2 ^ (((n : ℝ) + 1) / 2 + β) * √K *
          (r ^ (-(((n : ℝ) + 1) / 2 + β)) * r ^ (((n : ℝ) - 1) / 2)) * Q := by ring
    _ = _ := by
        rw [← Real.rpow_add hr]
        congr 3
        ring

/-- The constant of the Hölder half of the scaled estimate: the three terms of the estimate on the
thickening, with `R = r/2`, are each at most `r^{-(1+β)}` times a multiple of
`Q = A + r^{2-d/q} F + r^{1+α} K_G`, where `d = n + 1`. -/
private theorem mul_add_add_le_mul_mul {C₀ K r A F F' X KG α β t : ℝ} (hr : 0 < r) (hC₀ : 0 ≤ C₀)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hF : 0 ≤ F) (hKG : 0 ≤ KG) (hβα : β ≤ α)
    (hβt : β ≤ 1 - ((n : ℝ) + 1) / t) (hX : 0 ≤ X) (hFle : F' ≤ F)
    (hXsq : X ^ 2 ≤ K * r ^ ((n : ℝ) - 1) *
      (A + r ^ (2 - ((n : ℝ) + 1) / t) * F + r ^ (1 + α) * KG) ^ 2) :
    C₀ * (KG * (r / 2) ^ (α - β) + (r / 2) ^ (1 - ((n : ℝ) + 1) / t - β) * F' +
        (r / 2) ^ (-(((n : ℝ) + 1) / 2 + β)) * X) ≤
      C₀ * (2 + 2 ^ (((n : ℝ) + 1) / 2 + β) * √K) * r ^ (-(1 + β)) *
        (A + r ^ (2 - ((n : ℝ) + 1) / t) * F + r ^ (1 + α) * KG) := by
  set Q := A + r ^ (2 - ((n : ℝ) + 1) / t) * F + r ^ (1 + α) * KG
  have hF₂ : 0 ≤ r ^ (2 - ((n : ℝ) + 1) / t) * F := by positivity
  have hG₃ : 0 ≤ r ^ (1 + α) * KG := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hrβ : 0 ≤ r ^ (-(1 + β)) := by positivity
  have h₁ := half_rpow_mul_le (s := 1 + α) (β := β) hr (sub_nonneg.2 hβα) hKG (by ring)
  have h₂ := half_rpow_mul_le (e := 1 - ((n : ℝ) + 1) / t - β) (s := 2 - ((n : ℝ) + 1) / t)
    (β := β) hr (by linarith) hF (by ring)
  have h₃ := half_rpow_neg_mul_le (β := β) hr hK hQ0 hX hXsq
  have hT₁ : KG * (r / 2) ^ (α - β) ≤ r ^ (-(1 + β)) * Q :=
    (mul_comm KG _).trans_le (h₁.trans (mul_le_mul_of_nonneg_left (by linarith) hrβ))
  have hT₂ : (r / 2) ^ (1 - ((n : ℝ) + 1) / t - β) * F' ≤ r ^ (-(1 + β)) * Q :=
    (mul_le_mul_of_nonneg_left hFle (by positivity)).trans
      (h₂.trans (mul_le_mul_of_nonneg_left (by linarith) hrβ))
  calc C₀ * (KG * (r / 2) ^ (α - β) + (r / 2) ^ (1 - ((n : ℝ) + 1) / t - β) * F' +
        (r / 2) ^ (-(((n : ℝ) + 1) / 2 + β)) * X)
      ≤ C₀ * (r ^ (-(1 + β)) * Q + r ^ (-(1 + β)) * Q +
          2 ^ (((n : ℝ) + 1) / 2 + β) * √K * r ^ (-(1 + β)) * Q) := by
        gcongr
    _ = _ := by ring

/-- A Hölder bound on a set `s ⊆ U` for the precise representative of the gradient of the
restriction of `u ∈ H¹(Ω)` to an open `U ⊆ Ω` is one for the precise representative of `∇u`: the
two gradients agree almost everywhere on `U`, a neighbourhood of every point of `s`. -/
private theorem holderOnWith_preciseRepresentative_gradient_of_restrictL
    {Omega U : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hU : U ≤ Omega) {u : W1p volume Omega 2}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hs : s ⊆ U) {C β : ℝ≥0}
    (hH : HolderOnWith C β (preciseRepresentative volume (W1p.gradient (W1p.restrictL hU u) :
      EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) s) :
    HolderOnWith C β (preciseRepresentative volume (W1p.gradient u :
      EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) s := by
  have heq : EqOn (preciseRepresentative volume (W1p.gradient (W1p.restrictL hU u) :
        EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
      (preciseRepresentative volume (W1p.gradient u :
        EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) s :=
    fun x hx => preciseRepresentative_congr_ae_nhds (U.isOpen.mem_nhds (hs hx))
      (W1p.gradient_restrictL_ae hU u)
  intro x hx y hy
  rw [← heq hx, ← heq hy]
  exact hH x hx y hy

/-- **The Hölder half of the scaled estimate.** The constant of
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le` for the
Hölder seminorm of `∇u` on `B(x₀, r)`. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_ball
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ},
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ (2 * r)) →
      HolderOnWith KG α G (ball x₀ (2 * r)) → (Ka : ℝ) * r ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball x₀ (2 * r))) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < r → ball x₀ (2 * r) ⊆ Omega →
      HolderOnWith (C * r ^ (-(1 + (β : ℝ))) * (r ^ (-(((n : ℝ) + 1) / 2)) *
            √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
          r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG)).toNNReal β
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball x₀ r) := by
  obtain ⟨C₀, hC₀, hS⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
      (n := n) hβ hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M)
  have hα : 0 < α := hβ.trans_le hβα
  obtain ⟨K, hK, hgrad⟩ := exists_setIntegral_ball_norm_gradient_sq_le_mul_rpow_mul_sq (n := n) hα
    hq lam Lam
  refine ⟨C₀ * (2 + 2 ^ (((n : ℝ) + 1) / 2 + β) * √K), by positivity, ?_⟩
  intro Omega u a G f Ka KG x₀ r h haK hGK hM hf hu hr hball
  have hΦ := hgrad h haK hGK hf hu hr hball
  have hsub : ball x₀ (r / 2 + r) ⊆ ball x₀ (2 * r) := ball_subset_ball (by linarith)
  let B' : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ (r / 2 + r), isOpen_ball⟩
  have hB' : B' ≤ Omega := hsub.trans hball
  have hth : thickening (r / 2) (ball x₀ r) = ball x₀ (r / 2 + r) :=
    thickening_ball (half_pos hr) hr x₀
  have : IsFiniteMeasure (volume.restrict (ball x₀ (r / 2 + r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfB' : MemLp f q (volume.restrict (ball x₀ (r / 2 + r))) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  -- The restriction of `u` to `B(x₀, 3r/2)` solves the same equation there.
  have hu' := energyFormH1_restrictL_ofTestFunctionₗ_of_holderOnWith (B := B') hB' hsub
    (h.mono_set hsub) hα haK hGK (hfB'.mono_exponent hq) hu
  have hM' : (Ka : ℝ) * (r / 2) ^ (α : ℝ) ≤ M := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (half_le_self hr.le) α.property) Ka.property).trans hM
  have hH := hS (Omega := B') (u := W1p.restrictL hB' u) (S := ball x₀ r) (R := r / 2)
    (h.mono_set (ball_subset_ball (by linarith))) (by rw [hth]; exact haK.mono hsub)
    (by rw [hth]; exact hGK.mono hsub) hM' (by rw [hth]; exact hfB') hu' (half_pos hr) hth.le
  rw [hth] at hH
  have hH' := holderOnWith_preciseRepresentative_gradient_of_restrictL hB'
    (ball_subset_ball (by linarith)) hH
  refine hH'.mono_const (Real.toNNReal_le_toNNReal ?_)
  -- The `L²` norm of the gradient of the restriction is controlled by the Caccioppoli bound.
  have hgradB' : ‖W1p.gradient (W1p.restrictL hB' u)‖ ^ 2 ≤
      K * r ^ ((n : ℝ) - 1) * (r ^ (-(((n : ℝ) + 1) / 2)) *
          √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
        r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
          (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
        r ^ (1 + (α : ℝ)) * KG) ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine le_of_eq_of_le (integral_congr_ae ?_) hΦ
    exact (W1p.gradient_restrictL_ae hB' u).mono fun x hx => by simp only [hx]
  have hFle : (eLpNorm f q (volume.restrict (ball x₀ (r / 2 + r)))).toReal ≤
      (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  exact mul_add_add_le_mul_mul hr hC₀ hK (by positivity) ENNReal.toReal_nonneg KG.coe_nonneg
    (by exact_mod_cast hβα) hβq (norm_nonneg _) hFle hgradB'

/-- Some point `y` of `B(x₀, r) ⊆ Ω` has `r ‖g y‖ ≤ √(K / |B(0, 1)|) Q`, where `g` is the precise
representative of `∇u` and `∫_{B(x₀, r)} ‖∇u‖² ≤ K r^{n-1} Q²`: the minimum of `‖g‖²` over the
ball is at most its mean. -/
private theorem exists_mem_ball_mul_norm_preciseRepresentative_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r K Q : ℝ} (hr : 0 < r) (hball : ball x₀ r ⊆ Omega)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hgrad : ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ≤ K * r ^ ((n : ℝ) - 1) * Q ^ 2) :
    ∃ y ∈ ball x₀ r, r * ‖preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y‖ ≤
      √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q := by
  obtain ⟨g, hg⟩ : ∃ g, g = preciseRepresentative volume
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨_, rfl⟩
  rw [← hg]
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  rw [← hωdef]
  have hω : 0 < ω := hωdef ▸ Metric.measureReal_ball_pos volume 0 one_pos
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmem : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hball le_rfl)
  have hae : (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict (ball x₀ r)] g :=
    hg ▸ ae_eq_restrict_preciseRepresentative isOpen_ball
      (IntegrableOn.locallyIntegrableOn (hmem.integrable one_le_two))
  have hint : IntegrableOn (fun y => ‖g y‖ ^ 2) (ball x₀ r) :=
    (hmem.integrable_norm_pow two_ne_zero).congr (hae.mono fun y hy => by simp only [hy])
  obtain ⟨y, hy, hyle⟩ :=
    exists_le_setAverage (measure_ball_pos volume x₀ hr).ne' measure_ball_lt_top.ne hint
  have hvol : volume.real (ball x₀ r) = r ^ (n + 1) * ω := by
    rw [Measure.addHaar_real_ball_of_pos volume x₀ hr, finrank_euclideanSpace_fin, hωdef]
  have hmean : ∫ z in ball x₀ r, ‖g z‖ ^ 2 = ∫ z in ball x₀ r, ‖W1p.gradient u z‖ ^ 2 :=
    integral_congr_ae (hae.mono fun z hz => by simp only [hz])
  rw [setAverage_eq, smul_eq_mul, hmean, hvol] at hyle
  -- At `y`, `r ‖g y‖ ≤ √(K / ω) Q`.
  have hpow : r ^ 2 * r ^ ((n : ℝ) - 1) = r ^ (n + 1) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r (n + 1), ← Real.rpow_add hr]
    push_cast
    ring_nf
  have hy' : (r * ‖g y‖) ^ 2 ≤ (√(K / ω) * Q) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc r ^ 2 * ‖g y‖ ^ 2
        ≤ r ^ 2 * ((r ^ (n + 1) * ω)⁻¹ * (K * r ^ ((n : ℝ) - 1) * Q ^ 2)) := by
          gcongr
          exact hyle.trans (mul_le_mul_of_nonneg_left hgrad (by positivity))
      _ = (r ^ 2 * r ^ ((n : ℝ) - 1)) * K * Q ^ 2 / (r ^ (n + 1) * ω) := by
          field_simp
      _ = K / ω * Q ^ 2 := by
          rw [hpow]
          field_simp
  have hry : r * ‖g y‖ ≤ √(K / ω) * Q :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hy'
  exact ⟨y, hy, hry⟩

/-- **The supremum half of the scaled estimate.** If the precise representative `g` of `∇u` is
Hölder with constant `H` on `B(x₀, r) ⊆ Ω` and `∫_{B(x₀, r)} ‖∇u‖² ≤ K r^{n-1} Q²`, then
`r ‖g x‖ ≤ r H (2r)^β + √(K / |B(0, 1)|) Q` at every point `x` of `B(x₀, r)`: the Hölder bound
carries the bound of `exists_mem_ball_mul_norm_preciseRepresentative_le` from some point of the
ball to every other. -/
private theorem mul_norm_preciseRepresentative_le {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume Omega 2} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r H K Q : ℝ} {β : ℝ≥0}
    (hr : 0 < r) (hball : ball x₀ r ⊆ Omega) (hH0 : 0 ≤ H)
    (hH : HolderOnWith H.toNNReal β (preciseRepresentative volume
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
      (ball x₀ r))
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hgrad : ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ≤ K * r ^ ((n : ℝ) - 1) * Q ^ 2)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ ball x₀ r) :
    r * ‖preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x‖ ≤
      r * (H * (2 * r) ^ (β : ℝ)) +
        √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q := by
  obtain ⟨y, hy, hry⟩ := exists_mem_ball_mul_norm_preciseRepresentative_le hr hball hK hQ hgrad
  obtain ⟨g, hg⟩ : ∃ g, g = preciseRepresentative volume
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨_, rfl⟩
  rw [← hg] at hH hry ⊢
  -- From `y` to `x` by the Hölder bound, since `dist x y < 2r`.
  have hxy : dist x y ≤ 2 * r := by
    have := dist_triangle_right x y x₀
    rw [mem_ball] at hx hy
    linarith
  have hd := hH.dist_le_of_le hx hy hxy
  rw [Real.coe_toNNReal _ hH0, dist_eq_norm] at hd
  have hgx : ‖g x‖ ≤ ‖g y‖ + H * (2 * r) ^ (β : ℝ) :=
    (norm_le_norm_add_norm_sub' (g x) (g y)).trans (by linarith)
  nlinarith

/-- The assembly of the two halves of the scaled estimate, with the constant
`(1 + 2^β) C_h + √(K / |B(0, 1)|)`. -/
private theorem holderOnWith_and_mul_norm_le_of_holderOnWith
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r Ch K Q : ℝ} {β : ℝ≥0}
    (hr : 0 < r) (hball : ball x₀ (r / 2 + r) ⊆ Omega) (hCh : 0 ≤ Ch) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hH : HolderOnWith (Ch * r ^ (-(1 + (β : ℝ))) * Q).toNNReal β (preciseRepresentative volume
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
      (ball x₀ r))
    (hgrad : ∫ x in ball x₀ (r / 2 + r), ‖W1p.gradient u x‖ ^ 2 ≤
      K * r ^ ((n : ℝ) - 1) * Q ^ 2) :
    HolderOnWith (((1 + 2 ^ (β : ℝ)) * Ch +
        √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) *
          r ^ (-(1 + (β : ℝ))) * Q).toNNReal β (preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball x₀ r) ∧
      ∀ x ∈ ball x₀ r, r * ‖preciseRepresentative volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x‖ ≤
        ((1 + 2 ^ (β : ℝ)) * Ch +
          √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) * Q := by
  refine ⟨hH.mono_const (Real.toNNReal_le_toNNReal ?_), fun x hx => ?_⟩
  · have : 0 ≤ (2 ^ (β : ℝ) * Ch + √(K / volume.real
        (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) * r ^ (-(1 + (β : ℝ))) * Q := by
      positivity
    linarith
  have hsub : ball x₀ r ⊆ ball x₀ (r / 2 + r) := ball_subset_ball (by linarith)
  have hint : IntegrableOn (fun x => ‖W1p.gradient u x‖ ^ 2) (ball x₀ (r / 2 + r)) :=
    ((Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable_norm_pow two_ne_zero
  have hΦ : ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ≤ K * r ^ ((n : ℝ) - 1) * Q ^ 2 :=
    (setIntegral_mono_set hint (ae_of_all _ fun _ => by positivity) hsub.eventuallySubset).trans
      hgrad
  have hm := mul_norm_preciseRepresentative_le hr (hsub.trans hball) (by positivity) hH hK hQ hΦ hx
  -- `r (C_h r^{-(1+β)} Q) (2r)^β = 2^β C_h Q`.
  have hpow : r * r ^ (-(1 + (β : ℝ))) * (2 * r) ^ (β : ℝ) = 2 ^ (β : ℝ) := by
    have h1 : r * r ^ (-(1 + (β : ℝ))) * r ^ (β : ℝ) = 1 := by
      rw [mul_assoc, ← Real.rpow_add hr, show -(1 + (β : ℝ)) + β = -1 by ring,
        Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']
    rw [Real.mul_rpow zero_le_two hr.le]
    linear_combination (2 : ℝ) ^ (β : ℝ) * h1
  calc _ ≤ _ := hm
    _ = 2 ^ (β : ℝ) * Ch * Q +
        √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q := by
        rw [← hpow]
        ring
    _ ≤ _ := by nlinarith

/-- **The interior Schauder estimate for divergence-form equations, in scaled form.** Let
`0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and `β ≤ 1 - d/q`, where `d = n + 1` and `d/∞ = 0`.
There is a constant `C`, depending only on `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, such that the
following holds. Let `Ω ⊆ ℝ^{n+1}` be open and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every
test function `φ`. Let `B(x₀, 2r) ⊆ Ω`, let `a` be uniformly elliptic with constants `λ`, `Λ` on
`B(x₀, 2r)`, let `a` and `G` be `α`-Hölder on `B(x₀, 2r)` with constants `K_a` and `K_G`, the
oscillation of `a` measured in the operator norm of the attached bilinear forms, where
`r^α K_a ≤ M`, and let `f ∈ L^q(B(x₀, 2r))`. Write

`Q = r^{-d/2} ‖u‖_{L²(B(x₀, 2r))} + r^{2-d/q} ‖f‖_{L^q(B(x₀, 2r))} + r^{1+α} K_G`.

Then the precise representative of `∇u` is `β`-Hölder on `B(x₀, r)` with constant
`C r^{-(1+β)} Q`, and `r ‖∇u(x)‖ ≤ C Q` for every `x ∈ B(x₀, r)`. In other words
`r^{1+β} [∇u]_{β; B(x₀, r)} + r ‖∇u‖_{∞; B(x₀, r)} ≤ 2 C Q`. Every term scales like `u` under
`u ↦ u(x₀ + r ·)`. The largest admissible exponent is `β = min α (1 - d/q)` when this is less than
`1`, which needs `q > d`. The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ},
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ (2 * r)) →
      HolderOnWith KG α G (ball x₀ (2 * r)) → (Ka : ℝ) * r ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball x₀ (2 * r))) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      0 < r → ball x₀ (2 * r) ⊆ Omega →
      HolderOnWith (C * r ^ (-(1 + (β : ℝ))) * (r ^ (-(((n : ℝ) + 1) / 2)) *
            √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
          r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG)).toNNReal β
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball x₀ r) ∧
      ∀ x ∈ ball x₀ r, r * ‖preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x‖ ≤
        C * (r ^ (-(((n : ℝ) + 1) / 2)) * √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
          r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG) := by
  obtain ⟨Ch, hCh, hhol⟩ := exists_holderOnWith_preciseRepresentative_gradient_ball (n := n) hβ
    hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨K, hK, hgrad⟩ := exists_setIntegral_ball_norm_gradient_sq_le_mul_rpow_mul_sq (n := n)
    (hβ.trans_le hβα) hq lam Lam
  refine ⟨(1 + 2 ^ (β : ℝ)) * Ch +
    √(K / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), by positivity, ?_⟩
  intro Omega u a G f Ka KG x₀ r h haK hGK hM hf hu hr hball
  exact holderOnWith_and_mul_norm_le_of_holderOnWith hr
    ((ball_subset_ball (by linarith)).trans hball) hCh hK (by positivity)
    (hhol h haK hGK hM hf hu hr hball) (hgrad h haK hGK hf hu hr hball)

/-- A bound `|u| ≤ M_u` almost everywhere on `B(x₀, 2r)` bounds the scaled `L²` norm:
`r^{-d/2} ‖u‖_{L²(B(x₀, 2r))} ≤ 2^{d/2} |B(0, 1)|^{1/2} M_u`, where `d = n + 1`. -/
private theorem rpow_neg_mul_sqrt_setIntegral_le {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {u : W1p volume Omega 2} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r Mu : ℝ} (hr : 0 < r)
    (hball : ball x₀ (2 * r) ⊆ Omega)
    (hMu : ∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |W1p.value u x| ≤ Mu) :
    0 ≤ Mu ∧ r ^ (-(((n : ℝ) + 1) / 2)) * √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) ≤
      2 ^ (((n : ℝ) + 1) / 2) *
        √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Mu := by
  have hr2 : (0 : ℝ) < 2 * r := by positivity
  have hMu0 : 0 ≤ Mu := nonneg_of_ae_restrict_abs_le (measure_ball_pos volume x₀ hr2).ne' hMu
  have : IsFiniteMeasure (volume.restrict (ball x₀ (2 * r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : ∫ x in ball x₀ (2 * r), W1p.value u x ^ 2 ≤ ∫ _ in ball x₀ (2 * r), Mu ^ 2 :=
    integral_mono_ae ((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable_sq (integrable_const _)
      (hMu.mono fun x hx => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2)
  rw [setIntegral_const, smul_eq_mul] at hint
  have hsq : √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) ≤
      √(volume.real (ball x₀ (2 * r))) * Mu := by
    calc _ ≤ √(volume.real (ball x₀ (2 * r)) * Mu ^ 2) := Real.sqrt_le_sqrt hint
      _ = _ := by rw [Real.sqrt_mul measureReal_nonneg, Real.sqrt_sq hMu0]
  rw [Measure.sqrt_addHaar_real_ball volume x₀ hr2, finrank_euclideanSpace_fin] at hsq
  push_cast at hsq
  refine ⟨hMu0, (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq ?_⟩
  have h1 : r ^ (-(((n : ℝ) + 1) / 2)) * r ^ (((n : ℝ) + 1) / 2) = 1 := by
    rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
  rw [Real.mul_rpow zero_le_two hr.le]
  linear_combination (2 ^ (((n : ℝ) + 1) / 2) *
    √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Mu) * h1

/-- **The interior Schauder estimate for divergence-form equations, in scaled form with the
supremum of `|u|`.** This is
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le` with the
scaled `L²` norm of `u` replaced by a bound `M_u` for `|u|` almost everywhere on `B(x₀, 2r)`: with
`d = n + 1` and the hypotheses there, the precise representative of `∇u` is `β`-Hölder on
`B(x₀, r)` with constant `C r^{-(1+β)} Q`, and `r ‖∇u(x)‖ ≤ C Q` on `B(x₀, r)`, where

`Q = M_u + r^{2-d/q} ‖f‖_{L^q(B(x₀, 2r))} + r^{1+α} K_G`,

and `C` depends only on `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`. This is the form

`r^{1+β} [∇u]_{β; B_r} + r ‖∇u‖_{∞; B_r}`
`  ≲ ‖u‖_{∞; B_{2r}} + r^{2-d/q} ‖f‖_{L^q(B_{2r})} + r^{1+α} [G]_{α; B_{2r}}`

of the interior `C^{1,β}` estimate (Gilbarg–Trudinger, Theorem 8.32, for the `sup |u|` form). -/
theorem exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le_of_ae_abs_le
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0}
      {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {r Mu : ℝ},
      UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ (2 * r)) →
      HolderOnWith KG α G (ball x₀ (2 * r)) → (Ka : ℝ) * r ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (ball x₀ (2 * r))) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Omega, f x * φ x) →
      (∀ᵐ x ∂volume.restrict (ball x₀ (2 * r)), |W1p.value u x| ≤ Mu) →
      0 < r → ball x₀ (2 * r) ⊆ Omega →
      HolderOnWith (C * r ^ (-(1 + (β : ℝ))) * (Mu +
          r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG)).toNNReal β
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball x₀ r) ∧
      ∀ x ∈ ball x₀ r, r * ‖preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x‖ ≤
        C * (Mu + r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
            (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
          r ^ (1 + (α : ℝ)) * KG) := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le (n := n) hβ hβ1 hβα
      hq hβq (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 ^ (((n : ℝ) + 1) / 2) *
      √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ by positivity
  refine ⟨C * (c + 1), by positivity, ?_⟩
  intro Omega u a G f Ka KG x₀ r Mu h haK hGK hM hf hu hMu hr hball
  obtain ⟨hH, hsup⟩ := hmain h haK hGK hM hf hu hr hball
  obtain ⟨hMu0, hU⟩ := rpow_neg_mul_sqrt_setIntegral_le (n := n) hr hball hMu
  rw [← hc] at hU
  have h₂ : 0 ≤ r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
      (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal := by positivity
  have h₃ : 0 ≤ r ^ (1 + (α : ℝ)) * KG := by positivity
  -- The scaled `L²` term is at most `c M_u`.
  have hQle : r ^ (-(((n : ℝ) + 1) / 2)) * √(∫ x in ball x₀ (2 * r), W1p.value u x ^ 2) +
      r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
        (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
      r ^ (1 + (α : ℝ)) * KG ≤
      (c + 1) * (Mu + r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
        (eLpNorm f q (volume.restrict (ball x₀ (2 * r)))).toReal +
      r ^ (1 + (α : ℝ)) * KG) := by
    nlinarith [mul_nonneg hc0 h₂, mul_nonneg hc0 h₃]
  refine ⟨hH.mono_const (Real.toNNReal_le_toNNReal ?_), fun x hx => (hsup x hx).trans ?_⟩
  · exact (mul_le_mul_of_nonneg_left hQle (by positivity)).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left hQle hC).trans_eq (by ring)

end PDE

end TauCeti
