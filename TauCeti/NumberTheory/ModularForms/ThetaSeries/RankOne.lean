/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Theta series of rank-one lattices

The theta series of `ℤ ∙ 1 ⊆ ℝ` is Mathlib's `jacobiTheta`, with exponent `π i n² τ`. Rescaling by
any nonzero real scalar `c` gives `Θ_{c ℤ}(τ) = θ(c² τ)` (`ZLattice.thetaSeries_span_singleton`),
and for the dual lattice `(c ℤ)^∨` gives `Θ_{(c ℤ)^∨}(τ) = θ(c⁻² τ)` for all `c : ℝ`
(`ZLattice.thetaSeries_dual_span_singleton`, with both sides vanishing at `c = 0`). For `ℤ` itself,
the period-two expansion has constant coefficient one, coefficient two at each positive square, and
zero elsewhere, matching Mathlib's `hasSum_nat_jacobiTheta`.

On the imaginary axis `re τ = 0`, `y ↦ θ(i y)` is strictly decreasing on `(0, ∞)`
(`TauCeti.strictAntiOn_jacobiTheta_I_mul`), so `Θ_{c₂ ℤ}(τ) < Θ_{c₁ ℤ}(τ)` whenever
`0 < |c₁| < |c₂|` (`ZLattice.thetaSeries_span_singleton_lt_of_abs_lt`) — even when neither lattice
is contained in the other. Consequently `Θ_{(c ℤ)^∨}(i) = Θ_{c ℤ}(i)` and `Θ_{(c ℤ)^∨} = Θ_{c ℤ}`
each hold if and only if `|c| = 1` (`ZLattice.thetaSeries_dual_span_singleton_eq_I_iff`,
`ZLattice.thetaSeries_dual_span_singleton_eq_iff`).

For the non-integral lattice `L = ½ ℤ ⊆ ℝ`, the dual is `L^∨ = 2 ℤ < L`
(`ZLattice.dual_span_inv_two`, `ZLattice.dual_span_inv_two_lt`), the discriminant group `A_L` is
trivial (`ZLattice.subsingleton_discriminantGroup_span_inv_natCast`), and
`Θ_{2ℤ}(i) < Θ_{½ℤ}(i)`, so `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)` and `Θ_{L^∨}(i) ≠ ∑_{γ ∈ A_L} θ_γ(i)`
(`ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`,
`ZLattice.thetaSeries_dual_span_inv_natCast_ne_sum_thetaCosetClass_I`,
`ZLattice.thetaSeries_dual_span_inv_two_ne_tsum_thetaCosetClass_I`). This witnesses directly that
`ZLattice.IsIntegral.thetaSeries_dual_eq_sum` cannot drop its integrality hypothesis.

## Main statements

* `ZLattice.thetaSeries_span_one`, `ZLattice.thetaSeries_span_singleton`,
  `ZLattice.thetaSeries_dual_span_singleton`: `Θ_{ℤ}(τ) = θ(τ)`, `Θ_{c ℤ}(τ) = θ(c² τ)` (`c ≠ 0`),
  and `Θ_{(c ℤ)^∨}(τ) = θ(c⁻² τ)` (all `c : ℝ`).
* `ZLattice.qExpansion_two_thetaSeries_span_one_coeff`,
  `ZLattice.hasSum_thetaSeries_span_one_qParam`: the period-two square-supported `q`-expansion of
  `Θ_{ℤ}`.
* `ZLattice.thetaSeries_span_singleton_lt_of_abs_lt`,
  `ZLattice.thetaSeries_dual_span_singleton_eq_I_iff`,
  `ZLattice.thetaSeries_dual_span_singleton_eq_iff`: strict antitone comparison in `|c|` on the
  imaginary axis, and `Θ_{(c ℤ)^∨} = Θ_{c ℤ} ↔ |c| = 1`.
* `ZLattice.dual_span_inv_two`, `ZLattice.dual_span_inv_two_lt`,
  `ZLattice.thetaSeries_span_two_lt_thetaSeries_span_inv_two`,
  `ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`,
  `ZLattice.thetaSeries_dual_span_inv_two_ne_I`,
  `ZLattice.thetaSeries_dual_span_inv_natCast_ne_sum_thetaCosetClass_I`,
  `ZLattice.thetaSeries_dual_span_inv_two_ne_tsum_thetaCosetClass_I`: the non-integral lattices
  `n⁻¹ ℤ` (`n ≠ 1`) and `½ ℤ`, where `L^∨ = 2 ℤ < L` and `Θ_{L^∨}(i) ≠ ∑_{γ ∈ A_L} θ_γ(i)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped ComplexOrder Pointwise Real UpperHalfPlane

namespace ZLattice

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ 1 one_ne_zero).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- For `c ≠ 0`, the theta series of the rank-one lattice `c ℤ ⊆ ℝ` is `θ(c² τ)`. -/
theorem thetaSeries_span_singleton {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {c} : Submodule ℤ ℝ) τ = jacobiTheta ((c ^ 2 : ℝ) * (τ : ℂ)) := by
  have hspan : (span ℤ {c} : Submodule ℤ ℝ) = c • span ℤ {1} := by
    rw [Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]
  rw [hspan, thetaSeries_smul _ hc, thetaSeries_span_one, UpperHalfPlane.coe_pos_real_smul,
    Complex.real_smul]

/-- For every `c : ℝ`, the theta series of the dual of `c ℤ ⊆ ℝ` is `θ(c⁻² τ)` (for `c = 0` both
sides vanish: the dual of `0` is `ℝ`, which is not discrete, and `θ(0) = 0`). -/
theorem thetaSeries_dual_span_singleton (c : ℝ) (τ : ℍ) :
    thetaSeries (dual (span ℤ {c} : Submodule ℤ ℝ)) τ =
      jacobiTheta (((c ^ 2)⁻¹ : ℝ) * (τ : ℂ)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hnd : ¬ DiscreteTopology (⊤ : Submodule ℤ ℝ) := fun hd ↦ by
      obtain ⟨ε, hε, hball⟩ :=
        Metric.isOpen_singleton_iff.mp (isOpen_discrete {(0 : (⊤ : Submodule ℤ ℝ))})
      have hmem : (⟨ε / 2, trivial⟩ : (⊤ : Submodule ℤ ℝ)) = 0 :=
        hball _ (by simpa [abs_of_pos hε] using half_lt_self hε)
      have hval : ε / 2 = 0 := congrArg Subtype.val hmem
      linarith
    rw [Submodule.span_zero_singleton, dual_bot, ← thetaCoset_zero,
      thetaCoset_eq_zero_of_forall_not_summable _ 0 fun y hy hs ↦
        hnd (discreteTopology_of_summable_exp_neg_mul_norm_add_sq _ 0 (by positivity) hs)]
    simp [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_undef]
  · rw [dual_span_singleton hc, thetaSeries_span_singleton (inv_ne_zero hc), inv_pow]

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  rw [thetaSeries_smul _ (Real.sqrt_ne_zero'.mpr two_pos), thetaSeries_span_one]
  congr 1
  simp [Complex.real_smul]

/-- The period-two coefficients of the rank-one lattice theta series, explicitly supported at
the squares. -/
theorem qExpansion_two_thetaSeries_span_one_coeff (m : ℕ) :
    (qExpansion 2 (thetaSeries (span ℤ {1} : Submodule ℤ ℝ))).coeff m =
      if m = 0 then 1 else if IsSquare m then 2 else 0 := by
  rw [isUnimodular_span_one.isIntegral.qExpansion_two_thetaSeries_coeff,
    representationNumber_span_one]
  split_ifs <;> norm_num

/-- The lattice theta series has the period-two square-supported power series, so its terms
have exactly the same multiplicities as Jacobi's positive-square expansion. -/
theorem hasSum_thetaSeries_span_one_qParam (τ : ℍ) :
    HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else if IsSquare m then 2 else 0 : ℂ) * Periodic.qParam 2 τ ^ m)
      (thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ) := by
  classical
  simpa only [representationNumber_span_one, smul_eq_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_zero] using
    isUnimodular_span_one.isIntegral.hasSum_thetaSeries_qParam_two τ

/-! ### Imaginary-axis comparison and the lattice `½ ℤ` -/

/-- On the imaginary axis (`re τ = 0`), scaling up the generator of `c ℤ ⊆ ℝ` strictly decreases
its theta value: for `0 < |c₁| < |c₂|`, `Θ_{c₂ ℤ}(τ) < Θ_{c₁ ℤ}(τ)` in the real-part order on `ℂ`
(both values are real). -/
theorem thetaSeries_span_singleton_lt_of_abs_lt {c₁ c₂ : ℝ} (hc₁ : c₁ ≠ 0) (hc : |c₁| < |c₂|)
    {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (span ℤ {c₂} : Submodule ℤ ℝ) τ <
      thetaSeries (span ℤ {c₁} : Submodule ℤ ℝ) τ := by
  have hc₂ : c₂ ≠ 0 := abs_pos.mp ((abs_pos.mpr hc₁).trans hc)
  have hmul (r : ℝ) : (r : ℂ) * (τ : ℂ) = I * ((r * τ.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hτ]
  rw [thetaSeries_span_singleton hc₂, thetaSeries_span_singleton hc₁, hmul, hmul]
  exact TauCeti.strictAntiOn_jacobiTheta_I_mul
    (mul_pos (sq_pos_of_ne_zero hc₁) τ.im_pos) (mul_pos (sq_pos_of_ne_zero hc₂) τ.im_pos)
    (mul_lt_mul_of_pos_right (sq_lt_sq.mpr hc) τ.im_pos)

/-- At `τ = i`, `Θ_{(c ℤ)^∨}(i) = Θ_{c ℤ}(i)` holds if and only if `|c| = 1` (equivalently, `c ℤ`
is unimodular). -/
@[simp]
theorem thetaSeries_dual_span_singleton_eq_I_iff {c : ℝ} :
    thetaSeries (dual (span ℤ {c} : Submodule ℤ ℝ)) UpperHalfPlane.I =
      thetaSeries (span ℤ {c} : Submodule ℤ ℝ) UpperHalfPlane.I ↔ |c| = 1 := by
  refine ⟨fun heq ↦ ?_, fun h1 ↦ by rw [(isUnimodular_span_singleton_iff.mpr h1).dual_eq]⟩
  rcases eq_or_ne c 0 with rfl | hc
  · rw [thetaSeries_dual_span_singleton, span_singleton_eq_bot.mpr rfl, thetaSeries_apply,
      tsum_eq_single (0 : (⊥ : Submodule ℤ ℝ)) fun v hv ↦ (hv (Subsingleton.elim v 0)).elim] at heq
    simp [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_undef] at heq
  rcases lt_trichotomy |c| 1 with hlt | h1 | hgt
  · have hlt' : |c| < |c⁻¹| := by
      rw [abs_inv]
      exact hlt.trans ((one_lt_inv₀ (abs_pos.mpr hc)).mpr hlt)
    rw [dual_span_singleton hc] at heq
    exact ((thetaSeries_span_singleton_lt_of_abs_lt hc hlt' UpperHalfPlane.I_re).ne heq).elim
  · exact h1
  · have hgt' : |c⁻¹| < |c| := by
      rw [abs_inv]
      exact (inv_lt_one_of_one_lt₀ hgt).trans hgt
    rw [dual_span_singleton hc] at heq
    exact ((thetaSeries_span_singleton_lt_of_abs_lt (inv_ne_zero hc) hgt'
      UpperHalfPlane.I_re).ne heq.symm).elim

/-- Across `ℍ`, `Θ_{(c ℤ)^∨} = Θ_{c ℤ}` holds if and only if `|c| = 1`. -/
@[simp]
theorem thetaSeries_dual_span_singleton_eq_iff {c : ℝ} :
    thetaSeries (dual (span ℤ {c} : Submodule ℤ ℝ)) =
      thetaSeries (span ℤ {c} : Submodule ℤ ℝ) ↔ |c| = 1 :=
  ⟨fun h ↦ thetaSeries_dual_span_singleton_eq_I_iff.mp (congrFun h _),
    fun h1 ↦ by rw [(isUnimodular_span_singleton_iff.mpr h1).dual_eq]⟩

/-- The dual of `½ ℤ ⊆ ℝ` is `2 ℤ ⊆ ℝ`. -/
theorem dual_span_inv_two :
    dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) = span ℤ {2} := by
  simpa using dual_span_singleton (inv_ne_zero (two_ne_zero' ℝ))

/-- For `L = ½ ℤ ⊆ ℝ`, the dual lattice `L^∨ = 2 ℤ` is a strict sublattice of `L`. -/
theorem dual_span_inv_two_lt :
    dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) < span ℤ {(2⁻¹ : ℝ)} := by
  rw [dual_span_inv_two]
  refine lt_of_le_of_ne ?_ fun heq ↦ not_isIntegral_span_inv_two ?_
  · rw [span_singleton_le_iff_mem, mem_span_singleton]
    exact ⟨4, by norm_num⟩
  · rw [isIntegral_iff_le_dual, dual_span_inv_two, heq]

/-- On the imaginary axis, `Θ_{2ℤ}(τ) < Θ_{½ℤ}(τ)` as real numbers. -/
theorem thetaSeries_span_two_lt_thetaSeries_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ <
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) τ :=
  thetaSeries_span_singleton_lt_of_abs_lt (by norm_num) (by norm_num) hτ

/-- At `τ = i`, `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`. -/
theorem thetaSeries_span_two_ne_thetaSeries_span_inv_two_I :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I :=
  (thetaSeries_span_two_lt_thetaSeries_span_inv_two UpperHalfPlane.I_re).ne

/-- For `L = ½ ℤ ⊆ ℝ`, `Θ_{L^∨}(i) ≠ Θ_L(i)`. -/
theorem thetaSeries_dual_span_inv_two_ne_I :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I := by
  rw [dual_span_inv_two]
  exact thetaSeries_span_two_ne_thetaSeries_span_inv_two_I

/-- For `n ≠ 1`, the lattice `L = n⁻¹ ℤ ⊆ ℝ` satisfies `Θ_{L^∨}(i) ≠ ∑_{γ ∈ A_L} θ_γ(i)` whenever
`A_L` is finite (`n = 0` is vacuous since `A_0 ≃ ℝ` is infinite, and for `n ≥ 2`, `A_L` is trivial
while `L^∨ = n ℤ < L`): `IsIntegral L` cannot be dropped in
`ZLattice.IsIntegral.thetaSeries_dual_eq_sum`. -/
theorem thetaSeries_dual_span_inv_natCast_ne_sum_thetaCosetClass_I {n : ℕ} (hn : n ≠ 1)
    [Fintype (DiscriminantGroup (span ℤ {((n : ℝ)⁻¹)} : Submodule ℤ ℝ))] :
    thetaSeries (dual (span ℤ {((n : ℝ)⁻¹)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {((n : ℝ)⁻¹)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {((n : ℝ)⁻¹)} : Submodule ℤ ℝ) γ UpperHalfPlane.I := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have hne : span ℝ ((span ℤ {(((0 : ℕ) : ℝ)⁻¹)} : Submodule ℤ ℝ) : Set ℝ) ≠ ⊤ := by simp
    have := infinite_discriminantGroup_of_span_ne_top hne
    exact (not_finite (DiscriminantGroup (span ℤ {(((0 : ℕ) : ℝ)⁻¹)} : Submodule ℤ ℝ))).elim
  · have := subsingleton_discriminantGroup_span_inv_natCast hn0
    rw [Fintype.sum_subsingleton _ 0, thetaCosetClass_zero, Ne,
      thetaSeries_dual_span_singleton_eq_I_iff]
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    rw [abs_inv, abs_of_pos (zero_lt_one.trans hn1)]
    exact (inv_lt_one_of_one_lt₀ hn1).ne

/-- For `L = ½ ℤ ⊆ ℝ`, `A_L = L^∨ ⧸ (L ∩ L^∨)` is trivial (`L^∨ = 2 ℤ < L`), so
`∑'_{γ ∈ A_L} θ_γ(i) = Θ_{½ℤ}(i) ≠ Θ_{L^∨}(i)`. -/
theorem thetaSeries_dual_span_inv_two_ne_tsum_thetaCosetClass_I :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑' γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ UpperHalfPlane.I := by
  have : Subsingleton (DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) := by
    simpa using subsingleton_discriminantGroup_span_inv_natCast two_ne_zero
  rw [tsum_eq_single 0 fun γ hγ ↦ (hγ (Subsingleton.elim γ 0)).elim, thetaCosetClass_zero]
  exact thetaSeries_dual_span_inv_two_ne_I

end ZLattice
