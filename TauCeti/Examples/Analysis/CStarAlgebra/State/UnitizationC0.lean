/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Unitization
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# The unitization extension of a faithful trace on `c₀`

On `c₀ = C₀(ℕ, ℂ)`, ordered by its spectral order, `τ(f) = Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)` is a faithful positive
functional (`faithfulFunctional`, `eq_zero_of_faithfulFunctional_star_mul_self_eq_zero`). Since `c₀`
has no unit (`no_identity`), its extension `τ⁺¹` to the unitization `Unitization ℂ C₀(ℕ, ℂ)` is
faithful too, by `PositiveContinuousLinearMap.eq_zero_of_unitization_map_star_mul_self_eq_zero`
(`eq_zero_of_unitization_faithfulFunctional_star_mul_self_eq_zero`). The identification of this
unitization with the space `c` of convergent sequences is not formalized here.
-/

public section

open scoped ZeroAtInfty ComplexOrder

namespace TauCeti.UnitizationC0Example

/-- The spectral order on `c₀`, for which the nonnegative elements are the `g⋆ g`. -/
noncomputable local instance spectralPartialOrder : PartialOrder C₀(ℕ, ℂ) :=
  CStarAlgebra.spectralOrder _

/-- `c₀` with its spectral order is a star-ordered ring. -/
local instance spectralStarOrderedRing : StarOrderedRing C₀(ℕ, ℂ) :=
  CStarAlgebra.spectralOrderedRing _

/-- The weights `2⁻⁽ⁿ⁺¹⁾`, of sum `1`. -/
private noncomputable abbrev w (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

private theorem summable_w : Summable w :=
  (summable_geometric_two).mul_left (1 / 2) |>.congr fun n ↦ by simp [w, pow_succ, mul_comm]

/-- The weights `2⁻⁽ⁿ⁺¹⁾`, as an absolutely summable family. -/
private noncomputable def weights : lp (fun _ : ℕ ↦ ℂ) 1 :=
  ⟨fun n ↦ (w n : ℂ), memℓp_gen <| summable_w.congr fun n ↦ by simp [w]⟩

private theorem dualEquiv_weights_star_mul_self (g : C₀(ℕ, ℂ)) :
    ZeroAtInftyContinuousMap.dualEquiv ℂ ℕ weights (star g * g) =
      ((∑' n, w n * ‖g n‖ ^ 2 : ℝ) : ℂ) := by
  rw [ZeroAtInftyContinuousMap.dualEquiv_apply, Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  simp [weights, Complex.conj_mul']

private theorem summable_w_mul_sq (g : C₀(ℕ, ℂ)) : Summable fun n ↦ w n * ‖g n‖ ^ 2 :=
  (summable_w.mul_right (‖g‖ ^ 2)).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (g.norm_coe_le_norm n) 2)
      (by positivity)

/-- The faithful positive functional `τ(f) = Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)` on `c₀`. -/
noncomputable def faithfulFunctional : C₀(ℕ, ℂ) →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.ofClass <| PositiveLinearMap.mk₀
    (ZeroAtInftyContinuousMap.dualEquiv ℂ ℕ weights).toLinearMap fun f hf ↦ by
      obtain ⟨g, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hf
      rw [ContinuousLinearMap.coe_coe, dualEquiv_weights_star_mul_self]
      exact Complex.zero_le_real.mpr (tsum_nonneg fun n ↦ by positivity)

/-- `τ` is the series `Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)`. -/
@[simp]
theorem faithfulFunctional_apply (f : C₀(ℕ, ℂ)) :
    faithfulFunctional f = ∑' n, (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * f n :=
  ZeroAtInftyContinuousMap.dualEquiv_apply weights f

/-- **`τ` is faithful.** -/
theorem eq_zero_of_faithfulFunctional_star_mul_self_eq_zero (g : C₀(ℕ, ℂ))
    (h : faithfulFunctional (star g * g) = 0) : g = 0 := by
  have h' : ∑' n, w n * ‖g n‖ ^ 2 = 0 := by
    have : faithfulFunctional (star g * g) = _ := dualEquiv_weights_star_mul_self g
    exact_mod_cast this.symm.trans h
  have hz := (hasSum_zero_iff_of_nonneg (fun n ↦ by positivity)).mp
    (h' ▸ (summable_w_mul_sq g).hasSum)
  ext n
  have := congrFun hz n
  simpa [w] using this

/-- **`c₀` has no unit**: no element of `c₀` is a two-sided multiplicative identity. -/
theorem no_identity : ¬∃ e : C₀(ℕ, ℂ), ∀ a : C₀(ℕ, ℂ), e * a = a ∧ a * e = a := by
  rintro ⟨e, he⟩
  have h1 (n : ℕ) : e n = 1 := by
    simpa using congrArg (· n) (he (ZeroAtInftyContinuousMap.single n 1)).1
  exact one_ne_zero <|
    tendsto_nhds_unique (tendsto_const_nhds.congr fun n ↦ (h1 n).symm) e.tendsto_cofinite

/-- **Faithfulness of `τ⁺¹` on the unitization of `c₀`.** The extension `τ⁺¹` of the faithful
functional `τ` to `Unitization ℂ C₀(ℕ, ℂ)` vanishes on `x⋆ x` only for `x = 0`. -/
theorem eq_zero_of_unitization_faithfulFunctional_star_mul_self_eq_zero
    {x : Unitization ℂ C₀(ℕ, ℂ)} (hx : faithfulFunctional.unitization (star x * x) = 0) : x = 0 :=
  faithfulFunctional.eq_zero_of_unitization_map_star_mul_self_eq_zero
    eq_zero_of_faithfulFunctional_star_mul_self_eq_zero no_identity hx

end TauCeti.UnitizationC0Example
