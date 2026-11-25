/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Unitization
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.Order.Compact

/-!
# The unitization extension of a faithful trace on `c₀`

On `c₀ = C₀(ℕ, ℂ)`, ordered by its spectral order, `τ(f) = Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)` is a faithful positive
functional (`faithfulFunctional`, `eq_zero_of_faithfulFunctional_star_mul_self_eq_zero`). Since `c₀`
has no unit (`no_identity`), its extension `τ⁺¹` to the unitization `c` is faithful too, by
`PositiveContinuousLinearMap.eq_zero_of_unitization_map_star_mul_self_eq_zero`
(`unitization_faithfulFunctional_faithful`).
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
noncomputable abbrev w (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

private theorem summable_w : Summable w :=
  (summable_geometric_two).mul_left (1 / 2) |>.congr fun n ↦ by simp [w, pow_succ, mul_comm]

private theorem summable_mul (f : C₀(ℕ, ℂ)) : Summable fun n ↦ (w n : ℂ) * f n :=
  Summable.of_norm_bounded (summable_w.mul_left ‖f.toBCF‖) fun n ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (f.toBCF.norm_coe_le_norm n) (by positivity)

/-- The linear functional `f ↦ Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)` on `c₀`. -/
noncomputable def faithfulLinear : C₀(ℕ, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑' n, (w n : ℂ) * f n
  map_add' f g := by
    simp only [FunLike.coe_add, Pi.add_apply, mul_add]
    exact (summable_mul f).tsum_add (summable_mul g)
  map_smul' c f := by
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← tsum_mul_left]
    exact tsum_congr fun n ↦ by ring

private theorem faithfulLinear_star_mul_self (g : C₀(ℕ, ℂ)) :
    faithfulLinear (star g * g) = ((∑' n, w n * ‖g n‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  simp [Complex.conj_mul']

private theorem summable_w_mul_sq (g : C₀(ℕ, ℂ)) : Summable fun n ↦ w n * ‖g n‖ ^ 2 := by
  have := (summable_mul (star g * g)).norm
  refine this.congr fun n ↦ ?_
  simp [w, pow_two]

/-- The faithful positive functional `τ(f) = Σₙ 2⁻⁽ⁿ⁺¹⁾ f(n)` on `c₀`. -/
noncomputable def faithfulFunctional : C₀(ℕ, ℂ) →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.ofClass <| PositiveLinearMap.mk₀ faithfulLinear fun f hf ↦ by
    obtain ⟨g, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hf
    rw [faithfulLinear_star_mul_self]
    exact Complex.zero_le_real.mpr (tsum_nonneg fun n ↦ by positivity)

private theorem faithfulFunctional_apply (f : C₀(ℕ, ℂ)) :
    faithfulFunctional f = faithfulLinear f :=
  rfl

/-- **`τ` is faithful.** -/
theorem eq_zero_of_faithfulFunctional_star_mul_self_eq_zero (g : C₀(ℕ, ℂ))
    (h : faithfulFunctional (star g * g) = 0) : g = 0 := by
  have h' : ∑' n, w n * ‖g n‖ ^ 2 = 0 := by
    have := faithfulLinear_star_mul_self g
    rw [faithfulFunctional_apply] at h
    exact_mod_cast this.symm.trans h
  have hz := (hasSum_zero_iff_of_nonneg (fun n ↦ by positivity)).mp
    (h' ▸ (summable_w_mul_sq g).hasSum)
  ext n
  have := congrFun hz n
  simpa [w] using this

/-- **`c₀` has no unit**: a unit `e` would be `1` at every point, but `e` vanishes at infinity. -/
theorem no_identity : ¬∃ e : C₀(ℕ, ℂ), ∀ a : C₀(ℕ, ℂ), e * a = a ∧ a * e = a := by
  rintro ⟨e, he⟩
  have h1 (n : ℕ) : e n = 1 := by
    let a : C₀(ℕ, ℂ) := ⟨⟨Pi.single n 1, continuous_of_discreteTopology⟩, by
      rw [cocompact_eq_atTop]
      exact tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨n + 1, fun m hm ↦ by
        simp [show m ≠ n by omega]⟩)⟩
    have := congrArg (· n) (he a).1
    simpa [a] using this
  have ht := e.zero_at_infty'
  rw [cocompact_eq_atTop] at ht
  have := tendsto_nhds_unique (tendsto_const_nhds.congr fun n ↦ (h1 n).symm) ht
  exact one_ne_zero this

/-- **Check.** The extension `τ⁺¹` of the faithful functional `τ` to the unitization of `c₀` is
faithful, since `c₀` has no unit. -/
theorem unitization_faithfulFunctional_faithful {x : Unitization ℂ C₀(ℕ, ℂ)}
    (hx : faithfulFunctional.unitization (star x * x) = 0) : x = 0 :=
  faithfulFunctional.eq_zero_of_unitization_map_star_mul_self_eq_zero
    eq_zero_of_faithfulFunctional_star_mul_self_eq_zero no_identity hx

end TauCeti.UnitizationC0Example
