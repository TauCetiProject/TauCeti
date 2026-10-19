/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ExpLog
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic

/-!
# The logarithm identifies deep units with a deep additive group

Let `K` be a finite extension of `ℚ_[p]` with absolute ramification index `e`, and let `i` be a
depth with `e < (p - 1) * i`. On `𝓂[K] ^ i` the exponential series converges, and on
`U(K,i) = 1 + 𝓂[K] ^ i` the logarithm series converges; `TauCeti.log_exp_of_mem_maximalIdeal_pow`
and `TauCeti.exp_log_of_mem_unitFiltration` show that they are mutually inverse bijections.

This file proves that these bijections are group homomorphisms and homeomorphisms, and packages
them as an isomorphism of topological groups

`deepUnitExpLogEquiv : U(K,i) ≃ₜ* Multiplicative (𝓂[K] ^ i)`,

given by `u ↦ log u`, with inverse `x ↦ exp x`. The homomorphism property comes from the
functional equation `exp (x + y) = exp x * exp y` on `𝓂[K] ^ i`: in a nonarchimedean field the
Cauchy product of two convergent series converges to the product of their sums, and
coefficientwise it is the formal identity `PowerSeries.exp_mul_exp_eq_exp_add`. Continuity of the
exponential comes from its being an isometry of `𝓂[K] ^ i` into `K`, inherited from the isometry
property of the logarithm (`TauCeti.valuation_log_sub_log`).

This isomorphism turns multiplication of deep units into addition on `𝓂[K] ^ i`: raising to the
`n`-th power on `U(K,i)` corresponds to taking the `n`-fold sum on `𝓂[K] ^ i`.

## Main results

* `TauCeti.valuation_exp_sub_exp`: the exponential is an isometry on `𝓂[K] ^ i`.
* `TauCeti.continuous_exp_maximalIdeal_pow`: the exponential is continuous on `𝓂[K] ^ i`.
* `TauCeti.log_mul_of_mem_unitFiltration`: `log (u * w) = log u + log w` on `U(K,i)`.
* `TauCeti.deepUnitExpLogEquiv`: the isomorphism of topological groups
  `U(K,i) ≃ₜ* Multiplicative (𝓂[K] ^ i)` given by the logarithm, with the exponential as inverse.
* `TauCeti.exists_mem_unitFiltration_log_eq_smul`: every element of `K` has a nonzero
  `ℚ_p`-multiple which is the logarithm of a deep unit.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField NormedSpace

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}

/-- **The exponential is an isometry on deep elements.** On `𝓂[K] ^ i` with `(p - 1) * i > e`,
`v(exp x - exp y) = v(x - y)`. -/
theorem valuation_exp_sub_exp (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x y : (𝓂[K] ^ i : Ideal 𝒪[K])) :
    valuation K (exp (x : K) - exp (y : K)) = valuation K ((x : K) - y) := by
  obtain ⟨u, hu, hux⟩ := exists_mem_unitFiltration_eq_exp hi x
  obtain ⟨w, hw, hwy⟩ := exists_mem_unitFiltration_eq_exp hi y
  rw [← hux, ← hwy, ← valuation_log_sub_log hi hu hw, hux, hwy,
    log_exp_of_mem_maximalIdeal_pow hi, log_exp_of_mem_maximalIdeal_pow hi]

/-- On `𝓂[K] ^ i` with `(p - 1) * i > e`, the exponential is continuous. -/
theorem continuous_exp_maximalIdeal_pow (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    Continuous fun x : (𝓂[K] ^ i : Ideal 𝒪[K]) => exp (x : K) := by
  have hc : Continuous fun x : (𝓂[K] ^ i : Ideal 𝒪[K]) => ((x : 𝒪[K]) : K) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff.2 fun γ _ => ?_
  filter_upwards [(IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff.1 (hc.tendsto x) γ
    trivial] with y hy
  rwa [valuation_exp_sub_exp hi]

/-- **The logarithm is a homomorphism on deep units.** On `U(K,i)` with `(p - 1) * i > e`,
`log (u * w) = log u + log w`. -/
theorem log_mul_of_mem_unitFiltration (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u w : Kˣ} (hu : u ∈ unitFiltration K i) (hw : w ∈ unitFiltration K i) :
    log ((u : K) * w) = log (u : K) + log (w : K) := by
  obtain ⟨a, ha, hau⟩ := exists_mem_maximalIdeal_pow_eq_log hi hu
  obtain ⟨b, hb, hbw⟩ := exists_mem_maximalIdeal_pow_eq_log hi hw
  have hexp := exp_add_of_mem_maximalIdeal_pow hi ⟨a, ha⟩ ⟨b, hb⟩
  have hlog := log_exp_of_mem_maximalIdeal_pow hi (⟨a, ha⟩ + ⟨b, hb⟩)
  simp only [hau, hbw, exp_log_of_mem_unitFiltration hi hu,
    exp_log_of_mem_unitFiltration hi hw] at hexp
  push_cast at hlog
  rwa [hau, hbw, hexp] at hlog

/-- The logarithm of a deep unit, as an element of `𝓂[K] ^ i`. -/
private noncomputable def deepUnitLog (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (u : unitFiltration K i) : (𝓂[K] ^ i : Ideal 𝒪[K]) :=
  ⟨_, (exists_mem_maximalIdeal_pow_eq_log hi u.2).choose_spec.1⟩

private theorem coe_deepUnitLog (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (u : unitFiltration K i) : ((deepUnitLog hi u : 𝒪[K]) : K) = log ((u : Kˣ) : K) :=
  (exists_mem_maximalIdeal_pow_eq_log hi u.2).choose_spec.2

/-- The exponential of an element of `𝓂[K] ^ i`, as a deep unit. -/
private noncomputable def deepUnitExp (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) : unitFiltration K i :=
  ⟨_, (exists_mem_unitFiltration_eq_exp hi x).choose_spec.1⟩

private theorem coe_deepUnitExp (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) : ((deepUnitExp hi x : Kˣ) : K) = exp (x : K) :=
  (exists_mem_unitFiltration_eq_exp hi x).choose_spec.2

variable (K) in
/-- **The deep-unit logarithm.** For a finite extension `K` of `ℚ_[p]` with absolute ramification
index `e` and a depth `i` with `(p - 1) * i > e`, the logarithm is an isomorphism of topological
groups `U(K,i) ≃ₜ* Multiplicative (𝓂[K] ^ i)` from the deep units to the additive group
`𝓂[K] ^ i`, whose inverse is the exponential. -/
noncomputable def deepUnitExpLogEquiv (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    unitFiltration K i ≃ₜ* Multiplicative (𝓂[K] ^ i : Ideal 𝒪[K]) where
  toFun u := .ofAdd (deepUnitLog hi u)
  invFun x := deepUnitExp hi x.toAdd
  left_inv u := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_deepUnitExp, toAdd_ofAdd, coe_deepUnitLog, exp_log_of_mem_unitFiltration hi u.2]
  right_inv x := by
    refine Multiplicative.toAdd.injective (Subtype.ext (Subtype.ext ?_))
    rw [toAdd_ofAdd, coe_deepUnitLog, coe_deepUnitExp, log_exp_of_mem_maximalIdeal_pow hi]
  map_mul' u w := by
    refine Multiplicative.toAdd.injective (Subtype.ext (Subtype.ext ?_))
    simp only [toAdd_mul, toAdd_ofAdd, Submodule.coe_add, Subring.coe_add, coe_deepUnitLog,
      Subgroup.coe_mul, Units.val_mul]
    exact log_mul_of_mem_unitFiltration hi u.2 w.2
  continuous_toFun := by
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hi)
    refine continuous_ofAdd.comp (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
    exact (continuous_log_unitFiltration p hi1).congr fun u => (coe_deepUnitLog hi u).symm
  continuous_invFun := by
    refine Continuous.subtype_mk (Units.isEmbedding_val₀.continuous_iff.2 ?_) _
    exact ((continuous_exp_maximalIdeal_pow hi).comp continuous_toAdd).congr fun x =>
      (coe_deepUnitExp hi x.toAdd).symm

@[simp]
theorem coe_deepUnitExpLogEquiv_apply (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (u : unitFiltration K i) :
    (((deepUnitExpLogEquiv K hi u).toAdd : 𝒪[K]) : K) = log ((u : Kˣ) : K) :=
  coe_deepUnitLog hi u

@[simp]
theorem coe_deepUnitExpLogEquiv_symm_apply (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : Multiplicative (𝓂[K] ^ i : Ideal 𝒪[K])) :
    (((deepUnitExpLogEquiv K hi).symm x : Kˣ) : K) = exp ((x.toAdd : 𝒪[K]) : K) :=
  coe_deepUnitExp hi x.toAdd

/-- **Deep logarithms in every direction.** Every element `z` of `K` has a nonzero `ℚ_p`-multiple
which is the logarithm of a deep unit in `U(K,i)`: a nonzero element of `𝒪[ℚ_p]` carries `z` into
`𝒪[K]`, a further factor `p ^ i` carries it into `𝓂[K] ^ i`, and every element of `𝓂[K] ^ i` is
the logarithm of a deep unit. -/
theorem exists_mem_unitFiltration_log_eq_smul (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (z : K) : ∃ u ∈ unitFiltration K i, ∃ c : ℚ_[p], c ≠ 0 ∧ log (u : K) = c • z := by
  obtain ⟨a, ha, haz⟩ := exists_algebraMap_mul_mem_integerRing ℚ_[p] K z
  set w : (𝓂[K] ^ i : Ideal 𝒪[K]) := ⟨(p : 𝒪[K]) ^ i * ⟨_, haz⟩,
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (residuePrime_mem_maximalIdeal K p) i)⟩
  refine ⟨(deepUnitExpLogEquiv K hi).symm (Multiplicative.ofAdd w), SetLike.coe_mem _,
    (p : ℚ_[p]) ^ i * a, mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero)) (by simpa using ha), ?_⟩
  rw [← coe_deepUnitExpLogEquiv_apply hi, ContinuousMulEquiv.apply_symm_apply]
  simp [w, Algebra.smul_def, mul_assoc]

end TauCeti
