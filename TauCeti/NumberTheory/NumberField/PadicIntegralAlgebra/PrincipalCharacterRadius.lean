/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.NumberField.PadicIntegralAlgebra.Basic
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# The principal radius of a character of `O_pˣ`

Let `O_p = ℤ_p ⊗[ℤ] 𝓞 K` be the integral `p`-adic algebra of a number field `K`, and let
`κ : O_pˣ → Rˣ` be a continuous character with values in the units of a seminormed ring `R`, for
instance a uniform Banach `ℚ_p`-algebra with its power-multiplicative norm. The **principal
character radius** of `κ` is

```text
T(κ) = sup { ‖κ(u) - 1‖ : u ∈ H_depth },   depth = 1 for odd p, depth = 3 for p = 2,
```

where `H_r = 1 + pʳ O_p` is the principal unit group. It measures how far `κ` is from being
trivial on the principal units; it is the quantity from which the analytic radius of `κ` is
estimated (Andreatta–Iovita–Pilloni, Proposition 2.8), whose convention `depth = 3` at `p = 2` is
followed here. The supremum is attained, since `H_depth` is compact and `κ` is continuous.

The main result is the strict bound `T(κ) < 1` when `R` is ultrametric with `‖1‖ = 1`, its norm is
power-multiplicative and `‖p‖ < 1`, as for every uniform Banach `ℚ_p`-algebra. Indeed for
`u ∈ H_1` the powers `u ^ p ^ n` tend to `1`, so `κ(u) ^ p ^ n → 1`; and if `‖κ(u) - 1‖ ≥ 1` the
`p`-th power map would raise that distance to its `p`-th power
(`TauCeti.norm_sub_one_lt_one_of_tendsto_pow_prime_pow`), so each value is within distance less
than one of `1`; compactness turns this into a bound on the supremum.

The radius depends only on the restriction of `κ` to `H_depth`; in particular multiplying `κ` by a
finite-order character trivial on `H_depth` does not change it. A coefficient map `f : R →+* S`
with `‖f x‖ ≤ C ‖x‖` multiplies it by at most `C`. The trivial character has radius `0`.

## Main definitions

* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterDepth p`: the depth `1`, or `3`
  when `p = 2`.
* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterRadius κ`: the principal character
  radius `T(κ)`.

## Main results

* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterRadius_lt_one`: `T(κ) < 1` for an
  ultrametric power-multiplicative norm with `‖p‖ < 1`.
* `TauCeti.NumberField.PadicIntegralAlgebra.norm_sub_one_lt_one_of_mem_principalUnits`: under
  the same hypotheses, `‖κ(u) - 1‖ < 1` for every `u ∈ H_1`.
* `TauCeti.NumberField.PadicIntegralAlgebra.exists_norm_sub_one_eq_principalCharacterRadius`:
  the supremum is attained.
* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterRadius_le_iff`: the
  characterisation of `T(κ)` as the least upper bound of `‖κ(u) - 1‖` on `H_depth`.
* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterRadius_mul_of_forall_eq_one`:
  invariance under characters trivial on `H_depth`.
* `TauCeti.NumberField.PadicIntegralAlgebra.principalCharacterRadius_le_mul_of_norm_le`: the
  bound under bounded coefficient maps.

## References

* C. Birkbeck, B. Heuer, C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), §6.1.
* F. Andreatta, A. Iovita, V. Pilloni, *The adic, cuspidal, Hilbert eigenvarieties*, Res. Math.
  Sci. 3 (2016), §2, Proposition 2.8.
-/

public section

open Filter

namespace TauCeti.NumberField.PadicIntegralAlgebra

/-- The **depth** of the principal unit group on which the principal character radius is
measured: `1` for odd `p`, and `3` for `p = 2`. -/
def principalCharacterDepth (p : ℕ) : ℕ :=
  if p = 2 then 3 else 1

@[simp]
theorem principalCharacterDepth_two : principalCharacterDepth 2 = 3 := by
  simp [principalCharacterDepth]

theorem principalCharacterDepth_of_ne_two {p : ℕ} (hp : p ≠ 2) :
    principalCharacterDepth p = 1 := by
  simp [principalCharacterDepth, hp]

theorem one_le_principalCharacterDepth (p : ℕ) : 1 ≤ principalCharacterDepth p := by
  unfold principalCharacterDepth
  split_ifs <;> omega

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {R : Type*} [SeminormedRing R]

/-- The **principal character radius** `T(κ) = sup { ‖κ(u) - 1‖ : u ∈ H_depth }` of a continuous
character `κ : O_pˣ → Rˣ`, where `depth = principalCharacterDepth p`. -/
noncomputable def principalCharacterRadius (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) : ℝ :=
  ⨆ u : principalUnits K p (principalCharacterDepth p), ‖((κ u : Rˣ) : R) - 1‖

/-- The principal character radius depends only on the restriction of the character to
`H_depth`. -/
theorem principalCharacterRadius_congr {κ κ' : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ}
    (h : ∀ u ∈ principalUnits K p (principalCharacterDepth p), κ u = κ' u) :
    principalCharacterRadius κ = principalCharacterRadius κ' := by
  simp only [principalCharacterRadius]
  exact iSup_congr fun u ↦ by rw [h u u.property]

/-- The trivial character has principal character radius `0`. -/
@[simp]
theorem principalCharacterRadius_one :
    principalCharacterRadius (1 : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) = 0 := by
  simp [principalCharacterRadius]

/-- Multiplying a character by a character `χ` trivial on `H_depth`, for instance a finite-order
character of conductor at most `p ^ depth`, does not change its principal character radius. -/
theorem principalCharacterRadius_mul_of_forall_eq_one {R : Type*} [SeminormedCommRing R]
    (κ χ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ)
    (hχ : ∀ u ∈ principalUnits K p (principalCharacterDepth p), χ u = 1) :
    principalCharacterRadius (κ * χ) = principalCharacterRadius κ :=
  principalCharacterRadius_congr fun u hu ↦ by rw [ContinuousMonoidHom.mul_apply, hχ u hu, mul_one]

private theorem continuous_norm_sub_one (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) :
    Continuous fun u ↦ ‖((κ u : Rˣ) : R) - 1‖ :=
  continuous_norm.comp ((Units.continuous_val.comp κ.continuous).sub continuous_const)

variable [NumberField K]

private theorem exists_isMaxOn_norm_sub_one (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) :
    ∃ u ∈ principalUnits K p (principalCharacterDepth p), IsMaxOn (fun u ↦ ‖((κ u : Rˣ) : R) - 1‖)
      (principalUnits K p (principalCharacterDepth p)) u :=
  (isCompact_principalUnits K p _).exists_isMaxOn ⟨1, one_mem _⟩
    (continuous_norm_sub_one κ).continuousOn

private theorem bddAbove_range_norm_sub_one (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) :
    BddAbove (Set.range fun v : principalUnits K p (principalCharacterDepth p) ↦
      ‖((κ v : Rˣ) : R) - 1‖) := by
  obtain ⟨u, -, hmax⟩ := exists_isMaxOn_norm_sub_one κ
  exact ⟨_, Set.forall_mem_range.2 fun v ↦ hmax v.property⟩

/-- Every value `‖κ(u) - 1‖` with `u ∈ H_depth` is at most the principal character radius. -/
theorem norm_sub_one_le_principalCharacterRadius (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ)
    {u : (PadicIntegralAlgebra K p)ˣ} (hu : u ∈ principalUnits K p (principalCharacterDepth p)) :
    ‖((κ u : Rˣ) : R) - 1‖ ≤ principalCharacterRadius κ :=
  le_ciSup (bddAbove_range_norm_sub_one κ) ⟨u, hu⟩

/-- The principal character radius is the least upper bound of the values `‖κ(u) - 1‖` with
`u ∈ H_depth`. -/
theorem principalCharacterRadius_le_iff {κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ} {C : ℝ} :
    principalCharacterRadius κ ≤ C ↔
      ∀ u ∈ principalUnits K p (principalCharacterDepth p), ‖((κ u : Rˣ) : R) - 1‖ ≤ C := by
  rw [principalCharacterRadius, ciSup_le_iff (bddAbove_range_norm_sub_one κ), Subtype.forall]

/-- The supremum defining the principal character radius is attained: `H_depth` is compact and
`κ` is continuous. -/
theorem exists_norm_sub_one_eq_principalCharacterRadius
    (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) :
    ∃ u ∈ principalUnits K p (principalCharacterDepth p),
      ‖((κ u : Rˣ) : R) - 1‖ = principalCharacterRadius κ := by
  obtain ⟨u, hu, hmax⟩ := exists_isMaxOn_norm_sub_one κ
  exact ⟨u, hu, le_antisymm (norm_sub_one_le_principalCharacterRadius κ hu)
    (principalCharacterRadius_le_iff.mpr fun v hv ↦ hmax hv)⟩

/-- The principal character radius is nonnegative. -/
theorem principalCharacterRadius_nonneg (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) :
    0 ≤ principalCharacterRadius κ :=
  (norm_nonneg _).trans (norm_sub_one_le_principalCharacterRadius κ (one_mem _))

/-- **Bounded coefficient maps.** If `f : R →+* S` satisfies `‖f x‖ ≤ C ‖x‖` and the character
`κ'` with values in `Sˣ` is `f ∘ κ`, then `T(κ') ≤ C T(κ)`. -/
theorem principalCharacterRadius_le_mul_of_norm_le {S : Type*} [SeminormedRing S] (f : R →+* S)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖) {κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ}
    {κ' : (PadicIntegralAlgebra K p)ˣ →ₜ* Sˣ} (hκ' : ∀ u, (κ' u : S) = f (κ u)) :
    principalCharacterRadius κ' ≤ C * principalCharacterRadius κ :=
  principalCharacterRadius_le_iff.mpr fun u hu ↦ by
    rw [hκ', ← map_one f, ← map_sub]
    exact (hf _).trans (mul_le_mul_of_nonneg_left
      (norm_sub_one_le_principalCharacterRadius κ hu) hC)

section Ultrametric

variable [NormOneClass R] [IsUltrametricDist R]

/-- For an ultrametric power-multiplicative norm with `‖1‖ = 1` in which `p` has norm less than
one, a continuous character of `O_pˣ` sends every principal unit `u ∈ H_1` to within distance less
than one of `1`. -/
theorem norm_sub_one_lt_one_of_mem_principalUnits (hR : IsPowMul (‖·‖ : R → ℝ))
    (hpR : ‖(p : R)‖ < 1) (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ)
    {u : (PadicIntegralAlgebra K p)ˣ} (hu : u ∈ principalUnits K p 1) :
    ‖((κ u : Rˣ) : R) - 1‖ < 1 := by
  refine TauCeti.norm_sub_one_lt_one_of_tendsto_pow_prime_pow hR (Fact.out : p.Prime) hpR ?_
  have h := (Units.continuous_val.comp κ.continuous).tendsto 1 |>.comp
    (tendsto_pow_prime_pow_of_mem_principalUnits hu)
  simpa [Function.comp_def] using h

/-- **The strict principal-radius bound.** For an ultrametric power-multiplicative norm with
`‖1‖ = 1` in which `p` has norm less than one, as on a uniform Banach `ℚ_p`-algebra, the principal
character radius of every continuous character of `O_pˣ` is less than one. -/
theorem principalCharacterRadius_lt_one (hR : IsPowMul (‖·‖ : R → ℝ)) (hpR : ‖(p : R)‖ < 1)
    (κ : (PadicIntegralAlgebra K p)ˣ →ₜ* Rˣ) : principalCharacterRadius κ < 1 := by
  obtain ⟨u, hu, hT⟩ := exists_norm_sub_one_eq_principalCharacterRadius κ
  exact hT ▸ norm_sub_one_lt_one_of_mem_principalUnits hR hpR κ
    (principalUnits_antitone K p (one_le_principalCharacterDepth p) hu)

end Ultrametric

end TauCeti.NumberField.PadicIntegralAlgebra
