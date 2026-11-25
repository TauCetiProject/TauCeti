/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GL2.CompactWeightModule

/-!
# The discrete series of `GL₂(ℝ)` as explicit `𝔤𝔩₂(ℂ)`-modules

The discrete series `D_k(μ)` of `GL₂(ℝ)`, `k ≥ 2`, and its limit at `k = 1`, restricted to `SO(2)`,
has the weights `ℓ` with `|ℓ| ≥ k` and `ℓ ≡ k mod 2`, each with multiplicity one: two rays,
interchanged by the reflection `A = diag(1, -1)` of `O(2)`. In the compact Cartan basis
`H_c, X_c, Y_c` of `𝔤𝔩₂(ℂ)` (`TauCeti.compactCartanH` and its siblings), a weight vector `v_ℓ` is
normalized by

`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`,

and the identity matrix acts by the central scalar `μ`. This file builds these modules
explicitly, as Lie submodules of the module `TauCeti.CompactWeightModule k μ` on all weights:
`D_k(μ)` is the Lie submodule of the vectors supported on the two rays
(`TauCeti.discreteSeries k μ`): `X_c` leaves the negative ray only from `v_{-k}`, where its
coefficient `(k - k) / 2` vanishes, and `Y_c` leaves the positive ray only from `v_k`. The rays
themselves are Lie submodules `TauCeti.positiveDiscreteSeries k μ` and
`TauCeti.negativeDiscreteSeries k μ`, the lowest and highest weight modules `D_k^±`. The
definitions accept every `k : ℕ`, but only `k ≥ 1` gives a discrete series or its limit: for
`k = 0` the two rays overlap at the weight `0` and the module is the reducible even-weight module.

## Main definitions

* `TauCeti.discreteSeries k μ`: `D_k(μ)`, with the rays `TauCeti.positiveDiscreteSeries k μ` and
  `TauCeti.negativeDiscreteSeries k μ`.

## Main results

* `TauCeti.one_lie_discreteSeries`: the central scalar of `D_k(μ)` is `μ`.
* `TauCeti.gl2Casimir_discreteSeries`: the Casimir operator of `D_k(μ)` is `k (k - 2) / 4`.
* `TauCeti.discreteSeries_eq_sup`: `D_k(μ)` is the sum of its two rays.
* `TauCeti.CompactWeightModule.reflection_mem_negativeDiscreteSeries_iff`: the reflection
  interchanges the two rays.

Explicit checks: `TauCeti.lie_compactCartanY_weightVector_self`,
`TauCeti.lie_compactCartanX_weightVector_self`, `TauCeti.lie_compactCartanY_weightVector_add_two`,
`TauCeti.lie_compactCartanX_weightVector_neg_self`, `TauCeti.gl2Casimir_discreteSeries_two`
and `TauCeti.gl2Casimir_discreteSeries_one`.

## Implementation notes

`𝔤𝔩₂(ℂ)` is `Matrix (Fin 2) (Fin 2) ℂ` with the commutator bracket, through the local instance
`LieRing.ofAssociativeRing`, as elsewhere in Tau Ceti.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
* W. Casselman, *Representations of SL₂(ℝ)*, lecture notes, §§2, 5–6, pp. 9–11, 17–20.
-/

public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {μ : ℂ}

open CompactWeightModule (weightVector weightLieSubmodule toSubmodule_weightLieSubmodule
  weightVector_mem_weightLieSubmodule)

/-! ### The discrete series `D_k(μ)` -/

/-- The weights of `D_k`: `|ℓ| ≥ k` and `ℓ ≡ k mod 2`, the two rays. For `k = 0` this is the set of
all even integers, and the two rays overlap at `0`. -/
def discreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ |ℓ| ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the positive ray `D_k^+`: `ℓ ≥ k` and `ℓ ≡ k mod 2`. -/
def positiveDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ ℓ ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the negative ray `D_k^-`: `ℓ ≤ -k` and `ℓ ≡ k mod 2`. -/
def negativeDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | ℓ ≤ -(k : ℤ) ∧ ℓ % 2 = (k : ℤ) % 2}

/-- Membership in the weights of `D_k`. -/
@[simp]
theorem mem_discreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ discreteSeriesWeights k ↔ (k : ℤ) ≤ |ℓ| ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- Membership in the weights of the positive ray. -/
@[simp]
theorem mem_positiveDiscreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ positiveDiscreteSeriesWeights k ↔ (k : ℤ) ≤ ℓ ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- Membership in the weights of the negative ray. -/
@[simp]
theorem mem_negativeDiscreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ negativeDiscreteSeriesWeights k ↔ ℓ ≤ -(k : ℤ) ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- Negation maps the weights of the negative ray onto those of the positive ray. -/
theorem neg_mem_positiveDiscreteSeriesWeights_iff {k : ℕ} {ℓ : ℤ} :
    -ℓ ∈ positiveDiscreteSeriesWeights k ↔ ℓ ∈ negativeDiscreteSeriesWeights k := by
  simp only [mem_positiveDiscreteSeriesWeights, mem_negativeDiscreteSeriesWeights]
  omega

/-- The weights of `D_k` are those of its two rays. -/
theorem discreteSeriesWeights_eq_union (k : ℕ) :
    discreteSeriesWeights k =
      positiveDiscreteSeriesWeights k ∪ negativeDiscreteSeriesWeights k := by
  ext ℓ
  simp only [mem_discreteSeriesWeights, mem_positiveDiscreteSeriesWeights,
    mem_negativeDiscreteSeriesWeights, Set.mem_union]
  rcases abs_cases ℓ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

private theorem natCast_add_intCast_eq_zero {k : ℕ} {ℓ : ℤ} (h : (k : ℤ) + ℓ = 0) :
    (k : ℂ) + ℓ = 0 :=
  mod_cast h

private theorem natCast_sub_intCast_eq_zero {k : ℕ} {ℓ : ℤ} (h : (k : ℤ) - ℓ = 0) :
    (k : ℂ) - ℓ = 0 :=
  mod_cast h

private theorem positiveDiscreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ positiveDiscreteSeriesWeights k, ℓ + 2 ∉ positiveDiscreteSeriesWeights k →
      (k : ℂ) + ℓ = 0 := fun ℓ hℓ h ↦
  natCast_add_intCast_eq_zero (by rw [mem_positiveDiscreteSeriesWeights] at hℓ h; omega)

private theorem positiveDiscreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ positiveDiscreteSeriesWeights k, ℓ - 2 ∉ positiveDiscreteSeriesWeights k →
      (k : ℂ) - ℓ = 0 := fun ℓ hℓ h ↦
  natCast_sub_intCast_eq_zero (by rw [mem_positiveDiscreteSeriesWeights] at hℓ h; omega)

private theorem negativeDiscreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ negativeDiscreteSeriesWeights k, ℓ + 2 ∉ negativeDiscreteSeriesWeights k →
      (k : ℂ) + ℓ = 0 := fun ℓ hℓ h ↦
  natCast_add_intCast_eq_zero (by rw [mem_negativeDiscreteSeriesWeights] at hℓ h; omega)

private theorem negativeDiscreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ negativeDiscreteSeriesWeights k, ℓ - 2 ∉ negativeDiscreteSeriesWeights k →
      (k : ℂ) - ℓ = 0 := fun ℓ hℓ h ↦
  natCast_sub_intCast_eq_zero (by rw [mem_negativeDiscreteSeriesWeights] at hℓ h; omega)

private theorem discreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ + 2 ∉ discreteSeriesWeights k → (k : ℂ) + ℓ = 0 := by
  simp only [discreteSeriesWeights_eq_union, Set.mem_union, not_or]
  rintro ℓ (hℓ | hℓ) ⟨hP, hN⟩
  exacts [positiveDiscreteSeriesWeights_raise ℓ hℓ hP, negativeDiscreteSeriesWeights_raise ℓ hℓ hN]

private theorem discreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ - 2 ∉ discreteSeriesWeights k → (k : ℂ) - ℓ = 0 := by
  simp only [discreteSeriesWeights_eq_union, Set.mem_union, not_or]
  rintro ℓ (hℓ | hℓ) ⟨hP, hN⟩
  exacts [positiveDiscreteSeriesWeights_lower ℓ hℓ hP, negativeDiscreteSeriesWeights_lower ℓ hℓ hN]

/-- **The discrete series `D_k(μ)`** of `GL₂(ℝ)` (`k ≥ 2`), and its limit at `k = 1`, as an explicit
`𝔤𝔩₂(ℂ)`-module: the finitely supported vectors on the weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2`, with
`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, central
scalar `μ` and Casimir `k (k - 2) / 4`. Only `k ≥ 1` is meant: for `k = 0` this is the module on all
even weights, which is reducible and not a discrete series: `v_0` spans a one-dimensional submodule
killed by `H_c`, `X_c` and `Y_c`, on which the identity matrix acts by `μ`. -/
def discreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (discreteSeriesWeights k) discreteSeriesWeights_raise
    discreteSeriesWeights_lower

/-- The positive ray `D_k^+(μ)`, the lowest weight module of lowest weight `k`, the restriction of
`D_k(μ)` to the identity component of `GL₂(ℝ)` keeping the positive weights. -/
def positiveDiscreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (positiveDiscreteSeriesWeights k)
    positiveDiscreteSeriesWeights_raise positiveDiscreteSeriesWeights_lower

/-- The negative ray `D_k^-(μ)`, the highest weight module of highest weight `-k`. -/
def negativeDiscreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (negativeDiscreteSeriesWeights k)
    negativeDiscreteSeriesWeights_raise negativeDiscreteSeriesWeights_lower

/-- Membership in `D_k(μ)`: the coordinates are supported on the two rays. -/
theorem mem_discreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ discreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (discreteSeriesWeights k) :=
  CompactWeightModule.mem_weightLieSubmodule

/-- Membership in `D_k^+(μ)`: the coordinates are supported on the positive ray. -/
theorem mem_positiveDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ positiveDiscreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (positiveDiscreteSeriesWeights k) :=
  CompactWeightModule.mem_weightLieSubmodule

/-- Membership in `D_k^-(μ)`: the coordinates are supported on the negative ray. -/
theorem mem_negativeDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ negativeDiscreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (negativeDiscreteSeriesWeights k) :=
  CompactWeightModule.mem_weightLieSubmodule

/-- `D_k(μ)` is the sum of its two rays. -/
theorem discreteSeries_eq_sup (k : ℕ) :
    discreteSeries k μ = positiveDiscreteSeries k μ ⊔ negativeDiscreteSeries k μ := by
  refine LieSubmodule.toSubmodule_injective ?_
  simp only [discreteSeries, positiveDiscreteSeries, negativeDiscreteSeries,
    discreteSeriesWeights_eq_union, LieSubmodule.sup_toSubmodule, toSubmodule_weightLieSubmodule]
  simp [Finsupp.supported_union, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]

/-- `v_ℓ ∈ D_k(μ)` for every allowed weight. -/
theorem weightVector_mem_discreteSeries {k : ℕ} {ℓ : ℤ} (hℓ : ℓ ∈ discreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ discreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- `v_ℓ ∈ D_k^+(μ)` for every weight of the positive ray. -/
theorem weightVector_mem_positiveDiscreteSeries {k : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ positiveDiscreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ positiveDiscreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- `v_ℓ ∈ D_k^-(μ)` for every weight of the negative ray. -/
theorem weightVector_mem_negativeDiscreteSeries {k : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ negativeDiscreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ negativeDiscreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- **The Casimir operator of `D_k(μ)` is `k (k - 2) / 4`.** -/
theorem gl2Casimir_discreteSeries (k : ℕ) (v : discreteSeries k μ) :
    gl2Casimir (discreteSeries k μ) v = ((k : ℂ) * (k - 2) / 4) • v :=
  CompactWeightModule.gl2Casimir_lieSubmodule _ v

/-- **The central scalar of `D_k(μ)` is `μ`.** -/
theorem one_lie_discreteSeries (k : ℕ) (v : discreteSeries k μ) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v :=
  CompactWeightModule.one_lie_lieSubmodule _ v

namespace CompactWeightModule

/-! ### The reflection -/

/-- The reflection preserves `D_k(μ)`. -/
theorem reflection_mem_discreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ discreteSeries k μ ↔ v ∈ discreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_discreteSeriesWeights, abs_neg]
    omega

/-- **The reflection interchanges the two rays** `D_k^+(μ)` and `D_k^-(μ)`. -/
theorem reflection_mem_negativeDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ negativeDiscreteSeries k μ ↔ v ∈ positiveDiscreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_negativeDiscreteSeriesWeights, mem_positiveDiscreteSeriesWeights]
    omega

/-- The reflection maps the negative ray onto the positive ray. -/
theorem reflection_mem_positiveDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ positiveDiscreteSeries k μ ↔ v ∈ negativeDiscreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_negativeDiscreteSeriesWeights, mem_positiveDiscreteSeriesWeights]
    omega

end CompactWeightModule

/-! ### Checks -/

/-- At the lowest positive weight, `Y_c v_k = 0`. -/
theorem lie_compactCartanY_weightVector_self (k : ℕ) :
    ⁅compactCartanY, weightVector (k : ℂ) μ k⁆ = 0 := by
  simp

/-- At the lowest positive weight, `X_c v_k = k v_{k + 2}`. -/
theorem lie_compactCartanX_weightVector_self (k : ℕ) :
    ⁅compactCartanX, weightVector (k : ℂ) μ k⁆ = (k : ℂ) • weightVector (k : ℂ) μ (k + 2) := by
  simp only [lie_compactCartanX_weightVector, Int.cast_natCast]
  congr 1
  ring

/-- `Y_c v_{k + 2} = -v_k`: the minus sign that the bracket and the Casimir need. -/
theorem lie_compactCartanY_weightVector_add_two (k : ℕ) :
    ⁅compactCartanY, weightVector (k : ℂ) μ (k + 2)⁆ = -weightVector (k : ℂ) μ k := by
  simp only [lie_compactCartanY_weightVector, add_sub_cancel_right]
  push_cast
  rw [← neg_one_smul ℂ]
  congr 1
  ring

/-- At the highest negative weight, `X_c v_{-k} = 0`. -/
theorem lie_compactCartanX_weightVector_neg_self (k : ℕ) :
    ⁅compactCartanX, weightVector (k : ℂ) μ (-k)⁆ = 0 := by
  simp

/-- `D₂` has Casimir `0`, the infinitesimal character of the trivial representation; the scalar
`(k² - 1) / 4` would give `3 / 4`. -/
theorem gl2Casimir_discreteSeries_two (v : discreteSeries 2 μ) :
    gl2Casimir (discreteSeries 2 μ) v = 0 := by
  rw [gl2Casimir_discreteSeries]
  norm_num

/-- The limit `D₁` has Casimir `-1/4`. -/
theorem gl2Casimir_discreteSeries_one (v : discreteSeries 1 μ) :
    gl2Casimir (discreteSeries 1 μ) v = (-1 / 4 : ℂ) • v := by
  rw [gl2Casimir_discreteSeries]
  norm_num

end TauCeti
