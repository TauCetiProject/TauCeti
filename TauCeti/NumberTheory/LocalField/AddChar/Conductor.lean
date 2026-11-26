/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.Topology.Algebra.AddChar

import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Order.Int.ConditionallyCompleteOrder
import TauCeti.Algebra.Group.AddChar.Basic

/-!
# The conductor exponent of an additive character of a nonarchimedean local field

Let `K` be a nonarchimedean local field, with valuation ring `O` and maximal ideal `P`, and write
`P ^ m = {x | valuation K x ≤ uniformizer K ^ m}` for `m : ℤ`, a fractional ideal of `O`. Let `ψ`
be a nontrivial additive character of `K` which is trivial on a neighbourhood of `0`: for example
a continuous character with values in the unit circle (`AddChar.setOf_eq_one_mem_nhds_zero`, `K`
being a nonarchimedean additive group by `TauCeti.instNonarchimedeanRingOfIsValuativeTopology`).
Then the fractional ideals `P ^ m` on which `ψ` is trivial are exactly those with `m ≥ -ν` for a
unique integer `ν = ν(ψ)`, the *conductor exponent* `AddChar.conductorExponent ψ`: `ψ` is trivial
on `P ^ (-ν)` and nontrivial on `P ^ (-ν - 1)`. Such an exponent exists because the `P ^ m` form a
neighbourhood basis of `0`, and because `ψ` is nontrivial: if `ψ x₀ ≠ 1` then `ψ` is nontrivial on
every `P ^ m` containing `x₀`, that is for all `m ≤ v_K(x₀)`.

The conductor exponent controls the duality of fractional ideals under the pairing
`(x, y) ↦ ψ (x * y)`. For `b ∈ Kˣ` the character `ψ_b = ψ.mulShift b`, `x ↦ ψ (b * x)`, has
conductor exponent `ν(ψ) + v_K(b)`. Consequently the annihilator of `P ^ m` is `P ^ (-ν - m)`,
and likewise for the coordinatewise lattices of `Kⁿ` under the dot product and of matrices under
the trace form `(X, Y) ↦ trace (X * Y)`. These are the dual lattices entering the
self-dual Haar measures and Fourier inversion on these spaces.

## Main definitions

* `AddChar.conductorExponent`: the conductor exponent `ν(ψ)` of an additive character of `K`.

## Main results

* `AddChar.forall_eq_one_iff_neg_conductorExponent_le`: `ψ` is trivial on `P ^ m` exactly when
  `-ν(ψ) ≤ m`.
* `AddChar.conductorExponent_eq_iff`: `ν(ψ) = n` exactly when `ψ` is trivial on `P ^ (-n)` and
  nontrivial on `P ^ (-n - 1)`.
* `AddChar.conductorExponent_mulShift`: `ν(ψ_b) = ν(ψ) + v_K(b)`.
* `AddChar.forall_mul_eq_one_iff_valuation_le`: the annihilator of `P ^ m` under `ψ (x * y)` is
  `P ^ (-ν(ψ) - m)`.
* `AddChar.forall_dotProduct_eq_one_iff_forall_valuation_le` and
  `AddChar.forall_trace_mul_eq_one_iff_forall_valuation_le`: the annihilators of `(P ^ m)ⁿ` under
  the dot product and of `M_{l×n}(P ^ m)` under the trace form are `(P ^ (-ν(ψ) - m))ⁿ` and
  `M_{n×l}(P ^ (-ν(ψ) - m))`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, §1.7.
-/

public section
noncomputable section

open Filter Topology ValuativeRel TauCeti
open scoped Matrix

namespace AddChar

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Monoid

variable {M : Type*} [Monoid M]

variable (ψ : AddChar K M) in
/-- The conductor exponent `ν(ψ)` of an additive character `ψ` of a nonarchimedean local field:
`ψ` is trivial on the fractional ideal `P ^ (-ν(ψ))` and nontrivial on `P ^ (-ν(ψ) - 1)`, where
`P ^ m = {x | valuation K x ≤ uniformizer K ^ m}`. This characterization
(`AddChar.conductorExponent_eq_iff`) holds when `ψ` is nontrivial and trivial on a neighbourhood
of `0`; otherwise the value is meaningless. -/
def conductorExponent : ℤ :=
  -sInf {m : ℤ | ∀ x : K, valuation K x ≤ uniformizer K ^ m → ψ x = 1}

variable {ψ : AddChar K M}

/-- A nontrivial additive character of `K` which is trivial on a neighbourhood of `0` is trivial
on the fractional ideal `P ^ m` exactly when `-ν(ψ) ≤ m`. -/
theorem forall_eq_one_iff_neg_conductorExponent_le (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K))
    (h1 : ψ ≠ 1) (m : ℤ) :
    (∀ x : K, valuation K x ≤ uniformizer K ^ m → ψ x = 1) ↔ -ψ.conductorExponent ≤ m := by
  set S := {m : ℤ | ∀ x : K, valuation K x ≤ uniformizer K ^ m → ψ x = 1}
  -- `S` is nonempty because the `P ^ m` form a neighbourhood basis of `0`.
  have hne : S.Nonempty := by
    obtain ⟨m, -, hm⟩ := (hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).mem_iff.1 h0
    exact ⟨m, fun x hx ↦ hm hx⟩
  -- `S` is bounded below by `v_K(x₀) + 1` for any `x₀` with `ψ x₀ ≠ 1`.
  have hbdd : BddBelow S := by
    obtain ⟨x₀, hx₀⟩ := ne_one_iff.1 h1
    have hx₀0 : x₀ ≠ 0 := by
      rintro rfl
      exact hx₀ (map_zero_eq_one ψ)
    refine ⟨(normalizedValuation K (Units.mk0 x₀ hx₀0)).toAdd + 1, fun m hm ↦ ?_⟩
    by_contra! hlt
    exact hx₀ (hm x₀ ((valuation_le_uniformizer_zpow_iff (Units.mk0 x₀ hx₀0) m).2 (by omega)))
  rw [conductorExponent, neg_neg]
  refine ⟨fun hm ↦ csInf_le hbdd hm, fun hm x hx ↦ Int.csInf_mem hne hbdd x (hx.trans ?_)⟩
  exact zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hm

/-- A nontrivial additive character of `K` which is trivial on a neighbourhood of `0` is trivial
on `P ^ (-ν(ψ))`. -/
theorem eq_one_of_valuation_le (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) {x : K}
    (hx : valuation K x ≤ uniformizer K ^ (-ψ.conductorExponent)) : ψ x = 1 :=
  (forall_eq_one_iff_neg_conductorExponent_le h0 h1 _).2 le_rfl x hx

/-- A nontrivial additive character of `K` which is trivial on a neighbourhood of `0` is
nontrivial on `P ^ (-ν(ψ) - 1)`. -/
theorem exists_valuation_le_ne_one (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) :
    ∃ x : K, valuation K x ≤ uniformizer K ^ (-ψ.conductorExponent - 1) ∧ ψ x ≠ 1 := by
  by_contra! h
  have := (forall_eq_one_iff_neg_conductorExponent_le h0 h1 _).1 h
  omega

/-- The conductor exponent of a nontrivial additive character of `K` which is trivial on a
neighbourhood of `0` is the unique integer `n` such that `ψ` is trivial on `P ^ (-n)` and
nontrivial on `P ^ (-n - 1)`. -/
theorem conductorExponent_eq_iff (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) {n : ℤ} :
    ψ.conductorExponent = n ↔ (∀ x : K, valuation K x ≤ uniformizer K ^ (-n) → ψ x = 1) ∧
      ∃ x : K, valuation K x ≤ uniformizer K ^ (-n - 1) ∧ ψ x ≠ 1 := by
  refine ⟨?_, fun ⟨h, x, hx, hψx⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨fun _ ↦ eq_one_of_valuation_le h0 h1, exists_valuation_le_ne_one h0 h1⟩
  · have hle := (forall_eq_one_iff_neg_conductorExponent_le h0 h1 _).1 h
    have hlt : ¬-ψ.conductorExponent ≤ -n - 1 :=
      fun hle' ↦ hψx ((forall_eq_one_iff_neg_conductorExponent_le h0 h1 _).2 hle' x hx)
    omega

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] {ψ : AddChar K M}

/-- **The conductor exponent of a shifted character.** For `b ∈ Kˣ`, the character
`ψ_b = ψ.mulShift b`, `x ↦ ψ (b * x)`, has conductor exponent `ν(ψ_b) = ν(ψ) + v_K(b)`. -/
theorem conductorExponent_mulShift (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) (b : Kˣ) :
    (ψ.mulShift (b : K)).conductorExponent =
      ψ.conductorExponent + (normalizedValuation K b).toAdd := by
  have h1b : ψ.mulShift (b : K) ≠ 1 := (ψ.mulShift_unit_eq_one_iff b.isUnit).not.2 h1
  -- Compare the two characterizations of triviality on the fractional ideals `P ^ m`.
  have key (m : ℤ) : -(ψ.mulShift (b : K)).conductorExponent ≤ m ↔
      -ψ.conductorExponent ≤ m + (normalizedValuation K b).toAdd := by
    rw [← forall_eq_one_iff_neg_conductorExponent_le
        (setOf_mulShift_eq_one_mem_nhds_zero h0 _) h1b,
      ← forall_eq_one_iff_neg_conductorExponent_le h0 h1]
    refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
    · have := h (b⁻¹ * y) ((valuation_mul_le_uniformizer_zpow_iff b _ m).1 (by simpa using hy))
      simpa using this
    · exact h _ ((valuation_mul_le_uniformizer_zpow_iff b x m).2 hx)
  have h₁ := (key (-(ψ.mulShift (b : K)).conductorExponent)).1 le_rfl
  have h₂ := (key (-ψ.conductorExponent - (normalizedValuation K b).toAdd)).2 (by omega)
  omega

/-- **Duality of fractional ideals.** For a nontrivial additive character `ψ` of `K` which is
trivial on a neighbourhood of `0`, the annihilator of `P ^ m` under the pairing `ψ (x * y)` is
`P ^ (-ν(ψ) - m)`. -/
theorem forall_mul_eq_one_iff_valuation_le (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (m : ℤ) (y : K) :
    (∀ x : K, valuation K x ≤ uniformizer K ^ m → ψ (x * y) = 1) ↔
      valuation K y ≤ uniformizer K ^ (-ψ.conductorExponent - m) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  lift y to Kˣ using isUnit_iff_ne_zero.2 hy
  have hb := forall_eq_one_iff_neg_conductorExponent_le
    (setOf_mulShift_eq_one_mem_nhds_zero h0 (y : K))
    ((ψ.mulShift_unit_eq_one_iff y.isUnit).not.2 h1) m
  rw [conductorExponent_mulShift h0 h1] at hb
  simp only [mulShift_apply, mul_comm (y : K)] at hb
  rw [hb, valuation_le_uniformizer_zpow_iff]
  omega

/-- **Duality of coordinate lattices in `Kⁿ`.** For a nontrivial additive character `ψ` of `K`
which is trivial on a neighbourhood of `0`, the annihilator of `(P ^ m)ⁿ` under the pairing
`ψ (x ⬝ᵥ y)` is `(P ^ (-ν(ψ) - m))ⁿ`. -/
theorem forall_dotProduct_eq_one_iff_forall_valuation_le {ι : Type*} [Fintype ι]
    (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) (m : ℤ) (y : ι → K) :
    (∀ x : ι → K, (∀ i, valuation K (x i) ≤ uniformizer K ^ m) → ψ (x ⬝ᵥ y) = 1) ↔
      ∀ i, valuation K (y i) ≤ uniformizer K ^ (-ψ.conductorExponent - m) := by
  classical
  simp_rw [← forall_mul_eq_one_iff_valuation_le h0 h1]
  refine ⟨fun h i x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · -- Test against the vector with a single nonzero coordinate `x` in position `i`.
    rw [← single_dotProduct]
    refine h _ fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hx
    · simp [hj]
  · rw [dotProduct, map_sum_eq_prod]
    exact Finset.prod_eq_one fun i _ ↦ h i (x i) (hx i)

/-- **Duality of matrix lattices under the trace form.** For a nontrivial additive character `ψ`
of `K` which is trivial on a neighbourhood of `0`, the annihilator of the `l × n` matrices with
entries in `P ^ m` under the pairing `ψ (trace (X * Y))` is the set of `n × l` matrices with
entries in `P ^ (-ν(ψ) - m)`. -/
theorem forall_trace_mul_eq_one_iff_forall_valuation_le {l n : Type*} [Fintype l] [Fintype n]
    (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1) (m : ℤ) (Y : Matrix n l K) :
    (∀ X : Matrix l n K, (∀ i j, valuation K (X i j) ≤ uniformizer K ^ m) → ψ (X * Y).trace = 1) ↔
      ∀ i j, valuation K (Y i j) ≤ uniformizer K ^ (-ψ.conductorExponent - m) := by
  -- `trace (X * Y)` is the dot product of the vectorizations of `Xᵀ` and `Y`.
  have key := forall_dotProduct_eq_one_iff_forall_valuation_le h0 h1 m Y.vec
  rw [Matrix.vec_bijective.surjective.forall,
    (Matrix.transposeAddEquiv l n K).surjective.forall] at key
  simpa [Matrix.vec_dotProduct_vec, Matrix.vec, forall_comm (α := l)] using key

end CommMonoid

end AddChar
