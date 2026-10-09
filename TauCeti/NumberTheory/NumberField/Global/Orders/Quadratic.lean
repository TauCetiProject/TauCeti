/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.ProperIdeal
import Mathlib.RingTheory.FractionalIdeal.Operations
import TauCeti.Data.Rat.PrimitiveDenominator
import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice

/-!
# Proper ideals of quadratic orders are invertible

In an order `O` of a quadratic number field `K`, a fractional ideal is proper (its multiplier ring
is exactly `O`) if and only if it is invertible. In higher degree only the implication from
invertible to proper survives; the cubic order `ℤ + 2ℤ∛2 + 2ℤ∛4` has a proper noninvertible ideal.
So for quadratic orders the Picard group `Pic O` sees every proper ideal class, which is what
lets the ring class group of a quadratic order be described by proper ideals or, equivalently,
by primitive binary quadratic forms.

The proof is Cox's. Write a nonzero fractional ideal as a lattice `I = ℤα + ℤβ` and put
`τ = β / α`, a root of a primitive integral quadratic `a τ² - b τ - e = 0` (`gcd (a, b, e) = 1`).
Then `a τ` preserves `I`, so it lies in `O` when `I` is proper. With `τ' = b / a - τ` the
conjugate of `τ`, the elements `a / α` and `a τ' / α` carry `I` into `O`, and the products of
`α, β ∈ I` with them are `a`, `b` and `-e` up to integer combinations. Since `a`, `b` and `e`
generate the unit ideal of `ℤ`, the product of `I` with `1 / I = (O : I)` contains `1`, so it is
the unit ideal.

## Main results

In the namespace `TauCeti.GlobalNumberFields.NumberFieldOrder`:

* `IsProperFractionalIdeal.isUnit_of_finrank_eq_two`: a proper fractional ideal of an order in a
  quadratic field is invertible.
* `isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two`: for an order in a quadratic field,
  proper and invertible fractional ideals coincide.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Lemma 7.5.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- A nonzero fractional ideal of an order in a quadratic field is a lattice `ℤα + ℤβ` whose two
generators form a `ℚ`-basis of the field. -/
private theorem exists_eq_lattice_of_finrank_eq_two (hK : Module.finrank ℚ K = 2)
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : I ≠ 0) :
    ∃ α β : K, α ≠ 0 ∧ (∀ y : K, ∃ c d : ℚ, c • α + d • β = y) ∧
      ∀ x : K, x ∈ I ↔ ∃ m n : ℤ, m • α + n • β = x := by
  let b := Module.finBasisOfFinrankEq ℤ I ((finrank_int_eq_finrank_rat hI).trans hK)
  refine ⟨b 0, b 1, fun h ↦ b.ne_zero 0 (Subtype.ext h), fun y ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
      ((span_rat_range_basis hI b).symm ▸ Submodule.mem_top (x := y))
    exact ⟨c 0, c 1, by simpa [Fin.sum_univ_two] using hc⟩
  · rw [← SetLike.mem_coe, ← span_int_range_basis b, SetLike.mem_coe,
      Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c 0, c 1, by simp [Fin.sum_univ_two]⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨![m, n], by simp [Fin.sum_univ_two]⟩

/-- **A proper fractional ideal of a quadratic order is invertible** (Cox, Lemma 7.5). -/
theorem IsProperFractionalIdeal.isUnit_of_finrank_eq_two (hK : Module.finrank ℚ K = 2)
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : O.IsProperFractionalIdeal I) :
    IsUnit I := by
  have hI₀ := hI.ne_zero
  obtain ⟨α, β, hα, hspan, hmem⟩ := exists_eq_lattice_of_finrank_eq_two hK hI₀
  -- `τ = β / α` satisfies `τ² = c + d τ` over `ℚ`; clear denominators primitively.
  obtain ⟨c, d, hcd⟩ := hspan (β ^ 2 / α)
  obtain ⟨a, b, e, hb, he, u, v, w, huvw⟩ := Rat.exists_primitive_common_denominator d c
  have hrel : β ^ 2 = c * α ^ 2 + d * α * β := by
    rw [Rat.smul_def, Rat.smul_def] at hcd
    field_simp at hcd
    linear_combination -hcd
  have hb' : (a : K) * d = b := by exact_mod_cast congrArg (Rat.cast : ℚ → K) hb
  have he' : (a : K) * c = e := by exact_mod_cast congrArg (Rat.cast : ℚ → K) he
  -- Integer multiples stay in a fractional ideal, and elements of `O` lie in the unit ideal.
  have zmul (n : ℤ) {J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {z : K}
      (hz : z ∈ J) : (n : K) * z ∈ J := by
    simpa [Algebra.smul_def] using
      (J : Submodule O.toSubalgebra K).smul_mem (n : O.toSubalgebra) hz
  have addJ {J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {y z : K} (hy : y ∈ J)
      (hz : z ∈ J) : y + z ∈ J :=
    (J : Submodule O.toSubalgebra K).add_mem hy hz
  have mem_one {z : K} (hz : z ∈ O.toSubalgebra) :
      z ∈ (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :=
    (FractionalIdeal.mem_one_iff _).mpr ⟨⟨z, hz⟩, rfl⟩
  have mem_I (m n : ℤ) : (m : K) * α + n * β ∈ I := (hmem _).mpr ⟨m, n, by simp [zsmul_eq_mul]⟩
  have hαI : α ∈ I := by simpa using mem_I 1 0
  have hβI : β ∈ I := by simpa using mem_I 0 1
  have intCast_mem (n : ℤ) : (n : K) ∈ O.toSubalgebra := intCast_mem _ n
  -- The element `a τ` preserves `I`, so it lies in `O` because `I` is proper.
  have hθ : (a : K) * β / α ∈ O.toSubalgebra := by
    refine (O.isProperFractionalIdeal_iff I).mp hI _ fun y hy ↦ ?_
    obtain ⟨m, n, rfl⟩ := (hmem y).mp hy
    convert mem_I (n * e) (m * a + n * b) using 1
    push_cast [zsmul_eq_mul]
    field_simp
    linear_combination (a : K) * n * hrel + n * α ^ 2 * he' + n * α * β * hb'
  -- The elements `a / α` and `a τ' / α = (b - a τ) / α` carry `I` into `O`.
  have hy₁ : (a : K) / α ∈ 1 / I := by
    refine (FractionalIdeal.mem_div_iff_of_ne_zero hI₀).mpr fun y hy ↦ mem_one ?_
    obtain ⟨m, n, rfl⟩ := (hmem y).mp hy
    convert add_mem (intCast_mem (a * m)) (mul_mem (intCast_mem n) hθ) using 1
    push_cast [zsmul_eq_mul]
    field_simp
  have hy₂ : ((b : K) - a * β / α) / α ∈ 1 / I := by
    refine (FractionalIdeal.mem_div_iff_of_ne_zero hI₀).mpr fun y hy ↦ mem_one ?_
    obtain ⟨m, n, rfl⟩ := (hmem y).mp hy
    convert sub_mem (mul_mem (intCast_mem m) (sub_mem (intCast_mem b) hθ)) (intCast_mem (n * e))
      using 1
    push_cast [zsmul_eq_mul]
    field_simp
    linear_combination (-(a : K) * n) * hrel - n * α ^ 2 * he' - n * α * β * hb'
  -- Hence `1 = u a + v b + w e` lies in `I * (O / I)`.
  have h₁ : (1 : K) ∈ I * (1 / I) := by
    have key := addJ (addJ (zmul u (FractionalIdeal.mul_mem_mul hαI hy₁))
      (zmul v (addJ (FractionalIdeal.mul_mem_mul hβI hy₁)
        (FractionalIdeal.mul_mem_mul hαI hy₂))))
      (zmul (-w) (FractionalIdeal.mul_mem_mul hβI hy₂))
    have huvw' : (u : K) * a + v * b + w * e = 1 := by exact_mod_cast huvw
    convert key using 1
    push_cast
    field_simp
    linear_combination (-α ^ 2) * huvw' + (-(w : K) * a) * hrel - w * α * β * hb' - w * α ^ 2 * he'
  exact IsUnit.of_mul_eq_one (1 / I)
    (le_antisymm FractionalIdeal.mul_one_div_le_one (FractionalIdeal.one_le.mpr h₁))

/-- **Proper and invertible fractional ideals coincide in a quadratic order.** In higher degree
only invertible ideals are guaranteed to be proper. -/
theorem isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    O.IsProperFractionalIdeal I ↔ IsUnit I :=
  ⟨fun hI ↦ hI.isUnit_of_finrank_eq_two hK, O.isProperFractionalIdeal_of_isUnit⟩

end NumberFieldOrder

end TauCeti.GlobalNumberFields
