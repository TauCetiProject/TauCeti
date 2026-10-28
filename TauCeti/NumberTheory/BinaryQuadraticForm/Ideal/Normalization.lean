/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Proper
public import TauCeti.NumberTheory.QuadraticOrder.Ideal
import TauCeti.Data.Rat.PrimitiveDenominator
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Normalizing quadratic-order ideals to form ideals

A nonzero fractional ideal of a quadratic order has two integral generators, with the
first rational and the second having positive imaginary coordinate. Properness then
identifies the multiplier order of this lattice with the given quadratic order. This
normalization supplies the inverse direction of the binary form/ideal correspondence.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section
noncomputable section

open QuadraticAlgebra
open scoped nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

private theorem fractionalIdeal_eq_of_generators (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0))
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = D) (q t : ℚ)
    (β : QuadraticAlgebra ℚ (D : ℚ) 0)
    (hgen : ∀ z, z ∈ I ↔ ∃ m n : ℤ,
      m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z)
    (ht_a : (t : QuadraticAlgebra ℚ (D : ℚ) 0) * (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (q : QuadraticAlgebra ℚ (D : ℚ) 0))
    (ht_gen : (t : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D = β) :
    I = FractionalIdeal.spanSingleton
      (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (t : QuadraticAlgebra ℚ (D : ℚ) 0) * f.fractionalIdeal D hf := by
  ext z
  rw [hgen z, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨m, n, hz⟩
    refine ⟨m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D,
      (mem_fractionalIdeal_iff f D hf _).mpr ⟨m, n, rfl⟩, ?_⟩
    rw [← hz]
    simp only [zsmul_eq_mul]
    linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_a -
      (n : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_gen
  · rintro ⟨y, hy, hz⟩
    obtain ⟨m, n, hmn⟩ := (mem_fractionalIdeal_iff f D hf _).mp hy
    refine ⟨m, n, ?_⟩
    rw [hz, ← hmn]
    simp only [zsmul_eq_mul]
    linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_a -
      (n : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_gen

-- Mutual integral coordinates force the positive imaginary coefficient to be one half.
/-- Every proper fractional ideal of the nonsquare quadratic order is a positive rational
multiple of the ideal of a primitive positive-leading form of the given discriminant. -/
theorem exists_pos_primitive_form_fractionalIdeal_eq (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0))
    (hI : (QuadraticOrder.numberFieldOrder D hD).IsProperFractionalIdeal I) :
    ∃ (f : BinaryQuadraticForm ℤ) (hf : f.discrim = D), f.IsPrimitive ∧ 0 < f.a ∧
      ∃ r : ℚ, 0 < r ∧ I = FractionalIdeal.spanSingleton
        (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
        (r : QuadraticAlgebra ℚ (D : ℚ) 0) * f.fractionalIdeal D hf := by
  let O := QuadraticOrder.numberFieldOrder D hD
  -- Normalize the lattice to q times the span of 1 and a positive-imaginary element τ.
  obtain ⟨q, β, hq, hβ, hgen⟩ := QuadraticOrder.exists_rational_axis_generators D hD I hI.ne_zero
  let τ : QuadraticAlgebra ℚ (D : ℚ) 0 := q⁻¹ • β
  have hβτ : (q : QuadraticAlgebra ℚ (D : ℚ) 0) * τ = β := by
    rw [← Rat.smul_def]
    simp only [τ, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  have hτim : 0 < τ.im := by
    simpa only [τ, im_smul, smul_eq_mul] using mul_pos (inv_pos.mpr hq) hβ
  -- Clear the quadratic relation with a positive primitive integral denominator.
  let d := 2 * τ.re
  let c := (D : ℚ) * τ.im ^ 2 - τ.re ^ 2
  have hτrel : τ * τ = (c : QuadraticAlgebra ℚ (D : ℚ) 0) +
      (d : QuadraticAlgebra ℚ (D : ℚ) 0) * τ := by
    ext <;> simp [c, d] <;> ring
  obtain ⟨a, b, e, ha, hb, he, u, v, w, huvw⟩ :=
    Rat.exists_primitive_common_denominator d c
  have hbK : (a : QuadraticAlgebra ℚ (D : ℚ) 0) * (d : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (b : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → (QuadraticAlgebra ℚ (D : ℚ) 0)) hb
  have heK : (a : QuadraticAlgebra ℚ (D : ℚ) 0) * (c : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (e : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → (QuadraticAlgebra ℚ (D : ℚ) 0)) he
  have hrel : (a : QuadraticAlgebra ℚ (D : ℚ) 0) * (τ * τ) =
      (b : QuadraticAlgebra ℚ (D : ℚ) 0) * τ + (e : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    rw [hτrel]
    linear_combination τ * hbK + heK
  let θ : QuadraticAlgebra ℚ (D : ℚ) 0 := (a : QuadraticAlgebra ℚ (D : ℚ) 0) * τ
  -- Properness identifies the computed multiplier lattice with the given quadratic order.
  have hmult (x : QuadraticAlgebra ℚ (D : ℚ) 0) :
      (∀ z ∈ I, x * z ∈ I) ↔
        ∃ m n : ℤ, x = m • (1 : QuadraticAlgebra ℚ (D : ℚ) 0) + n • θ := by
    exact QuadraticOrder.forall_mul_mem_iff_exists_int_coefficients D hD I q β τ hq.ne'
      hτim.ne' hgen hβτ a b e hrel ⟨u, v, w, huvw⟩ x
  have hθ : θ ∈ O.toSubalgebra := by
    apply (O.isProperFractionalIdeal_iff I).mp hI θ
    exact (hmult θ).mpr ⟨0, 1, by simp⟩
  have hgenO : QuadraticOrder.generator D ∈ O.toSubalgebra := by
    dsimp only [O]
    rw [QuadraticOrder.numberFieldOrder_toSubalgebra]
    exact (QuadraticOrder.mem_toSubalgebra_iff D hD (QuadraticOrder.generator D)).mpr
      ⟨0, 1, by simp⟩
  have hgen_stable : ∀ z ∈ I, QuadraticOrder.generator D * z ∈ I := by
    intro z hz
    have h := (I : Submodule O.toSubalgebra (QuadraticAlgebra ℚ (D : ℚ) 0)).smul_mem
      ⟨QuadraticOrder.generator D, hgenO⟩ (FractionalIdeal.mem_coe.mpr hz)
    apply FractionalIdeal.mem_coe.mp
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply] using h
  have hθorder : θ ∈ QuadraticOrder.toSubalgebra D hD := by
    exact (congrArg (fun A ↦ θ ∈ A)
      (QuadraticOrder.numberFieldOrder_toSubalgebra D hD)).mp hθ
  obtain ⟨M, N, hθrep⟩ := (QuadraticOrder.mem_toSubalgebra_iff D hD θ).mp hθorder
  obtain ⟨r, s, hgenrep⟩ :=
    (hmult (QuadraticOrder.generator D)).mp hgen_stable
  -- Compare the integral order generators, with positivity fixing their orientation.
  have hhalf : (a : ℚ) * τ.im = 1 / 2 :=
    QuadraticOrder.mul_im_eq_half_of_mutual_generators D a ha τ hτim
      M N r s hθrep hgenrep
  -- Recover the discriminant and primitive coefficients from the cleared relation.
  dsimp [d] at hb
  dsimp [c] at he
  have hdisc : b ^ 2 + 4 * a * e = D := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linear_combination -((b : ℚ) + 2 * (a : ℚ) * τ.re) * hb - 4 * (a : ℚ) * he
      + 2 * (D : ℚ) * (2 * (a : ℚ) * τ.im + 1) * hhalf
  let f : BinaryQuadraticForm ℤ := ⟨a, -b, -e⟩
  have hf : f.discrim = D := by
    simpa [f, discrim_def, discrim] using hdisc
  have hp : f.IsPrimitive :=
    isPrimitive_of_linearCombination_eq_one f u (-v) (-w)
      (by simpa only [f, neg_mul_neg] using huvw)
  have hθgen : θ = f.idealGenerator D := by
    ext
    · simp [θ, f]
      linear_combination hb / 2
    · simpa [θ] using hhalf
  -- Compare the two integral generators to recover the ideal with positive rational scale.
  let t : ℚ := q / a
  have ht : 0 < t := div_pos hq (by exact_mod_cast ha)
  have haK : (a : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by exact_mod_cast ha.ne'
  have ht_a : (t : QuadraticAlgebra ℚ (D : ℚ) 0) * (a : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (q : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    dsimp [t]
    push_cast
    field_simp [haK]
  have ht_gen : (t : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D = β := by
    rw [← hθgen]
    dsimp [θ]
    rw [← mul_assoc, ht_a, hβτ]
  refine ⟨f, hf, hp, ha, t, ht, ?_⟩
  exact fractionalIdeal_eq_of_generators D hD I f hf q t β hgen ht_a ht_gen

end TauCeti.BinaryQuadraticForm
