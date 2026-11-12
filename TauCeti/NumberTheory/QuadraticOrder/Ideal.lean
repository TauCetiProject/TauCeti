/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Span
public import TauCeti.NumberTheory.QuadraticOrder.Field
public import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice
import TauCeti.Data.Rat.PrimitiveDenominator
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Rational-axis generators for quadratic-order ideals

A nonzero fractional ideal of a nonsquare quadratic order has two integral generators:
a positive rational element and an element with positive imaginary coordinate. These oriented
generators support normalization of proper fractional ideals to the ideals of primitive binary
quadratic forms. The multiplier criterion below identifies the order of such a two-generator
ideal from a primitive quadratic relation, supplying the order calculation in that normalization.
-/

public section
noncomputable section

open QuadraticAlgebra Module
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.QuadraticOrder

private theorem generators_neg_left (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0))
    (x y : QuadraticAlgebra ℚ (D : ℚ) 0)
    (hgen : ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • x + n • y = z) :
    ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (-x) + n • y = z := by
  intro z
  constructor
  · intro hz
    obtain ⟨m, n, hmn⟩ := (hgen z).mp hz
    exact ⟨-m, n, by simpa using hmn⟩
  · rintro ⟨m, n, hmn⟩
    exact (hgen z).mpr ⟨-m, n, by simpa using hmn⟩

/-- Independent sign changes of the two generators of an ideal, one of which is real and nonzero
and the other of which has nonzero imaginary coordinate, give a positive rational generator and a
generator of positive imaginary coordinate. -/
private theorem exists_pos_rational_axis_generators (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0))
    {α β : QuadraticAlgebra ℚ (D : ℚ) 0} (hα : α ≠ 0) (hαim : α.im = 0) (hβ : β.im ≠ 0)
    (hgen : ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • α + n • β = z) :
    ∃ q : ℚ, ∃ β : QuadraticAlgebra ℚ (D : ℚ) 0, 0 < q ∧ 0 < β.im ∧
      ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z := by
  let q := α.re
  have hαq : α = (q : _) := by
    ext <;> simp [q, hαim]
  have hq : q ≠ 0 := by
    rintro hzero
    exact hα (by simpa [hzero] using hαq)
  have hgenq : ∀ z, z ∈ I ↔ ∃ m n : ℤ,
      m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z :=
    fun z ↦ by simpa only [hαq] using hgen z
  -- Change the two generator signs independently to impose the required orientation.
  obtain ⟨q', β', hq', hβ', hgen'⟩ :
      ∃ q' : ℚ, ∃ β' : QuadraticAlgebra ℚ (D : ℚ) 0, 0 < q' ∧ β'.im ≠ 0 ∧
        ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (q' : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β' = z := by
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · refine ⟨-q, β, neg_pos.mpr hneg, hβ, ?_⟩
      simpa only [Rat.cast_neg] using generators_neg_left D hD I (q : _) β hgenq
    · exact ⟨q, β, hpos, hβ, hgenq⟩
  rcases lt_or_gt_of_ne hβ' with hneg | hpos
  · refine ⟨q', -β', hq', by simpa using neg_pos.mpr hneg, ?_⟩
    have hswap : ∀ z, z ∈ I ↔ ∃ m n : ℤ,
        m • β' + n • (q' : QuadraticAlgebra ℚ (D : ℚ) 0) = z := by
      intro z
      rw [← Submodule.mem_span_pair, Set.pair_comm, Submodule.mem_span_pair]
      exact hgen' z
    intro z
    rw [← Submodule.mem_span_pair, Set.pair_comm, Submodule.mem_span_pair]
    exact generators_neg_left D hD I β' (q' : _) hswap z
  · exact ⟨q', β', hq', hpos, hgen'⟩

/-- A nonzero ideal of the quadratic field order has integral generators consisting of
a positive rational element and an element of positive imaginary coordinate. -/
theorem exists_rational_axis_generators (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0)) (hI : I ≠ 0) :
    ∃ q : ℚ, ∃ β : QuadraticAlgebra ℚ (D : ℚ) 0, 0 < q ∧ 0 < β.im ∧
      ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z := by
  -- Full rank ensures that the two basis elements have a nonzero imaginary coordinate.
  let J : Submodule (QuadraticOrder.numberFieldOrder D hD).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0) := I
  let b := finBasisOfFinrankEq ℤ J
    ((GlobalNumberFields.NumberFieldOrder.finrank_int_eq_finrank_rat hI).trans
      (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0))
  let r₀ := (b 0 : QuadraticAlgebra ℚ (D : ℚ) 0).im
  let r₁ := (b 1 : QuadraticAlgebra ℚ (D : ℚ) 0).im
  have hrat : r₀ ≠ 0 ∨ r₁ ≠ 0 := by
    obtain ⟨i, hi⟩ := QuadraticAlgebra.exists_im_ne_zero_of_span_range_eq_top
      (fun i ↦ (b i : QuadraticAlgebra ℚ (D : ℚ) 0))
      (GlobalNumberFields.NumberFieldOrder.span_rat_range_basis hI b)
    fin_cases i
    exacts [Or.inl hi, Or.inr hi]
  -- A reduced rational ratio gives a primitive integral relation on imaginary coordinates.
  obtain ⟨u, v, huv, hprim⟩ := Rat.exists_isCoprime_intCast_mul_add_intCast_mul_eq_zero r₀ r₁
  -- Extend that primitive relation to a unimodular change of integral generators.
  obtain ⟨γ, hp, hr⟩ := huv.exists_SL2_col 0
  let α : J := u • b 0 + v • b 1
  let β : J := γ 0 1 • b 0 + γ 1 1 • b 1
  obtain ⟨hfirst, hcoordinates⟩ := b.fin_two_basis_generators γ.toGL
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hfirst hcoordinates
  have hα : α ≠ 0 := by
    simpa only [α, hp, hr] using hfirst
  have hαim : (α : QuadraticAlgebra ℚ (D : ℚ) 0).im = 0 := by
    simpa [α, r₀, r₁, zsmul_eq_mul] using hprim
  have hgen (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
      z ∈ I ↔ ∃ m n : ℤ, m • (α : QuadraticAlgebra ℚ (D : ℚ) 0) + n • (β : _) = z := by
    constructor
    · intro hz
      let zI : J := ⟨z, (FractionalIdeal.mem_coe (I := I)).mpr hz⟩
      obtain ⟨m, n, hmn⟩ := hcoordinates zI
      have hvec : m • α + n • β = zI := by
        simpa only [α, β, hp, hr] using hmn
      exact ⟨m, n, by simpa using congrArg Subtype.val hvec⟩
    · rintro ⟨m, n, rfl⟩
      exact (FractionalIdeal.mem_coe (I := I)).mp
        (by simpa [J] using (m • α + n • β).property)
  have hβ : (β : QuadraticAlgebra ℚ (D : ℚ) 0).im ≠ 0 := by
    intro hzero
    have hz_im (z : QuadraticAlgebra ℚ (D : ℚ) 0) (hz : z ∈ I) : z.im = 0 := by
      obtain ⟨m, n, rfl⟩ := (hgen z).mp hz
      simp [zsmul_eq_mul, hαim, hzero]
    rcases hrat with h₀ | h₁
    · exact h₀ (hz_im _ (b 0).property)
    · exact h₁ (hz_im _ (b 1).property)
  exact exists_pos_rational_axis_generators D hD I (fun h ↦ hα (Subtype.ext h)) hαim hβ hgen

/-- For an ideal generated by `q` and `q * τ`, a primitive integral quadratic relation
for `τ` identifies its multipliers with the integral span of `1` and `a * τ`. -/
theorem forall_mul_mem_iff_exists_int_coefficients (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0))
    (q : ℚ) (β τ : QuadraticAlgebra ℚ (D : ℚ) 0)
    (hq : q ≠ 0) (hτim : τ.im ≠ 0)
    (hgen : ∀ z, z ∈ I ↔ ∃ m n : ℤ,
      m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z)
    (hβτ : (q : QuadraticAlgebra ℚ (D : ℚ) 0) * τ = β)
    (a b e : ℤ)
    (hrel : (a : QuadraticAlgebra ℚ (D : ℚ) 0) * (τ * τ) =
      (b : QuadraticAlgebra ℚ (D : ℚ) 0) * τ + (e : QuadraticAlgebra ℚ (D : ℚ) 0))
    (hprim : ∃ u v w : ℤ, u * a + v * b + w * e = 1)
    (x : QuadraticAlgebra ℚ (D : ℚ) 0) :
    (∀ z ∈ I, x * z ∈ I) ↔ ∃ m n : ℤ,
      x = m • (1 : QuadraticAlgebra ℚ (D : ℚ) 0) +
        n • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * τ) := by
  constructor
  · intro hx
    obtain ⟨u, v, w, huvw⟩ := hprim
    have hqK : (q : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by exact_mod_cast hq
    -- Read the integral coordinates of the multiplier on the two lattice generators.
    have hqI : (q : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ I := (hgen _).mpr ⟨1, 0, by simp⟩
    have hβI : β ∈ I := (hgen _).mpr ⟨0, 1, by simp⟩
    obtain ⟨m, n, hm⟩ := (hgen _).mp (hx _ hqI)
    obtain ⟨r, s, hs⟩ := (hgen _).mp (hx _ hβI)
    simp only [zsmul_eq_mul] at hm hs
    rw [← hβτ] at hm hs
    have hx₁ : x = (m : QuadraticAlgebra ℚ (D : ℚ) 0) + (n : QuadraticAlgebra ℚ (D : ℚ) 0) * τ := by
      apply mul_right_cancel₀ hqK
      linear_combination -hm
    have hx₂ : x * τ = (r : QuadraticAlgebra ℚ (D : ℚ) 0) +
        (s : QuadraticAlgebra ℚ (D : ℚ) 0) * τ := by
      apply mul_right_cancel₀ hqK
      linear_combination -hs
    have hmain : ((m * a + n * b - s * a : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0) * τ +
        ((n * e - r * a : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0) = 0 := by
      push_cast
      linear_combination (a : QuadraticAlgebra ℚ (D : ℚ) 0) * hx₂ -
        (a : QuadraticAlgebra ℚ (D : ℚ) 0) * τ * hx₁ -
        (n : QuadraticAlgebra ℚ (D : ℚ) 0) * hrel
    -- Comparing imaginary and rational coordinates gives the two integral relations.
    have him := congrArg QuadraticAlgebra.im hmain
    have h₁ : m * a + n * b - s * a = 0 := by
      apply Int.cast_injective (α := ℚ)
      exact (mul_eq_zero.mp (by simpa using him)).resolve_right hτim
    have hre := congrArg QuadraticAlgebra.re hmain
    have h₂ : n * e - r * a = 0 := by
      apply Int.cast_injective (α := ℚ)
      simpa [h₁] using hre
    have hnb : n * b = (s - m) * a := by linear_combination h₁
    have hne : n * e = r * a := by linear_combination h₂
    -- Primitivity forces the second multiplier coordinate to be divisible by a.
    have hn : n = (u * n + v * (s - m) + w * r) * a := by
      linear_combination -n * huvw + v * hnb + w * hne
    refine ⟨m, u * n + v * (s - m) + w * r, ?_⟩
    rw [hx₁]
    simp only [zsmul_eq_mul, mul_one]
    have hnK : (n : QuadraticAlgebra ℚ (D : ℚ) 0) =
        ((u * n + v * (s - m) + w * r : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0) * a := by
      exact_mod_cast hn
    push_cast at hnK ⊢
    linear_combination τ * hnK
  · rintro ⟨m, n, rfl⟩ z hz
    -- The primitive quadratic relation proves stability for every integral combination.
    obtain ⟨r, s, rfl⟩ := (hgen z).mp hz
    apply (hgen _).mpr
    refine ⟨m * r + n * s * e, m * s + n * r * a + n * s * b, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    rw [← hβτ]
    linear_combination -(n : QuadraticAlgebra ℚ (D : ℚ) 0) *
      (s : QuadraticAlgebra ℚ (D : ℚ) 0) * (q : QuadraticAlgebra ℚ (D : ℚ) 0) * hrel

end TauCeti.QuadraticOrder
