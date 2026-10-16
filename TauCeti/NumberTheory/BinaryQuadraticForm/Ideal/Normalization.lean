/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Proper
public import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice
import TauCeti.Data.Rat.PrimitiveDenominator
import Mathlib.Tactic.Module
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

open QuadraticAlgebra Module
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

private theorem exists_pos_primitive_common_denominator (x y : ℚ) :
    ∃ a b c : ℤ, 0 < a ∧ (a : ℚ) * x = b ∧ (a : ℚ) * y = c ∧
      ∃ u v w : ℤ, u * a + v * b + w * c = 1 := by
  obtain ⟨a, b, c, hb, hc, u, v, w, huvw⟩ := Rat.exists_primitive_common_denominator x y
  have ha : a ≠ 0 := by
    intro hz
    have hb₀ : b = 0 := by
      apply Int.cast_injective (α := ℚ)
      simpa [hz] using hb.symm
    have hc₀ : c = 0 := by
      apply Int.cast_injective (α := ℚ)
      simpa [hz] using hc.symm
    simp [hz, hb₀, hc₀] at huvw
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine ⟨-a, -b, -c, neg_pos.mpr hneg, ?_, ?_, -u, -v, -w, ?_⟩
    · simpa only [Int.cast_neg, neg_mul] using congrArg Neg.neg hb
    · simpa only [Int.cast_neg, neg_mul] using congrArg Neg.neg hc
    · simpa only [neg_mul_neg] using huvw
  · exact ⟨a, b, c, hpos, hb, hc, u, v, w, huvw⟩

/-- A nonzero ideal of the quadratic field order has integral generators consisting of
a positive rational element and an element of positive imaginary coordinate. -/
theorem exists_rational_axis_generators (D : ℤ) [Fact (¬ IsSquare D)]
    (hD : D % 4 = 0 ∨ D % 4 = 1)
    (I : FractionalIdeal (nonZeroDivisors (QuadraticOrder.numberFieldOrder D hD).toSubalgebra)
      (QuadraticAlgebra ℚ (D : ℚ) 0)) (hI : I ≠ 0) :
    ∃ q : ℚ, ∃ β : QuadraticAlgebra ℚ (D : ℚ) 0, 0 < q ∧ 0 < β.im ∧
      ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (q : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β = z := by
  let J : Submodule (QuadraticOrder.numberFieldOrder D hD).toSubalgebra
      (QuadraticAlgebra ℚ (D : ℚ) 0) := I
  let b := finBasisOfFinrankEq ℤ J
    ((GlobalNumberFields.NumberFieldOrder.finrank_int_eq_finrank_rat hI).trans
      (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0))
  let r₀ := (b 0 : QuadraticAlgebra ℚ (D : ℚ) 0).im
  let r₁ := (b 1 : QuadraticAlgebra ℚ (D : ℚ) 0).im
  have hrat : r₀ ≠ 0 ∨ r₁ ≠ 0 := by
    by_contra! hzero
    have hspan := GlobalNumberFields.NumberFieldOrder.span_rat_range_basis hI b
    have hω : (omega : QuadraticAlgebra ℚ (D : ℚ) 0) ∈
        Submodule.span ℚ (Set.range fun i ↦ (b i : QuadraticAlgebra ℚ (D : ℚ) 0)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hω
    have him := congrArg QuadraticAlgebra.im ht
    simp only [Fin.sum_univ_two, im_add, im_smul, im_omega, smul_eq_mul] at him
    change t 0 * r₀ + t 1 * r₁ = 1 at him
    simp only [hzero.1, hzero.2, mul_zero, zero_add] at him
    norm_num at him
  let x : ℤ := r₁.num * r₀.den
  let y : ℤ := -r₀.num * r₁.den
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    rcases hrat with h₀ | h₁
    · exact Or.inr (mul_ne_zero (neg_ne_zero.mpr (Rat.num_ne_zero.mpr h₀)) (by simp))
    · exact Or.inl (mul_ne_zero (Rat.num_ne_zero.mpr h₁) (by simp))
  have hgcd : 0 < Int.gcd x y := by
    rcases hxy with hx | hy
    · exact Int.gcd_pos_of_ne_zero_left y hx
    · exact Int.gcd_pos_of_ne_zero_right x hy
  obtain ⟨u, v, huv, hx, hy⟩ := Int.exists_gcd_one hgcd
  have hraw : (x : ℚ) * r₀ + (y : ℚ) * r₁ = 0 := by
    dsimp [x, y]
    push_cast
    linear_combination (r₁.num : ℚ) * r₀.mul_den_eq_num - (r₀.num : ℚ) * r₁.mul_den_eq_num
  have hxQ : (x : ℚ) = (u : ℚ) * Int.gcd x y := by exact_mod_cast hx
  have hyQ : (y : ℚ) = (v : ℚ) * Int.gcd x y := by exact_mod_cast hy
  have hprim : (u : ℚ) * r₀ + (v : ℚ) * r₁ = 0 := by
    have hscale : (Int.gcd x y : ℚ) * ((u : ℚ) * r₀ + (v : ℚ) * r₁) = 0 := by
      linear_combination hraw - r₀ * hxQ - r₁ * hyQ
    exact (mul_eq_zero.mp hscale).resolve_left (by exact_mod_cast hgcd.ne')
  obtain ⟨γ, hp, hr⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr huv).exists_SL2_col 0
  have hdet : u * γ 1 1 - γ 0 1 * v = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    simpa only [hp, hr] using h
  let α : J := u • b 0 + v • b 1
  let β : J := γ 0 1 • b 0 + γ 1 1 • b 1
  have hα : α ≠ 0 := by
    intro hz
    have hu := congrArg (fun z : J ↦ b.repr z 0) hz
    have hv := congrArg (fun z : J ↦ b.repr z 1) hz
    have hu₀ : u = 0 := by simpa [α] using hu
    have hv₀ : v = 0 := by simpa [α] using hv
    simp only [hu₀, hv₀, Int.gcd_zero_left, Int.natAbs_zero] at huv
    norm_num at huv
  have hαim : (α : QuadraticAlgebra ℚ (D : ℚ) 0).im = 0 := by
    simpa [α, r₀, r₁, zsmul_eq_mul] using hprim
  have hgen (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
      z ∈ I ↔ ∃ m n : ℤ, m • (α : QuadraticAlgebra ℚ (D : ℚ) 0) + n • (β : _) = z := by
    constructor
    · intro hz
      let zI : J := ⟨z, hz⟩
      let p := b.repr zI 0
      let q := b.repr zI 1
      let m := γ 1 1 * p - γ 0 1 * q
      let n := -v * p + u * q
      have hm : m * u + n * γ 0 1 = p := by
        dsimp [m, n]
        linear_combination p * hdet
      have hn : m * v + n * γ 1 1 = q := by
        dsimp [m, n]
        linear_combination q * hdet
      have hvec : m • α + n • β = zI := by
        calc
          m • α + n • β = (m * u + n * γ 0 1) • b 0 +
              (m * v + n * γ 1 1) • b 1 := by dsimp [α, β]; module
          _ = zI := by
            rw [hm, hn]
            exact (by simpa only [Fin.sum_univ_two] using b.sum_repr zI)
      exact ⟨m, n, by simpa using congrArg Subtype.val hvec⟩
    · rintro ⟨m, n, rfl⟩
      apply FractionalIdeal.mem_coe.mp
      change m • (α : QuadraticAlgebra ℚ (D : ℚ) 0) + n • (β : _) ∈ J
      simpa using (m • α + n • β).property
  have hβ : (β : QuadraticAlgebra ℚ (D : ℚ) 0).im ≠ 0 := by
    intro hzero
    have hz_im (z : QuadraticAlgebra ℚ (D : ℚ) 0) (hz : z ∈ I) : z.im = 0 := by
      obtain ⟨m, n, rfl⟩ := (hgen z).mp hz
      simp [zsmul_eq_mul, hαim, hzero]
    rcases hrat with h₀ | h₁
    · exact h₀ (hz_im _ (b 0).property)
    · exact h₁ (hz_im _ (b 1).property)
  let q := (α : QuadraticAlgebra ℚ (D : ℚ) 0).re
  have hαq : (α : QuadraticAlgebra ℚ (D : ℚ) 0) = (q : _) := by
    ext <;> simp [q, hαim]
  have hq : q ≠ 0 := by
    intro hzero
    apply hα
    apply Subtype.ext
    simpa [hzero] using hαq
  obtain ⟨q', β', hq', hβ', hgen'⟩ :
      ∃ q' : ℚ, ∃ β' : QuadraticAlgebra ℚ (D : ℚ) 0, 0 < q' ∧ β'.im ≠ 0 ∧
        ∀ z, z ∈ I ↔ ∃ m n : ℤ, m • (q' : QuadraticAlgebra ℚ (D : ℚ) 0) + n • β' = z := by
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · refine ⟨-q, β, neg_pos.mpr hneg, hβ, ?_⟩
      intro z
      rw [hgen z, hαq]
      constructor <;> rintro ⟨m, n, hn⟩ <;> refine ⟨-m, n, ?_⟩ <;>
        simpa only [Rat.cast_neg, neg_smul, smul_neg, neg_neg] using hn
    · exact ⟨q, β, hpos, hβ, fun z ↦ by simpa only [hαq] using hgen z⟩
  rcases lt_or_gt_of_ne hβ' with hneg | hpos
  · refine ⟨q', -β', hq', by simpa using neg_pos.mpr hneg, ?_⟩
    intro z
    rw [hgen' z]
    constructor <;> rintro ⟨m, n, hn⟩ <;> refine ⟨m, -n, ?_⟩ <;>
      simpa only [neg_smul, smul_neg, neg_neg] using hn
  · exact ⟨q', β', hq', hpos, hgen'⟩

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
  obtain ⟨q, β, hq, hβ, hgen⟩ := exists_rational_axis_generators D hD I hI.ne_zero
  let τ : QuadraticAlgebra ℚ (D : ℚ) 0 := q⁻¹ • β
  have hqK : (q : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by exact_mod_cast hq.ne'
  have hβτ : (q : QuadraticAlgebra ℚ (D : ℚ) 0) * τ = β := by
    rw [← Rat.smul_def]
    simp only [τ, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  have hτim : 0 < τ.im := by
    simpa only [τ, im_smul, smul_eq_mul] using mul_pos (inv_pos.mpr hq) hβ
  let d := 2 * τ.re
  let c := (D : ℚ) * τ.im ^ 2 - τ.re ^ 2
  have hτrel : τ * τ = (c : QuadraticAlgebra ℚ (D : ℚ) 0) +
      (d : QuadraticAlgebra ℚ (D : ℚ) 0) * τ := by
    ext <;> simp [c, d] <;> ring
  obtain ⟨a, b, e, ha, hb, he, u, v, w, huvw⟩ := exists_pos_primitive_common_denominator d c
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
  have hθ : θ ∈ O.toSubalgebra := by
    apply (O.isProperFractionalIdeal_iff I).mp hI θ
    intro z hz
    obtain ⟨m, n, rfl⟩ := (hgen z).mp hz
    apply (hgen _).mpr
    refine ⟨n * e, m * a + n * b, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    rw [← hβτ]
    dsimp [θ]
    linear_combination -(n : QuadraticAlgebra ℚ (D : ℚ) 0) *
      (q : QuadraticAlgebra ℚ (D : ℚ) 0) * hrel
  have hmult (x : QuadraticAlgebra ℚ (D : ℚ) 0) (hx : ∀ z ∈ I, x * z ∈ I) :
      ∃ m n : ℤ, x = m • (1 : QuadraticAlgebra ℚ (D : ℚ) 0) + n • θ := by
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
    have him := congrArg QuadraticAlgebra.im hmain
    have h₁ : m * a + n * b - s * a = 0 := by
      apply Int.cast_injective (α := ℚ)
      exact (mul_eq_zero.mp (by simpa using him)).resolve_right hτim.ne'
    have hre := congrArg QuadraticAlgebra.re hmain
    have h₂ : n * e - r * a = 0 := by
      apply Int.cast_injective (α := ℚ)
      simpa [h₁] using hre
    have hnb : n * b = (s - m) * a := by linear_combination h₁
    have hne : n * e = r * a := by linear_combination h₂
    have hn : n = (u * n + v * (s - m) + w * r) * a := by
      linear_combination -n * huvw + v * hnb + w * hne
    refine ⟨m, u * n + v * (s - m) + w * r, ?_⟩
    rw [hx₁]
    simp only [zsmul_eq_mul, mul_one, θ]
    have hnK : (n : QuadraticAlgebra ℚ (D : ℚ) 0) =
        ((u * n + v * (s - m) + w * r : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0) * a := by
      exact_mod_cast hn
    push_cast at hnK ⊢
    linear_combination τ * hnK
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
  obtain ⟨r, s, hgenrep⟩ := hmult (QuadraticOrder.generator D) hgen_stable
  have hθim : (a : ℚ) * τ.im = (N : ℚ) / 2 := by
    have h := congrArg QuadraticAlgebra.im hθrep
    simpa [θ, zsmul_eq_mul, div_eq_mul_inv] using h
  have hgenim : 1 / 2 = (s : ℚ) * ((a : ℚ) * τ.im) := by
    have h := congrArg QuadraticAlgebra.im hgenrep
    simpa [θ, zsmul_eq_mul] using h
  have hsN : s * N = 1 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linear_combination -2 * hgenim - 2 * (s : ℚ) * hθim
  have hN : N = 1 := by
    have hNpos : 0 < N := by
      have hpos : 0 < (N : ℚ) := by
        have h : (N : ℚ) = 2 * (a : ℚ) * τ.im := by linear_combination -2 * hθim
        rw [h]
        exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast ha)) hτim
      exact_mod_cast hpos
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using hsN) with h | h
    · exact h
    · omega
  have hhalf : (a : ℚ) * τ.im = 1 / 2 := by simpa only [hN, Int.cast_one] using hθim
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
  have hp : f.IsPrimitive := by
    rw [isPrimitive_iff]
    apply Nat.dvd_one.mp
    have hdiv := ((f.content_dvd_a).mul_left u).add
      (((f.content_dvd_b).mul_left (-v)).add ((f.content_dvd_c).mul_left (-w)))
    have hbez : u * f.a + ((-v) * f.b + (-w) * f.c) = 1 := by
      simpa only [f, neg_mul_neg, add_assoc] using huvw
    rw [hbez] at hdiv
    exact_mod_cast hdiv
  have hθgen : θ = f.idealGenerator D := by
    ext
    · simp [θ, f]
      linear_combination hb / 2
    · simpa [θ] using hhalf
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
  ext z
  rw [hgen z, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨m, n, hz⟩
    refine ⟨m • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + n • f.idealGenerator D,
      (mem_fractionalIdeal_iff f D hf _).mpr ⟨m, n, rfl⟩, ?_⟩
    rw [← hz]
    simp only [zsmul_eq_mul, f]
    linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_a -
      (n : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_gen
  · rintro ⟨y, hy, hz⟩
    obtain ⟨m, n, hmn⟩ := (mem_fractionalIdeal_iff f D hf _).mp hy
    refine ⟨m, n, ?_⟩
    rw [hz, ← hmn]
    simp only [zsmul_eq_mul, f]
    linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_a -
      (n : QuadraticAlgebra ℚ (D : ℚ) 0) * ht_gen

end TauCeti.BinaryQuadraticForm
