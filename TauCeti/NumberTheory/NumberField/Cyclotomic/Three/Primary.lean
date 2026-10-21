/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

/-!
# Primary elements of the Eisenstein integers

Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ω]` for a primitive cube root of unity `ω`. An element `π` of
`𝓞 K` is *primary* if `π ≡ 2 (mod 3)`. This is the normalisation of the cubic residue symbol used
in the statement of cubic reciprocity: a prime of `ℤ[ω]` not above `3` has exactly one primary
associate, so the cubic symbol can be indexed by primary primes.

The predicate `TauCeti.IsPrimaryEisenstein` is stated in an arbitrary commutative ring, where it
already satisfies the closure property `IsPrimaryEisenstein.neg_mul`. Its content is for `ℤ[ω]`:

* `IsPrimitiveRoot.isPrimaryEisenstein_add_mul_iff`: `a + b ω` is primary if and only if
  `a ≡ 2` and `b ≡ 0` modulo `3`;
* `TauCeti.isPrimaryEisenstein_intCast_iff`: a rational integer is primary exactly when it is
  `2` modulo `3`;
* `IsPrimitiveRoot.existsUnique_isPrimaryEisenstein_unit_mul`: an element not divisible by
  `ω - 1` has exactly one primary multiple by a unit of `ℤ[ω]`;
* `TauCeti.existsUnique_associated_isPrimaryEisenstein`: a prime of `ℤ[ω]` of norm different
  from `3` has exactly one primary associate.

The uniqueness of the primary associate uses Mathlib's special case of Kummer's lemma,
`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §3.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3.
* M. C. Relyea, *On finite fields and higher reciprocity*, Lemmas 3.12 and 3.16.
* Xu, *Reciprocity Laws*, Proposition 4.5.
-/

public section

open NumberField

namespace TauCeti

section CommRing

variable {R : Type*} [CommRing R] {x y w : R}

/-- An element of a commutative ring is *primary* if it is congruent to `2` modulo `3`. In the
Eisenstein integers `ℤ[ω]` this is the normalisation of primes used in cubic reciprocity. Units
such as `-1` are primary, so the predicate is used together with primality. -/
def IsPrimaryEisenstein (x : R) : Prop :=
  (3 : R) ∣ x - 2

/-- Unfolding `IsPrimaryEisenstein` as a divisibility. -/
theorem isPrimaryEisenstein_iff : IsPrimaryEisenstein x ↔ (3 : R) ∣ x - 2 :=
  Iff.rfl

/-- If `x` and `y` are primary, then so is `-(x * y)`. -/
theorem IsPrimaryEisenstein.neg_mul (hx : IsPrimaryEisenstein x) (hy : IsPrimaryEisenstein y) :
    IsPrimaryEisenstein (-(x * y)) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  exact ⟨-(3 * s * t + 2 * s + 2 * t + 2), by linear_combination (-y) * hs - (2 + 3 * s) * ht⟩

/-- If `y` and `w * y` are both primary, then `w ≡ 1 (mod 3)`: a primary element is invertible
modulo `3`, with inverse `2`. -/
theorem IsPrimaryEisenstein.three_dvd_sub_one_of_mul (hy : IsPrimaryEisenstein y)
    (hwy : IsPrimaryEisenstein (w * y)) : (3 : R) ∣ w - 1 := by
  obtain ⟨s, hs⟩ := hy
  obtain ⟨t, ht⟩ := hwy
  exact ⟨2 * t - 2 * s - (w - 1) * (1 + 2 * s), by linear_combination 2 * ht - 2 * w * hs⟩

end CommRing

/-- In the ring of integers of a number field, a rational integer is primary exactly when it is
congruent to `2` modulo `3`. -/
@[simp]
theorem isPrimaryEisenstein_intCast_iff {K : Type*} [Field K] [NumberField K] {a : ℤ} :
    IsPrimaryEisenstein (a : 𝓞 K) ↔ a ≡ 2 [ZMOD 3] := by
  rw [isPrimaryEisenstein_iff, Int.modEq_comm, Int.modEq_iff_dvd]
  refine ⟨fun h ↦ ?_, fun h ↦ by exact_mod_cast Int.cast_dvd_cast _ _ h⟩
  have h' : algebraMap ℤ (𝓞 K) 3 ∣ algebraMap ℤ (𝓞 K) (a - 2) := by simpa using h
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  simpa only [Algebra.norm_algebraMap, Int.pow_dvd_pow_iff hd] using map_dvd (Algebra.norm ℤ) h'

end TauCeti

namespace IsPrimitiveRoot

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ 3)

/-- The integral basis `1, ζ` of `𝓞 K`, indexed by `Fin 2`. -/
private noncomputable def basisThree : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  hζ.integralPowerBasis.basis.reindex (finCongr (by simp [Nat.totient_prime Nat.prime_three]))

private theorem basisThree_apply (i : Fin 2) : basisThree hζ i = hζ.toInteger ^ (i : ℕ) := by
  simp [basisThree, PowerBasis.coe_basis]

private theorem intCast_add_intCast_mul_eq (a b : ℤ) :
    (a : 𝓞 K) + b * hζ.toInteger = a • basisThree hζ 0 + b • basisThree hζ 1 := by
  simp [basisThree_apply]

/-- Every element of `𝓞 K = ℤ[ζ]` is `a + b ζ` for integers `a` and `b`. -/
theorem exists_intCast_add_intCast_mul_toInteger_eq (x : 𝓞 K) :
    ∃ a b : ℤ, (a : 𝓞 K) + b * hζ.toInteger = x := by
  refine ⟨(basisThree hζ).repr x 0, (basisThree hζ).repr x 1, ?_⟩
  rw [intCast_add_intCast_mul_eq]
  conv_rhs => rw [← (basisThree hζ).sum_repr x]
  simp [Fin.sum_univ_two]

/-- An integer `m` divides `a + b ζ` in `𝓞 K = ℤ[ζ]` exactly when it divides both coordinates. -/
theorem intCast_dvd_intCast_add_intCast_mul_toInteger_iff {m a b : ℤ} :
    (m : 𝓞 K) ∣ a + b * hζ.toInteger ↔ m ∣ a ∧ m ∣ b := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨ha, hb⟩ ↦ ?_⟩
  · have hy' : a • basisThree hζ 0 + b • basisThree hζ 1 = m • y := by
      rw [← intCast_add_intCast_mul_eq, hy, zsmul_eq_mul]
    have h0 := congrArg (fun z ↦ (basisThree hζ).repr z 0) hy'
    have h1 := congrArg (fun z ↦ (basisThree hζ).repr z 1) hy'
    simp only [map_add, map_zsmul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul] at h0 h1
    exact ⟨⟨_, by simpa using h0⟩, ⟨_, by simpa using h1⟩⟩
  · exact dvd_add (Int.cast_dvd_cast _ _ ha) (dvd_mul_of_dvd_left (Int.cast_dvd_cast _ _ hb) _)

/-- **The coordinate criterion for primary Eisenstein integers.** For integers `a` and `b`, the
element `a + b ζ` of `𝓞 K = ℤ[ζ]` is primary if and only if `a ≡ 2` and `b ≡ 0` modulo `3`. -/
theorem isPrimaryEisenstein_add_mul_iff {a b : ℤ} :
    IsPrimaryEisenstein ((a : 𝓞 K) + b * hζ.toInteger) ↔ a ≡ 2 [ZMOD 3] ∧ b ≡ 0 [ZMOD 3] := by
  have h : (a : 𝓞 K) + b * hζ.toInteger - 2 = ((a - 2 : ℤ) : 𝓞 K) + b * hζ.toInteger := by
    push_cast; ring
  rw [isPrimaryEisenstein_iff, h, ← Int.cast_ofNat,
    intCast_dvd_intCast_add_intCast_mul_toInteger_iff, Int.modEq_comm, Int.modEq_iff_dvd,
    Int.modEq_zero_iff_dvd]

/-- Every element of `𝓞 K` not divisible by `ζ - 1` has a primary multiple by a unit. The proof is
the six-associate case analysis of Xu, *Reciprocity Laws*, Proposition 4.5. -/
theorem exists_isPrimaryEisenstein_unit_mul {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) :
    ∃ u : (𝓞 K)ˣ, IsPrimaryEisenstein ((u : 𝓞 K) * x) := by
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq x
  set ω := hζ.toInteger
  have hab : ¬ (3 : ℤ) ∣ a + b := by
    rintro ⟨c, hc⟩
    apply hx
    have h3 : ω - 1 ∣ ((3 : ℤ) : 𝓞 K) := by exact_mod_cast hζ.toInteger_sub_one_dvd_prime'
    have hx : (a : 𝓞 K) + b * ω = ((3 : ℤ) : 𝓞 K) * c + b * (ω - 1) := by
      have hc' : (a : 𝓞 K) + b = 3 * c := by exact_mod_cast hc
      push_cast
      linear_combination hc'
    rw [hx]
    exact dvd_add (dvd_mul_of_dvd_left h3 _) (dvd_mul_left _ _)
  let η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : 𝓞 K) = ω := IsCyclotomicExtension.Rat.Three.coe_eta hζ
  have h2 : ω ^ 2 = -ω - 1 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
      IsCyclotomicExtension.Rat.Three.eta_sq hζ
  have h3 : ω ^ 3 = 1 := hζ.toInteger_cube_eq_one
  -- A unit `u` with `u * (a + b ω) = a' + b' ω` and `a' ≡ 2`, `b' ≡ 0` modulo `3` works.
  have key (u : (𝓞 K)ˣ) (a' b' : ℤ) (h : (u : 𝓞 K) * (a + b * ω) = a' + b' * ω)
      (ha' : a' % 3 = 2) (hb' : b' % 3 = 0) :
      ∃ u : (𝓞 K)ˣ, IsPrimaryEisenstein ((u : 𝓞 K) * (a + b * ω)) :=
    ⟨u, by rw [h, hζ.isPrimaryEisenstein_add_mul_iff]; exact ⟨ha', hb'⟩⟩
  have ha3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha3 with ha3 | ha3 | ha3 <;> rcases hb3 with hb3 | hb3 | hb3
  · omega
  · exact key (-η ^ 2) (a - b) a (by push_cast [hη]; linear_combination (-a) * h2 - b * h3)
      (by omega) (by omega)
  · exact key (η ^ 2) (b - a) (-a) (by push_cast [hη]; linear_combination a * h2 + b * h3)
      (by omega) (by omega)
  · exact key (-1) (-a) (-b) (by push_cast; ring) (by omega) (by omega)
  · exact key η (-b) (a - b) (by push_cast [hη]; linear_combination b * h2) (by omega) (by omega)
  · omega
  · exact key 1 a b (by push_cast; ring) (by omega) (by omega)
  · omega
  · exact key (-η) b (b - a) (by push_cast [hη]; linear_combination (-b) * h2)
      (by omega) (by omega)

/-- **Primary associates in `ℤ[ω]`.** Every element of `𝓞 K` not divisible by `ζ - 1` has exactly
one primary multiple by a unit. -/
theorem existsUnique_isPrimaryEisenstein_unit_mul {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) :
    ∃! u : (𝓞 K)ˣ, IsPrimaryEisenstein ((u : 𝓞 K) * x) := by
  obtain ⟨u, hu⟩ := hζ.exists_isPrimaryEisenstein_unit_mul hx
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  set ω := hζ.toInteger
  have hdvd : (3 : 𝓞 K) ∣ ((v * u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 :=
    hu.three_dvd_sub_one_of_mul (by simpa [← mul_assoc] using hv)
  -- `3 = (ω - 1) ^ 2 * (-ω ^ 2)`, so `v * u⁻¹` is congruent to `1` modulo `(ω - 1) ^ 2`.
  have hlam : (ω - 1) ^ 2 ∣ (3 : 𝓞 K) := by
    have h2 : ω ^ 2 = -ω - 1 := by
      simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
        IsCyclotomicExtension.Rat.Three.eta_sq hζ
    refine ⟨-ω ^ 2, ?_⟩
    linear_combination (ω - 2) * hζ.toInteger_cube_eq_one + h2
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ (v * u⁻¹)
      ⟨1, by simpa using hlam.trans hdvd⟩ with h | h
  · exact mul_inv_eq_one.mp h
  · have h0 : IsPrimaryEisenstein ((0 : ℤ) : 𝓞 K) := by
      rw [isPrimaryEisenstein_iff]
      convert hdvd using 1
      rw [h]
      push_cast
      ring
    exact absurd ((isPrimaryEisenstein_intCast_iff (a := 0)).mp h0) (by decide)

end IsPrimitiveRoot

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In the third cyclotomic field, the norm of every unit of the ring of integers is `1`. -/
theorem norm_unit_eq_one_of_isCyclotomicExtension_three (u : (𝓞 K)ˣ) :
    Algebra.norm ℤ (u : 𝓞 K) = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hη : Algebra.norm ℤ hζ.toInteger = 1 := by
    have h := congrArg (Algebra.norm ℤ) hζ.toInteger_cube_eq_one
    rw [map_pow, map_one, ← one_pow 3] at h
    exact (Odd.strictMono_pow (by decide : Odd 3)).injective h
  have hneg : Algebra.norm ℤ (-1 : 𝓞 K) = 1 := by
    have h := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (-1)
    rw [map_neg, map_one] at h
    rw [h, RingOfIntegers.rank, IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)), Nat.totient_prime Nat.prime_three]
    norm_num
  have key (k : ℕ) : Algebra.norm ℤ (hζ.toInteger ^ k) = 1 ∧
      Algebra.norm ℤ (-hζ.toInteger ^ k) = 1 := by
    rw [neg_eq_neg_one_mul, map_mul, map_pow, hneg, hη]
    simp
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simpa using (key 0).2
  · simpa using (key 1).1
  · simpa using (key 1).2
  · simpa using (key 2).1
  · simpa using (key 2).2

/-- **Primary associates of Eisenstein primes.** A prime of `𝓞 K = ℤ[ω]` whose norm is not `3`
has exactly one primary associate. -/
theorem existsUnique_associated_isPrimaryEisenstein {π : 𝓞 K} (hπ : Prime π)
    (hN : Algebra.norm ℤ π ≠ 3) : ∃! ρ : 𝓞 K, Associated π ρ ∧ IsPrimaryEisenstein ρ := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hx : ¬ hζ.toInteger - 1 ∣ π := by
    rintro ⟨c, hc⟩
    have hc' : IsUnit c := (hπ.irreducible.isUnit_or_isUnit hc).resolve_left
      hζ.zeta_sub_one_prime'.not_isUnit
    apply hN
    rw [hc, map_mul, hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide),
      ← hc'.unit_spec, norm_unit_eq_one_of_isCyclotomicExtension_three]
    norm_num
  obtain ⟨u, hu, huniq⟩ := hζ.existsUnique_isPrimaryEisenstein_unit_mul hx
  refine ⟨u * π, ⟨⟨u, mul_comm _ _⟩, hu⟩, ?_⟩
  rintro ρ ⟨⟨v, rfl⟩, hρ⟩
  rw [mul_comm, huniq v (by simpa only [mul_comm π] using hρ)]

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
include hζ

/- `-1 - 3ω`, of norm `7`, is primary, while `3 + ω`, an associate of its conjugate `2 + 3ω`, and
the element `2 + ω` are not; `1 - ω`, the prime above `3`, is not primary. -/
example : IsPrimaryEisenstein (((-1 : ℤ) : 𝓞 K) + (-3 : ℤ) * hζ.toInteger) := by
  rw [hζ.isPrimaryEisenstein_add_mul_iff]; decide

example : ¬ IsPrimaryEisenstein (((3 : ℤ) : 𝓞 K) + (1 : ℤ) * hζ.toInteger) := by
  rw [hζ.isPrimaryEisenstein_add_mul_iff]; decide

example : ¬ IsPrimaryEisenstein (((2 : ℤ) : 𝓞 K) + (1 : ℤ) * hζ.toInteger) := by
  rw [hζ.isPrimaryEisenstein_add_mul_iff]; decide

example : ¬ IsPrimaryEisenstein (((1 : ℤ) : 𝓞 K) + (-1 : ℤ) * hζ.toInteger) := by
  rw [hζ.isPrimaryEisenstein_add_mul_iff]; decide

end Examples

/- The rational integer `2` is primary, while `1` is not. -/
example : IsPrimaryEisenstein ((2 : ℤ) : 𝓞 K) :=
  (isPrimaryEisenstein_intCast_iff (a := 2)).mpr (by decide)

example : ¬ IsPrimaryEisenstein ((1 : ℤ) : 𝓞 K) :=
  fun h ↦ absurd ((isPrimaryEisenstein_intCast_iff (a := 1)).mp h) (by decide)

end TauCeti
