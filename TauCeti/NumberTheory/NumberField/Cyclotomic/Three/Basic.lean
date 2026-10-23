/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# Basic facts about the Eisenstein integers

Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ζ]` for a primitive cube root of unity `ζ`. This file records
elementary facts about `ℤ[ζ]` complementing Mathlib's `Cyclotomic.Three`:

* `TauCeti.finrank_ringOfIntegers_three`: `𝓞 K` has rank `2` over `ℤ`;
* `IsPrimitiveRoot.toInteger_sub_one_sq_dvd_three`: the square of `ζ - 1`, the prime above `3`,
  divides `3`;
* `IsPrimitiveRoot.exists_intCast_add_intCast_mul_toInteger_eq`: every element of `ℤ[ζ]` is
  `a + b ζ` for integers `a` and `b`;
* `IsPrimitiveRoot.intCast_dvd_intCast_add_intCast_mul_toInteger_iff`: an integer divides
  `a + b ζ` exactly when it divides both `a` and `b`;
* `Units.norm_eq_one_of_isCyclotomicExtension_three`: every unit of `ℤ[ζ]` has norm `1`.
-/

public section

open NumberField

namespace TauCeti

/-- The ring of integers of the third cyclotomic field has rank `2` over `ℤ`. -/
theorem finrank_ringOfIntegers_three {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, IsCyclotomicExtension.finrank (n := 3) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)), Nat.totient_prime Nat.prime_three]

end TauCeti

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The square of `ζ - 1` divides `3` in `𝓞 K`. -/
theorem toInteger_sub_one_sq_dvd_three : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) := by
  obtain ⟨z, _, hz⟩ := hζ.toInteger_isPrimitiveRoot.self_sub_one_pow_dvd_order (k := 2) (by decide)
  exact ⟨z, by simpa only [Nat.cast_ofNat, mul_comm] using hz⟩

open TauCeti

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- The integral basis `1, ζ` of `𝓞 K`, indexed by `Fin 2`. -/
private noncomputable def basisThree : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  hζ.integralPowerBasis.basis.reindex (finCongr
    (hζ.integralPowerBasis.finrank.symm.trans finrank_ringOfIntegers_three))

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
@[simp]
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

end IsPrimitiveRoot

namespace Units

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In the third cyclotomic field, the norm of every unit of the ring of integers is `1`. -/
theorem norm_eq_one_of_isCyclotomicExtension_three (u : (𝓞 K)ˣ) :
    Algebra.norm ℤ (u : 𝓞 K) = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hη : Algebra.norm ℤ hζ.toInteger = 1 := by
    have h := congrArg (Algebra.norm ℤ) hζ.toInteger_cube_eq_one
    rw [map_pow, map_one, ← one_pow 3] at h
    exact (Odd.strictMono_pow (by decide : Odd 3)).injective h
  have hneg : Algebra.norm ℤ (-1 : 𝓞 K) = 1 := by
    have h := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (-1)
    rw [map_neg, map_one] at h
    simp [h, finrank_ringOfIntegers_three]
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

end Units
