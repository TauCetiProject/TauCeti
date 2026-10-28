/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Coordinates in quadratic cyclotomic fields

Let `K` be an `n`-th cyclotomic extension of `ℚ` and `ζ` a primitive `n`-th root of unity, so that
`𝓞 K = ℤ[ζ]` with integral power basis `1, ζ, …, ζ ^ (φ n - 1)`. When `φ n = 2`, that is for
`n ∈ {3, 4, 6}`, this file records the coordinates of `𝓞 K` in the basis `1, ζ`:

* `IsPrimitiveRoot.exists_intCast_add_intCast_mul_toInteger_eq`: if `φ n = 2`, every element of
  `𝓞 K` is `a + b ζ` for integers `a` and `b`;
* `IsPrimitiveRoot.intCast_dvd_intCast_add_intCast_mul_toInteger_iff`: if `2 ≤ φ n`, an integer
  divides `a + b ζ` exactly when it divides both `a` and `b`.
-/

public section

open NumberField

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- If `φ n = 2`, every element of `𝓞 K = ℤ[ζ]` is `a + b ζ` for integers `a` and `b`. -/
theorem exists_intCast_add_intCast_mul_toInteger_eq (hn : n.totient = 2) (x : 𝓞 K) :
    ∃ a b : ℤ, (a : 𝓞 K) + b * hζ.toInteger = x := by
  let B := hζ.integralPowerBasis.basis.reindex
    (finCongr (hζ.integralPowerBasis_dim.trans hn))
  have hB (j : Fin 2) : B j = hζ.toInteger ^ (j : ℕ) := by
    simp [B]
  refine ⟨B.repr x 0, B.repr x 1, ?_⟩
  conv_rhs => rw [← B.sum_repr x]
  simp [Fin.sum_univ_two, hB, zsmul_eq_mul]

/-- If `2 ≤ φ n`, an integer `m` divides `a + b ζ` in `𝓞 K = ℤ[ζ]` exactly when it divides both
coordinates. -/
theorem intCast_dvd_intCast_add_intCast_mul_toInteger_iff (hn : 2 ≤ n.totient) {m a b : ℤ} :
    (m : 𝓞 K) ∣ a + b * hζ.toInteger ↔ m ∣ a ∧ m ∣ b := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨ha, hb⟩ ↦ ?_⟩
  · have hdim : 2 ≤ hζ.integralPowerBasis.dim := hζ.integralPowerBasis_dim ▸ hn
    let B := hζ.integralPowerBasis.basis
    let i₀ : Fin hζ.integralPowerBasis.dim := ⟨0, by omega⟩
    let i₁ : Fin hζ.integralPowerBasis.dim := ⟨1, by omega⟩
    have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have hy' : a • B i₀ + b • B i₁ = m • y := by
      simpa [B, i₀, i₁, zsmul_eq_mul] using hy
    have h0 := congrArg (fun z ↦ B.repr z i₀) hy'
    have h1 := congrArg (fun z ↦ B.repr z i₁) hy'
    simp only [map_add, map_zsmul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, hne, hne.symm,
      ↓reduceIte] at h0 h1
    exact ⟨⟨_, by simpa using h0⟩, ⟨_, by simpa using h1⟩⟩
  · exact dvd_add (Int.cast_dvd_cast _ _ ha) (dvd_mul_of_dvd_left (Int.cast_dvd_cast _ _ hb) _)

end IsPrimitiveRoot
