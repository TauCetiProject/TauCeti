/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois
public import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# The Galois action on roots of uniformizers

Let `K` be an algebraically closed field of characteristic zero and `F = K⸨X⸩`. For a Galois
automorphism `σ` of the Puiseux field over `F`, a uniformizer `π` of `F` and an `n`-th root `α` of
`π` in the Puiseux field, the quotient `θₙ (σ) = σ (α) / α` is an `n`-th root of unity of `K`. This
file proves that it does not depend on the choice of `π` or of `α`: it is always the level-`n`
component of the image of `σ` under `TauCeti.puiseuxField.galEquivTateModule`, which is the root of
unity by which `σ` multiplies `t ^ (1 / n)`. Since those components form a point of the Tate module
`lim_n μₙ(K)`, the characters `θₙ` are compatible in `n`: `θₘ (σ) ^ (m / n) = θₙ (σ)` for `n ∣ m`
(`TauCeti.PrimeToPTateModule.proj_pow_div`).

The proof compares `α` with the reference root `t ^ (1 / n) v`, where `π = t u` with `u` a unit of
`K⟦t⟧` and `v ^ n = u`. Such a `v` exists by Hensel's lemma in `K⟦t⟧`
(`PowerSeries.exists_pow_eq_of_isUnit`). The two roots of `π` differ by an `n`-th root of unity,
which lies in `K` because `K` already contains `n` of them, and so is fixed by `σ`; so is `v`.

## Main results

* `TauCeti.puiseuxField.apply_eq_algebraMap_proj_galEquivTateModule_mul`: for every uniformizer `π`
  of `K⸨X⸩` and every `n`-th root `α` of `π`, `σ (α)` is `α` times the level-`n` component of the
  image of `σ` in the Tate module.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- **The characters `θₙ` are independent of the uniformizer and of the root.** Let `π` be a
uniformizer of `K⸨X⸩`, that is, a Laurent series of order one, and `α` an `n`-th root of `π` in
the Puiseux field. Then a Galois automorphism `σ` multiplies `α` by the level-`n` component of its
image in the Tate module `lim_n μₙ(K)`, which is the root of unity by which `σ` multiplies
`t ^ (1 / n)`. -/
theorem apply_eq_algebraMap_proj_galEquivTateModule_mul (σ : Gal(puiseuxField K/K⸨X⸩))
    (n : ℕ+) {π : K⸨X⸩} (hπ : π.order = 1) {α : puiseuxField K}
    (hα : α ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) π) :
    σ α = algebraMap K (puiseuxField K)
      ((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModule K σ) : Kˣ) : K) * α := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
  -- Write `π = t u` with `u` a unit of `K⟦t⟧`, and choose `v` with `v ^ n = u`.
  obtain ⟨v, hv⟩ := PowerSeries.exists_pow_eq_of_isUnit (n := n)
    (Nat.cast_ne_zero.mpr n.ne_zero) (TauCeti.LaurentSeries.isUnit_powerSeriesPart hπ0)
  have hπtu : π = HahnSeries.single 1 1 * ((v ^ (n : ℕ) : K⟦X⟧) : K⸨X⸩) := by
    rw [hv, ← hπ]
    exact (LaurentSeries.single_order_mul_powerSeriesPart π).symm
  -- The reference root `β = t ^ (1 / n) v` of `π`, on which `σ` acts through `t ^ (1 / n)`.
  set β : puiseuxField K :=
    levelParameter K n * algebraMap K⸨X⸩ (puiseuxField K) (v : K⸨X⸩) with hβ_def
  have hβ : β ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) π := by
    rw [hβ_def, mul_pow, coe_levelParameter_pow, ← map_pow, ← map_mul, hπtu,
      map_pow (HahnSeries.ofPowerSeries ℤ K) v]
  have hσβ : σ β = algebraMap K (puiseuxField K)
      ((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModule K σ) : Kˣ) : K) * β := by
    rw [hβ_def, map_mul, AlgEquiv.commutes, apply_coe_levelParameter, mul_assoc]
  -- `α / β` is an `n`-th root of unity, hence a constant `c`, which `σ` fixes.
  have hπ0' : algebraMap K⸨X⸩ (puiseuxField K) π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K⸨X⸩ (puiseuxField K)).injective).mpr hπ0
  have hβ0 : β ≠ 0 := fun h ↦ hπ0' (by rw [← hβ, h, zero_pow n.ne_zero])
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hω.map_of_injective (algebraMap K (puiseuxField K)).injective)
    |>.eq_pow_of_pow_eq_one (ξ := α / β) (by rw [div_pow, hα, hβ, div_self hπ0'])
  have hαβ : α = algebraMap K (puiseuxField K) (ω ^ i) * β := by
    rw [map_pow, hi, div_mul_cancel₀ _ hβ0]
  rw [hαβ, map_mul, hσβ, IsScalarTower.algebraMap_apply K K⸨X⸩ (puiseuxField K) (ω ^ i),
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  ring

end TauCeti.puiseuxField
