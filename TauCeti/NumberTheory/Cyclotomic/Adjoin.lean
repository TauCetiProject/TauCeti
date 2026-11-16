/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Adjoining roots of unity as an intermediate field

Adjoining one primitive `m`-th root of unity to `K` inside `M` gives the same intermediate field as
adjoining all the `m`-th roots of unity, and that intermediate field `K(ζ)` is an `m`-th cyclotomic
extension of `K`.

The statements live in the `IntermediateField` lattice, which is where the Galois correspondence
needs them; the cyclotomic one is transported from Mathlib's `Algebra.adjoin` statement
`IsPrimitiveRoot.adjoin_isCyclotomicExtension`. Unlike Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`, nothing is asked of the ambient
extension `M / K`, since a root of unity is integral over `K` on its own.

Over `ℚ`, a polynomial `P ∈ ℤ[X]` evaluated at a primitive `N`-th root of unity `ζ` whose value is
invariant under `ζ ↦ ζ ^ u` for all `u ∈ (ℤ/Nℤ)ˣ` is fixed by `Gal(ℚ(ζ)/ℚ)`, hence lies in `ℚ`,
and by integrality of `ζ` over `ℤ` lies in `ℤ` (`IsPrimitiveRoot.aeval_mem_range_intCast`).

## Main results

* `IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots`: `K(ζ) = K(μ_m)`.
* `IsPrimitiveRoot.isCyclotomicExtension_adjoin_singleton` and
  `IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots`: `K(ζ) = K(μ_m)` is an `m`-th cyclotomic
  extension of `K`.
* `IsPrimitiveRoot.aeval_mem_range_intCast`: cyclotomic Galois descent to `ℤ`.
-/

public section

open IntermediateField
open scoped Polynomial

/-- **Adjoining one primitive `m`-th root adjoins them all.** `K(ζ) = K(μ_m)` inside any
field extension of `K` containing a primitive `m`-th root of unity `ζ`: every `m`-th root of unity
is a power of `ζ`. -/
theorem IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) : adjoin K {ζ} = adjoin K {b : M | b ^ m = 1} :=
  le_antisymm (adjoin_simple_le_iff.mpr <| subset_adjoin K _ hζ.pow_eq_one) <|
    adjoin_le_iff.mpr fun _ hb ↦ by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
      exact pow_mem (mem_adjoin_simple_self K ζ) i

/-- **`K(ζ)` is an `m`-th cyclotomic extension of `K`.** Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` asks the whole ambient extension
`M / K` to be integral; only `ζ` needs to be, and a root of unity always is, being a root of
`X ^ m - 1`. -/
theorem IsPrimitiveRoot.isCyclotomicExtension_adjoin_singleton {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (adjoin K {ζ}) := by
  -- `K(ζ)` and `Algebra.adjoin K {ζ}` have the same carrier because `ζ` is algebraic over `K`.
  change IsCyclotomicExtension {m} K (adjoin K {ζ}).toSubalgebra
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos m)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

/-- **`K(μ_m)` is an `m`-th cyclotomic extension of `K`** inside any extension of `K` containing a
primitive `m`-th root of unity. -/
theorem IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (adjoin K {b : M | b ^ m = 1}) :=
  hζ.adjoin_singleton_eq_adjoin_nth_roots (K := K) ▸ hζ.isCyclotomicExtension_adjoin_singleton

/-- **Cyclotomic Galois descent to `ℤ`.** If `ζ` is a primitive `N`-th root of unity in a
characteristic-zero field `L` and `P ∈ ℤ[X]` satisfies `P(ζ ^ u) = P(ζ)` for every
`u ∈ (ℤ/Nℤ)ˣ`, then `P(ζ)` lies in the image of `ℤ`. -/
theorem IsPrimitiveRoot.aeval_mem_range_intCast {L : Type*} [Field L] [CharZero L]
    {N : ℕ} [NeZero N] {ζ : L} (hζ : IsPrimitiveRoot ζ N) (P : ℤ[X])
    (hP : ∀ u : (ZMod N)ˣ,
      Polynomial.aeval (ζ ^ (u : ZMod N).val) P = Polynomial.aeval ζ P) :
    Polynomial.aeval ζ P ∈ (Int.castRingHom L).range := by
  let K := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have : IsCyclotomicExtension {N} ℚ K := hζ.isCyclotomicExtension_adjoin_singleton
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := K)
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional (S := {N}) (K := ℚ) K
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζK : IsPrimitiveRoot ζK N := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  let x : K := Polynomial.aeval ζK P
  have hx_val : (x : L) = Polynomial.aeval ζ P := by
    simpa [x, ζK] using (Polynomial.aeval_algHom_apply (K.val : K →+* L).toIntAlgHom ζK P).symm
  have hfix : ∀ σ : K ≃ₐ[ℚ] K, σ x = x := fun σ ↦ by
    have hσ : σ x = Polynomial.aeval (σ ζK) P := by
      simpa [x] using (Polynomial.aeval_algHom_apply (σ : K →+* K).toIntAlgHom ζK P).symm
    rw [hσ, ← hζK.autToPow_spec ℚ σ]
    apply Subtype.ext
    set e := (hζK.autToPow ℚ σ : ZMod N).val
    have hpow : ((ζK ^ e : K) : L) = ζ ^ e := SubmonoidClass.coe_pow ζK e
    have hval : ((Polynomial.aeval (ζK ^ e) P : K) : L) = Polynomial.aeval (ζ ^ e) P := by
      rw [← hpow]
      exact (Polynomial.aeval_algHom_apply (K.val : K →+* L).toIntAlgHom (ζK ^ e) P).symm
    rw [hval, hx_val, hP (hζK.autToPow ℚ σ)]
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed x).mpr hfix)
  have hqL : algebraMap ℚ L q = Polynomial.aeval ζ P := by
    rw [IsScalarTower.algebraMap_apply ℚ K L, IntermediateField.algebraMap_apply, hq, hx_val]
  have hintL : IsIntegral ℤ (Polynomial.aeval ζ P) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact IsIntegral.sum _ fun i _ ↦
      (isIntegral_intCast _).mul ((hζ.isIntegral (NeZero.pos N)).pow i)
  have hintQ : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := L)).mp (hqL.symm ▸ hintL)
  let _ : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨m, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
  exact ⟨m, by simpa using hqL⟩
