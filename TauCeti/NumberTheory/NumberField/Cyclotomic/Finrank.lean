/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.Data.Nat.Factorization.PowDvd
import TauCeti.Data.Nat.Totient
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# The degree of a cyclotomic extension of a number field

Mathlib computes the degree of an `m`-th cyclotomic extension either over `ℚ`
(`IsCyclotomicExtension.Rat.finrank`) or over a base for which the `m`-th cyclotomic polynomial
is already known to be irreducible (`IsCyclotomicExtension.finrank`). Neither is directly usable
over a general number field `K`, where irreducibility of `Φ_m` over `K` is exactly what has to be
established.

This file supplies the arithmetic criterion: if `m` is coprime to the discriminant of `K`, then

`[M : K] = φ m`   for `M / K` an `m`-th cyclotomic extension with `K` a number field.

The mechanism is linear disjointness rather than a direct irreducibility argument. Inside `M`,
the two subfields `ℚ(ζ)` and (the image of) `K` have coprime discriminants, so Mathlib's
`NumberField.linearDisjoint_of_isGalois_isCoprime_discr` makes them linearly disjoint; their
compositum is `M`, so the degree of `M` over `K` equals the degree of `ℚ(ζ)` over `ℚ`, which is
`φ m`. Coprimality of the discriminants is where the hypothesis is spent, via the divisibility
input below.

## Main results

* `IsCyclotomicExtension.Rat.finrank_ringOfIntegers`: the ring of integers `𝓞 K` of an `n`-th
  cyclotomic extension `K / ℚ` (`n ≠ 0`) has `ℤ`-rank `φ n`.
* `IsCyclotomicExtension.Rat.prime_dvd_of_dvd_natAbs_discr`: a prime dividing the discriminant
  of an `m`-th cyclotomic field divides `m`. This is the divisibility input that turns
  coprimality to `m` into coprimality of discriminants.
* `IsCyclotomicExtension.finrank_eq_totient`: the degree identity `[M : K] = φ m`.
* `IsPrimitiveRoot.finrank_adjoin_eq_totient`: the base case `[ℚ(ζ) : ℚ] = φ m` for a primitive
  `m`-th root of unity `ζ` in an arbitrary field of characteristic zero.
* `IsPrimitiveRoot.totient_dvd_finrank_mul_finrank_adjoin`: over a field `K` of characteristic zero
  with `[K : ℚ]` finite, `φ(N) ∣ [K : ℚ] · [K(ζ) : K]` for a primitive `N`-th root of unity `ζ`.
* `IsPrimitiveRoot.pow_dvd_finrank_adjoin`: over such a `K`, `ℓ^n ∣ [K(ζ) : K]` for a primitive
  `ℓ^(n + [K : ℚ] + 1)`-th root of unity `ζ`, so these degrees have unbounded `ℓ`-adic valuation.

## Implementation notes

The hypothesis is `((NumberField.discr K).natAbs).Coprime m`, a statement about the *base*
field. It is the condition an arithmetic caller can actually arrange — e.g. by choosing `m` to
be a prime unramified in `K` — whereas the resulting intersection or irreducibility conditions
would have to be re-derived from it at each use.

Only the base `K` carries a `NumberField` hypothesis. `M` is finite over `K` by
`IsCyclotomicExtension.finiteDimensional`, hence a number field on its own, so demanding
`[NumberField M]` of the caller would be an avoidable hypothesis. The degree itself comes from
linear disjointness of `ℚ(ζ)` and the image of `K` inside `M`, whose compositum is `M`.

Adapted from the Birkbeck–Brasca Chebotarev density project.
-/

public section

open scoped NumberField

namespace IsCyclotomicExtension

namespace Rat

/-- **The `ℤ`-rank of the ring of integers of a cyclotomic field.** For an `n`-th cyclotomic
extension `K / ℚ` with `n ≠ 0`, the ring of integers `𝓞 K` has rank `φ n` over `ℤ`. -/
theorem finrank_ringOfIntegers (n : ℕ) (K : Type*) [Field K] [CharZero K] [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] :
    Module.finrank ℤ (𝓞 K) = n.totient := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [NumberField.RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank n K]

/-- A prime dividing the discriminant of an `m`-th cyclotomic extension of `ℚ` divides `m`. -/
theorem prime_dvd_of_dvd_natAbs_discr (E : Type*) [Field E] [NumberField E] (m : ℕ)
    [IsCyclotomicExtension {m} ℚ E] {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero p
  have : NeZero m := ⟨hm⟩
  refine hp.dvd_of_dvd_pow (n := m.totient) (hpd.trans ?_)
  obtain ⟨c, hc⟩ := Nat.prod_primeFactors_pow_totient_ediv_dvd m
  rw [IsCyclotomicExtension.Rat.natAbs_discr (K := E) (n := m), hc,
    Nat.mul_div_cancel_left _ (Finset.prod_pos fun q hq ↦
      pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)]
  exact dvd_mul_left _ _

/-- The discriminant of an `m`-th cyclotomic field is coprime to every integer coprime to `m`. -/
theorem isCoprime_discr_of_coprime_level (E : Type*) [Field E] [NumberField E] {m : ℕ}
    [IsCyclotomicExtension {m} ℚ E] {D : ℤ} (h : m.Coprime D.natAbs) :
    IsCoprime (NumberField.discr E) D := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hn
  obtain ⟨p, hp, hpd, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  exact hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd
    (prime_dvd_of_dvd_natAbs_discr E m hp hpd) hpD)

end Rat

/-- **The cyclotomic degree over a number field base.** If `M / K` is an `m`-th cyclotomic
extension with `K` a number field and `m` coprime to `discr K`, then `[M : K] = φ m`.

Coprimality to `discr K` stands in for irreducibility of `Φ_m` over `K`, and is the hypothesis
an arithmetic caller can arrange directly. Only the base `K` need be a number field. -/
theorem finrank_eq_totient (K M : Type*) [Field K] [NumberField K] [Field M]
    [Algebra K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  -- `M` is a number field rather than assumed one: a cyclotomic extension of a number field is
  -- finite over it, and a finite extension of a number field is again a number field.
  have : FiniteDimensional K M := IsCyclotomicExtension.finiteDimensional (S := {m}) (K := K) M
  have : NumberField M := NumberField.of_module_finite (K := K) (L := M)
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ}
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange
  have : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hsup : K₁ ⊔ K₂ = ⊤ :=
    TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top ℚ K M
      (IntermediateField.adjoin_eq_top_of_algebra _ _
        (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ))
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂]
    exact Rat.isCoprime_discr_of_coprime_level K₁ hcop.symm
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ := hld.finrank_right_eq_finrank hsup
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    -- `eK₂` is the embedding `K → M` with its range restricted, so coercing back to `M` returns
    -- that embedding: `RingHom.rangeRestrictFieldEquiv_apply_coe`.
    exact RingHom.rangeRestrictFieldEquiv_apply_coe _ x
  rw [hrelabel, hfr, hfinK₁]

end IsCyclotomicExtension

/-- **The degree of the field generated by a primitive root of unity.** If `ζ` is a primitive `m`-th
root of unity in a field of characteristic zero, then `[ℚ(ζ) : ℚ] = φ m`.

Mathlib's `IsCyclotomicExtension.Rat.finrank` computes this degree for a field that already carries
an `IsCyclotomicExtension {m} ℚ` instance; the ambient field here is arbitrary, and the instance for
`ℚ(ζ)` is supplied by `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`. -/
theorem IsPrimitiveRoot.finrank_adjoin_eq_totient {Ω : Type*} [Field Ω] [CharZero Ω] {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {ζ}) = m.totient := by
  have : IsCyclotomicExtension {m} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  exact IsCyclotomicExtension.Rat.finrank m _

/-- **Degrees of cyclotomic extensions.** If `ζ` is a primitive `N`-th root of unity in an
extension `E` of a field `K` of characteristic zero with `[K : ℚ]` finite, then
`φ(N) ∣ [K : ℚ] · [K(ζ) : K]`, since `[ℚ(ζ) : ℚ] = φ(N)`. -/
theorem IsPrimitiveRoot.totient_dvd_finrank_mul_finrank_adjoin {K E : Type*} [Field K]
    [CharZero K] [FiniteDimensional ℚ K] [Field E] [Algebra K E] {ζ : E} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) :
    N.totient ∣ Module.finrank ℚ K * Module.finrank K (IntermediateField.adjoin K {ζ}) := by
  have hint : IsIntegral K ζ := hζ.isIntegral hN |>.tower_top
  have := IntermediateField.adjoin.finiteDimensional hint
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let ζ' : IntermediateField.adjoin K {ζ} := IntermediateField.AdjoinSimple.gen K ζ
  have hζ' : IsPrimitiveRoot ζ' N :=
    hζ.of_map_of_injective (f := (IntermediateField.adjoin K {ζ}).val) Subtype.val_injective
  rw [Module.finrank_mul_finrank ℚ K (IntermediateField.adjoin K {ζ}),
    ← Polynomial.natDegree_cyclotomic N ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ' hN]
  exact minpoly.degree_dvd (hζ'.isIntegral hN).tower_top

/-- **Cyclotomic degrees have unbounded `ℓ`-adic valuation.** If `ζ` is a primitive
`ℓ^(n + [K : ℚ] + 1)`-th root of unity over a field `K` of characteristic zero with `[K : ℚ]`
finite, then `ℓ^n ∣ [K(ζ) : K]`. -/
theorem IsPrimitiveRoot.pow_dvd_finrank_adjoin {K E : Type*} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] [Field E] [Algebra K E] {ζ : E} {ℓ n : ℕ}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (n + Module.finrank ℚ K + 1))) (hℓ : ℓ ≠ 0) :
    ℓ ^ n ∣ Module.finrank K (IntermediateField.adjoin K {ζ}) := by
  have h := hζ.totient_dvd_finrank_mul_finrank_adjoin (K := K) (pow_pos (Nat.pos_of_ne_zero hℓ) _)
  exact Nat.pow_dvd_of_pow_add_dvd_mul Module.finrank_pos.ne'
    ((TauCeti.Nat.pow_dvd_totient_pow_succ ℓ _).trans h)
