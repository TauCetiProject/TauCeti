/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.IsGaloisGroup
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Basic
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.FixedField

/-!
# The double coset law for splitting in a non-Galois subfield

Let `M / K` be a finite Galois extension of number fields with group `G`, let `H` be a subgroup of
`G`, and let `E = M ^ H` be its fixed field, an intermediate field that need not be Galois over
`K`.  Fix a prime `p` of `𝓞 K` and a prime `Q` of `𝓞 M` above it, and let `D` be the
decomposition group of `Q`, that is, the stabilizer of `Q` in `G`.  This file proves that the
primes of `𝓞 E` above `p` are in bijection with the double cosets `H \ G / D`, the class of `σ`
corresponding to the contraction `σ Q ∩ 𝓞 E`.

The bijection specializes `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant`,
the invariant-ring construction in
`TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Basic`. It separates into two
ingredients. Two primes of `𝓞 M` have the same contraction to
`𝓞 E` exactly when they lie in one `H`-orbit, because `H` is the Galois group of `M / E` and a
Galois group acts transitively on the primes above a fixed prime; this is
`Ideal.under_fixedField_eq_iff_mem_orbit`, and it is where all the arithmetic sits.  The rest is
the group-theoretic identity that the `H`-orbits inside a transitive `G`-set are indexed by the
`H`-`D` double cosets, which is `TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer`.

Contracting from `𝓞 M` rather than working inside `𝓞 E` directly is what makes all of this
possible: a prime of a non-Galois subfield has no Galois-theoretic description of its own, and the
bijection is the dictionary that supplies one.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOver`: the bijection `H \ G / D ≃ p.primesOver (𝓞 E)`.

## Main results

* `NumberField.isGaloisGroup_ringOfIntegers_fixedField`: `H` is a Galois group of `𝓞 M` over
  `𝓞 E`, so the invariant-ring theory applies to `𝓞 K ⊆ 𝓞 E ⊆ 𝓞 M`.
* `Ideal.doubleCosetQuotientEquivPrimesOver_eq_doubleCosetQuotientEquivPrimesOverOfIsInvariant`:
  the bijection is the invariant-ring double coset law for these rings of integers.

* `Ideal.under_fixedField_eq_iff_mem_orbit`: two primes of `𝓞 M` contract to the same prime of
  `𝓞 E` exactly when one is an `H`-translate of the other.
* `Ideal.primesOver_under_fixedField_eq_singleton_of_le_stabilizer`: for `H ≤ D`, `Q` is the only
  prime of `𝓞 M` above `Q ∩ 𝓞 E`.
* `Ideal.exists_smul_under_fixedField_eq`: every prime of `𝓞 E` above `p` is such a contraction.
* `Ideal.doubleCosetQuotientEquivPrimesOver_mk`: the bijection sends the class of `σ` to
  `σ Q ∩ 𝓞 E`.
* `Ideal.doubleCosetQuotientEquivPrimesOver_smul_mk`: replacing `Q` by `τ Q` sends the class
  of `σ` to the prime indexed through `Q` by the class of `σ τ`.
* `Ideal.card_doubleCosetQuotient_eq_card_primesOver`: the resulting count.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, where the statement is
  recorded on page 55 and its proof is left to the reader.  G. J. Janusz, *Algebraic Number
  Fields*, Chapter I, gives a complete treatment.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace NumberField

/-- **A subgroup is the Galois group of the rings of integers over its fixed field.** This is
Mathlib's ring-of-integers instance applied to `IsGaloisGroup.fixedField`. Instance search does
not find it unaided: the action of `H` on `𝓞 M` restricted from `Gal(M/K)` and the one Mathlib's
instance builds from the action of `H` on `M` agree only after unfolding past instance
transparency. -/
instance isGaloisGroup_ringOfIntegers_fixedField {K M : Type*} [Field K] [Field M] [NumberField K]
    [NumberField M] [Algebra K M] (H : Subgroup (M ≃ₐ[K] M)) :
    IsGaloisGroup H (𝓞 ↥(fixedField H)) (𝓞 M) :=
  instIsGaloisGroupRingOfIntegersOfNumberField ↥(fixedField H) M H

end NumberField

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-- **Same contraction to the fixed field means same `H`-orbit.**  For a subgroup `H` of
`Gal(M/K)` with fixed field `E = M ^ H`, two primes of `𝓞 M` contract to the same prime of `𝓞 E`
exactly when one is an `H`-translate of the other.

This does not require `M / K` to be Galois. -/
theorem under_fixedField_eq_iff_mem_orbit (R R' : Ideal (𝓞 M)) [R.IsPrime] [R'.IsPrime]
    (H : Subgroup (M ≃ₐ[K] M)) :
    R.under (𝓞 ↥(fixedField H)) = R'.under (𝓞 ↥(fixedField H)) ↔ R ∈ MulAction.orbit H R' := by
  -- The extension over the fixed field is Galois without assuming that `M / K` is Galois.
  have : IsGalois ↥(fixedField H) M := IsGalois.of_fixed_field M H
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro h
    -- Use transitivity of `Gal(M/E)` on the primes above the common contraction.
    have : R.LiesOver (R'.under (𝓞 ↥(fixedField H))) := ⟨h.symm⟩
    have : R'.LiesOver (R'.under (𝓞 ↥(fixedField H))) := over_under _
    obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isGaloisGroup (R'.under (𝓞 ↥(fixedField H))) R' R
      (M ≃ₐ[↥(fixedField H)] M)
    exact ⟨(subgroupEquivAlgEquiv H).symm ρ, by
      rw [Subgroup.smul_def, ← H.subgroupEquivAlgEquiv_smul_ideal, MulEquiv.apply_symm_apply, hρ]⟩
  · rintro ⟨h, rfl⟩
    -- An automorphism fixing `E` pointwise does not move contraction to `𝓞 E`.
    rw [Subgroup.smul_def, ← H.subgroupEquivAlgEquiv_smul_ideal h R']
    exact under_smul _ R' _

/-- **A prime is alone above its contraction to a fixed field inside its decomposition group.**
If `H` is contained in the decomposition group of `Q`, then `Q` is the only prime of `𝓞 M` above
`Q ∩ 𝓞 (M ^ H)`: the other primes above it are the `H`-translates of `Q`, which all equal `Q`.

This does not require `M / K` to be Galois. -/
theorem primesOver_under_fixedField_eq_singleton_of_le_stabilizer (Q : Ideal (𝓞 M)) [Q.IsPrime]
    {H : Subgroup (M ≃ₐ[K] M)} (hH : H ≤ stabilizer (M ≃ₐ[K] M) Q) :
    (Q.under (𝓞 ↥(fixedField H))).primesOver (𝓞 M) = {Q} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro R ⟨_, hR⟩
  obtain ⟨h, rfl⟩ := mem_orbit_iff.1 ((under_fixedField_eq_iff_mem_orbit R Q H).1 hR.over.symm)
  exact mem_stabilizer_iff.1 (hH h.2)

/-- **Every prime of the fixed field above `p` is a contraction of a translate of `Q`.**  For
`M / K` Galois and `Q` a prime of `𝓞 M` above `p`, a prime `𝔮` of `𝓞 (M ^ H)` above `p` is
`σ Q ∩ 𝓞 (M ^ H)` for some `σ` in `Gal(M/K)`. -/
theorem exists_smul_under_fixedField_eq [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M))
    [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M))
    (𝔮 : Ideal (𝓞 ↥(fixedField H))) [𝔮.IsPrime] [𝔮.LiesOver p] :
    ∃ σ : M ≃ₐ[K] M, (σ • Q).under (𝓞 ↥(fixedField H)) = 𝔮 := by
  -- Lift `𝔮` to a prime `R` of `𝓞 M`; transitivity then makes `R` a translate of `Q`.
  obtain ⟨⟨R, hRp, hRo⟩⟩ := 𝔮.nonempty_primesOver (S := 𝓞 M)
  have : R.LiesOver p := LiesOver.trans R 𝔮 p
  have : IsGaloisGroup (M ≃ₐ[K] M) K M := IsGaloisGroup.of_isGalois _ M
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup p Q R (M ≃ₐ[K] M)
  exact ⟨σ, by rw [hσ]; exact hRo.over.symm⟩

/-- **The double coset law.**  For `M / K` a finite Galois extension of number fields with group
`G`, a subgroup `H ≤ G` with fixed field `E = M ^ H`, a prime `p` of `𝓞 K` and a prime `Q` of
`𝓞 M` above it with decomposition group `D`, the primes of `𝓞 E` above `p` are indexed by the
double cosets `H \ G / D`.

The class of `σ` corresponds to the contraction `σ Q ∩ 𝓞 E`, by
`Ideal.doubleCosetQuotientEquivPrimesOver_mk`. -/
noncomputable def doubleCosetQuotientEquivPrimesOver [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) :
    DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M)) (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)) ≃
      p.primesOver (𝓞 ↥(fixedField H)) :=
  Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H (𝓞 ↥(fixedField H))

/-- The number-field double coset law is the invariant-ring double coset law for the rings of
integers `𝓞 K ⊆ 𝓞 (M ^ H) ⊆ 𝓞 M`, so the invariant-ring API applies to it directly. -/
theorem doubleCosetQuotientEquivPrimesOver_eq_doubleCosetQuotientEquivPrimesOverOfIsInvariant
    [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
    (H : Subgroup (M ≃ₐ[K] M)) :
    doubleCosetQuotientEquivPrimesOver p Q H =
      Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H (𝓞 ↥(fixedField H)) := by
  rw [doubleCosetQuotientEquivPrimesOver]

/-- The double coset law sends the class of `σ` to the contraction `σ Q ∩ 𝓞 (M ^ H)`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOver_mk [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M))
    [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    (doubleCosetQuotientEquivPrimesOver p Q H (DoubleCoset.mk H _ σ) :
        Ideal (𝓞 ↥(fixedField H)))
      = (σ • Q).under (𝓞 ↥(fixedField H)) := by
  simp only [doubleCosetQuotientEquivPrimesOver,
    doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk]

/-- **The double coset law is compatible with the action of `G`.** Indexing the primes of
`𝓞 (M ^ H)` above `p` through the translate `τ Q` instead of `Q` sends the class of `σ` to the
prime that the indexing through `Q` attaches to the class of `σ τ`. -/
theorem doubleCosetQuotientEquivPrimesOver_smul_mk [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M))
    (τ σ : M ≃ₐ[K] M) :
    doubleCosetQuotientEquivPrimesOver p (τ • Q) H (DoubleCoset.mk H _ σ) =
      doubleCosetQuotientEquivPrimesOver p Q H (DoubleCoset.mk H _ (σ * τ)) :=
  Subtype.ext <| by simp only [doubleCosetQuotientEquivPrimesOver_mk, mul_smul]

/-- **The number of primes above `p` in a subfield is a number of double cosets.** -/
theorem card_doubleCosetQuotient_eq_card_primesOver [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) :
    Nat.card (DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)))
      = Nat.card (p.primesOver (𝓞 ↥(fixedField H))) :=
  Nat.card_congr (doubleCosetQuotientEquivPrimesOver p Q H)

end Ideal
