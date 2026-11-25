/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Charpoly
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.FieldOfValues
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.PowerTwist
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension.Basic

/-!
# Galois conjugates and values of the canonical extension

Let a finite group `S` act on a finite group `Γ` through `φ`, and let `ψ` be a canonical extension
(`TauCeti.IsCanonicalExtension`) of an irreducible character `χ` of `Γ` to `Γ ⋊[φ] S`, over an
algebraically closed field of characteristic zero.

For `j` coprime to `|Γ ⋊ S|`, the canonical extension of `χ^{(j)} : g ↦ χ(g ^ j)` is
`ψ^{(j)} : x ↦ ψ(x ^ j)` (`TauCeti.IsCanonicalExtension.apply_pow`): `ψ^{(j)}` is irreducible,
extends `χ^{(j)}`, and every representation affording it has determinant `(det ρ(x)) ^ j` at `x`
for a representation `ρ` affording `ψ` (`Representation.det_eq_det_pow_of_character_eq`), so it
is still trivial on `S`.

When `|Γ|` and `|S|` are coprime, this gives the values of `ψ` (Glauberman 1968, Theorem 2 (b),
p. 1470). An automorphism of a cyclotomic field fixing the values of `χ` acts on characters
through a power map `j` fixing `χ`, so by uniqueness of the canonical extension it fixes `ψ`. Hence
`ℚ(ψ) = ℚ(χ)` (`TauCeti.IsCanonicalExtension.adjoin_range_eq`), the fields being read through
`IsPrimitiveRoot.adjoin_range_eq_map_fixedField_cyclotomicPowerStabilizer`. On `S` every power map
fixes `ψ`: by the Chinese remainder theorem a power `j` coprime to `|Γ ⋊ S|` agrees on `S` with a
power `j'` that is `1` modulo `|Γ|`, and `j'` fixes `χ`. So `ψ(s)` is a rational algebraic integer,
an integer (`TauCeti.IsCanonicalExtension.exists_int_eq_apply_inr`). The Chinese remainder step
stands in for Glauberman's Lemma 1 (`ℚ(ζ_m) ⊓ ℚ(ζ_n) = ℚ` for coprime `m`, `n`,
`TauCeti.Cyclotomic.complexField_inf_eq_bot`): all power maps are read in the one cyclotomic field
of order `|Γ ⋊ S|`. The two statements together are `TauCeti.canonicalExtension_values`.

## Main results

* `TauCeti.IsCanonicalExtension.apply_pow`: the canonical extension of `χ^{(j)}` is `ψ^{(j)}`.
* `TauCeti.IsCanonicalExtension.apply_pow_eq_self`: power maps fixing `χ` fix `ψ`.
* `TauCeti.IsCanonicalExtension.adjoin_range_eq`: `ℚ(ψ) = ℚ(χ)`.
* `TauCeti.IsCanonicalExtension.exists_int_eq_apply_inr`: `ψ(s) ∈ ℤ` for `s ∈ S`.
* `TauCeti.canonicalExtension_values`: both, for the canonical extension of
  `TauCeti.existsUnique_canonicalExtension`.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 2, p. 1470.
-/

public section

open Module SemidirectProduct IntermediateField

namespace TauCeti

variable {k Γ S : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group Γ] [Group S] [Finite Γ]
  [Finite S] {φ : S →* MulAut Γ}

/-- **Galois conjugates of the canonical extension.** For `j` coprime to `|Γ ⋊ S|`, if `ψ` is the
canonical extension of `χ`, then `x ↦ ψ (x ^ j)` is the canonical extension of `g ↦ χ (g ^ j)`. -/
theorem IsCanonicalExtension.apply_pow {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (hψ : IsCanonicalExtension φ χ ψ) {j : ℕ} (hj : j.Coprime (Nat.card (Γ ⋊[φ] S))) :
    IsCanonicalExtension φ (fun g => χ (g ^ j)) fun x => ψ (x ^ j) := by
  obtain ⟨hirr, hinl, n, ρ, hρ, hdet⟩ := isCanonicalExtension_iff.1 hψ
  have hirr' := apply_pow_mem_irreducibleCharacters hirr hj
  obtain ⟨m, ρ', -, hρ'⟩ := mem_irreducibleCharacters_iff.1 hirr'
  refine isCanonicalExtension_iff.2 ⟨hirr', ?_, m, ρ', hρ', fun s => ?_⟩
  · funext g
    simpa only [Function.comp_apply, map_pow] using congrFun hinl (g ^ j)
  · rw [Representation.det_eq_det_pow_of_character_eq ρ ρ' fun y _ => by rw [hρ', hρ], hdet,
      one_pow]

/-- **Power maps fixing `χ` fix its canonical extension.** For `|Γ|` and `|S|` coprime and `j`
coprime to `|Γ ⋊ S|`, if `χ (g ^ j) = χ g` for every `g`, then the canonical extension `ψ` of `χ`
satisfies `ψ (x ^ j) = ψ x` for every `x`. -/
theorem IsCanonicalExtension.apply_pow_eq_self (hcop : (Nat.card Γ).Coprime (Nat.card S))
    {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k}
    (hψ : IsCanonicalExtension φ χ ψ) {j : ℕ}
    (hj : j.Coprime (Nat.card (Γ ⋊[φ] S))) (hχj : ∀ g, χ (g ^ j) = χ g) (x : Γ ⋊[φ] S) :
    ψ (x ^ j) = ψ x := by
  have h := hψ.apply_pow hj
  rw [show (fun g => χ (g ^ j)) = χ from funext hχj] at h
  exact congrFun ((existsUnique_canonicalExtension hcop hχ hψ.apply_aut).unique h hψ) x

omit [Finite Γ] [Finite S] in
/-- A power `j'` that is `1` modulo `|Γ|` and `j` modulo `|S|`, for `j` coprime to `|Γ ⋊ S|`:
it fixes every function on `Γ`, agrees with `j` on `S`, and is coprime to `|Γ ⋊ S|`. -/
private theorem exists_pow_eq_self_and_pow_eq (hcop : (Nat.card Γ).Coprime (Nat.card S)) {j : ℕ}
    (hj : j.Coprime (Nat.card (Γ ⋊[φ] S))) :
    ∃ j' : ℕ, j'.Coprime (Nat.card (Γ ⋊[φ] S)) ∧ (∀ g : Γ, g ^ j' = g) ∧
      ∀ s : S, s ^ j' = s ^ j := by
  obtain ⟨j', h₁, h₂⟩ := Nat.chineseRemainder hcop 1 j
  rw [SemidirectProduct.card] at hj ⊢
  refine ⟨j', Nat.Coprime.mul_right ?_ ?_, fun g => ?_, fun s => ?_⟩
  · rw [Nat.Coprime, h₁.gcd_eq, Nat.gcd_one_left]
  · rw [Nat.Coprime, h₂.gcd_eq]
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hj
  · rw [← pow_mod_natCard, h₁, pow_mod_natCard, pow_one]
  · rw [← pow_mod_natCard, h₂, pow_mod_natCard]

/-- **The field of values of the canonical extension** (Glauberman 1968, Theorem 2 (b), p. 1470).
For `|Γ|` and `|S|` coprime, the canonical extension `ψ` of an `S`-invariant irreducible character
`χ` has the same field of values: `ℚ(ψ) = ℚ(χ)`. -/
theorem IsCanonicalExtension.adjoin_range_eq (hcop : (Nat.card Γ).Coprime (Nat.card S))
    {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k}
    (hψ : IsCanonicalExtension φ χ ψ) :
    adjoin ℚ (Set.range ψ) = adjoin ℚ (Set.range χ) := by
  have : NeZero (Nat.card (Γ ⋊[φ] S)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨K, ζ, _, hζ⟩ := HasEnoughRootsOfUnity.exists_intermediateField_isCyclotomicExtension ℚ
    (M := k) (Nat.card (Γ ⋊[φ] S))
  have := IsCyclotomicExtension.isGalois {Nat.card (Γ ⋊[φ] S)} ℚ K
  have hΓ : Monoid.exponent Γ ∣ Nat.card (Γ ⋊[φ] S) :=
    (Group.exponent_dvd_nat_card (G := Γ)).trans
      (SemidirectProduct.card (φ := φ) ▸ dvd_mul_right _ _)
  refine le_antisymm ?_ (adjoin.mono _ _ _ ?_)
  · rw [hζ.adjoin_range_eq_map_fixedField_cyclotomicPowerStabilizer
        (Group.exponent_dvd_nat_card (G := Γ ⋊[φ] S))
        (irreducibleCharacters_subset_virtualCharacters (isCanonicalExtension_iff.1 hψ).1),
      hζ.adjoin_range_eq_map_fixedField_cyclotomicPowerStabilizer hΓ
        (irreducibleCharacters_subset_virtualCharacters hχ)]
    exact map_mono _ (IntermediateField.fixedField_le fun σ hσ =>
      (IsPrimitiveRoot.mem_cyclotomicPowerStabilizer_iff _ _ _ _).2 <|
        hψ.apply_pow_eq_self hcop hχ (ZMod.val_coe_unit_coprime _)
          ((IsPrimitiveRoot.mem_cyclotomicPowerStabilizer_iff _ _ _ _).1 hσ))
  · rintro _ ⟨g, rfl⟩
    exact ⟨inl g, congrFun (isCanonicalExtension_iff.1 hψ).2.1 g⟩

/-- **The canonical extension is integer-valued on `S`** (Glauberman 1968, Theorem 2 (b),
p. 1470). For `|Γ|` and `|S|` coprime, the canonical extension `ψ` of an `S`-invariant
irreducible character takes an integer value at every element of `S`. -/
theorem IsCanonicalExtension.exists_int_eq_apply_inr (hcop : (Nat.card Γ).Coprime (Nat.card S))
    {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k}
    (hψ : IsCanonicalExtension φ χ ψ) (s : S) :
    ∃ z : ℤ, ψ (inr s) = z := by
  have : NeZero (Nat.card (Γ ⋊[φ] S)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨K, ζ, _, hζ⟩ := HasEnoughRootsOfUnity.exists_intermediateField_isCyclotomicExtension ℚ
    (M := k) (Nat.card (Γ ⋊[φ] S))
  have := IsCyclotomicExtension.isGalois {Nat.card (Γ ⋊[φ] S)} ℚ K
  have := IsCyclotomicExtension.finiteDimensional {Nat.card (Γ ⋊[φ] S)} ℚ K
  have hS : Monoid.exponent S ∣ Nat.card (Γ ⋊[φ] S) :=
    (Group.exponent_dvd_nat_card (G := S)).trans
      (SemidirectProduct.card (φ := φ) ▸ dvd_mul_left _ _)
  -- Every power map fixes `ψ ∘ inr`, so its values are rational.
  have hstab : hζ.cyclotomicPowerStabilizer hS (ψ ∘ inr) = ⊤ := by
    refine eq_top_iff.2 fun σ _ => (IsPrimitiveRoot.mem_cyclotomicPowerStabilizer_iff _ _ _ _).2
      fun t => ?_
    obtain ⟨j', hj', hΓ, hS⟩ := exists_pow_eq_self_and_pow_eq (φ := φ) hcop
      (ZMod.val_coe_unit_coprime (hζ.autToPow ℚ σ))
    rw [Function.comp_apply, Function.comp_apply, ← hS, map_pow]
    exact hψ.apply_pow_eq_self hcop hχ hj' (fun g => by rw [hΓ]) _
  have hirr := (isCanonicalExtension_iff.1 hψ).1
  have hmem : ψ (inr s) ∈ adjoin ℚ (Set.range (ψ ∘ inr)) := subset_adjoin _ _ ⟨s, rfl⟩
  rw [hζ.adjoin_range_eq_map_fixedField_cyclotomicPowerStabilizer hS
      (comp_mem_virtualCharacters _ (irreducibleCharacters_subset_virtualCharacters hirr)),
    hstab, IsGalois.fixedField_top, IntermediateField.map_bot, mem_bot] at hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨n, ρ, -, hρ⟩ := mem_irreducibleCharacters_iff.1 hirr
  have hint : IsIntegral ℤ (algebraMap ℚ k q) := by
    rw [hq, ← hρ]
    exact ρ.isIntegral_character _
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_algebraMap_iff.1 hint)
  exact ⟨z, by rw [← hq, eq_intCast, map_intCast]⟩

/-- **Values of the canonical extension** (Glauberman 1968, Theorem 2 (b), p. 1470). For `|Γ|`
and `|S|` coprime, the canonical extension `ψ` of an `S`-invariant irreducible character `χ` has
the same field of values as `χ`, and its values on `S` are integers. -/
theorem canonicalExtension_values (hcop : (Nat.card Γ).Coprime (Nat.card S)) {χ : Γ → k}
    (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k} (hψ : IsCanonicalExtension φ χ ψ) :
    adjoin ℚ (Set.range ψ) = adjoin ℚ (Set.range χ) ∧ ∀ s : S, ∃ z : ℤ, ψ (inr s) = z :=
  ⟨hψ.adjoin_range_eq hcop hχ, hψ.exists_int_eq_apply_inr hcop hχ⟩

end TauCeti
