/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.LocalField.Padic
import Mathlib.NumberTheory.Cyclotomic.Gal
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.NumberTheory.LocalField.Unramified.Existence

/-!
# Local Artin symbols of uniformizers on roots of unity

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and let `π` be a
uniformizer of `K`. For every finite Galois extension `L/K`, the local Artin symbol of `π` acts on
the roots of unity of `L` of order prime to `q` by `ζ ↦ ζ ^ q`. The extension need not be
unramified: such roots of unity generate an unramified subextension, on which the Artin symbol of
`π` is arithmetic Frobenius.

This is the local cyclotomic input of the cyclotomic normalization of the local Artin map: over
`ℚ_ℓ`, the Artin symbol of `ℓ` acts on the `pⁿ`-th roots of unity, `p ≠ ℓ`, by `ζ ↦ ζ ^ ℓ`
(`localArtinMap_cyclotomic_padic`). For `ℚ₂(ζ₅)/ℚ₂`, which is unramified of degree four, the
Artin symbol of `2` is `ζ₅ ↦ ζ₅ ^ 2` (`localArtinMap_Q2_zeta5`); with geometric Frobenius the
exponent would be `3`.

On the roots of unity of `p`-power order, the Artin symbol of `p` over `ℚ_p` acts trivially: `p`
is the norm of `ζ - 1` from `ℚ_p(ζ)` for every primitive `pⁿ`-th root of unity `ζ` with `pⁿ ≠ 2`.
So the `p`-adic cyclotomic character takes the value `1` on every lift of `Art_{ℚ_p}(p)` to the
absolute Galois group (`localCyclotomicCharacter_artinMap_padic_uniformizer`). Together with the
value of the cyclotomic character on the Artin symbols of units, this determines the cyclotomic
character on the whole image of the Artin map of `ℚ_p`.

## Main results

* `TauCeti.ClassFieldTheory.localArtinMap_cyclotomic_uniformizer`: the Artin symbol of a
  uniformizer raises every root of unity of order prime to `q` to the `q`-th power.
* `TauCeti.ClassFieldTheory.localArtinMap_cyclotomic_padic`: over `ℚ_[p]`, the Artin symbol of
  `p` raises every root of unity of order prime to `p` to the `p`-th power.
* `TauCeti.ClassFieldTheory.localArtinMap_Q2_zeta5`: over `ℚ_[2]`, the Artin symbol of `2` sends
  a fifth root of unity `ζ` to `ζ ^ 2`.
* `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer`: the `p`-adic
  cyclotomic character of the Artin symbol of `p` over `ℚ_[p]` is `1`.

## Implementation notes

The roots of unity in question lie in the unramified extension `unramifiedExtension K Kˢ f` of
some degree `f`, where the finite local Artin map sends `π` to arithmetic Frobenius
(`localArtinMap_uniformizer`). The absolute local Artin map compares the Artin symbol on this
extension with the Artin symbol on `L` (`artinMap_restrict`), and the action on a root of unity
factors through the abelian group `(ℤ/nℤ)ˣ` (`IsPrimitiveRoot.autToPow`), so it only depends on
the class of an automorphism in `Gal(L/K)ᵃᵇ`.

For the roots of unity of `p`-power order over `ℚ_[p]`, the norm computation is Mathlib's
`IsPrimitiveRoot.sub_one_norm_isPrimePow`, which needs `Φ_{pⁿ}` to be irreducible over `ℚ_[p]`
(`TauCeti.irreducible_cyclotomic_prime_pow_ratPadic`). A norm has trivial finite Artin symbol
(`localArtinMap_eq_zero_iff`), so the restriction of a lift of `Art_{ℚ_p}(p)` to `ℚ_p(ζ)` is
trivial by `artinMap_restrict` and the injectivity of `IsPrimitiveRoot.autToPow`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1, and §2 for the norm residue symbol
  over `ℚ_p`.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open Polynomial ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The unramified extension of degree `f` of `K` inside its separable closure. -/
local notation "𝓤" f:max => unramifiedExtension K (SeparableClosure K) f

/-- An automorphism of the separable closure representing the absolute Artin symbol of a
uniformizer acts on the roots of `X^{q^f} − X` by the `q`-th power map: it restricts to arithmetic
Frobenius on the unramified extension of degree `f`. -/
private theorem absoluteGaloisGroupRestrictEquiv_apply_of_pow_natCard_pow_eq_self
    {π : Kˣ} (hπ : IsUniformizer K π) {σ : Field.absoluteGaloisGroup K}
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K π)
    {f : ℕ} (hf : f ≠ 0) {x : SeparableClosure K} (hx : x ^ Nat.card 𝓀[K] ^ f = x) :
    absoluteGaloisGroupRestrictEquiv K σ x = x ^ Nat.card 𝓀[K] := by
  let := finiteExtensionValuativeRel K (𝓤 f)
  let := finiteExtensionNormedFieldTopology K (𝓤 f)
  have := finiteExtension_isNonarchimedeanLocalField K (𝓤 f)
  have := finiteExtension_valuativeExtension K (𝓤 f)
  have : IsUnramified K (𝓤 f) := isUnramified_unramifiedExtension hf
  let : CommGroup Gal(𝓤 f/K) := IsCyclic.commGroup
  have hmem : x ∈ 𝓤 f := rootSet_subset_unramifiedExtension K _ f <| by
    rw [mem_rootSet]
    refine ⟨FiniteField.X_pow_card_pow_sub_X_ne_zero _ hf Finite.one_lt_card, ?_⟩
    simp [hx]
  -- The restriction of `σ` to the unramified extension is arithmetic Frobenius, since both
  -- represent the Artin symbol of `π` in its abelian Galois group.
  have hres : (𝓤 f).val.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) =
      frobeniusAlgEquiv (K := K) (L := 𝓤 f) := by
    have h := (artinMap_restrict K (𝓤 f) (𝓤 f).val π σ hσ).symm.trans
      (localArtinMap_uniformizer K (𝓤 f) (𝓤 f).val hπ)
    exact Abelianization.equivOfComm.injective (Additive.ofMul.injective h)
  have hy : (⟨x, hmem⟩ : 𝓤 f) ^ Nat.card 𝓀[K] ^ f = ⟨x, hmem⟩ := Subtype.ext hx
  have h := (𝓤 f).val.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv K σ)
    ⟨x, hmem⟩
  rw [hres, frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self hf hy] at h
  exact h.symm

/-- **The local Artin symbol of a uniformizer on roots of unity.** Let `L/K` be a finite Galois
extension of a nonarchimedean local field whose residue field has `q` elements, and let `σ`
represent the local Artin symbol of a uniformizer `π` in `Gal(L/K)ᵃᵇ`. Then `σ ζ = ζ ^ q` for every
`ζ ∈ L` with `ζ ^ m = 1` and `m` prime to `q`. -/
theorem localArtinMap_cyclotomic_uniformizer (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K) {π : Kˣ}
    (hπ : IsUniformizer K π) {σ : Gal(L/K)}
    (hσ : localArtinMap K L ι (Additive.ofMul π) = Additive.ofMul (Abelianization.of σ))
    {m : ℕ} (hm : (Nat.card 𝓀[K]).Coprime m) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ Nat.card 𝓀[K] := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Finite.one_lt_card (α := 𝓀[K])).ne' (Nat.coprime_zero_right _ |>.mp hm)
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap K π)
  set τ' := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K τ)
  -- `σ` and the restriction `τ'` of `τ` represent the same Artin symbol, so they agree on `ζ`,
  -- on which `Gal(L/K)` acts through the abelian group `(ℤ/dℤ)ˣ`.
  have hστ : σ ζ = τ' ζ := by
    have hζ' := IsPrimitiveRoot.orderOf ζ
    have : NeZero (orderOf ζ) :=
      ⟨(orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨m, Nat.pos_of_ne_zero hm0, hζ⟩)).ne'⟩
    have h := congrArg (Abelianization.lift (hζ'.autToPow K))
      (Additive.ofMul.injective (hσ.symm.trans (artinMap_restrict K L ι π τ hτ)))
    rw [Abelianization.lift_apply_of, Abelianization.lift_apply_of] at h
    rw [← hζ'.autToPow_spec K σ, ← hζ'.autToPow_spec K τ', h]
  -- `τ` acts on the root of unity `ι ζ` by the `q`-th power map.
  have hιζ := absoluteGaloisGroupRestrictEquiv_apply_of_pow_natCard_pow_eq_self K hπ hτ
    (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne'
    (pow_pow_totient_eq_self hm (x := ι ζ) (by rw [← map_pow, hζ, map_one]))
  have h := ι.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv K τ) ζ
  rw [hιζ, ← map_pow] at h
  exact hστ.trans (ι.injective h)

/-- **The local Artin symbol of `p` on roots of unity over `ℚ_[p]`.** If `σ` represents the Artin
symbol of `p` for a finite Galois extension `L/ℚ_[p]`, then `σ ζ = ζ ^ p` for every `ζ ∈ L` with
`ζ ^ m = 1` and `m` prime to `p`. -/
theorem localArtinMap_cyclotomic_padic (p : ℕ) [Fact p.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (ι : L →ₐ[ℚ_[p]] SeparableClosure ℚ_[p]) {σ : Gal(L/ℚ_[p])}
    (hσ : localArtinMap ℚ_[p] L ι
        (Additive.ofMul (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) =
      Additive.ofMul (Abelianization.of σ))
    {m : ℕ} (hm : p.Coprime m) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ p := by
  have hπ : IsUniformizer ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) := by
    rw [isUniformizer_def]
    apply Multiplicative.toAdd.injective
    rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, Padic.valuation_p,
      toAdd_ofAdd]
  have h := localArtinMap_cyclotomic_uniformizer ℚ_[p] L ι hπ hσ
    (by rwa [Padic.natCard_residueField]) hζ
  rwa [Padic.natCard_residueField] at h

/-- **The `ℚ₂(ζ₅)` test of local reciprocity.** Over `ℚ_[2]`, the Artin symbol of `2` sends a
fifth root of unity `ζ` to `ζ ^ 2`. The fifth roots of unity generate the unramified extension of
degree four of `ℚ_[2]`, and geometric Frobenius would send `ζ` to `ζ ^ 3`. -/
theorem localArtinMap_Q2_zeta5 (E : Type*) [Field E] [Algebra ℚ_[2] E]
    [FiniteDimensional ℚ_[2] E] [IsGalois ℚ_[2] E] (ι : E →ₐ[ℚ_[2]] SeparableClosure ℚ_[2])
    {σ : Gal(E/ℚ_[2])}
    (hσ : localArtinMap ℚ_[2] E ι (Additive.ofMul (Units.mk0 (2 : ℚ_[2]) two_ne_zero)) =
      Additive.ofMul (Abelianization.of σ))
    {ζ : E} (hζ : ζ ^ 5 = 1) :
    σ ζ = ζ ^ 2 :=
  localArtinMap_cyclotomic_padic 2 E ι (by simpa using hσ) (by norm_num) hζ

/-! ### The Artin symbol of `p` on roots of unity of `p`-power order -/

variable (p : ℕ) [Fact p.Prime]

/-- A lift `σ` of the Artin symbol of `p` over `ℚ_[p]` fixes every root of unity of `p`-power order
in the separable closure: such a root lies in `ℚ_p(ζ)` for a primitive `p^(n+2)`-th root of unity
`ζ`, and `p = N(ζ - 1)` is a norm from `ℚ_p(ζ)`. -/
private theorem absoluteGaloisGroupRestrictEquiv_artinMap_padic_apply_of_pow_eq_one
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)))
    {n : ℕ} {t : SeparableClosure ℚ_[p]} (ht : t ^ p ^ n = 1) :
    absoluteGaloisGroupRestrictEquiv ℚ_[p] σ t = t := by
  have hp := (Fact.out : p.Prime)
  -- Work at level `p ^ (n + 2) ≠ 2`, where `N(ζ - 1) = p` holds for every prime `p`.
  set m := p ^ (n + 2)
  have hm : 2 ^ 2 ≤ m :=
    (Nat.pow_le_pow_left hp.two_le 2).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have : NeZero m := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure ℚ_[p]) m
  let E := IntermediateField.adjoin ℚ_[p] {ζ}
  have := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have := IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] E
  have := IsCyclotomicExtension.isGalois {m} ℚ_[p] E
  set ζ' : E := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ⟩
  have hζ' : IsPrimitiveRoot ζ' m := IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
  have hnorm := hζ'.sub_one_norm_isPrimePow (hp.isPrimePow.pow (by omega))
    (irreducible_cyclotomic_prime_pow_ratPadic p (n + 2)) (by omega)
  rw [hp.pow_minFac (by omega)] at hnorm
  have hne : ζ' - 1 ≠ 0 := sub_ne_zero.2 (hζ'.ne_one (by omega))
  have hmem : Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 hp.ne_zero) ∈ normGroup ℚ_[p] E :=
    mem_normGroup_iff.2 ⟨Units.mk0 _ hne, by simp [hnorm]⟩
  -- The restriction of `σ` to `ℚ_p(ζ)` represents the Artin symbol of the norm `p`, which is
  -- trivial, and `Gal(ℚ_p(ζ)/ℚ_p)` embeds in `(ℤ/mℤ)ˣ` through its action on `ζ`.
  have hres := (artinMap_restrict ℚ_[p] E E.val _ σ hσ).symm.trans
    ((localArtinMap_eq_zero_iff ℚ_[p] E E.val _).2 hmem)
  have h1 : E.val.restrictNormalHom (absoluteGaloisGroupRestrictEquiv ℚ_[p] σ) = 1 := by
    have h := congrArg (Abelianization.lift (hζ'.autToPow ℚ_[p])) (Additive.ofMul.injective hres)
    rw [Abelianization.lift_apply_of, map_one] at h
    exact hζ'.autToPow_injective ℚ_[p] (h.trans (map_one _).symm)
  have hfix : absoluteGaloisGroupRestrictEquiv ℚ_[p] σ ζ = ζ := by
    have h := E.val.restrictNormalHom_commutes (absoluteGaloisGroupRestrictEquiv ℚ_[p] σ) ζ'
    rw [h1] at h
    exact h.symm
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (k := m) (by
    rw [show m = p ^ n * p ^ 2 by ring, pow_mul, ht, one_pow])
  rw [map_pow, hfix]

/-- **The cyclotomic character of the Artin symbol of `p` over `ℚ_[p]`.** If `σ` in the absolute
Galois group of `ℚ_[p]` represents the absolute local Artin symbol of `p`, then
`χ_cyc(σ) = 1` for the `p`-adic cyclotomic character: `σ` fixes every root of unity of `p`-power
order, because `p` is a norm from every `ℚ_p(μ_{pⁿ})`. -/
theorem localCyclotomicCharacter_artinMap_padic_uniformizer (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) :
    localCyclotomicCharacter p ℚ_[p] σ = 1 := by
  rw [← cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv,
    ← map_one (cyclotomicCharacter (SeparableClosure ℚ_[p]) p)]
  exact cyclotomicCharacter_eq_of_forall_pow_eq_one p fun _ _ ht ↦
    absoluteGaloisGroupRestrictEquiv_artinMap_padic_apply_of_pow_eq_one p σ hσ ht

end TauCeti.ClassFieldTheory
