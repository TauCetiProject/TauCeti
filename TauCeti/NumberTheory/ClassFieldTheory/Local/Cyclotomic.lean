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
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Cyclotomic

/-!
# Local Artin symbols on roots of unity

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

The same input computes the `p`-adic cyclotomic character of absolute Artin symbols when `p` is
not the residue characteristic: the Artin symbol of a unit lies in inertia, which fixes the roots
of unity of `p`-power order, and that of a uniformizer is a Frobenius lift, which raises them to
the `q`-th power, so `χ_p(Art_K(x)) = q ^ v_K(x)`. For every `p`, norm functoriality of the Artin
map reduces the cyclotomic character of the Artin symbols of a finite extension `L/K` to those of
`K`: `χ_L(Art_L(x)) = χ_K(Art_K(N_{L/K} x))`. When `p` is the residue characteristic, this passes
the cyclotomic character of Artin symbols from `ℚ_p` to its finite extensions.

On the roots of unity of `p`-power order, the Artin symbol of `p` over `ℚ_p` acts trivially: `p`
is the norm of `ζ - 1` from `ℚ_p(ζ)` for every primitive `pⁿ`-th root of unity `ζ` with `pⁿ ≠ 2`.
So the `p`-adic cyclotomic character takes the value `1` on every lift of `Art_{ℚ_p}(p)` to the
absolute Galois group (`localCyclotomicCharacter_artinMap_padic_uniformizer`). Together with the
value of the cyclotomic character on the Artin symbols of units, this determines the cyclotomic
character on the whole image of the Artin map of `ℚ_p`.

Over `ℚ_p`, the cyclotomic character and the action on the roots of unity of order prime to `p` can
be prescribed independently: for `u ∈ ℤ_pˣ` and `f ≥ 1` some `ρ ∈ G_{ℚ_p}` has `χ_cyc(ρ) = u` and
acts on the `(p^f − 1)`-st roots of unity as `ζ ↦ ζ ^ p`
(`exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one`). This is the finite-level linear
disjointness of `ℚ_p(μ_{p^∞})` and the unramified extension of degree `f` that the comparison of
the Artin symbols of units with the explicit cyclotomic symbols needs.

Since the image of the absolute Artin map is dense in `G_K^ab`, the image of the `p`-adic
cyclotomic character of `G_K` is the closure of its values on Artin symbols
(`range_localCyclotomicCharacter`). This is how the image is computed from evaluations of the
cyclotomic character at units and at a uniformizer.

## Main results

* `TauCeti.ClassFieldTheory.localArtinMap_cyclotomic_uniformizer`: the Artin symbol of a
  uniformizer raises every root of unity of order prime to `q` to the `q`-th power.
* `TauCeti.ClassFieldTheory.localArtinMap_cyclotomic_padic`: over `ℚ_[p]`, the Artin symbol of
  `p` raises every root of unity of order prime to `p` to the `p`-th power.
* `TauCeti.ClassFieldTheory.localArtinMap_Q2_zeta5`: over `ℚ_[2]`, the Artin symbol of `2` sends
  a fifth root of unity `ζ` to `ζ ^ 2`.
* `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap`: for `p` different
  from the residue characteristic, `χ_p(Art_K(x)) = q ^ v_K(x)`.
* `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm`: the cyclotomic
  character of the Artin symbol of `x ∈ Lˣ` is that of the Artin symbol of `N_{L/K} x`.
* `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer`: the `p`-adic
  cyclotomic character of the Artin symbol of `p` over `ℚ_[p]` is `1`.
* `TauCeti.ClassFieldTheory.exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one`: an
  element of `G_{ℚ_p}` with prescribed cyclotomic character acting as Frobenius on the
  `(p^f − 1)`-st roots of unity.
* `TauCeti.ClassFieldTheory.range_localCyclotomicCharacter`: the image of the cyclotomic
  character of `G_K` is the closure of its values on the absolute Artin symbols.

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

For the independent prescription, the cyclotomic character of `G_{ℚ_p}` is surjective
(`surjective_localCyclotomicCharacter_ratPadic`), so some `ρ₀` has `χ_cyc(ρ₀) = u`. A lift `τ` of
the Artin symbol of `p` has trivial cyclotomic character and is an arithmetic Frobenius lift; its
restriction to the unramified extension of degree `f` is that extension's Frobenius, which
generates its Galois group (`IsArithFrobeniusLift.zpowers_restrictNormalHom_unramifiedExtension`).
So `ρ₀` restricts there to a power `τ ^ j`, and `ρ = ρ₀ τ⁻ʲ τ` has character `u` and acts on the
unramified extension as `τ` does.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1, and §2 for the norm residue symbol
  over `ℚ_p`.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open Polynomial _root_.ValuativeRel

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
  have h := localArtinMap_cyclotomic_uniformizer ℚ_[p] L ι (Padic.isUniformizer_natCast_self p)
    hσ (by rwa [Padic.natCard_residueField]) hζ
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

/-! ### The cyclotomic character of absolute Artin symbols -/

/-- **The `p`-adic cyclotomic character of an Artin symbol, `p` away from the residue
characteristic.** Let `q` be the cardinality of the residue field of `K`, let `u ∈ ℤ_pˣ` be the
unit `q`, and let `x ∈ Kˣ`. Then the `p`-adic cyclotomic character of the absolute Artin symbol
of `x` is `q ^ v_K(x)`:

```text
χ_p (Art_K x) = q ^ v_K(x).
```

That `q` is a unit of `ℤ_[p]` forces `p` to differ from the residue characteristic. -/
theorem abelianizedLocalCyclotomicCharacter_artinMap {p : ℕ} [Fact p.Prime] {u : ℤ_[p]ˣ}
    (hu : (u : ℤ_[p]) = Nat.card 𝓀[K]) (x : Kˣ) :
    abelianizedLocalCyclotomicCharacter p K (artinMap K x) =
      u ^ (normalizedValuation K x).toAdd := by
  -- `q` is a power of the residue characteristic and a `p`-adic unit, so `p` is prime to it.
  have hp : p.Coprime (ringChar 𝓀[K]) := by
    refine (Nat.coprime_primes Fact.out (CharP.prime_ringChar 𝓀[K])).2 fun hpq ↦ ?_
    let _ := Fintype.ofFinite 𝓀[K]
    obtain ⟨d, -, hd⟩ := FiniteField.card 𝓀[K] (ringChar 𝓀[K])
    have h0 : PadicInt.toZMod (u : ℤ_[p]) = 0 := by
      rw [hu, map_natCast, Nat.card_eq_fintype_card, hd, ← hpq, Nat.cast_pow, ZMod.natCast_self,
        zero_pow d.ne_zero]
    exact not_isUnit_zero (h0 ▸ u.isUnit.map PadicInt.toZMod)
  -- Write `x = w * π ^ n` with `w` a unit and `π` a uniformizer.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ : IsUniformizer K (Units.mk0 (ϖ : K) fun h ↦ hϖ.ne_zero (Subtype.ext h)) :=
    (isUniformizer_iff_exists_irreducible K _).2 ⟨ϖ, hϖ, rfl⟩
  obtain ⟨w, n, hw, hx⟩ := exists_eq_mul_zpow_of_irreducible hϖ x
  -- The symbol of `π` is represented by a Frobenius lift, that of `w` by an element of inertia.
  obtain ⟨φ, hφ⟩ := QuotientGroup.mk_surjective
    (artinMap K (Units.mk0 (ϖ : K) fun h ↦ hϖ.ne_zero (Subtype.ext h)))
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap K w)
  have hφu : localCyclotomicCharacter p K φ = u := Units.ext <|
    ((isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer K hπ φ hφ).coe_localCyclotomicCharacter
      p hp).trans hu.symm
  have hτ1 : localCyclotomicCharacter p K τ = 1 :=
    localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup p hp
      (mem_inertiaSubgroup_of_mk_eq_artinMap K w hw τ hτ)
  have hart : artinMap K x =
      ((τ * φ ^ n : Field.absoluteGaloisGroup K) : Field.absoluteGaloisGroupAbelianization K) := by
    simp [hx, hτ, hφ]
  rw [hart, abelianizedLocalCyclotomicCharacter_mk, map_mul, map_zpow, hτ1, hφu, one_mul]
  subst x
  simp [(normalizedValuation_eq_one_iff w).2 hw, normalizedValuation_irreducible hϖ]

/-- **The cyclotomic character of the Artin symbol of a norm.** Let `L/K` be a finite separable
extension of nonarchimedean local fields. The absolute Artin symbol of `x ∈ Lˣ` and that of its
norm `N_{L/K} x` have the same `p`-adic cyclotomic character:

```text
χ_L (Art_L x) = χ_K (Art_K (N_{L/K} x)).
```

This reduces the cyclotomic character of the Artin symbols of a finite extension of `ℚ_p` to those
of `ℚ_p` itself. -/
theorem abelianizedLocalCyclotomicCharacter_artinMap_norm (p : ℕ) [Fact p.Prime] {L : Type}
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] (x : Lˣ) :
    abelianizedLocalCyclotomicCharacter p L (artinMap L x) =
      abelianizedLocalCyclotomicCharacter p K (artinMap K (Algebra.normUnits K x)) := by
  let iota : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap L x)
  rw [← hτ, ← artinMap_norm L iota x τ hτ, abelianizedLocalCyclotomicCharacter_mk,
    abelianizedLocalCyclotomicCharacter_mk, localCyclotomicCharacter_absoluteGaloisGroupExtend]

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

/-! ### Prescribing the cyclotomic character and the unramified action -/

/-- **Independent prescription of the cyclotomic character and the unramified action.** For
`u ∈ ℤ_pˣ` and `f ≠ 0` there is `ρ ∈ G_{ℚ_p}` whose `p`-adic cyclotomic character is `u` and which
raises every `(p ^ f − 1)`-st root of unity to the `p`-th power. -/
theorem exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one (u : ℤ_[p]ˣ) {f : ℕ}
    (hf : f ≠ 0) :
    ∃ ρ : Field.absoluteGaloisGroup ℚ_[p], localCyclotomicCharacter p ℚ_[p] ρ = u ∧
      ∀ z : AlgebraicClosure ℚ_[p], z ^ (p ^ f - 1) = 1 →
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ z = z ^ p := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective
    (artinMap ℚ_[p] (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 hp.ne_zero)))
  have hτχ := localCyclotomicCharacter_artinMap_padic_uniformizer p τ hτ
  have hτF := isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer ℚ_[p]
    (Padic.isUniformizer_natCast_self p) τ hτ
  have hτz (z : AlgebraicClosure ℚ_[p]) (hz : z ^ (p ^ f - 1) = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) τ z = z ^ p := by
    -- The roots of unity of order `p ^ f - 1` are the nonzero roots of `X ^ (p ^ f) - X`.
    have hpow : z ^ p ^ f = z := by
      rw [← Nat.sub_add_cancel (Nat.one_le_pow f p hp.pos), pow_succ, hz, one_mul]
    simpa using isArithFrobeniusLift_iff.1 hτF z f hf (by simpa using hpow)
  have hF := unramifiedExtension_eq_adjoin_setOf_pow_eq_one (K := ℚ_[p])
    (Ω := AlgebraicClosure ℚ_[p]) hf
  rw [Padic.natCard_residueField] at hF
  set F := unramifiedExtension ℚ_[p] (AlgebraicClosure ℚ_[p]) f
  let r : Field.absoluteGaloisGroup ℚ_[p] →* Gal(F/ℚ_[p]) := AlgEquiv.restrictNormalHom F
  obtain ⟨ρ₀, hρ₀⟩ := surjective_localCyclotomicCharacter_ratPadic p u
  -- `τ` restricts to the Frobenius of `F`, which generates `Gal(F/ℚ_p)`.
  obtain ⟨j, hj⟩ : ∃ j : ℤ, r τ ^ j = r ρ₀ := Subgroup.mem_zpowers_iff.1
    ((hτF.zpowers_restrictNormalHom_unramifiedExtension hf).symm ▸ Subgroup.mem_top (r ρ₀))
  refine ⟨ρ₀ * (τ ^ j)⁻¹ * τ, ?_, fun z hz ↦ ?_⟩
  · rw [map_mul, map_mul, map_inv, map_zpow, hρ₀, hτχ, one_zpow, inv_one, mul_one, mul_one]
  · have hr : r (ρ₀ * (τ ^ j)⁻¹ * τ) = r τ := by
      rw [map_mul, map_mul, map_inv, map_zpow, ← hj, mul_inv_cancel, one_mul]
    have hzF : z ∈ F := hF.ge (IntermediateField.subset_adjoin _ _ hz)
    calc _ = (r (ρ₀ * (τ ^ j)⁻¹ * τ) ⟨z, hzF⟩ : AlgebraicClosure ℚ_[p]) :=
          (AlgEquiv.restrictNormalHom_apply F _ _).symm
      _ = (r τ ⟨z, hzF⟩ : AlgebraicClosure ℚ_[p]) := by rw [hr]
      _ = z ^ p := (AlgEquiv.restrictNormalHom_apply F τ _).trans (hτz z hz)

/-! ### The image of the cyclotomic character -/

/-- **The image of the cyclotomic character is generated by the Artin symbols.** For a
nonarchimedean local field `K`, the image of the `p`-adic cyclotomic character of `G_K` is the
closure of its values on the image of the absolute local Artin map:

```text
χ_cyc(G_K) = closure (χ_cyc(Art_K(Kˣ))).
```

No relation between `p` and the residue characteristic of `K` is assumed.

The unit values of `χ_cyc ∘ Art_K` do not determine the image on their own: for `p = 3` and
`K = ℚ_3(√3)`, the extension `K(μ_3) = K(√-1)` is unramified over `K`, so the image is all of
`ℤ_3ˣ`, while the norms of units of `K` fill only the index-two subgroup `1 + 3ℤ_3`. -/
theorem range_localCyclotomicCharacter :
    (localCyclotomicCharacter p K).range =
      ((abelianizedLocalCyclotomicCharacter p K).toMonoidHom.comp
        (artinMap K)).range.topologicalClosure := by
  refine le_antisymm ?_ <| Subgroup.topologicalClosure_minimal _ ?_ <|
    MonoidHom.isClosed_range_of_continuous (localCyclotomicCharacter_continuous p K)
  · rintro _ ⟨σ, rfl⟩
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, MonoidHom.coe_range,
      MonoidHom.coe_comp, Set.range_comp]
    exact (abelianizedLocalCyclotomicCharacter p K).continuous.range_subset_closure_image_dense
      (denseRange_artinMap K) ⟨σ, abelianizedLocalCyclotomicCharacter_mk p K σ⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K x)
    exact ⟨σ, by simp [← hσ]⟩

/-- The image of the `p`-adic cyclotomic character of a nonarchimedean local field `K` lies in a
closed subgroup `H` of `ℤ_pˣ` exactly when the cyclotomic character of every absolute Artin symbol
does. -/
theorem range_localCyclotomicCharacter_le_iff {H : Subgroup ℤ_[p]ˣ}
    (hH : IsClosed (H : Set ℤ_[p]ˣ)) :
    (localCyclotomicCharacter p K).range ≤ H ↔
      ∀ x : Kˣ, abelianizedLocalCyclotomicCharacter p K (artinMap K x) ∈ H := by
  rw [range_localCyclotomicCharacter]
  refine ⟨fun h x ↦ h (Subgroup.le_topologicalClosure _ ⟨x, rfl⟩), fun h ↦ ?_⟩
  exact Subgroup.topologicalClosure_minimal _ (by rintro _ ⟨x, rfl⟩; exact h x) hH

end TauCeti.ClassFieldTheory
