/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Norm
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.LocalField.Norm.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The cyclotomic character of the local Artin symbols of `ℚ_p`

The absolute local Artin map of `ℚ_p` acts on the roots of unity of `p`-power order through the
inverse of the unit part:

```text
χ_cyc (Art_{ℚ_p} (pᵏ u)) = u⁻¹        (u ∈ ℤ_pˣ),
```

and for a finite extension `F/ℚ_p` the Artin symbol of a unit `u` of the valuation ring of `F`
(`v(u) = 1`) has cyclotomic character `N_{F/ℚ_p}(u)⁻¹`. This is the cyclotomic normalization of
local class field theory, with the arithmetic Frobenius convention. On the roots of unity of
`p`-power order it identifies the Artin map with the explicit local symbols `cyclotomicSymbol`,
which act there through `u⁻¹` as well (`TauCeti.unitsMap_cyclotomicSymbol_primePow`), so the
product formula for those explicit symbols becomes a statement about Artin symbols.

The proof uses no Lubin–Tate theory. It compares, at each finite level `pⁿ`, a representative of
the Artin symbol of a uniformizer `p u` with an automorphism acting through the explicit symbol
`cyclotomicSymbol`, inside a cyclotomic extension of `ℚ_p` on which local reciprocity forces the
two to agree on the roots of unity of order `pⁿ`. Norm functoriality of the Artin map then passes
from `ℚ_p` to its finite extensions.

## Main results

* `TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_padic`: the cyclotomic
  character of the Artin symbol of `pᵏ u` is `u⁻¹`.
* `TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap_padic`: a representative of the Artin
  symbol of a unit `u ∈ ℤ_pˣ` has cyclotomic character `u⁻¹`.
* `TauCeti.ClassFieldTheory.cyclotomicCharacter_artinMap`: for `F/ℚ_p` finite, a representative
  of the Artin symbol of a unit `u` of the valuation ring of `F` has cyclotomic character
  `N_{F/ℚ_p}(u)⁻¹`.
* `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_uniformizer`: for a uniformizer
  `ϖ` of a finite extension `K/ℚ_p`, its Artin symbol `σ` satisfies
  `χ_cyc(σ) · N_{K/ℚ_p}(ϖ) = p ^ f(K/ℚ_p)`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Example 8.2, for the explicit symbols.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §2, for the norm residue symbol over `ℚ_p`.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (p : ℕ) [Fact p.Prime]

/-- Let `g ∈ G_{ℚ_p}` represent the Artin symbol of `x`, and let `ρ ∈ G_{ℚ_p}` act on the `m`-th
roots of unity through the explicit symbol `cyclotomicSymbol m p x`. Then `ρ` fixes every finite
Galois extension of `ℚ_p` inside `ℚ_p(μ_m)` that `g` fixes. -/
private theorem apply_eq_self_of_mk_eq_artinMap_of_fixes {x : ℚ_[p]ˣ}
    (g : Field.absoluteGaloisGroup ℚ_[p])
    (hg : (g : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p] x)
    (m : ℕ) [NeZero m] (ρ : Field.absoluteGaloisGroup ℚ_[p])
    (hρ : ∀ z : AlgebraicClosure ℚ_[p], z ^ m = 1 →
      ρ.toRingEquiv z = z ^ ((cyclotomicSymbol m p x : ZMod m).val))
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    [IsGalois ℚ_[p] M]
    (hM : M ≤ IntermediateField.adjoin ℚ_[p] {z : AlgebraicClosure ℚ_[p] | z ^ m = 1})
    (hgM : ∀ z : M, DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g
      (z : AlgebraicClosure ℚ_[p]) = z) (z : M) :
    ρ.toRingEquiv (z : AlgebraicClosure ℚ_[p]) = z := by
  obtain ⟨y, hy⟩ := mem_normGroup_iff.1 (mem_normGroup_of_mk_eq_artinMap_of_fixes ℚ_[p] g hg M hgM)
  obtain rfl : Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y = x := Units.ext hy
  exact cyclotomicSymbol_norm_fixes p m M hM y ρ hρ z

/- Proof sketch. Fix `u ∈ ℤ_pˣ` and `n`, put `f = φ(pⁿ)`, `N = p ^ f - 1` and `E = ℚ_p(μ_{pⁿN})`,
and let `g` represent the Artin symbol of the uniformizer `p u`. Then `g` acts on `μ_N` as
arithmetic Frobenius `ζ ↦ ζ ^ p`, and `p u` is a norm from the fixed field `M` of `g` in `E` by
finite local reciprocity. Some `ρ ∈ G_{ℚ_p}` has cyclotomic character `u⁻¹` and also acts on `μ_N`
by `ζ ↦ ζ ^ p`; it acts on `μ_{pⁿN}` through `cyclotomicSymbol (pⁿN) p (p u)`, so it fixes `M`
(`TauCeti.cyclotomicSymbol_norm_fixes`), and on `E` it is a power `g ^ k`. Comparing the actions
on `μ_N`, where `p` has order exactly `f`, gives `k ≡ 1 mod f`; since the action of `g` on `μ_{pⁿ}`
has order dividing `f`, `g` and `ρ` agree on `μ_{pⁿ}`. -/

/-- **The comparison at a finite level.** If `g ∈ G_{ℚ_p}` represents the Artin symbol of `p u`,
`u ∈ ℤ_pˣ`, then `g` acts on the roots of unity of order `pⁿ` through `u⁻¹`. -/
private theorem toZModPow_localCyclotomicCharacter_of_mk_eq_artinMap {u : ℤ_[p]ˣ} {x : ℚ_[p]ˣ}
    (hx : (x : ℚ_[p]) = p * (u : ℤ_[p])) (g : Field.absoluteGaloisGroup ℚ_[p])
    (hg : (g : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p] x)
    (n : ℕ) :
    PadicInt.toZModPow n (localCyclotomicCharacter p ℚ_[p] g : ℤ_[p]) =
      PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
  have hp := (Fact.out : p.Prime)
  -- The level `m = pⁿ N`, with `N = p ^ f - 1` and `f = φ(pⁿ)`.
  set f := (p ^ n).totient
  have hf : f ≠ 0 := (Nat.totient_pos.2 (pow_pos hp.pos n)).ne'
  set N := p ^ f - 1
  have hN : N ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hf hp.one_lt)
  set m := p ^ n * N
  have : NeZero m := ⟨mul_ne_zero (pow_ne_zero n hp.ne_zero) hN⟩
  have hpN : p.Coprime N := Nat.coprime_pow_sub_one p f hp.one_lt hf
  have hcop : (p ^ n).Coprime N := hpN.pow_left n
  have hdN : N ∣ m := dvd_mul_left N _
  have hdP : p ^ n ∣ m := dvd_mul_right _ N
  -- `p u` is a uniformizer, so `g` is an arithmetic Frobenius lift: it raises the `N`-th roots of
  -- unity to the `p`-th power.
  have hv : (x : ℚ_[p]).valuation = 1 := by
    simp [hx, Padic.valuation_mul, hp.ne_zero, PadicInt.valuation_eq_zero_of_isUnit u.isUnit]
  have hπ : IsUniformizer ℚ_[p] x := by
    rw [isUniformizer_def, ← ofAdd_toAdd (normalizedValuation ℚ_[p] x),
      _root_.Padic.toAdd_normalizedValuation_eq_valuation, hv]
  have hgF := isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer ℚ_[p] hπ g hg
  have hgN (t : AlgebraicClosure ℚ_[p]) (ht : t ^ N = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g t = t ^ p := by
    have hpow : t ^ p ^ f = t := by
      rw [← Nat.sub_add_cancel (Nat.one_le_pow f p hp.pos), pow_succ, ht, one_mul]
    simpa using isArithFrobeniusLift_iff.1 hgF t f hf (by simpa using hpow)
  -- An element `ρ` with cyclotomic character `u⁻¹` that also raises the `N`-th roots of unity to
  -- the `p`-th power.
  obtain ⟨ρ, hρχ, hρN⟩ := exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one p u⁻¹ hf
  -- The cyclotomic field `E = ℚ_p(μ_m)`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ_[p]) m
  let E := IntermediateField.adjoin ℚ_[p] {ζ}
  have : IsCyclotomicExtension {m} ℚ_[p] E := hζ.intermediateField_adjoin_isCyclotomicExtension _
  have : FiniteDimensional ℚ_[p] E := IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] E
  have : IsAbelianGalois ℚ_[p] E := IsCyclotomicExtension.isAbelianGalois {m} ℚ_[p] E
  set ζ' : E := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ⟩
  have hζ' : IsPrimitiveRoot ζ' m := IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
  set gE := AlgEquiv.restrictNormalHom E g
  set ρE := AlgEquiv.restrictNormalHom E ρ
  -- The action of `κ ∈ G_{ℚ_p}` on the `d`-th roots of unity, for `d ∣ m`, determines the
  -- reduction modulo `d` of the exponent of its restriction to `E`.
  have hcast {d c : ℕ} (hd : d ∣ m) (κ : Field.absoluteGaloisGroup ℚ_[p])
      (hκ : ∀ t : AlgebraicClosure ℚ_[p], t ^ d = 1 →
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) κ t = t ^ c) :
      ((hζ'.autToPow ℚ_[p] (AlgEquiv.restrictNormalHom E κ) : ZMod m).cast : ZMod d) = c :=
    hζ'.cast_autToPow_eq_natCast hd <| Subtype.ext <|
      (AlgEquiv.restrictNormalHom_apply E κ _).trans <| by
        rw [IntermediateField.coe_pow, IntermediateField.coe_pow]
        exact hκ _ (by rw [← pow_mul, Nat.div_mul_cancel hd, hζ.pow_eq_one])
  -- The reductions of the exponents of `g` and `ρ` modulo `pⁿ` and modulo `N`.
  have hgP : ((hζ'.autToPow ℚ_[p] gE : ZMod m).cast : ZMod (p ^ n)) =
      PadicInt.toZModPow n (localCyclotomicCharacter p ℚ_[p] g : ℤ_[p]) := by
    rw [hcast hdP g fun t ht ↦ cyclotomicCharacter.spec p (AlgEquiv.toRingEquiv g) t ht,
      ZMod.natCast_zmod_val, localCyclotomicCharacter_apply]
  have hρP : ((hζ'.autToPow ℚ_[p] ρE : ZMod m).cast : ZMod (p ^ n)) =
      PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [hcast hdP ρ fun t ht ↦ cyclotomicCharacter.spec p (AlgEquiv.toRingEquiv ρ) t ht,
      ZMod.natCast_zmod_val, ← hρχ, localCyclotomicCharacter_apply]
  have hgN' : ((hζ'.autToPow ℚ_[p] gE : ZMod m).cast : ZMod N) = p := hcast hdN g hgN
  have hρN' : ((hζ'.autToPow ℚ_[p] ρE : ZMod m).cast : ZMod N) = p := hcast hdN ρ hρN
  -- The reductions of the explicit symbol of `p u` modulo `pⁿ` and modulo `N`.
  have hsP : ZMod.unitsMap hdP (cyclotomicSymbol m p x) =
      (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom u)⁻¹ :=
    unitsMap_cyclotomicSymbol_primePow m p hdP x 1 u (by simp [hx])
  have hsN : ZMod.unitsMap hdN (cyclotomicSymbol m p x) = ZMod.unitOfCoprime p hpN := by
    simpa using unitsMap_cyclotomicSymbol_of_coprime m p hdN hpN x 1 u (by simp [hx])
  -- `ρ` acts on the `m`-th roots of unity through the explicit symbol of `p u`, as the two agree
  -- modulo the coprime factors `pⁿ` and `N` of `m`.
  set r := hζ'.autToPow ℚ_[p] ρE
  have hrs : (r : ZMod m) = cyclotomicSymbol m p x := by
    refine ZMod.eq_of_cast_eq_of_coprime hcop ?_ ?_
    · rw [hρP, ← ZMod.unitsMap_val hdP, hsP]
      simp
    · rw [hρN', ← ZMod.unitsMap_val hdN, hsN, ZMod.coe_unitOfCoprime]
  have hρm (z : AlgebraicClosure ℚ_[p]) (hz : z ^ m = 1) :
      ρ.toRingEquiv z = z ^ ((cyclotomicSymbol m p x : ZMod m).val) := by
    have hρζ :
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ ζ = ζ ^ (r : ZMod m).val := by
      rw [← AlgEquiv.restrictNormalHom_apply E ρ ζ', ← hζ'.autToPow_spec ℚ_[p],
        IntermediateField.coe_pow]
    exact hrs ▸ hζ.map_eq_pow (ρ.toRingEquiv : AlgebraicClosure ℚ_[p] →+* _) hρζ hz
  -- The fixed field `M` of `g` in `E`. By local reciprocity `p u` is a norm from `M`, so `ρ` fixes
  -- `M` and its restriction to `E` is a power of that of `g`.
  let M : IntermediateField ℚ_[p] E := IntermediateField.fixedField (Subgroup.zpowers gE)
  have : IsGalois ℚ_[p] M := IsGalois.of_fixedField_normal_subgroup _
  have : FiniteDimensional ℚ_[p] (M.map E.val) :=
    (M.equivMap E.val).toLinearEquiv.finiteDimensional
  have : IsGalois ℚ_[p] (M.map E.val) := IsGalois.of_algEquiv (M.equivMap E.val)
  have hME : M.map E.val ≤ IntermediateField.adjoin ℚ_[p] {z | z ^ m = 1} := by
    rintro _ ⟨z, -, rfl⟩
    exact IntermediateField.adjoin.mono ℚ_[p] {ζ} {z | z ^ m = 1}
      (Set.singleton_subset_iff.2 hζ.pow_eq_one) (z : E).2
  have hgM :
      ∀ z : M.map E.val, DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g
        (z : AlgebraicClosure ℚ_[p]) = z := by
    rintro ⟨_, z, hz, rfl⟩
    exact (AlgEquiv.restrictNormalHom_apply E g z).symm.trans
      (congrArg Subtype.val ((IntermediateField.mem_fixedField_iff _ _).1 hz gE
        (Subgroup.mem_zpowers gE)))
  have hρE : ρE ∈ Subgroup.zpowers gE := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers gE),
      IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    exact Subtype.ext ((AlgEquiv.restrictNormalHom_apply E ρ z).trans
      (apply_eq_self_of_mk_eq_artinMap_of_fixes p g hg m ρ hρm (M.map E.val) hME hgM
        ⟨z, z, hz, rfl⟩))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hρE
  set a := hζ'.autToPow ℚ_[p] gE
  have hra : r = a ^ k := by simp only [r, a, ← hk, map_zpow]
  -- Modulo `N`, both act as `p`, which has order `f`; so `k ≡ 1` modulo `f`.
  have hqN : ZMod.unitsMap hdN a = ZMod.unitOfCoprime p hpN :=
    Units.ext (by rw [ZMod.unitsMap_val, hgN', ZMod.coe_unitOfCoprime])
  have hqN' : ZMod.unitsMap hdN r = ZMod.unitOfCoprime p hpN :=
    Units.ext (by rw [ZMod.unitsMap_val, hρN', ZMod.coe_unitOfCoprime])
  obtain ⟨j, hj⟩ : (f : ℤ) ∣ k - 1 := by
    rw [← TauCeti.ZMod.orderOf_unitOfCoprime_pow_sub_one p f hp.one_lt hf,
      orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, mul_inv_eq_one]
    convert (hqN'.symm.trans (by rw [hra, map_zpow, hqN])).symm
  -- Modulo `pⁿ`, the class of `g` has order dividing `f = φ(pⁿ)`, so `r` and `a` agree there.
  have hkj : k = f * j + 1 := by omega
  have hP : ZMod.unitsMap hdP r = ZMod.unitsMap hdP a := by
    rw [hra, map_zpow, hkj, zpow_add_one, zpow_mul, zpow_natCast,
      ZMod.pow_totient, one_zpow, one_mul]
  rw [← hgP, ← hρP, ← ZMod.unitsMap_val hdP, ← ZMod.unitsMap_val hdP, hP]

/-- **The cyclotomic character of the Artin symbols of `ℚ_p`.** If `x = pᵏ u` with `u ∈ ℤ_pˣ`, the
`p`-adic cyclotomic character of the absolute Artin symbol of `x` is `u⁻¹`:

```text
χ_cyc (Art_{ℚ_p} (pᵏ u)) = u⁻¹.
```

So the Artin symbol of `x` acts on the roots of unity of `p`-power order through the inverse of the
unit part of `x`, exactly as the explicit symbol `cyclotomicSymbol` prescribes. -/
theorem abelianizedLocalCyclotomicCharacter_artinMap_padic {x : ℚ_[p]ˣ} {k : ℤ} {u : ℤ_[p]ˣ}
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * (u : ℤ_[p])) :
    abelianizedLocalCyclotomicCharacter p ℚ_[p] (artinMap ℚ_[p] x) = u⁻¹ := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set π : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) hp0
  -- The Artin symbol of `p` has trivial cyclotomic character, so it suffices to treat `p u`.
  have hπ : abelianizedLocalCyclotomicCharacter p ℚ_[p] (artinMap ℚ_[p] π) = 1 := by
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap ℚ_[p] π)
    rw [← hτ, abelianizedLocalCyclotomicCharacter_mk,
      localCyclotomicCharacter_artinMap_padic_uniformizer p τ hτ]
  set y : ℚ_[p]ˣ := π * Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  have hxy : x = π ^ (k - 1) * y := Units.ext <| by
    simp [y, π, hx, zpow_sub_one₀ hp0, mul_assoc, inv_mul_cancel_left₀ hp0]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (artinMap ℚ_[p] y)
  have hgu : localCyclotomicCharacter p ℚ_[p] g = u⁻¹ := Units.ext <| PadicInt.ext_of_toZModPow.1
    (toZModPow_localCyclotomicCharacter_of_mk_eq_artinMap p (by simp [y, π]) g hg)
  rw [hxy, map_mul, map_zpow, map_mul, map_zpow, hπ, one_zpow, one_mul, ← hg,
    abelianizedLocalCyclotomicCharacter_mk, hgu]

/-- **The cyclotomic normalization of the local Artin map of `ℚ_p`.** If `σ ∈ G_{ℚ_p}` represents
the absolute Artin symbol of a unit `u ∈ ℤ_pˣ`, then the `p`-adic cyclotomic character of `σ` is
`u⁻¹`: `σ` raises every root of unity of order `pⁿ` to the power `u⁻¹ mod pⁿ`. -/
theorem cyclotomicCharacter_artinMap_padic (u : ℤ_[p]ˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p σ.toRingEquiv = u⁻¹ := by
  rw [← localCyclotomicCharacter_apply, ← abelianizedLocalCyclotomicCharacter_mk, hσ]
  exact abelianizedLocalCyclotomicCharacter_artinMap_padic p (k := 0) (by simp)

/-- **The cyclotomic normalization of the local Artin map of a finite extension of `ℚ_p`.** Let
`F/ℚ_p` be finite. If `σ ∈ G_F` represents the absolute Artin symbol of a unit `u` of the valuation
ring of `F` (`v(u) = 1`), then the `p`-adic cyclotomic character of `σ` is the inverse of the norm
of `u`:

```text
χ_cyc (Art_F u) = N_{F/ℚ_p}(u)⁻¹.
```
-/
theorem cyclotomicCharacter_artinMap (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [ValuativeExtension ℚ_[p] F] (u : Fˣ) (hu : ValuativeRel.valuation F (u : F) = 1)
    (σ : Field.absoluteGaloisGroup F)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization F) = artinMap F u) :
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom
        (cyclotomicCharacter (AlgebraicClosure F) p σ.toRingEquiv) =
      (Units.map (Algebra.norm ℚ_[p] : F →* ℚ_[p]) u)⁻¹ := by
  -- Instance search does not find `Nontrivial ℚ_[p]` within its budget, so it is supplied from
  -- the field structure.
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  -- The norm of `u` is a unit of `ℤ_p`.
  have hv : (Algebra.normUnits ℚ_[p] u : ℚ_[p]).valuation = 0 := by
    rw [← _root_.Padic.toAdd_normalizedValuation_eq_valuation,
      normalizedValuation_norm_eq_one_of_eq_one u ((normalizedValuation_eq_one_iff u).2 hu),
      toAdd_one]
  obtain ⟨w, hw⟩ := _root_.Padic.exists_eq_zpow_valuation_mul
    (Units.ne_zero (Algebra.normUnits ℚ_[p] u))
  rw [← localCyclotomicCharacter_apply, ← abelianizedLocalCyclotomicCharacter_mk, hσ,
    abelianizedLocalCyclotomicCharacter_artinMap_norm ℚ_[p] p,
    abelianizedLocalCyclotomicCharacter_artinMap_padic p hw]
  rw [Algebra.coe_normUnits] at hw hv
  rw [hv, zpow_zero, one_mul] at hw
  ext
  simp [hw]

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [ValuativeExtension ℚ_[p] K]

/-- If `σ` represents the arithmetic Artin symbol of a uniformizer `ϖ` of `K`, then
`χ_cyc(σ) · N_{K/ℚ_p}(ϖ) = p ^ f(K/ℚ_p)` in `ℚ_pˣ`. -/
theorem localCyclotomicCharacter_artinMap_uniformizer (ϖ : Kˣ)
    (hϖ : IsUniformizer K ϖ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K ϖ) :
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (localCyclotomicCharacter p K σ) *
        Algebra.normUnits ℚ_[p] ϖ =
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ^
        inertiaDegree ℚ_[p] K := by
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsSeparable ℚ_[p] K :=
    (inferInstance : Algebra.IsAlgebraic ℚ_[p] K).isSeparable_of_perfectField
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hval : (Algebra.normUnits ℚ_[p] ϖ : ℚ_[p]).valuation =
      (inertiaDegree ℚ_[p] K : ℤ) := by
    rw [← _root_.Padic.toAdd_normalizedValuation_eq_valuation,
      toAdd_normalizedValuation_norm, (isUniformizer_def ϖ).mp hϖ]
    simp
  obtain ⟨u, hu⟩ := _root_.Padic.exists_eq_zpow_valuation_mul
    (Units.ne_zero (Algebra.normUnits ℚ_[p] ϖ))
  have hu' : (Algebra.normUnits ℚ_[p] ϖ : ℚ_[p]) = (p : ℚ_[p]) ^
      (inertiaDegree ℚ_[p] K : ℤ) * u := by rwa [hval] at hu
  have hχ : localCyclotomicCharacter p K σ = u⁻¹ := by
    rw [← abelianizedLocalCyclotomicCharacter_mk, hσ,
      abelianizedLocalCyclotomicCharacter_artinMap_norm ℚ_[p] p]
    exact abelianizedLocalCyclotomicCharacter_artinMap_padic p hu'
  have hnorm : Algebra.normUnits ℚ_[p] ϖ =
      (Units.mk0 (p : ℚ_[p]) hp0) ^ inertiaDegree ℚ_[p] K *
        Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u := by
    apply Units.ext
    simpa [zpow_natCast] using hu'
  rw [hχ, hnorm, map_inv]
  simp

end TauCeti.ClassFieldTheory
