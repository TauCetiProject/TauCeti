/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import TauCeti.NumberTheory.GaussSum.Basic
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Stickelberger.GaussProduct
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

import Mathlib.Algebra.Algebra.ZMod
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.NumberTheory.MulChar.Cyclic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Compatible split-prime Gauss data

At a rational prime `p ≡ 1 (mod m)` and a prime ideal `P ∣ (p)` of `𝓞 K` with `Ideal.absNorm P = p`,
`TauCeti.SplitPrimeGaussData` bundles:
- a primitive generator `gen` of `(ZMod p)ˣ`,
- a primitive `m`-th root of unity `root : 𝓞 K`, and
- a multiplicative character `char : MulChar (ZMod p) (𝓞 K)` satisfying `char gen = root` and the
  compatibility congruence `char⁻¹ gen ≡ gen ^ ((p - 1) / m) (mod P)`.

`SplitPrimeGaussData.ofIdeal` constructs compatible data from any prime `P ∣ (p)` of norm `p`
coprime to `m` and any generator `g` of `(ZMod p)ˣ` by pulling back
`(Ideal.powerResidueSymbol P m)⁻¹` to `ZMod p` (`TauCeti.invPowerResidueMulChar`).
`TauCeti.exists_splitPrimeGaussData` establishes existence at every prime `p` with `m ∣ p - 1`.
The comparison, transport, and generator-reindexing lemmas connect `SplitPrimeGaussData` to
`Ideal.powerResidueSymbol`, native Gauss sums, `TauCeti.stickelbergerGaussProduct`, field
embeddings `K ≃+* K'`, `Gal(K/ℚ)`, and changes of generator of `(ZMod p)ˣ`.

## Main definitions

* `TauCeti.invPowerResidueMulChar`: pullback of `(Ideal.powerResidueSymbol P m)⁻¹` to `ZMod p`.
* `TauCeti.SplitPrimeGaussData` and `TauCeti.SplitPrimeGaussData.ofIdeal`: compatible split-prime
  Gauss data and its constructor deriving the character from `(Ideal.powerResidueSymbol P m)⁻¹`.
* `TauCeti.SplitPrimeGaussData.map`, `TauCeti.SplitPrimeGaussData.smul`, and
  `TauCeti.SplitPrimeGaussData.withGen`: field transport, Galois transport, and generator
  reindexing.

## Main results

* `TauCeti.exists_splitPrimeGaussData`: existence of compatible split-prime Gauss data whenever
  `m ∣ p - 1`.
* `TauCeti.SplitPrimeGaussData.char_eq_invPowerResidueMulChar`,
  `TauCeti.SplitPrimeGaussData.gaussSum_inv_powerResidueSymbol_eq`, and
  `TauCeti.SplitPrimeGaussData.algebraMap_stickelbergerGaussProduct`: comparison with the
  inverse power residue symbol, its Gauss sum, and `stickelbergerGaussProduct`.
* `TauCeti.SplitPrimeGaussData.smul_char`, `TauCeti.SplitPrimeGaussData.withGen_root_eq_of_zpow`,
  and `TauCeti.SplitPrimeGaussData.smul_withGen_root_eq`: character power formula under `Gal(K/ℚ)`
  and invariance of `root` under congruent or simultaneous Galois/generator reindexing.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped Pointwise

namespace TauCeti

section SplitPrime

variable {m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K]
  [HasEnoughRootsOfUnity (𝓞 K) m] {p : ℕ} [hp : Fact p.Prime]

/-- Pullback of the inverse `m`-th power residue symbol `(· / P)_m⁻¹` to `ZMod p` along
`algebraMap (ZMod p) (𝓞 K ⧸ P)`. -/
noncomputable def invPowerResidueMulChar (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K]
    [HasEnoughRootsOfUnity (𝓞 K) m] (P : Ideal (𝓞 K)) [P.IsMaximal] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) (𝓞 K ⧸ P)] : MulChar (ZMod p) (𝓞 K) :=
  MulChar.ofUnitHom <| (Ideal.powerResidueSymbol P m)⁻¹.toUnitHom.comp
    (Units.map (algebraMap (ZMod p) (𝓞 K ⧸ P)).toMonoidHom)

/-- Evaluation of `invPowerResidueMulChar` at any residue `t : ZMod p`. -/
@[simp]
theorem invPowerResidueMulChar_apply (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Algebra (ZMod p) (𝓞 K ⧸ P)] (t : ZMod p) :
    invPowerResidueMulChar m P t =
      (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) t) := by
  let _ := Ideal.Quotient.field P
  obtain rfl | ht := eq_or_ne t 0
  · rw [MulChar.map_zero, map_zero, MulChar.map_zero]
  obtain ⟨u, rfl⟩ := ht.isUnit
  simp [invPowerResidueMulChar]

/-- **Compatible split-prime Gauss data.** Bundles a prime ideal `P ∣ (p)` of `𝓞 K` with
`Ideal.absNorm P = p` and `p.Coprime m`, a generator `gen` of `(ZMod p)ˣ`, a primitive `m`-th
root of unity `root : 𝓞 K`, and a multiplicative character `char : MulChar (ZMod p) (𝓞 K)`
satisfying `char gen = root` and `char⁻¹ gen ≡ gen ^ ((p - 1) / m) (mod P)`. -/
structure SplitPrimeGaussData (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
    [HasEnoughRootsOfUnity (𝓞 K) m] (p : ℕ) [Fact p.Prime] where
  /-- The split prime ideal `P ∣ (p)` of `𝓞 K`. -/
  P : Ideal (𝓞 K)
  /-- `P` is a maximal ideal of `𝓞 K`. -/
  isMaximal : P.IsMaximal := by infer_instance
  /-- `P` lies over `(p) ⊆ ℤ`. -/
  liesOver : P.LiesOver (Ideal.span {(p : ℤ)}) := by infer_instance
  /-- `P` has degree one over `ℚ`: `Ideal.absNorm P = p`. -/
  absNorm_eq : Ideal.absNorm P = p
  /-- `p` is coprime to `m`. -/
  coprime : p.Coprime m
  /-- A primitive generator of `(ZMod p)ˣ`. -/
  gen : (ZMod p)ˣ
  /-- `gen` generates `(ZMod p)ˣ`. -/
  zpowers_gen : Subgroup.zpowers gen = ⊤
  /-- The compatible character `ZMod p →* 𝓞 K`. -/
  char : MulChar (ZMod p) (𝓞 K)
  /-- The primitive `m`-th root of unity `char gen : 𝓞 K`. -/
  root : 𝓞 K
  /-- `root` is a primitive `m`-th root of unity in `𝓞 K`. -/
  isPrimitiveRoot_root : IsPrimitiveRoot root m
  /-- Generator evaluation: `char gen = root`. -/
  char_gen : char (gen : ZMod p) = root
  /-- Compatibility congruence: `char⁻¹ gen ≡ gen ^ ((p - 1) / m) (mod P)`. -/
  mk_char_inv_gen :
    Ideal.Quotient.mk P (char⁻¹ (gen : ZMod p)) =
      (((gen : ZMod p) ^ ((p - 1) / m)).val : 𝓞 K ⧸ P)

namespace SplitPrimeGaussData

/-- The ideal `d.P` has norm coprime to `m`. -/
theorem absNorm_coprime (d : SplitPrimeGaussData m K p) : (Ideal.absNorm d.P).Coprime m :=
  d.absNorm_eq.symm ▸ d.coprime

/-- In split-prime Gauss data, `m ∣ p - 1`. -/
theorem dvd_pred (d : SplitPrimeGaussData m K p) : m ∣ p - 1 := by
  have := d.isMaximal
  simpa only [d.absNorm_eq] using NumberField.dvd_absNorm_sub_one d.absNorm_coprime

/-- Compatibility congruence expressed via `algebraMap (ZMod p) (𝓞 K ⧸ d.P)`. -/
theorem mk_char_inv_gen_eq_algebraMap (d : SplitPrimeGaussData m K p)
    [Algebra (ZMod p) (𝓞 K ⧸ d.P)] :
    Ideal.Quotient.mk d.P (d.char⁻¹ (d.gen : ZMod p)) =
      algebraMap (ZMod p) (𝓞 K ⧸ d.P) ((d.gen : ZMod p) ^ ((p - 1) / m)) := by
  rw [d.mk_char_inv_gen, ← map_natCast (algebraMap (ZMod p) (𝓞 K ⧸ d.P)),
    ZMod.natCast_zmod_val]

/-- **Root-reduction equality.** The primitive `m`-th root of unity `d.root` reduces modulo `d.P`
to `(d.gen : ZMod p)⁻¹ ^ ((p - 1) / m)`. -/
theorem mk_root_eq_algebraMap (d : SplitPrimeGaussData m K p) [Algebra (ZMod p) (𝓞 K ⧸ d.P)] :
    Ideal.Quotient.mk d.P d.root =
      algebraMap (ZMod p) (𝓞 K ⧸ d.P) (((d.gen : ZMod p)⁻¹) ^ ((p - 1) / m)) := by
  have := d.isMaximal; let _ := Ideal.Quotient.field d.P
  obtain ⟨u, hu⟩ := IsUnit.of_pow_eq_one d.isPrimitiveRoot_root.pow_eq_one (NeZero.ne m)
  have hmk_mul : Ideal.Quotient.mk d.P d.root *
      algebraMap (ZMod p) (𝓞 K ⧸ d.P) ((d.gen : ZMod p) ^ ((p - 1) / m)) = 1 := by
    rw [← d.mk_char_inv_gen_eq_algebraMap, ← map_mul, ← d.char_gen, MulChar.inv_apply_eq_inv,
      d.char_gen, ← hu, Ring.inverse_unit, Units.mul_inv, map_one]
  have hrhs_mul : algebraMap (ZMod p) (𝓞 K ⧸ d.P) (((d.gen : ZMod p)⁻¹) ^ ((p - 1) / m)) *
      algebraMap (ZMod p) (𝓞 K ⧸ d.P) ((d.gen : ZMod p) ^ ((p - 1) / m)) = 1 := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ d.gen.ne_zero, one_pow, map_one]
  have hne : algebraMap (ZMod p) (𝓞 K ⧸ d.P) ((d.gen : ZMod p) ^ ((p - 1) / m)) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr d.gen.ne_zero)
  exact mul_right_cancel₀ hne (hmk_mul.trans hrhs_mul.symm)

/-- Comparison of `d.char` with `(Ideal.powerResidueSymbol d.P m)⁻¹` via `algebraMap`. -/
theorem inv_powerResidueSymbol_algebraMap_eq (d : SplitPrimeGaussData m K p)
    [Algebra (ZMod p) (𝓞 K ⧸ d.P)] (t : ZMod p) :
    letI := d.isMaximal
    (Ideal.powerResidueSymbol d.P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ d.P) t) = d.char t :=
  have := d.isMaximal
  inv_powerResidueSymbol_algebraMap_eq_of_zpowers d.P d.absNorm_coprime d.absNorm_eq
    d.zpowers_gen (d.char_gen.symm ▸ d.isPrimitiveRoot_root.pow_eq_one)
    d.mk_char_inv_gen_eq_algebraMap t

/-- Every compatible split-prime character agrees with `invPowerResidueMulChar m d.P`. -/
theorem char_eq_invPowerResidueMulChar (d : SplitPrimeGaussData m K p)
    [Algebra (ZMod p) (𝓞 K ⧸ d.P)] :
    letI := d.isMaximal
    d.char = invPowerResidueMulChar m d.P := by
  have := d.isMaximal; ext t
  rw [invPowerResidueMulChar_apply, d.inv_powerResidueSymbol_algebraMap_eq]

/-- Comparison between the native Gauss sum over `𝓞 K ⧸ d.P` and the `ZMod p` Gauss sum of
`d.char`. -/
theorem gaussSum_inv_powerResidueSymbol_eq (d : SplitPrimeGaussData m K p)
    [Fintype (𝓞 K ⧸ d.P)] [Algebra (ZMod p) (𝓞 K ⧸ d.P)]
    {L : Type*} [CommRing L] (f : 𝓞 K →+* L) {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    letI := d.isMaximal
    gaussSum ((Ideal.powerResidueSymbol d.P m)⁻¹.ringHomComp f)
        (AddChar.traceChar (𝓞 K ⧸ d.P) hζ) =
      gaussSum (d.char.ringHomComp f) (AddChar.zmodChar p hζ.pow_eq_one) :=
  have := d.isMaximal
  gaussSum_inv_powerResidueSymbol_eq_of_eq d.P d.absNorm_eq f hζ
    d.inv_powerResidueSymbol_algebraMap_eq

/-- Split-prime compositum formula for `stickelbergerGaussProduct` attached to `d`. -/
theorem algebraMap_stickelbergerGaussProduct (d : SplitPrimeGaussData m K p)
    [IsCyclotomicExtension {m} ℚ K] [IsGalois ℚ K]
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [IsCyclotomicExtension {p} K L] [Algebra (ZMod p) (𝓞 K ⧸ d.P)]
    (hcop : ((NumberField.discr K).natAbs).Coprime p)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) (x : stickelbergerDenominatorIdeal m) :
    letI := d.isMaximal
    algebraMap K L
        (stickelbergerGaussProduct m K d.P d.absNorm_coprime (Multiplicative.ofAdd x) : K) =
      ∏ a : (ZMod m)ˣ,
        ((IsCyclotomicExtension.galEquivProd ℚ K L p hcop hζ).symm
          ((galEquivZMod m K).symm a, 1)
            (gaussSum
              (d.char.ringHomComp ((algebraMap K L).comp (algebraMap (𝓞 K) K)))
              (AddChar.zmodChar p hζ.pow_eq_one))) ^
          (x : MonoidAlgebra ℤ (ZMod m)ˣ).coeff a :=
  have := d.isMaximal; have := d.liesOver
  algebraMap_stickelbergerGaussProduct_of_zpowers m K d.P d.absNorm_coprime hcop hζ
    d.absNorm_eq d.zpowers_gen (d.char_gen.symm ▸ d.isPrimitiveRoot_root.pow_eq_one)
    d.mk_char_inv_gen_eq_algebraMap x

private theorem char_unitHom_pow_eq_one (d : SplitPrimeGaussData m K p) :
    (d.char.toUnitHom d.gen) ^ m = 1 :=
  Units.ext (by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      show (d.char.toUnitHom d.gen : 𝓞 K) = d.root from d.char_gen] using
      d.isPrimitiveRoot_root.pow_eq_one)

private theorem char_pow_eq_one (d : SplitPrimeGaussData m K p) (t : (ZMod p)ˣ) :
    d.char (t : ZMod p) ^ m = 1 := by
  have hord : orderOf d.char = m := by
    rw [← d.char.orderOf_apply_eq_orderOf (fun x ↦ d.zpowers_gen ▸ Subgroup.mem_top x),
      d.char_gen, ← d.isPrimitiveRoot_root.eq_orderOf]
  have hpow : d.char ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hord.dvd
  rw [← MulChar.pow_apply_coe, hpow, MulChar.one_apply_coe]

private theorem mk_char_inv_gen_of_eq (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Algebra (ZMod p) (𝓞 K ⧸ P)] (hNP : Ideal.absNorm P = p) (hcop : p.Coprime m)
    (χ : MulChar (ZMod p) (𝓞 K))
    (hχ : ∀ t, (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) t) = χ t)
    (g : (ZMod p)ˣ) (hpow : (χ (g : ZMod p)) ^ m = 1) :
    Ideal.Quotient.mk P (χ⁻¹ (g : ZMod p)) =
      (((g : ZMod p) ^ ((p - 1) / m)).val : 𝓞 K ⧸ P) := by
  have h1 : χ⁻¹ (g : ZMod p) =
      Ideal.powerResidueSymbol P m (algebraMap (ZMod p) (𝓞 K ⧸ P) (g : ZMod p)) := by
    obtain ⟨u, hu⟩ := IsUnit.of_pow_eq_one hpow (NeZero.ne m)
    have h1' :
        (Ideal.powerResidueSymbol P m)⁻¹ (algebraMap (ZMod p) (𝓞 K ⧸ P) (g : ZMod p)) =
          (u : 𝓞 K) := (hχ g).trans hu.symm
    rw [MulChar.inv_apply_eq_inv]; change Ring.inverse (χ g) = _; rw [← hu, Ring.inverse_unit]
    have h2 := congrArg Ring.inverse h1'
    rw [Ring.inverse_unit, ← MulChar.inv_apply_eq_inv, inv_inv] at h2
    exact h2.symm
  rw [h1, Ideal.mk_powerResidueSymbol (hNP ▸ hcop), hNP, ← map_pow]
  conv_lhs => rw [← ZMod.natCast_zmod_val ((g : ZMod p) ^ ((p - 1) / m)), map_natCast]

private theorem invPowerResidueMulChar_isPrimitiveRoot (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hNP : Ideal.absNorm P = p) (hcop : p.Coprime m)
    (g : (ZMod p)ˣ) (hg : Subgroup.zpowers g = ⊤) [Algebra (ZMod p) (𝓞 K ⧸ P)] :
    IsPrimitiveRoot (invPowerResidueMulChar m P (g : ZMod p)) m := by
  let _ := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard, hNP]
  let eQ : ZMod p ≃+* (𝓞 K ⧸ P) := ZMod.ringEquivOfPrime _ hp.out hcard
  let eU : (ZMod p)ˣ ≃* (𝓞 K ⧸ P)ˣ := Units.mapEquiv eQ.toMulEquiv
  have hug : ∀ u : (𝓞 K ⧸ P)ˣ, u ∈ Subgroup.zpowers (eU g) := by
    have hz : Subgroup.zpowers (eU g) = ⊤ := by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_zpowers eU.toMonoidHom g, hg]
      exact eq_top_iff.mpr fun u _ ↦
        Subgroup.mem_map.mpr ⟨eU.symm u, Subgroup.mem_top _, eU.apply_symm_apply u⟩
    exact fun u ↦ hz ▸ Subgroup.mem_top u
  have heQ : (eU g : 𝓞 K ⧸ P) = algebraMap (ZMod p) (𝓞 K ⧸ P) (g : ZMod p) :=
    DFunLike.congr_fun (Subsingleton.elim eQ.toRingHom (algebraMap (ZMod p) (𝓞 K ⧸ P))) (g : ZMod p)
  rw [IsPrimitiveRoot.iff_orderOf, invPowerResidueMulChar_apply, ← heQ]
  change orderOf ((Ideal.powerResidueSymbol P m)⁻¹ ((eU g : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) = m
  rw [MulChar.orderOf_apply_eq_orderOf _ hug, orderOf_inv,
    Ideal.orderOf_powerResidueSymbol (hNP ▸ hcop)]

/-- Construct compatible split-prime Gauss data from a prime ideal `P ∣ (p)` of norm `p`
coprime to `m` and any generator `g` of `(ZMod p)ˣ`, deriving the character from
`(Ideal.powerResidueSymbol P m)⁻¹`. -/
noncomputable def ofIdeal (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K]
    [HasEnoughRootsOfUnity (𝓞 K) m] {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hNP : Ideal.absNorm P = p) (hcop : p.Coprime m)
    (g : (ZMod p)ˣ) (hg : Subgroup.zpowers g = ⊤) :
    SplitPrimeGaussData m K p :=
  letI := Ideal.Quotient.field P
  haveI : CharP (𝓞 K ⧸ P) p :=
    Ideal.Quotient.charP_of_liesOver P Ideal.IsPrime.ne_top' p hp.out
  letI : Algebra (ZMod p) (𝓞 K ⧸ P) := ZMod.algebra _ p
  let χ := invPowerResidueMulChar m P
  have hprim := invPowerResidueMulChar_isPrimitiveRoot P hNP hcop g hg
  { P, absNorm_eq := hNP, coprime := hcop, gen := g, zpowers_gen := hg, char := χ
    root := χ (g : ZMod p), char_gen := rfl, isPrimitiveRoot_root := hprim
    mk_char_inv_gen := mk_char_inv_gen_of_eq P hNP hcop χ
      (fun t ↦ (invPowerResidueMulChar_apply P t).symm) g hprim.pow_eq_one }

/-- The character constructed by `ofIdeal` is `invPowerResidueMulChar`. -/
theorem ofIdeal_char (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hNP : Ideal.absNorm P = p) (hcop : p.Coprime m)
    (g : (ZMod p)ˣ) (hg : Subgroup.zpowers g = ⊤) [Algebra (ZMod p) (𝓞 K ⧸ P)] :
    (ofIdeal m P hNP hcop g hg).char = invPowerResidueMulChar m P := by
  unfold ofIdeal
  refine MulChar.ext fun t ↦ ?_
  simp only [invPowerResidueMulChar_apply]
  congr 2
  exact Subsingleton.elim _ _

/-- **Existence of compatible split-prime Gauss data.** In any `m`-th cyclotomic extension
`K / ℚ`, compatible split-prime Gauss data exists at every rational prime `p ≡ 1 (mod m)`. -/
theorem _root_.TauCeti.exists_splitPrimeGaussData {m : ℕ} [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    {p : ℕ} [hp : Fact p.Prime] (hm : m ∣ p - 1) :
    Nonempty (SplitPrimeGaussData m K p) := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hcop : p.Coprime m := Nat.coprime_of_dvd' fun k _ hkp hkm ↦ by
    have := Nat.dvd_sub hkp (hkm.trans hm); rwa [Nat.sub_sub_self hp1] at this
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop
  have hp_mod : (p : ZMod m) = 1 := by
    have hmod : p ≡ 1 [MOD m] := ((Nat.modEq_iff_dvd' hp1).2 hm).symm
    simpa only [← ZMod.natCast_eq_natCast_iff, Nat.cast_one] using hmod
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  obtain ⟨P, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)})
    (S := 𝓞 K)
  have hNP : Ideal.absNorm P = p := by
    rw [NumberField.absNorm_eq_pow_orderOf (n := m) (k := 0) (m := m) (by simp) hpm P, hp_mod,
      orderOf_one, pow_one]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨SplitPrimeGaussData.ofIdeal m P hNP hcop g (eq_top_iff.mpr fun x _ ↦ hg x)⟩

/-- **Transport of compatible split-prime Gauss data** along a field isomorphism
`e : K ≃+* K'`. -/
noncomputable def map {K' : Type*} [Field K'] [NumberField K']
    [HasEnoughRootsOfUnity (𝓞 K') m] (e : K ≃+* K') (d : SplitPrimeGaussData m K p) :
    SplitPrimeGaussData m K' p :=
  letI := d.isMaximal; letI := d.liesOver; let eO := NumberField.RingOfIntegers.mapRingEquiv e
  { P := d.P.map eO
    isMaximal := Ideal.map_isMaximal_of_equiv eO
    liesOver := Ideal.map_equiv_liesOver d.P (Ideal.span {(p : ℤ)}) eO.toIntAlgEquiv
    absNorm_eq := by rw [Ideal.absNorm_map_of_ringEquiv eO d.P, d.absNorm_eq]
    coprime := d.coprime, gen := d.gen, zpowers_gen := d.zpowers_gen
    char := d.char.ringHomComp eO.toRingHom, root := eO d.root
    isPrimitiveRoot_root := d.isPrimitiveRoot_root.map_of_injective eO.injective
    char_gen := by simp [MulChar.ringHomComp_apply, d.char_gen]
    mk_char_inv_gen := by
      have hinv :
          (d.char.ringHomComp eO.toRingHom)⁻¹ = d.char⁻¹.ringHomComp eO.toRingHom := by
        rw [← MulChar.ringHomComp_inv]
      rw [hinv, MulChar.ringHomComp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        ← Ideal.quotientEquiv_mk d.P (d.P.map eO) eO rfl, d.mk_char_inv_gen, map_natCast] }

/-- Transporting `SplitPrimeGaussData` along `e` maps the prime ideal `d.P` to `d.P.map eO`. -/
@[simp] theorem map_P {K' : Type*} [Field K'] [NumberField K'] [HasEnoughRootsOfUnity (𝓞 K') m]
    (e : K ≃+* K') (d : SplitPrimeGaussData m K p) :
    (d.map e).P = d.P.map (NumberField.RingOfIntegers.mapRingEquiv e) := by unfold map; rfl

/-- Transporting `SplitPrimeGaussData` along `e` preserves the generator `d.gen`. -/
@[simp] theorem map_gen {K' : Type*} [Field K'] [NumberField K'] [HasEnoughRootsOfUnity (𝓞 K') m]
    (e : K ≃+* K') (d : SplitPrimeGaussData m K p) : (d.map e).gen = d.gen := by unfold map; rfl

/-- Transporting `SplitPrimeGaussData` along `e` maps the root `d.root` via `mapRingEquiv e`. -/
@[simp] theorem map_root {K' : Type*} [Field K'] [NumberField K']
    [HasEnoughRootsOfUnity (𝓞 K') m] (e : K ≃+* K') (d : SplitPrimeGaussData m K p) :
    (d.map e).root = NumberField.RingOfIntegers.mapRingEquiv e d.root := by unfold map; rfl

/-- Transporting `SplitPrimeGaussData` along `e` postcomposes `d.char` with `mapRingEquiv e`. -/
@[simp] theorem map_char {K' : Type*} [Field K'] [NumberField K']
    [HasEnoughRootsOfUnity (𝓞 K') m] (e : K ≃+* K') (d : SplitPrimeGaussData m K p) :
    (d.map e).char = d.char.ringHomComp (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom := by
  unfold map; rfl

/-- Transporting `stickelbergerGaussProduct` along `e : K ≃+* K'` matches `d.map e`. -/
theorem map_stickelbergerGaussProduct {K' : Type*} [Field K'] [NumberField K']
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {m} ℚ K']
    (e : K ≃+* K') (d : SplitPrimeGaussData m K p)
    (x : stickelbergerDenominatorIdeal m) :
    letI := d.isMaximal; letI := (d.map e).isMaximal
    e (stickelbergerGaussProduct m K d.P d.absNorm_coprime (Multiplicative.ofAdd x) : K) =
      (stickelbergerGaussProduct m K' (d.map e).P (d.map e).absNorm_coprime
        (Multiplicative.ofAdd x) : K') :=
  have := d.isMaximal; have := (d.map e).isMaximal
  TauCeti.map_stickelbergerGaussProduct m d.P d.absNorm_coprime (d.map e).absNorm_coprime rfl x

/-- **Galois transport of compatible split-prime Gauss data** by `τ : Gal(K/ℚ)`. -/
noncomputable def smul (τ : Gal(K/ℚ)) (d : SplitPrimeGaussData m K p) :
    SplitPrimeGaussData m K p := d.map τ.toRingEquiv

/-- Galois transport `d.smul τ` acts on the underlying prime ideal by `τ • d.P`. -/
@[simp] theorem smul_P (τ : Gal(K/ℚ)) (d : SplitPrimeGaussData m K p) :
    (d.smul τ).P = τ • d.P := by simp [smul]

/-- Galois transport `d.smul τ` raises `d.char` to the cyclotomic power
`(galEquivZMod m K τ : ZMod m).val`. -/
theorem smul_char [IsCyclotomicExtension {m} ℚ K] (τ : Gal(K/ℚ))
    (d : SplitPrimeGaussData m K p) :
    (d.smul τ).char = d.char ^ (galEquivZMod m K τ : ZMod m).val := by
  refine MulChar.ext fun t ↦ ?_
  have hact := galEquivZMod_apply_of_pow_eq m K τ
    (by rw [← map_pow (algebraMap (𝓞 K) K), char_pow_eq_one d t, map_one])
  have hO : NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv (d.char (t : ZMod p)) =
      d.char (t : ZMod p) ^ (galEquivZMod m K τ : ZMod m).val :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K (by
      simpa only [map_pow] using
        (show algebraMap (𝓞 K) K
          (NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv (d.char (t : ZMod p))) =
          τ (algebraMap (𝓞 K) K (d.char (t : ZMod p))) from rfl).trans hact)
  simpa [smul, MulChar.pow_apply_coe] using hO

/-- **Generator reindexing at a fixed prime ideal.** Replacing `d.gen` by another generator `g'`
of `(ZMod p)ˣ` preserves `d.P` and `d.char`, updating `root` to `d.char g'`. -/
noncomputable def withGen (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) : SplitPrimeGaussData m K p :=
  have := d.isMaximal; have := d.liesOver
  ofIdeal m d.P d.absNorm_eq d.coprime g' hg'

/-- Reindexing the generator preserves `d.P`. -/
@[simp] theorem withGen_P (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) : (d.withGen g' hg').P = d.P := by unfold withGen ofIdeal; rfl

/-- Reindexing the generator updates `gen` to `g'`. -/
@[simp] theorem withGen_gen (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) : (d.withGen g' hg').gen = g' := by unfold withGen ofIdeal; rfl

/-- Reindexing the generator preserves `d.char`. -/
@[simp] theorem withGen_char (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) : (d.withGen g' hg').char = d.char := by
  have := d.isMaximal; have := d.liesOver; let _ := Ideal.Quotient.field d.P
  have : CharP (𝓞 K ⧸ d.P) p :=
    Ideal.Quotient.charP_of_liesOver d.P Ideal.IsPrime.ne_top' p hp.out
  let _ : Algebra (ZMod p) (𝓞 K ⧸ d.P) := ZMod.algebra _ p
  exact (ofIdeal_char d.P d.absNorm_eq d.coprime g' hg').trans
    d.char_eq_invPowerResidueMulChar.symm

/-- Reindexing the generator updates `root` to `d.char g'`. -/
@[simp] theorem withGen_root (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) : (d.withGen g' hg').root = d.char (g' : ZMod p) := by
  rw [← (d.withGen g' hg').char_gen, withGen_gen, withGen_char]

/-- Any two compatible split-prime data over the same prime ideal have the same character,
independently of the chosen generator. -/
theorem char_eq_of_P_eq (d₁ d₂ : SplitPrimeGaussData m K p) (hP : d₁.P = d₂.P) :
    d₁.char = d₂.char := by
  rcases d₁ with ⟨P₁, hmax₁, hlo₁, hNP₁, hcop₁, g₁, hg₁, χ₁, ζ₁, hprim₁, hχg₁, hmk₁⟩
  rcases d₂ with ⟨P₂, hmax₂, hlo₂, hNP₂, hcop₂, g₂, hg₂, χ₂, ζ₂, hprim₂, hχg₂, hmk₂⟩
  dsimp only at hP; subst hP
  have := hmax₁; have := hlo₁; let _ := Ideal.Quotient.field P₁
  have : CharP (𝓞 K ⧸ P₁) p :=
    Ideal.Quotient.charP_of_liesOver P₁ Ideal.IsPrime.ne_top' p hp.out
  let _ : Algebra (ZMod p) (𝓞 K ⧸ P₁) := ZMod.algebra _ p
  exact (SplitPrimeGaussData.char_eq_invPowerResidueMulChar
      ⟨P₁, hmax₁, hlo₁, hNP₁, hcop₁, g₁, hg₁, χ₁, ζ₁, hprim₁, hχg₁, hmk₁⟩).trans
    (SplitPrimeGaussData.char_eq_invPowerResidueMulChar
      ⟨P₁, hmax₂, hlo₂, hNP₂, hcop₂, g₂, hg₂, χ₂, ζ₂, hprim₂, hχg₂, hmk₂⟩).symm

/-- Changing the generator to `g' = d.gen ^ k` with `k ≡ 1 (mod m)` preserves `d.root`. -/
theorem withGen_root_eq_of_zpow (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ)
    (hg' : Subgroup.zpowers g' = ⊤) {k : ℤ} (hg'k : g' = d.gen ^ k) (hk : (k : ZMod m) = 1) :
    (d.withGen g' hg').root = d.root := by
  have h1 : d.char.toUnitHom d.gen ^ k = d.char.toUnitHom d.gen := by
    rw [zpow_eq_zpow_emod' k (char_unitHom_pow_eq_one d),
      (ZMod.intCast_eq_intCast_iff' k 1 m).mp (by simpa using hk),
      ← zpow_eq_zpow_emod' 1 (char_unitHom_pow_eq_one d), zpow_one]
  rw [withGen_root]
  change (d.char.toUnitHom g' : 𝓞 K) = d.root
  rw [hg'k, map_zpow, h1]
  exact d.char_gen

/-- **Simultaneous Galois and generator reindexing.** Applying `τ : Gal(K/ℚ)` to `d.P` while
replacing `d.gen` by a generator `g'` with `g' ^ k = d.gen` and
`(k : ZMod m) = galEquivZMod m K τ` preserves the primitive `m`-th root `d.root`. -/
theorem smul_withGen_root_eq [IsCyclotomicExtension {m} ℚ K] (τ : Gal(K/ℚ))
    (d : SplitPrimeGaussData m K p) (g' : (ZMod p)ˣ) (hg' : Subgroup.zpowers g' = ⊤)
    {k : ℤ} (hgk : g' ^ k = d.gen) (hk : (k : ZMod m) = galEquivZMod m K τ) :
    ((d.smul τ).withGen g' hg').root = d.root := by
  have hm_pow : d.char.toUnitHom g' ^ m = 1 := by
    simpa using char_unitHom_pow_eq_one (d.withGen g' hg')
  have hpow : d.char.toUnitHom g' ^ ((galEquivZMod m K τ : ZMod m).val : ℤ) =
      d.char.toUnitHom g' ^ k := by
    rw [zpow_eq_zpow_emod' _ hm_pow, zpow_eq_zpow_emod' k hm_pow,
      (ZMod.intCast_eq_intCast_iff' _ k m).mp (by simp [hk])]
  rw [withGen_root, smul_char, MulChar.pow_apply_coe]
  change ((d.char.toUnitHom g' ^ (galEquivZMod m K τ : ZMod m).val : (𝓞 K)ˣ) : 𝓞 K) = _
  rw [← zpow_natCast, hpow, ← map_zpow, hgk]
  exact d.char_gen

end SplitPrimeGaussData

end SplitPrime

end TauCeti
