/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Norm
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.RingTheory.Norm.Units
import TauCeti.RingTheory.RootsOfUnity.Coprime

/-!
# The cyclotomic character of the local Artin symbols of `ℚ_p`

This file proves the cyclotomic normalization of the absolute local Artin map of `ℚ_p` on units:
if `σ ∈ G_{ℚ_p}` represents `Art_{ℚ_p}(u)` for `u ∈ ℤ_pˣ`, then `χ_cyc(σ) = u⁻¹`
(`localCyclotomicCharacter_artinMap_padic`). It is the comparison of `Art_{ℚ_p}` with the explicit
local symbols of the cyclotomic fields: no reciprocity law and no Lubin–Tate theory enters.

## Main results

* `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic`: the `p`-adic cyclotomic
  character of the absolute Artin symbol of `u ∈ ℤ_pˣ` over `ℚ_[p]` is `u⁻¹`.

## The argument

Fix `n`, let `f = φ(p^n)`, `N = p^f − 1`, `m = p^n N` and `L = ℚ_p(μ_m)`. Let `τ` represent
`Art_{ℚ_p}(p)` and `g = τ σ`, which represents `Art_{ℚ_p}(p u)`. Since `p u` is a uniformizer,
`g` is an arithmetic Frobenius lift and acts on `μ_N` by `ζ ↦ ζ ^ p`; since `(ℤ/p^n)ˣ` has order
`f`, `g ^ f` fixes `μ_{p^n}`. Let `M ⊆ L` be the fixed field of `g`. As `g` fixes `M` and
represents the Artin symbol of `p u`, `p u` is a norm from `M` (`mem_normGroup_of_mk_eq_artinMap`).
Choose `ρ` with `χ_cyc(ρ) = u⁻¹` acting on `μ_N` by `ζ ↦ ζ ^ p`
(`exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one`); it acts on `μ_m` through
`cyclotomicSymbol m p (p u)`, so it fixes `M` (`cyclotomicSymbol_norm_fixes`). By the Galois
correspondence in `L`, `ρ` restricts to a power `g ^ k`, and comparing the two on a primitive
`N`-th root of unity gives `k ≡ 1` modulo `f`. Hence `g` and `ρ` agree on `μ_{p^n}`, and so do `σ`
and `ρ`, because `τ` fixes `μ_{p^n}` (`localCyclotomicCharacter_artinMap_padic_uniformizer`).

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Example 8.2, for the explicit local symbols of
  the cyclotomic fields over `ℚ`.
-/

public section

namespace TauCeti.ClassFieldTheory

open _root_.ValuativeRel

variable (p : ℕ) [Fact p.Prime]

/-! `Field.absoluteGaloisGroup ℚ_[p]` is a plain definition, so its elements act on
`AlgebraicClosure ℚ_[p]` only through an explicit coercion via
`Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])`, whose group laws it carries by definition. The next lemmas
record the facts about this action that the comparison uses. -/

private theorem absoluteGaloisGroup_mul_apply (a b : Field.absoluteGaloisGroup ℚ_[p])
    (w : AlgebraicClosure ℚ_[p]) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (a * b) w =
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a
        (DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) b w) :=
  AlgEquiv.mul_apply (A₁ := AlgebraicClosure ℚ_[p]) a b w

private theorem absoluteGaloisGroup_one_apply (w : AlgebraicClosure ℚ_[p]) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (1 : Field.absoluteGaloisGroup ℚ_[p]) w =
      w :=
  AlgEquiv.one_apply (A₁ := AlgebraicClosure ℚ_[p]) w

private theorem absoluteGaloisGroup_apply_one (a : Field.absoluteGaloisGroup ℚ_[p]) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a 1 = 1 :=
  map_one (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a

private theorem absoluteGaloisGroup_apply_pow (a : Field.absoluteGaloisGroup ℚ_[p])
    (w : AlgebraicClosure ℚ_[p]) (j : ℕ) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a (w ^ j) =
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a w ^ j :=
  map_pow (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a w j

/-- The class of `p` modulo `p ^ f - 1` has order `f`, read on a primitive `(p ^ f - 1)`-st root of
unity `ζ`: if `ζ ^ p = ζ ^ p ^ r` with `r < f`, then `r ≡ 1 [MOD f]`. -/
private theorem eq_one_mod_of_pow_eq_pow_pow {M : Type*} [CommMonoid M] {f r : ℕ} (hr : r < f)
    {ζ : M} (hζ : IsPrimitiveRoot ζ (p ^ f - 1)) (h : ζ ^ p = ζ ^ p ^ r) : r = 1 % f := by
  have hp := (Fact.out : p.Prime).two_le
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
  · omega
  have hsucc : p ^ f = p * p ^ (f - 1) := by rw [← pow_succ']; congr 1; omega
  have h2' : p ≤ p ^ (f - 1) := Nat.le_self_pow (by omega) p
  have hlt : p ^ (f - 1) < p ^ f - 1 := by
    have : 2 * p ^ (f - 1) ≤ p * p ^ (f - 1) := Nat.mul_le_mul_right _ hp
    omega
  have hpr : p ^ r < p ^ f - 1 :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hlt
  have : r = 1 := Nat.pow_right_injective hp
    (by simpa using (hζ.pow_inj (h2'.trans_lt hlt) hpr h).symm)
  rw [this, Nat.mod_eq_of_lt (by omega)]

/-- Two elements of `G_{ℚ_p}` whose cyclotomic characters agree modulo `p ^ n` agree on the
`p ^ n`-th roots of unity. -/
private theorem apply_eq_apply_of_toZModPow_eq {σ₁ σ₂ : Field.absoluteGaloisGroup ℚ_[p]} {n : ℕ}
    (h : PadicInt.toZModPow n (localCyclotomicCharacter p ℚ_[p] σ₁ : ℤ_[p]) =
      PadicInt.toZModPow n (localCyclotomicCharacter p ℚ_[p] σ₂ : ℤ_[p]))
    {z : AlgebraicClosure ℚ_[p]} (hz : z ^ p ^ n = 1) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ₁ z =
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ₂ z := by
  rw [localCyclotomicCharacter_apply, localCyclotomicCharacter_apply] at h
  exact (cyclotomicCharacter.spec p σ₁.toRingEquiv z hz).trans
    (h ▸ (cyclotomicCharacter.spec p σ₂.toRingEquiv z hz).symm)

/-- `p u` is a uniformizer of `ℚ_[p]` for every `u ∈ ℤ_pˣ`. -/
private theorem isUniformizer_mul_unit (u : ℤ_[p]ˣ) :
    IsUniformizer ℚ_[p] (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) *
      Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) := by
  rw [isUniformizer_def, map_mul, (isUniformizer_def _).1 (Padic.isUniformizer_natCast_self p),
    mul_eq_left]
  apply Multiplicative.toAdd.injective
  have h := PadicInt.valuation_mul u.ne_zero u⁻¹.ne_zero
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, toAdd_one, PadicInt.algebraMap_apply, PadicInt.valuation_coe]
  omega

/-- Every `φ(p ^ n)`-th power in `G_{ℚ_p}` fixes the `p ^ n`-th roots of unity, because `(ℤ/p^n)ˣ`
has order `φ(p ^ n)`. -/
private theorem pow_totient_mul_apply_eq_self (g : Field.absoluteGaloisGroup ℚ_[p]) {n : ℕ}
    (q : ℕ) {w : AlgebraicClosure ℚ_[p]} (hw : w ^ p ^ n = 1) :
    DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ ((p ^ n).totient * q)) w = w := by
  refine (apply_eq_apply_of_toZModPow_eq p (σ₂ := 1) ?_ hw).trans
    (absoluteGaloisGroup_one_apply p w)
  have h := ZMod.pow_totient (Units.map (PadicInt.toZModPow n).toMonoidHom
    (localCyclotomicCharacter p ℚ_[p] g))
  have h1 : PadicInt.toZModPow n (localCyclotomicCharacter p ℚ_[p] g : ℤ_[p]) ^
      (p ^ n).totient = 1 := by
    have := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one] at this
  rw [map_pow, map_one, pow_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_pow_eq_pow_val,
    map_pow, h1, one_pow, Units.val_one, map_one]

/-- An element `ρ ∈ G_{ℚ_p}` with `χ_cyc(ρ) = u⁻¹` that acts on the `N`-th roots of unity by
`ζ ↦ ζ ^ p`, for `N` prime to `p`, acts on the `p ^ n N`-th roots of unity through the explicit
symbol of `p u`. -/
private theorem apply_eq_pow_cyclotomicSymbol (u : ℤ_[p]ˣ) {n N : ℕ} [NeZero (p ^ n * N)]
    (hN : p.Coprime N) {ρ : Field.absoluteGaloisGroup ℚ_[p]}
    (hρχ : localCyclotomicCharacter p ℚ_[p] ρ = u⁻¹)
    (hρN : ∀ w : AlgebraicClosure ℚ_[p], w ^ N = 1 →
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ w = w ^ p)
    {w : AlgebraicClosure ℚ_[p]} (hw : w ^ (p ^ n * N) = 1) :
    ρ.toRingEquiv w = w ^ ((cyclotomicSymbol (p ^ n * N) p
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) *
        Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) : ZMod (p ^ n * N)).val) := by
  set x := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) *
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  have hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ (1 : ℤ) * ((u : ℤ_[p]) : ℚ_[p]) := by simp [x]
  refine (ρ.toRingEquiv : AlgebraicClosure ℚ_[p] →* _).map_eq_pow_of_coprime (hN.pow_left n)
    (fun w hw ↦ ?_) (fun w hw ↦ ?_) hw
  · -- On `μ_{p^n}` the symbol is `u⁻¹`, the cyclotomic character of `ρ`.
    have hval := congrArg (fun v : (ZMod (p ^ n))ˣ ↦ (v : ZMod (p ^ n)).val)
      (unitsMap_cyclotomicSymbol_primePow (p ^ n * N) p (dvd_mul_right (p ^ n) N) x 1 u hx)
    simp only [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast] at hval
    rw [pow_eq_pow_mod _ hw, hval]
    refine (cyclotomicCharacter.spec p ρ.toRingEquiv w hw).trans ?_
    rw [← localCyclotomicCharacter_apply, hρχ]
    simp
  · -- On `μ_N` the symbol is `p`.
    have hval := congrArg (fun v : (ZMod N)ˣ ↦ (v : ZMod N).val)
      (unitsMap_cyclotomicSymbol_of_coprime (p ^ n * N) p (dvd_mul_left N (p ^ n)) hN x 1 u hx)
    simp only [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast, zpow_one,
      ZMod.coe_unitOfCoprime] at hval
    rw [pow_eq_pow_mod _ hw, hval, ← pow_eq_pow_mod _ hw]
    exact hρN w hw

/-- The comparison at level `p ^ n`: if `σ` represents the Artin symbol of the unit `u`, then some
`ρ` with `χ_cyc(ρ) = u⁻¹` agrees with `σ` on the `p ^ n`-th roots of unity. -/
private theorem exists_localCyclotomicCharacter_eq_inv_and_apply_eq (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u))
    (n : ℕ) : ∃ ρ : Field.absoluteGaloisGroup ℚ_[p], localCyclotomicCharacter p ℚ_[p] ρ = u⁻¹ ∧
      ∀ z : AlgebraicClosure ℚ_[p], z ^ p ^ n = 1 →
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ z =
          DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ z := by
  have hp := (Fact.out : p.Prime)
  set f := (p ^ n).totient
  have hf : f ≠ 0 := (Nat.totient_pos.2 (pow_pos hp.pos n)).ne'
  set N := p ^ f - 1
  have hpf : 1 < p ^ f := Nat.one_lt_pow hf hp.one_lt
  have hcopN : p.Coprime N := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ hp.one_lt.ne' ?_
    have h1 := Nat.dvd_sub (dvd_pow_self p hf) h
    rw [Nat.sub_sub_self hpf.le] at h1
    exact Nat.eq_one_of_dvd_one h1
  set m := p ^ n * N with hm_def
  have hN0 : 0 < N := Nat.sub_pos_of_lt hpf
  have hm0 : 0 < m := Nat.mul_pos (pow_pos hp.pos n) hN0
  have : NeZero m := ⟨hm0.ne'⟩
  -- The comparison element: `u⁻¹` on `μ_{p^n}`, Frobenius on `μ_N`.
  obtain ⟨ρ, hρχ, hρN⟩ := exists_localCyclotomicCharacter_eq_and_apply_of_pow_eq_one p u⁻¹ hf
  refine ⟨ρ, hρχ, fun z hz ↦ ?_⟩
  -- A lift `τ` of `Art(p)` and the lift `g = τ σ` of `Art(p u)`.
  set π := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 hp.ne_zero)
  set u' := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap ℚ_[p] π)
  have hτχ := localCyclotomicCharacter_artinMap_padic_uniformizer p τ hτ
  set g := τ * σ
  have hg : (g : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p] (π * u') := by
    rw [map_mul, ← hτ, ← hσ, QuotientGroup.mk_mul]
  have hpow (w : AlgebraicClosure ℚ_[p]) (hw : w ^ N = 1) : w ^ p ^ f = w := by
    rw [← Nat.sub_add_cancel hpf.le, pow_succ, hw, one_mul]
  have hgN (w : AlgebraicClosure ℚ_[p]) (hw : w ^ N = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g w = w ^ p := by
    simpa using isArithFrobeniusLift_iff.1
      (isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer ℚ_[p] (isUniformizer_mul_unit p u) g
        hg) w f hf
      (by simpa using hpow w hw)
  -- `g ^ i` acts on `μ_N` by `w ↦ w ^ p ^ i`.
  have hgNpow (i : ℕ) (w : AlgebraicClosure ℚ_[p]) (hw : w ^ N = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ i) w = w ^ p ^ i := by
    induction i generalizing w with
    | zero => rw [pow_zero, pow_zero, pow_one, absoluteGaloisGroup_one_apply]
    | succ i ih =>
      rw [pow_succ, absoluteGaloisGroup_mul_apply, hgN w hw,
        ih _ (by rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]), ← pow_mul, pow_succ, mul_comm]
  -- The field `L = ℚ_p(μ_m)` and the fixed field `M` of `g` in it.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ_[p]) m
  set L := IntermediateField.adjoin ℚ_[p] {ζ}
  have := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have := IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] L
  have := IsCyclotomicExtension.isGalois {m} ℚ_[p] L
  have := IsCyclotomicExtension.isMulCommutative {m} ℚ_[p] L
  have hmemL (w : AlgebraicClosure ℚ_[p]) (hw : w ^ m = 1) : w ∈ L := by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  let rL : Field.absoluteGaloisGroup ℚ_[p] →* Gal(L/ℚ_[p]) := AlgEquiv.restrictNormalHom L
  have hrL (a : Field.absoluteGaloisGroup ℚ_[p]) (w : L) :
      (rL a w : AlgebraicClosure ℚ_[p]) =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) a (w : AlgebraicClosure ℚ_[p]) :=
    AlgEquiv.restrictNormalHom_apply L a w
  set H := Subgroup.zpowers (rL g)
  set M₁ := IntermediateField.fixedField H
  have hgM (x : M₁) : rL g x = x := (IntermediateField.mem_fixedField_iff H _).1 x.2 _
    (Subgroup.mem_zpowers _)
  -- `p u` is a norm from `M`, because `g` represents its Artin symbol and fixes `M`.
  set M := IntermediateField.lift M₁
  have : FiniteDimensional ℚ_[p] M :=
    (IntermediateField.liftAlgEquiv M₁).toLinearEquiv.finiteDimensional
  have : IsGalois ℚ_[p] M := IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv M₁)
  obtain ⟨y, hy⟩ := mem_normGroup_iff.1 <| mem_normGroup_of_mk_eq_artinMap ℚ_[p] M (π * u') g hg
    fun x ↦ by
      obtain ⟨x, rfl⟩ := (IntermediateField.liftAlgEquiv M₁).surjective x
      rw [IntermediateField.liftAlgEquiv_apply, ← hrL g x, hgM x]
  replace hy : Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y = π * u' := Units.ext hy
  -- `ρ` acts on `μ_m` through the symbol of `p u = N_{M/ℚ_p}(y)`, so it fixes `M`.
  have hM : M ≤ IntermediateField.adjoin ℚ_[p] {w : AlgebraicClosure ℚ_[p] | w ^ m = 1} :=
    (IntermediateField.lift_le M₁).trans <| IntermediateField.adjoin_simple_le_iff.2
      (IntermediateField.subset_adjoin _ _ hζ.pow_eq_one)
  have hρm (w : AlgebraicClosure ℚ_[p]) (hw : w ^ m = 1) : ρ.toRingEquiv w =
      w ^ ((cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y) :
        ZMod m).val) := by
    rw [hy]
    exact apply_eq_pow_cyclotomicSymbol p u hcopN hρχ hρN hw
  have hρM := cyclotomicSymbol_norm_fixes p m M hM y ρ hρm
  -- So `ρ` restricts to a power `g ^ k` on `L`.
  have hρH : rL ρ ∈ H := by
    rw [← IntermediateField.fixingSubgroup_fixedField H]
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ Subtype.ext ?_
    exact (hrL ρ x).trans (hρM ⟨(x : AlgebraicClosure ℚ_[p]), (IntermediateField.mem_lift x).2 hx⟩)
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hρH)
  replace hk : rL g ^ k = rL ρ := hk
  have hρg (w : AlgebraicClosure ℚ_[p]) (hw : w ^ m = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ w =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ k) w := by
    rw [← hrL ρ ⟨w, hmemL w hw⟩, ← hk, ← map_pow, hrL]
  -- Comparing `ρ` and `g ^ k` on a primitive `N`-th root of unity gives `k ≡ 1 [MOD f]`.
  have hpowq (v : AlgebraicClosure ℚ_[p]) (hv : v ^ N = 1) (q : ℕ) : v ^ p ^ (f * q) = v := by
    induction q with
    | zero => simp
    | succ q ih => rw [mul_add, mul_one, pow_add, pow_mul, ih, hpow v hv]
  set r := k % f
  have hk' : g ^ k = g ^ (f * (k / f)) * g ^ r := by rw [← pow_add, Nat.div_add_mod]
  have hgr (w : AlgebraicClosure ℚ_[p]) (hw : w ^ N = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ k) w = w ^ p ^ r := by
    rw [hk', absoluteGaloisGroup_mul_apply, hgNpow r w hw,
      hgNpow _ _ (by rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]), ← pow_mul, mul_comm, pow_mul,
      hpowq w hw]
  have hζN : IsPrimitiveRoot (ζ ^ p ^ n) N := hζ.pow hm0 hm_def
  have hζNeq : (ζ ^ p ^ n) ^ p = (ζ ^ p ^ n) ^ p ^ r :=
    (hρN _ hζN.pow_eq_one).symm.trans
      ((hρg _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])).trans
      (hgr _ hζN.pow_eq_one))
  have hr1 : r = 1 % f := eq_one_mod_of_pow_eq_pow_pow p (Nat.mod_lt _ (by omega)) hζN hζNeq
  -- Hence `g` acts on `μ_{p^n}` as `ρ`, and so does `σ`, because `τ` fixes `μ_{p^n}`.
  have hgz' (w : AlgebraicClosure ℚ_[p]) (hw : w ^ p ^ n = 1) (i : ℕ) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ i) w ^ p ^ n = 1 := by
    rw [← absoluteGaloisGroup_apply_pow, hw, absoluteGaloisGroup_apply_one]
  have hgz : DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g z =
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ z := by
    calc _ = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]))
          (g ^ (f * (1 / f)) * g ^ (1 % f)) z := by rw [← pow_add, Nat.div_add_mod, pow_one]
      _ = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ r) z := by
          rw [absoluteGaloisGroup_mul_apply, pow_totient_mul_apply_eq_self p g _ (hgz' z hz _), hr1]
      _ = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ k) z := by
          rw [hk', absoluteGaloisGroup_mul_apply, pow_totient_mul_apply_eq_self p g _ (hgz' z hz _)]
      _ = _ := (hρg z (by rw [hm_def, pow_mul, hz, one_pow])).symm
  have hτz : DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) τ
      (DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ z) =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ z :=
    (apply_eq_apply_of_toZModPow_eq p (σ₂ := 1) (by rw [hτχ, map_one])
      (by rw [← absoluteGaloisGroup_apply_pow, hz, absoluteGaloisGroup_apply_one])).trans
        (absoluteGaloisGroup_one_apply p _)
  exact hτz.symm.trans hgz

/-- **The cyclotomic normalization at `ℚ_p`**: `χ_cyc(Art_{ℚ_p}(u)) = u⁻¹` for `u ∈ ℤ_pˣ`. If `σ`
in the absolute Galois group of `ℚ_[p]` represents the absolute local Artin symbol of the unit `u`,
then its `p`-adic cyclotomic character is `u⁻¹`. -/
theorem localCyclotomicCharacter_artinMap_padic (u : ℤ_[p]ˣ)
    (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      artinMap ℚ_[p] (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    localCyclotomicCharacter p ℚ_[p] σ = u⁻¹ := by
  obtain ⟨ρ₀, hρ₀⟩ := surjective_localCyclotomicCharacter_ratPadic p u⁻¹
  rw [← hρ₀, localCyclotomicCharacter_apply, localCyclotomicCharacter_apply]
  refine cyclotomicCharacter_eq_of_forall_pow_eq_one p fun n t ht ↦ ?_
  obtain ⟨ρ, hρ, hσρ⟩ := exists_localCyclotomicCharacter_eq_inv_and_apply_eq p u σ hσ n
  exact (hσρ t ht).trans (apply_eq_apply_of_toZModPow_eq p (by rw [hρ, hρ₀]) ht)

end TauCeti.ClassFieldTheory
