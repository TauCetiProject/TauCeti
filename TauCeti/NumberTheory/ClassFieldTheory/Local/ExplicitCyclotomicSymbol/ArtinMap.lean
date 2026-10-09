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
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

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
  have hcopN : p.Coprime N :=
    ((Nat.coprime_self_sub_right hpf.le).2 (Nat.coprime_one_right _)).coprime_dvd_left
      (dvd_pow_self p hf)
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
      (isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer ℚ_[p]
        (Padic.isUniformizer_natCast_self_mul_unit p u) g hg) w f hf
      (by simpa using hpow w hw)
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
  have hρH : rL ρ ∈ H := AlgEquiv.restrictNormalHom_mem_of_forall_mem_fixedField L fun x hx ↦
    hρM ⟨(x : AlgebraicClosure ℚ_[p]), (IntermediateField.mem_lift x).2 hx⟩
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hρH)
  have hρg (w : AlgebraicClosure ℚ_[p]) (hw : w ^ m = 1) :
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ w =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ k) w := by
    rw [← hrL ρ ⟨w, hmemL w hw⟩, ← hk, ← map_pow, hrL]
  -- Comparing `ρ` and `g ^ k` on a primitive `N`-th root of unity gives `1 ≡ k [MOD f]`.
  have hζN : IsPrimitiveRoot (ζ ^ p ^ n) N := hζ.pow hm0 hm_def
  have hk1 : 1 ≡ k [MOD f] := hζN.modEq_of_pow_pow_eq_pow_pow hp.one_lt hf <| by
    rw [pow_one, ← hρN _ hζN.pow_eq_one,
      hρg _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]),
      absoluteGaloisGroup_pow_apply_eq_pow_pow hgN k hζN.pow_eq_one]
  -- Hence `g = g ^ 1` acts on `μ_{p^n}` as `g ^ k`, that is as `ρ`; so does `σ`, because `τ` fixes
  -- `μ_{p^n}`.
  have hgz : DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) g z =
      DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) ρ z := by
    calc _ = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ 1) z :=
          (pow_one g).symm ▸ rfl
      _ = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) (g ^ k) z :=
          apply_pow_eq_apply_pow_of_modEq_totient g hk1 hz
      _ = _ := (hρg z (by rw [hm_def, pow_mul, hz, one_pow])).symm
  have hτz : DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) τ
      (DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ z) =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ z :=
    apply_eq_self_of_toZModPow_localCyclotomicCharacter_eq_one
      (by rw [hτχ, Units.val_one, map_one])
      (by rw [← map_pow (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ, hz,
        map_one (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ])
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
  exact (hσρ t ht).trans
    (apply_eq_apply_of_toZModPow_localCyclotomicCharacter_eq (by rw [hρ, hρ₀]) ht)

end TauCeti.ClassFieldTheory
