/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Valuation.Discrete.Order

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Multiplicity
import TauCeti.RingTheory.LocalRing.Basic
import TauCeti.RingTheory.Valuation.NontrivialComap

/-!
# Rigidity of discrete valuations over Henselian local rings with finite residue field

Let `R` be a Henselian local ring whose residue field `k` is finite. Every multiplicative
homomorphism `f : Rˣ →* Multiplicative ℤ` is trivial: at least one of `2` or `3` is invertible in
`R` (since `3 - 2 = 1 ≠ 0` in `k`), so Hensel's lemma makes every principal unit `w ∈ 1 + 𝔪`
infinitely divisible by `2` or `3` in `Rˣ`, killing `f` on `1 + 𝔪`; raising an arbitrary unit to
the `#kˣ`-th power lands in `1 + 𝔪` and kills `f` on all of `Rˣ` (the target `Multiplicative ℤ`
cannot be relaxed to an arbitrary torsion-free abelian group such as `Multiplicative ℚ`, since for
odd `p` the `p`-adic logarithm embeds `1 + pℤ_p` as an open subgroup of `ℚ_p` and hence admits
nontrivial homomorphisms to `ℚ`). In particular, every `ℤᵐ⁰`-valued valuation on `R` takes the
value `1` on `Rˣ`.

For any field `K` carrying a `ValuativeRel` whose valuation ring `𝒪` is a discrete valuation ring,
a nontrivial valuation `v` on `K` (valued in an arbitrary linearly ordered commutative group with
zero) that sends every unit of `𝒪` to `1` is automatically equivalent to `valuation K`: on an
irreducible element `ϖ` of `𝒪`, the value `v ϖ = 1` would make `v` trivial on `𝒪` and hence on `K`,
while `1 < v ϖ` would force `v (1 + ϖ) = v ϖ > 1` against `1 + ϖ ∈ 𝒪ˣ`, leaving `v ϖ < 1` and
therefore `v x ≤ 1 ↔ x ∈ 𝒪`.

Combining the two steps gives F. K. Schmidt's discrete-valuation rigidity when `𝒪` is a Henselian
discrete valuation ring with finite residue field: every nontrivial `ℤᵐ⁰`-valued valuation on `K`
is equivalent to `valuation K`, and every algebraic field extension `L / K` carrying a nontrivial
rank-one discrete `ValuativeRel` is automatically a `ValuativeExtension K L`. Each hypothesis on
`K` and `L` is sharp:
* without Henselianity, `ℚ` carries inequivalent `p`-adic valuations;
* without finiteness of the residue field, the Henselization `ℚ(t)_{(t)}^h` embeds algebraically
  into `ℚ_p` via a transcendental `p`-adic unit, pulling back a `p`-adic valuation inequivalent to
  the `t`-adic one;
* without discreteness on `L`, pulling back the `ℓ`-adic valuation of `AlgebraicClosure ℚ_[ℓ]`
  along an abstract embedding of the algebraic part of `ℚ_[p]` into `AlgebraicClosure ℚ_[ℓ]`
  (`ℓ ≠ p`) gives an incompatible valuation on that Henselian discrete base;
* without rank at most one on `L`, a rank-two discrete valuation refining `valuation K` has strictly
  smaller unit ball;
* without algebraicity of `L / K`, the `t`-adic valuation of `K(t)` restricts trivially to `K`.

## Main results

* `MonoidHom.eq_one_of_henselianLocalRing`: every homomorphism `Rˣ →* Multiplicative ℤ` from the
  units of a Henselian local ring with finite residue field is trivial.
* `Valuation.map_units_eq_one_of_henselianLocalRing`,
  `Valuation.map_eq_one_of_henselianLocalRing`, and
  `Valuation.ord_eq_zero_of_henselianLocalRing`: every `ℤᵐ⁰`-valuation on `R` sends units to `1`
  (and has additive order `0` on units).
* `Valuation.isEquiv_valuation_of_map_units_eq_one`: on a field `K` whose valuation ring is a
  discrete valuation ring, any nontrivial valuation trivial on `(valuation K).integerˣ` is
  equivalent to `valuation K`.
* `Valuation.isEquiv_valuation_of_henselianLocalRing`: when `(valuation K).integer` is moreover
  Henselian with finite residue field, every nontrivial `ℤᵐ⁰`-valuation on `K` is equivalent to
  `valuation K`.
* `ValuativeExtension.of_henselianLocalRing`: every algebraic extension `L / K` with a nontrivial
  rank-one discrete `ValuativeRel` is automatically a `ValuativeExtension K L`.
* `RingHom.map_vle_map_iff_of_henselianLocalRing`,
  `RingEquiv.map_vle_map_iff_of_henselianLocalRing`, and
  `ValuativeRel.eq_of_henselianLocalRing`: automatic valuation compatibility of algebraic
  homomorphisms, abstract ring isomorphisms, and uniqueness of the nontrivial rank-one discrete
  `ValuativeRel` on `K`.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. **108** (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Theorem 4.4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section

open scoped WithZero
open IsLocalRing ValuativeRel

section HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- In a Henselian local ring, every homomorphism `Rˣ →* Multiplicative ℤ` kills the principal
units `{u : Rˣ | residue R u = 1}`. -/
private theorem MonoidHom.apply_eq_one_of_residue_eq_one (f : Rˣ →* Multiplicative ℤ) {u : Rˣ}
    (hu : residue R (u : R) = 1) : f u = 1 := by
  have ⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ IsUnit (ℓ : R) := by
    by_cases h2 : IsUnit ((2 : ℕ) : R)
    · exact ⟨2, le_rfl, h2⟩
    · exact ⟨3, by decide, Nat.Coprime.isUnit_natCast (n := 2) (by decide) h2⟩
  suffices h : (f u).toAdd = 0 from Multiplicative.toAdd.injective h
  by_contra h0
  refine FiniteMultiplicity.not_iff_forall.mpr (fun m ↦ ?_)
    ((Int.finiteMultiplicity_iff (a := (ℓ : ℤ))).mpr ⟨by simp; omega, h0⟩)
  obtain ⟨x, hx, hres⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq (n := ℓ ^ m)
    (by simpa using hℓ.pow m) isUnit_one (u := (u : R)) (by simp [hu])
  have hx_unit : IsUnit x := by
    rw [← residue_ne_zero_iff_isUnit, hres, map_one]
    exact one_ne_zero
  obtain ⟨y, rfl⟩ := hx_unit
  have hy : y ^ ℓ ^ m = u := Units.ext (by simpa using hx)
  refine ⟨(f y).toAdd, ?_⟩
  rw [← hy, map_pow, toAdd_pow, nsmul_eq_mul, Nat.cast_pow]

/-- **Every homomorphism from the units of a Henselian local ring with finite residue field to
`Multiplicative ℤ` is trivial.** -/
theorem MonoidHom.eq_one_of_henselianLocalRing [Finite (ResidueField R)]
    (f : Rˣ →* Multiplicative ℤ) : f = 1 := by
  ext u
  set N := Nat.card (ResidueField R)ˣ
  have hN : 0 < N := Nat.card_pos
  have hres : residue R ((u ^ N : Rˣ) : R) = 1 := by
    have h1 : Units.map (residue R).toMonoidHom u ^ N = 1 := pow_card_eq_one'
    simpa [← map_pow] using congrArg Units.val h1
  have hpow : (f u) ^ N = 1 := by
    rw [← map_pow]
    exact f.apply_eq_one_of_residue_eq_one hres
  have hadd : (N : ℤ) * (f u).toAdd = 0 := by
    simpa [toAdd_pow, nsmul_eq_mul] using congrArg Multiplicative.toAdd hpow
  rcases mul_eq_zero.mp hadd with hN0 | hfu
  · exact absurd (Int.ofNat_inj.mp hN0) hN.ne'
  · exact Multiplicative.toAdd.injective hfu

namespace Valuation

/-- **Every `ℤᵐ⁰`-valued valuation on a Henselian local ring with finite residue field takes the
value `1` on units.** -/
@[simp]
theorem map_units_eq_one_of_henselianLocalRing [Finite (ResidueField R)]
    (v : _root_.Valuation R ℤᵐ⁰) (u : Rˣ) : v (u : R) = 1 := by
  let f : Rˣ →* Multiplicative ℤ :=
    (OrderMonoidIso.unitsWithZero (α := Multiplicative ℤ)).toMonoidHom.comp
      (Units.map v.toMonoidHom)
  have hf : f u = 1 := by simp [f.eq_one_of_henselianLocalRing]
  have hv : Units.map v.toMonoidHom u = 1 :=
    (OrderMonoidIso.unitsWithZero (α := Multiplicative ℤ)).injective (by simpa [f] using hf)
  exact congrArg Units.val hv

/-- Every `ℤᵐ⁰`-valued valuation on a Henselian local ring with finite residue field sends
invertible elements to `1`. -/
theorem map_eq_one_of_henselianLocalRing [Finite (ResidueField R)]
    (v : _root_.Valuation R ℤᵐ⁰) {x : R} (hx : IsUnit x) : v x = 1 := by
  obtain ⟨u, rfl⟩ := hx
  exact v.map_units_eq_one_of_henselianLocalRing u

/-- Every `ℤᵐ⁰`-valued valuation on a Henselian local ring with finite residue field has additive
order `0` on invertible elements. -/
theorem ord_eq_zero_of_henselianLocalRing [Finite (ResidueField R)]
    (v : _root_.Valuation R ℤᵐ⁰) {x : R} (hx : IsUnit x) : v.ord x = 0 := by
  simp [ord_def, v.map_eq_one_of_henselianLocalRing hx]

end Valuation

end HenselianLocalRing

section DiscreteValuationRing

namespace Valuation

/-- In a discrete valuation ring `𝒪 = (valuation K).integer`, if a nontrivial valuation `v` on `K`
is `1` on `𝒪ˣ`, then every irreducible element `ϖ` of `𝒪` satisfies `v ϖ < 1`. -/
private theorem map_irreducible_lt_one_of_map_units_eq_one {K Γ₀ : Type*} [Field K]
    [ValuativeRel K] [IsDiscreteValuationRing (valuation K).integer]
    [LinearOrderedCommGroupWithZero Γ₀] (v : _root_.Valuation K Γ₀) [v.IsNontrivial]
    (hu : ∀ u : (valuation K).integerˣ, v ((u : (valuation K).integer) : K) = 1)
    {ϖ : (valuation K).integer} (hϖ : Irreducible ϖ) : v (ϖ : K) < 1 := by
  rcases lt_trichotomy (v (ϖ : K)) 1 with hlt | heq | hgt
  · exact hlt
  · exfalso
    obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
    have hone {a : (valuation K).integer} (ha : a ≠ 0) : v (a : K) = 1 := by
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      simp [hu u, heq]
    rcases le_total (valuation K x) 1 with hx | hx
    · exact hx1 (hone (a := ⟨x, hx⟩) (by simpa [Subtype.ext_iff] using hx0))
    · have hx_inv : x⁻¹ ∈ (valuation K).integer := by
        rw [Valuation.mem_integer_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hx
      have h1 := hone (a := ⟨x⁻¹, hx_inv⟩) (by simpa [Subtype.ext_iff] using inv_ne_zero hx0)
      exact hx1 (inv_eq_one.mp (by simpa using h1))
  · exfalso
    obtain ⟨u, hu'⟩ := TauCeti.isUnit_add_of_isUnit_of_not_isUnit isUnit_one hϖ.not_isUnit
    have hv1 : v (1 + (ϖ : K)) = 1 := by
      have := congrArg (fun z : (valuation K).integer ↦ v (z : K)) hu'
      exact this.symm.trans (hu u)
    have hvmax : v (1 + (ϖ : K)) = max (v 1) (v (ϖ : K)) :=
      v.map_add_of_distinct_val (by simpa using hgt.ne)
    rw [v.map_one, max_eq_right hgt.le, hv1] at hvmax
    exact hgt.ne hvmax

/-- **Unit-triviality criterion for equivalence with a DVR valuation.** Let `K` be a valued field
whose integer ring `𝒪 = (valuation K).integer` is a discrete valuation ring. Any nontrivial
valuation `v` on `K` (valued in an arbitrary linearly ordered commutative group with zero) that
takes the value `1` on `𝒪ˣ` is equivalent to `valuation K`. -/
theorem isEquiv_valuation_of_map_units_eq_one {K Γ₀ : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer] [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) [v.IsNontrivial]
    (hu : ∀ u : (valuation K).integerˣ, v ((u : (valuation K).integer) : K) = 1) :
    v.IsEquiv (valuation K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (valuation K).integer
  have hϖ_lt : v (ϖ : K) < 1 := v.map_irreducible_lt_one_of_map_units_eq_one hu hϖ
  have hle (a : (valuation K).integer) : v (a : K) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      simpa [hu u] using pow_le_one₀ zero_le hϖ_lt.le
  refine isEquiv_iff_val_le_one.mpr fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ hle ⟨x, hx⟩⟩
  by_contra hx'
  replace hx' : 1 < valuation K x := not_le.mp hx'
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx'
  have hy_mem : x⁻¹ ∈ (valuation K).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx'.le
  set y : (valuation K).integer := ⟨x⁻¹, hy_mem⟩
  have hy0 : y ≠ 0 := by simpa [y, Subtype.ext_iff] using inv_ne_zero hx0
  obtain ⟨n, u, hy_eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hyu : x⁻¹ = ((u : (valuation K).integer) : K) := by
      simpa [y] using congrArg (fun z : (valuation K).integer ↦ (z : K)) hy_eq
    have hmul : (((u⁻¹ : (valuation K).integerˣ) : (valuation K).integer) : K) * x⁻¹ = 1 := by
      calc (((u⁻¹ : (valuation K).integerˣ) : (valuation K).integer) : K) * x⁻¹
        _ = (((u⁻¹ : (valuation K).integerˣ) : (valuation K).integer) : K) *
              ((u : (valuation K).integer) : K) := by rw [hyu]
        _ = ((((u⁻¹ * u : (valuation K).integerˣ) : (valuation K).integer)) : K) := rfl
        _ = 1 := by rw [inv_mul_cancel]; rfl
    have hux : (((u⁻¹ : (valuation K).integerˣ) : (valuation K).integer) : K) = x := by
      simpa using (inv_eq_of_mul_eq_one_left hmul).symm
    exact hx'.not_ge (hux ▸ ((u⁻¹ : (valuation K).integerˣ) : (valuation K).integer).2)
  have hy_lt : v (x⁻¹) < 1 := by
    have hv_eq : v (x⁻¹) = v (ϖ : K) ^ n := by
      simpa [y, hu u] using congrArg (fun z : (valuation K).integer ↦ v (z : K)) hy_eq
    exact hv_eq.trans_lt (pow_lt_one₀ zero_le hϖ_lt hn0)
  have h1 : (1 : Γ₀) < 1 := calc
    (1 : Γ₀) = v (x * x⁻¹) := by rw [mul_inv_cancel₀ hx0, map_one]
    _ = v x * v (x⁻¹) := map_mul v _ _
    _ ≤ 1 * v (x⁻¹) := mul_le_mul_of_nonneg_right hx zero_le
    _ = v (x⁻¹) := one_mul _
    _ < 1 := hy_lt
  exact h1.false

/-- **F. K. Schmidt discrete-valuation rigidity (single field).** If `(valuation K).integer` is a
Henselian discrete valuation ring with finite residue field, every nontrivial `ℤᵐ⁰`-valued
valuation on `K` is equivalent to `valuation K`. -/
theorem isEquiv_valuation_of_henselianLocalRing {K : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer]
    [HenselianLocalRing (valuation K).integer]
    [Finite (ResidueField (valuation K).integer)]
    (v : _root_.Valuation K ℤᵐ⁰) [v.IsNontrivial] :
    v.IsEquiv (valuation K) :=
  v.isEquiv_valuation_of_map_units_eq_one fun u ↦
    (v.comap (algebraMap (valuation K).integer K)).map_units_eq_one_of_henselianLocalRing u

end Valuation

/-- **Automatic valuation compatibility along algebraic extensions of Henselian DVRs with finite
residue field.** Let `K` be a valued field whose integer ring is a Henselian discrete valuation
ring with finite residue field, and let `L / K` be an algebraic field extension carrying a
nontrivial rank-one discrete `ValuativeRel`. Then `L / K` is automatically a
`ValuativeExtension K L`. -/
theorem ValuativeExtension.of_henselianLocalRing (K L : Type*) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer]
    [HenselianLocalRing (valuation K).integer]
    [Finite (ResidueField (valuation K).integer)]
    [Field L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    [Algebra K L] [Algebra.IsAlgebraic K L] :
    ValuativeExtension K L := by
  have harch : MulArchimedean (ValueGroupWithZero L) :=
    (isRankLeOne_iff_mulArchimedean (R := L)).mp inferInstance
  obtain ⟨e⟩ := (ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff (R := L)).mpr
    ⟨inferInstance, inferInstance, harch⟩
  let f : ValueGroupWithZero L →*₀o ℤᵐ⁰ :=
    { toMonoidWithZeroHom := e.toMonoidWithZeroHom
      monotone' := e.toOrderIso.monotone }
  let w : Valuation L ℤᵐ⁰ := (valuation L).map f
  have hw_equiv : w.IsEquiv (valuation L) :=
    Valuation.isEquiv_map_self_of_strictMono f e.injective
  have : w.IsNontrivial := hw_equiv.isNontrivial_iff.mpr inferInstance
  have : (w.comap (algebraMap K L)).IsNontrivial := w.isNontrivial_comap_algebraMap
  have hK : (w.comap (algebraMap K L)).IsEquiv (valuation K) :=
    (w.comap (algebraMap K L)).isEquiv_valuation_of_henselianLocalRing
  refine ⟨fun {a b} ↦ ?_⟩
  rw [(valuation L).vle_iff_le, ← hw_equiv (algebraMap K L a) (algebraMap K L b),
    ← Valuation.comap_apply, ← Valuation.comap_apply, hK a b, ← (valuation K).vle_iff_le]

/-- Any integral ring homomorphism `f : K →+* L` (over a field `K`, equivalently one over which
`L` is algebraic) from a Henselian discrete-valued field `K` with finite residue field into a
nontrivial rank-one discrete valued field `L` automatically preserves and reflects the valuative
relation. -/
theorem RingHom.map_vle_map_iff_of_henselianLocalRing {K L : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer]
    [HenselianLocalRing (valuation K).integer]
    [_root_.Finite (ResidueField (valuation K).integer)]
    [Field L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    (f : K →+* L) (hf : f.IsIntegral) (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  let _ : Algebra K L := f.toAlgebra
  have : Algebra.IsIntegral K L := ⟨hf⟩
  have : ValuativeExtension K L := .of_henselianLocalRing K L
  exact ValuativeExtension.vle_iff_vle

/-- Every abstract ring isomorphism from a Henselian discrete-valued field `K` with finite residue
field onto a nontrivial rank-one discrete valued field `L` automatically preserves and reflects the
valuative relation. -/
@[simp]
theorem RingEquiv.map_vle_map_iff_of_henselianLocalRing {K L : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer]
    [HenselianLocalRing (valuation K).integer]
    [_root_.Finite (ResidueField (valuation K).integer)]
    [Field L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [IsNontrivial L]
    (e : K ≃+* L) (x y : K) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y :=
  e.toRingHom.map_vle_map_iff_of_henselianLocalRing
    (RingHom.isIntegral_of_surjective _ e.surjective) x y

/-- **Uniqueness of the nontrivial rank-one discrete valuative relation on a field over a Henselian
DVR with finite residue field.** If `r₁` makes `(valuation K).integer` a Henselian discrete
valuation ring with finite residue field and `r₂` is any nontrivial rank-one discrete valuative
relation on the same field `K`, then `r₁ = r₂`. -/
theorem ValuativeRel.eq_of_henselianLocalRing {K : Type*} [Field K]
    (r₁ r₂ : ValuativeRel K)
    [@IsDiscreteValuationRing (@valuation K _ r₁).integer _ _]
    [@HenselianLocalRing (@valuation K _ r₁).integer _]
    [Finite (ResidueField (@valuation K _ r₁).integer)]
    [@IsDiscrete K _ r₂] [@IsRankLeOne K _ r₂] [@IsNontrivial K _ r₂] :
    r₁ = r₂ := by
  ext x y
  exact (@RingEquiv.map_vle_map_iff_of_henselianLocalRing K K _ r₁ ‹_› ‹_› ‹_› _ r₂ ‹_› ‹_› ‹_›
    (RingEquiv.refl K) x y).symm

end DiscreteValuationRing
