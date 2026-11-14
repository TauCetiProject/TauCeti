/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Valuation.Discrete.Order
public import TauCeti.RingTheory.Valuation.NontrivialComap
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Rigidity of discrete valuations on Henselian local rings with finite residue field

Let `R` be a Henselian local ring with finite residue field `k` of cardinality `q`. Every
`ℤᵐ⁰`-valued valuation `v` on `R` takes the value `1` on `Rˣ`
(`Valuation.map_eq_one_of_isUnit_of_henselianLocalRing`). Indeed, for `u ∈ Rˣ`, the unit
`u ^ #(kˣ)` reduces to `1` in `k`. Since `(q : k) = 0`, the integer `q + 1 > 1` reduces to `1` in
`k` and is therefore invertible in `R`, together with all its powers `(q + 1) ^ n`. Hensel's lemma
(`TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq`) extracts a `(q + 1) ^ n`-th root of
`u ^ #(kˣ)` in `R` for every `n`, so `(q + 1) ^ n` divides `#(kˣ) · ord_v(u)` in `ℤ` for every `n`,
forcing `ord_v(u) = 0` and hence `v(u) = 1`.

Now let `K` be a field equipped with a valuation `w` whose valuation ring `w.integer` is a
Henselian discrete valuation ring with finite residue field — for instance any nonarchimedean local
field, with no topological hypothesis required. Applying the unit rigidity to the restriction of a
`ℤᵐ⁰`-valued valuation `v` of `K` to `w.integer` shows:

* `v` sends every `w`-unit to `1` (`Valuation.eq_one_of_eq_one_of_henselianLocalRing`);
* for an irreducible element `ϖ` of `w.integer`, `1 + ϖ` is a unit of `w.integer`, so
  `v(1 + ϖ) = 1` and the ultrametric equality rules out `1 < v(ϖ)`, giving `v ≤ 1` on all of
  `w.integer` (`Valuation.le_one_of_le_one_of_henselianLocalRing`);
* since a discrete valuation subring is maximal among proper subrings of `K`
  (`ValuationSubring.eq_of_le_of_ne_top`), every nontrivial `v : Valuation K ℤᵐ⁰` has the same
  valuation subring as `w` and is therefore equivalent to `w`
  (`Valuation.isEquiv_of_henselianLocalRing`), and every `v : Valuation K ℤᵐ⁰` is either trivial
  on `K` or equivalent to `w` (`Valuation.isTrivialOn_or_isEquiv_of_henselianLocalRing`).

For a ring homomorphism `f : K →+* L` into a ring carrying a discrete rank-at-most-one valuative
relation, nontriviality of `(valuation L).comap f` embeds the value group of `L`
order-isomorphically into `ℤᵐ⁰`
(`ValuativeRel.ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff`), so the pullback is
automatically equivalent to `valuation K` (`RingHom.isEquiv_comap_valuation_of_isNontrivial`).
Combining this with the two nontriviality criteria of `TauCeti.RingTheory.Valuation.NontrivialComap`
gives automatic valuation compatibility (`ValuativeExtension K L`) in two settings:

1. **Integral extensions** (`ValuativeExtension.of_isIntegral_of_isDiscrete`), when `L` is
   nontrivial and integral over `K` (in particular for any algebraic field extension);
2. **Finite residue fields** (`ValuativeExtension.of_finite_residueField`), for *any* algebra map
   `K → L` into a commutative ring with finite residue field, with no algebraicity or finiteness
   assumption on the extension.

## Main results

* `Valuation.ord_eq_zero_of_isUnit_of_henselianLocalRing` and
  `Valuation.map_eq_one_of_isUnit_of_henselianLocalRing`: every unit of a Henselian local ring with
  finite residue field has `ℤᵐ⁰`-order `0` and valuation `1`.
* `Valuation.isEquiv_of_henselianLocalRing`,
  `Valuation.isTrivialOn_or_isEquiv_of_henselianLocalRing`,
  `Valuation.eq_of_surjective_of_henselianLocalRing`, and
  `Valuation.compatible_of_henselianLocalRing`: on a field with a Henselian discrete valuation `w`
  of finite residue field, `w` is the unique equivalence class of nontrivial `ℤᵐ⁰`-valued
  valuations, and `K` carries at most one surjective `ℤᵐ⁰`-valued valuation.
* `RingHom.isEquiv_comap_valuation_of_isNontrivial` and
  `RingHom.map_vle_map_iff_of_isNontrivial_comap`: a nontrivial pullback of a discrete
  rank-at-most-one valuative relation is equivalent to `valuation K`.
* `ValuativeExtension.of_isIntegral_of_isDiscrete` and
  `ValuativeExtension.of_finite_residueField`: automatic `ValuativeExtension K L` under integrality
  or residue finiteness.

## Implementation notes

Neither `ValuativeExtension.of_isIntegral_of_isDiscrete` nor
`ValuativeExtension.of_finite_residueField` can be registered as a global `instance`: their
hypotheses mention typeclasses (`IsDiscreteValuationRing`, `HenselianLocalRing`, `Finite`,
`Algebra.IsIntegral`) whose parameters do not all appear conservatively in `ValuativeExtension K L`,
and downstream local-field instances derive `Module.Finite` from `ValuativeExtension`, which would
create an instance cycle with `Algebra.IsIntegral.of_finite`. Callers install them locally with
`have := ValuativeExtension.of_finite_residueField K L` (or the local-field specialization in
`TauCeti.NumberTheory.LocalField.ValuationRigidity`).

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Mathematische Annalen **108** (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Section 4.4.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section

open scoped WithZero

open IsLocalRing ValuativeRel

namespace Valuation

section HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- If every power of an integer `N > 1` divides `z : ℤ`, then `z = 0`. -/
private theorem eq_zero_of_forall_pow_dvd {N : ℕ} (hN : 1 < N) {z : ℤ}
    (hdvd : ∀ k : ℕ, (N : ℤ) ^ k ∣ z) : z = 0 := by
  have hnat : N ^ z.natAbs ∣ z.natAbs := Int.natCast_dvd_natCast.mp
    (by rw [Nat.cast_pow]; exact (hdvd z.natAbs).trans (Int.dvd_natAbs.mpr dvd_rfl))
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hnat (Nat.lt_pow_self hN))

/-- **Every unit of a Henselian local ring with finite residue field has `ℤᵐ⁰`-order `0`**: raising
to `#(kˣ)` gives a unit with residue `1`, which has `(q + 1) ^ n`-th roots for all `n` by Hensel's
lemma, so `#(kˣ) · ord_v(u)` is divisible by arbitrarily high powers of `q + 1 > 1`. -/
theorem ord_eq_zero_of_isUnit_of_henselianLocalRing (v : _root_.Valuation R ℤᵐ⁰) {u : R}
    (hu : IsUnit u) : v.ord u = 0 := by
  let _ := Fintype.ofFinite (ResidueField R)
  let _ := Fintype.ofFinite (ResidueField R)ˣ
  set m := Fintype.card (ResidueField R)ˣ
  set N := Fintype.card (ResidueField R) + 1
  have hm0 : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN : 1 < N := Nat.succ_lt_succ Fintype.card_pos
  -- `(q : k) = 0` in the finite residue field `k`, so `q + 1` reduces to `1` and is a unit in `R`.
  have hNunit : IsUnit (N : R) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_add, Nat.cast_card_eq_zero,
      Nat.cast_one, zero_add]
    exact one_ne_zero
  obtain ⟨u₀, rfl⟩ := hu
  have hres : residue R ((u₀ ^ m : Rˣ) : R) = 1 := by
    have hcard : Units.map (residue R).toMonoidHom u₀ ^ m = 1 := pow_card_eq_one
    simpa using congrArg (Units.val : (ResidueField R)ˣ → ResidueField R) hcard
  have hdvd (k : ℕ) : (N : ℤ) ^ k ∣ (m : ℤ) * v.ord (u₀ : R) := by
    have hk : IsUnit ((N ^ k : ℕ) : R) := by rw [Nat.cast_pow]; exact hNunit.pow k
    obtain ⟨x, hx, -⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq hk
      (x₀ := 1) (u := ((u₀ ^ m : Rˣ) : R)) isUnit_one (by rw [map_one, one_pow, hres])
    refine ⟨v.ord x, ?_⟩
    have hord := congrArg v.ord hx
    rw [Units.val_pow_eq_pow_val, v.ord_pow, v.ord_pow, Nat.cast_pow] at hord
    exact hord.symm
  exact (mul_eq_zero.mp (eq_zero_of_forall_pow_dvd hN hdvd)).resolve_left hm0

/-- **Every unit of a Henselian local ring with finite residue field has `ℤᵐ⁰`-valuation `1`.** -/
theorem map_eq_one_of_isUnit_of_henselianLocalRing (v : _root_.Valuation R ℤᵐ⁰) {u : R}
    (hu : IsUnit u) : v u = 1 := by
  obtain ⟨u₀, rfl⟩ := hu
  have hv0 : v (u₀ : R) ≠ 0 := left_ne_zero_of_mul_eq_one
    (by rw [← map_mul, Units.mul_inv, map_one])
  rw [v.valuation_eq_exp_neg_ord hv0, v.ord_eq_zero_of_isUnit_of_henselianLocalRing u₀.isUnit,
    neg_zero, WithZero.exp_zero]

end HenselianLocalRing

section HenselianDVR

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : _root_.Valuation K ℤᵐ⁰) (w : _root_.Valuation K Γ₀)
  [IsDiscreteValuationRing w.integer] [HenselianLocalRing w.integer]
  [Finite (ResidueField w.integer)]

omit [IsDiscreteValuationRing w.integer] in
/-- On a field with a Henselian valuation `w` of finite residue field, every `w`-unit has
`ℤᵐ⁰`-valuation `1` for any `v : Valuation K ℤᵐ⁰`. -/
theorem eq_one_of_eq_one_of_henselianLocalRing {x : K} (hx : w x = 1) : v x = 1 := by
  have hx_mem : x ∈ w.integer := hx.le
  have hunit : IsUnit (⟨x, hx_mem⟩ : w.integer) :=
    (Valuation.integer.integers w).isUnit_iff_valuation_eq_one.mpr hx
  simpa using (v.comap w.integer.subtype).map_eq_one_of_isUnit_of_henselianLocalRing hunit

/-- On a field with a Henselian discrete valuation `w` of finite residue field, every `w`-integral
element is `v`-integral for any `v : Valuation K ℤᵐ⁰`: for a uniformizer `ϖ`, `1 + ϖ` is a
`w`-unit, so `v(1 + ϖ) = 1` rules out `1 < v(ϖ)`. -/
theorem le_one_of_le_one_of_henselianLocalRing {x : K} (hx : w x ≤ 1) : v x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.integer
  have h1ϖ : IsUnit (1 + ϖ) :=
    TauCeti.isUnit_add_of_isUnit_of_not_isUnit isUnit_one hϖ.not_isUnit
  have hv1ϖ : v (1 + (ϖ : K)) = 1 := by
    simpa using (v.comap w.integer.subtype).map_eq_one_of_isUnit_of_henselianLocalRing h1ϖ
  have hvϖ : v (ϖ : K) ≤ 1 := by
    by_contra! hgt
    have heq : v ((ϖ : K) + 1) = v (ϖ : K) := v.map_add_eq_of_lt_left (by simpa using hgt)
    rw [add_comm, hv1ϖ] at heq
    exact hgt.ne heq
  obtain ⟨n, u, hfac⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨x, hx⟩ : w.integer)) (Subtype.coe_ne_coe.mp hx0) hϖ
  have hx_eq : x = ((u : w.integer) : K) * (ϖ : K) ^ n := by
    simpa using congrArg (Subtype.val : w.integer → K) hfac
  have hvu : v ((u : w.integer) : K) = 1 :=
    (v.comap w.integer.subtype).map_eq_one_of_isUnit_of_henselianLocalRing u.isUnit
  rw [hx_eq, map_mul, hvu, one_mul, map_pow]
  exact pow_le_one₀ zero_le hvϖ

/-- On a field with a Henselian discrete valuation `w` of finite residue field, `w.valuationSubring`
is contained in `v.valuationSubring` for every `v : Valuation K ℤᵐ⁰`. -/
theorem valuationSubring_le_of_henselianLocalRing :
    w.valuationSubring ≤ v.valuationSubring :=
  fun _ hx ↦ v.le_one_of_le_one_of_henselianLocalRing w hx

/-- **Uniqueness of nontrivial discrete valuations on a Henselian DVR field with finite residue
field**: every nontrivial `ℤᵐ⁰`-valued valuation `v` on `K` is equivalent to `w`. -/
theorem isEquiv_of_henselianLocalRing [v.IsNontrivial] : v.IsEquiv w := by
  have : IsDiscreteValuationRing w.valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing w.integer)
  have hne : v.valuationSubring ≠ ⊤ := by
    simp only [ne_eq, _root_.Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  exact (_root_.Valuation.isEquiv_iff_valuationSubring v w).mpr
    (ValuationSubring.eq_of_le_of_ne_top (A := w.valuationSubring) (B := v.valuationSubring)
      (v.valuationSubring_le_of_henselianLocalRing w) hne).symm

/-- **Dichotomy for `ℤᵐ⁰`-valued valuations on a Henselian DVR field with finite residue field**:
every `v : Valuation K ℤᵐ⁰` is either trivial on `K` or equivalent to `w`. -/
theorem isTrivialOn_or_isEquiv_of_henselianLocalRing : v.IsTrivialOn K ∨ v.IsEquiv w := by
  by_cases hv : v.IsNontrivial
  · exact Or.inr (v.isEquiv_of_henselianLocalRing w)
  · refine Or.inl ⟨fun x hx0 ↦ ?_⟩
    simpa using of_not_not fun h1 ↦ hv ⟨x, v.ne_zero_iff.mpr hx0, h1⟩

include w in
/-- **Uniqueness of surjective `ℤᵐ⁰`-valued valuations on a Henselian DVR field with finite
residue field**: any two surjective `ℤᵐ⁰`-valued valuations on `K` are equal. -/
theorem eq_of_surjective_of_henselianLocalRing {v₁ v₂ : _root_.Valuation K ℤᵐ⁰}
    (hv₁ : Function.Surjective v₁) (hv₂ : Function.Surjective v₂) : v₁ = v₂ := by
  have : v₁.IsNontrivial := isNontrivial_of_surjective hv₁
  have : v₂.IsNontrivial := isNontrivial_of_surjective hv₂
  exact eq_of_isEquiv_of_surjective hv₁ hv₂
    ((v₁.isEquiv_of_henselianLocalRing w).trans (v₂.isEquiv_of_henselianLocalRing w).symm)

end HenselianDVR

end Valuation

section ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K]
  [IsDiscreteValuationRing (valuation K).integer] [HenselianLocalRing (valuation K).integer]
  [_root_.Finite (ResidueField (valuation K).integer)]

/-- **Every nontrivial `ℤᵐ⁰`-valued valuation on a Henselian DVR field with finite residue field is
compatible with its valuative relation.** -/
theorem Valuation.compatible_of_henselianLocalRing (v : Valuation K ℤᵐ⁰) [v.IsNontrivial] :
    v.Compatible :=
  (v.isEquiv_of_henselianLocalRing (valuation K)).symm.compatible

namespace RingHom

section IsNontrivialComap

variable {L : Type*} [Ring L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L]

/-- **Pullback rigidity for discrete rank-at-most-one valuative relations**: if `K` has a Henselian
discrete valuation ring with finite residue field and `f : K →+* L` pulls back `valuation L` to a
nontrivial valuation on `K`, then that pullback is equivalent to `valuation K`. -/
theorem isEquiv_comap_valuation_of_isNontrivial (f : K →+* L)
    [((valuation L).comap f).IsNontrivial] :
    ((valuation L).comap f).IsEquiv (valuation K) := by
  obtain ⟨x, hx0, hx1⟩ := ‹((valuation L).comap f).IsNontrivial›.exists_val_nontrivial
  have hN : ValuativeRel.IsNontrivial L := ⟨valuation L (f x), hx0, hx1⟩
  obtain ⟨e⟩ := (ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff (R := L)).mpr
    ⟨‹_›, hN, inferInstance⟩
  let v : Valuation K ℤᵐ⁰ :=
    ((valuation L).comap f).map (e : ValueGroupWithZero L →*₀o ℤᵐ⁰)
  have heq : v.IsEquiv ((valuation L).comap f) :=
    Valuation.isEquiv_map_self_of_strictMono _ e.injective
  have : v.IsNontrivial := heq.isNontrivial_iff.mpr ‹_›
  exact heq.symm.trans (v.isEquiv_of_henselianLocalRing (valuation K))

/-- If `(valuation L).comap f` is nontrivial and `L` is discrete of rank at most one, then
`f : K →+* L` preserves and reflects the valuative relation. -/
theorem map_vle_map_iff_of_isNontrivial_comap (f : K →+* L)
    [((valuation L).comap f).IsNontrivial] (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rw [(valuation L).vle_iff_le, (valuation K).vle_iff_le]
  exact f.isEquiv_comap_valuation_of_isNontrivial x y

end IsNontrivialComap

section FiniteResidueField

variable {L : Type*} [CommRing L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L]
  [IsLocalRing (valuation L).integer] [_root_.Finite (ResidueField (valuation L).integer)]

/-- **Pullback rigidity under residue finiteness**: every ring homomorphism `f : K →+* L` from a
Henselian DVR field with finite residue field into a commutative ring carrying a discrete
rank-at-most-one valuative relation with finite residue field pulls back `valuation L` to a
valuation equivalent to `valuation K`, with no algebraicity assumption on `f`. -/
theorem isEquiv_comap_valuation_of_finite_residueField (f : K →+* L) :
    ((valuation L).comap f).IsEquiv (valuation K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (valuation K).integer
  have : (valuation K).IsNontrivial :=
    ⟨ϖ, (Valuation.integer.v_irreducible_pos hϖ).ne',
      (Valuation.integer.v_irreducible_lt_one hϖ).ne⟩
  have : Infinite K := (valuation K).infinite_of_isNontrivial
  have : ((valuation L).comap f).IsNontrivial :=
    (valuation L).isNontrivial_comap_of_finite_residueField f
  exact f.isEquiv_comap_valuation_of_isNontrivial

/-- Every ring homomorphism `f : K →+* L` into a commutative ring with discrete rank-at-most-one
valuative relation and finite residue field preserves and reflects `≤ᵥ`. -/
theorem map_vle_map_iff_of_finite_residueField (f : K →+* L) (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rw [(valuation L).vle_iff_le, (valuation K).vle_iff_le]
  exact f.isEquiv_comap_valuation_of_finite_residueField x y

end FiniteResidueField

end RingHom

/-- **Automatic valuation compatibility for integral extensions**: if `K` has a Henselian discrete
valuation ring with finite residue field and `L` is a nontrivial integral `K`-algebra carrying a
discrete rank-at-most-one valuative relation, then `L/K` is automatically a `ValuativeExtension`.

This applies in particular to any algebraic field extension `L/K` (via
`Algebra.IsAlgebraic.isIntegral`) and any module-finite extension (via
`Algebra.IsIntegral.of_finite`). -/
theorem ValuativeExtension.of_isIntegral_of_isDiscrete (K L : Type*) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer] [HenselianLocalRing (valuation K).integer]
    [_root_.Finite (ResidueField (valuation K).integer)]
    [Ring L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L] [ValuativeRel.IsNontrivial L]
    [Algebra K L] [Algebra.IsIntegral K L] :
    ValuativeExtension K L := by
  have : ((valuation L).comap (algebraMap K L)).IsNontrivial :=
    (valuation L).isNontrivial_comap_algebraMap
  exact ⟨fun {a b} ↦ (algebraMap K L).map_vle_map_iff_of_isNontrivial_comap a b⟩

/-- **Automatic valuation compatibility under residue finiteness**: if `K` has a Henselian discrete
valuation ring with finite residue field and `L` is a commutative `K`-algebra carrying a discrete
rank-at-most-one valuative relation whose valuation ring is local with finite residue field, then
`L/K` is automatically a `ValuativeExtension`, with no algebraicity or finiteness hypothesis on
`L/K`. -/
theorem ValuativeExtension.of_finite_residueField (K L : Type*) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer] [HenselianLocalRing (valuation K).integer]
    [_root_.Finite (ResidueField (valuation K).integer)]
    [CommRing L] [ValuativeRel L] [IsDiscrete L] [IsRankLeOne L]
    [IsLocalRing (valuation L).integer] [_root_.Finite (ResidueField (valuation L).integer)]
    [Algebra K L] :
    ValuativeExtension K L :=
  ⟨fun {a b} ↦ (algebraMap K L).map_vle_map_iff_of_finite_residueField a b⟩

end ValuativeRel
