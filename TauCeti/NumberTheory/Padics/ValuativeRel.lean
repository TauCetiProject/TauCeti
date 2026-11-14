/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
import TauCeti.NumberTheory.Padics.PrincipalUnits
import TauCeti.RingTheory.Valuation.NontrivialComap
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow

/-!
# Uniqueness of the discrete rank-one valuation on `ℚ_[p]` and compatibility on extensions

Every nontrivial `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is a positive integer power of
`Padic.mulValuation`, and hence equivalent to it. Consequently, `ℚ_[p]` carries a unique discrete,
nontrivial, rank-at-most-one `ValuativeRel`, namely its canonical `p`-adic `ValuativeRel`, and any
integral `ℚ_[p]`-algebra `R` equipped with a discrete, nontrivial, rank-at-most-one `ValuativeRel`
automatically satisfies `ValuativeExtension ℚ_[p] R`. In particular, a finite extension `F` of
`ℚ_[p]` equipped with `[IsNonarchimedeanLocalField F]` is automatically a `ValuativeExtension` of
`ℚ_[p]` without any auxiliary compatibility assumption between `Algebra ℚ_[p] F` and
`ValuativeRel F`.

The rigidity is algebraic and requires no continuity assumption on the valuation:

1. The first principal unit group `1 + pℤ_[p]` is a profinite pro-`p` group
   (`TauCeti.isProP_unitsPrincipal`), so `TauCeti.IsProP.subsingleton_monoidHom_multiplicativeInt`
   kills every group homomorphism `1 + pℤ_[p] →* Multiplicative ℤ`. Since `1 + pℤ_[p]` has finite
   index `p - 1` in `ℤ_[p]ˣ`, and `Multiplicative ℤ` is torsion-free, every group homomorphism
   `ℤ_[p]ˣ →* Multiplicative ℤ` is trivial.
2. Restricting a valuation `v : Valuation ℚ_[p] ℤᵐ⁰` to `ℤ_[p]ˣ` therefore sends every `p`-adic
   unit to `1`, so `v x = v p ^ x.valuation` for `x ≠ 0`. Since `1 + p` is a unit of `ℤ_[p]`, the
   ultrametric inequality forces `v p ≤ 1`; nontriviality of `v` is then equivalent to `v p < 1`,
   in which case `v = Padic.mulValuation ^ e` for `e = -log (v p) > 0`.
3. If `R` is an integral `ℚ_[p]`-algebra with a discrete, nontrivial, rank-at-most-one
   `ValuativeRel`, its value group is order-isomorphic to `ℤᵐ⁰`. Transporting `valuation R` along
   that isomorphism and pulling back along `algebraMap ℚ_[p] R` yields a `ℤᵐ⁰`-valued valuation on
   `ℚ_[p]` that remains nontrivial by `Valuation.isNontrivial_comap_algebraMap`, and is therefore
   equivalent to `Padic.mulValuation`.

Each hypothesis on `R` in `TauCeti.valuativeExtension_padic` is sharp:

* **Integrality** (`Algebra.IsIntegral ℚ_[p] R`): the Laurent series field `ℚ_[p]((T))` with its
  `T`-adic valuation is discrete, nontrivial, and rank one, while restricting to `ℚ_[p]` gives the
  trivial valuation.
* **Nontriviality** (`ValuativeRel.IsNontrivial R`): equipping `ℚ_[p]` itself with the trivial
  valuation is discrete and rank at most one, yet incompatible with the `p`-adic valuation.
* **Discreteness** (`ValuativeRel.IsDiscrete R`): a transcendence basis of `ℚ_[p]` over `ℚ` carries
  a `t`-adic valuation on `ℚ(t)` whose extension to `ℚ_[p]` can be chosen rank one (embeddable in
  `ℝ≥0`) and nontrivial, yet trivial on `ℚ` and hence inequivalent to `Padic.mulValuation`; its
  value group over `ℚ(t)` is divisible at primes other than `p`, so discreteness is what rules out
  such exotic valuations.

`TauCeti.valuativeExtension_padic` is exposed as a theorem rather than a global instance so that
explicit `[ValuativeExtension ℚ_[p] K]` assumptions on general tower lemmas remain usable without
triggering `unusedSectionVars` diagnostics.

## Main results

* `TauCeti.instSubsingletonMonoidHomUnitsPadicIntMultiplicativeInt`: there is no nontrivial group
  homomorphism `ℤ_[p]ˣ →* Multiplicative ℤ`.
* `Valuation.padicInt_units_eq_one`, `Valuation.padicInt_apply_eq_pow_valuation`,
  `Valuation.padicInt_le_one`: any `v : Valuation ℤ_[p] ℤᵐ⁰` is `1` on `ℤ_[p]ˣ`, satisfies
  `v x = v p ^ x.valuation` for `x ≠ 0`, and is bounded by `1` on all of `ℤ_[p]`.
* `Valuation.padicInt_isNontrivial_iff`, `Valuation.padicInt_eq_zero_iff`,
  `Valuation.existsUnique_eq_padicInt_mulValuation_pow`: `v : Valuation ℤ_[p] ℤᵐ⁰` is nontrivial
  iff `0 < v p ∧ v p < 1`, in which case it has trivial support and is uniquely a positive power of
  `x ↦ Padic.mulValuation (x : ℚ_[p])`.
* `Valuation.padic_coe_padicInt_units_eq_one`, `Valuation.padic_apply_eq_zpow_valuation`,
  `Valuation.padic_natCast_self_le_one`, `Valuation.padic_isNontrivial_iff`: for
  `v : Valuation ℚ_[p] ℤᵐ⁰`, `v x = v p ^ x.valuation` on nonzero `x`, `v p ≤ 1`, and `v` is
  nontrivial iff `v p < 1`.
* `Valuation.existsUnique_eq_padic_mulValuation_pow`, `Valuation.isEquiv_padic_mulValuation`,
  `Valuation.compatible_padic`: every nontrivial `v : Valuation ℚ_[p] ℤᵐ⁰` is a unique positive
  power of, hence equivalent to, `Padic.mulValuation`.
* `ValuativeRel.eq_padicInstValuativeRel`: `ℚ_[p]` admits a unique discrete, nontrivial,
  rank-at-most-one `ValuativeRel`.
* `TauCeti.valuativeExtension_padic`: any integral `ℚ_[p]`-algebra with a discrete, nontrivial,
  rank-at-most-one `ValuativeRel` satisfies `ValuativeExtension ℚ_[p] R`.

## References

* [J.-P. Serre, *Local Fields*][serre1979], Chapter II, §2 and Chapter XIV, §3.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Chapter 3, §3.2.
-/

public section

open scoped WithZero

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Rigidity of `ℤ`-valued characters on `ℤ_[p]ˣ`.** Every group homomorphism
`ℤ_[p]ˣ →* Multiplicative ℤ` is trivial: its restriction to the pro-`p` subgroup `1 + pℤ_[p]` is
trivial (`TauCeti.IsProP.subsingleton_monoidHom_multiplicativeInt`), so every value is
`(p - 1)`-torsion in `Multiplicative ℤ` and therefore `1`. -/
instance instSubsingletonMonoidHomUnitsPadicIntMultiplicativeInt :
    Subsingleton (ℤ_[p]ˣ →* Multiplicative ℤ) := by
  have : Subsingleton (unitsPrincipal p 1 →* Multiplicative ℤ) :=
    (isProP_unitsPrincipal p one_pos).subsingleton_monoidHom_multiplicativeInt
  refine ⟨fun f g ↦ MonoidHom.ext fun u ↦ ?_⟩
  suffices ∀ φ : ℤ_[p]ˣ →* Multiplicative ℤ, φ u = 1 by rw [this f, this g]
  intro φ
  have hmem : u ^ (unitsPrincipal p 1).index ∈ unitsPrincipal p 1 :=
    Subgroup.pow_index_mem (unitsPrincipal p 1) u
  have hpow : φ (u ^ (unitsPrincipal p 1).index) = 1 :=
    congrFun (congrArg DFunLike.coe (Subsingleton.elim (φ.comp (unitsPrincipal p 1).subtype) 1))
      ⟨u ^ (unitsPrincipal p 1).index, hmem⟩
  have hidx : (unitsPrincipal p 1).index ≠ 0 := by
    rw [index_unitsPrincipal_of_pos p one_pos]
    exact mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  rw [map_pow, ← Multiplicative.toAdd.injective.eq_iff, toAdd_pow, toAdd_one,
    nsmul_eq_zero_iff] at hpow
  exact Multiplicative.toAdd.injective (hpow.resolve_right hidx)

end TauCeti

namespace Valuation

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### `ℤᵐ⁰`-valued valuations on `ℤ_[p]` -/

/-- Any `ℤᵐ⁰`-valued valuation on `ℤ_[p]` takes the value `1` on every `p`-adic unit. -/
theorem padicInt_units_eq_one (v : Valuation ℤ_[p] ℤᵐ⁰) (u : ℤ_[p]ˣ) : v u = 1 := by
  let φ : ℤ_[p]ˣ →* Multiplicative ℤ :=
    WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map (v : ℤ_[p] →* ℤᵐ⁰))
  have hφ : φ u = 1 :=
    congrFun (congrArg DFunLike.coe (Subsingleton.elim φ 1)) u
  have hu : Units.map (v : ℤ_[p] →* ℤᵐ⁰) u = 1 :=
    (map_eq_one_iff _ WithZero.unitsWithZeroEquiv.injective).mp hφ
  exact congrArg Units.val hu

/-- Any `ℤᵐ⁰`-valued valuation on `ℤ_[p]` is determined on nonzero elements by its value at `p`:
`v x = v p ^ x.valuation`. -/
theorem padicInt_apply_eq_pow_valuation (v : Valuation ℤ_[p] ℤᵐ⁰) {x : ℤ_[p]} (hx : x ≠ 0) :
    v x = v p ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, v.padicInt_units_eq_one, one_mul]

/-- Any `ℤᵐ⁰`-valued valuation on `ℤ_[p]` satisfies `v p ≤ 1`, because `1 + p` is a unit in
`ℤ_[p]`. -/
theorem padicInt_natCast_self_le_one (v : Valuation ℤ_[p] ℤᵐ⁰) : v p ≤ 1 := by
  by_contra! hlt
  obtain ⟨u, hu⟩ := PadicInt.isUnit_one_add_of_dvd (dvd_refl (p : ℤ_[p]))
  have hv1 : v (1 + (p : ℤ_[p])) = 1 := by
    rw [← hu, v.padicInt_units_eq_one]
  have hv2 : v (1 + (p : ℤ_[p])) = v p :=
    v.map_add_eq_of_lt_right (by simpa only [map_one] using hlt)
  exact hlt.ne (hv1.symm.trans hv2)

/-- Every `ℤᵐ⁰`-valued valuation on `ℤ_[p]` is bounded by `1` on all of `ℤ_[p]`. -/
theorem padicInt_le_one (v : Valuation ℤ_[p] ℤᵐ⁰) (x : ℤ_[p]) : v x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [v.padicInt_apply_eq_pow_valuation hx]
    exact pow_le_one₀ zero_le v.padicInt_natCast_self_le_one

/-- A `ℤᵐ⁰`-valued valuation on `ℤ_[p]` is nontrivial if and only if `0 < v p` and `v p < 1`.
Unlike on `ℚ_[p]`, `0 < v p` is not automatic: composing the residue map `ℤ_[p] →+* ZMod p` with
the trivial valuation produces a `{0, 1}`-valued valuation with `v p = 0`. -/
theorem padicInt_isNontrivial_iff (v : Valuation ℤ_[p] ℤᵐ⁰) :
    v.IsNontrivial ↔ 0 < v p ∧ v p < 1 := by
  constructor
  · intro hv
    obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
    have hx_ne : x ≠ 0 := fun h ↦ hx0 (by simp [h])
    rw [v.padicInt_apply_eq_pow_valuation hx_ne] at hx0 hx1
    refine ⟨zero_lt_iff.mpr fun hp0 ↦ ?_, lt_of_le_of_ne v.padicInt_natCast_self_le_one fun hp1 ↦
      hx1 (by rw [hp1, one_pow])⟩
    rcases eq_or_ne x.valuation 0 with hval | hval
    · exact hx1 (by rw [hval, pow_zero])
    · exact hx0 (by rw [hp0, zero_pow hval])
  · rintro ⟨hp0, hp1⟩
    exact ⟨p, hp0.ne', hp1.ne⟩

/-- Every nontrivial `ℤᵐ⁰`-valued valuation on `ℤ_[p]` has trivial support (`v x = 0 ↔ x = 0`). -/
theorem padicInt_eq_zero_iff (v : Valuation ℤ_[p] ℤᵐ⁰) [v.IsNontrivial] {x : ℤ_[p]} :
    v x = 0 ↔ x = 0 := by
  refine ⟨fun hvx ↦ by_contra fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  have hp0 : v p ≠ 0 := (v.padicInt_isNontrivial_iff.mp inferInstance).1.ne'
  rw [v.padicInt_apply_eq_pow_valuation hx] at hvx
  exact pow_ne_zero _ hp0 hvx

/-- **Classification of `ℤᵐ⁰`-valued valuations on `ℤ_[p]`.** Every nontrivial valuation
`v : Valuation ℤ_[p] ℤᵐ⁰` is uniquely a positive integer power of
`x ↦ Padic.mulValuation (x : ℚ_[p])`. -/
theorem existsUnique_eq_padicInt_mulValuation_pow (v : Valuation ℤ_[p] ℤᵐ⁰) [v.IsNontrivial] :
    ∃! e : ℕ, 0 < e ∧ ∀ x : ℤ_[p], v x = Padic.mulValuation (x : ℚ_[p]) ^ e := by
  obtain ⟨hvp_pos, hvp1⟩ := v.padicInt_isNontrivial_iff.mp inferInstance
  have hvp0 : v p ≠ 0 := hvp_pos.ne'
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hmul_p : Padic.mulValuation (p : ℚ_[p]) = WithZero.exp (-1) := by
    rw [Padic.mulValuation_toFun, ite_eq_right hp0, Padic.valuation_p]
  have hlog : WithZero.log (v p) < 0 := by
    rw [← WithZero.exp_log hvp0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hvp1
    exact hvp1
  set e : ℕ := (-WithZero.log (v p)).toNat
  have he : 0 < e := Int.pos_iff_toNat_pos.mp (neg_pos.mpr hlog)
  have hvp : v p = Padic.mulValuation (p : ℚ_[p]) ^ e := by
    have he_cast : (e : ℤ) = -WithZero.log (v p) := Int.toNat_of_nonneg (neg_nonneg.mpr hlog.le)
    rw [hmul_p, ← WithZero.exp_nsmul, nsmul_eq_mul, he_cast, neg_mul_neg, mul_one,
      WithZero.exp_log hvp0]
  refine ⟨e, ⟨he, fun x ↦ ?_⟩, fun d ⟨_, hd⟩ ↦ ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx
    · simp [zero_pow he.ne']
    · have hmul_x : Padic.mulValuation (x : ℚ_[p]) =
          Padic.mulValuation (p : ℚ_[p]) ^ x.valuation := by
        simpa using ((Padic.mulValuation (p := p)).comap
          (PadicInt.Coe.ringHom (p := p))).padicInt_apply_eq_pow_valuation hx
      rw [v.padicInt_apply_eq_pow_valuation hx, hmul_x, hvp, ← pow_mul, mul_comm e, pow_mul]
  · have hpow : Padic.mulValuation (p : ℚ_[p]) ^ d = Padic.mulValuation (p : ℚ_[p]) ^ e := by
      simpa only [PadicInt.coe_natCast, hvp] using (hd p).symm
    rw [hmul_p, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj,
      nsmul_eq_mul, nsmul_eq_mul, mul_neg_one, mul_neg_one, neg_inj, Nat.cast_inj] at hpow
    exact hpow

/-! ### `ℤᵐ⁰`-valued valuations on `ℚ_[p]` -/

/-- Any `ℤᵐ⁰`-valued valuation on `ℚ_[p]` takes the value `1` on every unit of `ℤ_[p]`. -/
theorem padic_coe_padicInt_units_eq_one (v : Valuation ℚ_[p] ℤᵐ⁰) (u : ℤ_[p]ˣ) :
    v (u : ℚ_[p]) = 1 :=
  (v.comap (PadicInt.Coe.ringHom (p := p))).padicInt_units_eq_one u

/-- Any `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is determined on nonzero elements by its value at `p`:
`v x = v p ^ x.valuation`. -/
theorem padic_apply_eq_zpow_valuation (v : Valuation ℚ_[p] ℤᵐ⁰) {x : ℚ_[p]} (hx : x ≠ 0) :
    v x = v p ^ x.valuation := by
  obtain ⟨u, hu⟩ := Padic.exists_eq_zpow_valuation_mul hx
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow₀, v.padic_coe_padicInt_units_eq_one u, mul_one]

/-- Any `ℤᵐ⁰`-valued valuation on `ℚ_[p]` satisfies `v p ≤ 1`. -/
theorem padic_natCast_self_le_one (v : Valuation ℚ_[p] ℤᵐ⁰) : v p ≤ 1 := by
  simpa using (v.comap (PadicInt.Coe.ringHom (p := p))).padicInt_natCast_self_le_one

/-- Any `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is bounded by `1` on `ℤ_[p]`. -/
theorem padic_coe_padicInt_le_one (v : Valuation ℚ_[p] ℤᵐ⁰) (x : ℤ_[p]) :
    v (x : ℚ_[p]) ≤ 1 :=
  (v.comap (PadicInt.Coe.ringHom (p := p))).padicInt_le_one x

/-- A `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is nontrivial if and only if `v p < 1`. -/
theorem padic_isNontrivial_iff (v : Valuation ℚ_[p] ℤᵐ⁰) :
    v.IsNontrivial ↔ v p < 1 := by
  constructor
  · intro hv
    refine lt_of_le_of_ne v.padic_natCast_self_le_one fun hp1 ↦ ?_
    obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
    exact hx1 (by rw [v.padic_apply_eq_zpow_valuation ((v.ne_zero_iff).mp hx0), hp1, one_zpow])
  · intro hp1
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    exact ⟨p, (v.ne_zero_iff).mpr hp0, hp1.ne⟩

/-- **Classification of `ℤᵐ⁰`-valued valuations on `ℚ_[p]`.** Every nontrivial valuation
`v : Valuation ℚ_[p] ℤᵐ⁰` is uniquely a positive integer power `Padic.mulValuation ^ e` of the
`p`-adic valuation. -/
theorem existsUnique_eq_padic_mulValuation_pow (v : Valuation ℚ_[p] ℤᵐ⁰) [v.IsNontrivial] :
    ∃! e : ℕ, 0 < e ∧ ∀ x : ℚ_[p], v x = Padic.mulValuation x ^ e := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hvp0 : v p ≠ 0 := (v.ne_zero_iff).mpr hp0
  have hvp1 : v p < 1 := v.padic_isNontrivial_iff.mp inferInstance
  let v₀ : Valuation ℤ_[p] ℤᵐ⁰ := v.comap (PadicInt.Coe.ringHom (p := p))
  have : v₀.IsNontrivial := v₀.padicInt_isNontrivial_iff.mpr
    ⟨by simpa [v₀, zero_lt_iff] using hvp0, by simpa [v₀] using hvp1⟩
  obtain ⟨e, ⟨he, hv₀⟩, huniq⟩ := v₀.existsUnique_eq_padicInt_mulValuation_pow
  have hvp : v p = Padic.mulValuation (p : ℚ_[p]) ^ e := by simpa [v₀] using hv₀ p
  refine ⟨e, ⟨he, fun x ↦ ?_⟩, fun d ⟨hd_pos, hd⟩ ↦ huniq d ⟨hd_pos, fun z ↦ hd z⟩⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_pow he.ne']
  · rw [v.padic_apply_eq_zpow_valuation hx,
      (Padic.mulValuation (p := p)).padic_apply_eq_zpow_valuation hx, hvp, ← zpow_natCast,
      ← zpow_mul, mul_comm (e : ℤ), zpow_mul, zpow_natCast]

/-- Every nontrivial `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is equivalent to `Padic.mulValuation`. -/
theorem isEquiv_padic_mulValuation (v : Valuation ℚ_[p] ℤᵐ⁰) [v.IsNontrivial] :
    v.IsEquiv Padic.mulValuation := by
  obtain ⟨e, he, hv⟩ := v.existsUnique_eq_padic_mulValuation_pow.exists
  intro x y
  rw [hv x, hv y]
  exact pow_le_pow_iff_left₀ zero_le zero_le he.ne'

/-- Every nontrivial `ℤᵐ⁰`-valued valuation on `ℚ_[p]` is compatible with the canonical `p`-adic
`ValuativeRel`. -/
theorem compatible_padic (v : Valuation ℚ_[p] ℤᵐ⁰) [v.IsNontrivial] :
    v.Compatible :=
  v.isEquiv_padic_mulValuation.symm.compatible

end Valuation

namespace ValuativeRel

private theorem padic_vle_iff_mulValuation_le {p : ℕ} [Fact p.Prime] (x y : ℚ_[p]) :
    x ≤ᵥ y ↔ Padic.mulValuation x ≤ Padic.mulValuation y :=
  Valuation.Compatible.vle_iff_le x y

/-- **Uniqueness of the discrete rank-one valuative relation on `ℚ_[p]`.** Any discrete,
nontrivial, rank-at-most-one `ValuativeRel` on `ℚ_[p]` coincides with its canonical `p`-adic
`ValuativeRel`. -/
theorem eq_padicInstValuativeRel {p : ℕ} [Fact p.Prime] (vr : ValuativeRel ℚ_[p])
    [@IsDiscrete ℚ_[p] _ vr] [@IsNontrivial ℚ_[p] _ vr] [@IsRankLeOne ℚ_[p] _ vr] :
    vr = Padic.instValuativeRel := by
  obtain ⟨e⟩ := (ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff (R := ℚ_[p])).mpr
    ⟨‹_›, ‹_›, isRankLeOne_iff_mulArchimedean.mp ‹_›⟩
  let w : Valuation ℚ_[p] ℤᵐ⁰ :=
    (valuation ℚ_[p]).map (e : ValueGroupWithZero ℚ_[p] →*₀o ℤᵐ⁰)
  have hw_equiv : w.IsEquiv (valuation ℚ_[p]) :=
    (valuation ℚ_[p]).isEquiv_map_self_of_strictMono _ e.injective
  have hw_compat : @Valuation.Compatible ℚ_[p] ℤᵐ⁰ _ _ w vr := hw_equiv.symm.compatible
  have : w.IsNontrivial := hw_equiv.isNontrivial_iff.mpr inferInstance
  have hw_padic := w.isEquiv_padic_mulValuation
  ext x y
  exact (hw_compat.vle_iff_le x y).trans
    ((hw_padic x y).trans (padic_vle_iff_mulValuation_le x y).symm)

end ValuativeRel

namespace TauCeti

/-- **Automatic valuation compatibility over `ℚ_[p]`.** Let `R` be an integral `ℚ_[p]`-algebra
equipped with a discrete, nontrivial, rank-at-most-one `ValuativeRel` — for instance, any finite
extension of `ℚ_[p]` carrying `[IsNonarchimedeanLocalField R]`. Then `ValuativeRel R` restricts
along `algebraMap ℚ_[p] R` to the canonical `p`-adic valuation on `ℚ_[p]`, i.e.,
`ValuativeExtension ℚ_[p] R` holds automatically. -/
theorem valuativeExtension_padic (p : ℕ) [Fact p.Prime] (R : Type*) [Ring R] [ValuativeRel R]
    [ValuativeRel.IsDiscrete R] [ValuativeRel.IsNontrivial R] [ValuativeRel.IsRankLeOne R]
    [Algebra ℚ_[p] R] [Algebra.IsIntegral ℚ_[p] R] :
    ValuativeExtension ℚ_[p] R := by
  obtain ⟨e⟩ :=
    (ValuativeRel.ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff (R := R)).mpr
      ⟨inferInstance, inferInstance, ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance⟩
  let w : Valuation R ℤᵐ⁰ :=
    (ValuativeRel.valuation R).map (e : ValuativeRel.ValueGroupWithZero R →*₀o ℤᵐ⁰)
  have hw_equiv : w.IsEquiv (ValuativeRel.valuation R) :=
    (ValuativeRel.valuation R).isEquiv_map_self_of_strictMono _ e.injective
  have hw_compat : w.Compatible := hw_equiv.symm.compatible
  have : w.IsNontrivial := hw_equiv.isNontrivial_iff.mpr inferInstance
  have : (w.comap (algebraMap ℚ_[p] R)).IsNontrivial := w.isNontrivial_comap_algebraMap
  have hpadic := (w.comap (algebraMap ℚ_[p] R)).compatible_padic
  exact ⟨fun {a b} ↦ by
    rw [hw_compat.vle_iff_le, ← Valuation.comap_apply, ← Valuation.comap_apply,
      ← hpadic.vle_iff_le]⟩

end TauCeti
