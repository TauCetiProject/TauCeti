/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude, Wentao Li
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.ZMod.Units
public import TauCeti.Data.Nat.GCD

/-!
# Units and coprimality over `ZMod d`

Results connecting unit and coprimality data over `ZMod d`, independent of one another:

* `ZMod.isUnit_two_of_algebra` — two is a unit in every commutative `ZMod 3`-algebra.
  Its consumers are the short-root G₂ carrier's torus centralizer, positive-root factorization,
  and standard-comodule flag arguments.
* `Int.isUnit_intCast_iff_gcd_eq_one` — an integer is a *unit* mod `d` exactly when it is
  coprime to `d`. Its consumers are the Atkin-Lehner and bad-prime double-coset arguments in
  `TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/`, which need the `Int.gcd` form of the unit
  condition carried by membership of `Δ₀(N)`, and `Int.exists_nonneg_lt_and_dvd_mul_sub` in
  `TauCeti/Data/Int/LinearCongruence.lean`, which needs the other direction.
* `ZMod.isUnit_intCast_two_pow_of_odd` — an odd integer is a unit modulo every power
  of two, including the trivial modulus at exponent zero.
* `IsCoprime.exists_int_lifts` — a *pair* of coprime residues mod `d` lifts to a coprime pair
  of integers. Ported from the AINTLIB `LeanModularForms` project
  (`LeanModularForms/HeckeRIngs/GLn/SL2Surjection.lean`, Chris Birkbeck); its consumer is the
  strong approximation theorem `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` in
  `TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Basic.lean`.
* `TauCeti.comp_unitsMap_eq_comp_unitsMap_of_comp_mul_left` — a lowered unit homomorphism
  stays lowered after restricting to a multiple of its modulus.
* `ZMod.exists_unitOfCoprime_eq` — every unit of `ZMod d` is `ZMod.unitOfCoprime` of a natural
  number coprime to `d`, so a statement about all units may be checked on those.
* `ZMod.unitOfCoprime_mul` — `ZMod.unitOfCoprime` is multiplicative in its numerator.
* `TauCeti.eq_comp_unitsMap_of_comp_unitsMap_eq` — a unit homomorphism that agrees with a lowered
  one after restriction along `ZMod.unitsMap` is itself that lowered one, read at the smaller
  modulus. Its consumers are the descent arguments of
  `TauCeti/NumberTheory/ModularForms/Newforms/Descent/`, which carry a nebentypus lowered modulo
  `M / p` along a chain of divisibilities.
* `ZMod.zmultiples_coe_unit_eq_top` — a unit of `ZMod d` generates `ZMod d` additively, so that
  translation by it is a single cycle; its consumer is the genus-one Heegaard diagram of a lens
  space in `TauCeti/LowDimTopology/Heegaard/LensSpace.lean`.
* `ZMod.eq_of_cast_eq_of_coprime` — the uniqueness half of the Chinese remainder theorem: two
  residues modulo `a * b`, with `a` and `b` coprime, that agree modulo `a` and modulo `b` are
  equal. Its consumer is the cyclotomic normalization of the local Artin map in
  `TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean`.
* `TauCeti.ZMod.orderOf_unitOfCoprime_pow_sub_one` — for `q > 1` and `N > 0`, the class of `q`
  in `(ZMod (q ^ N - 1))ˣ` has exact order `N`; the coprimality it needs is
  `Nat.coprime_pow_sub_one` from `TauCeti/Data/Nat/GCD.lean`. Its consumers are the cyclotomic
  input to global class field theory in
  `TauCeti/NumberTheory/ClassFieldTheory/Global/Cyclotomic/Input.lean` and the cyclotomic
  normalization of the local Artin map in
  `TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean`.
-/

public section

variable {d : ℕ}

/-- Two is a unit in every commutative `ZMod 3`-algebra. -/
theorem ZMod.isUnit_two_of_algebra (A : Type*) [CommRing A] [Algebra (ZMod 3) A] :
    IsUnit (2 : A) := by
  have h : IsUnit (2 : ZMod 3) := by decide
  simpa only [map_ofNat] using h.map (algebraMap (ZMod 3) A)

/-- **An integer is a unit mod `d` exactly when it is coprime to `d`.** The `Int.gcd` form is
what consumers of `Nat.Coprime` want; `ZMod.coe_int_isUnit_iff_isCoprime` states the same
equivalence with `IsCoprime` over `ℤ` on the right, in the opposite argument order. -/
theorem Int.isUnit_intCast_iff_gcd_eq_one {a : ℤ} :
    IsUnit ((a : ℤ) : ZMod d) ↔ Int.gcd a d = 1 :=
  (ZMod.coe_int_isUnit_iff_isCoprime _ _).trans
    (isCoprime_comm.trans Int.isCoprime_iff_gcd_eq_one)

/-- An odd integer is a unit modulo any power of two, including exponent zero. -/
theorem ZMod.isUnit_intCast_two_pow_of_odd (n : ℕ) {a : ℤ} (ha : Odd a) :
    IsUnit (a : ZMod (2 ^ n)) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime a (2 ^ n)).mpr
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using (ha.isCoprime_two.pow_right (n := n)).symm

private lemma isCoprime_emod {a₁ c₁ : ℤ}
    (hac : IsCoprime (a₁ : ZMod d) (c₁ : ZMod d)) :
    IsCoprime (c₁ : ZMod d) ((a₁ % c₁ : ℤ) : ZMod d) := by
  have h : (a₁ % c₁ : ℤ) = a₁ + c₁ * (-(a₁ / c₁)) := by rw [Int.emod_def]; ring
  rw [h]
  push_cast
  exact hac.symm.add_mul_left_right _

/-- **A lowered unit homomorphism is determined at the smaller modulus.** If `χM` is pulled back
from `χ₀` modulo `M / p`, and `χ'` modulo `N'` agrees with `χM` after restriction to the units
modulo a common multiple `M'`, then `χ'` is itself pulled back from `χ₀`, along `N' / p`.
`ZMod.unitsMap` is surjective onto the units of a divisor, so the restriction can be cancelled. -/
theorem TauCeti.eq_comp_unitsMap_of_comp_unitsMap_eq {G : Type*} [MulOne G] {p M M' N' : ℕ}
    [NeZero M'] (hpM : p ∣ M) (hMN' : M ∣ N') (hN'M' : N' ∣ M')
    {χM : (ZMod M)ˣ →* G} {χ₀ : (ZMod (M / p))ˣ →* G}
    (hcomp : χM = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) {χ' : (ZMod N')ˣ →* G}
    (h : χ'.comp (ZMod.unitsMap hN'M') = χM.comp (ZMod.unitsMap (hMN'.trans hN'M'))) :
    χ' = (χ₀.comp (ZMod.unitsMap
        ((Nat.div_dvd_div_iff_right hpM (hpM.trans hMN')).mpr hMN'))).comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (hpM.trans hMN'))) := by
  rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp] at h
  refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective hN'M')).mp (h.trans ?_)
  rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, ZMod.unitsMap_comp, ZMod.unitsMap_comp]

/-- **A lowered unit homomorphism stays lowered after restricting to a multiple.** If `χ` modulo
`N` is pulled back from `χ₀` modulo `N / p`, then restricting `χ` to the units modulo `N * L` is
again a pull-back of `χ₀`, now along `N * L / p`. Both sides collapse to one `ZMod.unitsMap` by
`ZMod.unitsMap_comp`. -/
theorem TauCeti.comp_unitsMap_eq_comp_unitsMap_of_comp_mul_left {G : Type*} [MulOne G]
    {p N L : ℕ} (hpN : p ∣ N) {χ : (ZMod N)ˣ →* G} {χ₀ : (ZMod (N / p))ˣ →* G}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    χ.comp (ZMod.unitsMap (dvd_mul_left N L)) =
      (χ₀.comp (ZMod.unitsMap (Nat.mul_div_assoc L hpN ▸ dvd_mul_left (N / p) L))).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hpN L))) := by
  rw [hcomp, MonoidHom.comp_assoc, ZMod.unitsMap_comp, MonoidHom.comp_assoc, ZMod.unitsMap_comp]


/-- Coprime residues modulo `d` lift to coprime integers: if `a` and `c` are coprime in
`ZMod d`, there are integers `a₀`, `c₀` reducing to `a`, `c` with `IsCoprime a₀ c₀`. -/
theorem IsCoprime.exists_int_lifts {a c : ZMod d}
    (hac : IsCoprime a c) :
    ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a ∧ (c₀ : ZMod d) = c ∧ IsCoprime a₀ c₀ := by
  obtain ⟨a₁, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨c₁, rfl⟩ := ZMod.intCast_surjective c
  suffices h : ∀ n, ∀ a₁ c₁ : ℤ, c₁.natAbs ≤ n →
      IsCoprime (a₁ : ZMod d) (c₁ : ZMod d) →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = c₁ ∧ IsCoprime a₀ c₀ from
    h c₁.natAbs a₁ c₁ le_rfl hac
  have zero_case : ∀ a₁ : ℤ, IsCoprime (a₁ : ZMod d) 0 →
      ∃ a₀ c₀ : ℤ,
        (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = 0 ∧ IsCoprime a₀ c₀ := by
    intro a₁ hac
    have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
    exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
  intro n
  induction n with
  | zero =>
    intro a₁ c₁ hle hac
    have hc₁ : c₁ = 0 := by omega
    subst hc₁
    simpa using zero_case a₁ (by simpa using hac)
  | succ n ih =>
    intro a₁ c₁ hle hac
    by_cases hc₁ : c₁ = 0
    · subst hc₁; simpa using zero_case a₁ (by simpa using hac)
    obtain ⟨c₀, r₀, hc₀, hr₀, hcop⟩ := ih c₁ (a₁ % c₁)
      (Nat.lt_succ_iff.mp ((EuclideanDomain.remainder_lt a₁ hc₁).trans_le hle)) (isCoprime_emod hac)
    refine ⟨r₀ + a₁ / c₁ * c₀, c₀, ?_, hc₀, hcop.symm.add_mul_right_left _⟩
    conv_rhs => rw [← Int.emod_add_ediv_mul a₁ c₁]
    push_cast
    rw [hr₀, hc₀]

/-- **Every unit of `ZMod d` is `ZMod.unitOfCoprime` of a natural number coprime to `d`.**
A property of all units may therefore be checked on the units of this shape. -/
theorem ZMod.exists_unitOfCoprime_eq [NeZero d] (u : (ZMod d)ˣ) :
    ∃ (m : ℕ) (hm : Nat.Coprime m d), ZMod.unitOfCoprime m hm = u :=
  ⟨(u : ZMod d).val, ZMod.val_coe_unit_coprime u, ZMod.unitsEquivCoprime.symm_apply_apply u⟩

-- Deliberately not `@[simp]`: the right-hand side needs coprimality proofs for `m` and `n`
-- separately, which `simp` cannot synthesise from the left-hand side, so Mathlib's `simpNF`
-- linter reports that the lemma would never apply.
/-- **`ZMod.unitOfCoprime` is multiplicative in its numerator.** -/
theorem ZMod.unitOfCoprime_mul {m n : ℕ} (hm : Nat.Coprime m d) (hn : Nat.Coprime n d) :
    ZMod.unitOfCoprime (m * n) (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩)
      = ZMod.unitOfCoprime m hm * ZMod.unitOfCoprime n hn :=
  Units.ext (by push_cast [ZMod.coe_unitOfCoprime]; ring)

/-- A unit of `ZMod d` generates `ZMod d` as an additive group. -/
theorem ZMod.zmultiples_coe_unit_eq_top (u : (ZMod d)ˣ) :
    AddSubgroup.zmultiples (u : ZMod d) = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).mpr fun y => ?_
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (y * ((u⁻¹ : (ZMod d)ˣ) : ZMod d))
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [zsmul_eq_mul, hk, Units.inv_mul_cancel_right]⟩

/-- **Chinese remainder uniqueness.** If `a` and `b` are coprime, two elements of `ZMod (a * b)`
with the same reductions modulo `a` and modulo `b` are equal. -/
theorem ZMod.eq_of_cast_eq_of_coprime {a b : ℕ} (h : a.Coprime b) {x y : ZMod (a * b)}
    (ha : (x.cast : ZMod a) = y.cast) (hb : (x.cast : ZMod b) = y.cast) : x = y := by
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
  rw [ZMod.cast_intCast (dvd_mul_right a b), ZMod.cast_intCast (dvd_mul_right a b),
    ZMod.intCast_eq_intCast_iff_dvd_sub] at ha
  rw [ZMod.cast_intCast (dvd_mul_left b a), ZMod.cast_intCast (dvd_mul_left b a),
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hb
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Nat.cast_mul]
  exact h.isCoprime.mul_dvd ha hb

namespace TauCeti

namespace ZMod

/-- **The order of the residue-cardinality class.** If `q > 1` and `N > 0`, the class of `q` in
`(ZMod (q ^ N - 1))ˣ` has exact order `N`. This is the elementary arithmetic behind the choice of
cyclotomic modulus in Milne's global existence argument. -/
theorem orderOf_unitOfCoprime_pow_sub_one (q N : ℕ) (hq : 1 < q) (hN : N ≠ 0) :
    orderOf (ZMod.unitOfCoprime q (Nat.coprime_pow_sub_one q N hq hN)) = N := by
  let _ : NeZero (q ^ N - 1) := ⟨by
    have : 1 < q ^ N := one_lt_pow₀ hq hN
    omega⟩
  let m := q ^ N - 1
  let u := ZMod.unitOfCoprime q (Nat.coprime_pow_sub_one q N hq hN)
  have hpow : 1 ≤ q ^ N := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero N (Nat.ne_zero_of_lt hq))
  have huN : u ^ N = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow]
    simpa only [Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (q ^ N) 1 m).2 (Nat.ModEq.symm <|
        (Nat.modEq_iff_dvd' hpow).2 dvd_rfl)
  have hdvd : orderOf u ∣ N := orderOf_dvd_of_pow_eq_one huN
  apply Nat.dvd_antisymm hdvd
  by_contra hnot
  have hdle : orderOf u ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
  have hdlt : orderOf u < N := lt_of_le_of_ne hdle fun h ↦ hnot (h.symm ▸ dvd_rfl)
  have hu := pow_orderOf_eq_one u
  have hmod : q ^ orderOf u ≡ 1 [MOD m] := by
    have hu' := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at hu'
    apply (ZMod.natCast_eq_natCast_iff (q ^ orderOf u) 1 m).1
    rw [Nat.cast_pow]
    simpa only [Nat.cast_one] using hu'
  have hqpow : 1 ≤ q ^ orderOf u := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ (Nat.ne_zero_of_lt hq))
  have hm_dvd : m ∣ q ^ orderOf u - 1 :=
    (Nat.modEq_iff_dvd' hqpow).1 hmod.symm
  have hsmall : q ^ orderOf u - 1 < m := by
    dsimp [m]
    have := Nat.pow_lt_pow_right hq hdlt
    omega
  exact (Nat.not_dvd_of_pos_of_lt (by
    have hdpos := orderOf_pos u
    have : 1 < q ^ orderOf u := one_lt_pow₀ hq hdpos.ne'
    omega) hsmall) hm_dvd

end ZMod

end TauCeti
