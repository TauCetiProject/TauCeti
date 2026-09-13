/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.ZMod.Units

/-!
# Units and coprimality over `ZMod d`

Results connecting unit and coprimality data over `ZMod d`, independent of one another:

* `Int.isUnit_intCast_iff_gcd_eq_one` — an integer is a *unit* mod `d` exactly when it is
  coprime to `d`. Its consumers are the Atkin-Lehner and bad-prime double-coset arguments in
  `TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/`, which need the `Int.gcd` form of the unit
  condition carried by membership of `Δ₀(N)`, and `Int.exists_nonneg_lt_and_dvd_mul_sub` in
  `TauCeti/Data/Int/LinearCongruence.lean`, which needs the other direction.
* `IsCoprime.exists_int_lifts` — a *pair* of coprime residues mod `d` lifts to a coprime pair
  of integers. Ported from the AINTLIB `LeanModularForms` project
  (`LeanModularForms/HeckeRIngs/GLn/SL2Surjection.lean`, Chris Birkbeck); its consumer is the
  strong approximation theorem `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective` in
  `TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Basic.lean`.
* `TauCeti.comp_unitsMap_eq_comp_unitsMap_of_comp_mul_left` — a lowered unit homomorphism
  stays lowered after restricting to a multiple of its modulus.
* `TauCeti.eq_comp_unitsMap_of_comp_unitsMap_eq` — a unit homomorphism that agrees with a lowered
  one after restriction along `ZMod.unitsMap` is itself that lowered one, read at the smaller
  modulus. Its consumers are the descent arguments of
  `TauCeti/NumberTheory/ModularForms/Newforms/Descent/`, which carry a nebentypus lowered modulo
  `M / p` along a chain of divisibilities.
-/

public section

variable {d : ℕ}

/-- **An integer is a unit mod `d` exactly when it is coprime to `d`.** The `Int.gcd` form is
what consumers of `Nat.Coprime` want; `ZMod.coe_int_isUnit_iff_isCoprime` states the same
equivalence with `IsCoprime` over `ℤ` on the right, in the opposite argument order. -/
theorem Int.isUnit_intCast_iff_gcd_eq_one {a : ℤ} :
    IsUnit ((a : ℤ) : ZMod d) ↔ Int.gcd a d = 1 :=
  (ZMod.coe_int_isUnit_iff_isCoprime _ _).trans
    (isCoprime_comm.trans Int.isCoprime_iff_gcd_eq_one)

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
theorem TauCeti.eq_comp_unitsMap_of_comp_unitsMap_eq {G : Type*} [Monoid G] {p M M' N' : ℕ}
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
theorem TauCeti.comp_unitsMap_eq_comp_unitsMap_of_comp_mul_left {G : Type*} [Monoid G]
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
