/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.SubgroupConductor.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Rat

import Mathlib.Data.Nat.Totient
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The conductor of the trivial subgroup of a ray class group of `ℚ`

The ray class group of `ℚ` modulo `(n)·∞` is `(ZMod n)ˣ` (`ratModulusEquivZMod`), and it is the
Galois group of `ℚ(ζ_n)/ℚ`. This file computes the conductor of its trivial subgroup, that is,
the least modulus `𝔣` of `ℚ` for which the transition map from `(n)·∞` to `𝔣` is injective:

* for `n ≤ 2` it is the trivial modulus, as the ray class group is trivial;
* for `n > 2` with `n` not `2` modulo `4` it is `(n)·∞`;
* for `n > 2` with `n` equal to `2` modulo `4` it is `(n / 2)·∞`.

The real place always occurs for `n > 2`, as the class of `-1` is nontrivial modulo `(n)·∞` but
trivial modulo `(n)`. For `n = 2d` with `d` odd the reduction `(ZMod n)ˣ → (ZMod d)ˣ` is a
bijection, which is why the finite part drops to `(d)`.

## Main results

* `Subgroup.rayClassConductor_bot_ratModulus_of_le_two`,
  `Subgroup.rayClassConductor_bot_ratModulus`, and
  `Subgroup.rayClassConductor_bot_ratModulus_of_mod_four_eq_two`: the conductor
  of the trivial subgroup of `RayClassGroup (ratModulus n _)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {n : ℕ} (hn : n ≠ 0)

/-- The ray class group of `ℚ` modulo `(n)·∞` has `φ n` elements. -/
@[simp] theorem card_rayClassGroup_ratModulus :
    Nat.card (RayClassGroup (ratModulus n hn)) = n.totient := by
  have : NeZero n := ⟨hn⟩
  rw [Nat.card_congr (ratModulusEquivZMod n hn).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

variable {hn}

/-- **The transition map from `(n)·∞` to `(d)·∞` is injective exactly when `φ n = φ d`.** It is
surjective, between finite groups of orders `φ n` and `φ d`. -/
theorem ker_classMap_ratModulus_eq_bot_iff {d : ℕ} {hd : d ≠ 0}
    (h : ratModulus d hd ∣ ratModulus n hn) :
    (classMap h).ker = ⊥ ↔ n.totient = d.totient := by
  rw [MonoidHom.ker_eq_bot_iff, ← card_rayClassGroup_ratModulus hn,
    ← card_rayClassGroup_ratModulus hd]
  exact ⟨fun hinj ↦ Nat.card_eq_of_bijective _ ⟨hinj, classMap_surjective h⟩,
    fun hc ↦ ((classMap_surjective h).bijective_of_nat_card_le hc.le).1⟩

-- A divisor of `(n)·∞` is `(d)·∞` or `(d)` for a divisor `d` of `n`.
private theorem exists_eq_ratModulus_or_eq_ratFiniteModulus {𝔫 : Modulus ℚ}
    (h : 𝔫 ∣ ratModulus n hn) :
    ∃ (d : ℕ) (hd : d ≠ 0), d ∣ n ∧ (𝔫 = ratModulus d hd ∨ 𝔫 = ratFiniteModulus d hd) := by
  have hd : Ideal.absNorm 𝔫.finitePart ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔫.finitePart_ne_bot
  have hspan := Rat.RingOfIntegers.ideal_span_absNorm_eq_self 𝔫.finitePart
  obtain ⟨hfin, hinf⟩ := Modulus.dvd_iff.mp h
  rw [← hspan, ratModulus_finitePart, Ideal.span_singleton_dvd_span_singleton_iff_dvd,
    Rat.RingOfIntegers.natCast_dvd_natCast] at hfin
  rw [ratModulus_infinitePart] at hinf
  refine ⟨_, hd, hfin, ?_⟩
  rcases Finset.subset_singleton_iff.mp hinf with hinf | hinf
  · exact Or.inr (Modulus.ext (by rw [ratFiniteModulus_finitePart, hspan])
      (by rw [ratFiniteModulus_infinitePart, hinf]))
  · exact Or.inl (Modulus.ext (by rw [ratModulus_finitePart, hspan])
      (by rw [ratModulus_infinitePart, hinf]))

-- For `n > 2` the transition map from `(n)·∞` to a modulus `(d)` without the real place is not
-- injective: the class of `-1` is nontrivial modulo `(n)·∞` and trivial modulo `(d)`.
private theorem ker_classMap_ratFiniteModulus_ne_bot (h2 : 2 < n) {d : ℕ} {hd : d ≠ 0}
    (h : ratFiniteModulus d hd ∣ ratModulus n hn) : (classMap h).ker ≠ ⊥ := by
  have h₁ : ratFiniteModulus d hd ∣ ratModulus d hd := ratFiniteModulus_dvd_ratModulus
  have h₂ : ratModulus d hd ∣ ratModulus n hn :=
    ratModulus_dvd_ratModulus_iff.mpr (ratFiniteModulus_dvd_ratModulus_iff.mp h)
  set c := (ratModulusEquivZMod n hn).symm (-1)
  have hc1 : c ≠ 1 := by
    have : Fact (2 < n) := ⟨h2⟩
    rw [Ne, MulEquiv.symm_apply_eq, map_one, Units.ext_iff]
    exact ZMod.neg_one_ne_one
  have hc₂ : classMap h₂ c = residueSignRayClass (ratModulus d hd) (1, fun _ ↦ -1) := by
    rw [← (ratModulusEquivZMod d hd).injective.eq_iff, ratModulusEquivZMod_classMap,
      ratModulusEquivZMod_residueSignRayClass_neg_one, MulEquiv.apply_symm_apply]
    have hdn := ratFiniteModulus_dvd_ratModulus_iff.mp h
    ext
    simp [ZMod.unitsMap_val, ZMod.cast_neg hdn, ZMod.cast_one hdn]
  have hc : classMap h c = 1 := by
    rw [← classMap_classMap h₁ h₂, hc₂]
    exact (classMap_eq_one_iff_of_finitePart_eq h₁ (by simp) _).mpr
      ⟨fun _ ↦ -1, fun w hw ↦ by simp at hw, rfl⟩
  exact fun hbot ↦ hc1 ((MonoidHom.ker_eq_bot_iff _).mp hbot (hc.trans (map_one _).symm))

end TauCeti.GlobalNumberFields

namespace Subgroup

open TauCeti.GlobalNumberFields

variable {n : ℕ} {hn : n ≠ 0}

/-- **The conductor of the trivial subgroup modulo `(n)·∞` for `n ≤ 2` is trivial**: the ray class
group is then trivial. -/
@[simp] theorem rayClassConductor_bot_ratModulus_of_le_two (h2 : n ≤ 2) :
    rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n hn))) = Modulus.one ℚ := by
  refine Modulus.eq_one_of_dvd_one ((rayClassConductor_dvd_iff (Modulus.one_dvd _) ⊥).mpr ?_)
  have : Subsingleton (RayClassGroup (ratModulus n hn)) := by
    rw [← Finite.card_le_one_iff_subsingleton, card_rayClassGroup_ratModulus,
      Nat.totient_eq_one_iff.mpr (by omega)]
  exact fun c _ ↦ (Subgroup.mem_bot).mpr (Subsingleton.elim c 1)

-- For `n > 2` the conductor of the trivial subgroup is `(d)·∞` for the least divisor `d` of `n`
-- with `φ d = φ n`.
private theorem exists_rayClassConductor_bot_ratModulus_eq (h2 : 2 < n) :
    ∃ (d : ℕ) (hd : d ≠ 0), d ∣ n ∧ n.totient = d.totient ∧
      rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n hn))) = ratModulus d hd ∧
      ∀ d' : ℕ, d' ≠ 0 → d' ∣ n → n.totient = d'.totient → d ∣ d' := by
  set 𝔣 := rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n hn)))
  have key {𝔫 : Modulus ℚ} (h : 𝔫 ∣ ratModulus n hn) : 𝔣 ∣ 𝔫 ↔ (classMap h).ker = ⊥ := by
    rw [rayClassConductor_dvd_iff h, le_bot_iff]
  obtain ⟨d, hd, hdn, heq | heq⟩ :=
    exists_eq_ratModulus_or_eq_ratFiniteModulus (rayClassConductor_dvd ⊥)
  · have h' : ratModulus d hd ∣ ratModulus n hn := heq ▸ rayClassConductor_dvd ⊥
    refine ⟨d, hd, hdn, (ker_classMap_ratModulus_eq_bot_iff h').mp
      ((key h').mp (heq ▸ Modulus.dvd_refl _)), heq, fun d' hd' hd'n hφ ↦ ?_⟩
    have h'' : ratModulus d' hd' ∣ ratModulus n hn := ratModulus_dvd_ratModulus_iff.mpr hd'n
    have := (key h'').mpr ((ker_classMap_ratModulus_eq_bot_iff h'').mpr hφ)
    have hf : 𝔣 = ratModulus d hd := heq
    rwa [hf, ratModulus_dvd_ratModulus_iff] at this
  · have h' : ratFiniteModulus d hd ∣ ratModulus n hn := heq ▸ rayClassConductor_dvd ⊥
    exact absurd ((key h').mp (heq ▸ Modulus.dvd_refl _))
      (ker_classMap_ratFiniteModulus_ne_bot h2 h')

/-- **The conductor of the trivial subgroup modulo `(n)·∞` is `(n)·∞`** for `n > 2` not equal to
`2` modulo `4`. -/
@[simp] theorem rayClassConductor_bot_ratModulus (h2 : 2 < n) (h4 : n % 4 ≠ 2) :
    rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n hn))) = ratModulus n hn := by
  obtain ⟨d, hd, hdn, hφ, heq, -⟩ := exists_rayClassConductor_bot_ratModulus_eq h2
  rcases Nat.eq_or_eq_of_totient_eq_totient hdn hφ.symm with hdn' | hnd
  · exact heq.trans (by subst hdn'; rfl)
  · have hodd : Odd d := Nat.not_even_iff_odd.mp fun hd ↦ by
      have := hd.eq_of_totient_eq_totient hdn hφ.symm
      omega
    obtain ⟨k, hk⟩ := hodd
    omega

/-- **The conductor of the trivial subgroup modulo `(n)·∞` is `(n / 2)·∞`** for `n > 2` equal to
`2` modulo `4`: reduction `(ZMod n)ˣ → (ZMod (n / 2))ˣ` is then a bijection. -/
@[simp] theorem rayClassConductor_bot_ratModulus_of_mod_four_eq_two (h2 : 2 < n) (h4 : n % 4 = 2) :
    rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus n hn))) =
      ratModulus (n / 2) (by omega) := by
  obtain ⟨d, hd, hdn, hφ, heq, hmin⟩ := exists_rayClassConductor_bot_ratModulus_eq h2
  -- `n / 2` is odd, so doubling it does not change its totient.
  have hodd : Odd (n / 2) := ⟨n / 4, by omega⟩
  have hn : n = 2 * (n / 2) := by omega
  have hφ' : n.totient = (n / 2).totient := calc
    n.totient = (2 * (n / 2)).totient := congrArg Nat.totient hn
    _ = (n / 2).totient := Nat.totient_two_mul_of_odd hodd
  have hdvd := hmin (n / 2) (by omega) (Nat.div_dvd_of_dvd (by omega)) hφ'
  rcases Nat.eq_or_eq_of_totient_eq_totient hdn hφ.symm with hdn' | hnd
  · exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  · refine heq.trans ?_
    congr 1
    omega

end Subgroup
