/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# The image of the cyclotomic character

This file reads two properties of the field `K` off the image of its `p`-adic cyclotomic
character `χ = localCyclotomicCharacter p K`.

* **Roots of unity of the base field.** The values of `χ` modulo `p ^ n` record the action of
  `Gal(K^alg/K)` on the `p ^ n`-th roots of unity. So when `p` is invertible in `K`, the image of
  `χ` lies in the principal unit group `U^(n) = 1 + p ^ n ℤ_p` exactly when `K` contains a
  primitive `p ^ n`-th root of unity.
* **A square root of `-2`.** If `2 ≠ 0` in `K` and `-2` is a square in `K`, every value of the
  `2`-adic character is `1` or `3` modulo `8`: a square root of `-2` in the algebraic closure is
  `ξ + ξ ^ 3` for a primitive eighth root of unity `ξ`, and it is negated by the automorphisms
  acting on `ξ` by the exponents `5` and `7`.
* **Infinitude over a finite extension of `ℚ_p`.** For `K` finite over `ℚ_p`, the image of `χ` is
  infinite. If it had `m` elements, every `p`-power root of unity would have at most `m`
  conjugates over `K`, hence degree at most `[K : ℚ_p] · m` over `ℚ_p`. This contradicts the
  irreducibility of the cyclotomic polynomials `Φ_{p ^ n}` over `ℚ_p`.

In the dyadic case these are the two inputs that, together with the classification of the closed
subgroups of `ℤ₂ˣ`, determine the image of `χ` in each branch of the marked classification.

## Main results

* `TauCeti.localCyclotomicCharacter_mem_unitsPrincipal`: if `μ_{p ^ n} ⊆ K`, every value of the
  cyclotomic character lies in `U^(n)`.
* `TauCeti.range_localCyclotomicCharacter_le_unitsPrincipal_iff`: if `p` is invertible in `K`,
  the image lies in `U^(n)` if and only if `μ_{p ^ n} ⊆ K`.
* `TauCeti.toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three`: if `-2` is a square in
  `K` and `2 ≠ 0` in `K`, every value of the `2`-adic cyclotomic character is `1` or `3` modulo
  `8`.
* `TauCeti.isClosed_range_localCyclotomicCharacter`: the image is closed, since the absolute
  Galois group is compact.
* `TauCeti.infinite_range_localCyclotomicCharacter`: the image is infinite when `K` is a finite
  extension of `ℚ_p`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]

/-- If `K` contains a primitive `p ^ n`-th root of unity, every value of the cyclotomic character
of `K` is a principal unit `≡ 1 mod p ^ n`. -/
theorem localCyclotomicCharacter_mem_unitsPrincipal {n : ℕ}
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n)) (σ : Field.absoluteGaloisGroup K) :
    localCyclotomicCharacter p K σ ∈ unitsPrincipal p n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [unitsPrincipal_zero]
    exact Subgroup.mem_top _
  obtain ⟨ζ, hζ⟩ := hmu
  -- Every automorphism fixes `ζ`, so it acts on the `p ^ n`-th roots of unity by the exponent `1`.
  -- A primitive `p ^ n`-th root of unity in `K` with `n > 0` forces `p ≠ 0` in `K`, so the
  -- algebraic closure has all `p`-power roots of unity and the defining equation applies.
  have : NeZero (p : K) := ⟨fun h ↦ hζ.neZero'.out (by rw [Nat.cast_pow, h, zero_pow hn.ne'])⟩
  have hξ : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) ζ) (p ^ n) :=
    hζ.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hspec := cyclotomicCharacter.spec p (n := n) σ.toRingEquiv
    (algebraMap K (AlgebraicClosure K) ζ) hξ.pow_eq_one
  have hmod := ((hξ.isOfFinOrder (pow_ne_zero n hp.out.ne_zero)).pow_eq_pow_iff_modEq).mp
    (((pow_one _).trans (σ.commutes ζ).symm).trans hspec)
  rw [← hξ.eq_orderOf] at hmod
  rw [mem_unitsPrincipal_iff_toZModPow, localCyclotomicCharacter_apply]
  set c := PadicInt.toZModPow n (cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv : ℤ_[p])
  rw [← ZMod.natCast_zmod_val c, ← Nat.cast_one (R := ZMod (p ^ n)), ZMod.natCast_eq_natCast_iff]
  exact hmod.symm

/-- If `K` contains a primitive `p ^ n`-th root of unity, the image of the cyclotomic character of
`K` lies in the principal unit group `U^(n) = 1 + p ^ n ℤ_p`. -/
theorem range_localCyclotomicCharacter_le_unitsPrincipal {n : ℕ}
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n)) :
    (localCyclotomicCharacter p K).range ≤ unitsPrincipal p n := by
  rintro _ ⟨σ, rfl⟩
  exact localCyclotomicCharacter_mem_unitsPrincipal hmu σ

/-- If `p` is invertible in `K`, the image of the cyclotomic character lies in the principal unit
group `U^(n) = 1 + p ^ n ℤ_p` exactly when `K` contains a primitive `p ^ n`-th root of unity. -/
theorem range_localCyclotomicCharacter_le_unitsPrincipal_iff [NeZero (p : K)] (n : ℕ) :
    (localCyclotomicCharacter p K).range ≤ unitsPrincipal p n ↔
      ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n) := by
  refine ⟨fun h ↦ ?_, range_localCyclotomicCharacter_le_unitsPrincipal⟩
  -- Every automorphism acts on a primitive `p ^ n`-th root of unity `ξ` of the algebraic closure
  -- by the exponent `1`, so it fixes `ξ`.
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
  have hfix (σ : Field.absoluteGaloisGroup K) : σ.toRingEquiv ξ = ξ := by
    have hσ := h ⟨σ, rfl⟩
    rw [mem_unitsPrincipal_iff_toZModPow, localCyclotomicCharacter_apply] at hσ
    have hspec := cyclotomicCharacter.spec p σ.toRingEquiv ξ hξ.pow_eq_one
    rw [hσ, ZMod.val_one_eq_one_mod, hξ.eq_orderOf, pow_mod_orderOf, pow_one] at hspec
    exact hspec
  -- `ξ` is fixed by every automorphism, so it is purely inseparable over `K`; it is also
  -- separable, as a root of `X ^ p ^ n - 1`, hence it lies in `K`.
  have hperf : ξ ∈ perfectClosure K (AlgebraicClosure K) :=
    mem_perfectClosure_iff_fixed.mpr fun σ ↦ hfix σ
  have hsep : IsSeparable K (⟨ξ, hperf⟩ : perfectClosure K (AlgebraicClosure K)) := by
    rw [IsSeparable, IntermediateField.minpoly_eq]
    refine (X_pow_sub_one_separable_iff.mpr
      (by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (p : K)))).of_dvd
      (minpoly.dvd K ξ ?_)
    simp [hξ.pow_eq_one]
  obtain ⟨ζ, hζ⟩ := IsPurelyInseparable.inseparable K _ hsep
  refine ⟨ζ, IsPrimitiveRoot.of_map_of_injective ?_ (algebraMap K (AlgebraicClosure K)).injective⟩
  rw [IsScalarTower.algebraMap_apply K (perfectClosure K (AlgebraicClosure K)), hζ]
  exact hξ

/-- **The cyclotomic character of a field containing `√-2`.** If `2 ≠ 0` in `K` and `s ^ 2 = -2`
for some `s ∈ K`, every value of the `2`-adic cyclotomic character of `K` is `1` or `3` modulo `8`.
Equivalently, `σ ζ = ζ` or `σ ζ = ζ ^ 3` for every primitive eighth root of unity `ζ` of the
algebraic closure. -/
theorem toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three [NeZero (2 : K)] {s : K}
    (hs : s ^ 2 = -2) (σ : Field.absoluteGaloisGroup K) :
    PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2]) = 1 ∨
      PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2]) = 3 := by
  have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (_root_.map_ne_zero _).2 (NeZero.ne 2)
  have : NeZero ((2 ^ 3 : ℕ) : AlgebraicClosure K) :=
    ⟨by rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_ne_zero 3 h2⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (2 ^ 3)
  have h4 : ξ ^ 4 = -1 :=
    (hξ.pow_of_dvd (by norm_num) (by norm_num : 4 ∣ 2 ^ 3)).eq_neg_one_of_two_right
  -- `ξ + ξ ^ 3` is a square root of `-2`, so it is `±s` and every automorphism fixes it.
  have ht2 : (ξ + ξ ^ 3) ^ 2 = -2 := by linear_combination (ξ ^ 2 + 2) * h4
  have hfix : σ.toRingEquiv (ξ + ξ ^ 3) = ξ + ξ ^ 3 := by
    have hst : (algebraMap K (AlgebraicClosure K) s) ^ 2 = (ξ + ξ ^ 3) ^ 2 := by
      rw [← map_pow, hs, ht2, map_neg, map_ofNat]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hst with h | h
    · rw [← h]
      exact σ.commutes s
    · rw [show ξ + ξ ^ 3 = -algebraMap K _ s by rw [h, neg_neg], map_neg]
      exact congrArg _ (σ.commutes s)
  -- `σ` raises `ξ` to the power `x.val`, an odd residue modulo `8`.
  have hspec := cyclotomicCharacter.spec 2 (n := 3) σ.toRingEquiv ξ hξ.pow_eq_one
  rw [← localCyclotomicCharacter_apply] at hspec
  set x := PadicInt.toZModPow 3 (localCyclotomicCharacter 2 K σ : ℤ_[2])
  have hcop : x.val.Coprime (2 ^ 3) := ZMod.val_coe_unit_coprime
    (Units.map (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)).toMonoidHom
      (localCyclotomicCharacter 2 K σ))
  have hlt : x.val < 8 := ZMod.val_lt x
  rw [map_add, map_pow, hspec, ← pow_mul] at hfix
  -- The exponents `5` and `7` send `ξ + ξ ^ 3` to its negative, which is impossible since it is
  -- a square root of `-2 ≠ 0`.
  have hne : ξ + ξ ^ 3 ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at ht2
    exact h2 ht2
  interval_cases hc : x.val
  · simp at hcop
  · exact .inl (by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_one])
  · norm_num at hcop
  · exact .inr (by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_ofNat])
  · norm_num at hcop
  · refine absurd ((mul_eq_zero.mp ?_).resolve_left h2) hne
    linear_combination (-1) * hfix + (ξ + ξ ^ 3 * (ξ ^ 8 - ξ ^ 4 + 1)) * h4
  · norm_num at hcop
  · refine absurd ((mul_eq_zero.mp ?_).resolve_left h2) hne
    linear_combination (-1) * hfix + (ξ ^ 3 + ξ * (ξ ^ 16 - ξ ^ 12 + ξ ^ 8 - ξ ^ 4 + 1)) * h4

variable (p K) in
/-- The image of the cyclotomic character is closed in `ℤ_pˣ`. -/
theorem isClosed_range_localCyclotomicCharacter :
    IsClosed ((localCyclotomicCharacter p K).range : Set ℤ_[p]ˣ) := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range (localCyclotomicCharacter_continuous p K)).isClosed

/-- A `p ^ n`-th root of unity `ξ` of the algebraic closure has degree over `K` at most the number
of values of the cyclotomic character: each conjugate of `ξ` is `σ ξ = ξ ^ (χ σ mod p ^ n)`. -/
private theorem natDegree_minpoly_le_ncard_range [CharZero K]
    (hfin : ((localCyclotomicCharacter p K).range : Set ℤ_[p]ˣ).Finite) {n : ℕ}
    {ξ : AlgebraicClosure K} (hξ : ξ ^ p ^ n = 1) :
    (minpoly K ξ).natDegree ≤ ((localCyclotomicCharacter p K).range : Set ℤ_[p]ˣ).ncard := by
  classical
  have hroots : (minpoly K ξ).rootSet (AlgebraicClosure K) ⊆
      (fun a : ℤ_[p]ˣ ↦ ξ ^ (PadicInt.toZModPow n (a : ℤ_[p])).val) ''
        (localCyclotomicCharacter p K).range := by
    intro y hy
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsIntegral.isIntegral (R := K) ξ).isAlgebraic (mem_rootSet.mp hy).2
    let τ : Field.absoluteGaloisGroup K := σ
    refine ⟨localCyclotomicCharacter p K τ, ⟨τ, rfl⟩, ?_⟩
    beta_reduce
    rw [← hσ, localCyclotomicCharacter_apply]
    exact (cyclotomicCharacter.spec p τ.toRingEquiv ξ hξ).symm
  rw [← card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable K ξ)
    (IsAlgClosed.splits ((minpoly K ξ).map (algebraMap K (AlgebraicClosure K)))),
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hroots (hfin.image _)).trans (Set.ncard_image_le hfin)

variable (p K) in
/-- The image of the cyclotomic character of a finite extension `K` of `ℚ_p` is infinite. -/
theorem infinite_range_localCyclotomicCharacter [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    Infinite (localCyclotomicCharacter p K).range := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  -- If the image had `m` elements, a primitive `p ^ n`-th root of unity would have at most `m`
  -- conjugates over `K`, so its degree `φ(p ^ n)` over `ℚ_p` would be at most `[K : ℚ_p] · m`.
  rw [← not_finite_iff_infinite]
  intro hfin
  set A : Set ℤ_[p]ˣ := ((localCyclotomicCharacter p K).range : Set ℤ_[p]ˣ)
  have hAfin : A.Finite := Set.finite_coe_iff.mp hfin
  set N := Module.finrank ℚ_[p] K
  set n := N * A.ncard + 1
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
  have hint : IsIntegral K ξ := Algebra.IsIntegral.isIntegral ξ
  have hK : (minpoly K ξ).natDegree ≤ A.ncard :=
    natDegree_minpoly_le_ncard_range hAfin hξ.pow_eq_one
  -- Over `ℚ_p`, the minimal polynomial of `ξ` is the irreducible cyclotomic polynomial.
  have hQ : (minpoly ℚ_[p] ξ).natDegree = (p ^ n).totient := by
    rw [← minpoly.eq_of_irreducible_of_monic (irreducible_cyclotomic_prime_pow_ratPadic p n)
      ?_ (cyclotomic.monic _ _), natDegree_cyclotomic]
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hξ.isRoot_cyclotomic (pow_pos hp.out.pos n)
  -- The degree over `ℚ_p` is at most `[K⟮ξ⟯ : ℚ_p] = [K : ℚ_p] · [K⟮ξ⟯ : K]`.
  have hle : (minpoly ℚ_[p] ξ).natDegree ≤ N * (minpoly K ξ).natDegree := by
    have := adjoin.finiteDimensional hint
    have : FiniteDimensional ℚ_[p] K⟮ξ⟯ := Module.Finite.trans K K⟮ξ⟯
    have h := minpoly.natDegree_le (A := ℚ_[p]) (AdjoinSimple.gen K ξ)
    rwa [← Module.finrank_mul_finrank ℚ_[p] K K⟮ξ⟯, adjoin.finrank hint,
      ← minpoly.algHom_eq ((K⟮ξ⟯).val.restrictScalars ℚ_[p]) (K⟮ξ⟯).val.injective] at h
  -- But `φ(p ^ n) = p ^ (N · #A) · (p - 1) > N · #A`.
  have hlt : N * A.ncard < (p ^ n).totient := by
    rw [Nat.totient_prime_pow_succ hp.out]
    have h1 : N * A.ncard < p ^ (N * A.ncard) := Nat.lt_pow_self hp.out.one_lt
    have h2 : 0 < p - 1 := by have := hp.out.two_le; omega
    exact h1.trans_le (Nat.le_mul_of_pos_right _ h2)
  have := hQ ▸ hle.trans (Nat.mul_le_mul_left N hK)
  omega

end TauCeti
