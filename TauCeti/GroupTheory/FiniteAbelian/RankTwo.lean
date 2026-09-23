/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Index

/-!
# Rank-two finite abelian groups of prime-power exponent

A finite abelian group killed by `p ^ k`, of order `p ^ (2 * k)`, and with exactly `p ^ 2`
elements killed by `p` is the product of two cyclic groups of order `p ^ k`.  This is the
rank-two prime-power case of the structure theorem for finite abelian groups.

The criterion is useful when the total order and the first torsion layer are easier to count than
explicit generators.  It determines both the number of cyclic factors and their exponents.

## Main result

* `AddCommGroup.nonempty_addEquiv_prod_zmod_primePow`: the rank-two characterisation.
-/

public section

namespace AddCommGroup

open scoped DirectSum

variable {G : Type*} [AddCommGroup G]

/-- The subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively equivalent to `ZMod p`. -/
private noncomputable def torsionByPrimeEquiv (p k : ℕ) [NeZero p] :
    ZMod p ≃+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) := by
  let P : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) :=
    ⟨(p ^ k : ZMod (p ^ (k + 1))), AddSubgroup.torsionBy.nsmul_iff.2 (by
      simp only [nsmul_eq_mul]
      rw [mul_comm, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self])⟩
  let f : ZMod p →+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) :=
    ZMod.lift p ⟨zmultiplesHom _ P, by
      exact (zmultiplesHom_apply _ P (p : ℤ)).trans <|
        (natCast_zsmul P p).trans (AddSubgroup.torsionBy.nsmul P)⟩
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · dsimp only [f]
    rw [ZMod.lift_injective]
    intro m hm
    have hm' : ((m * (p : ℤ) ^ k : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
      simpa [P, ZMod.lift_coe, zmultiplesHom_apply, mul_comm] using congrArg Subtype.val hm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hm'
    have hp0 : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne p)
    have hm'' : (p : ℤ) ^ k * p ∣ (p : ℤ) ^ k * m := by
      simpa [pow_succ, mul_comm] using hm'
    have hpm : (p : ℤ) ∣ m := by
      exact (mul_dvd_mul_iff_left hp0).mp hm''
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).2 hpm
  · intro x
    have hx : ((p : ℤ) : ZMod (p ^ (k + 1))) * x.1 = 0 := by
      simpa only [Int.cast_smul_eq_zsmul, zsmul_eq_mul] using
        (Submodule.mem_torsionBy_iff _ _).mp x.2
    have hdiv : p ^ k ∣ x.1.val := by
      rw [← ZMod.natCast_zmod_val x.1] at hx
      simp only [Int.cast_natCast] at hx
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
      have hx' : p * p ^ k ∣ p * x.1.val := by
        simpa only [pow_succ, mul_comm (p ^ k)] using hx
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne p))).mp hx'
    refine ⟨(((x.1.val / p ^ k : ℕ) : ℤ) : ZMod p), Subtype.ext ?_⟩
    dsimp only [f]
    rw [ZMod.lift_coe]
    simp only [zmultiplesHom_apply]
    rw [natCast_zsmul]
    -- `Subtype.ext` leaves equality in the ambient `ZMod`; its scalar action is inherited.
    change (x.1.val / p ^ k) • (p ^ k : ZMod (p ^ (k + 1))) = x.1
    rw [nsmul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_zmod_val]

/-- A product of two copies of an additive group, presented as functions on `Fin 2`. -/
private def finTwoAddEquivProd (A : Type*) [AddCommGroup A] : (Fin 2 → A) ≃+ A × A :=
  { finTwoArrowEquiv A with map_add' := fun _ _ ↦ rfl }

/-- **Rank-two prime-power characterisation.** A finite abelian group killed by `p ^ k`, with
order `p ^ (2 * k)` and `p ^ 2` elements killed by `p`, is additively equivalent to
`ZMod (p ^ k) × ZMod (p ^ k)`. -/
theorem nonempty_addEquiv_prod_zmod_primePow [Finite G] {p k : ℕ} (hp : p.Prime)
    (hpow : ∀ x : G, p ^ k • x = 0)
    (hcard : Nat.card G = p ^ (2 * k))
    (hcardp : Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ 2) :
    Nonempty (G ≃+ ZMod (p ^ k) × ZMod (p ^ k)) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let E : G ≃+ (∀ i : ι, ZMod (n i)) := e.trans (DirectSum.addEquivProd _)
  have hn_dvd (i : ι) : n i ∣ p ^ k := by
    let x : (j : ι) → ZMod (n j) := Function.update 0 i 1
    have hx : p ^ k • x = 0 := by
      simpa using congrArg E (hpow (E.symm x))
    have hxi := congrFun hx i
    have hxi' : ((p ^ k : ℕ) : ZMod (n i)) = 0 := by
      simpa [x, nsmul_eq_mul] using hxi
    exact (ZMod.natCast_eq_zero_iff (p ^ k) (n i)).mp hxi'
  choose a ha_le ha using fun i ↦ (Nat.dvd_prime_pow hp).mp (hn_dvd i)
  have ha_pos (i : ι) : 0 < a i := by
    rw [Nat.pos_iff_ne_zero]
    intro hai
    simpa [ha i, hai] using hn i
  have hcard_prod : ∏ i, n i = p ^ (2 * k) := by
    rw [← hcard, Nat.card_congr E.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]
  have hcard_torsion_pi :
      Nat.card (AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ)) = p ^ Fintype.card ι := by
    let T : AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ) ≃
        (∀ i : ι, AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) :=
      { toFun := fun x i ↦ ⟨x.1 i, by
          -- Torsion membership in a product is pointwise scalar annihilation.
          change (p : ℤ) • x.1 i = 0
          have hx : (p : ℤ) • x.1 = 0 := x.2
          exact congrFun hx i⟩
        invFun := fun x ↦ ⟨fun i ↦ x i, by
          -- The scalar action and zero of a dependent function are defined pointwise.
          change (p : ℤ) • (fun i ↦ (x i : ZMod (n i))) = 0
          funext i
          exact (x i).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr T, Nat.card_pi]
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha i]
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ha_pos i).ne'
        rw [hj]
        simpa only [Nat.card_zmod] using
          Nat.card_congr (torsionByPrimeEquiv p j).symm.toEquiv
      _ = p ^ Fintype.card ι := by simp
  have hmap : (AddSubgroup.torsionBy G (p : ℤ)).map E.toAddMonoidHom =
      AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ) := by
    ext x
    rw [AddSubgroup.mem_map_equiv]
    -- Membership in both torsion subgroups unfolds to the displayed annihilation equations.
    change (p : ℤ) • E.symm x = 0 ↔ (p : ℤ) • x = 0
    constructor
    · intro hx
      simpa using congrArg E hx
    · intro hx
      apply E.injective
      simpa using hx
  have hιcard : Fintype.card ι = 2 := by
    have ht : p ^ Fintype.card ι = p ^ 2 := by
      rw [← hcard_torsion_pi, ← hcardp, ← hmap]
      exact Nat.card_congr
        (AddSubgroup.equivMapOfInjective _ E.toAddMonoidHom E.injective).symm.toEquiv
    exact Nat.pow_right_injective hp.two_le ht
  have hsum : ∑ i, a i = 2 * k := by
    apply Nat.pow_right_injective hp.two_le
    -- Applying injectivity exposes equality after applying the power function.
    change p ^ (∑ i, a i) = p ^ (2 * k)
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ a p]
    simp only [← ha, hcard_prod]
  have ha_eq (i : ι) : a i = k := by
    apply le_antisymm (ha_le i)
    by_contra hki
    have hai : a i < k := Nat.lt_of_not_ge hki
    have hlt : ∑ j, a j < ∑ _j : ι, k :=
      Finset.sum_lt_sum (fun j _ ↦ ha_le j) ⟨i, Finset.mem_univ i, hai⟩
    simp only [Finset.sum_const, Finset.card_univ, hιcard, nsmul_eq_mul] at hlt
    omega
  let r : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hιcard
  refine ⟨E |>.trans (AddEquiv.piCongrRight fun i ↦
      (ZMod.ringEquivCongr (by rw [ha i, ha_eq i])).toAddEquiv) |>.trans
      (AddEquiv.arrowCongr r (AddEquiv.refl (ZMod (p ^ k)))) |>.trans
      (finTwoAddEquivProd (ZMod (p ^ k)))⟩

end AddCommGroup

end
