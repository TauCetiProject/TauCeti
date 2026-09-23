/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.Algebra.Group.Prod
import TauCeti.Data.ZMod.Torsion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi

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

/-- Torsion in a product of additive groups is equivalent to the product of the torsion groups. -/
private def torsionByPiEquiv {ι : Type*} (p : ℕ) (n : ι → ℕ) :
    AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ) ≃
      (∀ i, AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) :=
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
    rw [Nat.card_congr (torsionByPiEquiv p n), Nat.card_pi]
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha i]
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ha_pos i).ne'
        rw [hj]
        simpa only [Nat.card_zmod] using
          Nat.card_congr (TauCeti.zmodTorsionByEquiv p j).symm.toEquiv
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
      (LinearEquiv.finTwoArrow ℕ (ZMod (p ^ k))).toAddEquiv⟩

end AddCommGroup

end
