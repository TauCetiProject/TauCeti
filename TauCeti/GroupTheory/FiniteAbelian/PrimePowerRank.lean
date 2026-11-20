/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.GroupTheory.Rank
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Pi
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Data.ZMod.Torsion

/-!
# Rank and `p`-torsion of finite abelian `p`-groups and `ZMod` products

For any `n ≠ 1` and finite index type `ι`, the product `ι → ZMod n` has minimal generator number
`AddGroup.rank (ι → ZMod n) = Fintype.card ι`. For a finite abelian `p`-group `G`
(`Nat.card G = p ^ e`), every nontrivial cyclic invariant factor contributes a factor of `p` to the
`p`-torsion subgroup `G[p]`, yielding `Nat.card (AddSubgroup.torsionBy G (p : ℤ)) =
p ^ AddGroup.rank G` and additivity of `AddGroup.rank` under direct products of finite abelian
`p`-groups.

Combined with an exponent bound, a finite abelian group killed by `p ^ k` of order `p ^ (r * k)` and
with `p ^ r` elements killed by `p` is additively equivalent to `Fin r → ZMod (p ^ k)`.

## Main statements

* `AddGroup.rank_zmod`, `AddGroup.rank_pi_zmod`, `AddGroup.rank_zmod_prod_self`, and
  `AddGroup.rank_pi_zmod_of_prime_dvd`: `AddGroup.rank` of `ZMod n`, `ι → ZMod n`,
  `ZMod n × ZMod n`, and heterogeneous `ZMod` products sharing a prime divisor.
* `TauCeti.AddCommGroup.natCard_torsionBy_eq_pow_rank`: for a finite abelian `p`-group `G`,
  `Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ AddGroup.rank G`.
* `TauCeti.AddCommGroup.rank_prod_of_prime_pow_card`: `AddGroup.rank (G × H) = AddGroup.rank G +
  AddGroup.rank H` for finite abelian `p`-groups `G` and `H`.
* `TauCeti.AddCommGroup.nonempty_addEquiv_pi_zmod_primePow` and
  `TauCeti.AddCommGroup.nonempty_addEquiv_prod_zmod_primePow`: homogeneous prime-power
  characterisations.
-/

public section

namespace AddGroup

/-- The rank of `ZMod n` is `0` when `n = 1` and `1` otherwise. -/
theorem rank_zmod (n : ℕ) : AddGroup.rank (ZMod n) = if n = 1 then 0 else 1 := by
  split_ifs with hn
  · subst hn
    exact AddGroup.rank_eq_zero _
  · have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn
    exact AddGroup.rank_eq_one_of_isAddCyclic (ZMod n)

private theorem rank_pi_zmod_prime (ι : Type*) [Fintype ι] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (ι → ZMod p) = Fintype.card ι := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  apply le_antisymm
  · calc AddGroup.rank (ι → ZMod p)
        ≤ ∑ _i : ι, AddGroup.rank (ZMod p) := AddGroup.rank_pi_le _
      _ = ∑ _i : ι, 1 := by simp [rank_zmod p, hp.ne_one]
      _ = Fintype.card ι := by simp
  · obtain ⟨S, hScard, hS⟩ := AddGroup.rank_spec (ι → ZMod p)
    let φ : (S → ZMod p) →+ (ι → ZMod p) :=
      { toFun := fun c ↦ ∑ s : S, c s • s.1
        map_zero' := by simp
        map_add' := fun a b ↦ by simp [add_smul, Finset.sum_add_distrib] }
    have hφ_apply (c : S → ZMod p) : φ c = ∑ s : S, c s • s.1 := rfl
    have hφ : Function.Surjective φ := by
      rw [← AddMonoidHom.range_eq_top, eq_top_iff, ← hS, AddSubgroup.closure_le]
      intro v hv
      exact ⟨Pi.single ⟨v, hv⟩ 1, (hφ_apply _).trans <|
        (Fintype.sum_eq_single ⟨v, hv⟩ fun s hs ↦ by rw [Pi.single_eq_of_ne hs, zero_smul]).trans
          (by rw [Pi.single_eq_same, one_smul])⟩
    have hle : Fintype.card (ι → ZMod p) ≤ Fintype.card (S → ZMod p) :=
      Fintype.card_le_of_surjective φ hφ
    simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      hScard] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

/-- For `n ≠ 1`, the rank of a finite product `ι → ZMod n` equals `Fintype.card ι`. -/
theorem rank_pi_zmod {ι : Type*} [Fintype ι] {n : ℕ} (hn : n ≠ 1) :
    AddGroup.rank (ι → ZMod n) = Fintype.card ι := by
  apply le_antisymm
  · calc AddGroup.rank (ι → ZMod n)
        ≤ ∑ _i : ι, AddGroup.rank (ZMod n) := AddGroup.rank_pi_le _
      _ = ∑ _i : ι, 1 := by simp [rank_zmod n, hn]
      _ = Fintype.card ι := by simp
  · let p : ℕ := if n = 0 then 2 else n.minFac
    have hp : p.Prime := by
      dsimp [p]
      split_ifs with h0
      · exact Nat.prime_two
      · exact Nat.minFac_prime hn
    have hdvd : p ∣ n := by
      dsimp [p]
      split_ifs with h0
      · simp [h0]
      · exact Nat.minFac_dvd n
    let : NeZero p := ⟨hp.ne_zero⟩
    let f : (ι → ZMod n) →+ (ι → ZMod p) :=
      { toFun := fun x i ↦ ZMod.castHom hdvd (ZMod p) (x i)
        map_zero' := funext fun _ ↦ map_zero _
        map_add' := fun _ _ ↦ funext fun _ ↦ map_add _ _ _ }
    have hf : Function.Surjective f := fun y ↦
      ⟨fun i ↦ ((y i).val : ZMod n), funext fun i ↦ by
        dsimp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [map_natCast, ZMod.natCast_zmod_val]⟩
    rw [← rank_pi_zmod_prime ι hp]
    exact AddGroup.rank_le_of_surjective f hf

/-- For `n ≠ 1`, the direct product `ZMod n × ZMod n` has rank `2`. -/
theorem rank_zmod_prod_self {n : ℕ} (hn : n ≠ 1) :
    AddGroup.rank (ZMod n × ZMod n) = 2 := by
  rw [AddGroup.rank_congr (LinearEquiv.finTwoArrow ℕ (ZMod n)).symm.toAddEquiv, rank_pi_zmod hn]
  simp

end AddGroup

namespace TauCeti.AddCommGroup

open scoped DirectSum

variable {G : Type*} [AddCommGroup G]

/-- **Rank-`r` prime-power characterisation.** An abelian group killed by `p ^ k`, with
order `p ^ (r * k)` and `p ^ r` elements killed by `p`, is additively equivalent to
`Fin r → ZMod (p ^ k)`. -/
theorem nonempty_addEquiv_pi_zmod_primePow {p k r : ℕ} (hp : p.Prime)
    (hpow : ∀ x : G, p ^ k • x = 0)
    (hcard : Nat.card G = p ^ (r * k))
    (hcardp : Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ r) :
    Nonempty (G ≃+ (Fin r → ZMod (p ^ k))) := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let E : G ≃+ (∀ i : ι, ZMod (n i)) := e.trans (DirectSum.addEquivProd _)
  -- Each cyclic factor has order dividing the exponent of `G`.
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
  have hcard_prod : ∏ i, n i = p ^ (r * k) := by
    rw [← hcard, Nat.card_congr E.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]
  -- Every nontrivial cyclic factor contributes exactly `p` points to the first torsion layer.
  have hcard_torsion_pi :
      Nat.card (AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ)) = p ^ Fintype.card ι := by
    rw [Nat.card_congr (TauCeti.AddSubgroup.torsionByPiEquiv (fun i ↦ ZMod (n i)) (p : ℤ)).toEquiv,
      Nat.card_pi]
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha i]
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ha_pos i).ne'
        rw [hj, pow_succ']
        simpa only [Nat.card_zmod] using
          Nat.card_congr (TauCeti.zmodTorsionByEquiv p (p ^ j)).symm.toEquiv
      _ = p ^ Fintype.card ι := by simp
  have hιcard : Fintype.card ι = r := by
    have ht : p ^ Fintype.card ι = p ^ r := by
      rw [← hcard_torsion_pi, ← hcardp]
      exact Nat.card_congr (AddEquiv.torsionByCongr E (p : ℤ)).symm.toEquiv
    exact Nat.pow_right_injective hp.two_le ht
  have hsum : ∑ i, a i = r * k := by
    apply Nat.pow_right_injective hp.two_le
    dsimp only
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ a p]
    simp only [← ha, hcard_prod]
  have ha_eq (i : ι) : a i = k := by
    apply le_antisymm (ha_le i)
    by_contra hki
    have hai : a i < k := Nat.lt_of_not_ge hki
    have hlt : ∑ j, a j < ∑ _j : ι, k :=
      Finset.sum_lt_sum (fun j _ ↦ ha_le j) ⟨i, Finset.mem_univ i, hai⟩
    simp only [Finset.sum_const, Finset.card_univ, hιcard, nsmul_eq_mul, Nat.cast_id] at hlt
    omega
  let e : ι ≃ Fin r := Fintype.equivFinOfCardEq hιcard
  refine ⟨E |>.trans (AddEquiv.piCongrRight fun i ↦
      (ZMod.ringEquivCongr (by rw [ha i, ha_eq i])).toAddEquiv) |>.trans
      (AddEquiv.arrowCongr e (AddEquiv.refl (ZMod (p ^ k))))⟩

/-- **Rank-two prime-power characterisation.** An abelian group killed by `p ^ k`, with
order `p ^ (2 * k)` and `p ^ 2` elements killed by `p`, is additively equivalent to
`ZMod (p ^ k) × ZMod (p ^ k)`. -/
theorem nonempty_addEquiv_prod_zmod_primePow {p k : ℕ} (hp : p.Prime)
    (hpow : ∀ x : G, p ^ k • x = 0)
    (hcard : Nat.card G = p ^ (2 * k))
    (hcardp : Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ 2) :
    Nonempty (G ≃+ ZMod (p ^ k) × ZMod (p ^ k)) :=
  (nonempty_addEquiv_pi_zmod_primePow hp hpow hcard hcardp).map fun e ↦
    e.trans (LinearEquiv.finTwoArrow ℕ (ZMod (p ^ k))).toAddEquiv

private theorem natCard_torsionBy_pi_zmod_eq_pow {ι : Type*} [Fintype ι] {n : ι → ℕ} {p : ℕ}
    (hp : p.Prime) (ha : ∀ i, ∃ j, n i = p ^ (j + 1)) :
    Nat.card (AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ)) = p ^ Fintype.card ι := by
  rw [Nat.card_congr (TauCeti.AddSubgroup.torsionByPiEquiv (fun i ↦ ZMod (n i)) (p : ℤ)).toEquiv,
    Nat.card_pi]
  let : NeZero p := ⟨hp.ne_zero⟩
  calc
    ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
      apply Finset.prod_congr rfl
      intro i _
      obtain ⟨j, hj⟩ := ha i
      rw [hj, pow_succ']
      simpa only [Nat.card_zmod] using
        Nat.card_congr (TauCeti.zmodTorsionByEquiv p (p ^ j)).symm.toEquiv
    _ = p ^ Fintype.card ι := by simp

/-- If a common prime `p` divides every modulus `n i`, the rank of `∀ i : ι, ZMod (n i)` equals
`Fintype.card ι`. -/
theorem _root_.AddGroup.rank_pi_zmod_of_prime_dvd {ι : Type*} [Fintype ι] {n : ι → ℕ} {p : ℕ}
    (hp : p.Prime) (hdvd : ∀ i, p ∣ n i) :
    AddGroup.rank (∀ i : ι, ZMod (n i)) = Fintype.card ι := by
  let : NeZero p := ⟨hp.ne_zero⟩
  apply le_antisymm
  · calc AddGroup.rank (∀ i : ι, ZMod (n i))
        ≤ ∑ i : ι, AddGroup.rank (ZMod (n i)) := AddGroup.rank_pi_le _
      _ = ∑ _i : ι, 1 := Finset.sum_congr rfl fun i _ ↦ by
          have hne : n i ≠ 1 := fun h1 ↦ hp.not_dvd_one (h1 ▸ hdvd i)
          simp [AddGroup.rank_zmod, hne]
      _ = Fintype.card ι := by simp
  · let f : (∀ i : ι, ZMod (n i)) →+ (ι → ZMod p) :=
      { toFun := fun x i ↦ ZMod.castHom (hdvd i) (ZMod p) (x i)
        map_zero' := funext fun _ ↦ map_zero _
        map_add' := fun _ _ ↦ funext fun _ ↦ map_add _ _ _ }
    have hf : Function.Surjective f := fun y ↦
      ⟨fun i ↦ ((y i).val : ZMod (n i)), funext fun i ↦ by
        dsimp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [map_natCast, ZMod.natCast_zmod_val]⟩
    rw [← AddGroup.rank_pi_zmod hp.ne_one]
    exact AddGroup.rank_le_of_surjective f hf

/-- For a finite abelian `p`-group `G` (`Nat.card G = p ^ e`), the `p`-torsion subgroup `G[p]` has
cardinality `p ^ AddGroup.rank G`. -/
theorem natCard_torsionBy_eq_pow_rank [Finite G] {p e : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ e) :
    Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ AddGroup.rank G := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨eG⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let E : G ≃+ (∀ i : ι, ZMod (n i)) := eG.trans (DirectSum.addEquivProd _)
  have hprod : ∏ i, n i = p ^ e := by
    rw [← hcard, Nat.card_congr E.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]
  have ha (i : ι) : ∃ j, n i = p ^ (j + 1) := by
    have hni : n i ∣ p ^ e := hprod ▸ Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hni
    rcases k with _ | j
    · exfalso; exact (hn i).ne' (by simpa using hk)
    · exact ⟨j, hk⟩
  have hdvd (i : ι) : p ∣ n i := by
    obtain ⟨j, hj⟩ := ha i
    exact ⟨p ^ j, by rw [hj, pow_succ']⟩
  rw [Nat.card_congr (AddEquiv.torsionByCongr E (p : ℤ)).toEquiv,
    natCard_torsionBy_pi_zmod_eq_pow hp ha, AddGroup.rank_congr E,
    AddGroup.rank_pi_zmod_of_prime_dvd hp hdvd]

/-- For finite abelian `p`-groups `G` and `H` at the same prime `p`, `AddGroup.rank` is additive
on `G × H`. -/
theorem rank_prod_of_prime_pow_card [Finite G] {H : Type*} [AddCommGroup H] [Finite H] {p a b : ℕ}
    (hp : p.Prime) (hG : Nat.card G = p ^ a) (hH : Nat.card H = p ^ b) :
    AddGroup.rank (G × H) = AddGroup.rank G + AddGroup.rank H := by
  have hGH : Nat.card (G × H) = p ^ (a + b) := by rw [Nat.card_prod, hG, hH, ← pow_add]
  apply Nat.pow_right_injective hp.two_le
  dsimp only
  rw [pow_add, ← natCard_torsionBy_eq_pow_rank hp hGH,
    ← natCard_torsionBy_eq_pow_rank hp hG, ← natCard_torsionBy_eq_pow_rank hp hH,
    Nat.card_congr (TauCeti.AddSubgroup.torsionByProdEquiv G H (p : ℤ)).toEquiv, Nat.card_prod]

end TauCeti.AddCommGroup

end
