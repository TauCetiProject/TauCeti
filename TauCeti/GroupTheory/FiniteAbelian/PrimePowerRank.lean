/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.Module.SpanRank
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Data.ZMod.Torsion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Pi

/-!
# Finite abelian groups of prime-power exponent and given rank

A finite abelian group killed by `p ^ k`, of order `p ^ (r * k)`, and with exactly `p ^ r`
elements killed by `p` is the product of `r` cyclic groups of order `p ^ k`.  This is the
homogeneous prime-power case of the structure theorem for finite abelian groups, and the
rank-two case is recorded separately. On a finite product `∏ᵢ ℤ/pᵏⁱ`, `AddGroup.rank` equals
`#{i | kᵢ ≠ 0}`.

The criterion is useful when the total order and the first torsion layer are easier to count than
explicit generators.  It determines both the number of cyclic factors and their exponents.

## Main result

* `TauCeti.AddCommGroup.nonempty_addEquiv_pi_zmod_primePow`: the rank-`r` characterisation.
* `TauCeti.AddCommGroup.nonempty_addEquiv_prod_zmod_primePow`: the rank-two case.
* `TauCeti.AddCommGroup.rank_pi_zmod_pow`: `AddGroup.rank` of `∏ᵢ ℤ/pᵏⁱ` is `#{i | kᵢ ≠ 0}`.
-/

public section

namespace TauCeti.AddCommGroup

open Finset
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

/-- The minimal number of generators of a finite product `∏ᵢ ℤ/pᵏⁱ` is the number of nonzero
exponents `kᵢ ≠ 0`. -/
theorem rank_pi_zmod_pow {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    AddGroup.rank (∀ i, ZMod (p ^ k i)) = #{i | k i ≠ 0} := by
  classical
  have hp : p.Prime := Fact.out
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [AddGroup.rank_eq_spanFinrank_top]
  apply le_antisymm
  · -- Single-coordinate generators on `{i // k i ≠ 0}` span the product, as `ZMod 1` is trivial.
    let g : {i // k i ≠ 0} → ∀ i, ZMod (p ^ k i) := fun j ↦ Pi.single j.val 1
    have hspan : Submodule.span ℤ (Set.range g) = ⊤ := by
      refine top_unique fun x _ ↦ ?_
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      by_cases hi : k i = 0
      · have : Subsingleton (ZMod (p ^ k i)) := by rw [hi, pow_zero]; infer_instance
        rw [Subsingleton.elim (x i) 0, Pi.single_zero]
        exact Submodule.zero_mem _
      · have hx : Pi.single i (x i) = ((x i).val : ℤ) • g ⟨i, hi⟩ := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp [g]
          · simp [g, hji]
        rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range g)).trans ?_
    calc (Set.range g).ncard ≤ Fintype.card {i // k i ≠ 0} := by
          simpa [Nat.card_eq_fintype_card] using Set.ncard_image_le (f := g) (s := Set.univ)
      _ = #{i | k i ≠ 0} := Fintype.card_subtype _
  · -- Reducing the nontrivial coordinates modulo `p` maps onto the `𝔽_p`-vector space `𝔽_p^S`.
    let π : (∀ i, ZMod (p ^ k i)) →ₗ[ℤ] ({i // k i ≠ 0} → ZMod p) :=
      LinearMap.pi fun j ↦
        ((ZMod.castHom (dvd_pow_self p j.property) (ZMod p)).toAddMonoidHom.toIntLinearMap).comp
          (LinearMap.proj j.val)
    have hsurj : Function.Surjective π := fun y ↦ by
      refine ⟨fun i ↦ if hi : k i ≠ 0 then ((y ⟨i, hi⟩).val : ZMod (p ^ k i)) else 0, ?_⟩
      ext ⟨i, hi⟩
      simp [π, hi]
    have hle := Submodule.spanFinrank_map_le_of_fg π (Module.Finite.fg_top (R := ℤ))
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hle
    calc #{i | k i ≠ 0} = Fintype.card {i // k i ≠ 0} := (Fintype.card_subtype _).symm
      _ = Module.finrank (ZMod p) ({i // k i ≠ 0} → ZMod p) := (Module.finrank_pi (ZMod p)).symm
      _ = (⊤ : Submodule (ZMod p) ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          Module.finrank_eq_spanFinrank_of_free
      _ = (⊤ : Submodule ℤ ({i // k i ≠ 0} → ZMod p)).spanFinrank :=
          (Submodule.spanFinrank_restrictScalars_eq
            (ZMod.ringHom_surjective (algebraMap ℤ (ZMod p))) ⊤).symm
      _ ≤ (⊤ : Submodule ℤ (∀ i, ZMod (p ^ k i))).spanFinrank := hle

end TauCeti.AddCommGroup

end
