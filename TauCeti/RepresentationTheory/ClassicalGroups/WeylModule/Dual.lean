/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.CentralCharacter
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Dual
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.HighestWeight
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.Irreducible.Dual

/-!
# Contragredients of rational Weyl modules

The contragredient of the rational Weyl module of a dominant weight has highest weight obtained
by reversing and negating the coordinates. Reversal preserves the set of torus weights by
permutation symmetry, and negation exchanges the weights of a representation and its dual.
Since the original weights all have the same total sum, reversal and negation convert the
original prefix bounds to prefix bounds for the dual.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Lectures 14–15.
-/

public section

open Matrix

namespace TauCeti

variable {n : ℕ}

private theorem weightSpace_dual_rationalWeylRep_ne_bot_iff (l : DominantWeight n)
    (a : Fin n → ℤ) :
    weightSpace (rationalWeylRep ℂ n l).dual a ≠ ⊥ ↔
      weightSpace (W := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (rationalWeylRep ℂ n l) (fun i ↦ -a i.rev) ≠ ⊥ := by
  rw [weightSpace_dual_ne_bot_iff (W := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
    weightChar_injective (isRationalRep_rationalWeylRep n l).iSup_weightSpace_eq_top]
  have hrev : (-a) ∘ ⇑Fin.revPerm = (fun i ↦ -a i.rev) := funext fun _ ↦ rfl
  rw [← hrev]
  exact not_congr (weightSpace_eq_bot_comp_perm_iff
    (W := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
    (rationalWeylRep ℂ n l) Fin.revPerm (-a)).symm

private theorem sum_le_sum_of_weightSpace_dual_rationalWeylRep_ne_bot
    (l : DominantWeight n) {a : Fin n → ℤ}
    (ha : weightSpace (rationalWeylRep ℂ n l).dual a ≠ ⊥) (m : ℕ) :
    prefixSum m a ≤ prefixSum m l.dual.val := by
  have ha' := (weightSpace_dual_rationalWeylRep_ne_bot_iff l a).mp ha
  have hsum := sum_eq_sum_of_weightSpace_ne_bot ha'
    (weightSpace_rationalWeylRep_self_ne_bot ℂ l)
  have hbound := sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha' (n - min m n)
  rw [← prefixSum_def, ← prefixSum_def] at hbound
  have htotal : (∑ i, a i) = ∑ i, l.dual.val i := by
    have hrev : (∑ i : Fin n, a i.rev) = ∑ i, a i := Equiv.sum_comp Fin.revPerm a
    rw [Finset.sum_neg_distrib, hrev] at hsum
    rw [DominantWeight.sum_dual, ← neg_eq_iff_eq_neg, hsum]
  have hprefix (x : Fin n → ℤ) :
      prefixSum (n - min m n) (fun i ↦ -x i.rev) = prefixSum (min m n) x - ∑ i, x i := by
    have hk : n - min m n ≤ n := Nat.sub_le _ _
    rw [prefixSum_comp_rev (x := fun i ↦ -x i) hk, Nat.sub_sub_self (Nat.min_le_right _ _),
      Finset.sum_neg_distrib, prefixSum_def]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n ↦ i.val < min m n) x
    simp only [not_lt] at hsplit
    omega
  have hl : (fun i ↦ -l.dual.val i.rev) = l.val := by
    funext i
    simp
  rw [← hl, hprefix, hprefix, htotal, sub_le_sub_iff_right, prefixSum_min,
    prefixSum_min] at hbound
  exact hbound

/-- The contragredient of `V_λ` for `GLₙ(ℂ)` is the rational Weyl module
of highest weight `(-λₙ, …, -λ₁)`. -/
theorem nonempty_equiv_dual_rationalWeylRep (l : DominantWeight n) :
    Nonempty ((rationalWeylRep ℂ n l).dual.Equiv (rationalWeylRep ℂ n l.dual)) := by
  have : (rationalWeylRep ℂ n l).dual.IsIrreducible :=
    Representation.IsIrreducible.dual (V := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
      (ρ := rationalWeylRep ℂ n l) inferInstance
  have hdual := (isRationalRep_rationalWeylRep n l).dual
  have hweight : weightSpace (rationalWeylRep ℂ n l).dual l.dual.val ≠ ⊥ := by
    rw [weightSpace_dual_rationalWeylRep_ne_bot_iff]
    simpa only [DominantWeight.dual_apply, Fin.rev_rev, neg_neg] using
      weightSpace_rationalWeylRep_self_ne_bot ℂ l
  obtain ⟨f, hf, hf₀⟩ := (Submodule.ne_bot_iff _).mp hweight
  obtain ⟨v, hv, hv₀⟩ := (Submodule.ne_bot_iff _).mp
    (weightSpace_rationalWeylRep_self_ne_bot ℂ l.dual)
  exact hdual.nonempty_equiv_of_highestWeightVector (isRationalRep_rationalWeylRep n l.dual)
    hf₀ hf (fun _ _ h c ↦ hdual.apply_transvectionUnit_eq_self_of_forall_sum_le
      (fun _ ha m ↦ by
        simpa only [prefixSum_def] using
          sum_le_sum_of_weightSpace_dual_rationalWeylRep_ne_bot l ha m) h hf c)
    hv₀ hv (fun _ _ h c ↦ rationalWeylRep_apply_transvectionUnit_eq_self l.dual h hv c)

end TauCeti
