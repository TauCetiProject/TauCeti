/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.SizeFormula
public import TauCeti.Combinatorics.PermutationTriple.GeneratingCount

/-!
# Passport sizes from generating counts

For a nonzero degree and a pretransitive monodromy group, the class sum for generating
triples gives the passport size after multiplying by the centralizer order and dividing by
the normalizer order.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling and J. Voight, *A database of Belyi maps*, §2.
-/

open Equiv

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ}

private theorem generatedSubgroup_subtype_eq_top_iff (P : PassportSpec n)
    (p : P.G × P.G × P.G) :
    productOneGeneratedSubgroup p = ⊤ ↔
      Subgroup.closure {(p.1 : Perm (Fin n)), (p.2.1 : Perm (Fin n))} = P.G := by
  rw [← Subgroup.map_subtype_inj]
  rw [← productOneGeneratedSubgroup_map P.G.subtype p,
    productOneGeneratedSubgroup_def]
  rw [← MonoidHom.range_eq_map]
  simp

/-- The class sum `genCountType` is the number of generating triples of a passport, before
quotienting by its normalizer. -/
theorem card_generatingTriples_eq_genCountType (P : PassportSpec n) :
    P.generatingTriples.card = P.G.genCountType P.lam0 P.lam1 P.laminf := by
  classical
  rw [← P.G.card_generatingTriplesOfFullCycleType]
  let lift : (p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n)) →
      p ∈ P.generatingTriples → P.G × P.G × P.G := fun p hp => by
    obtain ⟨hprod, hgen, -⟩ := mem_generatingTriples.mp hp
    have hx : p.1 ∈ P.G := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    have hy : p.2.1 ∈ P.G := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    have hzrel : p.2.2 * (p.2.1 * p.1) = 1 := by
      simpa only [mul_assoc] using hprod
    have hz : p.2.2 ∈ P.G := by
      rw [eq_inv_of_mul_eq_one_left hzrel]
      exact P.G.inv_mem (P.G.mul_mem hy hx)
    exact (⟨p.1, hx⟩, ⟨p.2.1, hy⟩, ⟨p.2.2, hz⟩)
  refine Finset.card_bij lift ?_ ?_ ?_
  · intro p hp
    obtain ⟨hprod, hgen, htypes⟩ := mem_generatingTriples.mp hp
    apply P.G.mem_generatingTriplesOfFullCycleType.mpr
    refine ⟨?_, (generatedSubgroup_subtype_eq_top_iff P (lift p hp)).mpr ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact hprod
    · simpa only [lift] using hgen
    · simpa only [lift] using congrArg Prod.fst htypes
    · simpa only [lift] using congrArg (fun t => t.2.1) htypes
    · simpa only [lift] using congrArg (fun t => t.2.2) htypes
  · intro p hp q hq heq
    apply Prod.ext
    · exact congrArg (fun x : P.G × P.G × P.G => (x.1 : Perm (Fin n))) heq
    apply Prod.ext
    · exact congrArg (fun x : P.G × P.G × P.G => (x.2.1 : Perm (Fin n))) heq
    · exact congrArg (fun x : P.G × P.G × P.G => (x.2.2 : Perm (Fin n))) heq
  · intro q hq
    obtain ⟨hprod, hgen, h0, h1, hi⟩ := P.G.mem_generatingTriplesOfFullCycleType.mp hq
    let p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) :=
      ((q.1 : Perm (Fin n)), (q.2.1 : Perm (Fin n)), (q.2.2 : Perm (Fin n)))
    have hp : p ∈ P.generatingTriples := by
      apply mem_generatingTriples.mpr
      refine ⟨?_, (generatedSubgroup_subtype_eq_top_iff P q).mp hgen, ?_⟩
      · exact congrArg Subtype.val hprod
      · exact Prod.ext h0 (Prod.ext h1 hi)
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The normalizer order divides the generating count by cycle type times the centralizer
order. This is the exact divisibility behind the natural-number passport-size formula. -/
theorem card_normalizer_dvd_genCountType_mul_card_centralizer (P : PassportSpec n) :
    Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) ∣
      P.G.genCountType P.lam0 P.lam1 P.laminf *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  rw [← P.card_generatingTriples_eq_genCountType, ← P.card_generatingTriples]
  exact P.card_normalizer_dvd_card_generatingTriple_mul_card_centralizer

/-- For nonzero degree and a pretransitive monodromy group, a passport's size is the
generating count by cycle type times the centralizer order divided by the normalizer order. -/
theorem passportSize_eq_genCountType_mul_card_centralizer_div_card_normalizer
    (P : PassportSpec n) (hn : n ≠ 0) (hG : MulAction.IsPretransitive P.G (Fin n)) :
    P.passportSize =
      P.G.genCountType P.lam0 P.lam1 P.laminf *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) /
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  rw [← P.card_generatingTriples_eq_genCountType]
  exact P.passportSize_eq_card_generatingTriples_mul_card_centralizer_div_card_normalizer hn hG

end PassportSpec

end TauCeti
