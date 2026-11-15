/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.Algebra.Group.Primary.Card

import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Primary decomposition of finite abelian groups

This file packages the canonical decomposition of a finite abelian group as the product of its
prime-primary components. The equivalence sends a tuple of primary elements to their sum in the
ambient group. It also defines the part of an additive subgroup lying in one primary component.

The proof follows the cardinality argument used by Mathlib's `Sylow.directProductOfNormal`:
primary components for distinct primes have coprime cardinalities
(`TauCeti.AddCommGroup.natCard_primaryComponent`), and the product of those cardinalities is the
cardinality of the group. The equivalence uses Mathlib's canonical
`AddCommGroup.primaryComponent` subgroups.

## Main results

* `AddSubgroup.primaryPart`: the part of a subgroup in one primary component.
* `TauCeti.AddCommGroup.primaryDecomposition`: a finite abelian group is additively equivalent to
  the product of its prime-primary components.
* `TauCeti.AddCommGroup.primaryDecomposition_apply`: the equivalence is the sum of the component
  inclusions.

## References

* D. Gorenstein, *Finite Groups*, Chapter 1.
-/

public section

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- The `p`-primary part of `H`, regarded as a subgroup of the ambient `p`-primary component. -/
def primaryPart (H : AddSubgroup G) (p : ℕ) :
    AddSubgroup (AddCommGroup.primaryComponent G p) :=
  H.comap (AddCommGroup.primaryComponent G p).subtype

@[simp]
theorem mem_primaryPart_iff (H : AddSubgroup G) (p : ℕ)
    (x : AddCommGroup.primaryComponent G p) :
    x ∈ primaryPart H p ↔ (x : G) ∈ H :=
  Iff.rfl

end AddSubgroup

namespace TauCeti

namespace AddCommGroup

variable (A : Type*) [AddCommGroup A] [Finite A]

omit [Finite A] in
private theorem primaryComponents_pairwise_addCommute :
    Pairwise fun p q : (Nat.card A).primeFactors ↦
      ∀ x y : A, x ∈ AddCommGroup.primaryComponent A p.1 →
        y ∈ AddCommGroup.primaryComponent A q.1 → AddCommute x y :=
  fun _ _ _ x y _ _ ↦ AddCommute.all x y

private noncomputable def primaryDecompositionHom :
    (∀ p : (Nat.card A).primeFactors, AddCommGroup.primaryComponent A p.1) →+ A :=
  AddSubgroup.noncommPiCoprod (primaryComponents_pairwise_addCommute A)

/-- A finite abelian group is canonically the direct product of its prime-primary components. -/
noncomputable def primaryDecomposition :
    (∀ p : (Nat.card A).primeFactors, AddCommGroup.primaryComponent A p.1) ≃+ A :=
  AddEquiv.ofBijective (primaryDecompositionHom A) (by
    classical
    let _ := Fintype.ofFinite A
    let _ : ∀ p : (Nat.card A).primeFactors,
        Fintype (AddCommGroup.primaryComponent A p.1) := fun _ ↦ Fintype.ofFinite _
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · rw [primaryDecompositionHom]
      apply AddSubgroup.injective_noncommPiCoprod_of_iSupIndep
      apply AddSubgroup.independent_of_coprime_order (primaryComponents_pairwise_addCommute A)
      rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hq' := Nat.prime_of_mem_primeFactors hq
      rw [← Nat.card_eq_fintype_card, natCard_primaryComponent A hp',
        ← Nat.card_eq_fintype_card, natCard_primaryComponent A hq']
      exact ((Nat.coprime_primes hp' hq').mpr (by simpa using hpq)).pow _ _
    · simp only [← Nat.card_eq_fintype_card]
      calc
        Nat.card (∀ p : (Nat.card A).primeFactors,
            AddCommGroup.primaryComponent A p.1) =
            ∏ p : (Nat.card A).primeFactors,
              Nat.card (AddCommGroup.primaryComponent A p.1) := Nat.card_pi
        _ = ∏ p : (Nat.card A).primeFactors,
            p.1 ^ (Nat.card A).factorization p.1 := by
          congr 1 with p
          exact natCard_primaryComponent A (Nat.prime_of_mem_primeFactors p.2)
        _ = ∏ p ∈ (Nat.card A).primeFactors,
            p ^ (Nat.card A).factorization p :=
          Finset.prod_finset_coe (fun p ↦ p ^ (Nat.card A).factorization p) _
        _ = (Nat.card A).factorization.prod (· ^ ·) := rfl
        _ = Nat.card A := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne')

/-- The canonical primary decomposition maps a tuple to the sum of its components. -/
@[simp]
theorem primaryDecomposition_apply (x) :
    primaryDecomposition A x = ∑ p, (x p : A) := by
  rw [primaryDecomposition, AddEquiv.ofBijective_apply, primaryDecompositionHom,
    AddSubgroup.noncommPiCoprod_apply, Finset.noncommSum_eq_sum]

end AddCommGroup

end TauCeti
