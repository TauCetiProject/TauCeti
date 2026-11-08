/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj.Prod
public import TauCeti.RepresentationTheory.Tensor.External
public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# Irreducible representations of product groups

Over an algebraically closed field whose characteristic divides neither group order, every
irreducible representation of a finite product group is an external tensor product, uniquely
up to equivalence of each factor. The representation being classified may have its carrier
in any universe. The proof combines factorization of the character pairing with the count
of conjugacy classes, using the existing completeness theorem for irreducible families.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Exercise 2.36.
-/

public section

open TauCeti

namespace Representation

section Pairing

variable {k G H V W V' W' : Type*} [Field k] [Group G] [Group H] [Fintype G] [Fintype H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
  [FiniteDimensional k V] [FiniteDimensional k W]
  [FiniteDimensional k V'] [FiniteDimensional k W']
  (ρ : Representation k G V) (σ : Representation k H W)
  (ρ' : Representation k G V') (σ' : Representation k H W')

/-- The character pairing of external products factors as the product of the two pairings. -/
@[simp]
theorem characterPairing_externalTensor :
    ClassFunction.characterPairing (ClassFunction.ofCharacter (ρ.externalTensor σ))
        (ClassFunction.ofCharacter (ρ'.externalTensor σ')) =
      ClassFunction.characterPairing (ClassFunction.ofCharacter ρ) (ClassFunction.ofCharacter ρ') *
        ClassFunction.characterPairing (ClassFunction.ofCharacter σ)
          (ClassFunction.ofCharacter σ') := by
  simp only [ClassFunction.characterPairing_ofCharacter, char_externalTensor,
    Nat.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv]
  have hmul (g : G) (h : H) :
      ρ.character g * σ.character h * (ρ'.character g⁻¹ * σ'.character h⁻¹) =
        (ρ.character g * ρ'.character g⁻¹) * (σ.character h * σ'.character h⁻¹) :=
    mul_mul_mul_comm ..
  simp_rw [hmul]
  rw [← Finset.sum_mul_sum]
  ring

variable [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]
  [ρ.IsIrreducible] [σ.IsIrreducible] [ρ'.IsIrreducible] [σ'.IsIrreducible]

omit [Fintype G] [Fintype H] [FiniteDimensional k V] [FiniteDimensional k W]
  [FiniteDimensional k V'] [FiniteDimensional k W'] in
/-- External products of irreducibles are equivalent exactly when their factors are equivalent. -/
@[simp]
theorem nonempty_equiv_externalTensor_iff [Finite G] [Finite H] :
    Nonempty ((ρ.externalTensor σ).Equiv (ρ'.externalTensor σ')) ↔
      Nonempty (ρ.Equiv ρ') ∧ Nonempty (σ.Equiv σ') := by
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite H
  have := ρ.asModuleEquiv.finiteDimensional
  have := σ.asModuleEquiv.finiteDimensional
  have := ρ'.asModuleEquiv.finiteDimensional
  have := σ'.asModuleEquiv.finiteDimensional
  constructor
  · rintro ⟨e⟩
    have he : ClassFunction.ofCharacter (ρ.externalTensor σ) =
        ClassFunction.ofCharacter (ρ'.externalTensor σ') :=
      Subtype.ext (funext fun p => by
        simpa only [ClassFunction.ofCharacter_apply] using congrFun (char_iso e) p)
    have hpair :
        ClassFunction.characterPairing (ClassFunction.ofCharacter ρ)
            (ClassFunction.ofCharacter ρ') *
          ClassFunction.characterPairing (ClassFunction.ofCharacter σ)
            (ClassFunction.ofCharacter σ') = 1 := by
      rw [← characterPairing_externalTensor, ← he, characterPairing_externalTensor,
        ClassFunction.characterPairing_ofCharacter_self,
        ClassFunction.characterPairing_ofCharacter_self, mul_one]
    constructor
    · by_contra h
      have : IsEmpty (ρ.Equiv ρ') := not_nonempty_iff.mp h
      have hzero := ClassFunction.characterPairing_ofCharacter_eq_zero ρ' ρ inferInstance
      rw [ClassFunction.characterPairing_symm] at hzero
      simp [hzero] at hpair
    · by_contra h
      have : IsEmpty (σ.Equiv σ') := not_nonempty_iff.mp h
      have hzero := ClassFunction.characterPairing_ofCharacter_eq_zero σ' σ inferInstance
      rw [ClassFunction.characterPairing_symm] at hzero
      simp [hzero] at hpair
  · rintro ⟨⟨e⟩, ⟨f⟩⟩
    exact ⟨e.externalTensor f⟩

end Pairing

section Classification

variable {k G H : Type*} [Field k] [Group G] [Group H] [Finite G] [Finite H]
  [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]

/-- Every irreducible of a product group is an external product of a unique pair of native
irreducible models. No restriction is imposed on the universe of its carrier. -/
theorem existsUnique_nonempty_equiv_externalTensor {U : Type*} [AddCommGroup U] [Module k U]
    (τ : Representation k (G × H) U) [τ.IsIrreducible] :
    ∃! p : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)),
      Nonempty (τ.Equiv ((irreducibleRepresentation k p.1).externalTensor
        (irreducibleRepresentation k p.2))) := by
  let R := fun p : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)) =>
    (irreducibleRepresentation k p.1).externalTensor (irreducibleRepresentation k p.2)
  have : ∀ p, (R p).IsIrreducible := fun p =>
    isIrreducible_externalTensor _ _ inferInstance inferInstance
  have hinj : ∀ p q, Nonempty ((R p).Equiv (R q)) → p = q := by
    intro p q hpq
    obtain ⟨hG, hH⟩ := (nonempty_equiv_externalTensor_iff _ _ _ _).mp hpq
    exact Prod.ext
      ((TauCeti.Representation.nonempty_equiv_iff_eq _
        (pairwise_isEmpty_equiv_irreducibleRepresentation k)).mp hG)
      ((TauCeti.Representation.nonempty_equiv_iff_eq _
        (pairwise_isEmpty_equiv_irreducibleRepresentation k)).mp hH)
  have hind : Pairwise fun p q => IsEmpty ((R p).Equiv (R q)) :=
    fun p q hpq => not_nonempty_iff.mp (fun h => hpq (hinj p q h))
  have hcard : Nat.card (Fin (Nat.card (ConjClasses G)) ×
      Fin (Nat.card (ConjClasses H))) = Nat.card (ConjClasses (G × H)) := by
    simp [ConjClasses.natCard_prod]
  let _ : Invertible (Nat.card (G × H) : k) := invertibleOfNonzero <| by
    rw [Nat.card_prod, Nat.cast_mul]
    exact mul_ne_zero (Invertible.ne_zero _) (Invertible.ne_zero _)
  obtain ⟨p, hp⟩ := ClassFunction.exists_nonempty_equiv R hind hcard τ
  refine ⟨p, hp, fun q hq => ?_⟩
  exact hinj q p ⟨hq.some.symm.trans hp.some⟩

end Classification

end Representation

namespace FDRep

open CategoryTheory

variable {k G H : Type*} [Field k] [Group G] [Group H] [Finite G] [Finite H]
  [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]

/-- Every simple representation of a product group is an external tensor product of simple
representations. The factors are unique up to isomorphism. -/
theorem externalTensor_classification (X : FDRep k (G × H)) [Simple X] :
    ∃ (V : FDRep k G) (W : FDRep k H), Simple V ∧ Simple W ∧
      Nonempty (X ≅ FDRep.of (Representation.externalTensor V.ρ W.ρ)) ∧
      ∀ (V' : FDRep k G) (W' : FDRep k H), Simple V' → Simple W' →
        Nonempty (X ≅ FDRep.of (Representation.externalTensor V'.ρ W'.ρ)) →
          Nonempty (V ≅ V') ∧ Nonempty (W ≅ W') := by
  have := isIrreducible_of_simple X
  obtain ⟨p, ⟨e⟩, -⟩ := Representation.existsUnique_nonempty_equiv_externalTensor X.ρ
  let V := FDRep.of (irreducibleRepresentation k p.1)
  let W := FDRep.of (irreducibleRepresentation k p.2)
  have hV : Simple V := (simple_iff_isIrreducible V).mpr (by
    simpa only [V, of_ρ'] using
      (inferInstance : (irreducibleRepresentation k p.1).IsIrreducible))
  have hW : Simple W := (simple_iff_isIrreducible W).mpr (by
    simpa only [W, of_ρ'] using
      (inferInstance : (irreducibleRepresentation k p.2).IsIrreducible))
  have i : X ≅ FDRep.of (Representation.externalTensor V.ρ W.ρ) :=
    e.toLinearEquiv.toFDRepIso fun g x => LinearMap.congr_fun (e.isIntertwining' g) x
  refine ⟨V, W, hV, hW, ⟨i⟩, fun V' W' hV' hW' ⟨j⟩ => ?_⟩
  have := hV'
  have := hW'
  have := isIrreducible_of_simple V
  have := isIrreducible_of_simple W
  have := isIrreducible_of_simple V'
  have := isIrreducible_of_simple W'
  obtain ⟨⟨f⟩, ⟨g⟩⟩ :=
    (Representation.nonempty_equiv_externalTensor_iff V.ρ W.ρ V'.ρ W'.ρ).mp
      ⟨isoToEquiv (i.symm ≪≫ j)⟩
  exact ⟨⟨f.toLinearEquiv.toFDRepIso fun a x => LinearMap.congr_fun (f.isIntertwining' a) x⟩,
    ⟨g.toLinearEquiv.toFDRepIso fun a x => LinearMap.congr_fun (g.isIntertwining' a) x⟩⟩

end FDRep
