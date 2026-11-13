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

The same classification organizes the character table of `G × H`. Its rows correspond to pairs
of rows of the tables of `G` and `H`, the row of `(i, j)` carrying the character
`(g, h) ↦ χᵢ(g) χⱼ(h)`. Its columns correspond to pairs of conjugacy classes. Under these two
relabellings the table of `G × H` is the Kronecker product of the two tables.

Class functions of the two factors combine in the same way: their external product
`(g, h) ↦ f(g) f'(h)` is a class function of `G × H`, and for two characters it is the character
of the external tensor product.

## Main definitions

* `TauCeti.irreducibleIndexProdEquiv`: the rows of the character table of `G × H` as pairs of
  rows of the tables of `G` and `H`.
* `TauCeti.ClassFunction.externalProduct`: the external product of class functions of `G` and `H`.

## Main results

* `TauCeti.ClassFunction.ofCharacter_externalTensor`: the class function of an external tensor
  product is the external product of the class functions of the factors.
* `FDRep.externalTensor_classification`: every simple representation of `G × H` is an external
  tensor product of simple representations, with factors unique up to isomorphism.
* `TauCeti.irreducibleCharacter_irreducibleIndexProdEquiv_symm` and
  `TauCeti.nonempty_equiv_irreducibleRepresentation_irreducibleIndexProdEquiv_symm`: the row of
  `(i, j)` carries the product character, afforded by the external tensor product of the
  representations in the rows `i` and `j`.
* `TauCeti.characterDegree_irreducibleIndexProdEquiv_symm` and `TauCeti.characterDegree_prod`:
  degrees multiply.
* `TauCeti.irreducibleCharacter_irreducibleIndexProdEquiv_symm_eq_one_iff`: the trivial character
  of `G × H` is the row of the pair of trivial rows.
* `TauCeti.submatrix_characterTable_prod` and `TauCeti.reindex_characterTable_prod`: the
  character table of `G × H` is the Kronecker product of the tables of `G` and `H`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Exercise 2.36, with the
  uniqueness of the factors from Theorem 2.12.
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

/-- External products of native irreducible models are equivalent only for equal index pairs. -/
private theorem eq_of_nonempty_equiv_externalTensor
    {p q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))}
    (h : Nonempty (((irreducibleRepresentation k p.1).externalTensor
      (irreducibleRepresentation k p.2)).Equiv
        ((irreducibleRepresentation k q.1).externalTensor (irreducibleRepresentation k q.2)))) :
    p = q := by
  obtain ⟨hG, hH⟩ := (nonempty_equiv_externalTensor_iff _ _ _ _).mp h
  exact Prod.ext
    ((TauCeti.Representation.nonempty_equiv_iff_eq _
      (pairwise_isEmpty_equiv_irreducibleRepresentation k)).mp hG)
    ((TauCeti.Representation.nonempty_equiv_iff_eq _
      (pairwise_isEmpty_equiv_irreducibleRepresentation k)).mp hH)

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
  have hinj : ∀ p q, Nonempty ((R p).Equiv (R q)) → p = q := fun _ _ =>
    eq_of_nonempty_equiv_externalTensor
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

namespace TauCeti

/-! ### External products of class functions -/

namespace ClassFunction

section ExternalProduct

variable {k G H : Type*} [Semiring k] [Group G] [Group H]

/-- The **external product** of a class function `f` of `G` and a class function `g` of `H` is the
class function `(x, y) ↦ f(x) g(y)` of `G × H`. For two characters it is the character of the
external tensor product (`TauCeti.ClassFunction.ofCharacter_externalTensor`). -/
def externalProduct (f : ClassFunction k G) (g : ClassFunction k H) : ClassFunction k (G × H) :=
  ⟨fun p => f.1 p.1 * g.1 p.2, mem_iff.2 fun p c => by
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mem_iff.1 f.2 p.1 c.1,
      mem_iff.1 g.2 p.2 c.2]⟩

/-- The external product evaluates to the product of the values on the two components. -/
@[simp]
theorem externalProduct_apply (f : ClassFunction k G) (g : ClassFunction k H) (p : G × H) :
    (externalProduct f g).1 p = f.1 p.1 * g.1 p.2 :=
  (rfl)

end ExternalProduct

/-- The class function of an external tensor product of finite-dimensional representations is the
external product of the class functions of the factors. It is not a `simp` lemma, since
`Representation.characterPairing_externalTensor` is stated on the left-hand side. -/
theorem ofCharacter_externalTensor {k G H V W : Type*} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k H W) :
    ofCharacter (ρ.externalTensor σ) = externalProduct (ofCharacter ρ) (ofCharacter σ) :=
  Subtype.ext (funext fun p => by simp)

end ClassFunction

/-! ### The character table of a product group -/

section ProductTable

open scoped Kronecker

variable (k : Type*) {G H : Type*} [Field k] [Group G] [Group H] [Finite G] [Finite H]
  [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]

/-- The product of the `i`-th irreducible character of `G` and the `j`-th one of `H` is an
irreducible character of `G × H`, that of the external tensor product. -/
private theorem mul_irreducibleCharacter_mem (i : Fin (Nat.card (ConjClasses G)))
    (j : Fin (Nat.card (ConjClasses H))) :
    (fun x : G × H => irreducibleCharacter k i x.1 * irreducibleCharacter k j x.2) ∈
      irreducibleCharacters k (G × H) := by
  have := Representation.isIrreducible_externalTensor (irreducibleRepresentation k i)
    (irreducibleRepresentation k j) inferInstance inferInstance
  have hchar : ((irreducibleRepresentation k i).externalTensor
      (irreducibleRepresentation k j)).character =
        fun x : G × H => irreducibleCharacter k i x.1 * irreducibleCharacter k j x.2 :=
    funext fun x => by simp
  exact hchar ▸ character_mem_irreducibleCharacters _

variable [Invertible (Nat.card (G × H) : k)]

/-- The product characters of distinct pairs of indices are distinct. -/
private theorem injective_mul_irreducibleCharacter :
    Function.Injective fun p : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)) =>
      fun x : G × H => irreducibleCharacter k p.1 x.1 * irreducibleCharacter k p.2 x.2 := by
  intro p q hpq
  let R := fun p : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)) =>
    (irreducibleRepresentation k p.1).externalTensor (irreducibleRepresentation k p.2)
  have hR : ∀ p, (R p).IsIrreducible := fun p =>
    Representation.isIrreducible_externalTensor _ _ inferInstance inferInstance
  have := hR p
  have := hR q
  have hchar : (R q).character = (R p).character := funext fun x => by
    simpa [R] using (congrFun hpq x).symm
  exact Representation.eq_of_nonempty_equiv_externalTensor
    (Representation.nonempty_equiv_of_character_eq_of_isIrreducible (R q) (R p) hchar)

variable (G H)

/-- **The rows of the character table of `G × H` are the pairs of rows of the two tables.** The
row of the pair `(i, j)` is the irreducible character `(g, h) ↦ χᵢ(g) χⱼ(h)` of the external
tensor product of the `i`-th irreducible of `G` and the `j`-th irreducible of `H`
(`TauCeti.irreducibleCharacter_irreducibleIndexProdEquiv_symm`). -/
noncomputable def irreducibleIndexProdEquiv :
    Fin (Nat.card (ConjClasses (G × H))) ≃
      Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)) :=
  (Equiv.ofBijective
    (fun p => (finEquivIrreducibleCharacters k (G × H)).symm
      ⟨_, mul_irreducibleCharacter_mem k p.1 p.2⟩)
    ((Nat.bijective_iff_injective_and_card _).2
      ⟨fun p q hpq => injective_mul_irreducibleCharacter k
          (congrArg Subtype.val ((finEquivIrreducibleCharacters k (G × H)).symm.injective hpq)),
        by simp [ConjClasses.natCard_prod]⟩)).symm

variable {G H}

/-- The irreducible character in the row of the pair `(i, j)` is the product of the `i`-th
irreducible character of `G` and the `j`-th one of `H`. -/
@[simp]
theorem irreducibleCharacter_irreducibleIndexProdEquiv_symm
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) (x : G × H) :
    irreducibleCharacter k ((irreducibleIndexProdEquiv k G H).symm q) x =
      irreducibleCharacter k q.1 x.1 * irreducibleCharacter k q.2 x.2 := by
  simp [irreducibleIndexProdEquiv, ← coe_finEquivIrreducibleCharacters_apply]

/-- Every irreducible character of `G × H` is the product of the irreducible characters of `G`
and `H` in the rows of its pair of indices. -/
theorem irreducibleCharacter_prod_apply (p : Fin (Nat.card (ConjClasses (G × H)))) (x : G × H) :
    irreducibleCharacter k p x = irreducibleCharacter k (irreducibleIndexProdEquiv k G H p).1 x.1 *
      irreducibleCharacter k (irreducibleIndexProdEquiv k G H p).2 x.2 := by
  rw [← irreducibleCharacter_irreducibleIndexProdEquiv_symm, Equiv.symm_apply_apply]

/-- The pair of indices of a row of the character table of `G × H` is characterized by its
character. -/
theorem irreducibleIndexProdEquiv_eq_iff (p : Fin (Nat.card (ConjClasses (G × H))))
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) :
    irreducibleIndexProdEquiv k G H p = q ↔
      irreducibleCharacter k p =
        fun x : G × H => irreducibleCharacter k q.1 x.1 * irreducibleCharacter k q.2 x.2 := by
  rw [← Equiv.eq_symm_apply, ← (irreducibleCharacter_injective k).eq_iff]
  exact Eq.congr_right (funext fun x => irreducibleCharacter_irreducibleIndexProdEquiv_symm k _ x)

/-- **The representation in the row of the pair `(i, j)` is the external tensor product** of the
representations in the rows `i` and `j`, up to equivalence. -/
theorem nonempty_equiv_irreducibleRepresentation_irreducibleIndexProdEquiv_symm
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) :
    Nonempty ((irreducibleRepresentation k ((irreducibleIndexProdEquiv k G H).symm q)).Equiv
      ((irreducibleRepresentation k q.1).externalTensor (irreducibleRepresentation k q.2))) := by
  have := Representation.isIrreducible_externalTensor (irreducibleRepresentation k q.1)
    (irreducibleRepresentation k q.2) inferInstance inferInstance
  refine Representation.nonempty_equiv_of_character_eq_of_isIrreducible _ _ (funext fun x => ?_)
  simp

/-- The pair of indices of a row of the character table of `G × H` is the unique pair whose
external tensor product is equivalent to the representation in that row. -/
theorem irreducibleIndexProdEquiv_eq_iff_nonempty_equiv
    (p : Fin (Nat.card (ConjClasses (G × H))))
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) :
    irreducibleIndexProdEquiv k G H p = q ↔
      Nonempty ((irreducibleRepresentation k p).Equiv
        ((irreducibleRepresentation k q.1).externalTensor (irreducibleRepresentation k q.2))) := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => (irreducibleIndexProdEquiv_eq_iff k p q).2 ?_⟩
  · rw [← (irreducibleIndexProdEquiv k G H).symm_apply_apply p, h]
    exact nonempty_equiv_irreducibleRepresentation_irreducibleIndexProdEquiv_symm k q
  · rw [← character_irreducibleRepresentation, Representation.char_iso e]
    exact funext fun x => by simp

/-- Every representation in a row of the character table of `G × H` is equivalent to the external
tensor product of the representations of `G` and `H` in the rows of its pair of indices. -/
theorem nonempty_equiv_irreducibleRepresentation_prod (p : Fin (Nat.card (ConjClasses (G × H)))) :
    Nonempty ((irreducibleRepresentation k p).Equiv
      ((irreducibleRepresentation k (irreducibleIndexProdEquiv k G H p).1).externalTensor
        (irreducibleRepresentation k (irreducibleIndexProdEquiv k G H p).2))) :=
  (irreducibleIndexProdEquiv_eq_iff_nonempty_equiv k p _).1 rfl

/-- **Degrees multiply**: the degree in the row of the pair `(i, j)` is the product of the degrees
in the rows `i` and `j`. -/
@[simp]
theorem characterDegree_irreducibleIndexProdEquiv_symm
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) :
    characterDegree k ((irreducibleIndexProdEquiv k G H).symm q) =
      characterDegree k q.1 * characterDegree k q.2 := by
  obtain ⟨e⟩ := nonempty_equiv_irreducibleRepresentation_irreducibleIndexProdEquiv_symm k q
  simpa using e.toLinearEquiv.finrank_eq

/-- Every degree of `G × H` is the product of the degrees of `G` and `H` in the rows of its pair
of indices. -/
theorem characterDegree_prod (p : Fin (Nat.card (ConjClasses (G × H)))) :
    characterDegree k p = characterDegree k (irreducibleIndexProdEquiv k G H p).1 *
      characterDegree k (irreducibleIndexProdEquiv k G H p).2 := by
  rw [← characterDegree_irreducibleIndexProdEquiv_symm, Equiv.symm_apply_apply]

/-- **The trivial character of `G × H` sits in the row of the pair of trivial rows**: the row of
`(i, j)` is the trivial character exactly when the rows `i` and `j` are. -/
@[simp]
theorem irreducibleCharacter_irreducibleIndexProdEquiv_symm_eq_one_iff
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H))) :
    irreducibleCharacter k ((irreducibleIndexProdEquiv k G H).symm q) = (fun _ => 1) ↔
      irreducibleCharacter k q.1 = (fun _ => 1) ∧ irreducibleCharacter k q.2 = (fun _ => 1) := by
  obtain ⟨i, j⟩ := q
  obtain ⟨i₀, hi₀⟩ := exists_irreducibleCharacter_eq_one k G
  obtain ⟨j₀, hj₀⟩ := exists_irreducibleCharacter_eq_one k H
  have h₀ : irreducibleCharacter k ((irreducibleIndexProdEquiv k G H).symm (i₀, j₀)) =
      fun _ => 1 := funext fun x => by simp [hi₀, hj₀]
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ((irreducibleIndexProdEquiv k G H).symm.injective
      (irreducibleCharacter_injective k (h.trans h₀.symm)))
    exact ⟨hi₀, hj₀⟩
  · rintro ⟨hi, hj⟩
    exact funext fun x => by simp [hi, hj]

/-- A row of the character table of `G × H` is the trivial character exactly when the rows of
its pair of indices are. -/
theorem irreducibleCharacter_prod_eq_one_iff (p : Fin (Nat.card (ConjClasses (G × H)))) :
    irreducibleCharacter k p = (fun _ => 1) ↔
      irreducibleCharacter k (irreducibleIndexProdEquiv k G H p).1 = (fun _ => 1) ∧
        irreducibleCharacter k (irreducibleIndexProdEquiv k G H p).2 = (fun _ => 1) := by
  rw [← irreducibleCharacter_irreducibleIndexProdEquiv_symm_eq_one_iff, Equiv.symm_apply_apply]

/-- The entry of the character table of `G × H` in the row of the pair `(i, j)` and the column of
the pair of classes `(C, D)` is the product of the corresponding entries of the two tables. -/
@[simp]
theorem characterTable_irreducibleIndexProdEquiv_symm_prodEquiv_symm
    (q : Fin (Nat.card (ConjClasses G)) × Fin (Nat.card (ConjClasses H)))
    (K : ConjClasses G × ConjClasses H) :
    characterTable k (G × H) ((irreducibleIndexProdEquiv k G H).symm q)
        ((ConjClasses.prodEquiv G H).symm K) =
      characterTable k G q.1 K.1 * characterTable k H q.2 K.2 := by
  obtain ⟨C, D⟩ := K
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective D
  simp

/-- Every entry of the character table of `G × H` is the product of the entries of the tables of
`G` and `H` in the rows of its pair of indices and the columns of its pair of classes. -/
theorem characterTable_prod_apply (p : Fin (Nat.card (ConjClasses (G × H))))
    (C : ConjClasses (G × H)) :
    characterTable k (G × H) p C =
      characterTable k G (irreducibleIndexProdEquiv k G H p).1 (ConjClasses.prodEquiv G H C).1 *
        characterTable k H (irreducibleIndexProdEquiv k G H p).2
          (ConjClasses.prodEquiv G H C).2 := by
  rw [← characterTable_irreducibleIndexProdEquiv_symm_prodEquiv_symm, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

variable (G H)

/-- The character table of `G × H`, with its rows and columns relabelled by pairs of rows and
pairs of conjugacy classes, is the Kronecker product of the tables of `G` and `H`. -/
@[simp]
theorem submatrix_characterTable_prod :
    (characterTable k (G × H)).submatrix (irreducibleIndexProdEquiv k G H).symm
        (ConjClasses.prodEquiv G H).symm =
      characterTable k G ⊗ₖ characterTable k H := by
  ext ⟨i, j⟩ ⟨C, D⟩
  simp

/-- **The character table of `G × H` is the Kronecker product of the tables of `G` and `H`**,
once its rows are indexed by pairs of rows (`TauCeti.irreducibleIndexProdEquiv`) and its columns
by pairs of conjugacy classes (`ConjClasses.prodEquiv`). -/
theorem reindex_characterTable_prod :
    Matrix.reindex (irreducibleIndexProdEquiv k G H) (ConjClasses.prodEquiv G H)
        (characterTable k (G × H)) =
      characterTable k G ⊗ₖ characterTable k H := by
  simp

end ProductTable

end TauCeti
