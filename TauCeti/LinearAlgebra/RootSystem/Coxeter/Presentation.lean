/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.ExchangeCondition
public import TauCeti.LinearAlgebra.RootSystem.BraidRelation
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
import all TauCeti.LinearAlgebra.RootSystem.SimpleReflections

/-!
# The Coxeter presentation of the Weyl group

The Coxeter matrix of a base gives an abstract presented group. Its generators map to the simple
reflections of the Weyl group because those reflections satisfy the Coxeter relations, and the
resulting homomorphism is surjective because the simple reflections generate the Weyl group.

**Tits' theorem** says that this homomorphism is also injective: the braid relations are the only
relations among the simple reflections, so the Weyl group with its simple reflections is a Coxeter
system for the Coxeter matrix of the base. Its Coxeter length is the number of inversions, the
positive roots sent to negative roots.

The proof is the characterization of Coxeter systems by the exchange condition
(`CoxeterSystem.ofExchange`), applied with the inversion count as length function. The inversion
count is the least length of a word in the simple reflections (`TauCeti.isLeast_ncard_inversions`),
the product of two simple reflections has the order prescribed by the Coxeter matrix
(`RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase`), and the exchange
condition is the root-level strong exchange condition
(`TauCeti.exists_wordProd_eraseIdx_eq_mul_ofIdx`): when the last letter does not lengthen a word,
its simple root is an inversion of the word, and the reflection in it deletes a letter.

## Main definitions

* `TauCeti.weylCoxeterHom`: the canonical homomorphism from the Coxeter group of a base to its Weyl
  group.
* `TauCeti.weylCoxeterSystem`: the Weyl group as a Coxeter system for the Coxeter matrix of a
  base.

## Main results

* `TauCeti.weylCoxeterHom_apply_simple`: the abstract generator maps to the corresponding simple
  root reflection.
* `TauCeti.weylCoxeterHom_wordProd`: the homomorphism sends an abstract word to the same word in
  the Weyl group.
* `TauCeti.weylCoxeterHom_surjective`: the canonical homomorphism is surjective.
* `TauCeti.weylCoxeterHom_injective`: **Tits' theorem**, the canonical homomorphism is injective.
* `TauCeti.weylCoxeterSystem_simple` and `TauCeti.weylCoxeterSystem_wordProd`: the simple
  reflections of the Coxeter system are the simple root reflections.
* `TauCeti.length_weylCoxeterSystem_eq`: the Coxeter length of a Weyl-group element is its number of
  inversions.
* `TauCeti.isReduced_weylCoxeterSystem_iff`: a word is reduced exactly when the element it spells
  has as many inversions as the word has letters.

## References

* J. Tits, *Le problème des mots dans les groupes de Coxeter*, Symposia Mathematica 1 (1969),
  175--185.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1, no. 5, Theorem 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Sections 1.5--1.9.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] (b : P.Base)

/-- The canonical homomorphism from the abstract Coxeter group attached to a base to its Weyl
group, sending each abstract generator to the corresponding simple root reflection. -/
noncomputable def weylCoxeterHom :
    (coxeterMatrixOfBase P b).Group →* P.weylGroup :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.lift
    ⟨fun i : b.support => RootPairing.weylGroup.ofIdx P (i : ι),
      RootPairing.weylGroup.pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one P b⟩

/-- The canonical homomorphism sends an abstract Coxeter generator to the corresponding simple
root reflection. -/
@[simp]
theorem weylCoxeterHom_apply_simple (i : b.support) :
    weylCoxeterHom P b ((coxeterMatrixOfBase P b).simple i) =
      RootPairing.weylGroup.ofIdx P (i : ι) :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.lift_apply_simple
    (RootPairing.weylGroup.pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one P b) i

/-- The canonical homomorphism sends a word in the abstract Coxeter generators to the same word in
the simple reflections of the Weyl group. -/
@[simp]
theorem weylCoxeterHom_wordProd (l : List b.support) :
    weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l) = wordProd P b l := by
  simp [CoxeterSystem.wordProd, wordProd, map_list_prod]

variable [P.IsReduced]

/-- The canonical homomorphism from the Coxeter presentation to the Weyl group is surjective. -/
theorem weylCoxeterHom_surjective : Function.Surjective (weylCoxeterHom P b) := by
  intro w
  obtain ⟨l, hl⟩ := exists_wordProd_eq P b w
  exact ⟨(coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l, by simpa using hl⟩


omit [P.IsReduced] in
/-- The product of the images of two abstract generators has the order prescribed by the Coxeter
matrix of the base. -/
private theorem orderOf_weylCoxeterHom_simple_mul_simple (i i' : b.support) :
    orderOf (weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.simple i) *
      weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.simple i')) =
        coxeterMatrixOfBase P b i i' := by
  simp

/-- The inversion count is the least length of an abstract word spelling an element. -/
private theorem isLeast_ncard_inversions_weylCoxeterHom (w : P.weylGroup) :
    IsLeast {n | ∃ l : List b.support,
        weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l) = w ∧
          l.length = n} ((inversions P b w).ncard) := by
  simpa only [weylCoxeterHom_wordProd] using isLeast_ncard_inversions P b w

/-- The exchange condition for the simple reflections of the Weyl group, read off the inversion
count: if appending a simple reflection to a word does not raise the inversion count, its simple
root is an inversion of the word, and the strong exchange condition deletes a letter. -/
private theorem exchange_weylCoxeterHom (l : List b.support) (i : b.support)
    (hl : (inversions P b (weylCoxeterHom P b
      ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l))).ncard = l.length)
    (hle : (inversions P b (weylCoxeterHom P b
      ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l *
        (coxeterMatrixOfBase P b).toCoxeterSystem.simple i))).ncard ≤ l.length) :
    ∃ j < l.length,
      weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd (l.eraseIdx j)) =
        weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l *
          (coxeterMatrixOfBase P b).toCoxeterSystem.simple i) := by
  simp only [map_mul, weylCoxeterHom_wordProd, CoxeterMatrix.toCoxeterSystem_simple,
    weylCoxeterHom_apply_simple] at hl hle ⊢
  have hpos := b.isPos_of_mem_support i.2
  have hlt : (inversions P b (wordProd P b l * RootPairing.weylGroup.ofIdx P (i : ι))).ncard <
      (inversions P b (wordProd P b l)).ncard := by
    rcases ncard_inversions_mul_ofIdx P (wordProd P b l) b i.2 with h | h <;> omega
  have hmem := (ncard_inversions_mul_ofIdx_lt_iff P b _ hpos).mp hlt
  exact exists_wordProd_eraseIdx_eq_mul_ofIdx P b hpos l ((mem_inversions P b _ _).mp hmem).2

/-- **Tits' theorem: the braid relations are the only relations among the simple reflections.**
The canonical homomorphism from the Coxeter group of a base to the Weyl group is injective. -/
theorem weylCoxeterHom_injective : Function.Injective (weylCoxeterHom P b) :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.injective_of_exchange (weylCoxeterHom P b)
    (fun w ↦ (inversions P b w).ncard) (orderOf_weylCoxeterHom_simple_mul_simple P b)
    (isLeast_ncard_inversions_weylCoxeterHom P b) (exchange_weylCoxeterHom P b)

/-- **The Weyl group is a Coxeter system.** For a base `b` of a finite reduced crystallographic
root system, the Weyl group with the simple reflections of `b` is a Coxeter system for the Coxeter
matrix of `b`: by Tits' theorem, it is the abstract Coxeter group of that matrix. -/
noncomputable def weylCoxeterSystem :
    CoxeterSystem (coxeterMatrixOfBase P b) P.weylGroup :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.ofExchange (weylCoxeterHom P b)
    (fun w ↦ (inversions P b w).ncard) (orderOf_weylCoxeterHom_simple_mul_simple P b)
    (isLeast_ncard_inversions_weylCoxeterHom P b) (exchange_weylCoxeterHom P b)

/-- The simple reflections of the Coxeter system of the Weyl group are the simple root
reflections. -/
@[simp]
theorem weylCoxeterSystem_simple (i : b.support) :
    (weylCoxeterSystem P b).simple i = RootPairing.weylGroup.ofIdx P (i : ι) := by
  rw [weylCoxeterSystem, CoxeterSystem.ofExchange_simple, CoxeterMatrix.toCoxeterSystem_simple,
    weylCoxeterHom_apply_simple]

/-- A word in the simple reflections of the Coxeter system of the Weyl group spells the same
element as the word in the simple root reflections. -/
@[simp]
theorem weylCoxeterSystem_wordProd (l : List b.support) :
    (weylCoxeterSystem P b).wordProd l = wordProd P b l := by
  rw [weylCoxeterSystem, CoxeterSystem.ofExchange_wordProd, weylCoxeterHom_wordProd]

/-- **Length equals inversions.** The Coxeter length of a Weyl-group element is the number of
positive roots it sends to negative roots. -/
@[simp]
theorem length_weylCoxeterSystem_eq (w : P.weylGroup) :
    (weylCoxeterSystem P b).length w = (inversions P b w).ncard :=
  CoxeterSystem.length_ofExchange _ _ _ _ _ w

/-- A word in the simple reflections is reduced exactly when the element it spells has as many
inversions as the word has letters. -/
theorem isReduced_weylCoxeterSystem_iff (l : List b.support) :
    (weylCoxeterSystem P b).IsReduced l ↔ (inversions P b (wordProd P b l)).ncard = l.length := by
  rw [CoxeterSystem.IsReduced, weylCoxeterSystem_wordProd, length_weylCoxeterSystem_eq]

end TauCeti
