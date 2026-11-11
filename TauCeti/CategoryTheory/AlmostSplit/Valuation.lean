/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.RadicalQuotient
public import TauCeti.CategoryTheory.Preadditive.Radical.ResidueQuotient
public import TauCeti.CategoryTheory.Preadditive.Radical.Valuation

/-!
# Valuations and multiplicities in an almost-split sequence

Let `0 → A → B → C → 0` be an almost-split sequence, with `A` and `C` having local endomorphism
rings, and let `B ≅ ⨁ P` be a decomposition of its middle term into finitely many objects with
local endomorphism rings. For an object `X` with a local endomorphism ring, write `μ` for the number
of summands `P j` isomorphic to `X`. Then the space `Irr(X, C)` of irreducible morphisms has
dimension `μ` over the residue division ring of `X`, and so does `Irr(A, X)`. In terms of the
valuations `(a, b)` of `TauCeti.irreducibleMorphismValuation`, this reads `b_{XC} = μ = a_{AX}`.
When `A` is the Auslander-Reiten translate of `C`, this is the valued mesh relation of the
Auslander-Reiten quiver at `C`.

The proof upgrades the identifications `Hom(X, B) / rad ≅ Irr(X, C)` and
`Hom(B, X) / rad ≅ Irr(A, X)` of `TauCeti/CategoryTheory/AlmostSplit/RadicalQuotient.lean` to
linear equivalences over the residue ring of `X`, and counts the multiplicity through
`TauCeti.finrank_residueOp_radicalQuotient_biproduct` and
`TauCeti.finrank_residue_radicalQuotient_biproduct`. No field and no finiteness over the base ring
is assumed, so this covers Artin algebras over a commutative Artinian ring. Over a field, the
`k`-dimensional form of these counts is
`TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left`.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_snd_eq_natCard`: the
  second entry of the valuation of `Irr(X, C)` is the multiplicity of `X` in the middle term.
* `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_fst_eq_natCard`: the
  first entry of the valuation of `Irr(A, X)` is the same multiplicity.
* `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_snd_eq_fst`: hence
  `b_{XC} = a_{AX}`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition VII.1.3.
-/

public section

open CategoryTheory CategoryTheory.Limits Module TauCeti

namespace CategoryTheory.ShortComplex.IsAlmostSplit

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  {S : ShortComplex C} [IsLocalRing (End S.X₁)] [IsLocalRing (End S.X₃)]
  (k : Type*) [Ring k] [Linear k C]

/-- The identification of morphisms into the middle term, modulo the radical, with irreducible
morphisms into the final term commutes with the residue action of the source. -/
theorem rightRadicalQuotientEquiv_residueOp_smul (hS : S.IsAlmostSplit) (X : C)
    (d : (End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
    (q : (X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) :
    hS.rightRadicalQuotientEquiv k X (d • q) = d • hS.rightRadicalQuotientEquiv k X q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  induction q using Submodule.Quotient.induction_on with | _ f
  simp only [radicalQuotient_residueOp_smul_mk, rightRadicalQuotientEquiv_mk,
    irreducibleMorphismSpace_residueOp_smul_eq, irreducibleMorphismPrecomp_irreducibleMorphismMk]
  congr 1
  ext
  simp

/-- The identification of morphisms out of the middle term, modulo the radical, with irreducible
morphisms out of the initial term commutes with the residue action of the target. -/
theorem leftRadicalQuotientEquiv_residue_smul (hS : S.IsAlmostSplit) (X : C)
    (d : End X ⧸ Ring.jacobson (End X)) (q : (S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) :
    hS.leftRadicalQuotientEquiv k X (d • q) = d • hS.leftRadicalQuotientEquiv k X q := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective d
  induction q using Submodule.Quotient.induction_on with | _ f
  simp only [radicalQuotient_residue_smul_mk, leftRadicalQuotientEquiv_mk,
    irreducibleMorphismSpace_residue_smul_eq, irreducibleMorphismPostcomp_irreducibleMorphismMk]
  congr 1
  ext
  simp

variable {J : Type*} [Finite J] (P : J → C) [HasBiproduct P] [∀ j, IsLocalRing (End (P j))]

/-- **The multiplicity of a summand of the middle term, through the final term**: in an
almost-split sequence `0 → A → B → C → 0` with `B ≅ ⨁ P`, the dimension of `Irr(X, C)` over the
residue division ring of `X` (the second entry of its valuation) is the number of summands `P j`
isomorphic to `X`. -/
theorem irreducibleMorphismValuation_snd_eq_natCard (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P)
    (X : C) [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k X S.X₃).2 = Nat.card {j // Nonempty (P j ≅ X)} := by
  rw [irreducibleMorphismValuation_snd, ← finrank_residueOp_radicalQuotient_biproduct k X P,
    ← (radicalQuotientCongrRight k X e).finrank_eq]
  exact ((hS.rightRadicalQuotientEquiv k X).toAddEquiv.toLinearEquiv
    (hS.rightRadicalQuotientEquiv_residueOp_smul k X)).finrank_eq.symm

/-- **The multiplicity of a summand of the middle term, through the initial term**: in an
almost-split sequence `0 → A → B → C → 0` with `B ≅ ⨁ P`, the dimension of `Irr(A, X)` over the
residue division ring of `X` (the first entry of its valuation) is the number of summands `P j`
isomorphic to `X`. -/
theorem irreducibleMorphismValuation_fst_eq_natCard (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P)
    (X : C) [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k S.X₁ X).1 = Nat.card {j // Nonempty (P j ≅ X)} := by
  rw [irreducibleMorphismValuation_fst, ← finrank_residue_radicalQuotient_biproduct k X P,
    ← (radicalQuotientCongrLeft k X e).finrank_eq]
  exact ((hS.leftRadicalQuotientEquiv k X).toAddEquiv.toLinearEquiv
    (hS.leftRadicalQuotientEquiv_residue_smul k X)).finrank_eq.symm

/-- **The valued mesh relation of an almost-split sequence** `0 → A → B → C → 0`: for every object
`X` with a local endomorphism ring, the second entry of the valuation of `Irr(X, C)` equals the
first entry of the valuation of `Irr(A, X)`, both being the multiplicity of `X` as a summand of
`B`. -/
theorem irreducibleMorphismValuation_snd_eq_fst (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C)
    [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k X S.X₃).2 = (irreducibleMorphismValuation k S.X₁ X).1 := by
  rw [hS.irreducibleMorphismValuation_snd_eq_natCard k P e,
    hS.irreducibleMorphismValuation_fst_eq_natCard k P e]

end CategoryTheory.ShortComplex.IsAlmostSplit
