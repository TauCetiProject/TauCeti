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

Let `0 → A → B → C → 0` be an almost-split sequence in a balanced `k`-linear category (its end
terms `A` and `C` then have local endomorphism rings), and let `B ≅ ⨁ P` be a decomposition of its
middle term into finitely many objects with local endomorphism rings. For an object `X` with a
local endomorphism ring, write `μ` for the number of summands `P j` isomorphic to `X`. Then the
space `Irr(X, C)` of irreducible morphisms has dimension `μ` over the residue division ring of
`X`, and so does `Irr(A, X)`. In terms of the
valuations `(a, b)` of `TauCeti.irreducibleMorphismValuation`, this reads `b_{XC} = μ = a_{AX}`.
When `A` is the Auslander-Reiten translate of `C`, this is the valued mesh relation of the
Auslander-Reiten quiver at `C`.

The identifications `Hom(X, B) / rad ≅ Irr(X, C)` and `Hom(B, X) / rad ≅ Irr(A, X)` of
`TauCeti/CategoryTheory/AlmostSplit/RadicalQuotient.lean` commute with the residue actions of `X`
(`rightRadicalQuotientEquiv_residueOp_smul` and `leftRadicalQuotientEquiv_residue_smul`), so they
are linear equivalences over the residue ring of `X` (`rightRadicalQuotientResidueEquiv` and
`leftRadicalQuotientResidueEquiv`). The multiplicity is then counted by
`TauCeti.finrank_residueOp_radicalQuotient_biproduct` and
`TauCeti.finrank_residue_radicalQuotient_biproduct`. No field and no finiteness over the base ring
is assumed, so this covers Artin algebras over a commutative Artinian ring. Over a field, the
`k`-dimensional form of these counts is
`TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left`.

## Main definitions

* `CategoryTheory.ShortComplex.IsAlmostSplit.rightRadicalQuotientResidueEquiv` and
  `CategoryTheory.ShortComplex.IsAlmostSplit.leftRadicalQuotientResidueEquiv`: the
  identifications `Hom(X, B) / rad ≅ Irr(X, C)` and `Hom(B, X) / rad ≅ Irr(A, X)` as linear
  equivalences over the residue ring of `X`.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.finite_residueOp_irreducibleMorphismSpace` and
  `CategoryTheory.ShortComplex.IsAlmostSplit.finite_residue_irreducibleMorphismSpace`: `Irr(X, C)`
  and `Irr(A, X)` are finite over the residue division ring of `X`.
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
  {S : ShortComplex C}
  (k : Type*) [Ring k] [Linear k C]

/-- The identification of morphisms into the middle term, modulo the radical, with irreducible
morphisms into the final term commutes with the residue action of the source. -/
@[simp]
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
@[simp]
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

/-- **Morphisms into the middle term, modulo the radical, are irreducible morphisms into the final
term**, as a linear equivalence over the residue ring of the source. -/
noncomputable def rightRadicalQuotientResidueEquiv (hS : S.IsAlmostSplit) (X : C) :
    ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) ≃ₗ[(End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ]
      irreducibleMorphismSpace k X S.X₃ :=
  (hS.rightRadicalQuotientEquiv k X).toAddEquiv.toLinearEquiv
    (hS.rightRadicalQuotientEquiv_residueOp_smul k X)

@[simp]
theorem rightRadicalQuotientResidueEquiv_apply (hS : S.IsAlmostSplit) (X : C)
    (q : (X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) :
    hS.rightRadicalQuotientResidueEquiv k X q = hS.rightRadicalQuotientEquiv k X q :=
  (rfl)

@[simp]
theorem rightRadicalQuotientResidueEquiv_symm_apply (hS : S.IsAlmostSplit) (X : C)
    (q : irreducibleMorphismSpace k X S.X₃) :
    (hS.rightRadicalQuotientResidueEquiv k X).symm q = (hS.rightRadicalQuotientEquiv k X).symm q :=
  (rfl)

/-- The inverse identification of irreducible morphisms into the final term with morphisms into the
middle term, modulo the radical, commutes with the residue action of the source. -/
@[simp]
theorem rightRadicalQuotientEquiv_symm_residueOp_smul (hS : S.IsAlmostSplit) (X : C)
    (d : (End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (q : irreducibleMorphismSpace k X S.X₃) :
    (hS.rightRadicalQuotientEquiv k X).symm (d • q) =
      d • (hS.rightRadicalQuotientEquiv k X).symm q :=
  (hS.rightRadicalQuotientResidueEquiv k X).symm.map_smul d q

/-- **Morphisms out of the middle term, modulo the radical, are irreducible morphisms out of the
initial term**, as a linear equivalence over the residue ring of the target. -/
noncomputable def leftRadicalQuotientResidueEquiv (hS : S.IsAlmostSplit) (X : C) :
    ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) ≃ₗ[End X ⧸ Ring.jacobson (End X)]
      irreducibleMorphismSpace k S.X₁ X :=
  (hS.leftRadicalQuotientEquiv k X).toAddEquiv.toLinearEquiv
    (hS.leftRadicalQuotientEquiv_residue_smul k X)

@[simp]
theorem leftRadicalQuotientResidueEquiv_apply (hS : S.IsAlmostSplit) (X : C)
    (q : (S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) :
    hS.leftRadicalQuotientResidueEquiv k X q = hS.leftRadicalQuotientEquiv k X q :=
  (rfl)

@[simp]
theorem leftRadicalQuotientResidueEquiv_symm_apply (hS : S.IsAlmostSplit) (X : C)
    (q : irreducibleMorphismSpace k S.X₁ X) :
    (hS.leftRadicalQuotientResidueEquiv k X).symm q = (hS.leftRadicalQuotientEquiv k X).symm q :=
  (rfl)

/-- The inverse identification of irreducible morphisms out of the initial term with morphisms out
of the middle term, modulo the radical, commutes with the residue action of the target. -/
@[simp]
theorem leftRadicalQuotientEquiv_symm_residue_smul (hS : S.IsAlmostSplit) (X : C)
    (d : End X ⧸ Ring.jacobson (End X)) (q : irreducibleMorphismSpace k S.X₁ X) :
    (hS.leftRadicalQuotientEquiv k X).symm (d • q) = d • (hS.leftRadicalQuotientEquiv k X).symm q :=
  (hS.leftRadicalQuotientResidueEquiv k X).symm.map_smul d q

/-- The second entry of the valuation of `Irr(X, C)`, for an almost-split sequence
`0 → A → B → C → 0`, is the dimension of `(X ⟶ B) / rad` over the residue ring of `X`. -/
theorem irreducibleMorphismValuation_snd_eq_finrank (hS : S.IsAlmostSplit) (X : C) :
    (irreducibleMorphismValuation k X S.X₃).2 =
      finrank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
        ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) := by
  rw [irreducibleMorphismValuation_snd, (hS.rightRadicalQuotientResidueEquiv k X).finrank_eq]

/-- The first entry of the valuation of `Irr(A, X)`, for an almost-split sequence
`0 → A → B → C → 0`, is the dimension of `(B ⟶ X) / rad` over the residue ring of `X`. -/
theorem irreducibleMorphismValuation_fst_eq_finrank (hS : S.IsAlmostSplit) (X : C) :
    (irreducibleMorphismValuation k S.X₁ X).1 =
      finrank (End X ⧸ Ring.jacobson (End X)) ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) := by
  rw [irreducibleMorphismValuation_fst, (hS.leftRadicalQuotientResidueEquiv k X).finrank_eq]

variable {J : Type*} [Finite J] (P : J → C) [HasBiproduct P] [∀ j, IsLocalRing (End (P j))]

/-- In an almost-split sequence `0 → A → B → C → 0` with `B ≅ ⨁ P` a finite biproduct of objects
with local endomorphism rings, `Irr(X, C)` is a finite module over the residue division ring of an
object `X` with a local endomorphism ring. -/
theorem finite_residueOp_irreducibleMorphismSpace (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C)
    [IsLocalRing (End X)] :
    Module.Finite ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X S.X₃) :=
  .equiv ((radicalQuotientCongrRight k X e).symm.trans (hS.rightRadicalQuotientResidueEquiv k X))

/-- In an almost-split sequence `0 → A → B → C → 0` with `B ≅ ⨁ P` a finite biproduct of objects
with local endomorphism rings, `Irr(A, X)` is a finite module over the residue division ring of an
object `X` with a local endomorphism ring. -/
theorem finite_residue_irreducibleMorphismSpace (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C)
    [IsLocalRing (End X)] :
    Module.Finite (End X ⧸ Ring.jacobson (End X)) (irreducibleMorphismSpace k S.X₁ X) :=
  .equiv ((radicalQuotientCongrLeft k X e).symm.trans (hS.leftRadicalQuotientResidueEquiv k X))

/-- **The multiplicity of a summand of the middle term, through the final term**: in an
almost-split sequence `0 → A → B → C → 0` in a balanced category, with `B ≅ ⨁ P` a finite biproduct
of objects with local endomorphism rings, and for an object `X` with a local endomorphism ring, the
dimension of `Irr(X, C)` over the residue division ring of `X` (the second entry of its valuation)
is the number of summands `P j` isomorphic to `X`. -/
theorem irreducibleMorphismValuation_snd_eq_natCard (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P)
    (X : C) [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k X S.X₃).2 = Nat.card {j // Nonempty (P j ≅ X)} := by
  rw [hS.irreducibleMorphismValuation_snd_eq_finrank k,
    (radicalQuotientCongrRight k X e).finrank_eq, finrank_residueOp_radicalQuotient_biproduct k X P]

/-- **The multiplicity of a summand of the middle term, through the initial term**: in an
almost-split sequence `0 → A → B → C → 0` in a balanced category, with `B ≅ ⨁ P` a finite biproduct
of objects with local endomorphism rings, and for an object `X` with a local endomorphism ring, the
dimension of `Irr(A, X)` over the residue division ring of `X` (the first entry of its valuation)
is the number of summands `P j` isomorphic to `X`. -/
theorem irreducibleMorphismValuation_fst_eq_natCard (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P)
    (X : C) [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k S.X₁ X).1 = Nat.card {j // Nonempty (P j ≅ X)} := by
  rw [hS.irreducibleMorphismValuation_fst_eq_finrank k,
    (radicalQuotientCongrLeft k X e).finrank_eq, finrank_residue_radicalQuotient_biproduct k X P]

/-- **The valued mesh relation of an almost-split sequence** `0 → A → B → C → 0` in a balanced
category, whose middle term `B ≅ ⨁ P` is a finite biproduct of objects with local endomorphism
rings: for every object `X` with a local endomorphism ring, the second entry of the valuation of
`Irr(X, C)` equals the first entry of the valuation of `Irr(A, X)`, both being the multiplicity of
`X` as a summand of `B`. -/
theorem irreducibleMorphismValuation_snd_eq_fst (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C)
    [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k X S.X₃).2 = (irreducibleMorphismValuation k S.X₁ X).1 := by
  rw [hS.irreducibleMorphismValuation_snd_eq_natCard k P e,
    hS.irreducibleMorphismValuation_fst_eq_natCard k P e]

end CategoryTheory.ShortComplex.IsAlmostSplit
