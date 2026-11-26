/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.Rational
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.GaloisModule
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Torus.Cocharacter.Basic

/-!
# Split tori and the Galois action on characters and cocharacters

A torus over a field `k` is split exactly when the absolute Galois group acts trivially on its
character lattice, or equivalently on its cocharacter lattice. The character form follows from
the diagonalizability criterion for groups of multiplicative type
(`TauCeti.multiplicativeTypeCommHopfAlgProperty.groupLikeSpannedProperty_iff_forall_smul_eq`),
since a reduced connected diagonalizable group is a split torus. The cocharacter form uses the
perfect, Galois-invariant pairing between characters and cocharacters of a torus.

## Main declarations

* `TauCeti.torusCommHopfAlgProperty.splitTorusCommHopfAlgProperty_iff_forall_smul_eq`: a torus is
  split exactly when the Galois action on its character lattice is trivial.
* `TauCeti.TorusCommHopfAlgCat.forall_smul_cocharacter_eq_iff`: a Galois element fixes every
  cocharacter of a torus exactly when it fixes every character.
* `TauCeti.TorusCommHopfAlgCat.splitTorusCommHopfAlgProperty_iff_forall_smul_cocharacter_eq`: a
  torus is split exactly when the Galois action on its cocharacter lattice is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.g, Corollary 12.24.
-/

public section

namespace TauCeti

universe u

namespace torusCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A torus is split exactly when the absolute Galois group acts trivially on its character
lattice.** This holds over every field. -/
theorem splitTorusCommHopfAlgProperty_iff_forall_smul_eq (hH : torusCommHopfAlgProperty k H) :
    splitTorusCommHopfAlgProperty k H ↔
      ∀ (σ : Field.absoluteGaloisGroup k) (χ : CommHopfAlgCat.geometricCharacterGroup H.obj),
        σ • χ = χ := by
  rw [← (hH.multiplicativeType k H).groupLikeSpannedProperty_iff_forall_smul_eq]
  refine ⟨splitTorusCommHopfAlgProperty.groupLikeSpanned k H, fun hspan ↦ ?_⟩
  have := (hH.geometricallyReduced k H).isReduced
  have := (hH.geometricallyConnected k H).connectedSpace
  exact splitTorusCommHopfAlgProperty.of_groupLikeSetSpan_eq_top H
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff k H).mp hspan)

end torusCommHopfAlgProperty

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- An absolute Galois element fixes every cocharacter of a torus exactly when it fixes every
character: the two lattices are in perfect, Galois-invariant duality. -/
theorem forall_smul_cocharacter_eq_iff (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k) :
    (∀ f : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
        (toMultiplicativeTypeCommHopfAlgCat T), σ • f = f) ↔
      ∀ χ : CommHopfAlgCat.geometricCharacterGroup T.obj.obj, σ • χ = χ := by
  refine ⟨fun hf χ ↦ ?_, fun hχ ↦
    MultiplicativeTypeCommHopfAlgCat.smul_cocharacter_eq_of_forall_smul_eq _ hχ⟩
  let P := MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing
    (toMultiplicativeTypeCommHopfAlgCat T)
  -- The pairing is perfect for a torus, so a character is determined by its pairings.
  apply Additive.ofMul.injective
  apply P.toPerfPair.injective
  apply LinearMap.ext
  intro f
  have hσχ : Additive.ofMul (σ • χ) = σ • Additive.ofMul χ := by
    apply Additive.toMul.injective
    rw [CommHopfAlgCat.toMul_smul, toMul_ofMul, toMul_ofMul]
  have hP : P (σ • Additive.ofMul χ) (σ • f) = P (Additive.ofMul χ) f :=
    MultiplicativeTypeCommHopfAlgCat.characterCocharacterPairing_galois_invariant _ σ _ f
  simpa only [LinearMap.toPerfPair_apply, hf, hσχ] using hP

/-- **A torus is split exactly when the absolute Galois group acts trivially on its cocharacter
lattice.** This holds over every field. -/
theorem splitTorusCommHopfAlgProperty_iff_forall_smul_cocharacter_eq (T : TorusCommHopfAlgCat k) :
    splitTorusCommHopfAlgProperty k T.obj ↔
      ∀ (σ : Field.absoluteGaloisGroup k) (f : MultiplicativeTypeCommHopfAlgCat.cocharacterLattice
        (toMultiplicativeTypeCommHopfAlgCat T)), σ • f = f := by
  simp only [forall_smul_cocharacter_eq_iff,
    T.property.splitTorusCommHopfAlgProperty_iff_forall_smul_eq]

end TorusCommHopfAlgCat

end TauCeti
