/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Conjugation of maximal tori

Conjugation by a rational point is an automorphism of the ambient affine group, so it preserves
maximal tori. This file records that invariance for the Hopf-ideal definition of a maximal torus.

This invariance is the half of a conjugacy statement for maximal tori that does not depend on
the existence of a conjugating rational point. Generic consequences of a theorem conjugating
diagonalizable subgroups into a distinguished maximal torus are also collected here, so concrete
matrix groups only need to supply that group-specific input.

## Main declarations

* `TauCeti.HopfIdeal.IsMaximalTorus.conjugate`: the conjugate of a maximal torus is maximal.
* `TauCeti.HopfIdeal.isMaximalTorus_conjugate_iff`: maximal-torus status is invariant under
  conjugation.
* `TauCeti.HopfIdeal.exists_eq_conjugate_of_isMaximalTorus_of_split`: a split maximal torus is
  conjugate to a distinguished maximal torus whenever diagonalizable subgroups can be conjugated
  into it.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Section 11.1.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The conjugate of a maximal torus by a rational point is a maximal torus. -/
theorem IsMaximalTorus.conjugate {I : HopfIdeal k H}
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-- Maximal-torus status is invariant under conjugation by a rational point.

This is not a `simp` lemma: `isMaximalTorus_iff` unfolds `IsMaximalTorus` on the left-hand
side, so the statement is never in `simp`-normal form. -/
theorem isMaximalTorus_conjugate_iff
    (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    have h := hI.conjugate g⁻¹
    simpa using h
  · exact fun hI ↦ hI.conjugate g

/-- A split maximal torus is conjugate to a distinguished maximal torus, provided it can be
conjugated into the distinguished torus. -/
theorem exists_eq_conjugate_of_isMaximalTorus_of_split
    (D : HopfIdeal k H)
    (hD : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) D)
    {I : HopfIdeal k H}
    (hcontain :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          I) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (hsplit : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I)) :
    ∃ g : WithConv (H →ₐ[k] k), I = D.conjugate g := by
  obtain ⟨m, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).mp hsplit
  have hspan : DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        I) :=
    (DiagonalizableGroup.groupLikeSpannedProperty k).prop_of_iso e
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mpr
        (MonoidAlgebra.groupLikeSetSpan_eq_top (R := k) _))
  obtain ⟨g, hg⟩ := hcontain hspan
  have hDg := (isMaximalTorus_iff k _ _).mp (hD.conjugate g)
  exact ⟨g, le_antisymm (((isMaximalTorus_iff k _ _).mp hI).2 _ hDg.1 hg) hg⟩

/-- Any two split maximal tori are conjugate when diagonalizable subgroups can be conjugated into
a distinguished maximal torus. -/
theorem exists_conjugate_eq_of_isMaximalTorus_of_split
    (D : HopfIdeal k H)
    (hD : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) D)
    {I J : HopfIdeal k H}
    (hcontainI :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          I) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    (hcontainJ :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          J) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ J)
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (hJ : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J)
    (hsplitI : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I))
    (hsplitJ : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J)) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  obtain ⟨g, rfl⟩ := exists_eq_conjugate_of_isMaximalTorus_of_split D hD hcontainI hI hsplitI
  obtain ⟨h, rfl⟩ := exists_eq_conjugate_of_isMaximalTorus_of_split D hD hcontainJ hJ hsplitJ
  exact ⟨h * g⁻¹, by simp [conjugate_mul]⟩

/-- Over an algebraically closed field, the maximal tori are exactly the conjugates of a
distinguished maximal torus when diagonalizable subgroups can be conjugated into it. -/
theorem isMaximalTorus_iff_exists_eq_conjugate [IsAlgClosed k]
    (D : HopfIdeal k H)
    (hD : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) D)
    (I : HopfIdeal k H)
    (hcontain :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          I) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I ↔
      ∃ g : WithConv (H →ₐ[k] k), I = D.conjugate g := by
  constructor
  · intro hI
    have htorus := ((isMaximalTorus_iff k (_root_.CommHopfAlgCat.of k H) I).mp hI).1
    have hsplit := torusCommHopfAlgProperty.split k _ htorus
    exact exists_eq_conjugate_of_isMaximalTorus_of_split (k := k) (H := H)
      D hD hcontain hI hsplit
  · rintro ⟨g, rfl⟩
    exact hD.conjugate g

/-- Over an algebraically closed field, any two maximal tori are conjugate when diagonalizable
subgroups can be conjugated into a distinguished maximal torus. -/
theorem exists_conjugate_eq_of_isMaximalTorus [IsAlgClosed k]
    (D : HopfIdeal k H)
    (hD : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) D)
    {I J : HopfIdeal k H}
    (hcontainI :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          I) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    (hcontainJ :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          J) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ J)
    (hI : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I)
    (hJ : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  have htorusI := ((isMaximalTorus_iff k (_root_.CommHopfAlgCat.of k H) I).mp hI).1
  have htorusJ := ((isMaximalTorus_iff k (_root_.CommHopfAlgCat.of k H) J).mp hJ).1
  have hsplitI := torusCommHopfAlgProperty.split k _ htorusI
  have hsplitJ := torusCommHopfAlgProperty.split k _ htorusJ
  exact exists_conjugate_eq_of_isMaximalTorus_of_split (k := k) (H := H)
    D hD hcontainI hcontainJ hI hJ hsplitI hsplitJ

end TauCeti.HopfIdeal
