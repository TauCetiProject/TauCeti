/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence

/-!
# Conjugation of Borel subgroups

Conjugation by a rational point is an automorphism of the ambient affine group, so it preserves
Borel subgroups. This file records that invariance for the Hopf-ideal definition of a Borel
subgroup, both over a general field and in the algebraically closed formulation.

This invariance is the half of a conjugacy statement for Borel subgroups that does not depend on
the existence of a conjugating rational point. Over an algebraically closed field, the generic
consequences of a theorem conjugating every Borel candidate into a distinguished one are also
collected here: the distinguished candidate is then a Borel subgroup, the Borel subgroups are
exactly its conjugates, and any two of them are conjugate. Concrete matrix groups only need to
supply that group-specific input, which Lie--Kolchin provides for the general linear group.

## Main declarations

* `TauCeti.HopfIdeal.IsBorel.conjugate`: the conjugate of a Borel subgroup is Borel.
* `TauCeti.HopfIdeal.isBorel_conjugate_iff`: Borel status is invariant under conjugation.
* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.conjugate` and
  `TauCeti.HopfIdeal.isBorelOverAlgClosed_conjugate_iff`: the same invariance for the
  algebraically closed Borel predicate.
* `TauCeti.HopfIdeal.isBorelOverAlgClosed_of_forall_exists_conjugate_le`: a Borel candidate into
  which every Borel candidate can be conjugated is a Borel subgroup.
* `TauCeti.HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate`: the Borel subgroups are then
  exactly its conjugates.
* `TauCeti.HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed`: any two Borel subgroups are
  then conjugate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Section 11.1.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

section General

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The conjugate of a Borel subgroup by a rational point is a Borel subgroup. -/
theorem IsBorel.conjugate {I : HopfIdeal k H}
    (hI : IsBorel k (_root_.CommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsBorel k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-- Borel status is invariant under conjugation by a rational point.

This is not a `simp` lemma: `isBorel_iff` unfolds `IsBorel` on the left-hand side, so the
statement is never in `simp`-normal form. -/
theorem isBorel_conjugate_iff (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    IsBorel k (_root_.CommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsBorel k (_root_.CommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    have h := hI.conjugate g⁻¹
    simpa using h
  · exact fun hI ↦ hI.conjugate g

/-- Over an algebraically closed field, the conjugate of a Borel subgroup by a rational point is
a Borel subgroup. -/
theorem IsBorelOverAlgClosed.conjugate {I : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (g : WithConv (H →ₐ[k] k)) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) (I.conjugate g) := by
  have h := hI.comapOfIso (HopfAlgebra.pointConjugationFiniteTypeIso g)
  rw [conjugate_eq_comapOfSurjective]
  simpa only [HopfAlgebra.pointConjugationFiniteTypeIso_hom] using h

/-- The algebraically closed Borel property is invariant under conjugation by a rational point.

This is not a `simp` lemma: `isBorelOverAlgClosed_iff` unfolds `IsBorelOverAlgClosed` on the
left-hand side, so the statement is never in `simp`-normal form. -/
theorem isBorelOverAlgClosed_conjugate_iff (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) (I.conjugate g) ↔
      IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  constructor
  · intro hI
    have h := hI.conjugate g⁻¹
    simpa using h
  · exact fun hI ↦ hI.conjugate g

end General

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- **A Borel candidate into which every Borel candidate can be conjugated is a Borel
subgroup.** Over an algebraically closed field, if `D` cuts out a smooth, connected, solvable
closed subgroup and every such closed subgroup lies in a conjugate of it, then `D` is maximal
among them. -/
theorem isBorelOverAlgClosed_of_forall_exists_conjugate_le (D : HopfIdeal k H)
    (hD : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) D)
    (hcontain : ∀ I : HopfIdeal k H, IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) I →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) D := by
  obtain ⟨B, hB⟩ := exists_minimal_isBorelCandidate (FiniteTypeCommHopfAlgCat.of k H)
  obtain ⟨g, hg⟩ := hcontain B hB.prop
  have hBg : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) (B.conjugate g⁻¹) :=
    IsBorelOverAlgClosed.conjugate ((isBorelOverAlgClosed_iff _ _ _).mpr ⟨inferInstance, hB⟩) g⁻¹
  have hDB : D ≤ B.conjugate g⁻¹ := by
    simpa using conjugate_mono g⁻¹ hg
  rwa [le_antisymm hDB (((isBorelOverAlgClosed_iff _ _ _).mp hBg).2.2 hD hDB)]

/-- **Over an algebraically closed field, the Borel subgroups are exactly the conjugates of a
distinguished Borel candidate** into which every Borel candidate can be conjugated. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate (D : HopfIdeal k H)
    (hD : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) D)
    (hcontain : ∀ I : HopfIdeal k H, IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) I →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    (I : HopfIdeal k H) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I ↔
      ∃ g : WithConv (H →ₐ[k] k), I = D.conjugate g := by
  have hDB := isBorelOverAlgClosed_of_forall_exists_conjugate_le D hD hcontain
  constructor
  · intro hI
    have hImin := ((isBorelOverAlgClosed_iff _ _ _).mp hI).2
    obtain ⟨g, hg⟩ := hcontain I hImin.prop
    have hDg := ((isBorelOverAlgClosed_iff _ _ _).mp (hDB.conjugate g)).2
    exact ⟨g, le_antisymm (hImin.2 hDg.prop hg) hg⟩
  · rintro ⟨g, rfl⟩
    exact hDB.conjugate g

/-- **Over an algebraically closed field, any two Borel subgroups are conjugate** by a rational
point, provided every Borel candidate can be conjugated into a distinguished Borel candidate. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed (D : HopfIdeal k H)
    (hD : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) D)
    (hcontain : ∀ I : HopfIdeal k H, IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) I →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    {I J : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (hJ : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  obtain ⟨g, rfl⟩ := (isBorelOverAlgClosed_iff_exists_eq_conjugate D hD hcontain I).mp hI
  obtain ⟨h, rfl⟩ := (isBorelOverAlgClosed_iff_exists_eq_conjugate D hD hcontain J).mp hJ
  exact ⟨h * g⁻¹, by simp [conjugate_mul]⟩

end AlgClosed

end TauCeti.HopfIdeal
