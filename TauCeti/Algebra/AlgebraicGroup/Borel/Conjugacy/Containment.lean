/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Existence
public import TauCeti.Algebra.AlgebraicGroup.Torus.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Torus.Existence

/-!
# Conjugating solvable subgroups into a prescribed Borel

Over an algebraically closed field, every smooth connected solvable closed subgroup can be
conjugated into any prescribed Borel subgroup. In particular this applies to tori. Every Borel
therefore contains a torus maximal in the entire ambient group, rather than merely maximal
among its own torus subgroups.

These results allow maximal-torus conjugacy to be studied inside a single connected solvable
group. They do not assert conjugacy of tori inside that group. The ambient affine group may be
disconnected or nonreduced, and there is no restriction on the characteristic.

The inputs are the extension of a Borel candidate to a Borel in `Borel.Existence`, general
Borel conjugacy in `Borel.Conjugacy.Existence`, and existence and conjugation invariance of
ambient maximal tori in `Torus.Existence` and `Torus.Conjugation`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§11.1 and 11.3.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {B I : HopfIdeal k H}

/-- Every smooth geometrically connected solvable closed subgroup can be conjugated into a
prescribed Borel subgroup. In defining-ideal order, `B ≤ I.conjugate g` says that the conjugate
of the subgroup defined by `I` lies in the Borel defined by `B`. -/
theorem IsBorelOverAlgClosed.exists_le_conjugate_of_isBorelCandidate
    (hB : IsBorelOverAlgClosed k H B) (hI : IsBorelCandidate k H I) :
    ∃ g : WithConv (H →ₐ[k] k), B ≤ I.conjugate g := by
  obtain ⟨D, hDI, hD⟩ := exists_minimal_isBorelCandidate_le H hI
  have hDb : IsBorelOverAlgClosed k H D :=
    (isBorelOverAlgClosed_iff k H D).mpr ⟨inferInstance, hD⟩
  obtain ⟨g, hg⟩ := hDb.exists_conjugate_eq hB
  exact ⟨g, hg ▸ conjugate_mono g hDI⟩

/-- Every Borel subgroup contains a torus maximal in the ambient affine group. Maximality is
with respect to all ambient torus subgroups, including those outside the prescribed Borel. -/
theorem IsBorelOverAlgClosed.exists_isMaximalTorus_ge
    (hB : IsBorelOverAlgClosed k H B) :
    ∃ I : HopfIdeal k H, B ≤ I ∧ IsMaximalTorus k H.obj I := by
  obtain ⟨I, hI⟩ := exists_isMaximalTorus H
  have htorus := (isMaximalTorus_iff k H.obj I).mp hI |>.1
  obtain ⟨g, hg⟩ := hB.exists_le_conjugate_of_isBorelCandidate
    (torusCommHopfAlgProperty.isBorelCandidate htorus)
  exact ⟨I.conjugate g, hg, hI.conjugate g⟩

end TauCeti.HopfIdeal
