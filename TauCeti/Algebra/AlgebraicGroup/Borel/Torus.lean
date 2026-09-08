/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Tori contained in Borel subgroups

Every torus in a finite-type affine group over an algebraically closed field is contained in a
Borel subgroup. The coordinate-ring order is contravariant: if `I` defines the torus and `J`
defines the Borel, containment is the inequality `J ≤ I`. The result follows by viewing a torus
as a smooth, geometrically connected, geometrically solvable Borel candidate and applying the
maximal-candidate existence theorem.

Over an arbitrary field, a Borel containing a given torus need not descend to the ground field.
The geometric form therefore base-changes both the ambient group and the torus ideal to an
algebraic closure, then constructs a Borel there. The quotient-by-base-change comparison is needed
to recognize the base-changed closed subgroup as a torus.

## Main declarations

* `TauCeti.HopfIdeal.exists_isBorelOverAlgClosed_le_of_torus`: every torus over an algebraically
  closed field is contained in a Borel subgroup.
* `TauCeti.HopfIdeal.IsMaximalTorus.exists_isBorelOverAlgClosed_le`: every maximal torus over an
  algebraically closed field is contained in a Borel subgroup.
* `TauCeti.HopfIdeal.exists_geometricBorel_le_baseChangeHopfIdeal_of_torus`: after passage to an
  algebraic closure, every torus is contained in a Borel subgroup of the geometric fibre.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.6 and §17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* T. A. Springer, *Linear Algebraic Groups*, §6.2.

This supplies the torus-to-Borel containment step in Layer 7, "Borel subgroups, maximal tori, and
their conjugacy", of the ReductiveGroups roadmap. Conjugacy of Borel subgroups and maximal tori
remains separate.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- **Every torus over an algebraically closed field is contained in a Borel subgroup.**

In Hopf-ideal order, `J ≤ I` means that the closed subgroup cut out by `J` contains the torus
cut out by `I`. -/
theorem exists_isBorelOverAlgClosed_le_of_torus [IsAlgClosed k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {I : HopfIdeal k H}
    (hI : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    ∃ J : HopfIdeal k H, J ≤ I ∧ IsBorelOverAlgClosed k H J := by
  obtain ⟨J, hJI, hJ⟩ := exists_minimal_isBorelCandidate_le H
    (HopfIdeal.torusCommHopfAlgProperty.isBorelCandidate hI)
  exact ⟨J, hJI, (isBorelOverAlgClosed_iff k H J).mpr ⟨inferInstance, hJ⟩⟩

namespace IsMaximalTorus

/-- Every maximal torus over an algebraically closed field is contained in a Borel subgroup. -/
theorem exists_isBorelOverAlgClosed_le [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : IsMaximalTorus k H.obj I) :
    ∃ J : HopfIdeal k H, J ≤ I ∧ IsBorelOverAlgClosed k H J := by
  apply exists_isBorelOverAlgClosed_le_of_torus H
  exact (isMaximalTorus_iff k H.obj I).mp hI |>.1

end IsMaximalTorus

/-- **After passage to an algebraic closure, every torus is contained in a Borel subgroup.**

The returned ideal is a Borel subgroup of the geometric fibre and contains the base change of the
given torus. No descent of that Borel to the ground field is asserted. -/
theorem exists_geometricBorel_le_baseChangeHopfIdeal_of_torus
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {I : HopfIdeal k H}
    (hI : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
    let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
    ∃ J : HopfIdeal K H', J ≤ I' ∧ IsBorelOverAlgClosed K H' J := by
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  have hsplit : splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient H I)) := by
    rw [torusCommHopfAlgProperty_iff] at hI
    rw [splitTorusCommHopfAlgProperty_iff]
    exact hI
  have hsplit' : splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient H' I') :=
    (splitTorusCommHopfAlgProperty K).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K) qIso.symm) hsplit
  exact exists_isBorelOverAlgClosed_le_of_torus H'
    (splitTorusCommHopfAlgProperty.torus K _ hsplit')

end HopfIdeal

end

end TauCeti
