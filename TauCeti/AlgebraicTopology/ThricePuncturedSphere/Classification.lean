/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.MonodromyTriple
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber
public import TauCeti.Combinatorics.PermutationTriple.IsoClass

/-!
# Covers of the thrice-punctured sphere are determined by their permutation triples

A connected cover of the thrice-punctured sphere `U = ℂ ∖ {0, 1}` of degree `n` can be rigidified
at the basepoint `b = 1/2` in three ways (`TauCeti.ConnectedFiberNumberedCover`,
`TauCeti.ConnectedPointedCover`, `TauCeti.ConnectedCover`), and each rigidification has its own
combinatorial invariant:

* a cover with numbered fibre has a literal connected permutation triple, its monodromy triple
  along the peripheral loops (`IsCoveringMap.monodromyTriple`);
* a bare cover has the isomorphism class of that triple (`TauCeti.ConnectedIsoClass`), obtained
  from any numbering;
* a pointed cover has the class of that triple with the label of the chosen point marked, modulo
  relabeling the triple and the label together (`TauCeti.MarkedIsoClass`).

Each invariant is constant on isomorphism classes of covers, so descends to a map out of the
corresponding quotient. The three maps commute with the forgetful maps between the
rigidifications and their combinatorial counterparts.

This file proves that each of the three maps is **injective**. At the numbered level this is the
statement that a numbered cover is determined by its numbered monodromy
(`TauCeti.connectedFiberNumberedCoverIso_iff_permCongrHom_comp_monodromyPerm_eq`), together with
the fact that `periph0` and `periph1` generate `π₁(U, b)`, so that the triple determines the
monodromy representation (`TauCeti.ThricePuncturedSphere.permutationTriple_injective`). The other
two levels follow by equivariance for relabeling, since forgetting the numbering, or keeping only
one labelled point, is passing to the relabeling orbits on both sides.

Surjectivity, the realisation of every connected triple by a cover, needs in addition that every
pair of permutations is the monodromy along `periph0` and `periph1` of some representation of
`π₁(U, b)`, that is, that `π₁(U, b)` is free on `periph0` and `periph1`.

## Main declarations

* `TauCeti.ConnectedFiberNumberedCover.connectedTriple`: the connected monodromy triple of a cover
  with numbered fibre, with `connectedTriple_eq_connectedTriple_iff`: two numbered covers have the
  same triple exactly when they are isomorphic.
* `TauCeti.ConnectedFiberNumberedCoverClass.triple`, `TauCeti.ConnectedCoverClass.isoClass`,
  `TauCeti.ConnectedPointedCoverClass.markedClass`: the three classifying maps.
* `TauCeti.ConnectedFiberNumberedCoverClass.triple_injective`,
  `TauCeti.ConnectedCoverClass.isoClass_injective`,
  `TauCeti.ConnectedPointedCoverClass.markedClass_injective`: their injectivity.
* `TauCeti.ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering`,
  `TauCeti.ConnectedFiberNumberedCoverClass.markedClass_markLabel`,
  `TauCeti.ConnectedPointedCoverClass.isoClass_forgetPoint`: compatibility with the forgetful
  maps.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Theorem 2.61 (covers with the same branch values are isomorphic exactly when their monodromies
  are conjugate).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the classification of
  covering spaces).
-/

public section

open Equiv MulAction

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

/-! ### Numbered covers and literal triples -/

namespace ConnectedFiberNumberedCover

/-- The monodromy triple of a connected cover of `ℂ ∖ {0, 1}` with numbered fibre over `1/2`, as a
connected triple: it is connected because the total space is path connected. -/
noncomputable def connectedTriple
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    ConnectedTriple n :=
  letI := c.pathConnected
  ⟨c.cover.isCoveringMap_proj.monodromyTriple c.ν,
    c.cover.isCoveringMap_proj.isConnected_monodromyTriple c.ν⟩

variable (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

@[simp]
theorem coe_connectedTriple :
    (c.connectedTriple : PermutationTriple n) = c.cover.isCoveringMap_proj.monodromyTriple c.ν :=
  (rfl)

/-- Relabeling the fibre relabels the triple. -/
@[simp]
theorem connectedTriple_smul (τ : Perm (Fin n)) :
    (τ • c).connectedTriple = τ • c.connectedTriple :=
  Subtype.ext (c.cover.isCoveringMap_proj.monodromyTriple_trans c.ν τ)

/-- **Two covers of `ℂ ∖ {0, 1}` with numbered fibres have the same triple exactly when they are
isomorphic**, by an isomorphism preserving every label. -/
theorem connectedTriple_eq_connectedTriple_iff
    {c c' : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n} :
    c.connectedTriple = c'.connectedTriple ↔ ConnectedFiberNumberedCoverIso c c' := by
  rw [connectedFiberNumberedCoverIso_iff_permCongrHom_comp_monodromyPerm_eq, Subtype.ext_iff,
    coe_connectedTriple, coe_connectedTriple, IsCoveringMap.monodromyTriple_def,
    IsCoveringMap.monodromyTriple_def, permutationTriple_injective.eq_iff]

end ConnectedFiberNumberedCover

namespace ConnectedFiberNumberedCoverClass

/-- The connected triple of an isomorphism class of numbered covers of `ℂ ∖ {0, 1}`. -/
noncomputable def triple :
    ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
      ConnectedTriple n :=
  Quotient.lift ConnectedFiberNumberedCover.connectedTriple fun _ _ h =>
    ConnectedFiberNumberedCover.connectedTriple_eq_connectedTriple_iff.2 h

@[simp]
theorem triple_mk
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (mk c).triple = c.connectedTriple :=
  (rfl)

/-- Relabeling a numbered class relabels its triple. -/
@[simp]
theorem triple_smul (τ : Perm (Fin n))
    (C : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (τ • C).triple = τ • C.triple :=
  Quotient.inductionOn C fun c => c.connectedTriple_smul τ

/-- **A numbered cover of `ℂ ∖ {0, 1}` is determined up to isomorphism by its triple.** -/
theorem triple_injective :
    Function.Injective
      (triple : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
        ConnectedTriple n) := fun C C' =>
  Quotient.inductionOn₂ C C' fun _ _ h =>
    Quotient.sound (ConnectedFiberNumberedCover.connectedTriple_eq_connectedTriple_iff.1 h)

/-- Two numbered classes whose triples are relabelings of each other are relabelings of each
other. -/
private theorem smul_eq_of_smul_triple_eq {τ : Perm (Fin n)}
    {C C' : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n}
    (h : τ • C'.triple = C.triple) : τ • C' = C :=
  triple_injective (by rw [triple_smul, h])

end ConnectedFiberNumberedCoverClass

/-! ### Bare covers and isomorphism classes of triples -/

namespace ConnectedCoverClass

open ConnectedFiberNumberedCoverClass

/-- The isomorphism class of the triple of a connected cover of `ℂ ∖ {0, 1}`: the relabeling orbit
of the triple of any numbering of the cover (`isoClass_forgetNumbering`). -/
noncomputable def isoClass
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    ConnectedIsoClass n :=
  Quotient.map' (s₁ := orbitRel (Perm (Fin n)) _) (s₂ := orbitRel (Perm (Fin n)) _) triple
    (fun _ _ ⟨τ, hτ⟩ => ⟨τ, (triple_smul τ _).symm.trans (congrArg triple hτ)⟩)
    (orbitRelQuotientEquiv.symm C)

end ConnectedCoverClass

/-- **Forgetting the numbering of a cover is passing to the isomorphism class of its triple.** -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering
    (C : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    C.forgetNumbering.isoClass = ConnectedIsoClass.mk C.triple := by
  rw [ConnectedCoverClass.isoClass, ← orbitRelQuotientEquiv_mk, symm_apply_apply]
  exact Quotient.map'_mk'' _ _ C

/-- **A connected cover of `ℂ ∖ {0, 1}` is determined up to isomorphism by the isomorphism class of
its triple.** -/
theorem ConnectedCoverClass.isoClass_injective :
    Function.Injective
      (isoClass : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
        ConnectedIsoClass n) := by
  intro C C' h
  obtain ⟨N, rfl⟩ := ConnectedFiberNumberedCoverClass.forgetNumbering_surjective C
  obtain ⟨N', rfl⟩ := ConnectedFiberNumberedCoverClass.forgetNumbering_surjective C'
  rw [ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedIsoClass.mk_eq_mk_iff_exists_smul] at h
  obtain ⟨τ, hτ⟩ := h
  exact ConnectedFiberNumberedCoverClass.forgetNumbering_eq_forgetNumbering_iff.2
    ⟨τ⁻¹, inv_smul_eq_iff.2 (ConnectedFiberNumberedCoverClass.smul_eq_of_smul_triple_eq hτ).symm⟩

/-! ### Pointed covers and marked triples -/

namespace ConnectedPointedCoverClass

open ConnectedFiberNumberedCoverClass

/-- The marked class of a pointed connected cover of `ℂ ∖ {0, 1}`: the triple of any numbering of
the cover, with the label of the chosen point marked, modulo relabeling triple and label together
(`markedClass_markLabel`). -/
noncomputable def markedClass
    (C : ConnectedPointedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    MarkedIsoClass n :=
  Quotient.liftOn' (markedOrbitRelQuotientEquiv.symm C)
    (fun Ci => MarkedIsoClass.mk (triple Ci.1) Ci.2)
    (by
      intro Ci Ci' h
      obtain ⟨τ, hτ⟩ := h
      apply MarkedIsoClass.mk_eq_mk_iff.2
      have htriple : τ • triple Ci'.1 = triple Ci.1 :=
        (triple_smul τ _).symm.trans (congrArg (triple ∘ Prod.fst) hτ)
      have hi : τ Ci'.2 = Ci.2 := by
        simpa [Perm.smul_def] using (congrArg Prod.snd hτ)
      exact ⟨τ, Prod.ext htriple hi⟩)

end ConnectedPointedCoverClass

/-- **Keeping only the point labelled `i` of a numbered cover is marking the label `i` of its
triple.** -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.markedClass_markLabel
    (C : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n)
    (i : Fin n) :
    (C.markLabel i).markedClass = MarkedIsoClass.mk C.triple i := by
  rw [ConnectedPointedCoverClass.markedClass, ← markedOrbitRelQuotientEquiv_mk, symm_apply_apply]
  rfl

/-- Forgetting the chosen point of a cover is forgetting the marked label of its marked class. -/
@[simp]
theorem ConnectedPointedCoverClass.isoClass_forgetPoint
    (C : ConnectedPointedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    C.forgetPoint.isoClass = C.markedClass.forget := by
  obtain ⟨N, i, rfl⟩ := C.exists_markLabel_eq
  simp

/-- **A pointed connected cover of `ℂ ∖ {0, 1}` is determined up to pointed isomorphism by its
marked class.** -/
theorem ConnectedPointedCoverClass.markedClass_injective :
    Function.Injective
      (markedClass : ConnectedPointedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
        MarkedIsoClass n) := by
  intro C C' h
  obtain ⟨N, i, rfl⟩ := C.exists_markLabel_eq
  obtain ⟨N', i', rfl⟩ := C'.exists_markLabel_eq
  rw [ConnectedFiberNumberedCoverClass.markedClass_markLabel,
    ConnectedFiberNumberedCoverClass.markedClass_markLabel,
    MarkedIsoClass.mk_eq_mk_iff_exists_smul] at h
  obtain ⟨τ, hτ, hτi⟩ := h
  exact ConnectedFiberNumberedCoverClass.markLabel_eq_markLabel_iff.2
    ⟨τ⁻¹, inv_smul_eq_iff.2 (ConnectedFiberNumberedCoverClass.smul_eq_of_smul_triple_eq hτ).symm,
      by simp [← hτi]⟩

end TauCeti
