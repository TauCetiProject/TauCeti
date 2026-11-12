/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.MatrixBaseChange

/-!
# Componentwise torsion over a finite product of fields

Let `C` be a `ℤ`-graded chain complex of modules over a commutative ring `A`, with an ordered
basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree. For a ring homomorphism `φ : A →+* K`
into a field, the coordinate base change `HomologicalComplex.matrixBaseChange c φ` is the chain
complex of `K`-vector spaces `Kⁿ⁽ⁱ⁾` whose differentials are the matrices of the differentials of
`C` in the bases `c`, with `φ` applied to every entry.

A reduced Artinian ring `Q`, such as the total ring of fractions of a reduced Noetherian ring, is
the finite product of its residue fields `Q ⧸ m` over its maximal ideals `m`
(`IsArtinianRing.equivPi`). For a ring homomorphism `f : A →+* Q`, the *componentwise torsion*
`HomologicalComplex.componentwiseReidemeisterTorsion c f : Q` is the element whose component in
`Q ⧸ m` is the torsion of the coordinate base change of `C` along `A → Q → Q ⧸ m`
(`HomologicalComplex.mk_componentwiseReidemeisterTorsion`). For a bounded complex a component
vanishes exactly when the corresponding base change is not acyclic
(`HomologicalComplex.mk_componentwiseReidemeisterTorsion_eq_zero_iff`), so the componentwise
torsion keeps track of partial acyclicity: it is a unit exactly when every component complex is
acyclic (`HomologicalComplex.isUnit_componentwiseReidemeisterTorsion_iff`), and it is `0` exactly
when none is (`HomologicalComplex.componentwiseReidemeisterTorsion_eq_zero_iff`). A single
global zero convention would forget the components on which the complex is acyclic. The
componentwise torsion of an unbounded complex is `0`
(`HomologicalComplex.componentwiseReidemeisterTorsion_of_not_finite`).

When `Q` is a field `F`, the componentwise torsion along `f : A →+* F` is the torsion of the
coordinate base change of `C` along `f`
(`HomologicalComplex.componentwiseReidemeisterTorsion_eq_reidemeisterTorsion_matrixBaseChange`);
for a based complex over `F` and `f = RingHom.id F` it is the torsion
`HomologicalComplex.reidemeisterTorsion` of the based complex itself
(`HomologicalComplex.componentwiseReidemeisterTorsion_id`). The componentwise torsion is natural
under ring homomorphisms `g : Q →+* Q'` between reduced Artinian rings
(`HomologicalComplex.map_componentwiseReidemeisterTorsion`): `g` sends the componentwise torsion
along `f` to the componentwise torsion along `g ∘ f`. The proof compares components through the
residue field homomorphism `Q ⧸ g⁻¹(m') → Q' ⧸ m'`, using that every prime ideal of an Artinian
ring is maximal. It is also invariant under a change of coefficient ring of the complex that
preserves the matrices of the differentials
(`HomologicalComplex.componentwiseReidemeisterTorsion_eq_of_toMatrix_eq`).

These two compatibilities compare torsions of the same based complex computed in different
reduced Artinian rings. For instance, suppose that a based complex over a group ring `ℤ[H]` and
its base change to a completion `R` of `ℤ[H]` are given componentwise torsions along ring
homomorphisms `ℤ[H] →+* Q` and `R →+* Q'` into reduced Artinian rings. Then any ring homomorphism
`Q →+* Q'` compatible with the completion map carries the first torsion to the second.

## Main definitions

* `HomologicalComplex.componentwiseReidemeisterTorsion c f`: the componentwise torsion in a
  reduced Artinian ring.

## Main results

* `HomologicalComplex.mk_componentwiseReidemeisterTorsion`: the components of the componentwise
  torsion.
* `HomologicalComplex.isUnit_componentwiseReidemeisterTorsion_iff`,
  `HomologicalComplex.componentwiseReidemeisterTorsion_eq_zero_iff`: for a bounded complex, units
  and zero detect acyclicity of every component, respectively of no component.
* `HomologicalComplex.componentwiseReidemeisterTorsion_id`: over a field, the componentwise torsion
  is the torsion.
* `HomologicalComplex.map_componentwiseReidemeisterTorsion`: naturality in the reduced Artinian
  ring.

## References

* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §I.2 and §I.3 (torsions
  of chain complexes over rings that are finite products of fields).
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2 (torsion in the total ring of fractions of a Novikov ring, with zero components on
  the components where the complex is not acyclic).
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

attribute [local instance] Ideal.Quotient.field

variable {A : Type*} [CommRing A] (C : ChainComplex (ModuleCat A) ℤ) {n : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) A (C.X i))
  {Q : Type*} [CommRing Q] [IsArtinianRing Q] [IsReduced Q] (f : A →+* Q)

/-- The componentwise torsion of a based complex `C` over `A` along a ring homomorphism
`f : A →+* Q` into a reduced Artinian ring, which is the finite product of its residue fields
`Q ⧸ m`: the element of `Q` whose component in `Q ⧸ m` is the torsion of the coordinate base change
of `C` along `A → Q → Q ⧸ m`. A component is `0` exactly when that base change is not acyclic, or
when `C` is unbounded. -/
noncomputable def componentwiseReidemeisterTorsion : Q :=
  (IsArtinianRing.equivPi Q).symm fun m ↦
    (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
      (C.matrixBaseChangeBasis c _)

/-- The component of the componentwise torsion in the residue field `Q ⧸ m` is the torsion of the
coordinate base change of `C` along `A → Q → Q ⧸ m`. -/
@[simp]
theorem mk_componentwiseReidemeisterTorsion (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseReidemeisterTorsion c f) =
      (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
        (C.matrixBaseChangeBasis c _) := by
  rw [componentwiseReidemeisterTorsion, ← IsArtinianRing.equivPi_apply, AlgEquiv.apply_symm_apply]

variable {C c f}

/-- The componentwise torsion is characterized by its components: an element of `Q` is the
componentwise torsion exactly when its component in each residue field `Q ⧸ m` is the torsion of
the coordinate base change of `C` along `A → Q → Q ⧸ m`. -/
theorem eq_componentwiseReidemeisterTorsion_iff {x : Q} :
    x = C.componentwiseReidemeisterTorsion c f ↔ ∀ m : MaximalSpectrum Q,
      Ideal.Quotient.mk m.asIdeal x =
        (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
          (C.matrixBaseChangeBasis c _) := by
  simp_rw [← mk_componentwiseReidemeisterTorsion, ← IsArtinianRing.equivPi_apply, ← funext_iff,
    (IsArtinianRing.equivPi Q).injective.eq_iff]

/-- The componentwise torsion of an unbounded complex is `0`. -/
@[simp]
theorem componentwiseReidemeisterTorsion_of_not_finite (hn : ¬{i | n i ≠ 0}.Finite) :
    C.componentwiseReidemeisterTorsion c f = 0 :=
  (eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦ by
    rw [map_zero, reidemeisterTorsion_of_not_finite _ _ hn]).symm

/-- For a bounded complex, the component of the componentwise torsion in `Q ⧸ m` vanishes exactly
when the coordinate base change of `C` along `A → Q → Q ⧸ m` is not acyclic. -/
theorem mk_componentwiseReidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite)
    (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseReidemeisterTorsion c f) = 0 ↔
      ¬(C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [mk_componentwiseReidemeisterTorsion, reidemeisterTorsion_eq_zero_iff _ _ hn]

/-- The componentwise torsion of a bounded complex is a unit exactly when the coordinate base
change of `C` to every residue field of `Q` is acyclic. -/
theorem isUnit_componentwiseReidemeisterTorsion_iff (hn : {i | n i ≠ 0}.Finite) :
    IsUnit (C.componentwiseReidemeisterTorsion c f) ↔ ∀ m : MaximalSpectrum Q,
      (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [← isUnit_map_iff (IsArtinianRing.equivPi Q), Pi.isUnit_iff]
  refine forall_congr' fun m ↦ ?_
  rw [IsArtinianRing.equivPi_apply, isUnit_iff_ne_zero, ne_eq,
    mk_componentwiseReidemeisterTorsion_eq_zero_iff hn, not_not]

/-- The componentwise torsion of a bounded complex is `0` exactly when the coordinate base change
of `C` to no residue field of `Q` is acyclic. -/
theorem componentwiseReidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite) :
    C.componentwiseReidemeisterTorsion c f = 0 ↔ ∀ m : MaximalSpectrum Q,
      ¬(C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [eq_comm, eq_componentwiseReidemeisterTorsion_iff]
  refine forall_congr' fun m ↦ ?_
  rw [map_zero, eq_comm, reidemeisterTorsion_eq_zero_iff _ _ hn]

/-- In a field `F`, the componentwise torsion along `f : A →+* F` is the torsion of the coordinate
base change of `C` along `f`. -/
theorem componentwiseReidemeisterTorsion_eq_reidemeisterTorsion_matrixBaseChange {F : Type*}
    [Field F] (f : A →+* F) :
    C.componentwiseReidemeisterTorsion c f =
      (C.matrixBaseChange c f).reidemeisterTorsion (C.matrixBaseChangeBasis c f) :=
  (eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦
    map_reidemeisterTorsion_matrixBaseChange f (Ideal.Quotient.mk m.asIdeal)).symm

/-- Over a field `F`, the componentwise torsion along the identity is the torsion of the based
complex. -/
@[simp]
theorem componentwiseReidemeisterTorsion_id {F : Type*} [Field F]
    {C : ChainComplex (ModuleCat F) ℤ} {c : ∀ i, Basis (Fin (n i)) F (C.X i)} :
    C.componentwiseReidemeisterTorsion c (RingHom.id F) = C.reidemeisterTorsion c :=
  (eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦
    map_reidemeisterTorsion (Ideal.Quotient.mk m.asIdeal) fun i ↦ by
      rw [toMatrix_matrixBaseChange_d, RingHom.comp_id]).symm

/-- **Naturality of the componentwise torsion.** A ring homomorphism `g : Q →+* Q'` between
reduced Artinian rings sends the componentwise torsion along `f` to the componentwise torsion
along `g ∘ f`. -/
theorem map_componentwiseReidemeisterTorsion {Q' : Type*} [CommRing Q'] [IsArtinianRing Q']
    [IsReduced Q'] (g : Q →+* Q') :
    g (C.componentwiseReidemeisterTorsion c f) = C.componentwiseReidemeisterTorsion c (g.comp f) :=
  eq_componentwiseReidemeisterTorsion_iff.2 fun m' ↦ by
    -- The preimage `p` of `m'` is prime, hence maximal in the Artinian ring `Q`, and `g` induces
    -- a homomorphism `ψ : Q ⧸ p →+* Q' ⧸ m'` of residue fields.
    let p : MaximalSpectrum Q := ⟨m'.asIdeal.comap g, IsArtinianRing.isMaximal_of_isPrime _⟩
    let ψ := Ideal.quotientMap m'.asIdeal g (le_refl p.asIdeal)
    have hψ : (Ideal.Quotient.mk m'.asIdeal).comp (g.comp f) =
        ψ.comp ((Ideal.Quotient.mk p.asIdeal).comp f) := by
      ext x
      simp [ψ]
    have hg : Ideal.Quotient.mk m'.asIdeal (g (C.componentwiseReidemeisterTorsion c f)) =
        ψ (Ideal.Quotient.mk p.asIdeal (C.componentwiseReidemeisterTorsion c f)) := by
      rw [Ideal.quotientMap_mk]
    rw [hg, mk_componentwiseReidemeisterTorsion, map_reidemeisterTorsion_matrixBaseChange, hψ]

/-- The componentwise torsion is invariant under a change of coefficient ring of the complex which
preserves the matrices of the differentials: if the differentials of a based complex `(C', c')`
over `A'` have the images under `h : A →+* A'` of the matrices of the differentials of `C`, then
the componentwise torsion of `C'` along `f'` is the componentwise torsion of `C` along `f' ∘ h`. -/
theorem componentwiseReidemeisterTorsion_eq_of_toMatrix_eq {A' : Type*} [CommRing A']
    {C' : ChainComplex (ModuleCat A') ℤ} {c' : ∀ i, Basis (Fin (n i)) A' (C'.X i)}
    (h : A →+* A')
    (hd : ∀ i, LinearMap.toMatrix (c' (i + 1)) (c' i) (C'.d (i + 1) i).hom =
      (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map h)
    (f' : A' →+* Q) :
    C'.componentwiseReidemeisterTorsion c' f' = C.componentwiseReidemeisterTorsion c (f'.comp h) :=
  eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦ by
    rw [mk_componentwiseReidemeisterTorsion]
    -- Both coordinate base changes have the same differential matrices, so their torsions agree
    -- by scalar extension along the identity.
    exact (map_reidemeisterTorsion (RingHom.id _) fun i ↦ by
      simp [hd, Matrix.map_map, Function.comp_assoc]).symm

end HomologicalComplex
