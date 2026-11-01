/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic

/-!
# Componentwise torsion over a finite product of fields

Let `C` be a `ℤ`-graded chain complex of modules over a commutative ring `A`, with an ordered
basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree. For a ring homomorphism `φ : A →+* K`
into a field, the *coordinate base change* `HomologicalComplex.baseChange c φ` is the chain complex
of `K`-vector spaces `Kⁿ⁽ⁱ⁾` whose differentials are the matrices of the differentials of `C`
in the bases `c`, with `φ` applied to every entry. It is the coordinate model of the scalar
extension `K ⊗_A C` with its induced bases, chosen so that the matrices of its differentials are
the images of those of `C` by definition. Its torsion is natural in `φ`
(`HomologicalComplex.map_reidemeisterTorsion_baseChange`), and it only depends on the matrices of
the differentials (`HomologicalComplex.reidemeisterTorsion_eq_reidemeisterTorsion_baseChange`).

A reduced Artinian ring `Q`, such as the total ring of fractions of a reduced Noetherian ring, is
the finite product of its residue fields `Q ⧸ m` over its maximal ideals `m`
(`IsArtinianRing.equivPi`). For a ring homomorphism `f : A →+* Q`, the *componentwise torsion*
`HomologicalComplex.componentwiseReidemeisterTorsion c f : Q` is the element whose component in
`Q ⧸ m` is the torsion of the base change of `C` along `A → Q → Q ⧸ m`
(`HomologicalComplex.mk_componentwiseReidemeisterTorsion`). For a bounded complex a component
vanishes exactly when the corresponding base change is not acyclic
(`HomologicalComplex.mk_componentwiseReidemeisterTorsion_eq_zero_iff`), so the componentwise
torsion keeps track of partial acyclicity: it is a unit exactly when every component complex is
acyclic (`HomologicalComplex.isUnit_componentwiseReidemeisterTorsion_iff`), and it is `0` exactly
when none is (`HomologicalComplex.componentwiseReidemeisterTorsion_eq_zero_iff`). A single
global zero convention would forget the components on which the complex is acyclic.

For a field `F` and `f = RingHom.id F` the componentwise torsion is the torsion
`HomologicalComplex.reidemeisterTorsion` of the based complex itself
(`HomologicalComplex.componentwiseReidemeisterTorsion_id`). It is natural under ring homomorphisms
`g : Q →+* Q'` between reduced Artinian rings
(`HomologicalComplex.map_componentwiseReidemeisterTorsion`): `g` sends the componentwise torsion
along `f` to the componentwise torsion along `g ∘ f`. The proof compares components through the
residue field homomorphism `Q ⧸ g⁻¹(m') → Q' ⧸ m'`, using that every prime ideal of an Artinian
ring is maximal. It is also invariant under a change of coefficient ring of the complex that
preserves the matrices of the differentials
(`HomologicalComplex.componentwiseReidemeisterTorsion_eq_of_toMatrix_eq`).

These two compatibilities compare torsions of the same based complex computed in different total
rings of fractions. For instance, a based complex over a group ring `ℤ[H]` has a componentwise
torsion in the total ring of fractions `Q(ℤ[H])`, and the base change of that complex to a
completion of `ℤ[H]` has a componentwise torsion in the total ring of fractions of the completion.
Whenever a ring homomorphism between the two total rings of fractions is compatible with the
completion map, it carries the first torsion to the second.

## Main definitions

* `HomologicalComplex.baseChange c φ`: the base change of a based complex along a ring
  homomorphism into a field, in coordinates.
* `HomologicalComplex.componentwiseReidemeisterTorsion c f`: the componentwise torsion in a
  reduced Artinian ring.

## Main results

* `HomologicalComplex.mk_componentwiseReidemeisterTorsion`: the components of the componentwise
  torsion.
* `HomologicalComplex.isUnit_componentwiseReidemeisterTorsion_iff`,
  `HomologicalComplex.componentwiseReidemeisterTorsion_eq_zero_iff`: units and zero detect
  acyclicity of every component, respectively of no component.
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

variable {A : Type*} [CommRing A] (C : ChainComplex (ModuleCat A) ℤ) {n : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) A (C.X i))

/-- The matrices of two consecutive differentials of a based complex multiply to zero. -/
theorem toMatrix_d_mul_toMatrix_d (i : ℤ) :
    LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom *
      LinearMap.toMatrix (c (i + 1 + 1)) (c (i + 1)) (C.d (i + 1 + 1) (i + 1)).hom = 0 := by
  rw [← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero, map_zero]

section BaseChange

variable {K : Type*} [CommRing K] (φ : A →+* K)

/-- The base change of a based complex `C` along a ring homomorphism `φ : A →+* K`, in
coordinates: the chain complex of free `K`-modules `Kⁿ⁽ⁱ⁾` whose differentials are the matrices
of the differentials of `C` in the bases `c i`, with `φ` applied to every entry. -/
noncomputable def baseChange : ChainComplex (ModuleCat K) ℤ :=
  ChainComplex.of (fun i ↦ ModuleCat.of K (Fin (n i) → K))
    (fun i ↦ ModuleCat.ofHom (Matrix.toLin'
      ((LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map φ)))
    fun i ↦ by
      ext1
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ← Matrix.toLin'_mul,
        ← Matrix.map_mul, toMatrix_d_mul_toMatrix_d, Matrix.map_zero _ (map_zero φ), map_zero,
        ModuleCat.hom_zero]

/-- The standard basis of the base change `HomologicalComplex.baseChange c φ` in degree `i`. -/
noncomputable def baseChangeBasis (i : ℤ) : Basis (Fin (n i)) K ((C.baseChange c φ).X i) :=
  Pi.basisFun K (Fin (n i))

/-- The matrices of the differentials of the base change, in the standard bases, are the images
under `φ` of the matrices of the differentials of `C`. -/
@[simp]
theorem toMatrix_baseChange_d (i : ℤ) :
    LinearMap.toMatrix (C.baseChangeBasis c φ (i + 1)) (C.baseChangeBasis c φ i)
        ((C.baseChange c φ).d (i + 1) i).hom =
      (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map φ := by
  simp only [baseChange, ChainComplex.of_d, ModuleCat.hom_ofHom]
  exact LinearMap.toMatrix_toLin (Pi.basisFun K (Fin (n (i + 1)))) (Pi.basisFun K (Fin (n i))) _

end BaseChange

section BaseChangeTorsion

/-! ### The torsion of the base change to a field -/

variable {C c} {K : Type*} [Field K] (φ : A →+* K)

/-- The torsion of the base change only depends on the matrices of the differentials: a based
complex `(D, e)` over `K` whose differentials have the images under `φ` of the matrices of the
differentials of `C` has the torsion of `HomologicalComplex.baseChange c φ`. -/
theorem reidemeisterTorsion_eq_reidemeisterTorsion_baseChange
    {D : ChainComplex (ModuleCat K) ℤ} {e : ∀ i, Basis (Fin (n i)) K (D.X i)}
    (hd : ∀ i, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom =
      (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map φ) :
    D.reidemeisterTorsion e =
      (C.baseChange c φ).reidemeisterTorsion (C.baseChangeBasis c φ) :=
  (map_reidemeisterTorsion (RingHom.id K) fun i ↦ by simp [hd]).symm

/-- The torsion of the base change is natural in the field: a homomorphism of fields `ψ : K →+* L`
sends the torsion of the base change along `φ` to the torsion of the base change along
`ψ ∘ φ`. -/
theorem map_reidemeisterTorsion_baseChange {L : Type*} [Field L] (ψ : K →+* L) :
    ψ ((C.baseChange c φ).reidemeisterTorsion (C.baseChangeBasis c φ)) =
      (C.baseChange c (ψ.comp φ)).reidemeisterTorsion (C.baseChangeBasis c (ψ.comp φ)) :=
  map_reidemeisterTorsion ψ fun i ↦ by
    rw [toMatrix_baseChange_d, toMatrix_baseChange_d, Matrix.map_map, RingHom.coe_comp]

/-- The torsion of a based complex `C` over a field `F` is the torsion of its base change along
the identity of `F`. -/
theorem reidemeisterTorsion_baseChange_id {F : Type*} [Field F]
    {C : ChainComplex (ModuleCat F) ℤ} {c : ∀ i, Basis (Fin (n i)) F (C.X i)} :
    (C.baseChange c (RingHom.id F)).reidemeisterTorsion (C.baseChangeBasis c (RingHom.id F)) =
      C.reidemeisterTorsion c :=
  (map_reidemeisterTorsion (C := C) (c := c) (RingHom.id F) fun i ↦
    toMatrix_baseChange_d C c _ i).symm

/-- The torsion of the base change is invariant under a change of coefficient ring of the complex
which preserves the matrices of the differentials: if the differentials of a based complex
`(C', c')` over `A'` have the images under `h : A →+* A'` of the matrices of the differentials of
`C`, then the base change of `C'` along `φ'` has the torsion of the base change of `C` along
`φ' ∘ h`. -/
theorem reidemeisterTorsion_baseChange_eq_of_toMatrix_eq {A' : Type*} [CommRing A']
    {C' : ChainComplex (ModuleCat A') ℤ} {c' : ∀ i, Basis (Fin (n i)) A' (C'.X i)}
    (h : A →+* A')
    (hd : ∀ i, LinearMap.toMatrix (c' (i + 1)) (c' i) (C'.d (i + 1) i).hom =
      (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map h)
    (φ' : A' →+* K) :
    (C'.baseChange c' φ').reidemeisterTorsion (C'.baseChangeBasis c' φ') =
      (C.baseChange c (φ'.comp h)).reidemeisterTorsion (C.baseChangeBasis c (φ'.comp h)) :=
  reidemeisterTorsion_eq_reidemeisterTorsion_baseChange _ fun i ↦ by
    rw [toMatrix_baseChange_d, hd, Matrix.map_map, RingHom.coe_comp]

end BaseChangeTorsion

section Componentwise

/-! ### Componentwise torsion in a reduced Artinian ring -/

attribute [local instance] Ideal.Quotient.field

variable {Q : Type*} [CommRing Q] [IsArtinianRing Q] [IsReduced Q] (f : A →+* Q)

/-- The componentwise torsion of a based complex `C` over `A` along a ring homomorphism
`f : A →+* Q` into a reduced Artinian ring, which is the finite product of its residue fields
`Q ⧸ m`: the element of `Q` whose component in `Q ⧸ m` is the torsion of the base change of `C`
along `A → Q → Q ⧸ m`. A component is `0` exactly when that base change is not acyclic, or when
`C` is unbounded. -/
noncomputable def componentwiseReidemeisterTorsion : Q :=
  (IsArtinianRing.equivPi Q).symm fun m ↦
    (C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
      (C.baseChangeBasis c _)

/-- The component of the componentwise torsion in the residue field `Q ⧸ m` is the torsion of the
base change of `C` along `A → Q → Q ⧸ m`. -/
@[simp]
theorem mk_componentwiseReidemeisterTorsion (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseReidemeisterTorsion c f) =
      (C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
        (C.baseChangeBasis c _) := by
  rw [componentwiseReidemeisterTorsion, ← IsArtinianRing.equivPi_apply, AlgEquiv.apply_symm_apply]

variable {C c f}

/-- The componentwise torsion is characterized by its components: an element of `Q` is the
componentwise torsion exactly when its component in each residue field `Q ⧸ m` is the torsion of
the base change of `C` along `A → Q → Q ⧸ m`. -/
theorem eq_componentwiseReidemeisterTorsion_iff {x : Q} :
    x = C.componentwiseReidemeisterTorsion c f ↔ ∀ m : MaximalSpectrum Q,
      Ideal.Quotient.mk m.asIdeal x =
        (C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
          (C.baseChangeBasis c _) := by
  simp_rw [← mk_componentwiseReidemeisterTorsion, ← IsArtinianRing.equivPi_apply, ← funext_iff,
    (IsArtinianRing.equivPi Q).injective.eq_iff]

/-- For a bounded complex, the component of the componentwise torsion in `Q ⧸ m` vanishes exactly
when the base change of `C` along `A → Q → Q ⧸ m` is not acyclic. -/
theorem mk_componentwiseReidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite)
    (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseReidemeisterTorsion c f) = 0 ↔
      ¬(C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [mk_componentwiseReidemeisterTorsion, reidemeisterTorsion_eq_zero_iff _ _ hn]

/-- The componentwise torsion of a bounded complex is a unit exactly when the base change of `C` to
every residue field of `Q` is acyclic. -/
theorem isUnit_componentwiseReidemeisterTorsion_iff (hn : {i | n i ≠ 0}.Finite) :
    IsUnit (C.componentwiseReidemeisterTorsion c f) ↔ ∀ m : MaximalSpectrum Q,
      (C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [← isUnit_map_iff (IsArtinianRing.equivPi Q), Pi.isUnit_iff]
  refine forall_congr' fun m ↦ ?_
  rw [IsArtinianRing.equivPi_apply, isUnit_iff_ne_zero, ne_eq,
    mk_componentwiseReidemeisterTorsion_eq_zero_iff hn, not_not]

/-- The componentwise torsion of a bounded complex is `0` exactly when the base change of `C` to
no residue field of `Q` is acyclic. -/
theorem componentwiseReidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite) :
    C.componentwiseReidemeisterTorsion c f = 0 ↔ ∀ m : MaximalSpectrum Q,
      ¬(C.baseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [eq_comm, eq_componentwiseReidemeisterTorsion_iff]
  refine forall_congr' fun m ↦ ?_
  rw [map_zero, eq_comm, reidemeisterTorsion_eq_zero_iff _ _ hn]

/-- Over a field `F`, the componentwise torsion along the identity is the torsion of the based
complex. -/
theorem componentwiseReidemeisterTorsion_id {F : Type*} [Field F]
    {C : ChainComplex (ModuleCat F) ℤ} {c : ∀ i, Basis (Fin (n i)) F (C.X i)} :
    C.componentwiseReidemeisterTorsion c (RingHom.id F) = C.reidemeisterTorsion c := by
  refine (eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦ ?_).symm
  rw [← reidemeisterTorsion_baseChange_id, map_reidemeisterTorsion_baseChange]

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
    rw [hg, mk_componentwiseReidemeisterTorsion, map_reidemeisterTorsion_baseChange, hψ]

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
    rw [mk_componentwiseReidemeisterTorsion, reidemeisterTorsion_baseChange_eq_of_toMatrix_eq h hd,
      RingHom.comp_assoc]

end Componentwise

end HomologicalComplex
