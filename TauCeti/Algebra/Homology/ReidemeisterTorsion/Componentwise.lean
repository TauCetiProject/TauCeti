/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Ambiguity
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.MatrixBaseChange
import TauCeti.RingTheory.Artinian.EquivPi

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

The same construction applies to a based two-periodic complex `C`, graded by `ZMod 2`, with the
torsion `HomologicalComplex.parityTorsion` of its coordinate base changes to the residue fields
(`HomologicalComplex.componentwiseParityTorsion`). Floer–Novikov complexes of symplectomorphisms
are two-periodic complexes over Novikov rings, and when the total quotient ring of the Novikov ring
is a finite product of fields their torsion is read in the whole of it, with zero components
exactly where the complex is not acyclic
(`HomologicalComplex.mk_componentwiseParityTorsion_eq_zero_iff`). No boundedness condition is
needed. The componentwise torsion of a two-periodic complex has the same
characterization, zero pattern, field case and naturality as that of a `ℤ`-graded complex
(`HomologicalComplex.componentwiseParityTorsion_id`,
`HomologicalComplex.map_componentwiseParityTorsion`,
`HomologicalComplex.componentwiseParityTorsion_eq_of_toMatrix_eq`).

Changing the bases `c i` of `C` to `c' i` multiplies the componentwise torsion by the image under
`f` of a unit of `A` built from the determinants `[c'ᵢ / cᵢ]` of the new bases with respect to the
old ones: `[c'₀ / c₀] · [c₁ / c'₁]` for a two-periodic complex
(`HomologicalComplex.componentwiseParityTorsion_eq_mul_det`) and `∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)` for a
`ℤ`-graded one (`HomologicalComplex.componentwiseReidemeisterTorsion_eq_mul_finprod_det`). Bases of
Floer–Novikov complexes are fixed only up to the order of the generators, their signs, and the
deck transformations of the chosen lifts, which change these determinants by signed deck
monomials. So the componentwise torsion is well defined as a class modulo signed deck monomials
(`TauCeti.TorsionClass`): if every determinant `[c'ᵢ / cᵢ]` has trivial class, the torsions in
the two bases have the same class, whether or not some of their components vanish
(`TauCeti.TorsionClass.mk_componentwiseParityTorsion_eq_of_mk_det_eq_one`,
`TauCeti.TorsionClass.mk_componentwiseReidemeisterTorsion_eq_of_mk_det_eq_one`).

## Main definitions

* `HomologicalComplex.componentwiseReidemeisterTorsion c f`: the componentwise torsion in a
  reduced Artinian ring.
* `HomologicalComplex.componentwiseParityTorsion c f`: the componentwise torsion of a based
  two-periodic complex in a reduced Artinian ring.

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
* `HomologicalComplex.mk_componentwiseParityTorsion`,
  `HomologicalComplex.isUnit_componentwiseParityTorsion_iff`,
  `HomologicalComplex.componentwiseParityTorsion_eq_zero_iff`,
  `HomologicalComplex.componentwiseParityTorsion_id`,
  `HomologicalComplex.map_componentwiseParityTorsion`: the same results for two-periodic complexes.
* `HomologicalComplex.componentwiseParityTorsion_eq_one`: the zero two-periodic complex has
  componentwise torsion `1`.
* `HomologicalComplex.componentwiseReidemeisterTorsion_eq_mul_finprod_det`,
  `HomologicalComplex.componentwiseParityTorsion_eq_mul_det`: the change of the componentwise
  torsion under a change of the bases.
* `TauCeti.TorsionClass.mk_componentwiseReidemeisterTorsion_eq_of_mk_det_eq_one`,
  `TauCeti.TorsionClass.mk_componentwiseParityTorsion_eq_of_mk_det_eq_one`: the class of the
  componentwise torsion modulo signed deck monomials does not change when the bases change by
  signed deck monomials.

## References

* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §I.2 and §I.3 (torsions
  of chain complexes over rings that are finite products of fields).
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2 (torsion in the total ring of fractions of a Novikov ring, with zero components on
  the components where the complex is not acyclic).
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), §2 (torsion of two-periodic Floer–Novikov complexes).
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

attribute [local instance] Ideal.Quotient.field

variable {A : Type*} [CommRing A] {Q : Type*} [CommRing Q] [IsArtinianRing Q] [IsReduced Q]

section Graded

variable (C : ChainComplex (ModuleCat A) ℤ) {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) A (C.X i))
  (f : A →+* Q)

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
        (C.matrixBaseChangeBasis c _) :=
  IsArtinianRing.mk_equivPi_symm _ m

variable {C c f}

/-- The componentwise torsion is characterized by its components: an element of `Q` is the
componentwise torsion exactly when its component in each residue field `Q ⧸ m` is the torsion of
the coordinate base change of `C` along `A → Q → Q ⧸ m`. -/
theorem eq_componentwiseReidemeisterTorsion_iff {x : Q} :
    x = C.componentwiseReidemeisterTorsion c f ↔ ∀ m : MaximalSpectrum Q,
      Ideal.Quotient.mk m.asIdeal x =
        (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).reidemeisterTorsion
          (C.matrixBaseChangeBasis c _) :=
  IsArtinianRing.eq_equivPi_symm_iff

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
  rw [componentwiseReidemeisterTorsion, IsArtinianRing.isUnit_equivPi_symm_iff]
  exact forall_congr' fun m ↦ (reidemeisterTorsion_eq_zero_iff _ _ hn).not_left

/-- The componentwise torsion of a bounded complex is `0` exactly when the coordinate base change
of `C` to no residue field of `Q` is acyclic. -/
theorem componentwiseReidemeisterTorsion_eq_zero_iff (hn : {i | n i ≠ 0}.Finite) :
    C.componentwiseReidemeisterTorsion c f = 0 ↔ ∀ m : MaximalSpectrum Q,
      ¬(C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [componentwiseReidemeisterTorsion, IsArtinianRing.equivPi_symm_eq_zero_iff]
  exact forall_congr' fun m ↦ reidemeisterTorsion_eq_zero_iff _ _ hn

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
    obtain ⟨p, ψ, hψ⟩ := IsArtinianRing.exists_quotient_ringHom_mk_comp g m'
    rw [hψ, mk_componentwiseReidemeisterTorsion, map_reidemeisterTorsion_matrixBaseChange,
      show (Ideal.Quotient.mk m'.asIdeal).comp (g.comp f) =
        ψ.comp ((Ideal.Quotient.mk p.asIdeal).comp f) from RingHom.ext fun x ↦ hψ (f x)]

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

/-- The basis-change formula for the componentwise torsion: replacing the bases `c i` of `C` by
`c' i` multiplies the componentwise torsion by the image under `f` of the unit
`∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)` of `A`, where `[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect
to `c i`. This holds for every complex, both sides being `0` when `C` is unbounded. -/
theorem componentwiseReidemeisterTorsion_eq_mul_finprod_det
    (c' : ∀ i, Basis (Fin (n i)) A (C.X i)) :
    C.componentwiseReidemeisterTorsion c' f = C.componentwiseReidemeisterTorsion c f *
      f ↑(∏ᶠ i : ℤ, ((c i).isUnit_det (c' i)).unit ^ (i.negOnePow : ℤ)) := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [componentwiseReidemeisterTorsion_of_not_finite hn]
  -- The unit factors are `1` in the degrees where `C` vanishes.
  have hfin : Function.HasFiniteMulSupport fun i : ℤ ↦
      ((c i).isUnit_det (c' i)).unit ^ (i.negOnePow : ℤ) :=
    hn.subset <| Function.mulSupport_subset_iff'.2 fun i hi ↦ by
      have : IsEmpty (Fin (n i)) := by rw [show n i = 0 by simpa using hi]; infer_instance
      ext
      simp
  refine (eq_componentwiseReidemeisterTorsion_iff.2 fun m ↦ ?_).symm
  rw [map_mul, mk_componentwiseReidemeisterTorsion,
    reidemeisterTorsion_matrixBaseChange_eq_mul_finprod_det _ c c']
  congr 1
  -- Read the image of the unit in the residue field through `Units.map`.
  have hψ (u : Aˣ) : Ideal.Quotient.mk m.asIdeal (f u) =
      ((Units.coeHom _).comp (Units.map ((Ideal.Quotient.mk m.asIdeal).comp f).toMonoidHom)) u := by
    simp
  rw [hψ, map_finprod _ hfin]
  simp [Units.val_zpow_eq_zpow_val]

end Graded

section Periodic

/-! ### Two-periodic complexes -/

variable (C : HomologicalComplex (ModuleCat A) (ComplexShape.up (ZMod 2))) {n : ZMod 2 → ℕ}
  (c : ∀ i, Basis (Fin (n i)) A (C.X i)) (f : A →+* Q)

/-- The componentwise torsion of a based two-periodic complex `C` over `A` along a ring
homomorphism `f : A →+* Q` into a reduced Artinian ring, which is the finite product of its
residue fields `Q ⧸ m`: the element of `Q` whose component in `Q ⧸ m` is the torsion of the
coordinate base change of `C` along `A → Q → Q ⧸ m`. A component is `0` exactly when that base
change is not acyclic. -/
noncomputable def componentwiseParityTorsion : Q :=
  (IsArtinianRing.equivPi Q).symm fun m ↦
    (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).parityTorsion
      (C.matrixBaseChangeBasis c _)

/-- The component of the componentwise torsion of a two-periodic complex in the residue field
`Q ⧸ m` is the torsion of the coordinate base change of `C` along `A → Q → Q ⧸ m`. -/
@[simp]
theorem mk_componentwiseParityTorsion (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseParityTorsion c f) =
      (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).parityTorsion
        (C.matrixBaseChangeBasis c _) :=
  IsArtinianRing.mk_equivPi_symm _ m

variable {C c f}

/-- The componentwise torsion of a two-periodic complex is characterized by its components: an
element of `Q` is the componentwise torsion exactly when its component in each residue field
`Q ⧸ m` is the torsion of the coordinate base change of `C` along `A → Q → Q ⧸ m`. -/
theorem eq_componentwiseParityTorsion_iff {x : Q} :
    x = C.componentwiseParityTorsion c f ↔ ∀ m : MaximalSpectrum Q,
      Ideal.Quotient.mk m.asIdeal x =
        (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).parityTorsion
          (C.matrixBaseChangeBasis c _) :=
  IsArtinianRing.eq_equivPi_symm_iff

/-- The component of the componentwise torsion of a two-periodic complex in `Q ⧸ m` vanishes
exactly when the coordinate base change of `C` along `A → Q → Q ⧸ m` is not acyclic. -/
theorem mk_componentwiseParityTorsion_eq_zero_iff (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseParityTorsion c f) = 0 ↔
      ¬(C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [mk_componentwiseParityTorsion, parityTorsion_eq_zero_iff]

/-- The componentwise torsion of a two-periodic complex is a unit exactly when the coordinate base
change of `C` to every residue field of `Q` is acyclic. -/
theorem isUnit_componentwiseParityTorsion_iff :
    IsUnit (C.componentwiseParityTorsion c f) ↔ ∀ m : MaximalSpectrum Q,
      (C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [componentwiseParityTorsion, IsArtinianRing.isUnit_equivPi_symm_iff]
  exact forall_congr' fun m ↦ parityTorsion_eq_zero_iff.not_left

/-- The componentwise torsion of a two-periodic complex is `0` exactly when the coordinate base
change of `C` to no residue field of `Q` is acyclic. -/
theorem componentwiseParityTorsion_eq_zero_iff :
    C.componentwiseParityTorsion c f = 0 ↔ ∀ m : MaximalSpectrum Q,
      ¬(C.matrixBaseChange c ((Ideal.Quotient.mk m.asIdeal).comp f)).Acyclic := by
  rw [componentwiseParityTorsion, IsArtinianRing.equivPi_symm_eq_zero_iff]
  exact forall_congr' fun m ↦ parityTorsion_eq_zero_iff

/-- The zero two-periodic complex, with the empty bases, has componentwise torsion `1`. -/
theorem componentwiseParityTorsion_eq_one (h₀ : n 0 = 0) (h₁ : n 1 = 0) :
    C.componentwiseParityTorsion c f = 1 :=
  (eq_componentwiseParityTorsion_iff.2 fun _ ↦ by rw [map_one, parityTorsion_eq_one h₀ h₁]).symm

/-- In a field `F`, the componentwise torsion of a two-periodic complex along `f : A →+* F` is the
torsion of the coordinate base change of `C` along `f`. -/
theorem componentwiseParityTorsion_eq_parityTorsion_matrixBaseChange {F : Type*} [Field F]
    (f : A →+* F) :
    C.componentwiseParityTorsion c f =
      (C.matrixBaseChange c f).parityTorsion (C.matrixBaseChangeBasis c f) :=
  (eq_componentwiseParityTorsion_iff.2 fun m ↦
    map_parityTorsion_matrixBaseChange f (Ideal.Quotient.mk m.asIdeal)).symm

/-- Over a field `F`, the componentwise torsion of a two-periodic complex along the identity is the
torsion of the based complex. -/
@[simp]
theorem componentwiseParityTorsion_id {F : Type*} [Field F]
    {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))}
    {c : ∀ i, Basis (Fin (n i)) F (C.X i)} :
    C.componentwiseParityTorsion c (RingHom.id F) = C.parityTorsion c :=
  (eq_componentwiseParityTorsion_iff.2 fun m ↦
    map_parityTorsion (Ideal.Quotient.mk m.asIdeal) fun i j ↦ by
      rw [toMatrix_matrixBaseChange_d, RingHom.comp_id]).symm

/-- **Naturality of the componentwise torsion of a two-periodic complex.** A ring homomorphism
`g : Q →+* Q'` between reduced Artinian rings sends the componentwise torsion along `f` to the
componentwise torsion along `g ∘ f`. -/
theorem map_componentwiseParityTorsion {Q' : Type*} [CommRing Q'] [IsArtinianRing Q']
    [IsReduced Q'] (g : Q →+* Q') :
    g (C.componentwiseParityTorsion c f) = C.componentwiseParityTorsion c (g.comp f) :=
  eq_componentwiseParityTorsion_iff.2 fun m' ↦ by
    obtain ⟨p, ψ, hψ⟩ := IsArtinianRing.exists_quotient_ringHom_mk_comp g m'
    rw [hψ, mk_componentwiseParityTorsion, map_parityTorsion_matrixBaseChange,
      show (Ideal.Quotient.mk m'.asIdeal).comp (g.comp f) =
        ψ.comp ((Ideal.Quotient.mk p.asIdeal).comp f) from RingHom.ext fun x ↦ hψ (f x)]

/-- The componentwise torsion of a two-periodic complex is invariant under a change of coefficient
ring of the complex which preserves the matrices of the differentials: if the differentials of a
based two-periodic complex `(C', c')` over `A'` have the images under `h : A →+* A'` of the
matrices of the differentials of `C`, then the componentwise torsion of `C'` along `f'` is the
componentwise torsion of `C` along `f' ∘ h`. -/
theorem componentwiseParityTorsion_eq_of_toMatrix_eq {A' : Type*} [CommRing A']
    {C' : HomologicalComplex (ModuleCat A') (ComplexShape.up (ZMod 2))}
    {c' : ∀ i, Basis (Fin (n i)) A' (C'.X i)} (h : A →+* A')
    (hd : ∀ i j, LinearMap.toMatrix (c' i) (c' j) (C'.d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map h)
    (f' : A' →+* Q) :
    C'.componentwiseParityTorsion c' f' = C.componentwiseParityTorsion c (f'.comp h) :=
  eq_componentwiseParityTorsion_iff.2 fun m ↦ by
    rw [mk_componentwiseParityTorsion]
    -- Both coordinate base changes have the same differential matrices, so their torsions agree
    -- by scalar extension along the identity.
    exact (map_parityTorsion (RingHom.id _) fun i j ↦ by
      simp [hd, Matrix.map_map, Function.comp_assoc]).symm

/-- The basis-change formula for the componentwise torsion of a two-periodic complex: replacing
the bases `c i` of `C` by `c' i` multiplies the componentwise torsion by
`f [c'₀ / c₀] · f [c₁ / c'₁]`, where `[c'ᵢ / cᵢ]` is the determinant of `c' i` with respect to
`c i`. -/
theorem componentwiseParityTorsion_eq_mul_det (c' : ∀ i, Basis (Fin (n i)) A (C.X i)) :
    C.componentwiseParityTorsion c' f = C.componentwiseParityTorsion c f *
      (f ((c 0).det (c' 0)) * f ((c' 1).det (c 1))) :=
  (eq_componentwiseParityTorsion_iff.2 fun m ↦ by
    rw [map_mul, map_mul, mk_componentwiseParityTorsion,
      parityTorsion_matrixBaseChange_eq_mul_det _ c c', RingHom.comp_apply,
      RingHom.comp_apply]).symm

end Periodic

end HomologicalComplex

namespace TauCeti.TorsionClass

/-! ### Torsion classes modulo signs and deck monomials -/

open HomologicalComplex

variable {G A Q : Type*} [Group G] [CommRing A] [CommRing Q] [IsArtinianRing Q] [IsReduced Q]
  {m : G →* Aˣ} {m' : G →* Qˣ} {f : A →+* Q}

/-- **Torsion classes do not depend on bases chosen up to signed deck monomials.** If the
determinant of each `c' i` with respect to `c i` has trivial class, that is, is a signed deck
monomial of `A` (`TauCeti.TorsionClass.mk_eq_mk_iff`), then the
componentwise torsions of a based two-periodic complex in the bases `c` and `c'` have the same
class modulo the signed deck monomials of `Q`, for a ring homomorphism `f : A →+* Q` sending
deck monomials to deck monomials. -/
theorem mk_componentwiseParityTorsion_eq_of_mk_det_eq_one
    {C : HomologicalComplex (ModuleCat A) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
    {c c' : ∀ i, Basis (Fin (n i)) A (C.X i)} (hf : ∀ g, Units.map f (m g) = m' g)
    (h : ∀ i, mk m ((c i).det (c' i)) = 1) :
    mk m' (C.componentwiseParityTorsion c' f) = mk m' (C.componentwiseParityTorsion c f) := by
  -- The inverse change of bases has trivial class as well.
  have h₁ : mk m ((c' 1).det (c 1)) = 1 := by
    rw [← (c 1).det_inv (c' 1), mk_coe_eq_one_iff]
    exact inv_mem ((mk_coe_eq_one_iff m _).1 (h 1))
  rw [componentwiseParityTorsion_eq_mul_det (c := c) c', map_mul, map_mul, ← map_mk f hf,
    ← map_mk f hf, h 0, h₁, map_one, mul_one, mul_one]

/-- **Torsion classes do not depend on bases chosen up to signed deck monomials.** If the
determinant of each `c' i` with respect to `c i` has trivial class, that is, is a signed deck
monomial of `A` (`TauCeti.TorsionClass.mk_eq_mk_iff`), then the
componentwise torsions of a based complex in the bases `c` and `c'` have the same class modulo
the signed deck monomials of `Q`, for a ring homomorphism `f : A →+* Q` sending deck monomials to
deck monomials. -/
theorem mk_componentwiseReidemeisterTorsion_eq_of_mk_det_eq_one
    {C : ChainComplex (ModuleCat A) ℤ} {n : ℤ → ℕ} {c c' : ∀ i, Basis (Fin (n i)) A (C.X i)}
    (hf : ∀ g, Units.map f (m g) = m' g) (h : ∀ i, mk m ((c i).det (c' i)) = 1) :
    mk m' (C.componentwiseReidemeisterTorsion c' f) =
      mk m' (C.componentwiseReidemeisterTorsion c f) := by
  rw [componentwiseReidemeisterTorsion_eq_mul_finprod_det (c := c) c', map_mul, ← map_mk f hf]
  -- The units whose class is trivial are the signed deck monomials, which contain the product.
  have hU : (∏ᶠ i : ℤ, ((c i).isUnit_det (c' i)).unit ^ (i.negOnePow : ℤ)) ∈
      signedMonomialSubgroup m :=
    finprod_induction (· ∈ signedMonomialSubgroup m) (one_mem _) (fun _ _ ↦ mul_mem)
      fun i ↦ zpow_mem ((mk_coe_eq_one_iff m _).1 (h i)) _
  rw [(mk_coe_eq_one_iff m _).2 hU, map_one, mul_one]

end TauCeti.TorsionClass
