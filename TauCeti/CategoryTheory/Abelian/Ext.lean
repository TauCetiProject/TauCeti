/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Ext
public import TauCeti.Algebra.Homology.Opposite

/-!
# Comparing two resolutions computing the same `Ext`

Mathlib's `CategoryTheory.ProjectiveResolution.isoExt` computes `Extⁿ(X, Y)` from any projective
resolution `P` of `X`, as the `n`-th cohomology of the complex `Hom(P, Y)`. When two resolutions
`P` and `Q` of `X` are related by a chain map `φ : P ⟶ Q` lying over the identity of `X`, the two
computations are related by the map `Hom(Q, Y) ⟶ Hom(P, Y)` given by precomposition with `φ`.
This file proves that compatibility.

This is the tool for making a comparison isomorphism through `Ext` explicit: any isomorphism built
by passing from one resolution to another through `Ext` is, on cohomology, precomposition with a
chain map between the resolutions, as soon as such a chain map can be written down.

## Main results

* `CategoryTheory.ProjectiveResolution.isoExt_hom_comp_homologyMap`: for a chain map `φ : P ⟶ Q`
  over the identity, `Q.isoExt n Y` followed by precomposition with `φ` is `P.isoExt n Y`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.2 (comparison theorem) and
  Section 2.4 (derived functors are independent of the resolution).
-/

public section

open CategoryTheory

namespace CategoryTheory.ProjectiveResolution

variable {R : Type*} [Ring R] {C : Type*} [Category* C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/-- **`Ext` computed from two resolutions related by a chain map.** If `φ : P ⟶ Q` is a chain map
between projective resolutions of `X` lying over the identity of `X`, then computing `Extⁿ(X, Y)`
from `Q` and precomposing with `φ` gives the computation from `P`. -/
theorem isoExt_hom_comp_homologyMap {X : C} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) (Y : C) :
    (Q.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n =
      (P.isoExt n Y).hom := by
  have h := isoLeftDerivedObj_hom_naturality (𝟙 X) P Q φ
    (comm.trans (Category.comp_id _).symm) ((linearYoneda R C).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hP := congrArg Quiver.Hom.unop ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2 h.symm))
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex _).map φ) n
  -- `isoExt` is by definition the inverse of `isoLeftDerivedObj`, unopposed, followed by the
  -- inverse of `homologyUnop`; its two constituents are what the two naturality squares govern.
  have e : (Q.isoExt n Y).hom =
      (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyUnop _ n).inv := rfl
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hP)))

end CategoryTheory.ProjectiveResolution
