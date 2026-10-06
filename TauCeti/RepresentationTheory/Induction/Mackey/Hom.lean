/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Decomposition
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Rep.DirectSum

/-!
# The Mackey decomposition of intertwining spaces

The representation-level Mackey decomposition and the two induction–restriction adjunctions
identify the intertwining space between two induced representations with a product of
intertwining spaces over the double-coset intersections. This holds over a commutative ring,
without semisimplicity or a restriction on the characteristic. For finite-dimensional
representations over a field it gives an equality of natural-number dimensions, rather than
an equality of their casts into the field.

The direction of Hom matters: `Hom(Ind A, Ind B)` corresponds to `Hom(Res A, Res ({}^s B))`
over `H ∩ sKs⁻¹`. In modular characteristic reversing both Hom spaces requires additional
hypotheses, whereas the equivalence here does not.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.3–7.4.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I, §10.
-/

public section

open CategoryTheory
open TauCeti

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {H K : Subgroup G}

/-- The intertwining space between induced representations decomposes over double cosets,
without any semisimplicity assumption. -/
noncomputable def indHomMackeyLinearEquiv (A : Rep.{u} k H) (B : Rep.{u} k K) :
    (Rep.ind H.subtype A ⟶ Rep.ind K.subtype B) ≃ₗ[k]
      (∀ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        Rep.res ((mackeySubgroup D.out K H).subgroupOf H).subtype A ⟶
          Rep.res (mackeyToH D.out K H) B) := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  -- In each Mackey summand, the finite-index biadjunction moves induction out of the target.
  let e (s : G) :
      (A ⟶ Rep.mackeySummand K H s B) ≃ₗ[k]
        (Rep.res ((mackeySubgroup s K H).subgroupOf H).subtype A ⟶
          Rep.res (mackeyToH s K H) B) :=
    (Linear.homCongr k (Iso.refl A) (Rep.indCoindIso.{u, u, u}
      (Rep.res (mackeyToH s K H) B))).trans
        (Rep.resCoindHomEquiv.{u, u, u, u}
          ((mackeySubgroup s K H).subgroupOf H).subtype A
          (Rep.res (mackeyToH s K H) B)).symm
  -- First move induction out of the source, then split the restricted target over double cosets.
  let f := Rep.indResHomEquiv.{u, u, u, u} H.subtype A (Rep.ind K.subtype B)
  let g := Linear.homCongr k (Iso.refl A) (Rep.mackeyDecomposition (K := H) B)
  let h := Rep.homDirectSumLinearEquiv A
    (fun D : DoubleCoset.Quotient (H : Set G) (K : Set G) ↦ Rep.mackeySummand K H D.out B)
  exact f.trans (g.trans (h.trans (LinearEquiv.piCongrRight fun D ↦ e D.out)))

open scoped Classical in
/-- A double-coset component is obtained by Frobenius reciprocity, the Mackey decomposition,
projection onto that summand, and the finite-index induction–coinduction adjunction. -/
@[simp]
theorem indHomMackeyLinearEquiv_apply (A : Rep.{u} k H) (B : Rep.{u} k K)
    (φ : Rep.ind H.subtype A ⟶ Rep.ind K.subtype B)
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A B φ D =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      (Rep.resCoindHomEquiv ((mackeySubgroup D.out K H).subgroupOf H).subtype A
        (Rep.res (mackeyToH D.out K H) B)).symm
          ((Rep.homDirectSumLinearEquiv A
            (fun E : DoubleCoset.Quotient (H : Set G) (K : Set G) ↦
              Rep.mackeySummand K H E.out B)
            ((Rep.indResHomEquiv H.subtype A (Rep.ind K.subtype B) φ) ≫
              (Rep.mackeyDecomposition (K := H) B).hom) D) ≫
            (Rep.indCoindIso (Rep.res (mackeyToH D.out K H) B)).hom) := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  simp only [indHomMackeyLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]

end Rep

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] {H K : Subgroup G}

/-- The finite-dimensional Mackey decomposition of intertwining spaces, over every field. -/
noncomputable def indHomMackeyLinearEquiv (A : FDRep k H) (B : FDRep k K) :
    (indFDRep A ⟶ indFDRep B) ≃ₗ[k]
      (∀ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B) :=
  (FDRep.forget₂HomLinearEquiv (indFDRep A) (indFDRep B)).symm.trans <|
    (Linear.homCongr k (indFDRepForgetIso A) (indFDRepForgetIso B)).trans <|
    (Rep.indHomMackeyLinearEquiv
      ((forget₂ (FDRep k H) (Rep k H)).obj A)
      ((forget₂ (FDRep k K) (Rep k K)).obj B)).trans <|
    LinearEquiv.piCongrRight fun D ↦ FDRep.forget₂HomLinearEquiv
      (resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A)
      ((Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B)

/-- Each finite-dimensional component is the corresponding `Rep` component, transported
through the forgetful Hom equivalence and the induced-model comparison isomorphisms. -/
@[simp]
theorem indHomMackeyLinearEquiv_apply (A : FDRep k H) (B : FDRep k K)
    (φ : indFDRep A ⟶ indFDRep B)
    (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    indHomMackeyLinearEquiv A B φ D =
      FDRep.forget₂HomLinearEquiv
        (resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A)
        ((Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B)
        (Rep.indHomMackeyLinearEquiv
          ((forget₂ (FDRep k H) (Rep k H)).obj A)
          ((forget₂ (FDRep k K) (Rep k K)).obj B)
          ((indFDRepForgetIso A).inv ≫
            (FDRep.forget₂HomLinearEquiv (indFDRep A) (indFDRep B)).symm φ ≫
            (indFDRepForgetIso B).hom) D) := by
  simp only [indHomMackeyLinearEquiv, LinearEquiv.trans_apply,
    Linear.homCongr_apply, Category.assoc]
  exact LinearEquiv.piCongrRight_apply _ _ D

end FDRep
