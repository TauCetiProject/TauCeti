/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Homotopy invariance of the linear Hom complex

Let `C` be an `R`-linear preadditive category. Pre- and postcomposition by homotopic cochain
maps induce homotopic maps of `R`-linear Hom complexes `CochainComplex.linearHomComplex R F G`.
If `h` is a homotopy from `ψ` to `ψ'`, viewed as a degree `-1` cochain with `δ h = ψ - ψ'`, then
`z ↦ z ∘ h` is a homotopy from postcomposition by `ψ` to postcomposition by `ψ'`. Dually, if `h`
is a homotopy from `φ` to `φ'`, then `z ↦ (-1)ᵖ h ∘ z` on cochains of degree `p` is a homotopy
from precomposition by `φ` to precomposition by `φ'`.

Hence the linear Hom complex descends to a bifunctor
`TauCeti.linearHomComplexHomotopyFunctor R C : K(C)ᵒᵖ ⥤ K(C) ⥤ K(R)` on homotopy categories,
contravariant in the source and covariant in the target. Composed with a K-injective
replacement in the target, this bifunctor computes derived `Hom` complexes.

## Main definitions

* `TauCeti.linearHomComplexPrecompHomotopy` and `TauCeti.linearHomComplexPostcompHomotopy`:
  the homotopies induced by a homotopy in the source or in the target.
* `TauCeti.linearHomComplexHomotopyFunctor`: the linear Hom complex on homotopy categories.

## References

* B. Keller, *Deriving DG categories*, Section 2.2.
-/

public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

section Homotopy

variable {F₁ F₂ G₁ G₂ : CochainComplex C ℤ}

/-- Postcomposition by a degree `-1` cochain, as a degree `-1` cochain between linear Hom
complexes. -/
private def postcompCochain (F : CochainComplex C ℤ) (h : Cochain G₁ G₂ (-1)) :
    Cochain (linearHomComplex R F G₁) (linearHomComplex R F G₂) (-1) :=
  Cochain.mk fun p _ hpq ↦ ModuleCat.ofHom
    { toFun z := (z : Cochain F G₁ p).comp h hpq
      map_add' z z' := Cochain.add_comp z z' h hpq
      map_smul' r z := Cochain.smul_comp r z h hpq }

/-- Precomposition by a degree `-1` cochain, with the sign `(-1)ᵖ` on cochains of degree `p`, as
a degree `-1` cochain between linear Hom complexes. -/
private def precompCochain (h : Cochain F₁ F₂ (-1)) (G : CochainComplex C ℤ) :
    Cochain (linearHomComplex R F₂ G) (linearHomComplex R F₁ G) (-1) :=
  Cochain.mk fun p q hpq ↦ ModuleCat.ofHom
    { toFun z := p.negOnePow • h.comp (z : Cochain F₂ G p) (by omega)
      map_add' z z' := by rw [Cochain.comp_add, smul_add]
      map_smul' r z := by
        rw [Cochain.comp_smul, RingHom.id_apply, smul_comm] }

/-- A homotopy between `ψ` and `ψ'` induces a homotopy between postcomposition by `ψ` and
postcomposition by `ψ'` on linear Hom complexes. -/
def linearHomComplexPostcompHomotopy (F : CochainComplex C ℤ) {ψ ψ' : G₁ ⟶ G₂}
    (h : Homotopy ψ ψ') :
    Homotopy (linearHomComplexPostcomp R F ψ) (linearHomComplexPostcomp R F ψ') :=
  (Cochain.equivHomotopy _ _).symm ⟨postcompCochain R F (Cochain.ofHomotopy h), by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    rw [Cochain.add_v, δ_v (-1) 0 (by omega) _ p p hpq (p - 1) (p + 1) (by omega) rfl]
    ext (z : Cochain F G₁ p)
    simp only [linearHomComplex_X, Cochain.ofHom_v, linearHomComplexPostcomp_f_apply,
      postcompCochain, Cochain.mk_v, Int.negOnePow_zero, one_smul, ModuleCat.hom_add,
      ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.add_apply, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, linearHomComplex_d_hom_apply]
    rw [δ_comp z (Cochain.ofHomotopy h) _ (p + 1) 0 p (by omega) rfl (by omega),
      δ_ofHomotopy, Cochain.comp_sub]
    simp⟩

/-- A homotopy between `φ` and `φ'` induces a homotopy between precomposition by `φ` and
precomposition by `φ'` on linear Hom complexes. -/
def linearHomComplexPrecompHomotopy {φ φ' : F₁ ⟶ F₂} (h : Homotopy φ φ')
    (G : CochainComplex C ℤ) :
    Homotopy (linearHomComplexPrecomp R φ G) (linearHomComplexPrecomp R φ' G) :=
  (Cochain.equivHomotopy _ _).symm ⟨precompCochain R (Cochain.ofHomotopy h) G, by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    rw [Cochain.add_v, δ_v (-1) 0 (by omega) _ p p hpq (p - 1) (p + 1) (by omega) rfl]
    ext (z : Cochain F₂ G p)
    simp only [linearHomComplex_X, Cochain.ofHom_v, linearHomComplexPrecomp_f_apply,
      precompCochain, Cochain.mk_v, Int.negOnePow_zero, one_smul, ModuleCat.hom_add,
      ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.add_apply, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_zsmul_unit,
      linearHomComplex_d_hom_apply]
    rw [δ_comp (Cochain.ofHomotopy h) z _ 0 (p + 1) p (by omega) (by omega) rfl, δ_ofHomotopy,
      Cochain.sub_comp, Int.negOnePow_succ, smul_add, smul_smul, Int.units_mul_self]
    simp⟩

end Homotopy

variable (C) in
/-- The `R`-linear Hom complex as a bifunctor on homotopy categories, contravariant in the source
and covariant in the target. On the images of complexes `F` and `G` it is the image of
`CochainComplex.linearHomComplex R F G`. -/
-- Expose the object assignment so that the values on images of complexes have computed types.
@[expose]
def linearHomComplexHomotopyFunctor :
    (HomotopyCategory C (.up ℤ))ᵒᵖ ⥤ HomotopyCategory C (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{v} R) (.up ℤ) :=
  Functor.leftOp <| CategoryTheory.Quotient.lift _
    { obj F := .op <| CategoryTheory.Quotient.lift _
        ((linearHomComplexFunctor R).obj (.op F) ⋙ HomotopyCategory.quotient _ _)
        (fun _ _ _ _ ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _
          (linearHomComplexPostcompHomotopy R F h))
      map φ := .op <| CategoryTheory.Quotient.natTransLift _
        (Functor.whiskerRight ((linearHomComplexFunctor R).map φ.op)
          (HomotopyCategory.quotient _ _))
      -- After `simp`, both sides agree up to `Quotient.lift_obj_functor_obj`, which is `rfl`.
      map_id F := by
        apply Quiver.Hom.unop_inj
        apply CategoryTheory.Quotient.natTrans_ext
        ext G
        simp
        rfl
      map_comp φ φ' := by
        apply Quiver.Hom.unop_inj
        apply CategoryTheory.Quotient.natTrans_ext
        ext G
        simp
        rfl }
    (fun _ _ _ _ ⟨h⟩ ↦ by
      apply Quiver.Hom.unop_inj
      apply CategoryTheory.Quotient.natTrans_ext
      ext G
      exact HomotopyCategory.eq_of_homotopy _ _ (linearHomComplexPrecompHomotopy R h G))

@[simp]
lemma linearHomComplexHomotopyFunctor_obj_obj (F G : CochainComplex C ℤ) :
    ((linearHomComplexHomotopyFunctor R C).obj
        (.op ((HomotopyCategory.quotient C _).obj F))).obj
          ((HomotopyCategory.quotient C _).obj G) =
      (HomotopyCategory.quotient _ _).obj (linearHomComplex R F G) :=
  (rfl)

@[simp]
lemma linearHomComplexHomotopyFunctor_obj_map (F : CochainComplex C ℤ) {G₁ G₂ : CochainComplex C ℤ}
    (ψ : G₁ ⟶ G₂) :
    ((linearHomComplexHomotopyFunctor R C).obj
        (.op ((HomotopyCategory.quotient C _).obj F))).map
          ((HomotopyCategory.quotient C _).map ψ) =
      (HomotopyCategory.quotient _ _).map (linearHomComplexPostcomp R F ψ) :=
  (rfl)

@[simp]
lemma linearHomComplexHomotopyFunctor_map_app {F₁ F₂ : CochainComplex C ℤ} (φ : F₁ ⟶ F₂)
    (G : CochainComplex C ℤ) :
    ((linearHomComplexHomotopyFunctor R C).map ((HomotopyCategory.quotient C _).map φ).op).app
        ((HomotopyCategory.quotient C _).obj G) =
      (HomotopyCategory.quotient _ _).map (linearHomComplexPrecomp R φ G) :=
  (rfl)

end TauCeti
