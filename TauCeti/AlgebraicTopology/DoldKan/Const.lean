/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.Monoidal

/-!
# Constant simplicial objects and degree-zero complexes under Dold–Kan

In an idempotent-complete preadditive category `C` with finite coproducts and a zero object, the
pseudoabelian Dold–Kan correspondence identifies constant simplicial objects
`(SimplicialObject.const C).obj X` with degree-zero complexes `(ChainComplex.single₀ C).obj X`.

## Main definitions and results

* `isZero_N_const_obj_X_succ`: in positive degrees, the normalized chains of a constant simplicial
  object vanish.
* `N.constIso`: `SimplicialObject.const C ⋙ N ≅ ChainComplex.single₀ C`.
* `Γ.single₀Iso`: `ChainComplex.single₀ C ⋙ Γ ≅ SimplicialObject.const C`.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §3.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994), §8.4.
-/

public noncomputable section

universe v u

open CategoryTheory Limits AlgebraicTopology.DoldKan

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

omit [HasZeroObject C] in
/-- In positive degree `m + 1`, the normalized chain complex of a constant simplicial object is
zero, because every simplex is in the image of `σ 0 = 𝟙 X`. -/
lemma isZero_N_const_obj_X_succ (X : C) (m : ℕ) :
    IsZero ((N.obj ((SimplicialObject.const C).obj X)).X (m + 1)) := by
  have hP : (PInfty (X := (SimplicialObject.const C).obj X)).f (m + 1) = 0 := by
    have hσ := σ_comp_PInfty ((SimplicialObject.const C).obj X) (0 : Fin (m + 1))
    dsimp [SimplicialObject.σ] at hσ
    rwa [Category.id_comp] at hσ
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.id_f,
    ← inclusionN_app_comp_PInftyToN_app ((SimplicialObject.const C).obj X),
    HomologicalComplex.comp_f, ← inclusionN_app_comp_PInfty ((SimplicialObject.const C).obj X),
    HomologicalComplex.comp_f, hP, comp_zero, zero_comp]

private def N.constIsoApp (X : C) :
    N.obj ((SimplicialObject.const C).obj X) ≅ (ChainComplex.single₀ C).obj X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 =>
        { hom := (inclusionN.app ((SimplicialObject.const C).obj X)).f 0
          inv := (PInftyToN.app ((SimplicialObject.const C).obj X)).f 0
          hom_inv_id := by
            rw [← HomologicalComplex.comp_f, inclusionN_app_comp_PInftyToN_app,
              HomologicalComplex.id_f]
          inv_hom_id := by
            rw [← HomologicalComplex.comp_f, PInftyToN_app_comp_inclusionN_app, PInfty_f_0]; rfl }
          ≪≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).symm
      | m + 1 =>
        (isZero_N_const_obj_X_succ X m).iso
          (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 X (m + 1) (by omega)))
    (fun i j hij ↦ by
      dsimp [ComplexShape.down] at hij
      obtain rfl := hij.symm
      exact (isZero_N_const_obj_X_succ X j).eq_of_src _ _)

/-- The normalized chain complex functor `N` sends constant simplicial objects to degree-zero
complexes, naturally in the object `X : C`. -/
def N.constIso : SimplicialObject.const C ⋙ N ≅ ChainComplex.single₀ C :=
  NatIso.ofComponents N.constIsoApp fun {X Y} f ↦ by
    ext
    simp only [Functor.comp_map, HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero,
      N.constIsoApp, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.trans_hom,
      ChainComplex.single₀ObjXSelf]
    have hnat := congrArg (fun φ : N.obj ((SimplicialObject.const C).obj X) ⟶
        (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj Y) ↦
          φ.f 0)
      (inclusionN.naturality ((SimplicialObject.const C).map f))
    simp only [HomologicalComplex.comp_f,
      AlgebraicTopology.alternatingFaceMapComplex_map_f] at hnat
    simpa using hnat

/-- In degree `0`, the forward map of `N.constIso` at `X` is the inclusion of normalized chains. -/
@[simp]
lemma N.constIso_hom_app_f_zero (X : C) :
    (N.constIso.hom.app X).f 0 = (inclusionN.app ((SimplicialObject.const C).obj X)).f 0 := by
  simp [N.constIso, N.constIsoApp]

/-- In degree `0`, the inverse map of `N.constIso` at `X` is the projection onto normalized
chains. -/
@[simp]
lemma N.constIso_inv_app_f_zero (X : C) :
    (N.constIso.inv.app X).f 0 = (PInftyToN.app ((SimplicialObject.const C).obj X)).f 0 := by
  simp [N.constIso, N.constIsoApp]

/-- Under the inverse Dold–Kan functor `Γ`, degree-zero chain complexes
`(ChainComplex.single₀ C).obj X` correspond naturally to constant simplicial objects
`(SimplicialObject.const C).obj X`. -/
def Γ.single₀Iso : ChainComplex.single₀ C ⋙ Γ ≅ SimplicialObject.const C :=
  NatIso.ofComponents
    (fun X ↦ Γ.mapIso (N.constIso.symm.app X) ≪≫
      (ε (C := C)).symm.app ((SimplicialObject.const C).obj X))
    (fun {X Y} f ↦ by
      dsimp
      rw [← Category.assoc, ← Γ.map_comp, N.constIso.inv.naturality f, Γ.map_comp, Category.assoc]
      simpa [Category.assoc] using
        whisker_eq (Γ.map (N.constIso.inv.app X))
          ((ε (C := C)).inv.naturality ((SimplicialObject.const C).map f)))

end CategoryTheory.Idempotents.DoldKan
