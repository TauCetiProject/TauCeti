/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# The graded-split stable category is the curved homotopy category

A null-homotopic closed map factors through the cone of the identity of its source. Conversely,
every map factoring through a contractible module is zero in the homotopy category. Since the
relative projectives of the graded-split exact structure are exactly the contractible modules,
its stable ideal is the kernel of the existing closed-to-homotopy functor. The resulting
comparison is an additive linear equivalence, without introducing another homotopy category.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Frobenius`: the stable ideal and
  comparison proofs adapt the corresponding componentwise split construction.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}

/-- The projective stable ideal of the graded-split exact structure is the kernel of the
canonical functor to the curved homotopy category. -/
theorem gradedSplitExact_projectiveStableIdeal_eq_kerIdeal :
    (gradedSplitExact (h := h)).projectiveStableIdeal =
      (dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R).kerIdeal := by
  ext X Y f
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff,
    CategoryTheory.Functor.mem_kerIdeal_hom]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩
    have hP' := (gradedSplitExact_isProjective_iff (ForgetEnrichment.to _ P)).mp hP
    rw [Functor.map_comp, hP'.eq_of_src ((dgClosedToHomotopy R).map p) 0, comp_zero]
  · intro hf
    obtain ⟨g, hg⟩ := (quotient_map_eq_zero_iff_factors_coneIdentity f).mp hf
    exact ⟨_, gradedSplitExact_isProjective_of_isZero_homotopy (isZero_homotopy_cone_isIso _),
      _, g, hg.symm⟩

/-- The canonical additive comparison from the graded-split stable category to the existing
curved homotopy category. -/
noncomputable def gradedSplitStableToHomotopy :
    (gradedSplitExact (h := h)).ProjectiveStableCategory ⥤
      DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) :=
  (gradedSplitExact (h := h)).projectiveStableIdeal.lift (dgClosedToHomotopy R)
    gradedSplitExact_projectiveStableIdeal_eq_kerIdeal.le

/-- The stable comparison restricts to the canonical homotopy quotient. -/
theorem projectiveStableFunctor_comp_gradedSplitStableToHomotopy :
    (gradedSplitExact (h := h)).projectiveStableFunctor ⋙ gradedSplitStableToHomotopy =
      dgClosedToHomotopy R := by
  rw [gradedSplitStableToHomotopy, Quotient.lift_spec]

/-- The stable comparison sends a closed object's stable image to its homotopy class. -/
@[simp]
theorem gradedSplitStableToHomotopy_obj_projectiveStableFunctor_obj
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) :
    gradedSplitStableToHomotopy.obj ((gradedSplitExact (h := h)).projectiveStableFunctor.obj X) =
      (dgClosedToHomotopy R).obj X :=
  congrArg (fun F ↦ F.obj X) projectiveStableFunctor_comp_gradedSplitStableToHomotopy

/-- On the class of a closed map, the stable comparison is the canonical homotopy quotient. -/
@[simp]
theorem gradedSplitStableToHomotopy_map_projectiveStableFunctor_map
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)} (f : X ⟶ Y) :
    gradedSplitStableToHomotopy.map ((gradedSplitExact (h := h)).projectiveStableFunctor.map f) =
      eqToHom (gradedSplitStableToHomotopy_obj_projectiveStableFunctor_obj X) ≫
        (dgClosedToHomotopy R).map f ≫
          eqToHom (gradedSplitStableToHomotopy_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom projectiveStableFunctor_comp_gradedSplitStableToHomotopy f

instance : (gradedSplitStableToHomotopy (h := h)).Additive := by
  unfold gradedSplitStableToHomotopy
  infer_instance

instance : (gradedSplitStableToHomotopy (h := h)).Linear R := by
  unfold gradedSplitStableToHomotopy
  infer_instance

instance : (gradedSplitStableToHomotopy (h := h)).IsEquivalence := by
  let : (dgClosedToHomotopy (C := CurvedDGRightModuleCat.{u, u, u} h) R).EssSurj :=
    ⟨fun X ↦ ⟨ForgetEnrichment.of _ (DGHomotopyCategory.underlying R X), ⟨Iso.refl X⟩⟩⟩
  unfold gradedSplitStableToHomotopy
  exact MorphismIdeal.isEquivalence_lift _ _ _
    gradedSplitExact_projectiveStableIdeal_eq_kerIdeal.ge

/-- The linear equivalence between the graded-split stable category and the existing curved
homotopy category. -/
noncomputable def gradedSplitStableHomotopyEquivalence :
    (gradedSplitExact (h := h)).ProjectiveStableCategory ≌
      DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h) :=
  (gradedSplitStableToHomotopy (h := h)).asEquivalence

end TauCeti.CurvedDGRightModuleCat
