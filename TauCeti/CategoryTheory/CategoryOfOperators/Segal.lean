/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CategoryOfOperators.Nerve
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.NatTrans

/-!
# Inert projections of the symmetric operator nerve

The inert projection at a coordinate of a family has a strongly coCartesian lift to the
singleton family with that member. These lifts form a natural transformation from the
inclusion of families to singleton-coordinate inclusion. Its nerve gives the cylinder
over the inert projection, and its upper endpoint is coordinate evaluation.

The upper endpoints together give an isomorphism to the product of singleton fibers.
These cylinders supply the projection data used in the Segal condition for the monoidal nerve.

## References

* J. Lurie, *Higher Algebra*, Construction 2.0.0.1.
-/

public section

universe w v u

open CategoryTheory Limits MonoidalCategory Simplicial SSet

namespace TauCeti.CategoryOfOperators

variable (C : Type u) [Category.{v} C]

variable [MonoidalCategory C] [SymmetricCategory C]

/-! ## Cylinders on the strict simplicial fibers -/

/-- The upper endpoint on the fiber, sending a family to its singleton coordinate. -/
noncomputable def nerveFiberProjection (b : FinPointed.{max u v}) (i : Fin b.len) :
    (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet) ⟶
      (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm (FinPointed.mk 1)) : SSet) :=
  (nerveFiberIso C b).inv ≫ nerveMap (singletonCoordinate C b i) ≫
    (nerveFiberIso C (FinPointed.mk 1)).hom

/-- The upper endpoint becomes coordinate evaluation under the singleton-fiber comparison. -/
@[reassoc (attr := simp)]
lemma nerveFiberProjection_comp_nerveFiberEval
    (b : FinPointed.{max u v}) (i : Fin b.len) :
    nerveFiberProjection C b i ≫ nerveFiberEval C (FinPointed.mk 1) 0 =
      nerveFiberEval C b i := by
  simp only [nerveFiberProjection, Category.assoc, nerveFiberEval_eq, Iso.hom_inv_id_assoc]
  ext n s
  rfl

/-- Combining the projection endpoints recovers the product comparison of the strict fiber. -/
lemma pi_lift_nerveFiberProjection (b : FinPointed.{max u v}) :
    Pi.lift (fun i ↦ nerveFiberProjection C b i ≫ (nerveFiberOneIso C).hom) =
      (nerveFiberPiIso C b).hom := by
  simp only [nerveFiberOneIso_hom]
  apply Pi.hom_ext
  intro i
  exact (Pi.lift_comp_π _ i).trans
    ((nerveFiberProjection_comp_nerveFiberEval C b i).trans
      (nerveFiberPiIso_hom_π C b i).symm)

/-- The upper endpoints together give a strict Segal isomorphism to the product of
singleton fibers. -/
instance isIso_pi_lift_nerveFiberProjection (b : FinPointed.{max u v}) :
    IsIso (Pi.lift (fun i ↦ nerveFiberProjection C b i)) := by
  let e := Pi.mapIso (fun _ : Fin b.len ↦ nerveFiberOneIso C)
  have h : Pi.lift (fun i ↦ nerveFiberProjection C b i) ≫ e.hom =
      (nerveFiberPiIso C b).hom := by
    apply Pi.hom_ext
    intro i
    dsimp only [e]
    rw [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
    simpa only [nerveFiberOneIso_hom] using
      (nerveFiberProjection_comp_nerveFiberEval C b i).trans
        (nerveFiberPiIso_hom_π C b i).symm
  have : IsIso (Pi.lift (fun i ↦ nerveFiberProjection C b i) ≫ e.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

private noncomputable def fiberInertProjection (b : FinPointed.{max u v}) (i : Fin b.len) :
    (toFiber C b).strictInv ⋙ ι C b ⟶
      (toFiber C b).strictInv ⋙ singletonCoordinate C b i ⋙ ι C (FinPointed.mk 1) :=
  Functor.whiskerLeft (toFiber C b).strictInv (inertProjection C b i)

/-- The cylinder of the inert projection, obtained by taking the nerve of its natural
transformation on the ordinary strict fiber. -/
noncomputable def nerveFiberProjectionCylinder (b : FinPointed.{max u v}) (i : Fin b.len) :
    (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet) ⊗ Δ[1] ⟶
      nerve (CategoryOfOperators.{max u v} C) :=
  (((fiberInertProjection C b i).nerveHomotopy).precomp
    (nerve.fiberIso (toFinPointed C) b).inv).h

/-- The cylinder starts at the strict fiber inclusion. -/
@[reassoc (attr := simp)]
lemma ι₀_nerveFiberProjectionCylinder (b : FinPointed.{max u v}) (i : Fin b.len) :
    ι₀ ≫ nerveFiberProjectionCylinder C b i =
      (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b)).ι := by
  calc
    _ = (nerve.fiberIso (toFinPointed C) b).inv ≫
        nerveMap ((toFiber C b).strictInv ⋙ ι C b) :=
      (((fiberInertProjection C b i).nerveHomotopy).precomp
        (nerve.fiberIso (toFinPointed C) b).inv).h₀
    _ = _ := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro s
      exact (Functor.assoc _ _ _).symm.trans
        ((congrArg (· ⋙ ι C b) (nerveFiberIso_inv_app C b n s).symm).trans
          (nerveFiberIso_inv_app_comp C b n s))

/-- The cylinder ends at singleton-coordinate inclusion. -/
@[reassoc (attr := simp)]
lemma ι₁_nerveFiberProjectionCylinder (b : FinPointed.{max u v}) (i : Fin b.len) :
    ι₁ ≫ nerveFiberProjectionCylinder C b i = nerveFiberProjection C b i ≫
      (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm (FinPointed.mk 1))).ι := by
  calc
    _ = (nerve.fiberIso (toFinPointed C) b).inv ≫
        nerveMap ((toFiber C b).strictInv ⋙ singletonCoordinate C b i ⋙
          ι C (FinPointed.mk 1)) :=
      (((fiberInertProjection C b i).nerveHomotopy).precomp
        (nerve.fiberIso (toFinPointed C) b).inv).h₁
    _ = _ := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro s
      exact (Functor.assoc _ _ _).symm.trans
        ((congrArg (· ⋙ singletonCoordinate C b i ⋙ ι C (FinPointed.mk 1))
          (nerveFiberIso_inv_app C b n s).symm).trans
          ((Functor.assoc _ _ _).symm.trans
            (nerveFiberIso_hom_app_coe C (FinPointed.mk 1) n _).symm))

private lemma uncurry_fiberInertProjection_comp (b : FinPointed.{max u v})
    (i : Fin b.len) :
    Functor.uncurry.obj (ComposableArrows.mk₁ (fiberInertProjection C b i)) ⋙
      toFinPointed C =
      CategoryTheory.Prod.fst _ _ ⋙ ComposableArrows.mk₁ (FinPointed.ρ i) := by
  refine CategoryTheory.Functor.ext (fun ⟨a, X⟩ ↦ ?_) (fun ⟨a, X⟩ ⟨a', Y⟩ ⟨f, g⟩ ↦ ?_)
  · fin_cases a <;> rfl
  · have h := leOfHom f
    fin_cases a <;> fin_cases a' <;> dsimp at h <;> try omega
    all_goals simp [Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.Mk₁.map,
      fiberInertProjection, Functor.whiskerLeft, inertProjection_app, toFinPointed]

/-- The projection cylinder lies over the edge given by the inert projection. -/
@[reassoc (attr := simp)]
lemma nerveFiberProjectionCylinder_comp (b : FinPointed.{max u v}) (i : Fin b.len) :
    nerveFiberProjectionCylinder C b i ≫ nerveMap (toFinPointed C) =
      CartesianMonoidalCategory.snd _ _ ≫
        yonedaEquiv.symm (nerve.edgeMk (FinPointed.ρ i)).edge := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  simp only [nerveFiberProjectionCylinder, Homotopy.precomp_h, NatTrans.comp_app,
    types_comp_apply, nerveMap_app]
  rw [NatTrans.nerveHomotopy_h_app]
  -- Express both nerves as strings so that the ordinary base equation applies.
  change ((stdSimplex.asOrderHom x.2).monotone.functor.prod'
    ((nerve.fiberIso (toFinPointed C) b).inv.app n x.1) ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ (fiberInertProjection C b i))) ⋙
        toFinPointed C =
      (stdSimplex.asOrderHom x.2).monotone.functor ⋙ ComposableArrows.mk₁ (FinPointed.ρ i)
  rw [Functor.assoc, uncurry_fiberInertProjection_comp]
  rfl

/-- Each vertical edge of the projection cylinder is the nerve of the ordinary
strongly coCartesian singleton projection lift. -/
lemma nerveFiberProjectionCylinder_app_verticalEdge (b : FinPointed.{max u v})
    (i : Fin b.len) (x : (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet) _⦋0⦌) :
    (nerveFiberProjectionCylinder C b i).app _ (verticalEdge x) =
      (nerve.edgeMk (toSingleton C b i ((toFiber C b).strictInv.obj
        (nerveEquiv ((nerve.fiberIso (toFinPointed C) b).inv.app _ x))))).edge := by
  simp only [nerveFiberProjectionCylinder, Homotopy.precomp_h, NatTrans.comp_app,
    types_comp_apply, whiskerRight_app_verticalEdge]
  conv_lhs =>
    rw [← nerveEquiv.symm_apply_apply ((nerve.fiberIso (toFinPointed C) b).inv.app _ x)]
  simpa only [fiberInertProjection, Functor.whiskerLeft_app, inertProjection_app] using
    NatTrans.nerveHomotopy_h_app_verticalEdge (fiberInertProjection C b i)
      (nerveEquiv ((nerve.fiberIso (toFinPointed C) b).inv.app _ x))

end TauCeti.CategoryOfOperators
