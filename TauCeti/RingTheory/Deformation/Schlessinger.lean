/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Deformation.Lift.Pullback
public import TauCeti.RingTheory.Deformation.PredeformationFunctor

/-!
# Gluing lifts and strict classes over Artinian coefficient rings

Lifts in a fixed basis glue uniquely over a fibre product of coefficient rings. For strict
classes, one first changes basis on the surjective leg to make the lifts agree over the common
quotient. This gives Schlessinger's condition (H1). Over the residue field the strict kernel is
trivial, so the two conjugating matrices also glue, giving (H2). More generally, the comparison
is injective whenever strict stabilizers lift along the surjective leg.

The gluing results are supplied by `TauCeti.RingTheory.Deformation.Lift.Pullback`. For the
application to deformation functors, see B. Mazur, *Deforming Galois representations*,
MSRI Publ. 16 (1989), §§1.1–1.2.
-/

public section

open CategoryTheory Limits Matrix

namespace TauCeti.Deformation

variable {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Monoid G] [TopologicalSpace G]
  {ρbar : G →* GL n k}

open ArtinLocalAlg

variable (Λ ρbar)

/-- The framed lifting functor, equipped with its unique residue-field point. -/
def liftPredeformationFunctor (hρ : IsLocallyConstant ρbar) : PredeformationFunctor Λ k :=
  ⟨liftFunctor Λ ρbar, (inferInstance : Subsingleton (Lift ρbar (residue Λ k))),
    Lift.nonempty_residue_iff.mpr hρ⟩

/-- The functor of strict classes, equipped with its unique residue-field point. -/
def strictClassPredeformationFunctor (hρ : IsLocallyConstant ρbar) : PredeformationFunctor Λ k :=
  ⟨strictClassFunctor Λ ρbar, (inferInstance : Subsingleton (StrictClass ρbar (residue Λ k))),
    (Lift.nonempty_residue_iff.mpr hρ).map StrictClass.mk⟩

variable {Λ ρbar}

@[simp]
theorem liftPredeformationFunctor_obj (hρ : IsLocallyConstant ρbar) :
    (liftPredeformationFunctor Λ ρbar hρ).obj = liftFunctor Λ ρbar :=
  (rfl)

@[simp]
theorem strictClassPredeformationFunctor_obj (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).obj = strictClassFunctor Λ ρbar :=
  (rfl)

/-- Framed lifts satisfy the Rim–Schlessinger condition. -/
instance (hρ : IsLocallyConstant ρbar) :
    (liftPredeformationFunctor Λ ρbar hρ).IsDeformationFunctor where
  bijective_fiberProductMap := by
    intro A₁ A₂ B f g hg
    rw [Function.bijective_iff_existsUnique]
    simp_rw [PredeformationFunctor.fiberProductMap_eq_iff]
    rw [liftPredeformationFunctor_obj]
    intro w
    have hw : Lift.map f w.val.1 = Lift.map g w.val.2 :=
      (liftFunctor_map_apply Λ ρbar f w.val.1).symm.trans
        (w.property.trans (liftFunctor_map_apply Λ ρbar g w.val.2))
    refine (existsUnique_congr fun z ↦ ?_).mpr (Lift.existsUnique_map_pullback f g hg hw)
    constructor
    · intro hz
      exact ⟨(liftFunctor_map_apply Λ ρbar _ z).symm.trans hz.1,
        (liftFunctor_map_apply Λ ρbar _ z).symm.trans hz.2⟩
    · intro hz
      exact ⟨(liftFunctor_map_apply Λ ρbar _ z).trans hz.1,
        (liftFunctor_map_apply Λ ρbar _ z).trans hz.2⟩

/-- The comparison map for strict classes is surjective over any coefficient fibre product
with a surjective leg. -/
theorem strictClassPredeformationFunctor_surjective_fiberProductMap (hρ : IsLocallyConstant ρbar)
    {A₁ A₂ B : ArtinLocalAlg Λ k} (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    (hg : Function.Surjective g.hom.left.hom) :
    Function.Surjective ((strictClassPredeformationFunctor Λ ρbar hρ).fiberProductMap f g hg) := by
  unfold Function.Surjective
  simp_rw [PredeformationFunctor.fiberProductMap_eq_iff]
  rw [strictClassPredeformationFunctor_obj]
  intro w
  have hw : StrictClass.map f w.val.1 = StrictClass.map g w.val.2 :=
    (strictClassFunctor_map_apply Λ ρbar f w.val.1).symm.trans
      (w.property.trans (strictClassFunctor_map_apply Λ ρbar g w.val.2))
  obtain ⟨z, hz₁, hz₂⟩ := StrictClass.exists_map_pullback f g hg hw
  exact ⟨z, (strictClassFunctor_map_apply Λ ρbar _ z).trans hz₁,
    (strictClassFunctor_map_apply Λ ρbar _ z).trans hz₂⟩

/-- Strict classes of lifts satisfy Schlessinger's condition (H1). -/
instance (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).SatisfiesH1 where
  surjective_fiberProductMap := fun _ _ _ f g hg ↦
    strictClassPredeformationFunctor_surjective_fiberProductMap hρ f g hg.surjective

/-- Strict classes glue uniquely over the residue field for any two coefficient algebras. -/
theorem strictClassPredeformationFunctor_bijective_fiberProductMap_toResidue
    (hρ : IsLocallyConstant ρbar) (A₁ A₂ : ArtinLocalAlg Λ k) :
    Function.Bijective ((strictClassPredeformationFunctor Λ ρbar hρ).fiberProductMap
      (toResidue A₁) (toResidue A₂) (toResidue_surjective _)) := by
  refine ⟨?_, strictClassPredeformationFunctor_surjective_fiberProductMap hρ
    (toResidue A₁) (toResidue A₂) (toResidue_surjective _)⟩
  unfold Function.Injective
  simp_rw [PredeformationFunctor.fiberProductMap_eq_iff,
    PredeformationFunctor.fiberProductMap_fst, PredeformationFunctor.fiberProductMap_snd]
  rw [strictClassPredeformationFunctor_obj]
  intro x y hxy
  exact StrictClass.eq_of_stabilizers_lift_of_map_pullback_eq _ _ _
    (fun _ a _ ↦ ⟨1, Subsingleton.elim _ a, one_smul _ _⟩)
    ((strictClassFunctor_map_apply Λ ρbar _ x).symm.trans
      (hxy.1.trans (strictClassFunctor_map_apply Λ ρbar _ y)))
    ((strictClassFunctor_map_apply Λ ρbar _ x).symm.trans
      (hxy.2.trans (strictClassFunctor_map_apply Λ ρbar _ y)))

/-- Strict classes of lifts satisfy Schlessinger's condition (H2). -/
instance (hρ : IsLocallyConstant ρbar) :
    (strictClassPredeformationFunctor Λ ρbar hρ).SatisfiesH2 where
  bijective_fiberProductMap A :=
    strictClassPredeformationFunctor_bijective_fiberProductMap_toResidue hρ A (dualNumbers Λ k)

end TauCeti.Deformation
