/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Sites
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Monoidal restriction to open subschemes

Restriction of modules from a scheme `X` to an open subscheme `U` is strong monoidal:
restriction commutes with the sheafified tensor product and preserves the structure sheaf.
Consequently exact pairings, and hence left and right duals, restrict to `U`.

The monoidal structure descends precomposition of presheaves through sheafification. For the
inclusion of an open subscheme, the coefficient map of `Scheme.Modules.restrictFunctor` is the
identity. Its comparison with pullback transports the restricted pairing to the actual
pullback objects, without choosing a new monoidal structure on pullback.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Restriction to an open subscheme preserves tensor products and the structure sheaf. -/
instance restrictFunctorMonoidal (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).Monoidal := by
  unfold Scheme.Modules.restrictFunctor
  simp only [Scheme.Opens.ι_appIso]
  exact SheafOfModules.pushforwardModuleMonoidal U.ι.opensFunctor X.sheaf

/-- Pullback to an open subscheme preserves exact pairings, by restriction of the evaluation
and coevaluation maps. -/
@[instance_reducible]
def pullbackInclusionExactPairing (U : X.Opens) (M N : X.Modules) [ExactPairing M N] :
    ExactPairing ((Scheme.Modules.pullback U.ι).obj M)
      ((Scheme.Modules.pullback U.ι).obj N) := by
  letI := (Scheme.Modules.restrictFunctor U.ι).mapExactPairing M N
  exact exactPairingCongr
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm

/-- Evaluation of the pulled-back pairing is restricted evaluation, read through the tensor,
unit and restriction--pullback comparisons. -/
@[simp]
theorem pullbackInclusionExactPairing_evaluation (U : X.Opens) (M N : X.Modules)
    [ExactPairing M N] :
    @ExactPairing.evaluation U.toScheme.Modules _ _ _ _
      (pullbackInclusionExactPairing U M N) =
      (Scheme.Modules.pullback U.ι).obj N ◁
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv ≫
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).inv ▷
          (Scheme.Modules.restrictFunctor U.ι).obj M ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor U.ι) N M ≫
        (Scheme.Modules.restrictFunctor U.ι).map (ε_ M N) ≫
        Functor.OplaxMonoidal.η (Scheme.Modules.restrictFunctor U.ι) := by
  calc
    _ = (Scheme.Modules.pullback U.ι).obj N ◁
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).inv ≫
        (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).inv ▷
          (Scheme.Modules.restrictFunctor U.ι).obj M ≫
        @ExactPairing.evaluation U.toScheme.Modules _ _ _ _
          ((Scheme.Modules.restrictFunctor U.ι).mapExactPairing M N)) := (rfl)
    _ = _ := by rw [Functor.mapExactPairing_evaluation]

/-- Coevaluation of the pulled-back pairing is restricted coevaluation through the same
canonical comparisons. -/
@[simp]
theorem pullbackInclusionExactPairing_coevaluation (U : X.Opens) (M N : X.Modules)
    [ExactPairing M N] :
    @ExactPairing.coevaluation U.toScheme.Modules _ _ _ _
      (pullbackInclusionExactPairing U M N) =
      Functor.LaxMonoidal.ε (Scheme.Modules.restrictFunctor U.ι) ≫
        (Scheme.Modules.restrictFunctor U.ι).map (η_ M N) ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor U.ι) M N ≫
        (Scheme.Modules.restrictFunctor U.ι).obj M ◁
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).hom ≫
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom ▷
          (Scheme.Modules.pullback U.ι).obj N := by
  calc
    _ = (@ExactPairing.coevaluation U.toScheme.Modules _ _ _ _
          ((Scheme.Modules.restrictFunctor U.ι).mapExactPairing M N) ≫
        (Scheme.Modules.restrictFunctor U.ι).obj M ◁
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).hom) ≫
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom ▷
          (Scheme.Modules.pullback U.ι).obj N := (rfl)
    _ = _ := by rw [Functor.mapExactPairing_coevaluation]; simp only [Category.assoc]

/-- A module with a left dual still has a left dual after pullback to an open subscheme. -/
theorem nonempty_hasLeftDual_pullback_inclusion (U : X.Opens) (M : X.Modules)
    (hM : Nonempty (HasLeftDual M)) :
    Nonempty (HasLeftDual ((Scheme.Modules.pullback U.ι).obj M)) := by
  obtain ⟨hM⟩ := hM
  let := pullbackInclusionExactPairing U (ᘁM) M
  exact ⟨⟨(Scheme.Modules.pullback U.ι).obj (ᘁM)⟩⟩

/-- A module with a right dual still has a right dual after pullback to an open subscheme. -/
theorem nonempty_hasRightDual_pullback_inclusion (U : X.Opens) (M : X.Modules)
    (hM : Nonempty (HasRightDual M)) :
    Nonempty (HasRightDual ((Scheme.Modules.pullback U.ι).obj M)) := by
  obtain ⟨hM⟩ := hM
  let := pullbackInclusionExactPairing U M (Mᘁ)
  exact ⟨⟨(Scheme.Modules.pullback U.ι).obj (Mᘁ)⟩⟩

namespace AlgebraicGeometry.QuasicoherentSheaf

/-- A dualizable quasicoherent sheaf remains dualizable after pullback to an open subscheme. -/
theorem nonempty_hasLeftDual_pullback_inclusion (U : X.Opens) (E : QuasicoherentSheaf X)
    (hE : Nonempty (HasLeftDual E)) :
    Nonempty (HasLeftDual ((pullback U.ι).obj E)) := by
  obtain ⟨hE⟩ := hE
  let D := ᘁE
  let : ExactPairing (C := X.Modules) D.obj E.obj :=
    @Functor.mapExactPairing (QuasicoherentSheaf X) inferInstance inferInstance X.Modules
      inferInstance (Scheme.Modules.instMonoidalCategory X) (ObjectProperty.ι _)
      (@ObjectProperty.monoidalι X.Modules _ _ _
        (Scheme.Modules.isMonoidal_isQuasicoherent X)) D E (inferInstanceAs (ExactPairing D E))
  let := pullbackInclusionExactPairing U D.obj E.obj
  let h : ExactPairing (C := U.toScheme.Modules) ((pullback U.ι).obj D).obj
      ((pullback U.ι).obj E).obj :=
    exactPairingCongr (eqToIso (pullback_obj_obj U.ι D)) (eqToIso (pullback_obj_obj U.ι E))
  let : ExactPairing ((pullback U.ι).obj D) ((pullback U.ι).obj E) :=
    @ObjectProperty.exactPairingFullSubcategory U.toScheme.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent U.toScheme) _ _ h
  exact ⟨⟨(pullback U.ι).obj D⟩⟩

end AlgebraicGeometry.QuasicoherentSheaf

end

end TauCeti
