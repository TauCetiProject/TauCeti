/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.Modules.Biprod

/-!
# Finite colimits of coherent formal modules

Coherent formal modules on any adic thickening system have finite biproducts and finite
colimits. Evaluation at each level preserves finite colimits, and the evaluations jointly
detect colimit cocones. Pullback along a morphism of systems consequently preserves finite
colimits as well.

The constructions use the finite presentation of direct sums and cokernels, and the fact that
pullback of module sheaves preserves colimits. They require no Noetherian hypothesis. This
provides the finite-colimit part of the abelian structure on coherent formal modules on a
Noetherian formal completion, whose kernels generally cannot be computed levelwise.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped ZeroObject

universe u v w

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

noncomputable section

variable {𝔛 𝔜 : AdicThickeningSystem.{u}}

/-- The module sheaf at a specified level of a coherent formal module. -/
abbrev evaluation (n : ℕ) : CoherentFormalModule 𝔛 ⥤ (𝔛.X n).Modules where
  obj M := M.obj n
  map f := f.app n

instance (n : ℕ) : (evaluation (𝔛 := 𝔛) n).Additive where
  map_add := rfl

private abbrev zeroModule : CoherentFormalModule 𝔛 where
  obj _ := 0
  isFinitePresentation n :=
    (SheafOfModules.isFinitePresentation (𝔛.X n).ringCatSheaf).prop_zero
  transitionIso n := (Functor.mapZeroObject (Scheme.Modules.pullback (𝔛.ι n)))

/-- The zero system is a zero object, independently of Noetherian hypotheses. -/
instance : HasZeroObject (CoherentFormalModule 𝔛) :=
  ⟨⟨zeroModule, (isZero_iff_forall_isZero_obj _).mpr fun _ ↦ isZero_zero _⟩⟩

private abbrev biprodModule (M N : CoherentFormalModule 𝔛) : CoherentFormalModule 𝔛 where
  obj n := M.obj n ⊞ N.obj n
  isFinitePresentation n := inferInstance
  transitionIso n := by
    let G := Scheme.Modules.pullback (𝔛.ι n)
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts G
    exact G.mapBiprod _ _ ≪≫ biprod.mapIso (M.transitionIso n) (N.transitionIso n)

private def biprodFst (M N : CoherentFormalModule 𝔛) : biprodModule M N ⟶ M where
  app n := biprod.fst
  naturality n := by
    simp [biprodModule]

private def biprodSnd (M N : CoherentFormalModule 𝔛) : biprodModule M N ⟶ N where
  app n := biprod.snd
  naturality n := by
    simp [biprodModule]

private def biprodInl (M N : CoherentFormalModule 𝔛) : M ⟶ biprodModule M N where
  app n := biprod.inl
  naturality n := by
    simp [biprodModule]

private def biprodInr (M N : CoherentFormalModule 𝔛) : N ⟶ biprodModule M N where
  app n := biprod.inr
  naturality n := by
    simp [biprodModule]

private def biprodBicone (M N : CoherentFormalModule 𝔛) : BinaryBicone M N where
  pt := biprodModule M N
  fst := biprodFst M N
  snd := biprodSnd M N
  inl := biprodInl M N
  inr := biprodInr M N
  inl_fst := by apply hom_ext; intro n; simp [biprodInl, biprodFst]
  inl_snd := by apply hom_ext; intro n; simp [biprodInl, biprodSnd]
  inr_fst := by apply hom_ext; intro n; simp [biprodInr, biprodFst]
  inr_snd := by apply hom_ext; intro n; simp [biprodInr, biprodSnd]

/-- Binary direct sums are computed levelwise. -/
instance : HasBinaryBiproducts (CoherentFormalModule 𝔛) where
  has_binary_biproduct M N := hasBinaryBiproduct_of_total (biprodBicone M N) (by
    apply hom_ext
    intro n
    exact biprod.total)

/-- Coherent formal modules admit finite direct sums. -/
instance : HasFiniteBiproducts (CoherentFormalModule 𝔛) :=
  have : HasFiniteProducts (CoherentFormalModule 𝔛) :=
    hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Coherent formal modules admit all finite colimits. -/
instance : HasFiniteColimits (CoherentFormalModule 𝔛) :=
  have : HasCoequalizers (CoherentFormalModule 𝔛) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- Evaluation preserves cokernels, which are constructed levelwise. -/
instance evaluation_preservesCokernel (n : ℕ) {M N : CoherentFormalModule 𝔛} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (evaluation n) := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
  exact (isColimitMapCoconeCoforkEquiv' (evaluation n)
    (CokernelCofork.condition (cokernelCocone f))).symm (cokernelIsCokernel (f.app n))

/-- Finite colimits of coherent formal modules are computed at each level. -/
instance evaluation_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (evaluation (𝔛 := 𝔛) n) :=
  have : HasCoequalizers (CoherentFormalModule 𝔛) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

variable {J : Type v} [Category.{w} J] {F : J ⥤ CoherentFormalModule 𝔛}

/-- A cocone of coherent formal modules is colimiting if it is colimiting at every level.
This also applies to infinite diagrams whenever their proposed colimit is coherent. -/
def isColimitOfEvaluation (c : Cocone F)
    (hc : ∀ n, IsColimit ((evaluation n).mapCocone c)) : IsColimit c where
  desc s :=
    { app n := (hc n).desc ((evaluation n).mapCocone s)
      naturality n := by
        apply (isColimitOfPreserves (Scheme.Modules.pullback (𝔛.ι n)) (hc (n + 1))).hom_ext
        intro j
        have hfac (k : ℕ) : (c.ι.app j).app k ≫
            (hc k).desc ((evaluation k).mapCocone s) = (s.ι.app j).app k :=
          (hc k).fac ((evaluation k).mapCocone s) j
        have hs := (s.ι.app j).naturality n
        have ht := (c.ι.app j).naturality n
        dsimp only [Functor.const] at hs ht
        dsimp only [Functor.mapCocone_ι_app, evaluation]
        rw [← Functor.map_comp_assoc, hfac, hs, reassoc_of% ht, hfac] }
  fac s j := hom_ext fun n ↦ (hc n).fac ((evaluation n).mapCocone s) j
  uniq s m hm := hom_ext fun n ↦ (hc n).uniq ((evaluation n).mapCocone s) (m.app n)
    (fun j ↦ congrArg (fun f ↦ f.app n) (hm j))

/-- Evaluation of pullback is pullback of the evaluated module. -/
private def pullbackEvaluationIso (g : 𝔛 ⟶ 𝔜) (n : ℕ) :
    pullback g ⋙ evaluation n ≅ evaluation n ⋙ Scheme.Modules.pullback (g.app n) :=
  NatIso.ofComponents (fun M ↦ Iso.refl ((Scheme.Modules.pullback (g.app n)).obj (M.obj n)))
    (fun f ↦ by
      -- The components are identities because `pullback_obj_obj` identifies their endpoints.
      -- Normalize the composite functors and the prescribed levelwise pullback together.
      dsimp only [Functor.comp_map, Functor.comp_obj, evaluation, pullback, Iso.refl_hom]
      simp only [Category.comp_id, Category.id_comp])

/-- Pullback of coherent formal modules preserves finite colimits, without Noetherian or
flatness hypotheses on the morphism of systems. -/
instance pullback_preservesFiniteColimits (g : 𝔛 ⟶ 𝔜) :
    PreservesFiniteColimits (pullback g) where
  preservesFiniteColimits J _ _ :=
    { preservesColimit := fun {F} ↦
        { preserves := fun {c} hc ↦ ⟨isColimitOfEvaluation _ fun n ↦ by
            have : PreservesColimit F (pullback g ⋙ evaluation n) :=
              preservesColimit_of_natIso F (pullbackEvaluationIso g n).symm
            exact isColimitOfPreserves (pullback g ⋙ evaluation n) hc⟩ } }

end

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
