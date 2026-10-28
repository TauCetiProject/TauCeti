/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Homology
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian
public import TauCeti.Algebra.Homology.TotallyAcyclic.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Gorenstein-projective modules as Gorenstein-projective objects of `mod-A`

Let `A` be a left noetherian ring, so that the finitely generated `A`-modules form an abelian
category `FGModuleCat A`. The module notion of total acyclicity (`CochainComplex.IsTotallyAcyclic`:
finitely generated projective terms, acyclic, and `Hom_A(P, A)` acyclic) agrees with total
acyclicity in the abelian category `FGModuleCat A` (`CochainComplex.IsTotallyAcyclicProjective`:
projective terms, acyclic, and `Hom(P, Q)` acyclic for every projective object `Q`). Testing the
regular module suffices because finitely generated projective modules are retracts of finite free
modules (`CochainComplex.IsTotallyAcyclic.exact_hom_projective`). Consequently a finitely generated
module is Gorenstein-projective in the module sense (`TauCeti.IsGorensteinProjective`) if and
only if it is a Gorenstein-projective object of `FGModuleCat A`
(`CategoryTheory.isGorensteinProjective`).

So the abelian-category theory applies to the finitely generated Gorenstein-projective modules over
a noetherian ring. Right modules over `R` are the case `A = Rᵐᵒᵖ`.

## Main results

* `CochainComplex.isTotallyAcyclicProjective_iff_isTotallyAcyclic`: a cochain complex of finitely
  generated modules is totally acyclic in `FGModuleCat A` if and only if its underlying complex of
  modules is totally acyclic in the module sense.
* `FGModuleCat.isGorensteinProjective_iff`: a finitely generated module is a Gorenstein-projective
  object of `FGModuleCat A` if and only if it is a Gorenstein-projective module.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Ring A]

namespace CochainComplex

/-- The terms of the underlying complex of modules are the underlying modules of the terms. -/
private lemma forget₂_mapHomologicalComplex_obj_X (P : CochainComplex (FGModuleCat.{v} A) ℤ)
    (n : ℤ) :
    (((forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).mapHomologicalComplex _).obj P).X n =
      (P.X n).obj := by
  rw [Functor.mapHomologicalComplex_obj_X, FGModuleCat.forget₂_obj]

/-- The differentials of the underlying complex of modules are the underlying morphisms of the
differentials. -/
private lemma forget₂_mapHomologicalComplex_obj_d (P : CochainComplex (FGModuleCat.{v} A) ℤ)
    (i j : ℤ) :
    (((forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).mapHomologicalComplex _).obj P).d i j =
      (P.d i j).hom := by
  rw [Functor.mapHomologicalComplex_obj_d, FGModuleCat.forget₂_map]

variable [IsNoetherianRing A] [Small.{v} A]

/-- **Total acyclicity in `mod-A` is total acyclicity of modules**: a cochain complex of finitely
generated modules over a left noetherian ring is totally acyclic in the abelian category
`FGModuleCat A` if and only if its underlying complex of modules is totally acyclic. -/
theorem isTotallyAcyclicProjective_iff_isTotallyAcyclic
    (P : CochainComplex (FGModuleCat.{v} A) ℤ) :
    P.IsTotallyAcyclicProjective ↔ IsTotallyAcyclic
      (((forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).mapHomologicalComplex _).obj P) := by
  let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  have hac : ((F.mapHomologicalComplex _).obj P).Acyclic ↔ P.Acyclic :=
    forall_congr' fun n ↦ (P.sc n).exact_map_iff_of_faithful F
  rw [isTotallyAcyclicProjective_iff_factor]
  -- Below, linear maps out of the terms of the underlying complex of modules are used as linear
  -- maps out of the underlying modules of the terms of `P`, and conversely. This is the
  -- definitional equality of `forget₂_mapHomologicalComplex_obj_X`; the differentials agree by
  -- `forget₂_mapHomologicalComplex_obj_d`.
  constructor
  · rintro ⟨hproj, hP, h⟩
    refine ⟨fun n ↦ ?_, fun n ↦ ?_, hac.2 hP, fun i j k hij hjk φ ↦ ⟨fun hφ ↦ ?_, ?_⟩⟩
    · rw [forget₂_mapHomologicalComplex_obj_X]
      infer_instance
    · have := FGModuleCat.moduleProjective_of_projective (P.X n)
      rw [forget₂_mapHomologicalComplex_obj_X]
      exact ModuleCat.projective_of_categoryTheory_projective (P.X n).obj
    · -- Test against the regular module, through a `v`-small copy of it.
      let e := Shrink.linearEquiv.{v} A A
      let Q := FGModuleCat.of A (Shrink.{v} A)
      have := Module.Projective.of_equiv e.symm
      have := FGModuleCat.projective_of_moduleProjective A Q
      obtain rfl : i = j - 1 := by lia
      -- `φ` is defined on the term `(P.X j).obj`, by `forget₂_mapHomologicalComplex_obj_X`.
      have hφ' (x : P.X (j - 1)) : φ ((P.d (j - 1) j).hom.hom x) = 0 := by
        simpa [forget₂_mapHomologicalComplex_obj_d] using LinearMap.congr_fun hφ x
      let ψ : P.X j ⟶ Q := ObjectProperty.homMk (ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ φ))
      obtain ⟨g, hg⟩ := h j k hjk Q ψ (ObjectProperty.hom_ext _ (ModuleCat.hom_ext
        (LinearMap.ext fun x ↦ by simp [ψ, hφ'])))
      -- `g.hom.hom` is defined on `(P.X k).obj`, the term of the underlying complex in degree `k`.
      refine ⟨e.toLinearMap ∘ₗ g.hom.hom, LinearMap.ext fun x ↦ ?_⟩
      have := congrArg e (LinearMap.congr_fun (congrArg (fun f ↦ f.hom.hom) hg) x)
      simpa [ψ, forget₂_mapHomologicalComplex_obj_d] using this
    · rintro ⟨g, rfl⟩
      refine LinearMap.ext fun x ↦ ?_
      have := LinearMap.congr_fun (congrArg (fun f ↦ f.hom.hom) (P.d_comp_d i j k)) x
      simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
        LinearMap.comp_apply] at this
      simp [this]
  · intro hP'
    refine ⟨fun n ↦ ?_, hac.1 hP'.acyclic, fun i j hij Q _ φ hφ ↦ ?_⟩
    · have := hP'.projective n
      rw [forget₂_mapHomologicalComplex_obj_X] at this
      have : Module.Projective A (P.X n) := ModuleCat.projective_of_module_projective (P.X n).obj
      exact FGModuleCat.projective_of_moduleProjective A (P.X n)
    · have := FGModuleCat.moduleProjective_of_projective Q
      -- `φ.hom.hom` is a linear map out of the term of the underlying complex in degree `i`, and
      -- the resulting `g` out of the one in degree `j`, by `forget₂_mapHomologicalComplex_obj_X`.
      obtain ⟨g, hg⟩ := ((hP'.exact_hom_projective (Q := Q) (i - 1) i j (by lia) hij)
        φ.hom.hom).1 (LinearMap.ext fun x ↦ by
          simpa [forget₂_mapHomologicalComplex_obj_d] using congrArg (fun f ↦ f.hom.hom x) hφ)
      exact ⟨ObjectProperty.homMk (ModuleCat.ofHom g), ObjectProperty.hom_ext _
        (ModuleCat.hom_ext (by simpa [forget₂_mapHomologicalComplex_obj_d] using hg))⟩

end CochainComplex

namespace FGModuleCat

open CochainComplex

variable [IsNoetherianRing A] [Small.{v} A]

/-- **Gorenstein-projective modules are the Gorenstein-projective objects of `mod-A`**: over a
left noetherian ring, a finitely generated module is a Gorenstein-projective object of the abelian
category `FGModuleCat A` if and only if it is a Gorenstein-projective module. -/
theorem isGorensteinProjective_iff (M : FGModuleCat.{v} A) :
    isGorensteinProjective (FGModuleCat.{v} A) M ↔ TauCeti.IsGorensteinProjective.{v} A M.obj := by
  let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  rw [CategoryTheory.isGorensteinProjective_iff, TauCeti.isGorensteinProjective_iff]
  constructor
  · rintro ⟨P, hP, ⟨e⟩⟩
    exact ⟨(F.mapHomologicalComplex _).obj P,
      (CochainComplex.isTotallyAcyclicProjective_iff_isTotallyAcyclic P).1 hP,
      ⟨(P.sc 0).mapCyclesIso F ≪≫ F.mapIso e⟩⟩
  · rintro ⟨P, hP, ⟨e⟩⟩
    let K := liftHomologicalComplex P hP.finite
    refine ⟨K, (CochainComplex.isTotallyAcyclicProjective_iff_isTotallyAcyclic K).2
      (hP.of_iso (liftHomologicalComplexIso P hP.finite).symm), ⟨F.preimageIso ?_⟩⟩
    exact ((K.sc 0).mapCyclesIso F).symm ≪≫
      HomologicalComplex.cyclesMapIso (liftHomologicalComplexIso P hP.finite) 0 ≪≫ e

end FGModuleCat
