/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

variable {A : Type u} [Ring A] [IsNoetherianRing A] [Small.{v} A]

namespace CochainComplex

omit [IsNoetherianRing A] [Small.{v} A] in
/-- The forgetful functor from finitely generated modules is the inclusion of a full subcategory,
so it acts on morphisms by taking the underlying morphism. -/
private lemma forget₂_map_eq {X Y : FGModuleCat.{v} A} (f : X ⟶ Y) :
    (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).map f = f.hom :=
  rfl

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
  constructor
  · rintro ⟨hproj, hP, h⟩
    refine ⟨fun n ↦ inferInstanceAs (Module.Finite A (P.X n)), fun n ↦ ?_, hac.2 hP,
      fun i j k hij hjk φ ↦ ⟨fun hφ ↦ ?_, ?_⟩⟩
    · have := FGModuleCat.moduleProjective_of_projective (P.X n)
      exact ModuleCat.projective_of_categoryTheory_projective (P.X n).obj
    · -- Test against the regular module, through a `v`-small copy of it.
      let e := Shrink.linearEquiv.{v} A A
      let Q := FGModuleCat.of A (Shrink.{v} A)
      have := Module.Projective.of_equiv e.symm
      have := FGModuleCat.projective_of_moduleProjective A Q
      obtain rfl : i = j - 1 := by lia
      have hφ' (x : P.X (j - 1)) : φ ((P.d (j - 1) j).hom.hom x) = 0 := by
        simpa [forget₂_map_eq] using LinearMap.congr_fun hφ x
      let ψ : P.X j ⟶ Q := ObjectProperty.homMk (ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ φ))
      obtain ⟨g, hg⟩ := h j k hjk Q ψ (ObjectProperty.hom_ext _ (ModuleCat.hom_ext
        (LinearMap.ext fun x ↦ by simp [ψ, hφ'])))
      refine ⟨e.toLinearMap ∘ₗ g.hom.hom, LinearMap.ext fun x ↦ ?_⟩
      have := congrArg e (LinearMap.congr_fun (congrArg (fun f ↦ f.hom.hom) hg) x)
      simpa [ψ, forget₂_map_eq] using this
    · rintro ⟨g, rfl⟩
      refine LinearMap.ext fun x ↦ ?_
      have := LinearMap.congr_fun (congrArg (fun f ↦ f.hom.hom) (P.d_comp_d i j k)) x
      simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
        LinearMap.comp_apply] at this
      simp [forget₂_map_eq, this]
  · intro hP'
    refine ⟨fun n ↦ ?_, hac.1 hP'.acyclic, fun i j hij Q _ φ hφ ↦ ?_⟩
    · have : Module.Projective A (P.X n) :=
        @ModuleCat.projective_of_module_projective _ _ (P.X n).obj _ (hP'.projective n)
      exact FGModuleCat.projective_of_moduleProjective A (P.X n)
    · have := FGModuleCat.moduleProjective_of_projective Q
      obtain ⟨g, hg⟩ := ((hP'.exact_hom_projective (Q := Q) (i - 1) i j (by lia) hij)
        φ.hom.hom).1 (LinearMap.ext fun x ↦ congrArg (fun f ↦ f.hom.hom x) hφ)
      exact ⟨FGModuleCat.ofHom g, ObjectProperty.hom_ext _ (ModuleCat.hom_ext hg)⟩

end CochainComplex

namespace FGModuleCat

open CochainComplex

/-- A cochain complex of modules with finitely generated terms, as a complex in `FGModuleCat A`. -/
private def liftComplex (P : CochainComplex (ModuleCat.{v} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) : CochainComplex (FGModuleCat.{v} A) ℤ where
  X n := ⟨P.X n, hP n⟩
  d i j := ObjectProperty.homMk (P.d i j)
  shape i j hij := ObjectProperty.hom_ext _ (P.shape i j hij)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (P.d_comp_d i j k)

/-- The underlying complex of modules of `liftComplex P hP` is `P`. -/
private def liftComplexIso (P : CochainComplex (ModuleCat.{v} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) :
    ((forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)).mapHomologicalComplex _).obj
      (liftComplex P hP) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i
    dsimp [liftComplex]
    simp [forget₂_map_eq])

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
    let K := liftComplex P hP.finite
    refine ⟨K, (CochainComplex.isTotallyAcyclicProjective_iff_isTotallyAcyclic K).2
      (hP.of_iso (liftComplexIso P hP.finite).symm), ⟨F.preimageIso ?_⟩⟩
    exact ((K.sc 0).mapCyclesIso F).symm ≪≫
      HomologicalComplex.cyclesMapIso (liftComplexIso P hP.finite) 0 ≪≫ e

end FGModuleCat
