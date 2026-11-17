/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.GlobalSections
public import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Global sections and equivalence of coherent formal modules on `spf I`

Let `I` be an ideal of a commutative ring `R`. A coherent formal module `M` on the formal spectrum
`spf I`, whose levels are the affine schemes `Spec (R ⧸ I ^ (n + 1))`, is a system of finitely
presented modules `M n` on these levels with reduction isomorphisms `ι n ^* M (n + 1) ≅ M n`. Taking
global sections level by level turns it into a tower of `R`-modules
`Γ(M 0) ← Γ(M 1) ← Γ(M 2) ← ⋯`, whose transitions pull a section back along the closed immersion
`ι n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))` and then apply the reduction isomorphism.

Since `M (n + 1)` is quasi-coherent, its pullback along `ι n` has global sections
`(R ⧸ I ^ (n + 1)) ⊗ Γ(M (n + 1)) = Γ(M (n + 1)) ⧸ I ^ (n + 1) Γ(M (n + 1))`, so the tower is an
`I`-adic system; its first term is finite, being the sections of a finitely presented module on an
affine scheme (`isFiniteAdicSystem_sectionsTower_obj`). Morphisms of coherent formal modules on
`spf I` are the morphisms of these towers, so `finiteSectionsTower I` is fully faithful for any
commutative ring `R`.

When every quotient `R ⧸ I ^ (n + 1)` is Noetherian — in particular when `I` is finitely generated
and `R ⧸ I` is Noetherian (`essSurj_finiteSectionsTower_of_fg`), or when `R` is Noetherian — every
finite `I`-adic system `(Mₙ)` arises in this way: `I ^ (n + 1)` annihilates `Mₙ`, so
`(R ⧸ I ^ (n + 1)) ⊗[R] Mₙ` is a finite — hence finitely presented — `(R ⧸ I ^ (n + 1))`-module
whose associated sheaf has global sections `Mₙ`, and the transitions of `(Mₙ)` lift to reduction
isomorphisms (`essSurj_finiteSectionsTower`). Conversely, essential surjectivity of
`finiteSectionsTower I` forces every `R ⧸ I ^ (n + 1)` to be Noetherian
(`essSurj_finiteSectionsTower_iff`, `isEquivalence_finiteSectionsTower_iff`). Consequently, without
Noetherianity essential surjectivity fails even for `I = ⊥`: over `k[x₀, x₁, …]` (`k` nontrivial),
`finiteSectionsTower ⊥` is not essentially surjective
(`not_essSurj_finiteSectionsTower_mvPolynomial`).

Combining `finiteSectionsTower I` with the equivalence between finite `R`-modules and finite
`I`-adic systems (`TauCeti.ModuleTower.finiteReductionEquiv`) proves Stacks, Lemma 30.23.1
(`CoherentFormalModule.spfEquiv`, `Spf.coherentFormalModuleEquiv`): over an `I`-adically complete
Noetherian ring `R`, coherent formal modules on `spf I` are equivalent to finite `R`-modules, with
inverse functor `finiteSectionsLim I` taking the inverse limit of levelwise global sections.

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsTower`,
  `finiteSectionsTower`: the tower of global sections of the levels of a coherent formal module on
  `spf I`, and its lift to `I`-adic systems with finite first term.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsLim`,
  `finiteSectionsLim`: the inverse limit `lim Γ(M n)` of levelwise global sections.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.spfEquiv`,
  `TauCeti.AlgebraicGeometry.Spf.coherentFormalModuleEquiv`: equivalence between finite modules over
  a Noetherian `I`-adically complete ring and coherent formal modules on its formal spectrum.

## Main results

* `CoherentFormalModule.isFiniteAdicSystem_sectionsTower_obj`: the tower of global sections is an
  `I`-adic system with finite first term.
* `CoherentFormalModule.sectionsTower` is additive, full, and faithful; `finiteSectionsTower I` is
  an equivalence if and only if every `R ⧸ I ^ (n + 1)` is Noetherian
  (`isEquivalence_finiteSectionsTower`, `isEquivalence_finiteSectionsTower_iff`), in particular when
  `I` is finitely generated and `R ⧸ I` is Noetherian (`isEquivalence_finiteSectionsTower_of_fg`)
  or when `R` is Noetherian.
* `CoherentFormalModule.not_essSurj_finiteSectionsTower_mvPolynomial`: `finiteSectionsTower ⊥` is
  not essentially surjective over `MvPolynomial ℕ k` for nontrivial `k`.

## References

* [Stacks Project, Lemma 30.23.1](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped ChangeOfRings
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

noncomputable section

/-! ### The tower of global sections -/

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The tower `Γ(M 0) ← Γ(M 1) ← ⋯` of global sections of the levels of a coherent formal module
`M` on `spf I`, as `R`-modules. The transition `Γ(M (n + 1)) ⟶ Γ(M n)` pulls a section back along
`ι n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))` and applies the reduction isomorphism
(`sectionsTower_obj_transition_apply`). -/
-- `@[expose]` is forced by dependent typing: without the terms of `(sectionsTower I).obj M`
-- reducing definitionally to the global sections of the levels of `M`,
-- `sectionsTower_obj_transition_apply` and `sectionsTower_map_app` do not typecheck.
@[expose]
def sectionsTower : CoherentFormalModule (spf I) ⥤ ModuleTower.{u} R where
  obj M := Functor.ofOpSequence
    (X := fun n ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj
      (moduleSpecΓFunctor.obj (M.obj n)))
    fun n ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).map
        ((CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).moduleSpecΓPullbackAdjoint
            (M.transitionIso n).hom) ≫
      (ModuleCat.restrictScalarsComp'App _ _ _
        (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))).symm
        _).inv
  map {M N} f := NatTrans.ofOpSequence
    (fun n ↦ (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map
      (moduleSpecΓFunctor.map (f.app n))) fun n ↦ by
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
    exact (CommRingCat.Hom.restrictScalars_moduleSpecΓPullbackAdjoint_naturality_iff _ _ _ _
      (hN₁ := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj (n + 1)))
      (M.transitionIso n).hom (N.transitionIso n).hom (f.app (n + 1)) (f.app n)).2 (f.naturality n)
  -- `simp` cannot see through `NatTrans.ofOpSequence` here, whose components are only
  -- definitionally the images of the levelwise maps.
  map_id M := by
    ext ⟨n⟩ : 2
    exact (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map_id _
  map_comp f g := by
    ext ⟨n⟩ : 2
    exact (congrArg (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map
      (moduleSpecΓFunctor.map_comp (f.app n) (g.app n))).trans (Functor.map_comp _ _ _)

@[simp]
theorem sectionsTower_obj_obj (M : CoherentFormalModule (spf I)) (n : ℕ) :
    ((sectionsTower I).obj M).obj (op n) =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj
        (moduleSpecΓFunctor.obj (M.obj n)) :=
  (rfl)

@[simp]
theorem sectionsTower_map_app {M N : CoherentFormalModule (spf I)} (f : M ⟶ N) (n : ℕ) :
    ((sectionsTower I).map f).app (op n) =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map
        (moduleSpecΓFunctor.map (f.app n)) :=
  (rfl)

/-- The transition `Γ(M (n + 1)) ⟶ Γ(M n)` of the tower of global sections pulls a section back
along `ι n` and applies the reduction isomorphism `ι n ^* M (n + 1) ≅ M n`. -/
theorem sectionsTower_obj_transition_apply (M : CoherentFormalModule (spf I)) (n : ℕ)
    (x : ((sectionsTower I).obj M).obj (op (n + 1))) :
    ((sectionsTower I).obj M).transition n x =
      moduleSpecΓFunctor.map (M.transitionIso n).hom
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          ((spf I).ι n)).unit.app (M.obj (n + 1))) x) := by
  rw [ModuleTower.transition_def]
  simp only [sectionsTower, Functor.ofOpSequence_map_homOfLE_succ]
  -- The transition is `moduleSpecΓPullbackAdjoint` up to `restrictScalars` and
  -- `restrictScalarsComp'App`, which do not change underlying maps. These cannot be unfolded by
  -- `rw`: the goal only typechecks after identifying the level `(spf I).X n` with
  -- `Spec (R ⧸ I ^ (n + 1))`.
  exact CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ (M.transitionIso n).hom x

/-- **The global sections of a coherent formal module on `spf I` form a finite `I`-adic system.**
Each transition `Γ(M (n + 1)) ⟶ Γ(M n)` is surjective with kernel `I ^ (n + 1) Γ(M (n + 1))`, and
`Γ(M 0)` is a finite `R`-module. -/
theorem isFiniteAdicSystem_sectionsTower_obj (M : CoherentFormalModule (spf I)) :
    ModuleTower.isFiniteAdicSystem I ((sectionsTower I).obj M) := by
  have hφ (n : ℕ) : Function.Surjective (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))) :=
    Ideal.Quotient.factor_surjective _
  have hq (n : ℕ) := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj n)
  have he (n : ℕ) := (moduleSpecΓFunctor.mapIso (M.transitionIso n)).toLinearEquiv.bijective
  refine (ModuleTower.isFiniteAdicSystem_iff I _).2
    ⟨⟨fun n y ↦ ?_, fun n ↦ le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.2 fun r hr y _ ↦ ?_)⟩,
      ?_⟩
  · obtain ⟨z, rfl⟩ := (he n).2 y
    obtain ⟨x, rfl⟩ := @CommRingCat.Hom.moduleSpecΓFunctor_map_unit_surjective _ _
      (CommRingCat.ofHom _) (hφ n) (M.obj (n + 1)) (hq (n + 1)) z
    exact ⟨x, sectionsTower_obj_transition_apply I M n x⟩
  · -- A section in the kernel restricts to zero on `Spec (R ⧸ I ^ (n + 1))`, so it lies in
    -- `I ^ (n + 1) Γ(M (n + 1))`, first for the action of `R ⧸ I ^ (n + 2)`, hence for that of `R`.
    have h : x ∈ LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction ((spf I).ι n)).unit.app
          (M.obj (n + 1)))).hom :=
      (he n).1 (((sectionsTower_obj_transition_apply I M n x).symm.trans hx).trans
        (map_zero _).symm)
    refine Submodule.smul_induction_on (p := fun z : moduleSpecΓFunctor.obj (M.obj (n + 1)) ↦
      (z : ((sectionsTower I).obj M).obj (op (n + 1))) ∈ I ^ (n + 1) • ⊤)
        ((SetLike.ext_iff.1 (@CommRingCat.Hom.ker_moduleSpecΓFunctor_map_unit _ _
          (CommRingCat.ofHom _) (hφ n) _ (hq (n + 1))) x).1 h) (fun k hk y _ ↦ ?_)
        (fun _ _ ↦ Submodule.add_mem _)
    replace hk : k ∈ RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))) := hk
    rw [Ideal.Quotient.factor_ker,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    exact Submodule.smul_mem_smul (M := ((sectionsTower I).obj M).obj (op (n + 1))) (n := y) hr
      Submodule.mem_top
  · -- `I ^ (n + 1)` kills the sections of `M n`, a module over `R ⧸ I ^ (n + 1)`.
    rw [LinearMap.mem_ker, map_smul]
    exact (ModuleCat.restrictScalars.smul_def (Ideal.Quotient.mk (I ^ (n + 1)))
      (M := moduleSpecΓFunctor.obj (M.obj n)) r _).trans
        (by rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]; rfl)
  · have := @Scheme.Modules.finitePresentation_moduleSpecΓ _ (M.obj 0) (M.isFinitePresentation 0)
    exact ((Ideal.Quotient.mk _).finite_restrictScalars_iff Ideal.Quotient.mk_surjective _).2
      inferInstance

instance : (sectionsTower I).Faithful where
  map_injective {M N} _ _ h := hom_ext fun n ↦
    (@Scheme.Modules.moduleSpecΓFunctor_map_bijective _ (M.obj n) (N.obj n)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj n))).1
        ((ModuleCat.restrictScalars _).map_injective (congrArg (·.app (op n)) h))

instance : (sectionsTower I).Full where
  map_surjective {M N} τ := by
    have hfull (n : ℕ) := (Ideal.Quotient.mk (I ^ (n + 1))).full_restrictScalars
      Ideal.Quotient.mk_surjective
    choose f hf using fun n ↦
      (@Scheme.Modules.moduleSpecΓFunctor_map_bijective _ (M.obj n) (N.obj n)
        (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj n))).2
          (@Functor.preimage _ _ _ _ _ _ _ (hfull n) (τ.app (op n)))
    have hτ (n : ℕ) : (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map
        (moduleSpecΓFunctor.map (f n)) = τ.app (op n) := by
      have := hfull n
      exact (congrArg (ModuleCat.restrictScalars _).map (hf n)).trans (Functor.map_preimage _ _)
    refine ⟨{ app := f, naturality := fun n ↦ ?_ }, NatTrans.ext (funext fun n ↦ hτ n.unop)⟩
    have h := τ.naturality (homOfLE (Nat.le_succ n)).op
    simp only [sectionsTower, Functor.ofOpSequence_map_homOfLE_succ, ← hτ] at h
    exact (CommRingCat.Hom.restrictScalars_moduleSpecΓPullbackAdjoint_naturality_iff _ _ _ _
      (hN₁ := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (M.obj (n + 1)))
      (M.transitionIso n).hom (N.transitionIso n).hom (f (n + 1)) (f n)).1 h

instance : (sectionsTower I).Additive where
  map_add {_ _ _ _} := NatTrans.ext <| funext fun ⟨_⟩ ↦
    ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- The tower of global sections of a coherent formal module on `spf I`, as an `I`-adic system with
finite first term (`isFiniteAdicSystem_sectionsTower_obj`). It is additive and fully faithful, and
is an equivalence if and only if every quotient `R ⧸ I ^ (n + 1)` is Noetherian
(`isEquivalence_finiteSectionsTower`, `isEquivalence_finiteSectionsTower_iff`). -/
-- `@[expose]` is forced by dependent typing, as for `ModuleTower.finiteReduction`: the morphisms
-- in `finiteSectionsTower_map_hom` are morphisms of towers only because the underlying towers of
-- `finiteSectionsTower I` reduce definitionally to those of `sectionsTower I`.
@[expose, simps! obj_obj map_hom]
def finiteSectionsTower : CoherentFormalModule (spf I) ⥤ ModuleTower.FiniteAdicSystem.{u} I :=
  (ModuleTower.isFiniteAdicSystem I).lift (sectionsTower I) (isFiniteAdicSystem_sectionsTower_obj I)

instance : (finiteSectionsTower I).Additive where
  map_add {_ _ f g} :=
    (ModuleTower.isFiniteAdicSystem I).hom_ext ((sectionsTower I).map_add (f := f) (g := g))

instance : (finiteSectionsTower I).Full :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Full

instance : (finiteSectionsTower I).Faithful :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Faithful

end

/-! ### Essential surjectivity on `spf I` -/

noncomputable section

variable {R : Type u} [CommRing R]

private def spfLiftModule (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    ModuleCat.{u} (R ⧸ I ^ (n + 1)) :=
  (ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj (F.obj.obj (op n))

private instance finite_spfLiftModule (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I)
    (n : ℕ) :
    Module.Finite (R ⧸ I ^ (n + 1)) (spfLiftModule I F n) :=
  Module.Finite.equiv
    (ModuleCat.extendScalarsAlgebraMapIso (S := R ⧸ I ^ (n + 1))
      (F.obj.obj (op n))).symm.toLinearEquiv

private abbrev spfLiftSheaf (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).Modules :=
  tilde (R := .of (R ⧸ I ^ (n + 1))) (spfLiftModule I F n)

private lemma isFinitePresentation_spfLiftSheaf (I : Ideal R)
    (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) [IsNoetherianRing (R ⧸ I ^ (n + 1))] :
    (spfLiftSheaf I F n).IsFinitePresentation := by
  have : Module.FinitePresentation (R ⧸ I ^ (n + 1)) (spfLiftModule I F n) :=
    Module.finitePresentation_of_finite (R ⧸ I ^ (n + 1)) (spfLiftModule I F n)
  exact isFinitePresentation_tilde (R := .of (R ⧸ I ^ (n + 1))) (spfLiftModule I F n)

private lemma isIso_extendRestrictUnit_spfLift (I : Ideal R)
    (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ (n + 1)))).unit.app
      (F.obj.obj (op n))) := by
  have hF := ((ModuleTower.isFiniteAdicSystem_iff I _).1 F.property).1
  rw [ModuleCat.isIso_extendRestrictScalarsAdj_unit_app_iff_of_surjective
    Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact hF.pow_smul_top_eq_bot n

private def spfLiftSectionIso (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    F.obj.obj (op n) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj
        (moduleSpecΓFunctor.obj (spfLiftSheaf I F n)) :=
  letI := isIso_extendRestrictUnit_spfLift I F n
  asIso ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ (n + 1)))).unit.app
    (F.obj.obj (op n))) ≪≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapIso
      ((tilde.toTildeΓNatIso (R := .of (R ⧸ I ^ (n + 1)))).app (spfLiftModule I F n))

private def spfLiftTransitionQuotMap (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I)
    (n : ℕ) :
    moduleSpecΓFunctor.obj (spfLiftSheaf I F (n + 1)) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).obj
        (moduleSpecΓFunctor.obj (spfLiftSheaf I F n)) :=
  letI := (Ideal.Quotient.mk (I ^ (n + 1 + 1))).full_restrictScalars Ideal.Quotient.mk_surjective
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).preimage
    (((spfLiftSectionIso I F (n + 1)).inv ≫
        F.obj.map (homOfLE (Nat.le_succ n)).op ≫
        (spfLiftSectionIso I F n).hom) ≫
      (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (I ^ (n + 1 + 1))) _
        (Ideal.Quotient.mk (I ^ (n + 1)))
        (Ideal.Quotient.factor_comp_mk
          (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))).symm _).hom)

private lemma map_spfLiftTransitionQuotMap (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I)
    (n : ℕ) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).map
        (spfLiftTransitionQuotMap I F n) =
      ((spfLiftSectionIso I F (n + 1)).inv ≫
          F.obj.map (homOfLE (Nat.le_succ n)).op ≫
          (spfLiftSectionIso I F n).hom) ≫
        (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (I ^ (n + 1 + 1))) _
          (Ideal.Quotient.mk (I ^ (n + 1)))
          (Ideal.Quotient.factor_comp_mk
            (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))).symm _).hom := by
  have := (Ideal.Quotient.mk (I ^ (n + 1 + 1))).full_restrictScalars Ideal.Quotient.mk_surjective
  exact Functor.map_preimage _ _

private lemma spfLiftTransitionQuotMap_apply (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I)
    (n : ℕ) (x : moduleSpecΓFunctor.obj (spfLiftSheaf I F (n + 1))) :
    (spfLiftTransitionQuotMap I F n x : moduleSpecΓFunctor.obj (spfLiftSheaf I F n)) =
      (spfLiftSectionIso I F n).hom
        (F.obj.transition n ((spfLiftSectionIso I F (n + 1)).inv x)) := by
  rw [ModuleTower.transition_def]
  exact congrArg (fun f ↦ (f x : moduleSpecΓFunctor.obj (spfLiftSheaf I F n)))
    (map_spfLiftTransitionQuotMap I F n)

private lemma spfLiftTransitionQuotMap_surjective (I : Ideal R)
    (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    Function.Surjective (spfLiftTransitionQuotMap I F n) := by
  have hF := ((ModuleTower.isFiniteAdicSystem_iff I _).1 F.property).1
  intro y
  let y' : (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).obj
      (moduleSpecΓFunctor.obj (spfLiftSheaf I F n)) := y
  obtain ⟨w, hw⟩ := hF.transition_surjective n ((spfLiftSectionIso I F n).inv y')
  refine ⟨(spfLiftSectionIso I F (n + 1)).hom w, ?_⟩
  exact (spfLiftTransitionQuotMap_apply I F n _).trans
    ((congrArg (fun z ↦ (spfLiftSectionIso I F n).hom (F.obj.transition n z))
      ((spfLiftSectionIso I F (n + 1)).hom_inv_id_apply w)).trans
      ((congrArg (spfLiftSectionIso I F n).hom hw).trans
        ((spfLiftSectionIso I F n).inv_hom_id_apply y')))

private lemma ker_spfLiftTransitionQuotMap (I : Ideal R)
    (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    LinearMap.ker (spfLiftTransitionQuotMap I F n).hom =
      RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))) • ⊤ := by
  have hF := ((ModuleTower.isFiniteAdicSystem_iff I _).1 F.property).1
  let M₁ := moduleSpecΓFunctor.obj (spfLiftSheaf I F (n + 1))
  let : Module R M₁ := Module.compHom M₁ (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
  have : IsScalarTower R (R ⧸ I ^ (n + 1 + 1)) M₁ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine Submodule.restrictScalars_injective R (R ⧸ I ^ (n + 1 + 1)) M₁ ?_
  rw [Ideal.Quotient.factor_ker, ← Ideal.Quotient.algebraMap_eq,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  let e : F.obj.obj (op (n + 1)) ≃ₗ[R] M₁ := (spfLiftSectionIso I F (n + 1)).toLinearEquiv
  have htop : Submodule.map (e : _ →ₗ[R] _)
      (I ^ (n + 1) • (⊤ : Submodule R (F.obj.obj (op (n + 1))))) =
      I ^ (n + 1) • (⊤ : Submodule R M₁) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  ext x
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← htop, Submodule.mem_map_equiv,
    ← hF.ker_transition n, LinearMap.mem_ker]
  exact ⟨fun hx ↦ (spfLiftSectionIso I F n).toLinearEquiv.injective
      (((spfLiftTransitionQuotMap_apply I F n x).symm.trans hx).trans (map_zero _).symm),
    fun hx ↦ (spfLiftTransitionQuotMap_apply I F n x).trans
      ((congrArg (spfLiftSectionIso I F n).hom hx).trans (map_zero _))⟩

private lemma isIso_spfLiftTransitionExt (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I)
    (n : ℕ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).homEquiv
        _ _).symm (spfLiftTransitionQuotMap I F n)) :=
  (ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_iff_of_surjective
      (Ideal.Quotient.factor_surjective _) (spfLiftTransitionQuotMap I F n)).2
    ⟨spfLiftTransitionQuotMap_surjective I F n, ker_spfLiftTransitionQuotMap I F n⟩

private def spfLiftTransitionIso (I : Ideal R) (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))).obj
      (spfLiftSheaf I F (n + 1)) ≅ spfLiftSheaf I F n :=
  letI := isIso_spfLiftTransitionExt I F n
  Scheme.Modules.isoOfModuleSpecΓIso
    (((CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).moduleSpecΓPullbackIso
        (spfLiftSheaf I F (n + 1))).symm ≪≫
      asIso (((ModuleCat.extendRestrictScalarsAdj
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).homEquiv _ _).symm
        (spfLiftTransitionQuotMap I F n)))

private abbrev spfLift (I : Ideal R) [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))]
    (F : ModuleTower.FiniteAdicSystem.{u} I) :
    CoherentFormalModule (spf I) where
  obj := spfLiftSheaf I F
  isFinitePresentation n := isFinitePresentation_spfLiftSheaf I F n
  transitionIso := spfLiftTransitionIso I F

private lemma sectionsTower_spfLift_transition (I : Ideal R)
    [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))]
    (F : ModuleTower.FiniteAdicSystem.{u} I) (n : ℕ) :
    ((sectionsTower I).obj (spfLift I F)).map (homOfLE (Nat.le_succ n)).op =
      (spfLiftSectionIso I F (n + 1)).inv ≫
        F.obj.map (homOfLE (Nat.le_succ n)).op ≫
        (spfLiftSectionIso I F n).hom := by
  simp only [sectionsTower, Functor.ofOpSequence_map_homOfLE_succ, spfLift]
  have := isIso_spfLiftTransitionExt I F n
  have hadj : (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))).moduleSpecΓPullbackAdjoint
        (spfLiftTransitionIso I F n).hom = spfLiftTransitionQuotMap I F n := by
    let φ := Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))
    let e := (CommRingCat.ofHom φ).moduleSpecΓPullbackIso (spfLiftSheaf I F (n + 1))
    let g := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv
      (moduleSpecΓFunctor.obj (spfLiftSheaf I F (n + 1)))
      (moduleSpecΓFunctor.obj (spfLiftSheaf I F n))).symm (spfLiftTransitionQuotMap I F n)
    refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
    refine (CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply
      (CommRingCat.ofHom φ) (spfLiftTransitionIso I F n).hom x).trans ?_
    have hmap := Scheme.Modules.moduleSpecΓFunctor_map_isoOfModuleSpecΓIso_hom (e.symm ≪≫ asIso g)
    have h1 := (CommRingCat.Hom.moduleSpecΓPullback_app_one_tmul
      (CommRingCat.ofHom φ) (spfLiftSheaf I F (n + 1)) x).symm
    rw [← CommRingCat.Hom.moduleSpecΓPullbackIso_hom] at h1
    let t : (ModuleCat.extendScalars φ).obj (moduleSpecΓFunctor.obj (spfLiftSheaf I F (n + 1))) :=
      (1 : R ⧸ I ^ (n + 1)) ⊗ₜ[R ⧸ I ^ (n + 1 + 1), φ] x
    let u := e.hom t
    refine (congrArg (moduleSpecΓFunctor.map (spfLiftTransitionIso I F n).hom) h1).trans ?_
    refine (congrArg (fun f ↦ f.hom u) hmap).trans ?_
    exact (congrArg g (e.hom_inv_id_apply t)).trans
      ((ModuleCat.extendRestrictScalarsAdj_homEquiv_apply g x).symm.trans
        (congrArg (fun h ↦ h.hom x)
          (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply
            (spfLiftTransitionQuotMap I F n))))
  rw [hadj, map_spfLiftTransitionQuotMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- When every quotient `R ⧸ I ^ (n + 1)` is Noetherian — in particular when `R` is Noetherian —
every `I`-adic system with finite first term is the global-sections tower of a coherent formal
module on `spf I`. No `I`-adic completeness assumption on `R` is needed. -/
instance essSurj_finiteSectionsTower (I : Ideal R) [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))] :
    (finiteSectionsTower I).EssSurj where
  mem_essImage F := by
    let e : (sectionsTower I).obj (spfLift I F) ≅ F.obj :=
      { hom := NatTrans.ofOpSequence (fun n ↦ (spfLiftSectionIso I F n).inv) fun n ↦
          (congrArg (· ≫ (spfLiftSectionIso I F n).inv)
            (sectionsTower_spfLift_transition I F n)).trans <|
            ModuleCat.hom_ext <| LinearMap.ext fun x ↦
              (spfLiftSectionIso I F n).hom_inv_id_apply _
        inv := NatTrans.ofOpSequence (fun n ↦ (spfLiftSectionIso I F n).hom) fun n ↦
          ((congrArg ((spfLiftSectionIso I F (n + 1)).hom ≫ ·)
            (sectionsTower_spfLift_transition I F n)).trans <|
            ModuleCat.hom_ext <| LinearMap.ext fun x ↦
              congrArg
                (fun y ↦ (spfLiftSectionIso I F n).hom
                  ((F.obj.map (homOfLE (Nat.le_succ n)).op) y))
                ((spfLiftSectionIso I F (n + 1)).hom_inv_id_apply x)).symm
        hom_inv_id := by
          ext ⟨n⟩ : 2
          exact (spfLiftSectionIso I F n).inv_hom_id
        inv_hom_id := by
          ext ⟨n⟩ : 2
          exact (spfLiftSectionIso I F n).hom_inv_id }
    exact ⟨spfLift I F, ⟨(ModuleTower.isFiniteAdicSystem I).isoMk e⟩⟩

/-- When `I` is finitely generated and `R ⧸ I` is Noetherian, every quotient `R ⧸ I ^ (n + 1)` is
Noetherian, so `finiteSectionsTower I` is essentially surjective without global Noetherianity or
`I`-adic completeness assumptions on `R`. -/
theorem essSurj_finiteSectionsTower_of_fg (I : Ideal R) (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    (finiteSectionsTower I).EssSurj :=
  have : ∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1)) := fun n ↦
    Ideal.isNoetherianRing_quotient_pow_of_fg I hI (n + 1)
  inferInstance

/-- `finiteSectionsTower I` is essentially surjective if and only if every quotient
`R ⧸ I ^ (n + 1)` is Noetherian. -/
theorem essSurj_finiteSectionsTower_iff (I : Ideal R) :
    (finiteSectionsTower I).EssSurj ↔ ∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1)) := by
  refine ⟨fun hEss n ↦ (isNoetherianRing_iff_ideal_fg _).2 fun J ↦ ?_,
    fun h ↦ @essSurj_finiteSectionsTower _ _ I h⟩
  let S := R ⧸ I ^ (n + 1)
  let φ : R →+* S := Ideal.Quotient.mk (I ^ (n + 1))
  let M : ModuleCat.{u} R := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (S ⧸ J))
  have : Module.Finite S (S ⧸ J) := .of_surjective J.mkQ (Submodule.mkQ_surjective J)
  have : Module.Finite R M :=
    (φ.finite_restrictScalars_iff Ideal.Quotient.mk_surjective (ModuleCat.of S (S ⧸ J))).2
      inferInstance
  let F : ModuleTower.FiniteAdicSystem.{u} I :=
    (ModuleTower.finiteReduction.{u} I).obj (FGModuleCat.of R M)
  have hker : LinearMap.ker (ModuleTower.reductionπ I M n) = ⊥ := by
    rw [ModuleTower.ker_quotientsπ]
    refine eq_bot_iff.2 (Submodule.smul_le.2 fun r hr x _ ↦ ?_)
    rw [Submodule.mem_bot]
    exact (ModuleCat.restrictScalars.smul_def φ (M := ModuleCat.of S (S ⧸ J)) r x).trans
      (by rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]; rfl)
  let eRed : M ≃ₗ[R] F.obj.obj (op n) :=
    LinearEquiv.ofBijective (ModuleTower.reductionπ I M n)
      ⟨LinearMap.ker_eq_bot.1 hker, ModuleTower.quotientsπ_surjective _ _ n⟩
  obtain ⟨ℱ, ⟨e⟩⟩ := hEss.mem_essImage F
  let eR : (ModuleCat.restrictScalars φ).obj (moduleSpecΓFunctor.obj (ℱ.obj n)) ≅
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (S ⧸ J)) :=
    ((evaluation _ _).obj (op n)).mapIso ((ModuleTower.isFiniteAdicSystem I).ι.mapIso e) ≪≫
      eRed.symm.toModuleIso
  have := φ.full_restrictScalars Ideal.Quotient.mk_surjective
  let eS : moduleSpecΓFunctor.obj (ℱ.obj n) ≅ ModuleCat.of S (S ⧸ J) :=
    (Functor.FullyFaithful.ofFullyFaithful (ModuleCat.restrictScalars φ)).preimageIso eR
  have : Module.FinitePresentation S (moduleSpecΓFunctor.obj (ℱ.obj n)) :=
    @Scheme.Modules.finitePresentation_moduleSpecΓ _ (ℱ.obj n) (ℱ.isFinitePresentation n)
  have : Module.FinitePresentation S (S ⧸ J) := .of_equiv eS.toLinearEquiv
  obtain ⟨s, hs⟩ := Module.FinitePresentation.fg_ker J.mkQ (Submodule.mkQ_surjective J)
  exact ⟨s, hs.trans (Submodule.ker_mkQ J)⟩

/-- When every quotient `R ⧸ I ^ (n + 1)` is Noetherian — in particular when `R` is Noetherian —
taking levelwise global sections identifies coherent formal modules on `spf I` with `I`-adic
systems of `R`-modules having finite first term. -/
instance isEquivalence_finiteSectionsTower (I : Ideal R)
    [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))] :
    (finiteSectionsTower I).IsEquivalence where

/-- When `I` is finitely generated and `R ⧸ I` is Noetherian, taking levelwise global sections
identifies coherent formal modules on `spf I` with finite `I`-adic systems, without global
Noetherianity or `I`-adic completeness assumptions on `R`. -/
theorem isEquivalence_finiteSectionsTower_of_fg (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] :
    (finiteSectionsTower I).IsEquivalence :=
  have : ∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1)) := fun n ↦
    Ideal.isNoetherianRing_quotient_pow_of_fg I hI (n + 1)
  inferInstance

/-- Taking levelwise global sections identifies coherent formal modules on `spf I` with finite
`I`-adic systems if and only if every quotient `R ⧸ I ^ (n + 1)` is Noetherian. -/
theorem isEquivalence_finiteSectionsTower_iff (I : Ideal R) :
    (finiteSectionsTower I).IsEquivalence ↔ ∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1)) :=
  ⟨fun h ↦ have := h; (essSurj_finiteSectionsTower_iff I).1 inferInstance,
    fun h ↦ @isEquivalence_finiteSectionsTower _ _ I h⟩

/-! ### Failure of essential surjectivity without Noetherianity -/

/-- **Essential surjectivity of `finiteSectionsTower` fails without Noetherianity.** Over the
infinite-variable polynomial ring `k[x₀, x₁, …]` (`k` nontrivial), `k[x₀, x₁, …]` is not Noetherian
(the ideal `(x₀, x₁, …)` is not finitely generated), so `finiteSectionsTower ⊥` fails to be
essentially surjective by `essSurj_finiteSectionsTower_iff`. -/
theorem not_essSurj_finiteSectionsTower_mvPolynomial (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ (finiteSectionsTower (⊥ : Ideal (MvPolynomial ℕ k))).EssSurj := fun hEss ↦ by
  have : IsNoetherianRing (MvPolynomial ℕ k ⧸ (⊥ : Ideal (MvPolynomial ℕ k)) ^ 1) :=
    (essSurj_finiteSectionsTower_iff (⊥ : Ideal (MvPolynomial ℕ k))).1 hEss 0
  have : IsNoetherianRing (MvPolynomial ℕ k) := isNoetherianRing_of_ringEquiv _
    ((Ideal.quotEquivOfEq (pow_one (⊥ : Ideal (MvPolynomial ℕ k)))).trans
      (RingEquiv.quotientBot (MvPolynomial ℕ k)))
  exact MvPolynomial.not_isNoetherianRing ℕ k inferInstance

/-! ### Inverse-limit sections, completion on `spf I`, and Tag 087W -/

/-- The inverse limit `lim Γ(M n)` of the levelwise global sections of a coherent formal module on
`spf I`. -/
def sectionsLim (I : Ideal R) : CoherentFormalModule (spf I) ⥤ ModuleCat.{u} R :=
  sectionsTower I ⋙ ModuleTower.limFunctor R

instance (I : Ideal R) : (sectionsLim I).Additive :=
  inferInstanceAs (sectionsTower I ⋙ ModuleTower.limFunctor R).Additive

/-- Over an `I`-adically precomplete ring, the inverse limit `lim Γ(M n)` of a coherent formal
module on `spf I` as a finite `R`-module (`ModuleTower.finiteLim`). -/
def finiteSectionsLim (I : Ideal R) [IsPrecomplete I R] :
    CoherentFormalModule (spf I) ⥤ FGModuleCat.{u} R :=
  finiteSectionsTower I ⋙ ModuleTower.finiteLim I

instance (I : Ideal R) [IsPrecomplete I R] : (finiteSectionsLim I).Additive :=
  inferInstanceAs (finiteSectionsTower I ⋙ ModuleTower.finiteLim I).Additive

/-- **Coherent formal modules on `spf I` over a complete Noetherian ring** (Stacks, Lemma 30.23.1):
for an `I`-adically complete Noetherian ring `R`, coherent formal modules on `spf I` are equivalent
to finite `R`-modules via finite `I`-adic systems, with inverse functor `finiteSectionsLim I` taking
the inverse limit of levelwise global sections. -/
@[stacks 087W]
def spfEquiv (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] :
    FGModuleCat.{u} R ≌ CoherentFormalModule (spf I) :=
  (ModuleTower.finiteReductionEquiv I).trans (finiteSectionsTower I).asEquivalence.symm

@[simp]
theorem spfEquiv_inverse (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] :
    (spfEquiv I).inverse = finiteSectionsLim I := by
  simp [spfEquiv, finiteSectionsLim]

end

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

namespace TauCeti.AlgebraicGeometry.Spf

open AdicThickeningSystem

/-- **Coherent formal modules on `Spf A`** (Stacks, Lemma 30.23.1): for a Noetherian adic ring `A`,
coherent formal modules on `Spf A` are equivalent to finite `A`-modules via finite `I`-adic systems
and inverse-limit global sections. -/
@[stacks 087W]
noncomputable def coherentFormalModuleEquiv (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    FGModuleCat.{u} A.carrier ≌ CoherentFormalModule (Spf A) :=
  CoherentFormalModule.spfEquiv A.ideal

@[simp]
theorem coherentFormalModuleEquiv_inverse (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    (coherentFormalModuleEquiv A).inverse =
      CoherentFormalModule.finiteSectionsLim A.ideal :=
  CoherentFormalModule.spfEquiv_inverse A.ideal

end TauCeti.AlgebraicGeometry.Spf

