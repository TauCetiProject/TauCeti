/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.GlobalSections
public import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic

/-!
# Global sections of coherent formal modules on `spf I`

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
`spf I` are exactly the morphisms of these towers: global sections identify quasi-coherent modules
on an affine scheme with modules over its ring, and a family of linear maps compatible with the
transitions of the towers is compatible with the reduction isomorphisms. Thus
`finiteSectionsTower I` is a fully faithful functor from coherent formal modules on `spf I` to the
`I`-adic systems with finite first term, for any commutative ring `R`.

Over a noetherian ring it is moreover essentially surjective, hence an equivalence (Stacks,
Lemma 30.23.1). The `n`-th term `Mₙ` of an `I`-adic system with `M₀` finite is a finite, hence
finitely presented, module over `R ⧸ I ^ (n + 1)`, and the pullback of the associated sheaf `Mₙ₊₁~`
to `Spec (R ⧸ I ^ (n + 1))` is the sheaf associated with `Mₙ₊₁ ⧸ I ^ (n + 1) Mₙ₊₁ ≅ Mₙ`, so the
sheaves `Mₙ~` form a coherent formal module with tower of sections `(Mₙ)`. When `R` is moreover
`I`-adically complete, finite `I`-adic systems are the reductions of finite `R`-modules
(`TauCeti.ModuleTower.finiteReduction_isEquivalence`), so for a noetherian adic ring `A` the
coherent formal modules on `Spf A` are equivalent to the finite `A`-modules
(`spfEquivFGModuleCat`). Applied to the completion `Â` of a noetherian ring along an
ideal, this describes the coherent formal modules on `Spf Â`.

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsTower`: the tower
  of global sections of the levels of a coherent formal module on `spf I`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.finiteSectionsTower`: the
  same functor, valued in `I`-adic systems with finite first term.
* `CoherentFormalModule.spfEquivFGModuleCat`: for an adic ring `A` with noetherian
  underlying ring, the equivalence between coherent formal modules on `Spf A` and finite
  `A`-modules, with `spfEquivFGModuleCatFunctorCompFiniteReductionIso` identifying the
  tower of sections with the reduction of the corresponding module.

## Main results

* `CoherentFormalModule.isFiniteAdicSystem_sectionsTower_obj`: the tower of global sections is an
  `I`-adic system with finite first term.
* `CoherentFormalModule.sectionsTower` is full and faithful.
* `CoherentFormalModule.finiteSectionsTower` is an equivalence when `R` is noetherian.

## References

* [Stacks Project, Lemma 30.23.1](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open scoped ChangeOfRings

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

/-- Taking the tower of global sections is additive. -/
instance : (sectionsTower I).Additive where
  map_add {M N f g} := by
    ext ⟨n⟩ : 2
    have : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I ^ (n + 1)))).Additive :=
      (moduleSpecΓFunctor (R := _)).additive_of_preserves_binary_products
    exact (congrArg (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).map
      (moduleSpecΓFunctor.map_add (f := f.app n) (g := g.app n))).trans
        (Functor.map_add _)

/-- The tower of global sections of a coherent formal module on `spf I`, as an `I`-adic system with
finite first term (`isFiniteAdicSystem_sectionsTower_obj`). It is fully faithful. -/
-- `@[expose]` is forced by dependent typing, as for `ModuleTower.finiteReduction`: the morphisms
-- in `finiteSectionsTower_map_hom` are morphisms of towers only because the underlying towers of
-- `finiteSectionsTower I` reduce definitionally to those of `sectionsTower I`.
@[expose, simps! obj_obj map_hom]
def finiteSectionsTower : CoherentFormalModule (spf I) ⥤ ModuleTower.FiniteAdicSystem.{u} I :=
  (ModuleTower.isFiniteAdicSystem I).lift (sectionsTower I) (isFiniteAdicSystem_sectionsTower_obj I)

/-- Taking global sections valued in finite adic systems is additive. -/
instance : (finiteSectionsTower I).Additive :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Additive

instance : (finiteSectionsTower I).Full :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Full

instance : (finiteSectionsTower I).Faithful :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Faithful

/-! ### Finite adic systems are towers of sections

Let `(Mₙ)` be an `I`-adic system with `M₀` finite over a noetherian ring `R`. Each `Mₙ` is killed by
`I ^ (n + 1)`, so it is a finite, hence finitely presented, module over `R ⧸ I ^ (n + 1)`, and its
associated sheaf `Mₙ~` is a finitely presented module on `Spec (R ⧸ I ^ (n + 1))`. The pullback of
`Mₙ₊₁~` along `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))` is the sheaf associated with
`(R ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁ = Mₙ₊₁ ⧸ I ^ (n + 1) Mₙ₊₁`, which the transition identifies with `Mₙ`.
These sheaves therefore form a coherent formal module on `spf I` whose tower of global sections is
`(Mₙ)`, so `finiteSectionsTower I` is essentially surjective.
-/

section EssSurj

variable {I} {F : ModuleTower.{u} R} (hF : F.IsAdicSystem I)

open ModuleTower.IsAdicSystem

variable [IsNoetherianRing R] [Module.Finite R (F.obj (op 0))]

/-- The coherent formal module on `spf I` whose `n`-th level is the sheaf associated with the
`n`-th term `Mₙ` of an `I`-adic system with `M₀` finite, over a noetherian ring. Its reduction
isomorphisms are `ι n ^* Mₙ₊₁~ ≅ ((R ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁)~ ≅ Mₙ~`. -/
private def ofAdicSystem : CoherentFormalModule (spf I) where
  obj n := tilde (levelModule hF n)
  isFinitePresentation n :=
    (ModuleCat.isFinitePresentation_tilde_iff (R := CommRingCat.of (R ⧸ I ^ (n + 1))) _).2
      (finitePresentation_levelModule hF n)
  transitionIso n :=
    (tildeFunctorCompPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))))).app (levelModule hF (n + 1)) ≪≫
      have := (ConcreteCategory.isIso_iff_bijective _).2 (levelReduction_bijective hF n)
      (tilde.functor _).mapIso (asIso (levelReduction hF n))

private lemma ofAdicSystem_transitionIso_hom (n : ℕ) :
    ((ofAdicSystem hF).transitionIso n).hom =
      (tildeFunctorCompPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))))).hom.app
          (levelModule hF (n + 1)) ≫ tilde.map (levelReduction hF n) :=
  (rfl)

/-- The term `Mₙ` of the adic system is the module of global sections of the `n`-th level of
`ofAdicSystem hF`, through the unit `M ⟶ Γ(M~)`. -/
private def sectionsIso (n : ℕ) :
    F.obj (op n) ≅ ((sectionsTower I).obj (ofAdicSystem hF)).obj (op n) :=
  letI := (isTorsionBySet_obj hF n).module
  haveI := (isTorsionBySet_obj hF n).isScalarTower (S := R)
  (ModuleCat.restrictScalarsAlgebraMapIso (R := R)
    (S := R ⧸ I ^ (n + 1)) (F.obj (op n))).symm ≪≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapIso
    ((tilde.toTildeΓNatIso (R := CommRingCat.of (R ⧸ I ^ (n + 1)))).app (levelModule hF n))

private lemma sectionsIso_hom_apply (n : ℕ) (x : F.obj (op n)) :
    (sectionsIso hF n).hom.hom x =
      (tilde.toTildeΓNatIso (R := CommRingCat.of (R ⧸ I ^ (n + 1)))).hom.app
        (levelModule hF n) x := by
  let := (isTorsionBySet_obj hF n).module
  have := (isTorsionBySet_obj hF n).isScalarTower (S := R)
  exact (ModuleCat.comp_apply _ _ x).trans <|
    (ModuleCat.restrictScalars.map_apply (Ideal.Quotient.mk (I ^ (n + 1))) _ _).trans <|
      congrArg _ (ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := R)
        (S := R ⧸ I ^ (n + 1)) (F.obj (op n)) x)

/-- The isomorphisms `sectionsIso hF n` are compatible with the transitions. -/
private lemma sectionsTower_ofAdicSystem_transition (n : ℕ) (x : F.obj (op (n + 1))) :
    ((sectionsTower I).obj (ofAdicSystem hF)).transition n ((sectionsIso hF (n + 1)).hom.hom x) =
      (sectionsIso hF n).hom.hom (F.transition n x) := by
  rw [sectionsTower_obj_transition_apply, ofAdicSystem_transitionIso_hom,
    sectionsIso_hom_apply, sectionsIso_hom_apply]
  exact (moduleSpecΓFunctor_map_comp_tilde_map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))) (levelReduction hF n)
      x).trans
    (congrArg ((tilde.toTildeΓNatIso (R := CommRingCat.of (R ⧸ I ^ (n + 1)))).hom.app
      (levelModule hF n)).hom (levelReduction_one_tmul hF n x))

/-- The isomorphism from the adic system to the tower of global sections of `ofAdicSystem hF`. -/
private def sectionsHom : F ⟶ (sectionsTower I).obj (ofAdicSystem hF) :=
  NatTrans.ofOpSequence (fun n ↦ (sectionsIso hF n).hom) fun n ↦ by
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleTower.map_hom_eq_transitionOfLE,
      ModuleTower.transitionOfLE_succ]
    exact (sectionsTower_ofAdicSystem_transition hF n x).symm

private instance : IsIso (sectionsHom hF) :=
  have (n : ℕᵒᵖ) : IsIso ((sectionsHom hF).app n) := (sectionsIso hF n.unop).isIso_hom
  NatIso.isIso_of_isIso_app _

end EssSurj

/-- **Finite adic systems are towers of sections of coherent formal modules.** Over a noetherian
ring `R`, every `I`-adic system `(Mₙ)` with `M₀` finite is the tower of global sections of a
coherent formal module on `spf I`, the system of sheaves `Mₙ~` on `Spec (R ⧸ I ^ (n + 1))`. -/
instance [IsNoetherianRing R] : (finiteSectionsTower I).EssSurj where
  mem_essImage F := by
    obtain ⟨hF, hF₀⟩ := (ModuleTower.isFiniteAdicSystem_iff I _).1 F.property
    exact ⟨ofAdicSystem hF, ⟨ObjectProperty.isoMk _ (asIso (sectionsHom hF)).symm⟩⟩

/-- **Coherent formal modules on `spf I` are finite adic systems** (Stacks, Lemma 30.23.1): over a
noetherian ring `R`, taking global sections levelwise is an equivalence from coherent formal modules
on `spf I` to `I`-adic systems of `R`-modules with finite first term. -/
@[stacks 087W]
instance [IsNoetherianRing R] : (finiteSectionsTower I).IsEquivalence where

end

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

/-! ### Coherent formal modules on the formal spectrum of a noetherian adic ring -/

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

open AdicThickeningSystem

/-- **Coherent formal modules on `Spf A` are finite `A`-modules** (Stacks, Lemma 30.23.1): for an
adic ring `A` whose underlying ring is noetherian, the coherent formal modules on `Spf A` are
equivalent to the finite `A`-modules. A coherent formal module `(Mₙ)` corresponds to a finite
module `M` whose reductions `M ⧸ I ^ (n + 1) M` are the global sections `Γ(Mₙ)`
(`spfEquivFGModuleCatFunctorCompFiniteReductionIso`). For the `I`-adic completion `Â` of a
noetherian ring along an ideal `I`, this identifies coherent formal modules on `Spf Â` with finite
`Â`-modules. -/
-- The forward module must reduce to the limit in the type of the projection formula below.
@[expose, stacks 087W]
noncomputable def spfEquivFGModuleCat (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    CoherentFormalModule (Spf A) ≌ FGModuleCat.{u} A.carrier :=
  (CoherentFormalModule.finiteSectionsTower A.ideal).asEquivalence.trans
    (ModuleTower.finiteReductionEquiv A.ideal).symm

/-- Under `spfEquivFGModuleCat A`, the tower of global sections of a coherent formal
module on `Spf A` is the reduction `(M ⧸ I ^ (n + 1) M)ₙ` of the corresponding finite `A`-module
`M`. -/
noncomputable def spfEquivFGModuleCatFunctorCompFiniteReductionIso (A : AdicRing.{u})
    [IsNoetherianRing A.carrier] :
    (spfEquivFGModuleCat A).functor ⋙ ModuleTower.finiteReduction A.ideal ≅
      CoherentFormalModule.finiteSectionsTower A.ideal :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleTower.finiteReductionEquiv A.ideal).counitIso ≪≫
      Functor.rightUnitor _

/-- The equivalence takes the inverse limit of the tower of global sections. -/
@[simp]
theorem spfEquivFGModuleCat_functor (A : AdicRing.{u})
    [IsNoetherianRing A.carrier] :
    (spfEquivFGModuleCat A).functor =
      CoherentFormalModule.finiteSectionsTower A.ideal ⋙ ModuleTower.finiteLim A.ideal := (rfl)

/-- The reductions-to-sections comparison is induced by the projections from the inverse limit. -/
@[simp]
theorem spfEquivFGModuleCatFunctorCompFiniteReductionIso_hom_app_reductionπ
    (A : AdicRing.{u}) [IsNoetherianRing A.carrier] (M : CoherentFormalModule (Spf A))
    (n : ℕ) (x : ((CoherentFormalModule.sectionsTower A.ideal).obj M).lim) :
    dsimp% only [CategoryTheory.Functor.comp_obj, CategoryTheory.ObjectProperty.ι_obj,
      FGModuleCat.obj_carrier]
    (((spfEquivFGModuleCatFunctorCompFiniteReductionIso A).hom.app M).hom.app
      (op n)).hom (ModuleTower.reductionπ A.ideal _ n x) =
        ((CoherentFormalModule.sectionsTower A.ideal).obj M).limπ n x := by
  exact ModuleTower.finiteReductionEquiv_counitIso_hom_app_reductionπ A.ideal
    ((finiteSectionsTower A.ideal).obj M) n x

/-- The inverse equivalence associates to a finite module a coherent formal module whose
sections are its reductions. -/
noncomputable def spfEquivFGModuleCatInverseCompFiniteSectionsTowerIso
    (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    (spfEquivFGModuleCat A).inverse ⋙
      CoherentFormalModule.finiteSectionsTower A.ideal ≅ ModuleTower.finiteReduction A.ideal :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (CoherentFormalModule.finiteSectionsTower A.ideal).asEquivalence.counitIso ≪≫
      Functor.rightUnitor _

/-- The equivalence with finite modules preserves addition of morphisms. -/
instance (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    (spfEquivFGModuleCat A).functor.Additive := by
  exact inferInstanceAs (CoherentFormalModule.finiteSectionsTower A.ideal ⋙
    ModuleTower.finiteLim A.ideal).Additive

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
