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
`I`-adic systems with finite first term, for any commutative ring `R`. This is one ingredient of
Stacks, Lemma 30.23.1, which identifies coherent formal modules on `Spf` of an `I`-adically complete
Noetherian ring with its finite modules: that equivalence also needs `finiteSectionsTower I` to be
essentially surjective for Noetherian `R`, and that finite `I`-adic systems are the finite modules
(`TauCeti.ModuleTower.finiteReduction_isEquivalence`).

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsTower`: the tower
  of global sections of the levels of a coherent formal module on `spf I`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.finiteSectionsTower`: the
  same functor, valued in `I`-adic systems with finite first term.

## Main results

* `CoherentFormalModule.isFiniteAdicSystem_sectionsTower_obj`: the tower of global sections is an
  `I`-adic system with finite first term.
* `CoherentFormalModule.sectionsTower` is full and faithful.

## References

* [Stacks Project, Lemma 30.23.1](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
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

/-- The tower of global sections of a coherent formal module on `spf I`, as an `I`-adic system with
finite first term (`isFiniteAdicSystem_sectionsTower_obj`). It is fully faithful. -/
-- `@[expose]` is forced by dependent typing, as for `ModuleTower.finiteReduction`: the morphisms
-- in `finiteSectionsTower_map_hom` are morphisms of towers only because the underlying towers of
-- `finiteSectionsTower I` reduce definitionally to those of `sectionsTower I`.
@[expose, simps! obj_obj map_hom]
def finiteSectionsTower : CoherentFormalModule (spf I) ⥤ ModuleTower.FiniteAdicSystem.{u} I :=
  (ModuleTower.isFiniteAdicSystem I).lift (sectionsTower I) (isFiniteAdicSystem_sectionsTower_obj I)

instance : (finiteSectionsTower I).Full :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Full

instance : (finiteSectionsTower I).Faithful :=
  inferInstanceAs ((ModuleTower.isFiniteAdicSystem I).lift _ _).Faithful

end

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
