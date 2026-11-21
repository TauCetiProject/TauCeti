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
`spf I` are exactly the morphisms of these towers: global sections identify quasi-coherent modules
on an affine scheme with modules over its ring, and a family of linear maps compatible with the
transitions of the towers is compatible with the reduction isomorphisms. Thus
`finiteSectionsTower I` is an additive, fully faithful functor from coherent formal modules on
`spf I` to `I`-adic systems with finite first term, for any commutative ring `R`.

When every quotient `R ⧸ I ^ (n + 1)` is Noetherian — in particular when `I` is finitely generated
and `R ⧸ I` is Noetherian (`essSurj_finiteSectionsTower_of_fg`), or when `R` is Noetherian — every
finite `I`-adic system `(Mₙ)` arises in this way: `Mₙ` is a finite, hence finitely presented,
module over `R ⧸ I ^ (n + 1)`, and the pullback of the associated sheaf `Mₙ₊₁~` to
`Spec (R ⧸ I ^ (n + 1))` is the sheaf associated with `Mₙ₊₁ ⧸ I ^ (n + 1) Mₙ₊₁ ≅ Mₙ`, so the
sheaves `Mₙ~` form a coherent formal module with tower of sections `(Mₙ)`
(`essSurj_finiteSectionsTower`). Conversely, essential surjectivity of `finiteSectionsTower I`
forces every `R ⧸ I ^ (n + 1)` to be Noetherian (`essSurj_finiteSectionsTower_iff`,
`isEquivalence_finiteSectionsTower_iff`). Consequently, without Noetherianity essential surjectivity
fails even for `I = ⊥`: over `k[x₀, x₁, …]` (`k` nontrivial), `finiteSectionsTower ⊥` is not
essentially surjective (`not_essSurj_finiteSectionsTower_mvPolynomial`).

When `R` is moreover `I`-adically complete and Noetherian, finite `I`-adic systems are the
reductions of finite `R`-modules (`TauCeti.ModuleTower.finiteReductionEquiv`), giving the
equivalence `CoherentFormalModule.spfEquivFGModuleCat` for a Noetherian adic ring `A` (`Spf A`)
(Stacks, Lemma 30.23.1). Applied to the completion `Â` of a Noetherian ring along an ideal, this
describes the coherent formal modules on `Spf Â`.

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsTower`: the tower
  of global sections of the levels of a coherent formal module on `spf I`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.finiteSectionsTower`: the
  same functor, valued in `I`-adic systems with finite first term.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.sectionsLim`,
  `finiteSectionsLim`: the inverse limit `lim Γ(M n)` of levelwise global sections.
* `CoherentFormalModule.spfEquivFGModuleCat`: for an adic ring `A` with noetherian
  underlying ring, the equivalence between coherent formal modules on `Spf A` and finite
  `A`-modules, with `spfEquivFGModuleCatFunctorCompFiniteReductionIso` identifying the
  tower of sections with the reduction of the corresponding module.

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
finite first term (`isFiniteAdicSystem_sectionsTower_obj`). It is additive and fully faithful, and
is an equivalence if and only if every quotient `R ⧸ I ^ (n + 1)` is Noetherian
(`isEquivalence_finiteSectionsTower`, `isEquivalence_finiteSectionsTower_iff`). -/
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

variable [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))] [Module.Finite R (F.obj (op 0))]

/-- The coherent formal module on `spf I` whose `n`-th level is the sheaf associated with the
`n`-th term `Mₙ` of an `I`-adic system with `M₀` finite, when `R ⧸ I ^ (n + 1)` is noetherian.
Its reduction isomorphisms are `ι n ^* Mₙ₊₁~ ≅ ((R ⧸ I ^ (n + 1)) ⊗ Mₙ₊₁)~ ≅ Mₙ~`. -/
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

/-- When every quotient `R ⧸ I ^ (n + 1)` is Noetherian — in particular when `R` is Noetherian —
every `I`-adic system with finite first term is the global-sections tower of a coherent formal
module on `spf I`. No `I`-adic completeness assumption on `R` is needed. -/
instance essSurj_finiteSectionsTower [∀ n, IsNoetherianRing (R ⧸ I ^ (n + 1))] :
    (finiteSectionsTower I).EssSurj where
  mem_essImage F := by
    obtain ⟨hF, hF₀⟩ := (ModuleTower.isFiniteAdicSystem_iff I _).1 F.property
    exact ⟨ofAdicSystem hF, ⟨ObjectProperty.isoMk _ (asIso (sectionsHom hF)).symm⟩⟩

end

noncomputable section

variable {R : Type u} [CommRing R]

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
-- `@[expose]` is forced by dependent typing: `sectionsLim_map` and `limπ_sectionsLim_map` need
-- `(sectionsLim I).obj M` to reduce to `ModuleCat.of R ((sectionsTower I).obj M).lim`.
@[expose]
def sectionsLim (I : Ideal R) : CoherentFormalModule (spf I) ⥤ ModuleCat.{u} R :=
  sectionsTower I ⋙ ModuleTower.limFunctor R

instance (I : Ideal R) : (sectionsLim I).Additive :=
  inferInstanceAs (sectionsTower I ⋙ ModuleTower.limFunctor R).Additive

/-- `sectionsLim I` is the composition of `sectionsTower I` with `ModuleTower.limFunctor R`. -/
theorem sectionsLim_eq (I : Ideal R) :
    sectionsLim I = sectionsTower I ⋙ ModuleTower.limFunctor R :=
  (rfl)

/-- On objects, `sectionsLim I` sends `M` to the inverse limit of `(sectionsTower I).obj M`. -/
@[simp]
theorem sectionsLim_obj (I : Ideal R) (M : CoherentFormalModule (spf I)) :
    (sectionsLim I).obj M = ModuleCat.of R ((sectionsTower I).obj M).lim :=
  (rfl)

/-- On morphisms, `sectionsLim I` sends `f` to the induced map on inverse limits. -/
@[simp]
theorem sectionsLim_map (I : Ideal R) {M N : CoherentFormalModule (spf I)} (f : M ⟶ N) :
    (sectionsLim I).map f =
      ModuleCat.ofHom (TauCeti.ModuleTower.limMap ((sectionsTower I).map f)) :=
  (rfl)

/-- The `n`-th projection of `(sectionsLim I).map f` is global sections of `f.app n`. -/
theorem limπ_sectionsLim_map (I : Ideal R) {M N : CoherentFormalModule (spf I)} (f : M ⟶ N)
    (n : ℕ) (x : (sectionsLim I).obj M) :
    ((sectionsTower I).obj N).limπ n ((sectionsLim I).map f x) =
      moduleSpecΓFunctor.map (f.app n) (((sectionsTower I).obj M).limπ n x) :=
  LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap ((sectionsTower I).map f) n) x

/-- Over an `I`-adically precomplete ring, the inverse limit `lim Γ(M n)` of a coherent formal
module on `spf I` as a finite `R`-module (`ModuleTower.finiteLim`). -/
-- `@[expose]` is forced by dependent typing: `finiteSectionsLim_map_hom` needs
-- `((finiteSectionsLim I).obj M).obj` to reduce to `ModuleCat.of R ((sectionsTower I).obj M).lim`.
@[expose]
def finiteSectionsLim (I : Ideal R) [IsPrecomplete I R] :
    CoherentFormalModule (spf I) ⥤ FGModuleCat.{u} R :=
  finiteSectionsTower I ⋙ ModuleTower.finiteLim I

instance (I : Ideal R) [IsPrecomplete I R] : (finiteSectionsLim I).Additive :=
  inferInstanceAs (finiteSectionsTower I ⋙ ModuleTower.finiteLim I).Additive

/-- `finiteSectionsLim I` is the composition of `finiteSectionsTower I` with
`ModuleTower.finiteLim I`. -/
theorem finiteSectionsLim_eq (I : Ideal R) [IsPrecomplete I R] :
    finiteSectionsLim I = finiteSectionsTower I ⋙ ModuleTower.finiteLim I :=
  (rfl)

/-- On objects, the underlying module of `(finiteSectionsLim I).obj M` is the inverse limit of
`(sectionsTower I).obj M`. -/
@[simp]
theorem finiteSectionsLim_obj_obj (I : Ideal R) [IsPrecomplete I R]
    (M : CoherentFormalModule (spf I)) :
    ((finiteSectionsLim I).obj M).obj = ModuleCat.of R ((sectionsTower I).obj M).lim :=
  (rfl)

/-- On morphisms, the underlying `ModuleCat` morphism of `(finiteSectionsLim I).map f` is
`ModuleTower.limMap ((sectionsTower I).map f)`. -/
@[simp]
theorem finiteSectionsLim_map_hom (I : Ideal R) [IsPrecomplete I R]
    {M N : CoherentFormalModule (spf I)} (f : M ⟶ N) :
    ((finiteSectionsLim I).map f).hom =
      ModuleCat.ofHom (TauCeti.ModuleTower.limMap ((sectionsTower I).map f)) :=
  (rfl)

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
    (spfEquivFGModuleCat A).functor = CoherentFormalModule.finiteSectionsLim A.ideal :=
  (rfl)

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
    (spfEquivFGModuleCat A).functor.Additive :=
  inferInstanceAs (CoherentFormalModule.finiteSectionsLim A.ideal).Additive

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
