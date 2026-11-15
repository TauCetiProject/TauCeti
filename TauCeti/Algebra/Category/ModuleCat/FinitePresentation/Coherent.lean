/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.WeakKernels
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.CategoryTheory.Preadditive.Progenerator
public import TauCeti.RingTheory.Coherent.Basic

import TauCeti.Algebra.Module.FinitePresentation

/-!
# Coherence and the category of finitely presented modules

Over any ring `R`, the object property `TauCeti.finitePresentationModules R` of finitely presented
`R`-modules contains the zero module and is closed under finite products, cokernels and retracts.
Its inclusion into `ModuleCat R` therefore preserves epimorphisms, every finitely generated
projective `R`-module is projective in the full subcategory of finitely presented `R`-modules, and
the regular module `R` is a progenerator of that subcategory.

Closing the finitely presented `R`-modules under kernels requires a condition on `R`. By Chase's
theorem, the following properties of `R` are equivalent (`TauCeti.isCoherentRing_tfae`):

* `R` is left coherent (`TauCeti.IsCoherentRing R`), i.e., every finitely generated left ideal of
  `R` is finitely presented;
* `TauCeti.finitePresentationModules R` is closed under kernels in `ModuleCat R`;
* the full subcategory of finitely presented `R`-modules is abelian;
* the full subcategory of finitely presented `R`-modules has kernels;
* the category `proj R` (`(TauCeti.finiteProjectiveModules R).FullSubcategory`) of finitely
  generated projective `R`-modules has weak kernels;
* the category `mod (proj R)` of finitely presented functors on `proj R` is closed under kernels in
  the functor category.

In particular, when `[TauCeti.IsCoherentRing R]` holds,
`(finitePresentationModules R).FullSubcategory` is automatically an abelian category whose kernels
and cokernels are computed in `ModuleCat R`, and `(finiteProjectiveModules R).FullSubcategory` has
weak kernels. Over a left Noetherian ring, finite presentation coincides with finite generation
(`TauCeti.finitePresentationModules_eq_finiteModules`).

## Main definitions

* `TauCeti.finitePresentationModulesRegular`: the regular module `R` as an object of
  `(finitePresentationModules R).FullSubcategory`.

## Main results

* `TauCeti.isProgenerator_finitePresentationModulesRegular`: the regular module `R` is a
  progenerator of `(finitePresentationModules R).FullSubcategory` over every ring `R`.
* `TauCeti.isCoherentRing_tfae`: the six-way equivalence between left coherence of `R`, closure of
  `finitePresentationModules R` under kernels, `Abelian` and `HasKernels` on
  `(finitePresentationModules R).FullSubcategory`, `HasWeakKernels` on `proj R`, and closure of
  `mod (proj R)` under kernels.
* `TauCeti.hasWeakKernels_finiteProjectiveModules_iff_isCoherentRing`,
  `TauCeti.isClosedUnderKernels_finitePresentationModules_iff_isCoherentRing`, and
  `TauCeti.nonempty_abelian_finitePresentationModules_iff_isCoherentRing`: pairwise equivalences.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), 457–473.
* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer (1966), 189–231.
* N. Bourbaki, *Algèbre Commutative*, Ch. I, §2, Exercise 12.
* [The Stacks Project, Section 10.90, Tag 05CU](https://stacks.math.columbia.edu/tag/05CU).
-/

public section

universe u

open CategoryTheory Limits
open scoped ZeroObject

namespace TauCeti

variable (R : Type u) [Ring R]

/-! ### Unconditional closure properties of `finitePresentationModules` -/

/-- The underlying module of an object in `(finitePresentationModules R).FullSubcategory` is
finitely presented. -/
instance (X : (finitePresentationModules R).FullSubcategory) :
    Module.FinitePresentation R X.obj :=
  finitePresentationModules_iff.mp X.property

/-- Every finitely generated projective `R`-module is finitely presented. -/
theorem finiteProjectiveModules_le_finitePresentationModules :
    finiteProjectiveModules R ≤ finitePresentationModules R := fun M hM ↦ by
  obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp hM
  exact finitePresentationModules_iff.mpr (Module.finitePresentation_of_projective R M)

/-- Every finitely presented `R`-module is finitely generated. -/
theorem finitePresentationModules_le_finiteModules :
    finitePresentationModules R ≤ ModuleCat.isFG R := fun M hM ↦ by
  have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
  exact (ModuleCat.isFG_iff M).mpr inferInstance

/-- Over a left Noetherian ring, finite presentation agrees with finite generation. -/
theorem finitePresentationModules_eq_finiteModules [IsNoetherianRing R] :
    finitePresentationModules R = ModuleCat.isFG R :=
  le_antisymm (finitePresentationModules_le_finiteModules R) fun M hM ↦ by
    have : Module.Finite R M := (ModuleCat.isFG_iff M).mp hM
    exact finitePresentationModules_iff.mpr (Module.finitePresentation_of_finite R M)

/-- The zero `R`-module is finitely presented. -/
instance : (finitePresentationModules R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    finitePresentationModules_iff.mpr inferInstance⟩

/-- Finitely presented `R`-modules are closed under binary products. -/
instance : (finitePresentationModules R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    exact finitePresentationModules_iff.mpr
      (Module.FinitePresentation.of_equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm)

/-- Finitely presented `R`-modules are closed under finite products. -/
instance : (finitePresentationModules R).IsClosedUnderFiniteProducts :=
  .mk'

/-- Finitely presented `R`-modules are closed under cokernels in `ModuleCat R`: the cokernel of
`f : M ⟶ N` is the quotient of `N` by the finitely generated submodule `LinearMap.range f.hom`. -/
instance : (finitePresentationModules R).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ @⟨M, N, f, c, hc, hM, hN⟩
    have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    have hQ : Module.FinitePresentation R (N ⧸ LinearMap.range f.hom) :=
      Module.FinitePresentation.quotient (Submodule.fg_range f.hom)
    let e : c.pt ≅ ModuleCat.of R (N ⧸ LinearMap.range f.hom) :=
      hc.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit f)
    exact (finitePresentationModules R).prop_of_iso e.symm (finitePresentationModules_iff.mpr hQ)

/-- Finitely presented `R`-modules are stable under retracts: if `i ≫ r = 𝟙 M`, then `r` is
surjective with kernel `LinearMap.range (1 - i ∘ r)`, which is finitely generated when `N` is. -/
instance : (finitePresentationModules R).IsStableUnderRetracts where
  of_retract {M N} h hN := by
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    have hcomp : h.r.hom ∘ₗ h.i.hom = LinearMap.id := congrArg ModuleCat.Hom.hom h.retract
    refine finitePresentationModules_iff.mpr
      (Module.finitePresentation_of_surjective h.r.hom
        (LinearMap.surjective_of_comp_eq_id h.i.hom h.r.hom hcomp) ?_)
    rw [LinearMap.ker_eq_range_of_comp_eq_id hcomp]
    exact Submodule.fg_range _

/-! ### The regular module as a progenerator of finitely presented modules -/

/-- Because `finitePresentationModules R` contains zero and is closed under cokernels, its
inclusion into `ModuleCat R` preserves epimorphisms. -/
instance : (finitePresentationModules R).ι.PreservesEpimorphisms :=
  (finitePresentationModules R).preservesEpimorphisms_ι_of_isNormalMonoCategory

/-- Any finitely presented `R`-module that is projective as an `R`-module is a projective object of
`(finitePresentationModules R).FullSubcategory`. -/
theorem projective_finitePresentationModules_of_projective
    (P : (finitePresentationModules R).FullSubcategory) [Module.Projective R P.obj] :
    Projective P where
  factors {E Z} f e _ := by
    have : Epi e.hom := inferInstanceAs (Epi ((finitePresentationModules R).ι.map e))
    exact ⟨ObjectProperty.homMk (Projective.factorThru f.hom e.hom),
      ObjectProperty.hom_ext _ (Projective.factorThru_comp f.hom e.hom)⟩

/-- The regular module `R`, viewed as an object of `(finitePresentationModules R).FullSubcategory`.
-/
@[expose] def finitePresentationModulesRegular : (finitePresentationModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finitePresentationModules_iff.mpr
    (inferInstanceAs (Module.FinitePresentation R R))⟩

@[simp]
theorem finitePresentationModulesRegular_obj :
    (finitePresentationModulesRegular R).obj = ModuleCat.of R R :=
  (rfl)

instance : Projective (finitePresentationModulesRegular R) :=
  have : Module.Projective R (finitePresentationModulesRegular R).obj :=
    inferInstanceAs (Module.Projective R R)
  projective_finitePresentationModules_of_projective R (finitePresentationModulesRegular R)

/-- Over any ring `R`, the regular module `R` is a progenerator of the category of finitely
presented `R`-modules. -/
theorem isProgenerator_finitePresentationModulesRegular :
    IsProgenerator (finitePresentationModulesRegular R) where
  exists_epi_biproduct X := by
    obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R X.obj
    let B : (finitePresentationModules R).FullSubcategory :=
      ⨁ fun _ : Fin n ↦ finitePresentationModulesRegular R
    let eB : B.obj ≅ ModuleCat.of R (Fin n → R) :=
      ((finitePresentationModules R).ι.mapBiproduct
        (fun _ : Fin n ↦ finitePresentationModulesRegular R)) ≪≫
        ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)
    have : Epi (ModuleCat.ofHom q : ModuleCat.of R (Fin n → R) ⟶ X.obj) :=
      (ModuleCat.epi_iff_surjective _).mpr hq
    have : Epi (eB.hom ≫ ModuleCat.ofHom q) := epi_comp _ _
    refine ⟨n, ObjectProperty.homMk (eB.hom ≫ ModuleCat.ofHom q), ?_⟩
    exact (finitePresentationModules R).ι.epi_of_epi_map ‹_›

/-! ### Chase's coherence theorem -/

/-- Over a left coherent ring `R`, finitely presented `R`-modules are closed under kernels in
`ModuleCat R`. Combined with `ContainsZero`, `IsClosedUnderCokernels` and
`IsClosedUnderFiniteProducts`, this makes `(finitePresentationModules R).FullSubcategory` abelian.
-/
instance [IsCoherentRing R] : (finitePresentationModules R).IsClosedUnderKernels where
  kernels_le := by
    rintro _ @⟨M, N, f, c, hc, hM, hN⟩
    have : Module.FinitePresentation R M := finitePresentationModules_iff.mp hM
    have : Module.FinitePresentation R N := finitePresentationModules_iff.mp hN
    have : Module.IsCoherent R M := IsCoherentRing.isCoherent_of_finitePresentation
    have : Module.IsCoherent R N := IsCoherentRing.isCoherent_of_finitePresentation
    have hK : Module.FinitePresentation R (LinearMap.ker f.hom) :=
      Module.IsCoherent.toFinitePresentation
    let e : c.pt ≅ ModuleCat.of R (LinearMap.ker f.hom) :=
      hc.conePointUniqueUpToIso (ModuleCat.kernelIsLimit f)
    exact (finitePresentationModules R).prop_of_iso e.symm (finitePresentationModules_iff.mpr hK)

/-- If the full subcategory of finitely presented `R`-modules has kernels (not assumed to be
preserved by the inclusion into `ModuleCat R`), then `proj R` has weak kernels: choosing a finite
free cover of the kernel in `(finitePresentationModules R).FullSubcategory` lifts morphisms from
projective modules. -/
theorem hasWeakKernels_finiteProjectiveModules_of_hasKernels
    [HasKernels (finitePresentationModules R).FullSubcategory] :
    HasWeakKernels (finiteProjectiveModules R).FullSubcategory where
  hasWeakLimit {P Q} f := by
    let ι := ObjectProperty.ιOfLE (finiteProjectiveModules_le_finitePresentationModules R)
    let f' := ι.map f
    let K := kernel f'
    obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R K.obj
    let F : (finiteProjectiveModules R).FullSubcategory :=
      ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩
    let w : F ⟶ P := ObjectProperty.homMk (ModuleCat.ofHom q ≫ (kernel.ι f').hom)
    have hwf : w ≫ f = 0 := ObjectProperty.hom_ext _ <| by
      -- Unfold composition in the full subcategory to `ModuleCat R`.
      change (ModuleCat.ofHom q ≫ (kernel.ι f').hom) ≫ f.hom = 0
      rw [Category.assoc]
      exact (congrArg (ModuleCat.ofHom q ≫ ·) congr($(kernel.condition f').hom)).trans
        Limits.comp_zero
    refine HasWeakLimit.mk ⟨KernelFork.ofι w hwf, Fork.IsWeakLimit.mk' _ fun s ↦ ?_⟩
    have hs : ι.map s.ι ≫ f' = 0 := by
      rw [← ι.map_comp, KernelFork.condition, ι.map_zero]
    let u : ι.obj s.pt ⟶ K := kernel.lift f' (ι.map s.ι) hs
    have hu : u.hom ≫ (kernel.ι f').hom = s.ι.hom := congr($(kernel.lift_ι f' (ι.map s.ι) hs).hom)
    have : Epi (ModuleCat.ofHom q : F.obj ⟶ K.obj) := (ModuleCat.epi_iff_surjective _).mpr hq
    let v : s.pt.obj ⟶ F.obj := Projective.factorThru u.hom (ModuleCat.ofHom q)
    refine ⟨ObjectProperty.homMk v, ObjectProperty.hom_ext _ ?_⟩
    -- Unfold composition in the full subcategory to `ModuleCat R`.
    change v ≫ ModuleCat.ofHom q ≫ (kernel.ι f').hom = s.ι.hom
    rw [← Category.assoc, Projective.factorThru_comp, hu]

instance [IsCoherentRing R] : HasWeakKernels (finiteProjectiveModules R).FullSubcategory :=
  hasWeakKernels_finiteProjectiveModules_of_hasKernels R

/-- If `proj R` has weak kernels, then `R` is left coherent: for every linear map `f : Rⁿ →ₗ[R] R`,
a weak kernel `w : W ⟶ Rⁿ` in `proj R` has image equal to `LinearMap.ker f`, which is therefore
finitely generated. -/
theorem isCoherentRing_of_hasWeakKernels_finiteProjectiveModules
    [HasWeakKernels (finiteProjectiveModules R).FullSubcategory] : IsCoherentRing R := by
  rw [isCoherentRing_iff, Module.isCoherent_iff_forall_fg_ker]
  refine ⟨inferInstance, fun n f ↦ ?_⟩
  let F : (finiteProjectiveModules R).FullSubcategory :=
    ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩
  let R₀ : (finiteProjectiveModules R).FullSubcategory :=
    ⟨ModuleCat.of R R, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩
  let φ : F ⟶ R₀ := ObjectProperty.homMk (ModuleCat.ofHom f)
  suffices hker : LinearMap.ker f = LinearMap.range (weakKernel.ι φ).hom.hom by
    rw [hker]
    exact Submodule.fg_range (weakKernel.ι φ).hom.hom
  apply le_antisymm
  · intro x hx
    let g : R₀ ⟶ F :=
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Fin n → R) x))
    have hg : g ≫ φ = 0 := ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <|
      LinearMap.ext fun (r : R) ↦ by
        -- Unfold composition of wrapped linear maps in the full subcategory.
        change f ((LinearMap.toSpanSingleton R (Fin n → R) x) r) = 0
        rw [LinearMap.toSpanSingleton_apply, map_smul, LinearMap.mem_ker.mp hx, smul_zero]
    let u : R₀ ⟶ weakKernel φ := weakKernel.lift φ g hg
    refine ⟨u.hom.hom (1 : R), ?_⟩
    have hu : (weakKernel.ι φ).hom.hom (u.hom.hom (1 : R)) = g.hom.hom (1 : R) :=
      congrArg (fun k ↦ k.hom.hom (1 : R)) (weakKernel.lift_ι φ g hg)
    exact hu.trans (one_smul R x)
  · rintro _ ⟨y, rfl⟩
    have hw : ((weakKernel.ι φ).hom ≫ φ.hom).hom y = 0 :=
      congrArg (fun k ↦ k.hom.hom y) (weakKernel.condition φ)
    simpa [φ] using hw

/-- **Chase's coherence theorem and categorical characterizations of left coherence.** For any ring
`R`, the following are equivalent:
1. `R` is left coherent (`TauCeti.IsCoherentRing R`);
2. `TauCeti.finitePresentationModules R` is closed under kernels in `ModuleCat R`;
3. `(TauCeti.finitePresentationModules R).FullSubcategory` is an abelian category;
4. `(TauCeti.finitePresentationModules R).FullSubcategory` has kernels;
5. `(TauCeti.finiteProjectiveModules R).FullSubcategory` (`proj R`) has weak kernels;
6. `TauCeti.isFinitelyPresentedFunctor (TauCeti.finiteProjectiveModules R).FullSubcategory`
   (`mod (proj R)`) is closed under kernels in the functor category. -/
theorem isCoherentRing_tfae :
    List.TFAE
      [IsCoherentRing R,
        (finitePresentationModules R).IsClosedUnderKernels,
        Nonempty (Abelian (finitePresentationModules R).FullSubcategory),
        HasKernels (finitePresentationModules R).FullSubcategory,
        HasWeakKernels (finiteProjectiveModules R).FullSubcategory,
        (isFinitelyPresentedFunctor
          (finiteProjectiveModules R).FullSubcategory).IsClosedUnderKernels] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ ⟨inferInstance⟩
  tfae_have 3 → 4 := fun ⟨_⟩ ↦ inferInstance
  tfae_have 4 → 5 := fun _ ↦ hasWeakKernels_finiteProjectiveModules_of_hasKernels R
  tfae_have 5 → 6 := fun _ ↦ inferInstance
  tfae_have 6 → 5 := fun _ ↦ hasWeakKernels_of_isClosedUnderKernels
  tfae_have 5 → 1 := fun _ ↦ isCoherentRing_of_hasWeakKernels_finiteProjectiveModules R
  tfae_finish

variable {R}

/-- `proj R` has weak kernels if and only if `R` is left coherent. -/
theorem hasWeakKernels_finiteProjectiveModules_iff_isCoherentRing :
    HasWeakKernels (finiteProjectiveModules R).FullSubcategory ↔ IsCoherentRing R :=
  (isCoherentRing_tfae R).out 5 1

/-- `finitePresentationModules R` is closed under kernels in `ModuleCat R` if and only if `R` is
left coherent. -/
theorem isClosedUnderKernels_finitePresentationModules_iff_isCoherentRing :
    (finitePresentationModules R).IsClosedUnderKernels ↔ IsCoherentRing R :=
  (isCoherentRing_tfae R).out 2 1

/-- `(finitePresentationModules R).FullSubcategory` has kernels if and only if `R` is left
coherent. -/
theorem hasKernels_finitePresentationModules_iff_isCoherentRing :
    HasKernels (finitePresentationModules R).FullSubcategory ↔ IsCoherentRing R :=
  (isCoherentRing_tfae R).out 4 1

/-- `(finitePresentationModules R).FullSubcategory` is abelian if and only if `R` is left coherent.
-/
theorem nonempty_abelian_finitePresentationModules_iff_isCoherentRing :
    Nonempty (Abelian (finitePresentationModules R).FullSubcategory) ↔ IsCoherentRing R :=
  (isCoherentRing_tfae R).out 3 1

/-- `(finitePresentationModules R).FullSubcategory` is abelian if and only if `proj R` has weak
kernels. -/
theorem nonempty_abelian_finitePresentationModules_iff_hasWeakKernels :
    Nonempty (Abelian (finitePresentationModules R).FullSubcategory) ↔
      HasWeakKernels (finiteProjectiveModules R).FullSubcategory :=
  (isCoherentRing_tfae R).out 3 5

end TauCeti
