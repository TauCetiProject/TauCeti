/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels
public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic
public import TauCeti.RingTheory.Coherent.Basic

/-!
# Coherence and the category of finitely presented modules

Over any ring `R`, `TauCeti.finitePresentationModules R` contains zero and is closed under finite
products, cokernels and retracts (`TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Basic`).
Closing the finitely presented `R`-modules under kernels is equivalent to `R` being left coherent
(`TauCeti.IsCoherentRing R`), and likewise to
`(TauCeti.finitePresentationModules R).FullSubcategory` having kernels or being abelian, and to
`proj R` (`(TauCeti.finiteProjectiveModules R).FullSubcategory`) having weak kernels.

The six-way equivalence including closure of finitely presented functors on `proj R` under kernels
is in `TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Coherent.FinitelyPresentedFunctor`.

## Main results

* `TauCeti.hasWeakKernels_finiteProjectiveModules_of_hasKernels` and
  `TauCeti.isCoherentRing_of_hasWeakKernels_finiteProjectiveModules`: the forward and backward steps
  relating kernels in `finitePresentationModules R`, weak kernels in `proj R`, and
  `IsCoherentRing R`.
* `TauCeti.hasWeakKernels_finiteProjectiveModules_iff_isCoherentRing`,
  `TauCeti.isClosedUnderKernels_finitePresentationModules_iff_isCoherentRing`,
  `TauCeti.hasKernels_finitePresentationModules_iff_isCoherentRing`,
  `TauCeti.nonempty_abelian_finitePresentationModules_iff_isCoherentRing`, and
  `TauCeti.nonempty_abelian_finitePresentationModules_iff_hasWeakKernels`: pairwise equivalences
  between left coherence of `R`, the module criteria, and `HasWeakKernels` on `proj R`.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), 457–473.
* N. Bourbaki, *Algèbre Commutative*, Ch. I, §2, Exercise 12.
* [The Stacks Project, Section 10.90, Tag 05CU](https://stacks.math.columbia.edu/tag/05CU).
-/

public section

universe u

open CategoryTheory Limits
open scoped ZeroObject

namespace TauCeti

variable (R : Type u) [Ring R]

/-! ### Coherence criteria for modules and projective modules -/

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
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, w,
        Category.assoc]
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
    simp only [ObjectProperty.FullSubcategory.comp_hom, KernelFork.ι_ofι, ObjectProperty.homMk_hom,
      w, ← Category.assoc]
    rw [Projective.factorThru_comp, hu]

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
  let eR : (finiteProjectiveModulesRegular R).obj ≅ ModuleCat.of R R :=
    eqToIso (finiteProjectiveModulesRegular_obj R)
  let φ : F ⟶ finiteProjectiveModulesRegular R :=
    ObjectProperty.homMk (ModuleCat.ofHom f ≫ eR.inv)
  suffices hker : LinearMap.ker f = LinearMap.range (weakKernel.ι φ).hom.hom by
    rw [hker]
    exact Submodule.fg_range (weakKernel.ι φ).hom.hom
  apply le_antisymm
  · intro x hx
    let g : finiteProjectiveModulesRegular R ⟶ F :=
      ObjectProperty.homMk (eR.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R (Fin n → R) x))
    have hg : g ≫ φ = 0 := ObjectProperty.hom_ext _ <| by
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        ObjectProperty.zero_hom, g, φ, Category.assoc]
      have hfx : ModuleCat.ofHom (LinearMap.toSpanSingleton R (Fin n → R) x) ≫
          ModuleCat.ofHom f = 0 := ModuleCat.hom_ext <| LinearMap.ext fun (r : R) ↦ by
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
          LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.toSpanSingleton_apply, map_smul,
          LinearMap.mem_ker.mp hx, smul_zero]
      rw [← Category.assoc (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Fin n → R) x)),
        hfx, Limits.zero_comp, Limits.comp_zero]
    let u : finiteProjectiveModulesRegular R ⟶ weakKernel φ := weakKernel.lift φ g hg
    refine ⟨u.hom.hom (eR.inv.hom (1 : R)), ?_⟩
    have hu : (weakKernel.ι φ).hom.hom (u.hom.hom (eR.inv.hom (1 : R))) =
        g.hom.hom (eR.inv.hom (1 : R)) :=
      congrArg (fun k ↦ k.hom.hom (eR.inv.hom (1 : R))) (weakKernel.lift_ι φ g hg)
    rw [hu]
    simp only [g, ObjectProperty.homMk_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, Iso.inv_hom_id_apply, LinearMap.toSpanSingleton_apply, one_smul]
  · rintro _ ⟨y, rfl⟩
    have hw : ((weakKernel.ι φ).hom ≫ φ.hom ≫ eR.hom).hom y = 0 := by
      rw [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, weakKernel.condition,
        ObjectProperty.zero_hom, Limits.zero_comp, ModuleCat.hom_zero, LinearMap.zero_apply]
    refine LinearMap.mem_ker.mpr ?_
    simpa only [φ, ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using hw

variable {R}

/-- `proj R` has weak kernels if and only if `R` is left coherent. -/
theorem hasWeakKernels_finiteProjectiveModules_iff_isCoherentRing :
    HasWeakKernels (finiteProjectiveModules R).FullSubcategory ↔ IsCoherentRing R :=
  ⟨fun _ ↦ isCoherentRing_of_hasWeakKernels_finiteProjectiveModules R, fun _ ↦ inferInstance⟩

/-- `finitePresentationModules R` is closed under kernels in `ModuleCat R` if and only if `R` is
left coherent. -/
theorem isClosedUnderKernels_finitePresentationModules_iff_isCoherentRing :
    (finitePresentationModules R).IsClosedUnderKernels ↔ IsCoherentRing R :=
  ⟨fun _ ↦
    have : HasKernels (finitePresentationModules R).FullSubcategory := inferInstance
    have := hasWeakKernels_finiteProjectiveModules_of_hasKernels R
    isCoherentRing_of_hasWeakKernels_finiteProjectiveModules R,
   fun _ ↦ inferInstance⟩

/-- `(finitePresentationModules R).FullSubcategory` has kernels if and only if `R` is left
coherent. -/
theorem hasKernels_finitePresentationModules_iff_isCoherentRing :
    HasKernels (finitePresentationModules R).FullSubcategory ↔ IsCoherentRing R :=
  ⟨fun _ ↦
    have := hasWeakKernels_finiteProjectiveModules_of_hasKernels R
    isCoherentRing_of_hasWeakKernels_finiteProjectiveModules R,
   fun _ ↦ inferInstance⟩

/-- `(finitePresentationModules R).FullSubcategory` is abelian if and only if `R` is left coherent.
-/
theorem nonempty_abelian_finitePresentationModules_iff_isCoherentRing :
    Nonempty (Abelian (finitePresentationModules R).FullSubcategory) ↔ IsCoherentRing R :=
  ⟨fun ⟨_⟩ ↦ hasKernels_finitePresentationModules_iff_isCoherentRing.mp inferInstance,
   fun _ ↦ ⟨inferInstance⟩⟩

/-- `(finitePresentationModules R).FullSubcategory` is abelian if and only if `proj R` has weak
kernels. -/
theorem nonempty_abelian_finitePresentationModules_iff_hasWeakKernels :
    Nonempty (Abelian (finitePresentationModules R).FullSubcategory) ↔
      HasWeakKernels (finiteProjectiveModules R).FullSubcategory :=
  nonempty_abelian_finitePresentationModules_iff_isCoherentRing.trans
    hasWeakKernels_finiteProjectiveModules_iff_isCoherentRing.symm

end TauCeti
