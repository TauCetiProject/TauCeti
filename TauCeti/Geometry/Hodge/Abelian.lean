/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import TauCeti.Geometry.Hodge.Semisimple

/-!
# The abelian category of polarizable rational Hodge structures

Polarizable rational Hodge structures of a fixed weight form an abelian category. Together with
the splitting of every monomorphism and the decomposition of every object into a finite biproduct
of simple objects (`TauCeti.Geometry.Hodge.Semisimple`), this is the semisimplicity of the
category of polarizable rational Hodge structures in its categorical form.

The kernel of a morphism `f : X ⟶ Y` is the rational Hodge substructure of `X` carried by the
kernel of the rational map of `f`. Its cokernel is a rational Hodge substructure of `Y`
complementary to the rational image of `f`, with the projection along the image as cokernel map.
Such a complement exists because `Y` is polarizable, and it is again polarizable, being a
substructure of `Y`. The rational realization carries these kernels and cokernels to the kernels
and cokernels of rational vector spaces, so it identifies the coimage–image comparison of `f`
with that of its rational map, which is invertible. The abelian structure then comes from
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat.kernelFork` and
  `TauCeti.Hodge.PolarizableHodgeStructureCat.kernelIsLimit`: the kernel of a morphism.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.rangeComplement`: a chosen rational Hodge
  substructure complementary to the rational image of a morphism.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.cokernelCofork` and
  `TauCeti.Hodge.PolarizableHodgeStructureCat.cokernelIsColimit`: the cokernel of a morphism.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.abelian`: polarizable rational Hodge structures of
  weight `n` form an abelian category.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2; Peters--Steenbrink, *Mixed Hodge
Structures*, §2.1. The construction of the abelian structure follows
`TauCeti.Geometry.Hodge.Mixed.Abelian`.
-/

public section

namespace TauCeti.Hodge.PolarizableHodgeStructureCat

open CategoryTheory Limits

universe u

variable {n : ℤ} {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y)

/-! ### Kernels -/

/-- The rational Hodge substructure of the source carried by the kernel of the rational map of a
morphism. -/
noncomputable def kerSubstructure : RationalHodgeSubstructure X.isBaseChangeRat X.hs :=
  RationalHodgeSubstructure.ofRationalMorphismKer
    (MixedHodgeStructure.Hom.toLinearMap_def f.hom ▸ Hom.isMorphism f)

/-- The rational subspace of `kerSubstructure f` is the kernel of the rational map of `f`. -/
@[simp]
theorem kerSubstructure_WQ : (kerSubstructure f).WQ = LinearMap.ker f.hom.toRatLinearMap :=
  RationalHodgeSubstructure.ofRationalMorphismKer_WQ _

/-- The kernel fork of a morphism of polarizable rational Hodge structures: the inclusion of the
rational Hodge substructure on the kernel of its rational map. -/
-- Exposure is required for the dependent point and structure-map lemmas below to elaborate.
@[expose]
noncomputable def kernelFork : KernelFork f :=
  KernelFork.ofι (substructureInclusion X (kerSubstructure f)) <| by
    apply Hom.ext
    ext x
    simpa using (kerSubstructure_WQ f).le x.2

/-- The structure map of the kernel fork is the inclusion of the kernel substructure. -/
@[simp]
theorem kernelFork_ι : (kernelFork f).ι = substructureInclusion X (kerSubstructure f) :=
  rfl

/-- The point of the kernel fork is the object induced on the kernel substructure. -/
@[simp]
theorem kernelFork_pt : (kernelFork f).pt = ofSubstructure X (kerSubstructure f) :=
  rfl

/-- The inclusion of the kernel of the rational map is a kernel. -/
noncomputable def kernelIsLimit : IsLimit (kernelFork f) :=
  haveI : IsSplitMono (kernelFork f).ι := isSplitMono_substructureInclusion X (kerSubstructure f)
  KernelFork.IsLimit.ofι _ (kernelFork f).condition
    (fun g hg ↦ substructureLift (kerSubstructure f) g fun x ↦ by
      simpa using LinearMap.congr_fun (congrArg (·.hom.toRatLinearMap) hg) x)
    (fun _ _ ↦ substructureLift_comp_substructureInclusion _ _ _)
    (fun _ _ _ hm ↦ (cancel_mono _).1
      (hm.trans (substructureLift_comp_substructureInclusion _ _ _).symm))

/-! ### Cokernels -/

/-- The rational Hodge substructure of the target carried by the image of the rational map of a
morphism. -/
noncomputable def rangeSubstructure : RationalHodgeSubstructure Y.isBaseChangeRat Y.hs :=
  RationalHodgeSubstructure.ofRationalMorphismRange
    (MixedHodgeStructure.Hom.toLinearMap_def f.hom ▸ Hom.isMorphism f)

/-- The rational subspace of `rangeSubstructure f` is the image of the rational map of `f`. -/
@[simp]
theorem rangeSubstructure_WQ :
    (rangeSubstructure f).WQ = LinearMap.range f.hom.toRatLinearMap :=
  RationalHodgeSubstructure.ofRationalMorphismRange_WQ _

/-- A chosen rational Hodge substructure of the target complementary to the rational image of a
morphism. It exists because the lattice of rational Hodge substructures of a polarizable Hodge
structure is complemented. -/
noncomputable def rangeComplement : RationalHodgeSubstructure Y.isBaseChangeRat Y.hs :=
  haveI := RationalHodgeSubstructure.complementedLattice_of_isPolarizable
    (hℚ := Y.isBaseChangeRat) Y.isPolarizable
  (exists_isCompl (rangeSubstructure f)).choose

/-- The chosen complement is complementary to the rational image. -/
theorem isCompl_rangeComplement_rangeSubstructure :
    IsCompl (rangeComplement f) (rangeSubstructure f) :=
  haveI := RationalHodgeSubstructure.complementedLattice_of_isPolarizable
    (hℚ := Y.isBaseChangeRat) Y.isPolarizable
  (exists_isCompl (rangeSubstructure f)).choose_spec.symm

/-- The cokernel cofork of a morphism of polarizable rational Hodge structures: the projection of
the target onto a complement of the rational image, along that image. -/
-- Exposure is required for the dependent point and structure-map lemmas below to elaborate.
@[expose]
noncomputable def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (substructureRetractionOfIsCompl Y (rangeComplement f) (rangeSubstructure f)
    (isCompl_rangeComplement_rangeSubstructure f)) <| by
    apply Hom.ext
    ext x
    simp

/-- The structure map of the cokernel cofork is the projection onto the chosen complement of the
rational image, along that image. -/
@[simp]
theorem cokernelCofork_π :
    (cokernelCofork f).π = substructureRetractionOfIsCompl Y (rangeComplement f)
      (rangeSubstructure f) (isCompl_rangeComplement_rangeSubstructure f) :=
  rfl

/-- The point of the cokernel cofork is the object induced on the image complement. -/
@[simp]
theorem cokernelCofork_pt : (cokernelCofork f).pt = ofSubstructure Y (rangeComplement f) :=
  rfl

/-- The projection onto a complement of the rational image, along that image, is a cokernel. -/
noncomputable def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (substructureRetractionOfIsCompl Y (rangeComplement f)
    (rangeSubstructure f) (isCompl_rangeComplement_rangeSubstructure f))
    (cokernelCofork f).condition
    (fun g _ ↦ substructureInclusion Y (rangeComplement f) ≫ g)
    (fun g hg ↦ by
      apply Hom.ext
      ext y
      -- `y` differs from its projection by a vector of the image, which `g` annihilates.
      have h := RationalHodgeSubstructure.isCompl_iff_WQ.1
        (isCompl_rangeComplement_rangeSubstructure f)
      have hproj := Submodule.projection_add_projection_eq_self h y
      obtain ⟨x, hx⟩ : (rangeSubstructure f).WQ.projection (rangeComplement f).WQ h.symm y ∈
          LinearMap.range f.hom.toRatLinearMap := by
        rw [← rangeSubstructure_WQ]
        exact Submodule.projection_apply_mem _ y
      have hgf : g.hom.toRatLinearMap (f.hom.toRatLinearMap x) = 0 := by
        simpa using LinearMap.congr_fun (congrArg (·.hom.toRatLinearMap) hg) x
      simp only [comp_toRatLinearMap, LinearMap.comp_apply,
        substructureRetractionOfIsCompl_toRatLinearMap, substructureInclusion_toRatLinearMap]
      conv_rhs => rw [← hproj, map_add, ← hx, hgf, add_zero]
      rfl)
    (fun _ _ m hm ↦ by
      subst hm
      exact (substructureInclusion_comp_substructureRetractionOfIsCompl_assoc Y _ _ _ m).symm)

/-! ### The abelian structure -/

/-- Polarizable rational Hodge structures have kernels. -/
instance : HasKernels (PolarizableHodgeStructureCat.{u} n) :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- Polarizable rational Hodge structures have cokernels. -/
instance : HasCokernels (PolarizableHodgeStructureCat.{u} n) :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- The rational realization of a short complex of polarizable rational Hodge structures is exact
exactly when the image of its first rational map is the kernel of its second. -/
theorem exact_map_rational_iff {S : ShortComplex (PolarizableHodgeStructureCat.{u} n)} :
    (S.map rational).Exact ↔
      LinearMap.range S.f.hom.toRatLinearMap = LinearMap.ker S.g.hom.toRatLinearMap := by
  -- Up to the object equalities `rational_obj`, the realized complex is the complex of rational
  -- maps.
  let S' : ShortComplex (ModuleCat.{u} ℚ) :=
    ShortComplex.mk (ModuleCat.ofHom S.f.hom.toRatLinearMap)
      (ModuleCat.ofHom S.g.hom.toRatLinearMap) <| by
        rw [← ModuleCat.ofHom_comp, ← comp_toRatLinearMap, S.zero, zero_toRatLinearMap]
        rfl
  let e : S.map rational ≅ S' :=
    ShortComplex.isoMk (eqToIso (rational_obj _)) (eqToIso (rational_obj _))
      (eqToIso (rational_obj _)) (by simp [S']) (by simp [S'])
  exact (ShortComplex.exact_iff_of_iso e).trans (ShortComplex.moduleCat_exact_iff_range_eq_ker _)

/-- The rational realization preserves kernels. -/
noncomputable instance rational_preservesKernel :
    PreservesLimit (parallelPair f 0) rational := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  refine ((kernelFork f).isLimitMapConeEquiv rational).symm ?_
  let S := ShortComplex.mk (substructureInclusion X (kerSubstructure f)) f (kernelFork f).condition
  have := isSplitMono_substructureInclusion X (kerSubstructure f)
  have : Mono (S.map rational).f := (inferInstance : Mono (rational.map S.f))
  exact ((exact_map_rational_iff (S := S)).2 (by
    simp only [S]
    rw [substructureInclusion_toRatLinearMap, Submodule.range_subtype,
      kerSubstructure_WQ])).fIsKernel

/-- The rational realization preserves cokernels. -/
noncomputable instance rational_preservesCokernel :
    PreservesColimit (parallelPair f 0) rational := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
  refine ((cokernelCofork f).isColimitMapCoconeEquiv rational).symm ?_
  have : IsSplitEpi (substructureRetractionOfIsCompl Y (rangeComplement f) (rangeSubstructure f)
      (isCompl_rangeComplement_rangeSubstructure f)) :=
    IsSplitEpi.mk' ⟨substructureInclusion Y (rangeComplement f),
      substructureInclusion_comp_substructureRetractionOfIsCompl _ _ _ _⟩
  let S := ShortComplex.mk f (substructureRetractionOfIsCompl Y (rangeComplement f)
    (rangeSubstructure f) (isCompl_rangeComplement_rangeSubstructure f))
    (cokernelCofork f).condition
  have : Epi (S.map rational).g := (inferInstance : Epi (rational.map S.g))
  exact ((exact_map_rational_iff (S := S)).2 (by
    simp only [S]
    rw [substructureRetractionOfIsCompl_toRatLinearMap, Submodule.ker_projectionOnto,
      rangeSubstructure_WQ])).gIsCokernel

/-- The coimage–image comparison of a morphism of polarizable rational Hodge structures is an
isomorphism. -/
noncomputable instance isIso_coimageImageComparison :
    IsIso (Abelian.coimageImageComparison f) := by
  have : IsIso (rational.map (Abelian.coimageImageComparison f)) :=
    (Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso rational f).hom).mpr inferInstance
  exact isIso_of_reflects_iso _ rational

/-- **Polarizable rational Hodge structures of weight `n` form an abelian category.** -/
noncomputable instance abelian : Abelian (PolarizableHodgeStructureCat.{u} n) :=
  Abelian.ofCoimageImageComparisonIsIso

end TauCeti.Hodge.PolarizableHodgeStructureCat
