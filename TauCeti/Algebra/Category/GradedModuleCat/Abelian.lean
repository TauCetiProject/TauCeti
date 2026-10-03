/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# The category of graded modules is abelian

This file proves that the category `TauCeti.GradedModuleCat 𝒜` of graded `𝒜`-modules is abelian.
Kernels, cokernels and finite products are formed on underlying modules: the kernel of a
morphism `f : M ⟶ N` is `ker f` with the grading of `M`, its cokernel is `N ⧸ range f` with the
grading of `N`, and the product of finitely many graded modules is their direct sum, graded
degreewise. These make sense because a map of degree zero has a homogeneous kernel and a
homogeneous image.

The forgetful functor to `ModuleCat A` therefore preserves kernels and cokernels, and it reflects
isomorphisms, because the inverse of a bijective map of degree zero again has degree zero. Since
`ModuleCat A` is abelian, so is `GradedModuleCat 𝒜`. This transfer argument, which builds the
`Abelian` instance from `Abelian.PreservesCoimage.hom_coimageImageComparison`, follows Mathlib's
proof that `FGModuleCat` is abelian (`Mathlib.Algebra.Category.FGModuleCat.Abelian`).
Together with the grading shift `TauCeti.GradedModuleCat.shift 𝒜`, this makes graded modules a
graded abelian category, whose canonical exact structure is
`TauCeti.GradedExactStructure.abelian`.

## Main definitions

* `TauCeti.GradedModuleCat.kernelCone` and `TauCeti.GradedModuleCat.cokernelCocone`: the kernel
  and cokernel of a morphism of graded modules, formed on underlying modules.
* `TauCeti.GradedModuleCat.cokernelGrading`: the grading of `N ⧸ range f` induced from `N`.
* `TauCeti.GradedModuleCat.productFan`: the product of finitely many graded modules, formed as
  their direct sum.

## Main results

* `TauCeti.GradedModuleCat.kernelIsLimit`, `TauCeti.GradedModuleCat.cokernelIsColimit` and
  `TauCeti.GradedModuleCat.productFanIsLimit`: these are limits and colimits.
* `TauCeti.GradedModuleCat.mem_kernelCone_pt_piece_iff`,
  `TauCeti.GradedModuleCat.mem_cokernelCocone_pt_piece_iff` and
  `TauCeti.GradedModuleCat.mem_productFan_pt_piece_iff`: the homogeneous elements of kernels,
  cokernels and finite products.
* The instance `Abelian (TauCeti.GradedModuleCat 𝒜)`.
* `TauCeti.GradedModuleCat.epi_iff_surjective`: epimorphisms are precisely the maps whose
  underlying linear maps are surjective.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory Limits

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N)

section Kernel

/-- The kernel of a morphism of graded modules: the kernel of the underlying linear map, with
the grading of the source. -/
noncomputable abbrev kernelObj : GradedModuleCat.{v} 𝒜 where
  carrier := LinearMap.ker f.hom
  grading := M.grading.ker f.isHomogeneous
  gradedSMul := ⟨fun {_ _} _ _ ha hz ↦ by
    rw [InternalGrading.mem_ker_piece] at hz ⊢
    exact SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hz⟩

/-- The inclusion of the kernel of a morphism of graded modules. -/
@[expose]
noncomputable def kernelι : kernelObj f ⟶ M :=
  ofHom (M := kernelObj f) (LinearMap.ker f.hom).subtype <|
    LinearMap.isHomogeneous_def.2 fun _ _ hz ↦ by simpa [kernelObj] using hz

@[reassoc (attr := simp)]
theorem kernelι_comp : kernelι f ≫ f = 0 :=
  hom_ext <| LinearMap.ext fun z ↦ z.2

/-- The kernel fork of a morphism of graded modules. -/
@[expose]
noncomputable def kernelCone : KernelFork f :=
  KernelFork.ofι (kernelι f) (kernelι_comp f)

@[simp]
theorem hom_kernelCone_ι : (kernelCone f).ι.hom = (LinearMap.ker f.hom).subtype :=
  rfl

/-- An element of the kernel of `f` has degree `p` exactly when it has degree `p` in the source. -/
@[simp]
theorem mem_kernelCone_pt_piece_iff {p : ℤ} {z : (kernelCone f).pt} :
    z ∈ (kernelCone f).pt.grading.piece p ↔ (kernelCone f).ι.hom z ∈ M.grading.piece p :=
  InternalGrading.mem_ker_piece _ _

/-- The kernel of a morphism of graded modules is a limit. -/
noncomputable def kernelIsLimit : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι (kernelι f) (kernelι_comp f)
    (fun g hg ↦ ofHom (N := kernelObj f)
      (LinearMap.codRestrict _ g.hom fun x ↦
        LinearMap.mem_ker.2 (by simpa using LinearMap.congr_fun (congr_arg Hom.hom hg) x))
      (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        simpa [kernelObj] using map_mem g hx))
    (fun _ _ ↦ rfl) fun g hg m hm ↦ by subst hm; rfl

instance : HasKernels (GradedModuleCat.{v} 𝒜) :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

instance : PreservesLimit (parallelPair f 0) toModuleCat :=
  preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm (ModuleCat.kernelIsLimit (toModuleCat.map f)))

end Kernel

section Cokernel

private theorem isHomogeneous_range_restrictScalars :
    DirectSum.SetLike.IsHomogeneous N.grading.piece ((LinearMap.range f.hom).restrictScalars k) :=
  f.isHomogeneous.isHomogeneous_range

/-- The grading of the quotient of `N` by the image of `f`, whose degree-`p` piece is the image
of `Nₚ`. -/
noncomputable def cokernelGrading : InternalGrading k (N ⧸ LinearMap.range f.hom) :=
  (N.grading.quotient ((LinearMap.range f.hom).restrictScalars k)
    (isHomogeneous_range_restrictScalars f)).map
    (Submodule.Quotient.restrictScalarsEquiv k (LinearMap.range f.hom))

/-- An element of the quotient of `N` by the image of `f` has degree `p` exactly when it is the
class of an element of degree `p`. -/
@[simp]
theorem mem_cokernelGrading_piece_iff {p : ℤ} {y : N ⧸ LinearMap.range f.hom} :
    y ∈ (cokernelGrading f).piece p ↔
      ∃ x ∈ N.grading.piece p, Submodule.Quotient.mk x = y := by
  rw [cokernelGrading, InternalGrading.mem_map_piece_iff, InternalGrading.mem_quotient_piece_iff]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [LinearEquiv.eq_symm_apply, Submodule.Quotient.restrictScalarsEquiv_mk]

/-- The cokernel of a morphism of graded modules: the quotient of the target by the image, with
the grading induced from the target. -/
noncomputable abbrev cokernelObj : GradedModuleCat.{v} 𝒜 where
  carrier := N ⧸ LinearMap.range f.hom
  grading := cokernelGrading f
  gradedSMul := ⟨fun {_ _} a _ ha hy ↦ by
    obtain ⟨x, hx, rfl⟩ := (mem_cokernelGrading_piece_iff f).1 hy
    exact (mem_cokernelGrading_piece_iff f).2
      ⟨a • x, SetLike.GradedSMul.smul_mem (B := N.grading.piece) ha hx, rfl⟩⟩

/-- The projection onto the cokernel of a morphism of graded modules. -/
@[expose]
noncomputable def cokernelπ : N ⟶ cokernelObj f :=
  ofHom (N := cokernelObj f) (LinearMap.range f.hom).mkQ <|
    LinearMap.isHomogeneous_def.2 fun _ x hx ↦
      (mem_cokernelGrading_piece_iff f).2 ⟨x, by simpa using hx, rfl⟩

@[reassoc (attr := simp)]
theorem comp_cokernelπ : f ≫ cokernelπ f = 0 :=
  hom_ext <| LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

/-- The cokernel cofork of a morphism of graded modules. -/
@[expose]
noncomputable def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

@[simp]
theorem hom_cokernelCocone_π : (cokernelCocone f).π.hom = (LinearMap.range f.hom).mkQ :=
  rfl

/-- An element of the cokernel of `f` has degree `p` exactly when it is the class of an element
of degree `p`. -/
@[simp]
theorem mem_cokernelCocone_pt_piece_iff {p : ℤ} {y : (cokernelCocone f).pt} :
    y ∈ (cokernelCocone f).pt.grading.piece p ↔
      ∃ x ∈ N.grading.piece p, (cokernelCocone f).π.hom x = y :=
  mem_cokernelGrading_piece_iff f

/-- The cokernel of a morphism of graded modules is a colimit. -/
noncomputable def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (comp_cokernelπ f)
    (fun g hg ↦ ofHom (M := cokernelObj f)
      ((LinearMap.range f.hom).liftQ g.hom (LinearMap.range_le_ker_iff.2 (congr_arg Hom.hom hg)))
      (LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ by
        obtain ⟨x, hx, rfl⟩ := (mem_cokernelGrading_piece_iff f).1 hy
        simpa using map_mem g hx))
    (fun _ _ ↦ rfl) fun g hg m hm ↦ hom_ext <| Submodule.linearMap_qext _ <|
      (congr_arg Hom.hom hm).trans (Submodule.liftQ_mkQ _ _ _).symm

instance : HasCokernels (GradedModuleCat.{v} 𝒜) :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

instance : PreservesColimit (parallelPair f 0) toModuleCat :=
  preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (ModuleCat.cokernelIsColimit (toModuleCat.map f)))

end Cokernel

section Product

variable {J : Type} (M : J → GradedModuleCat.{v} 𝒜)

/-- The direct sum of a family of graded modules, graded degreewise. -/
abbrev directSumObj : GradedModuleCat.{v} 𝒜 where
  carrier := DirectSum J fun j ↦ M j
  grading := InternalGrading.directSum fun j ↦ (M j).grading
  gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx ⊢
    exact fun j ↦ SetLike.GradedSMul.smul_mem (B := (M j).grading.piece) ha (hx j)⟩

/-- The fan exhibiting the direct sum of a family of graded modules as their product, which it is
when the family is finite. -/
@[expose]
def productFan : Fan M :=
  Fan.mk (directSumObj M) fun j ↦
    ofHom (M := directSumObj M) (DirectSum.component A J (fun j ↦ M j) j) <|
      LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        simp only [directSumObj, InternalGrading.directSum_piece,
          InternalGrading.mem_directSumPiece_iff] at hx
        rw [add_zero]
        exact hx j

@[simp]
theorem hom_productFan_proj (j : J) (x : directSumObj M) :
    ((productFan M).proj j).hom x = x j :=
  rfl

/-- An element of the direct sum has degree `p` exactly when each of its components does. -/
@[simp]
theorem mem_productFan_pt_piece_iff {p : ℤ} {x : (productFan M).pt} :
    x ∈ (productFan M).pt.grading.piece p ↔
      ∀ j, ((productFan M).proj j).hom x ∈ (M j).grading.piece p := by
  have h := InternalGrading.mem_directSumPiece_iff (fun j ↦ (M j).grading) p x
  rw [← InternalGrading.directSum_piece] at h
  exact h

variable [Finite J]

/-- The direct sum of finitely many graded modules is their product. -/
noncomputable def productFanIsLimit : IsLimit (productFan M) :=
  letI := Fintype.ofFinite J
  Fan.IsLimit.mk _
    (fun s ↦ ofHom (N := directSumObj M)
      ((DirectSum.linearEquivFunOnFintype A J fun j ↦ M j).symm.toLinearMap ∘ₗ
        LinearMap.pi fun j ↦ Hom.hom (s.proj j))
      (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        rw [add_zero, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff]
        exact fun j ↦ map_mem (s.proj j) hx))
    (fun _ _ ↦ rfl)
    fun s m hm ↦ by
      refine hom_ext <| LinearMap.ext fun x ↦ DFinsupp.ext fun j ↦ ?_
      exact LinearMap.congr_fun (congr_arg Hom.hom (hm j)) x

instance : HasProduct M :=
  HasLimit.mk ⟨_, productFanIsLimit M⟩

instance : HasFiniteProducts (GradedModuleCat.{v} 𝒜) :=
  ⟨fun _ ↦ ⟨fun _ ↦ hasLimit_of_iso Discrete.natIsoFunctor.symm⟩⟩

end Product

instance : (toModuleCat (𝒜 := 𝒜)).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    let e := (asIso (toModuleCat.map f)).toLinearEquiv
    have he : LinearMap.IsHomogeneous e.toLinearMap M.grading.piece N.grading.piece 0 :=
      f.isHomogeneous
    exact ⟨ofHom e.symm.toLinearMap (LinearMap.IsHomogeneous.linearEquiv_symm he),
      by ext x; exact e.symm_apply_apply x, by ext x; exact e.apply_symm_apply x⟩

instance {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  have := IsIso.of_isIso_fac_right
    (Abelian.PreservesCoimage.hom_coimageImageComparison toModuleCat f).symm
  exact isIso_of_reflects_iso _ toModuleCat

instance : Abelian (GradedModuleCat.{v} 𝒜) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- A morphism of graded modules is an epimorphism exactly when its underlying map is
surjective. -/
theorem epi_iff_surjective (f : M ⟶ N) : Epi f ↔ Function.Surjective f.hom := by
  constructor
  · intro hf
    have hzero : cokernelπ f = 0 := (cancel_epi f).mp (by simp)
    intro y
    have hy := LinearMap.congr_fun (congrArg Hom.hom hzero) y
    exact (Submodule.Quotient.mk_eq_zero _).mp hy
  · intro hf
    have : Epi (toModuleCat.map f) := (ModuleCat.epi_iff_surjective _).mpr hf
    exact (toModuleCat (𝒜 := 𝒜)).epi_of_epi_map inferInstance

/-- The forgetful functor preserves homology because kernels and cokernels are formed on
underlying modules. -/
instance : (toModuleCat (𝒜 := 𝒜)).PreservesHomology where

/-- A short complex of graded modules is exact exactly when its underlying linear maps are
exact. No additional condition on the internal degrees is needed. -/
theorem exact_iff {S : ShortComplex (GradedModuleCat.{v} 𝒜)} :
    S.Exact ↔ Function.Exact S.f.hom S.g.hom := by
  rw [← S.exact_map_iff_of_faithful toModuleCat,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end TauCeti.GradedModuleCat
