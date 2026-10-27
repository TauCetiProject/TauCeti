/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.Product
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Small products of graded modules

The categorical product has the degreewise product grading. Its total module is the submodule
of the Cartesian product consisting of finite sums of homogeneous families, as constructed by
`InternalGrading.product`. A degree-zero family of maps has values in this submodule because
the finite degree support of a source element controls all of its images simultaneously.

The finite direct-sum product fan in `GradedModuleCat.Abelian` also applies when the scalar
pieces do not decompose the algebra. The degreewise fan here allows arbitrary index types
and uses the graded-algebra decomposition to keep the total product stable under scalars.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.GradedModuleCat

universe uk uA v

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {J : Type v}
  (M : J → GradedModuleCat.{v} 𝒜)

/-- The degreewise product of graded modules, with finite total degree support. -/
@[expose, implicit_reducible]
noncomputable def product : GradedModuleCat.{v} 𝒜 := by
  let G := fun j ↦ (M j).grading
  let P := InternalGrading.productScalarSubmodule G 𝒜
  let H : InternalGrading k P := InternalGrading.product G
  letI : SetLike.GradedSMul 𝒜 H.piece :=
    ⟨fun {_ _} a x ha hx ↦
      (InternalGrading.mem_product_piece_iff G _ _).mpr fun j ↦
        SetLike.GradedSMul.smul_mem (B := (M j).grading.piece) ha
          ((InternalGrading.mem_product_piece_iff G _ _).mp hx j)⟩
  exact
    { carrier := P
      grading := H }

/-- The product grading is checked in every component. -/
@[simp]
theorem mem_product_piece_iff (p : ℤ) (x : product M) :
    x ∈ (product M).grading.piece p ↔ ∀ j, x.1 j ∈ (M j).grading.piece p :=
  InternalGrading.mem_product_piece_iff _ _ _

-- Type the subtype comparison at the bundled product carrier, so projection rewrites do not
-- have to infer its dependent module presentation from a raw submodule element.
private theorem product_subtype_apply (x : product M) :
    (Submodule.subtype
      (InternalGrading.productScalarSubmodule (fun j ↦ (M j).grading) 𝒜)) x = x.1 :=
  Submodule.subtype_apply x

/-- The graded projection to one factor. -/
noncomputable def productπ (j : J) : product M ⟶ M j :=
  ofHom ((LinearMap.proj j).comp
    (Submodule.subtype (InternalGrading.productScalarSubmodule (fun j ↦ (M j).grading) 𝒜)))
    (by
      rw [LinearMap.isHomogeneous_def]
      intro p x hx
      rw [LinearMap.comp_apply, LinearMap.proj_apply,
        congrFun (product_subtype_apply M x) j]
      simpa only [add_zero] using (mem_product_piece_iff M p x).mp hx j)

/-- The projection is the corresponding coordinate of the family. -/
@[simp]
theorem productπ_apply (j : J) (x : product M) : (productπ M j).hom x = x.1 j := by
  dsimp only [productπ, hom_ofHom]
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  exact congrFun (product_subtype_apply M x) j

/-- A family of degree-zero maps lifts into the degreewise product. -/
noncomputable def productLift {N : GradedModuleCat.{v} 𝒜} (f : ∀ j, N ⟶ M j) :
    N ⟶ product M :=
  ofHom (InternalGrading.productLift (fun j ↦ (M j).grading) 𝒜 N.grading 0
    (fun j ↦ (f j).hom) (fun j ↦ by
      rw [LinearMap.isHomogeneous_def]
      intro p x hx
      simpa only [LinearMap.restrictScalars_apply] using (f j).isHomogeneous.map_mem hx))
    (by
      rw [LinearMap.isHomogeneous_def]
      intro p x hx
      apply (mem_product_piece_iff M (p + 0) _).mpr
      intro j
      rw [InternalGrading.productLift_apply]
      exact (f j).isHomogeneous.map_mem hx)

/-- The lift has the prescribed components. -/
@[simp]
theorem productLift_apply {N : GradedModuleCat.{v} 𝒜} (f : ∀ j, N ⟶ M j)
    (x : N) (j : J) : ((productLift M f).hom x).1 j = (f j).hom x := by
  dsimp only [productLift, hom_ofHom]
  apply InternalGrading.productLift_apply

/-- The lifted map followed by a projection is the prescribed map. -/
@[reassoc (attr := simp)]
theorem productLift_π {N : GradedModuleCat.{v} 𝒜} (f : ∀ j, N ⟶ M j) (j : J) :
    productLift M f ≫ productπ M j = f j := by
  apply hom_ext
  ext x
  simp only [hom_comp, LinearMap.comp_apply, productπ_apply, productLift_apply]

/-- Maps into the product are determined by their projections. -/
theorem product_hom_ext {N : GradedModuleCat.{v} 𝒜} {f g : N ⟶ product M}
    (hfg : ∀ j, f ≫ productπ M j = g ≫ productπ M j) : f = g := by
  apply hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext j
  simpa only [hom_comp, LinearMap.comp_apply, productπ_apply] using
    congrArg (fun t ↦ t.hom x) (hfg j)

/-- The fan of graded product projections. -/
noncomputable abbrev degreewiseProductFan : Fan M :=
  Fan.mk (product M) (productπ M)

/-- The degreewise product satisfies the categorical product universal property. -/
noncomputable def degreewiseProductFanIsLimit : IsLimit (degreewiseProductFan M) :=
  Fan.IsLimit.mk _ (fun s ↦ productLift M s.proj)
    (fun s j ↦ productLift_π M s.proj j)
    (fun s _ hm ↦ product_hom_ext M fun j ↦
      (hm j).trans (productLift_π M s.proj j).symm)

noncomputable instance hasProductDegreewise (X : J → GradedModuleCat.{v} 𝒜) : HasProduct X :=
  HasLimit.mk { cone := degreewiseProductFan X, isLimit := degreewiseProductFanIsLimit X }

instance : HasProducts.{v} (GradedModuleCat.{v} 𝒜) :=
  fun _ ↦ ⟨fun _ ↦ hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

end TauCeti.GradedModuleCat
