/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Comparison

/-!
# Transporting contractions along isomorphisms of complexes

A contraction can be pulled back along an equivariant isomorphism of complexes. The
augmentation is composed with the inverse isomorphism. The retraction is precomposed with the
isomorphism in degree zero, while the homotopy is conjugated degree by degree. This lets a
regrouped tensor resolution inherit its contraction without reconstructing the contracting
homotopy on the regrouped factors.
-/

public section

open CategoryTheory

namespace TopRep.ResolutionContraction

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G]
  {X : TopRep.{max v w} R G} {J K : CochainComplex (TopRep.{max v w} R G) ℕ}

/-- Pull back a contraction along an equivariant isomorphism of complexes. The coefficient
object is unchanged. -/
noncomputable def ofIso (c : ResolutionContraction X J) (e : K ≅ J) :
    ResolutionContraction X K where
  ι := c.ι ≫ e.inv.f 0
  proj := c.proj ∘ₗ (e.hom.f 0).hom.toLinearMap
  hom n := (e.inv.f n).hom.toLinearMap ∘ₗ c.hom n ∘ₗ (e.hom.f (n + 1)).hom.toLinearMap
  proj_ι x := by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      hom_comp, ← ContIntertwiningMap.toContinuousLinearMap_apply,
      ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply]
    simp only [ContIntertwiningMap.toContinuousLinearMap_apply]
    exact (congrArg c.proj
      (ConcreteCategory.congr_hom (HomologicalComplex.Hom.isoApp e 0).inv_hom_id
        (c.ι.hom x))).trans (c.proj_ι x)
  ι_proj_add_hom_d z := by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [← ConcreteCategory.comp_apply, ← e.hom.comm,
      ConcreteCategory.comp_apply (e.hom.f 0) (J.d 0 1), ConcreteCategory.comp_apply,
      ← map_add, c.ι_proj_add_hom_d]
    exact ConcreteCategory.congr_hom (HomologicalComplex.Hom.isoApp e 0).hom_inv_id z
  d_hom_add_hom_d n z := by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContIntertwiningMap.toContinuousLinearMap_apply]
    rw [← ConcreteCategory.comp_apply, e.inv.comm, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply (K.d (n + 1) (n + 2)), ← e.hom.comm,
      ConcreteCategory.comp_apply, ← map_add, c.d_hom_add_hom_d]
    exact ConcreteCategory.congr_hom (HomologicalComplex.Hom.isoApp e (n + 1)).hom_inv_id z
  continuous_proj := by
    have h := c.continuous_proj.comp
      (((map_continuous (e.hom.f 0).hom).comp continuous_fst).prodMk continuous_snd)
    exact h.congr fun p ↦ by
      simp only [Function.comp_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContIntertwiningMap.toContinuousLinearMap_apply]
      rw [(e.hom.f 0).hom.isIntertwining]
  continuous_hom n := by
    have h := (map_continuous (e.inv.f n).hom).comp (c.continuous_hom n |>.comp
      (((map_continuous (e.hom.f (n + 1)).hom).comp continuous_fst).prodMk continuous_snd))
    exact h.congr fun p ↦ by
      simp only [Function.comp_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContIntertwiningMap.toContinuousLinearMap_apply]
      rw [(e.hom.f (n + 1)).hom.isIntertwining, (e.inv.f n).hom.isIntertwining]

/-- The transported augmentation is the original augmentation followed by the inverse
chain isomorphism in degree zero. -/
@[simp] theorem ofIso_ι (c : ResolutionContraction X J) (e : K ≅ J) :
    (c.ofIso e).ι = c.ι ≫ e.inv.f 0 := (rfl)

/-- The transported retraction first applies the chain isomorphism in degree zero. -/
@[simp] theorem ofIso_proj_apply (c : ResolutionContraction X J) (e : K ≅ J)
    (z : (K.X 0).V) :
    (c.ofIso e).proj z = c.proj ((e.hom.f 0).hom z) := (rfl)

/-- The transported homotopy is the conjugate of the original homotopy. -/
@[simp] theorem ofIso_hom_apply (c : ResolutionContraction X J) (e : K ≅ J) (n : ℕ)
    (z : (K.X (n + 1)).V) :
    (c.ofIso e).hom n z = (e.inv.f n).hom (c.hom n ((e.hom.f (n + 1)).hom z)) := (rfl)

end TopRep.ResolutionContraction
