/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic

import TauCeti.AlgebraicTopology.FundamentalGroup.ComplSingleton
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.Geometry.Manifold.Connected

/-!
# The fundamental group of a connected sum

In dimension at least three, the fundamental group of a connected sum is the free product of
those of its summands. The two punctured summands form an open cover whose intersection is a
punctured coordinate space, hence simply connected. The equivalence combines
`TauCeti.vanKampenEquiv` for this cover with
`TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective` for the summands.

`TauCeti.ConnectedSum.fundamentalGroupMulEquiv` uses points of the two punctured summands which
are identified in the connected sum as basepoints. For example, a nonzero coordinate `v` gives
these points as `e₁ v` and `e₂ (EuclideanGeometry.inversion 0 1 v)`, with their identification
provided by `TauCeti.ConnectedSum.inl_eq_inr`. Its two characteristic equations identify the
free factors using loops in the punctured summands and the actual puncture-inclusion maps.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §1.2,
  the Seifert--van Kampen theorem.
-/

public section

open Set Function Topology TopologicalSpace EuclideanGeometry

namespace TauCeti.ConnectedSum

variable {E M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [T1Space M] [TopologicalSpace N] [T1Space N]
  {e₁ : E → M} {e₂ : E → N}

private def neckMap (h₁ : IsOpenEmbedding e₁) : ({0}ᶜ : Set E) → ConnectedSum e₁ e₂ :=
  fun v ↦ inl e₁ e₂ ⟨e₁ v, mem_puncture.2 (h₁.injective.ne v.property)⟩

private theorem isEmbedding_neckMap (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsEmbedding (neckMap (e₂ := e₂) h₁) := by
  have he : IsEmbedding (fun v : ({0}ᶜ : Set E) ↦
      (⟨e₁ v, mem_puncture.2 (h₁.injective.ne v.property)⟩ : puncture e₁)) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp (h₁.isEmbedding.comp IsEmbedding.subtypeVal)
  exact (isOpenEmbedding_inl h₁ h₂).isEmbedding.comp he

private theorem range_neckMap (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    range (neckMap (e₂ := e₂) h₁) = range (inl e₁ e₂) ∩ range (inr e₁ e₂) := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨⟨_, apply_inversion_mem_puncture h₂.injective v.property⟩,
      (inl_eq_inr (v : E) _ _).symm⟩⟩
  · rintro ⟨⟨x, rfl⟩, y, hy⟩
    obtain ⟨v, hv, hvx, -⟩ := (inl_eq_inr_iff h₁.injective).1 hy.symm
    exact ⟨⟨v, hv⟩, congrArg (inl e₁ e₂) (Subtype.ext hvx)⟩

/-- The overlap of the two punctured summands is simply connected in dimension at least three.
It is the embedded punctured coordinate space. -/
theorem isSimplyConnected_range_inl_inter_range_inr (h : 2 < Module.rank ℝ E)
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsSimplyConnected (range (inl e₁ e₂) ∩ range (inr e₁ e₂)) := by
  have hRadius : (0 : ℝ) < 1 := zero_lt_one
  have hs : IsSimplyConnected ({0}ᶜ : Set E) := by
    simpa only [compl_eq_univ_sdiff] using
      (starConvex_univ (𝕜 := ℝ) (x := (0 : E))).isSimplyConnected_sdiff_singleton h
        hRadius (subset_univ (Metric.sphere (0 : E) 1))
  have : SimplyConnectedSpace ({0}ᶜ : Set E) := hs.simplyConnectedSpace
  have hUniv : IsSimplyConnected (univ : Set ({0}ᶜ : Set E)) :=
    (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace_iff.2 inferInstance
  rw [← range_neckMap h₁ h₂, ← image_univ]
  exact (isEmbedding_neckMap h₁ h₂).isSimplyConnected_image.2 hUniv

variable [ChartedSpace E M] [ChartedSpace E N] [ConnectedSpace M] [ConnectedSpace N]
  (h : 2 < Module.rank ℝ E) (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (x : puncture e₁) (y : puncture e₂) (hxy : inl e₁ e₂ x = inr e₁ e₂ y)

private noncomputable def puncturedFundamentalGroupEquiv :
    Monoid.Coprod (FundamentalGroup (puncture e₁) x) (FundamentalGroup (puncture e₂) y) ≃*
      FundamentalGroup (ConnectedSum e₁ e₂) (inl e₁ e₂ x) := by
  -- Compute the range-subtype basepoints before identifying them with the common point.
  have hl : (isOpenEmbedding_inl h₁ h₂).isEmbedding.toHomeomorph x =
      (⟨inl e₁ e₂ x, x, rfl⟩ : range (inl e₁ e₂)) := by
    apply Subtype.ext
    exact (isOpenEmbedding_inl h₁ h₂).isEmbedding.toHomeomorph_apply_coe x
  have hr : (isOpenEmbedding_inr h₁ h₂).isEmbedding.toHomeomorph y =
      (⟨inl e₁ e₂ x, y, hxy.symm⟩ : range (inr e₁ e₂)) := by
    apply Subtype.ext
    exact ((isOpenEmbedding_inr h₁ h₂).isEmbedding.toHomeomorph_apply_coe y).trans hxy.symm
  let l := FundamentalGroup.homeomorphMulEquivOfEq
    (isOpenEmbedding_inl h₁ h₂).isEmbedding.toHomeomorph hl
  let r := FundamentalGroup.homeomorphMulEquivOfEq
    (isOpenEmbedding_inr h₁ h₂).isEmbedding.toHomeomorph hr
  refine (l.coprodCongr r).trans (vanKampenEquiv ?_ ?_ ?_
    (isSimplyConnected_range_inl_inter_range_inr h h₁ h₂) ⟨x, rfl⟩ ⟨y, hxy.symm⟩)
  · rw [(isOpenEmbedding_inl h₁ h₂).isOpen_range.interior_eq,
      (isOpenEmbedding_inr h₁ h₂).isOpen_range.interior_eq, range_inl_union_range_inr]
  · rw [← image_univ]
    have : PathConnectedSpace (puncture e₁ : Set M) := by
      rw [← isPathConnected_iff_pathConnectedSpace, coe_puncture]
      exact isPathConnected_compl_of_finite_of_one_lt_rank (Cardinal.one_lt_two.trans h)
        (finite_singleton (e₁ 0))
    exact isPathConnected_univ.image (continuous_inl e₁ e₂)
  · rw [← image_univ]
    have : PathConnectedSpace (puncture e₂ : Set N) := by
      rw [← isPathConnected_iff_pathConnectedSpace, coe_puncture]
      exact isPathConnected_compl_of_finite_of_one_lt_rank (Cardinal.one_lt_two.trans h)
        (finite_singleton (e₂ 0))
    exact isPathConnected_univ.image (continuous_inr e₁ e₂)

private theorem puncturedFundamentalGroupEquiv_inl (g : FundamentalGroup (puncture e₁) x) :
    puncturedFundamentalGroupEquiv h h₁ h₂ x y hxy (Monoid.Coprod.inl g) =
      FundamentalGroup.map ⟨inl e₁ e₂, continuous_inl e₁ e₂⟩ x g := by
  simp only [puncturedFundamentalGroupEquiv, MulEquiv.trans_apply, MulEquiv.coprodCongr_apply,
    Monoid.Coprod.map_apply_inl]
  erw [← MulEquiv.coe_toMonoidHom, MulEquiv.toMonoidHom_eq_coe,
    vanKampenEquiv_toMonoidHom, vanKampenLift_apply_inl]
  -- Fix the range-subtype basepoint before composing the induced maps.
  change FundamentalGroup.map (ContinuousMap.subtypeVal (range (inl e₁ e₂))) _
    (FundamentalGroup.homeomorphMulEquivOfEq _ _ g) = _
  rw [FundamentalGroup.homeomorphMulEquivOfEq_apply, ← FundamentalGroup.mapOfEq_rfl,
    FundamentalGroup.mapOfEq_comp]
  calc
    _ = FundamentalGroup.mapOfEq ⟨inl e₁ e₂, continuous_inl e₁ e₂⟩ rfl g :=
      FundamentalGroup.mapOfEq_congr (by ext; rfl) _ rfl g
    _ = _ := by rw [FundamentalGroup.mapOfEq_rfl]

private theorem puncturedFundamentalGroupEquiv_inr (g : FundamentalGroup (puncture e₂) y) :
    puncturedFundamentalGroupEquiv h h₁ h₂ x y hxy (Monoid.Coprod.inr g) =
      FundamentalGroup.mapOfEq ⟨inr e₁ e₂, continuous_inr e₁ e₂⟩ hxy.symm g := by
  simp only [puncturedFundamentalGroupEquiv, MulEquiv.trans_apply, MulEquiv.coprodCongr_apply,
    Monoid.Coprod.map_apply_inr]
  erw [← MulEquiv.coe_toMonoidHom, MulEquiv.toMonoidHom_eq_coe,
    vanKampenEquiv_toMonoidHom, vanKampenLift_apply_inr]
  -- Fix the range-subtype basepoint before composing the induced maps.
  change FundamentalGroup.map (ContinuousMap.subtypeVal (range (inr e₁ e₂))) _
    (FundamentalGroup.homeomorphMulEquivOfEq _ _ g) = _
  rw [FundamentalGroup.homeomorphMulEquivOfEq_apply, ← FundamentalGroup.mapOfEq_rfl,
    FundamentalGroup.mapOfEq_comp]
  exact FundamentalGroup.mapOfEq_congr (by ext; rfl) _ _ g

private theorem puncture_map_bijective {X : Type*} [TopologicalSpace X] [T1Space X]
    [ChartedSpace E X] [ConnectedSpace X] (h : 2 < Module.rank ℝ E) (e : E → X) :
    ∀ z : (puncture e : Set X),
      Bijective (FundamentalGroup.map (ContinuousMap.subtypeVal (puncture e : Set X)) z) := by
  rw [coe_puncture]
  exact fundamentalGroup_map_subtypeVal_compl_singleton_bijective h (e 0)

/-- **The fundamental group of a connected sum is the free product of the fundamental groups
of its summands**, in dimension at least three. The basepoints `x` and `y` lie in the punctured
summands and are identified by the gluing. The factor maps are characterized by
`fundamentalGroupMulEquiv_inl_map` and `fundamentalGroupMulEquiv_inr_map`. -/
noncomputable def fundamentalGroupMulEquiv :
    Monoid.Coprod (FundamentalGroup M x.val) (FundamentalGroup N y.val) ≃*
      FundamentalGroup (ConnectedSum e₁ e₂) (inl e₁ e₂ x) :=
  ((MulEquiv.ofBijective (FundamentalGroup.map (ContinuousMap.subtypeVal (puncture e₁ : Set M)) x)
      (puncture_map_bijective h e₁ x)).symm.coprodCongr
    (MulEquiv.ofBijective
      (FundamentalGroup.map (ContinuousMap.subtypeVal (puncture e₂ : Set N)) y)
      (puncture_map_bijective h e₂ y)).symm).trans
    (puncturedFundamentalGroupEquiv h h₁ h₂ x y hxy)

-- Match the factor equations before simp changes the puncture carrier coercions.
/-- A loop in the first punctured summand represents the first free factor after the puncture
inclusion identifies its fundamental group with that of the original manifold. -/
@[simp↓]
theorem fundamentalGroupMulEquiv_inl_map (g : FundamentalGroup (puncture e₁) x) :
    fundamentalGroupMulEquiv h h₁ h₂ x y hxy
        (Monoid.Coprod.inl
          (FundamentalGroup.map (ContinuousMap.subtypeVal (puncture e₁ : Set M)) x g)) =
      FundamentalGroup.map ⟨inl e₁ e₂, continuous_inl e₁ e₂⟩ x g := by
  unfold fundamentalGroupMulEquiv
  -- The ambient basepoints are the values of the puncture inclusions.
  erw [MulEquiv.trans_apply, MulEquiv.coprodCongr_apply, Monoid.Coprod.map_apply_inl,
    MulEquiv.symm_apply_apply]
  exact puncturedFundamentalGroupEquiv_inl h h₁ h₂ x y hxy g

/-- A loop in the second punctured summand represents the second free factor. The image is
based at the first summand's point using the given identification `hxy`. -/
@[simp↓]
theorem fundamentalGroupMulEquiv_inr_map (g : FundamentalGroup (puncture e₂) y) :
    fundamentalGroupMulEquiv h h₁ h₂ x y hxy
        (Monoid.Coprod.inr
          (FundamentalGroup.map (ContinuousMap.subtypeVal (puncture e₂ : Set N)) y g)) =
      FundamentalGroup.mapOfEq ⟨inr e₁ e₂, continuous_inr e₁ e₂⟩ hxy.symm g := by
  unfold fundamentalGroupMulEquiv
  -- The ambient basepoints are the values of the puncture inclusions.
  erw [MulEquiv.trans_apply, MulEquiv.coprodCongr_apply, Monoid.Coprod.map_apply_inr,
    MulEquiv.symm_apply_apply]
  exact puncturedFundamentalGroupEquiv_inr h h₁ h₂ x y hxy g

end TauCeti.ConnectedSum
