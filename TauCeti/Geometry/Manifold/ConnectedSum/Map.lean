/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum

/-!
# Maps of connected sums induced by maps of the summands

The connected sum `TauCeti.ConnectedSum e₁ e₂` of `M` and `N` removes the centres of the balls
`e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. Injective
maps `φ : M → M'` and `ψ : N → N'` carrying the balls to balls `e₁' = φ ∘ e₁` and `e₂' = ψ ∘ e₂`
carry glued points to glued points, so they induce a map of connected sums
`TauCeti.ConnectedSum.map`, which is `φ` on the first punctured summand and `ψ` on the second.

The image of this map consists of the points of the punctured summands of the target lying in the
images of `φ` and `ψ` (`TauCeti.ConnectedSum.range_map`). When `φ` and `ψ` are open embeddings, so
is the induced map (`TauCeti.ConnectedSum.isOpenEmbedding_map`), and when they are `C^n` local
diffeomorphisms, so is the induced map, for the charts of the connected sums
(`TauCeti.ConnectedSum.isLocalDiffeomorph_map`). The main use is with `φ` or `ψ` the inclusion of
an open subset containing the ball: removing from a summand points outside its ball removes the
same points from the connected sum.

## Main definitions

* `TauCeti.ConnectedSum.map`: the map of connected sums induced by maps of the summands.

## Main results

* `TauCeti.ConnectedSum.map_inl`, `TauCeti.ConnectedSum.map_inr`: the induced map on the punctured
  summands.
* `TauCeti.ConnectedSum.range_map`: its image.
* `TauCeti.ConnectedSum.isOpenEmbedding_map`: maps induced by open embeddings are open
  embeddings.
* `TauCeti.ConnectedSum.isLocalDiffeomorph_map`: maps induced by `C^n` local diffeomorphisms are
  `C^n` local diffeomorphisms.
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {M' : Type*} [TopologicalSpace M'] [T1Space M']
  {N : Type*} [TopologicalSpace N] [T1Space N] {N' : Type*} [TopologicalSpace N'] [T1Space N']
  {e₁ : E → M} {e₁' : E → M'} {e₂ : E → N} {e₂' : E → N'} {φ : M → M'} {ψ : N → N'}

variable (φ ψ) in
/-- **The map of connected sums induced by maps of the summands.** Injective maps `φ : M → M'` and
`ψ : N → N'` with `φ ∘ e₁ = e₁'` and `ψ ∘ e₂ = e₂'` induce the map from the connected sum along
`e₁`, `e₂` to the connected sum along `e₁'`, `e₂'` which is `φ` on the first punctured summand and
`ψ` on the second. -/
def map (hφ : Injective φ) (hψ : Injective ψ) (h₁ : φ ∘ e₁ = e₁') (h₂ : ψ ∘ e₂ = e₂') :
    ConnectedSum e₁ e₂ → ConnectedSum e₁' e₂' :=
  lift (inl e₁' e₂' ∘ punctureMap φ hφ (congrFun h₁ 0))
    (inr e₁' e₂' ∘ punctureMap ψ hψ (congrFun h₂ 0))
    fun v hv hx hy ↦ by
      have hmx : e₁' v ∈ puncture e₁' := by
        have h := (punctureMap φ hφ (congrFun h₁ 0) ⟨e₁ v, hx⟩).2
        rwa [coe_punctureMap, Subtype.coe_mk, ← comp_apply (f := φ) (g := e₁), h₁] at h
      have hmy : e₂' (inversion 0 1 v) ∈ puncture e₂' := by
        have h := (punctureMap ψ hψ (congrFun h₂ 0) ⟨e₂ (inversion 0 1 v), hy⟩).2
        rwa [coe_punctureMap, Subtype.coe_mk, ← comp_apply (f := ψ) (g := e₂), h₂] at h
      have hx' : punctureMap φ hφ (congrFun h₁ 0) ⟨e₁ v, hx⟩ = ⟨e₁' v, hmx⟩ :=
        Subtype.ext (by rw [coe_punctureMap]; exact congrFun h₁ v)
      have hy' : punctureMap ψ hψ (congrFun h₂ 0) ⟨e₂ (inversion 0 1 v), hy⟩ =
          ⟨e₂' (inversion 0 1 v), hmy⟩ :=
        Subtype.ext (by rw [coe_punctureMap]; exact congrFun h₂ _)
      simp only [comp_apply, hx', hy']
      exact inl_eq_inr v _ _

variable (hφ : Injective φ) (hψ : Injective ψ) (h₁ : φ ∘ e₁ = e₁') (h₂ : ψ ∘ e₂ = e₂')

@[simp]
theorem map_inl (x : puncture e₁) :
    map φ ψ hφ hψ h₁ h₂ (inl e₁ e₂ x) = inl e₁' e₂' (punctureMap φ hφ (congrFun h₁ 0) x) :=
  lift_inl _ _ _ x

@[simp]
theorem map_inr (y : puncture e₂) :
    map φ ψ hφ hψ h₁ h₂ (inr e₁ e₂ y) = inr e₁' e₂' (punctureMap ψ hψ (congrFun h₂ 0) y) :=
  lift_inr _ _ _ y

theorem map_comp_mk :
    map φ ψ hφ hψ h₁ h₂ ∘ mk e₁ e₂ =
      mk e₁' e₂' ∘
        Sum.map (punctureMap φ hφ (congrFun h₁ 0)) (punctureMap ψ hψ (congrFun h₂ 0)) := by
  ext (x | y) <;> simp

/-- The identity maps of the summands induce the identity of the connected sum. -/
@[simp]
theorem map_id : map id id injective_id injective_id (id_comp e₁) (id_comp e₂) = id :=
  hom_ext (fun x ↦ by rw [map_inl, punctureMap_id]; rfl) fun y ↦ by
    rw [map_inr, punctureMap_id]; rfl

/-- Maps of connected sums compose. -/
theorem map_map {M'' N'' : Type*} [TopologicalSpace M''] [T1Space M''] [TopologicalSpace N'']
    [T1Space N''] {e₁'' : E → M''} {e₂'' : E → N''} {φ' : M' → M''} {ψ' : N' → N''}
    (hφ' : Injective φ') (hψ' : Injective ψ') (h₁' : φ' ∘ e₁' = e₁'') (h₂' : ψ' ∘ e₂' = e₂'')
    (p : ConnectedSum e₁ e₂) :
    map φ' ψ' hφ' hψ' h₁' h₂' (map φ ψ hφ hψ h₁ h₂ p) =
      map (φ' ∘ φ) (ψ' ∘ ψ) (hφ'.comp hφ) (hψ'.comp hψ) (by rw [comp_assoc, h₁, h₁'])
        (by rw [comp_assoc, h₂, h₂']) p := by
  obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ p
  · simp only [mk_inl, map_inl]
    exact congrArg _ (Subtype.ext (by simp))
  · simp only [mk_inr, map_inr]
    exact congrArg _ (Subtype.ext (by simp))

theorem continuous_map (hφc : Continuous φ) (hψc : Continuous ψ) :
    Continuous (map φ ψ hφ hψ h₁ h₂) :=
  continuous_lift _ _ _
    ((continuous_inl e₁' e₂').comp (continuous_punctureMap hφ (congrFun h₁ 0) hφc))
    ((continuous_inr e₁' e₂').comp (continuous_punctureMap hψ (congrFun h₂ 0) hψc))

/-- The map induced by injective maps of the summands is injective, for injective balls. -/
theorem map_injective (he₁ : Injective e₁) (he₂ : Injective e₂) :
    Injective (map φ ψ hφ hψ h₁ h₂) := by
  have he₁' : Injective e₁' := h₁ ▸ hφ.comp he₁
  have he₂' : Injective e₂' := h₂ ▸ hψ.comp he₂
  intro p q hpq
  obtain ⟨z, rfl⟩ := mk_surjective e₁ e₂ p
  obtain ⟨z', rfl⟩ := mk_surjective e₁ e₂ q
  have key : ∀ w, map φ ψ hφ hψ h₁ h₂ (mk e₁ e₂ w) =
      mk e₁' e₂'
        (Sum.map (punctureMap φ hφ (congrFun h₁ 0)) (punctureMap ψ hψ (congrFun h₂ 0)) w) :=
    congrFun (map_comp_mk hφ hψ h₁ h₂)
  rw [key, key, mk_eq_mk_iff he₁' he₂'] at hpq
  rw [mk_eq_mk_iff he₁ he₂]
  rcases z with x | y <;> rcases z' with x' | y' <;>
    simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, rel_inl_inr,
      not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr, reduceCtorEq, or_false, false_or,
      Subtype.ext_iff, coe_punctureMap] at hpq ⊢
  · exact hφ hpq
  · obtain ⟨v, hv, hvx, hvy⟩ := hpq
    refine ⟨v, hv, hφ ?_, hψ ?_⟩
    · rw [← hvx, ← congrFun h₁ v, comp_apply]
    · rw [← hvy, ← congrFun h₂ _, comp_apply]
  · obtain ⟨v, hv, hvx, hvy⟩ := hpq
    refine ⟨v, hv, hφ ?_, hψ ?_⟩
    · rw [← hvx, ← congrFun h₁ v, comp_apply]
    · rw [← hvy, ← congrFun h₂ _, comp_apply]
  · exact hψ hpq

/-- **The image of an induced map** consists of the points of the punctured summands lying in the
images of the maps of the summands. -/
theorem range_map :
    range (map φ ψ hφ hψ h₁ h₂) =
      inl e₁' e₂' '' {x | (x : M') ∈ range φ} ∪ inr e₁' e₂' '' {y | (y : N') ∈ range ψ} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ q
    · exact Or.inl ⟨_, ⟨x, (coe_punctureMap _ _ x).symm⟩, by rw [mk_inl, map_inl]⟩
    · exact Or.inr ⟨_, ⟨y, (coe_punctureMap _ _ y).symm⟩, by rw [mk_inr, map_inr]⟩
  · rintro (⟨x, ⟨x₀, hx₀⟩, rfl⟩ | ⟨y, ⟨y₀, hy₀⟩, rfl⟩)
    · have hx₀' : x₀ ∈ puncture e₁ := mem_puncture.2 fun h ↦
        mem_puncture.1 x.2 (by rw [← hx₀, h, ← congrFun h₁ 0, comp_apply])
      exact ⟨inl e₁ e₂ ⟨x₀, hx₀'⟩, by
        rw [map_inl]; exact congrArg _ (Subtype.ext ((coe_punctureMap _ _ _).trans hx₀))⟩
    · have hy₀' : y₀ ∈ puncture e₂ := mem_puncture.2 fun h ↦
        mem_puncture.1 y.2 (by rw [← hy₀, h, ← congrFun h₂ 0, comp_apply])
      exact ⟨inr e₁ e₂ ⟨y₀, hy₀'⟩, by
        rw [map_inr]; exact congrArg _ (Subtype.ext ((coe_punctureMap _ _ _).trans hy₀))⟩

/-- **Maps induced by open embeddings are open embeddings**, for balls which are open
embeddings. -/
theorem isOpenEmbedding_map (hφo : IsOpenEmbedding φ) (hψo : IsOpenEmbedding ψ)
    (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂) :
    IsOpenEmbedding (map φ ψ hφ hψ h₁ h₂) := by
  have he₁' : IsOpenEmbedding e₁' := h₁ ▸ hφo.comp he₁
  have he₂' : IsOpenEmbedding e₂' := h₂ ▸ hψo.comp he₂
  refine .of_continuous_injective_isOpenMap (continuous_map hφ hψ h₁ h₂ hφo.continuous
    hψo.continuous) (map_injective hφ hψ h₁ h₂ he₁.injective he₂.injective) fun U hU ↦ ?_
  -- The image of `U` is the image under the quotient map of the open set `Sum.map _ _ '' (mk⁻¹ U)`.
  rw [← (mk_surjective e₁ e₂).image_preimage U, ← image_comp, map_comp_mk, image_comp]
  exact (isOpenQuotientMap_mk he₁' he₂').isOpenMap _
    (((isOpenMap_punctureMap hφ _ hφo.isOpenMap).sumMap (isOpenMap_punctureMap hψ _ hψo.isOpenMap))
      _ (hU.preimage (continuous_mk e₁ e₂)))

section Smooth

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [ChartedSpace H M] [ChartedSpace H M'] [ChartedSpace H N] [ChartedSpace H N']

variable [IsManifold I n M] [IsManifold I n M'] [IsManifold I n N] [IsManifold I n N']

/-- **Maps induced by `C^n` local diffeomorphisms are `C^n` local diffeomorphisms**, for the charts
of the connected sums, when the balls are open embeddings and `C^n` local diffeomorphisms. -/
theorem isLocalDiffeomorph_map (dφ : IsLocalDiffeomorph I I n φ) (dψ : IsLocalDiffeomorph I I n ψ)
    (he₁ : IsOpenEmbedding e₁) (he₂ : IsOpenEmbedding e₂) (he₁' : IsOpenEmbedding e₁')
    (he₂' : IsOpenEmbedding e₂') (de₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁)
    (de₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) :
    letI := chartedSpace (H := H) he₁ he₂
    letI := chartedSpace (H := H) he₁' he₂'
    IsLocalDiffeomorph I I n (map φ ψ hφ hψ h₁ h₂) := by
  let := chartedSpace (H := H) he₁ he₂
  let := chartedSpace (H := H) he₁' he₂'
  -- The balls of the target are the images of those of the source.
  have de₁' : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁' := by
    rw [← h₁]
    exact fun v ↦ (de₁ v).comp (hg := dφ _)
  have de₂' : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂' := by
    rw [← h₂]
    exact fun v ↦ (de₂ v).comp (hg := dψ _)
  have hmk := isLocalDiffeomorph_mk he₁ he₂ de₁ de₂
  have hmk' := isLocalDiffeomorph_mk he₁' he₂' de₁' de₂'
  intro p
  obtain ⟨z, rfl⟩ := mk_surjective e₁ e₂ p
  refine IsLocalDiffeomorphAt.of_comp_right ?_ (hmk z)
  rw [map_comp_mk]
  have hin : IsLocalDiffeomorphAt I I n
      (Sum.map (punctureMap φ hφ (congrFun h₁ 0)) (punctureMap ψ hψ (congrFun h₂ 0))) z := by
    rcases z with x | y
    · refine IsLocalDiffeomorphAt.of_comp_right (e := Sum.inl) ?_ (isLocalDiffeomorph_sumInl x)
      exact (isLocalDiffeomorph_punctureMap hφ _ dφ x).comp (hg := isLocalDiffeomorph_sumInl _)
    · refine IsLocalDiffeomorphAt.of_comp_right (e := Sum.inr) ?_ (isLocalDiffeomorph_sumInr y)
      exact (isLocalDiffeomorph_punctureMap hψ _ dψ y).comp (hg := isLocalDiffeomorph_sumInr _)
  exact hin.comp (hg := hmk' _)

end Smooth

end TauCeti.ConnectedSum
