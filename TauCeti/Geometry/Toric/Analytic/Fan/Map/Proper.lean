/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Compact
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Orbit

/-!
# Proper analytic toric maps satisfy the support condition

Let `f : Φ → Ψ` be a morphism of regular fans with real-linear map `f_ℝ`, and let `τ` be a cone
of `Ψ`. The source cones `σ` with `f_ℝ σ ⊆ τ` are exactly those whose charts the analytic map
sends into the chart of `τ`, and their union always lies in the inverse image `f_ℝ⁻¹ τ`. The
support condition for `τ` asks that the two sets be equal. This file proves that the support
condition holds for every target cone whenever the analytic map of a nonempty source fan is
proper.

The proof follows the one for compact realizations
(`TauCeti.Toric.Fan.isComplete_of_compactSpace_analyticRealization`). Given `w` with `f_ℝ w ∈ τ`,
the torus points `t k` at which each character `m` has absolute value `exp (-k ⟨m, w⟩)` are sent
by the analytic map to torus points at which every character of the dual semigroup of `τ` has
absolute value at most `1`. These lie in a compact part of the chart of `τ`, so properness gives
a cluster point `p` of the `t k`. The image of `p` lies in the chart of `τ`, so `p` lies in the
orbit of a source cone `σ` with `f_ℝ σ ⊆ τ`, hence in the chart of `σ`, and then `w ∈ σ`.

The nonemptiness hypothesis is necessary: the empty subfan of a nonempty fan has a proper
inclusion, but `0` lies in the inverse image of every ambient cone and in no cone of the empty
subfan.

## Main declarations

* `TauCeti.Toric.FanHom.preimage_realMap_eq_iUnion_of_isProperMap`: if the analytic map of a
  morphism of regular fans with nonempty source is proper, then for every target cone `τ` the
  inverse image of `τ` is the union of the source cones mapped into `τ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.4.
-/

public section

open Filter Set

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- If the analytic map of a morphism of regular fans with nonempty source is proper, then for
every target cone `τ` the inverse image of `τ` under the real-linear map is the union of the
source cones mapped into `τ`. The nonemptiness hypothesis is necessary: the inclusion of the
empty subfan is proper, but `0` lies in the inverse image of every cone and in no cone of the
empty fan. -/
theorem preimage_realMap_eq_iUnion_of_isProperMap (hΦ0 : Nonempty Φ.cones)
    (hf : IsProperMap (f.analyticMap hΦ hΨ)) (τ : Ψ.cones) :
    f.realMap ⁻¹' (τ.1 : Set V') =
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), (σ.1 : Set V) := by
  refine Subset.antisymm (fun w hw ↦ ?_) (iUnion₂_subset fun σ hστ x hx ↦
    hστ (Submodule.mem_map_of_mem hx))
  -- The torus points `t k` with `‖t k m‖ = exp (-k ⟨m, w⟩)` are sent into the compact part `K`
  -- of the chart of `τ` where every monomial has absolute value at most `1`.
  choose t ht using fun k : ℕ ↦ Φ.lattice.exists_complexTorus_norm_eq ((k : ℝ) • w)
  let K := Ψ.analyticAffineChartι hΨ τ ''
    {x : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice τ.1) |
      ∀ s, ‖x (MonoidAlgebra.single (Multiplicative.ofAdd s) 1)‖ ≤ 1}
  have hK : IsCompact K :=
    Ψ.isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_le_one hΨ τ
  have htK (k : ℕ) : f.analyticMap hΦ hΨ (Φ.analyticTorusι hΦ hΦ0 (t k)) ∈ K := by
    rw [f.analyticMap_analyticTorusι]
    refine Ψ.analyticTorusι_mem_image_setOf_forall_norm_apply_single_le_one hΨ _ fun m ↦ ?_
    have hm : 0 ≤ Ψ.lattice.realCharacter m (f.realMap ((k : ℝ) • w)) :=
      (mem_dualSemigroup _ _).1 m.2 (by rw [map_smul]; exact τ.1.smul_mem k.cast_nonneg hw)
    rw [complexTorusMap_apply, characterEvaluation_apply, ← Real.exp_zero]
    convert Real.exp_le_exp.2 (neg_nonpos.2 hm) using 1
    rw [← LinearMap.comp_apply, ← Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap
      f.realMap f.map_lattice]
    exact ht k _
  -- By properness the `t k` cluster at a point `p` whose image lies in the chart of `τ`.
  obtain ⟨p, hpK, hp⟩ := (hf.isCompact_preimage hK).exists_mapClusterPt
    (u := fun k ↦ Φ.analyticTorusι hΦ hΦ0 (t k)) (f := atTop)
    (tendsto_principal.2 (Eventually.of_forall fun k ↦ htK k))
  have hpτ : f.analyticMap hΦ hΨ p ∈ range (Ψ.analyticAffineChartι hΨ τ) :=
    image_subset_range _ _ hpK
  -- The point `p` lies in the orbit of a source cone `σ` mapped into `τ`, hence in its chart.
  rw [← mem_preimage, f.preimage_analyticMap_range_analyticAffineChartι hΦ hΨ τ,
    mem_iUnion₂] at hpτ
  obtain ⟨σ, hστ, hpσ⟩ := hpτ
  obtain ⟨y, rfl⟩ := (Φ.mem_range_analyticAffineChartι_iff hΦ hpσ).2 le_rfl
  exact mem_iUnion₂.2 ⟨σ, hστ, Φ.mem_of_mapClusterPt_analyticTorusι hΦ hΦ0 ht hp⟩

end TauCeti.Toric.FanHom
