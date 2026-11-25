/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex.Basic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact

/-!
# Stability of the fixed-point index under small perturbations

Let `E` be a finite-dimensional real normed space, `U ⊆ E` an open set and `f : U → E` a
continuous map with compact fixed set. The fixed points of `f` may be degenerate, and need not
even be isolated. This file shows that the fixed-point index `ContinuousMap.fixedPointIndex` of
`f` is the index of every map `g` that is uniformly close to `f` on a suitable neighbourhood `V`
of the fixed set (`ContinuousMap.exists_pos_forall_fixedPointIndex_eq`):

there are an open set `V ⊆ U` containing every fixed point of `f`, with compact closure inside
`U`, and `δ > 0`, such that every continuous `g : V → E` with `‖g z - f z‖ < δ` on `V` has a
compact fixed set and `i(g) = i(f)`.

In particular, if such a `g` has only nondegenerate fixed points, then it has finitely many and
their signed count `∑ sign det (1 - g'(x))` is the index of `f`
(`ContinuousMap.fixedPointIndex_eq_sum_sign_det`), whichever perturbation `g` is used. This is
how a degenerate fixed set is counted: through any small perturbation with nondegenerate fixed
points, computed on a neighbourhood whose boundary carries no fixed points.

The comparison behind it is the fixed-point form of Rouché's principle
(`ContinuousMap.fixedPointIndex_eq_of_norm_sub_lt`): if `‖g z - f z‖ < ‖f z - z‖ + ‖g z - z‖`
outside a compact set `K`, then no point outside `K` lies on the segment from `f z` to `g z`, so
the straight-line homotopy from `f` to `g` has its fixed points over `K` and the two indices
agree. For the stability theorem, `V` is a thickening of the fixed set of `f` and `δ` is the
least displacement `‖f z - z‖` on the annulus between that thickening and a thinner one.

## Main results

* `ContinuousMap.isCompact_setOf_apply_eq_of_norm_sub_lt`,
  `ContinuousMap.fixedPointIndex_eq_of_norm_sub_lt`: Rouché's principle for the fixed-point
  index.
* `ContinuousMap.exists_pos_forall_fixedPointIndex_eq`: the index is unchanged by small
  perturbations on an isolating neighbourhood of the fixed set.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5.
* R. F. Brown, *The Lefschetz Fixed Point Theorem*, Scott, Foresman and Co., 1971, Chapter IV.
-/

public section

open Metric Set Topology TopologicalSpace

namespace ContinuousMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let `f, g : s → E` be continuous on a subset `s` of `E`. If
`‖g z - f z‖ < ‖f z - z‖ + ‖g z - z‖` at every point outside a compact set `K`, then every fixed
point of `g` lies in `K`, so the fixed set of `g` is compact. -/
theorem isCompact_setOf_apply_eq_of_norm_sub_lt {s : Set E} {f g : C(s, E)} {K : Set s}
    (hK : IsCompact K)
    (hfg : ∀ z ∉ K, ‖g z - f z‖ < ‖f z - z‖ + ‖g z - z‖) :
    IsCompact {z | g z = z} := by
  refine hK.of_isClosed_subset (isClosed_eq g.continuous continuous_subtypeVal) fun z hz ↦ ?_
  by_contra hzK
  have h := hfg z hzK
  rw [mem_ofPred_eq] at hz
  simp [hz, norm_sub_rev] at h

/-- **Rouché's principle for the fixed-point index.** If `‖g z - f z‖ < ‖f z - z‖ + ‖g z - z‖`
at every point outside a compact set `K`, then `f` and `g` have the same fixed-point index: the
straight-line homotopy from `f` to `g` has no fixed point outside `K`. -/
theorem fixedPointIndex_eq_of_norm_sub_lt {f g : C(U, E)} {K : Set U} (hK : IsCompact K)
    (hfg : ∀ z ∉ K, ‖g z - f z‖ < ‖f z - z‖ + ‖g z - z‖) :
    f.fixedPointIndex = g.fixedPointIndex := by
  refine fixedPointIndex_eq_of_homotopy (.affine f g) ((isCompact_univ.prod hK).of_isClosed_subset
    (isClosed_eq (Homotopy.affine f g).continuous (continuous_subtypeVal.comp continuous_snd))
    fun ⟨t, z⟩ hz ↦ ⟨mem_univ t, ?_⟩)
  by_contra hzK
  -- A fixed point `z` lies on the segment from `f z` to `g z`, so its distances to the endpoints
  -- add up to only `‖g z - f z‖`.
  simp only [mem_ofPred_eq, Homotopy.affine_apply] at hz
  have hle := (show Wbtw ℝ (f z) (z : E) (g z) from ⟨t, t.property, hz⟩).dist_add_dist
  exact (hfg z hzK).ne' (by simpa only [dist_eq_norm, norm_sub_rev] using hle)

/-- **Stability of the fixed-point index.** Let `f : U → E` have a compact fixed set. There are
an open set `V ⊆ U` containing every fixed point of `f`, with compact closure contained in `U`,
and `δ > 0` with the following property: every continuous map `g : V → E` with
`‖g z - f z‖ < δ` for all `z ∈ V` has a compact fixed set and the same fixed-point index as `f`.

The fixed points of `f` may be degenerate. If those of `g` are nondegenerate, they are finitely
many and the index of `f` is their signed count (`ContinuousMap.fixedPointIndex_eq_sum_sign_det`),
for every such perturbation `g`. -/
theorem exists_pos_forall_fixedPointIndex_eq (f : C(U, E)) (hf : IsCompact {z | f z = z}) :
    ∃ V : Opens E, ∃ hVU : V ≤ U, (∀ z, f z = z → (z : E) ∈ V) ∧
      IsCompact (closure (V : Set E)) ∧ closure (V : Set E) ⊆ U ∧
      ∃ δ > 0, ∀ g : C(V, E), (∀ z, ‖g z - f (inclusion hVU z)‖ < δ) →
        IsCompact {z | g z = z} ∧ g.fixedPointIndex = f.fixedPointIndex := by
  set F : Set E := Subtype.val '' {z | f z = z}
  have hF : IsCompact F := hf.image continuous_subtypeVal
  obtain ⟨ρ, hρ, hρU⟩ := hF.exists_cthickening_subset_open U.isOpen (by
    rintro _ ⟨z, -, rfl⟩
    exact z.property)
  let V : Opens E := ⟨thickening ρ F, isOpen_thickening⟩
  have hVU : V ≤ U := (thickening_subset_cthickening ρ F).trans hρU
  have hclV : closure (V : Set E) ⊆ cthickening ρ F := closure_thickening_subset_cthickening ρ F
  -- On the annulus `A` between the `ρ / 2`- and `ρ`-thickenings of the fixed set, the
  -- displacement `‖f z - z‖` is bounded below by some `δ > 0`.
  set A : Set E := cthickening ρ F \ thickening (ρ / 2) F
  have hA : IsCompact (Subtype.val ⁻¹' A : Set U) :=
    IsInducing.subtypeVal.isCompact_preimage' (hF.cthickening.diff isOpen_thickening)
      (by rw [Subtype.range_coe]; exact sdiff_subset.trans hρU)
  obtain ⟨δ, hδ, hδA⟩ := hA.exists_forall_le' (f := fun z ↦ ‖f z - z‖) (by fun_prop) (a := 0)
    fun z hz ↦ norm_pos_iff.2 (sub_ne_zero.2 fun hfz ↦
      hz.2 (self_subset_thickening (half_pos hρ) F ⟨z, hfz, rfl⟩))
  refine ⟨V, hVU, fun z hz ↦ self_subset_thickening hρ F ⟨z, hz, rfl⟩,
    hF.cthickening.of_isClosed_subset isClosed_closure hclV, hclV.trans hρU, δ, hδ,
    fun g hg ↦ ?_⟩
  -- Outside the compact set `K` of points of `V` in the `ρ / 2`-thickening, the points of `V` lie
  -- in the annulus, so `g` is closer to `f` than `f` is to the identity.
  set K : Set V := Subtype.val ⁻¹' cthickening (ρ / 2) F
  have hK : IsCompact K := IsInducing.subtypeVal.isCompact_preimage' hF.cthickening (by
    rw [Subtype.range_coe]
    exact cthickening_subset_thickening' hρ (half_lt_self hρ) F)
  have hfg (z : V) (hz : z ∉ K) :
      ‖g z - f.comp (inclusion hVU) z‖ < ‖f.comp (inclusion hVU) z - z‖ + ‖g z - z‖ := by
    have hzA : inclusion hVU z ∈ (Subtype.val ⁻¹' A : Set U) :=
      ⟨thickening_subset_cthickening ρ F z.property,
        fun h ↦ hz (thickening_subset_cthickening (ρ / 2) F h)⟩
    calc ‖g z - f.comp (inclusion hVU) z‖ < δ := hg z
      _ ≤ ‖f.comp (inclusion hVU) z - z‖ := hδA _ hzA
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)
  refine ⟨isCompact_setOf_apply_eq_of_norm_sub_lt hK hfg, ?_⟩
  rw [← fixedPointIndex_eq_of_norm_sub_lt hK hfg,
    fixedPointIndex_comp_inclusion hVU f fun z hz ↦ self_subset_thickening hρ F ⟨z, hz, rfl⟩]

end ContinuousMap
