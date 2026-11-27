/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Integrals of invariant top forms under finite group actions

Let a finite group `G` act on an oriented manifold `M` by orientation-preserving homeomorphisms,
and let `ω` be a compactly supported continuous top form on `M` invariant under `G`. On an
orbifold chart `U / G` the integral of `ω` is weighted by the order of the full chart group,
`|G|⁻¹ ∫_U ω`, so that every point is counted with the inverse order of its isotropy group. This
file proves the formula that compares such weights for different groups: the **isotropy index
formula**.

Let `V ⊆ M` be an open set whose translates `g • V` are each equal to `V` or disjoint from it, a
block of the action (`MulAction.IsBlock`), and let `H = {g | g • V = V}` be its stabilizer. If `ω`
is supported in `G • V`, then

`|G|⁻¹ ∫_M ω = |H|⁻¹ ∫_V ω`

(`TauCeti.inv_natCard_mul_integralTopForm_eq_of_isBlock`). The translates of `V`
correspond to the cosets `G / H`, they cover the support of `ω`, and each contributes
`∫_V ω`, since `ω` is invariant and `g` preserves orientations. So the chart `V / H` computes the
same weighted integral as the chart `M / G`. For instance, `V` may be a slice chart around a point
with isotropy group `H`, inside an ambient chart `M / G`, with `G • V` a neighbourhood of its
orbit.

The splitting of `ω` along the translates uses the restriction of a form to a set, extended by
zero (`TauCeti.RoughForm.indicator`), and the criterion `TauCeti.IsSmoothForm.indicator` for such
a restriction to an open set to be `C^n`.

The finite counting behind the weight `|G|⁻¹`, which assigns weight `|G_x|⁻¹` to a point `x` with
stabilizer `G_x`, is `MulAction.inv_natCard_mul_sum_eq_sum_quotient`.

## Main results

* `TauCeti.IsSmoothForm.indicator_smul_set_of_isBlock`: the restrictions of a `C^n` form
  supported in the translates of an open block to the translates are `C^n`.
* `TauCeti.tsupport_indicator_subset_of_isBlock`: the restriction of such a form to the block `V`
  has support in `V`.
* `TauCeti.sum_indicator_smul_set_eq_natCard_smul`: for a form supported in the union of the
  translates of a block, the restrictions of the form to the translates add up to the order of
  the stabilizer of the block times the form.
* `TauCeti.inv_natCard_mul_integralTopForm_eq_of_isBlock`: the isotropy index formula.

## References

* Alejandro Adem, Johann Leida and Yongbin Ruan, *Orbifolds and Stringy Topology*, Cambridge
  Tracts in Mathematics 171, Cambridge University Press, 2007, Section 2.1 (integration on
  orbifolds).
* Ieke Moerdijk and Dorette A. Pronk, *Orbifolds, sheaves and groupoids*, K-Theory 12 (1997),
  3–21.
-/

public section

noncomputable section

open Set Filter MulAction
open scoped Manifold Topology Pointwise

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable {G : Type*} [Group G] [MulAction G M]

/-- Pulling the restriction of a form to `g • V` back along `g` gives the restriction to `V` of
the pulled back form. -/
theorem mpullback_smul_indicator_smul_set (g : G) (V : Set M) (ω : RoughForm I M F k) :
    mpullback I I (fun x : M ↦ g • x) (ω.indicator (g • V)) =
      (mpullback I I (fun x : M ↦ g • x) ω).indicator V := by
  rw [RoughForm.mpullback_indicator, preimage_smul, inv_smul_smul]

/-- If `V` is a block of the action, its translates being pairwise equal or disjoint, then for a
form supported in their union the restrictions of the form to the translates of `V` add up to `|H|`
times the form, for the stabilizer `H` of `V`. -/
theorem sum_indicator_smul_set_eq_natCard_smul [Fintype G] {V : Set M} (hV : IsBlock G V)
    (ω : RoughForm I M F k)
    (hsupp : Function.support (M := E [⋀^Fin k]→L[ℝ] F) ω ⊆ ⋃ g : G, g • V) :
    ∑ g : G, ω.indicator (g • V) = (Nat.card (stabilizer G V) : ℝ) • ω := by
  classical
  funext x
  rw [Finset.sum_apply, Pi.smul_apply]
  by_cases hx : ω x = 0
  · simp [RoughForm.indicator_apply, hx]
  obtain ⟨g₀, hg₀⟩ := mem_iUnion.mp (hsupp hx)
  -- The translates containing `x` are exactly those equal to `g₀ • V`, and the elements `g` with
  -- `g • V = g₀ • V` form the coset `g₀ H`.
  have hmem (g : G) : x ∈ g • V ↔ g₀⁻¹ * g ∈ stabilizer G V := by
    rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hg₀⟩
    rcases isBlock_iff_smul_eq_smul_or_disjoint.mp hV g g₀ with h' | h'
    · exact h'
    · exact absurd hg₀ (h'.notMem_of_mem_left h)
  simp_rw [RoughForm.indicator_apply, hmem]
  -- Reindexing along `g ↦ g₀ * g` turns the sum into a count of the elements of `H`.
  rw [← Equiv.sum_comp (Equiv.mulLeft g₀)]
  simp [Finset.sum_ite, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.cast_smul_eq_nsmul]

/-- Let `V` be an open block of the action, its translates being pairwise equal or disjoint, and
let `ω` be supported in the union of the translates. Then the support of the restriction of `ω` to
`V` lies in `V`. -/
theorem tsupport_indicator_subset_of_isBlock [ContinuousConstSMul G M] {V : Set M}
    (hVo : IsOpen V) (hV : IsBlock G V) {ω : RoughForm I M F k}
    (hsupp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω ⊆ ⋃ g : G, g • V) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (ω.indicator V) ⊆ V := by
  -- A point of the support of `ω` outside `V` lies in a translate disjoint from `V`, which is a
  -- neighbourhood of it missing `V`.
  intro x hx
  obtain ⟨g, hg⟩ := mem_iUnion.mp (hsupp (RoughForm.tsupport_indicator_subset _ ω hx))
  rcases hV.smul_eq_or_disjoint g with h | h
  · exact h ▸ hg
  · exact absurd (mem_closure_iff.mp (RoughForm.tsupport_indicator_subset_closure _ ω hx) _
      (hVo.smul g) hg) (not_nonempty_iff_eq_empty.mpr h.inter_eq)

variable [IsManifold I 1 M]

/-- Let `V` be an open block of the action, its translates being pairwise equal or disjoint, and
let `ω` be a `C^n` form supported in the union of the translates. Then the restriction of `ω` to
each translate is `C^n`. -/
theorem IsSmoothForm.indicator_smul_set_of_isBlock [ContinuousConstSMul G M] {n : WithTop ℕ∞}
    {ω : RoughForm I M F k} (hω : IsSmoothForm I n ω) {V : Set M} (hVo : IsOpen V)
    (hV : IsBlock G V) (hsupp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω ⊆ ⋃ g : G, g • V)
    (g : G) : IsSmoothForm I n (ω.indicator (g • V)) := by
  -- The restriction vanishes near every point outside the translate: away from the support of `ω`
  -- because `ω` does, and on the support because a different translate, disjoint from this one, is
  -- a neighbourhood there.
  refine hω.indicator (hVo.smul g) fun x hx ↦ ?_
  by_cases hxs : x ∈ _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ω
  · obtain ⟨g', hg'⟩ := mem_iUnion.mp (hsupp hxs)
    rcases isBlock_iff_smul_eq_smul_or_disjoint.mp hV g' g with h | h
    · exact absurd (h ▸ hg') hx
    · filter_upwards [(hVo.smul g').mem_nhds hg'] with y hy
      exact RoughForm.indicator_apply_of_notMem ω (h.notMem_of_mem_left hy)
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
    by_cases hyg : y ∈ g • V
    · rw [RoughForm.indicator_apply_of_mem ω hyg]
      exact hy
    · exact RoughForm.indicator_apply_of_notMem ω hyg

variable [FiniteDimensional ℝ E]

/-- **The isotropy index formula.** Let a finite group `G` act on an oriented manifold by
orientation-preserving homeomorphisms, and let `ω` be a compactly supported continuous
`G`-invariant top form. If `V` is an open block of the action, its translates being pairwise
equal or disjoint, and `ω` is supported in `G • V`, then the weighted integrals over the charts
`M / G` and `V / H`, for the stabilizer `H` of `V`, agree: `|G|⁻¹ ∫_M ω = |H|⁻¹ ∫_V ω`. -/
theorem inv_natCard_mul_integralTopForm_eq_of_isBlock [Finite G]
    [ContinuousConstSMul G M] (o : Manifold.Orientation I M (Fin k))
    (ho : ∀ (g : G) x, Manifold.Orientation.IsOrientationPreservingAt o o (fun y : M ↦ g • y) x)
    {ω : RoughForm I M ℝ k} (hω : IsSmoothForm I 0 ω)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ω))
    (hinv : ∀ g : G, mpullback I I (fun x : M ↦ g • x) ω = ω) (V : TopologicalSpace.Opens M)
    (hV : IsBlock G (V : Set M))
    (hsupp : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ω ⊆ ⋃ g : G, g • (V : Set M)) :
    (Nat.card G : ℝ)⁻¹ * integralTopForm o ω =
      (Nat.card (stabilizer G (V : Set M)) : ℝ)⁻¹ *
        integralTopForm (o.restrict V) (mpullback I I ((↑) : V → M) ω) := by
  classical
  have := Fintype.ofFinite G
  have hb : Module.Basis (Fin k) ℝ E :=
    Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  -- Each translate contributes the integral over `V`, since `g` preserves `ω` and orientations.
  have hφ1 (g : G) :
      integralTopForm o (ω.indicator (g • (V : Set M))) = integralTopForm o (ω.indicator V) := by
    have he : Topology.IsOpenEmbedding fun x : M ↦ g • x := (Homeomorph.smul g).isOpenEmbedding
    rw [← he.integralTopForm_mpullback_of_isOrientationPreservingAt (ho g)
        fun x _ ↦ ⟨g⁻¹ • x, smul_inv_smul g x⟩,
      mpullback_smul_indicator_smul_set, hinv]
  -- Each restriction to a translate is continuous and compactly supported, hence integrable.
  have hint (g : G) : IntegrableTopForm (ω.indicator (g • (V : Set M))) :=
    (hω.indicator_smul_set_of_isBlock V.isOpen hV hsupp g).integrableTopForm
      (hc.of_isClosed_subset (isClosed_tsupport _) (RoughForm.tsupport_indicator_subset _ ω)) hb
  have hsum := congrArg (integralTopForm o)
    (sum_indicator_smul_set_eq_natCard_smul hV ω ((subset_tsupport _).trans hsupp))
  rw [integralTopForm_smul, integralTopForm_sum o _ Finset.univ fun g _ ↦ hint g] at hsum
  simp only [hφ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    at hsum
  -- The restriction to `V` integrates as the form on the open subset `V`.
  rw [← integralTopForm_mpullback_subtypeVal o V
      (tsupport_indicator_subset_of_isBlock V.isOpen hV hsupp),
    RoughForm.mpullback_subtypeVal_indicator] at hsum
  have hG : (Nat.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : (Nat.card (stabilizer G (V : Set M)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  linarith

end TauCeti
