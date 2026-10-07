/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import TauCeti.Geometry.Toric.Analytic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Analytic.Fan.Topology

/-!
# Compactness of the analytic realization of a regular fan

A nonempty regular fan has compact analytic realization exactly when it is complete, that is,
when its cones cover the ambient real vector space `V`.

Both directions read the absolute values of characters on the dense torus. For a torus point `t`,
the numbers `-log ‖t m‖` are additive in the character `m`, so they are the values at a single
point `w` of `V` of the real extensions of the characters
(`TauCeti.Toric.IsIntegralLattice.exists_realCharacter_apply_eq`). When `w` lies in a cone `σ`,
every character of the dual semigroup of `σ` has absolute value at most `1` at `t`, so `t` lies in
the image of the compact part of the chart of `σ` where all monomials are bounded by `1`
(`TauCeti.Toric.isCompact_setOf_forall_norm_apply_single_le_one`). For a complete fan these
finitely many compact sets cover the dense torus, and hence its closure, the whole realization.

Conversely, given `w` in `V`, the torus points `t k` with `‖t k m‖ = exp (-k ⟨m, w⟩)` have a
cluster point in a compact realization, which lies in the chart of some cone `σ`. Near that
point every character of the dual semigroup of `σ` is bounded, which forces `0 ≤ ⟨m, w⟩` for
each of them, and a regular cone is cut out by its dual semigroup
(`TauCeti.Toric.IsRegularCone.mem_iff_forall_realCharacter_nonneg`), so `w ∈ σ`.

The converse needs the fan to be nonempty: the realization of the empty fan is empty, hence
compact, but the empty fan is not complete.

## Main declarations

* `TauCeti.Toric.IsIntegralLattice.exists_complexTorus_norm_eq`: for every `v` in `V`, a torus
  point at which every character `m` has absolute value `exp (-⟨m, v⟩)`.
* `TauCeti.Toric.Fan.isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_le_one`:
  the part of a chart where every monomial has absolute value at most `1` is compact.
* `TauCeti.Toric.Fan.mem_of_mapClusterPt_analyticTorusι`: if the torus points along the ray
  through `w` cluster at a point of the chart of a cone `σ`, then `w ∈ σ`.
* `TauCeti.Toric.Fan.compactSpace_analyticRealization_of_isComplete`: the realization of a
  complete regular fan is compact.
* `TauCeti.Toric.Fan.isComplete_of_compactSpace_analyticRealization`: a nonempty regular fan with
  compact realization is complete.
* `TauCeti.Toric.Fan.compactSpace_analyticRealization_iff_isComplete`: the two conditions are
  equivalent for a nonempty regular fan.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.4.
-/

public section

open Multiplicative Topology Filter Set

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- For every point `v` of `V` there is a torus point at which every integral character `m` has
absolute value `exp (-⟨m, v⟩)`. -/
theorem _root_.TauCeti.Toric.IsIntegralLattice.exists_complexTorus_norm_eq
    (h : IsIntegralLattice i) (v : V) :
    ∃ t : ComplexTorus N, ∀ m, ‖((t m : ℂˣ) : ℂ)‖ = Real.exp (-h.realCharacter m v) := by
  refine ⟨{ toFun m := Units.mk0 (Real.exp (-h.realCharacter m v) : ℂ)
              (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
            map_zero_eq_one' := by ext; simp
            map_add_eq_mul' a b := by
              ext
              simp only [map_add, LinearMap.add_apply, neg_add, Real.exp_add, Units.val_mul,
                Units.val_mk0]
              push_cast
              ring }, fun m ↦ ?_⟩
  simp [Complex.norm_exp]

/-- The part of the chart of a cone `σ` where every monomial has absolute value at most `1` is a
compact subset of the realization. -/
theorem isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_le_one
    (σ : Φ.cones) :
    IsCompact (Φ.analyticAffineChartι hΦ σ ''
      {x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) |
        ∀ s, ‖x (MonoidAlgebra.single (ofAdd s) 1)‖ ≤ 1}) := by
  have h := isCompact_setOf_forall_norm_apply_single_le_one (Φ.analyticChartGenerators σ).2
  rw [← Φ.analyticAffineChart_str_eq σ] at h
  -- The compact set lives in the chart, whose topology is not found by instance search.
  exact @IsCompact.image _ _ (Φ.analyticAffineChart σ).str _ _ _ h
    (Φ.analyticAffineChartι hΦ σ).hom.continuous

/-- A torus point at which every character of the dual semigroup of a cone `σ` has absolute value
at most `1` lies in the part of the chart of `σ` where every monomial has absolute value at
most `1`. -/
theorem analyticTorusι_mem_image_setOf_forall_norm_apply_single_le_one
    (hΦ0 : Nonempty Φ.cones) {σ : Φ.cones} {t : ComplexTorus N}
    (ht : ∀ m : dualSemigroup Φ.lattice σ.1, ‖((t m : ℂˣ) : ℂ)‖ ≤ 1) :
    Φ.analyticTorusι hΦ hΦ0 t ∈ Φ.analyticAffineChartι hΦ σ ''
      {x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) |
        ∀ s, ‖x (MonoidAlgebra.single (ofAdd s) 1)‖ ≤ 1} := by
  refine ⟨_, fun s ↦ ?_, (Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 σ t).symm⟩
  rw [AffineSemigroupComplexPoint.ambient_smul_apply_single, default_apply_single, mul_one]
  exact ht s

/-- For a complete fan, every point of the dense torus lies in the chart of some cone at a point
where every monomial has absolute value at most `1`. -/
private theorem analyticTorusι_mem_iUnion_image (hc : Φ.IsComplete) (hΦ0 : Nonempty Φ.cones)
    (t : ComplexTorus N) :
    Φ.analyticTorusι hΦ hΦ0 t ∈ ⋃ σ : Φ.cones, Φ.analyticAffineChartι hΦ σ ''
      {x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) |
        ∀ s, ‖x (MonoidAlgebra.single (ofAdd s) 1)‖ ≤ 1} := by
  -- The point `w` of `V` at which the characters take the values `-log ‖t m‖`.
  let f : (N →+ ℤ) →+ ℝ :=
    { toFun m := -Real.log ‖((t m : ℂˣ) : ℂ)‖
      map_zero' := by simp
      map_add' a b := by
        rw [AddChar.map_add_eq_mul, Units.val_mul, norm_mul,
          Real.log_mul (norm_ne_zero_iff.2 (t a).ne_zero) (norm_ne_zero_iff.2 (t b).ne_zero)]
        ring }
  obtain ⟨w, hw⟩ := Φ.lattice.exists_realCharacter_apply_eq f
  obtain ⟨σ, hσ, hwσ⟩ := Φ.isComplete_iff.1 hc w
  refine mem_iUnion.2 ⟨⟨σ, hσ⟩,
    Φ.analyticTorusι_mem_image_setOf_forall_norm_apply_single_le_one hΦ hΦ0 fun s ↦ ?_⟩
  have hs : 0 ≤ f s := hw s ▸ (mem_dualSemigroup _ _).1 s.2 hwσ
  have hfs : f s = -Real.log ‖((t s : ℂˣ) : ℂ)‖ := rfl
  exact (Real.log_nonpos_iff (norm_nonneg _)).1 (by linarith)

/-- The analytic realization of a complete regular fan is compact. -/
theorem compactSpace_analyticRealization_of_isComplete (hc : Φ.IsComplete) :
    CompactSpace (Φ.analyticRealization hΦ) := by
  obtain ⟨σ₀, hσ₀, -⟩ := Φ.isComplete_iff.1 hc 0
  have hΦ0 : Nonempty Φ.cones := ⟨⟨σ₀, hσ₀⟩⟩
  -- The parts of the charts where every monomial has absolute value at most `1` are compact, and
  -- they cover the dense torus, whose closure is the whole realization.
  let K : Φ.cones → Set (Φ.analyticRealization hΦ) := fun σ ↦
    Φ.analyticAffineChartι hΦ σ ''
      {x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) |
        ∀ s, ‖x (MonoidAlgebra.single (ofAdd s) 1)‖ ≤ 1}
  have hK : ∀ σ, IsCompact (K σ) :=
    Φ.isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_le_one hΦ
  have hd : Dense (range (Φ.analyticTorusι hΦ hΦ0)) := by
    rw [Φ.range_analyticTorusι hΦ hΦ0]
    exact Φ.dense_analyticDenseTorus hΦ hΦ0
  refine ⟨(isCompact_iUnion hK).of_isClosed_subset isClosed_univ ?_⟩
  rw [← hd.closure_eq]
  exact closure_minimal (range_subset_iff.2 (Φ.analyticTorusι_mem_iUnion_image hΦ hc hΦ0))
    (isCompact_iUnion hK).isClosed

/-- If a point of the chart of a cone `σ` is a cluster point of a family of torus points, then
each character of the dual semigroup of `σ` is frequently bounded on that family. -/
private theorem exists_frequently_norm_lt_of_mapClusterPt (hΦ0 : Nonempty Φ.cones)
    {ι : Type*} {l : Filter ι} {t : ι → ComplexTorus N} {σ : Φ.cones}
    {y : (Φ.analyticAffineChartDiagram).obj σ}
    (h : MapClusterPt (Φ.analyticAffineChartι hΦ σ y) l fun k ↦ Φ.analyticTorusι hΦ hΦ0 (t k))
    (m : dualSemigroup Φ.lattice σ.1) : ∃ C : ℝ, ∃ᶠ k in l, ‖((t k m : ℂˣ) : ℂ)‖ < C := by
  let g := (Φ.analyticChartGenerators σ).2
  -- The bundled chart point, read as an algebra homomorphism so that it can be evaluated.
  let y' : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) := y
  let C := ‖y' (MonoidAlgebra.single (ofAdd m) 1)‖ + 1
  let U : Set (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :=
    {z | ‖z (MonoidAlgebra.single (ofAdd m) 1)‖ < C}
  have hU : IsOpen[affinePointTopology g] U := by
    let _ := affinePointTopology g
    exact isOpen_lt (continuous_norm.comp (continuous_apply_single g _)) continuous_const
  rw [← Φ.analyticAffineChart_str_eq σ g] at hU
  have hyU : y' ∈ U := by
    simp only [U, C, mem_ofPred_eq]
    exact lt_add_one _
  have hnhds : Φ.analyticAffineChartι hΦ σ '' U ∈ 𝓝 (Φ.analyticAffineChartι hΦ σ y) :=
    ((Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).isOpenMap U hU).mem_nhds ⟨y, hyU, rfl⟩
  refine ⟨C, (mapClusterPt_iff_frequently.1 h _ hnhds).mono fun k ⟨z, hz, hzk⟩ ↦ ?_⟩
  rw [Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 σ] at hzk
  have hzt := (Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).injective hzk
  have hz' : ‖(t k • default : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
      (MonoidAlgebra.single (ofAdd m) 1)‖ < C := by
    rw [← hzt]
    exact hz
  rwa [AffineSemigroupComplexPoint.ambient_smul_apply_single, default_apply_single,
    mul_one] at hz'

/-- Let `t k` be torus points at which every integral character `m` has absolute value
`exp (-k ⟨m, w⟩)`. If they cluster at a point of the chart of a cone `σ`, then `w ∈ σ`. -/
theorem mem_of_mapClusterPt_analyticTorusι (hΦ0 : Nonempty Φ.cones) {w : V}
    {t : ℕ → ComplexTorus N}
    (ht : ∀ (k : ℕ) m, ‖((t k m : ℂˣ) : ℂ)‖ = Real.exp (-Φ.lattice.realCharacter m ((k : ℝ) • w)))
    {σ : Φ.cones} {y : (Φ.analyticAffineChartDiagram).obj σ}
    (h : MapClusterPt (Φ.analyticAffineChartι hΦ σ y) atTop
      fun k ↦ Φ.analyticTorusι hΦ hΦ0 (t k)) :
    w ∈ σ.1 := by
  -- Every character of the dual semigroup of `σ` stays frequently bounded along `t`, which forces
  -- it to be nonnegative at `w`.
  refine (IsRegularCone.mem_iff_forall_realCharacter_nonneg Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2)).2 fun m hm ↦ ?_
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨C, hC⟩ := Φ.exists_frequently_norm_lt_of_mapClusterPt hΦ hΦ0 h ⟨m, hm⟩
  -- Along `w` the absolute value of the character `m` tends to infinity.
  have hlim : Tendsto (fun k : ℕ ↦ (k : ℝ) * -Φ.lattice.realCharacter m w) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (neg_pos.2 hneg)
  have hev : ∀ᶠ k : ℕ in atTop, C ≤ ‖((t k m : ℂˣ) : ℂ)‖ :=
    Tendsto.congr (fun k ↦ by simp [ht, mul_neg]) (Real.tendsto_exp_atTop.comp hlim)
      |>.eventually_ge_atTop C
  obtain ⟨k, hk, hk'⟩ := (hC.and_eventually hev).exists
  exact lt_irrefl _ (hk.trans_le hk')

/-- A nonempty regular fan with compact analytic realization is complete. -/
theorem isComplete_of_compactSpace_analyticRealization (hΦ0 : Nonempty Φ.cones)
    [CompactSpace (Φ.analyticRealization hΦ)] : Φ.IsComplete := by
  refine Φ.isComplete_iff.2 fun w ↦ ?_
  -- A cluster point of the torus points `t k` with `‖t k m‖ = exp (-k ⟨m, w⟩)` lies in the chart
  -- of a cone `σ`, and then `w ∈ σ`.
  choose t ht using fun k : ℕ ↦ Φ.lattice.exists_complexTorus_norm_eq ((k : ℝ) • w)
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun k ↦ Φ.analyticTorusι hΦ hΦ0 (t k)) atTop)
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ p
  exact ⟨σ.1, σ.2, Φ.mem_of_mapClusterPt_analyticTorusι hΦ hΦ0 ht hp⟩

/-- A nonempty regular fan has compact analytic realization exactly when it is complete. The
nonemptiness hypothesis is necessary: the realization of the empty fan is empty, hence compact,
while the empty fan is not complete. -/
theorem compactSpace_analyticRealization_iff_isComplete (hΦ0 : Nonempty Φ.cones) :
    CompactSpace (Φ.analyticRealization hΦ) ↔ Φ.IsComplete :=
  ⟨fun _ ↦ Φ.isComplete_of_compactSpace_analyticRealization hΦ hΦ0,
    Φ.compactSpace_analyticRealization_of_isComplete hΦ⟩

end TauCeti.Toric.Fan
