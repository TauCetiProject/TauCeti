/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.MulAction
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Making bounded scalar actions contractive

For a module with an explicit action bound `‖a • x‖ ≤ C * ‖a‖ * ‖x‖`, the adapted norm
is `sup_a ‖a • x‖ / ‖a‖`. The zero scalar contributes zero, so this is also the supremum
over nonzero scalars. Over a norm-one ring it lies between the original norm and `C` times
that norm, and scalar multiplication is contractive for the adapted norm. Ultrametricity
of the original module norm is preserved. No multiplicativity of the scalar norm is needed.

`adaptedAddGroupNorm` bundles this construction using the native additive norm interface.
`adaptedNormedAddCommGroup` retains the original uniformity and topology definitionally, so
completeness, continuity, and potential orthonormalisability transport without new instances.
Install its contractive-action and ultrametric structures explicitly using
`isBoundedSMul_adaptedNormedAddCommGroup` and `isUltrametricDist_adaptedNormedAddCommGroup`.
The construction applies to the zero module as well, and does not require completeness.
-/

public section

open scoped NNReal Uniformity

namespace TauCeti

variable (R : Type*) [SeminormedRing R]

section Seminormed

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M]

/-- The supremum of the scalar-action ratios. Under a uniform action bound it is finite;
when the scalar norm is normalized at one, it is an equivalent seminorm on the module.
It is a norm when the original seminorm separates points. -/
noncomputable def adaptedNorm (x : M) : ℝ := ⨆ a : R, ‖a • x‖ / ‖a‖

variable {R} {C : ℝ≥0}

/-- An explicit action bound bounds the family defining the adapted norm. -/
theorem bddAbove_range_actionRatio
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    BddAbove (Set.range fun a : R ↦ ‖a • x‖ / ‖a‖) := by
  refine ⟨C * ‖x‖, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact div_le_of_le_mul₀ (norm_nonneg a) (mul_nonneg C.coe_nonneg (norm_nonneg x))
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using h a x)

/-- The adapted norm is at most the given action constant times the original norm. -/
theorem adaptedNorm_le
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    adaptedNorm R x ≤ C * ‖x‖ := by
  refine ciSup_le fun a ↦ ?_
  exact div_le_of_le_mul₀ (norm_nonneg a) (mul_nonneg C.coe_nonneg (norm_nonneg x))
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using h a x)

/-- Each scalar-action ratio is bounded by the adapted norm. -/
theorem actionRatio_le_adaptedNorm
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (a : R) (x : M) :
    ‖a • x‖ / ‖a‖ ≤ adaptedNorm R x :=
  le_ciSup (bddAbove_range_actionRatio h x) a

/-- The adapted norm is nonnegative, including on the zero module. -/
theorem adaptedNorm_nonneg
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    0 ≤ adaptedNorm R x := by
  simpa using actionRatio_le_adaptedNorm h 0 x

/-- The adapted norm vanishes at zero. -/
@[simp]
theorem adaptedNorm_zero : adaptedNorm R (0 : M) = 0 := by
  simp [adaptedNorm]

/-- Negation preserves the adapted norm. -/
@[simp]
theorem adaptedNorm_neg (x : M) : adaptedNorm R (-x) = adaptedNorm R x := by
  simp [adaptedNorm]

/-- The adapted norm satisfies the triangle inequality. -/
theorem adaptedNorm_add_le
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x y : M) :
    adaptedNorm R (x + y) ≤ adaptedNorm R x + adaptedNorm R y := by
  refine ciSup_le fun a ↦ ?_
  calc
    ‖a • (x + y)‖ / ‖a‖ ≤ (‖a • x‖ + ‖a • y‖) / ‖a‖ :=
      div_le_div_of_nonneg_right (by simpa only [smul_add] using norm_add_le (a • x) (a • y))
        (norm_nonneg a)
    _ = ‖a • x‖ / ‖a‖ + ‖a • y‖ / ‖a‖ := add_div _ _ _
    _ ≤ adaptedNorm R x + adaptedNorm R y :=
      add_le_add (actionRatio_le_adaptedNorm h a x) (actionRatio_le_adaptedNorm h a y)

/-- Ultrametricity is preserved by the adapted norm. -/
theorem adaptedNorm_add_le_max [IsUltrametricDist M]
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x y : M) :
    adaptedNorm R (x + y) ≤ max (adaptedNorm R x) (adaptedNorm R y) := by
  refine ciSup_le fun a ↦ ?_
  calc
    ‖a • (x + y)‖ / ‖a‖ ≤ max ‖a • x‖ ‖a • y‖ / ‖a‖ :=
      div_le_div_of_nonneg_right (by simpa only [smul_add] using
        IsUltrametricDist.norm_add_le_max (a • x) (a • y)) (norm_nonneg a)
    _ = max (‖a • x‖ / ‖a‖) (‖a • y‖ / ‖a‖) :=
      (max_div_div_right (norm_nonneg a) _ _).symm
    _ ≤ max (adaptedNorm R x) (adaptedNorm R y) :=
      max_le_max (actionRatio_le_adaptedNorm h a x) (actionRatio_le_adaptedNorm h a y)

/-- The un-divided scalar-action estimate supplied by the adapted norm. -/
theorem norm_smul_le_mul_adaptedNorm
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (a : R) (x : M) :
    ‖a • x‖ ≤ ‖a‖ * adaptedNorm R x := by
  by_cases ha : ‖a‖ = 0
  · simpa [ha] using h a x
  · exact (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha))).mp
      (actionRatio_le_adaptedNorm h a x) |>.trans_eq (mul_comm _ _)

/-- A nonnegative bound on the adapted norm is equivalent to a uniform scalar-action bound. -/
theorem adaptedNorm_le_iff
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) {B : ℝ} (hB : 0 ≤ B) :
    adaptedNorm R x ≤ B ↔ ∀ a : R, ‖a • x‖ ≤ ‖a‖ * B := by
  constructor
  · intro hx a
    exact (norm_smul_le_mul_adaptedNorm h a x).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  · intro hx
    exact ciSup_le fun a ↦ div_le_of_le_mul₀ (norm_nonneg _) hB (by
      simpa only [mul_comm] using hx a)

/-- The scalar action is contractive for the adapted norm. -/
theorem adaptedNorm_smul_le
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (a : R) (x : M) :
    adaptedNorm R (a • x) ≤ ‖a‖ * adaptedNorm R x := by
  refine ciSup_le fun b ↦ ?_
  by_cases hb : ‖b‖ = 0
  · simpa only [hb, div_zero] using mul_nonneg (norm_nonneg a) (adaptedNorm_nonneg h x)
  · apply (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb))).mpr
    calc
      ‖b • (a • x)‖ = ‖(b * a) • x‖ := by rw [mul_smul]
      _ ≤ ‖b * a‖ * adaptedNorm R x := norm_smul_le_mul_adaptedNorm h _ _
      _ ≤ (‖b‖ * ‖a‖) * adaptedNorm R x :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (adaptedNorm_nonneg h x)
      _ = (‖a‖ * adaptedNorm R x) * ‖b‖ := by ring

variable [NormOneClass R]

/-- The original norm is bounded by the adapted norm, by testing the scalar one. -/
theorem norm_le_adaptedNorm
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    ‖x‖ ≤ adaptedNorm R x := by
  simpa using actionRatio_le_adaptedNorm h 1 x

/-- Contractive scalar actions leave the norm unchanged under adaptation. -/
@[simp]
theorem adaptedNorm_eq_norm [IsBoundedSMul R M] (x : M) : adaptedNorm R x = ‖x‖ := by
  have h (a : R) (y : M) : ‖a • y‖ ≤ (1 : ℝ≥0) * ‖a‖ * ‖y‖ := by
    simpa only [NNReal.coe_one, one_mul] using norm_smul_le a y
  exact le_antisymm (by simpa using adaptedNorm_le h x) (norm_le_adaptedNorm h x)

end Seminormed

variable {R} {C : ℝ≥0} {M : Type*} [NormedAddCommGroup M] [Module R M] [NormOneClass R]

/-- The adapted norm, bundled as a native additive group norm. -/
noncomputable def adaptedAddGroupNorm
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) : AddGroupNorm M where
  toFun := adaptedNorm R
  map_zero' := adaptedNorm_zero
  add_le' := adaptedNorm_add_le h
  neg' := adaptedNorm_neg
  eq_zero_of_map_eq_zero' x hx := norm_eq_zero.mp <|
    le_antisymm ((norm_le_adaptedNorm h x).trans_eq hx) (norm_nonneg _)

/-- Evaluation of the bundled adapted norm. -/
@[simp]
theorem adaptedAddGroupNorm_apply
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    adaptedAddGroupNorm h x = adaptedNorm R x := (rfl)

/-- The adapted additive norm induces the original uniformity. -/
theorem adaptedAddGroupNorm_uniformity
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) :
    𝓤 M = @uniformity M (adaptedAddGroupNorm h).toNormedAddCommGroup.toUniformSpace := by
  have hupper := adaptedNorm_le h
  have hlower := norm_le_adaptedNorm h
  let g := ‹NormedAddCommGroup M›
  have hn (x : M) : adaptedAddGroupNorm h x = adaptedNorm R x :=
    adaptedAddGroupNorm_apply h x
  let n := (adaptedAddGroupNorm h).toNormedAddCommGroup
  -- Restore the original instance for implicit arguments; the second metric is always explicit.
  let := g
  -- The native metric constructor evaluates the norm on the additive difference.
  have hd (x y : M) : @dist M n.toDist x y = adaptedNorm R (-x + y) := hn _
  have hf : @UniformContinuous M M g.toUniformSpace n.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M g.toPseudoEMetricSpace n.toPseudoEMetricSpace C id
    apply @LipschitzWith.of_dist_le_mul M M g.toPseudoMetricSpace n.toPseudoMetricSpace C id
    intro x y
    simpa only [id_eq, hd, dist_eq_norm_neg_add] using hupper (-x + y)
  have hg : @UniformContinuous M M n.toUniformSpace g.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M n.toPseudoEMetricSpace g.toPseudoEMetricSpace 1 id
    apply @LipschitzWith.of_dist_le_mul M M n.toPseudoMetricSpace g.toPseudoMetricSpace 1 id
    intro x y
    simpa only [id_eq, hd, NNReal.coe_one, one_mul, dist_eq_norm_neg_add] using hlower (-x + y)
  apply le_antisymm
  · intro s hs
    exact @uniformContinuous_def M M g.toUniformSpace n.toUniformSpace id |>.mp hf s hs
  · intro s hs
    exact @uniformContinuous_def M M n.toUniformSpace g.toUniformSpace id |>.mp hg s hs

/-- A contractive renorming retaining the original uniformity and topology definitionally.
Consequently existing completeness and continuity proofs, and continuous linear equivalences,
remain usable after installing this structure locally. -/
noncomputable abbrev adaptedNormedAddCommGroup
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) : NormedAddCommGroup M :=
  { (adaptedAddGroupNorm h).toNormedAddCommGroup with
    toMetricSpace := (adaptedAddGroupNorm h).toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (adaptedAddGroupNorm_uniformity h) }

/-- The norm in the renormed structure is the adapted norm, not the original one. -/
@[simp]
theorem norm_adaptedNormedAddCommGroup
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) (x : M) :
    @norm M (adaptedNormedAddCommGroup h).toNorm x = adaptedNorm R x := (rfl)

/-- The scalar action is bounded with constant one after contractive renorming. -/
theorem isBoundedSMul_adaptedNormedAddCommGroup
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) :
    letI := adaptedNormedAddCommGroup h
    IsBoundedSMul R M := by
  have hs := adaptedNorm_smul_le h
  let := adaptedNormedAddCommGroup h
  exact IsBoundedSMul.of_norm_smul_le hs

/-- An ultrametric module remains ultrametric after contractive renorming. -/
theorem isUltrametricDist_adaptedNormedAddCommGroup [IsUltrametricDist M]
    (h : ∀ (a : R) (x : M), ‖a • x‖ ≤ C * ‖a‖ * ‖x‖) :
    letI := adaptedNormedAddCommGroup h
    IsUltrametricDist M := by
  have hadd := adaptedNorm_add_le_max h
  let := adaptedNormedAddCommGroup h
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hadd

end TauCeti
