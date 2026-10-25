/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.Snowflaking
public import TauCeti.Topology.MetricSpace.Holder.Norm

/-!
# Parabolic distance and Hölder seminorms

`ParabolicSpace X T` equips space-time with the distance
`dist x y + (dist t s) ^ (1 / 2)`, using Mathlib's `WithLp 1` product and snowflaked
time. Take `T = Set.Icc a b` for a closed slab, or `T = ℝ` for all times.
Its coordinate homeomorphism identifies its topology with the ordinary product topology;
classical differentiation can therefore be performed after transport to ordinary coordinates.

The parabolic Hölder seminorm is Mathlib's `eHolderNorm` on this carrier. It bounds each
spatial α seminorm and each temporal α/2 seminorm. Conversely, the sum of the two uniform
slice seminorms bounds the parabolic seminorm. Thus finiteness of the parabolic seminorm is
equivalent to uniform Hölder bounds on both families of slices. These comparisons require no
restriction on the nonnegative exponent and apply also to empty or singleton time intervals.

## References

A. Lunardi, *Linear and nonlinear diffusion problems*, Chapter 3, parabolic Hölder spaces.
The metric construction reuses `Metric.Snowflaking` and `WithLp.homeomorphProd`.
-/

public section

noncomputable section

namespace TauCeti

open scoped NNReal ENNReal

/-- Space-time with the sum of spatial distance and square root of temporal distance. -/
abbrev ParabolicSpace (X T : Type*) :=
  WithLp 1 (X × Metric.Snowflaking T (1 / 2) (by norm_num) (by norm_num))

namespace ParabolicSpace

variable {X T Y : Type*}

/-- The space-time point with spatial coordinate `x` and time coordinate `t`. -/
def mk (x : X) (t : T) : ParabolicSpace X T :=
  WithLp.toLp 1 (x, Metric.Snowflaking.toSnowflaking t)

/-- Every parabolic point has spatial and temporal coordinates. -/
theorem exists_mk_eq (p : ParabolicSpace X T) : ∃ x t, mk x t = p :=
  ⟨p.ofLp.1, p.ofLp.2.ofSnowflaking, rfl⟩

/-- Parabolic points are equal exactly when both coordinates are equal. -/
@[simp]
theorem mk_inj {x y : X} {t s : T} : mk x t = mk y s ↔ x = y ∧ t = s := by
  simp [mk]

/-- Ordinary product coordinates, with the same topology as the parabolic metric. -/
def homeomorphProd [TopologicalSpace X] [TopologicalSpace T] : ParabolicSpace X T ≃ₜ X × T :=
  (WithLp.homeomorphProd 1 X _).trans
    ((Homeomorph.refl X).prodCongr Metric.Snowflaking.homeomorph)

@[simp]
theorem homeomorphProd_mk [TopologicalSpace X] [TopologicalSpace T] (x : X) (t : T) :
    homeomorphProd (mk x t) = (x, t) := (rfl)

@[simp]
theorem homeomorphProd_symm_apply [TopologicalSpace X] [TopologicalSpace T] (p : X × T) :
    homeomorphProd.symm p = mk p.1 p.2 := (rfl)

/-- The parabolic distance in ordinary coordinates. -/
@[simp]
theorem dist_mk [PseudoMetricSpace X] [PseudoMetricSpace T] (x y : X) (t s : T) :
    dist (mk x t) (mk y s) = dist x y + dist t s ^ (1 / 2 : ℝ) := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp [mk]

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace T]

/-- The extended parabolic distance in ordinary coordinates. -/
@[simp]
theorem edist_mk (x y : X) (t s : T) :
    edist (mk x t) (mk y s) = edist x y + edist t s ^ (1 / 2 : ℝ) := by
  rw [WithLp.prod_edist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp [mk]

variable [PseudoEMetricSpace Y] {α C : ℝ≥0} {f : ParabolicSpace X T → Y}

/-- A parabolic Hölder estimate gives the same spatial Hölder bound at every time. -/
theorem holderWith_space (hf : HolderWith C α f) (t : T) :
    HolderWith C α (fun x ↦ f (mk x t)) := by
  intro x y
  simpa using hf (mk x t) (mk y t)

private theorem edist_rpow_half_div (t s : T) (α : ℝ≥0) :
    edist t s ^ ((α / 2 : ℝ≥0) : ℝ) = (edist t s ^ (1 / 2 : ℝ)) ^ (α : ℝ) := by
  rw [← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- A parabolic α-Hölder estimate gives a temporal α/2-Hölder bound at every point. -/
theorem holderWith_time (hf : HolderWith C α f) (x : X) :
    HolderWith C (α / 2) (fun t ↦ f (mk x t)) := by
  intro t s
  simpa only [edist_mk, edist_self, zero_add, ← edist_rpow_half_div] using
    hf (mk x t) (mk x s)

/-- Uniform spatial and temporal estimates give a parabolic estimate, with the sum of constants. -/
theorem holderWith_of_slices {A B : ℝ≥0}
    (hx : ∀ t, HolderWith A α (fun x ↦ f (mk x t)))
    (ht : ∀ x, HolderWith B (α / 2) (fun t ↦ f (mk x t))) :
    HolderWith (A + B) α f := by
  intro p q
  obtain ⟨x, t, rfl⟩ := exists_mk_eq p
  obtain ⟨y, s, rfl⟩ := exists_mk_eq q
  have hx' := hx t x y
  have ht' := ht y t s
  calc
    edist (f (mk x t)) (f (mk y s)) ≤
        edist (f (mk x t)) (f (mk y t)) + edist (f (mk y t)) (f (mk y s)) :=
      edist_triangle _ _ _
    _ ≤ A * edist x y ^ (α : ℝ) + B * (edist t s ^ (1 / 2 : ℝ)) ^ (α : ℝ) := by
      rw [← edist_rpow_half_div]
      exact add_le_add hx' ht'
    _ ≤ A * (edist x y + edist t s ^ (1 / 2 : ℝ)) ^ (α : ℝ) +
        B * (edist x y + edist t s ^ (1 / 2 : ℝ)) ^ (α : ℝ) := by
      gcongr <;> simp
    _ = (A + B : ℝ≥0) * edist (mk x t) (mk y s) ^ (α : ℝ) := by
      rw [edist_mk, ENNReal.coe_add, add_mul]

/-- Each spatial slice seminorm is bounded by the parabolic seminorm. -/
theorem eHolderNorm_space_le (f : ParabolicSpace X T → Y) (α : ℝ≥0) (t : T) :
    eHolderNorm α (fun x ↦ f (mk x t)) ≤ eHolderNorm α f := by
  exact eHolderNorm_le_of_holderWith fun _ hC ↦ holderWith_space hC t

/-- Each temporal α/2 slice seminorm is bounded by the parabolic α seminorm. -/
theorem eHolderNorm_time_le (f : ParabolicSpace X T → Y) (α : ℝ≥0) (x : X) :
    eHolderNorm (α / 2) (fun t ↦ f (mk x t)) ≤ eHolderNorm α f := by
  exact eHolderNorm_le_of_holderWith fun _ hC ↦ holderWith_time hC x

/-- The sum of the uniform slice seminorms is at most twice the parabolic seminorm.
Together with `eHolderNorm_le_iSup_add_iSup`, this gives equivalence of the two seminorms. -/
theorem iSup_add_iSup_le_two_mul_eHolderNorm (f : ParabolicSpace X T → Y) (α : ℝ≥0) :
    (⨆ t, eHolderNorm α (fun x ↦ f (mk x t))) +
      (⨆ x, eHolderNorm (α / 2) (fun t ↦ f (mk x t))) ≤ 2 * eHolderNorm α f := by
  rw [two_mul]
  exact add_le_add (iSup_le fun t ↦ eHolderNorm_space_le f α t)
    (iSup_le fun x ↦ eHolderNorm_time_le f α x)

/-- The parabolic seminorm is bounded by the sum of the uniform spatial and temporal seminorms.
The inequality is in extended nonnegative reals, so it also holds for infinite seminorms. -/
theorem eHolderNorm_le_iSup_add_iSup (f : ParabolicSpace X T → Y) (α : ℝ≥0) :
    eHolderNorm α f ≤ (⨆ t, eHolderNorm α (fun x ↦ f (mk x t))) +
      ⨆ x, eHolderNorm (α / 2) (fun t ↦ f (mk x t)) := by
  let A := ⨆ t, eHolderNorm α (fun x ↦ f (mk x t))
  let B := ⨆ x, eHolderNorm (α / 2) (fun t ↦ f (mk x t))
  by_cases hA : A = ∞
  · dsimp only [A] at hA
    simp [hA]
  by_cases hB : B = ∞
  · dsimp only [B] at hB
    simp [hB]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hAε : A < (A.toNNReal + ε / 2 : ℝ≥0) := by
    rw [← ENNReal.coe_toNNReal hA, ENNReal.coe_lt_coe]
    exact lt_add_of_pos_right _ (half_pos hε)
  have hBε : B < (B.toNNReal + ε / 2 : ℝ≥0) := by
    rw [← ENNReal.coe_toNNReal hB, ENNReal.coe_lt_coe]
    exact lt_add_of_pos_right _ (half_pos hε)
  have hx (t : T) : HolderWith (A.toNNReal + ε / 2) α (fun x ↦ f (mk x t)) :=
    holderWith_of_eHolderNorm_lt
      ((le_iSup (fun t ↦ eHolderNorm α (fun x ↦ f (mk x t))) t).trans_lt hAε)
  have ht (x : X) : HolderWith (B.toNNReal + ε / 2) (α / 2) (fun t ↦ f (mk x t)) :=
    holderWith_of_eHolderNorm_lt
      ((le_iSup (fun x ↦ eHolderNorm (α / 2) (fun t ↦ f (mk x t))) x).trans_lt hBε)
  convert (holderWith_of_slices hx ht).eHolderNorm_le using 1
  rw [add_add_add_comm, add_halves, ENNReal.coe_add, ENNReal.coe_add,
    ENNReal.coe_toNNReal hA, ENNReal.coe_toNNReal hB]

/-- Parabolic Hölder regularity is equivalent to finiteness of both uniform slice seminorms.
Pointwise finiteness of the slice seminorms alone would not suffice. -/
theorem memHolder_iff_slices (f : ParabolicSpace X T → Y) (α : ℝ≥0) :
    MemHolder α f ↔
      (⨆ t, eHolderNorm α (fun x ↦ f (mk x t))) < ∞ ∧
        (⨆ x, eHolderNorm (α / 2) (fun t ↦ f (mk x t))) < ∞ := by
  constructor
  · intro hf
    exact ⟨(iSup_le fun t ↦ eHolderNorm_space_le f α t).trans_lt hf.eHolderNorm_lt_top,
      (iSup_le fun x ↦ eHolderNorm_time_le f α x).trans_lt hf.eHolderNorm_lt_top⟩
  · rintro ⟨hx, ht⟩
    exact eHolderNorm_lt_top.mp <|
      (eHolderNorm_le_iSup_add_iSup f α).trans_lt (ENNReal.add_lt_top.mpr ⟨hx, ht⟩)

end PseudoEMetricSpace

end ParabolicSpace
end TauCeti
