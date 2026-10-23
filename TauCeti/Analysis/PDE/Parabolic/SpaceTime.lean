/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.Snowflaking
public import TauCeti.Topology.MetricSpace.Holder

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Parabolic space-time and parabolic Hölder seminorms

Parabolic Hölder spaces measure regularity with respect to the parabolic distance

`d_par((x, t), (y, s)) = dist x y + √|t - s|`,

under which one time derivative counts as two space derivatives. This file realizes space-time
with this distance as the `L¹` product of the spatial space with the square-root snowflake of the
time line (`Metric.Snowflaking ℝ (1 / 2)`), so that the parabolic Hölder seminorm of a function on
a set of space-time points is Mathlib's `eHolderNorm` for this metric. The coordinate
homeomorphism with `X × ℝ` transports functions to ordinary space-time, where they can be
differentiated.

On a slab `X × T` of space-time points with times in `T`, the parabolic `α`-Hölder seminorm is
equivalent to the sum of the spatial `α`-Hölder seminorm of the time slices and the temporal
`α / 2`-Hölder seminorm of the space slices:

`max ([v]_{x,α}, [v]_{t,α/2}) ≤ [v]_{α,par} ≤ [v]_{x,α} + [v]_{t,α/2}`.

The second inequality uses the intermediate point with the spatial coordinate of one point and the
time of the other, which lies in the slab. The general formula for a Hölder seminorm as a supremum
of difference quotients (`MemHolder.nnHolderNorm_eq_iSup_dist_div`) together with
`ParabolicSpaceTime.dist_eq` expresses `[v]_{α,par}` as the supremum of
`dist (v z) (v w) / d_par(z, w) ^ α` over distinct points.

## Main declarations

* `TauCeti.ParabolicSpaceTime X`: space-time over `X` with the parabolic distance.
* `TauCeti.ParabolicSpaceTime.dist_eq`: the parabolic distance formula.
* `TauCeti.ParabolicSpaceTime.homeomorphProd`: the coordinate homeomorphism with `X × ℝ`.
* `TauCeti.ParabolicSpaceTime.slab T`: the space-time points whose time lies in `T`.
* `TauCeti.ParabolicSpaceTime.eSpaceHolderNorm` and `TauCeti.ParabolicSpaceTime.eTimeHolderNorm`:
  the spatial and temporal Hölder seminorms of a function on a slab.
* `TauCeti.ParabolicSpaceTime.eHolderNorm_le_eSpaceHolderNorm_add_eTimeHolderNorm`,
  `TauCeti.ParabolicSpaceTime.eSpaceHolderNorm_le_eHolderNorm` and
  `TauCeti.ParabolicSpaceTime.eTimeHolderNorm_div_two_le_eHolderNorm`: the comparison of the
  parabolic seminorm with the separate seminorms.

## References

* G. M. Lieberman, *Second Order Parabolic Differential Equations*, Chapter IV.
-/

public section

noncomputable section

open Set Metric
open scoped NNReal ENNReal

namespace TauCeti

/-- **Parabolic space-time** over `X`: pairs of a point of `X` and a time, with the parabolic
distance `dist x y + √|t - s|` between `(x, t)` and `(y, s)`. It is the `L¹` product of `X` with
the square-root snowflake of `ℝ`. -/
abbrev ParabolicSpaceTime (X : Type*) : Type _ :=
  WithLp 1 (X × Snowflaking ℝ (1 / 2) one_half_pos one_half_lt_one.le)

namespace ParabolicSpaceTime

variable {X F : Type*}

/-- The space-time point with spatial coordinate `x` and time `t`. -/
def mk (x : X) (t : ℝ) : ParabolicSpaceTime X :=
  WithLp.toLp 1 (x, Snowflaking.toSnowflaking t)

/-- The spatial coordinate of a space-time point. -/
def space (z : ParabolicSpaceTime X) : X :=
  z.fst

/-- The time coordinate of a space-time point. -/
def time (z : ParabolicSpaceTime X) : ℝ :=
  Snowflaking.ofSnowflaking z.snd

@[simp]
theorem space_mk (x : X) (t : ℝ) : (mk x t).space = x :=
  (rfl)

@[simp]
theorem time_mk (x : X) (t : ℝ) : (mk x t).time = t :=
  (rfl)

@[simp]
theorem mk_space_time (z : ParabolicSpaceTime X) : mk z.space z.time = z :=
  (rfl)

@[ext]
theorem ext {z w : ParabolicSpaceTime X} (hs : z.space = w.space) (ht : z.time = w.time) :
    z = w := by
  rw [← mk_space_time z, ← mk_space_time w, hs, ht]

@[simp]
theorem edist_mk_mk [PseudoEMetricSpace X] (x y : X) (t s : ℝ) :
    edist (mk x t) (mk y s) = edist x y + edist t s ^ (1 / 2 : ℝ) := by
  rw [WithLp.prod_edist_eq_add (by simp)]
  simp [mk]

/-- **The parabolic distance**: `dist (x, t) (y, s) = dist x y + √|t - s|`. -/
@[simp]
theorem dist_mk_mk [PseudoMetricSpace X] (x y : X) (t s : ℝ) :
    dist (mk x t) (mk y s) = dist x y + √|t - s| := by
  rw [WithLp.prod_dist_eq_add (by simp), Real.sqrt_eq_rpow, ← Real.dist_eq]
  simp [mk]

/-- The parabolic extended distance: `edist (x, t) (y, s) = edist x y + edist t s ^ (1 / 2)`. -/
theorem edist_eq [PseudoEMetricSpace X] (z w : ParabolicSpaceTime X) :
    edist z w = edist z.space w.space + edist z.time w.time ^ (1 / 2 : ℝ) := by
  rw [← edist_mk_mk, mk_space_time, mk_space_time]

/-- **The parabolic distance** in coordinates: `dist z w = dist x y + √|t - s|` for
`z = (x, t)` and `w = (y, s)`. -/
theorem dist_eq [PseudoMetricSpace X] (z w : ParabolicSpaceTime X) :
    dist z w = dist z.space w.space + √|z.time - w.time| := by
  rw [← dist_mk_mk, mk_space_time, mk_space_time]

/-- The coordinate homeomorphism of parabolic space-time with `X × ℝ`. Derivatives of functions on
parabolic space-time are taken after transport along this map. -/
def homeomorphProd [TopologicalSpace X] : ParabolicSpaceTime X ≃ₜ X × ℝ :=
  (WithLp.homeomorphProd 1 X _).trans ((Homeomorph.refl X).prodCongr Snowflaking.homeomorph)

@[simp]
theorem homeomorphProd_apply [TopologicalSpace X] (z : ParabolicSpaceTime X) :
    homeomorphProd z = (z.space, z.time) :=
  (rfl)

@[simp]
theorem homeomorphProd_symm_apply [TopologicalSpace X] (p : X × ℝ) :
    homeomorphProd.symm p = mk p.1 p.2 :=
  (rfl)

/-- The slab `X × T` of space-time points whose time lies in `T`. For `T = Icc a b` this is the
closed slab `X × [a, b]`. -/
def slab (T : Set ℝ) : Set (ParabolicSpaceTime X) :=
  {z | z.time ∈ T}

@[simp]
theorem mem_slab {T : Set ℝ} {z : ParabolicSpaceTime X} : z ∈ slab T ↔ z.time ∈ T :=
  Iff.rfl

theorem mk_mem_slab {T : Set ℝ} {x : X} {t : ℝ} : mk x t ∈ slab T ↔ t ∈ T :=
  Iff.rfl

section Seminorms

variable {T : Set ℝ}

/-- The **spatial `α`-Hölder seminorm** of a function `v` on the slab `X × T`: the supremum over
times `t ∈ T` of the `α`-Hölder seminorm of the time slice `x ↦ v (x, t)`. -/
def eSpaceHolderNorm [PseudoEMetricSpace X] [PseudoEMetricSpace F] (α : ℝ≥0)
    (v : slab (X := X) T → F) : ℝ≥0∞ :=
  ⨆ t : T, eHolderNorm α fun x : X => v ⟨mk x t, mk_mem_slab.2 t.2⟩

/-- The **temporal `γ`-Hölder seminorm** `[v]_{t,γ}` of a function `v` on the slab `X × T`: the
supremum over points `x` of the `γ`-Hölder seminorm, for the ordinary distance on `T ⊆ ℝ`, of the
space slice `t ↦ v (x, t)`. -/
def eTimeHolderNorm [PseudoEMetricSpace F] (γ : ℝ≥0) (v : slab (X := X) T → F) : ℝ≥0∞ :=
  ⨆ x : X, eHolderNorm γ fun t : T => v ⟨mk x t, mk_mem_slab.2 t.2⟩

/-- The spatial seminorm is the least common bound for the Hölder seminorms of the time slices. -/
theorem eSpaceHolderNorm_le_iff [PseudoEMetricSpace X] [PseudoEMetricSpace F] {α : ℝ≥0}
    {v : slab (X := X) T → F} {C : ℝ≥0∞} :
    eSpaceHolderNorm α v ≤ C ↔
      ∀ t : T, eHolderNorm α (fun x : X => v ⟨mk x t, mk_mem_slab.2 t.2⟩) ≤ C :=
  iSup_le_iff

/-- The temporal seminorm is the least common bound for the Hölder seminorms of the space
slices. -/
theorem eTimeHolderNorm_le_iff [PseudoEMetricSpace F] {γ : ℝ≥0} {v : slab (X := X) T → F}
    {C : ℝ≥0∞} :
    eTimeHolderNorm γ v ≤ C ↔
      ∀ x : X, eHolderNorm γ (fun t : T => v ⟨mk x t, mk_mem_slab.2 t.2⟩) ≤ C :=
  iSup_le_iff

/-- The spatial seminorm bounds the spatial increments of `v` at a fixed time. -/
theorem edist_le_eSpaceHolderNorm_mul_rpow [MetricSpace X] [PseudoEMetricSpace F] (α : ℝ≥0)
    (v : slab (X := X) T → F) (t : T) (x y : X) :
    edist (v ⟨mk x t, mk_mem_slab.2 t.2⟩) (v ⟨mk y t, mk_mem_slab.2 t.2⟩) ≤
      eSpaceHolderNorm α v * edist x y ^ (α : ℝ) :=
  (edist_le_eHolderNorm_mul_rpow α (fun x : X => v ⟨mk x t, mk_mem_slab.2 t.2⟩) x y).trans
    (by gcongr; exact eSpaceHolderNorm_le_iff.1 le_rfl t)

/-- The temporal seminorm bounds the time increments of `v` at a fixed point. -/
theorem edist_le_eTimeHolderNorm_mul_rpow [PseudoEMetricSpace F] (γ : ℝ≥0)
    (v : slab (X := X) T → F) (x : X) (t s : T) :
    edist (v ⟨mk x t, mk_mem_slab.2 t.2⟩) (v ⟨mk x s, mk_mem_slab.2 s.2⟩) ≤
      eTimeHolderNorm γ v * edist t s ^ (γ : ℝ) :=
  (edist_le_eHolderNorm_mul_rpow γ (fun t : T => v ⟨mk x t, mk_mem_slab.2 t.2⟩) t s).trans
    (by gcongr; exact eTimeHolderNorm_le_iff.1 le_rfl x)

/-- The spatial seminorm is at most the parabolic seminorm: at a fixed time, the parabolic
distance is the spatial distance. -/
theorem eSpaceHolderNorm_le_eHolderNorm [PseudoEMetricSpace X] [PseudoEMetricSpace F] (α : ℝ≥0)
    (v : slab (X := X) T → F) : eSpaceHolderNorm α v ≤ eHolderNorm α v := by
  refine eSpaceHolderNorm_le_iff.2 fun t => ?_
  have hg : HolderWith 1 1 fun x : X => (⟨mk x t, mk_mem_slab.2 t.2⟩ : slab (X := X) T) :=
    fun x y => by simp [Subtype.edist_eq]
  simpa only [mul_one, Function.comp_def, ENNReal.coe_one, ENNReal.one_rpow] using
    hg.eHolderNorm_comp_le one_ne_zero α v

/-- The temporal `α / 2`-Hölder seminorm is at most the parabolic `α`-Hölder seminorm: at a fixed
point, the parabolic distance is the square root of the time distance. -/
theorem eTimeHolderNorm_div_two_le_eHolderNorm [PseudoEMetricSpace X] [PseudoEMetricSpace F]
    (α : ℝ≥0) (v : slab (X := X) T → F) : eTimeHolderNorm (α / 2) v ≤ eHolderNorm α v := by
  refine eTimeHolderNorm_le_iff.2 fun x => ?_
  have hg : HolderWith 1 (1 / 2) fun t : T => (⟨mk x t, mk_mem_slab.2 t.2⟩ : slab (X := X) T) :=
    fun t s => by simp [Subtype.edist_eq]
  simpa only [mul_one_div, mul_one, Function.comp_def, ENNReal.coe_one, ENNReal.one_rpow] using
    hg.eHolderNorm_comp_le one_ne_zero α v

/-- **The parabolic Hölder seminorm is controlled by the separate seminorms.** On a slab, the
parabolic `α`-Hölder seminorm is at most the sum of the spatial `α`-Hölder seminorm and the
temporal `α / 2`-Hölder seminorm. -/
theorem eHolderNorm_le_eSpaceHolderNorm_add_eTimeHolderNorm [MetricSpace X]
    [PseudoEMetricSpace F] (α : ℝ≥0) (v : slab (X := X) T → F) :
    eHolderNorm α v ≤ eSpaceHolderNorm α v + eTimeHolderNorm (α / 2) v := by
  rw [eHolderNorm_eq_iSup_edist_div]
  refine iSup₂_le fun z w => iSup_le fun _ => ENNReal.div_le_of_le_mul ?_
  obtain ⟨z, hz⟩ := z
  obtain ⟨w, hw⟩ := w
  -- Pass through the point with the spatial coordinate of `w` and the time of `z`.
  set t : T := ⟨z.time, hz⟩
  set s : T := ⟨w.time, hw⟩
  have hdx : edist z.space w.space ≤ edist z w := by
    rw [edist_eq]
    exact le_self_add
  have hdt : edist (t : ℝ) s ^ ((α / 2 : ℝ≥0) : ℝ) ≤ edist z w ^ (α : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_two, div_eq_mul_one_div, mul_comm, ENNReal.rpow_mul,
      edist_eq]
    gcongr
    exact le_add_self
  calc edist (v ⟨z, hz⟩) (v ⟨w, hw⟩)
      = edist (v ⟨mk z.space t, mk_mem_slab.2 t.2⟩) (v ⟨mk w.space s, mk_mem_slab.2 s.2⟩) := by
        simp only [t, s, mk_space_time]
    _ ≤ edist (v ⟨mk z.space t, mk_mem_slab.2 t.2⟩) (v ⟨mk w.space t, mk_mem_slab.2 t.2⟩) +
          edist (v ⟨mk w.space t, mk_mem_slab.2 t.2⟩)
            (v ⟨mk w.space s, mk_mem_slab.2 s.2⟩) :=
        edist_triangle _ _ _
    _ ≤ eSpaceHolderNorm α v * edist z.space w.space ^ (α : ℝ) +
          eTimeHolderNorm (α / 2) v * edist t s ^ ((α / 2 : ℝ≥0) : ℝ) :=
        add_le_add (edist_le_eSpaceHolderNorm_mul_rpow α v t _ _)
          (edist_le_eTimeHolderNorm_mul_rpow (α / 2) v _ t s)
    _ ≤ eSpaceHolderNorm α v * edist z w ^ (α : ℝ) +
          eTimeHolderNorm (α / 2) v * edist z w ^ (α : ℝ) := by
        rw [Subtype.edist_eq]
        gcongr
    _ = (eSpaceHolderNorm α v + eTimeHolderNorm (α / 2) v) * edist z w ^ (α : ℝ) :=
        (add_mul _ _ _).symm

/-- A function on a slab is parabolically `α`-Hölder if and only if its time slices are uniformly
`α`-Hölder in space and its space slices are uniformly `α / 2`-Hölder in time. -/
theorem memHolder_iff_eSpaceHolderNorm_lt_top_and_eTimeHolderNorm_lt_top [MetricSpace X]
    [PseudoEMetricSpace F] {α : ℝ≥0} {v : slab (X := X) T → F} :
    MemHolder α v ↔ eSpaceHolderNorm α v < ∞ ∧ eTimeHolderNorm (α / 2) v < ∞ := by
  rw [← eHolderNorm_lt_top]
  refine ⟨fun h => ⟨(eSpaceHolderNorm_le_eHolderNorm α v).trans_lt h,
    (eTimeHolderNorm_div_two_le_eHolderNorm α v).trans_lt h⟩, fun h => ?_⟩
  exact (eHolderNorm_le_eSpaceHolderNorm_add_eTimeHolderNorm α v).trans_lt
    (ENNReal.add_lt_top.2 h)

end Seminorms

end ParabolicSpaceTime

end TauCeti
