/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform modulus of continuity on subsets of pseudometric spaces

For a map `f : X → Y` between pseudometric spaces, a subset `S : Set X`, and a mesh `h : ℝ`,
this file defines `TauCeti.modulusOfContinuityOn f S h` as the supremum of `dist (f x) (f y)` over
all pairs `x, y ∈ S` with `dist x y ≤ h`, taking the value `0` when no such pair exists.

## Main definitions and results

* `TauCeti.modulusOfContinuityOn`: the uniform modulus of continuity of `f` on `S` at mesh `h`.
* `TauCeti.modulusOfContinuityOn_le`, `TauCeti.dist_le_modulusOfContinuityOn`,
  `TauCeti.modulusOfContinuityOn_le_iff`: upper and lower bounds for increments at mesh `h`.
* `TauCeti.modulusOfContinuityOn_mono`, `TauCeti.monotone_modulusOfContinuityOn`,
  `TauCeti.modulusOfContinuityOn_mono_set`: monotonicity in the mesh and in the domain subset when
  the increment set is bounded above.
* `UniformContinuousOn.tendsto_modulusOfContinuityOn_nhdsGT_zero`,
  `ContinuousOn.tendsto_modulusOfContinuityOn_nhdsGT_zero`,
  `ContinuousOn.bddAbove_modulusOfContinuityOn_set`,
  `TauCeti.uniformContinuousOn_iff_tendsto_modulusOfContinuityOn`: vanishing of the modulus as
  `h → 0⁺` for uniformly continuous maps, boundedness of increment sets on compact domains, and
  characterization when small-mesh increment sets are bounded above.
* `Isometry.modulusOfContinuityOn_comp`, `TauCeti.modulusOfContinuityOn_neg`,
  `TauCeti.modulusOfContinuityOn_smul`, `TauCeti.modulusOfContinuityOn_add_le`,
  `LipschitzOnWith.modulusOfContinuityOn_le`, `LipschitzOnWith.bddAbove_modulusOfContinuityOn_set`,
  `HolderOnWith.modulusOfContinuityOn_le`, `HolderOnWith.bddAbove_modulusOfContinuityOn_set`:
  invariance, scaling, subadditivity, and Lipschitz/Hölder bounds.
* `TauCeti.modulusOfContinuityOn_Iic_nnreal_mul`: rescaling `[0, 1]` to `[0, T]` on `ℝ≥0`.
* `ContinuousOn.modulusOfContinuityOn_Iic_one_le_of_dyadic`: deterministic binary-expansion
  chaining bound for `modulusOfContinuityOn f (Set.Iic 1) h` from dyadic grid increments.

## Implementation notes

Because `Real.sSup` maps unbounded-above sets to `0`, lower-bound and monotonicity statements that
read individual increments back out of `modulusOfContinuityOn f S h` assume `BddAbove` of the
increment set `{a | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)}`, supplied for bounded
images by `TauCeti.bddAbove_modulusOfContinuityOn_set`, for continuous maps on compact sets by
`ContinuousOn.bddAbove_modulusOfContinuityOn_set`, and for Lipschitz or Hölder maps by
`LipschitzOnWith.bddAbove_modulusOfContinuityOn_set` and
`HolderOnWith.bddAbove_modulusOfContinuityOn_set`. Upper bounds
(`TauCeti.modulusOfContinuityOn_le`), nonnegativity, and scalar rescaling
(`TauCeti.modulusOfContinuityOn_smul`) hold unconditionally.
-/

public section

noncomputable section

open Filter Set
open scoped NNReal Topology Pointwise

namespace TauCeti

section PseudoMetricSpace

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- The uniform modulus of continuity of `f : X → Y` on `S : Set X` at mesh `h : ℝ`:
`sup {dist (f x) (f y) | x ∈ S, y ∈ S, dist x y ≤ h}`, equal to `0` when no such pair exists. -/
def modulusOfContinuityOn (f : X → Y) (S : Set X) (h : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)}

/-- Unfolding lemma for `modulusOfContinuityOn`. -/
theorem modulusOfContinuityOn_def (f : X → Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn f S h =
      sSup {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)} := (rfl)

/-- The uniform modulus of continuity is always nonnegative. -/
theorem modulusOfContinuityOn_nonneg (f : X → Y) (S : Set X) (h : ℝ) :
    0 ≤ modulusOfContinuityOn f S h := by
  rw [modulusOfContinuityOn]
  exact Real.sSup_nonneg fun a ⟨x, _, y, _, _, ha⟩ ↦ ha ▸ dist_nonneg

/-- Unconditional upper bound: if `0 ≤ M` bounds `dist (f x) (f y)` for every pair in `S` at
distance at most `h`, then `modulusOfContinuityOn f S h ≤ M`. -/
theorem modulusOfContinuityOn_le {f : X → Y} {S : Set X} {h M : ℝ} (hM : 0 ≤ M)
    (hle : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ h → dist (f x) (f y) ≤ M) :
    modulusOfContinuityOn f S h ≤ M := by
  rw [modulusOfContinuityOn]
  exact Real.sSup_le (fun a ⟨x, hx, y, hy, hxy, ha⟩ ↦ ha ▸ hle x hx y hy hxy) hM

/-- On the empty set, the modulus of continuity vanishes. -/
@[simp]
theorem modulusOfContinuityOn_empty (f : X → Y) (h : ℝ) :
    modulusOfContinuityOn f ∅ h = 0 :=
  le_antisymm (modulusOfContinuityOn_le le_rfl fun _ hx ↦ hx.elim)
    (modulusOfContinuityOn_nonneg f ∅ h)

/-- At negative mesh, no pair satisfies `dist x y ≤ h`, so the modulus vanishes. -/
theorem modulusOfContinuityOn_of_neg (f : X → Y) (S : Set X) {h : ℝ} (hh : h < 0) :
    modulusOfContinuityOn f S h = 0 :=
  le_antisymm
    (modulusOfContinuityOn_le le_rfl fun x _ y _ hxy ↦
      absurd (dist_nonneg (x := x) (y := y)) (not_le.2 (hxy.trans_lt hh)))
    (modulusOfContinuityOn_nonneg f S h)

/-- On a subsingleton domain, every pair of points in `S` coincides, so the modulus vanishes. -/
theorem modulusOfContinuityOn_subsingleton (f : X → Y) {S : Set X} (hS : S.Subsingleton) (h : ℝ) :
    modulusOfContinuityOn f S h = 0 :=
  le_antisymm
    (modulusOfContinuityOn_le le_rfl fun x hx y hy _ ↦ by rw [hS hx hy, dist_self])
    (modulusOfContinuityOn_nonneg f S h)

/-- A constant map has identically zero modulus of continuity. -/
@[simp]
theorem modulusOfContinuityOn_const (c : Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn (fun _ : X ↦ c) S h = 0 :=
  le_antisymm (modulusOfContinuityOn_le le_rfl fun _ _ _ _ _ ↦ by simp)
    (modulusOfContinuityOn_nonneg _ S h)

/-- When `f '' S` is metrically bounded, the set of increments defining `modulusOfContinuityOn`
is bounded above. -/
theorem bddAbove_modulusOfContinuityOn_set {f : X → Y} {S : Set X}
    (hf : Bornology.IsBounded (f '' S)) (h : ℝ) :
    BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)} := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hf
  refine ⟨D, ?_⟩
  rintro a ⟨x, hx, y, hy, -, rfl⟩
  exact hD (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- Each increment of `f` on `S` at distance at most `h` is bounded by
`modulusOfContinuityOn f S h` whenever the mesh-`h` increment set is bounded above. -/
theorem dist_le_modulusOfContinuityOn {f : X → Y} {S : Set X} {x y : X} {h : ℝ}
    (hbdd : BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)})
    (hx : x ∈ S) (hy : y ∈ S) (hxy : dist x y ≤ h) :
    dist (f x) (f y) ≤ modulusOfContinuityOn f S h :=
  le_csSup hbdd ⟨x, hx, y, hy, hxy, rfl⟩

/-- Characterization of upper bounds on `modulusOfContinuityOn f S h` when `S` is nonempty,
`0 ≤ h`, and the mesh-`h` increment set is bounded above. -/
theorem modulusOfContinuityOn_le_iff {f : X → Y} {S : Set X} (hS : S.Nonempty) {h M : ℝ}
    (hh : 0 ≤ h)
    (hbdd : BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)}) :
    modulusOfContinuityOn f S h ≤ M ↔ ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ h → dist (f x) (f y) ≤ M := by
  refine ⟨fun hle x hx y hy hxy ↦ (dist_le_modulusOfContinuityOn hbdd hx hy hxy).trans hle,
    fun hle ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := hS
  have hM : 0 ≤ M := by
    simpa only [dist_self] using hle x₀ hx₀ x₀ hx₀ (by simpa only [dist_self] using hh)
  exact modulusOfContinuityOn_le hM hle

private lemma modulusOfContinuityOn_le_of_subset {f : X → Y} {S₁ S₂ : Set X} {h₁ h₂ : ℝ}
    (hsub : {a : ℝ | ∃ x ∈ S₁, ∃ y ∈ S₁, dist x y ≤ h₁ ∧ a = dist (f x) (f y)} ⊆
      {a : ℝ | ∃ x ∈ S₂, ∃ y ∈ S₂, dist x y ≤ h₂ ∧ a = dist (f x) (f y)})
    (hbdd : BddAbove {a : ℝ | ∃ x ∈ S₂, ∃ y ∈ S₂, dist x y ≤ h₂ ∧ a = dist (f x) (f y)}) :
    modulusOfContinuityOn f S₁ h₁ ≤ modulusOfContinuityOn f S₂ h₂ := by
  let A₁ := {a : ℝ | ∃ x ∈ S₁, ∃ y ∈ S₁, dist x y ≤ h₁ ∧ a = dist (f x) (f y)}
  rcases A₁.eq_empty_or_nonempty with hempty | hne
  · simpa [modulusOfContinuityOn, A₁, hempty] using modulusOfContinuityOn_nonneg f S₂ h₂
  · exact csSup_le_csSup hbdd hne hsub

/-- Pairwise monotonicity of `modulusOfContinuityOn f S` in the mesh when the larger mesh's
increment set is bounded above. -/
theorem modulusOfContinuityOn_mono {f : X → Y} {S : Set X} {h₁ h₂ : ℝ} (hh : h₁ ≤ h₂)
    (hbdd : BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h₂ ∧ a = dist (f x) (f y)}) :
    modulusOfContinuityOn f S h₁ ≤ modulusOfContinuityOn f S h₂ :=
  modulusOfContinuityOn_le_of_subset
    (fun _ ⟨x, hx, y, hy, hxy, ha⟩ ↦ ⟨x, hx, y, hy, hxy.trans hh, ha⟩) hbdd

/-- Monotonicity of `modulusOfContinuityOn f S` in the mesh when the increment set is bounded above
at every mesh. -/
theorem monotone_modulusOfContinuityOn {f : X → Y} {S : Set X}
    (hbdd : ∀ h, BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)}) :
    Monotone (modulusOfContinuityOn f S) :=
  fun _ h₂ hh ↦ modulusOfContinuityOn_mono hh (hbdd h₂)

/-- Monotonicity of `modulusOfContinuityOn` in the domain set when the larger domain's increment
set at mesh `h` is bounded above. -/
theorem modulusOfContinuityOn_mono_set {f : X → Y} {S₁ S₂ : Set X} (hS : S₁ ⊆ S₂) {h : ℝ}
    (hbdd : BddAbove {a : ℝ | ∃ x ∈ S₂, ∃ y ∈ S₂, dist x y ≤ h ∧ a = dist (f x) (f y)}) :
    modulusOfContinuityOn f S₁ h ≤ modulusOfContinuityOn f S₂ h :=
  modulusOfContinuityOn_le_of_subset
    (fun _ ⟨x, hx, y, hy, hxy, ha⟩ ↦ ⟨x, hS hx, y, hS hy, hxy, ha⟩) hbdd

end PseudoMetricSpace

section MetricSpace

variable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]

/-- In a metric space, distance at most `0` forces equality of points, so the modulus at mesh `0`
vanishes. -/
@[simp]
theorem modulusOfContinuityOn_zero (f : X → Y) (S : Set X) :
    modulusOfContinuityOn f S 0 = 0 :=
  le_antisymm
    (modulusOfContinuityOn_le le_rfl fun _ _ _ _ hxy ↦ by rw [dist_le_zero.1 hxy, dist_self])
    (modulusOfContinuityOn_nonneg f S 0)

end MetricSpace

end TauCeti

/-- For a map that is uniformly continuous on `S`, the uniform modulus of continuity tends to `0`
as `h → 0⁺`, without any boundedness assumption on `S` or `f '' S`. -/
theorem UniformContinuousOn.tendsto_modulusOfContinuityOn_nhdsGT_zero
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {S : Set X}
    (hf : UniformContinuousOn f S) :
    Tendsto (TauCeti.modulusOfContinuityOn f S) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff_le.1 hf (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (TauCeti.modulusOfContinuityOn_nonneg f S h)]
  refine (TauCeti.modulusOfContinuityOn_le (half_pos hε).le fun x hx y hy hxy ↦ ?_).trans_lt
    (half_lt_self hε)
  exact hdist x hx y hy (hxy.trans hh.2.le)

/-- Continuous maps on compact sets have uniform modulus of continuity tending to `0` as
`h → 0⁺`. -/
theorem ContinuousOn.tendsto_modulusOfContinuityOn_nhdsGT_zero
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : Set X} (hf : ContinuousOn f K) (hK : IsCompact K) :
    Tendsto (TauCeti.modulusOfContinuityOn f K) (𝓝[>] 0) (𝓝 0) :=
  (hK.uniformContinuousOn_of_continuous hf).tendsto_modulusOfContinuityOn_nhdsGT_zero

/-- For a continuous map on a compact set `K`, the increment set defining
`modulusOfContinuityOn f K h` is bounded above at every mesh `h`. -/
theorem ContinuousOn.bddAbove_modulusOfContinuityOn_set
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : Set X} (hf : ContinuousOn f K) (hK : IsCompact K) (h : ℝ) :
    BddAbove {a : ℝ | ∃ x ∈ K, ∃ y ∈ K, dist x y ≤ h ∧ a = dist (f x) (f y)} :=
  TauCeti.bddAbove_modulusOfContinuityOn_set (hK.image_of_continuousOn hf).isBounded h

/-- Post-composing with an isometry preserves the uniform modulus of continuity. -/
theorem Isometry.modulusOfContinuityOn_comp {X Y Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {g : Y → Z} (hg : Isometry g)
    (f : X → Y) (S : Set X) (h : ℝ) :
    TauCeti.modulusOfContinuityOn (g ∘ f) S h = TauCeti.modulusOfContinuityOn f S h := by
  simp [TauCeti.modulusOfContinuityOn, hg.dist_eq]

/-- A `K`-Lipschitz map on `S` has modulus of continuity at most `K * h` for `h ≥ 0`. -/
theorem LipschitzOnWith.modulusOfContinuityOn_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {K : ℝ≥0} {f : X → Y} {S : Set X} (hf : LipschitzOnWith K f S)
    {h : ℝ} (hh : 0 ≤ h) :
    TauCeti.modulusOfContinuityOn f S h ≤ (K : ℝ) * h :=
  TauCeti.modulusOfContinuityOn_le (mul_nonneg K.coe_nonneg hh) fun x hx y hy hxy ↦
    (hf.dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_left hxy K.coe_nonneg)

/-- A `(C, r)`-Hölder map on `S` has modulus of continuity at most `C * h ^ (r : ℝ)` for `h ≥ 0`. -/
theorem HolderOnWith.modulusOfContinuityOn_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {S : Set X} (hf : HolderOnWith C r f S)
    {h : ℝ} (hh : 0 ≤ h) :
    TauCeti.modulusOfContinuityOn f S h ≤ (C : ℝ) * h ^ (r : ℝ) :=
  TauCeti.modulusOfContinuityOn_le (by positivity) fun _ hx _ hy hxy ↦
    (hf.dist_le hx hy).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hxy r.coe_nonneg) C.coe_nonneg)

/-- For a `(C, r)`-Hölder map on `S`, the increment set defining `modulusOfContinuityOn f S h` is
bounded above at every mesh `h` (even when `f '' S` is unbounded). -/
theorem HolderOnWith.bddAbove_modulusOfContinuityOn_set {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {S : Set X} (hf : HolderOnWith C r f S)
    (h : ℝ) :
    BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)} :=
  ⟨(C : ℝ) * (max h 0) ^ (r : ℝ), by
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    exact (hf.dist_le hx hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (hxy.trans (le_max_left h 0)) r.coe_nonneg) C.coe_nonneg)⟩

/-- For a `K`-Lipschitz map on `S`, the increment set defining `modulusOfContinuityOn f S h` is
bounded above at every mesh `h` (even when `f '' S` is unbounded). -/
theorem LipschitzOnWith.bddAbove_modulusOfContinuityOn_set {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {K : ℝ≥0} {f : X → Y} {S : Set X} (hf : LipschitzOnWith K f S)
    (h : ℝ) :
    BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)} :=
  hf.holderOnWith.bddAbove_modulusOfContinuityOn_set h

namespace TauCeti

section ContinuityAndNormed

variable {X Y : Type*} [PseudoMetricSpace X]

/-- When small-mesh increment sets are bounded above, uniform continuity on `S` is equivalent to
vanishing of `modulusOfContinuityOn f S` along `𝓝[>] 0`. -/
theorem uniformContinuousOn_iff_tendsto_modulusOfContinuityOn [PseudoMetricSpace Y]
    {f : X → Y} {S : Set X}
    (hbdd : ∀ᶠ h in 𝓝[>] 0,
      BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)}) :
    UniformContinuousOn f S ↔ Tendsto (modulusOfContinuityOn f S) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨UniformContinuousOn.tendsto_modulusOfContinuityOn_nhdsGT_zero, fun hlim ↦ ?_⟩
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ, ⟨hδ_pos, hδ_bdd⟩, hδ_lt⟩ :=
    ((eventually_mem_nhdsWithin.and hbdd).and ((tendsto_order.1 hlim).2 ε hε)).exists
  exact ⟨δ, hδ_pos, fun x hx y hy hxy ↦
    (dist_le_modulusOfContinuityOn hδ_bdd hx hy hxy.le).trans_lt hδ_lt⟩

/-- Negating a map into a seminormed group preserves its uniform modulus of continuity. -/
@[simp]
theorem modulusOfContinuityOn_neg [SeminormedAddCommGroup Y] (f : X → Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn (-f) S h = modulusOfContinuityOn f S h :=
  isometry_neg.modulusOfContinuityOn_comp f S h

/-- Pointwise negation preserves the uniform modulus of continuity. -/
@[simp]
theorem modulusOfContinuityOn_fun_neg [SeminormedAddCommGroup Y] (f : X → Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn (fun x ↦ -f x) S h = modulusOfContinuityOn f S h :=
  modulusOfContinuityOn_neg f S h

/-- Scalar multiplication scales the uniform modulus of continuity by `‖c‖`, unconditionally. -/
@[simp]
theorem modulusOfContinuityOn_smul {𝕜 : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup Y]
    [Module 𝕜 Y] [NormSMulClass 𝕜 Y] (c : 𝕜) (f : X → Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn (c • f) S h = ‖c‖ * modulusOfContinuityOn f S h := by
  have hset : {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (c • f x) (c • f y)} =
      ‖c‖ • {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)} := by
    ext a
    simp only [mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul, dist_smul₀]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact ⟨dist (f x) (f y), ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, hxy, rfl⟩
  rw [modulusOfContinuityOn, modulusOfContinuityOn, Pi.smul_def, hset,
    Real.sSup_smul_of_nonneg (norm_nonneg c), smul_eq_mul]

/-- Pointwise scalar multiplication scales the uniform modulus of continuity by `‖c‖`. -/
@[simp]
theorem modulusOfContinuityOn_fun_smul {𝕜 : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup Y]
    [Module 𝕜 Y] [NormSMulClass 𝕜 Y] (c : 𝕜) (f : X → Y) (S : Set X) (h : ℝ) :
    modulusOfContinuityOn (fun x ↦ c • f x) S h = ‖c‖ * modulusOfContinuityOn f S h :=
  modulusOfContinuityOn_smul c f S h

/-- Subadditivity of the uniform modulus of continuity for maps into a seminormed group whose
mesh-`h` increment sets are bounded above. -/
theorem modulusOfContinuityOn_add_le [SeminormedAddCommGroup Y] {f g : X → Y} {S : Set X}
    {h : ℝ}
    (hf : BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (f x) (f y)})
    (hg : BddAbove {a : ℝ | ∃ x ∈ S, ∃ y ∈ S, dist x y ≤ h ∧ a = dist (g x) (g y)}) :
    modulusOfContinuityOn (f + g) S h ≤
      modulusOfContinuityOn f S h + modulusOfContinuityOn g S h := by
  refine modulusOfContinuityOn_le
    (add_nonneg (modulusOfContinuityOn_nonneg f S h) (modulusOfContinuityOn_nonneg g S h))
    fun x hx y hy hxy ↦ ?_
  calc dist (f x + g x) (f y + g y)
      ≤ dist (f x) (f y) + dist (g x) (g y) := dist_add_add_le _ _ _ _
    _ ≤ modulusOfContinuityOn f S h + modulusOfContinuityOn g S h :=
        add_le_add (dist_le_modulusOfContinuityOn hf hx hy hxy)
          (dist_le_modulusOfContinuityOn hg hx hy hxy)

end ContinuityAndNormed

section NNRealInterval

variable {Y : Type*} [PseudoMetricSpace Y]

/-- At horizon `T = 0`, the interval `Set.Iic (0 : ℝ≥0)` is `{0}`, so the modulus vanishes. -/
@[simp]
theorem modulusOfContinuityOn_Iic_zero (f : ℝ≥0 → Y) (h : ℝ) :
    modulusOfContinuityOn f (Iic (0 : ℝ≥0)) h = 0 :=
  modulusOfContinuityOn_subsingleton f
    (fun _ hx _ hy ↦ (nonpos_iff_eq_zero.1 hx).trans (nonpos_iff_eq_zero.1 hy).symm) h

/-- Explicit real-increment form of `modulusOfContinuityOn` on `Set.Iic T` for real-valued paths. -/
theorem modulusOfContinuityOn_Iic_real_eq (g : ℝ≥0 → ℝ) (T : ℝ≥0) (h : ℝ) :
    modulusOfContinuityOn g (Iic T) h =
      sSup {a : ℝ | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ dist s t ≤ h ∧ a = |g t - g s|} := by
  rw [modulusOfContinuityOn]
  congr 1
  ext a
  simp only [mem_Iic, mem_ofPred_eq, Real.dist_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, t, ht, hst, rfl⟩
    exact ⟨t, s, ht, hs, dist_comm s t ▸ hst, rfl⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨t, ht, s, hs, dist_comm s t ▸ hst, rfl⟩

/-- Linearly rescaling `[0, 1]` by `T > 0` identifies the modulus at mesh `h` with the modulus
on `[0, T]` at mesh `T * h`. -/
theorem modulusOfContinuityOn_Iic_nnreal_mul (f : ℝ≥0 → Y) {T : ℝ≥0} (hT : 0 < T) (h : ℝ) :
    modulusOfContinuityOn (fun u : ℝ≥0 ↦ f (T * u)) (Iic 1) h =
      modulusOfContinuityOn f (Iic T) ((T : ℝ) * h) := by
  have hT_pos : (0 : ℝ) < T := hT
  have hT_ne : T ≠ 0 := hT.ne'
  rw [modulusOfContinuityOn, modulusOfContinuityOn]
  congr 1
  ext a
  simp only [mem_Iic, mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu, v, hv, huv, rfl⟩
    refine ⟨T * u, mul_le_of_le_one_right' hu, T * v, mul_le_of_le_one_right' hv, ?_, rfl⟩
    have hd : dist (T * u) (T * v) = (T : ℝ) * dist u v := by
      simp only [NNReal.dist_eq, NNReal.coe_mul, ← mul_sub, abs_mul, abs_of_pos hT_pos]
    rw [hd]
    exact mul_le_mul_of_nonneg_left huv hT_pos.le
  · rintro ⟨s, hs, t, ht, hst, rfl⟩
    refine ⟨s / T, div_le_one_of_le₀ hs zero_le, t / T, div_le_one_of_le₀ ht zero_le, ?_, ?_⟩
    · have hd : dist (s / T) (t / T) = dist s t / (T : ℝ) := by
        simp only [NNReal.dist_eq, NNReal.coe_div, ← sub_div, abs_div, abs_of_pos hT_pos]
      rw [hd, div_le_iff₀ hT_pos, mul_comm]
      exact hst
    · simp [mul_div_cancel₀ _ hT_ne]

/-- Dyadic floor approximation of `x ∈ [0, 1]` at level `r`: `⌊x * 2 ^ r⌋₊ / 2 ^ r`. -/
private def dyadicApprox (r : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  (⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ : ℝ≥0) / 2 ^ r

private lemma dyadicApprox_def (r : ℕ) (x : ℝ≥0) :
    dyadicApprox r x = (⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ : ℝ≥0) / 2 ^ r := rfl

private lemma coe_dyadicApprox (r : ℕ) (x : ℝ≥0) :
    (dyadicApprox r x : ℝ) = (⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ : ℝ) / (2 : ℝ) ^ r := by
  simp [dyadicApprox]

private lemma dyadicApprox_le_and_lt {x : ℝ≥0} (r : ℕ) :
    dyadicApprox r x ≤ x ∧ (x : ℝ) < (dyadicApprox r x : ℝ) + 1 / (2 : ℝ) ^ r := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hle : (⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ : ℝ) ≤ (x : ℝ) * (2 : ℝ) ^ r :=
    Nat.floor_le (by positivity)
  have hlt : (x : ℝ) * (2 : ℝ) ^ r < (⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_le_coe, coe_dyadicApprox, div_le_iff₀ h2]
    exact hle
  · rw [coe_dyadicApprox, ← add_div, lt_div_iff₀ h2]
    exact hlt

private lemma tendsto_dyadicApprox (x : ℝ≥0) :
    Tendsto (fun r : ℕ ↦ dyadicApprox r x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun r hr ↦ ?_⟩
  obtain ⟨hle, hlt⟩ := dyadicApprox_le_and_lt (x := x) r
  rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hle)), neg_sub]
  have h1 : (x : ℝ) - dyadicApprox r x < (1 / 2 : ℝ) ^ r := by
    simpa [one_div_pow] using sub_lt_iff_lt_add'.2 hlt
  exact h1.trans_le ((pow_le_pow_of_le_one (by positivity) (by norm_num) hr).trans hN.le)

private lemma dist_dyadicApprox_succ_le {f : ℝ≥0 → Y} {x : ℝ≥0} (hx : x ≤ 1) (r : ℕ) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hstep : ∀ i < 2 ^ (r + 1),
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ (r + 1))) (f ((i : ℝ≥0) / 2 ^ (r + 1))) ≤ B) :
    dist (f (dyadicApprox r x)) (f (dyadicApprox (r + 1) x)) ≤ B := by
  set k := ⌊(x : ℝ) * (2 : ℝ) ^ r⌋₊ with hk_def
  set m := ⌊(x : ℝ) * (2 : ℝ) ^ (r + 1)⌋₊ with hm_def
  have hm_le_pow : m ≤ 2 ^ (r + 1) := by
    refine Nat.floor_le_of_le ?_
    calc (x : ℝ) * (2 : ℝ) ^ (r + 1) ≤ 1 * (2 : ℝ) ^ (r + 1) := by
          gcongr; exact_mod_cast hx
      _ = ((2 ^ (r + 1) : ℕ) : ℝ) := by push_cast; ring
  have h2k_le : 2 * k ≤ m := by
    refine Nat.le_floor ?_
    calc ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      _ ≤ 2 * ((x : ℝ) * (2 : ℝ) ^ r) := by gcongr; exact Nat.floor_le (by positivity)
      _ = (x : ℝ) * (2 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
  have hm_lt : m < 2 * k + 2 := by
    rw [← @Nat.cast_lt ℝ]
    calc (m : ℝ) ≤ (x : ℝ) * (2 : ℝ) ^ (r + 1) := Nat.floor_le (by positivity)
      _ = 2 * ((x : ℝ) * (2 : ℝ) ^ r) := by rw [pow_succ]; ring
      _ < 2 * ((k : ℝ) + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = ((2 * k + 2 : ℕ) : ℝ) := by push_cast; ring
  have h2k_eq : dyadicApprox r x = ((2 * k : ℕ) : ℝ≥0) / 2 ^ (r + 1) := by
    apply NNReal.coe_injective
    rw [coe_dyadicApprox, ← hk_def]
    push_cast [pow_succ]
    field_simp
  rcases eq_or_lt_of_le h2k_le with h_eq | h_lt
  · have hsame : dyadicApprox (r + 1) x = dyadicApprox r x := by
      rw [h2k_eq, dyadicApprox_def, ← hm_def, ← h_eq]
    rw [hsame, dist_self]
    exact hB0
  · have hm_eq : m = 2 * k + 1 := by omega
    have hi_lt : 2 * k < 2 ^ (r + 1) := by omega
    have hm_approx : dyadicApprox (r + 1) x = ((2 * k + 1 : ℕ) : ℝ≥0) / 2 ^ (r + 1) := by
      rw [dyadicApprox_def, ← hm_def, hm_eq]
    rw [h2k_eq, hm_approx, dist_comm]
    exact hstep (2 * k) hi_lt

private lemma dist_dyadicApprox_le_tsum {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1))
    {x : ℝ≥0} (hx : x ≤ 1) (n : ℕ) {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r) :
    dist (f (dyadicApprox n x)) (f x) ≤ ∑' k : ℕ, M (n + 1 + k) := by
  have hM_nonneg (k : ℕ) : 0 ≤ M (n + 1 + k) :=
    dist_nonneg.trans (hM (n + 1 + k) (by omega) 0 (Nat.two_pow_pos _))
  have hshift_sum : Summable (fun k : ℕ ↦ M (n + 1 + k)) :=
    hM_sum.comp_injective (add_right_injective (n + 1))
  have hstep (k : ℕ) :
      dist (f (dyadicApprox (k + n) x)) (f (dyadicApprox (k.succ + n) x)) ≤ M (n + 1 + k) := by
    have hidx : n + 1 + k = k + n + 1 := by omega
    rw [Nat.succ_add, hidx]
    exact dist_dyadicApprox_succ_le hx (k + n) (hidx ▸ hM_nonneg k) (hM (k + n + 1) (by omega))
  have h_app : Tendsto (fun k : ℕ ↦ dyadicApprox (k + n) x) atTop (𝓝 x) :=
    (tendsto_dyadicApprox x).comp (tendsto_add_atTop_nat n)
  have h_nhds : Tendsto (fun k : ℕ ↦ dyadicApprox (k + n) x) atTop (𝓝[Iic 1] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_app
      (Eventually.of_forall fun k ↦ (dyadicApprox_le_and_lt (k + n)).1.trans hx)
  simpa only [Nat.zero_add] using dist_le_tsum_of_dist_le_of_tendsto₀
    (f := fun k ↦ f (dyadicApprox (k + n) x)) (fun k ↦ M (n + 1 + k))
    hstep hshift_sum ((hf x hx).tendsto.comp h_nhds)

private lemma dist_le_of_dyadic {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1)) (n : ℕ)
    {h C : ℝ} (hC0 : 0 ≤ C)
    (hcoarse : ∀ i j : ℕ, i < j → j ≤ 2 ^ n →
      ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n →
      dist (f ((j : ℝ≥0) / 2 ^ n)) (f ((i : ℝ≥0) / 2 ^ n)) ≤ C)
    {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r)
    {s t : ℝ≥0} (hst : s ≤ t) (ht1 : t ≤ 1) (hdiff : (t : ℝ) - s ≤ h) :
    dist (f s) (f t) ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by
  have hs1 : s ≤ 1 := hst.trans ht1
  -- Approximate `s` and `t` from below on the level-`n` dyadic grid.
  set i := ⌊(s : ℝ) * (2 : ℝ) ^ n⌋₊ with hi_def
  set j := ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ with hj_def
  have hij : i ≤ j := Nat.floor_mono (by gcongr)
  have hj_le : j ≤ 2 ^ n := Nat.floor_le_of_le <| by
    calc (t : ℝ) * (2 : ℝ) ^ n ≤ 1 * (2 : ℝ) ^ n := by gcongr; exact_mod_cast ht1
      _ = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
  -- Bound the coarse level-`n` jump between `dyadicApprox n s` and `dyadicApprox n t`.
  have hmid : dist (f (dyadicApprox n s)) (f (dyadicApprox n t)) ≤ C := by
    rcases eq_or_lt_of_le hij with h_eq | h_lt
    · rw [dyadicApprox_def, dyadicApprox_def, ← hi_def, ← hj_def, h_eq, dist_self]
      exact hC0
    · have hlen : ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n := by
        have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have hrhs : h + 1 / (2 : ℝ) ^ n = (h * (2 : ℝ) ^ n + 1) / (2 : ℝ) ^ n := by
          field_simp
        rw [Nat.cast_sub hij, hrhs, div_lt_div_iff_of_pos_right h2]
        have hj_r : (j : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n := Nat.floor_le (by positivity)
        have hi_r : (s : ℝ) * (2 : ℝ) ^ n < (i : ℝ) + 1 := Nat.lt_floor_add_one _
        have hts_mul : ((t : ℝ) - s) * (2 : ℝ) ^ n ≤ h * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hdiff h2.le
        linarith
      rw [dist_comm]
      exact hcoarse i j h_lt hj_le hlen
  -- Combine the coarse jump with the two dyadic refinement tails at `s` and `t`.
  have htail_s := dist_dyadicApprox_le_tsum hf hs1 n hM_sum hM
  have htail_t := dist_dyadicApprox_le_tsum hf ht1 n hM_sum hM
  calc dist (f s) (f t)
      ≤ dist (f s) (f (dyadicApprox n s)) + dist (f (dyadicApprox n s)) (f (dyadicApprox n t)) +
          dist (f (dyadicApprox n t)) (f t) := dist_triangle4 _ _ _ _
    _ = dist (f (dyadicApprox n s)) (f s) + dist (f (dyadicApprox n s)) (f (dyadicApprox n t)) +
          dist (f (dyadicApprox n t)) (f t) := by rw [dist_comm (f s)]
    _ ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by linarith

end NNRealInterval

end TauCeti

/-- **Deterministic dyadic chaining bound on `[0, 1]`**: if `f : ℝ≥0 → Y` is continuous on `[0, 1]`,
`C ≥ 0` bounds every level-`n` dyadic increment of length `< h + 2 ^ (-n)`, and a summable sequence
`M` bounds single-step dyadic increments at all finer levels `r ≥ n + 1`, then
`modulusOfContinuityOn f (Set.Iic 1) h ≤ C + 2 * ∑' k, M (n + 1 + k)`. -/
theorem ContinuousOn.modulusOfContinuityOn_Iic_one_le_of_dyadic {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1)) (n : ℕ) {h C : ℝ} (hC0 : 0 ≤ C)
    (hcoarse : ∀ i j : ℕ, i < j → j ≤ 2 ^ n →
      ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n →
      dist (f ((j : ℝ≥0) / 2 ^ n)) (f ((i : ℝ≥0) / 2 ^ n)) ≤ C)
    {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r) :
    TauCeti.modulusOfContinuityOn f (Iic 1) h ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by
  have htsum_nonneg : 0 ≤ ∑' k : ℕ, M (n + 1 + k) :=
    (dist_nonneg (x := f (TauCeti.dyadicApprox n 0)) (y := f 0)).trans
      (TauCeti.dist_dyadicApprox_le_tsum hf zero_le_one n hM_sum hM)
  -- Reduce to ordered pairs `x ≤ y` in `[0, 1]` and apply `TauCeti.dist_le_of_dyadic`.
  refine TauCeti.modulusOfContinuityOn_le (by positivity) fun x hx y hy hxy ↦ ?_
  rcases le_total x y with hle | hle
  · refine TauCeti.dist_le_of_dyadic hf n hC0 hcoarse hM_sum hM hle hy ?_
    rwa [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hle)), neg_sub] at hxy
  · rw [dist_comm]
    refine TauCeti.dist_le_of_dyadic hf n hC0 hcoarse hM_sum hM hle hx ?_
    rwa [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hle))] at hxy
