/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.Interval.VanishingOn
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Data.ENNReal.Inv

/-!
# Interval Sobolev functions vanishing at one endpoint

On a bounded interval `(a, b)` the boundary parts are the subsets of `{a, b}`. For `Γ = {a, b}`
the space `W^{1,p}_Γ(a, b)` of Sobolev functions vanishing on `Γ`
(`TauCeti.w1pVanishingOnSubmodule`) is `W^{1,p}_0(a, b)`, the kernel of the endpoint trace for
finite `p`. This file treats the mixed case of one endpoint. For `1 ≤ p < ∞`, a class lies in
`W^{1,p}_{{a}}(a, b)` exactly when its continuous representative vanishes at `a`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero`), and
symmetrically at `b`. This is the trace characterization of `W^{1,p}_Γ` in dimension one. In
particular `t ↦ t - a` lies in `W^{1,p}_{{a}}(a, b)` for finite `p`. At `p = ∞` it does not, since
every generator has derivative zero near `a` while `t ↦ t - a` has derivative `1`; so finite `p`
is assumed.

Every class of `W^{1,p}_{{a}}(a, b)` vanishes at `a`, for every `p`, as every class of
`W^{1,p}_Γ(a, b)` vanishes on `[a, b] ∩ closure Γ`
(`TauCeti.W1p.intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule`). For the
converse, the affine function `t ↦ t - a` is the restriction to `(a, b)` of the tent
`(b - a) - |t - b|`, which lies in `W^{1,p}_0(a, 2b - a)`, and restriction maps `W^{1,p}_0` of a
larger open set missing `Γ` into `W^{1,p}_Γ` (`TauCeti.W1p.restrictL_mem_w1pVanishingOnSubmodule`).

The two one-endpoint spaces together give the remaining boundary part, `Γ = ∅`: for finite `p`,
`W^{1,p}_∅(a, b)` is all of `W^{1,p}(a, b)`
(`TauCeti.W1p.w1pVanishingOnSubmodule_empty_Ioo_eq_top`), since every class is a class vanishing at
`a` plus an affine class vanishing at `b`. So the mixed problem with no Dirichlet part on an
interval is the Neumann problem, tested on all of `W^{1,p}(a, b)`.

The continuous representative of `u ∈ W^{1,p}(a, b)` is Hölder continuous of exponent `1 - 1/p`,

`|u(t) - u(s)| ≤ |t - s|^{1 - 1/p} ‖u'‖_{Lᵖ(a,b)}`, `s, t ∈ [a, b]`

(`TauCeti.W1p.abs_intervalRepresentativeL_sub_le`, in
`TauCeti.Analysis.Sobolev.W1p.Interval.Representative`). If `u` vanishes at `a`, this gives
`|u(t)| ≤ (t - a)^{1 - 1/p} ‖u'‖_{Lᵖ}` and the **Poincaré–Friedrichs inequality**
`‖u‖_{Lᵖ(a,b)} ≤ (b - a) ‖u'‖_{Lᵖ(a,b)}`
(`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`), with the constant
scaling like the length of the interval. Both hold for every `1 ≤ p ≤ ∞`, with `1 / p.toReal = 0`
at `p = ∞`, and so on all of `W^{1,p}_{{a}}(a, b)`, since every class there vanishes at `a`
(`TauCeti.W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton`).

## Main declarations

* `TauCeti.W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton` and
  `TauCeti.W1p.intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton`: classes of
  `W^{1,p}_{{a}}(a, b)` and `W^{1,p}_{{b}}(a, b)` vanish at the endpoint, for every `p`.
* `TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero` and
  `TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_snd_eq_zero`: the trace
  characterization of `W^{1,p}_{{a}}(a, b)` and `W^{1,p}_{{b}}(a, b)` for finite `p`.
* `TauCeti.W1p.w1pVanishingOnSubmodule_empty_Ioo_eq_top`: `W^{1,p}_∅(a, b) = W^{1,p}(a, b)` for
  finite `p`.
* `TauCeti.W1p.abs_intervalRepresentativeL_le_of_intervalTraceL_fst_eq_zero`,
  `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero` and their versions
  at `b`: the pointwise bound and the Poincaré–Friedrichs inequality.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.8 (the Hölder estimate `|u(x) - u(y)| ≤ ‖u'‖_p |x - y|^{1 - 1/p}` in its proof),
  Theorem 8.12 (`W^{1,p}_0` as the functions vanishing at both endpoints) and §8.4, Example 5 (a
  boundary condition at one endpoint only).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Distributions

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

/-! ### Membership in `W^{1,p}_{{a}}(a, b)` -/

/-- A class whose value on `(a, b)` is a Lipschitz function vanishing at the endpoints of a larger
interval `(a', b')` that misses `Γ` lies in `W^{1,p}_Γ(a, b)`, for finite `p`: the function
represents a class of `W^{1,p}_0(a', b')`, whose restriction to `(a, b)` is a limit of
generators. -/
private theorem mem_w1pVanishingOnSubmodule_of_lipschitzWith (hp : p ≠ ⊤) {a' b' : ℝ}
    (ha' : a' ≤ a) (hb' : b ≤ b') {Γ : Set ℝ} (hΓ : Disjoint Γ (Ioo a' b')) {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hfa : f a' = 0) (hfb : f b' = 0)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : value u =ᵐ[volume.restrict (Ioo a b)] f) :
    u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p Γ := by
  have hdf : MemLp (deriv f) p (volume.restrict (Ioo a' b')) :=
    MemLp.of_bound (measurable_deriv f).aestronglyMeasurable K
      (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hf)
  obtain ⟨w, hw, hwf, -⟩ := hf.lipschitzOnWith.absolutelyContinuousOnInterval
    |>.exists_mem_w1p0Submodule_value_gradient_ae_eq hdf hp hfa hfb
  have hle : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⟨Ioo a' b', isOpen_Ioo⟩ :=
    Ioo_subset_Ioo ha' hb'
  convert restrictL_mem_w1pVanishingOnSubmodule hle hΓ hw using 1
  refine ext_value (Lp.ext (hu.trans ?_))
  exact ((value_restrictL_ae hle w).trans
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha' hb') hwf)).symm

/-- The tent `t ↦ c (r - |t - m|)` is Lipschitz. -/
private theorem lipschitzWith_tent (c r m : ℝ) :
    LipschitzWith ‖c‖₊ fun t : ℝ ↦ c * (r - |t - m|) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, coe_nnNorm, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  calc |r - |x - m| - (r - |y - m|)| = |(|y - m| - |x - m|)| := by ring_nf
    _ ≤ |(y - m) - (x - m)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |x - y| := by rw [abs_sub_comm]; ring_nf

/-- The affine class vanishing at `a`, `t ↦ c (t - a) / (b - a)`, lies in `W^{1,p}_{{a}}(a, b)`
for finite `p`: it is the restriction of the tent `c ((b - a) - |t - b|) / (b - a)`, which vanishes
at both endpoints of `(a, 2b - a)`. -/
private theorem intervalLiftL_fst_zero_mem_w1pVanishingOnSubmodule (hp : p ≠ ⊤)
    (hab : a < b) (c : ℝ) :
    intervalLiftL a b (0, c) ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {a} := by
  refine mem_w1pVanishingOnSubmodule_of_lipschitzWith hp le_rfl (b' := 2 * b - a) (by linarith)
    (disjoint_singleton_left.2 (by simp))
    (lipschitzWith_tent (c * (b - a)⁻¹) (b - a) b) ?_ ?_ ?_
  · rw [abs_of_nonpos (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith)]
    ring
  · filter_upwards [value_ae_eq_intervalRepresentativeL hab (intervalLiftL (p := p) a b (0, c)),
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), intervalRepresentativeL_intervalLiftL,
      abs_of_nonpos (by linarith [hmem.2])]
    ring

/-- The affine class vanishing at `b`, `t ↦ c (b - t) / (b - a)`, lies in `W^{1,p}_{{b}}(a, b)`
for finite `p`: it is the restriction of the tent `c ((b - a) - |t - a|) / (b - a)`, which vanishes
at both endpoints of `(2a - b, b)`. -/
private theorem intervalLiftL_snd_zero_mem_w1pVanishingOnSubmodule (hp : p ≠ ⊤)
    (hab : a < b) (c : ℝ) :
    intervalLiftL a b (c, 0) ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {b} := by
  refine mem_w1pVanishingOnSubmodule_of_lipschitzWith hp (a' := 2 * a - b) (by linarith) le_rfl
    (disjoint_singleton_left.2 (by simp))
    (lipschitzWith_tent (c * (b - a)⁻¹) (b - a) a) ?_ ?_ ?_
  · rw [abs_of_nonpos (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith)]
    ring
  · filter_upwards [value_ae_eq_intervalRepresentativeL hab (intervalLiftL (p := p) a b (c, 0)),
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), intervalRepresentativeL_intervalLiftL,
      abs_of_nonneg (by linarith [hmem.1])]
    field_simp
    ring

/-- A class in `W^{1,p}_{{a}}(a, b)` has continuous representative vanishing at `a`, even at
`p = ∞`, as every class of `W^{1,p}_Γ(a, b)` vanishes on `[a, b] ∩ closure Γ`. -/
theorem intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {a}) :
    (intervalTraceL hab u).1 = 0 := by
  rw [intervalTraceL_apply]
  exact intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule hab hu
    (subset_closure (mem_singleton a))

/-- A class in `W^{1,p}_{{b}}(a, b)` has continuous representative vanishing at `b`, even at
`p = ∞`, as every class of `W^{1,p}_Γ(a, b)` vanishes on `[a, b] ∩ closure Γ`. -/
theorem intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {b}) :
    (intervalTraceL hab u).2 = 0 := by
  rw [intervalTraceL_apply]
  exact intervalRepresentativeL_eq_zero_of_mem_w1pVanishingOnSubmodule hab hu
    (subset_closure (mem_singleton b))

/-- **The trace characterization of `W^{1,p}_{{a}}(a, b)`.** For `1 ≤ p < ∞`, a class lies in the
space of Sobolev functions vanishing at the endpoint `a` exactly when its continuous representative
vanishes at `a`. No condition is imposed at `b`. -/
-- Rewrite before simplification of the open-set coercion in the Sobolev carrier.
@[simp↓]
theorem mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero (hp : p ≠ ⊤)
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} :
    u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {a} ↔
      (intervalTraceL hab u).1 = 0 := by
  refine ⟨intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab, fun hu ↦ ?_⟩
  -- Split off the affine class with the same value at `b`; the rest has zero trace.
  have h0 := (intervalTraceL_eq_iff_sub_intervalLiftL_mem hp hab u
    (0, (intervalTraceL hab u).2)).1 (Prod.ext hu rfl)
  have hmem := add_mem (w1p0Submodule_le_w1pVanishingOnSubmodule
    (disjoint_singleton_left.2 (by simp)) h0)
    (intervalLiftL_fst_zero_mem_w1pVanishingOnSubmodule hp hab
      (intervalTraceL hab u).2)
  rwa [sub_add_cancel] at hmem

/-- **The trace characterization of `W^{1,p}_{{b}}(a, b)`.** For `1 ≤ p < ∞`, a class lies in the
space of Sobolev functions vanishing at the endpoint `b` exactly when its continuous representative
vanishes at `b`. No condition is imposed at `a`. -/
-- Rewrite before simplification of the open-set coercion in the Sobolev carrier.
@[simp↓]
theorem mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_snd_eq_zero (hp : p ≠ ⊤)
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} :
    u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {b} ↔
      (intervalTraceL hab u).2 = 0 := by
  refine ⟨intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab, fun hu ↦ ?_⟩
  -- Split off the affine class with the same value at `a`; the rest has zero trace.
  have h0 := (intervalTraceL_eq_iff_sub_intervalLiftL_mem hp hab u
    ((intervalTraceL hab u).1, 0)).1 (Prod.ext rfl hu)
  have hmem := add_mem (w1p0Submodule_le_w1pVanishingOnSubmodule
    (disjoint_singleton_left.2 (by simp)) h0)
    (intervalLiftL_snd_zero_mem_w1pVanishingOnSubmodule hp hab
      (intervalTraceL hab u).1)
  rwa [sub_add_cancel] at hmem

/-- **No boundary part, no condition, on an interval.** For `1 ≤ p < ∞`, the space
`W^{1,p}_∅(a, b)` of Sobolev functions vanishing on the empty boundary part is all of
`W^{1,p}(a, b)`: every class is the sum of a class vanishing at `a` and the affine class with the
same value at `a` that vanishes at `b`, and both lie in `W^{1,p}_∅(a, b)`. -/
theorem w1pVanishingOnSubmodule_empty_Ioo_eq_top (hp : p ≠ ⊤) :
    w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ∅ = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ?_
  rcases le_or_gt b a with hba | hab
  · -- On an empty interval every class is zero.
    have h0 : volume.restrict (Ioo a b) = 0 := by simp [Ioo_eq_empty_of_le hba]
    have hu : u = 0 := ext_value <| Lp.ext <| by simp [h0, Filter.EventuallyEq]
    exact hu ▸ zero_mem _
  set c := (intervalTraceL hab u).1
  have ha : u - intervalLiftL a b (c, 0) ∈
      w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {a} := by
    rw [mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero hp hab, map_sub,
      intervalTraceL_intervalLiftL, Prod.fst_sub, sub_self]
  have hb : intervalLiftL a b (c, 0) ∈
      w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {b} := by
    rw [mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_snd_eq_zero hp hab,
      intervalTraceL_intervalLiftL]
  have hmem := add_mem (w1pVanishingOnSubmodule_antitone (empty_subset _) ha)
    (w1pVanishingOnSubmodule_antitone (empty_subset _) hb)
  rwa [sub_add_cancel] at hmem

/-! ### Pointwise bounds and the Poincaré–Friedrichs inequality -/

/-- **The pointwise bound at a vanishing endpoint.** If the continuous representative of
`u ∈ W^{1,p}(a, b)` vanishes at `a`, then `|u(t)| ≤ (t - a)^{1 - 1/p} ‖u'‖_{Lᵖ(a,b)}`. -/
theorem abs_intervalRepresentativeL_le_of_intervalTraceL_fst_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : (intervalTraceL hab u).1 = 0) (t : Icc a b) :
    |intervalRepresentativeL hab u t| ≤ ((t : ℝ) - a) ^ (1 - 1 / p.toReal) * ‖gradient u‖ := by
  have h0 : intervalRepresentativeL hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 := by
    rwa [intervalTraceL_apply] at hu
  simpa only [h0, sub_zero, abs_of_nonneg (sub_nonneg.2 t.property.1)] using
    abs_intervalRepresentativeL_sub_le hab u ⟨a, left_mem_Icc.2 hab.le⟩ t

/-- **The pointwise bound at a vanishing endpoint.** If the continuous representative of
`u ∈ W^{1,p}(a, b)` vanishes at `b`, then `|u(t)| ≤ (b - t)^{1 - 1/p} ‖u'‖_{Lᵖ(a,b)}`. -/
theorem abs_intervalRepresentativeL_le_of_intervalTraceL_snd_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : (intervalTraceL hab u).2 = 0) (t : Icc a b) :
    |intervalRepresentativeL hab u t| ≤ (b - t) ^ (1 - 1 / p.toReal) * ‖gradient u‖ := by
  have h0 : intervalRepresentativeL hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 := by
    rwa [intervalTraceL_apply] at hu
  simpa only [h0, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg.2 t.property.2)] using
    abs_intervalRepresentativeL_sub_le hab u t ⟨b, right_mem_Icc.2 hab.le⟩

/-- A pointwise bound `|u(t)| ≤ (b - a)^{1 - 1/p} ‖u'‖_{Lᵖ}` on `[a, b]` gives
`‖u‖_{Lᵖ(a,b)} ≤ (b - a) ‖u'‖_{Lᵖ(a,b)}`. -/
private theorem norm_value_le_mul_norm_gradient_of_forall_abs_le (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : ∀ t : Icc a b, |intervalRepresentativeL hab u t| ≤
      (b - a) ^ (1 - 1 / p.toReal) * ‖gradient u‖) :
    ‖value u‖ ≤ (b - a) * ‖gradient u‖ := by
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖value u t‖ ≤ (b - a) ^ (1 - 1 / p.toReal) * ‖gradient u‖ := by
    filter_upwards [value_ae_eq_intervalRepresentativeL hab u] with t ht
    rw [ht, Real.norm_eq_abs]
    exact hu _
  have hm : (measureUnivNNReal (volume.restrict
      ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) : ℝ) = b - a := by
    simp [measureUnivNNReal, ENNReal.coe_toNNReal_eq_toReal, hab.le]
  refine (Lp.norm_le_of_ae_bound (by positivity) hbound).trans_eq ?_
  rw [hm, ← mul_assoc, ← Real.rpow_add (sub_pos.2 hab)]
  simp

/-- **The Poincaré–Friedrichs inequality on an interval, vanishing at `a`.** If the continuous
representative of `u ∈ W^{1,p}(a, b)` vanishes at `a`, then
`‖u‖_{Lᵖ(a,b)} ≤ (b - a) ‖u'‖_{Lᵖ(a,b)}`. This holds on all of `W^{1,p}_{{a}}(a, b)` for every
`1 ≤ p ≤ ∞`. -/
theorem norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : (intervalTraceL hab u).1 = 0) :
    ‖value u‖ ≤ (b - a) * ‖gradient u‖ := by
  have hexp := ENNReal.one_sub_one_div_toReal_nonneg (Fact.out : 1 ≤ p)
  refine norm_value_le_mul_norm_gradient_of_forall_abs_le hab fun t ↦
    (abs_intervalRepresentativeL_le_of_intervalTraceL_fst_eq_zero hab hu t).trans ?_
  gcongr
  exacts [sub_nonneg.2 t.property.1, t.property.2]

/-- **The Poincaré–Friedrichs inequality on an interval, vanishing at `b`.** If the continuous
representative of `u ∈ W^{1,p}(a, b)` vanishes at `b`, then
`‖u‖_{Lᵖ(a,b)} ≤ (b - a) ‖u'‖_{Lᵖ(a,b)}`. This holds on all of `W^{1,p}_{{b}}(a, b)` for every
`1 ≤ p ≤ ∞`. -/
theorem norm_value_le_mul_norm_gradient_of_intervalTraceL_snd_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : (intervalTraceL hab u).2 = 0) :
    ‖value u‖ ≤ (b - a) * ‖gradient u‖ := by
  have hexp := ENNReal.one_sub_one_div_toReal_nonneg (Fact.out : 1 ≤ p)
  refine norm_value_le_mul_norm_gradient_of_forall_abs_le hab fun t ↦
    (abs_intervalRepresentativeL_le_of_intervalTraceL_snd_eq_zero hab hu t).trans ?_
  gcongr
  exacts [sub_nonneg.2 t.property.2, t.property.1]

end TauCeti.W1p
