/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Basic
public import TauCeti.Analysis.Holder.Interpolation
public import TauCeti.Analysis.Holder.Normed

/-!
# Parabolic Hölder seminorms on time slabs

For a function `v` on a set of parabolic space-time, typically the closed time slab `E × [a, b]`,
the parabolic `α`-Hölder seminorm `[v]_{α,par}` is Mathlib's `eHolderNorm α v`, taken with respect
to the parabolic distance `dist x y + √|t - s|`. This file identifies it with the supremum of the
parabolic difference quotients and, on slabs, compares it with two separate seminorms:

* the *spatial* seminorm `spaceEHolderNorm α v`, the supremum over times `t` of the `α`-Hölder
  seminorms of the slices `x ↦ v (x, t)`;
* the *temporal* seminorm `timeEHolderNorm γ v`, the supremum over positions `x` of the
  `γ`-Hölder seminorms of the slices `t ↦ v (x, t)`, with respect to the ordinary time distance
  `|t - s|`.

A function is parabolically `α`-Hölder exactly when it is `α`-Hölder in space and `α / 2`-Hölder
in time, uniformly, with
`max (spaceEHolderNorm α v) (timeEHolderNorm (α / 2) v) ≤ eHolderNorm α v`
and `eHolderNorm α v ≤ spaceEHolderNorm α v + timeEHolderNorm (α / 2) v`.

For a function `u` of the coordinates, twice differentiable in space and differentiable in time,
the temporal `(1 + α) / 2` seminorm of the spatial gradient `D_x u` on a slab is at most the sum of
the parabolic `α` seminorms of the Hessian `D_x² u` and of the time derivative `∂ₜ u`. Thus this
seminorm, which enters the norm of `C^{2+α, 1+α/2}`, is controlled by the other top-order terms.

Bounded Lipschitz maps on ordinary space-time also give uniformly parabolic Hölder maps
under translations of space and time.

Finally, a bounded `α`-Hölder field on space is a time-independent bounded parabolically
`α`-Hölder field on any slab, since the spatial position is `1`-Lipschitz for the parabolic
distance.

## Main declarations

* `TauCeti.ParabolicSpaceTime.exists_holderWith_comp_coords`: the bounded Lipschitz bridge
  from ordinary space-time to parabolic Hölder maps, uniformly under translation.
* `TauCeti.ParabolicSpaceTime.eHolderNorm_eq_iSup_dist_add_sqrt`: the parabolic seminorm is the
  supremum of `dist (v p) (v q) / (dist x y + √|t - s|) ^ α`.
* `TauCeti.ParabolicSpaceTime.spaceEHolderNorm`, `TauCeti.ParabolicSpaceTime.timeEHolderNorm`:
  the separate spatial and temporal seminorms.
* `TauCeti.ParabolicSpaceTime.holderWith_of_holderOnWith_slab`: the time slices of a
  parabolically Hölder function on a slab are Hölder in space with the same constant.
* `TauCeti.ParabolicSpaceTime.eHolderNorm_le_timeEHolderNorm`,
  `TauCeti.ParabolicSpaceTime.memHolder_timeSlice_of_timeEHolderNorm_lt_top`: each time slice is
  controlled by the temporal seminorm.
* `TauCeti.ParabolicSpaceTime.timeEHolderNorm_le_of_lipschitzWith`: reparametrizing time by a
  `1`-Lipschitz map, such as a restriction or a time reversal, does not increase the temporal
  seminorm.
* `TauCeti.ParabolicSpaceTime.spaceEHolderNorm_le_eHolderNorm`,
  `TauCeti.ParabolicSpaceTime.timeEHolderNorm_div_two_le_eHolderNorm`,
  `TauCeti.ParabolicSpaceTime.eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm`: the
  comparison of the parabolic seminorm with the separate ones.
* `TauCeti.ParabolicSpaceTime.memHolder_slab_iff`: the corresponding characterisation of
  parabolic Hölder functions.
* `TauCeti.ParabolicSpaceTime.timeEHolderNorm_le_timeEHolderNorm_add_spaceEHolderNorm`,
  `TauCeti.ParabolicSpaceTime.timeEHolderNorm_le_eHolderNorm_add_eHolderNorm`: control of the
  temporal seminorm of the spatial gradient.
* `TauCeti.HolderSpace.compSlabSpaceL`: a Hölder field on space as a time-independent parabolic
  Hölder field on a slab.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

open Set
open scoped ENNReal NNReal

namespace TauCeti.ParabolicSpaceTime

variable {E F : Type*} {a b : ℝ}

/-- Bounded Lipschitz maps on ordinary space-time are uniformly Hölder for the
parabolic distance, even when time ranges over the whole real line. -/
theorem exists_holderWith_comp_coords [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ≥0} (hα : α ≤ 1) {f : E × ℝ → F}
    {K : ℝ≥0} (hf : LipschitzWith K f) {M : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ M) :
    ∃ C : ℝ≥0, ∀ z : E × ℝ,
      HolderWith C α (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) := by
  let C : ℝ≥0 := ⟨max (K : ℝ) (2 * M), le_max_of_le_left K.coe_nonneg⟩
  have hbig (p q : E × ℝ) : dist (f p) (f q) ≤ 2 * M := by
    calc
      _ ≤ ‖f p‖ + ‖f q‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hbound p, hbound q]
  refine ⟨C, fun z ↦ ?_⟩
  have hdist (p q : ParabolicSpaceTime E) :
      dist (f (p.space - z.1, p.time - z.2)) (f (q.space - z.1, q.time - z.2)) ≤
        C * dist p q := by
    by_cases hd : dist p q ≤ 1
    · have ht := abs_time_sub_le_dist_of_dist_le_one p q hd
      calc
        _ ≤ K * dist (p.space - z.1, p.time - z.2) (q.space - z.1, q.time - z.2) :=
          hf.dist_le_mul _ _
        _ ≤ K * dist p q := by
          gcongr
          simpa [Prod.dist_eq, dist_sub_right, Real.dist_eq] using
            max_le (dist_space_le p q) ht
        _ ≤ C * dist p q := by gcongr; exact le_max_left _ _
    · calc
        _ ≤ 2 * M := hbig _ _
        _ ≤ C * dist p q := by
          have hc : 2 * M ≤ (C : ℝ) := le_max_right _ _
          nlinarith [C.coe_nonneg]
  have hlip : LipschitzWith C
      (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) :=
    LipschitzWith.of_dist_le_mul hdist
  have hzero : HolderWith C 0
      (fun p : ParabolicSpaceTime E ↦ f (p.space - z.1, p.time - z.2)) := by
    intro p q
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    exact (hbig _ _).trans (le_max_right _ _)
  simpa using hzero.of_le_of_le hlip.holderWith (by positivity : 0 ≤ α) hα

/-- The parabolic Hölder seminorm of a function on a set of parabolic space-time is the supremum
of the parabolic difference quotients `dist (v p) (v q) / (dist x y + √|t - s|) ^ α` over distinct
points `p = (x, t)` and `q = (y, s)`. -/
theorem eHolderNorm_eq_iSup_dist_add_sqrt [MetricSpace E] [PseudoMetricSpace F] (α : ℝ≥0)
    {S : Set (ParabolicSpaceTime E)} (v : S → F) :
    eHolderNorm α v = ⨆ (p) (q) (_ : p ≠ q), ENNReal.ofReal (dist (v p) (v q) /
      (dist (p : ParabolicSpaceTime E).space (q : ParabolicSpaceTime E).space +
        √|(p : ParabolicSpaceTime E).time - (q : ParabolicSpaceTime E).time|) ^ (α : ℝ)) := by
  simp_rw [eHolderNorm_eq_iSup_dist, Subtype.dist_eq, dist_eq]

variable [PseudoEMetricSpace F]

/-- The spatial `α`-Hölder seminorm of a function on the slab `E × [a, b]`: the supremum over
times `t ∈ [a, b]` of the `α`-Hölder seminorms of the slices `x ↦ v (x, t)`. -/
def spaceEHolderNorm [PseudoEMetricSpace E] (α : ℝ≥0) (v : slab (E := E) a b → F) : ℝ≥0∞ :=
  ⨆ t : Icc a b, eHolderNorm α fun x => v (slabMk x t)

/-- The temporal `γ`-Hölder seminorm of a function on the slab `E × [a, b]`: the supremum over
positions `x` of the `γ`-Hölder seminorms of the slices `t ↦ v (x, t)`, with respect to the
ordinary distance `|t - s|` on `[a, b]`. -/
def timeEHolderNorm (γ : ℝ≥0) (v : slab (E := E) a b → F) : ℝ≥0∞ :=
  ⨆ x : E, eHolderNorm γ fun t : Icc a b => v (slabMk x t)

/-- The spatial seminorm is bounded by `C` exactly when every time slice satisfies the
`α`-Hölder inequality with constant `C`. -/
theorem spaceEHolderNorm_le_iff [MetricSpace E] {α : ℝ≥0} {v : slab (E := E) a b → F} {C : ℝ≥0∞} :
    spaceEHolderNorm α v ≤ C ↔ ∀ (t : Icc a b) (x y : E),
      edist (v (slabMk x t)) (v (slabMk y t)) ≤ C * edist x y ^ (α : ℝ) := by
  simp only [spaceEHolderNorm, iSup_le_iff, eHolderNorm_le_iff]

/-- A function of the coordinates that is parabolically `α`-Hölder on the slab `E × [a, b]` is
`α`-Hölder in space, with the same constant, on every time slice of the slab. -/
theorem holderWith_of_holderOnWith_slab [PseudoEMetricSpace E] {f : ℝ → E → F} {H α : ℝ≥0}
    {s : ℝ} (hpar : HolderOnWith H α (fun p : ParabolicSpaceTime E => f p.time p.space)
      (slab a b)) (hs : s ∈ Icc a b) : HolderWith H α (f s) := by
  intro y z
  simpa [edist_ofCoords] using hpar (ofCoords y s) (by simpa using hs) (ofCoords z s)
    (by simpa using hs)

/-- The temporal seminorm is bounded by `C` exactly when every spatial position satisfies the
`γ`-Hölder inequality in time with constant `C`. -/
theorem timeEHolderNorm_le_iff {γ : ℝ≥0} {v : slab (E := E) a b → F} {C : ℝ≥0∞} :
    timeEHolderNorm γ v ≤ C ↔ ∀ (x : E) (t s : Icc a b),
      edist (v (slabMk x t)) (v (slabMk x s)) ≤ C * edist t s ^ (γ : ℝ) := by
  simp only [timeEHolderNorm, iSup_le_iff, eHolderNorm_le_iff]

/-- The Hölder seminorm of each time slice is bounded by the temporal seminorm. -/
theorem eHolderNorm_le_timeEHolderNorm (γ : ℝ≥0) (v : slab (E := E) a b → F) (x : E) :
    eHolderNorm γ (fun t : Icc a b => v (slabMk x t)) ≤ timeEHolderNorm γ v :=
  le_iSup (fun x => eHolderNorm γ fun t : Icc a b => v (slabMk x t)) x

/-- If the temporal `γ`-seminorm is finite, then every time slice is `γ`-Hölder. -/
theorem memHolder_timeSlice_of_timeEHolderNorm_lt_top {γ : ℝ≥0} {v : slab (E := E) a b → F}
    (h : timeEHolderNorm γ v < ∞) (x : E) : MemHolder γ fun t : Icc a b => v (slabMk x t) :=
  eHolderNorm_lt_top.1 ((eHolderNorm_le_timeEHolderNorm γ v x).trans_lt h)

/-- Reparametrizing time by a `1`-Lipschitz map does not increase the temporal seminorm: if
`w (x, t) = v (x, φ t)` on the slab `E × [a', b']` for a `1`-Lipschitz `φ : [a', b'] → [a, b]`,
such as the inclusion of a subinterval or the reversal `t ↦ T - t`, then
`[w]_{t,γ} ≤ [v]_{t,γ}`. -/
theorem timeEHolderNorm_le_of_lipschitzWith {a' b' : ℝ} {γ : ℝ≥0} {v : slab (E := E) a b → F}
    {w : slab (E := E) a' b' → F} {φ : Icc a' b' → Icc a b} (hφ : LipschitzWith 1 φ)
    (hw : ∀ x t, w (slabMk x t) = v (slabMk x (φ t))) :
    timeEHolderNorm γ w ≤ timeEHolderNorm γ v := by
  refine timeEHolderNorm_le_iff.2 fun x t s ↦ ?_
  rw [hw, hw]
  calc edist (v (slabMk x (φ t))) (v (slabMk x (φ s)))
      ≤ timeEHolderNorm γ v * edist (φ t) (φ s) ^ (γ : ℝ) :=
        timeEHolderNorm_le_iff.1 le_rfl x (φ t) (φ s)
    _ ≤ timeEHolderNorm γ v * edist t s ^ (γ : ℝ) := by
        gcongr
        simpa using hφ t s

variable [MetricSpace E]

/-- The spatial seminorm is bounded by the parabolic seminorm: at a common time, the parabolic
distance is the spatial distance. -/
theorem spaceEHolderNorm_le_eHolderNorm (α : ℝ≥0) (v : slab (E := E) a b → F) :
    spaceEHolderNorm α v ≤ eHolderNorm α v := by
  refine spaceEHolderNorm_le_iff.2 fun t x y => ?_
  simpa [edist_slabMk] using edist_le_eHolderNorm_mul α v (slabMk x t) (slabMk y t)

/-- The temporal `α / 2`-seminorm is bounded by the parabolic `α`-seminorm: at a common position,
the parabolic distance is the square root of the time distance. -/
theorem timeEHolderNorm_div_two_le_eHolderNorm (α : ℝ≥0) (v : slab (E := E) a b → F) :
    timeEHolderNorm (α / 2) v ≤ eHolderNorm α v := by
  refine timeEHolderNorm_le_iff.2 fun x t s => ?_
  rw [← edist_slabMk_same_space_rpow x t s]
  exact edist_le_eHolderNorm_mul α v (slabMk x t) (slabMk x s)

/-- The parabolic `α`-seminorm is bounded by the sum of the spatial `α`-seminorm and the temporal
`α / 2`-seminorm. -/
theorem eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm (α : ℝ≥0)
    (v : slab (E := E) a b → F) :
    eHolderNorm α v ≤ spaceEHolderNorm α v + timeEHolderNorm (α / 2) v := by
  refine eHolderNorm_le_iff.2 fun p q => ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  obtain ⟨y, s, rfl⟩ : ∃ y s, slabMk y s = q := ⟨_, _, slabMk_space_slabTime q⟩
  have hspace : edist x y ^ (α : ℝ) ≤ edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
    rw [edist_slabMk]
    gcongr
    exact le_self_add
  have htime : edist t s ^ ((α / 2 : ℝ≥0) : ℝ) ≤ edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
    rw [← edist_slabMk_same_space_rpow x t s, edist_slabMk, edist_slabMk, edist_self, zero_add]
    gcongr
    exact le_add_self
  -- Move first in space at the time `t`, then in time at the position `y`.
  calc edist (v (slabMk x t)) (v (slabMk y s))
      ≤ edist (v (slabMk x t)) (v (slabMk y t)) + edist (v (slabMk y t)) (v (slabMk y s)) :=
        edist_triangle _ _ _
    _ ≤ spaceEHolderNorm α v * edist x y ^ (α : ℝ) +
        timeEHolderNorm (α / 2) v * edist t s ^ ((α / 2 : ℝ≥0) : ℝ) := by
        gcongr
        · exact spaceEHolderNorm_le_iff.1 le_rfl t x y
        · exact timeEHolderNorm_le_iff.1 le_rfl y t s
    _ ≤ (spaceEHolderNorm α v + timeEHolderNorm (α / 2) v) *
        edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
        rw [add_mul]
        gcongr

/-- A function on a slab is parabolically `α`-Hölder exactly when it is `α`-Hölder in space and
`α / 2`-Hölder in time, uniformly in the other variable. -/
theorem memHolder_slab_iff {α : ℝ≥0} {v : slab (E := E) a b → F} :
    MemHolder α v ↔ spaceEHolderNorm α v < ∞ ∧ timeEHolderNorm (α / 2) v < ∞ := by
  rw [← eHolderNorm_lt_top]
  refine ⟨fun h => ⟨(spaceEHolderNorm_le_eHolderNorm α v).trans_lt h,
    (timeEHolderNorm_div_two_le_eHolderNorm α v).trans_lt h⟩, fun h => ?_⟩
  exact (eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α v).trans_lt
    (ENNReal.add_lt_top.2 h)

end TauCeti.ParabolicSpaceTime

/-! ### The temporal seminorm of the spatial gradient -/

namespace TauCeti.ParabolicSpaceTime

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {u : E → ℝ → F}
  {u' : E → ℝ → E →L[ℝ] F} {u'' : E → ℝ → E →L[ℝ] E →L[ℝ] F} {uₜ : E → ℝ → F}

/-- **The temporal seminorm of the spatial gradient is controlled.** Let `u (x, t)` be twice
differentiable in `x ∈ E` and differentiable in `t` within `[a, b]`, with spatial derivatives
`u'`, `u''` and time derivative `uₜ`. On the slab `E × [a, b]`, the temporal `(1 + α) / 2`
seminorm of the gradient `u'` is at most the sum of the temporal `α / 2` seminorm of the Hessian
`u''` and the spatial `α` seminorm of `uₜ`. -/
theorem timeEHolderNorm_le_timeEHolderNorm_add_spaceEHolderNorm (α : ℝ≥0)
    (hu' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u · t) (u' y t) y)
    (hu'' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u' · t) (u'' y t) y)
    (huₜ : ∀ y, ∀ t ∈ Icc a b, HasDerivWithinAt (u y) (uₜ y t) (Icc a b) t) :
    timeEHolderNorm ((1 + α) / 2)
        (fun p : slab (E := E) a b => u' (p : ParabolicSpaceTime E).space (slabTime p)) ≤
      timeEHolderNorm (α / 2)
          (fun p : slab (E := E) a b => u'' (p : ParabolicSpaceTime E).space (slabTime p)) +
        spaceEHolderNorm α
          (fun p : slab (E := E) a b => uₜ (p : ParabolicSpaceTime E).space (slabTime p)) := by
  set C₂ := timeEHolderNorm (α / 2)
    (fun p : slab (E := E) a b => u'' (p : ParabolicSpaceTime E).space (slabTime p))
  set Cₜ := spaceEHolderNorm α
    (fun p : slab (E := E) a b => uₜ (p : ParabolicSpaceTime E).space (slabTime p))
  rcases eq_or_ne C₂ ∞ with h₂ | h₂
  · simp [h₂]
  rcases eq_or_ne Cₜ ∞ with hₜ | hₜ
  · simp [hₜ]
  have hC₂ : ∀ y, HolderOnWith C₂.toNNReal (α / 2) (u'' y) (Icc a b) := fun y t ht s hs => by
    simpa [ENNReal.coe_toNNReal h₂] using timeEHolderNorm_le_iff.1 (le_refl C₂) y ⟨t, ht⟩ ⟨s, hs⟩
  have hCₜ : ∀ t ∈ Icc a b, HolderWith Cₜ.toNNReal α (uₜ · t) := fun t ht y z => by
    simpa [ENNReal.coe_toNNReal hₜ] using spaceEHolderNorm_le_iff.1 (le_refl Cₜ) ⟨t, ht⟩ y z
  refine timeEHolderNorm_le_iff.2 fun x t s => ?_
  have := holderOnWith_Icc_of_hasFDerivAt_of_hasDerivWithinAt hu' hu'' huₜ hC₂ hCₜ x t t.2 s s.2
  simpa [ENNReal.coe_toNNReal h₂, ENNReal.coe_toNNReal hₜ, Subtype.edist_eq] using this

/-- **The temporal seminorm of the spatial gradient is controlled by parabolic seminorms.** On
the slab `E × [a, b]`, the temporal `(1 + α) / 2` seminorm of the spatial gradient of `u` is at
most the sum of the parabolic `α` seminorms of its Hessian and of its time derivative. In
particular it is finite whenever these are. -/
theorem timeEHolderNorm_le_eHolderNorm_add_eHolderNorm (α : ℝ≥0)
    (hu' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u · t) (u' y t) y)
    (hu'' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u' · t) (u'' y t) y)
    (huₜ : ∀ y, ∀ t ∈ Icc a b, HasDerivWithinAt (u y) (uₜ y t) (Icc a b) t) :
    timeEHolderNorm ((1 + α) / 2)
        (fun p : slab (E := E) a b => u' (p : ParabolicSpaceTime E).space (slabTime p)) ≤
      eHolderNorm α
          (fun p : slab (E := E) a b => u'' (p : ParabolicSpaceTime E).space (slabTime p)) +
        eHolderNorm α
          (fun p : slab (E := E) a b => uₜ (p : ParabolicSpaceTime E).space (slabTime p)) :=
  (timeEHolderNorm_le_timeEHolderNorm_add_spaceEHolderNorm α hu' hu'' huₜ).trans
    (add_le_add (timeEHolderNorm_div_two_le_eHolderNorm α _) (spaceEHolderNorm_le_eHolderNorm α _))

end TauCeti.ParabolicSpaceTime

namespace TauCeti.HolderSpace

/-! ### Time-independent Hölder fields on a slab -/

variable {α : ℝ≥0} {E Y : Type*} [MetricSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {a b : ℝ}

open ParabolicSpaceTime

/-- A bounded `α`-Hölder field on space, viewed as a time-independent bounded parabolically
`α`-Hölder field on the slab `E × [a, b]`: precomposition with the spatial position, which is
`1`-Lipschitz for the parabolic distance. -/
def compSlabSpaceL : HolderSpace α E Y →L[ℝ] HolderSpace α (slab (E := E) a b) Y :=
  compLipschitzL _ lipschitzWith_slabSpace

@[simp]
theorem compSlabSpaceL_apply (f : HolderSpace α E Y) (p : slab (E := E) a b) :
    compSlabSpaceL f p = f (p : ParabolicSpaceTime E).space :=
  compLipschitzL_apply _ _ _

end TauCeti.HolderSpace
