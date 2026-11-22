/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Position and frequency derivatives of weakly parameter-dependent symbols

A weakly parameter-dependent symbol `a(x, ξ, r)` (`TauCeti.WeakParameterSymbol`) is holomorphic
in the reciprocal spectral parameter `r ∈ R` for every fixed `(x, ξ)`, and smooth in `(x, ξ)` for
every fixed `r`, but no joint regularity in `(x, ξ, r)` is part of the definition. This file shows
that its derivatives in the position and in the frequency are again weakly parameter-dependent,
with the parameter derivatives of `∂_{x_l} a` and `∂_{ξ_l} a` the position and frequency
derivatives of those of `a`:

`∂_r^j ∂_{x_l} a = ∂_{x_l} ∂_r^j a`, `∂_r^j ∂_{ξ_l} a = ∂_{ξ_l} ∂_r^j a`.

These are the operations from which the terms `∂_ξ^α b ∂_x^α a` of the composition expansion of
two weakly parameter-dependent symbols are built.

## Main definitions and results

* `TauCeti.WeakParameterSymbol.frequencyDeriv`: the frequency derivative `∂_{ξ_l} a`, of
  frequency order `m - 1`, with parameter derivatives `∂_{ξ_l} ∂_r^j a`
  (`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_frequencyDeriv`) and values
  `∂_{ξ_l} a(·, ·, r)` (`TauCeti.WeakParameterSymbol.toSymbol_frequencyDeriv`).
* `TauCeti.WeakParameterSymbol.spatialDeriv`: the position derivative `∂_{x_l} a`, of frequency
  order `m`, with parameter derivatives `∂_{x_l} ∂_r^j a`
  (`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_spatialDeriv`) and values
  `∂_{x_l} a(·, ·, r)` (`TauCeti.WeakParameterSymbol.toSymbol_spatialDeriv`).

Both derivatives are `ℂ`-linear (`TauCeti.WeakParameterSymbol.frequencyDeriv_add`,
`TauCeti.WeakParameterSymbol.frequencyDeriv_smul` and their position counterparts).

## Implementation notes

The derivative of `a(·, r)` at a point `p` in a direction `v` is the limit of the difference
quotients `t⁻¹ (a(p + t v, r) - a(p, r))`, which are holomorphic in `r`. The second derivatives of
`a(·, r)` are bounded on the segment `p + [-1, 1] v` uniformly in `r ∈ R`, by the symbol estimates
of order `m`, so the difference quotients converge uniformly in `r ∈ R`. By Weierstrass's theorem
the limit is holomorphic in `r`, and its parameter derivatives are the limits of those of the
difference quotients (`TauCeti.differentiableOn_of_hasDerivAt_of_tendstoUniformlyOn`,
`TauCeti.hasDerivAt_iteratedDeriv_of_tendstoUniformlyOn`). This needs the coefficient space `W` to
be complete.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
-/

public section

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace TauCeti

namespace WeakParameterSymbol

variable {n : ℕ} {R : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {d m : ℝ}

/-! ### Derivatives in the point along a direction -/

/-- On a compact set of points `(x, ξ)`, the second derivatives of the parameter derivative
`∂_r^j a(·, r)` are bounded uniformly in `r ∈ R`. -/
private theorem exists_norm_iteratedFDeriv_two_le (a : WeakParameterSymbol n R V W d m) (j : ℕ)
    {Q : Set (CoordinateSpace n × CoordinateSpace n)} (hQ : IsCompact Q) :
    ∃ B, ∀ r ∈ R, ∀ q ∈ Q,
      ‖iteratedFDeriv ℝ 2 (fun p ↦ iteratedDeriv j (a.coefficient p) r) q‖ ≤ B := by
  choose C hC0 hC using fun w : Fin 2 → Fin n ⊕ Fin n ↦ a.exists_bound _
    (hQ.image continuous_fst) j ((List.ofFn w).filterMap Sum.getLeft?)
    ((List.ofFn w).filterMap Sum.getRight?)
  choose D hD using fun w : Fin 2 → Fin n ⊕ Fin n ↦
    (hQ.image continuous_snd).exists_bound_of_continuousOn
      (f := fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^
        ((m + d * j - ((List.ofFn w).filterMap Sum.getRight?).length) / 2))
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun _ ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').continuousOn
  refine ⟨∑ w, C w * D w, fun r hr q hq ↦ ?_⟩
  refine (norm_iteratedFDeriv_le_sum_mixedDeriv ((a.contDiff_iteratedDeriv j r hr).of_le
    (by simp)) q).trans (Finset.sum_le_sum fun w _ ↦ ?_)
  refine (hC w q.1 (mem_image_of_mem _ hq) q.2 r hr).trans
    (mul_le_mul_of_nonneg_left ?_ (hC0 w))
  have h := hD w q.2 (mem_image_of_mem _ hq)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- Along a direction `v`, the derivative of `a(·, r)` is Lipschitz on the segment
`p + [-1, 1] v`, uniformly in `r ∈ R`: its second derivatives are bounded there by the symbol
estimates. -/
private theorem exists_norm_fderiv_apply_sub_le (a : WeakParameterSymbol n R V W d m)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, ∀ r ∈ R, ∀ t ∈ ball (0 : ℝ) 1,
      ‖fderiv ℝ (fun q ↦ a.coefficient q r) (p + t • v) v -
          fderiv ℝ (fun q ↦ a.coefficient q r) (p + (0 : ℝ) • v) v‖ ≤ C * |t| := by
  obtain ⟨B, hB⟩ := a.exists_norm_iteratedFDeriv_two_le 0
    (isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const)) :
      IsCompact ((fun t : ℝ ↦ p + t • v) '' Icc (-1) 1))
  refine ⟨B * ‖v‖ ^ 2, fun r hr t ht ↦ ?_⟩
  set G := fun q ↦ a.coefficient q r
  have hG₂ : ContDiff ℝ 1 (fderiv ℝ G) :=
    (a.contDiff_coefficient_apply hr).fderiv_right (by simp)
  -- `s ↦ D G(p + s v) v` has derivative `D² G(p + s v)(v, v)`, bounded by `B ‖v‖²` on `[0, t]`
  have hφ (s : ℝ) : HasDerivAt (fun s : ℝ ↦ fderiv ℝ G (p + s • v) v)
      (fderiv ℝ (fderiv ℝ G) (p + s • v) v v) s := by
    have hline : HasDerivAt (fun t : ℝ ↦ p + t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have h := ((hG₂.differentiable one_ne_zero _).hasFDerivAt.clm_apply
      (hasFDerivAt_const v (p + s • v))).comp_hasDerivAt s hline
    exact h.congr_deriv (by simp)
  have hbound (s : ℝ) (hs : s ∈ uIcc 0 t) :
      ‖fderiv ℝ (fderiv ℝ G) (p + s • v) v v‖ ≤ B * ‖v‖ ^ 2 := by
    have hs1 : s ∈ Icc (-1 : ℝ) 1 := by
      have := abs_sub_left_of_mem_uIcc hs
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      rw [sub_zero, sub_zero] at this
      exact abs_le.1 (this.trans ht.le)
    have h2 := (iteratedFDeriv ℝ 2 G (p + s • v)).le_opNorm ![v, v]
    rw [iteratedFDeriv_two_apply] at h2
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    refine h2.trans ?_
    rw [← sq]
    exact mul_le_mul_of_nonneg_right (by simpa [G] using hB r hr _ (mem_image_of_mem _ hs1))
      (by positivity)
  have h := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ ↦ (hφ s).hasDerivWithinAt) hbound left_mem_uIcc right_mem_uIcc
  rwa [sub_zero, Real.norm_eq_abs] at h

variable [CompleteSpace W]

/-- **Derivatives in the point and in the parameter commute.** For a point `p` and a direction `v`
of `ℝⁿ × ℝⁿ`, the derivative `r ↦ D a(·, r)(p) v` of the coefficient is holomorphic on `R`, and its
`j`-th parameter derivative is the derivative `D (∂_r^j a(·, r))(p) v`. -/
private theorem differentiableOn_fderiv_apply_and_iteratedDeriv_eq
    (a : WeakParameterSymbol n R V W d m) (p v : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableOn ℂ (fun r ↦ fderiv ℝ (fun q ↦ a.coefficient q r) p v) R ∧
      ∀ j : ℕ, ∀ r ∈ R, iteratedDeriv j (fun r ↦ fderiv ℝ (fun q ↦ a.coefficient q r) p v) r =
        fderiv ℝ (fun q ↦ iteratedDeriv j (a.coefficient q) r) p v := by
  -- `t ↦ ∂_r^j a(p + t v, r)` has derivative `D (∂_r^j a(·, r))(p + t v) v`
  have hderiv (j : ℕ) {r : ℂ} (hr : r ∈ R) (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ iteratedDeriv j (a.coefficient (p + t • v)) r)
        (fderiv ℝ (fun q ↦ iteratedDeriv j (a.coefficient q) r) (p + t • v) v) t :=
    ((a.contDiff_iteratedDeriv j r hr).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using ((hasDerivAt_id t).smul_const v).const_add p)
  obtain ⟨C, hC⟩ := a.exists_norm_fderiv_apply_sub_le p v
  -- the Lipschitz bound makes `D a(p + t v, ·) v` converge uniformly on `R` as `t → 0`
  have hf' : TendstoUniformlyOn
      (fun (t : ℝ) r ↦ fderiv ℝ (fun q ↦ a.coefficient q r) (p + t • v) v)
      (fun r ↦ fderiv ℝ (fun q ↦ a.coefficient q r) (p + (0 : ℝ) • v) v) (𝓝 0) R := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |C| * |t| < ε :=
      ((continuous_const.mul continuous_abs).tendsto' (0 : ℝ) 0 (by simp)).eventually
        (gt_mem_nhds hε)
    filter_upwards [ball_mem_nhds (0 : ℝ) one_pos, hsmall] with t ht htε r hr
    rw [dist_comm, dist_eq_norm]
    exact (hC r hr t ht).trans_lt
      ((mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg t)).trans_lt htε)
  have hF (t : ℝ) (_ : t ∈ ball (0 : ℝ) 1) : DifferentiableOn ℂ (a.coefficient (p + t • v)) R :=
    a.differentiableOn_coefficient _
  have hf (r : ℂ) (hr : r ∈ R) (t : ℝ) (_ : t ∈ ball (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ a.coefficient (p + t • v) r)
        (fderiv ℝ (fun q ↦ a.coefficient q r) (p + t • v) v) t := by
    simpa using hderiv 0 hr t
  refine ⟨?_, fun j r hr ↦ ?_⟩
  · simpa using differentiableOn_of_hasDerivAt_of_tendstoUniformlyOn R.isOpen one_pos hF hf hf'
  · have h := hasDerivAt_iteratedDeriv_of_tendstoUniformlyOn R.isOpen one_pos hF hf hf' j hr
    simpa using h.unique (hderiv j hr 0)

/-! ### Frequency derivatives -/

omit [CompleteSpace W] in
/-- The frequency derivative of the coefficient is its derivative in the direction `(0, e_l)`. -/
private theorem coordinateDeriv_snd_coefficient (a : WeakParameterSymbol n R V W d m) (l : Fin n)
    (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    coordinateDeriv [l] (fun η ↦ a.coefficient (p.1, η) r) p.2 =
      fderiv ℝ (fun q ↦ a.coefficient q r) p (0, EuclideanSpace.single l 1) := by
  by_cases hr : r ∈ R
  · refine coordinateDeriv_snd_eq_fderiv (f := fun q ↦ a.coefficient q r) ?_ l
    exact (a.contDiff_coefficient_apply hr).differentiable (by simp) p
  · simp [a.coefficient_of_notMem _ r hr, ← Pi.zero_def]

/-- The frequency derivative `∂_{ξ_l} a` of a weakly parameter-dependent symbol of frequency order
`m`, a weakly parameter-dependent symbol of frequency order `m - 1`. Its `j`-th parameter
derivative is the frequency derivative `∂_{ξ_l} ∂_r^j a` of the `j`-th parameter derivative of `a`
(`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_frequencyDeriv`). -/
def frequencyDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m) :
    WeakParameterSymbol n R V W d (m - 1) :=
  ofIteratedDerivSymbol (fun p r ↦ coordinateDeriv [l] (fun η ↦ a.coefficient (p.1, η) r) p.2)
    (fun p ↦ DifferentiableOn.contDiffOn
      ((a.differentiableOn_fderiv_apply_and_iteratedDeriv_eq p _).1.congr
        fun r _ ↦ a.coordinateDeriv_snd_coefficient l p r) R.isOpen)
    (fun p r hr ↦ by simp [a.coefficient_of_notMem _ r hr, ← Pi.zero_def])
    (fun j r hr ↦ Symbol.inclusion (le_of_eq (by ring))
      (Symbol.frequencyDeriv l (a.iteratedDerivSymbol j hr)))
    (fun j r hr p ↦ by
      rw [funext fun r ↦ a.coordinateDeriv_snd_coefficient l p r,
        (a.differentiableOn_fderiv_apply_and_iteratedDeriv_eq p _).2 j r hr,
        Symbol.coefficient_inclusion, Symbol.coefficient_frequencyDeriv]
      simp only [coefficient_iteratedDerivSymbol]
      exact coordinateDeriv_snd_eq_fderiv
        (f := fun q ↦ iteratedDeriv j (a.coefficient q) r)
        ((a.contDiff_iteratedDeriv j r hr).differentiable (by simp) p) l)
    (fun j K α β ↦ (a.bddAbove_seminorm_iteratedDerivSymbol j K α (β ++ [l])).imp
      fun C hC r hr ↦ (Symbol.seminorm_inclusion_le _ K α β _).trans
        ((Symbol.seminorm_frequencyDeriv l K α β _).trans_le (hC ⟨⟨r, hr⟩, rfl⟩)))

@[simp]
theorem coefficient_frequencyDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m)
    (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (frequencyDeriv l a).coefficient p r =
      coordinateDeriv [l] (fun η ↦ a.coefficient (p.1, η) r) p.2 :=
  congrFun (congrFun (coefficient_ofIteratedDerivSymbol ..) p) r

/-- The parameter derivatives of `∂_{ξ_l} a` are the frequency derivatives of those of `a`. -/
@[simp]
theorem iteratedDerivSymbol_frequencyDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m)
    (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (frequencyDeriv l a).iteratedDerivSymbol j hr = Symbol.inclusion (le_of_eq (by ring))
      (Symbol.frequencyDeriv l (a.iteratedDerivSymbol j hr)) :=
  iteratedDerivSymbol_ofIteratedDerivSymbol ..

/-- The value of `∂_{ξ_l} a` at a parameter is the frequency derivative of the value of `a`. -/
@[simp]
theorem toSymbol_frequencyDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m) {r : ℂ}
    (hr : r ∈ R) : (frequencyDeriv l a).toSymbol hr = Symbol.frequencyDeriv l (a.toSymbol hr) :=
  Symbol.ext (funext fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem frequencyDeriv_add (l : Fin n) (a b : WeakParameterSymbol n R V W d m) :
    frequencyDeriv l (a + b) = frequencyDeriv l a + frequencyDeriv l b :=
  ext_of_mem fun p r hr ↦ by
    rw [← coefficient_toSymbol _ hr, ← coefficient_toSymbol _ hr]
    simp only [toSymbol_add, toSymbol_frequencyDeriv, map_add]

@[simp]
theorem frequencyDeriv_smul (l : Fin n) (c : ℂ) (a : WeakParameterSymbol n R V W d m) :
    frequencyDeriv l (c • a) = c • frequencyDeriv l a :=
  ext_of_mem fun p r hr ↦ by
    rw [← coefficient_toSymbol _ hr, ← coefficient_toSymbol _ hr]
    simp only [toSymbol_smul, toSymbol_frequencyDeriv, map_smul]

@[simp]
theorem frequencyDeriv_zero (l : Fin n) :
    frequencyDeriv l (0 : WeakParameterSymbol n R V W d m) = 0 := by
  simpa using frequencyDeriv_smul l 0 (0 : WeakParameterSymbol n R V W d m)

/-! ### Position derivatives -/

omit [CompleteSpace W] in
/-- The position derivative of the coefficient is its derivative in the direction `(e_l, 0)`. -/
private theorem coordinateDeriv_fst_coefficient (a : WeakParameterSymbol n R V W d m) (l : Fin n)
    (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    coordinateDeriv [l] (fun y ↦ a.coefficient (y, p.2) r) p.1 =
      fderiv ℝ (fun q ↦ a.coefficient q r) p (EuclideanSpace.single l 1, 0) := by
  by_cases hr : r ∈ R
  · refine coordinateDeriv_fst_eq_fderiv (f := fun q ↦ a.coefficient q r) ?_ l
    exact (a.contDiff_coefficient_apply hr).differentiable (by simp) p
  · simp [a.coefficient_of_notMem _ r hr, ← Pi.zero_def]

/-- The position derivative `∂_{x_l} a` of a weakly parameter-dependent symbol of frequency order
`m`, again a weakly parameter-dependent symbol of frequency order `m`. Its `j`-th parameter
derivative is the position derivative `∂_{x_l} ∂_r^j a` of the `j`-th parameter derivative of `a`
(`TauCeti.WeakParameterSymbol.iteratedDerivSymbol_spatialDeriv`). -/
def spatialDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m) :
    WeakParameterSymbol n R V W d m :=
  ofIteratedDerivSymbol (fun p r ↦ coordinateDeriv [l] (fun y ↦ a.coefficient (y, p.2) r) p.1)
    (fun p ↦ DifferentiableOn.contDiffOn
      ((a.differentiableOn_fderiv_apply_and_iteratedDeriv_eq p _).1.congr
        fun r _ ↦ a.coordinateDeriv_fst_coefficient l p r) R.isOpen)
    (fun p r hr ↦ by simp [a.coefficient_of_notMem _ r hr, ← Pi.zero_def])
    (fun j r hr ↦ Symbol.spatialDeriv l (a.iteratedDerivSymbol j hr))
    (fun j r hr p ↦ by
      rw [funext fun r ↦ a.coordinateDeriv_fst_coefficient l p r,
        (a.differentiableOn_fderiv_apply_and_iteratedDeriv_eq p _).2 j r hr,
        Symbol.coefficient_spatialDeriv]
      simp only [coefficient_iteratedDerivSymbol]
      exact coordinateDeriv_fst_eq_fderiv
        (f := fun q ↦ iteratedDeriv j (a.coefficient q) r)
        ((a.contDiff_iteratedDeriv j r hr).differentiable (by simp) p) l)
    (fun j K α β ↦ (a.bddAbove_seminorm_iteratedDerivSymbol j K (α ++ [l]) β).imp
      fun C hC r hr ↦ (Symbol.seminorm_spatialDeriv l K α β _).trans_le (hC ⟨⟨r, hr⟩, rfl⟩))

@[simp]
theorem coefficient_spatialDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m)
    (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (spatialDeriv l a).coefficient p r =
      coordinateDeriv [l] (fun y ↦ a.coefficient (y, p.2) r) p.1 :=
  congrFun (congrFun (coefficient_ofIteratedDerivSymbol ..) p) r

/-- The parameter derivatives of `∂_{x_l} a` are the position derivatives of those of `a`. -/
@[simp]
theorem iteratedDerivSymbol_spatialDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m)
    (j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (spatialDeriv l a).iteratedDerivSymbol j hr =
      Symbol.spatialDeriv l (a.iteratedDerivSymbol j hr) :=
  iteratedDerivSymbol_ofIteratedDerivSymbol ..

/-- The value of `∂_{x_l} a` at a parameter is the position derivative of the value of `a`. -/
@[simp]
theorem toSymbol_spatialDeriv (l : Fin n) (a : WeakParameterSymbol n R V W d m) {r : ℂ}
    (hr : r ∈ R) : (spatialDeriv l a).toSymbol hr = Symbol.spatialDeriv l (a.toSymbol hr) :=
  Symbol.ext (funext fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem spatialDeriv_add (l : Fin n) (a b : WeakParameterSymbol n R V W d m) :
    spatialDeriv l (a + b) = spatialDeriv l a + spatialDeriv l b :=
  ext_of_mem fun p r hr ↦ by
    rw [← coefficient_toSymbol _ hr, ← coefficient_toSymbol _ hr]
    simp only [toSymbol_add, toSymbol_spatialDeriv, map_add]

@[simp]
theorem spatialDeriv_smul (l : Fin n) (c : ℂ) (a : WeakParameterSymbol n R V W d m) :
    spatialDeriv l (c • a) = c • spatialDeriv l a :=
  ext_of_mem fun p r hr ↦ by
    rw [← coefficient_toSymbol _ hr, ← coefficient_toSymbol _ hr]
    simp only [toSymbol_smul, toSymbol_spatialDeriv, map_smul]

@[simp]
theorem spatialDeriv_zero (l : Fin n) :
    spatialDeriv l (0 : WeakParameterSymbol n R V W d m) = 0 := by
  simpa using spatialDeriv_smul l 0 (0 : WeakParameterSymbol n R V W d m)

end WeakParameterSymbol

end TauCeti
