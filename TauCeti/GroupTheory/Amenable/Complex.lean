/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Complex

/-!
# Complex means

Bekka, de la Harpe and Valette define means on complex-valued functions. A *complex mean* on
`TauCeti.ComplexUCB G` is a complex linear functional `M` which takes the value `1` at `1` and is
positive in the sense that `0 ≤ M f` for every real function `f ≥ 0`, the order on `ℂ` being
`ComplexOrder`. Positivity therefore only concerns real nonnegative functions.

Complex means are exactly the complexifications of the (real) means of `TauCeti.Mean`. A mean `m`
complexifies to

```text
m.toComplexMean f = m (re f) + m (im f) * I,
```

and a complex mean `M` restricts to the real mean `M.toMean f = re (M f)` on real functions.
Positivity forces `M f` to be real for every real function `f`, since `f` is the difference of the
nonnegative functions `‖f‖` and `‖f‖ - f`; with `f = ofReal (re f) + I • ofReal (im f)`, this shows
that the two constructions are mutually inverse. They preserve left invariance, so a topological
group is amenable exactly when it carries a left-invariant complex mean. A complex mean is bounded
by the supremum norm, `‖M f‖ ≤ ‖f‖`, and has operator norm one.

The real means remain the primary API; this file only provides the comparison with the complex
convention.

## Main definitions

* `TauCeti.ComplexMean G`: a complex linear functional on `ComplexUCB G`, nonnegative on real
  nonnegative functions and taking the value `1` at `1`.
* `TauCeti.Mean.toComplexMean`: the complexification `f ↦ m (re f) + m (im f) * I` of a mean.
* `TauCeti.ComplexMean.toMean`: the restriction `f ↦ re (M f)` of a complex mean to real
  functions.
* `TauCeti.Mean.complexMeanEquiv`: the bijection between means and complex means.
* `TauCeti.ComplexMean.IsLeftInvariant`: `M (L_g f) = M f` for all `g` and `f`.

## Main results

* `TauCeti.ComplexMean.apply_ofReal`: a complex mean takes the real value `M.toMean f` at a real
  function `f`.
* `TauCeti.Mean.toMean_toComplexMean`, `TauCeti.ComplexMean.toComplexMean_toMean`: the inverse
  laws.
* `TauCeti.Mean.isLeftInvariant_toComplexMean_iff`,
  `TauCeti.ComplexMean.isLeftInvariant_toMean_iff`: both constructions preserve and reflect left
  invariance.
* `TauCeti.amenable_iff_exists_complexMean`: a topological group is amenable exactly when it
  carries a left-invariant complex mean.
* `TauCeti.ComplexMean.norm_toContinuousLinearMap`: a complex mean has operator norm one.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1, especially
  Definition G.1.4.
-/

public section

noncomputable section

open Complex
open scoped BoundedContinuousFunction ComplexOrder

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G) in
/-- A complex mean on `ComplexUCB G`: a complex linear functional which is nonnegative, for the
order `ComplexOrder` on `ℂ`, at every real nonnegative function, and takes the value `1` at the
constant function `1`. -/
structure ComplexMean extends ComplexUCB G →ₗ[ℂ] ℂ where
  /-- A complex mean is nonnegative at every real nonnegative function. -/
  map_nonneg' : ∀ f : UCB G, 0 ≤ f → 0 ≤ toFun (ComplexUCB.ofReal f)
  /-- A complex mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

namespace ComplexMean

instance : FunLike (ComplexMean G) (ComplexUCB G) ℂ where
  coe M := M.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (ComplexMean G) ℂ (ComplexUCB G) ℂ where
  map_add M := map_add M.toLinearMap
  map_smulₛₗ M := map_smul M.toLinearMap

/-- Two complex means are equal when they agree on every function. -/
@[ext]
theorem ext {M N : ComplexMean G} (h : ∀ f, M f = N f) : M = N :=
  DFunLike.ext M N h

@[simp]
theorem coe_toLinearMap (M : ComplexMean G) : ⇑M.toLinearMap = ⇑M :=
  (rfl)

/-- A complex mean takes the value `1` at the constant function `1`. -/
@[simp]
theorem map_one (M : ComplexMean G) : M 1 = 1 :=
  M.map_one'

/-- A complex mean is nonnegative at every real nonnegative function. -/
theorem map_nonneg (M : ComplexMean G) {f : UCB G} (hf : 0 ≤ f) : 0 ≤ M (ComplexUCB.ofReal f) :=
  M.map_nonneg' f hf

variable (M : ComplexMean G)

/-- A complex mean takes real values at real functions. -/
theorem im_apply_ofReal (f : UCB G) : (M (ComplexUCB.ofReal f)).im = 0 := by
  -- `f` is the difference of the nonnegative functions `‖f‖ • 1` and `‖f‖ • 1 - f`.
  have h₁ := (nonneg_iff.1 (M.map_nonneg (sub_nonneg.2 (UCB.le_norm_smul_one f)))).2
  have h₂ := (nonneg_iff.1 (M.map_nonneg (UCB.le_def.2 fun x => by simp : (0 : UCB G) ≤ ‖f‖ • 1))).2
  simp only [map_sub, sub_im] at h₁
  linarith

/-! ### Restriction to real functions -/

/-- The restriction `f ↦ re (M f)` of a complex mean to real functions, as a mean on `UCB G`. -/
def toMean : Mean G :=
  Mean.mk₀ (reLm ∘ₗ M.toLinearMap.restrictScalars ℝ ∘ₗ ComplexUCB.ofReal.toLinearMap)
    (fun f hf => (nonneg_iff.1 (M.map_nonneg hf)).1)
    (by simp)

theorem toMean_apply (f : UCB G) : M.toMean f = (M (ComplexUCB.ofReal f)).re :=
  Mean.mk₀_apply _ _ _ f

/-- A complex mean takes the real value `M.toMean f` at a real function `f`. -/
@[simp]
theorem apply_ofReal (f : UCB G) : M (ComplexUCB.ofReal f) = M.toMean f :=
  Complex.ext (by simp [toMean_apply]) (by simp [im_apply_ofReal])

/-- A complex mean is determined by its restriction to real functions:
`M f = M.toMean (re f) + M.toMean (im f) * I`. -/
theorem apply_eq_toMean_re_add_toMean_im_mul_I (f : ComplexUCB G) :
    M f = M.toMean (ComplexUCB.re f) + M.toMean (ComplexUCB.im f) * I := by
  conv_lhs => rw [← ComplexUCB.ofReal_re_add_I_smul_ofReal_im f]
  rw [map_add, map_smul, apply_ofReal, apply_ofReal, smul_eq_mul, mul_comm]

/-- A complex mean is bounded by the supremum norm: `‖M f‖ ≤ ‖f‖`. -/
theorem norm_apply_le (f : ComplexUCB G) : ‖M f‖ ≤ ‖f‖ := by
  -- Rotate `f` by a unit scalar `c` so that `M (c • f) = ‖M f‖` is real and nonnegative.
  obtain ⟨c, hc, hcM⟩ := exists_norm_eq_mul_self (M f)
  have h : ‖M f‖ = M.toMean (ComplexUCB.re (c • f)) := by
    have := congrArg Complex.re (M.apply_eq_toMean_re_add_toMean_im_mul_I (c • f))
    simpa [map_smul, ← hcM] using this
  calc ‖M f‖ ≤ |M.toMean (ComplexUCB.re (c • f))| := h.le.trans (le_abs_self _)
    _ ≤ ‖ComplexUCB.re (c • f)‖ := M.toMean.abs_apply_le_norm _
    _ ≤ ‖c • f‖ := ComplexUCB.norm_re_le _
    _ = ‖f‖ := by rw [norm_smul, hc, one_mul]

/-- The continuous linear functional underlying a complex mean. -/
def toContinuousLinearMap : ComplexUCB G →L[ℂ] ℂ :=
  M.toLinearMap.mkContinuous 1 fun f => by simpa using M.norm_apply_le f

@[simp]
theorem coe_toContinuousLinearMap : ⇑M.toContinuousLinearMap = ⇑M :=
  (rfl)

/-- A complex mean has operator norm one. -/
theorem norm_toContinuousLinearMap : ‖M.toContinuousLinearMap‖ = 1 := by
  refine le_antisymm (M.toLinearMap.mkContinuous_norm_le zero_le_one _) ?_
  simpa using M.toContinuousLinearMap.le_opNorm 1

/-! ### Left invariance -/

/-- A complex mean `M` on `ComplexUCB G` is left invariant when `M (L_g f) = M f` for every `g`
and `f`, where `(L_g f)(x) = f (g⁻¹ * x)`. -/
def IsLeftInvariant : Prop :=
  ∀ (g : G) (f : ComplexUCB G), M (ComplexUCB.leftTranslation g f) = M f

/-- The defining property of a left-invariant complex mean. -/
theorem isLeftInvariant_iff {M : ComplexMean G} :
    M.IsLeftInvariant ↔ ∀ (g : G) (f : ComplexUCB G), M (ComplexUCB.leftTranslation g f) = M f :=
  Iff.rfl

/-- A left-invariant complex mean takes the same value at a function and at its left
translates. -/
@[simp]
theorem IsLeftInvariant.apply_leftTranslation {M : ComplexMean G} (hM : M.IsLeftInvariant)
    (g : G) (f : ComplexUCB G) : M (ComplexUCB.leftTranslation g f) = M f :=
  hM g f

end ComplexMean

namespace Mean

/-! ### Complexification of means -/

variable (m : Mean G)

/-- The complexification `f ↦ m (re f) + m (im f) * I` of a mean, as a complex mean on
`ComplexUCB G`. -/
def toComplexMean : ComplexMean G where
  toFun f := m (ComplexUCB.re f) + m (ComplexUCB.im f) * I
  map_add' f f' := by
    simp only [map_add, ofReal_add]
    ring
  map_smul' c f := by
    apply Complex.ext <;> simp
  map_nonneg' f hf := by simpa using m.toPositiveLinearMap.map_nonneg hf
  map_one' := by simp

@[simp]
theorem toComplexMean_apply (f : ComplexUCB G) :
    m.toComplexMean f = m (ComplexUCB.re f) + m (ComplexUCB.im f) * I :=
  (rfl)

/-- Restricting the complexification of a mean to real functions recovers the mean. -/
@[simp]
theorem toMean_toComplexMean : m.toComplexMean.toMean = m :=
  ext fun f => by
    rw [ComplexMean.toMean_apply, toComplexMean_apply]
    simp

end Mean

/-- Complexifying the restriction of a complex mean to real functions recovers the complex mean. -/
@[simp]
theorem ComplexMean.toComplexMean_toMean (M : ComplexMean G) : M.toMean.toComplexMean = M :=
  ext fun f => by rw [Mean.toComplexMean_apply, M.apply_eq_toMean_re_add_toMean_im_mul_I]

/-- Complexification is a bijection from means on `UCB G` to complex means on `ComplexUCB G`,
with inverse the restriction to real functions. -/
def Mean.complexMeanEquiv : Mean G ≃ ComplexMean G where
  toFun := Mean.toComplexMean
  invFun := ComplexMean.toMean
  left_inv := Mean.toMean_toComplexMean
  right_inv := ComplexMean.toComplexMean_toMean

@[simp]
theorem Mean.complexMeanEquiv_apply (m : Mean G) : Mean.complexMeanEquiv m = m.toComplexMean :=
  (rfl)

@[simp]
theorem Mean.complexMeanEquiv_symm_apply (M : ComplexMean G) :
    Mean.complexMeanEquiv.symm M = M.toMean :=
  (rfl)

/-- Restriction to real functions preserves and reflects left invariance. -/
@[simp]
theorem ComplexMean.isLeftInvariant_toMean_iff {M : ComplexMean G} :
    M.toMean.IsLeftInvariant ↔ M.IsLeftInvariant := by
  refine ⟨fun hM => ComplexMean.isLeftInvariant_iff.2 fun g f => ?_,
    fun hM => Mean.isLeftInvariant_iff.2 fun g f => ?_⟩
  · simp [M.apply_eq_toMean_re_add_toMean_im_mul_I, hM.apply_leftTranslation]
  · simpa using congrArg Complex.re (hM.apply_leftTranslation g (ComplexUCB.ofReal f))

/-- Complexification preserves and reflects left invariance. -/
@[simp]
theorem Mean.isLeftInvariant_toComplexMean_iff {m : Mean G} :
    m.toComplexMean.IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← ComplexMean.isLeftInvariant_toMean_iff, toMean_toComplexMean]

/-- A topological group is amenable exactly when `ComplexUCB G` carries a left-invariant complex
mean. -/
theorem amenable_iff_exists_complexMean :
    Amenable G ↔ ∃ M : ComplexMean G, M.IsLeftInvariant := by
  rw [amenable_iff, ← Mean.complexMeanEquiv.exists_congr_right]
  simp

end TauCeti
