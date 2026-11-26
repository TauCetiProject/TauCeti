/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Volume

/-!
# Top powers of a Hermitian metric and their integrals

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)`, of complex dimension `n = finrank ℂ E`, and
let `κ` be a smooth real two-form on `X`. Its wedge powers `κ^m` are the smooth forms
`TauCeti.SmoothForm.wedgePow κ m`: `κ^0` is the constant function `1` and
`κ^(m + 1) = κ^m ∧ κ`. The top power is `κ^n = n!·(κⁿ/n!)`, where `κⁿ/n!` is the symplectic
volume form `TauCeti.SmoothTwoForm.volumeForm κ n`
(`TauCeti.SmoothTwoForm.wedgePow_eq_factorial_smul_volumeForm`).

When `κ` tames the complex structure of `X`, for instance when `κ` is a Hermitian metric
(`TauCeti.SmoothTwoForm.Compatible`), its top power `κ^n` is positive on every tangent basis that
is positively oriented for the canonical orientation `TauCeti.complexManifoldOrientation E X`
(`TauCeti.SmoothTwoForm.Tames.wedgePow_apply_pos`): the symplectic orientation of a taming form
is the complex orientation.

The integral `∫_X g·κ^n` of a function `g` against the top power, for the canonical orientation,
is `TauCeti.formPowIntegral κ g`. On a compact manifold it is linear in continuous `g`. For a
taming `κ` on a manifold of positive dimension it is nonnegative on `g ≥ 0`; on a compact manifold
it is moreover monotone in continuous `g`, and strictly positive on a continuous `g ≥ 0` that is
positive somewhere. So its value `V = ∫_X κ^n` at `g = 1` is positive on a nonempty compact
manifold of positive dimension (`TauCeti.SmoothTwoForm.Tames.formPowIntegral_one_pos`). The
opposite orientation would make it negative.

## Main definitions

* `TauCeti.formPowIntegral κ g`: the integral `∫_X g·κ^n` for the canonical orientation.

## Main results

* `TauCeti.SmoothTwoForm.Tames.wedgePow_apply_pos`: a taming `κ` has `κ^n` positive on positively
  oriented tangent bases.
* `TauCeti.formPowIntegral_zero`, `TauCeti.formPowIntegral_const_mul`,
  `TauCeti.formPowIntegral_neg`, `TauCeti.formPowIntegral_add`, `TauCeti.formPowIntegral_sub`:
  linearity in `g`, additivity on continuous `g` on a compact manifold.
* `TauCeti.SmoothTwoForm.Tames.formPowIntegral_nonneg`: for a taming `κ` on a manifold of
  positive dimension, `g ≥ 0` has nonnegative integral.
* `TauCeti.SmoothTwoForm.Tames.formPowIntegral_mono`: for a taming `κ` on a compact manifold of
  positive dimension, monotonicity in continuous `g`.
* `TauCeti.SmoothTwoForm.Tames.formPowIntegral_pos`,
  `TauCeti.SmoothTwoForm.Tames.formPowIntegral_one_pos`: on a compact manifold of positive
  dimension, a continuous `g ≥ 0` that is positive somewhere has positive integral; in particular
  `V > 0` when the manifold is nonempty.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

namespace SmoothTwoForm

/-- **The top power of a taming form is positive.** If a smooth two-form `κ` on a complex manifold
tames its complex structure, then its top power `κ^n`, `n = finrank ℂ E`, is positive on every
tangent basis that is positively oriented for the canonical orientation. -/
theorem Tames.wedgePow_apply_pos {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {x : X}
    (b : Basis (Fin (2 * finrank ℂ E)) ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hb : b.orientation = (complexManifoldOrientation E X).orientationAt x) :
    0 < (SmoothForm.wedgePow κ (finrank ℂ E)).val x b := by
  have hk := finrank_real_of_complex E
  have hn := hκ.isNondegenerate
  -- The canonical orientation is the volume orientation of `κ` at `x`.
  have ho : (complexManifoldOrientation E X).orientationAt x =
      (hn.volumeOrientation hk).orientationAt x := by
    rw [← SmoothAlmostComplexStructure.orientation_ofComplexManifold, ← hκ.orientation_eq hk,
      IsNondegenerate.orientationAt_orientation, IsNondegenerate.orientationAt_volumeOrientation]
  have hpos := (hn.orientation_eq_orientationAt_volumeOrientation_iff hk b).1 (hb.trans ho)
  rw [wedgePow_eq_factorial_smul_volumeForm, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  positivity

/-- A Hermitian metric, a two-form compatible with the complex structure, has top power `κ^n`
positive on positively oriented tangent bases. -/
theorem Compatible.wedgePow_apply_pos {κ : SmoothTwoForm 𝓘(ℝ, E) X}
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X)) {x : X}
    (b : Basis (Fin (2 * finrank ℂ E)) ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hb : b.orientation = (complexManifoldOrientation E X).orientationAt x) :
    0 < (SmoothForm.wedgePow κ (finrank ℂ E)).val x b :=
  hκ.tames.wedgePow_apply_pos b hb

end SmoothTwoForm

/-- The integral `∫_X g·κ^n` of a function `g` against the top power `κ^n`, `n = finrank ℂ E`, of
a smooth two-form, for the canonical orientation of the complex manifold `X`. -/
def formPowIntegral (κ : SmoothTwoForm 𝓘(ℝ, E) X) (g : X → ℝ) : ℝ :=
  integralTopForm (complexManifoldOrientation E X)
    (fun x ↦ g x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x)

/-- Unfolding lemma for `formPowIntegral`. -/
theorem formPowIntegral_def (κ : SmoothTwoForm 𝓘(ℝ, E) X) (g : X → ℝ) :
    formPowIntegral κ g = integralTopForm (complexManifoldOrientation E X)
      (fun x ↦ g x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x) :=
  (rfl)

/-- The integral of the zero function vanishes: `∫_X 0·κ^n = 0`. -/
@[simp]
theorem formPowIntegral_zero (κ : SmoothTwoForm 𝓘(ℝ, E) X) : formPowIntegral κ 0 = 0 := by
  rw [formPowIntegral_def, ← integralTopForm_zero (complexManifoldOrientation E X)]
  congr 1
  funext x
  rw [Pi.zero_apply, zero_smul, Pi.zero_apply]

/-- Constant factors come out of the integral: `∫_X (c·g)·κ^n = c·∫_X g·κ^n`. -/
theorem formPowIntegral_const_mul (κ : SmoothTwoForm 𝓘(ℝ, E) X) (c : ℝ) (g : X → ℝ) :
    formPowIntegral κ (fun x ↦ c * g x) = c * formPowIntegral κ g :=
  integralTopForm_mul_smul _ c g _

/-- Negation comes out of the integral: `∫_X (-g)·κ^n = -∫_X g·κ^n`. -/
theorem formPowIntegral_neg (κ : SmoothTwoForm 𝓘(ℝ, E) X) (g : X → ℝ) :
    formPowIntegral κ (fun x ↦ -g x) = -formPowIntegral κ g := by
  simpa only [neg_one_mul] using formPowIntegral_const_mul κ (-1) g

/-- **Additivity**: on a compact complex manifold, `∫_X (g + h)·κ^n = ∫_X g·κ^n + ∫_X h·κ^n` for
continuous `g` and `h`. -/
theorem formPowIntegral_add [CompactSpace X] (κ : SmoothTwoForm 𝓘(ℝ, E) X) {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) :
    formPowIntegral κ (fun x ↦ g x + h x) = formPowIntegral κ g + formPowIntegral κ h :=
  integralTopForm_add_smul_of_compactSpace _ (SmoothForm.wedgePow κ (finrank ℂ E)).isSmoothForm
    hg hh

/-- On a compact complex manifold, `∫_X (g - h)·κ^n = ∫_X g·κ^n - ∫_X h·κ^n` for continuous `g`
and `h`. -/
theorem formPowIntegral_sub [CompactSpace X] (κ : SmoothTwoForm 𝓘(ℝ, E) X) {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) :
    formPowIntegral κ (fun x ↦ g x - h x) = formPowIntegral κ g - formPowIntegral κ h := by
  simp only [sub_eq_add_neg]
  rw [formPowIntegral_add κ (h := fun x ↦ -h x) hg hh.neg, formPowIntegral_neg]

namespace SmoothTwoForm

variable [NeZero (finrank ℂ E)] {κ : SmoothTwoForm 𝓘(ℝ, E) X}

/-- **Positivity**: on a complex manifold of positive dimension, if `κ` tames the complex
structure, then `∫_X g·κ^n ≥ 0` for every `g ≥ 0`. -/
theorem Tames.formPowIntegral_nonneg
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g : X → ℝ}
    (hg : ∀ x, 0 ≤ g x) : 0 ≤ formPowIntegral κ g :=
  integralTopForm_smul_nonneg _ (fun _ b hb ↦ (hκ.wedgePow_apply_pos b hb).le) hg

/-- **Monotonicity**: on a compact complex manifold of positive dimension and for `κ` taming the
complex structure, continuous functions with `g ≤ h` satisfy `∫_X g·κ^n ≤ ∫_X h·κ^n`. -/
theorem Tames.formPowIntegral_mono [CompactSpace X]
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    formPowIntegral κ g ≤ formPowIntegral κ h :=
  integralTopForm_smul_mono_of_compactSpace _ (SmoothForm.wedgePow κ (finrank ℂ E)).isSmoothForm
    (fun _ b hb ↦ (hκ.wedgePow_apply_pos b hb).le) hg hh hgh

/-- **Strict positivity**: on a compact complex manifold of positive dimension and for `κ` taming
the complex structure, a continuous `g ≥ 0` that is positive at some point has `∫_X g·κ^n > 0`. -/
theorem Tames.formPowIntegral_pos [CompactSpace X]
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g : X → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {x₀ : X} (hx₀ : 0 < g x₀) :
    0 < formPowIntegral κ g := by
  have : Nonempty (Fin (2 * finrank ℂ E)) :=
    ⟨⟨0, Nat.mul_pos two_pos (Nat.pos_of_ne_zero (NeZero.ne _))⟩⟩
  let b := ((complexManifoldOrientation E X).orientationAt x₀).someBasis
    ((complexManifoldOrientation E X).finrank_tangentSpace_eq x₀).symm
  have hb : b.orientation = (complexManifoldOrientation E X).orientationAt x₀ :=
    Orientation.someBasis_orientation _ _
  refine integralTopForm_pos _
    ((SmoothForm.wedgePow κ (finrank ℂ E)).isSmoothForm.fun_smul_of_continuous hg)
    (isClosed_tsupport _).isCompact
    (fun x c hc ↦ ?_) ⟨x₀, b, hb, ?_⟩
  · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (hg0 x) (hκ.wedgePow_apply_pos c hc).le
  · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos hx₀ (hκ.wedgePow_apply_pos b hb)

/-- **The volume is positive**: on a nonempty compact complex manifold of positive dimension, a
two-form `κ` taming the complex structure, for instance a Hermitian metric, has
`V = ∫_X κ^n > 0`. -/
theorem Tames.formPowIntegral_one_pos [CompactSpace X] [Nonempty X]
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) :
    0 < formPowIntegral κ 1 :=
  hκ.formPowIntegral_pos continuous_const (fun _ ↦ zero_le_one)
    (x₀ := Classical.arbitrary X) one_pos

end SmoothTwoForm

end TauCeti
