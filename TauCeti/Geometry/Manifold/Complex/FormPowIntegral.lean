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
is `TauCeti.formPowIntegral E κ g`. On a compact manifold it is linear in continuous `g`, and for
a taming `κ` it is monotone; so its value `V = ∫_X κ^n` at `g = 1` is positive on a nonempty
compact manifold of positive dimension (`TauCeti.formPowIntegral_one_pos`). The opposite orientation
would make it negative.

## Main definitions

* `TauCeti.formPowIntegral E κ g`: the integral `∫_X g·κ^n` for the canonical orientation.

## Main results

* `TauCeti.SmoothTwoForm.wedgePow_eq_factorial_smul_volumeForm`: `κ^n = n!·(κⁿ/n!)`.
* `TauCeti.SmoothTwoForm.Tames.wedgePow_apply_pos`: a taming `κ` has `κ^n` positive on positively
  oriented tangent bases.
* `TauCeti.formPowIntegral_add`, `TauCeti.formPowIntegral_mul_left`: linearity in `g`.
* `TauCeti.SmoothTwoForm.Tames.formPowIntegral_nonneg`,
  `TauCeti.SmoothTwoForm.Tames.formPowIntegral_mono`: positivity and monotonicity in `g`.
* `TauCeti.SmoothTwoForm.Tames.formPowIntegral_pos`,
  `TauCeti.SmoothTwoForm.Tames.formPowIntegral_one_pos`: on a compact manifold, a continuous
  `g ≥ 0` that is positive somewhere has positive integral; in particular `V > 0`.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

namespace SmoothTwoForm

/-- **The top power is `n!` times the volume form**: `κ^n = n!·(κⁿ/n!)`. -/
theorem wedgePow_eq_factorial_smul_volumeForm {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (κ : SmoothTwoForm I M) (n : ℕ) :
    SmoothForm.wedgePow κ n = (n.factorial : ℝ) • κ.volumeForm n := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [Submodule.coe_smul, Pi.smul_apply, volumeForm_apply, SmoothForm.wedgePow_apply, smul_smul,
    mul_inv_cancel₀ (by positivity), one_smul]

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

variable (E) in
/-- The integral `∫_X g·κ^n` of a function `g` against the top power `κ^n`, `n = finrank ℂ E`, of
a smooth two-form, for the canonical orientation of the complex manifold `X`. -/
def formPowIntegral (κ : SmoothTwoForm 𝓘(ℝ, E) X) (g : X → ℝ) : ℝ :=
  integralTopForm (complexManifoldOrientation E X)
    (fun x ↦ g x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x)

/-- Unfolding lemma for `formPowIntegral`. -/
theorem formPowIntegral_def (κ : SmoothTwoForm 𝓘(ℝ, E) X) (g : X → ℝ) :
    formPowIntegral E κ g = integralTopForm (complexManifoldOrientation E X)
      (fun x ↦ g x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x) :=
  (rfl)

/-- Constant factors come out of the integral: `∫_X (c·g)·κ^n = c·∫_X g·κ^n`. -/
theorem formPowIntegral_mul_left (κ : SmoothTwoForm 𝓘(ℝ, E) X) (c : ℝ) (g : X → ℝ) :
    formPowIntegral E κ (fun x ↦ c * g x) = c * formPowIntegral E κ g := by
  rw [formPowIntegral_def, formPowIntegral_def, ← integralTopForm_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, mul_smul]

omit [FiniteDimensional ℂ E] in
/-- For a continuous function `g`, the top form `g·κ^n` is continuous. -/
theorem isSmoothForm_smul_wedgePow (κ : SmoothTwoForm 𝓘(ℝ, E) X) {g : X → ℝ}
    (hg : Continuous g) :
    IsSmoothForm 𝓘(ℝ, E) 0 (fun x ↦ g x • (SmoothForm.wedgePow κ (finrank ℂ E)).val x) := by
  have : IsManifold 𝓘(ℝ, E) (0 + 1) X := by
    simpa using (inferInstance : IsManifold 𝓘(ℝ, E) 1 X)
  exact ((SmoothForm.wedgePow κ (finrank ℂ E)).isSmoothForm.of_le bot_le).fun_smul
    (contMDiff_zero_iff.2 hg)

/-- **Additivity**: on a compact complex manifold, `∫_X (g + h)·κ^n = ∫_X g·κ^n + ∫_X h·κ^n` for
continuous `g` and `h`. -/
theorem formPowIntegral_add [CompactSpace X] (κ : SmoothTwoForm 𝓘(ℝ, E) X) {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) :
    formPowIntegral E κ (fun x ↦ g x + h x) = formPowIntegral E κ g + formPowIntegral E κ h := by
  rw [formPowIntegral_def, formPowIntegral_def, formPowIntegral_def,
    ← integralTopForm_add_of_compactSpace _ (isSmoothForm_smul_wedgePow κ hg)
      (isSmoothForm_smul_wedgePow κ hh)]
  congr 1
  funext x
  rw [Pi.add_apply, add_smul]

namespace SmoothTwoForm

variable [NeZero (finrank ℂ E)] {κ : SmoothTwoForm 𝓘(ℝ, E) X}

/-- **Positivity**: if `κ` tames the complex structure, then `∫_X g·κ^n ≥ 0` for every `g ≥ 0`. -/
theorem Tames.formPowIntegral_nonneg
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g : X → ℝ}
    (hg : ∀ x, 0 ≤ g x) : 0 ≤ formPowIntegral E κ g :=
  integralTopForm_nonneg _ fun x b hb ↦ by
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (hg x) (hκ.wedgePow_apply_pos b hb).le

/-- **Monotonicity**: on a compact complex manifold and for `κ` taming the complex structure,
continuous functions with `g ≤ h` satisfy `∫_X g·κ^n ≤ ∫_X h·κ^n`. -/
theorem Tames.formPowIntegral_mono [CompactSpace X]
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    formPowIntegral E κ g ≤ formPowIntegral E κ h := by
  have hadd := formPowIntegral_add κ (h := fun x ↦ h x - g x) hg (hh.sub hg)
  simp only [add_sub_cancel] at hadd
  rw [hadd, le_add_iff_nonneg_right]
  exact hκ.formPowIntegral_nonneg fun x ↦ sub_nonneg.2 (hgh x)

/-- **Strict positivity**: on a compact complex manifold and for `κ` taming the complex structure,
a continuous `g ≥ 0` that is positive at some point has `∫_X g·κ^n > 0`. -/
theorem Tames.formPowIntegral_pos [CompactSpace X]
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) {g : X → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {x₀ : X} (hx₀ : 0 < g x₀) :
    0 < formPowIntegral E κ g := by
  have : Nonempty (Fin (2 * finrank ℂ E)) :=
    ⟨⟨0, Nat.mul_pos two_pos (Nat.pos_of_ne_zero (NeZero.ne _))⟩⟩
  let b := ((complexManifoldOrientation E X).orientationAt x₀).someBasis
    ((complexManifoldOrientation E X).finrank_tangentSpace_eq x₀).symm
  have hb : b.orientation = (complexManifoldOrientation E X).orientationAt x₀ :=
    Orientation.someBasis_orientation _ _
  refine integralTopForm_pos _ (isSmoothForm_smul_wedgePow κ hg) (isClosed_tsupport _).isCompact
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
    0 < formPowIntegral E κ 1 :=
  hκ.formPowIntegral_pos continuous_const (fun _ ↦ zero_le_one)
    (x₀ := Classical.arbitrary X) one_pos

end SmoothTwoForm

end TauCeti
