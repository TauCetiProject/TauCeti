/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Stabilizer
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Fredholm.Parametric
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.Analysis.Fredholm.StabilizedPerturbation

/-!
# The kernel and the index of glued operators on the cylinder

Let `D₁` and `D₂` be first-order operators `D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the cylinder `ℝ × S¹`,
from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, W)`, with essentially bounded coefficient fields `M₁`
and `M₂` whose ends match: `M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞`.
Gluing them along a neck of length `2 R` gives the operator `D_R` of the coefficient field
`M_R = gluedCoeff M₁ M₂ R`, equal to `M₁(· + R, ·)` on `s < 0` and to `M₂(· - R, ·)` on `s ≥ 0`.
This file proves that the index is additive under this gluing: if `D₁` and `D₂` are Fredholm,
then so is `D_R` for every sufficiently long neck, and

`ind D_R = ind D₁ + ind D₂`

(`TauCeti.CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq`).
For linearized Floer operators along trajectories this is the additivity of the index under the
catenation of trajectories at a common nondegenerate orbit.

**Stabilized kernels.** The pieces need not be onto. Let `ιᵢ : Sᵢ → L²` be stabilizers whose
sections vanish near the glued ends and such that the stabilized operators
`Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` have bounded right inverses `Qᵢ`, and let `A_R` be the stabilized glued
operator `(ξ, σ₁, σ₂) ↦ D_R ξ + j_R (σ₁, σ₂)`, with the translated stabilizers
`j_R = gluedStabilizer ι₁ ι₂ R`. For long necks `A_R` has right inverses `Q` of norm at most
`4 (‖Q₁‖ + ‖Q₂‖)`
(`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`).
The main theorem
(`exists_forall_ge_finiteDimensional_and_finrank_ker_coprod_jetOperator_gluedCoeff_eq`) compares
the kernels: when the kernels `Eᵢ` of `Aᵢ` are finite-dimensional, then for long necks the kernel
`E_R` of `A_R` is finite-dimensional, of dimension `dim E₁ + dim E₂`. The index additivity
follows, since a surjective stabilization by `S` has index `ind D + dim S` and kernel `E`, so that
`ind D = dim E - dim S` (`ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective`).
Stabilizers made of test sections exist for every Fredholm piece
(`ContinuousLinearMap.IsFredholm.exists_le_testSectionLp_isTopCompl`).

The two inequalities between `dim E_R` and `dim E₁ + dim E₂` come from two injective linear maps.
Write `β = neckCutoff (-(2 / R))` for the cutoff equal to `1` on `s ≤ 0` and to `0` on `s ≥ R / 2`.

* **Cutting.** An element `(ξ, σ₁, σ₂)` of `E_R` is cut into the pieces `((β ξ)(· - R, ·), σ₁)`
  and `(((1 - β) ξ)(· + R, ·), σ₂)`, translated back to the pieces. They nearly lie in the kernels
  of `A₁` and `A₂` (`TauCeti.CylinderSobolev.norm_coprod_translate_cutoffL_le`): on the support of
  `β` the glued field is close to the translate of `M₁`, the derivative of `β` is `O(1 / R)`, and
  the stabilizers are supported where `β` is `1` or `0`. Projecting the pieces to `Eᵢ` along the
  ranges of the `Qᵢ` is injective on `E_R`, since the pieces add up to `(ξ, σ₁, σ₂)`.
* **Pregluing.** Two elements `(ξᵢ, σᵢ)` of `E₁` and `E₂` are preglued to
  `(β ξ₁(· + R, ·) + (1 - β) ξ₂(· - R, ·), σ₁, σ₂)`, which nearly lies in `E_R`
  (`TauCeti.CylinderSobolev.norm_jetOperator_cutoffL_translate_add_le`), and corrected into `E_R`
  along the range of `Q`.
  This is injective, because the pregluing is `ξ₁(· + R, ·)` on `s < 0` and `ξ₂(· - R, ·)` on
  `s > R / 2`, so it controls `ξ₁` and `ξ₂` up to their tails beyond the neck. These tails are
  uniformly small on the finite-dimensional spaces `Eᵢ` for long necks
  (`TauCeti.CylinderSobolev.eventually_forall_norm_multiplicationOperator_le`).

## Main results

* `exists_forall_ge_finiteDimensional_and_finrank_ker_coprod_jetOperator_gluedCoeff_eq`: the
  kernel of the stabilized glued operator has dimension `dim E₁ + dim E₂` for long necks.
* `TauCeti.CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq`: the
  glued operator of two Fredholm operators is Fredholm for long necks, with
  `ind D_R = ind D₁ + ind D₂`.
* `exists_pos_exists_forall_ge_isFredholm_and_index_eq_of_norm_sub_jetOperator_gluedCoeff_le`: so
  is every operator within a fixed distance `ε` of `D_R`, with `ε` independent of `R`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  (stabilizing a Fredholm operator) and Chapter 10 (linear gluing, and the kernel of the glued
  operator through pregluing and cutting).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3 (the Fredholm index of the linearized Floer operator and
  its behaviour under gluing).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology Module
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- **Cutting one piece off.** Let `ξ ∈ W^{1,2}` and `σ ∈ S`, let `N` be a coefficient field and `β`
a cutoff, and suppose that `-(ι σ)(· + a, ·)` is `β D_N ξ`. If `M(· + a, ·)` is within `ε` of `N`
wherever `β ≠ 0`, with `‖M‖ ≤ B` and `|β'| ≤ d`, then the cut piece `β ξ`, translated by `-a`, with
`σ` nearly lies in the kernel of the stabilized operator `(ξ, σ) ↦ D_M ξ + ι σ`: its image has norm
at most `(ε + d B) ‖ξ‖`. -/
theorem norm_coprod_translate_cutoffL_le {M N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure)
    {ι : S →L[ℝ] Lp W 2 stripMeasure} (a : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖M (z + (a, 0))‖ ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hMN : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖M (z + (a, 0)) - N z‖ ≤ ε) {ξ : H1 V} {σ : S}
    (hζ : ∀ᵐ z ∂stripMeasure, (-translateLp a (ι σ)) z =
      β z.1 • jetOperator 2 stripMeasure N (ξ : Lp (V × V × V) 2 stripMeasure) z) :
    ‖(((jetOperator 2 stripMeasure M).comp (H1 V).subtypeL).coprod ι)
        (translate 2 (testSection V) (-a) (cutoffL hβ hβ1 hβ'1 ξ), σ)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  have hG := hM.comp_measurePreserving (measurePreserving_add_strip a)
  rw [← (translateLp (E := W) (p := 2) a).norm_map]
  have key : translateLp a ((((jetOperator 2 stripMeasure M).comp (H1 V).subtypeL).coprod ι)
      (translate 2 (testSection V) (-a) (cutoffL hβ hβ1 hβ'1 ξ), σ)) =
      jetOperator 2 stripMeasure (fun z ↦ M (z + (a, 0)))
        (cutoffL hβ hβ1 hβ'1 ξ : Lp (V × V × V) 2 stripMeasure) - -translateLp a (ι σ) := by
    simp [translateLp_jetOperator hM, translateLp_translateLp]
  rw [key]
  exact norm_jetOperator_cutoffL_sub_le hG hN hβ hβ1 hβ'1 hB hd hε hMN hζ

/-- **Pregluing one piece.** Let `(ξ, σ)` lie in the kernel of the stabilized operator
`(ξ, σ) ↦ D_M ξ + ι σ`, and let `β` be a cutoff equal to `1` wherever the translated stabilizer
`(ι σ)(· + a, ·)` does not vanish. If `N` is within `ε` of `M(· + a, ·)` wherever `β ≠ 0`, with
`‖N‖ ≤ B` and `|β'| ≤ d`, then `D_N` of the translated cut-off piece `β ξ(· + a, ·)` plus
`(ι σ)(· + a, ·)` has norm at most `(ε + d B) ‖ξ‖`. -/
theorem norm_jetOperator_cutoffL_translate_add_le {M N : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) (hN : MemLp N ∞ stripMeasure)
    {ι : S →L[ℝ] Lp W 2 stripMeasure} (a : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) {B d ε : ℝ}
    (hB : ∀ᵐ z ∂stripMeasure, ‖N z‖ ≤ B) (hd : ∀ s, |deriv β s| ≤ d) (hε : 0 ≤ ε)
    (hNM : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖N z - M (z + (a, 0))‖ ≤ ε) {ξ : H1 V} {σ : S}
    (hξ : (((jetOperator 2 stripMeasure M).comp (H1 V).subtypeL).coprod ι) (ξ, σ) = 0)
    (hβι : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 1 → translateLp a (ι σ) z = 0) :
    ‖jetOperator 2 stripMeasure N
        (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) a ξ) : Lp (V × V × V) 2 stripMeasure) +
      translateLp a (ι σ)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  have hG := hM.comp_measurePreserving (measurePreserving_add_strip a)
  -- `D_{M(· + a)}` of the translate of `ξ` is the translate of `D_M ξ = -ι σ`.
  have hD : jetOperator 2 stripMeasure (fun z ↦ M (z + (a, 0)))
      (translate 2 (testSection V) a ξ : Lp (V × V × V) 2 stripMeasure) = -translateLp a (ι σ) := by
    have h : jetOperator 2 stripMeasure M (ξ : Lp (V × V × V) 2 stripMeasure) = -ι σ :=
      eq_neg_of_add_eq_zero_left (by simpa using hξ)
    rw [coe_translate, ← translateLp_jetOperator hM, h, map_neg]
  have hζ : ∀ᵐ z ∂stripMeasure, (-translateLp a (ι σ)) z = β z.1 • jetOperator 2 stripMeasure
      (fun z ↦ M (z + (a, 0))) (translate 2 (testSection V) a ξ : Lp (V × V × V) 2 stripMeasure)
        z := by
    rw [hD]
    filter_upwards [Lp.coeFn_neg (translateLp a (ι σ)), hβι] with z h₁ h₂
    by_cases hz : β z.1 = 1
    · rw [hz, one_smul]
    · rw [h₁, Pi.neg_apply, h₂ hz, neg_zero, smul_zero]
  have h := norm_jetOperator_cutoffL_sub_le hN hG hβ hβ1 hβ'1 hB hd hε hNM hζ
  rwa [sub_neg_eq_add, LinearIsometryEquiv.norm_map] at h


variable {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
  [NormedAddCommGroup S₂] [NormedSpace ℝ S₂]

/-- The two pieces cut off an element `(ξ, σ₁, σ₂)` of the kernel of the stabilized glued
operator, translated back to the pieces, nearly lie in the kernels of the stabilized pieces. -/
private theorem norm_coprod_cut_le {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B) (hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B)
    (hβd : ∀ s, |deriv β s| ≤ d) (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {ξ : H1 V} {σ : S₁ × S₂}
    (hx : (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) (ξ, σ) = 0) :
    ‖(((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
        (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 ξ), σ.1)‖ ≤ (ε + d * B) * ‖ξ‖ ∧
      ‖(((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
        (translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 ξ), σ.2)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  set G := Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R)
  have hG := (memLp_uncurry_gluedCoeff hM₁ hM₂ R).1
  -- `D_G ξ = -j_R σ`.
  have hD : jetOperator 2 stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) =
      -(translateLp R (ι₁ σ.1) + translateLp (-R) (ι₂ σ.2)) :=
    eq_neg_of_add_eq_zero_left (by simpa using hx)
  have hv₁ := ae_translateLp_eq_zero_of_sub_lt hι₁ R σ.1
  have hv₂ := ae_translateLp_eq_zero_of_lt_neg_sub hι₂ (-R) σ.2
  have hζ₁ : ∀ᵐ z ∂stripMeasure, (-translateLp R (ι₁ σ.1)) z =
      β z.1 • jetOperator 2 stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) z := by
    rw [hD]
    filter_upwards [Lp.coeFn_neg (translateLp R (ι₁ σ.1)),
      Lp.coeFn_neg (translateLp R (ι₁ σ.1) + translateLp (-R) (ι₂ σ.2)),
      Lp.coeFn_add (translateLp R (ι₁ σ.1)) (translateLp (-R) (ι₂ σ.2)), hv₁, hv₂]
      with z h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.neg_apply, Pi.neg_apply, h₃, Pi.add_apply]
    rcases le_or_gt z.1 (T - R) with hz | hz
    · rw [hβ0 _ (by linarith), one_smul, h₅ (by linarith), add_zero]
    rw [h₄ hz, neg_zero, zero_add]
    rcases lt_or_ge z.1 (-T - -R) with hz' | hz'
    · rw [h₅ hz', neg_zero, smul_zero]
    · rw [hβR _ (by linarith), zero_smul]
  have hζ₂ : ∀ᵐ z ∂stripMeasure, (-translateLp (-R) (ι₂ σ.2)) z =
      (1 - β z.1) • jetOperator 2 stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) z := by
    rw [hD]
    filter_upwards [Lp.coeFn_neg (translateLp (-R) (ι₂ σ.2)),
      Lp.coeFn_neg (translateLp R (ι₁ σ.1) + translateLp (-R) (ι₂ σ.2)),
      Lp.coeFn_add (translateLp R (ι₁ σ.1)) (translateLp (-R) (ι₂ σ.2)), hv₁, hv₂]
      with z h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.neg_apply, Pi.neg_apply, h₃, Pi.add_apply]
    rcases le_or_gt (-T - -R) z.1 with hz | hz
    · rw [hβR _ (by linarith), sub_zero, one_smul, h₄ (by linarith), zero_add]
    rw [h₅ hz, neg_zero, add_zero]
    rcases lt_or_ge (T - R) z.1 with hz' | hz'
    · rw [h₄ hz', neg_zero, smul_zero]
    · rw [hβ0 _ (by linarith), sub_self, zero_smul]
  refine ⟨norm_coprod_translate_cutoffL_le hM₁ hG R hβ hβ1 hβ'1
    ((measurePreserving_add_strip R).quasiMeasurePreserving.ae hB₁) hβd hε
    (hn₁.mono fun z h hz ↦ (norm_sub_rev _ _).trans_le (h hz)) hζ₁, ?_⟩
  have h := norm_coprod_translate_cutoffL_le hM₂ hG (-R) hγ hγ1 hγ'1
    ((measurePreserving_add_strip (-R)).quasiMeasurePreserving.ae hB₂) hγd hε
    (hn₂.mono fun z h hz ↦ (norm_sub_rev _ _).trans_le (h hz)) hζ₂
  rwa [neg_neg] at h

/-- Pregluing two elements of the kernels of the stabilized pieces gives an element nearly in the
kernel of the stabilized glued operator. -/
private theorem norm_coprod_preglue_le {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB : ∀ᵐ z ∂stripMeasure,
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤ B)
    (hβd : ∀ s, |deriv β s| ≤ d) (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {ξ₁ ξ₂ : H1 V} {σ₁ : S₁} {σ₂ : S₂}
    (hk₁ : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁) (ξ₁, σ₁) = 0)
    (hk₂ : (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂) (ξ₂, σ₂) = 0) :
    ‖(((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))
        (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R ξ₁) +
          cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) ξ₂), (σ₁, σ₂))‖ ≤
      (ε + d * B) * (‖ξ₁‖ + ‖ξ₂‖) := by
  set G := Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R)
  have hG := (memLp_uncurry_gluedCoeff hM₁ hM₂ R).1
  have hv₁ := ae_translateLp_eq_zero_of_sub_lt hι₁ R σ₁
  have hv₂ := ae_translateLp_eq_zero_of_lt_neg_sub hι₂ (-R) σ₂
  have e₁ := norm_jetOperator_cutoffL_translate_add_le hM₁ hG R hβ hβ1 hβ'1 hB hβd hε hn₁ hk₁
    (hv₁.mono fun z h hz ↦ h (by
      by_contra hz'
      exact hz (hβ0 _ (by linarith))))
  have e₂ := norm_jetOperator_cutoffL_translate_add_le hM₂ hG (-R) hγ hγ1 hγ'1 hB hγd hε hn₂ hk₂
    (hv₂.mono fun z h hz ↦ h (by
      by_contra hz'
      exact hz (by simp only [hβR z.1 (by linarith), sub_zero])))
  calc _ = ‖(jetOperator 2 stripMeasure G
          (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R ξ₁) : Lp (V × V × V) 2 stripMeasure) +
          translateLp R (ι₁ σ₁)) + (jetOperator 2 stripMeasure G
          (cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) ξ₂) :
            Lp (V × V × V) 2 stripMeasure) + translateLp (-R) (ι₂ σ₂))‖ := by
        simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
          Submodule.subtypeL_apply, map_add, gluedStabilizer_apply]
        abel_nf
    _ ≤ (ε + d * B) * ‖ξ₁‖ + (ε + d * B) * ‖ξ₂‖ := (norm_add_le _ _).trans (add_le_add e₁ e₂)
    _ = _ := by ring

/-- The pregluing `β f₁ + γ f₂` of two sections with complementary cutoffs, `β = 1` and `γ = 0` on
`s < 0` and `β = 0` and `γ = 1` on `s > R / 2`, is `f₁` on `s < 0` and `f₂` on `s > R / 2`; so it
controls `f₁` and `f₂` up to their parts on `s ≥ 0` and `s ≤ R / 2`. -/
private theorem norm_le_norm_cutoffL_add_cutoffL {R : ℝ} {β γ : ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) (hγ : ContDiff ℝ 2 γ)
    (hγ1 : ∀ s, |γ s| ≤ 1) (hγ'1 : ∀ s, |deriv γ s| ≤ 1)
    (hβ₀ : ∀ s < 0, β =ᶠ[𝓝 s] fun _ ↦ 1) (hγ₀ : ∀ s < 0, γ =ᶠ[𝓝 s] fun _ ↦ 0)
    (hβR : ∀ s, R / 2 < s → β =ᶠ[𝓝 s] fun _ ↦ 0) (hγR : ∀ s, R / 2 < s → γ =ᶠ[𝓝 s] fun _ ↦ 1)
    (f₁ f₂ : H1 V) :
    ‖f₁‖ ≤ ‖cutoffL hβ hβ1 hβ'1 f₁ + cutoffL hγ hγ1 hγ'1 f₂‖ +
        ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 < 0}ᶜ
          (measurableSet_lt measurable_fst measurable_const).compl)
          (f₁ : Lp (V × V × V) 2 stripMeasure)‖ ∧
      ‖f₂‖ ≤ ‖cutoffL hβ hβ1 hβ'1 f₁ + cutoffL hγ hγ1 hγ'1 f₂‖ +
        ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R / 2 < z.1}ᶜ
          (measurableSet_lt measurable_const measurable_fst).compl)
          (f₂ : Lp (V × V × V) 2 stripMeasure)‖ := by
  set g := cutoffL hβ hβ1 hβ'1 f₁ + cutoffL hγ hγ1 hγ'1 f₂
  have key {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (f : H1 V)
      (hg : Lp.multiplicationOperator (linftyIndicator stripMeasure A hA)
        (g : Lp (V × V × V) 2 stripMeasure) =
        Lp.multiplicationOperator (linftyIndicator stripMeasure A hA)
          (f : Lp (V × V × V) 2 stripMeasure)) :
      ‖f‖ ≤ ‖g‖ + ‖Lp.multiplicationOperator (linftyIndicator stripMeasure Aᶜ hA.compl)
        (f : Lp (V × V × V) 2 stripMeasure)‖ := by
    set m := Lp.multiplicationOperator (linftyIndicator stripMeasure Aᶜ hA.compl)
      (f : Lp (V × V × V) 2 stripMeasure)
    calc ‖f‖ = ‖Lp.multiplicationOperator (linftyIndicator stripMeasure A hA)
          (g : Lp (V × V × V) 2 stripMeasure) + m‖ := by
          rw [hg, Lp.multiplicationOperator_linftyIndicator_add_compl, Submodule.norm_coe]
      _ ≤ ‖g‖ + ‖m‖ := (norm_add_le _ _).trans (add_le_add_left
          ((Lp.norm_multiplicationOperator_linftyIndicator_apply_le hA _).trans_eq
            (Submodule.norm_coe g)) _)
  refine ⟨key (measurableSet_lt measurable_fst measurable_const) f₁ ?_,
    key (measurableSet_lt measurable_const measurable_fst) f₂ ?_⟩
  · rw [Submodule.coe_add, map_add, multiplicationOperator_linftyIndicator_cutoffL hβ hβ1 hβ'1 _
      (fun z hz ↦ hβ₀ z.1 hz), multiplicationOperator_linftyIndicator_cutoffL hγ hγ1 hγ'1 _
      (fun z hz ↦ hγ₀ z.1 hz), one_smul, zero_smul, add_zero]
  · rw [Submodule.coe_add, map_add, multiplicationOperator_linftyIndicator_cutoffL hβ hβ1 hβ'1 _
      (fun z hz ↦ hβR z.1 hz), multiplicationOperator_linftyIndicator_cutoffL hγ hγ1 hγ'1 _
      (fun z hz ↦ hγR z.1 hz), one_smul, zero_smul, zero_add]

/-- The kernel of an operator on `W^{1,2} × S` is a free module. (The instance is found through
its image in `L² × S`, where instance search identifies the additive structures directly.) -/
private theorem free_ker {S Y : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : H1 V × S →L[ℝ] Y) : Module.Free ℝ A.ker :=
  Module.Free.of_equiv (Submodule.equivMapOfInjective
    (((H1 V).subtype.prodMap LinearMap.id : H1 V × S →ₗ[ℝ] _ × S))
    ((H1 V).injective_subtype.prodMap Function.injective_id) A.ker).symm

/-- If `x ≤ c x` with `c < 1`, then `x ≤ 0`. -/
private theorem nonpos_of_le_mul_of_lt_one {x c : ℝ} (h : x ≤ c * x) (hc : c < 1) : x ≤ 0 := by
  nlinarith

/-- A bound `‖x‖ ≤ ‖a‖ + ‖b‖` on the first components bounds `(x, s₁, s₂)` by `(a, s₁)` and
`(b, s₂)`. -/
private theorem norm_mk_mk_le {X Y₁ Y₂ : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y₁] [SeminormedAddCommGroup Y₂] {x a b : X} (s₁ : Y₁) (s₂ : Y₂)
    (h : ‖x‖ ≤ ‖a‖ + ‖b‖) : ‖(x, (s₁, s₂))‖ ≤ ‖(a, s₁)‖ + ‖(b, s₂)‖ :=
  norm_prod_le_iff.2 ⟨h.trans (add_le_add (norm_fst_le (a, s₁)) (norm_fst_le (b, s₂))),
    norm_prod_le_iff.2 ⟨(norm_snd_le (a, s₁)).trans (le_add_of_nonneg_right (norm_nonneg _)),
      (norm_snd_le (b, s₂)).trans (le_add_of_nonneg_left (norm_nonneg _))⟩⟩

/-- An element of the kernel of the stabilized glued operator whose two cut pieces are fixed by the
projections `id - Qᵢ Aᵢ` vanishes, once the pieces' errors are small compared with
`‖Q₁‖ + ‖Q₂‖`: each piece is then bounded by `‖Qᵢ‖` times its small error, and the pieces add up
to the element. -/
private theorem eq_zero_of_cut {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB0 : 0 ≤ B) (hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B)
    (hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B) (hβd : ∀ s, |deriv β s| ≤ d)
    (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hsmall : (‖Q₁‖ + ‖Q₂‖) * (ε + d * B) < 1) {v : H1 V × (S₁ × S₂)}
    (hv : (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) v = 0)
    (h₁ : ((translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1) : H1 V × S₁) =
      Q₁ ((((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
        (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1)))
    (h₂ : ((translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1), v.2.2) : H1 V × S₂) =
      Q₂ ((((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
        (translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1), v.2.2))) :
    v = 0 := by
  obtain ⟨e₁, e₂⟩ := norm_coprod_cut_le hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1 hγ hγ1 hγ'1
    hβ0 hβR hB₁ hB₂ hβd hγd hε hn₁ hn₂ (ξ := v.1) (σ := v.2) (by simpa using hv)
  have hδ : 0 ≤ ε + d * B := add_nonneg hε (mul_nonneg ((abs_nonneg _).trans (hβd 0)) hB0)
  -- The cutoffs add up to `1` and the translations are isometries, so `v` is bounded by the pieces.
  have hξ : ‖v.1‖ ≤ ‖translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1)‖ +
      ‖translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1)‖ := by
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    conv_lhs => rw [← cutoffL_add_cutoffL hβ hβ1 hβ'1 hγ hγ1 hγ'1 (funext fun s ↦ by simp) v.1]
    exact norm_add_le _ _
  set p₁ : H1 V × S₁ := (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1)
  set p₂ : H1 V × S₂ := (translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1), v.2.2)
  have key : ‖v‖ ≤ (‖Q₁‖ + ‖Q₂‖) * (ε + d * B) * ‖v‖ :=
    calc ‖v‖ ≤ ‖p₁‖ + ‖p₂‖ := norm_mk_mk_le v.2.1 v.2.2 hξ
      _ ≤ ‖Q₁‖ * ((ε + d * B) * ‖v.1‖) + ‖Q₂‖ * ((ε + d * B) * ‖v.1‖) :=
        add_le_add (((congrArg norm h₁).trans_le (Q₁.le_opNorm _)).trans
          (mul_le_mul_of_nonneg_left e₁ (norm_nonneg _)))
          (((congrArg norm h₂).trans_le (Q₂.le_opNorm _)).trans
            (mul_le_mul_of_nonneg_left e₂ (norm_nonneg _)))
      _ = (‖Q₁‖ + ‖Q₂‖) * (ε + d * B) * ‖v.1‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_fst_le v) (by positivity)
  exact norm_le_zero_iff.1 (nonpos_of_le_mul_of_lt_one key hsmall)

/-- **The kernel of the glued operator is at most as large as those of the pieces.** Cutting an
element of the kernel of `D_R ⊕ j_R` along the neck and projecting the two pieces to the kernels of
`Dᵢ ⊕ ιᵢ` along the ranges of the right inverses `Qᵢ` is injective once the pieces' errors are
small compared with `‖Q₁‖ + ‖Q₂‖`. -/
private theorem finiteDimensional_and_finrank_ker_le {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB0 : 0 ≤ B) (hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B)
    (hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B) (hβd : ∀ s, |deriv β s| ≤ d)
    (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (hsmall : (‖Q₁‖ + ‖Q₂‖) * (ε + d * B) < 1) :
    FiniteDimensional ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ∧
    finrank ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ≤
      finrank ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
        finrank ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker := by
  have hzero (v) := eq_zero_of_cut hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1 hγ hγ1 hγ'1 hβ0 hβR hB0
    hB₁ hB₂ hβd hγd hε hn₁ hn₂ hsmall (v := v)
  set A₁ := ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁
  set A₂ := ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂
  set A := ((jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)
  -- The cut pieces, translated back to the pieces.
  set c₁ : H1 V × (S₁ × S₂) →L[ℝ] H1 V × S₁ :=
    ((translate 2 (testSection V) (-R)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((cutoffL hβ hβ1 hβ'1).comp (ContinuousLinearMap.fst ℝ _ _))).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) with hc₁def
  set c₂ : H1 V × (S₁ × S₂) →L[ℝ] H1 V × S₂ :=
    ((translate 2 (testSection V) R).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((cutoffL hγ hγ1 hγ'1).comp (ContinuousLinearMap.fst ℝ _ _))).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) with hc₂def
  have hc₁ (v : H1 V × (S₁ × S₂)) :
      c₁ v = (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1) := by
    simp [hc₁def]
  have hc₂ (v : H1 V × (S₁ × S₂)) :
      c₂ v = (translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1), v.2.2) := by
    simp [hc₂def]
  have hr₁ := ContinuousLinearMap.rightInverse_of_comp hQ₁
  have hr₂ := ContinuousLinearMap.rightInverse_of_comp hQ₂
  clear_value A₁ A₂ A c₁ c₂
  -- The cut pieces projected to the kernels of the pieces along the ranges of `Q₁` and `Q₂`.
  let Φ : A.ker →ₗ[ℝ] A₁.ker × A₂.ker :=
    (((A₁.projKerOfRightInverse Q₁ hr₁).comp c₁ : _ →ₗ[ℝ] _) ∘ₗ A.ker.subtype).prod
      (((A₂.projKerOfRightInverse Q₂ hr₂).comp c₂ : _ →ₗ[ℝ] _) ∘ₗ A.ker.subtype)
  have hinj : Function.Injective Φ := by
    intro x y hxy
    rw [← sub_eq_zero]
    have h : Φ (x - y) = 0 := (map_sub Φ x y).trans (by rw [hxy]; exact sub_self (Φ y))
    generalize x - y = w at h ⊢
    obtain ⟨v, hv⟩ := w
    have h₁ : c₁ v - Q₁ (A₁ (c₁ v)) = 0 := congrArg (fun y ↦ ((y.1 : A₁.ker) : H1 V × S₁)) h
    have h₂ : c₂ v - Q₂ (A₂ (c₂ v)) = 0 := congrArg (fun y ↦ ((y.2 : A₂.ker) : H1 V × S₂)) h
    rw [sub_eq_zero, hc₁] at h₁
    rw [sub_eq_zero, hc₂] at h₂
    exact Subtype.ext (hzero v hv h₁ h₂)
  have := free_ker A₁
  have := free_ker A₂
  have := isNoetherian_of_isNoetherianRing_of_finite ℝ (A₁.ker × A₂.ker)
  exact ⟨Module.Finite.of_injective Φ hinj,
    (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq Module.finrank_prod⟩

/-- The pregluing `β f₁(· + R, ·) + (1 - β) f₂(· - R, ·)` controls `f₁` up to its part on
`s ≥ R` and `f₂` up to its part on `s ≤ -R / 2`, the parts that the cutoffs move beyond the neck. -/
private theorem norm_le_norm_preglue_add {R : ℝ} {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1) (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s)
    (hγ1 : ∀ s, |1 - β s| ≤ 1) (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0) (f₁ f₂ : H1 V) :
    ‖f₁‖ ≤ ‖cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R f₁) +
        cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) f₂)‖ +
        ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
          (measurableSet_le measurable_const measurable_fst))
          (f₁ : Lp (V × V × V) 2 stripMeasure)‖ ∧
      ‖f₂‖ ≤ ‖cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R f₁) +
        cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) f₂)‖ +
        ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
          (measurableSet_le measurable_fst measurable_const))
          (f₂ : Lp (V × V × V) 2 stripMeasure)‖ := by
  have hβ₀ (s : ℝ) (hs : s < 0) : β =ᶠ[𝓝 s] fun _ ↦ 1 :=
    (eventually_lt_nhds hs).mono fun t ht ↦ hβ0 t ht.le
  have hβR' (s : ℝ) (hs : R / 2 < s) : β =ᶠ[𝓝 s] fun _ ↦ 0 :=
    (eventually_gt_nhds hs).mono fun t ht ↦ hβR t ht.le
  obtain ⟨l₁, l₂⟩ := norm_le_norm_cutoffL_add_cutoffL (V := V) hβ hβ1 hβ'1 hγ hγ1 hγ'1 hβ₀
    (fun s hs ↦ (hβ₀ s hs).mono fun t ht ↦ by simp [ht]) hβR'
    (fun s hs ↦ (hβR' s hs).mono fun t ht ↦ by simp [ht]) (translate 2 (testSection V) R f₁)
    (translate 2 (testSection V) (-R) f₂)
  -- The parts of the translates beyond the neck are the tails of the original sections.
  rw [LinearIsometryEquiv.norm_map, coe_translate,
    ← translateLp_multiplicationOperator_linftyIndicator (A := {z : ℝ × ℝ | R ≤ z.1})
      (measurableSet_le measurable_const measurable_fst) _ R (fun z ↦ by simp),
    LinearIsometryEquiv.norm_map] at l₁
  rw [LinearIsometryEquiv.norm_map, coe_translate,
    ← translateLp_multiplicationOperator_linftyIndicator (A := {z : ℝ × ℝ | z.1 ≤ -(R / 2)})
      (measurableSet_le measurable_fst measurable_const) _ (-R) (fun z ↦ by
        simp only [mem_compl_iff, mem_ofPred_eq, Prod.fst_add, not_lt]
        constructor <;> intro h <;> linarith), LinearIsometryEquiv.norm_map] at l₂
  exact ⟨l₁, l₂⟩

/-- Two elements of the kernels of the stabilized pieces whose pregluing is fixed by the
projection `id - Q A` onto the kernel of the stabilized glued operator vanish, once the pregluing
error is small compared with `‖Q‖` and their tails beyond the neck are small: the pregluing is
then bounded by `‖Q‖` times its small error, and it controls both elements up to their tails. -/
private theorem eq_zero_of_preglue {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂stripMeasure,
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤ B)
    (hβd : ∀ s, |deriv β s| ≤ d) (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    {θ : ℝ} (hθ : 0 ≤ θ)
    (ht₁ : ∀ k ∈ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (ht₂ : ∀ k ∈ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (hsmall : 2 * ‖Q‖ * (ε + d * B) + θ < 1) {k₁ : H1 V × S₁} {k₂ : H1 V × S₂}
    (hk₁ : k₁ ∈ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker)
    (hk₂ : k₂ ∈ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker)
    (h : ((cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
        cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1), (k₁.2, k₂.2)) :
          H1 V × (S₁ × S₂)) = Q ((((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))
          (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
            cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1), (k₁.2, k₂.2)))) :
    k₁ = 0 ∧ k₂ = 0 := by
  set g := cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
    cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1)
  have eA := norm_coprod_preglue_le hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1 hγ hγ1 hγ'1
    hβ0 hβR hB hβd hγd hε hn₁ hn₂ (ξ₁ := k₁.1) (σ₁ := k₁.2) (ξ₂ := k₂.1)
    (σ₂ := k₂.2) (by simpa using hk₁) (by simpa using hk₂)
  have eP := ((congrArg norm h).trans_le (Q.le_opNorm _)).trans
    (mul_le_mul_of_nonneg_left eA (norm_nonneg Q))
  obtain ⟨l₁, l₂⟩ := norm_le_norm_preglue_add hβ hβ1 hβ'1 hγ hγ1 hγ'1 hβ0 hβR k₁.1 k₂.1
  -- With `N = ‖(k₁, k₂)‖`, both elements are at most `(2 ‖Q‖ δ + θ) N`, so `N = 0`.
  set N := ‖((k₁, k₂) : (H1 V × S₁) × (H1 V × S₂))‖
  have hδ : 0 ≤ ε + d * B := add_nonneg hε (mul_nonneg ((abs_nonneg _).trans (hβd 0)) hB0)
  have hg := norm_fst_le ((g, (k₁.2, k₂.2)) : H1 V × (S₁ × S₂))
  have hs₁ := (norm_fst_le (k₁.2, k₂.2)).trans (norm_snd_le ((g, (k₁.2, k₂.2)) :
    H1 V × (S₁ × S₂)))
  have hs₂ := (norm_snd_le (k₁.2, k₂.2)).trans (norm_snd_le ((g, (k₁.2, k₂.2)) :
    H1 V × (S₁ × S₂)))
  have hN₁ : ‖k₁‖ ≤ N := norm_fst_le (k₁, k₂)
  have hN₂ : ‖k₂‖ ≤ N := norm_snd_le (k₁, k₂)
  have hpreN : ‖((g, (k₁.2, k₂.2)) : H1 V × (S₁ × S₂))‖ ≤ 2 * ‖Q‖ * (ε + d * B) * N :=
    calc _ ≤ ‖Q‖ * ((ε + d * B) * (2 * N)) := eP.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith [norm_fst_le k₁, norm_fst_le k₂]) hδ)
          (norm_nonneg _))
      _ = _ := by ring
  have hθ₁ : θ * ‖k₁‖ ≤ θ * N := mul_le_mul_of_nonneg_left hN₁ hθ
  have hθ₂ : θ * ‖k₂‖ ≤ θ * N := mul_le_mul_of_nonneg_left hN₂ hθ
  have hθN : 0 ≤ θ * N := mul_nonneg hθ (norm_nonneg _)
  have key : N ≤ (2 * ‖Q‖ * (ε + d * B) + θ) * N := norm_prod_le_iff.2
    ⟨norm_prod_le_iff.2 ⟨by linarith [ht₁ k₁ hk₁], by linarith⟩,
      norm_prod_le_iff.2 ⟨by linarith [ht₂ k₂ hk₂], by linarith⟩⟩
  have hN0 := nonpos_of_le_mul_of_lt_one key hsmall
  exact ⟨norm_le_zero_iff.1 (hN₁.trans hN0), norm_le_zero_iff.1 (hN₂.trans hN0)⟩

/-- **The kernel of the glued operator is at least as large as those of the pieces.** Pregluing
elements of the kernels of `Dᵢ ⊕ ιᵢ` and correcting the result into the kernel of `D_R ⊕ j_R` along
the range of a right inverse `Q` is injective once the pregluing errors are small compared with
`‖Q‖` and the elements of the kernels of the pieces are small beyond the neck. -/
private theorem finrank_ker_add_finrank_ker_le {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |β s| ≤ 1) (hβ'1 : ∀ s, |deriv β s| ≤ 1)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - β s) (hγ1 : ∀ s, |1 - β s| ≤ 1)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ 1)
    (hβ0 : ∀ s ≤ 0, β s = 1) (hβR : ∀ s, R / 2 ≤ s → β s = 0)
    {B d ε : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂stripMeasure,
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤ B)
    (hβd : ∀ s, |deriv β s| ≤ d) (hγd : ∀ s, |deriv (fun s ↦ 1 - β s) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).comp Q = ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker]
    {θ : ℝ} (hθ : 0 ≤ θ)
    (ht₁ : ∀ k ∈ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (ht₂ : ∀ k ∈ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (hsmall : 2 * ‖Q‖ * (ε + d * B) + θ < 1) :
    finrank ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
        finrank ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker ≤
      finrank ℝ (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker := by
  have hzero (k₁ k₂) := eq_zero_of_preglue hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1 hγ hγ1 hγ'1 hβ0
    hβR hB0 hB hβd hγd hε hn₁ hn₂ hθ ht₁ ht₂ hsmall (k₁ := k₁) (k₂ := k₂)
  set A₁ := ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁
  set A₂ := ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂
  set A := ((jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)
  -- The pregluing of two elements of `W^{1,2} × Sᵢ`.
  set pre : (H1 V × S₁) × (H1 V × S₂) →L[ℝ] H1 V × (S₁ × S₂) :=
    (((cutoffL hβ hβ1 hβ'1).comp
      ((translate 2 (testSection V) R).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)))) +
      ((cutoffL hγ hγ1 hγ'1).comp
      ((translate 2 (testSection V) (-R)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))).prod
      (((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) with hpredef
  have hpre (k₁ : H1 V × S₁) (k₂ : H1 V × S₂) : pre (k₁, k₂) =
      (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
        cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1), (k₁.2, k₂.2)) := by
    simp [hpredef]
  have hr := ContinuousLinearMap.rightInverse_of_comp hQ
  clear_value A₁ A₂ A pre
  -- The pregluing corrected into the kernel of the glued operator along the range of `Q`.
  let Ψ : A₁.ker × A₂.ker →ₗ[ℝ] A.ker :=
    ((A.projKerOfRightInverse Q hr).comp pre : _ →ₗ[ℝ] _) ∘ₗ A₁.ker.subtype.prodMap A₂.ker.subtype
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    rw [← sub_eq_zero]
    have h : Ψ (x - y) = 0 := (map_sub Ψ x y).trans (by rw [hxy]; exact sub_self (Ψ y))
    generalize x - y = w at h ⊢
    obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := w
    have h' : pre (k₁, k₂) - Q (A (pre (k₁, k₂))) = 0 := congrArg Subtype.val h
    rw [sub_eq_zero, hpre] at h'
    obtain ⟨rfl, rfl⟩ := hzero k₁ k₂ hk₁ hk₂ h'
    rfl
  have := free_ker A₁
  have := free_ker A₂
  have := free_ker A
  exact Module.finrank_prod.symm.trans_le (LinearMap.finrank_le_finrank_of_injective hinj)

/-- The first components of a space of elements of `W^{1,2} × S`, as `L²` jets. -/
private abbrev jetComponents {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (K : Submodule ℝ (H1 V × S)) : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  K.map ((H1 V).subtype ∘ₗ LinearMap.fst ℝ (H1 V) S)

/-- **The kernels for one neck length.** For a neck length `R` at which the cutting and
pregluing errors are small, the kernel of `D_R ⊕ j_R` has the dimension of the kernels of the
pieces. -/
private theorem finiteDimensional_and_finrank_ker_eq {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    (hR : 0 < R) {L : ℝ} (hL : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) (hRL : 2 / R * L ≤ 1)
    {B ε : ℝ} (hB0 : 0 ≤ B) (hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B)
    (hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B) (hB : ∀ᵐ z ∂stripMeasure,
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤ B)
    (hε : 0 ≤ ε) (hn : ∀ᵐ z ∂stripMeasure, neckCutoff (-(2 / R)) z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).comp Q = ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (ht₁ : ∀ f ∈
      jetComponents (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst)) f‖ ≤ 1 / 2 * ‖f‖)
    (ht₂ : ∀ f ∈
      jetComponents (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const)) f‖ ≤ 1 / 2 * ‖f‖)
    (hsmall₁ : (‖Q₁‖ + ‖Q₂‖) * (ε + 2 / R * L * B) < 1)
    (hsmall₂ : 2 * ‖Q‖ * (ε + 2 / R * L * B) + 1 / 2 < 1) :
    FiniteDimensional ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ∧
    finrank ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker =
      finrank ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
        finrank ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker := by
  -- The cutoff `β = neckCutoff (-(2 / R))`, equal to `1` on `s ≤ 0` and `0` on `s ≥ R / 2`.
  set β := neckCutoff (-(2 / R))
  have hβ : ContDiff ℝ 2 β := contDiff_neckCutoff _
  have hβ1 (s : ℝ) : |β s| ≤ 1 := abs_neckCutoff_le_one _ s
  have hβd (s : ℝ) : |deriv β s| ≤ 2 / R * L :=
    (abs_deriv_neckCutoff_le hL _ s).trans_eq (by rw [abs_neg, abs_of_pos (by positivity)])
  have hβ'1 (s : ℝ) : |deriv β s| ≤ 1 := (hβd s).trans hRL
  have hγ : ContDiff ℝ 2 fun s ↦ 1 - β s := contDiff_const.sub hβ
  have hγ1 (s : ℝ) : |1 - β s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [neckCutoff_nonneg (-(2 / R)) s, neckCutoff_le_one (-(2 / R)) s]
  have hγd (s : ℝ) : |deriv (fun s ↦ 1 - β s) s| ≤ 2 / R * L := by
    rw [deriv_const_sub, abs_neg]
    exact hβd s
  have hγ'1 (s : ℝ) : |deriv (fun s ↦ 1 - β s) s| ≤ 1 := (hγd s).trans hRL
  have hβ0 (s : ℝ) (hs : s ≤ 0) : β s = 1 := neckCutoff_neg_two_div_eq_one hR.le hs
  have hβR (s : ℝ) (hs : R / 2 ≤ s) : β s = 0 := neckCutoff_neg_two_div_eq_zero hR hs
  -- On the support of `1 - β`, where `s > 0`, the glued field is `M₂(· - R, ·)`.
  have hn₂ : ∀ᵐ z ∂stripMeasure, 1 - β z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε :=
    ae_of_all _ fun z hz ↦ by
      have h0 : 0 ≤ z.1 := by
        by_contra h
        exact hz (by rw [hβ0 _ (not_le.1 h).le, sub_self])
      rw [uncurry_gluedCoeff_of_nonneg _ _ _ h0, sub_self, norm_zero]
      exact hε
  obtain ⟨hfin, hle⟩ := finiteDimensional_and_finrank_ker_le hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1
    hγ hγ1 hγ'1 hβ0 hβR hB0 hB₁ hB₂ hβd hγd hε hn hn₂ hQ₁ hQ₂ hsmall₁
  -- The tails of the elements of the kernels of the pieces are those of their jets.
  have ht₁' (k) (hk : k ∈ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker) :
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ 1 / 2 * ‖k‖ :=
    (ht₁ _ (Submodule.mem_map_of_mem hk)).trans (mul_le_mul_of_nonneg_left
      ((Submodule.norm_coe _).trans_le (norm_fst_le k)) (by norm_num))
  have ht₂' (k) (hk : k ∈ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) :
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ 1 / 2 * ‖k‖ :=
    (ht₂ _ (Submodule.mem_map_of_mem hk)).trans (mul_le_mul_of_nonneg_left
      ((Submodule.norm_coe _).trans_le (norm_fst_le k)) (by norm_num))
  exact ⟨hfin, le_antisymm hle (finrank_ker_add_finrank_ker_le hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1
    hβ'1 hγ hγ1 hγ'1 hβ0 hβR hB0 hB hβd hγd hε hn hn₂ hQ (by norm_num) ht₁' ht₂'
    hsmall₂)⟩

/-- The choice of `ε` and of the neck length making the cutting and the pregluing errors
`2 ε + 2 L B / R` small: with `ε = 1 / (64 (K + 1))` and `R ≥ 128 L B (K + 1)`, they are at most
`3 / (64 (K + 1))`. -/
private theorem small_errors {K L B ε R q : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (hε : ε = 1 / (64 * (K + 1))) (hR : 0 < R) (hRLB : 128 * L * B * (K + 1) ≤ R)
    (hq : q ≤ 4 * K) :
    K * (2 * ε + 2 / R * L * B) < 1 ∧ 2 * q * (2 * ε + 2 / R * L * B) + 1 / 2 < 1 := by
  have hδ0 : 0 ≤ 2 * ε + 2 / R * L * B := by rw [hε]; positivity
  have hδ : (K + 1) * (2 * ε + 2 / R * L * B) ≤ 3 / 64 := by
    have h₁ : (K + 1) * (2 * ε) = 1 / 32 := by rw [hε]; field_simp; ring
    have h₂ : (K + 1) * (2 / R * L * B) ≤ 1 / 64 := by
      rw [show (K + 1) * (2 / R * L * B) = 2 * L * B * (K + 1) / R by ring, div_le_iff₀ hR]
      linarith
    linarith [mul_add (K + 1) (2 * ε) (2 / R * L * B)]
  constructor <;> nlinarith [hq]

variable [CompleteSpace W] in
/-- **The kernels of glued stabilized operators.** Let `D₁` and `D₂` be first-order operators on
the cylinder with essentially bounded coefficient fields `M₁` and `M₂` whose ends match,
`M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞` uniformly in `t`. Let
`ιᵢ : Sᵢ → L²` be stabilizers, the sections `ι₁ σ₁` vanishing for `s > T` and `ι₂ σ₂` for
`s < -T`, such that the stabilized operators `(ξ, σ) ↦ Dᵢ ξ + ιᵢ σ` have bounded linear right
inverses and finite-dimensional kernels `Eᵢ`. Then for every sufficiently long neck the kernel
`E_R` of the stabilized glued operator `(ξ, σ₁, σ₂) ↦ D_R ξ + j_R (σ₁, σ₂)`
(`TauCeti.CylinderSobolev.gluedStabilizer`) is finite-dimensional, of dimension
`dim E₁ + dim E₂`. -/
theorem exists_forall_ge_finiteDimensional_and_finrank_ker_coprod_jetOperator_gluedCoeff_eq
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker] :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, FiniteDimensional ℝ (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ∧
      finrank ℝ (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker =
        finrank ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
          finrank ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- Opaque names for the constants keep the arithmetic below away from the operator norms.
  obtain ⟨K, hK⟩ : ∃ K, K = ‖Q₁‖ + ‖Q₂‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨B, hB⟩ : ∃ B, B = lpNorm M₁ ∞ stripMeasure + lpNorm M₂ ∞ stripMeasure := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (64 * (K + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 h₁ ε hε0)
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (Metric.tendstoUniformlyOn_iff.1 h₂ ε hε0)
  obtain ⟨R₁, hR₁⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff hM₁ hM₂
    h₁ h₂ hι₁ hι₂ hQ₁ hQ₂
  -- The kernels of the pieces have uniformly small tails beyond the neck.
  have hf₁ : FiniteDimensional ℝ
      (jetComponents (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker) :=
    Module.Finite.map _ _
  have hf₂ : FiniteDimensional ℝ
      (jetComponents (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) :=
    Module.Finite.map _ _
  -- Instance search times out on `FiniteDimensional` of these kernels (the instance mismatch of
  -- `free_ker`), so `hf₁` and `hf₂` are passed explicitly.
  obtain ⟨ht₁, -⟩ := @eventually_forall_norm_multiplicationOperator_le (V × V × V) _ _ _ hf₁
    (1 / 2) (by norm_num)
  obtain ⟨-, ht₂⟩ := @eventually_forall_norm_multiplicationOperator_le (V × V × V) _ _ _ hf₂
    (1 / 2) (by norm_num)
  obtain ⟨R₂, hR₂⟩ :=
    eventually_atTop.1 (ht₁.and ((tendsto_id.atTop_div_const two_pos).eventually ht₂))
  refine ⟨max (max R₁ R₂) (max (max (2 * T₁) (-2 * T₂))
    (max (max (T + 1) (2 * T)) (max 1 (max (2 * L) (128 * L * B * (K + 1)))))), fun R hR ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨⟨hRR₁, hRR₂⟩, ⟨hRT₁, hRT₂⟩, ⟨hRT, h2TR⟩, hR1, hR2L, hRLB⟩ := hR
  have hRpos : 0 < R := by linarith
  obtain ⟨Q, hQ, hQn⟩ := hR₁ R hRR₁
  obtain ⟨hR₂₁, hR₂₂⟩ := hR₂ R hRR₂
  have hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B := (ae_le_lpNorm_exponent_top hM₁).mono fun z h ↦
    h.trans (by rw [hB]; exact le_add_of_nonneg_right lpNorm_nonneg)
  have hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B := (ae_le_lpNorm_exponent_top hM₂).mono fun z h ↦
    h.trans (by rw [hB]; exact le_add_of_nonneg_left lpNorm_nonneg)
  have hRL : 2 / R * L ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hRpos]; linarith
  obtain ⟨hsmall₁, hsmall₂⟩ := small_errors hK0 hL0 hB0 hε hRpos hRLB (hK ▸ hQn)
  rw [hK] at hsmall₁
  exact finiteDimensional_and_finrank_ker_eq hM₁ hM₂ hι₁ hι₂ (by linarith) h2TR hRpos hL hRL hB0
    hB₁ hB₂ ((memLp_uncurry_gluedCoeff hM₁ hM₂ R).2.mono fun z h ↦ hB ▸ h) (by positivity)
    (ae_norm_uncurry_gluedCoeff_sub_le_left hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂) hQ₁ hQ₂ hQ hR₂₁ hR₂₂
    hsmall₁ hsmall₂

variable [CompleteSpace V] [CompleteSpace W] in
/-- **Index additivity under gluing.** Let `D₁` and `D₂` be first-order operators on the cylinder,
from `W^{1,2}(ℝ × S¹, V)` to `L²`, with essentially bounded coefficient fields `M₁` and `M₂` whose
ends match: `M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞`, uniformly in `t`.
If `D₁` and `D₂` are Fredholm, then for every sufficiently long neck the operator `D_R` of the glued
coefficient field `M_R` (`TauCeti.gluedCoeff`, neck length `2 R`) is Fredholm, and
`ind D_R = ind D₁ + ind D₂`. -/
theorem exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    (hD₁ : ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).IsFredholm ∧
      ((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).index =
        ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).index +
          ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).index := by
  obtain ⟨S₁, -, -, hS₁, ⟨T₁, hT₁⟩, Q₁, hQ₁⟩ := hD₁.exists_le_testSectionLp_isTopCompl
  obtain ⟨S₂, -, -, hS₂, ⟨T₂, hT₂⟩, Q₂, hQ₂⟩ := hD₂.exists_le_testSectionLp_isTopCompl
  have hι₁ := ae_subtypeL_eq_zero_of_lt hT₁ (le_max_left T₁ T₂)
  have hι₂ := ae_subtypeL_eq_zero_of_lt_neg hT₂ (le_max_right T₁ T₂)
  have := hD₁.finite_ker
  have := hD₂.finite_ker
  have := (hD₁.coprod_of_finiteDimensional S₁.subtypeL).finite_ker
  have := (hD₂.coprod_of_finiteDimensional S₂.subtypeL).finite_ker
  obtain ⟨R₀, hR₀⟩ :=
    exists_forall_ge_finiteDimensional_and_finrank_ker_coprod_jetOperator_gluedCoeff_eq hM₁ hM₂
      h₁ h₂ hι₁ hι₂ hQ₁ hQ₂
  obtain ⟨R₁, hR₁⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff hM₁ hM₂
    h₁ h₂ hι₁ hι₂ hQ₁ hQ₂
  refine ⟨max R₀ R₁, fun R hR ↦ ?_⟩
  obtain ⟨hfin, hrank⟩ := hR₀ R (le_of_max_le_left hR)
  obtain ⟨Q, hQ, -⟩ := hR₁ R (le_of_max_le_right hR)
  set D := (jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL
  have hsurj := (ContinuousLinearMap.rightInverse_of_comp hQ).surjective
  have hF := ContinuousLinearMap.IsFredholm.of_surjective_coprod D _ hsurj hfin
  have := hF.finite_ker
  refine ⟨hF, ?_⟩
  rw [ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective _ _ hsurj,
    ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective _ _
      (ContinuousLinearMap.rightInverse_of_comp hQ₁).surjective,
    ContinuousLinearMap.index_eq_finrank_ker_coprod_sub_of_surjective _ _
      (ContinuousLinearMap.rightInverse_of_comp hQ₂).surjective, hrank, Module.finrank_prod]
  push_cast
  ring

variable [CompleteSpace V] [CompleteSpace W] in
/-- **Index additivity under gluing, for every nearby operator.** Under the hypotheses of
`TauCeti.CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq`, there are
`ε > 0` and `R₀` such that for every neck `R ≥ R₀`, every operator `P` from `W^{1,2}` to `L²` within
`ε` in operator norm of the glued operator `D_R` is Fredholm, of index `ind D₁ + ind D₂`.

The radius `ε` does not depend on `R`. So an operator `P_R` that approaches `D_R` as `R → ∞`, such
as the linearized operator along a map pre-glued with neck length `2 R`, is Fredholm of index
`ind D₁ + ind D₂` for every long neck. A radius taken from the openness of the Fredholm operators
at each `D_R` separately could shrink as `R` grows. -/
theorem exists_pos_exists_forall_ge_isFredholm_and_index_eq_of_norm_sub_jetOperator_gluedCoeff_le
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    (hD₁ : ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ P : H1 V →L[ℝ] Lp W 2 stripMeasure,
      ‖P - (jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL‖ ≤ ε →
      P.IsFredholm ∧
        P.index = ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).index +
          ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).index := by
  -- The stabilized glued operators have right inverses bounded by `C`, independently of `R`.
  obtain ⟨-, S₁, S₂, -, -, hS₁, hS₂, -, -, C, R₀, hR₀⟩ :=
    exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm_smooth hM₁
      hM₂ h₁ h₂ hD₁ hD₂
  obtain ⟨R₁, hR₁⟩ :=
    exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq hM₁ hM₂ h₁ h₂ hD₁ hD₂
  refine ⟨1 / (4 * (|C| + 1)), by positivity, max R₀ R₁, fun R hR P hP ↦ ?_⟩
  obtain ⟨Q, hQ, hQn⟩ := hR₀ R (le_of_max_le_left hR)
  obtain ⟨hF, hind⟩ := hR₁ R (le_of_max_le_right hR)
  rw [← hind]
  refine hF.isFredholm_and_index_eq_of_norm_sub_mul_lt hQ ?_
  calc _ ≤ 1 / (4 * (|C| + 1)) * |C| := mul_le_mul hP (hQn.trans (le_abs_self C))
        (ContinuousLinearMap.opNorm_nonneg Q) (by positivity)
    _ < 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) two_pos]
      linarith [abs_nonneg C]

end TauCeti.CylinderSobolev
