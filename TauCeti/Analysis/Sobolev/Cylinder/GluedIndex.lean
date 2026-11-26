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

/-!
# The kernel, the exact sequence and the index of glued operators on the cylinder

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
  `(β ξ₁(· + R, ·) + (1 - β) ξ₂(· - R, ·), σ₁, σ₂)` (`TauCeti.CylinderSobolev.neckPreglue`), which
  nearly lies in `E_R` (`TauCeti.CylinderSobolev.norm_jetOperator_cutoffL_translate_add_le`), and
  corrected into `E_R` along the range of `Q` (`TauCeti.CylinderSobolev.gluedKernelMap`).
  This is injective, because the pregluing is `ξ₁(· + R, ·)` on `s < 0` and `ξ₂(· - R, ·)` on
  `s > R / 2`, so it controls `ξ₁` and `ξ₂` up to their tails beyond the neck. These tails are
  uniformly small on the finite-dimensional spaces `Eᵢ` for long necks
  (`TauCeti.CylinderSobolev.eventually_forall_norm_multiplicationOperator_le`).

So the corrected pregluing is an isomorphism `E₁ × E₂ ≃ E_R` for long necks, for every right
inverse `Q` of bounded norm
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_bijective_gluedKernelMap`).

**The exact sequence.** Through this isomorphism, the exact sequence
`0 → ker D_R → E_R → S₁ × S₂ → coker D_R → 0` of the surjective stabilization
(`ContinuousLinearMap.exact_kerCoprodHom_parameterProj`,
`ContinuousLinearMap.exact_parameterProj_parameterToCoker`) becomes the exact sequence of linear
gluing (`ContinuousLinearMap.exact_of_linearEquiv_ker_coprod`)

`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`

(`TauCeti.CylinderSobolev.exists_forall_ge_forall_exists_linearEquiv_exact_gluedKernelMap`). Its
middle map is the obstruction map `b_R` (`TauCeti.CylinderSobolev.gluedObstructionMap`), the
stabilizer component of the corrected pregluing. When
`b_R = 0` the kernel of `D_R` is `E₁ × E₂` and its cokernel is `S₁ × S₂`. For stabilizers
complementing the ranges of the pieces, `Eᵢ = ker Dᵢ × {0}`, and in the surjective case
(`Sᵢ = 0`) there is no obstruction.

## Main definitions

* `TauCeti.CylinderSobolev.neckPreglue`: the pregluing of two pieces along a neck of length `2 R`.
* `TauCeti.CylinderSobolev.gluedKernelMap`: the pregluing of elements of the kernels of the pieces,
  corrected into the kernel of the glued operator along a right inverse.
* `TauCeti.CylinderSobolev.gluedObstructionMap`: the obstruction map `b_R`, the stabilizer
  component of the corrected pregluing.

## Main results

* `exists_forall_ge_forall_bijective_gluedKernelMap`: for long necks the corrected pregluing is an
  isomorphism `E₁ × E₂ ≃ E_R`.
* `exists_forall_ge_forall_exists_linearEquiv_exact_gluedKernelMap`: the exact sequence
  `0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`, and its splitting when `b_R = 0`.
* `exists_forall_ge_finiteDimensional_and_finrank_ker_coprod_jetOperator_gluedCoeff_eq`: the
  kernel of the stabilized glued operator has dimension `dim E₁ + dim E₂` for long necks.
* `TauCeti.CylinderSobolev.exists_forall_ge_isFredholm_and_index_jetOperator_gluedCoeff_eq`: the
  glued operator of two Fredholm operators is Fredholm for long necks, with
  `ind D_R = ind D₁ + ind D₂`.

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
      β z.1 • jetOperator stripMeasure N (ξ : Lp (V × V × V) 2 stripMeasure) z) :
    ‖(((jetOperator stripMeasure M).comp (H1 V).subtypeL).coprod ι)
        (translate 2 (testSection V) (-a) (cutoffL hβ hβ1 hβ'1 ξ), σ)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  have hG := hM.comp_measurePreserving (measurePreserving_add_strip a)
  rw [← (translateLp (E := W) (p := 2) a).norm_map]
  have key : translateLp a ((((jetOperator stripMeasure M).comp (H1 V).subtypeL).coprod ι)
      (translate 2 (testSection V) (-a) (cutoffL hβ hβ1 hβ'1 ξ), σ)) =
      jetOperator stripMeasure (fun z ↦ M (z + (a, 0)))
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
    (hξ : (((jetOperator stripMeasure M).comp (H1 V).subtypeL).coprod ι) (ξ, σ) = 0)
    (hβι : ∀ᵐ z ∂stripMeasure, β z.1 ≠ 1 → translateLp a (ι σ) z = 0) :
    ‖jetOperator stripMeasure N
        (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) a ξ) : Lp (V × V × V) 2 stripMeasure) +
      translateLp a (ι σ)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  have hG := hM.comp_measurePreserving (measurePreserving_add_strip a)
  -- `D_{M(· + a)}` of the translate of `ξ` is the translate of `D_M ξ = -ι σ`.
  have hD : jetOperator stripMeasure (fun z ↦ M (z + (a, 0)))
      (translate 2 (testSection V) a ξ : Lp (V × V × V) 2 stripMeasure) = -translateLp a (ι σ) := by
    have h : jetOperator stripMeasure M (ξ : Lp (V × V × V) 2 stripMeasure) = -ι σ :=
      eq_neg_of_add_eq_zero_left (by simpa using hξ)
    rw [coe_translate, ← translateLp_jetOperator hM, h, map_neg]
  have hζ : ∀ᵐ z ∂stripMeasure, (-translateLp a (ι σ)) z = β z.1 • jetOperator stripMeasure
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
    (hx : (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) (ξ, σ) = 0) :
    ‖(((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
        (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 ξ), σ.1)‖ ≤ (ε + d * B) * ‖ξ‖ ∧
      ‖(((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
        (translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 ξ), σ.2)‖ ≤ (ε + d * B) * ‖ξ‖ := by
  set G := Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R)
  have hG := (memLp_uncurry_gluedCoeff hM₁ hM₂ R).1
  -- `D_G ξ = -j_R σ`.
  have hD : jetOperator stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) =
      -(translateLp R (ι₁ σ.1) + translateLp (-R) (ι₂ σ.2)) :=
    eq_neg_of_add_eq_zero_left (by simpa using hx)
  have hv₁ := ae_translateLp_eq_zero_of_sub_lt hι₁ R σ.1
  have hv₂ := ae_translateLp_eq_zero_of_lt_neg_sub hι₂ (-R) σ.2
  have hζ₁ : ∀ᵐ z ∂stripMeasure, (-translateLp R (ι₁ σ.1)) z =
      β z.1 • jetOperator stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) z := by
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
      (1 - β z.1) • jetOperator stripMeasure G (ξ : Lp (V × V × V) 2 stripMeasure) z := by
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
    (hk₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁) (ξ₁, σ₁) = 0)
    (hk₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂) (ξ₂, σ₂) = 0) :
    ‖(((jetOperator stripMeasure
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
  calc _ = ‖(jetOperator stripMeasure G
          (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R ξ₁) : Lp (V × V × V) 2 stripMeasure) +
          translateLp R (ι₁ σ₁)) + (jetOperator stripMeasure G
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
    (hv : (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) v = 0)
    (h₁ : ((translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1) : H1 V × S₁) =
      Q₁ ((((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
        (translate 2 (testSection V) (-R) (cutoffL hβ hβ1 hβ'1 v.1), v.2.1)))
    (h₂ : ((translate 2 (testSection V) R (cutoffL hγ hγ1 hγ'1 v.1), v.2.2) : H1 V × S₂) =
      Q₂ ((((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
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
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (hsmall : (‖Q₁‖ + ‖Q₂‖) * (ε + d * B) < 1) :
    FiniteDimensional ℝ (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ∧
    finrank ℝ (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ≤
      finrank ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
        finrank ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker := by
  have hzero (v) := eq_zero_of_cut hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ hβ1 hβ'1 hγ hγ1 hγ'1 hβ0 hβR hB0
    hB₁ hB₂ hβd hγd hε hn₁ hn₂ hsmall (v := v)
  set A₁ := ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁
  set A₂ := ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂
  set A := ((jetOperator stripMeasure
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
    (ht₁ : ∀ k ∈ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (ht₂ : ∀ k ∈ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (hsmall : 2 * ‖Q‖ * (ε + d * B) + θ < 1) {k₁ : H1 V × S₁} {k₂ : H1 V × S₂}
    (hk₁ : k₁ ∈ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker)
    (hk₂ : k₂ ∈ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker)
    (h : ((cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
        cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1), (k₁.2, k₂.2)) :
          H1 V × (S₁ × S₂)) = Q ((((jetOperator stripMeasure
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

/-! ### Pregluing along the neck -/

/-- The neck cutoff `β = neckCutoff a`, the complementary cutoff `1 - β` and their derivatives are
bounded. -/
private theorem exists_bound_neckCutoff (a : ℝ) : ∃ B : ℝ,
    (∀ s, |neckCutoff a s| ≤ B) ∧ (∀ s, |deriv (neckCutoff a) s| ≤ B) ∧
      (∀ s, |1 - neckCutoff a s| ≤ B) ∧ ∀ s, |deriv (fun s ↦ 1 - neckCutoff a s) s| ≤ B := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  refine ⟨max 1 (|a| * L), fun s ↦ (abs_neckCutoff_le_one a s).trans (le_max_left _ _),
    fun s ↦ (abs_deriv_neckCutoff_le hL a s).trans (le_max_right _ _), fun s ↦ ?_, fun s ↦ ?_⟩
  · exact (abs_one_sub_neckCutoff_le_one a s).trans (le_max_left _ _)
  · rw [abs_deriv_one_sub_neckCutoff]
    exact (abs_deriv_neckCutoff_le hL a s).trans (le_max_right _ _)

/-- **Pregluing along a neck of length `2 R`.** Elements `(ξ₁, σ₁)` of `W^{1,2} × S₁` and
`(ξ₂, σ₂)` of `W^{1,2} × S₂` are preglued to

`(β ξ₁(· + R, ·) + (1 - β) ξ₂(· - R, ·), (σ₁, σ₂))`,

for the neck cutoff `β = neckCutoff (-(2 / R))`, which is `1` on `s ≤ 0` and `0` on `s ≥ R / 2`
(`TauCeti.CylinderSobolev.coe_fst_neckPreglue_apply`,
`TauCeti.CylinderSobolev.snd_neckPreglue_apply`). The pieces are translated to the two halves of
the neck as in the glued coefficient field `TauCeti.gluedCoeff`, which is `M₁(· + R, ·)` on `s < 0`
and `M₂(· - R, ·)` on `s ≥ 0`. -/
noncomputable def neckPreglue (R : ℝ) : (H1 V × S₁) × (H1 V × S₂) →L[ℝ] H1 V × (S₁ × S₂) :=
  have hB := (exists_bound_neckCutoff (-(2 / R))).choose_spec
  (((cutoffL (contDiff_neckCutoff _) hB.1 hB.2.1).comp
      ((translate 2 (testSection V) R).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)))) +
    ((cutoffL (β := fun s ↦ 1 - neckCutoff (-(2 / R)) s)
      (contDiff_const.sub (contDiff_neckCutoff _)) hB.2.2.1 hB.2.2.2).comp
      ((translate 2 (testSection V) (-R)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))

/-- The `W^{1,2}` component of the pregluing, as an `L²` jet:
`β ξ₁(· + R, ·) + (1 - β) ξ₂(· - R, ·)` for the neck cutoff `β = neckCutoff (-(2 / R))`. -/
@[simp]
theorem coe_fst_neckPreglue_apply (R : ℝ) (k₁ : H1 V × S₁) (k₂ : H1 V × S₂) :
    ((neckPreglue R (k₁, k₂)).1 : Lp (V × V × V) 2 stripMeasure) =
      jetOperator stripMeasure (cutoffCoeff V (neckCutoff (-(2 / R))))
          (translateLp R (k₁.1 : Lp (V × V × V) 2 stripMeasure)) +
        jetOperator stripMeasure (cutoffCoeff V fun s ↦ 1 - neckCutoff (-(2 / R)) s)
          (translateLp (-R) (k₂.1 : Lp (V × V × V) 2 stripMeasure)) := by
  simp [neckPreglue, coe_translate]

/-- The stabilizer components of the pregluing are those of the two pieces. -/
@[simp]
theorem snd_neckPreglue_apply (R : ℝ) (k₁ : H1 V × S₁) (k₂ : H1 V × S₂) :
    (neckPreglue R (k₁, k₂)).2 = (k₁.2, k₂.2) := by
  simp [neckPreglue]

/-- The pregluing written with the cutoff operators `cutoffL`, for any bounds `B₁`, `B₂` on the
cutoffs `β = neckCutoff (-(2 / R))` and `1 - β` and their derivatives: it is
`(β ξ₁(· + R, ·) + (1 - β) ξ₂(· - R, ·), (σ₁, σ₂))`, independently of the bounds used to define
`TauCeti.CylinderSobolev.neckPreglue`. -/
theorem neckPreglue_eq_cutoffL {R : ℝ} (hβ : ContDiff ℝ 2 (neckCutoff (-(2 / R))))
    {B₁ : ℝ} (hβ1 : ∀ s, |neckCutoff (-(2 / R)) s| ≤ B₁)
    (hβ'1 : ∀ s, |deriv (neckCutoff (-(2 / R))) s| ≤ B₁)
    (hγ : ContDiff ℝ 2 fun s ↦ 1 - neckCutoff (-(2 / R)) s) {B₂ : ℝ}
    (hγ1 : ∀ s, |1 - neckCutoff (-(2 / R)) s| ≤ B₂)
    (hγ'1 : ∀ s, |deriv (fun s ↦ 1 - neckCutoff (-(2 / R)) s) s| ≤ B₂)
    (k₁ : H1 V × S₁) (k₂ : H1 V × S₂) :
    neckPreglue R (k₁, k₂) = (cutoffL hβ hβ1 hβ'1 (translate 2 (testSection V) R k₁.1) +
      cutoffL hγ hγ1 hγ'1 (translate 2 (testSection V) (-R) k₂.1), (k₁.2, k₂.2)) := by
  refine Prod.ext (Subtype.ext ?_) (snd_neckPreglue_apply R k₁ k₂)
  rw [coe_fst_neckPreglue_apply]
  simp [coe_translate]

/-- **The corrected pregluing.** Let `A` be an operator on `W^{1,2} × (S₁ × S₂)` with a right
inverse `Q`, and let `K₁`, `K₂` be subspaces of `W^{1,2} × S₁` and `W^{1,2} × S₂`, typically the
kernels `E₁`, `E₂` of the stabilized pieces. The pregluing `p = neckPreglue R` of an element of
`K₁ × K₂`, corrected into the kernel of `A` along the range of `Q`, is `p k - Q (A (p k))`
(`TauCeti.CylinderSobolev.coe_gluedKernelMap_apply`). For the stabilized glued operator
`A = D_R ⊕ j_R` and long necks it is an isomorphism `E₁ × E₂ ≃ E_R`
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_bijective_gluedKernelMap`). -/
noncomputable def gluedKernelMap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : H1 V × (S₁ × S₂) →L[ℝ] Y) (Q : Y →L[ℝ] H1 V × (S₁ × S₂))
    (hQ : Function.RightInverse Q A) (K₁ : Submodule ℝ (H1 V × S₁))
    (K₂ : Submodule ℝ (H1 V × S₂)) (R : ℝ) : K₁ × K₂ →L[ℝ] A.ker :=
  (A.projKerOfRightInverse Q hQ).comp ((neckPreglue R).comp (K₁.subtypeL.prodMap K₂.subtypeL))

/-- The corrected pregluing is the pregluing minus `Q A` of it. -/
@[simp]
theorem coe_gluedKernelMap_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : H1 V × (S₁ × S₂) →L[ℝ] Y) (Q : Y →L[ℝ] H1 V × (S₁ × S₂))
    (hQ : Function.RightInverse Q A) (K₁ : Submodule ℝ (H1 V × S₁))
    (K₂ : Submodule ℝ (H1 V × S₂)) (R : ℝ) (k : K₁ × K₂) :
    (gluedKernelMap A Q hQ K₁ K₂ R k : H1 V × (S₁ × S₂)) =
      neckPreglue R ((k.1 : H1 V × S₁), (k.2 : H1 V × S₂)) -
        Q (A (neckPreglue R ((k.1 : H1 V × S₁), (k.2 : H1 V × S₂)))) :=
  ContinuousLinearMap.coe_projKerOfRightInverse_apply A Q hQ _

/-- **The obstruction map** `b_R`. Let `A` be an operator on `W^{1,2} × (S₁ × S₂)` with a right
inverse `Q`, and let `K₁`, `K₂` be subspaces of `W^{1,2} × S₁` and `W^{1,2} × S₂`. The obstruction
map sends an element of `K₁ × K₂` to the stabilizer component `(σ₁, σ₂)` of its corrected pregluing
`TauCeti.CylinderSobolev.gluedKernelMap`, namely `(σ₁, σ₂) - (Q (A (p k))).2` for the pregluing
`p k` (`TauCeti.CylinderSobolev.gluedObstructionMap_apply`). For the stabilized glued operator
`A = D_R ⊕ j_R` and the kernels `E₁`, `E₂` of the stabilized pieces it is the middle map of the
exact sequence `0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_exists_linearEquiv_exact_gluedKernelMap`). -/
noncomputable def gluedObstructionMap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : H1 V × (S₁ × S₂) →L[ℝ] Y) (Q : Y →L[ℝ] H1 V × (S₁ × S₂))
    (hQ : Function.RightInverse Q A) (K₁ : Submodule ℝ (H1 V × S₁))
    (K₂ : Submodule ℝ (H1 V × S₂)) (R : ℝ) : K₁ × K₂ →L[ℝ] S₁ × S₂ :=
  (ContinuousLinearMap.snd ℝ (H1 V) (S₁ × S₂)).comp
    (A.ker.subtypeL.comp (gluedKernelMap A Q hQ K₁ K₂ R))

/-- The obstruction map is the stabilizer component of the pregluing minus that of `Q A` of it. -/
@[simp]
theorem gluedObstructionMap_apply {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : H1 V × (S₁ × S₂) →L[ℝ] Y) (Q : Y →L[ℝ] H1 V × (S₁ × S₂))
    (hQ : Function.RightInverse Q A) (K₁ : Submodule ℝ (H1 V × S₁))
    (K₂ : Submodule ℝ (H1 V × S₂)) (R : ℝ) (k : K₁ × K₂) :
    gluedObstructionMap A Q hQ K₁ K₂ R k = ((k.1 : H1 V × S₁).2, (k.2 : H1 V × S₂).2) -
      (Q (A (neckPreglue R ((k.1 : H1 V × S₁), (k.2 : H1 V × S₂))))).2 := by
  simp [gluedObstructionMap]

/-- **The corrected pregluing is injective.** Pregluing elements of the kernels of `Dᵢ ⊕ ιᵢ`
with the neck cutoff and correcting the result into the kernel of `D_R ⊕ j_R` along the range of a
right inverse `Q` (`TauCeti.CylinderSobolev.gluedKernelMap`) is injective once the pregluing errors
are small compared with `‖Q‖` and the elements of the kernels of the pieces are small beyond the
neck. -/
private theorem injective_gluedKernelMap_of_lt_one {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T R : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0) (hTR : T < R) (h2TR : 2 * T ≤ R)
    (hR : 0 < R) (hβ'1 : ∀ s, |deriv (neckCutoff (-(2 / R))) s| ≤ 1)
    {B d ε : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂stripMeasure,
      ‖Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z‖ ≤ B)
    (hβd : ∀ s, |deriv (neckCutoff (-(2 / R))) s| ≤ d) (hε : 0 ≤ ε)
    (hn₁ : ∀ᵐ z ∂stripMeasure, neckCutoff (-(2 / R)) z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₁ (z + (R, 0))‖ ≤ ε)
    (hn₂ : ∀ᵐ z ∂stripMeasure, 1 - neckCutoff (-(2 / R)) z.1 ≠ 0 → ‖Function.uncurry
      (gluedCoeff (Function.curry M₁) (Function.curry M₂) R) z - M₂ (z + (-R, 0))‖ ≤ ε)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    {θ : ℝ} (hθ : 0 ≤ θ)
    (ht₁ : ∀ k ∈ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (ht₂ : ∀ k ∈ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ θ * ‖k‖)
    (hsmall : 2 * ‖Q‖ * (ε + d * B) + θ < 1) :
    Function.Injective (gluedKernelMap (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
      (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
      (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R) := by
  -- The properties of the neck cutoff `β = neckCutoff (-(2 / R))` and of `1 - β`.
  have hβ : ContDiff ℝ 2 (neckCutoff (-(2 / R))) := contDiff_neckCutoff _
  have hγ : ContDiff ℝ 2 fun s ↦ 1 - neckCutoff (-(2 / R)) s := contDiff_const.sub hβ
  have hγ'1 (s : ℝ) := (abs_deriv_one_sub_neckCutoff (-(2 / R)) s).trans_le (hβ'1 s)
  have hγd (s : ℝ) := (abs_deriv_one_sub_neckCutoff (-(2 / R)) s).trans_le (hβd s)
  have hzero (k₁ k₂) := eq_zero_of_preglue hM₁ hM₂ hι₁ hι₂ hTR h2TR hβ (abs_neckCutoff_le_one _)
    hβ'1 hγ (abs_one_sub_neckCutoff_le_one _) hγ'1
    (fun _ hs ↦ neckCutoff_neg_two_div_eq_one hR.le hs)
    (fun _ hs ↦ neckCutoff_neg_two_div_eq_zero hR hs) hB0 hB hβd hγd hε hn₁ hn₂ hθ ht₁ ht₂ hsmall
    (k₁ := k₁) (k₂ := k₂)
  refine (injective_iff_map_eq_zero _).2 fun w h ↦ ?_
  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := w
  -- The corrected pregluing vanishes exactly when the pregluing is fixed by `Q A`.
  have h' := congrArg Subtype.val h
  rw [coe_gluedKernelMap_apply, ZeroMemClass.coe_zero, sub_eq_zero,
    neckPreglue_eq_cutoffL hβ (abs_neckCutoff_le_one _) hβ'1 hγ (abs_one_sub_neckCutoff_le_one _)
      hγ'1] at h'
  obtain ⟨rfl, rfl⟩ := hzero k₁ k₂ hk₁ hk₂ h'
  rfl

/-- The first components of a space of elements of `W^{1,2} × S`, as `L²` jets. -/
private abbrev jetComponents {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (K : Submodule ℝ (H1 V × S)) : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  K.map ((H1 V).subtype ∘ₗ LinearMap.fst ℝ (H1 V) S)

/-- **The kernels for one neck length.** For a neck length `R` at which the cutting and
pregluing errors are small, the corrected pregluing is an isomorphism from the product of the
kernels of the stabilized pieces onto the kernel of `D_R ⊕ j_R`. -/
private theorem bijective_gluedKernelMap_of_lt_one {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
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
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (ht₁ : ∀ f ∈ jetComponents (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst)) f‖ ≤ 1 / 2 * ‖f‖)
    (ht₂ : ∀ f ∈ jetComponents (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker,
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const)) f‖ ≤ 1 / 2 * ‖f‖)
    (hsmall₁ : (‖Q₁‖ + ‖Q₂‖) * (ε + 2 / R * L * B) < 1)
    (hsmall₂ : 2 * ‖Q‖ * (ε + 2 / R * L * B) + 1 / 2 < 1) :
    Function.Bijective (gluedKernelMap (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
      (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
      (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R) := by
  -- The cutoff `β = neckCutoff (-(2 / R))`, equal to `1` on `s ≤ 0` and `0` on `s ≥ R / 2`.
  set β := neckCutoff (-(2 / R))
  have hβ : ContDiff ℝ 2 β := contDiff_neckCutoff _
  have hβ1 (s : ℝ) : |β s| ≤ 1 := abs_neckCutoff_le_one _ s
  have hβd (s : ℝ) : |deriv β s| ≤ 2 / R * L :=
    (abs_deriv_neckCutoff_le hL _ s).trans_eq (by rw [abs_neg, abs_of_pos (by positivity)])
  have hβ'1 (s : ℝ) : |deriv β s| ≤ 1 := (hβd s).trans hRL
  have hγ : ContDiff ℝ 2 fun s ↦ 1 - β s := contDiff_const.sub hβ
  have hγ1 (s : ℝ) : |1 - β s| ≤ 1 := abs_one_sub_neckCutoff_le_one _ s
  have hγd (s : ℝ) : |deriv (fun s ↦ 1 - β s) s| ≤ 2 / R * L :=
    (abs_deriv_one_sub_neckCutoff _ s).trans_le (hβd s)
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
  have ht₁' (k) (hk : k ∈ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker) :
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | R ≤ z.1}
        (measurableSet_le measurable_const measurable_fst))
        ((k : H1 V × S₁).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ 1 / 2 * ‖k‖ :=
    (ht₁ _ (Submodule.mem_map_of_mem hk)).trans (mul_le_mul_of_nonneg_left
      ((Submodule.norm_coe _).trans_le (norm_fst_le k)) (by norm_num))
  have ht₂' (k) (hk : k ∈ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) :
      ‖Lp.multiplicationOperator (linftyIndicator stripMeasure {z : ℝ × ℝ | z.1 ≤ -(R / 2)}
        (measurableSet_le measurable_fst measurable_const))
        ((k : H1 V × S₂).1 : Lp (V × V × V) 2 stripMeasure)‖ ≤ 1 / 2 * ‖k‖ :=
    (ht₂ _ (Submodule.mem_map_of_mem hk)).trans (mul_le_mul_of_nonneg_left
      ((Submodule.norm_coe _).trans_le (norm_fst_le k)) (by norm_num))
  have hinj := injective_gluedKernelMap_of_lt_one hM₁ hM₂ hι₁ hι₂ hTR h2TR hR hβ'1 hB0 hB hβd hε
    hn hn₂ hQ (by norm_num) ht₁' ht₂' hsmall₂
  have := free_ker (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
  have := free_ker (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
  -- The injective map between spaces whose dimensions satisfy the reverse inequality is onto.
  have hge := Module.finrank_prod.symm.trans_le (LinearMap.finrank_le_finrank_of_injective hinj)
  -- The spaces are given by name: elaboration fails to infer them from `hinj`.
  have := hfin
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ×
      (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker)
    (V₂ := (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker)
    (Module.finrank_prod.trans (le_antisymm hle hge).symm)).1 hinj⟩

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

/-- **Small tails beyond the neck.** For long necks, the jets of the elements of two
finite-dimensional spaces `K₁ ⊆ W^{1,2} × S₁` and `K₂ ⊆ W^{1,2} × S₂`, such as the kernels of the
stabilized pieces, have at most half their norm on `s ≥ R` and on `s ≤ -(R / 2)` respectively. -/
private theorem exists_forall_ge_norm_tail_le (K₁ : Submodule ℝ (H1 V × S₁))
    (K₂ : Submodule ℝ (H1 V × S₂)) [FiniteDimensional ℝ K₁] [FiniteDimensional ℝ K₂] :
    ∃ R₂ : ℝ, ∀ R ≥ R₂,
      (∀ f ∈ jetComponents K₁, ‖Lp.multiplicationOperator (linftyIndicator stripMeasure
        {z : ℝ × ℝ | R ≤ z.1} (measurableSet_le measurable_const measurable_fst)) f‖ ≤
          1 / 2 * ‖f‖) ∧
      ∀ f ∈ jetComponents K₂, ‖Lp.multiplicationOperator (linftyIndicator stripMeasure
        {z : ℝ × ℝ | z.1 ≤ -(R / 2)} (measurableSet_le measurable_fst measurable_const)) f‖ ≤
          1 / 2 * ‖f‖ := by
  have hf₁ : FiniteDimensional ℝ (jetComponents K₁) := Module.Finite.map _ _
  have hf₂ : FiniteDimensional ℝ (jetComponents K₂) := Module.Finite.map _ _
  -- Instance search times out on `FiniteDimensional` of these spaces (the instance mismatch of
  -- `free_ker`), so `hf₁` and `hf₂` are passed explicitly.
  obtain ⟨ht₁, -⟩ := @eventually_forall_norm_multiplicationOperator_le (V × V × V) _ _ _ hf₁
    (1 / 2) (by norm_num)
  obtain ⟨-, ht₂⟩ := @eventually_forall_norm_multiplicationOperator_le (V × V × V) _ _ _ hf₂
    (1 / 2) (by norm_num)
  exact eventually_atTop.1 (ht₁.and ((tendsto_id.atTop_div_const two_pos).eventually ht₂))

/-- **The corrected pregluing is an isomorphism onto the glued kernel.** Let `D₁` and `D₂` be
first-order operators on the cylinder with essentially bounded coefficient fields `M₁` and `M₂`
whose ends match, `M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞` uniformly in
`t`. Let `ιᵢ : Sᵢ → L²` be stabilizers, the sections `ι₁ σ₁` vanishing for `s > T` and `ι₂ σ₂` for
`s < -T`, such that the stabilized operators `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` have bounded linear right
inverses and finite-dimensional kernels `Eᵢ`. Then for every bound `C`, for every sufficiently long
neck and every right inverse `Q` of norm at most `C` of the stabilized glued operator
`A_R (ξ, σ₁, σ₂) = D_R ξ + j_R (σ₁, σ₂)`, the pregluing corrected along `Q`
(`TauCeti.CylinderSobolev.gluedKernelMap`) is a linear isomorphism `E₁ × E₂ ≃ E_R` onto the kernel
`E_R` of `A_R`. Right inverses of norm at most `4 (‖Q₁‖ + ‖Q₂‖)` exist for long necks
(`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`). -/
theorem exists_forall_ge_forall_bijective_gluedKernelMap
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (C : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ (Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂))
      (hQ : Function.RightInverse Q (((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))), ‖Q‖ ≤ C →
      Function.Bijective (gluedKernelMap (((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
        (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
        (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R) := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- Opaque names for the constants keep the arithmetic below away from the operator norms. The
  -- constant `K` bounds both the right inverses of the pieces and the given right inverses.
  obtain ⟨K, hK⟩ : ∃ K, K = max (‖Q₁‖ + ‖Q₂‖) C := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_of_le_left (by positivity)
  obtain ⟨B, hB⟩ : ∃ B, B = lpNorm M₁ ∞ stripMeasure + lpNorm M₂ ∞ stripMeasure := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (64 * (K + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 h₁ ε hε0)
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (Metric.tendstoUniformlyOn_iff.1 h₂ ε hε0)
  -- The kernels of the pieces have uniformly small tails beyond the neck.
  obtain ⟨R₂, hR₂⟩ := exists_forall_ge_norm_tail_le
    (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
    (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker
  refine ⟨max R₂ (max (max (2 * T₁) (-2 * T₂))
    (max (max (T + 1) (2 * T)) (max 1 (max (2 * L) (128 * L * B * (K + 1)))))),
    fun R hR Q hQ hQn ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨hRR₂, ⟨hRT₁, hRT₂⟩, ⟨hRT, h2TR⟩, hR1, hR2L, hRLB⟩ := hR
  have hRpos : 0 < R := by linarith
  obtain ⟨hR₂₁, hR₂₂⟩ := hR₂ R hRR₂
  have hB₁ : ∀ᵐ z ∂stripMeasure, ‖M₁ z‖ ≤ B := (ae_le_lpNorm_exponent_top hM₁).mono fun z h ↦
    h.trans (by rw [hB]; exact le_add_of_nonneg_right lpNorm_nonneg)
  have hB₂ : ∀ᵐ z ∂stripMeasure, ‖M₂ z‖ ≤ B := (ae_le_lpNorm_exponent_top hM₂).mono fun z h ↦
    h.trans (by rw [hB]; exact le_add_of_nonneg_left lpNorm_nonneg)
  have hRL : 2 / R * L ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hRpos]; linarith
  have hQK : ‖Q‖ ≤ 4 * K := by
    have : C ≤ K := hK ▸ le_max_right _ _
    linarith [norm_nonneg Q]
  obtain ⟨hsmall₁, hsmall₂⟩ := small_errors hK0 hL0 hB0 hε hRpos hRLB hQK
  have hδ : 0 ≤ 2 * ε + 2 / R * L * B := by positivity
  have hsmall₁' : (‖Q₁‖ + ‖Q₂‖) * (2 * ε + 2 / R * L * B) < 1 :=
    (mul_le_mul_of_nonneg_right (hK ▸ le_max_left _ _) hδ).trans_lt hsmall₁
  exact bijective_gluedKernelMap_of_lt_one hM₁ hM₂ hι₁ hι₂ (by linarith) h2TR hRpos hL hRL hB0
    hB₁ hB₂ ((memLp_uncurry_gluedCoeff hM₁ hM₂ R).2.mono fun z h ↦ hB ▸ h) (by positivity)
    (ae_norm_uncurry_gluedCoeff_sub_le_left hT₁ hT₂ hε0.le hRpos hRT₁ hRT₂) hQ₁ hQ₂ hQ hR₂₁ hR₂₂
    hsmall₁' hsmall₂

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
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker] :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, FiniteDimensional ℝ (((jetOperator stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker ∧
      finrank ℝ (((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker =
        finrank ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker +
          finrank ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_forall_bijective_gluedKernelMap hM₁ hM₂ h₁ h₂ hι₁ hι₂ hQ₁
    hQ₂ (4 * (‖Q₁‖ + ‖Q₂‖))
  obtain ⟨R₁, hR₁⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff hM₁ hM₂
    h₁ h₂ hι₁ hι₂ hQ₁ hQ₂
  refine ⟨max R₀ R₁, fun R hR ↦ ?_⟩
  obtain ⟨Q, hQ, hQn⟩ := hR₁ R (le_of_max_le_right hR)
  have hr := ContinuousLinearMap.rightInverse_of_comp hQ
  -- The corrected pregluing identifies the kernel `E_R` with `E₁ × E₂`.
  let e := LinearEquiv.ofBijective (gluedKernelMap _ Q hr
    (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
    (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R).toLinearMap
    (hR₀ R (le_of_max_le_left hR) Q hr hQn)
  have := free_ker (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁)
  have := free_ker (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂)
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans Module.finrank_prod⟩

/-- **The exact sequence of linear gluing.** Let `D₁` and `D₂` be first-order operators on the
cylinder with essentially bounded coefficient fields whose ends match, as in
`TauCeti.CylinderSobolev.exists_forall_ge_forall_bijective_gluedKernelMap`, with stabilizers
`ιᵢ : Sᵢ → L²` vanishing near the glued ends, such that the stabilized pieces
`Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` have bounded linear right inverses and finite-dimensional kernels `Eᵢ`.
Fix a bound `C`. For every sufficiently long neck and every right inverse `Q` of norm at most `C`
of the stabilized glued operator `A_R (ξ, σ₁, σ₂) = D_R ξ + j_R (σ₁, σ₂)`, the pregluing corrected
along `Q` is a linear isomorphism `e : E₁ × E₂ ≃ E_R` onto the kernel of `A_R`, and the sequence

`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`

is exact. Its maps are `ξ ↦ e⁻¹ (ξ, 0)`; the **obstruction map** `b_R`, the stabilizer component
`(σ₁, σ₂)` of `e k ∈ E_R` (`TauCeti.CylinderSobolev.gluedObstructionMap`); and
`(σ₁, σ₂) ↦ [j_R (σ₁, σ₂)]`. When `b_R = 0`, the first map is an isomorphism `ker D_R ≃ E₁ × E₂`
and the last one an isomorphism `S₁ × S₂ ≃ coker D_R`.

For stabilizers complementing the ranges of the pieces, such as those of
`exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm`, the kernel
`Eᵢ` is `ker Dᵢ × {0}` (`ContinuousLinearMap.ker_coprod_of_disjoint_range`), and the sequence
reads `0 → ker D_R → ker D₁ × ker D₂ → S₁ × S₂ → coker D_R → 0`. -/
theorem exists_forall_ge_forall_exists_linearEquiv_exact_gluedKernelMap
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W}
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure} {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker]
    [FiniteDimensional ℝ (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker]
    (C : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ (Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂))
      (hQ : Function.RightInverse Q (((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))), ‖Q‖ ≤ C →
      ∃ e : ((((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ×
          (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) ≃ₗ[ℝ]
          (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker,
        (∀ k, e k = gluedKernelMap (((jetOperator stripMeasure
          (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
          (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
          (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R k) ∧
        Function.Injective (e.symm.toLinearMap ∘ₗ (ContinuousLinearMap.kerCoprodHom
          ((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R)).toLinearMap) ∧
        Function.Exact (e.symm.toLinearMap ∘ₗ (ContinuousLinearMap.kerCoprodHom
          ((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R)).toLinearMap)
          (gluedObstructionMap (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
            (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
            (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R).toLinearMap ∧
        Function.Exact (gluedObstructionMap (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
            (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
            (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R).toLinearMap
          (ContinuousLinearMap.parameterToCoker ((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R)) ∧
        Function.Surjective (ContinuousLinearMap.parameterToCoker ((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R)) ∧
        ((gluedObstructionMap (((jetOperator stripMeasure
          (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) Q hQ
          (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
          (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R).toLinearMap = 0 →
          Function.Bijective (e.symm.toLinearMap ∘ₗ (ContinuousLinearMap.kerCoprodHom
            ((jetOperator stripMeasure
              (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
                (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R)).toLinearMap) ∧
          Function.Bijective (ContinuousLinearMap.parameterToCoker ((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL) (gluedStabilizer ι₁ ι₂ R))) := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_forall_bijective_gluedKernelMap hM₁ hM₂ h₁ h₂ hι₁ hι₂ hQ₁
    hQ₂ C
  refine ⟨R₀, fun R hR Q hQ hQn ↦ ?_⟩
  -- The corrected pregluing identifies `E₁ × E₂` with the kernel `E_R` of `A_R`, along which the
  -- exact sequence `0 → ker D_R → E_R → S₁ × S₂ → coker D_R → 0` of the stabilization is
  -- transported.
  let e := LinearEquiv.ofBijective (gluedKernelMap _ Q hQ
    (((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker
    (((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker R).toLinearMap
    (hR₀ R hR Q hQ hQn)
  -- Through `e`, the parameter projection of `E_R` is the obstruction map.
  have hb : (ContinuousLinearMap.parameterProj _ _).toLinearMap ∘ₗ e.toLinearMap =
      (gluedObstructionMap _ Q hQ _ _ R).toLinearMap :=
    LinearMap.ext fun k ↦ by simp [e, gluedObstructionMap]
  exact ⟨e, fun _ ↦ LinearEquiv.ofBijective_apply _ _,
    hb ▸ ContinuousLinearMap.exact_of_linearEquiv_ker_coprod _ _ e hQ.surjective⟩

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
    (hD₁ : ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).IsFredholm ∧
      ((jetOperator stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).index =
        ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).index +
          ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).index := by
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
  set D := (jetOperator stripMeasure
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

end TauCeti.CylinderSobolev
