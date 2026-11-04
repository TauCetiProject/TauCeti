/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Analysis.Calculus.Morse.QuadraticMap
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# A Morse function on real projective space

For weights `w : Fin (n + 1) → ℝ`, the function

`[v] ↦ (∑ⱼ wⱼ vⱼ²) / ∑ⱼ vⱼ²`

on real projective space `ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)` is the standard example of a Morse function
on projective space. When the weights are distinct it is a Morse function whose critical points
are exactly the `n + 1` coordinate points `[eᵢ]`, and the Morse index at `[eᵢ]` is the number of
weights smaller than `wᵢ`. So there is exactly one critical point of each index `0, …, n`.

In the standard affine chart at `i` the function is
`z ↦ (wᵢ + ∑ₖ w_{i.succAbove k} zₖ²) / (1 + ∑ₖ zₖ²)`. Its critical points are found from the
quotient rule: at a critical point `z`, each coordinate satisfies `w_{i.succAbove k} zₖ = f zₖ`,
and summing these against `zₖ` gives `f = wᵢ`, so every coordinate vanishes. For the Hessian at
the origin, the substitution `φ(z) = z / √(1 + ∑ₖ zₖ²)` turns the chart expression into
`wᵢ + ∑ₖ (w_{i.succAbove k} - wᵢ) yₖ²` exactly, and `φ` has derivative the identity at the
origin. The Morse data of this diagonal quadratic form are computed in
`TauCeti.Analysis.Calculus.Morse.QuadraticMap`.

## Main declarations

* `TauCeti.projectiveWeightedSumSquares`: the function `[v] ↦ (∑ⱼ wⱼ vⱼ²) / ∑ⱼ vⱼ²`.
* `TauCeti.projectiveWeightedSumSquares_affineChart_symm`: its expression in the affine charts.
* `TauCeti.contMDiff_projectiveWeightedSumSquares`: it is smooth, indeed analytic.
* `TauCeti.isManifoldNondegenerateCriticalPoint_projectiveWeightedSumSquares` and
  `TauCeti.manifoldMorseIndex_projectiveWeightedSumSquares`: if `wᵢ` differs from the other
  weights, `[eᵢ]` is a nondegenerate critical point of index `#{j | wⱼ < wᵢ}`.
* `TauCeti.criticalPoints_projectiveWeightedSumSquares`: for distinct weights the critical points
  are the coordinate points.
* `TauCeti.isMorse_projectiveWeightedSumSquares`: for distinct weights it is a Morse function.
* `TauCeti.totalCriticalCount_projectiveWeightedSumSquares` and
  `TauCeti.criticalCount_projectiveWeightedSumSquares`: it has `n + 1` critical points, one of each
  index `j ≤ n`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, where the analogous function on complex projective space is studied.
-/

public section

open Function Projectivization Set
open QuadraticMap (polarBilin_apply_apply weightedSumSquares weightedSumSquares_apply)
open scoped ContDiff Manifold LinearAlgebra.Projectivization

noncomputable section

namespace TauCeti

section Def

variable {ι : Type*} [Fintype ι]

/-- The **weighted sum of squares** on real projective space: the function
`[v] ↦ (∑ⱼ wⱼ vⱼ²) / ∑ⱼ vⱼ²`, which is well defined because numerator and denominator are both
homogeneous of degree two. For distinct weights it is a Morse function with the coordinate points as
its critical points (`TauCeti.isMorse_projectiveWeightedSumSquares`). -/
def projectiveWeightedSumSquares (w : ι → ℝ) : ℙ ℝ (ι → ℝ) → ℝ :=
  Projectivization.lift (fun v ↦ (∑ j, w j * v.1 j ^ 2) / ∑ j, v.1 j ^ 2) fun a b t h ↦ by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using h)
    simp only [h, Pi.smul_apply, smul_eq_mul, mul_pow, mul_left_comm (w _), ← Finset.mul_sum]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

/-- The weighted sum of squares in homogeneous coordinates. -/
@[simp]
theorem projectiveWeightedSumSquares_mk (w : ι → ℝ) (v : ι → ℝ) (hv : v ≠ 0) :
    projectiveWeightedSumSquares w (mk ℝ v hv) = (∑ j, w j * v j ^ 2) / ∑ j, v j ^ 2 :=
  Projectivization.lift_mk _ _ v hv

end Def

variable {n : ℕ} (w : Fin (n + 1) → ℝ)

/-- In the standard affine chart at `i`, the weighted sum of squares is
`z ↦ (wᵢ + ∑ₖ w_{i.succAbove k} zₖ²) / (1 + ∑ₖ zₖ²)`. -/
theorem projectiveWeightedSumSquares_affineChart_symm (i : Fin (n + 1)) (z : Fin n → ℝ) :
    projectiveWeightedSumSquares w ((affineChart i).symm z) =
      (w i + ∑ k, w (i.succAbove k) * z k ^ 2) / (1 + ∑ k, z k ^ 2) := by
  simp [Fin.sum_univ_succAbove _ i]

/-! ### The chart expression -/

section Chart

/-- The sum of squares `z ↦ ∑ₖ zₖ²` on `Fin n → ℝ`, as a diagonal quadratic form. -/
private abbrev sumSq (n : ℕ) : QuadraticMap ℝ (Fin n → ℝ) ℝ :=
  weightedSumSquares ℝ (1 : Fin n → ℝ)

private theorem one_add_sumSquares_pos (z : Fin n → ℝ) : 0 < 1 + sumSq n z := by
  have : 0 ≤ sumSq n z := by
    rw [sumSq, weightedSumSquares_apply]
    exact Finset.sum_nonneg fun k _ ↦ by simpa using mul_self_nonneg (z k)
  linarith

/-- The weighted sum of squares, read in the affine chart at `i`, is the quotient
`z ↦ (wᵢ + P z) / (1 + N z)` of the diagonal forms `P` and `N` with weights `w ∘ i.succAbove`
and `1`. -/
private theorem projectiveWeightedSumSquares_comp_affineChart_symm (i : Fin (n + 1)) :
    projectiveWeightedSumSquares w ∘ (affineChart i).symm = fun z ↦
      (w i + weightedSumSquares ℝ (fun k ↦ w (i.succAbove k)) z) / (1 + sumSq n z) := by
  funext z
  rw [comp_apply, projectiveWeightedSumSquares_affineChart_symm]
  simp [sumSq, weightedSumSquares_apply, _root_.sq]

/-- The chart expression `z ↦ (c + P z) / (1 + N z)` is smooth. -/
private theorem contDiff_chartQuotient (b : Fin n → ℝ) (c : ℝ) {r : ℕ∞ω} :
    ContDiff ℝ r fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + sumSq n z) :=
  (contDiff_const.add (weightedSumSquares ℝ b).contDiff).div
    (contDiff_const.add (sumSq n).contDiff) fun z ↦ (one_add_sumSquares_pos z).ne'

/-- **Critical points in a chart.** If no weight `bₖ` equals `c`, the only critical point of
`g(z) = (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` is the origin. Differentiating `g · (1 + N) = c + P`
gives `bₖ zₖ = g(z) zₖ` at a critical point, and summing these against `zₖ` shows `g(z) = c`. -/
private theorem eq_zero_of_fderiv_chartQuotient_eq_zero {b : Fin n → ℝ} {c : ℝ}
    (hb : ∀ k, b k ≠ c) {z : Fin n → ℝ}
    (hz : fderiv ℝ (fun y ↦ (c + weightedSumSquares ℝ b y) / (1 + sumSq n y)) z = 0) :
    z = 0 := by
  set P := weightedSumSquares ℝ b
  set N := sumSq n
  set g := fun y ↦ (c + P y) / (1 + N y) with hg_def
  have hD (y : Fin n → ℝ) := (one_add_sumSquares_pos y).ne'
  have hg : HasFDerivAt g (0 : (Fin n → ℝ) →L[ℝ] ℝ) z := by
    rw [← hz]
    exact ((contDiff_chartQuotient b c (r := 1)).differentiable one_ne_zero z).hasFDerivAt
  -- Differentiating `g * (1 + N) = c + P` at `z` gives `P'(z) = g(z) • N'(z)`.
  have hprod : HasFDerivAt (fun y ↦ c + P y) (g z • fderiv ℝ N z) z := by
    have h := hg.mul ((N.hasFDerivAt z).const_add 1)
    rw [smul_zero, add_zero] at h
    convert h using 1
    · funext y
      exact (div_mul_cancel₀ _ (hD y)).symm
    · simp [(N.hasFDerivAt z).fderiv]
  -- On a basis vector, the derivative of a diagonal form is twice its associated bilinear form.
  have hpolar (a : Fin n → ℝ) (k : Fin n) :
      fderiv ℝ (weightedSumSquares ℝ a) z (Pi.single k 1) = 2 * (a k * z k) := by
    have h := congrArg (fun B ↦ B z (Pi.single k 1))
      (QuadraticMap.two_nsmul_associated ℝ (weightedSumSquares ℝ a))
    simp only [LinearMap.smul_apply, polarBilin_apply_apply,
      QuadraticMap.associated_weightedSumSquares] at h
    rw [QuadraticMap.fderiv_apply, ← h]
    simp [Pi.single_apply]
  have hcoord (k : Fin n) : b k * z k = g z * z k := by
    have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L (Pi.single k 1))
      ((P.hasFDerivAt z).const_add c |>.unique hprod)
    simp only [← (P.hasFDerivAt z).fderiv, smul_apply, smul_eq_mul, P, N, sumSq, hpolar,
      Pi.one_apply, one_mul] at h
    linarith
  -- Summing `bₖ zₖ² = g(z) zₖ²` gives `P z = g(z) N z`, hence `g(z) = c`.
  have hsum : P z = g z * N z := by
    simp only [P, N, sumSq, weightedSumSquares_apply, smul_eq_mul, Pi.one_apply, one_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_assoc, hcoord k, mul_assoc]
  have hgc : g z = c := by
    have h : g z * (1 + N z) = c + P z := div_mul_cancel₀ _ (hD z)
    rw [hsum] at h
    linarith
  funext k
  have h := hcoord k
  rw [hgc] at h
  exact (mul_eq_zero.1 (by linarith : (b k - c) * z k = 0)).resolve_left (sub_ne_zero.2 (hb k))

/-- The substitution `φ(z) = z / √(1 + ∑ₖ zₖ²)`, which carries the chart expression onto a constant
plus a diagonal quadratic form. -/
private def chartSubstitution (z : Fin n → ℝ) : Fin n → ℝ :=
  (√(1 + sumSq n z))⁻¹ • z

private theorem contDiff_chartSubstitution_scale {r : ℕ∞ω} :
    ContDiff ℝ r fun z : Fin n → ℝ ↦ (√(1 + sumSq n z))⁻¹ :=
  ((contDiff_const.add (sumSq n).contDiff).sqrt
    fun z ↦ (one_add_sumSquares_pos z).ne').inv
      fun z ↦ (Real.sqrt_pos.2 (one_add_sumSquares_pos z)).ne'

private theorem contDiff_chartSubstitution {r : ℕ∞ω} :
    ContDiff ℝ r (chartSubstitution (n := n)) :=
  contDiff_chartSubstitution_scale.smul contDiff_id

private theorem chartSubstitution_zero : chartSubstitution (0 : Fin n → ℝ) = 0 := by
  simp [chartSubstitution]

/-- The substitution `φ` has derivative the identity at the origin. -/
private theorem fderiv_chartSubstitution_zero :
    fderiv ℝ (chartSubstitution (n := n)) 0 = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  have h := ((contDiff_chartSubstitution_scale (r := 1)).differentiable one_ne_zero
    0).hasFDerivAt.smul (hasFDerivAt_id (𝕜 := ℝ) (0 : Fin n → ℝ))
  refine h.fderiv.trans ?_
  ext v
  simp

/-- After the substitution `φ`, the chart expression `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` is the
constant `c` plus the diagonal form with weights `bₖ - c`. -/
private theorem chartQuotient_eq_comp_chartSubstitution (b : Fin n → ℝ) (c : ℝ) :
    (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + sumSq n z)) =
      (fun y ↦ weightedSumSquares ℝ (fun k ↦ b k - c) y + c) ∘ chartSubstitution := by
  funext z
  have hD := one_add_sumSquares_pos z
  have hsq : (√(1 + sumSq n z))⁻¹ * (√(1 + sumSq n z))⁻¹ = (1 + sumSq n z)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hD.le]
  have hsplit :
      weightedSumSquares ℝ (fun k ↦ b k - c) z = weightedSumSquares ℝ b z - c * sumSq n z := by
    simp only [sumSq, weightedSumSquares_apply, smul_eq_mul, Pi.one_apply, one_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [comp_apply, chartSubstitution, QuadraticMap.map_smul, smul_eq_mul, hsq, hsplit]
  field_simp
  ring

/-- **The origin of a chart.** If no weight `bₖ` equals `c`, the origin is a nondegenerate critical
point of `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)`, of Morse index `#{k | bₖ < c}`. -/
private theorem isNondegenerateCriticalPoint_chartQuotient {b : Fin n → ℝ} {c : ℝ}
    (hb : ∀ k, b k ≠ c) :
    IsNondegenerateCriticalPoint
        (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + sumSq n z)) 0 ∧
      morseIndex (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + sumSq n z)) 0 =
        {k | b k < c}.ncard := by
  set Q := weightedSumSquares ℝ (fun k ↦ b k - c)
  have hQ : ContDiffAt ℝ 2 (fun y ↦ Q y + c) (chartSubstitution 0) :=
    (Q.contDiff.add contDiff_const).contDiffAt
  have hφ : ContDiffAt ℝ 2 (chartSubstitution (n := n)) 0 := contDiff_chartSubstitution.contDiffAt
  have hinv : (fderiv ℝ (chartSubstitution (n := n)) 0).IsInvertible := by
    rw [fderiv_chartSubstitution_zero]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hfd : fderiv ℝ (fun y ↦ Q y + c) = fderiv ℝ Q := funext fun _ ↦ fderiv_add_const c
  have hnd : IsNondegenerateCriticalPoint Q 0 :=
    (QuadraticMap.isNondegenerateCriticalPoint_zero_iff Q).2 <|
      QuadraticMap.nondegenerate_weightedSumSquares fun k ↦
        isRegular_iff_ne_zero.2 (sub_ne_zero.2 (hb k))
  rw [chartQuotient_eq_comp_chartSubstitution]
  refine ⟨(isNondegenerateCriticalPoint_comp_iff hQ hφ hinv).2 ?_, ?_⟩
  · rw [chartSubstitution_zero, isNondegenerateCriticalPoint_add_const_iff]
    exact hnd
  · have hcrit : fderiv ℝ (fun y ↦ Q y + c) (chartSubstitution 0) = 0 := by
      rw [hfd, chartSubstitution_zero]
      exact hnd.fderiv_eq_zero
    have hhess : hessianQuadraticForm (fun y ↦ Q y + c) 0 = hessianQuadraticForm Q 0 := by
      ext v
      simp only [hessianQuadraticForm_apply, hfd]
    rw [morseIndex_comp hQ hφ hcrit hinv, chartSubstitution_zero, morseIndex_def, hhess,
      ← morseIndex_def, QuadraticMap.morseIndex_eq_sigNeg,
      QuadraticForm.sigNeg_weightedSumSquares]
    simp only [sub_neg]

end Chart

/-! ### Smoothness and critical points -/

/-- The weighted sum of squares on real projective space is smooth, indeed analytic. -/
theorem contMDiff_projectiveWeightedSumSquares {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) r (projectiveWeightedSumSquares w) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hchart : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) r
      ((projectiveWeightedSumSquares w ∘ (affineChart i).symm) ∘ affineChart i) (affineOpen i) := by
    rw [projectiveWeightedSumSquares_comp_affineChart_symm]
    exact (contDiff_chartQuotient _ _).contMDiff.comp_contMDiffOn (contMDiffOn_affineChart i r)
  refine ((hchart.congr fun y hy ↦ ?_).contMDiffAt ((isOpen_affineOpen i).mem_nhds hi))
  simp [(affineChart i).left_inv (by simpa using hy)]

variable {w}

/-- **The coordinate points are nondegenerate critical points.** If the weight `wᵢ` differs from
all the other weights, the coordinate point `[eᵢ]` is a nondegenerate critical point of the
weighted sum of squares. -/
theorem isManifoldNondegenerateCriticalPoint_projectiveWeightedSumSquares {i : Fin (n + 1)}
    (hw : ∀ j, j ≠ i → w j ≠ w i) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w)
      (mk ℝ (Pi.single i 1) (by simp)) := by
  have h := isManifoldNondegenerateCriticalPoint_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := 2)
      (affineOpenPartialHomeomorph_mem_atlas i)) (f := projectiveWeightedSumSquares w)
    (v := 0) (by simp)
  simp only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, comp_id,
    coe_affineOpenPartialHomeomorph_symm, comp_apply, id_eq, affineChart_symm_zero] at h
  rw [projectiveWeightedSumSquares_comp_affineChart_symm] at h
  exact h (isNondegenerateCriticalPoint_chartQuotient fun k ↦ hw _ (Fin.succAbove_ne i k)).1

/-- **The Morse index of a coordinate point.** If the weight `wᵢ` differs from all the other
weights, the Morse index of the weighted sum of squares at the coordinate point `[eᵢ]` is the number
of weights smaller than `wᵢ`. -/
theorem manifoldMorseIndex_projectiveWeightedSumSquares {i : Fin (n + 1)}
    (hw : ∀ j, j ≠ i → w j ≠ w i) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w)
      (mk ℝ (Pi.single i 1) (by simp)) = {j | w j < w i}.ncard := by
  have hb := isNondegenerateCriticalPoint_chartQuotient fun k ↦ hw _ (Fin.succAbove_ne i k)
  rw [← projectiveWeightedSumSquares_comp_affineChart_symm] at hb
  have h := manifoldMorseIndex_symm_eq_morseIndex_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := 2)
      (affineOpenPartialHomeomorph_mem_atlas i)) (f := projectiveWeightedSumSquares w)
    (v := 0) (by simp) (by simpa using hb.1)
  simp only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, comp_id,
    coe_affineOpenPartialHomeomorph_symm, comp_apply, id_eq, affineChart_symm_zero] at h
  rw [h, hb.2]
  -- The weights below `wᵢ` are the weights `w (i.succAbove k)` below `wᵢ`.
  have himage : {j | w j < w i} = i.succAbove '' {k | w (i.succAbove k) < w i} := by
    ext j
    cases j using Fin.succAboveCases i with
    | x => simp [Fin.succAbove_ne]
    | p k => simp [Fin.succAbove_right_injective.eq_iff]
  rw [himage, ncard_image_of_injective _ Fin.succAbove_right_injective]

/-- **The critical points are the coordinate points.** For distinct weights, the critical points of
the weighted sum of squares on real projective space are exactly the `n + 1` coordinate points
`[eᵢ]`. -/
theorem criticalPoints_projectiveWeightedSumSquares (hw : Injective w) :
    criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) =
      range fun i ↦ mk ℝ (Pi.single i 1) (by simp) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨i, hi⟩ := exists_mem_affineOpen x
    have hsrc : x ∈ (affineOpenPartialHomeomorph (K := ℝ) i).source := by simpa using hi
    have hcrit := (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.subset_maximalAtlas (n := 1) (affineOpenPartialHomeomorph_mem_atlas i)) hsrc
      ((contMDiff_projectiveWeightedSumSquares w (r := 1) x).mdifferentiableAt one_ne_zero)).1
      (mem_criticalPoints.1 hx)
    simp only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, comp_id,
      coe_affineOpenPartialHomeomorph_symm, OpenPartialHomeomorph.extend_coe,
      modelWithCornersSelf_coe, id_comp, coe_affineOpenPartialHomeomorph,
      projectiveWeightedSumSquares_comp_affineChart_symm] at hcrit
    have hz := eq_zero_of_fderiv_chartQuotient_eq_zero
      (fun k ↦ hw.ne (Fin.succAbove_ne i k)) hcrit
    refine ⟨i, ?_⟩
    dsimp only
    rw [← affineChart_symm_zero, ← hz, (affineChart i).left_inv (by simpa using hi)]
  · rintro ⟨i, rfl⟩
    exact (isManifoldNondegenerateCriticalPoint_projectiveWeightedSumSquares
      fun j hj ↦ hw.ne hj).mem_criticalPoints

/-- **The weighted sum of squares is a Morse function** on real projective space when the weights
are distinct. -/
theorem isMorse_projectiveWeightedSumSquares (hw : Injective w) :
    IsMorse 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints,
    criticalPoints_projectiveWeightedSumSquares hw]
  refine ⟨(contMDiff_projectiveWeightedSumSquares w).contMDiffOn, ?_⟩
  rintro _ - ⟨i, rfl⟩
  exact isManifoldNondegenerateCriticalPoint_projectiveWeightedSumSquares fun j hj ↦ hw.ne hj

/-! ### Counting critical points -/

/-- For distinct weights, the weighted sum of squares on `ℝℙⁿ` has `n + 1` critical points. -/
theorem totalCriticalCount_projectiveWeightedSumSquares (hw : Injective w) :
    totalCriticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) = n + 1 := by
  rw [totalCriticalCount_def, criticalPoints_projectiveWeightedSumSquares hw,
    ← image_univ, injective_mk_single.encard_image, encard_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]
  rfl

/-- For distinct weights, the weighted sum of squares on `ℝℙⁿ` has exactly one critical point of
each index `j ≤ n`, and none of larger index. -/
theorem criticalCount_projectiveWeightedSumSquares (hw : Injective w) (j : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) j =
      if j ≤ n then 1 else 0 := by
  -- Sorting the weights by `σ`, the coordinate point `[e_{σ m}]` has index `m`.
  set σ := Tuple.sort w
  have hmono : StrictMono (w ∘ σ) :=
    (Tuple.monotone_sort w).strictMono_of_injective (hw.comp σ.injective)
  have hrank (m : Fin (n + 1)) : {l | w l < w (σ m)}.ncard = m := by
    have h : {l | w l < w (σ m)} = σ '' Iio m := by
      ext l
      obtain ⟨l, rfl⟩ := σ.surjective l
      simp only [mem_ofPred_eq, mem_image, mem_Iio, σ.injective.eq_iff, exists_eq_right]
      exact hmono.lt_iff_lt
    rw [h, ncard_image_of_injective _ σ.injective, ncard_eq_toFinset_card', toFinset_Iio,
      Fin.card_Iio]
  have hset : {x ∈ criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) |
      manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w) x = j} =
      (fun i ↦ mk ℝ (Pi.single i 1 : Fin (n + 1) → ℝ) (by simp)) '' (σ '' {m | (m : ℕ) = j}) := by
    rw [criticalPoints_projectiveWeightedSumSquares hw]
    ext x
    simp only [mem_ofPred_eq, mem_range, mem_image]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      obtain ⟨m, rfl⟩ := σ.surjective i
      rw [manifoldMorseIndex_projectiveWeightedSumSquares fun l hl ↦ hw.ne hl, hrank] at hi
      exact ⟨σ m, ⟨m, hi, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨⟨σ m, rfl⟩, by
        rw [manifoldMorseIndex_projectiveWeightedSumSquares fun l hl ↦ hw.ne hl, hrank, hm]⟩
  rw [criticalCount_def, hset, injective_mk_single.encard_image, σ.injective.encard_image]
  split_ifs with hj
  · rw [encard_eq_one]
    exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, by ext m; simp [Fin.ext_iff]⟩
  · rw [encard_eq_zero, eq_empty_iff_forall_notMem]
    intro m hm
    exact hj (hm ▸ Nat.le_of_lt_succ m.2)

end TauCeti
