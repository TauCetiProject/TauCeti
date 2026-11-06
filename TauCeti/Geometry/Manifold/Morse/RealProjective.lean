/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Analysis.Calculus.Morse.Pi
import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The weighted Rayleigh quotient on real projective space

For real weights `w : Fin (n + 1) → ℝ`, the **weighted Rayleigh quotient**

`projectiveRayleighQuotient w [v] = (∑ j, w j * v j ^ 2) / ∑ j, v j ^ 2`

is the Rayleigh quotient of the diagonal quadratic form with weights `w`, which is invariant under
scaling and so is a function on real projective space `ℝℙⁿ = ℙ ℝ (Fin (n + 1) → ℝ)`, with its
standard smooth structure of affine charts. It is the standard Morse function on `ℝℙⁿ`: for
`n = 2` and the weights `0, 1, 2` it is `[x : y : z] ↦ (y² + 2z²) / (x² + y² + z²)`.

Its critical points are the lines spanned by eigenvectors of the diagonal form: `[v]` is critical
exactly when every nonzero coordinate `v j` carries the weight `w j` equal to the value at `[v]`.
At the coordinate point `[eᵢ]` the function takes the value `w i`. In the affine chart at `i`, with
`ρ(z) = 1 + ∑ₖ zₖ²`, it is

`w i + ∑ₖ (w (i.succAbove k) - w i) * (zₖ / √ρ(z))²`,

and `z ↦ z / √ρ(z)` is a change of coordinates fixing `0` with identity derivative there. So
`[eᵢ]` is nondegenerate exactly when the weight `w i` is simple, and then its Morse index is the
number of weights below `w i`. The function is Morse exactly when the weights are distinct, and then
it has one critical point of each index `0, …, n`.

## Main declarations

* `TauCeti.projectiveRayleighQuotient`: the weighted Rayleigh quotient on `ℝℙⁿ`, with its values
  in homogeneous coordinates `TauCeti.projectiveRayleighQuotient_mk` and in the affine charts
  `TauCeti.projectiveRayleighQuotient_affineChart_symm`.
* `TauCeti.contMDiff_projectiveRayleighQuotient`: it is smooth, indeed analytic.
* `TauCeti.mk_mem_criticalPoints_projectiveRayleighQuotient_iff`: its critical points are the
  eigenlines of the diagonal form.
* `TauCeti.isManifoldNondegenerateCriticalPoint_projectiveRayleighQuotient_mk_single_iff` and
  `TauCeti.manifoldMorseIndex_projectiveRayleighQuotient_mk_single`: nondegeneracy and Morse
  index at a coordinate point.
* `TauCeti.isMorse_projectiveRayleighQuotient_iff`: it is Morse exactly when the weights are
  distinct.
* `TauCeti.criticalPoints_projectiveRayleighQuotient`,
  `TauCeti.totalCriticalCount_projectiveRayleighQuotient` and
  `TauCeti.criticalCount_projectiveRayleighQuotient`: for distinct weights the critical points are
  the `n + 1` coordinate points, one of each index `j ≤ n`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 6, where the analogous function `∑ cⱼ |zⱼ|²` on complex projective space is treated.
-/

public section

open Set Function Filter Topology Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace TauCeti

variable {n : ℕ} (w : Fin (n + 1) → ℝ)

/-- **The weighted Rayleigh quotient on real projective space**: the function
`[v] ↦ (∑ j, w j * v j ^ 2) / ∑ j, v j ^ 2` on `ℙ ℝ (Fin (n + 1) → ℝ)`, the Rayleigh quotient of
the diagonal quadratic form with weights `w`. -/
noncomputable def projectiveRayleighQuotient : ℙ ℝ (Fin (n + 1) → ℝ) → ℝ :=
  Projectivization.lift (fun v ↦ (∑ j, w j * v.1 j ^ 2) / ∑ j, v.1 j ^ 2) fun a b t h ↦ by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using h)
    simp only [h, Pi.smul_apply, smul_eq_mul, mul_pow, mul_left_comm (w _), ← Finset.mul_sum]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

/-- The weighted Rayleigh quotient in homogeneous coordinates. -/
@[simp]
theorem projectiveRayleighQuotient_mk (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) :
    projectiveRayleighQuotient w (mk ℝ v hv) = (∑ j, w j * v j ^ 2) / ∑ j, v j ^ 2 :=
  (rfl)

/-- **The weighted Rayleigh quotient in an affine chart.** At the point `[Fin.insertNth i 1 z]`
it is `(w i + ∑ₖ w (i.succAbove k) * zₖ²) / (1 + ∑ₖ zₖ²)`. -/
theorem projectiveRayleighQuotient_affineChart_symm (i : Fin (n + 1)) (z : Fin n → ℝ) :
    projectiveRayleighQuotient w ((affineChart i).symm z) =
      (w i + ∑ k, w (i.succAbove k) * z k ^ 2) / (1 + ∑ k, z k ^ 2) := by
  rw [affineChart_symm_apply, projectiveRayleighQuotient_mk, Fin.sum_univ_succAbove _ i,
    Fin.sum_univ_succAbove _ i]
  simp

/-- The value of the weighted Rayleigh quotient at the coordinate point `[eᵢ]` is `w i`. -/
theorem projectiveRayleighQuotient_mk_single (i : Fin (n + 1)) :
    projectiveRayleighQuotient w (mk ℝ (Pi.single i 1) (Pi.single_ne_zero_iff.2 one_ne_zero)) =
      w i := by
  simp [Pi.single_apply]

/-- The denominator `1 + ∑ₖ zₖ²` of the weighted Rayleigh quotient in an affine chart is
positive. -/
private theorem one_add_sum_sq_pos (z : Fin n → ℝ) : 0 < 1 + ∑ k, z k ^ 2 := by
  positivity

/-- **The weighted Rayleigh quotient is smooth**, indeed analytic. -/
theorem contMDiff_projectiveRayleighQuotient (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) r (projectiveRayleighQuotient w) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  -- On the affine open at `i` the function factors through the affine chart at `i`.
  have hg : ContDiff ℝ r fun z : Fin n → ℝ ↦
      (w i + ∑ k, w (i.succAbove k) * z k ^ 2) / (1 + ∑ k, z k ^ 2) :=
    ContDiff.div (by fun_prop) (by fun_prop) fun z ↦ (one_add_sum_sq_pos z).ne'
  have hchart : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) r (affineChart i) x :=
    (contMDiffOn_affineChart i r).contMDiffAt ((isOpen_affineOpen i).mem_nhds hi)
  refine ContMDiffAt.congr_of_eventuallyEq (hg.contMDiff.contMDiffAt.comp x hchart) ?_
  filter_upwards [(isOpen_affineOpen i).mem_nhds hi] with y hy
  rw [comp_apply, ← projectiveRayleighQuotient_affineChart_symm,
    (affineChart i).left_inv (by simpa using hy)]

/-- The derivative of a sum of weighted squares of the coordinates. -/
private theorem hasFDerivAt_sum_mul_sq (a : Fin n → ℝ) (z : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ ↦ ∑ k, a k * z k ^ 2)
      (∑ k, (2 * a k * z k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) k) z := by
  refine HasFDerivAt.fun_sum fun k _ ↦ ?_
  refine (((hasDerivAt_pow 2 (z k)).const_mul (a k)).comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) k z)).congr_fderiv ?_
  ext u
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- **Critical points in an affine chart.** The differential of the coordinate expression of the
weighted Rayleigh quotient in the affine chart at `i` vanishes at `z` exactly when every
coordinate `zₖ` is zero or carries the weight equal to the value at `z`. -/
private theorem fderiv_affineChart_symm_eq_zero_iff (i : Fin (n + 1)) (z : Fin n → ℝ) :
    fderiv ℝ (projectiveRayleighQuotient w ∘ (affineChart i).symm) z = 0 ↔
      ∀ k, z k = 0 ∨ w (i.succAbove k) = projectiveRayleighQuotient w ((affineChart i).symm z) := by
  obtain ⟨g, hgdef⟩ : ∃ g, g = projectiveRayleighQuotient w ∘ (affineChart i).symm := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : (Fin n → ℝ) → ℝ, s = fun z ↦ 1 + ∑ k, z k ^ 2 := ⟨_, rfl⟩
  rw [← hgdef]
  have hgs (y : Fin n → ℝ) : g y * s y = w i + ∑ k, w (i.succAbove k) * y k ^ 2 := by
    simp only [hgdef, hsdef, comp_apply]
    rw [projectiveRayleighQuotient_affineChart_symm, div_mul_cancel₀ _ (one_add_sum_sq_pos y).ne']
  have hgd : DifferentiableAt ℝ g z := by
    have := (contMDiff_projectiveRayleighQuotient w 1).comp
      (contMDiff_affineChart_symm (𝕜 := ℝ) i 1)
    exact hgdef ▸ (this.contDiff.differentiable one_ne_zero) z
  have hs : HasFDerivAt s
      (∑ k, (2 * 1 * z k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) k) z := by
    simpa [hsdef] using (hasFDerivAt_sum_mul_sq (fun _ ↦ 1) z).const_add 1
  have hN := (hasFDerivAt_sum_mul_sq (fun k ↦ w (i.succAbove k)) z).const_add (w i)
  -- Differentiating `g * s = N` determines the derivative of `g`.
  have hprod := hgd.hasFDerivAt.mul hs
  rw [show g * s = fun y ↦ w i + ∑ k, w (i.succAbove k) * y k ^ 2 from funext hgs] at hprod
  have heq := hN.unique hprod
  -- Evaluating both derivatives on the basis vector `eₖ`.
  have hcoord (k : Fin n) : 2 * w (i.succAbove k) * z k =
      g z * (2 * 1 * z k) + s z * fderiv ℝ g z (Pi.single k 1) := by
    simpa [Pi.single_apply] using congrArg (fun L ↦ L (Pi.single k (1 : ℝ))) heq
  have hg : g z = projectiveRayleighQuotient w ((affineChart i).symm z) := by
    rw [hgdef, comp_apply]
  have hspos : 0 < s z := by
    rw [hsdef]
    exact one_add_sum_sq_pos z
  constructor
  · intro h k
    have hD : fderiv ℝ g z (Pi.single k 1) = 0 := by simp [h]
    have : 2 * z k * (w (i.succAbove k) - g z) = 0 := by
      linear_combination hcoord k + s z * hD
    rcases mul_eq_zero.1 this with h0 | h0
    · exact Or.inl (by linarith)
    · exact Or.inr (hg ▸ sub_eq_zero.1 h0)
  · intro h
    refine ContinuousLinearMap.ext fun u ↦ ?_
    have hu : u = ∑ k, u k • Pi.single k (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hu, map_sum]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul]
    have hk := hcoord k
    have : s z * fderiv ℝ g z (Pi.single k 1) = 0 := by
      rcases h k with h0 | h0
      · rw [h0] at hk
        linear_combination -hk
      · linear_combination -hk + 2 * z k * h0 - 2 * z k * hg
    rw [(mul_eq_zero.1 this).resolve_left hspos.ne', smul_zero]

/-- **Euler's relation in an affine chart.** If every coordinate `zₖ` is zero or carries the
weight equal to the value at `z`, then that value is the weight `w i` of the chart. -/
private theorem eq_projectiveRayleighQuotient_affineChart_symm (i : Fin (n + 1))
    {z : Fin n → ℝ}
    (h : ∀ k, z k = 0 ∨ w (i.succAbove k) = projectiveRayleighQuotient w ((affineChart i).symm z)) :
    w i = projectiveRayleighQuotient w ((affineChart i).symm z) := by
  set c := projectiveRayleighQuotient w ((affineChart i).symm z) with hcdef
  have hc : c * (1 + ∑ k, z k ^ 2) = w i + ∑ k, w (i.succAbove k) * z k ^ 2 := by
    rw [hcdef, projectiveRayleighQuotient_affineChart_symm,
      div_mul_cancel₀ _ (one_add_sum_sq_pos z).ne']
  have hsum : ∑ k, w (i.succAbove k) * z k ^ 2 = ∑ k, c * z k ^ 2 :=
    Finset.sum_congr rfl fun k _ ↦ by rcases h k with h0 | h0 <;> simp [h0]
  rw [hsum, ← Finset.mul_sum, mul_add, mul_one] at hc
  linarith

/-- **Critical points of the weighted Rayleigh quotient.** A point `[v]` of real projective space
is a critical point exactly when `v` is an eigenvector of the diagonal form: every nonzero
coordinate `v j` carries the weight `w j` equal to the value at `[v]`. -/
theorem mk_mem_criticalPoints_projectiveRayleighQuotient_iff {v : Fin (n + 1) → ℝ} (hv : v ≠ 0) :
    mk ℝ v hv ∈ criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) ↔
      ∀ j, v j = 0 ∨ w j = projectiveRayleighQuotient w (mk ℝ v hv) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [Pi.zero_apply] at hi
  have hx : mk ℝ v hv ∈ (affineOpenPartialHomeomorph (K := ℝ) i).source := by
    simpa using (mk_mem_affineOpen_iff i v hv).2 hi
  have hsymm : (affineChart i).symm (affineChart i (mk ℝ v hv)) = mk ℝ v hv :=
    (affineChart i).left_inv (by simpa using hx)
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    (affineOpenPartialHomeomorph_mem_maximalAtlas i 1) hx
    ((contMDiff_projectiveRayleighQuotient w 1).mdifferentiableAt one_ne_zero),
    affineOpenPartialHomeomorph_extend, fderiv_affineChart_symm_eq_zero_iff, hsymm,
    Fin.forall_iff_succAbove i]
  simp only [affineChart_mk, div_eq_zero_iff, hi, or_false]
  refine ⟨fun h ↦ ⟨Or.inr ?_, h⟩, fun h ↦ h.2⟩
  have := eq_projectiveRayleighQuotient_affineChart_symm w i (z := affineChart i (mk ℝ v hv))
  rw [hsymm] at this
  refine this fun k ↦ ?_
  simpa [affineChart_mk, hi] using h k

/-- The coordinate point `[eᵢ]` is a critical point of the weighted Rayleigh quotient. -/
theorem mk_single_mem_criticalPoints_projectiveRayleighQuotient (i : Fin (n + 1)) :
    mk ℝ (Pi.single i 1) (Pi.single_ne_zero_iff.2 one_ne_zero) ∈
      criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) := by
  rw [mk_mem_criticalPoints_projectiveRayleighQuotient_iff, projectiveRayleighQuotient_mk_single]
  intro j
  rcases eq_or_ne j i with rfl | hj
  · exact Or.inr rfl
  · exact Or.inl (Pi.single_eq_of_ne hj 1)

/-! ### The coordinate expression at a coordinate point -/

/-- The change of coordinates `z ↦ z / √(1 + ∑ₖ zₖ²)` which turns the weighted Rayleigh quotient in
an affine chart into a diagonal quadratic form. -/
private noncomputable def ballCoord (z : Fin n → ℝ) : Fin n → ℝ :=
  (√(1 + ∑ k, z k ^ 2))⁻¹ • z

private theorem contDiff_ballCoord : ContDiff ℝ 2 (ballCoord (n := n)) := by
  have h : ContDiff ℝ 2 fun z : Fin n → ℝ ↦ √(1 + ∑ k, z k ^ 2) :=
    ContDiff.sqrt (by fun_prop) fun z ↦ (one_add_sum_sq_pos z).ne'
  exact (h.inv fun z ↦ (Real.sqrt_pos.2 (one_add_sum_sq_pos z)).ne').smul contDiff_id

@[simp]
private theorem ballCoord_zero : ballCoord (0 : Fin n → ℝ) = 0 := by
  simp [ballCoord]

private theorem hasFDerivAt_ballCoord_zero :
    HasFDerivAt (ballCoord (n := n)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 := by
  have hc : DifferentiableAt ℝ (fun z : Fin n → ℝ ↦ (√(1 + ∑ k, z k ^ 2))⁻¹) 0 :=
    (DifferentiableAt.sqrt (by fun_prop) (by simp)).inv (by simp)
  refine (hc.hasFDerivAt.smul (hasFDerivAt_id (0 : Fin n → ℝ))).congr_fderiv ?_
  ext u j
  simp

private theorem isInvertible_fderiv_ballCoord_zero :
    (fderiv ℝ (ballCoord (n := n)) 0).IsInvertible := by
  rw [hasFDerivAt_ballCoord_zero.fderiv]
  exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

/-- The summands `s ↦ c * s ^ 2` of the diagonal quadratic form
`∑ₖ (w (i.succAbove k) - w i) * yₖ²`, viewed as a separated sum. -/
private theorem contDiffAt_sq_mul (c t : ℝ) : ContDiffAt ℝ 2 (fun s : ℝ ↦ c * s ^ 2) t := by
  fun_prop

private theorem deriv_sq_mul (c : ℝ) : deriv (fun s : ℝ ↦ c * s ^ 2) = fun s ↦ 2 * c * s := by
  funext s
  rw [((hasDerivAt_pow 2 s).const_mul c).deriv]
  ring

private theorem deriv_sq_mul_zero (c : ℝ) : deriv (fun s : ℝ ↦ c * s ^ 2) 0 = 0 := by
  simp only [deriv_sq_mul, mul_zero]

private theorem deriv_deriv_sq_mul_zero (c : ℝ) :
    deriv (deriv fun s : ℝ ↦ c * s ^ 2) 0 = 2 * c := by
  rw [deriv_sq_mul, ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * c)).deriv, mul_one]

/-- **The weighted Rayleigh quotient in the affine chart at `i`, in ball coordinates.** -/
private theorem projectiveRayleighQuotient_comp_affineChart_symm_eq (i : Fin (n + 1)) :
    projectiveRayleighQuotient w ∘ (affineChart i).symm =
      fun z ↦ (∑ k, (w (i.succAbove k) - w i) * ballCoord z k ^ 2) + w i := by
  funext z
  have hs := one_add_sum_sq_pos z
  rw [comp_apply, projectiveRayleighQuotient_affineChart_symm, div_eq_iff hs.ne']
  simp only [ballCoord, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow,
    Real.sq_sqrt hs.le]
  have hsum : ∑ k, (w (i.succAbove k) - w i) * ((1 + ∑ l, z l ^ 2)⁻¹ * z k ^ 2) =
      (1 + ∑ l, z l ^ 2)⁻¹ * (∑ k, w (i.succAbove k) * z k ^ 2 - w i * ∑ k, z k ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hsum, add_mul, mul_comm _ (1 + _), ← mul_assoc, mul_inv_cancel₀ hs.ne']
  ring

/-- **Nondegeneracy at a coordinate point.** The coordinate point `[eᵢ]` is a nondegenerate
critical point of the weighted Rayleigh quotient exactly when the weight `w i` is simple. -/
theorem isManifoldNondegenerateCriticalPoint_projectiveRayleighQuotient_mk_single_iff
    (i : Fin (n + 1)) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w)
        (mk ℝ (Pi.single i 1) (Pi.single_ne_zero_iff.2 one_ne_zero)) ↔
      ∀ j, j ≠ i → w j ≠ w i := by
  -- Read nondegeneracy in the affine chart at `i`, centred at `[eᵢ]`.
  rw [isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas i 2) (by simp),
    affineOpenPartialHomeomorph_extend, affineChart_mk_single,
    projectiveRayleighQuotient_comp_affineChart_symm_eq,
    isNondegenerateCriticalPoint_add_const_iff]
  rw [show (fun z ↦ ∑ k, (w (i.succAbove k) - w i) * ballCoord z k ^ 2) =
      (fun y : Fin n → ℝ ↦ ∑ k, (w (i.succAbove k) - w i) * y k ^ 2) ∘ ballCoord from rfl,
    isNondegenerateCriticalPoint_comp_iff (by fun_prop) (contDiff_ballCoord.contDiffAt)
      isInvertible_fderiv_ballCoord_zero, ballCoord_zero,
    isNondegenerateCriticalPoint_sum_comp_eval_iff
      (φ := fun k s ↦ (w (i.succAbove k) - w i) * s ^ 2) fun k ↦ contDiffAt_sq_mul _ _]
  simp only [Pi.zero_apply, deriv_sq_mul_zero, deriv_deriv_sq_mul_zero, true_and, ne_eq,
    mul_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero, Fin.forall_iff_succAbove i,
    not_true_eq_false, IsEmpty.forall_iff, true_and, Fin.succAbove_ne, not_false_eq_true,
    forall_const]

/-- **The Morse index at a coordinate point.** The Morse index of the weighted Rayleigh quotient at
the coordinate point `[eᵢ]` is the number of weights below `w i`. -/
theorem manifoldMorseIndex_projectiveRayleighQuotient_mk_single (i : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w)
        (mk ℝ (Pi.single i 1) (Pi.single_ne_zero_iff.2 one_ne_zero)) =
      {j | w j < w i}.ncard := by
  -- Read the index in the affine chart at `i`, centred at `[eᵢ]`.
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas i 2) (by simp)
      ((contMDiff_projectiveRayleighQuotient w 2).contMDiffAt)
      (mem_criticalPoints.1 (mk_single_mem_criticalPoints_projectiveRayleighQuotient w i)),
    affineOpenPartialHomeomorph_extend, affineChart_mk_single]
  set H : (Fin n → ℝ) → ℝ := fun y ↦ ∑ k, (w (i.succAbove k) - w i) * y k ^ 2 with hH
  have hHd : ContDiffAt ℝ 2 H (ballCoord 0) := by
    rw [ballCoord_zero]
    fun_prop
  have hHcrit : fderiv ℝ H 0 = 0 :=
    (fderiv_sum_comp_eval_eq_zero_iff (φ := fun k s ↦ (w (i.succAbove k) - w i) * s ^ 2)
      fun k ↦ (contDiffAt_sq_mul _ _).differentiableAt (by norm_num)).2 fun k ↦
        deriv_sq_mul_zero _
  -- Adding the constant `w i` does not change the Hessian.
  have hconst : hessianQuadraticForm (fun _ : Fin n → ℝ ↦ w i) 0 = 0 := by
    ext v
    simp [hessianQuadraticForm_apply]
  rw [projectiveRayleighQuotient_comp_affineChart_symm_eq, morseIndex_def,
    show (fun z ↦ (∑ k, (w (i.succAbove k) - w i) * ballCoord z k ^ 2) + w i) =
      H ∘ ballCoord + fun _ ↦ w i from rfl,
    hessianQuadraticForm_add (hHd.comp 0 contDiff_ballCoord.contDiffAt) contDiffAt_const, hconst,
    add_zero, ← morseIndex_def,
    morseIndex_comp hHd contDiff_ballCoord.contDiffAt
      (by rw [ballCoord_zero]; exact hHcrit) isInvertible_fderiv_ballCoord_zero, ballCoord_zero,
    hH, morseIndex_sum_comp_eval (φ := fun k s ↦ (w (i.succAbove k) - w i) * s ^ 2)
      fun k ↦ contDiffAt_sq_mul _ _]
  simp only [Pi.zero_apply, deriv_deriv_sq_mul_zero]
  -- The negative weights are those of the coordinates `i.succAbove k` with weight below `w i`.
  have himage : {j | w j < w i} = i.succAbove '' {k | 2 * (w (i.succAbove k) - w i) < 0} := by
    ext j
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro hj
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i)
        (by rintro rfl; exact lt_irrefl _ hj)
      exact ⟨k, by linarith, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      linarith
  rw [himage, ncard_image_of_injective _ (Fin.succAbove_right_injective)]

/-! ### Distinct weights -/

variable {w}

/-- **Critical points for distinct weights.** If the weights are distinct, the critical points of
the weighted Rayleigh quotient are exactly the coordinate points `[eᵢ]`. -/
theorem criticalPoints_projectiveRayleighQuotient (hw : Injective w) :
    criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) =
      range fun i ↦ mk ℝ (Pi.single i (1 : ℝ)) (Pi.single_ne_zero_iff.2 one_ne_zero) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · induction x using Projectivization.ind with | h v hv =>
    rw [mk_mem_criticalPoints_projectiveRayleighQuotient_iff] at hx
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    rw [Pi.zero_apply] at hi
    have hwi := (hx i).resolve_left hi
    -- Every other coordinate vanishes, since its weight would equal `w i`.
    have hzero (j : Fin (n + 1)) (hj : j ≠ i) : v j = 0 :=
      (hx j).resolve_right fun h ↦ hj (hw (h.trans hwi.symm))
    refine ⟨i, (mk_eq_mk_iff ℝ _ _ _ _).2 ⟨Units.mk0 (v i)⁻¹ (inv_ne_zero hi), ?_⟩⟩
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [hi]
    · simp [Pi.single_eq_of_ne hj, hzero j hj]
  · rintro ⟨i, rfl⟩
    exact mk_single_mem_criticalPoints_projectiveRayleighQuotient w i

/-- **The weighted Rayleigh quotient is Morse exactly when the weights are distinct.** -/
theorem isMorse_projectiveRayleighQuotient_iff :
    IsMorse 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) ↔ Injective w := by
  constructor
  · intro h i j hij
    by_contra hne
    exact (isManifoldNondegenerateCriticalPoint_projectiveRayleighQuotient_mk_single_iff w j).1
      (h.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (mk_single_mem_criticalPoints_projectiveRayleighQuotient w j)) i hne hij
  · intro hw
    refine isMorse_iff.2 ⟨contMDiff_projectiveRayleighQuotient w ∞, fun x hx ↦ ?_⟩
    have hx' : x ∈ criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) :=
      mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2 hx
    rw [criticalPoints_projectiveRayleighQuotient hw] at hx'
    obtain ⟨i, rfl⟩ := hx'
    exact (isManifoldNondegenerateCriticalPoint_projectiveRayleighQuotient_mk_single_iff w i).2
      fun j hj h ↦ hj (hw h)

/-- For distinct weights the weighted Rayleigh quotient has exactly `n + 1` critical points. -/
theorem totalCriticalCount_projectiveRayleighQuotient (hw : Injective w) :
    totalCriticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) = n + 1 := by
  rw [totalCriticalCount_def, criticalPoints_projectiveRayleighQuotient hw,
    ← image_univ, mk_single_injective.injOn.encard_image, encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  norm_cast

/-- For distinct weights, the number of weights below `w i` determines `i`. -/
private theorem ncard_setOf_lt_injective (hw : Injective w) :
    Injective fun i ↦ {j | w j < w i}.ncard := by
  intro i i' h
  by_contra hne
  -- The set of weights below the larger of `w i`, `w i'` strictly contains the other set.
  have key (a b : Fin (n + 1)) (hab : w a < w b) : {j | w j < w a}.ncard < {j | w j < w b}.ncard :=
    ncard_lt_ncard ⟨fun j hj ↦ lt_trans hj hab, fun hsub ↦ lt_irrefl (w a) (hsub hab)⟩
      (toFinite _)
  rcases lt_or_gt_of_ne (hw.ne hne) with hlt | hlt
  · exact (key i i' hlt).ne h
  · exact (key i' i hlt).ne h.symm

/-- **One critical point of each index.** For distinct weights the weighted Rayleigh quotient on
`ℝℙⁿ` has exactly one critical point of each index `j ≤ n`, and none of larger index. -/
theorem criticalCount_projectiveRayleighQuotient (hw : Injective w) (j : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) j = if j ≤ n then 1 else 0 := by
  set r : Fin (n + 1) → ℕ := fun i ↦ {k | w k < w i}.ncard with hr
  have hrlt (i : Fin (n + 1)) : r i < n + 1 := by
    calc r i < (univ : Set (Fin (n + 1))).ncard :=
          ncard_lt_ncard ⟨subset_univ _, fun h ↦ lt_irrefl (w i) (h (mem_univ i))⟩ (toFinite _)
      _ = n + 1 := by simp
  -- The index map is a bijection from the coordinate points onto `{0, …, n}`.
  let R : Fin (n + 1) → Fin (n + 1) := fun i ↦ ⟨r i, hrlt i⟩
  have hR : Bijective R :=
    Finite.injective_iff_bijective.1 fun i i' h ↦
      ncard_setOf_lt_injective hw (congrArg Fin.val h)
  have hset : {x ∈ criticalPoints 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) |
      manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveRayleighQuotient w) x = j} =
      (fun i ↦ mk ℝ (Pi.single i (1 : ℝ)) (Pi.single_ne_zero_iff.2 one_ne_zero)) ''
        {i | r i = j} := by
    rw [criticalPoints_projectiveRayleighQuotient hw]
    ext x
    simp only [mem_range, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨i, rfl⟩, hj⟩
      exact ⟨i, by rw [← hj, manifoldMorseIndex_projectiveRayleighQuotient_mk_single], rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, by rw [manifoldMorseIndex_projectiveRayleighQuotient_mk_single, ← hi]⟩
  rw [criticalCount_def, hset, mk_single_injective.injOn.encard_image]
  split_ifs with hj
  · obtain ⟨i, hi⟩ := hR.2 ⟨j, Nat.lt_succ_of_le hj⟩
    have : {i | r i = j} = {i} := by
      ext i'
      simp only [mem_ofPred_eq, mem_singleton_iff]
      refine ⟨fun h ↦ hR.1 (Fin.ext (h.trans (congrArg Fin.val hi).symm)), fun h ↦ ?_⟩
      rw [h]
      exact congrArg Fin.val hi
    simp [this]
  · simp only [encard_eq_zero, eq_empty_iff_forall_notMem, mem_ofPred_eq]
    intro i hi
    have := hrlt i
    omega

end TauCeti

end
