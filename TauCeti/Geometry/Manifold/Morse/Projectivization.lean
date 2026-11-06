/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.WeightedNormSq
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Data.Set.Card

/-!
# Moment functions on real and complex projective space

For weights `w : Fin (n + 1) → ℝ` and `𝕜 = ℝ` or `ℂ`, the **moment function**

`f [v] = (∑ k, w k * ‖v k‖ ^ 2) / ∑ k, ‖v k‖ ^ 2`

on the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is the standard Morse function on `ℝPⁿ` and
`ℂPⁿ` (`TauCeti.projectiveMomentFunction`). Projective space is charted on `Fin n → 𝕜` by its
standard affine charts, and its Morse theory is read in the real model `𝓘(ℝ, Fin n → 𝕜)`; over `ℂ`
the real smooth structure is `IsManifold.restrictScalars` of the complex one. When the weights are
distinct the moment
function is a Morse function (`TauCeti.isMorse_projectiveMomentFunction`) whose critical points are
exactly the `n + 1` coordinate lines `[e j]` (`TauCeti.criticalPoints_projectiveMomentFunction`),
and the Morse index at `[e j]` is `finrank ℝ 𝕜` times the number of weights smaller than `w j`
(`TauCeti.manifoldMorseIndex_projectiveMomentFunction`). So there is exactly one critical point
of each index `finrank ℝ 𝕜 * j` with `j ≤ n` and none of any other index: indices `0, 1, …, n` on
`ℝPⁿ` and `0, 2, …, 2n` on `ℂPⁿ`. These counts are the Betti numbers of `ℂPⁿ` and the mod `2` Betti
numbers of `ℝPⁿ`, which makes the moment functions the standard test cases for perfect Morse
functions; the homology is not computed here. On `ℝP²` three distinct weights give a minimum, a
saddle and a maximum.

In the affine chart at `i`, with `z = (v (i.succAbove k) / v i)ₖ`, the moment function is
`w i + affineMomentFunction c z` for the weights `c k = w (i.succAbove k) - w i`, where
`affineMomentFunction c z = (∑ k, c k * ‖z k‖ ^ 2) / (1 + ∑ k, ‖z k‖ ^ 2)`
(`TauCeti.projectiveMomentFunction_affineChart_symm`). The calculus is done for this chart function
on `ι → F`, for a real inner product space `F`. Its derivative along the rescaling of the `k`-th
coordinate is `2 ‖z k‖² (c k - g z) / (1 + ∑ ‖z l‖²)`, so at a critical point every nonzero
coordinate has weight `g z`; with distinct nonzero weights this forces `z = 0`
(`TauCeti.fderiv_affineMomentFunction_eq_zero_iff`). At the origin the second-order part of
`g` is the weighted sum of squared norms `∑ k, c k * ‖z k‖ ^ 2`, whose Morse data are computed in
`TauCeti.Analysis.Calculus.Morse.WeightedNormSq`.

## Main declarations

* `TauCeti.affineMomentFunction`: the moment function read in an affine chart, with
  `TauCeti.fderiv_affineMomentFunction_eq_zero_iff`,
  `TauCeti.isNondegenerateCriticalPoint_affineMomentFunction_zero_iff` and
  `TauCeti.morseIndex_affineMomentFunction_zero`.
* `TauCeti.projectiveMomentFunction`: the moment function on projective space, with its value
  `TauCeti.projectiveMomentFunction_mk` in homogeneous coordinates.
* `TauCeti.contMDiff_projectiveMomentFunction`: it is smooth.
* `TauCeti.criticalPoints_projectiveMomentFunction`: for distinct weights its critical points are
  the coordinate lines.
* `TauCeti.isMorse_projectiveMomentFunction`: for distinct weights it is a Morse function.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction`: the index at `[e j]` is
  `finrank ℝ 𝕜 * #{k | w k < w j}`; for the weights `w k = k` it is `finrank ℝ 𝕜 * j`
  (`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast`).
* `TauCeti.totalCriticalCount_projectiveMomentFunction`,
  `TauCeti.criticalCount_projectiveMomentFunction_mul` and
  `TauCeti.criticalCount_projectiveMomentFunction_eq_zero`: there are `n + 1` critical points, one
  of each index `finrank ℝ 𝕜 * j` with `j ≤ n`, and none of any other index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §4, the Morse function `∑ c j * |z j| ^ 2` on complex projective space.
-/

public section

open Function Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti

/-! ### The moment function in an affine chart -/

section Model

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]

/-- The moment function of projective space read in an affine chart, up to an additive constant:
`z ↦ (∑ k, c k * ‖z k‖ ^ 2) / (1 + ∑ k, ‖z k‖ ^ 2)` on `ι → F`. -/
noncomputable def affineMomentFunction (c : ι → ℝ) (z : ι → F) : ℝ :=
  (∑ k, c k * ‖z k‖ ^ 2) / (1 + ∑ k, ‖z k‖ ^ 2)

/-- The chart moment function, written out. -/
@[simp]
theorem affineMomentFunction_apply (c : ι → ℝ) (z : ι → F) :
    affineMomentFunction c z = (∑ k, c k * ‖z k‖ ^ 2) / (1 + ∑ k, ‖z k‖ ^ 2) :=
  (rfl)

/-- The chart moment function is the quotient `a / (1 + b)` of the weighted and the unweighted
sums of squared norms. -/
private theorem affineMomentFunction_eq_comp (c : ι → ℝ) :
    affineMomentFunction (F := F) c = (fun p : ℝ × ℝ ↦ p.1 / (1 + p.2)) ∘
      fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2) :=
  (rfl)

variable [InnerProductSpace ℝ F]

/-- The chart moment function is smooth. -/
theorem contDiff_affineMomentFunction (c : ι → ℝ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (affineMomentFunction (F := F) c) := by
  have hsq (k : ι) : ContDiff ℝ m fun z : ι → F ↦ ‖z k‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ : ι ↦ F) k)
  exact (contDiff_sum_mul_norm_sq c).div (contDiff_const.add (ContDiff.sum fun k _ ↦ hsq k))
    fun z ↦ by positivity

/-- The derivative of the chart moment function `g` along the rescaling of the `k`-th coordinate
is `2 ‖z k‖² (c k - g z) / (1 + ∑ ‖z l‖²)`. -/
private theorem fderiv_affineMomentFunction_apply_single [DecidableEq ι] (c : ι → ℝ)
    (z : ι → F) (k : ι) :
    fderiv ℝ (affineMomentFunction c) z (Pi.single k (z k)) =
      2 * ‖z k‖ ^ 2 * (c k - affineMomentFunction c z) / (1 + ∑ l, ‖z l‖ ^ 2) := by
  set a := ‖z k‖ ^ 2
  set Q := ∑ l, c l * ‖z l‖ ^ 2
  set N := 1 + ∑ l, ‖z l‖ ^ 2
  have hN : 0 < N := by positivity
  -- Along the line `t ↦ z + t • Pi.single k (z k)` only the `k`-th coordinate moves, scaled by
  -- `1 + t`.
  have hline (t : ℝ) : affineMomentFunction c (z + t • (Pi.single k (z k) : ι → F)) =
      (Q + c k * a * (2 * t + t ^ 2)) / (N + a * (2 * t + t ^ 2)) := by
    have hcoord (l : ι) : ‖(z + t • (Pi.single k (z k) : ι → F)) l‖ ^ 2 =
        ‖z l‖ ^ 2 + if l = k then a * (2 * t + t ^ 2) else 0 := by
      by_cases hl : l = k
      · subst hl
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, ite_true, a]
        rw [show z l + t • z l = (1 + t) • z l by rw [add_smul, one_smul], norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs]
        ring
      · simp [hl]
    simp only [affineMomentFunction_apply, hcoord, mul_add, Finset.sum_add_distrib, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Q, N]
    ring
  have hd : HasDerivAt (fun t : ℝ ↦ affineMomentFunction c (z + t • (Pi.single k (z k) : ι → F)))
      (fderiv ℝ (affineMomentFunction c) z (Pi.single k (z k))) 0 := by
    have hl : HasDerivAt (fun t : ℝ ↦ z + t • (Pi.single k (z k) : ι → F))
        (Pi.single k (z k)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (z k) : ι → F)).const_add z
    exact ((contDiff_affineMomentFunction c (m := 1)).differentiable one_ne_zero
      z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hd' : HasDerivAt (fun t : ℝ ↦ (Q + c k * a * (2 * t + t ^ 2)) / (N + a * (2 * t + t ^ 2)))
      ((c k * a * 2 * N - Q * (a * 2)) / N ^ 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ 2 * t + t ^ 2) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).fun_add (hasDerivAt_pow 2 (0 : ℝ))
    simpa using ((h1.const_mul (c k * a)).const_add Q).fun_div ((h1.const_mul a).const_add N)
      (by simpa using hN.ne')
  rw [funext hline] at hd
  rw [hd.unique hd', affineMomentFunction_apply]
  field_simp
  ring

/-- The weighted and the unweighted sums of squared norms have zero derivative at the origin. -/
private theorem hasFDerivAt_sum_mul_norm_sq_prod_zero (c : ι → ℝ) :
    HasFDerivAt (fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2))
      (0 : (ι → F) →L[ℝ] ℝ × ℝ) 0 := by
  have h := (hasFDerivAt_sum_mul_norm_sq_zero (F := F) c).prodMk
    (hasFDerivAt_sum_mul_norm_sq_zero (F := F) fun _ ↦ (1 : ℝ))
  simp only [one_mul] at h
  convert h using 1
  ext <;> simp

/-- The origin is a critical point of the chart moment function. -/
theorem fderiv_affineMomentFunction_zero (c : ι → ℝ) :
    fderiv ℝ (affineMomentFunction (F := F) c) 0 = 0 := by
  have hh : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ p.1 / (1 + p.2))
      ((fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2)) 0) := by
    fun_prop (disch := simp)
  rw [affineMomentFunction_eq_comp,
    (hh.hasFDerivAt.comp (0 : ι → F) (hasFDerivAt_sum_mul_norm_sq_prod_zero c)).fderiv,
    ContinuousLinearMap.comp_zero]

/-- **The critical points of the chart moment function.** For distinct nonzero weights, the
origin is the only critical point of `affineMomentFunction c`. -/
theorem fderiv_affineMomentFunction_eq_zero_iff {c : ι → ℝ} (hc : Injective c)
    (hc₀ : ∀ k, c k ≠ 0) {z : ι → F} :
    fderiv ℝ (affineMomentFunction c) z = 0 ↔ z = 0 := by
  classical
  refine ⟨fun hz ↦ ?_, fun hz ↦ hz ▸ fderiv_affineMomentFunction_zero c⟩
  -- Every nonzero coordinate has weight equal to the value of the function.
  have hk (k : ι) : z k = 0 ∨ c k = affineMomentFunction c z := by
    have h := fderiv_affineMomentFunction_apply_single c z k
    rw [hz, zero_apply, eq_comm, div_eq_zero_iff] at h
    rcases h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (sub_eq_zero.1 h)
    · exact absurd h (by positivity)
  by_contra h₀
  obtain ⟨k, hk₀⟩ : ∃ k, z k ≠ 0 := by simpa [funext_iff] using h₀
  have hgk : affineMomentFunction c z = c k := ((hk k).resolve_left hk₀).symm
  -- Distinct weights leave a single nonzero coordinate, whose weight cannot be the value.
  have hzl (l : ι) (hl : l ≠ k) : z l = 0 :=
    (hk l).resolve_right fun h ↦ hl (hc (h.trans hgk))
  have hQ : ∑ l, c l * ‖z l‖ ^ 2 = c k * ‖z k‖ ^ 2 :=
    Finset.sum_eq_single k (fun l _ hl ↦ by simp [hzl l hl]) (by simp)
  have hN : ∑ l, ‖z l‖ ^ 2 = ‖z k‖ ^ 2 :=
    Finset.sum_eq_single k (fun l _ hl ↦ by simp [hzl l hl]) (by simp)
  rw [affineMomentFunction_apply, hQ, hN, div_eq_iff (by positivity)] at hgk
  exact hc₀ k (by linarith)

/-- At the origin, the Hessian of the chart moment function is that of the weighted sum of
squared norms `∑ k, c k * ‖z k‖ ^ 2`. -/
private theorem hessianQuadraticForm_affineMomentFunction_zero (c : ι → ℝ) :
    hessianQuadraticForm (affineMomentFunction (F := F) c) 0 =
      hessianQuadraticForm (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) 0 := by
  have hh : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ p.1 / (1 + p.2))
      ((fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2)) 0) := by
    simp only [Pi.zero_apply, norm_zero]
    fun_prop (disch := simp)
  have hφ : ContDiffAt ℝ 2 (fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2)) 0 := by
    simpa using ((contDiff_sum_mul_norm_sq c).prodMk
      (contDiff_sum_mul_norm_sq (F := F) fun _ ↦ (1 : ℝ))).contDiffAt
  -- The quotient `a / (1 + b)` has derivative `(a, b) ↦ a` at the origin.
  have hfst : fderiv ℝ (fun p : ℝ × ℝ ↦ p.1 / (1 + p.2))
      ((fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2)) 0) =
        ContinuousLinearMap.fst ℝ ℝ ℝ := by
    have hinv : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ (1 + p.2)⁻¹) 0 := by
      fun_prop (disch := simp)
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).fun_mul hinv.hasFDerivAt
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero, inv_one, zero_smul, one_smul,
      zero_add] at h
    have h0 : (fun z : ι → F ↦ (∑ k, c k * ‖z k‖ ^ 2, ∑ k, ‖z k‖ ^ 2)) 0 = 0 := by simp
    rw [h0]
    simp_rw [div_eq_mul_inv]
    exact h.fderiv
  rw [affineMomentFunction_eq_comp, hessianQuadraticForm_comp_eq_fderiv_comp (x := 0) hh hφ
    (hasFDerivAt_sum_mul_norm_sq_prod_zero c).fderiv, hfst]
  rfl

variable [FiniteDimensional ℝ F]

/-- **Nondegeneracy of the chart moment function.** For a nonzero finite-dimensional `F`, the
origin is a nondegenerate critical point of `affineMomentFunction c` exactly when no weight
vanishes. -/
theorem isNondegenerateCriticalPoint_affineMomentFunction_zero_iff [Nontrivial F] (c : ι → ℝ) :
    IsNondegenerateCriticalPoint (affineMomentFunction (F := F) c) 0 ↔ ∀ k, c k ≠ 0 := by
  rw [← isNondegenerateCriticalPoint_sum_mul_norm_sq_zero_iff (F := F),
    isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate,
    isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate,
    hessianQuadraticForm_affineMomentFunction_zero]
  simp [(contDiff_affineMomentFunction c).contDiffAt, fderiv_affineMomentFunction_zero,
    (contDiff_sum_mul_norm_sq c).contDiffAt, (hasFDerivAt_sum_mul_norm_sq_zero c).fderiv]

/-- **The Morse index of the chart moment function** at the origin is `finrank ℝ F` times the
number of negative weights. -/
theorem morseIndex_affineMomentFunction_zero (c : ι → ℝ) :
    morseIndex (affineMomentFunction (F := F) c) 0 = finrank ℝ F * {k | c k < 0}.ncard := by
  rw [morseIndex_def, hessianQuadraticForm_affineMomentFunction_zero, ← morseIndex_def,
    morseIndex_sum_mul_norm_sq]

end Model

/-! ### The moment function on projective space -/

section Projective

open Projectivization

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The **moment function** `[v] ↦ (∑ k, w k * ‖v k‖ ^ 2) / ∑ k, ‖v k‖ ^ 2` on the projective space
`ℙ 𝕜 (Fin (n + 1) → 𝕜)`, for weights `w : Fin (n + 1) → ℝ`. -/
noncomputable def projectiveMomentFunction (w : Fin (n + 1) → ℝ) : ℙ 𝕜 (Fin (n + 1) → 𝕜) → ℝ :=
  Projectivization.lift (fun v ↦ (∑ k, w k * ‖v.1 k‖ ^ 2) / ∑ k, ‖v.1 k‖ ^ 2) fun a b t h ↦ by
    -- Rescaling a vector by `t ≠ 0` multiplies both sums by `‖t‖ ^ 2`.
    have ht : ‖t‖ ^ 2 ≠ 0 := by
      rintro h0
      exact a.2 (by simp_all)
    simp only [h, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_left_comm (w _),
      ← Finset.mul_sum]
    exact mul_div_mul_left _ _ ht

/-- The moment function in homogeneous coordinates. -/
@[simp]
theorem projectiveMomentFunction_mk (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    projectiveMomentFunction w (mk 𝕜 v hv) = (∑ k, w k * ‖v k‖ ^ 2) / ∑ k, ‖v k‖ ^ 2 :=
  (rfl)

/-- **The moment function in an affine chart.** In the `i`-th standard affine chart the moment
function is `w i + affineMomentFunction c` for the weights `c k = w (i.succAbove k) - w i`. -/
theorem projectiveMomentFunction_affineChart_symm (w : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (z : Fin n → 𝕜) :
    projectiveMomentFunction w ((affineChart i).symm z) =
      w i + affineMomentFunction (fun k ↦ w (i.succAbove k) - w i) z := by
  rw [affineChart_symm_apply, projectiveMomentFunction_mk, Fin.sum_univ_succAbove _ i,
    Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, norm_one, one_pow, mul_one,
    affineMomentFunction_apply, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h : 1 + ∑ k, ‖z k‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- In the preferred extended chart at a point of the `i`-th affine open, the moment function is
`w i + affineMomentFunction c` for the weights `c k = w (i.succAbove k) - w i`. -/
private theorem projectiveMomentFunction_comp_extChartAt_symm (w : Fin (n + 1) → ℝ)
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} {i : Fin (n + 1)}
    (hi : chartAt (Fin n → 𝕜) x = affineOpenPartialHomeomorph i) :
    projectiveMomentFunction w ∘ (extChartAt 𝓘(ℝ, Fin n → 𝕜) x).symm =
      fun z ↦ w i + affineMomentFunction (fun k ↦ w (i.succAbove k) - w i) z := by
  funext z
  rw [extChartAt_coe_symm, hi, modelWithCornersSelf_coe_symm, comp_id, comp_apply,
    coe_affineOpenPartialHomeomorph_symm, projectiveMomentFunction_affineChart_symm]

/-- The weights of the chart moment function at `i` are nonzero when `w i` differs from every
other weight. -/
private theorem sub_ne_zero_of_ne {w : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hw : ∀ k, k ≠ i → w k ≠ w i) (k : Fin n) : w (i.succAbove k) - w i ≠ 0 :=
  sub_ne_zero.2 (hw _ (Fin.succAbove_ne i k))

/-- The moment function on projective space is smooth. -/
theorem contMDiff_projectiveMomentFunction (w : Fin (n + 1) → ℝ) {m : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ) m (projectiveMomentFunction (𝕜 := 𝕜) w) := by
  intro x
  obtain ⟨i, hi⟩ := exists_chartAt_eq (𝕜 := 𝕜) x
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt, projectiveMomentFunction_comp_extChartAt_symm w hi]
  exact (contDiff_const.add (contDiff_affineMomentFunction _)).contDiffAt

/-- **The critical points of a moment function.** For distinct weights, the critical points of the
moment function are exactly the coordinate lines `[e j] = (affineChart j).symm 0`. -/
theorem criticalPoints_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) =
      range fun j ↦ (affineChart j).symm 0 := by
  ext x
  obtain ⟨i, hi⟩ := exists_chartAt_eq (𝕜 := 𝕜) x
  have hc : Injective fun k ↦ w (i.succAbove k) - w i :=
    fun k l hkl ↦ Fin.succAbove_right_injective (hw (sub_left_injective hkl))
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    projectiveMomentFunction_comp_extChartAt_symm w hi, fderiv_const_add,
    fderiv_affineMomentFunction_eq_zero_iff hc (sub_ne_zero_of_ne fun k hk ↦ hw.ne hk)]
  have hx : x ∈ affineOpen i := by
    simpa [hi] using mem_chart_source (Fin n → 𝕜) x
  rw [extChartAt_coe, hi, modelWithCornersSelf_coe, id_comp, coe_affineOpenPartialHomeomorph,
    mem_range]
  constructor
  · intro h0
    exact ⟨i, by rw [← h0, (affineChart i).left_inv (by simpa using hx)]⟩
  · rintro ⟨j, rfl⟩
    rw [affineChart_symm_zero_mem_affineOpen_iff.1 hx]
    exact (affineChart j).right_inv (by simp)

/-- The coordinate line `[e j]` is a critical point of every moment function. -/
theorem affineChart_symm_zero_mem_criticalPoints_projectiveMomentFunction
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (affineChart j).symm 0 ∈
      criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    projectiveMomentFunction_comp_extChartAt_symm w (chartAt_affineChart_symm_zero (𝕜 := 𝕜) j),
    fderiv_const_add, extChartAt_affineChart_symm_zero]
  exact fderiv_affineMomentFunction_zero _

/-- **Nondegeneracy of the critical points of a moment function.** The coordinate line `[e j]` is
a nondegenerate critical point of the moment function exactly when `w j` differs from every other
weight. -/
theorem isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w)
      ((affineChart j).symm 0) ↔ ∀ k, k ≠ j → w k ≠ w j := by
  rw [isManifoldNondegenerateCriticalPoint_iff,
    projectiveMomentFunction_comp_extChartAt_symm w (chartAt_affineChart_symm_zero (𝕜 := 𝕜) j),
    extChartAt_affineChart_symm_zero]
  simp_rw [add_comm (w j)]
  rw [isNondegenerateCriticalPoint_add_const_iff (f := affineMomentFunction _),
    isNondegenerateCriticalPoint_affineMomentFunction_zero_iff]
  refine ⟨fun h k hk ↦ ?_, fun h ↦ sub_ne_zero_of_ne h⟩
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
  exact sub_ne_zero.1 (h l)

/-- **The moment function with distinct weights is a Morse function** on projective space. -/
theorem isMorse_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    IsMorse 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) := by
  refine isMorse_iff.2 ⟨contMDiff_projectiveMomentFunction w, fun x hx ↦ ?_⟩
  have hx' : x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) :=
    mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2 hx
  rw [criticalPoints_projectiveMomentFunction hw] at hx'
  obtain ⟨j, rfl⟩ := hx'
  exact (isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff w j).2
    fun k hk ↦ hw.ne hk

/-- **The Morse index of a moment function** at the coordinate line `[e j]` is `finrank ℝ 𝕜` times
the number of weights smaller than `w j`. -/
theorem manifoldMorseIndex_projectiveMomentFunction (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w)
      ((affineChart j).symm 0) = finrank ℝ 𝕜 * {k | w k < w j}.ncard := by
  rw [manifoldMorseIndex_def,
    projectiveMomentFunction_comp_extChartAt_symm w (chartAt_affineChart_symm_zero (𝕜 := 𝕜) j),
    extChartAt_affineChart_symm_zero, morseIndex_const_add (f := affineMomentFunction _),
    morseIndex_affineMomentFunction_zero]
  -- The weights below `w j` are the images under `j.succAbove` of the negative chart weights.
  congr 1
  rw [← (Fin.succAbove_right_injective (p := j)).injOn.ncard_image]
  congr 1
  ext k
  simp only [mem_image, mem_ofPred_eq, sub_neg]
  refine ⟨fun ⟨l, hl, hlk⟩ ↦ hlk ▸ hl, fun hk ↦ ?_⟩
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (fun h : k = j ↦ (h ▸ hk).false)
  exact ⟨l, hk, rfl⟩

/-- For the weights `w k = k`, the Morse index at the coordinate line `[e j]` is
`finrank ℝ 𝕜 * j`: it is `j` on `ℝPⁿ` and `2 j` on `ℂPⁿ`. -/
theorem manifoldMorseIndex_projectiveMomentFunction_natCast (j : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜)
      (projectiveMomentFunction (𝕜 := 𝕜) fun k : Fin (n + 1) ↦ ((k : ℕ) : ℝ))
      ((affineChart j).symm 0) = finrank ℝ 𝕜 * j := by
  rw [manifoldMorseIndex_projectiveMomentFunction]
  congr 1
  have h : {k : Fin (n + 1) | ((k : ℕ) : ℝ) < ((j : ℕ) : ℝ)} = ↑(Finset.Iio j) := by
    ext k
    simp only [mem_ofPred_eq, Nat.cast_lt, Finset.coe_Iio, mem_Iio, Fin.lt_def]
  rw [h, ncard_coe_finset, Fin.card_Iio]

/-- **Critical counts of a moment function.** For distinct weights, the number of critical points
of index `m` is the number of `j` such that `finrank ℝ 𝕜` times the number of weights below `w j`
is `m`. -/
theorem criticalCount_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) (m : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) m =
      {j : Fin (n + 1) | finrank ℝ 𝕜 * {k | w k < w j}.ncard = m}.encard := by
  rw [criticalCount_def, criticalPoints_projectiveMomentFunction hw,
    ← (injective_affineChart_symm_zero (K := 𝕜) (n := n)).injOn.encard_image]
  congr 1
  ext x
  simp only [mem_range, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    exact ⟨j, by rwa [manifoldMorseIndex_projectiveMomentFunction] at hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, rfl⟩, by rwa [manifoldMorseIndex_projectiveMomentFunction]⟩

/-- A moment function with distinct weights has exactly `n + 1` critical points. -/
theorem totalCriticalCount_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    totalCriticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) = n + 1 := by
  rw [totalCriticalCount_def, criticalPoints_projectiveMomentFunction hw, ← image_univ,
    (injective_affineChart_symm_zero (K := 𝕜) (n := n)).injOn.encard_image, encard_univ,
    ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]
  norm_cast

/-- **Critical counts of a moment function by index.** For distinct weights and every `j ≤ n`, the
moment function has exactly one critical point of index `finrank ℝ 𝕜 * j`. -/
theorem criticalCount_projectiveMomentFunction_mul {w : Fin (n + 1) → ℝ} (hw : Injective w)
    {j : ℕ} (hj : j ≤ n) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) (finrank ℝ 𝕜 * j) = 1 := by
  obtain ⟨i, hi, hu⟩ :=
    existsUnique_ncard_setOf_lt_eq hw (m := j) (by simpa using Nat.lt_succ_of_le hj)
  rw [criticalCount_projectiveMomentFunction hw, encard_eq_one]
  refine ⟨i, ext fun k ↦ ?_⟩
  simp only [mem_ofPred_eq, mem_singleton_iff, mul_right_inj' finrank_pos.ne']
  exact ⟨hu k, fun hk ↦ hk ▸ hi⟩

/-- A moment function with distinct weights has no critical point whose index is not of the form
`finrank ℝ 𝕜 * j` with `j ≤ n`. -/
theorem criticalCount_projectiveMomentFunction_eq_zero {w : Fin (n + 1) → ℝ} (hw : Injective w)
    {m : ℕ} (hm : ∀ j ≤ n, finrank ℝ 𝕜 * j ≠ m) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction (𝕜 := 𝕜) w) m = 0 := by
  rw [criticalCount_projectiveMomentFunction hw, encard_eq_zero, eq_empty_iff_forall_notMem]
  refine fun i hi ↦ hm _ (Nat.lt_succ_iff.1 ?_) hi
  simpa using ncard_lt_card (s := {k | w k < w i}) fun h ↦ lt_irrefl (w i) (h.symm ▸ mem_univ i :)

end Projective

end TauCeti

end
