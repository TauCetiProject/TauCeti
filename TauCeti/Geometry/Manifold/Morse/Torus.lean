/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.Calculus.Morse.Pi
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Topology.Circle.AddCircle

/-!
# The cosine Morse function on a torus

For a finite family of positive periods `p i`, the torus `Tᵐ = ∀ i, AddCircle (p i)`, with
`m = card ι`, carries the **cosine function**

`torusCos p x = ∑ i, cos (2π xᵢ / pᵢ)`,

defined through the real parts of `AddCircle.toCircle`. It is the standard Morse function on a
torus. Its critical points are the `2ᵐ` points all of whose coordinates are `0` or the half period
`pᵢ / 2`; each of them is nondegenerate, and its Morse index is the number of coordinates equal to
`0`, where the cosine of that factor attains its maximum. Hence the cosine function has exactly
`(m choose j)` critical points of index `j`, and `2ᵐ` critical points in all. These binomial
coefficients are the Betti numbers of `Tᵐ`, which makes the cosine function the standard test case
for the Morse inequalities; the homology of the torus is not computed here.

In the preferred chart at any point, whose coordinates are local real lifts of the coordinates of
the point, the cosine function is the separated sum `y ↦ ∑ i, cos (2π yᵢ / pᵢ)`
(`TauCeti.torusCos_comp_extChartAt_symm`). The statements about critical points and indices are
therefore those of `TauCeti.Analysis.Calculus.Morse.Pi` for the one-variable functions
`t ↦ cos (2π t / pᵢ)`. For `m = 2` this is the classical function on the two-torus with one
minimum, two saddles and one maximum.

## Main declarations

* `TauCeti.torusCos`: the cosine function on a torus, with `TauCeti.torusCos_coe` evaluating it
  at the class of a real vector.
* `TauCeti.torusCos_comp_extChartAt_symm`: its expression in the preferred charts.
* `TauCeti.contMDiff_torusCos` and `TauCeti.isMorse_torusCos`: it is a smooth Morse function.
* `TauCeti.mem_criticalPoints_torusCos_iff`: its critical points are the points with all
  coordinates `0` or the half period.
* `TauCeti.manifoldMorseIndex_torusCos`: the Morse index at a critical point is the number of
  coordinates equal to `0`.
* `TauCeti.criticalCount_torusCos` and `TauCeti.totalCriticalCount_torusCos`: there are
  `(m choose j)` critical points of index `j`, and `2ᵐ` critical points in all.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Set Filter Function Topology AddCircle
open scoped Manifold ContDiff Real

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ)

/-- **The cosine function on a torus** `∀ i, AddCircle (p i)`: the sum over the factors of the
cosine of the angle, `x ↦ ∑ i, cos (2π xᵢ / pᵢ)`, written with the real parts of
`AddCircle.toCircle`. -/
noncomputable def torusCos (x : ∀ i, AddCircle (p i)) : ℝ :=
  ∑ i, (toCircle (x i) : ℂ).re

/-- The cosine function on a torus is the sum of the real parts of `AddCircle.toCircle` of the
coordinates. -/
theorem torusCos_def (x : ∀ i, AddCircle (p i)) : torusCos p x = ∑ i, (toCircle (x i) : ℂ).re :=
  (rfl)

/-- At the class of a real vector `t`, the cosine function on a torus is `∑ i, cos (2π tᵢ / pᵢ)`. -/
@[simp]
theorem torusCos_coe (t : ι → ℝ) :
    torusCos p (fun i ↦ (t i : AddCircle (p i))) = ∑ i, Real.cos (2 * π / p i * t i) := by
  simp [torusCos_def]

/-- The cosine function on a torus is continuous. -/
theorem continuous_torusCos : Continuous (torusCos p) := by
  rw [show torusCos p = fun x ↦ ∑ i, (toCircle (x i) : ℂ).re from funext (torusCos_def p)]
  fun_prop

variable [∀ i, Fact (0 < p i)]

/-- The point of the preferred chart of the torus at `x` is a family of real lifts of the
coordinates of `x`. -/
private theorem coe_extChartAt_self_apply (x : ∀ i, AddCircle (p i)) (i : ι) :
    ((extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i : ℝ) : AddCircle (p i)) = x i := by
  rw [extChartAt_pi]
  exact coe_extChartAt_apply (x i) (mem_extChartAt_source (x i))

/-- **The cosine function in the preferred charts.** Near the image of `x` in its preferred chart,
the coordinate expression of the cosine function on the torus is the separated sum
`y ↦ ∑ i, cos (2π yᵢ / pᵢ)`. -/
theorem torusCos_comp_extChartAt_symm (x : ∀ i, AddCircle (p i)) :
    torusCos p ∘ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm
      =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x)]
      fun y ↦ ∑ i, Real.cos (2 * π / p i * y i) := by
  filter_upwards [extChartAt_target_mem_nhds (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x]
    with y hy
  rw [extChartAt_pi] at hy ⊢
  have hsymm : (PartialEquiv.pi fun i ↦ extChartAt 𝓘(ℝ) (x i)).symm y =
      fun i ↦ (y i : AddCircle (p i)) :=
    funext fun i ↦ extChartAt_symm_apply (x i) (hy i (mem_univ i))
  rw [comp_apply, hsymm, torusCos_coe]

/-- The cosine function on a torus is smooth. -/
theorem contMDiff_torusCos :
    ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 𝓘(ℝ) ∞ (torusCos p) := by
  intro x
  rw [contMDiffAt_iff, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    ModelWithCorners.range_eq_univ, contDiffWithinAt_univ, id_comp]
  refine ⟨(continuous_torusCos p).continuousAt, ContDiffAt.congr_of_eventuallyEq ?_
    (torusCos_comp_extChartAt_symm p x)⟩
  fun_prop

/-- The derivative of the angle cosine `t ↦ cos (c t)` of a factor. -/
private theorem deriv_cos_mul (c t : ℝ) :
    deriv (fun s ↦ Real.cos (c * s)) t = -(c * Real.sin (c * t)) := by
  rw [deriv_comp_mul_left (f := Real.cos), Real.deriv_cos, smul_eq_mul, mul_neg]

/-- The second derivative of the angle cosine `t ↦ cos (c t)` of a factor. -/
private theorem deriv_deriv_cos_mul (c t : ℝ) :
    deriv (deriv fun s ↦ Real.cos (c * s)) t = -(c ^ 2 * Real.cos (c * t)) := by
  rw [show (deriv fun s ↦ Real.cos (c * s)) = fun s ↦ -(c * Real.sin (c * s)) from
      funext (deriv_cos_mul c), deriv.fun_neg, deriv_const_mul _ (by fun_prop),
    deriv_comp_mul_left (f := Real.sin), Real.deriv_sin, smul_eq_mul]
  ring

/-- The derivative of the angle cosine of the `i`-th factor at a lift of `x i` vanishes exactly
when `x i` is `0` or the half period. -/
private theorem deriv_cos_eq_zero_iff (i : ι) (x : ∀ i, AddCircle (p i)) :
    deriv (fun s ↦ Real.cos (2 * π / p i * s))
        (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) = 0 ↔
      x i = 0 ∨ x i = ((p i / 2 : ℝ) : AddCircle (p i)) := by
  have hc : 2 * π / p i ≠ 0 := div_ne_zero (by positivity) (Fact.out : 0 < p i).ne'
  rw [deriv_cos_mul, neg_eq_zero, mul_eq_zero, or_iff_right hc, ← im_toCircle_coe,
    coe_extChartAt_self_apply, im_toCircle_eq_zero_iff (Fact.out : 0 < p i).ne']

/-- The second derivative of the angle cosine of the `i`-th factor at a lift of `x i` is negative
exactly when the cosine is positive. -/
private theorem deriv_deriv_cos_neg_iff (i : ι) (x : ∀ i, AddCircle (p i)) :
    deriv (deriv fun s ↦ Real.cos (2 * π / p i * s))
        (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) < 0 ↔
      0 < (toCircle (x i) : ℂ).re := by
  have hc : 0 < (2 * π / p i) ^ 2 :=
    pow_pos (div_pos (by positivity) (Fact.out : 0 < p i)) 2
  rw [deriv_deriv_cos_mul, neg_lt_zero, ← re_toCircle_coe, coe_extChartAt_self_apply,
    mul_pos_iff_of_pos_left hc]

/-- **Critical points of the cosine function on a torus**: the points all of whose coordinates are
`0` or the half period. -/
theorem mem_criticalPoints_torusCos_iff {x : ∀ i, AddCircle (p i)} :
    x ∈ criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) ↔
      ∀ i, x i = 0 ∨ x i = ((p i / 2 : ℝ) : AddCircle (p i)) := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    (torusCos_comp_extChartAt_symm p x).fderiv_eq,
    fderiv_sum_comp_eval_eq_zero_iff (φ := fun i s ↦ Real.cos (2 * π / p i * s))
      fun i ↦ by fun_prop]
  exact forall_congr' fun i ↦ deriv_cos_eq_zero_iff p i x

/-- **The cosine function on a torus is a Morse function.** -/
theorem isMorse_torusCos : IsMorse (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) := by
  refine isMorse_iff.2 ⟨contMDiff_torusCos p, fun x hx ↦ ?_⟩
  have hcrit := (mem_criticalPoints_torusCos_iff p).1
    (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2 hx)
  rw [isManifoldNondegenerateCriticalPoint_iff]
  refine IsNondegenerateCriticalPoint.congr_of_eventuallyEq ?_
    (torusCos_comp_extChartAt_symm p x).symm
  refine (isNondegenerateCriticalPoint_sum_comp_eval_iff
    (φ := fun i s ↦ Real.cos (2 * π / p i * s)) fun i ↦ by fun_prop).2 fun i ↦
      ⟨(deriv_cos_eq_zero_iff p i x).2 (hcrit i), ?_⟩
  -- At a critical point the angle cosine of each factor is `±1`, so its second derivative is not
  -- zero.
  have hc : 2 * π / p i ≠ 0 := div_ne_zero (by positivity) (Fact.out : 0 < p i).ne'
  rw [deriv_deriv_cos_mul, neg_ne_zero, mul_ne_zero_iff, ← re_toCircle_coe,
    coe_extChartAt_self_apply]
  refine ⟨pow_ne_zero 2 hc, ?_⟩
  rcases hcrit i with h | h <;> simp [h, (Fact.out : 0 < p i).ne']

/-- **The Morse index of the cosine function on a torus** at a critical point is the number of
coordinates equal to `0`, where the cosine of the factor attains its maximum. -/
theorem manifoldMorseIndex_torusCos {x : ∀ i, AddCircle (p i)}
    (hx : x ∈ criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p)) :
    manifoldMorseIndex (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) x =
      {i | x i = 0}.ncard := by
  rw [manifoldMorseIndex_def, morseIndex_congr_of_eventuallyEq (torusCos_comp_extChartAt_symm p x),
    morseIndex_sum_comp_eval (φ := fun i s ↦ Real.cos (2 * π / p i * s)) fun i ↦ by fun_prop]
  congr 1
  ext i
  rw [mem_ofPred_eq, mem_ofPred_eq, deriv_deriv_cos_neg_iff]
  rcases (mem_criticalPoints_torusCos_iff p).1 hx i with h | h
  · simp [h]
  · simp [h, coe_half_period_ne_zero (Fact.out : 0 < p i).ne', (Fact.out : 0 < p i).ne']

open scoped Classical in
/-- The critical point of the cosine function whose coordinates are `0` on `s` and the half period
off `s`. -/
private noncomputable def torusCosCriticalPoint (s : Finset ι) : ∀ i, AddCircle (p i) :=
  fun i ↦ if i ∈ s then 0 else ((p i / 2 : ℝ) : AddCircle (p i))

omit [Fintype ι] in
private theorem torusCosCriticalPoint_injective : Injective (torusCosCriticalPoint p) := by
  intro s t hst
  ext i
  have h := congrFun hst i
  have hne := coe_half_period_ne_zero (Fact.out : 0 < p i).ne'
  simp only [torusCosCriticalPoint] at h
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht, hne, hne.symm] at h ⊢

/-- The critical points of the cosine function are the points `torusCosCriticalPoint p s`, and
the one indexed by `s` has `s` as its set of zero coordinates. -/
private theorem exists_torusCosCriticalPoint_eq {x : ∀ i, AddCircle (p i)}
    (hx : x ∈ criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p)) :
    torusCosCriticalPoint p {i | x i = 0}.toFinset = x := by
  ext1 i
  rcases (mem_criticalPoints_torusCos_iff p).1 hx i with h | h <;>
    simp [torusCosCriticalPoint, h, coe_half_period_ne_zero (Fact.out : 0 < p i).ne']

private theorem torusCosCriticalPoint_mem_criticalPoints (s : Finset ι) :
    torusCosCriticalPoint p s ∈
      criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) :=
  (mem_criticalPoints_torusCos_iff p).2 fun i ↦ by
    by_cases hi : i ∈ s <;> simp [torusCosCriticalPoint, hi]

omit [Fintype ι] in
private theorem setOf_eq_zero_torusCosCriticalPoint (s : Finset ι) :
    {i | torusCosCriticalPoint p s i = 0} = s := by
  ext i
  by_cases hi : i ∈ s
  · simp [torusCosCriticalPoint, hi]
  · simpa [torusCosCriticalPoint, hi] using coe_half_period_ne_zero (Fact.out : 0 < p i).ne'

/-- The critical points of the cosine function on a torus are parametrized by their sets of zero
coordinates. -/
private theorem criticalPoints_torusCos_eq_range :
    criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) =
      range (torusCosCriticalPoint p) := by
  ext x
  refine ⟨fun hx ↦ ⟨_, exists_torusCosCriticalPoint_eq p hx⟩, ?_⟩
  rintro ⟨s, rfl⟩
  exact torusCosCriticalPoint_mem_criticalPoints p s

/-- **Binomial critical counts on a torus.** The cosine function on the torus `∀ i, AddCircle (p i)`
has exactly `(m choose j)` critical points of Morse index `j`, where `m = card ι`. -/
theorem criticalCount_torusCos (j : ℕ) :
    criticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) j =
      (Fintype.card ι).choose j := by
  classical
  have hset : {x ∈ criticalPoints (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) |
      manifoldMorseIndex (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) x = j} =
      torusCosCriticalPoint p '' ((Finset.univ : Finset ι).powersetCard j : Set (Finset ι)) := by
    ext x
    simp only [mem_sep_iff, mem_image, Finset.mem_coe, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hx, hj⟩
      refine ⟨{i | x i = 0}.toFinset, ?_, exists_torusCosCriticalPoint_eq p hx⟩
      rw [← hj, manifoldMorseIndex_torusCos p hx, ncard_eq_toFinset_card']
    · rintro ⟨s, hs, rfl⟩
      refine ⟨torusCosCriticalPoint_mem_criticalPoints p s, ?_⟩
      rw [manifoldMorseIndex_torusCos p (torusCosCriticalPoint_mem_criticalPoints p s),
        setOf_eq_zero_torusCosCriticalPoint, ncard_coe_finset, hs]
  rw [criticalCount_def, hset,
    (torusCosCriticalPoint_injective p).injOn.encard_image, encard_coe_eq_coe_finsetCard,
    Finset.card_powersetCard, Finset.card_univ]

/-- The cosine function on the torus `∀ i, AddCircle (p i)` has exactly `2 ^ m` critical points,
where `m = card ι`. -/
theorem totalCriticalCount_torusCos :
    totalCriticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCos p) =
      2 ^ Fintype.card ι := by
  rw [totalCriticalCount_def, criticalPoints_torusCos_eq_range,
    ← image_univ, (torusCosCriticalPoint_injective p).injOn.encard_image, encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_finset]
  norm_cast

end TauCeti

end
