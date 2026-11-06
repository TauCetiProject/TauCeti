/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Analysis.Calculus.Morse.QuadraticMap
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
origin. These facts about such quotients of diagonal forms are proved in
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
open QuadraticMap (weightedSumSquares weightedSumSquares_apply)
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

/-- The weighted sum of squares, read in the affine chart at `i`, is the quotient
`z ↦ (wᵢ + P z) / (1 + N z)` of the diagonal forms `P` and `N` with weights `w ∘ i.succAbove`
and `1`. -/
private theorem projectiveWeightedSumSquares_comp_affineChart_symm (i : Fin (n + 1)) :
    projectiveWeightedSumSquares w ∘ (affineChart i).symm = fun z ↦
      (w i + weightedSumSquares ℝ (fun k ↦ w (i.succAbove k)) z) /
        (1 + weightedSumSquares ℝ (1 : Fin n → ℝ) z) := by
  funext z
  rw [comp_apply, projectiveWeightedSumSquares_affineChart_symm]
  simp [weightedSumSquares_apply, _root_.sq]

/-! ### Smoothness and critical points -/

/-- The weighted sum of squares on real projective space is smooth, indeed analytic. -/
theorem contMDiff_projectiveWeightedSumSquares {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) r (projectiveWeightedSumSquares w) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hchart : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) r
      ((projectiveWeightedSumSquares w ∘ (affineChart i).symm) ∘ affineChart i) (affineOpen i) := by
    rw [projectiveWeightedSumSquares_comp_affineChart_symm]
    exact (QuadraticMap.contDiff_const_add_weightedSumSquares_div _ _).contMDiff.comp_contMDiffOn
      (contMDiffOn_affineChart i r)
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
  rw [coe_affineOpenPartialHomeomorph_extend_symm, affineChart_symm_zero] at h
  rw [projectiveWeightedSumSquares_comp_affineChart_symm] at h
  exact h (QuadraticMap.isNondegenerateCriticalPoint_const_add_weightedSumSquares_div
    fun k ↦ hw _ (Fin.succAbove_ne i k))

/-- **The Morse index of a coordinate point.** If the weight `wᵢ` differs from all the other
weights, the Morse index of the weighted sum of squares at the coordinate point `[eᵢ]` is the number
of weights smaller than `wᵢ`. -/
theorem manifoldMorseIndex_projectiveWeightedSumSquares {i : Fin (n + 1)}
    (hw : ∀ j, j ≠ i → w j ≠ w i) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveWeightedSumSquares w)
      (mk ℝ (Pi.single i 1) (by simp)) = {j | w j < w i}.ncard := by
  have hb' : ∀ k, w (i.succAbove k) ≠ w i := fun k ↦ hw _ (Fin.succAbove_ne i k)
  have hnd := QuadraticMap.isNondegenerateCriticalPoint_const_add_weightedSumSquares_div hb'
  rw [← projectiveWeightedSumSquares_comp_affineChart_symm] at hnd
  have h := manifoldMorseIndex_symm_eq_morseIndex_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := 2)
      (affineOpenPartialHomeomorph_mem_atlas i)) (f := projectiveWeightedSumSquares w)
    (v := 0) (by simp) (by simpa using hnd)
  rw [coe_affineOpenPartialHomeomorph_extend_symm, affineChart_symm_zero] at h
  rw [h, projectiveWeightedSumSquares_comp_affineChart_symm,
    QuadraticMap.morseIndex_const_add_weightedSumSquares_div hb']
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
    rw [coe_affineOpenPartialHomeomorph_extend_symm, coe_affineOpenPartialHomeomorph_extend,
      projectiveWeightedSumSquares_comp_affineChart_symm] at hcrit
    have hz := QuadraticMap.eq_zero_of_fderiv_const_add_weightedSumSquares_div_eq_zero
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
    ← image_univ, mk_single_left_injective.encard_image, encard_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin, Nat.cast_succ]

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
  rw [criticalCount_def, hset, mk_single_left_injective.encard_image, σ.injective.encard_image]
  split_ifs with hj
  · rw [encard_eq_one]
    exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, by ext m; simp [Fin.ext_iff]⟩
  · rw [encard_eq_zero, eq_empty_iff_forall_notMem]
    intro m hm
    exact hj (hm ▸ Nat.le_of_lt_succ m.2)

end TauCeti
