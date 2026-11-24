/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Fin.Tuple
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Topology.Order.Sublevel
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Geometry.Manifold.Morse.Bott.Projectivization
import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Crossing a critical hyperplane of real projective space

On `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` consider the moment function with weight `1` on the first `N`
homogeneous coordinates and weight `0` on the last one
(`TauCeti.projectiveHyperplaneMomentFunction`),

`f [v] = (∑_{i < N} vᵢ²) / ∑ᵢ vᵢ² = 1 - v_N² / ∑ᵢ vᵢ²`.

For `N ≥ 2` its weights are not distinct, so it is not a Morse function. Its critical set is the
point `[e_N]`, where `f` takes its minimum `0`, together with the hyperplane `{v_N = 0}`
(`TauCeti.criticalPoints_projectiveHyperplaneMomentFunction`). For `N ≥ 1` this hyperplane is a
copy of `ℝℙᴺ⁻¹`, on which `f` attains its maximum `1`
(`TauCeti.projectiveHyperplaneMomentFunction_eq_one_iff`).

The Morse index is `1` at every point of the hyperplane
(`TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen`): the only
weight below the value `1` is the weight `0` of the normal coordinate `v_N`. Like every projective
moment function (`TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`), it is Morse–Bott.
For `N ≥ 1` the hyperplane is the image of `ℝℙᴺ⁻¹` under the smooth embedding `[v] ↦ [v : 0]`
(`TauCeti.projectiveHyperplaneEmbedding`, an instance of the embedding
`Projectivization.isSmoothEmbedding_map` of a linear inclusion), and it is a nondegenerate
critical submanifold (`TauCeti.isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding`).
The hyperplane and the minimum, embedded as copies of `ℝℙᴺ⁻¹` and of the point `ℝℙ⁰`, form a
Morse–Bott family (`TauCeti.isMorseBottFamily_projectiveHyperplaneMomentFunction`). These are the
general theorems `TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction` and
`TauCeti.isMorseBottFamily_projectiveMomentFunction` for the weights `1, …, 1, 0`. Since `ℝℙᴺ⁻¹`
needs `N ≥ 1`, every declaration of the section on the critical components is stated with ambient
space `ℝℙᴺ⁺¹`, that is, with `N + 1` in place of `N`. The negative normal bundle of the
hyperplane is its normal line bundle in `ℝℙᴺ`, the tautological line bundle of `ℝℙᴺ⁻¹`; for
`N = 2` it is the Möbius line over the circle `ℝℙ¹`. This identification is background here and
is not formalized in this file.

Below the top level, every sublevel `{f ≤ c}` with `0 ≤ c < 1` lies in the affine chart where
`v_N ≠ 0`, and in that chart it is the ball `{z | ‖z‖₂² / (1 + ‖z‖₂²) ≤ c}`, so it is contractible
(`TauCeti.contractibleSpace_sublevel_projectiveHyperplaneMomentFunction`). Hence for `1 ≤ d` the
relative homology of the critical band `({f ≤ d}, {f ≤ c}) = (ℝℙᴺ, {f ≤ c})` is the reduced
homology of `ℝℙᴺ`: it vanishes in degree `0`
(`TauCeti.isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction`) and agrees
with `Hₖ(ℝℙᴺ)` in every positive degree `k`
(`TauCeti.singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction`). With integer
coefficients it is `ℤ/2` in the odd degrees `k < N`, and it vanishes in the even positive degrees
for every coefficient ring in which `2` is right-regular.

This is a test of the Morse–Bott attachment formula
`Hₖ(M_{c+ε}, M_{c-ε}) ≅ H_{k-λ}(C; o(ν⁻))` for a critical component `C` of index `λ`, whose
coefficients are twisted by the orientation system `o(ν⁻)` of the negative normal bundle. For
`N = 2` the component is the circle, `λ = 1`, and the band has `H₁(ℝℙ², {f ≤ c}; ℤ) ≅ ℤ/2`
(`TauCeti.singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv`), the
zeroth homology of the circle with coefficients twisted by the Möbius orientation system. It is
not `ℤ`, the zeroth homology of the circle with constant integer coefficients
(`TauCeti.not_nonempty_linearEquiv_int_projectiveHyperplaneMomentFunction_two`),
so the integral formula cannot be stated with untwisted coefficients.

## Main results

* `TauCeti.criticalPoints_projectiveHyperplaneMomentFunction`: the critical set is the point
  `[e_N]` together with the hyperplane `{v_N = 0}`.
* `TauCeti.projectiveHyperplaneMomentFunction_eq_one_iff`: the hyperplane is the level set
  `f⁻¹(1)`.
* `TauCeti.range_projectiveHyperplaneEmbedding`: the embedding `[v] ↦ [v : 0]` of `ℝℙᴺ` into
  `ℝℙᴺ⁺¹` has image the hyperplane `{v_{N+1} = 0}`.
* `TauCeti.isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding`: the hyperplane
  `{v_{N+1} = 0}` of `ℝℙᴺ⁺¹` is a Morse–Bott critical submanifold.
* `TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen`: the Morse
  index at every point of the hyperplane is `1`.
* `TauCeti.isMorseBottFamily_projectiveHyperplaneMomentFunction`: on `ℝℙᴺ⁺¹`, the hyperplane
  `{v_{N+1} = 0}` and the minimum `[e_{N+1}]` exhibit the moment function as a Morse–Bott function.
* `TauCeti.contractibleSpace_sublevel_projectiveHyperplaneMomentFunction`: the sublevels
  `{f ≤ c}` with `0 ≤ c < 1` are contractible.
* `TauCeti.singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction` and
  `TauCeti.isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction`: the
  relative homology of a band crossing the top level is the reduced homology of `ℝℙᴺ`.
* `TauCeti.singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd` and
  `TauCeti.isZero_singularHomology_sublevelPair_projectiveHyperplaneMomentFunction_of_even`:
  it is `ℤ/2` in odd degrees below `N` with integer coefficients, and zero in even degrees
  when `2` is right-regular in the coefficients.
* `TauCeti.singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv` and
  `TauCeti.not_nonempty_linearEquiv_int_projectiveHyperplaneMomentFunction_two`:
  on `ℝℙ²` the band crossing the critical circle has `H₁ ≅ ℤ/2`, not `ℤ`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, course notes, 2006,
  Theorem 15.4, p. 146.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42.
-/

public section

noncomputable section

open CategoryTheory Limits Set Projectivization
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ}

variable (N) in
/-- The moment function on `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` with weight `1` on the first `N`
homogeneous coordinates and weight `0` on the last one, `[v] ↦ (∑_{i < N} vᵢ²) / ∑ᵢ vᵢ²`. Its
critical set is the point `[e_N]` and the hyperplane `{v_N = 0}`. -/
def projectiveHyperplaneMomentFunction : ℙ ℝ (Fin (N + 1) → ℝ) → ℝ :=
  projectiveMomentFunction ℝ fun i ↦ if i = Fin.last N then 0 else 1

/-- The moment function with weights `1, …, 1, 0` as a `TauCeti.projectiveMomentFunction`. -/
theorem projectiveHyperplaneMomentFunction_def :
    projectiveHyperplaneMomentFunction N =
      projectiveMomentFunction ℝ fun i ↦ if i = Fin.last N then 0 else 1 :=
  (rfl)

/-- The moment function is smooth. -/
theorem contMDiff_projectiveHyperplaneMomentFunction {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin N → ℝ) 𝓘(ℝ) r (projectiveHyperplaneMomentFunction N) :=
  contMDiff_projectiveMomentFunction _

/-- The moment function in homogeneous coordinates: `f [v] = 1 - v_N² / ∑ᵢ vᵢ²`. -/
@[simp]
theorem projectiveHyperplaneMomentFunction_mk (v : Fin (N + 1) → ℝ) (hv : v ≠ 0) :
    projectiveHyperplaneMomentFunction N (mk ℝ v hv) =
      1 - v (Fin.last N) ^ 2 / ∑ i, v i ^ 2 := by
  have hsum : ∑ i, (if i = Fin.last N then (0 : ℝ) else 1) * v i ^ 2 =
      ∑ i, v i ^ 2 - v (Fin.last N) ^ 2 := by
    simp [Fin.sum_univ_castSucc, Fin.castSucc_ne_last]
  rw [projectiveHyperplaneMomentFunction, projectiveMomentFunction_mk]
  simp only [Real.norm_eq_abs, sq_abs, hsum]
  rw [sub_div, div_self (by simpa using (sum_norm_sq_pos hv).ne')]

/-- The moment function is at most `1`, its value on the critical hyperplane. -/
theorem projectiveHyperplaneMomentFunction_le_one (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    projectiveHyperplaneMomentFunction N x ≤ 1 := by
  rw [projectiveHyperplaneMomentFunction_def]
  exact projectiveMomentFunction_le (fun i ↦ by split_ifs <;> norm_num) x

/-- The level set `f⁻¹(1)` is the hyperplane `{v_N = 0}`, the complement of the affine open where
the last homogeneous coordinate is nonzero. -/
theorem projectiveHyperplaneMomentFunction_eq_one_iff {x : ℙ ℝ (Fin (N + 1) → ℝ)} :
    projectiveHyperplaneMomentFunction N x = 1 ↔ x ∉ affineOpen (Fin.last N) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction_mk, mk_mem_affineOpen_iff, not_not, sub_eq_self,
    div_eq_zero_iff, or_iff_left (by simpa using (sum_norm_sq_pos hv).ne'),
    pow_eq_zero_iff two_ne_zero]

/-- In the affine chart where the last homogeneous coordinate is `1`, the moment function is
`z ↦ ‖z‖₂² / (1 + ‖z‖₂²)`. -/
theorem projectiveHyperplaneMomentFunction_affineChart_symm (z : Fin N → ℝ) :
    projectiveHyperplaneMomentFunction N ((affineChart (Fin.last N)).symm z) =
      (∑ j, z j ^ 2) / (1 + ∑ j, z j ^ 2) := by
  have h := congrFun (projectiveMomentFunction_comp_affineChart_symm (𝕜 := ℝ)
    (fun i ↦ if i = Fin.last N then 0 else 1) (Fin.last N)) z
  simp only [Function.comp_apply, ProjectiveMomentChart.model_apply, Fin.succAbove_last,
    Fin.castSucc_ne_last, ite_false, ite_true, one_mul, zero_add, Real.norm_eq_abs,
    sq_abs] at h
  exact h

/-- **The critical points.** The critical set of the moment function is the point `[e_N]` together
with the hyperplane `{v_N = 0}`, the complement of the affine open where `v_N ≠ 0`. -/
theorem criticalPoints_projectiveHyperplaneMomentFunction :
    criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveHyperplaneMomentFunction N) =
      insert (mk ℝ (Pi.single (Fin.last N) 1) (by simp)) (affineOpen (Fin.last N))ᶜ := by
  ext x
  rw [mem_insert_iff, mem_compl_iff]
  by_cases hx : x ∈ affineOpen (Fin.last N)
  · -- In the affine open the weight `0` of the last coordinate is simple, so the only critical
    -- point there is `[e_N]`.
    rw [projectiveHyperplaneMomentFunction_def,
      mem_criticalPoints_projectiveMomentFunction_iff (fun i hi ↦ by simp [hi]) hx]
    simp [hx]
  · -- On the hyperplane the value is `1`, the weight of every coordinate that can be nonzero.
    simp only [hx, not_false_eq_true, or_true, iff_true]
    induction x using Projectivization.ind with | h v hv =>
    rw [projectiveHyperplaneMomentFunction_def, mk_mem_criticalPoints_projectiveMomentFunction_iff,
      ← projectiveHyperplaneMomentFunction_def, projectiveHyperplaneMomentFunction_eq_one_iff.2 hx]
    intro j
    by_cases hj : j = Fin.last N
    · exact .inl (by simpa [hj, mk_mem_affineOpen_iff] using hx)
    · exact .inr (by simp [hj])

/-- **The Morse index along the critical hyperplane.** At every point of the critical hyperplane
`{v_N = 0}` the Morse index of the moment function is `1`: the only weight below the value `1` is
the weight `0` of the normal coordinate `v_N`. -/
theorem manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen
    {x : ℙ ℝ (Fin (N + 1) → ℝ)} (hx : x ∉ affineOpen (Fin.last N)) :
    manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) (projectiveHyperplaneMomentFunction N) x = 1 := by
  have hcrit : x ∈ criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveHyperplaneMomentFunction N) := by
    rw [criticalPoints_projectiveHyperplaneMomentFunction]
    exact .inr hx
  rw [projectiveHyperplaneMomentFunction_def] at hcrit ⊢
  rw [manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints hcrit,
    ← projectiveHyperplaneMomentFunction_def, projectiveHyperplaneMomentFunction_eq_one_iff.2 hx,
    Module.finrank_self, one_mul]
  have : {i | (if i = Fin.last N then (0 : ℝ) else 1) < 1} = {Fin.last N} := by
    ext i
    by_cases hi : i = Fin.last N <;> simp [hi]
  rw [this, ncard_singleton]

/-! ### The critical components

The statements in this section are indexed by `N + 1`: the ambient space is
`ℝℙᴺ⁺¹ = ℙ ℝ (Fin (N + 2) → ℝ)`, with moment function `projectiveHyperplaneMomentFunction (N + 1)`,
critical hyperplane `{v_{N+1} = 0}`, a copy of `ℝℙᴺ`, and minimum `[e_{N+1}]`. The circle `ℝℙ¹` in
`ℝℙ²`, which is the case `N = 2` in the module docstring, is the case `N = 1` here.
-/

section Components

/-- The homogeneous coordinates `(v, 0)` of the point `[v]` of `ℝℙᴺ` on the hyperplane
`{v_{N+1} = 0}` of `ℝℙᴺ⁺¹`, as a linear map. -/
private noncomputable def hyperplaneCoord : (Fin (N + 1) → ℝ) →ₗ[ℝ] Fin (N + 2) → ℝ :=
  Function.ExtendByZero.linearMap ℝ ℝ Fin.castSucc

private theorem injective_hyperplaneCoord : Function.Injective (hyperplaneCoord (N := N)) :=
  Function.extend_injective (Fin.castSucc_injective _) 0

/-- The coordinate of weight `0` of the homogeneous coordinates `(v, 0)` of a point of the
hyperplane vanishes. -/
private theorem hyperplaneCoord_apply_of_ne (v : Fin (N + 1) → ℝ) {i : Fin (N + 2)}
    (hi : (if i = Fin.last (N + 1) then (0 : ℝ) else 1) ≠ 1) : hyperplaneCoord v i = 0 := by
  obtain rfl : i = Fin.last (N + 1) := by
    by_contra h
    simp [h] at hi
  exact Function.ExtendByZero.linearMap_castSucc_last ℝ v

/-- Exactly `N + 1` coordinates of `ℝℙᴺ⁺¹` have weight `1`. -/
private theorem ncard_weight_eq_one :
    {i : Fin (N + 2) | (if i = Fin.last (N + 1) then (0 : ℝ) else 1) = 1}.ncard = N + 1 := by
  have : {i : Fin (N + 2) | (if i = Fin.last (N + 1) then (0 : ℝ) else 1) = 1} =
      {Fin.last (N + 1)}ᶜ := by
    ext i
    by_cases hi : i = Fin.last (N + 1) <;> simp [hi]
  rw [this, ncard_compl, ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

variable (N) in
/-- The critical hyperplane `{v_{N+1} = 0}` of `ℝℙᴺ⁺¹` as a smooth embedding of `ℝℙᴺ`, sending `[v]`
to `[v : 0]`. -/
noncomputable def projectiveHyperplaneEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin N → ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) ∞ (ℙ ℝ (Fin (N + 1) → ℝ))
      (ℙ ℝ (Fin (N + 2) → ℝ)) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_map (𝕜' := ℝ) _ injective_hyperplaneCoord (by simp))

private theorem coe_projectiveHyperplaneEmbedding :
    ⇑(projectiveHyperplaneEmbedding N) = map hyperplaneCoord injective_hyperplaneCoord :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

/-- The hyperplane embedding in homogeneous coordinates: `[v] ↦ [v : 0]`. -/
@[simp]
theorem projectiveHyperplaneEmbedding_mk (v : Fin (N + 1) → ℝ) (hv : v ≠ 0) :
    projectiveHyperplaneEmbedding N (mk ℝ v hv) =
      mk ℝ (Fin.snoc v 0) (Fin.snoc_ne_zero_iff.2 (.inl hv)) := by
  rw [coe_projectiveHyperplaneEmbedding, map_mk]
  simp only [hyperplaneCoord, Function.ExtendByZero.linearMap_castSucc_apply]

/-- The image of the hyperplane embedding is the hyperplane `{v_{N+1} = 0}`, the complement of the
affine open where the last homogeneous coordinate is nonzero. -/
theorem range_projectiveHyperplaneEmbedding :
    range (projectiveHyperplaneEmbedding N) = (affineOpen (Fin.last (N + 1)))ᶜ := by
  rw [coe_projectiveHyperplaneEmbedding,
    range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction _ injective_hyperplaneCoord
      (fun v _ ↦ hyperplaneCoord_apply_of_ne v) ncard_weight_eq_one,
    ← projectiveHyperplaneMomentFunction_def, criticalPoints_projectiveHyperplaneMomentFunction]
  -- Inside the critical set, the level set `f⁻¹(1)` is the hyperplane.
  ext x
  simp only [mem_inter_iff, mem_insert_iff, mem_compl_iff, mem_preimage, mem_singleton_iff,
    projectiveHyperplaneMomentFunction_eq_one_iff]
  exact ⟨And.right, fun hx ↦ ⟨.inr hx, hx⟩⟩

/-- **The critical hyperplane is a Morse–Bott critical submanifold.** The hyperplane
`{v_{N+1} = 0}`, a copy of `ℝℙᴺ`, is a nondegenerate critical submanifold of the moment function
on `ℝℙᴺ⁺¹`, as the projective subspace of the weight space of `1`. -/
theorem isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding :
    (projectiveHyperplaneEmbedding N).IsNondegenerateCriticalSubmanifold
      (projectiveHyperplaneMomentFunction (N + 1)) :=
  isNondegenerateCriticalSubmanifold_projectiveMomentFunction _ injective_hyperplaneCoord
    (fun v _ ↦ hyperplaneCoord_apply_of_ne v) ncard_weight_eq_one (by simp)

/-- The homogeneous coordinates `c • e_{N+1}` of the minimum `[e_{N+1}]` of the moment function on
`ℝℙᴺ⁺¹`, as a linear map on `ℝ¹`. -/
private noncomputable def minimumCoord : (Fin 1 → ℝ) →ₗ[ℝ] Fin (N + 2) → ℝ :=
  LinearMap.single ℝ (fun _ ↦ ℝ) (Fin.last (N + 1)) ∘ₗ LinearMap.proj 0

private theorem minimumCoord_apply (v : Fin 1 → ℝ) :
    minimumCoord (N := N) v = v 0 • Pi.single (Fin.last (N + 1)) 1 := by
  ext j
  by_cases hj : j = Fin.last (N + 1)
  · subst hj
    simp [minimumCoord]
  · simp [minimumCoord, hj]

private theorem injective_minimumCoord : Function.Injective (minimumCoord (N := N)) :=
  fun v w h ↦ funext fun j ↦ by
    rw [Subsingleton.elim j 0]
    simpa [minimumCoord] using h

/-- Every coordinate of weight `1` of a point of the line through `e_{N+1}` vanishes. -/
private theorem minimumCoord_apply_of_ne (v : Fin 1 → ℝ) {i : Fin (N + 2)}
    (hi : (if i = Fin.last (N + 1) then (0 : ℝ) else 1) ≠ 0) : minimumCoord v i = 0 := by
  have hi' : i ≠ Fin.last (N + 1) := by
    rintro rfl
    simp at hi
  simp [minimumCoord_apply, hi']

/-- Exactly one coordinate of `ℝℙᴺ⁺¹` has weight `0`. -/
private theorem ncard_weight_eq_zero :
    {i : Fin (N + 2) | (if i = Fin.last (N + 1) then (0 : ℝ) else 1) = 0}.ncard = 0 + 1 := by
  have : {i : Fin (N + 2) | (if i = Fin.last (N + 1) then (0 : ℝ) else 1) = 0} =
      {Fin.last (N + 1)} := by
    ext i
    by_cases hi : i = Fin.last (N + 1) <;> simp [hi]
  rw [this, ncard_singleton]

variable (N) in
/-- The minimum `[e_{N+1}]` of the moment function on `ℝℙᴺ⁺¹` as a smooth embedding of the point
`ℝℙ⁰`. -/
noncomputable def projectiveMinimumEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin 0 → ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) ∞ (ℙ ℝ (Fin 1 → ℝ))
      (ℙ ℝ (Fin (N + 2) → ℝ)) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_map (𝕜' := ℝ) _ injective_minimumCoord (by simp))

private theorem coe_projectiveMinimumEmbedding :
    ⇑(projectiveMinimumEmbedding N) = map minimumCoord injective_minimumCoord :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

/-- The point embedding sends the point of `ℝℙ⁰` to the minimum `[e_{N+1}]`. -/
@[simp]
theorem projectiveMinimumEmbedding_apply (x : ℙ ℝ (Fin 1 → ℝ)) :
    projectiveMinimumEmbedding N x = mk ℝ (Pi.single (Fin.last (N + 1)) 1) (by simp) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [coe_projectiveMinimumEmbedding, map_mk,
    mk_eq_mk_iff' ℝ _ _ _ (by simp)]
  exact ⟨v 0, (minimumCoord_apply v).symm⟩

/-- The homogeneous coordinates of the two critical components: those of the hyperplane for `true`
and those of the minimum for `false`. -/
private noncomputable def componentCoord :
    (b : Bool) → (Fin (cond b N 0 + 1) → ℝ) →ₗ[ℝ] Fin (N + 2) → ℝ
  | true => hyperplaneCoord
  | false => minimumCoord

variable (N) in
/-- The two critical components of the moment function on `ℝℙᴺ⁺¹`: for `true` the critical
hyperplane `{v_{N+1} = 0}`, a copy of `ℝℙᴺ`, and for `false` the minimum `[e_{N+1}]`, a copy of
`ℝℙ⁰`. -/
noncomputable def projectiveHyperplaneCriticalComponent :
    (b : Bool) → SmoothEmbedding 𝓘(ℝ, Fin (cond b N 0) → ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) ∞
      (ℙ ℝ (Fin (cond b N 0 + 1) → ℝ)) (ℙ ℝ (Fin (N + 2) → ℝ))
  | true => projectiveHyperplaneEmbedding N
  | false => projectiveMinimumEmbedding N

/-- The critical component indexed by `true` is the critical hyperplane. -/
@[simp]
theorem projectiveHyperplaneCriticalComponent_true :
    projectiveHyperplaneCriticalComponent N true = projectiveHyperplaneEmbedding N :=
  (rfl)

/-- The critical component indexed by `false` is the minimum. -/
@[simp]
theorem projectiveHyperplaneCriticalComponent_false :
    projectiveHyperplaneCriticalComponent N false = projectiveMinimumEmbedding N :=
  (rfl)

/-- **The moment function with weights `1, …, 1, 0` is a Morse–Bott function.** On `ℝℙᴺ⁺¹` its
critical components are the critical hyperplane `{v_{N+1} = 0}`, a copy of `ℝℙᴺ`, and the minimum
`[e_{N+1}]`, a copy of `ℝℙ⁰`. The index `1` along the hyperplane is
`manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen`. -/
theorem isMorseBottFamily_projectiveHyperplaneMomentFunction :
    IsMorseBottFamily (projectiveHyperplaneCriticalComponent N)
      (projectiveHyperplaneMomentFunction (N + 1)) :=
  isMorseBottFamily_projectiveMomentFunction (c := fun b ↦ cond b 1 0) (m := fun b ↦ cond b N 0)
    (by rintro (_ | _) (_ | _) h <;> simp_all)
    (by
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = Fin.last (N + 1)
      exacts [⟨false, by simp [hi]⟩, ⟨true, by simp [hi]⟩])
    componentCoord (by rintro (_ | _); exacts [injective_minimumCoord, injective_hyperplaneCoord])
    (by
      rintro (_ | _) v j hj
      exacts [minimumCoord_apply_of_ne v hj, hyperplaneCoord_apply_of_ne v hj])
    (by rintro (_ | _); exacts [ncard_weight_eq_zero, ncard_weight_eq_one])
    (by
      -- After unfolding the `Bool` matches, each goal is the coercion lemma of its embedding up to
      -- the type index `cond b N 0`, which reduces to `N` or `0` definitionally.
      rintro (_ | _) <;> simp only [projectiveHyperplaneCriticalComponent_true,
        projectiveHyperplaneCriticalComponent_false, componentCoord]
      exacts [coe_projectiveMinimumEmbedding, coe_projectiveHyperplaneEmbedding])

end Components

/-- Every sublevel below the top level lies in the affine open where the last homogeneous
coordinate is nonzero. -/
theorem sublevel_projectiveHyperplaneMomentFunction_subset_affineOpen {c : ℝ} (hc : c < 1) :
    {x | projectiveHyperplaneMomentFunction N x ≤ c} ⊆ affineOpen (Fin.last N) := fun x hx ↦ by
  rw [mem_ofPred_eq, projectiveHyperplaneMomentFunction_def] at hx
  by_contra h
  exact (lt_projectiveMomentFunction_of_notMem_affineOpen (fun i hi ↦ by simpa [hi] using hc) h
    |>.trans_le hx).false

/-- **The sublevels below the critical hyperplane are contractible.** For `0 ≤ c < 1`, the
sublevel `{f ≤ c}` is contractible. -/
theorem contractibleSpace_sublevel_projectiveHyperplaneMomentFunction {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) : ContractibleSpace {x | projectiveHyperplaneMomentFunction N x ≤ c} := by
  rw [projectiveHyperplaneMomentFunction_def]
  exact contractibleSpace_sublevel_projectiveMomentFunction (k := Fin.last N) (by simpa using hc₀)
    fun i hi ↦ by simpa [hi] using hc₁

/-! ### The relative homology of a band crossing the top level -/

section Homology

variable {A : Type*} [Category A] [HasCoproducts.{0} A] [Abelian A] (R : A) {c d : ℝ}

/-- **A band crossing the top level in positive degrees.** For `0 ≤ c < 1 ≤ d`, the lower sublevel
`{f ≤ c}` is contractible, so in every positive degree the relative homology of the band
`({f ≤ d}, {f ≤ c})` is the homology of `ℝℙᴺ`. The isomorphism is the map induced by the
identification `ℝℙᴺ = {f ≤ d}`, followed by the quotient map to relative homology. -/
def singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (hd : 1 ≤ d) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).obj
        (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) ≅
      (sublevelPair (projectiveHyperplaneMomentFunction N) (hc₁.le.trans hd)).singularHomology R
        (k + 1) :=
  have : ContractibleSpace
      (sublevelPair (projectiveHyperplaneMomentFunction N) (hc₁.le.trans hd)).snd :=
    contractibleSpace_sublevel_projectiveHyperplaneMomentFunction hc₀ hc₁
  ((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).mapIso
      (TopCat.isoOfHomeo (sublevelHomeomorphUniv fun x ↦
        (projectiveHyperplaneMomentFunction_le_one x).trans hd).symm) ≪≫
    (sublevelPair _ _).singularHomologyIsoOfContractibleSpace R k

/-- The forward map of `singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction` is
induced by the inclusion `ℝℙᴺ → {f ≤ d}`, followed by the quotient map to relative homology. -/
@[reassoc]
theorem singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction_hom (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (hd : 1 ≤ d) (k : ℕ) :
    (singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction R hc₀ hc₁ hd k).hom =
      ((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).map
          (TopCat.ofHom ⟨fun x ↦ ⟨x, (projectiveHyperplaneMomentFunction_le_one x).trans hd⟩,
            by fun_prop⟩) ≫
        (sublevelPair (projectiveHyperplaneMomentFunction N) (hc₁.le.trans hd)).singularHomologyπ
          R (k + 1) := by
  -- Instance search does not see through the subspace of `sublevelPair`, so the contractibility
  -- of `{f ≤ c}` is supplied explicitly.
  rw [singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction, Iso.trans_hom,
    Functor.mapIso_hom, @TopPair.singularHomologyIsoOfContractibleSpace_hom _ _ _ _ _ R
      (contractibleSpace_sublevel_projectiveHyperplaneMomentFunction hc₀ hc₁) k]
  congr 2
  ext x
  exact sublevelHomeomorphUniv_symm_apply _ x

/-- **A band in degree zero.** For `0 ≤ c ≤ d`, the zeroth relative homology of the band
`({f ≤ d}, {f ≤ c})` vanishes, since `{f ≤ d}` is path-connected (contractible for `d < 1`, and
all of `ℝℙᴺ` for `1 ≤ d`) and `{f ≤ c}` contains the minimum `[e_N]`. -/
theorem isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction
    (hc₀ : 0 ≤ c) (hcd : c ≤ d) :
    IsZero ((sublevelPair (projectiveHyperplaneMomentFunction N) hcd).singularHomology R 0) :=
  have : PathConnectedSpace (sublevelPair (projectiveHyperplaneMomentFunction N) hcd).fst := by
    rcases lt_or_ge d 1 with hd | hd
    · have := contractibleSpace_sublevel_projectiveHyperplaneMomentFunction (N := N)
        (hc₀.trans hcd) hd
      exact inferInstanceAs (PathConnectedSpace {x | projectiveHyperplaneMomentFunction N x ≤ d})
    · have hle x := (projectiveHyperplaneMomentFunction_le_one (N := N) x).trans hd
      exact (sublevelHomeomorphUniv hle).symm.surjective.pathConnectedSpace
        (sublevelHomeomorphUniv hle).symm.continuous
  have : Nonempty (sublevelPair (projectiveHyperplaneMomentFunction N) hcd).snd :=
    ⟨⟨mk ℝ (Pi.single (Fin.last N) 1) (by simp), by
      rw [mem_ofPred_eq, projectiveHyperplaneMomentFunction_def,
        projectiveMomentFunction_mk_single]
      simpa using hc₀⟩⟩
  TopPair.isZero_singularHomology_zero _ R

/-- **Integral homology of a band crossing the top level in odd degrees.** For `0 ≤ c < 1 ≤ d` and
odd `k < N`, `Hₖ({f ≤ d}, {f ≤ c}; ℤ) ≅ ℤ/2`. -/
def singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) (hd : 1 ≤ d) : ∀ {k : ℕ}, Odd k → k < N →
      (((sublevelPair (projectiveHyperplaneMomentFunction N) (hc₁.le.trans hd)).singularHomology
        (ModuleCat.of ℤ ℤ) k : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ZMod 2)
  | 0, hk, _ => (Nat.not_odd_zero hk).elim
  | k + 1, hk, hkN =>
    (singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction _ hc₀ hc₁ hd
      k).symm.toLinearEquiv ≪≫ₗ
      RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd hk hkN

/-- **Homology of a band crossing the top level in even degrees.** If `2` is right-regular in `S`,
then for `0 ≤ c < 1 ≤ d` and even `k`, `Hₖ({f ≤ d}, {f ≤ c}; S) = 0`. -/
theorem isZero_singularHomology_sublevelPair_projectiveHyperplaneMomentFunction_of_even
    (S : Type) [Ring S] (h2 : IsRightRegular (2 : S)) (hc₀ : 0 ≤ c) (hc₁ : c < 1) (hd : 1 ≤ d)
    {k : ℕ} (hk : Even k) :
    IsZero ((sublevelPair (projectiveHyperplaneMomentFunction N) (hc₁.le.trans hd)).singularHomology
      (ModuleCat.of S S) k) := by
  rcases k with _ | k
  · exact isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction _ hc₀ _
  · exact (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := N) S h2 hk
      k.succ_ne_zero).of_iso
        (singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction _ hc₀ hc₁ hd k).symm

/-- **The band crossing the critical circle of `ℝℙ²`.** On `ℝℙ²` the critical hyperplane is the
circle `ℝℙ¹`, and for `0 ≤ c < 1 ≤ d` the band crossing it has `H₁({f ≤ d}, {f ≤ c}; ℤ) ≅ ℤ/2`.
This is the zeroth homology of the circle with coefficients twisted by the orientation system of
the Möbius line, the normal bundle of the circle. -/
def singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (hd : 1 ≤ d) :
    ((sublevelPair (projectiveHyperplaneMomentFunction 2) (hc₁.le.trans hd)).singularHomology
      (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ZMod 2 :=
  singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd hc₀ hc₁ hd
    odd_one one_lt_two

/-- **The band crossing the critical circle of `ℝℙ²` does not have untwisted homology.** The group
`H₁({f ≤ d}, {f ≤ c}; ℤ) ≅ ℤ/2` of the band crossing the critical circle is not isomorphic to `ℤ`,
the zeroth homology of the circle with constant integer coefficients. -/
theorem not_nonempty_linearEquiv_int_projectiveHyperplaneMomentFunction_two
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) (hd : 1 ≤ d) :
    ¬ Nonempty (((sublevelPair (projectiveHyperplaneMomentFunction 2)
      (hc₁.le.trans hd)).singularHomology (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ℤ) := by
  rintro ⟨e⟩
  have : Finite ℤ :=
    .of_equiv _ ((singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv
      hc₀ hc₁ hd).symm.trans e).toEquiv
  exact not_finite ℤ

end Homology

end TauCeti
