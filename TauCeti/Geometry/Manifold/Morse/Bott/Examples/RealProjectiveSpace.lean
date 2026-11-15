/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.LinearEmbedding
public import TauCeti.Topology.Order.Sublevel
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.Morse.Bott.Slice
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

The function is Morse–Bott. For `N ≥ 1` the hyperplane is the image of `ℝℙᴺ⁻¹` under the smooth
embedding `[v] ↦ [v : 0]` (`TauCeti.projectiveHyperplaneEmbedding`, an instance of the embedding
`Projectivization.isSmoothEmbedding_map` of a linear inclusion). Along the line `t ↦ [v : t]`
through a point of the hyperplane the function is `t ↦ 1 - t² / (‖v‖₂² + t²)`, whose second
derivative `-2 / ‖v‖₂²` at `t = 0` is negative. Since the hyperplane has codimension one, this line
is transverse to it, so the Hessian is nondegenerate in the normal direction
(`TauCeti.isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding`) and the Morse index
is `1` at every point of the hyperplane
(`TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen`). The
minimum `[e_N]` is a nondegenerate critical point, so the hyperplane and the minimum, embedded
as copies of `ℝℙᴺ⁻¹` and of the point `ℝℙ⁰`, form a Morse–Bott family
(`TauCeti.isMorseBottFamily_projectiveHyperplaneMomentFunction`). Since `ℝℙᴺ⁻¹` needs `N ≥ 1`, these
declarations are stated with ambient space `ℝℙᴺ⁺¹`, that is, with `N + 1` in place of `N`. The
negative normal bundle of the hyperplane is its normal line bundle in `ℝℙᴺ`, the tautological line
bundle of `ℝℙᴺ⁻¹`; for `N = 2` it is the Möbius line over the circle `ℝℙ¹`. This identification is
background here and is not formalized in this file.

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
* `TauCeti.range_projectiveHyperplaneEmbedding`: the embedding `[v] ↦ [v : 0]` of `ℝℙᴺ⁻¹` into
  `ℝℙᴺ` has image the hyperplane.
* `TauCeti.isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding`: the hyperplane is a
  Morse–Bott critical submanifold.
* `TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen`: the Morse
  index at every point of the hyperplane is `1`.
* `TauCeti.isMorseBottFamily_projectiveHyperplaneMomentFunction`: the hyperplane and the minimum
  exhibit the moment function as a Morse–Bott function.
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

/-- A nonzero vector has a nonzero sum of squares. -/
private theorem sum_sq_ne_zero {v : Fin (N + 1) → ℝ} (hv : v ≠ 0) : ∑ i, v i ^ 2 ≠ 0 :=
  fun h ↦ hv <| funext fun i ↦ (Finset.sum_sq_eq_zero_iff _ _).1 h i (Finset.mem_univ i)

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
  rw [sub_div, div_self (sum_sq_ne_zero hv)]

/-- The moment function is at most `1`, its value on the critical hyperplane. -/
theorem projectiveHyperplaneMomentFunction_le_one (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    projectiveHyperplaneMomentFunction N x ≤ 1 := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction_mk, sub_le_self_iff]
  exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i))

/-- The level set `f⁻¹(1)` is the hyperplane `{v_N = 0}`, the complement of the affine open where
the last homogeneous coordinate is nonzero. -/
theorem projectiveHyperplaneMomentFunction_eq_one_iff {x : ℙ ℝ (Fin (N + 1) → ℝ)} :
    projectiveHyperplaneMomentFunction N x = 1 ↔ x ∉ affineOpen (Fin.last N) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction_mk, mk_mem_affineOpen_iff, not_not, sub_eq_self,
    div_eq_zero_iff, or_iff_left (sum_sq_ne_zero hv), pow_eq_zero_iff two_ne_zero]

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

private theorem hyperplaneCoord_apply (v : Fin (N + 1) → ℝ) :
    hyperplaneCoord v = Fin.snoc v 0 := by
  rw [← Fin.snoc_init_self (hyperplaneCoord v), hyperplaneCoord,
    Function.ExtendByZero.init_linearMap_castSucc, Function.ExtendByZero.linearMap_castSucc_last]

/-- Appending a coordinate to a nonzero vector gives a nonzero vector. -/
private theorem snoc_ne_zero {v : Fin (N + 1) → ℝ} (hv : v ≠ 0) (t : ℝ) :
    (Fin.snoc v t : Fin (N + 2) → ℝ) ≠ 0 := fun h ↦
  hv (funext fun j ↦ by simpa using congrFun h j.castSucc)

private theorem injective_hyperplaneCoord : Function.Injective (hyperplaneCoord (N := N)) :=
  Function.extend_injective (Fin.castSucc_injective _) 0

variable (N) in
/-- The critical hyperplane `{v_{N+1} = 0}` of `ℝℙᴺ⁺¹` as a smooth embedding of `ℝℙᴺ`, sending `[v]`
to `[v : 0]`. -/
noncomputable def projectiveHyperplaneEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin N → ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) ∞ (ℙ ℝ (Fin (N + 1) → ℝ))
      (ℙ ℝ (Fin (N + 2) → ℝ)) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_map _ injective_hyperplaneCoord (by simp))

/-- The hyperplane embedding in homogeneous coordinates: `[v] ↦ [v : 0]`. -/
@[simp]
theorem projectiveHyperplaneEmbedding_mk (v : Fin (N + 1) → ℝ) (hv : v ≠ 0) :
    projectiveHyperplaneEmbedding N (mk ℝ v hv) =
      -- A `by` block keeps the private `snoc_ne_zero` out of this public statement.
      mk ℝ (Fin.snoc v 0) (by exact snoc_ne_zero hv 0) := by
  rw [projectiveHyperplaneEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply, map_mk]
  simp only [hyperplaneCoord_apply]

/-- The image of the hyperplane embedding is the hyperplane `{v_{N+1} = 0}`, the complement of the
affine open where the last homogeneous coordinate is nonzero. -/
theorem range_projectiveHyperplaneEmbedding :
    range (projectiveHyperplaneEmbedding N) = (affineOpen (Fin.last (N + 1)))ᶜ := by
  ext x
  rw [mem_compl_iff]
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Projectivization.ind with | h v hv =>
    rw [projectiveHyperplaneEmbedding_mk, mk_mem_affineOpen_iff, Fin.snoc_last, not_not]
  · intro hx
    induction x using Projectivization.ind with | h w hw =>
    rw [mk_mem_affineOpen_iff, not_not] at hx
    obtain ⟨u, rfl⟩ : ∃ u, w = Fin.snoc u 0 := ⟨Fin.init w, by rw [← hx, Fin.snoc_init_self]⟩
    have hu : u ≠ 0 := by
      rintro rfl
      exact hw (funext fun j ↦ by induction j using Fin.lastCases <;> simp)
    exact ⟨mk ℝ u hu, projectiveHyperplaneEmbedding_mk u hu⟩

/-- The moment function along the line `t ↦ [v : t]` through the point `[v : 0]` of the critical
hyperplane: `t ↦ 1 - t² / (‖v‖₂² + t²)`. -/
private theorem projectiveHyperplaneMomentFunction_mk_snoc (v : Fin (N + 1) → ℝ) (t : ℝ)
    (h : Fin.snoc v t ≠ (0 : Fin (N + 2) → ℝ)) :
    projectiveHyperplaneMomentFunction (N + 1) (mk ℝ (Fin.snoc v t) h) =
      1 - t ^ 2 / (∑ j, v j ^ 2 + t ^ 2) := by
  rw [projectiveHyperplaneMomentFunction_mk, Fin.snoc_last, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The derivative of `t ↦ 1 - t² / (a + t²)` is `t ↦ -2at / (a + t²)²`. -/
private theorem hasDerivAt_one_sub_sq_div_add_sq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2 / (a + t ^ 2)) (-(2 * a * t / (a + t ^ 2) ^ 2)) t := by
  have hne : a + t ^ 2 ≠ 0 := by positivity
  convert (HasDerivAt.div (hasDerivAt_pow 2 t) ((hasDerivAt_pow 2 t).const_add a) hne).const_sub
    1 using 1
  field_simp
  ring

/-- The second derivative at `0` of `t ↦ 1 - t² / (a + t²)` is `-2 / a`. -/
private theorem iteratedDeriv_two_one_sub_sq_div_add_sq {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 2 (fun t : ℝ ↦ 1 - t ^ 2 / (a + t ^ 2)) 0 = -2 / a := by
  have h₂ : HasDerivAt (fun t : ℝ ↦ -(2 * a * t / (a + t ^ 2) ^ 2)) (-2 / a) 0 := by
    convert (HasDerivAt.div ((hasDerivAt_id (0 : ℝ)).const_mul (2 * a))
      (((hasDerivAt_pow 2 (0 : ℝ)).const_add a).fun_pow 2) (by simp [ha.ne'])).neg using 1
    · ext t
      simp
    · simp [field]
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    funext fun t ↦ (hasDerivAt_one_sub_sq_div_add_sq ha t).deriv]
  exact h₂.deriv

/-- Through a point `[v : 0]` of the critical hyperplane the line `t ↦ [v : t]` is a smooth curve,
and the moment function along it is `t ↦ 1 - t² / (‖v‖₂² + t²)`, with second derivative
`-2 / ‖v‖₂² < 0` at `t = 0`. -/
private theorem exists_slice_projectiveHyperplaneEmbedding (s : ℙ ℝ (Fin (N + 1) → ℝ)) :
    ∃ φ : ℝ → ℙ ℝ (Fin (N + 2) → ℝ), φ 0 = projectiveHyperplaneEmbedding N s ∧
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) 2 φ 0 ∧
      ContDiffAt ℝ 2 (projectiveHyperplaneMomentFunction (N + 1) ∘ φ) 0 ∧
      deriv (projectiveHyperplaneMomentFunction (N + 1) ∘ φ) 0 = 0 ∧
      iteratedDeriv 2 (projectiveHyperplaneMomentFunction (N + 1) ∘ φ) 0 < 0 := by
  induction s using Projectivization.ind with | h v hv =>
  have hF := snoc_ne_zero hv
  -- In homogeneous coordinates the curve is the affine line `t ↦ (v, 0) + t • e_{N+1}`.
  have hsnoc : (fun t : ℝ ↦ (Fin.snoc v t : Fin (N + 2) → ℝ)) =
      fun t ↦ Fin.snoc v 0 + t • Pi.single (Fin.last (N + 1)) 1 := by
    ext t j
    induction j using Fin.lastCases <;> simp [Fin.castSucc_ne_last]
  set a := ∑ j, v j ^ 2
  have ha : 0 < a := lt_of_le_of_ne (Finset.sum_nonneg fun j _ ↦ sq_nonneg (v j))
    (Ne.symm (sum_sq_ne_zero (N := N) hv))
  have hcomp : projectiveHyperplaneMomentFunction (N + 1) ∘ (fun t ↦ mk ℝ (Fin.snoc v t) (hF t)) =
      fun t ↦ 1 - t ^ 2 / (a + t ^ 2) :=
    funext fun t ↦ projectiveHyperplaneMomentFunction_mk_snoc v t (hF t)
  have hsmooth : ContDiff ℝ 2 fun t : ℝ ↦ 1 - t ^ 2 / (a + t ^ 2) :=
    contDiff_const.sub ((contDiff_id.pow 2).div (contDiff_const.add (contDiff_id.pow 2))
      fun t ↦ by positivity)
  refine ⟨fun t ↦ mk ℝ (Fin.snoc v t) (hF t), ?_, ?_, ?_, ?_, ?_⟩
  · rw [projectiveHyperplaneEmbedding_mk]
  · refine contMDiffAt_of_eventually_eq_mk (F := fun t : ℝ ↦ (Fin.snoc v t : Fin (N + 2) → ℝ))
      ?_ (Filter.Eventually.of_forall fun t ↦ ⟨hF t, rfl⟩)
    rw [hsnoc]
    exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff.contMDiffAt
  · rw [hcomp]
    exact hsmooth.contDiffAt
  · rw [hcomp, (hasDerivAt_one_sub_sq_div_add_sq ha 0).deriv]
    simp
  · rw [hcomp, iteratedDeriv_two_one_sub_sq_div_add_sq ha]
    exact div_neg_of_neg_of_pos (by norm_num) ha

/-- The normal space of the critical hyperplane is a line. -/
private theorem finrank_normalSpace_projectiveHyperplaneEmbedding (s : ℙ ℝ (Fin (N + 1) → ℝ)) :
    Module.finrank ℝ ((projectiveHyperplaneEmbedding N).NormalSpace s (by simp)) = 1 := by
  rw [SmoothEmbedding.finrank_normalSpace]
  -- Tangent spaces of `ℝℙᴺ` and `ℝℙᴺ⁺¹` are the model spaces `Fin N → ℝ` and `Fin (N + 1) → ℝ`.
  change Module.finrank ℝ (Fin (N + 1) → ℝ) - Module.finrank ℝ (Fin N → ℝ) = 1
  simp

/-- The critical hyperplane is a critical submanifold: it consists of critical points. -/
private theorem isCriticalSubmanifold_projectiveHyperplaneEmbedding :
    (projectiveHyperplaneEmbedding N).IsCriticalSubmanifold
      (projectiveHyperplaneMomentFunction (N + 1)) where
  contMDiffAt _ := contMDiff_projectiveHyperplaneMomentFunction.contMDiffAt
  mem_criticalPoints s := by
    rw [criticalPoints_projectiveHyperplaneMomentFunction]
    exact .inr (range_projectiveHyperplaneEmbedding (N := N) ▸ mem_range_self s)

/-- Along the line `t ↦ [v : t]` the slice of the moment function through a point of the critical
hyperplane is transverse to it. -/
private theorem exists_slice_bijective_projectiveHyperplaneEmbedding
    (s : ℙ ℝ (Fin (N + 1) → ℝ)) :
    ∃ φ : ℝ → ℙ ℝ (Fin (N + 2) → ℝ), φ 0 = projectiveHyperplaneEmbedding N s ∧
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) 2 φ 0 ∧
      IsNondegenerateCriticalPoint (projectiveHyperplaneMomentFunction (N + 1) ∘ φ) 0 ∧
      iteratedDeriv 2 (projectiveHyperplaneMomentFunction (N + 1) ∘ φ) 0 < 0 ∧
      Function.Bijective fun t : ℝ ↦ (projectiveHyperplaneEmbedding N).normalClass s (by simp)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) φ 0 t) := by
  obtain ⟨φ, hφ0, hφ, hsmooth, hderiv, hneg⟩ := exists_slice_projectiveHyperplaneEmbedding s
  have hcrit := isCriticalSubmanifold_projectiveHyperplaneEmbedding (N := N)
  refine ⟨φ, hφ0, hφ, (isNondegenerateCriticalPoint_real_iff hsmooth).2 ⟨hderiv, hneg.ne⟩, hneg,
    hcrit.bijective_normalClass_mfderiv_of_finrank_eq_one (by simp) hφ0 hφ
      (Module.finrank_self ℝ) (finrank_normalSpace_projectiveHyperplaneEmbedding s) (v := 1) ?_⟩
  rw [fderiv_fderiv_apply_eq_smul_iteratedDeriv, smul_eq_mul, one_mul, one_mul]
  exact hneg.ne

/-- **The critical hyperplane is a Morse–Bott critical submanifold.** The hyperplane
`{v_{N+1} = 0}`, a copy of `ℝℙᴺ`, is a nondegenerate critical submanifold of the moment function
on `ℝℙᴺ⁺¹`: the Hessian is nondegenerate in the normal direction. -/
theorem isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding :
    (projectiveHyperplaneEmbedding N).IsNondegenerateCriticalSubmanifold
      (projectiveHyperplaneMomentFunction (N + 1)) := by
  have hcrit := isCriticalSubmanifold_projectiveHyperplaneEmbedding (N := N)
  refine (hcrit.isNondegenerateCriticalSubmanifold_iff (by simp)).2 fun s ↦ ?_
  obtain ⟨φ, hφ0, hφ, hN, -, hbij⟩ := exists_slice_bijective_projectiveHyperplaneEmbedding s
  exact hcrit.ker_normalHessian_eq_bot_of_isNondegenerateCriticalPoint_comp (by simp) hφ0 hφ
    hbij.2 hN

/-- **The Morse index along the critical hyperplane.** At every point of the critical hyperplane
`{v_{N+1} = 0}` of `ℝℙᴺ⁺¹` the Morse index of the moment function is `1`: the Hessian is negative
in the direction normal to the hyperplane. -/
theorem manifoldMorseIndex_projectiveHyperplaneMomentFunction_of_notMem_affineOpen
    {x : ℙ ℝ (Fin (N + 2) → ℝ)} (hx : x ∉ affineOpen (Fin.last (N + 1))) :
    manifoldMorseIndex 𝓘(ℝ, Fin (N + 1) → ℝ) (projectiveHyperplaneMomentFunction (N + 1)) x =
      1 := by
  obtain ⟨s, rfl⟩ : x ∈ range (projectiveHyperplaneEmbedding N) := by
    rwa [range_projectiveHyperplaneEmbedding]
  obtain ⟨φ, hφ0, hφ, -, hneg, hbij⟩ := exists_slice_bijective_projectiveHyperplaneEmbedding s
  rw [← isCriticalSubmanifold_projectiveHyperplaneEmbedding.morseIndex_comp (by simp) hφ0 hφ hbij]
  exact morseIndex_real_of_neg hneg

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

variable (N) in
/-- The minimum `[e_{N+1}]` of the moment function on `ℝℙᴺ⁺¹` as a smooth embedding of the point
`ℝℙ⁰`. -/
noncomputable def projectiveMinimumEmbedding :
    SmoothEmbedding 𝓘(ℝ, Fin 0 → ℝ) 𝓘(ℝ, Fin (N + 1) → ℝ) ∞ (ℙ ℝ (Fin 1 → ℝ))
      (ℙ ℝ (Fin (N + 2) → ℝ)) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_map _ injective_minimumCoord (by simp))

/-- The point embedding sends the point of `ℝℙ⁰` to the minimum `[e_{N+1}]`. -/
@[simp]
theorem projectiveMinimumEmbedding_apply (x : ℙ ℝ (Fin 1 → ℝ)) :
    projectiveMinimumEmbedding N x = mk ℝ (Pi.single (Fin.last (N + 1)) 1) (by simp) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveMinimumEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply, map_mk,
    mk_eq_mk_iff' ℝ _ _ _ (by simp)]
  exact ⟨v 0, (minimumCoord_apply v).symm⟩

/-- The minimum `[e_{N+1}]` is a Morse–Bott critical submanifold of dimension `0`: it is a
nondegenerate critical point, since its weight `0` is simple. -/
theorem isNondegenerateCriticalSubmanifold_projectiveMinimumEmbedding :
    (projectiveMinimumEmbedding N).IsNondegenerateCriticalSubmanifold
      (projectiveHyperplaneMomentFunction (N + 1)) :=
  SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton.2 fun _ ↦ by
    rw [projectiveMinimumEmbedding_apply, projectiveHyperplaneMomentFunction,
      isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff]
    intro i hi
    simp [hi]

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
critical components are the critical hyperplane `{v_{N+1} = 0}`, a copy of `ℝℙᴺ` of index `1`,
and the minimum `[e_{N+1}]`, a copy of `ℝℙ⁰` of index `0`. -/
theorem isMorseBottFamily_projectiveHyperplaneMomentFunction :
    IsMorseBottFamily (projectiveHyperplaneCriticalComponent N)
      (projectiveHyperplaneMomentFunction (N + 1)) := by
  refine .of_pairwise_disjoint (by simp) contMDiff_projectiveHyperplaneMomentFunction
    (fun b ↦ ?_) ?_ ?_
  · cases b
    · exact isNondegenerateCriticalSubmanifold_projectiveMinimumEmbedding
    · exact isNondegenerateCriticalSubmanifold_projectiveHyperplaneEmbedding
  · -- The minimum lies in the affine open where the last coordinate is nonzero.
    have hmin : range (projectiveMinimumEmbedding N) ⊆ affineOpen (Fin.last (N + 1)) := by
      rintro _ ⟨x, rfl⟩
      simp [mk_mem_affineOpen_iff]
    have hdisj : Disjoint (range (projectiveMinimumEmbedding N))
        (range (projectiveHyperplaneEmbedding N)) := by
      rw [range_projectiveHyperplaneEmbedding]
      exact disjoint_compl_right.mono_left hmin
    rintro (_ | _) (_ | _) h
    · exact (h rfl).elim
    · exact hdisj
    · exact hdisj.symm
    · exact (h rfl).elim
  · intro x hx
    rw [criticalPoints_projectiveHyperplaneMomentFunction] at hx
    rcases hx with rfl | hx
    · exact mem_iUnion.2 ⟨false, ⟨mk ℝ 1 one_ne_zero, projectiveMinimumEmbedding_apply _⟩⟩
    · exact mem_iUnion.2 ⟨true, range_projectiveHyperplaneEmbedding (N := N) ▸ hx⟩

end Components

/-- Every sublevel below the top level lies in the affine open where the last homogeneous
coordinate is nonzero. -/
theorem sublevel_projectiveHyperplaneMomentFunction_subset_affineOpen {c : ℝ} (hc : c < 1) :
    {x | projectiveHyperplaneMomentFunction N x ≤ c} ⊆ affineOpen (Fin.last N) := fun x hx ↦ by
  by_contra h
  exact (projectiveHyperplaneMomentFunction_eq_one_iff.2 h ▸ hx : (1 : ℝ) ≤ c).not_gt hc

/-- **The sublevels below the critical hyperplane are contractible.** For `0 ≤ c < 1`, the
sublevel `{f ≤ c}` is contractible. -/
theorem contractibleSpace_sublevel_projectiveHyperplaneMomentFunction {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) : ContractibleSpace {x | projectiveHyperplaneMomentFunction N x ≤ c} := by
  set X := {x | projectiveHyperplaneMomentFunction N x ≤ c}
  set Z : Set (Fin N → ℝ) := {z | (∑ j, z j ^ 2) / (1 + ∑ j, z j ^ 2) ≤ c} with hZdef
  have hZ : affineChart (Fin.last N) '' (X ∩ affineOpen (Fin.last N)) = Z := by
    rw [inter_comm, ← affineChart_source, PartialEquiv.image_source_inter_eq', affineChart_target,
      univ_inter]
    ext z
    simp only [X, Z, mem_preimage, mem_ofPred_eq,
      projectiveHyperplaneMomentFunction_affineChart_symm]
  -- The function `s ↦ s / (1 + s)` is monotone on `s ≥ 0`, and scaling `z` by `b ∈ [0, 1]`
  -- scales `‖z‖₂²` by `b² ≤ 1`.
  have hstar : StarConvex ℝ 0 Z := by
    intro y hy a b _ hb hab
    have hs : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg (y j)
    have hscale : ∑ j, (a • (0 : Fin N → ℝ) + b • y) j ^ 2 = b ^ 2 * ∑ j, y j ^ 2 := by
      simp only [smul_zero, zero_add, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    have hb1 : b ^ 2 ≤ 1 := pow_le_one₀ hb (hab ▸ le_add_of_nonneg_left ‹0 ≤ a›)
    rw [hZdef, mem_ofPred_eq] at hy ⊢
    refine le_trans ?_ hy
    rw [hscale, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg b) hs, mul_nonneg (sub_nonneg.2 hb1) hs]
  have hne : Z.Nonempty := ⟨0, by simpa [Z] using hc₀⟩
  have := hstar.contractibleSpace hne
  have hX : X = X ∩ affineOpen (Fin.last N) :=
    (inter_eq_left.2 (sublevel_projectiveHyperplaneMomentFunction_subset_affineOpen hc₁)).symm
  exact ((Homeomorph.setCongr hX).trans (interAffineOpenHomeomorph hZ)).contractibleSpace

/-! ### The relative homology of a band crossing the top level -/

section Homology

variable {A : Type*} [Category A] [HasCoproducts.{0} A] [Abelian A] (R : A) {c d : ℝ}

/-- The homeomorphism from `ℝℙᴺ` to its whole sublevel `{f ≤ d}`, for `1 ≤ d`. -/
private def homeomorphTopSublevel (hd : 1 ≤ d) :
    ℙ ℝ (Fin (N + 1) → ℝ) ≃ₜ {x | projectiveHyperplaneMomentFunction N x ≤ d} where
  toFun x := ⟨x, (projectiveHyperplaneMomentFunction_le_one x).trans hd⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_subtype_val

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
      (TopCat.isoOfHomeo (homeomorphTopSublevel hd)) ≪≫
    -- The source of `singularHomologyπ` is the homology of the singular simplicial set of
    -- `{f ≤ d}`, which agrees with the target of the first factor only up to unfolding
    -- `singularHomologyFunctor` and `TopPair.toSSetPair`; so the morphism is left implicit.
    @asIso _ _ _ _ _ (TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R k)

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
  dsimp only [singularHomologyIsoSublevelPairProjectiveHyperplaneMomentFunction, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, TopCat.isoOfHomeo_hom]
  -- `homeomorphTopSublevel hd` is defined with the inclusion `x ↦ ⟨x, _⟩` as its forward map.
  rfl

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
    · exact (homeomorphTopSublevel hd).surjective.pathConnectedSpace
        (homeomorphTopSublevel hd).continuous
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
