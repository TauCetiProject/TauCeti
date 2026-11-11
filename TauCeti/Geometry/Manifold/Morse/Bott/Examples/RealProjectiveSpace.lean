/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Topology.Order.Sublevel
import Mathlib.Analysis.Convex.Contractible

/-!
# Crossing a critical hyperplane of real projective space

On `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` consider the moment function with weight `1` on the first `N`
homogeneous coordinates and weight `0` on the last one
(`TauCeti.projectiveHyperplaneMomentFunction`),

`f [v] = (∑_{i < N} vᵢ²) / ∑ᵢ vᵢ² = 1 - v_N² / ∑ᵢ vᵢ²`.

Its weights are not distinct, so it is not a Morse function. Its critical set is the point
`[e_N]`, the minimum at the level `0`, together with the hyperplane `{v_N = 0} ≅ ℝℙᴺ⁻¹`, on which
`f` attains its maximum `1` (`TauCeti.criticalPoints_projectiveHyperplaneMomentFunction`). At the
coordinate points of the hyperplane the Morse index is `1`
(`TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_mk_single_castSucc`): the Hessian
is negative only in the direction normal to the hyperplane. The hyperplane is the critical
component of a Morse–Bott function of index `1`, whose negative normal bundle is the normal line
bundle of `ℝℙᴺ⁻¹` in `ℝℙᴺ`, the tautological line bundle; for `N = 2` it is the Möbius line over
the circle `ℝℙ¹`. These two facts are background here and are not formalized in this file.

Below the top level, every sublevel `{f ≤ c}` with `0 ≤ c < 1` lies in the affine chart where
`v_N ≠ 0`, and in that chart it is the ball `{z | ‖z‖₂² / (1 + ‖z‖₂²) ≤ c}`, so it is contractible
(`TauCeti.contractibleSpace_sublevel_projectiveHyperplaneMomentFunction`). Hence the relative
homology of the critical band `({f ≤ 1}, {f ≤ c}) = (ℝℙᴺ, {f ≤ c})` is the reduced homology of
`ℝℙᴺ`: it vanishes in degree `0`
(`TauCeti.isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction`) and agrees
with `Hₖ(ℝℙᴺ)` in every positive degree `k`
(`TauCeti.singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIso`). With integer
coefficients it is `ℤ/2` in the odd degrees `k < N` and vanishes in the even positive degrees.

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

* `TauCeti.criticalPoints_projectiveHyperplaneMomentFunction`: the critical set is the minimum
  `[e_N]` together with the hyperplane `{v_N = 0}`.
* `TauCeti.projectiveHyperplaneMomentFunction_eq_one_iff`: the hyperplane is the top level
  `f⁻¹(1)`.
* `TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_mk_single_castSucc`: the Morse
  index at the coordinate points `[eₖ]`, `k < N`, of the hyperplane is `1`.
* `TauCeti.contractibleSpace_sublevel_projectiveHyperplaneMomentFunction`: the sublevels below
  the top level are contractible.
* `TauCeti.singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIso` and
  `TauCeti.isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction`: the
  relative homology of the top critical band is the reduced homology of `ℝℙᴺ`.
* `TauCeti.singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd` and
  `TauCeti.isZero_singularHomology_int_sublevelPair_projectiveHyperplaneMomentFunction_of_even`:
  with integer coefficients it is `ℤ/2` in odd degrees below `N` and zero in even positive degrees.
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
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ}

variable (N) in
/-- The moment function on `ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)` with weight `1` on the first `N`
homogeneous coordinates and weight `0` on the last one, `[v] ↦ (∑_{i < N} vᵢ²) / ∑ᵢ vᵢ²`. Its
critical set is the point `[e_N]` and the hyperplane `{v_N = 0}`. -/
def projectiveHyperplaneMomentFunction : ℙ ℝ (Fin (N + 1) → ℝ) → ℝ :=
  projectiveMomentFunction ℝ fun i ↦ if i = Fin.last N then 0 else 1

/-- The moment function in homogeneous coordinates: `f [v] = 1 - v_N² / ∑ᵢ vᵢ²`. -/
@[simp]
theorem projectiveHyperplaneMomentFunction_mk (v : Fin (N + 1) → ℝ) (hv : v ≠ 0) :
    projectiveHyperplaneMomentFunction N (mk ℝ v hv) =
      1 - v (Fin.last N) ^ 2 / ∑ i, v i ^ 2 := by
  have hpos : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun i _ ↦ sq_nonneg (v i))
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hj).symm⟩
  have hsum : ∑ i, (if i = Fin.last N then (0 : ℝ) else 1) * v i ^ 2 =
      ∑ i, v i ^ 2 - v (Fin.last N) ^ 2 := by
    simp [Fin.sum_univ_castSucc, Fin.castSucc_ne_last]
  rw [projectiveHyperplaneMomentFunction, projectiveMomentFunction_mk]
  simp only [Real.norm_eq_abs, sq_abs, hsum]
  rw [sub_div, div_self hpos.ne']

/-- The moment function is at most `1`, its value on the critical hyperplane. -/
theorem projectiveHyperplaneMomentFunction_le_one (x : ℙ ℝ (Fin (N + 1) → ℝ)) :
    projectiveHyperplaneMomentFunction N x ≤ 1 := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction_mk, sub_le_self_iff]
  exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i))

/-- The top level `f⁻¹(1)` is the hyperplane `{v_N = 0}`, the complement of the affine open where
the last homogeneous coordinate is nonzero. -/
theorem projectiveHyperplaneMomentFunction_eq_one_iff {x : ℙ ℝ (Fin (N + 1) → ℝ)} :
    projectiveHyperplaneMomentFunction N x = 1 ↔ x ∉ affineOpen (Fin.last N) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction_mk, mk_mem_affineOpen_iff, not_not, sub_eq_self,
    div_eq_zero_iff, or_iff_left (Finset.sum_pos' (fun i _ ↦ sq_nonneg (v i)) ?_).ne',
    pow_eq_zero_iff two_ne_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  exact ⟨j, Finset.mem_univ j, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hj).symm⟩

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

/-- **The critical points.** The critical set of the moment function is its minimum `[e_N]`
together with the hyperplane `{v_N = 0}`, where it attains its maximum `1`. -/
theorem criticalPoints_projectiveHyperplaneMomentFunction :
    criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveHyperplaneMomentFunction N) =
      insert (mk ℝ (Pi.single (Fin.last N) 1) (by simp)) (affineOpen (Fin.last N))ᶜ := by
  ext x
  induction x using Projectivization.ind with | h v hv =>
  rw [projectiveHyperplaneMomentFunction, mk_mem_criticalPoints_projectiveMomentFunction_iff,
    ← projectiveHyperplaneMomentFunction, mem_insert_iff, mem_compl_iff, mk_mem_affineOpen_iff,
    not_not]
  by_cases hN : v (Fin.last N) = 0
  · -- On the hyperplane the value is `1`, the weight of every coordinate that can be nonzero.
    have h1 : projectiveHyperplaneMomentFunction N (mk ℝ v hv) = 1 := by
      rw [projectiveHyperplaneMomentFunction_mk, hN]
      simp
    simp only [hN, or_true, iff_true, h1]
    intro j
    by_cases hj : j = Fin.last N
    · exact .inl (hj ▸ hN)
    · exact .inr (by simp [hj])
  · simp only [hN, or_false]
    constructor
    · -- The last coordinate is nonzero, so the value is its weight `0`, and every other
      -- coordinate, of weight `1`, vanishes.
      intro h
      have h0 : projectiveHyperplaneMomentFunction N (mk ℝ v hv) = 0 := by
        exact (by simpa [hN] using h (Fin.last N) : (0 : ℝ) = _).symm
      refine (mk_eq_mk_iff' ℝ _ _ hv (by simp)).2 ⟨v (Fin.last N), funext fun j ↦ ?_⟩
      by_cases hj : j = Fin.last N
      · subst hj
        simp
      · have := h j
        simp only [h0, hj, ite_false, one_ne_zero, or_false] at this
        simp [hj, this]
    · intro h
      obtain ⟨a, ha⟩ := (mk_eq_mk_iff' ℝ _ _ hv (by simp)).1 h
      have h0 : projectiveHyperplaneMomentFunction N (mk ℝ v hv) = 0 := by
        rw [h, projectiveHyperplaneMomentFunction, projectiveMomentFunction_mk_single]
        simp
      intro j
      by_cases hj : j = Fin.last N
      · exact .inr (by simp [hj, h0])
      · exact .inl (by simp [← ha, hj])

/-- **The index of the critical hyperplane.** At each coordinate point `[eₖ]`, `k < N`, of the
critical hyperplane `{v_N = 0}`, the Morse index is `1`: the only weight below the weight `1` of
`eₖ` is the weight `0` of the normal coordinate `v_N`. -/
theorem manifoldMorseIndex_projectiveHyperplaneMomentFunction_mk_single_castSucc (k : Fin N) :
    manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) (projectiveHyperplaneMomentFunction N)
      (mk ℝ (Pi.single k.castSucc 1) (by simp)) = 1 := by
  rw [projectiveHyperplaneMomentFunction, manifoldMorseIndex_projectiveMomentFunction,
    Module.finrank_self, one_mul]
  have : {i | (if i = Fin.last N then (0 : ℝ) else 1) <
      if k.castSucc = Fin.last N then 0 else 1} = {Fin.last N} := by
    ext i
    by_cases hi : i = Fin.last N <;> simp [hi, Fin.castSucc_ne_last]
  rw [this, ncard_singleton]

/-- Every sublevel below the top level lies in the affine open where the last homogeneous
coordinate is nonzero. -/
theorem sublevel_projectiveHyperplaneMomentFunction_subset_affineOpen {c : ℝ} (hc : c < 1) :
    {x | projectiveHyperplaneMomentFunction N x ≤ c} ⊆ affineOpen (Fin.last N) := fun x hx ↦ by
  by_contra h
  exact (projectiveHyperplaneMomentFunction_eq_one_iff.2 h ▸ hx : (1 : ℝ) ≤ c).not_gt hc

/-- **The sublevels below the critical hyperplane are contractible.** For `0 ≤ c < 1`, the
sublevel `{f ≤ c}` lies in the affine chart where the last homogeneous coordinate is `1`, in which
it is the set `{z | ‖z‖₂² / (1 + ‖z‖₂²) ≤ c}`, star-convex about `0`. -/
theorem contractibleSpace_sublevel_projectiveHyperplaneMomentFunction {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) : ContractibleSpace {x | projectiveHyperplaneMomentFunction N x ≤ c} := by
  set X := {x | projectiveHyperplaneMomentFunction N x ≤ c}
  set Z : Set (Fin N → ℝ) := {z | (∑ j, z j ^ 2) / (1 + ∑ j, z j ^ 2) ≤ c} with hZdef
  have hZ : affineChart (Fin.last N) '' (X ∩ affineOpen (Fin.last N)) = Z := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxX, hxU⟩, rfl⟩
      have hx := (affineChart (K := ℝ) (Fin.last N)).left_inv (by simpa using hxU)
      rw [hZdef, mem_ofPred_eq, ← projectiveHyperplaneMomentFunction_affineChart_symm, hx]
      exact hxX
    · intro hz
      refine ⟨(affineChart (Fin.last N)).symm z, ⟨?_, ?_⟩,
        (affineChart (Fin.last N)).right_inv (by simp)⟩
      · rw [mem_ofPred_eq, projectiveHyperplaneMomentFunction_affineChart_symm]
        exact hz
      · simp
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

/-! ### The relative homology of the top critical band -/

section Homology

variable {A : Type*} [Category A] [HasCoproducts.{0} A] [Abelian A] (R : A) {c : ℝ}

/-- The homeomorphism from `ℝℙᴺ` to its whole sublevel `{f ≤ 1}`. -/
private def homeomorphTopSublevel :
    ℙ ℝ (Fin (N + 1) → ℝ) ≃ₜ {x | projectiveHyperplaneMomentFunction N x ≤ 1} :=
  (Homeomorph.Set.univ _).symm.trans
    (Homeomorph.setCongr (eq_univ_of_forall projectiveHyperplaneMomentFunction_le_one).symm)

/-- **The top critical band in positive degrees.** For `0 ≤ c < 1`, the lower sublevel `{f ≤ c}`
is contractible, so in every positive degree the relative homology of the band
`({f ≤ 1}, {f ≤ c})` is the homology of `ℝℙᴺ`. The isomorphism is the map induced by the
identification `ℝℙᴺ = {f ≤ 1}`, followed by the quotient map to relative homology. -/
def singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIso (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).obj
        (TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) ≅
      (sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).singularHomology R (k + 1) :=
  have : ContractibleSpace (sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).snd :=
    contractibleSpace_sublevel_projectiveHyperplaneMomentFunction hc₀ hc₁
  ((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).mapIso
      (TopCat.isoOfHomeo homeomorphTopSublevel) ≪≫
    @asIso _ _ _ _ _ (TopPair.isIso_singularHomologyπ _ R
      (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R _ _)
      (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R _ _))

/-- **The top critical band in degree zero.** For `0 ≤ c < 1`, the zeroth relative homology of the
band `({f ≤ 1}, {f ≤ c})` vanishes, since `ℝℙᴺ` is path-connected and `{f ≤ c}` contains the
minimum `[e_N]`. -/
theorem isZero_singularHomology_zero_sublevelPair_projectiveHyperplaneMomentFunction
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) :
    IsZero ((sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).singularHomology R 0) :=
  have : PathConnectedSpace (sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).fst :=
    homeomorphTopSublevel.surjective.pathConnectedSpace homeomorphTopSublevel.continuous
  have : ContractibleSpace (sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).snd :=
    contractibleSpace_sublevel_projectiveHyperplaneMomentFunction hc₀ hc₁
  TopPair.isZero_singularHomology_zero _ R

/-- **Integral homology of the top critical band in odd degrees.** For `0 ≤ c < 1` and odd
`k < N`, `Hₖ(ℝℙᴺ, {f ≤ c}; ℤ) ≅ ℤ/2`. -/
def singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) : ∀ {k : ℕ}, Odd k → k < N →
      (((sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).singularHomology
        (ModuleCat.of ℤ ℤ) k : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ZMod 2)
  | 0, hk, _ => (Nat.not_odd_zero hk).elim
  | k + 1, hk, hkN =>
    (singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIso _ hc₀ hc₁
      k).symm.toLinearEquiv ≪≫ₗ
      RealProjectiveSpace.singularHomologyIntLinearEquivProjectivizationOfOdd hk hkN

/-- **Integral homology of the top critical band in even degrees.** For `0 ≤ c < 1` and even
`k > 0`, `Hₖ(ℝℙᴺ, {f ≤ c}; ℤ) = 0`. -/
theorem isZero_singularHomology_int_sublevelPair_projectiveHyperplaneMomentFunction_of_even
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) :
    IsZero ((sublevelPair (projectiveHyperplaneMomentFunction N) hc₁.le).singularHomology
      (ModuleCat.of ℤ ℤ) k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  exact (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := N) ℤ
    (isRegular_iff_ne_zero.2 two_ne_zero).right hk hk0).of_iso
    (singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIso _ hc₀ hc₁ k).symm

/-- **The band crossing the critical circle of `ℝℙ²`.** On `ℝℙ²` the critical hyperplane is the
circle `ℝℙ¹`, and for `0 ≤ c < 1` the band crossing it has `H₁(ℝℙ², {f ≤ c}; ℤ) ≅ ℤ/2`. This is
the zeroth homology of the circle with coefficients twisted by the orientation system of the
Möbius line, the normal bundle of the circle. -/
def singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) :
    ((sublevelPair (projectiveHyperplaneMomentFunction 2) hc₁.le).singularHomology
      (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ZMod 2 :=
  singularHomologySublevelPairProjectiveHyperplaneMomentFunctionIntLinearEquivOfOdd hc₀ hc₁
    odd_one one_lt_two

/-- **The band crossing the critical circle of `ℝℙ²` does not have untwisted homology.** The group
`H₁(ℝℙ², {f ≤ c}; ℤ) ≅ ℤ/2` of the band crossing the critical circle is not isomorphic to `ℤ`, the
zeroth homology of the circle with constant integer coefficients. -/
theorem not_nonempty_linearEquiv_int_projectiveHyperplaneMomentFunction_two
    (hc₀ : 0 ≤ c) (hc₁ : c < 1) :
    ¬ Nonempty (((sublevelPair (projectiveHyperplaneMomentFunction 2) hc₁.le).singularHomology
      (ModuleCat.of ℤ ℤ) 1 : ModuleCat.{0} ℤ) ≃ₗ[ℤ] ℤ) := by
  rintro ⟨e⟩
  have : Finite ℤ :=
    .of_equiv _ ((singularHomologyOneSublevelPairProjectiveHyperplaneMomentFunctionTwoLinearEquiv
      hc₀ hc₁).symm.trans e).toEquiv
  exact not_finite ℤ

end Homology

end TauCeti
