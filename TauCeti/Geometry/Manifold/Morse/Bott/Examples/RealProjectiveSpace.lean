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

For `N ≥ 2` its weights are not distinct, so it is not a Morse function. Its critical set is the
point `[e_N]`, where `f` takes its minimum `0`, together with the hyperplane `{v_N = 0}`
(`TauCeti.criticalPoints_projectiveHyperplaneMomentFunction`). For `N ≥ 1` this hyperplane is a
copy of `ℝℙᴺ⁻¹`, on which `f` attains its maximum `1`
(`TauCeti.projectiveHyperplaneMomentFunction_eq_one_iff`). At the coordinate points of the
hyperplane the Morse index is `1`
(`TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_mk_single_castSucc`): the Hessian
is negative only in the direction normal to the hyperplane. The hyperplane is the critical
component of a Morse–Bott function of index `1`, whose negative normal bundle is the normal line
bundle of `ℝℙᴺ⁻¹` in `ℝℙᴺ`, the tautological line bundle; for `N = 2` it is the Möbius line over
the circle `ℝℙ¹`. These two facts are background here and are not formalized in this file.

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
* `TauCeti.manifoldMorseIndex_projectiveHyperplaneMomentFunction_mk_single_castSucc`: the Morse
  index at the coordinate points `[eₖ]`, `k < N`, of the hyperplane is `1`.
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

/-- **The Morse index at the coordinate points of the critical hyperplane.** At each coordinate
point `[eₖ]`, `k < N`, of the critical hyperplane `{v_N = 0}`, the Morse index is `1`: the only
weight below the weight `1` of `eₖ` is the weight `0` of the normal coordinate `v_N`. -/
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
