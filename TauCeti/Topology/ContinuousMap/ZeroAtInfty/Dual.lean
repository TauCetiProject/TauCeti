/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The continuous dual of `c₀`

On a discrete index type `ι`, over real or complex scalars, the pairing `∑' i, a i * f i`
identifies absolutely summable families `a ∈ ℓ¹` with continuous linear functionals on
`C₀(ι, 𝕜)`, isometrically. The inverse records the values of a functional on the unit coordinate
vectors. The index type is arbitrary, including empty and uncountable types; no enumeration is
chosen, and for `ι = ℕ` this is the classical identification `c₀* = ℓ¹`.

The forward map restricts Mathlib's pairing `lp.dualPairing` between `ℓ¹` and `ℓ∞` along the
isometric inclusion `ZeroAtInftyContinuousMap.toLpInfty` of `C₀(ι, 𝕜)` into `ℓ∞`, which is
defined for an arbitrary topological space `α` and normed group `E`. The pairing is bilinear,
including over complex scalars: the coefficients of a functional are its values on coordinate
vectors, without conjugation.

## Main declarations

* `ZeroAtInftyContinuousMap.toLpInfty`: the inclusion of `C₀(α, E)` into `ℓ∞`, as a linear
  isometry.
* `ZeroAtInftyContinuousMap.hasSum_apply_single_one_mul`: every continuous linear functional on
  `C₀(ι, 𝕜)` is given by its coordinate series.
* `ZeroAtInftyContinuousMap.sum_norm_apply_single_one_le`: the coordinate values of a functional
  have finite partial sums of norms bounded by its norm.
* `ZeroAtInftyContinuousMap.dualEquiv`: the isometric equivalence `ℓ¹ ≃ₗᵢ C₀(ι, 𝕜)*`.
* `ZeroAtInftyContinuousMap.norm_eq_tsum_norm_apply_single_one`: the norm of a functional on
  `C₀(ι, 𝕜)` is the sum of the norms of its coordinate values.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open scoped ENNReal ZeroAtInfty ComplexConjugate

namespace ZeroAtInftyContinuousMap

section LpInfty

variable (𝕜 : Type*) {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedRing 𝕜]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The inclusion of `C₀(α, E)` into the bounded families `ℓ∞(α, E)`, as a linear isometry. -/
def toLpInfty : C₀(α, E) →ₗᵢ[𝕜] lp (fun _ : α ↦ E) ∞ where
  toFun f := ⟨⇑f, memℓp_infty ⟨‖f‖, Set.forall_mem_range.2 (norm_coe_le_norm f)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    rw [lp.norm_eq_ciSup, norm_eq_iSup_norm]
    rfl

variable {𝕜}

/-- The inclusion of `C₀(α, E)` into `ℓ∞` does not change values. -/
@[simp]
theorem toLpInfty_apply (f : C₀(α, E)) (x : α) : toLpInfty 𝕜 f x = f x :=
  (rfl)

end LpInfty

variable {𝕜 ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

section NormedField

variable [NormedField 𝕜] [DecidableEq ι]

/-- Every continuous linear functional on `C₀(ι, 𝕜)` is given by its coordinate series. -/
theorem hasSum_apply_single_one_mul (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) (f : C₀(ι, 𝕜)) :
    HasSum (fun i ↦ Λ (single i 1) * f i) (Λ f) := by
  simpa [mul_comm] using (hasSum_smul_single_one f).mapL Λ

end NormedField

section RCLike

variable [RCLike 𝕜]

section Coordinates

variable [DecidableEq ι]

/-- The finite partial sums of the norms of the coordinate values of a functional on `C₀(ι, 𝕜)`
are bounded by its norm. -/
theorem sum_norm_apply_single_one_le (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) (s : Finset ι) :
    ∑ i ∈ s, ‖Λ (single i 1)‖ ≤ ‖Λ‖ := by
  -- Test `Λ` against the finitely supported family of the conjugate phases of its coordinates.
  set u : ι → 𝕜 := fun i ↦ conj (Λ (single i 1)) / (‖Λ (single i 1)‖ : 𝕜)
  have hu (i : ι) : ‖u i‖ ≤ 1 := by
    simpa [u] using div_self_le_one ‖Λ (single i 1)‖
  have hΛu (i : ι) : Λ (single i (u i)) = ‖Λ (single i 1)‖ := by
    rw [← smul_single_one, map_smul, smul_eq_mul, div_mul_eq_mul_div, RCLike.conj_mul]
    rcases eq_or_ne (‖Λ (single i 1)‖ : 𝕜) 0 with h | h
    · simp [h]
    · field_simp
  set g : C₀(ι, 𝕜) := ∑ i ∈ s, single i (u i)
  have hg : ‖g‖ ≤ 1 := (norm_le zero_le_one).2 fun j ↦ by
    by_cases hj : j ∈ s <;> simp [g, Pi.single_apply, hj, hu]
  have hΛg : Λ g = ((∑ i ∈ s, ‖Λ (single i 1)‖ : ℝ) : 𝕜) := by
    simp [g, map_sum, hΛu]
  calc ∑ i ∈ s, ‖Λ (single i 1)‖ = ‖Λ g‖ := by
        rw [hΛg, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    _ ≤ ‖Λ‖ * ‖g‖ := Λ.le_opNorm g
    _ ≤ ‖Λ‖ := mul_le_of_le_one_right (norm_nonneg Λ) hg

/-- The coordinate values of a functional on `C₀(ι, 𝕜)` are absolutely summable. -/
theorem summable_norm_apply_single_one (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) :
    Summable fun i ↦ ‖Λ (single i 1)‖ :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_apply_single_one_le Λ)

end Coordinates

variable (𝕜 ι) in
/-- The isometric duality between absolutely summable scalar families and the continuous dual of
`C₀(ι, 𝕜)`. It sends `a` to the functional `f ↦ ∑' i, a i * f i`. -/
def dualEquiv : lp (fun _ : ι ↦ 𝕜) 1 ≃ₗᵢ[𝕜] StrongDual 𝕜 C₀(ι, 𝕜) := by
  classical
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let J : C₀(ι, 𝕜) →L[𝕜] lp (fun _ : ι ↦ 𝕜) ∞ := (toLpInfty 𝕜).toContinuousLinearMap
  have hJ : ‖J‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  let D := lp.dualPairing (𝕜 := 𝕜) 1 ∞ (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)
  let P : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] StrongDual 𝕜 C₀(ι, 𝕜) :=
    ContinuousLinearMap.precomp 𝕜 J ∘L D
  have hP (a : lp (fun _ : ι ↦ 𝕜) 1) (i : ι) (z : 𝕜) : P a (single i z) = a i * z := by
    simp only [P, D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      lp.dualPairing_apply, ContinuousLinearMap.mul_apply', J,
      LinearIsometry.coe_toContinuousLinearMap, toLpInfty_apply, coe_single, Pi.single_apply,
      mul_ite, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) 1) : ‖P a‖ = ‖a‖ := by
    apply le_antisymm
    · calc ‖P a‖ ≤ ‖D a‖ * ‖J‖ := (D a).opNorm_comp_le J
        _ ≤ ‖D a‖ := mul_le_of_le_one_right (norm_nonneg _) hJ
        _ ≤ ‖D‖ * ‖a‖ := D.le_opNorm a
        _ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg a) (by
          exact_mod_cast lp.norm_dualPairing (p := 1) (q := ∞)
            (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul))
    · refine lp.norm_le_of_forall_sum_le (by simp) (norm_nonneg (P a)) fun s ↦ ?_
      simpa [hP] using sum_norm_apply_single_one_le (P a) s
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm } fun Λ ↦ ?_
  let a : lp (fun _ : ι ↦ 𝕜) 1 :=
    ⟨fun i ↦ Λ (single i 1), memℓp_gen (by simpa using summable_norm_apply_single_one Λ)⟩
  refine ⟨a, continuousLinearMap_ext fun i z ↦ ?_⟩
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, hP]
  rw [← smul_single_one i z, map_smul, smul_eq_mul, mul_comm]

/-- The forward duality map is the scalar series pairing. -/
theorem dualEquiv_apply (a : lp (fun _ : ι ↦ 𝕜) 1) (f : C₀(ι, 𝕜)) :
    dualEquiv 𝕜 ι a f = ∑' i, a i * f i := by
  simp [dualEquiv, LinearIsometryEquiv.coe_ofSurjective, lp.dualPairing_apply]

variable [DecidableEq ι]

/-- On a coordinate vector, the functional of a summable family is multiplication by that
coordinate. -/
@[simp]
theorem dualEquiv_apply_single (a : lp (fun _ : ι ↦ 𝕜) 1) (i : ι) (z : 𝕜) :
    dualEquiv 𝕜 ι a (single i z) = a i * z := by
  simp [dualEquiv_apply, Pi.single_apply]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem dualEquiv_symm_apply (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) (i : ι) :
    (dualEquiv 𝕜 ι).symm Λ i = Λ (single i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 C₀(ι, 𝕜) ↦ g (single i 1))
    ((dualEquiv 𝕜 ι).apply_symm_apply Λ)
  rwa [dualEquiv_apply_single, mul_one] at h

/-- The coordinate evaluations of `C₀(ι, 𝕜)` correspond to the unit vectors of `ℓ¹`. -/
@[simp]
theorem dualEquiv_symm_evalCLM (i : ι) :
    (dualEquiv 𝕜 ι).symm (evalCLM 𝕜 i) = lp.single 1 i 1 := by
  ext j
  simp [lp.single_apply, single_apply, Pi.single_apply, eq_comm]

/-- The norm of a functional on `C₀(ι, 𝕜)` is the sum of the norms of its coordinate values. -/
theorem norm_eq_tsum_norm_apply_single_one (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) :
    ‖Λ‖ = ∑' i, ‖Λ (single i 1)‖ := by
  rw [← (dualEquiv 𝕜 ι).symm.norm_map Λ, lp.norm_eq_tsum_rpow (by simp)]
  simp

end RCLike

end ZeroAtInftyContinuousMap
