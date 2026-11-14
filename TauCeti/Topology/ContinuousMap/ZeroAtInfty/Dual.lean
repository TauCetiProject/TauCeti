/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The continuous dual of `C₀(ι, E)` on a discrete index

On a discrete index type `ι`, over real or complex scalars, the pairing `∑' i, a i * f i`
identifies absolutely summable families `a ∈ ℓ¹` with continuous linear functionals on
`C₀(ι, 𝕜)`, isometrically. More generally, for a normed space `E`, the pairing `∑' i, φ i (f i)`
identifies `ℓ¹(ι, E*)` isometrically with the continuous dual of `C₀(ι, E)`. In both cases the
inverse records the action of a functional on coordinate vectors. The index type is arbitrary,
including empty and uncountable types; no enumeration is chosen, and for `ι = ℕ` the scalar case
is the classical identification `c₀* = ℓ¹`.

The forward maps restrict Mathlib's pairing `lp.dualPairing` between `ℓ¹` and `ℓ∞` along the
isometric inclusion `ZeroAtInftyContinuousMap.toLpInfty` of `C₀(ι, E)` into `ℓ∞(ι, E)`, which is
defined for an arbitrary topological space `α` and normed group `E`. The scalar pairing is
bilinear, including over complex scalars: the coefficients of a functional are its values on
coordinate vectors, without conjugation.

## Main declarations

* `ZeroAtInftyContinuousMap.toLpInfty`: the inclusion of `C₀(α, E)` into `ℓ∞`, as a linear
  isometry.
* `ZeroAtInftyContinuousMap.hasSum_apply_single_one_mul` and
  `ZeroAtInftyContinuousMap.hasSum_comp_singleCLM`: every continuous linear functional on
  `C₀(ι, 𝕜)` (and every continuous linear map out of `C₀(ι, E)`) is given by its coordinate
  series.
* `ZeroAtInftyContinuousMap.sum_norm_apply_single_le_of_forall_norm_le_one`,
  `ZeroAtInftyContinuousMap.sum_norm_apply_single_one_le`, and
  `ZeroAtInftyContinuousMap.sum_norm_comp_singleCLM_le`: the coordinate values or coordinate
  functionals have finite partial sums of norms bounded by the norm of the functional.
* `ZeroAtInftyContinuousMap.dualEquiv`: the isometric equivalence `ℓ¹ ≃ₗᵢ C₀(ι, 𝕜)*`.
* `ZeroAtInftyContinuousMap.strongDualEquiv`: the isometric equivalence
  `ℓ¹(ι, E*) ≃ₗᵢ C₀(ι, E)*`.
* `ZeroAtInftyContinuousMap.norm_eq_tsum_norm_apply_single_one` and
  `ZeroAtInftyContinuousMap.norm_eq_tsum_norm_comp_singleCLM`: the norm of a functional is the
  sum of the norms of its coordinates.
* `ZeroAtInftyContinuousMap.exists_forall_re_apply_eq_of_bddAbove`: a real functional on
  `C₀(ι, ℝ)`, read along a bounded family of points of a Banach space, is the real part of
  evaluation at a single point.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Chapter 4.
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

section SeminormedCommRing

variable [SeminormedCommRing 𝕜] [DecidableEq ι]

/-- Every continuous linear functional on `C₀(ι, 𝕜)` is given by its coordinate series. -/
theorem hasSum_apply_single_one_mul (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) (f : C₀(ι, 𝕜)) :
    HasSum (fun i ↦ Λ (single i 1) * f i) (Λ f) := by
  simpa [mul_comm] using (hasSum_smul_single_one f).mapL Λ

end SeminormedCommRing

section Semiring

variable {E M : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid M] [TopologicalSpace M] [Module 𝕜 M] [DecidableEq ι]

/-- Every continuous linear map out of `C₀(ι, E)` is given by the series of its coordinate maps
`Λ ∘ singleCLM 𝕜 i`. -/
theorem hasSum_comp_singleCLM (Λ : C₀(ι, E) →L[𝕜] M) (f : C₀(ι, E)) :
    HasSum (fun i ↦ Λ.comp (singleCLM 𝕜 i) (f i)) (Λ f) := by
  simpa using (hasSum_single f).mapL Λ

end Semiring

section RCLike

variable [RCLike 𝕜]

section Coordinates

variable [DecidableEq ι]

/-- Along any family of vectors in the closed unit ball of `E`, the values of a functional on
`C₀(ι, E)` at the corresponding coordinate vectors have finite partial sums of norms bounded by
`‖Λ‖`. -/
theorem sum_norm_apply_single_le_of_forall_norm_le_one {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (Λ : StrongDual 𝕜 C₀(ι, E)) {v : ι → E} (hv : ∀ i, ‖v i‖ ≤ 1)
    (s : Finset ι) :
    ∑ i ∈ s, ‖Λ (single i (v i))‖ ≤ ‖Λ‖ := by
  -- Rotate each `v i` by the conjugate phase of `Λ (single i (v i))` to align the terms in `ℝ≥0`.
  set u : ι → 𝕜 := fun i ↦ conj (Λ (single i (v i))) / (‖Λ (single i (v i))‖ : 𝕜)
  have hu (i : ι) : ‖u i • v i‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (by simpa [u] using div_self_le_one ‖Λ (single i (v i))‖)).trans (hv i)
  have hΛu (i : ι) : Λ (single i (u i • v i)) = ‖Λ (single i (v i))‖ := by
    rw [single_smul, map_smul, smul_eq_mul, div_mul_eq_mul_div, RCLike.conj_mul]
    rcases eq_or_ne (‖Λ (single i (v i))‖ : 𝕜) 0 with h | h
    · simp [h]
    · field_simp
  set g : C₀(ι, E) := ∑ i ∈ s, single i (u i • v i)
  have hg : ‖g‖ ≤ 1 := (norm_le zero_le_one).2 fun j ↦ by
    by_cases hj : j ∈ s <;> simp [g, hj, hu]
  have hΛg : Λ g = ((∑ i ∈ s, ‖Λ (single i (v i))‖ : ℝ) : 𝕜) := by
    simp [g, map_sum, hΛu]
  calc ∑ i ∈ s, ‖Λ (single i (v i))‖ = ‖Λ g‖ := by
        rw [hΛg, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    _ ≤ ‖Λ‖ * ‖g‖ := Λ.le_opNorm g
    _ ≤ ‖Λ‖ := mul_le_of_le_one_right (norm_nonneg Λ) hg

/-- The finite partial sums of the norms of the coordinate values of a functional on `C₀(ι, 𝕜)`
are bounded by its norm. -/
theorem sum_norm_apply_single_one_le (Λ : StrongDual 𝕜 C₀(ι, 𝕜)) (s : Finset ι) :
    ∑ i ∈ s, ‖Λ (single i 1)‖ ≤ ‖Λ‖ :=
  sum_norm_apply_single_le_of_forall_norm_le_one Λ (fun _ ↦ norm_one.le) s

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

section VectorValued

variable [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [DecidableEq ι]

/-- The finite partial sums of the norms of the coordinate functionals of a functional on
`C₀(ι, E)` are bounded by its norm. -/
theorem sum_norm_comp_singleCLM_le (Λ : StrongDual 𝕜 C₀(ι, E)) (s : Finset ι) :
    ∑ i ∈ s, ‖Λ.comp (singleCLM 𝕜 i)‖ ≤ ‖Λ‖ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ := ε / (s.card + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  -- Choose unit-ball vectors `v i` witnessing `‖Λ ∘ singleCLM 𝕜 i‖` within `δ`.
  have hex (i : ι) : ∃ v : E, ‖v‖ ≤ 1 ∧ ‖Λ.comp (singleCLM 𝕜 i)‖ - δ ≤ ‖Λ (single i v)‖ := by
    by_cases hpos : 0 ≤ ‖Λ.comp (singleCLM 𝕜 i)‖ - δ
    · by_contra! hle
      have hnorm : ‖Λ.comp (singleCLM 𝕜 i)‖ ≤ ‖Λ.comp (singleCLM 𝕜 i)‖ - δ :=
        (Λ.comp (singleCLM 𝕜 i)).opNorm_le_of_unit_norm hpos fun v hv ↦ by
          simpa using (hle v hv.le).le
      linarith
    · exact ⟨0, by simp, by simp [le_of_lt (not_le.1 hpos)]⟩
  choose v hv1 hΛv using hex
  have hcard : (s.card : ℝ) * δ ≤ ε := by
    have hdiv : (s.card : ℝ) / (s.card + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < s.card + 1)).2 (by linarith)
    calc (s.card : ℝ) * δ = (s.card / (s.card + 1)) * ε := by rw [hδ_def]; ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hdiv hε.le
      _ = ε := one_mul ε
  calc ∑ i ∈ s, ‖Λ.comp (singleCLM 𝕜 i)‖
      ≤ ∑ i ∈ s, (‖Λ (single i (v i))‖ + δ) :=
        Finset.sum_le_sum fun i _ ↦ by linarith [hΛv i]
    _ = (∑ i ∈ s, ‖Λ (single i (v i))‖) + s.card * δ := by
        simp [Finset.sum_add_distrib]
    _ ≤ ‖Λ‖ + ε := add_le_add (sum_norm_apply_single_le_of_forall_norm_le_one Λ hv1 s) hcard

/-- The coordinate functionals of a functional on `C₀(ι, E)` have summable norms. -/
theorem summable_norm_comp_singleCLM (Λ : StrongDual 𝕜 C₀(ι, E)) :
    Summable fun i ↦ ‖Λ.comp (singleCLM 𝕜 i)‖ :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_comp_singleCLM_le Λ)

/-- The norm of a functional on `C₀(ι, E)` is the sum of the norms of its coordinate
functionals. -/
theorem norm_eq_tsum_norm_comp_singleCLM (Λ : StrongDual 𝕜 C₀(ι, E)) :
    ‖Λ‖ = ∑' i, ‖Λ.comp (singleCLM 𝕜 i)‖ := by
  refine le_antisymm ?_
    ((summable_norm_comp_singleCLM Λ).tsum_le_of_sum_le (sum_norm_comp_singleCLM_le Λ))
  refine Λ.opNorm_le_bound (tsum_nonneg fun _ ↦ norm_nonneg _) fun f ↦ ?_
  calc ‖Λ f‖ ≤ ∑' i, ‖Λ.comp (singleCLM 𝕜 i)‖ * ‖f‖ :=
        (hasSum_comp_singleCLM Λ f).norm_le_of_bounded
          ((summable_norm_comp_singleCLM Λ).mul_right ‖f‖).hasSum fun i ↦
            (Λ.comp (singleCLM 𝕜 i)).le_opNorm_of_le (norm_coe_le_norm f i)
    _ = (∑' i, ‖Λ.comp (singleCLM 𝕜 i)‖) * ‖f‖ := tsum_mul_right

end VectorValued

section Representation

variable [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A continuous linear functional `Λ` on `C₀(ι, ℝ)`, read along a bounded family `v` of points of
a Banach space `E`, is the real part of evaluation at a single point `x` of `E`: for every
`f : StrongDual 𝕜 E`, `re (f x) = Λ g` whenever `g` is the family of the real parts of `f` along
`v`. The point is `∑' i, Λ (single i 1) • v i`. -/
theorem exists_forall_re_apply_eq_of_bddAbove {v : ι → E}
    (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) (Λ : StrongDual ℝ C₀(ι, ℝ)) :
    ∃ x : E, ∀ (f : StrongDual 𝕜 E) (g : C₀(ι, ℝ)), (∀ i, g i = RCLike.re (f (v i))) →
      RCLike.re (f x) = Λ g := by
  classical
  -- The coefficients of `Λ` are absolutely summable and `v` is bounded, so they define a point
  -- `∑' i, a i • v i` of `E`.
  set a := fun i ↦ Λ (single i 1)
  obtain ⟨M, hM⟩ := hv
  have hsum : Summable fun i ↦ (a i : 𝕜) • v i :=
    .of_norm_bounded ((summable_norm_apply_single_one Λ).mul_right M) fun i ↦ by
      rw [norm_smul, RCLike.norm_ofReal, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM ⟨i, rfl⟩) (norm_nonneg _)
  refine ⟨∑' i, (a i : 𝕜) • v i, fun f g hg ↦ ?_⟩
  have h₁ := (hsum.hasSum.mapL f).mapL RCLike.reCLM
  have h₂ := hasSum_apply_single_one_mul Λ g
  simp only [hg, RCLike.reCLM_apply, map_smul, smul_eq_mul, RCLike.re_ofReal_mul] at h₁ h₂
  exact h₁.unique h₂

end Representation

end ZeroAtInftyContinuousMap

namespace ZeroAtInftyContinuousMap

variable {𝕜 ι E : Type*} [TopologicalSpace ι] [DiscreteTopology ι] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 ι E) in
/-- The isometric duality between absolutely summable families of continuous linear functionals on
`E` and the continuous dual of `C₀(ι, E)`. It sends `φ` to the functional `f ↦ ∑' i, φ i (f i)`. -/
def strongDualEquiv : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1 ≃ₗᵢ[𝕜] StrongDual 𝕜 C₀(ι, E) := by
  classical
  have hid : ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.norm_id_le
  let J : C₀(ι, E) →L[𝕜] lp (fun _ : ι ↦ E) ∞ := (toLpInfty 𝕜).toContinuousLinearMap
  have hJ : ‖J‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  let D := lp.dualPairing (𝕜 := 𝕜) 1 ∞
    (fun _ : ι ↦ ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)) (fun _ ↦ hid)
  let P : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1 →L[𝕜] StrongDual 𝕜 C₀(ι, E) :=
    ContinuousLinearMap.precomp 𝕜 J ∘L D
  have hP (φ : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1) (i : ι) :
      (P φ).comp (singleCLM 𝕜 i) = φ i := by
    ext x
    simp only [P, D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      lp.dualPairing_apply, ContinuousLinearMap.id_apply, J,
      LinearIsometry.coe_toContinuousLinearMap, toLpInfty_apply, singleCLM_apply, coe_single,
      Pi.single_apply, apply_ite (φ _), map_zero, tsum_ite_eq]
  have hnorm (φ : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1) : ‖P φ‖ = ‖φ‖ := by
    apply le_antisymm
    · calc ‖P φ‖ ≤ ‖D φ‖ * ‖J‖ := (D φ).opNorm_comp_le J
        _ ≤ ‖D φ‖ := mul_le_of_le_one_right (norm_nonneg _) hJ
        _ ≤ ‖D‖ * ‖φ‖ := D.le_opNorm φ
        _ ≤ ‖φ‖ := mul_le_of_le_one_left (norm_nonneg φ) (by
          exact_mod_cast lp.norm_dualPairing (p := 1) (q := ∞)
            (fun _ : ι ↦ ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)) (fun _ ↦ hid))
    · refine lp.norm_le_of_forall_sum_le (by simp) (norm_nonneg (P φ)) fun s ↦ ?_
      simpa [hP φ] using sum_norm_comp_singleCLM_le (P φ) s
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm } fun Λ ↦ ?_
  let φ : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1 :=
    ⟨fun i ↦ Λ.comp (singleCLM 𝕜 i), memℓp_gen (by simpa using summable_norm_comp_singleCLM Λ)⟩
  exact ⟨φ, continuousLinearMap_ext fun i x ↦ by
    simpa [φ] using congr($(hP φ i) x)⟩

/-- The forward vector-valued duality map is the coordinatewise functional series pairing. -/
theorem strongDualEquiv_apply (φ : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1) (f : C₀(ι, E)) :
    strongDualEquiv 𝕜 ι E φ f = ∑' i, φ i (f i) := by
  simp [strongDualEquiv, LinearIsometryEquiv.coe_ofSurjective, lp.dualPairing_apply]

variable [DecidableEq ι]

/-- On a coordinate vector, the functional associated with a summable family `φ` applies `φ i`. -/
@[simp]
theorem strongDualEquiv_apply_single (φ : lp (fun _ : ι ↦ StrongDual 𝕜 E) 1) (i : ι) (x : E) :
    strongDualEquiv 𝕜 ι E φ (single i x) = φ i x := by
  simp [strongDualEquiv_apply, Pi.single_apply, apply_ite (φ _)]

/-- The inverse vector-valued duality map records a functional's coordinate functionals. -/
@[simp]
theorem strongDualEquiv_symm_apply (Λ : StrongDual 𝕜 C₀(ι, E)) (i : ι) :
    (strongDualEquiv 𝕜 ι E).symm Λ i = Λ.comp (singleCLM 𝕜 i) := by
  ext x
  have h := congrArg (fun g : StrongDual 𝕜 C₀(ι, E) ↦ g (single i x))
    ((strongDualEquiv 𝕜 ι E).apply_symm_apply Λ)
  simpa only [ContinuousLinearMap.comp_apply, singleCLM_apply, strongDualEquiv_apply_single] using h

/-- Composing a functional `g : StrongDual 𝕜 E` with evaluation at `i` corresponds to the single
entry `lp.single 1 i g` in `ℓ¹(ι, E*)`. -/
@[simp]
theorem strongDualEquiv_symm_comp_evalCLM (g : StrongDual 𝕜 E) (i : ι) :
    (strongDualEquiv 𝕜 ι E).symm (g.comp (evalCLM 𝕜 i)) =
      lp.single (E := fun _ : ι ↦ StrongDual 𝕜 E) 1 i g := by
  ext j x
  by_cases hij : i = j <;> simp [lp.single_apply, single_apply, hij]

end ZeroAtInftyContinuousMap
