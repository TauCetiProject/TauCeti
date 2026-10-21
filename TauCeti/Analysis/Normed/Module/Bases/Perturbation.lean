/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Map
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Small perturbations of Schauder bases

If `b` is a generalized Schauder basis of a Banach space and
`δ = ∑' i, ‖b.coord i‖ * ‖b i - c i‖ < 1`, with the series summable, then a bounded
linear equivalence sends `b i` to `c i`. Its norm is at most `1 + δ`, and its inverse
has norm at most `(1 - δ)⁻¹`. Transporting `b` gives a basis with vectors `c`, retaining
the original summation filter; no unconditional convergence of the basis expansion is assumed.

The error operator is the norm-convergent sum of the rank-one operators
`x ↦ b.coord i x • (b i - c i)`. Mathlib's `Units.oneSub` makes `1 - error`
invertible by the Neumann series.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1,
  the principle of small perturbations.
-/

public section

noncomputable section

namespace GeneralSchauderBasis

variable {β 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 E L) (c : β → E)

private def perturbationError : E →L[𝕜] E :=
  ∑' i, (b.coord i).smulRight (b i - c i)

private theorem norm_perturbationError_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖)) :
    ‖b.perturbationError c‖ ≤ ∑' i, ‖b.coord i‖ * ‖b i - c i‖ :=
  tsum_of_norm_bounded hs.hasSum fun i ↦
    (ContinuousLinearMap.norm_smulRight_apply (b.coord i) (b i - c i)).le

variable [CompleteSpace E]

private theorem summable_perturbationError
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖)) :
    Summable (fun i ↦ (b.coord i).smulRight (b i - c i)) :=
  hs.of_norm_bounded fun i ↦
    (ContinuousLinearMap.norm_smulRight_apply (b.coord i) (b i - c i)).le

/-- The bounded equivalence sending a basis to a small perturbation of its vectors.
The weighted error series must be summable and have sum strictly less than one. -/
def smallPerturbationEquiv
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofUnit
    (Units.oneSub (b.perturbationError c) ((b.norm_perturbationError_le c hs).trans_lt hδ))

/-- As a bounded operator, the perturbing equivalence is the identity minus the
norm-convergent series of rank-one errors. -/
theorem smallPerturbationEquiv_toContinuousLinearMap
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) :
    (b.smallPerturbationEquiv c hs hδ : E →L[𝕜] E) =
      1 - ∑' i, (b.coord i).smulRight (b i - c i) := (rfl)

/-- The perturbing equivalence is the identity minus the sum of the rank-one errors. -/
theorem smallPerturbationEquiv_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) (x : E) :
    b.smallPerturbationEquiv c hs hδ x =
      x - ∑' i, b.coord i x • (b i - c i) := by
  rw [← ContinuousLinearEquiv.coe_coe, smallPerturbationEquiv_toContinuousLinearMap]
  simp only [sub_apply, one_apply_eq_self,
    tsum_apply (b.summable_perturbationError c hs),
    ContinuousLinearMap.smulRight_apply]

@[simp]
theorem smallPerturbationEquiv_apply_basis
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) (i : β) :
    b.smallPerturbationEquiv c hs hδ (b i) = c i := by
  classical
  rw [smallPerturbationEquiv_apply, tsum_eq_single i]
  · simp [b.ortho]
  · intro j hji
    simp [b.ortho, hji.symm]

/-- The norm of the perturbing equivalence is at most one plus the weighted error. -/
theorem norm_smallPerturbationEquiv_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) :
    ‖(b.smallPerturbationEquiv c hs hδ : E →L[𝕜] E)‖ ≤
      1 + ∑' i, ‖b.coord i‖ * ‖b i - c i‖ := by
  rw [smallPerturbationEquiv_toContinuousLinearMap]
  exact (norm_sub_le _ _).trans
    (add_le_add (ContinuousLinearMap.norm_id_le) (b.norm_perturbationError_le c hs))

/-- The inverse equivalence has the geometric-series bound. -/
theorem norm_smallPerturbationEquiv_symm_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) :
    ‖((b.smallPerturbationEquiv c hs hδ).symm : E →L[𝕜] E)‖ ≤
      (1 - ∑' i, ‖b.coord i‖ * ‖b i - c i‖)⁻¹ := by
  let δ := ∑' i, ‖b.coord i‖ * ‖b i - c i‖
  let e := b.smallPerturbationEquiv c hs hδ
  have herr (x : E) : ‖x - e x‖ ≤ δ * ‖x‖ := by
    have hx : x - e x = b.perturbationError c x := by
      simp [e, smallPerturbationEquiv_apply, perturbationError,
        tsum_apply (b.summable_perturbationError c hs)]
    rw [hx]
    exact (b.perturbationError c).le_of_opNorm_le (b.norm_perturbationError_le c hs) x
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have h := herr (e.symm y)
  have htri := norm_le_norm_sub_add (e.symm y) y
  simp only [e.apply_symm_apply] at h
  have hlower : (1 - δ) * ‖e.symm y‖ ≤ ‖y‖ := by linarith
  calc
    ‖e.symm y‖ ≤ ‖y‖ / (1 - δ) :=
      (le_div_iff₀ (sub_pos.mpr hδ)).mpr ((mul_comm _ _).trans_le hlower)
    _ = (1 - δ)⁻¹ * ‖y‖ := by rw [div_eq_mul_inv, mul_comm]

/-- A small perturbation of a generalized Schauder basis is a basis with the same summation
filter. This includes both classical and unconditional Schauder bases. -/
def perturb
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) :
    GeneralSchauderBasis β 𝕜 E L :=
  b.map (b.smallPerturbationEquiv c hs hδ)

@[simp]
theorem perturb_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) (i : β) :
    b.perturb c hs hδ i = c i := by
  simp [perturb]

@[simp]
theorem perturb_coord_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖b i - c i‖))
    (hδ : (∑' i, ‖b.coord i‖ * ‖b i - c i‖) < 1) (i : β) (x : E) :
    (b.perturb c hs hδ).coord i x =
      b.coord i ((b.smallPerturbationEquiv c hs hδ).symm x) := by
  simp only [perturb, map_coord_apply]

end GeneralSchauderBasis
