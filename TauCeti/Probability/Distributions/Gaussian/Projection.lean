/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Gaussian
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Orthogonal projections of standard Gaussian vectors

The projection of a standard Gaussian onto a subspace is standard Gaussian on that subspace.
Its squared norm therefore has chi-squared law with degrees of freedom equal to the dimension
of the subspace. Projections onto any family of mutually orthogonal subspaces are jointly
independent, as are their squared norms. The product-measure identities describe their joint
laws, and the `HasLaw` results transfer them to random vectors on any probability space.

Zero subspaces, zero-dimensional ambient spaces, and empty projection families are included.
No assumption that the subspaces span the ambient space is needed.

The proofs use Mathlib's standard Gaussian covariance and joint Gaussian independence criterion,
and the Gaussian radius identity `TauCeti.Probability.stdGaussian_map_norm`.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Submodule

/-- Orthogonal projection of a standard Gaussian is standard Gaussian on the target subspace. -/
@[simp]
theorem map_orthogonalProjectionOnto_stdGaussian (K : Submodule ℝ E) :
    (stdGaussian E).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun ((stdGaussian E).map K.orthogonalProjectionOnto) t =
        charFun (stdGaussian E) (t : E) := by
      rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
      simp
    _ = charFun (stdGaussian K) t := by
      rw [charFun_stdGaussian, charFun_stdGaussian]
      simp only [Submodule.norm_coe]

/-- The squared length of a standard Gaussian projected onto a subspace has chi-squared law
with degree equal to the rank of the projection. A zero subspace gives the point mass at zero. -/
@[simp]
theorem map_norm_sq_starProjection_stdGaussian (K : Submodule ℝ E) :
    (stdGaussian E).map (fun x ↦ ‖K.starProjection x‖ ^ 2) =
      TauCeti.Probability.chiSquaredMeasure (Module.finrank ℝ K) := by
  rw [← TauCeti.Probability.stdGaussian_map_norm_sq K,
    ← K.map_orthogonalProjectionOnto_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Submodule.starProjection_apply, Submodule.norm_coe]

end Submodule

namespace TauCeti.Probability

variable {ι : Type*}

/-- A standard Gaussian's projections onto mutually orthogonal subspaces are jointly
independent, without requiring these subspaces to span the ambient space. -/
theorem iIndepFun_orthogonalProjectionOnto_stdGaussian (K : ι → Submodule ℝ E)
    (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    iIndepFun (fun i x ↦ (K i).orthogonalProjectionOnto x) (stdGaussian E) := by
  refine iIndepFun_iff_finset.2 fun s ↦ ?_
  let L := ContinuousLinearMap.pi fun i : s ↦ (K i).orthogonalProjectionOnto
  have hG := IsGaussian.hasGaussianLaw_id (μ := stdGaussian E) |>.map_fun L
  apply hG.iIndepFun_of_covariance_inner
  intro i j hij x y
  simp only [L, ContinuousLinearMap.pi_apply, id_eq]
  simp_rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← covarianceBilin_apply_eq_cov IsGaussian.hasGaussianLaw_id.memLp_two,
    covarianceBilin_stdGaussian, innerSL_apply_apply]
  exact (hK (Subtype.val_injective.ne hij)).inner_eq x.property y.property

/-- The joint projection law is the product of the standard Gaussians on the subspaces. -/
theorem map_orthogonalProjectionOnto_stdGaussian_pi [Fintype ι] (K : ι → Submodule ℝ E)
    (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    (stdGaussian E).map (fun x i ↦ (K i).orthogonalProjectionOnto x) =
      Measure.pi (fun i ↦ stdGaussian (K i)) :=
  ((iIndepFun_orthogonalProjectionOnto_stdGaussian K hK).hasLaw_pi
    (fun i ↦ ⟨by fun_prop, (K i).map_orthogonalProjectionOnto_stdGaussian⟩)).map_eq

/-- Squared lengths of mutually orthogonal Gaussian projections are jointly independent. -/
theorem iIndepFun_norm_sq_orthogonalProjectionOnto_stdGaussian
    (K : ι → Submodule ℝ E) (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    iIndepFun (fun i x ↦ ‖(K i).orthogonalProjectionOnto x‖ ^ 2) (stdGaussian E) :=
  (iIndepFun_orthogonalProjectionOnto_stdGaussian K hK).comp
    (fun i (x : K i) ↦ ‖x‖ ^ 2) (by fun_prop)

/-- Squared lengths of mutually orthogonal Gaussian projections have the product of the
chi-squared laws with the respective projection ranks. Zero ranks and empty families are allowed. -/
theorem map_norm_sq_orthogonalProjectionOnto_stdGaussian_pi [Fintype ι] (K : ι → Submodule ℝ E)
    (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    (stdGaussian E).map (fun x i ↦ ‖(K i).orthogonalProjectionOnto x‖ ^ 2) =
      Measure.pi (fun i ↦ chiSquaredMeasure (Module.finrank ℝ (K i))) :=
  ((iIndepFun_norm_sq_orthogonalProjectionOnto_stdGaussian K hK).hasLaw_pi fun i ↦
    ⟨by fun_prop, (K i).map_norm_sq_starProjection_stdGaussian⟩).map_eq

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}

/-- A standard Gaussian random vector projects to a standard Gaussian on each subspace. -/
theorem HasLaw.orthogonalProjectionOnto_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    (K : Submodule ℝ E) :
    HasLaw (fun ω ↦ K.orthogonalProjectionOnto (X ω)) (stdGaussian K) P :=
  (HasLaw.mk (by fun_prop) K.map_orthogonalProjectionOnto_stdGaussian).fun_comp hX

/-- The squared norm of a Gaussian projection has chi-squared law, including rank zero. -/
theorem HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian
    (hX : HasLaw X (stdGaussian E) P) (K : Submodule ℝ E) :
    HasLaw (fun ω ↦ ‖K.orthogonalProjectionOnto (X ω)‖ ^ 2)
      (chiSquaredMeasure (Module.finrank ℝ K)) P :=
  (hX.orthogonalProjectionOnto_stdGaussian K).norm_sq_stdGaussian

/-- The joint law of mutually orthogonal projections of a standard Gaussian random vector is
the product of the standard Gaussian laws on the subspaces. -/
theorem HasLaw.pi_orthogonalProjectionOnto_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    {ι : Type*} [Fintype ι] (K : ι → Submodule ℝ E) (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    HasLaw (fun ω i ↦ (K i).orthogonalProjectionOnto (X ω))
      (Measure.pi fun i ↦ stdGaussian (K i)) P :=
  (HasLaw.mk (by fun_prop) (map_orthogonalProjectionOnto_stdGaussian_pi K hK)).fun_comp hX

/-- Mutually orthogonal projections of a standard Gaussian random vector are jointly independent. -/
theorem HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    {ι : Type*} (K : ι → Submodule ℝ E) (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    iIndepFun (fun i ω ↦ (K i).orthogonalProjectionOnto (X ω)) P := by
  let _ := hX.isProbabilityMeasure
  refine iIndepFun_iff_finset.2 fun s ↦ ?_
  exact (iIndepFun_iff_hasLaw_pi_pi
    (fun i : s ↦ hX.orthogonalProjectionOnto_stdGaussian (K i))).2
    (hX.pi_orthogonalProjectionOnto_stdGaussian (fun i : s ↦ K i)
      (fun _ _ hij ↦ hK (Subtype.val_injective.ne hij)))

/-- Squared lengths of mutually orthogonal projections of a standard Gaussian random vector
are jointly independent. -/
theorem HasLaw.iIndepFun_norm_sq_orthogonalProjectionOnto_stdGaussian
    (hX : HasLaw X (stdGaussian E) P) {ι : Type*} (K : ι → Submodule ℝ E)
    (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    iIndepFun (fun i ω ↦ ‖(K i).orthogonalProjectionOnto (X ω)‖ ^ 2) P :=
  (hX.iIndepFun_orthogonalProjectionOnto_stdGaussian K hK).comp
    (fun i (x : K i) ↦ ‖x‖ ^ 2) (by fun_prop)

/-- The squared norms of mutually orthogonal projections of a standard Gaussian random vector
have the product of chi-squared laws, with degrees equal to the projection ranks. -/
theorem HasLaw.pi_norm_sq_orthogonalProjectionOnto_stdGaussian
    (hX : HasLaw X (stdGaussian E) P) {ι : Type*} [Fintype ι] (K : ι → Submodule ℝ E)
    (hK : Pairwise fun i j ↦ K i ⟂ K j) :
    HasLaw (fun ω i ↦ ‖(K i).orthogonalProjectionOnto (X ω)‖ ^ 2)
      (Measure.pi fun i ↦ chiSquaredMeasure (Module.finrank ℝ (K i))) P :=
  (HasLaw.mk (by fun_prop) (map_norm_sq_orthogonalProjectionOnto_stdGaussian_pi K hK)).fun_comp hX

end ProbabilityTheory
