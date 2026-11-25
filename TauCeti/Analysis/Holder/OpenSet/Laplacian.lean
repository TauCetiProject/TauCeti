/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Holder.OpenSet.Basic

/-!
# The Laplacian on the Hölder space `C^{2,α}(Ω)`

Let `Ω` be an open set of a finite-dimensional real inner product space `E`. The Laplacian
`Δu = ∑ᵢ D²u(eᵢ, eᵢ)`, for an orthonormal basis `(eᵢ)`, is a fixed continuous linear function of
the second derivative. Applied to the Hölder field `D²u` of an element `u ∈ C^{2,α}(Ω)`, it gives
a bounded `α`-Hölder function on `Ω`. This file packages the Laplacian as a continuous linear map
`C^{2,α}(Ω, F) → C^{0,α}(Ω, F)`, the second space being the bounded `α`-Hölder functions on the
subtype `Ω`, and identifies it with Mathlib's Laplacian of any function on `E` agreeing with `u`
near the evaluation point. The operator norm is at most `dim E`.

This is the principal part of the linearization at `0` of the minimal graph operator, which the
implicit-function argument for the small-data Dirichlet problem inverts together with the
boundary trace.

## Main declarations

* `TauCeti.CkHolderSpaceOn.laplacianL`: the Laplacian `C^{2,α}(Ω, F) →L[ℝ] C^{0,α}(Ω, F)`.
* `TauCeti.CkHolderSpaceOn.laplacianL_apply`: it equals `Δ` of a representative of the germ.
* `TauCeti.CkHolderSpaceOn.norm_laplacianL_le`: its operator norm is at most `dim E`.
-/

public noncomputable section

open Filter InnerProductSpace TopologicalSpace
open scoped NNReal Laplacian Topology

namespace TauCeti.CkHolderSpaceOn

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (α Ω F) in
/-- The Laplacian `Δu = ∑ᵢ D²u(eᵢ, eᵢ)` as a continuous linear map from `C^{2,α}(Ω, F)` to the
bounded `α`-Hölder functions on `Ω`, for the standard orthonormal basis `(eᵢ)` of `E`. -/
def laplacianL : CkHolderSpaceOn 2 α Ω F →L[ℝ] HolderSpace α Ω F :=
  HolderSpace.compLeftL (∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) F
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]) ∘L iteratedFDerivHolderL

/-- The Laplacian of an element of `C^{2,α}(Ω)` agrees on `Ω` with the Laplacian of its zero
extension. -/
theorem laplacianL_apply_eq_laplacian_extend (u : CkHolderSpaceOn 2 α Ω F) (x : Ω) :
    laplacianL α Ω F u x = Δ u.extend x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have h := u.iteratedFDeriv_eq u.extend_apply (Fin.last 2) x
  simp only [Fin.val_last] at h
  simp [laplacianL, h]

/-- The Laplacian of an element of `C^{2,α}(Ω)` is determined by its germ at the evaluation
point. -/
theorem laplacianL_apply (u : CkHolderSpaceOn 2 α Ω F) (x : Ω) {g : E → F}
    (hg : u.extend =ᶠ[𝓝 (x : E)] g) :
    laplacianL α Ω F u x = Δ g x :=
  (laplacianL_apply_eq_laplacian_extend u x).trans (laplacian_congr_nhds hg).eq_of_nhds

/-- The Laplacian `C^{2,α}(Ω) → C^{0,α}(Ω)` has operator norm at most `dim E`. -/
theorem norm_laplacianL_le : ‖laplacianL α Ω F‖ ≤ Module.finrank ℝ E := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul (HolderSpace.norm_compLeftL_le _) norm_iteratedFDerivHolderL_le_one
    (norm_nonneg _) (norm_nonneg _)).trans ?_
  rw [mul_one]
  have hcard : ∑ _i : Fin (Module.finrank ℝ E), (1 : ℝ) = Module.finrank ℝ E := by simp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans_eq hcard)
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m ↦ ?_
  refine (m.le_opNorm _).trans_eq ?_
  simp [Fin.prod_univ_two, (stdOrthonormalBasis ℝ E).orthonormal.1 i]

end TauCeti.CkHolderSpaceOn
