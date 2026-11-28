/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.LinearAlgebra.Multilinear.Basis

/-!
# The norm of a multilinear map from its values on bases

On finite-dimensional spaces `E j` with bases `b j`, a continuous multilinear map `T` is
determined by its values `T (b j (r j))_j` on tuples of basis vectors, and its operator norm is
controlled by them:

`‖T‖ ≤ (∏ j, ‖(b j).equivFunL‖) ∑_r ‖T (b j (r j))_j‖`,

where `(b j).equivFunL` is the coordinate isomorphism. This is the multilinear counterpart of
`Module.Basis.opNorm_le`. For the iterated derivative `D^n u (x)` of a function, with the same
basis in every slot, it bounds the full derivative by its partial derivatives along the basis
directions. For orthonormal bases the coordinate isomorphisms have norm at most one, which gives
`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`.

## Main results

* `ContinuousMultilinearMap.opNorm_le_prod_mul_sum_norm_apply_basis`: the bound above.
* `ContinuousMultilinearMap.sum_smulRight_apply_basis`: the expansion of a continuous multilinear
  map in the products of the coordinate functionals of the bases.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 G κ : Type*} {E ι : κ → Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G] [∀ j, Fintype (ι j)] [Fintype κ] [DecidableEq κ]

/-- The operator norm of a continuous multilinear map is at most the product of the norms of the
coordinate isomorphisms `(b j).equivFunL` of bases `b j`, one for each argument, times the sum of
the norms of its values on all tuples of basis vectors. -/
theorem opNorm_le_prod_mul_sum_norm_apply_basis (T : ContinuousMultilinearMap 𝕜 E G)
    (b : ∀ j, Module.Basis (ι j) 𝕜 (E j)) :
    ‖T‖ ≤ (∏ j, ‖((b j).equivFunL : E j →L[𝕜] ι j → 𝕜)‖) *
      ∑ r : ∀ j, ι j, ‖T fun j ↦ b j (r j)‖ := by
  refine T.opNorm_le_bound (mul_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)) fun m ↦ ?_
  -- Expand each argument in the basis and use multilinearity.
  rw [← coe_coe, T.toMultilinearMap.apply_eq_sum_prod_repr_smul b m, coe_coe, Finset.mul_sum,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)
  rw [norm_smul, norm_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with j
  -- The coordinates `(b j).repr (m j)` are the values of the coordinate isomorphism.
  rw [← Module.Basis.equivFunL_apply]
  exact (norm_le_pi_norm ((b j).equivFunL (m j)) (r j)).trans
    (((b j).equivFunL : E j →L[𝕜] ι j → 𝕜).le_opNorm (m j))

/-- A continuous multilinear map on finite-dimensional spaces `E j` with bases `b j` is the sum,
over all tuples `r` of basis indices, of the product of the coordinate functionals
`(b j).coord (r j)` times its value on the tuple of basis vectors `b j (r j)`. -/
theorem sum_smulRight_apply_basis [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ContinuousMultilinearMap 𝕜 E G) (b : ∀ j, Module.Basis (ι j) 𝕜 (E j)) :
    ∑ r : ∀ j, ι j, ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 κ 𝕜).compContinuousLinearMap fun j ↦
        LinearMap.toContinuousLinearMap ((b j).coord (r j))).smulRight (T fun j ↦ b j (r j)) =
      T := by
  classical
  refine toMultilinearMap_injective <| Module.Basis.ext_multilinear b fun r ↦ ?_
  simp only [coe_coe, sum_apply, smulRight_apply, compContinuousLinearMap_apply,
    mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hr'
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hj]), zero_smul]
  · simp

end ContinuousMultilinearMap
