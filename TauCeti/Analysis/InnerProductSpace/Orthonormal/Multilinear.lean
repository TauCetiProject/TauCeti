/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Holder.Basic

/-!
# The norm of a multilinear map on an orthonormal basis

A continuous multilinear map `M` on finite-dimensional inner product spaces is determined by its
values on tuples of vectors of orthonormal bases `b j`, and its operator norm is controlled by
them: `‖M‖ ≤ ∑_r ‖M (fun j => b j (r j))‖`, the sum running over all tuples `r` of basis indices
(`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`). For a second derivative,
this bounds the norm of the Hessian by the sum of the absolute values of its matrix entries.
The linear case, `‖L‖ ≤ ∑ i, ‖L (b i)‖`, is
`ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`; for a first derivative it bounds
the norm of the gradient by the sum of the absolute values of the partial derivatives.

Conversely, the entries `H ![b i, b j]` of a bilinear map on an orthonormal basis are bounded by
the operator norm (`ContinuousMultilinearMap.norm_apply_orthonormalBasis_le`). For a bilinear map
`H` on a space with an orthonormal basis indexed by `ι`, an entry bound `‖H ![b i, b j]‖ ≤ B`
gives `‖H‖ ≤ (card ι)² B` (`ContinuousMultilinearMap.opNorm_le_card_sq_mul_of_norm_apply_le`).
A Hölder family of bilinear maps has Hölder entries with the same constant
(`HolderOnWith.apply_orthonormalBasis`), and conversely a family whose entries are Hölder with
constant `C` is Hölder with constant `(card ι)² C` (`HolderOnWith.of_apply_orthonormalBasis`).
These are the bounds relating a Hessian to its matrix entries.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E G ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

/-- The operator norm of a continuous linear map on an inner product space is at most the sum of
the norms of its values on the vectors of an orthonormal basis. -/
theorem opNorm_le_sum_norm_apply_orthonormalBasis (L : E →L[𝕜] G) (b : OrthonormalBasis ι 𝕜 E) :
    ‖L‖ ≤ ∑ i, ‖L (b i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  -- Expand the argument in the basis and use linearity.
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  gcongr
  exact (PiLp.norm_apply_le (b.repr x) i).trans_eq (b.repr.norm_map x)

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {𝕜 G κ : Type*} {E ι : κ → Type*} [RCLike 𝕜]
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [∀ j, Fintype (ι j)] [Fintype κ]

open scoped Classical in
/-- The operator norm of a continuous multilinear map on inner product spaces is at most the sum
of the norms of its values on tuples of vectors of orthonormal bases, one for each argument. -/
theorem opNorm_le_sum_norm_apply_orthonormalBasis
    (M : ContinuousMultilinearMap 𝕜 E G) (b : ∀ j, OrthonormalBasis (ι j) 𝕜 (E j)) :
    ‖M‖ ≤ ∑ r : ∀ j, ι j, ‖M fun j => b j (r j)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  -- Expand each argument in the basis and use multilinearity.
  have hM : M m = ∑ r : ∀ j, ι j, (∏ j, (b j).repr (m j) (r j)) •
      M fun j => b j (r j) := by
    conv_lhs => rw [← funext fun j => (b j).sum_repr (m j)]
    rw [M.map_sum]
    exact Finset.sum_congr rfl fun r _ => M.map_smul_univ _ _
  rw [hM, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr with j
  exact (PiLp.norm_apply_le ((b j).repr (m j)) (r j)).trans_eq ((b j).repr.norm_map (m j))

end ContinuousMultilinearMap

section Bilinear

variable {𝕜 E G ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

namespace ContinuousMultilinearMap

/-- An entry `H ![b i, b j]` of a bilinear map on an orthonormal basis `b` has norm at most the
operator norm. -/
theorem norm_apply_orthonormalBasis_le (H : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) G)
    (b : OrthonormalBasis ι 𝕜 E) (i j : ι) : ‖H ![b i, b j]‖ ≤ ‖H‖ := by
  simpa [Fin.prod_univ_two] using H.le_opNorm ![b i, b j]

/-- A bilinear map whose entries `H ![b i, b j]` on an orthonormal basis `b` are bounded by `B`
has operator norm at most `(card ι)² B`. -/
theorem opNorm_le_card_sq_mul_of_norm_apply_le
    (H : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) G) (b : OrthonormalBasis ι 𝕜 E) {B : ℝ}
    (hB : ∀ i j, ‖H ![b i, b j]‖ ≤ B) : ‖H‖ ≤ (Fintype.card ι : ℝ) ^ 2 * B := by
  classical
  refine (H.opNorm_le_sum_norm_apply_orthonormalBasis fun _ => b).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ B fun r _ => ?_).trans_eq ?_
  · have hr : (fun k => b (r k)) = ![b (r 0), b (r 1)] := by
      ext k : 1
      fin_cases k <;> rfl
    rw [hr]
    exact hB _ _
  · simp [Finset.card_univ, nsmul_eq_mul]

end ContinuousMultilinearMap

/-- A family of bilinear maps which is Hölder on a set has entries `H x ![b i, b j]`, on an
orthonormal basis `b`, which are Hölder there with the same constant. -/
theorem HolderOnWith.apply_orthonormalBasis {X : Type*} [PseudoEMetricSpace X]
    {H : X → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) G} {C r : NNReal} {s : Set X}
    (h : HolderOnWith C r H s) (b : OrthonormalBasis ι 𝕜 E) (i j : ι) :
    HolderOnWith C r (fun x => H x ![b i, b j]) s := fun x hx y hy => by
  refine le_trans ?_ (h x hx y hy)
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← sub_apply]
  exact ENNReal.ofReal_le_ofReal ((H x - H y).norm_apply_orthonormalBasis_le b i j)

/-- A family of bilinear maps whose entries `H x ![b i, b j]`, on an orthonormal basis `b` indexed
by `ι`, are Hölder on a set with constant `C` is Hölder there with constant `(card ι)² C`. This is
the converse of `HolderOnWith.apply_orthonormalBasis`. -/
theorem HolderOnWith.of_apply_orthonormalBasis {X : Type*} [PseudoMetricSpace X]
    {H : X → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) G} {C r : NNReal} {s : Set X}
    (b : OrthonormalBasis ι 𝕜 E) (h : ∀ i j, HolderOnWith C r (fun x => H x ![b i, b j]) s) :
    HolderOnWith ((Fintype.card ι : NNReal) ^ 2 * C) r H s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  rw [dist_eq_norm]
  refine ((H x - H y).opNorm_le_card_sq_mul_of_norm_apply_le b
    (B := C * dist x y ^ (r : ℝ)) fun i j => ?_).trans_eq (by push_cast; ring)
  rw [sub_apply, ← dist_eq_norm]
  exact (h i j).dist_le hx hy

end Bilinear
