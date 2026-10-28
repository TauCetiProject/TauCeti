/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Finite sections in a Hilbert basis

A countable Hilbert basis identifies the first `n + 1` coordinates with the genuine
Euclidean space on `Fin (n + 1)`. Compression to these coordinates is contractive,
commutes with adjoints, and its zero extension converges strongly to the original
operator, together with its adjoint. This provides the common finite-section
construction for native square-summable sequences and Hardy space via its Hilbert basis.

The coordinate expansion uses Mathlib's `HilbertBasis.hasSum_repr`.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for the finite-section method.
-/

public section

open scoped InnerProductSpace Topology
open Filter

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

namespace HilbertBasis

/-- Include the first `n + 1` coordinates in the Hilbert space. -/
noncomputable def finiteInclusion (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] H :=
  LinearMap.isometryOfInner
    { toFun := fun x ↦ ∑ i : Fin (n + 1), x i • b i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    (by
      intro x y
      simpa [PiLp.inner_apply, mul_comm] using
        (b.orthonormal.comp Fin.val Fin.val_injective).inner_sum x y Finset.univ)

/-- Inclusion is the finite basis expansion. -/
theorem finiteInclusion_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    b.finiteInclusion n x = ∑ i : Fin (n + 1), x i • b i := (rfl)

variable [CompleteSpace H]

/-- Restriction to the first `n + 1` Hilbert coordinates. -/
noncomputable def coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    H →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  (b.finiteInclusion n).toContinuousLinearMap.adjoint

/-- Coordinate restriction returns the corresponding Hilbert coefficient. -/
@[simp]
theorem coordinateCutoff_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H)
    (i : Fin (n + 1)) : b.coordinateCutoff n x i = b.repr x i := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (b.finiteInclusion n).toContinuousLinearMap (PiLp.single 2 i (1 : 𝕜)) x
  simpa [coordinateCutoff, EuclideanSpace.inner_single_left, finiteInclusion_apply,
    PiLp.single_apply, HilbertBasis.repr_apply_apply] using h

/-- The adjoint of coordinate restriction is the finite-coordinate inclusion. -/
@[simp]
theorem adjoint_coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.coordinateCutoff n).adjoint = (b.finiteInclusion n).toContinuousLinearMap := by
  simp [coordinateCutoff]

/-- Restricting an included vector recovers all its finite coordinates. -/
@[simp]
theorem coordinateCutoff_finiteInclusion (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    b.coordinateCutoff n (b.finiteInclusion n x) = x := by
  exact DFunLike.congr_fun (b.finiteInclusion n).adjoint_comp_self x

/-- Coordinate restriction is contractive. -/
theorem norm_coordinateCutoff_le (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.coordinateCutoff n‖ ≤ 1 := by
  simp [coordinateCutoff, LinearIsometry.norm_toContinuousLinearMap]

/-- The orthogonal projection retaining the first `n + 1` basis coordinates. -/
noncomputable def finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : H →L[𝕜] H :=
  (b.finiteInclusion n).toContinuousLinearMap ∘L b.coordinateCutoff n

/-- The projection is the partial Hilbert expansion. -/
theorem finiteProjection_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    b.finiteProjection n x = ∑ i : Fin (n + 1), b.repr x i • b i := by
  simp [finiteProjection, finiteInclusion_apply]

/-- Projection retains precisely the chosen coordinates. -/
@[simp]
theorem repr_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) (i : ℕ) :
    b.repr (b.finiteProjection n x) i = if i < n + 1 then b.repr x i else 0 := by
  rw [finiteProjection_apply]
  simp only [map_sum, map_smul, b.repr_self, lp.coeFn_sum, lp.coeFn_smul,
    Finset.sum_apply, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i < n + 1
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin (n + 1))]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ i := fun h ↦ hj (Fin.ext h)
      simp [Ne.symm hj']
    · simp
  · simp [hi, show ∀ j : Fin (n + 1), i ≠ j.val from fun j h ↦ hi (h ▸ j.isLt)]

/-- Finite coordinate projections are contractions. -/
theorem norm_finiteProjection_le (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteProjection n‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (b.finiteInclusion n).norm_toContinuousLinearMap_le
      (b.norm_coordinateCutoff_le n) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))

/-- The partial Hilbert expansions converge to the original vector. -/
theorem tendsto_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Tendsto (fun n ↦ b.finiteProjection n x) atTop (𝓝 x) := by
  have h := (b.hasSum_repr x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  exact (b.finiteProjection_apply n x).trans
    (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ b.repr x i • b i) (n + 1))

end HilbertBasis

variable [CompleteSpace H]

namespace ContinuousLinearMap

/-- Compress an operator to the first `n + 1` coordinates of a Hilbert basis. -/
noncomputable def finiteSection (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  b.coordinateCutoff n ∘L T ∘L (b.finiteInclusion n).toContinuousLinearMap

/-- Coordinates of a compressed operator are coordinates of its action on the finite expansion. -/
@[simp]
theorem finiteSection_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin (n + 1)) :
    T.finiteSection b n x i = b.repr (T (b.finiteInclusion n x)) i := by
  simp [finiteSection]

/-- The identity compresses to the identity on the actual finite Euclidean carrier. -/
@[simp]
theorem finiteSection_id (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 H).finiteSection b n =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  ext x
  simp [finiteSection]

/-- Compression commutes with the Hilbert adjoint. -/
@[simp]
theorem adjoint_finiteSection (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.finiteSection b n).adjoint = T.adjoint.finiteSection b n := by
  simp [finiteSection, HilbertBasis.coordinateCutoff, adjoint_comp, comp_assoc]

/-- Finite-section operator norms are bounded by the original operator norm. -/
theorem norm_finiteSection_le (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖T.finiteSection b n‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖b.coordinateCutoff n‖ * (‖T‖ * ‖(b.finiteInclusion n).toContinuousLinearMap‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
        (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) :=
      mul_le_mul (b.norm_coordinateCutoff_le n)
        (mul_le_mul_of_nonneg_left (b.finiteInclusion n).norm_toContinuousLinearMap_le
          (norm_nonneg _))
        (by positivity) zero_le_one
    _ = ‖T‖ := by simp

/-- Include a finite section back into the full Hilbert space, with zero outside its coordinates. -/
noncomputable def zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : H →L[𝕜] H :=
  (b.finiteInclusion n).toContinuousLinearMap ∘L T.finiteSection b n ∘L b.coordinateCutoff n

/-- The zero extension is the two-sided compression by the finite-coordinate projection. -/
theorem zeroExtendedFiniteSection_eq (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.zeroExtendedFiniteSection b n = b.finiteProjection n ∘L T ∘L b.finiteProjection n := by
  simp [zeroExtendedFiniteSection, finiteSection, HilbertBasis.finiteProjection, comp_assoc]

/-- Restricting a zero extension to finite coordinates recovers its finite section. -/
theorem coordinateCutoff_zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    b.coordinateCutoff n (T.zeroExtendedFiniteSection b n (b.finiteInclusion n x)) =
      T.finiteSection b n x := by
  simp [zeroExtendedFiniteSection]

/-- Zero extension also commutes with adjoints. -/
@[simp]
theorem adjoint_zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.zeroExtendedFiniteSection b n).adjoint = T.adjoint.zeroExtendedFiniteSection b n := by
  simp [zeroExtendedFiniteSection, HilbertBasis.coordinateCutoff, adjoint_comp, comp_assoc]

/-- Zero extensions of finite sections converge strongly to the original bounded operator. -/
theorem tendsto_zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Tendsto (fun n ↦ T.zeroExtendedFiniteSection b n x) atTop (𝓝 (T x)) := by
  simp only [zeroExtendedFiniteSection_eq, comp_apply]
  exact tendsto_apply_of_eventually_norm_le
    (Eventually.of_forall (b.norm_finiteProjection_le))
    (b.tendsto_finiteProjection (T x))
    ((T.continuous.tendsto x).comp (b.tendsto_finiteProjection x))

/-- The adjoints of the zero extensions converge strongly to the original adjoint. -/
theorem tendsto_adjoint_zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Tendsto (fun n ↦ (T.zeroExtendedFiniteSection b n).adjoint x) atTop
      (𝓝 (T.adjoint x)) := by
  simpa using T.adjoint.tendsto_zeroExtendedFiniteSection b x

end ContinuousLinearMap
