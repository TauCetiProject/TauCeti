/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Projection
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Finite sections in a Hilbert basis

A countable Hilbert basis identifies the first `n + 1` coordinates with the genuine
Euclidean space on `Fin (n + 1)`. Compression to these coordinates is contractive,
commutes with adjoints, and its zero extension converges strongly to the original
operator, together with its adjoint. The finite-coordinate projection is the coordinate
projection `b.projection (Set.Iio (n + 1))`. Bundling the finite sections into the `ℓ^∞`
bounded product via `HilbertBasis.finiteSectionLpₗᵢ` (with operator-first form
`ContinuousLinearMap.finiteSectionLp`) gives a linear isometric embedding
`‖T.finiteSectionLp b‖ = ‖T‖`, and transporting the Hilbert basis along a linear
isometric equivalence `HilbertBasis.mapₗᵢ` conjugates projections and sections.
This provides the common finite-section construction for native square-summable
sequences and Hardy space via its Hilbert basis.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for the finite-section method.
-/

public section

open scoped ENNReal InnerProductSpace Topology
open Filter

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

namespace HilbertBasis

/-- Include the first `n + 1` coordinates in the Hilbert space. -/
noncomputable def finiteInclusion (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] H :=
  (b.orthonormal.comp Fin.val Fin.val_injective).synthesisMapIsometry

/-- Inclusion is the finite basis expansion. -/
theorem finiteInclusion_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    b.finiteInclusion n x = ∑ i : Fin (n + 1), x i • b i :=
  (b.orthonormal.comp Fin.val Fin.val_injective).synthesisMapIsometry_apply x

/-- Including a finite coordinate vector gives the corresponding Hilbert basis vector. -/
@[simp]
theorem finiteInclusion_single (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (i : Fin (n + 1)) : b.finiteInclusion n (PiLp.single 2 i (1 : 𝕜)) = b i := by
  rw [finiteInclusion_apply]
  simp [PiLp.single_apply]

/-- Transporting a Hilbert basis across a linear isometric equivalence post-composes
`HilbertBasis.finiteInclusion` with that equivalence. -/
@[simp]
theorem finiteInclusion_mapₗᵢ {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    (b : HilbertBasis ℕ 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    (b.mapₗᵢ e).finiteInclusion n = e.toLinearIsometry.comp (b.finiteInclusion n) := by
  ext x
  simp [finiteInclusion_apply, map_sum, map_smul]

variable [CompleteSpace H]

/-- Restriction to the first `n + 1` Hilbert coordinates. -/
noncomputable def coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    H →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  (b.finiteInclusion n).toContinuousLinearMap.adjoint

/-- Coordinate restriction returns the corresponding Hilbert coefficient. -/
@[simp]
theorem coordinateCutoff_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H)
    (i : Fin (n + 1)) : b.coordinateCutoff n x i = b.repr x i := by
  simpa only [coordinateCutoff, finiteInclusion, Function.comp_apply,
    HilbertBasis.repr_apply_apply] using
    (b.orthonormal.comp Fin.val Fin.val_injective).adjoint_synthesisMapIsometry_apply x i

/-- The adjoint of finite-coordinate inclusion is coordinate restriction. -/
@[simp]
theorem adjoint_finiteInclusion (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.finiteInclusion n).toContinuousLinearMap.adjoint = b.coordinateCutoff n :=
  (rfl)

/-- The adjoint of coordinate restriction is the finite-coordinate inclusion. -/
@[simp]
theorem adjoint_coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.coordinateCutoff n).adjoint = (b.finiteInclusion n).toContinuousLinearMap := by
  simp only [coordinateCutoff, ContinuousLinearMap.adjoint_adjoint]

/-- Restricting an included vector recovers all its finite coordinates. -/
@[simp]
theorem coordinateCutoff_finiteInclusion (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    b.coordinateCutoff n (b.finiteInclusion n x) = x := by
  exact DFunLike.congr_fun (b.finiteInclusion n).adjoint_comp_self x

/-- Coordinate restriction is contractive. -/
theorem norm_coordinateCutoff_le (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.coordinateCutoff n‖ ≤ 1 := by
  rw [coordinateCutoff, ContinuousLinearMap.adjoint.norm_map]
  exact (b.finiteInclusion n).norm_toContinuousLinearMap_le

/-- The orthogonal projection retaining the first `n + 1` basis coordinates. -/
noncomputable def finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : H →L[𝕜] H :=
  (b.finiteInclusion n).toContinuousLinearMap ∘L b.coordinateCutoff n

/-- Inclusion composed with coordinate restriction is the finite-coordinate projection. -/
@[simp]
theorem finiteInclusion_comp_coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.finiteInclusion n).toContinuousLinearMap ∘L b.coordinateCutoff n =
      b.finiteProjection n :=
  (rfl)

/-- Extending the finite identity operator by zero gives `b.finiteProjection n`. -/
theorem cornerEmbedding_finiteInclusion_id (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.finiteInclusion n).cornerEmbedding
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) = b.finiteProjection n := by
  simp

/-- The projection is the partial Hilbert expansion. -/
theorem finiteProjection_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    b.finiteProjection n x = ∑ i : Fin (n + 1), b.repr x i • b i := by
  simp only [finiteProjection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, finiteInclusion_apply, coordinateCutoff_apply]

/-- Including the restricted coordinates of a vector gives its finite-coordinate projection. -/
@[simp]
theorem finiteInclusion_coordinateCutoff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    b.finiteInclusion n (b.coordinateCutoff n x) = b.finiteProjection n x := by
  simp only [finiteProjection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]

/-- Projection retains precisely the chosen coordinates. -/
@[simp]
theorem repr_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) (i : ℕ) :
    b.repr (b.finiteProjection n x) i = if i < n + 1 then b.repr x i else 0 := by
  rw [b.repr_apply_apply, finiteProjection_apply,
    Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ b.repr x j • b j)]
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, Finset.mem_range]

/-- A basis vector is retained exactly when its index lies in the finite section. -/
@[simp]
theorem finiteProjection_basis (b : HilbertBasis ℕ 𝕜 H) (n i : ℕ) :
    b.finiteProjection n (b i) = if i < n + 1 then b i else 0 := by
  rw [finiteProjection_apply,
    Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ b.repr (b i) j • b j)]
  simp [HilbertBasis.repr_apply_apply, orthonormal_iff_ite.mp b.orthonormal,
    ite_smul, Finset.mem_range]

/-- The finite-section projection onto the first `n + 1` basis vectors is the coordinate
projection onto the indices `i < n + 1`. -/
theorem finiteProjection_eq_projection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    b.finiteProjection n = b.projection (Set.Iio (n + 1)) := by
  ext1 x
  apply b.repr.injective
  ext i
  by_cases hi : i < n + 1 <;> simp [hi]

/-- Finite-coordinate projection is idempotent. -/
@[simp]
theorem finiteProjection_comp_self (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    b.finiteProjection n ∘L b.finiteProjection n = b.finiteProjection n := by
  ext x
  simp [← finiteInclusion_coordinateCutoff]

/-- Finite-coordinate projection is self-adjoint. -/
@[simp]
theorem adjoint_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.finiteProjection n).adjoint = b.finiteProjection n := by
  simp only [finiteProjection, coordinateCutoff, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Finite coordinate projections are contractions. -/
theorem norm_finiteProjection_le (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteProjection n‖ ≤ 1 := by
  calc
    _ ≤ ‖(b.finiteInclusion n).toContinuousLinearMap‖ * ‖b.coordinateCutoff n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      gcongr
      · exact (b.finiteInclusion n).norm_toContinuousLinearMap_le
      · exact b.norm_coordinateCutoff_le n
    _ = 1 := by simp

/-- Every finite-coordinate projection has operator norm one. -/
@[simp]
theorem norm_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteProjection n‖ = 1 := by
  apply le_antisymm (b.norm_finiteProjection_le n)
  simpa [b.orthonormal.norm_eq_one] using (b.finiteProjection n).le_opNorm (b 0)

/-- The complementary tail projection `1 - b.finiteProjection n` has operator norm one. -/
@[simp]
theorem norm_one_sub_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖(1 : H →L[𝕜] H) - b.finiteProjection n‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [b.finiteProjection_eq_projection]
    exact IsStarProjection.norm_le _ (b.isStarProjection_projection _).one_sub
  · simpa [b.orthonormal.norm_eq_one] using
      ((1 : H →L[𝕜] H) - b.finiteProjection n).le_opNorm (b (n + 1))

/-- The difference `b.finiteProjection n - 1` has operator norm one. -/
@[simp]
theorem norm_finiteProjection_sub_one (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteProjection n - 1‖ = 1 := by
  rw [← norm_neg, neg_sub, norm_one_sub_finiteProjection]

/-- The partial Hilbert expansions converge to the original vector. -/
theorem tendsto_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Tendsto (fun n ↦ b.finiteProjection n x) atTop (𝓝 x) := by
  have h := (b.hasSum_repr x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  exact (b.finiteProjection_apply n x).trans
    (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ b.repr x i • b i) (n + 1))

/-- Transporting a Hilbert basis across a linear isometric equivalence pre-composes
`HilbertBasis.coordinateCutoff` with the inverse equivalence. -/
@[simp]
theorem coordinateCutoff_mapₗᵢ {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [CompleteSpace H'] (b : HilbertBasis ℕ 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    (b.mapₗᵢ e).coordinateCutoff n = b.coordinateCutoff n ∘L (e.symm : H' →L[𝕜] H) := by
  ext y i
  simp

/-- Transporting a Hilbert basis across a linear isometric equivalence conjugates
`HilbertBasis.finiteProjection` by that equivalence. -/
@[simp]
theorem finiteProjection_mapₗᵢ {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [CompleteSpace H'] (b : HilbertBasis ℕ 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    (b.mapₗᵢ e).finiteProjection n =
      (e : H →L[𝕜] H') ∘L b.finiteProjection n ∘L (e.symm : H' →L[𝕜] H) := by
  rw [finiteProjection, finiteProjection]
  ext y
  simp

end HilbertBasis

variable [CompleteSpace H]

namespace ContinuousLinearMap

/-- Compress an operator to the first `n + 1` coordinates of a Hilbert basis. -/
noncomputable def finiteSection (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  T.compression (b.finiteInclusion n).toContinuousLinearMap

/-- A finite section is compression along the finite-coordinate inclusion. -/
theorem finiteSection_def (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.finiteSection b n = T.compression (b.finiteInclusion n).toContinuousLinearMap :=
  (rfl)

/-- Coordinates of a compressed operator are coordinates of its action on the finite expansion. -/
@[simp]
theorem finiteSection_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin (n + 1)) :
    T.finiteSection b n x i = b.repr (T (b.finiteInclusion n x)) i := by
  simp [finiteSection]

/-- A finite section applied to restricted coordinates restricts the operator applied to the
finite-coordinate projection. -/
theorem finiteSection_coordinateCutoff (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : H) :
    T.finiteSection b n (b.coordinateCutoff n x) =
      b.coordinateCutoff n (T (b.finiteProjection n x)) := by
  simp [finiteSection]

/-- The finite-section matrix entry is the corresponding Hilbert inner product. -/
theorem finiteSection_single_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (i j : Fin (n + 1)) :
    T.finiteSection b n (PiLp.single 2 j (1 : 𝕜)) i = ⟪b i, T (b j)⟫_𝕜 := by
  simp [HilbertBasis.repr_apply_apply]

/-- Compression preserves the zero operator. -/
@[simp]
theorem finiteSection_zero (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (0 : H →L[𝕜] H).finiteSection b n = 0 := by
  simp [finiteSection]

/-- Compression preserves addition of operators. -/
@[simp]
theorem finiteSection_add (T S : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T + S).finiteSection b n = T.finiteSection b n + S.finiteSection b n := by
  simp [finiteSection]

/-- Compression preserves subtraction of operators. -/
@[simp]
theorem finiteSection_sub (T S : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T - S).finiteSection b n = T.finiteSection b n - S.finiteSection b n := by
  simp [finiteSection]

/-- Compression preserves negation of operators. -/
@[simp]
theorem finiteSection_neg (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (-T).finiteSection b n = -T.finiteSection b n := by
  rw [← zero_sub, finiteSection_sub, finiteSection_zero, zero_sub]

/-- Compression preserves scalar multiplication of operators. -/
@[simp]
theorem finiteSection_smul (c : 𝕜) (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (c • T).finiteSection b n = c • T.finiteSection b n := by
  simp [finiteSection]

/-- The identity compresses to the identity on the actual finite Euclidean carrier. -/
@[simp]
theorem finiteSection_id (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 H).finiteSection b n =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  ext x
  simp [finiteSection]

/-- Compression preserves the multiplicative identity operator. -/
@[simp]
theorem finiteSection_one (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (1 : H →L[𝕜] H).finiteSection b n = 1 :=
  finiteSection_id b n

/-- Compression commutes with the Hilbert adjoint. -/
@[simp]
theorem adjoint_finiteSection (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T.finiteSection b n).adjoint = T.adjoint.finiteSection b n := by
  simp only [finiteSection, adjoint_compression]

/-- Compression preserves the star operation on the operator algebra. -/
@[simp]
theorem finiteSection_star (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (star T).finiteSection b n = star (T.finiteSection b n) := by
  simp only [star_eq_adjoint, adjoint_finiteSection]

/-- Finite sections in a Hilbert basis transported across a linear isometric equivalence agree
with finite sections of the conjugated operator in the original basis. -/
@[simp]
theorem finiteSection_mapₗᵢ {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [CompleteSpace H'] (S : H' →L[𝕜] H') (b : HilbertBasis ℕ 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    S.finiteSection (b.mapₗᵢ e) n =
      ((e.symm : H' →L[𝕜] H) ∘L S ∘L (e : H →L[𝕜] H')).finiteSection b n := by
  ext x i
  simp

/-- Finite-section operator norms are bounded by the original operator norm. -/
theorem norm_finiteSection_le (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖T.finiteSection b n‖ ≤ ‖T‖ := by
  rw [finiteSection, compression_def, HilbertBasis.adjoint_finiteInclusion]
  calc
    _ ≤ ‖b.coordinateCutoff n‖ * (‖T‖ * ‖(b.finiteInclusion n).toContinuousLinearMap‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
        (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by
      gcongr
      · exact b.norm_coordinateCutoff_le n
      · exact (b.finiteInclusion n).norm_toContinuousLinearMap_le
    _ = ‖T‖ := by simp

/-- Include a finite section back into the full Hilbert space, with zero outside its coordinates. -/
noncomputable def zeroExtendedFiniteSection (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : H →L[𝕜] H :=
  (b.finiteInclusion n).cornerEmbedding (T.finiteSection b n)

/-- The zero extension applies the finite section to the restricted coordinates and includes the
result. -/
theorem zeroExtendedFiniteSection_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (x : H) :
    T.zeroExtendedFiniteSection b n x =
      b.finiteInclusion n (T.finiteSection b n (b.coordinateCutoff n x)) := by
  simp only [zeroExtendedFiniteSection, LinearIsometry.cornerEmbedding_apply_apply,
    HilbertBasis.adjoint_finiteInclusion]

/-- Zero extension of finite sections preserves the zero operator. -/
@[simp]
theorem zeroExtendedFiniteSection_zero (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (0 : H →L[𝕜] H).zeroExtendedFiniteSection b n = 0 := by
  simp [zeroExtendedFiniteSection]

/-- Zero extension of finite sections preserves negation of operators. -/
@[simp]
theorem zeroExtendedFiniteSection_neg (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (-T).zeroExtendedFiniteSection b n = -T.zeroExtendedFiniteSection b n := by
  simp [zeroExtendedFiniteSection]

/-- Zero extension of finite sections preserves addition of operators. -/
@[simp]
theorem zeroExtendedFiniteSection_add (T S : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T + S).zeroExtendedFiniteSection b n =
      T.zeroExtendedFiniteSection b n + S.zeroExtendedFiniteSection b n := by
  simp [zeroExtendedFiniteSection]

/-- Zero extension of finite sections preserves subtraction of operators. -/
@[simp]
theorem zeroExtendedFiniteSection_sub (T S : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (T - S).zeroExtendedFiniteSection b n =
      T.zeroExtendedFiniteSection b n - S.zeroExtendedFiniteSection b n := by
  simp [zeroExtendedFiniteSection]

/-- Zero extension of finite sections preserves scalar multiplication of operators. -/
@[simp]
theorem zeroExtendedFiniteSection_smul (c : 𝕜) (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (c • T).zeroExtendedFiniteSection b n = c • T.zeroExtendedFiniteSection b n := by
  simp [zeroExtendedFiniteSection]

/-- The zero-extended `n`-th finite section of the identity map is `b.finiteProjection n`. -/
@[simp]
theorem zeroExtendedFiniteSection_id (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 H).zeroExtendedFiniteSection b n = b.finiteProjection n := by
  simp [zeroExtendedFiniteSection]

/-- A finite section and its zero extension have exactly the same operator norm. -/
@[simp]
theorem norm_zeroExtendedFiniteSection_eq (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖T.zeroExtendedFiniteSection b n‖ = ‖T.finiteSection b n‖ := by
  rw [zeroExtendedFiniteSection, LinearIsometry.norm_map]

/-- The norm of a zero-extended finite section is bounded by the original operator norm. -/
theorem norm_zeroExtendedFiniteSection_le (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖T.zeroExtendedFiniteSection b n‖ ≤ ‖T‖ := by
  rw [norm_zeroExtendedFiniteSection_eq]
  exact T.norm_finiteSection_le b n

/-- The zero extension is the two-sided compression by the finite-coordinate projection. -/
theorem zeroExtendedFiniteSection_eq (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.zeroExtendedFiniteSection b n = b.finiteProjection n ∘L T ∘L b.finiteProjection n := by
  rw [zeroExtendedFiniteSection, finiteSection, LinearIsometry.cornerEmbedding_compression,
    HilbertBasis.adjoint_finiteInclusion, HilbertBasis.finiteInclusion_comp_coordinateCutoff,
    compression_def, HilbertBasis.adjoint_finiteProjection]

/-- Restricting a zero extension to finite coordinates recovers its finite section. -/
@[simp]
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
  simp only [zeroExtendedFiniteSection, LinearIsometry.adjoint_cornerEmbedding,
    adjoint_finiteSection]

/-- Zero extension of finite sections preserves `star`. -/
@[simp]
theorem zeroExtendedFiniteSection_star (T : H →L[𝕜] H)
    (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (star T).zeroExtendedFiniteSection b n = star (T.zeroExtendedFiniteSection b n) := by
  simp only [star_eq_adjoint, adjoint_zeroExtendedFiniteSection]

/-- Transporting a Hilbert basis across a linear isometric equivalence conjugates
`ContinuousLinearMap.zeroExtendedFiniteSection`. -/
@[simp]
theorem zeroExtendedFiniteSection_mapₗᵢ {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace 𝕜 H'] [CompleteSpace H'] (S : H' →L[𝕜] H') (b : HilbertBasis ℕ 𝕜 H)
    (e : H ≃ₗᵢ[𝕜] H') (n : ℕ) :
    S.zeroExtendedFiniteSection (b.mapₗᵢ e) n =
      (e : H →L[𝕜] H') ∘L
        ((e.symm : H' →L[𝕜] H) ∘L S ∘L (e : H →L[𝕜] H')).zeroExtendedFiniteSection b n ∘L
        (e.symm : H' →L[𝕜] H) := by
  ext y
  simp [zeroExtendedFiniteSection_eq]

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

-- Try `Module`-based `SMul` before `Algebra.toSMul`, which times out unifying `Semiring` paths on
-- `lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞`.
attribute [local instance 2000] SMulZeroClass.toSMul

private noncomputable def finiteSectionLpAux (b : HilbertBasis ℕ 𝕜 H) (T : H →L[𝕜] H) :
    lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞ :=
  ⟨fun n ↦ T.finiteSection b n,
    memℓp_infty ⟨‖T‖, Set.forall_mem_range.mpr (T.norm_finiteSection_le b)⟩⟩

private theorem finiteSectionLpAux_apply (b : HilbertBasis ℕ 𝕜 H) (T : H →L[𝕜] H) (n : ℕ) :
    finiteSectionLpAux b T n = T.finiteSection b n :=
  rfl

private theorem finiteSectionLpAux_add (b : HilbertBasis ℕ 𝕜 H) (T S : H →L[𝕜] H) :
    finiteSectionLpAux b (T + S) = finiteSectionLpAux b T + finiteSectionLpAux b S := by
  ext n
  simp [finiteSectionLpAux_apply]

private theorem finiteSectionLpAux_smul (b : HilbertBasis ℕ 𝕜 H) (c : 𝕜) (T : H →L[𝕜] H) :
    finiteSectionLpAux b (c • T) = c • finiteSectionLpAux b T := by
  ext n
  simp [finiteSectionLpAux_apply]

private theorem norm_finiteSectionLpAux (b : HilbertBasis ℕ 𝕜 H) (T : H →L[𝕜] H) :
    ‖finiteSectionLpAux b T‖ = ‖T‖ := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le (norm_nonneg T) (T.norm_finiteSection_le b)
  · refine T.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
    refine le_of_tendsto' (T.tendsto_zeroExtendedFiniteSection b x).norm fun n ↦ ?_
    calc
      ‖T.zeroExtendedFiniteSection b n x‖ ≤ ‖T.zeroExtendedFiniteSection b n‖ * ‖x‖ :=
        le_opNorm _ _
      _ = ‖finiteSectionLpAux b T n‖ * ‖x‖ := by
        rw [norm_zeroExtendedFiniteSection_eq, finiteSectionLpAux_apply]
      _ ≤ ‖finiteSectionLpAux b T‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (lp.norm_apply_le_norm ENNReal.top_ne_zero (finiteSectionLpAux b T) n) (norm_nonneg x)

/-- Bundle the finite sections in a Hilbert basis `b` as a linear isometry into the bounded product
`lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞`. -/
noncomputable def _root_.HilbertBasis.finiteSectionLpₗᵢ (b : HilbertBasis ℕ 𝕜 H) :
    (H →L[𝕜] H) →ₗᵢ[𝕜]
      lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞ where
  toLinearMap :=
    { toFun := finiteSectionLpAux b
      map_add' := finiteSectionLpAux_add b
      map_smul' := finiteSectionLpAux_smul b }
  norm_map' := norm_finiteSectionLpAux b

/-- Bundle the finite sections of `T` in a Hilbert basis `b` as an element of the bounded product
`lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞`. -/
noncomputable def finiteSectionLp (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    lp (fun n ↦ EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) ∞ :=
  b.finiteSectionLpₗᵢ T

/-- Applying `HilbertBasis.finiteSectionLpₗᵢ` gives `ContinuousLinearMap.finiteSectionLp`. -/
@[simp]
theorem _root_.HilbertBasis.finiteSectionLpₗᵢ_apply (b : HilbertBasis ℕ 𝕜 H) (T : H →L[𝕜] H) :
    b.finiteSectionLpₗᵢ T = T.finiteSectionLp b :=
  (rfl)

/-- Coercing `T.finiteSectionLp b` to a sequence returns `T.finiteSection b`. -/
theorem coeFn_finiteSectionLp (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    ⇑(T.finiteSectionLp b) = T.finiteSection b :=
  (rfl)

/-- Evaluating `T.finiteSectionLp b` at index `n` returns `T.finiteSection b n`. -/
@[simp]
theorem finiteSectionLp_apply (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.finiteSectionLp b n = T.finiteSection b n :=
  (rfl)

/-- Bundling finite sections preserves `0`. -/
@[simp]
theorem finiteSectionLp_zero (b : HilbertBasis ℕ 𝕜 H) :
    (0 : H →L[𝕜] H).finiteSectionLp b = 0 :=
  b.finiteSectionLpₗᵢ.map_zero

/-- Bundling finite sections preserves `1`. -/
@[simp]
theorem finiteSectionLp_one (b : HilbertBasis ℕ 𝕜 H) :
    (1 : H →L[𝕜] H).finiteSectionLp b = 1 := by
  ext n
  simp [lp.infty_coeFn_one, ContinuousLinearMap.one_def]

/-- Bundling finite sections preserves negation. -/
@[simp]
theorem finiteSectionLp_neg (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    (-T).finiteSectionLp b = -T.finiteSectionLp b :=
  b.finiteSectionLpₗᵢ.map_neg T

/-- Bundling finite sections preserves addition. -/
@[simp]
theorem finiteSectionLp_add (T S : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    (T + S).finiteSectionLp b = T.finiteSectionLp b + S.finiteSectionLp b :=
  b.finiteSectionLpₗᵢ.map_add T S

/-- Bundling finite sections preserves subtraction. -/
@[simp]
theorem finiteSectionLp_sub (T S : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    (T - S).finiteSectionLp b = T.finiteSectionLp b - S.finiteSectionLp b :=
  b.finiteSectionLpₗᵢ.map_sub T S

/-- Bundling finite sections preserves scalar multiplication. -/
@[simp]
theorem finiteSectionLp_smul (c : 𝕜) (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    (c • T).finiteSectionLp b = c • T.finiteSectionLp b :=
  b.finiteSectionLpₗᵢ.map_smul c T

/-- Bundling finite sections commutes with `star`. -/
@[simp]
theorem finiteSectionLp_star (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    (star T).finiteSectionLp b = star (T.finiteSectionLp b) := by
  ext n
  simp

/-- Bundled finite sections in a transported Hilbert basis agree with those of the conjugated
operator in the original basis. -/
@[simp]
theorem finiteSectionLp_mapₗᵢ {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
    [CompleteSpace H'] (S : H' →L[𝕜] H') (b : HilbertBasis ℕ 𝕜 H) (e : H ≃ₗᵢ[𝕜] H') :
    S.finiteSectionLp (b.mapₗᵢ e) =
      ((e.symm : H' →L[𝕜] H) ∘L S ∘L (e : H →L[𝕜] H')).finiteSectionLp b := by
  ext n
  simp

/-- The supremum norm of the finite sections of `T` equals the operator norm of `T`. -/
@[simp]
theorem norm_finiteSectionLp (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) :
    ‖T.finiteSectionLp b‖ = ‖T‖ :=
  b.finiteSectionLpₗᵢ.norm_map T

end ContinuousLinearMap
