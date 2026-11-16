/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# The curvature reaction tensor on four-tensors

Under Ricci flow on a Riemannian manifold, the pullback of the Riemann curvature four-tensor to a
fixed metric bundle via Uhlenbeck's moving frame evolves by a reaction-diffusion equation
`D_t R = Δ R + Q(R)`. On each tangent fibre `(V, ⟪·, ·⟫)`, the reaction term `Q(r)` of a
four-tensor `r : FourTensor V` is the quadratic contraction whose components in an orthonormal
basis `b` are

`Q(r)_ijkl = ∑_pq r_ijpq r_klpq + 2 ∑_pq r_ipkq r_jplq - 2 ∑_pq r_iplq r_jpkq`

with `r_abcd = r(b a, b b', b c, b d)`. Expanding these components against the rank-one coordinate
four-tensors `coordFourTensor b i j k l` in `stdOrthonormalBasis ℝ V` defines
`TauCeti.FourTensor.reactionTensor`.

Although `reactionTensor` is written in the standard orthonormal basis, each double sum over `p, q`
is a full metric contraction of two four-tensors, so `reactionTensor` is independent of the chosen
orthonormal basis (`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`). More generally,
pulling back along any continuous linear map whose adjoint is a linear isometry — in particular any
linear isometric equivalence or any orthogonal projection onto a subspace — commutes with
`reactionTensor`.

Symmetrizing the bilinear contraction produces a continuous symmetric bilinear map
`TauCeti.FourTensor.reactionBilinear V` with `reactionBilinear V r r = reactionTensor r`. From this
polarization we obtain quadratic homogeneity, smoothness (`ContDiff ℝ ∞`), an explicit Fréchet
derivative `2 • reactionBilinear V r`, explicit dimensional operator-norm bounds
`‖reactionTensor r‖ ≤ 5 * (finrank ℝ V) ^ 2 * ‖r‖ ^ 2`, and explicit radius-linear Lipschitz bounds
on bounded sets.

For algebraic curvature tensors, first Bianchi cancellation implies that `reactionTensor` and
`reactionBilinear V` preserve all four algebraic curvature symmetries
(`TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`, `TauCeti.FourTensor.reactionTensor_mem`),
and simplifies the Ricci and scalar contractions of `Q(r)` to
`Ric(Q(r))(u, v) = 2 ∑_pq Ric(r)(b p, b q) r(b p, u, b q, v)` and
`Scal(Q(r)) = 2 ∑_pq Ric(r)(b p, b q) ^ 2`. On the constant-curvature tensor of curvature `1`,
`Q` acts with eigenvalue `2 (n - 1)`, and on the curvature tensor of `S^k × ℝ^(n - k)` obtained by
pulling back the constant-curvature tensor of a `k`-dimensional subspace `K` along its orthogonal
projection, `Q` acts with eigenvalue `2 (k - 1)` (in particular `2` when `dim K = 2`).

## Main definitions

* `TauCeti.FourTensor.reactionComponent`: the components `Q(r)_ijkl` of the reaction tensor in an
  orthonormal basis.
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction map `FourTensor V → FourTensor V`.
* `TauCeti.FourTensor.reactionBilinear`: the symmetric continuous bilinear polarization
  `FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V` with
  `reactionBilinear V r r = reactionTensor r`.

## Main statements

* `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: basis independence of `reactionTensor`
  across all orthonormal bases of `V`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor` and
  `TauCeti.FourTensor.reactionTensor_mem`: `reactionTensor` maps `algebraicCurvatureSubmodule V` to
  itself.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv` and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto`: orthogonal
  and coisometric equivariance of `reactionTensor`.
* `TauCeti.FourTensor.norm_reactionTensor_le`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`, and
  `TauCeti.FourTensor.contDiff_reactionTensor`: explicit dimensional bounds, bounded-set Lipschitz
  estimates, Fréchet derivative, and smoothness of `reactionTensor`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_reactionTensor_apply_orthonormalBasis` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_reactionTensor_eq_sum`: the Ricci and scalar
  contractions of `reactionTensor r` for an algebraic curvature tensor `r`.
* `TauCeti.FourTensor.reactionTensor_constantCurvature` and
  `TauCeti.FourTensor.reactionTensor_constantCurvature_comp_orthogonalProjectionOnto`: evaluation of
  `reactionTensor` on constant-curvature and subspace-product curvature tensors.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 2.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
* P. Topping, *Lectures on the Ricci Flow*, London Math. Soc. Lecture Note Ser. 325, Cambridge
  University Press (2006), Section 2.5.
-/

public section

open scoped InnerProductSpace NNReal

noncomputable section

namespace TauCeti

namespace FourTensor

section Helpers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem abs_apply_basis_le_34 {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (r : FourTensor V) (u v : V) (p q : ι) :
    |r ![u, v, b p, b q]| ≤ ‖r‖ * ‖u‖ * ‖v‖ := by
  simpa only [Fin.prod_univ_four, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, hb.1 p, hb.1 q, mul_one, mul_assoc] using
    r.le_opNorm ![u, v, b p, b q]

private theorem abs_apply_basis_le_24 {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (r : FourTensor V) (u z : V) (p q : ι) :
    |r ![u, b p, z, b q]| ≤ ‖r‖ * ‖u‖ * ‖z‖ := by
  simpa only [Fin.prod_univ_four, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, hb.1 p, hb.1 q, one_mul, mul_one, mul_assoc] using
    r.le_opNorm ![u, b p, z, b q]

private def slice34 (r : FourTensor V) (u v : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

private def slice24 (r : FourTensor V) (u z : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

end Helpers

section Reaction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The components of the reaction tensor `Q(r)` in an orthonormal basis `b`, with
`r_ijpq = r(b i, b j, b p, b q)`:
`Q(r)_ijkl = ∑_pq r_ijpq r_klpq + 2 ∑_pq r_ipkq r_jplq - 2 ∑_pq r_iplq r_jpkq`. -/
def reactionComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
  2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
  2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q])

/-- The reaction tensor `Q(r)` of the curvature evolution equation, expanded in the standard
orthonormal basis of `V`:
`Q(r) = ∑_ijkl Q(r)_ijkl • coordFourTensor (stdOrthonormalBasis ℝ V) i j k l`.
Its independence of the orthonormal basis is `reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

private def reactionBilinearComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * s ![b k, b l, b p, b q]) +
  2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * s ![b j, b p, b l, b q]) -
  2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * s ![b j, b p, b k, b q])

private def reactionBilinearRawFun (r s : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionBilinearComponent (stdOrthonormalBasis ℝ V) r s i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

private def slice12 (r : FourTensor V) (x y : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)

private def slice13 (r : FourTensor V) (x y : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u z ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)

private def tensorBilin (A B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  A.compr₂ ((LinearMap.lsmul ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℝ)).flip B)

/-- The four-tensor whose value on `(u, v, z, w)` is the asymmetric contraction of `r` and `s` in
an orthonormal basis `b`. -/
private def reactionBilinearContraction {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) : FourTensor V :=
  (∑ p, ∑ q, ofLinearMap₄ (tensorBilin (slice12 r (b p) (b q)) (slice12 s (b p) (b q)))) +
  (2 : ℝ) • (∑ p, ∑ q, ofLinearMap₄
    ((LinearMap.lflip (R₀ := ℝ)).toLinearMap.comp
      (tensorBilin (slice13 r (b p) (b q)) (slice13 s (b p) (b q))))) -
  (2 : ℝ) • (∑ p, ∑ q, ofLinearMap₄
    (((LinearMap.lflip (R₀ := ℝ)).toLinearMap.comp
      (tensorBilin (slice13 r (b p) (b q)) (slice13 s (b p) (b q)))).compr₂
      (LinearMap.lflip (R₀ := ℝ)).toLinearMap))

private theorem reactionBilinearContraction_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinearContraction b r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  simp [reactionBilinearContraction, tensorBilin, slice12, slice13]

private theorem reactionBilinearRawFun_eq_contraction (r s : FourTensor V) :
    reactionBilinearRawFun r s = reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s := by
  rw [← sum_coordFourTensor_eq (stdOrthonormalBasis ℝ V)
    (reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s)]
  simp only [reactionBilinearRawFun, reactionBilinearContraction_apply, reactionBilinearComponent]

private theorem reactionBilinearRawFun_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinearRawFun r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  let b₀ := stdOrthonormalBasis ℝ V
  have hid : ∀ x y : V, ⟪(id : V → V) x, y⟫_ℝ = ⟪x, (LinearIsometry.id : V →ₗᵢ[ℝ] V) y⟫_ℝ :=
    fun _ _ ↦ rfl
  have h1 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid (slice34 r u v) (slice34 s z w)
  have h2 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid (slice24 r u z) (slice24 s v w)
  have h3 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid (slice24 r u w) (slice24 s v z)
  simp only [Real.inner_apply, slice34, slice24, LinearMap.mk₂_apply, id_eq] at h1 h2 h3
  rw [reactionBilinearRawFun_eq_contraction, reactionBilinearContraction_apply, h1, h2, h3]

/-- **Basis independence of the reaction tensor**: in every orthonormal basis `b` of `V`, `Q(r)` is
the contraction
`Q(r)(u, v, z, w) = ∑_pq r(u, v, b p, b q) r(z, w, b p, b q)
  + 2 ∑_pq r(u, b p, z, b q) r(v, b p, w, b q) - 2 ∑_pq r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) :=
  reactionBilinearRawFun_apply_orthonormalBasis b r r u v z w

/-- Evaluating `reactionTensor r` on four vectors of any orthonormal basis `b` recovers
`reactionComponent b r`. -/
@[simp]
theorem reactionTensor_apply_orthonormalBasis_eq_reactionComponent {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (i j k l : ι) :
    reactionTensor r ![b i, b j, b k, b l] = reactionComponent b r i j k l :=
  reactionTensor_apply_orthonormalBasis b r (b i) (b j) (b k) (b l)

/-- Expanding `reactionComponent b r` against `coordFourTensor b` in any orthonormal basis `b`
produces `reactionTensor r`. -/
theorem sum_reactionComponent_smul_coordFourTensor {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, reactionComponent b r i j k l • coordFourTensor b i j k l) =
      reactionTensor r := by
  simpa only [reactionTensor_apply_orthonormalBasis_eq_reactionComponent] using
    sum_coordFourTensor_eq b (reactionTensor r)

end Reaction

section Polarization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem norm_reactionBilinearRawFun_le (r s : FourTensor V) :
    ‖reactionBilinearRawFun r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  let b := stdOrthonormalBasis ℝ V
  have hb := b.orthonormal
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm,
    reactionBilinearRawFun_apply_orthonormalBasis b, Fin.prod_univ_four]
  simp only [Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue]
  set M := ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have hsum1 : |∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    rw [← Finset.sum_product']
    refine (Finset.abs_sum_le_card_nsmul (B := M) fun pq _ ↦ ?_).trans_eq (by simp [sq])
    rw [abs_mul]
    calc |r ![m 0, m 1, b pq.1, b pq.2]| * |s ![m 2, m 3, b pq.1, b pq.2]|
        ≤ (‖r‖ * ‖m 0‖ * ‖m 1‖) * (‖s‖ * ‖m 2‖ * ‖m 3‖) := by
          gcongr <;> exact abs_apply_basis_le_34 hb _ _ _ _ _
      _ = M := by simp only [M]; ring
  have hsum23 (u₁ u₂ : V) (hu : ‖u₁‖ * ‖u₂‖ = ‖m 2‖ * ‖m 3‖) :
      |∑ p, ∑ q, r ![m 0, b p, u₁, b q] * s ![m 1, b p, u₂, b q]| ≤
        (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    rw [← Finset.sum_product']
    refine (Finset.abs_sum_le_card_nsmul (B := M) fun pq _ ↦ ?_).trans_eq (by simp [sq])
    rw [abs_mul]
    calc |r ![m 0, b pq.1, u₁, b pq.2]| * |s ![m 1, b pq.1, u₂, b pq.2]|
        ≤ (‖r‖ * ‖m 0‖ * ‖u₁‖) * (‖s‖ * ‖m 1‖ * ‖u₂‖) := by
          gcongr <;> exact abs_apply_basis_le_24 hb _ _ _ _ _
      _ = M := by simp only [M]; linear_combination ‖r‖ * ‖s‖ * ‖m 0‖ * ‖m 1‖ * hu
  have hsum2 := hsum23 (m 2) (m 3) rfl
  have hsum3 := hsum23 (m 3) (m 2) (mul_comm _ _)
  have habs (a b c : ℝ) : |a + 2 * b - 2 * c| ≤ |a| + 2 * |b| + 2 * |c| :=
    (abs_sub _ _).trans <| by
      simpa [abs_mul] using add_le_add_right (abs_add_le a (2 * b)) |2 * c|
  calc |(∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]) +
        2 * (∑ p, ∑ q, r ![m 0, b p, m 2, b q] * s ![m 1, b p, m 3, b q]) -
        2 * (∑ p, ∑ q, r ![m 0, b p, m 3, b q] * s ![m 1, b p, m 2, b q])|
      ≤ _ := habs _ _ _
    _ ≤ (Module.finrank ℝ V : ℝ) ^ 2 * M + 2 * ((Module.finrank ℝ V : ℝ) ^ 2 * M) +
          2 * ((Module.finrank ℝ V : ℝ) ^ 2 * M) := by gcongr
    _ = 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ *
          (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by simp only [M]; ring

private def reactionBilinearFun (r s : FourTensor V) : FourTensor V :=
  (1 / 2 : ℝ) • (reactionBilinearRawFun r s + reactionBilinearRawFun s r)

private theorem reactionBilinearFun_comm (r s : FourTensor V) :
    reactionBilinearFun r s = reactionBilinearFun s r := by
  simp only [reactionBilinearFun, add_comm]

private theorem reactionBilinearFun_self (r : FourTensor V) :
    reactionBilinearFun r r = reactionTensor r := by
  change (1 / 2 : ℝ) • (reactionTensor r + reactionTensor r) = reactionTensor r
  rw [← two_smul ℝ (reactionTensor r), smul_smul]; norm_num

private theorem reactionBilinearFun_add_left (r₁ r₂ s : FourTensor V) :
    reactionBilinearFun (r₁ + r₂) s = reactionBilinearFun r₁ s + reactionBilinearFun r₂ s := by
  ext m; rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm]
  simp only [reactionBilinearFun, smul_apply, add_apply, smul_eq_mul,
    reactionBilinearRawFun_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem reactionBilinearFun_smul_left (c : ℝ) (r s : FourTensor V) :
    reactionBilinearFun (c • r) s = c • reactionBilinearFun r s := by
  ext m; rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm]
  simp only [reactionBilinearFun, smul_apply, add_apply, smul_eq_mul,
    reactionBilinearRawFun_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    mul_assoc, mul_left_comm _ c, ← Finset.mul_sum]
  ring

private theorem reactionBilinearFun_add_right (r s₁ s₂ : FourTensor V) :
    reactionBilinearFun r (s₁ + s₂) = reactionBilinearFun r s₁ + reactionBilinearFun r s₂ := by
  rw [reactionBilinearFun_comm, reactionBilinearFun_add_left,
    reactionBilinearFun_comm s₁, reactionBilinearFun_comm s₂]

private theorem reactionBilinearFun_smul_right (c : ℝ) (r s : FourTensor V) :
    reactionBilinearFun r (c • s) = c • reactionBilinearFun r s := by
  rw [reactionBilinearFun_comm, reactionBilinearFun_smul_left, reactionBilinearFun_comm]

private theorem norm_reactionBilinearFun_le (r s : FourTensor V) :
    ‖reactionBilinearFun r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  rw [reactionBilinearFun, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := norm_reactionBilinearRawFun_le r s
  have h2 := norm_reactionBilinearRawFun_le s r
  calc (1 / 2 : ℝ) * ‖reactionBilinearRawFun r s + reactionBilinearRawFun s r‖
      ≤ (1 / 2 : ℝ) * (‖reactionBilinearRawFun r s‖ + ‖reactionBilinearRawFun s r‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ +
          5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖s‖ * ‖r‖) := by gcongr
    _ = 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by ring

variable (V) in
/-- The symmetric continuous bilinear polarization of `reactionTensor`:
`reactionBilinear V r r = reactionTensor r` and
`reactionBilinear V r s = reactionBilinear V s r`. -/
def reactionBilinear : FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ reactionBilinearFun
      reactionBilinearFun_add_left
      reactionBilinearFun_smul_left
      reactionBilinearFun_add_right
      reactionBilinearFun_smul_right)
    (5 * (Module.finrank ℝ V : ℝ) ^ 2)
    norm_reactionBilinearFun_le

private theorem reactionBilinear_eq_fun (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinearFun r s := rfl

/-- `reactionBilinear V` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinear V s r :=
  reactionBilinearFun_comm r s

/-- Flipping the two arguments of `reactionBilinear V` leaves it unchanged. -/
@[simp]
theorem reactionBilinear_flip : (reactionBilinear V).flip = reactionBilinear V := by
  ext r s m; exact DFunLike.congr_fun (reactionBilinear_comm s r) m

/-- On the diagonal, `reactionBilinear V r r` is `reactionTensor r`. -/
@[simp]
theorem reactionBilinear_self (r : FourTensor V) :
    reactionBilinear V r r = reactionTensor r :=
  reactionBilinearFun_self r

/-- Contraction formula for `reactionBilinear V r s` in any orthonormal basis `b` of `V`. -/
theorem reactionBilinear_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinear V r s ![u, v, z, w] =
      (1 / 2 : ℝ) * ((∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
        (∑ p, ∑ q, s ![u, v, b p, b q] * r ![z, w, b p, b q])) +
      ((∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) +
        (∑ p, ∑ q, s ![u, b p, z, b q] * r ![v, b p, w, b q])) -
      ((∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) +
        (∑ p, ∑ q, s ![u, b p, w, b q] * r ![v, b p, z, b q])) := by
  simp only [reactionBilinear_eq_fun, reactionBilinearFun, smul_apply, add_apply,
    reactionBilinearRawFun_apply_orthonormalBasis b, smul_eq_mul]
  ring

/-- The reaction tensor of `0` is `0`. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  simp [← reactionBilinear_self]

/-- `reactionTensor` is even: `Q(-r) = Q(r)`. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  simp [← reactionBilinear_self]

/-- `reactionTensor` is homogeneous of degree two: `Q(c • r) = c ^ 2 • Q(r)`. -/
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = c ^ 2 • reactionTensor r := by
  simp [← reactionBilinear_self, sq, smul_smul]

/-- Binomial expansion of `reactionTensor` via `reactionBilinear V`. -/
theorem reactionTensor_add (r s : FourTensor V) :
    reactionTensor (r + s) =
      reactionTensor r + (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  simp only [← reactionBilinear_self, map_add, add_apply, reactionBilinear_comm s r, two_smul]
  abel

/-- Expansion of `reactionTensor (r - s)` via `reactionBilinear V`. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  simp only [← reactionBilinear_self, map_sub, sub_apply, reactionBilinear_comm s r, two_smul]
  abel

/-- Polarization identity recovering `reactionBilinear V` from `reactionTensor`. -/
theorem reactionBilinear_eq_sub (r s : FourTensor V) :
    reactionBilinear V r s = (1 / 4 : ℝ) • (reactionTensor (r + s) - reactionTensor (r - s)) := by
  rw [reactionTensor_add, reactionTensor_sub]
  ext m
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Difference-of-squares factorization `Q(r) - Q(s) = B(r + s, r - s)`. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilinear V (r + s) (r - s) := by
  simp only [← reactionBilinear_self, map_add, map_sub, add_apply, reactionBilinear_comm s r]
  abel

end Polarization

section NormAndRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Explicit dimensional operator-norm bound on `reactionBilinear V r s`. -/
theorem norm_reactionBilinear_apply_le (r s : FourTensor V) :
    ‖reactionBilinear V r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ :=
  norm_reactionBilinearFun_le r s

/-- Explicit dimensional operator-norm bound on `reactionBilinear V r`. -/
theorem norm_reactionBilinear_le (r : FourTensor V) :
    ‖reactionBilinear V r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_reactionBilinear_apply_le r)

/-- Explicit dimensional quadratic operator-norm bound on `reactionTensor r`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ ^ 2 := by
  simpa only [reactionBilinear_self, sq, mul_assoc] using norm_reactionBilinear_apply_le r r

/-- Explicit dimensional difference bound for `reactionTensor`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  rw [reactionTensor_sub_reactionTensor]
  calc ‖reactionBilinear V (r + s) (r - s)‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r + s‖ * ‖r - s‖ :=
        norm_reactionBilinear_apply_le (r + s) (r - s)
    _ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖ := by
        gcongr; exact norm_add_le r s

/-- On any set `s` of four-tensors bounded in norm by `R`, `reactionTensor` is Lipschitz with
explicit dimensional constant `10 * (finrank ℝ V) ^ 2 * R`. -/
theorem lipschitzOnWith_reactionTensor_of_norm_le {s : Set (FourTensor V)} {R : ℝ≥0}
    (hs : ∀ r ∈ s, ‖r‖ ≤ R) :
    LipschitzOnWith (10 * (Module.finrank ℝ V : ℝ≥0) ^ 2 * R)
      (reactionTensor (V := V)) s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro r hr q hq
  calc ‖reactionTensor r - reactionTensor q‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖q‖) * ‖r - q‖ :=
        norm_reactionTensor_sub_le r q
    _ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ((R : ℝ) + R) * ‖r - q‖ := by
        gcongr; exacts [hs r hr, hs q hq]
    _ = ((10 * (Module.finrank ℝ V : ℝ≥0) ^ 2 * R : ℝ≥0) : ℝ) * ‖r - q‖ := by
        push_cast; ring

/-- `reactionTensor` is Lipschitz on every closed ball `Metric.closedBall 0 R` with explicit
dimensional constant `10 * (finrank ℝ V) ^ 2 * R`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (R : ℝ≥0) :
    LipschitzOnWith (10 * (Module.finrank ℝ V : ℝ≥0) ^ 2 * R) (reactionTensor (V := V))
      (Metric.closedBall 0 R) :=
  lipschitzOnWith_reactionTensor_of_norm_le fun _ hr ↦ mem_closedBall_zero_iff.mp hr

/-- `reactionTensor` is Lipschitz on every bounded set of four-tensors. -/
theorem exists_lipschitzOnWith_reactionTensor_of_isBounded {s : Set (FourTensor V)}
    (hs : Bornology.IsBounded s) :
    ∃ K, LipschitzOnWith K (reactionTensor (V := V)) s := by
  obtain ⟨C, hC⟩ := hs.exists_pos_norm_le
  exact ⟨_, lipschitzOnWith_reactionTensor_of_norm_le (R := ⟨C, hC.1.le⟩) fun r hr ↦ hC.2 r hr⟩

/-- `reactionTensor` has strict Fréchet derivative `2 • reactionBilinear V r` at `r`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r := by
  have h := (reactionBilinear V).hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id r) (hasStrictFDerivAt_id r)
  have hder : (reactionBilinear V).precompR (FourTensor V) r (.id ℝ (FourTensor V)) +
      (reactionBilinear V).precompL (FourTensor V) (.id ℝ (FourTensor V)) r =
      (2 : ℝ) • reactionBilinear V r := by
    ext q m
    simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      reactionBilinear_comm q r, two_smul]
  simpa only [id, reactionBilinear_self, hder] using h

/-- `reactionTensor` has Fréchet derivative `2 • reactionBilinear V r` at `r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- `reactionTensor` is Fréchet differentiable everywhere. -/
theorem differentiable_reactionTensor : Differentiable ℝ (reactionTensor (V := V)) :=
  fun r ↦ (hasFDerivAt_reactionTensor r).differentiableAt

/-- The Fréchet derivative of `reactionTensor` at `r` is `2 • reactionBilinear V r`. -/
@[simp]
theorem fderiv_reactionTensor (r : FourTensor V) :
    fderiv ℝ (reactionTensor (V := V)) r = (2 : ℝ) • reactionBilinear V r :=
  (hasFDerivAt_reactionTensor r).fderiv

/-- `reactionTensor` is smooth (`C^n` for every `n`, in particular `C^∞`). -/
theorem contDiff_reactionTensor {n : WithTop ℕ∞} :
    ContDiff ℝ n (reactionTensor (V := V)) := by
  rw [show (reactionTensor (V := V)) = fun r ↦ reactionBilinear V r r from
    funext fun r ↦ (reactionBilinear_self r).symm]
  exact (reactionBilinear V).isBoundedBilinearMap.contDiff.comp₂ contDiff_id contDiff_id

/-- `reactionTensor` is continuous. -/
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := ⊤)).continuous

/-- `reactionTensor` is locally Lipschitz. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 1)).locallyLipschitz

end NormAndRegularity

section Equivariance

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private theorem reactionBilinearRawFun_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V →ₗᵢ[ℝ] W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (r s : FourTensor V) :
    reactionBilinearRawFun (r.compContinuousLinearMap fun _ ↦ f)
        (s.compContinuousLinearMap fun _ ↦ f) =
      (reactionBilinearRawFun r s).compContinuousLinearMap fun _ ↦ f := by
  let bW := stdOrthonormalBasis ℝ W
  let bV := stdOrthonormalBasis ℝ V
  ext m; rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm,
    compContinuousLinearMap_apply_vec, reactionBilinearRawFun_apply_orthonormalBasis bW,
    reactionBilinearRawFun_apply_orthonormalBasis bV]
  simp only [compContinuousLinearMap_apply_vec]
  have h1 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg
    (slice34 r (f (m 0)) (f (m 1))) (slice34 s (f (m 2)) (f (m 3)))
  have h2 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg
    (slice24 r (f (m 0)) (f (m 2))) (slice24 s (f (m 1)) (f (m 3)))
  have h3 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg
    (slice24 r (f (m 0)) (f (m 3))) (slice24 s (f (m 1)) (f (m 2)))
  simp only [Real.inner_apply, slice34, slice24, LinearMap.mk₂_apply] at h1 h2 h3
  rw [h1, h2, h3]

/-- Coisometric equivariance of `reactionBilinear`: if the adjoint of `f : W →L[ℝ] V` is a linear
isometry `g : V →ₗᵢ[ℝ] W`, pulling back four-tensors along `f` commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V →ₗᵢ[ℝ] W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (r s : FourTensor V) :
    reactionBilinear W (r.compContinuousLinearMap fun _ ↦ f)
        (s.compContinuousLinearMap fun _ ↦ f) =
      (reactionBilinear V r s).compContinuousLinearMap fun _ ↦ f := by
  ext m
  simp only [reactionBilinear_eq_fun, reactionBilinearFun, smul_apply, add_apply,
    reactionBilinearRawFun_compContinuousLinearMap_of_inner_eq hfg,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- Coisometric equivariance of `reactionTensor`: if the adjoint of `f : W →L[ℝ] V` is a linear
isometry `g : V →ₗᵢ[ℝ] W`, pulling back along `f` commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V →ₗᵢ[ℝ] W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ f) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ f := by
  simpa only [reactionBilinear_self] using
    reactionBilinear_compContinuousLinearMap_of_inner_eq hfg r r

/-- Orthogonal equivariance of `reactionBilinear` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`. -/
theorem reactionBilinear_compContinuousLinearMap_linearIsometryEquiv
    (e : W ≃ₗᵢ[ℝ] V) (r s : FourTensor V) :
    reactionBilinear W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilinear V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionBilinear_compContinuousLinearMap_of_inner_eq (g := e.symm.toLinearIsometry)
    (fun x y ↦ e.inner_map_eq_flip x y) r s

/-- Orthogonal equivariance of `reactionTensor` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`. -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    reactionTensor
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionTensor_compContinuousLinearMap_of_inner_eq (g := e.symm.toLinearIsometry)
    (fun x y ↦ e.inner_map_eq_flip x y) r

/-- Pulling back two four-tensors on a subspace `K ≤ V` along `K.orthogonalProjectionOnto`
(extending them by zero on `Kᗮ`) commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_orthogonalProjectionOnto
    (K : Submodule ℝ V) (r s : FourTensor K) :
    reactionBilinear V (r.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto)
        (s.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (reactionBilinear K r s).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto :=
  reactionBilinear_compContinuousLinearMap_of_inner_eq (g := K.subtypeₗᵢ)
    (fun x y ↦ K.inner_orthogonalProjectionOnto_eq_of_mem_right y x) r s

/-- Pulling back a four-tensor on a subspace `K ≤ V` along `K.orthogonalProjectionOnto`
(extending it by zero on `Kᗮ`) commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto
    (K : Submodule ℝ V) (r : FourTensor K) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto :=
  reactionTensor_compContinuousLinearMap_of_inner_eq (g := K.subtypeₗᵢ)
    (fun x y ↦ K.inner_orthogonalProjectionOnto_eq_of_mem_right y x) r

end Equivariance

section AlgebraicCurvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private def reactionS₁ (r : FourTensor V) (u v z w : V) : ℝ :=
  let b := stdOrthonormalBasis ℝ V
  ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]

private def reactionS₂ (r : FourTensor V) (u v z w : V) : ℝ :=
  let b := stdOrthonormalBasis ℝ V
  ∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]

private theorem reactionTensor_eq_S₁_S₂ (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      reactionS₁ r u v z w + 2 * reactionS₂ r u v z w - 2 * reactionS₂ r u v w z :=
  reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V) r u v z w

/-- Key Bianchi contraction identity behind the first Bianchi identity of `reactionTensor r`:
`2 (S₂(v, z, u, w) - S₂(z, u, w, v)) = -S₁(u, v, z, w)`. -/
private theorem two_mul_reactionS₂_sub_eq_neg_reactionS₁ {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v z w : V) :
    2 * (reactionS₂ r v z u w - reactionS₂ r z u w v) = -reactionS₁ r u v z w := by
  let b := stdOrthonormalBasis ℝ V
  have hdiff : reactionS₂ r v z u w - reactionS₂ r z u w v =
      -(∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) := by
    simp only [reactionS₂, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    have hcyc := hr.cyclic_eq_zero u v (b p) (b q)
    rw [hr.antisymm_first (b p) u v (b q)] at hcyc
    linear_combination hcyc * r ![z, b p, w, b q]
  have hskew : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) =
      ∑ p, ∑ q, r ![u, v, b p, b q] * r ![b p, w, z, b q] := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_last u v (b q) (b p), hr.swap_pairs z (b q) w (b p),
      hr.antisymm_first w (b p) z (b q)]
    ring
  have hsum : 2 * (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) = reactionS₁ r u v z w := by
    rw [two_mul]
    conv_lhs => rhs; rw [hskew]
    simp only [reactionS₁, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    have hcyc := hr.cyclic_eq_zero z (b p) w (b q)
    rw [hr.antisymm_first w z (b p) (b q)] at hcyc
    linear_combination r ![u, v, b p, b q] * hcyc
  rw [hdiff]
  linear_combination -hsum

/-- The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor:
`reactionTensor` preserves pair antisymmetry, pair interchange, and the first Bianchi identity. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.reactionTensor r) := by
  have hS₁_first (u v z w : V) : reactionS₁ r v u z w = -reactionS₁ r u v z w := by
    simp only [reactionS₁, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hr.antisymm_first v u]; ring
  have hS₁_last (u v z w : V) : reactionS₁ r u v w z = -reactionS₁ r u v z w := by
    simp only [reactionS₁, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hr.antisymm_first w z]; ring
  have hS₂_first (u v z w : V) : reactionS₂ r v u z w = reactionS₂ r u v w z :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
  have hS₁_swap (u v z w : V) : reactionS₁ r z w u v = reactionS₁ r u v z w :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
  have hS₂_swap (u v z w : V) : reactionS₂ r z w u v = reactionS₂ r u v z w := by
    simp only [reactionS₂]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by
      rw [hr.swap_pairs z _ u _, hr.swap_pairs w _ v _]
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [reactionTensor_eq_S₁_S₂]
  · rw [hS₁_first v u, hS₂_first v u z w, hS₂_first v u w z]; ring
  · rw [hS₁_last]; ring
  · rw [hS₁_swap u v z w, hS₂_swap u v z w, hS₂_swap v u z w, hS₂_first u v z w]
  · linear_combination two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr u v z w +
      two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr v z u w +
      two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr z u v w

/-- `reactionTensor` maps `algebraicCurvatureSubmodule V` into itself. -/
theorem reactionTensor_mem (r : FourTensor V) (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr (mem_algebraicCurvatureSubmodule.mp hr).reactionTensor

/-- `reactionTensor` maps the carrier of `algebraicCurvatureSubmodule V` to itself. -/
theorem mapsTo_reactionTensor_algebraicCurvatureSubmodule :
    Set.MapsTo (reactionTensor (V := V))
      (algebraicCurvatureSubmodule V) (algebraicCurvatureSubmodule V) :=
  fun r hr ↦ reactionTensor_mem r hr

/-- The symmetric bilinear polarization `reactionBilinear V` preserves algebraic curvature
tensors. -/
theorem IsAlgebraicCurvature.reactionBilinear {r s : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s) :
    IsAlgebraicCurvature (FourTensor.reactionBilinear V r s) := by
  rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
  rw [reactionBilinear_eq_sub]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (reactionTensor_mem _ (Submodule.add_mem _ hr hs))
    (reactionTensor_mem _ (Submodule.sub_mem _ hr hs)))

/-- `reactionBilinear V` maps pairs in `algebraicCurvatureSubmodule V` into
`algebraicCurvatureSubmodule V`. -/
theorem reactionBilinear_mem {r s : FourTensor V} (hr : r ∈ algebraicCurvatureSubmodule V)
    (hs : s ∈ algebraicCurvatureSubmodule V) :
    reactionBilinear V r s ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr <|
    (mem_algebraicCurvatureSubmodule.mp hr).reactionBilinear
      (mem_algebraicCurvatureSubmodule.mp hs)

end AlgebraicCurvature

section ContractionsAndExamples

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem sum_ricci_first_eq_two_mul_third {ι : Type*} [Fintype ι] {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (b : ι → V) (u v : V) :
    (∑ c, ∑ a, ∑ d, r ![b c, u, b a, b d] * r ![b c, v, b a, b d]) =
      2 * ∑ c, ∑ a, ∑ d, r ![b c, b a, v, b d] * r ![u, b a, b c, b d] := by
  set F₁ := ∑ c, ∑ a, ∑ d, r ![b c, u, b a, b d] * r ![b c, v, b a, b d]
  set F₃ := ∑ c, ∑ a, ∑ d, r ![b c, b a, v, b d] * r ![u, b a, b c, b d]
  let h (w : V) (x y z : ι) : ℝ := r ![b x, b y, b z, w]
  have hh_anti (w : V) (x y z : ι) : h w y x z = -h w x y z := hr.antisymm_first _ _ _ _
  have hh_bianchi (w : V) (x y z : ι) : h w x y z = -(h w y z x + h w z x y) := by
    linear_combination hr.cyclic_eq_zero (b x) (b y) (b z) w
  have hF₁ : F₁ = ∑ c, ∑ a, ∑ d, h u a d c * h v a d c :=
    Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun d _ ↦ by
        simp only [h]; rw [hr.swap_pairs (b c) u, hr.swap_pairs (b c) v]
  have hF₃ : F₃ = -∑ c, ∑ a, ∑ d, h u d c a * h v c a d := by
    simp only [F₃, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [h]
    rw [hr.antisymm_last (b c) (b a) v (b d), hr.swap_pairs u (b a) (b c) (b d),
      hr.antisymm_first (b c) (b d) u (b a), hr.antisymm_last (b d) (b c) u (b a)]
    ring
  have hA₁ : (∑ c, ∑ a, ∑ d, h u d c a * h v d c a) = F₁ := by
    rw [hF₁, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
  have hA₂ : (∑ c, ∑ a, ∑ d, h u c a d * h v c a d) = F₁ := by
    rw [hF₁]; conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm
  have hB : (∑ c, ∑ a, ∑ d, h u c a d * h v d c a) = ∑ c, ∑ a, ∑ d, h u d c a * h v c a d :=
    Finset.sum_congr rfl fun c _ ↦ by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
        rw [hh_anti u y c x, hh_anti v c x y]; ring
  have hprod : F₁ = ∑ c, ∑ a, ∑ d, ((h u d c a * h v d c a + h u c a d * h v c a d) +
      (h u d c a * h v c a d + h u c a d * h v d c a)) := by
    rw [hF₁]
    exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun d _ ↦ by rw [hh_bianchi u a d c, hh_bianchi v a d c]; ring
  simp only [Finset.sum_add_distrib, hA₁, hA₂, hB] at hprod
  linear_combination -(hprod + 2 * hF₃)

variable [FiniteDimensional ℝ V]

/-- For an algebraic curvature tensor `r`, first Bianchi cancellation reduces the Ricci contraction
of `reactionTensor r` in any orthonormal basis `b` to
`Ric(Q(r))(u, v) = 2 ∑_pq Ric(r)(b p, b q) r(b p, u, b q, v)`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) (u v : V) :
    ricci (FourTensor.reactionTensor r) u v =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * r ![b p, u, b q, v] := by
  rw [ricci_apply_orthonormalBasis b]
  simp_rw [reactionTensor_apply_orthonormalBasis b, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hF₂ : (∑ c, ∑ p, ∑ q, r ![b c, b p, b c, b q] * r ![u, b p, v, b q]) =
      ∑ p, ∑ q, ricci r (b p) (b q) * r ![b p, u, b q, v] := by
    simp only [ricci_apply_orthonormalBasis b]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [hr.antisymm_first u (b p), hr.antisymm_last (b p) u v (b q), neg_neg]
  linear_combination sum_ricci_first_eq_two_mul_third hr b u v + 2 * hF₂

/-- If an algebraic curvature tensor `r` is Ricci-flat (`ricci r = 0`), then `reactionTensor r` is
also Ricci-flat. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor_eq_zero_of_ricci_eq_zero {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hric : ricci r = 0) :
    ricci (FourTensor.reactionTensor r) = 0 := by
  ext u v
  simp [hr.ricci_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V), hric]

/-- If an algebraic curvature tensor `r` is Einstein with constant `c` (`ricci r = c • innerₗ V`),
then `reactionTensor r` is Einstein with constant `2 * c ^ 2`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor_of_ricci_eq_smul_inner {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {c : ℝ} (hric : ricci r = c • innerₗ V) :
    ricci (FourTensor.reactionTensor r) = (2 * c ^ 2) • innerₗ V := by
  classical
  let b := stdOrthonormalBasis ℝ V
  ext u v
  rw [hr.ricci_reactionTensor_apply_orthonormalBasis b]
  have hdiag (p : Fin (Module.finrank ℝ V)) :
      (∑ q, ricci r (b p) (b q) * r ![b p, u, b q, v]) = c * r ![b p, u, b p, v] := by
    simp_rw [hric, LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
      orthonormal_iff_ite.mp b.orthonormal]
    simp
  simp_rw [hdiag, ← Finset.mul_sum, ← ricci_apply_orthonormalBasis b, hric,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  ring

/-- For an algebraic curvature tensor `r`, the scalar contraction of `reactionTensor r` is twice
the squared Hilbert-Schmidt norm of `ricci r` in any orthonormal basis `b`:
`Scal(Q(r)) = 2 ∑_pq Ric(r)(b p, b q) ^ 2`. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_eq_sum {ι : Type*} [Fintype ι]
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) :
    scalar (FourTensor.reactionTensor r) = 2 * ∑ p, ∑ q, ricci r (b p) (b q) ^ 2 := by
  rw [scalar_apply, bilinFormTrace_eq_sum _ b]
  simp_rw [hr.ricci_reactionTensor_apply_orthonormalBasis b, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← Finset.mul_sum, sq, ricci_apply_orthonormalBasis b]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [hr.antisymm_first (b p) (b j), hr.antisymm_last (b j) (b p) (b q) (b j), neg_neg]

/-- For an algebraic curvature tensor `r`, the scalar contraction of `reactionTensor r` is
nonnegative. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_nonneg {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : 0 ≤ scalar (FourTensor.reactionTensor r) := by
  rw [hr.scalar_reactionTensor_eq_sum (stdOrthonormalBasis ℝ V)]; positivity

/-- For an algebraic curvature tensor `r`, `scalar (reactionTensor r) = 0` if and only if `r` is
Ricci-flat (`ricci r = 0`). -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_eq_zero_iff {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : scalar (FourTensor.reactionTensor r) = 0 ↔ ricci r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [hr.scalar_reactionTensor_eq_sum b]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hsum : (∑ p, ∑ q, ricci r (b p) (b q) ^ 2) = 0 := by linarith
  have hpq (p q : Fin (Module.finrank ℝ V)) : ricci r (b p) (b q) = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ sq_nonneg (ricci r (b i) (b j))).mp hsum p (Finset.mem_univ p)
    exact sq_eq_zero_iff.mp <| (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      sq_nonneg (ricci r (b p) (b j))).mp hp q (Finset.mem_univ q)
  ext u v
  rw [← b.sum_repr' u, ← b.sum_repr' v]
  simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hpq]

private theorem sum_constantCurvature_mul_constantCurvature_24 (u v z w : V) :
    (∑ p, ∑ q,
        constantCurvature V ![u, stdOrthonormalBasis ℝ V p, z, stdOrthonormalBasis ℝ V q] *
          constantCurvature V ![v, stdOrthonormalBasis ℝ V p, w, stdOrthonormalBasis ℝ V q]) =
      ((Module.finrank ℝ V : ℝ) - 2) * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ) + ⟪u, v⟫_ℝ * ⟪z, w⟫_ℝ := by
  classical
  set b := stdOrthonormalBasis ℝ V
  have hq (p : Fin (Module.finrank ℝ V)) :
      (∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q]) =
        ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, z⟫_ℝ * (⟪v, b p⟫_ℝ * ⟪b p, w⟫_ℝ) -
          ⟪v, w⟫_ℝ * (⟪u, b p⟫_ℝ * ⟪b p, z⟫_ℝ) + (⟪z, b p⟫_ℝ * ⟪b p, w⟫_ℝ) * ⟪u, v⟫_ℝ := by
    simp only [constantCurvature_apply]
    have hring (q : Fin (Module.finrank ℝ V)) :
        (⟪u, z⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪b p, z⟫_ℝ) *
            (⟪v, w⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪v, b q⟫_ℝ * ⟪b p, w⟫_ℝ) =
          ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ * (⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
            ⟪u, z⟫_ℝ * ⟪b p, w⟫_ℝ * (⟪v, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
            ⟪v, w⟫_ℝ * ⟪b p, z⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) +
            ⟪z, b p⟫_ℝ * ⟪b p, w⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪b q, v⟫_ℝ) := by
      rw [real_inner_comm (b q) v, real_inner_comm z (b p)]; ring
    simp_rw [hring, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      b.sum_inner_mul_inner u v, orthonormal_iff_ite.mp b.orthonormal]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, b.sum_inner_mul_inner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- On the constant-curvature tensor of curvature `1` on an `n`-dimensional space `V`,
`reactionTensor` acts with eigenvalue `2 (n - 1)`. -/
@[simp]
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  let b := stdOrthonormalBasis ℝ V
  ext m
  rw [show m = ![m 0, m 1, m 2, m 3] from (FinVec.etaExpand_eq m).symm,
    reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul, constantCurvature_apply]
  have hS₁ : (∑ p, ∑ q, constantCurvature V ![m 0, m 1, b p, b q] *
      constantCurvature V ![m 2, m 3, b p, b q]) =
        2 * (⟪m 0, m 2⟫_ℝ * ⟪m 1, m 3⟫_ℝ - ⟪m 0, m 3⟫_ℝ * ⟪m 1, m 2⟫_ℝ) := by
    simp only [constantCurvature_apply]
    have hring (p q : Fin (Module.finrank ℝ V)) :
        (⟪m 0, b p⟫_ℝ * ⟪m 1, b q⟫_ℝ - ⟪m 0, b q⟫_ℝ * ⟪m 1, b p⟫_ℝ) *
            (⟪m 2, b p⟫_ℝ * ⟪m 3, b q⟫_ℝ - ⟪m 2, b q⟫_ℝ * ⟪m 3, b p⟫_ℝ) =
          (⟪m 0, b p⟫_ℝ * ⟪b p, m 2⟫_ℝ) * (⟪m 1, b q⟫_ℝ * ⟪b q, m 3⟫_ℝ) -
            (⟪m 0, b p⟫_ℝ * ⟪b p, m 3⟫_ℝ) * (⟪m 1, b q⟫_ℝ * ⟪b q, m 2⟫_ℝ) -
            (⟪m 1, b p⟫_ℝ * ⟪b p, m 2⟫_ℝ) * (⟪m 0, b q⟫_ℝ * ⟪b q, m 3⟫_ℝ) +
            (⟪m 1, b p⟫_ℝ * ⟪b p, m 3⟫_ℝ) * (⟪m 0, b q⟫_ℝ * ⟪b q, m 2⟫_ℝ) := by
      simp only [real_inner_comm (b p), real_inner_comm (b q)]; ring
    simp_rw [hring, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      b.sum_inner_mul_inner, ← Finset.sum_mul, b.sum_inner_mul_inner]
    ring
  rw [hS₁, sum_constantCurvature_mul_constantCurvature_24 (m 0) (m 1) (m 2) (m 3),
    sum_constantCurvature_mul_constantCurvature_24 (m 0) (m 1) (m 3) (m 2),
    real_inner_comm (m 2) (m 3)]
  ring

/-- On the constant-curvature tensor of sectional curvature `κ`, `reactionTensor` gives
`2 (n - 1) κ ^ 2 • constantCurvature V`. -/
theorem reactionTensor_smul_constantCurvature (κ : ℝ) :
    reactionTensor (κ • constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1) * κ ^ 2) • constantCurvature V := by
  rw [reactionTensor_smul, reactionTensor_constantCurvature, smul_smul]; congr 1; ring

/-- On the curvature four-tensor of `S^k × ℝ^(n - k)` obtained by pulling back `constantCurvature K`
along the orthogonal projection onto a subspace `K ≤ V` of dimension `k`, `reactionTensor` acts with
eigenvalue `2 (k - 1)`. -/
theorem reactionTensor_constantCurvature_comp_orthogonalProjectionOnto (K : Submodule ℝ V) :
    reactionTensor
        ((constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (2 * ((Module.finrank ℝ K : ℝ) - 1)) •
        (constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto := by
  rw [reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto,
    reactionTensor_constantCurvature]
  ext m; simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- On the rank-one curvature four-tensor of `S² × ℝ^(n - 2)` associated with a two-dimensional
subspace `K ≤ V`, `reactionTensor` acts with eigenvalue `2`. -/
theorem reactionTensor_constantCurvature_comp_orthogonalProjectionOnto_of_finrank_eq_two
    {K : Submodule ℝ V} (hK : Module.finrank ℝ K = 2) :
    reactionTensor
        ((constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (2 : ℝ) •
        (constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto := by
  rw [reactionTensor_constantCurvature_comp_orthogonalProjectionOnto, hK]; norm_num

end ContractionsAndExamples

end FourTensor

end TauCeti
