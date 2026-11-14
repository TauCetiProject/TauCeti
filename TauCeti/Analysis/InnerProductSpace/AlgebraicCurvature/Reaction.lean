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

* `TauCeti.FourTensor.coordFourTensor`: the rank-one four-tensor
  `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫`.
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

private theorem abs_sum_sum_le_card_sq_mul {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) {M : ℝ}
    (hf : ∀ p q, |f p q| ≤ M) :
    |∑ p, ∑ q, f p q| ≤ (Fintype.card ι : ℝ) ^ 2 * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((Fintype.card ι : ℝ) * M) fun p _ ↦ ?_).trans_eq
    (by simp [sq]; ring)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_card_nsmul _ _ M fun q _ ↦ hf p q).trans_eq (by simp))

section CoordFourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The rank-one four-tensor `(u, v, z, w) ↦ ⟪b i, u⟫ ⟪b j, v⟫ ⟪b k, z⟫ ⟪b l, w⟫` attached to four
vectors of a family `b`. -/
def coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) : FourTensor V :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4 ℝ).compContinuousLinearMap
    ![innerSL ℝ (b i), innerSL ℝ (b j), innerSL ℝ (b k), innerSL ℝ (b l)]

/-- Evaluation of `coordFourTensor` on four vectors. -/
@[simp]
theorem coordFourTensor_apply {ι : Type*} (b : ι → V) (i j k l : ι) (u v z w : V) :
    coordFourTensor b i j k l ![u, v, z, w] =
      ⟪b i, u⟫_ℝ * ⟪b j, v⟫_ℝ * ⟪b k, z⟫_ℝ * ⟪b l, w⟫_ℝ := by
  simp [coordFourTensor, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

/-- The operator norm of `coordFourTensor b i j k l` is `‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖`. -/
@[simp]
theorem norm_coordFourTensor {ι : Type*} (b : ι → V) (i j k l : ι) :
    ‖coordFourTensor b i j k l‖ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ := by
  apply le_antisymm
  · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
    have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
    rw [hm, coordFourTensor_apply, Fin.prod_univ_four]
    simp only [Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue, abs_mul]
    have h0 := abs_real_inner_le_norm (b i) (m 0)
    have h1 := abs_real_inner_le_norm (b j) (m 1)
    have h2 := abs_real_inner_le_norm (b k) (m 2)
    have h3 := abs_real_inner_le_norm (b l) (m 3)
    calc |⟪b i, m 0⟫_ℝ| * |⟪b j, m 1⟫_ℝ| * |⟪b k, m 2⟫_ℝ| * |⟪b l, m 3⟫_ℝ|
        ≤ (‖b i‖ * ‖m 0‖) * (‖b j‖ * ‖m 1‖) * (‖b k‖ * ‖m 2‖) * (‖b l‖ * ‖m 3‖) := by gcongr
      _ = ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by ring
  · set P := ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖
    by_cases hP : P = 0
    · rw [hP]; exact norm_nonneg _
    · have hPpos : 0 < P := lt_of_le_of_ne (by positivity) (Ne.symm hP)
      have hle := (coordFourTensor b i j k l).le_opNorm ![b i, b j, b k, b l]
      rw [coordFourTensor_apply, Fin.prod_univ_four] at hle
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] at hle
      have hsq : |‖b i‖ ^ 2 * ‖b j‖ ^ 2 * ‖b k‖ ^ 2 * ‖b l‖ ^ 2| = P * P := by
        rw [abs_of_nonneg (by positivity)]; simp only [P]; ring
      rw [hsq] at hle
      exact le_of_mul_le_mul_right hle hPpos

/-- Every coordinate four-tensor of an orthonormal family has unit operator norm. -/
theorem norm_coordFourTensor_of_orthonormal {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (i j k l : ι) : ‖coordFourTensor b i j k l‖ = 1 := by
  simp [hb.1]

/-- Pulling back `coordFourTensor (f ∘ b)` along a linear isometry `f` gives `coordFourTensor b`. -/
@[simp]
theorem coordFourTensor_compContinuousLinearMap_linearIsometry {ι : Type*} (f : W →ₗᵢ[ℝ] V)
    (b : ι → W) (i j k l : ι) :
    (coordFourTensor (f ∘ b) i j k l).compContinuousLinearMap
      (fun _ ↦ f.toContinuousLinearMap) = coordFourTensor b i j k l := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, compContinuousLinearMap_apply_vec]
  simp

private theorem sum_inner_mul_apply_first {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v z w : V) :
    ∑ i, ⟪b i, u⟫_ℝ * r ![b i, v, z, w] = r ![u, v, z, w] := by
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ r ![x, v, z, w]
      map_add' := fun _ _ ↦ apply_add_first ..
      map_smul' := fun _ _ ↦ apply_smul_first .. }
  simpa [φ] using congrArg φ (b.sum_repr' u)

private theorem sum_inner_mul_apply_second {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v z w : V) :
    ∑ j, ⟪b j, v⟫_ℝ * r ![u, b j, z, w] = r ![u, v, z, w] := by
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ r ![u, x, z, w]
      map_add' := fun _ _ ↦ apply_add_second ..
      map_smul' := fun _ _ ↦ apply_smul_second .. }
  simpa [φ] using congrArg φ (b.sum_repr' v)

private theorem sum_inner_mul_apply_third {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v z w : V) :
    ∑ k, ⟪b k, z⟫_ℝ * r ![u, v, b k, w] = r ![u, v, z, w] := by
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ r ![u, v, x, w]
      map_add' := fun _ _ ↦ apply_add_third ..
      map_smul' := fun _ _ ↦ apply_smul_third .. }
  simpa [φ] using congrArg φ (b.sum_repr' z)

private theorem sum_inner_mul_apply_fourth {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (u v z w : V) :
    ∑ l, ⟪b l, w⟫_ℝ * r ![u, v, z, b l] = r ![u, v, z, w] := by
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ r ![u, v, z, x]
      map_add' := fun _ _ ↦ apply_add_fourth ..
      map_smul' := fun _ _ ↦ apply_smul_fourth .. }
  simpa [φ] using congrArg φ (b.sum_repr' w)

private theorem abs_apply_basis_le_34 {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (r : FourTensor V) (u v : V) (p q : ι) :
    |r ![u, v, b p, b q]| ≤ ‖r‖ * ‖u‖ * ‖v‖ := by
  have h := r.le_opNorm ![u, v, b p, b q]
  rw [Fin.prod_univ_four] at h
  simpa only [Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, hb.1 p, hb.1 q, mul_one, mul_assoc] using h

private theorem abs_apply_basis_le_24 {ι : Type*} {b : ι → V} (hb : Orthonormal ℝ b)
    (r : FourTensor V) (u z : V) (p q : ι) :
    |r ![u, b p, z, b q]| ≤ ‖r‖ * ‖u‖ * ‖z‖ := by
  have h := r.le_opNorm ![u, b p, z, b q]
  rw [Fin.prod_univ_four] at h
  simpa only [Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, hb.1 p, hb.1 q, one_mul, mul_one, mul_assoc] using h

/-- Every four-tensor on `V` is the sum of its components in an orthonormal basis `b` against the
corresponding coordinate four-tensors `coordFourTensor b i j k l`. -/
theorem sum_coordFourTensor_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) :
    (∑ i, ∑ j, ∑ k, ∑ l, r ![b i, b j, b k, b l] • coordFourTensor b i j k l) = r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm]
  simp only [sum_apply, smul_apply, coordFourTensor_apply, smul_eq_mul]
  have h4 (i j k : ι) :
      ∑ l, r ![b i, b j, b k, b l] *
          (⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * ⟪b k, m 2⟫_ℝ * ⟪b l, m 3⟫_ℝ) =
        ⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * ⟪b k, m 2⟫_ℝ * r ![b i, b j, b k, m 3] := by
    rw [← sum_inner_mul_apply_fourth b r (b i) (b j) (b k) (m 3), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have h3 (i j : ι) :
      ∑ k, ⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * ⟪b k, m 2⟫_ℝ * r ![b i, b j, b k, m 3] =
        ⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * r ![b i, b j, m 2, m 3] := by
    rw [← sum_inner_mul_apply_third b r (b i) (b j) (m 2) (m 3), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have h2 (i : ι) :
      ∑ j, ⟪b i, m 0⟫_ℝ * ⟪b j, m 1⟫_ℝ * r ![b i, b j, m 2, m 3] =
        ⟪b i, m 0⟫_ℝ * r ![b i, m 1, m 2, m 3] := by
    rw [← sum_inner_mul_apply_second b r (b i) (m 1) (m 2) (m 3), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [h4, h3, h2, sum_inner_mul_apply_first]

/-- Parseval contraction along a linear map `f : V →ₗ[ℝ] W` whose adjoint is a linear isometry
`g : W →ₗᵢ[ℝ] V`. -/
private theorem sum_mul_comp_eq_of_inner_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bV : OrthonormalBasis ι ℝ V) (bW : OrthonormalBasis κ ℝ W)
    {f : V →ₗ[ℝ] W} {g : W →ₗᵢ[ℝ] V} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (φ ψ : W →ₗ[ℝ] ℝ) :
    ∑ p, φ (f (bV p)) * ψ (f (bV p)) = ∑ a, φ (bW a) * ψ (bW a) := by
  classical
  have hexp (h : W →ₗ[ℝ] ℝ) (p : ι) :
      h (f (bV p)) = ∑ a, ⟪bV p, g (bW a)⟫_ℝ * h (bW a) := by
    conv_lhs => rw [← bW.sum_repr' (f (bV p)), map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, real_inner_comm (f (bV p)) (bW a), hfg]
  simp_rw [hexp φ, hexp ψ, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  have hsum : ∀ c,
      (∑ p, ⟪bV p, g (bW a)⟫_ℝ * φ (bW a) * (⟪bV p, g (bW c)⟫_ℝ * ψ (bW c))) =
        φ (bW a) * ψ (bW c) * ⟪bW a, bW c⟫_ℝ := by
    intro c
    have hp : (∑ p, ⟪g (bW a), bV p⟫_ℝ * ⟪bV p, g (bW c)⟫_ℝ) = ⟪bW a, bW c⟫_ℝ := by
      rw [bV.sum_inner_mul_inner, g.inner_map_map]
    calc (∑ p, ⟪bV p, g (bW a)⟫_ℝ * φ (bW a) * (⟪bV p, g (bW c)⟫_ℝ * ψ (bW c)))
        = φ (bW a) * ψ (bW c) * ∑ p, ⟪g (bW a), bV p⟫_ℝ * ⟪bV p, g (bW c)⟫_ℝ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [real_inner_comm (g (bW a)) (bV p)]; ring
      _ = φ (bW a) * ψ (bW c) * ⟪bW a, bW c⟫_ℝ := by rw [hp]
  simp_rw [hsum, orthonormal_iff_ite.mp bW.orthonormal]
  simp

/-- Double Parseval contraction of two bilinear forms along a map `f : V →ₗ[ℝ] W` whose adjoint is
a linear isometry `g : W →ₗᵢ[ℝ] V`. -/
private theorem sum_sum_mul_comp_eq_of_inner_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bV : OrthonormalBasis ι ℝ V) (bW : OrthonormalBasis κ ℝ W)
    {f : V →ₗ[ℝ] W} {g : W →ₗᵢ[ℝ] V} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (M N : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) :
    (∑ p, ∑ q, M (f (bV p)) (f (bV q)) * N (f (bV p)) (f (bV q))) =
      ∑ a, ∑ c, M (bW a) (bW c) * N (bW a) (bW c) := by
  have hinner (p : ι) :
      (∑ q, M (f (bV p)) (f (bV q)) * N (f (bV p)) (f (bV q))) =
        ∑ c, M (f (bV p)) (bW c) * N (f (bV p)) (bW c) :=
    sum_mul_comp_eq_of_inner_eq bV bW hfg (M (f (bV p))) (N (f (bV p)))
  simp_rw [hinner]
  rw [Finset.sum_comm]
  have houter (c : κ) :
      (∑ p, M (f (bV p)) (bW c) * N (f (bV p)) (bW c)) =
        ∑ a, M (bW a) (bW c) * N (bW a) (bW c) :=
    sum_mul_comp_eq_of_inner_eq bV bW hfg (M.flip (bW c)) (N.flip (bW c))
  simp_rw [houter]
  exact Finset.sum_comm

private def slice34 (r : FourTensor W) (u v : W) : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, v, x, y])
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

private def slice24 (r : FourTensor W) (u z : W) : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![u, x, z, y])
    (fun _ _ _ ↦ apply_add_second ..) (fun _ _ _ ↦ apply_smul_second ..)
    (fun _ _ _ ↦ apply_add_fourth ..) (fun _ _ _ ↦ apply_smul_fourth ..)

end CoordFourTensor

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
  have hid : ∀ x y : V,
      ⟪(LinearMap.id : V →ₗ[ℝ] V) x, y⟫_ℝ = ⟪x, (LinearIsometry.id : V →ₗᵢ[ℝ] V) y⟫_ℝ :=
    fun _ _ ↦ rfl
  have h1 := sum_sum_mul_comp_eq_of_inner_eq b₀ b hid (slice34 r u v) (slice34 s z w)
  have h2 := sum_sum_mul_comp_eq_of_inner_eq b₀ b hid (slice24 r u z) (slice24 s v w)
  have h3 := sum_sum_mul_comp_eq_of_inner_eq b₀ b hid (slice24 r u w) (slice24 s v z)
  simp only [slice34, slice24, LinearMap.mk₂_apply, LinearMap.id_apply] at h1 h2 h3
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
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, reactionBilinearRawFun_apply_orthonormalBasis b, Fin.prod_univ_four]
  simp only [Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue]
  set M := ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have hsum1 : |∑ p, ∑ q, r ![m 0, m 1, b p, b q] * s ![m 2, m 3, b p, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    refine (abs_sum_sum_le_card_sq_mul _ (M := M) fun p q ↦ ?_).trans_eq (by simp)
    rw [abs_mul]
    calc |r ![m 0, m 1, b p, b q]| * |s ![m 2, m 3, b p, b q]|
        ≤ (‖r‖ * ‖m 0‖ * ‖m 1‖) * (‖s‖ * ‖m 2‖ * ‖m 3‖) := by
          gcongr
          · exact abs_apply_basis_le_34 hb r (m 0) (m 1) p q
          · exact abs_apply_basis_le_34 hb s (m 2) (m 3) p q
      _ = M := by simp only [M]; ring
  have hsum23 (u₁ u₂ : V) (hu : ‖u₁‖ * ‖u₂‖ = ‖m 2‖ * ‖m 3‖) :
      |∑ p, ∑ q, r ![m 0, b p, u₁, b q] * s ![m 1, b p, u₂, b q]| ≤
        (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    refine (abs_sum_sum_le_card_sq_mul _ (M := M) fun p q ↦ ?_).trans_eq (by simp)
    rw [abs_mul]
    calc |r ![m 0, b p, u₁, b q]| * |s ![m 1, b p, u₂, b q]|
        ≤ (‖r‖ * ‖m 0‖ * ‖u₁‖) * (‖s‖ * ‖m 1‖ * ‖u₂‖) := by
          gcongr
          · exact abs_apply_basis_le_24 hb r (m 0) u₁ p q
          · exact abs_apply_basis_le_24 hb s (m 1) u₂ p q
      _ = ‖r‖ * ‖s‖ * (‖m 0‖ * ‖m 1‖ * (‖u₁‖ * ‖u₂‖)) := by ring
      _ = M := by rw [hu]; simp only [M]; ring
  have hsum2 := hsum23 (m 2) (m 3) rfl
  have hsum3 := hsum23 (m 3) (m 2) (mul_comm _ _)
  have habs : ∀ a b c : ℝ, |a + 2 * b - 2 * c| ≤ |a| + 2 * |b| + 2 * |c| := fun a b c ↦ by
    calc |a + 2 * b - 2 * c| ≤ |a + 2 * b| + |2 * c| := abs_sub _ _
      _ ≤ |a| + |2 * b| + |2 * c| := by gcongr; exact abs_add_le _ _
      _ = |a| + 2 * |b| + 2 * |c| := by simp [abs_mul]
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
  simp only [reactionBilinearFun]
  -- `reactionBilinearRawFun r r` is definitionally `reactionTensor r`.
  change (1 / 2 : ℝ) • (reactionTensor r + reactionTensor r) = reactionTensor r
  rw [← two_smul ℝ (reactionTensor r), smul_smul]
  norm_num

private theorem reactionBilinearFun_add_left (r₁ r₂ s : FourTensor V) :
    reactionBilinearFun (r₁ + r₂) s = reactionBilinearFun r₁ s + reactionBilinearFun r₂ s := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm]
  simp only [reactionBilinearFun, smul_apply, add_apply, smul_eq_mul,
    reactionBilinearRawFun_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem reactionBilinearFun_smul_left (c : ℝ) (r s : FourTensor V) :
    reactionBilinearFun (c • r) s = c • reactionBilinearFun r s := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm]
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
  simp only [reactionBilinearFun]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
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
    reactionBilinear V r s = reactionBilinearFun r s :=
  (rfl)

/-- `reactionBilinear V` is symmetric in its two four-tensor arguments. -/
theorem reactionBilinear_comm (r s : FourTensor V) :
    reactionBilinear V r s = reactionBilinear V s r :=
  reactionBilinearFun_comm r s

/-- Flipping the two arguments of `reactionBilinear V` leaves it unchanged. -/
@[simp]
theorem reactionBilinear_flip : (reactionBilinear V).flip = reactionBilinear V := by
  ext r s m
  exact DFunLike.congr_fun (reactionBilinear_comm s r) m

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
  simp only [← reactionBilinear_self, map_add, add_apply, reactionBilinear_comm s r]
  rw [two_smul]
  abel

/-- Expansion of `reactionTensor (r - s)` via `reactionBilinear V`. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilinear V r s + reactionTensor s := by
  simp only [← reactionBilinear_self, map_sub, sub_apply, reactionBilinear_comm s r]
  rw [two_smul]
  abel

/-- Polarization identity recovering `reactionBilinear V` from `reactionTensor`. -/
theorem reactionBilinear_eq_sub (r s : FourTensor V) :
    reactionBilinear V r s = (1 / 4 : ℝ) • (reactionTensor (r + s) - reactionTensor (r - s)) := by
  rw [reactionTensor_add, reactionTensor_sub]
  have h : reactionTensor r + (2 : ℝ) • reactionBilinear V r s + reactionTensor s -
      (reactionTensor r - (2 : ℝ) • reactionBilinear V r s + reactionTensor s) =
      (4 : ℝ) • reactionBilinear V r s := by
    ext m
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [h, smul_smul]
  norm_num

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
        gcongr
        · exact hs r hr
        · exact hs q hq
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
  dsimp only [id] at h
  have hfun : (fun y : FourTensor V ↦ reactionBilinear V y y) = reactionTensor :=
    funext reactionBilinear_self
  have hder : (reactionBilinear V).precompR (FourTensor V) r (.id ℝ (FourTensor V)) +
      (reactionBilinear V).precompL (FourTensor V) (.id ℝ (FourTensor V)) r =
      (2 : ℝ) • reactionBilinear V r := by
    ext q m
    simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      reactionBilinear_comm q r, two_smul]
  rwa [hfun, hder] at h

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
  have h : (reactionTensor (V := V)) = fun r ↦ reactionBilinear V r r :=
    funext fun r ↦ (reactionBilinear_self r).symm
  rw [h]
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
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, compContinuousLinearMap_apply_vec,
    reactionBilinearRawFun_apply_orthonormalBasis bW,
    reactionBilinearRawFun_apply_orthonormalBasis bV]
  simp only [compContinuousLinearMap_apply_vec]
  have h1 := sum_sum_mul_comp_eq_of_inner_eq bW bV (f := f.toLinearMap) hfg
    (slice34 r (f (m 0)) (f (m 1))) (slice34 s (f (m 2)) (f (m 3)))
  have h2 := sum_sum_mul_comp_eq_of_inner_eq bW bV (f := f.toLinearMap) hfg
    (slice24 r (f (m 0)) (f (m 2))) (slice24 s (f (m 1)) (f (m 3)))
  have h3 := sum_sum_mul_comp_eq_of_inner_eq bW bV (f := f.toLinearMap) hfg
    (slice24 r (f (m 0)) (f (m 3))) (slice24 s (f (m 1)) (f (m 2)))
  simp only [slice34, slice24, LinearMap.mk₂_apply, ContinuousLinearMap.coe_coe] at h1 h2 h3
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
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, compContinuousLinearMap_apply_vec]
  simp only [reactionBilinear_eq_fun, reactionBilinearFun, smul_apply, add_apply,
    reactionBilinearRawFun_compContinuousLinearMap_of_inner_eq hfg,
    compContinuousLinearMap_apply_vec]

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
  have hdiff :
      reactionS₂ r v z u w - reactionS₂ r z u w v =
        -(∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) := by
    simp only [reactionS₂, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    have hcyc := hr.cyclic_eq_zero u v (b p) (b q)
    rw [hr.antisymm_first (b p) u v (b q)] at hcyc
    linear_combination hcyc * r ![z, b p, w, b q]
  have hskew :
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) =
        ∑ p, ∑ q, r ![u, v, b p, b q] * r ![b p, w, z, b q] := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_last u v (b q) (b p), hr.swap_pairs z (b q) w (b p),
      hr.antisymm_first w (b p) z (b q)]
    ring
  have hsum :
      2 * (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) = reactionS₁ r u v z w := by
    have htwo :
        2 * (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) =
          (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) +
            ∑ p, ∑ q, r ![u, v, b p, b q] * r ![b p, w, z, b q] := by
      rw [← hskew]; ring
    rw [htwo, ← Finset.sum_add_distrib]
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
  · have h1 := two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr u v z w
    have h2 := two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr v z u w
    have h3 := two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr z u v w
    linear_combination h1 + h2 + h3

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
  rw [← mem_algebraicCurvatureSubmodule, reactionBilinear_eq_sub]
  have hr' : r ∈ algebraicCurvatureSubmodule V := mem_algebraicCurvatureSubmodule.mpr hr
  have hs' : s ∈ algebraicCurvatureSubmodule V := mem_algebraicCurvatureSubmodule.mpr hs
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (reactionTensor_mem _ (Submodule.add_mem _ hr' hs'))
    (reactionTensor_mem _ (Submodule.sub_mem _ hr' hs')))

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
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_comm]
  have hA₂ : (∑ c, ∑ a, ∑ d, h u c a d * h v c a d) = F₁ := by
    rw [hF₁]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm
  have hB : (∑ c, ∑ a, ∑ d, h u c a d * h v d c a) = ∑ c, ∑ a, ∑ d, h u d c a * h v c a d :=
    Finset.sum_congr rfl fun c _ ↦ by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
        rw [hh_anti u y c x, hh_anti v c x y]; ring
  have hprod :
      F₁ =
        ∑ c, ∑ a, ∑ d,
          ((h u d c a * h v d c a + h u c a d * h v c a d) +
            (h u d c a * h v c a d + h u c a d * h v d c a)) := by
    rw [hF₁]
    exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun d _ ↦ by
        rw [hh_bianchi u a d c, hh_bianchi v a d c]
        ring
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
  have hF₂ :
      (∑ c, ∑ p, ∑ q, r ![b c, b p, b c, b q] * r ![u, b p, v, b q]) =
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
  rw [hr.ricci_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V), hric]
  simp

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
  rw [← Finset.mul_sum, sq]
  congr 1
  rw [ricci_apply_orthonormalBasis b]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [hr.antisymm_first (b p) (b j), hr.antisymm_last (b j) (b p) (b q) (b j), neg_neg]

/-- For an algebraic curvature tensor `r`, the scalar contraction of `reactionTensor r` is
nonnegative. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_nonneg {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    0 ≤ scalar (FourTensor.reactionTensor r) := by
  rw [hr.scalar_reactionTensor_eq_sum (stdOrthonormalBasis ℝ V)]
  positivity

/-- For an algebraic curvature tensor `r`, `scalar (reactionTensor r) = 0` if and only if `r` is
Ricci-flat (`ricci r = 0`). -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_eq_zero_iff {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.reactionTensor r) = 0 ↔ ricci r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [hr.scalar_reactionTensor_eq_sum b]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hsum : (∑ p, ∑ q, ricci r (b p) (b q) ^ 2) = 0 := by linarith
  have hpq (p q : Fin (Module.finrank ℝ V)) : ricci r (b p) (b q) = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ sq_nonneg (ricci r (b i) (b j))).mp hsum p (Finset.mem_univ p)
    have hq := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      sq_nonneg (ricci r (b p) (b j))).mp hp q (Finset.mem_univ q)
    exact sq_eq_zero_iff.mp hq
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
  have hparseval (x y : V) : (∑ p, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ) = ⟪x, y⟫_ℝ := by
    simpa only [real_inner_comm x (b _), real_inner_comm y (b _)] using
      b.sum_inner_mul_inner x y
  have hq (p : Fin (Module.finrank ℝ V)) :
      (∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q]) =
        ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, z⟫_ℝ * (⟪v, b p⟫_ℝ * ⟪w, b p⟫_ℝ) -
          ⟪v, w⟫_ℝ * (⟪u, b p⟫_ℝ * ⟪z, b p⟫_ℝ) +
          (⟪z, b p⟫_ℝ * ⟪w, b p⟫_ℝ) * ⟪u, v⟫_ℝ := by
    simp only [constantCurvature_apply]
    have hring (q : Fin (Module.finrank ℝ V)) :
        (⟪u, z⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪b p, z⟫_ℝ) *
            (⟪v, w⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪v, b q⟫_ℝ * ⟪b p, w⟫_ℝ) =
          ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ * (⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
            ⟪u, z⟫_ℝ * ⟪b p, w⟫_ℝ * (⟪v, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
            ⟪v, w⟫_ℝ * ⟪b p, z⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) +
            ⟪b p, z⟫_ℝ * ⟪b p, w⟫_ℝ * (⟪u, b q⟫_ℝ * ⟪v, b q⟫_ℝ) := by ring
    simp_rw [hring, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hparseval u v, orthonormal_iff_ite.mp b.orthonormal]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      real_inner_comm w (b p), real_inner_comm z (b p)]
    ring
  simp_rw [hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hparseval v w, hparseval u z, hparseval z w]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- On the constant-curvature tensor of curvature `1` on an `n`-dimensional space `V`,
`reactionTensor` acts with eigenvalue `2 (n - 1)`. -/
@[simp]
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  let b := stdOrthonormalBasis ℝ V
  have hparseval (x y : V) : (∑ p, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ) = ⟪x, y⟫_ℝ := by
    simpa only [real_inner_comm x (b _), real_inner_comm y (b _)] using
      b.sum_inner_mul_inner x y
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := (FinVec.etaExpand_eq m).symm
  rw [hm, reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul,
    constantCurvature_apply]
  have hS₁ :
      (∑ p, ∑ q, constantCurvature V ![m 0, m 1, b p, b q] *
          constantCurvature V ![m 2, m 3, b p, b q]) =
        2 * (⟪m 0, m 2⟫_ℝ * ⟪m 1, m 3⟫_ℝ - ⟪m 0, m 3⟫_ℝ * ⟪m 1, m 2⟫_ℝ) := by
    simp only [constantCurvature_apply]
    have hring (p q : Fin (Module.finrank ℝ V)) :
        (⟪m 0, b p⟫_ℝ * ⟪m 1, b q⟫_ℝ - ⟪m 0, b q⟫_ℝ * ⟪m 1, b p⟫_ℝ) *
            (⟪m 2, b p⟫_ℝ * ⟪m 3, b q⟫_ℝ - ⟪m 2, b q⟫_ℝ * ⟪m 3, b p⟫_ℝ) =
          (⟪m 0, b p⟫_ℝ * ⟪m 2, b p⟫_ℝ) * (⟪m 1, b q⟫_ℝ * ⟪m 3, b q⟫_ℝ) -
            (⟪m 0, b p⟫_ℝ * ⟪m 3, b p⟫_ℝ) * (⟪m 1, b q⟫_ℝ * ⟪m 2, b q⟫_ℝ) -
            (⟪m 1, b p⟫_ℝ * ⟪m 2, b p⟫_ℝ) * (⟪m 0, b q⟫_ℝ * ⟪m 3, b q⟫_ℝ) +
            (⟪m 1, b p⟫_ℝ * ⟪m 3, b p⟫_ℝ) * (⟪m 0, b q⟫_ℝ * ⟪m 2, b q⟫_ℝ) := by ring
    simp_rw [hring, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hparseval,
      ← Finset.sum_mul, hparseval]
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
  rw [reactionTensor_smul, reactionTensor_constantCurvature, smul_smul]
  congr 1
  ring

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
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- On the rank-one curvature four-tensor of `S² × ℝ^(n - 2)` associated with a two-dimensional
subspace `K ≤ V`, `reactionTensor` acts with eigenvalue `2`. -/
theorem reactionTensor_constantCurvature_comp_orthogonalProjectionOnto_of_finrank_eq_two
    {K : Submodule ℝ V} (hK : Module.finrank ℝ K = 2) :
    reactionTensor
        ((constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (2 : ℝ) •
        (constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto := by
  rw [reactionTensor_constantCurvature_comp_orthogonalProjectionOnto, hK]
  norm_num

end ContractionsAndExamples

end FourTensor

end TauCeti
