/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Dimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Algebra.Order.BigOperators.Group.Finset
import TauCeti.Analysis.Calculus.Bilinear
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
pulling back along any continuous linear map whose adjoint preserves inner products — in particular
any linear isometric equivalence, any orthogonal projection onto a subspace, or the zero extension
`WithLp.fstL` from `V` to `WithLp 2 (V × U)` — commutes with `reactionTensor`.

Symmetrizing the bilinear contraction produces a continuous symmetric bilinear map
`TauCeti.FourTensor.reactionBilinear V` with `reactionBilinear V r r = reactionTensor r`. From this
polarization we obtain quadratic homogeneity, smoothness (`ContDiff ℝ ∞`), an explicit Fréchet
derivative `2 • reactionBilinear V r`, explicit dimensional operator-norm bounds
`‖reactionTensor r‖ ≤ 5 * (finrank ℝ V) ^ 2 * ‖r‖ ^ 2`, and explicit radius-linear Lipschitz bounds
on bounded sets.

`reactionBilinear V` preserves pair antisymmetry and pair interchange
(`TauCeti.FourTensor.IsBivectorSymmetric.reactionBilinear`). For algebraic curvature tensors,
first Bianchi cancellation implies that `reactionTensor` and `reactionBilinear V` also preserve the
first Bianchi identity, hence all four algebraic curvature symmetries
(`TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`, `TauCeti.FourTensor.reactionTensor_mem`),
and simplifies the Ricci and scalar contractions of `Q(r)` to
`Ric(Q(r))(u, v) = 2 ∑_pq Ric(r)(b p, b q) r(b p, u, b q, v)` and
`Scal(Q(r)) = 2 ∑_pq Ric(r)(b p, b q) ^ 2`, with polarized versions for `reactionBilinear V r s`;
in terms of the action `TauCeti.FourTensor.curvatureAction` of `r` on bilinear forms,
`Ric(Q(r)) = 2 r(Ric(r))` and `Scal(Q(r)) = 2 tr(Ric♯ Ric♯)`. Pairing `r` with a Kulkarni–Nomizu
product `h ⊙ g` of a symmetric form `h` with the inner product gives
`B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`: the terms of `r` with an argument `h♯ x`, where
`h♯ = bilinFormToEnd h`, cancel by the first Bianchi identity. This evaluates `Q(k ⊙ g)`, and for
`h = g` it gives
`reactionBilinear V r (constantCurvature V) = kulkarniNomizu (ricci r) (innerₗ V)`. On the
constant-curvature tensor of curvature `1`, `Q` acts with eigenvalue `2 (n - 1)`, and on the
curvature tensor of `S^k × ℝ^(n - k)` obtained by pulling back the constant-curvature tensor of a
`k`-dimensional subspace `K` along its orthogonal projection, `Q` acts with eigenvalue
`2 (k - 1)` (in particular `2` when `dim K = 2`). On the rank-one two-plane curvature tensor
`TauCeti.FourTensor.planeCurvature u v`, the last two sums in `Q` cancel term by term and
`Q(planeCurvature u v) = (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v`, which is
`2 • planeCurvature u v` for an orthonormal pair `u, v`.

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
* `TauCeti.FourTensor.IsBivectorSymmetric.reactionBilinear`: `reactionBilinear V` preserves
  bivector-symmetric four-tensors.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor` and
  `TauCeti.FourTensor.reactionTensor_mem`: `reactionTensor` maps `algebraicCurvatureSubmodule V` to
  itself.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_of_inner_eq`: coisometric equivariance
  of `reactionTensor`, specializing to orthogonal equivariance
  (`TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`) and subspace
  orthogonal-projection (zero-extension) equivariance
  (`TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto`).
* `TauCeti.FourTensor.norm_reactionTensor_le`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`, and
  `TauCeti.FourTensor.contDiff_reactionTensor`: explicit dimensional bounds, bounded-set Lipschitz
  estimates, Fréchet derivative, and smoothness of `reactionTensor`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_reactionTensor_apply_orthonormalBasis` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_reactionTensor_apply_orthonormalBasis`: the Ricci
  and scalar contractions of `reactionTensor r` for an algebraic curvature tensor `r`.
* `FourTensor.IsAlgebraicCurvature.ricci_reactionBilinear_apply_orthonormalBasis` and
  `FourTensor.IsAlgebraicCurvature.scalar_reactionBilinear_apply_orthonormalBasis`: their
  polarized versions for `reactionBilinear V r s`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_reactionTensor` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_reactionTensor`: `Ric(Q(r)) = 2 r(Ric(r))` and
  `Scal(Q(r)) = 2 tr(Ric♯ Ric♯)`.
* `TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right` and its symmetric
  counterpart: `B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`.
* `TauCeti.FourTensor.reactionTensor_kulkarniNomizu_innerₗ`: the reaction tensor of `k ⊙ g`.
* `TauCeti.FourTensor.reactionBilinear_constantCurvature_right`: pairing with the
  constant-curvature tensor gives `kulkarniNomizu (ricci r) (innerₗ V)`.
* `TauCeti.FourTensor.reactionTensor_constantCurvature` and
  `FourTensor.reactionTensor_constantCurvature_compContinuousLinearMap_orthogonalProjectionOnto`:
  evaluation of `reactionTensor` on constant-curvature and subspace-product curvature tensors.
* `TauCeti.FourTensor.reactionTensor_planeCurvature` and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_fstL`: rank-one plane curvature
  tensors and zero extension to `WithLp 2 (V × U)`.

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

open LinearMap (BilinForm)
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

end Helpers

section Reaction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The components of the reaction tensor `Q(r)` in an orthonormal basis `b`, with
`r_ijpq = r(b i, b j, b p, b q)`:
`Q(r)_ijkl = ∑_pq r_ijpq r_klpq + 2 ∑_pq r_ipkq r_jplq - 2 ∑_pq r_iplq r_jpkq`. -/
def reactionComponent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) : ℝ :=
  (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
  2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
  2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q])

/-- Explicit sum formula for `reactionComponent b r i j k l`. -/
theorem reactionComponent_def {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r : FourTensor V) (i j k l : ι) :
    reactionComponent b r i j k l =
      (∑ p, ∑ q, r ![b i, b j, b p, b q] * r ![b k, b l, b p, b q]) +
      2 * (∑ p, ∑ q, r ![b i, b p, b k, b q] * r ![b j, b p, b l, b q]) -
      2 * (∑ p, ∑ q, r ![b i, b p, b l, b q] * r ![b j, b p, b k, b q]) :=
  (rfl)

variable [FiniteDimensional ℝ V]

/-- The reaction tensor `Q(r)` of the curvature evolution equation, expanded in the standard
orthonormal basis of `V`:
`Q(r) = ∑_ijkl Q(r)_ijkl • coordFourTensor (stdOrthonormalBasis ℝ V) i j k l`.
Its independence of the orthonormal basis is `reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
      coordFourTensor (stdOrthonormalBasis ℝ V) i j k l

/-- Definition of `reactionTensor r` as its coordinate expansion in `stdOrthonormalBasis ℝ V`. -/
theorem reactionTensor_def (r : FourTensor V) :
    reactionTensor r =
      ∑ i, ∑ j, ∑ k, ∑ l,
        reactionComponent (stdOrthonormalBasis ℝ V) r i j k l •
          coordFourTensor (stdOrthonormalBasis ℝ V) i j k l :=
  (rfl)

/-- The bilinear form `(u, v) ↦ r ![u, v, x, y]`: `toLinearMap₄ r` evaluated at `x` and `y` in its
last two slots. -/
private def slice12 (r : FourTensor V) (x y : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (toLinearMap₄ r).compr₂ (LinearMap.applyₗ y ∘ₗ LinearMap.applyₗ x)

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
      (tensorBilin (ricciSlice r (b p) (b q)) (ricciSlice s (b p) (b q))))) -
  (2 : ℝ) • (∑ p, ∑ q, ofLinearMap₄
    (((LinearMap.lflip (R₀ := ℝ)).toLinearMap.comp
      (tensorBilin (ricciSlice r (b p) (b q)) (ricciSlice s (b p) (b q)))).compr₂
      (LinearMap.lflip (R₀ := ℝ)).toLinearMap))

private theorem reactionBilinearContraction_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinearContraction b r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  simp [reactionBilinearContraction, tensorBilin, slice12, ricciSlice_apply]

private theorem reactionTensor_eq_contraction (r : FourTensor V) :
    reactionTensor r = reactionBilinearContraction (stdOrthonormalBasis ℝ V) r r := by
  rw [← sum_coordFourTensor_eq (stdOrthonormalBasis ℝ V)
    (reactionBilinearContraction (stdOrthonormalBasis ℝ V) r r)]
  simp only [reactionTensor, reactionBilinearContraction_apply, reactionComponent]

private theorem reactionBilinearContraction_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q]) := by
  let b₀ := stdOrthonormalBasis ℝ V
  have hid : ∀ x y : V, ⟪(id : V → V) x, y⟫_ℝ = ⟪x, (id : V → V) y⟫_ℝ := fun _ _ ↦ rfl
  have h1 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid hid (toLinearMap₄ r u v)
    (toLinearMap₄ s z w)
  have h2 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid hid ((toLinearMap₄ r u).flip z)
    ((toLinearMap₄ s v).flip w)
  have h3 := b₀.sum_sum_inner_comp_eq_of_inner_eq b hid hid ((toLinearMap₄ r u).flip w)
    ((toLinearMap₄ s v).flip z)
  simp only [Real.inner_apply, toLinearMap₄_apply, LinearMap.flip_apply, id_eq] at h1 h2 h3
  rw [reactionBilinearContraction_apply, h1, h2, h3]

/-- **Basis independence of the reaction tensor**: in every orthonormal basis `b` of `V`, `Q(r)` is
the contraction
`Q(r)(u, v, z, w) = ∑_pq r(u, v, b p, b q) r(z, w, b p, b q)
  + 2 ∑_pq r(u, b p, z, b q) r(v, b p, w, b q) - 2 ∑_pq r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) := by
  rw [reactionTensor_eq_contraction]
  exact reactionBilinearContraction_apply_orthonormalBasis b r r u v z w

/-- Evaluating `reactionTensor r` on four vectors of any orthonormal basis `b` recovers
`reactionComponent b r`. -/
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

private theorem norm_reactionBilinearContraction_le (r s : FourTensor V) :
    ‖reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s‖ ≤
      5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  let b := stdOrthonormalBasis ℝ V
  have hb := b.orthonormal
  refine opNorm_le_bound_vec (by positivity) fun u v z w ↦ ?_
  rw [reactionBilinearContraction_apply_orthonormalBasis b]
  set M := ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖)
  have hsum1 : |∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]| ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    rw [← Finset.sum_product']
    refine (Finset.abs_sum_le_card_nsmul (B := M) fun pq _ ↦ ?_).trans_eq (by simp [sq])
    rw [abs_mul]
    calc |r ![u, v, b pq.1, b pq.2]| * |s ![z, w, b pq.1, b pq.2]|
        ≤ (‖r‖ * ‖u‖ * ‖v‖) * (‖s‖ * ‖z‖ * ‖w‖) := by
          gcongr <;> exact abs_apply_basis_le_34 hb _ _ _ _ _
      _ = M := by simp only [M]; ring
  have hsum23 (u₁ u₂ : V) (hu : ‖u₁‖ * ‖u₂‖ = ‖z‖ * ‖w‖) :
      |∑ p, ∑ q, r ![u, b p, u₁, b q] * s ![v, b p, u₂, b q]| ≤
        (Module.finrank ℝ V : ℝ) ^ 2 * M := by
    rw [← Finset.sum_product']
    refine (Finset.abs_sum_le_card_nsmul (B := M) fun pq _ ↦ ?_).trans_eq (by simp [sq])
    rw [abs_mul]
    calc |r ![u, b pq.1, u₁, b pq.2]| * |s ![v, b pq.1, u₂, b pq.2]|
        ≤ (‖r‖ * ‖u‖ * ‖u₁‖) * (‖s‖ * ‖v‖ * ‖u₂‖) := by
          gcongr <;> exact abs_apply_basis_le_24 hb _ _ _ _ _
      _ = M := by simp only [M]; linear_combination ‖r‖ * ‖s‖ * ‖u‖ * ‖v‖ * hu
  have hsum2 := hsum23 z w rfl
  have hsum3 := hsum23 w z (mul_comm _ _)
  have habs (a b c : ℝ) : |a + 2 * b - 2 * c| ≤ |a| + 2 * |b| + 2 * |c| :=
    (abs_sub _ _).trans <| by
      simpa [abs_mul] using add_le_add_right (abs_add_le a (2 * b)) |2 * c|
  calc |(∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
        2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q])|
      ≤ _ := habs _ _ _
    _ ≤ (Module.finrank ℝ V : ℝ) ^ 2 * M + 2 * ((Module.finrank ℝ V : ℝ) ^ 2 * M) +
          2 * ((Module.finrank ℝ V : ℝ) ^ 2 * M) := by gcongr
    _ = 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ * ‖u‖ * ‖v‖ * ‖z‖ * ‖w‖ := by
          simp only [M]; ring

private def reactionBilinearFun (r s : FourTensor V) : FourTensor V :=
  (1 / 2 : ℝ) •
    (reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s +
      reactionBilinearContraction (stdOrthonormalBasis ℝ V) s r)

private theorem reactionBilinearFun_comm (r s : FourTensor V) :
    reactionBilinearFun r s = reactionBilinearFun s r := by
  simp only [reactionBilinearFun, add_comm]

private theorem reactionBilinearFun_self (r : FourTensor V) :
    reactionBilinearFun r r = reactionTensor r := by
  rw [reactionBilinearFun, ← reactionTensor_eq_contraction, ← two_smul ℝ (reactionTensor r),
    smul_smul]
  norm_num

private theorem reactionBilinearFun_add_left (r₁ r₂ s : FourTensor V) :
    reactionBilinearFun (r₁ + r₂) s = reactionBilinearFun r₁ s + reactionBilinearFun r₂ s := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [reactionBilinearFun, smul_apply, add_apply, smul_eq_mul,
    reactionBilinearContraction_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem reactionBilinearFun_smul_left (c : ℝ) (r s : FourTensor V) :
    reactionBilinearFun (c • r) s = c • reactionBilinearFun r s := by
  refine ext_vec fun u v z w ↦ ?_
  simp only [reactionBilinearFun, smul_apply, add_apply, smul_eq_mul,
    reactionBilinearContraction_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
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
  have h1 := norm_reactionBilinearContraction_le r s
  have h2 := norm_reactionBilinearContraction_le s r
  have hadd := norm_add_le (reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s)
    (reactionBilinearContraction (stdOrthonormalBasis ℝ V) s r)
  linarith

variable (V) in
/-- The symmetric continuous bilinear polarization of `reactionTensor`:
`reactionBilinear V r r = reactionTensor r` and
`reactionBilinear V r s = reactionBilinear V s r`. -/
def reactionBilinear : FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ reactionBilinearFun
      reactionBilinearFun_add_left reactionBilinearFun_smul_left
      reactionBilinearFun_add_right reactionBilinearFun_smul_right)
    (5 * (Module.finrank ℝ V : ℝ) ^ 2) norm_reactionBilinearFun_le

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
    reactionBilinearContraction_apply_orthonormalBasis b, smul_eq_mul]
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
theorem reactionBilinear_eq_smul_sub (r s : FourTensor V) :
    reactionBilinear V r s = (1 / 4 : ℝ) • (reactionTensor (r + s) - reactionTensor (r - s)) := by
  rw [reactionTensor_add, reactionTensor_sub]
  ext m; simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]; ring

/-- Difference-of-squares factorization `Q(r) - Q(s) = B(r + s, r - s)`. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilinear V (r + s) (r - s) := by
  simp only [← reactionBilinear_self, map_add, map_sub, add_apply, reactionBilinear_comm s r]
  abel

end Polarization

section NormAndRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Explicit dimensional operator-norm bound on `reactionBilinear V`. -/
theorem norm_reactionBilinear_le :
    -- Cache the canonical inner operator-space instances to keep typeclass synthesis shallow.
    @norm _ (by
      letI : SeminormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) := inferInstance
      letI : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) := inferInstance
      infer_instance) (reactionBilinear V) ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 := by
  let : SeminormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  let : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  exact LinearMap.mkContinuous₂_norm_le _ (by positivity) norm_reactionBilinearFun_le

/-- Explicit dimensional operator-norm bound on `reactionBilinear V r`. -/
theorem norm_reactionBilinear_apply_le (r : FourTensor V) :
    ‖reactionBilinear V r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ := by
  let : SeminormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  let : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  exact ((reactionBilinear V).le_opNorm r).trans <|
    mul_le_mul_of_nonneg_right norm_reactionBilinear_le (norm_nonneg r)

/-- Explicit dimensional operator-norm bound on `reactionBilinear V r s`. -/
theorem norm_reactionBilinear_apply_apply_le (r s : FourTensor V) :
    ‖reactionBilinear V r s‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by
  let : SeminormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  let : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  exact ((reactionBilinear V).le_opNorm₂ r s).trans <| by gcongr; exact norm_reactionBilinear_le

/-- Explicit dimensional quadratic operator-norm bound on `reactionTensor r`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ ^ 2 := by
  simpa only [reactionBilinear_self, sq, mul_assoc] using norm_reactionBilinear_apply_apply_le r r

/-- Explicit dimensional difference bound for `reactionTensor`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖s‖) * ‖r - s‖ := by
  let : SeminormedAddCommGroup (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  let : NormedSpace ℝ (FourTensor V →L[ℝ] FourTensor V) := inferInstance
  rw [← reactionBilinear_self r, ← reactionBilinear_self s]
  refine ((reactionBilinear V).norm_apply_apply_sub_apply_apply_le r s).trans ?_
  gcongr; exact norm_reactionBilinear_le

/-- On any set `s` of four-tensors bounded in norm by `R`, `reactionTensor` is Lipschitz with
explicit dimensional constant `10 * (finrank ℝ V) ^ 2 * R`. -/
theorem lipschitzOnWith_reactionTensor_of_norm_le {s : Set (FourTensor V)} {R : ℝ≥0}
    (hs : ∀ r ∈ s, ‖r‖ ≤ R) :
    LipschitzOnWith (10 * (Module.finrank ℝ V : ℝ≥0) ^ 2 * R)
      (reactionTensor (V := V)) s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro r hr q hq
  calc ‖reactionTensor r - reactionTensor q‖
      ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ + ‖q‖) * ‖r - q‖ := norm_reactionTensor_sub_le r q
    _ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ((R : ℝ) + R) * ‖r - q‖ := by
        gcongr; exacts [hs r hr, hs q hq]
    _ = ((10 * (Module.finrank ℝ V : ℝ≥0) ^ 2 * R : ℝ≥0) : ℝ) * ‖r - q‖ := by push_cast; ring

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
  have hEq : (reactionTensor (V := V)) = fun q ↦ reactionBilinear V q q :=
    funext fun q ↦ (reactionBilinear_self q).symm
  have hder : (reactionBilinear V).flip r + reactionBilinear V r =
      (2 : ℝ) • reactionBilinear V r := by rw [reactionBilinear_flip, (two_smul ℝ _).symm]
  rw [hEq, ← hder]
  exact (reactionBilinear V).hasStrictFDerivAt_apply_self r

/-- `reactionTensor` has Fréchet derivative `2 • reactionBilinear V r` at `r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilinear V r) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- `reactionTensor` is Fréchet differentiable everywhere. -/
@[fun_prop]
theorem differentiable_reactionTensor : Differentiable ℝ (reactionTensor (V := V)) :=
  fun r ↦ (hasFDerivAt_reactionTensor r).differentiableAt

/-- The Fréchet derivative of `reactionTensor` at `r` is `2 • reactionBilinear V r`. -/
@[simp]
theorem fderiv_reactionTensor (r : FourTensor V) :
    fderiv ℝ (reactionTensor (V := V)) r = (2 : ℝ) • reactionBilinear V r :=
  (hasFDerivAt_reactionTensor r).fderiv

/-- `reactionTensor` is smooth (`C^n` for every `n`, in particular `C^∞`). -/
@[fun_prop]
theorem contDiff_reactionTensor {n : WithTop ℕ∞} :
    ContDiff ℝ n (reactionTensor (V := V)) := by
  have hEq : (reactionTensor (V := V)) = fun r ↦ reactionBilinear V r r :=
    funext fun r ↦ (reactionBilinear_self r).symm
  rw [hEq]; exact (reactionBilinear V).contDiff_apply_self

/-- `reactionTensor` is continuous. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := ⊤)).continuous

/-- `reactionTensor` is locally Lipschitz. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 1)).locallyLipschitz

end NormAndRegularity

section Equivariance

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private theorem reactionBilinearContraction_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V → W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (hg : ∀ x y, ⟪g x, g y⟫_ℝ = ⟪x, y⟫_ℝ) (r s : FourTensor V) :
    reactionBilinearContraction (stdOrthonormalBasis ℝ W)
        (r.compContinuousLinearMap fun _ ↦ f) (s.compContinuousLinearMap fun _ ↦ f) =
      (reactionBilinearContraction (stdOrthonormalBasis ℝ V) r s).compContinuousLinearMap
        fun _ ↦ f := by
  let bW := stdOrthonormalBasis ℝ W
  let bV := stdOrthonormalBasis ℝ V
  refine ext_vec fun u v z w ↦ ?_
  rw [compContinuousLinearMap_apply_vec, reactionBilinearContraction_apply_orthonormalBasis bW,
    reactionBilinearContraction_apply_orthonormalBasis bV]
  simp only [compContinuousLinearMap_apply_vec]
  have h1 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg hg
    (toLinearMap₄ r (f u) (f v)) (toLinearMap₄ s (f z) (f w))
  have h2 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg hg
    ((toLinearMap₄ r (f u)).flip (f z)) ((toLinearMap₄ s (f v)).flip (f w))
  have h3 := bW.sum_sum_inner_comp_eq_of_inner_eq bV hfg hg
    ((toLinearMap₄ r (f u)).flip (f w)) ((toLinearMap₄ s (f v)).flip (f z))
  simp only [Real.inner_apply, toLinearMap₄_apply, LinearMap.flip_apply] at h1 h2 h3
  rw [h1, h2, h3]

/-- Coisometric equivariance of `reactionBilinear`: if `f : W →L[ℝ] V` has an
inner-product-preserving adjoint `g : V → W` (`⟪f x, y⟫ = ⟪x, g y⟫` and `⟪g x, g y⟫ = ⟪x, y⟫`),
pulling back four-tensors along `f` commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V → W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (hg : ∀ x y, ⟪g x, g y⟫_ℝ = ⟪x, y⟫_ℝ) (r s : FourTensor V) :
    reactionBilinear W (r.compContinuousLinearMap fun _ ↦ f)
        (s.compContinuousLinearMap fun _ ↦ f) =
      (reactionBilinear V r s).compContinuousLinearMap fun _ ↦ f := by
  ext m
  simp only [reactionBilinear_eq_fun, reactionBilinearFun, smul_apply, add_apply,
    reactionBilinearContraction_compContinuousLinearMap_of_inner_eq hfg hg,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- Coisometric equivariance of `reactionTensor`: if `f : W →L[ℝ] V` has an
inner-product-preserving adjoint `g : V → W` (`⟪f x, y⟫ = ⟪x, g y⟫` and `⟪g x, g y⟫ = ⟪x, y⟫`),
pulling back along `f` commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_of_inner_eq
    {f : W →L[ℝ] V} {g : V → W} (hfg : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, g y⟫_ℝ)
    (hg : ∀ x y, ⟪g x, g y⟫_ℝ = ⟪x, y⟫_ℝ) (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ f) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ f := by
  simpa only [reactionBilinear_self] using
    reactionBilinear_compContinuousLinearMap_of_inner_eq hfg hg r r

/-- Orthogonal equivariance of `reactionBilinear` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`. -/
theorem reactionBilinear_compContinuousLinearMap_linearIsometryEquiv
    (e : W ≃ₗᵢ[ℝ] V) (r s : FourTensor V) :
    reactionBilinear W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilinear V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionBilinear_compContinuousLinearMap_of_inner_eq (g := e.symm)
    (fun x y ↦ e.inner_map_eq_flip x y) (fun x y ↦ e.symm.inner_map_map x y) r s

/-- Orthogonal equivariance of `reactionTensor` under a linear isometric equivalence
`e : W ≃ₗᵢ[ℝ] V`. -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    reactionTensor
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionTensor_compContinuousLinearMap_of_inner_eq (g := e.symm)
    (fun x y ↦ e.inner_map_eq_flip x y) (fun x y ↦ e.symm.inner_map_map x y) r

/-- Pulling back two four-tensors on a subspace `K ≤ V` along `K.orthogonalProjectionOnto`
(extending them by zero on `Kᗮ`) commutes with `reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_orthogonalProjectionOnto
    (K : Submodule ℝ V) (r s : FourTensor K) :
    reactionBilinear V (r.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto)
        (s.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (reactionBilinear K r s).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto :=
  reactionBilinear_compContinuousLinearMap_of_inner_eq (g := Subtype.val)
    (fun x y ↦ K.inner_orthogonalProjectionOnto_eq_of_mem_right y x) (fun _ _ ↦ rfl) r s

/-- Pulling back a four-tensor on a subspace `K ≤ V` along `K.orthogonalProjectionOnto`
(extending it by zero on `Kᗮ`) commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto
    (K : Submodule ℝ V) (r : FourTensor K) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto :=
  reactionTensor_compContinuousLinearMap_of_inner_eq (g := Subtype.val)
    (fun x y ↦ K.inner_orthogonalProjectionOnto_eq_of_mem_right y x) (fun _ _ ↦ rfl) r

/-- Zero extension from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` commutes with
`reactionBilinear`. -/
theorem reactionBilinear_compContinuousLinearMap_fstL {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r s : FourTensor V) :
    reactionBilinear (WithLp 2 (V × U))
        (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U)
        (s.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U) =
      (reactionBilinear V r s).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U :=
  reactionBilinear_compContinuousLinearMap_of_inner_eq (g := fun x ↦ WithLp.toLp 2 (x, 0))
    (fun _ _ ↦ by simp [WithLp.prod_inner_apply]) (fun _ _ ↦ by simp [WithLp.prod_inner_apply])
    r s

/-- Zero extension from `V` to `WithLp 2 (V × U)` along `WithLp.fstL` commutes with
`reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_fstL {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V U := by
  simpa only [reactionBilinear_self] using reactionBilinear_compContinuousLinearMap_fstL r r

end Equivariance

section AlgebraicCurvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The reaction bilinear map preserves bivector-symmetric four-tensors: if `r` and `s` are
antisymmetric in each pair and symmetric under interchanging the pairs, so is `Q(r, s)`. -/
theorem IsBivectorSymmetric.reactionBilinear {r s : FourTensor V} (hr : IsBivectorSymmetric r)
    (hs : IsBivectorSymmetric s) : IsBivectorSymmetric (FourTensor.reactionBilinear V r s) := by
  let b := stdOrthonormalBasis ℝ V
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [reactionBilinear_apply_orthonormalBasis b]
  · simp only [hr.antisymm_first v u, hs.antisymm_first v u, neg_mul, Finset.sum_neg_distrib,
      mul_comm (s _) (r _)]
    ring
  · simp only [hr.antisymm_first w z, hs.antisymm_first w z, mul_neg, Finset.sum_neg_distrib,
      mul_comm (s _) (r _)]
    ring
  · simp only [hr.swap_pairs z _ u _, hs.swap_pairs w _ v _, hr.swap_pairs w _ v _,
      hs.swap_pairs z _ u _, hr.swap_pairs z _ v _, hs.swap_pairs w _ u _, hr.swap_pairs w _ u _,
      hs.swap_pairs z _ v _]
    have hc (f : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ) :
        ∑ p, ∑ q, f q p = ∑ p, ∑ q, f p q := Finset.sum_comm
    rw [hc fun p q ↦ r ![u, b p, z, b q] * s ![v, b p, w, b q],
      hc fun p q ↦ s ![u, b p, z, b q] * r ![v, b p, w, b q],
      hc fun p q ↦ r ![v, b p, z, b q] * s ![u, b p, w, b q],
      hc fun p q ↦ s ![v, b p, z, b q] * r ![u, b p, w, b q]]
    simp only [mul_comm (s _) (r _)]
    ring

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
  have h := reactionBilinear_self r ▸
    hr.isBivectorSymmetric.reactionBilinear hr.isBivectorSymmetric
  refine ⟨h.antisymm_first, h.antisymm_last, h.swap_pairs, fun u v z w ↦ ?_⟩
  simp only [reactionTensor_eq_S₁_S₂]
  linear_combination two_mul_reactionS₂_sub_eq_neg_reactionS₁ hr u v z w +
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
  rw [reactionBilinear_eq_smul_sub]
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

/-- The Ricci contraction of the reaction tensor of an algebraic curvature tensor:
`Ric(Q(r)) = 2 r(Ric(r))`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.reactionTensor r) = (2 : ℝ) • curvatureAction r (ricci r) := by
  ext u v
  rw [hr.ricci_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    LinearMap.smul_apply, LinearMap.smul_apply,
    curvatureAction_apply_orthonormalBasis (stdOrthonormalBasis ℝ V), smul_eq_mul]

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
theorem IsAlgebraicCurvature.scalar_reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis ι ℝ V) :
    scalar (FourTensor.reactionTensor r) = 2 * ∑ p, ∑ q, ricci r (b p) (b q) ^ 2 := by
  rw [scalar_apply, LinearMap.BilinMap.metricTrace_eq_sum _ b]
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

/-- The scalar contraction of the reaction tensor of an algebraic curvature tensor is twice the
squared norm of its Ricci tensor: `Scal(Q(r)) = 2 tr(Ric♯ ∘ Ric♯)`, with
`Ric♯ = bilinFormToEnd (ricci r)`. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.reactionTensor r) =
      2 * LinearMap.trace ℝ V (bilinFormToEnd (ricci r) ∘ₗ bilinFormToEnd (ricci r)) := by
  rw [hr.scalar_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    LinearMap.BilinForm.trace_bilinFormToEnd_comp_bilinFormToEnd
      (stdOrthonormalBasis ℝ V) hr.isSymm_ricci]
  simp only [sq]

/-- For an algebraic curvature tensor `r`, the scalar contraction of `reactionTensor r` is
nonnegative. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_nonneg {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : 0 ≤ scalar (FourTensor.reactionTensor r) := by
  rw [hr.scalar_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]; positivity

/-- For an algebraic curvature tensor `r`, `scalar (reactionTensor r) = 0` if and only if `r` is
Ricci-flat (`ricci r = 0`). -/
theorem IsAlgebraicCurvature.scalar_reactionTensor_eq_zero_iff {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : scalar (FourTensor.reactionTensor r) = 0 ↔ ricci r = 0 := by
  let b := stdOrthonormalBasis ℝ V
  rw [hr.scalar_reactionTensor_apply_orthonormalBasis b]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hsum : (∑ p, ∑ q, ricci r (b p) (b q) ^ 2) = 0 := by linarith
  have hpq (p q : Fin (Module.finrank ℝ V)) : ricci r (b p) (b q) = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ sq_nonneg (ricci r (b i) (b j))).mp hsum p (Finset.mem_univ p)
    exact sq_eq_zero_iff.mp <| (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      sq_nonneg (ricci r (b p) (b j))).mp hp q (Finset.mem_univ q)
  exact LinearMap.BilinForm.ext_basis b.toBasis fun p q ↦ by simpa using hpq p q

/-- For algebraic curvature tensors `r` and `s`, the Ricci contraction of `reactionBilinear V r s`
in any orthonormal basis `b` is
`Ric(B(r, s))(u, v) = ∑_pq (Ric(r)(b p, b q) s(b p, u, b q, v) +
  Ric(s)(b p, b q) r(b p, u, b q, v))`. -/
theorem IsAlgebraicCurvature.ricci_reactionBilinear_apply_orthonormalBasis {ι : Type*}
    [Fintype ι] {r s : FourTensor V} (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s)
    (b : OrthonormalBasis ι ℝ V) (u v : V) :
    ricci (FourTensor.reactionBilinear V r s) u v =
      ∑ p, ∑ q, (ricci r (b p) (b q) * s ![b p, u, b q, v] +
        ricci s (b p) (b q) * r ![b p, u, b q, v]) := by
  have hrs : IsAlgebraicCurvature (r + s) := by
    rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
    exact Submodule.add_mem _ hr hs
  have h := congrArg (fun t ↦ ricci t u v) (reactionTensor_add r s)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hrs.ricci_reactionTensor_apply_orthonormalBasis b,
    hr.ricci_reactionTensor_apply_orthonormalBasis b,
    hs.ricci_reactionTensor_apply_orthonormalBasis b, add_apply] at h
  have hsum :
      (∑ p, ∑ q, (ricci r (b p) (b q) + ricci s (b p) (b q)) *
          (r ![b p, u, b q, v] + s ![b p, u, b q, v])) -
        (∑ p, ∑ q, ricci r (b p) (b q) * r ![b p, u, b q, v]) -
        (∑ p, ∑ q, ricci s (b p) (b q) * s ![b p, u, b q, v]) =
      ∑ p, ∑ q, (ricci r (b p) (b q) * s ![b p, u, b q, v] +
        ricci s (b p) (b q) * r ![b p, u, b q, v]) := by
    simp_rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

/-- For algebraic curvature tensors `r` and `s`, the scalar contraction of
`reactionBilinear V r s` in any orthonormal basis `b` is twice the Hilbert-Schmidt inner product
of their Ricci tensors: `Scal(B(r, s)) = 2 ∑_pq Ric(r)(b p, b q) Ric(s)(b p, b q)`. -/
theorem IsAlgebraicCurvature.scalar_reactionBilinear_apply_orthonormalBasis {ι : Type*}
    [Fintype ι] {r s : FourTensor V} (hr : IsAlgebraicCurvature r) (hs : IsAlgebraicCurvature s)
    (b : OrthonormalBasis ι ℝ V) :
    scalar (FourTensor.reactionBilinear V r s) =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * ricci s (b p) (b q) := by
  have hrs : IsAlgebraicCurvature (r + s) := by
    rw [← mem_algebraicCurvatureSubmodule] at hr hs ⊢
    exact Submodule.add_mem _ hr hs
  have h := congrArg scalar (reactionTensor_add r s)
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul,
    hrs.scalar_reactionTensor_apply_orthonormalBasis b,
    hr.scalar_reactionTensor_apply_orthonormalBasis b,
    hs.scalar_reactionTensor_apply_orthonormalBasis b] at h
  have hsum :
      (∑ p, ∑ q, (ricci r (b p) (b q) + ricci s (b p) (b q)) ^ 2) -
        (∑ p, ∑ q, ricci r (b p) (b q) ^ 2) - (∑ p, ∑ q, ricci s (b p) (b q) ^ 2) =
      2 * ∑ p, ∑ q, ricci r (b p) (b q) * ricci s (b p) (b q) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

/-- **Reaction against a Kulkarni–Nomizu product with the inner product.** For an algebraic
curvature tensor `r` and a symmetric bilinear form `h`, the polarized reaction of `r` with
`h ⊙ g` is `B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`. -/
theorem reactionBilinear_kulkarniNomizu_innerₗ_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {h : BilinForm ℝ V} (hh : h.IsSymm) :
    reactionBilinear V r (kulkarniNomizu h (innerₗ V)) =
      kulkarniNomizu (curvatureAction r h) (innerₗ V) + kulkarniNomizu h (ricci r) := by
  set b := stdOrthonormalBasis ℝ V
  set H := bilinFormToEnd h
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis b, add_apply, kulkarniNomizu_apply,
    kulkarniNomizu_apply]
  simp only [innerₗ_apply_apply]
  have s1a := sum_mul_kulkarniNomizu_innerₗ_last b hr h u v z w
  have s1b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      2 * (r ![z, w, H u, v] + r ![z, w, u, H v]) := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_last b hr h z w u v
  have s2a := sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh u z v w
  have s2b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      h u z * ricci r v w + ⟪u, z⟫_ℝ * curvatureAction r h v w - r ![v, z, w, H u] -
        r ![v, H z, w, u] := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh v w u z
  have s3a := sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh u w v z
  have s3b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      h u w * ricci r v z + ⟪u, w⟫_ℝ * curvatureAction r h v z - r ![v, w, z, H u] -
        r ![v, H w, z, u] := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh v z u w
  rw [s1a, s1b, s2a, s2b, s3a, s3b]
  -- The terms of `r` with an argument `h♯ x` cancel by the first Bianchi identity, one group
  -- for each of `x = z, w, u, v`.
  linear_combination hr.cyclic_eq_zero u v (H z) w - hr.antisymm_last v (H z) w u +
    hr.swap_first_last u (H z) w v - hr.cyclic_eq_zero u v (H w) z +
    hr.antisymm_last u v z (H w) - hr.swap_first_last u (H w) z v +
    hr.antisymm_last v (H w) z u + hr.cyclic_last_eq_zero (H u) v z w +
    hr.swap_pairs z w (H u) v - hr.reverse v z w (H u) + hr.reverse v w z (H u) -
    hr.antisymm_last (H u) w z v + hr.cyclic_last_eq_zero (H v) u w z + hr.reverse z w u (H v) -
    hr.reverse u w z (H v) + hr.reverse u z w (H v) - hr.antisymm_last (H v) z w u

/-- Symmetric counterpart of `TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right`:
`B(h ⊙ g, r) = r(h) ⊙ g + h ⊙ Ric(r)`. -/
theorem reactionBilinear_kulkarniNomizu_innerₗ_left {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {h : BilinForm ℝ V} (hh : h.IsSymm) :
    reactionBilinear V (kulkarniNomizu h (innerₗ V)) r =
      kulkarniNomizu (curvatureAction r h) (innerₗ V) + kulkarniNomizu h (ricci r) := by
  rw [reactionBilinear_comm, reactionBilinear_kulkarniNomizu_innerₗ_right hr hh]

/-- The reaction tensor of a Kulkarni–Nomizu product with the inner product: for a symmetric form
`k` with `k♯ = bilinFormToEnd k` on an `n`-dimensional space,
`Q(k ⊙ g) = (tr(k♯ k♯) g + (tr k) k - 2 ⟪k♯ k♯ ·, ·⟫) ⊙ g + k ⊙ ((n - 2) k + (tr k) g)`. -/
theorem reactionTensor_kulkarniNomizu_innerₗ {k : BilinForm ℝ V} (hk : k.IsSymm) :
    reactionTensor (kulkarniNomizu k (innerₗ V)) =
      kulkarniNomizu (LinearMap.trace ℝ V (bilinFormToEnd k ∘ₗ bilinFormToEnd k) • innerₗ V +
          LinearMap.BilinMap.metricTrace k • k -
          (2 : ℝ) • (innerₗ V).comp (bilinFormToEnd k ∘ₗ bilinFormToEnd k))
        (innerₗ V) +
      kulkarniNomizu k
        (((Module.finrank ℝ V : ℝ) - 2) • k + LinearMap.BilinMap.metricTrace k • innerₗ V) := by
  rw [← reactionBilinear_self, reactionBilinear_kulkarniNomizu_innerₗ_right
    (isAlgebraicCurvature_kulkarniNomizu hk (BilinForm.isSymm_iff.mpr isSymm_inner)) hk,
    curvatureAction_kulkarniNomizu_innerₗ hk hk, ricci_kulkarniNomizu_innerₗ, two_smul]
  rw [sub_sub (α := LinearMap.BilinForm ℝ V)]

/-- Pairing an algebraic curvature tensor `r` with `constantCurvature V` under `reactionBilinear V`
produces the Kulkarni–Nomizu product `kulkarniNomizu (ricci r) (innerₗ V)`: the case `h = g` of
`TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right`. -/
theorem reactionBilinear_constantCurvature_right {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear V r (constantCurvature V) = kulkarniNomizu (ricci r) (innerₗ V) := by
  rw [constantCurvature_eq_half_smul_kulkarniNomizu, map_smul,
    reactionBilinear_kulkarniNomizu_innerₗ_right hr (BilinForm.isSymm_iff.mpr isSymm_inner),
    curvatureAction_innerₗ]
  refine ext_vec fun u v z w ↦ ?_
  simp only [smul_apply, add_apply, kulkarniNomizu_apply, smul_eq_mul]
  ring

/-- Symmetric counterpart of `reactionBilinear_constantCurvature_right`. -/
theorem reactionBilinear_constantCurvature_left {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    reactionBilinear V (constantCurvature V) r = kulkarniNomizu (ricci r) (innerₗ V) := by
  rw [reactionBilinear_comm, reactionBilinear_constantCurvature_right hr]

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
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul, constantCurvature_apply]
  have hS₁ : (∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] *
      constantCurvature V ![z, w, b p, b q]) =
        2 * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ) := by
    simp only [constantCurvature_apply]
    have hring (p q : Fin (Module.finrank ℝ V)) :
        (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) *
            (⟪z, b p⟫_ℝ * ⟪w, b q⟫_ℝ - ⟪z, b q⟫_ℝ * ⟪w, b p⟫_ℝ) =
          (⟪u, b p⟫_ℝ * ⟪b p, z⟫_ℝ) * (⟪v, b q⟫_ℝ * ⟪b q, w⟫_ℝ) -
            (⟪u, b p⟫_ℝ * ⟪b p, w⟫_ℝ) * (⟪v, b q⟫_ℝ * ⟪b q, z⟫_ℝ) -
            (⟪v, b p⟫_ℝ * ⟪b p, z⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪b q, w⟫_ℝ) +
            (⟪v, b p⟫_ℝ * ⟪b p, w⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪b q, z⟫_ℝ) := by
      simp only [real_inner_comm (b p), real_inner_comm (b q)]; ring
    simp_rw [hring, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      b.sum_inner_mul_inner, ← Finset.sum_mul, b.sum_inner_mul_inner]
    ring
  rw [hS₁, sum_constantCurvature_mul_constantCurvature_24 u v z w,
    sum_constantCurvature_mul_constantCurvature_24 u v w z, real_inner_comm z w]
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
theorem reactionTensor_constantCurvature_compContinuousLinearMap_orthogonalProjectionOnto
    (K : Submodule ℝ V) :
    reactionTensor
        ((constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (2 * ((Module.finrank ℝ K : ℝ) - 1)) •
        (constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto := by
  rw [reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto,
    reactionTensor_constantCurvature]
  ext m; simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- On the rank-one curvature four-tensor of `S² × ℝ^(n - 2)` associated with a two-dimensional
subspace `K ≤ V`, `reactionTensor` acts with eigenvalue `2`. -/
theorem
reactionTensor_constantCurvature_compContinuousLinearMap_orthogonalProjectionOnto_of_finrank_eq_two
    {K : Submodule ℝ V} (hK : Module.finrank ℝ K = 2) :
    reactionTensor
        ((constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto) =
      (2 : ℝ) •
        (constantCurvature K).compContinuousLinearMap fun _ ↦ K.orthogonalProjectionOnto := by
  rw [reactionTensor_constantCurvature_compContinuousLinearMap_orthogonalProjectionOnto, hK]
  norm_num

/-- On the rank-one curvature tensor `planeCurvature u v`, the reaction tensor acts by scalar
multiplication by `2 (‖u‖² ‖v‖² - ⟪u, v⟫²) = 2 * constantCurvature V ![u, v, u, v]`. -/
theorem reactionTensor_planeCurvature (u v : V) :
    reactionTensor (planeCurvature u v) =
      (2 * constantCurvature V ![u, v, u, v]) • planeCurvature u v := by
  set b := stdOrthonormalBasis ℝ V
  have hnorm :
      (∑ p, ∑ q, (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2) =
        2 * constantCurvature V ![u, v, u, v] := by
    simp_rw [← planeCurvature_apply_self]
    rw [Finset.sum_comm, ← scalar_apply_orthonormalBasis b, scalar_planeCurvature]
  refine ext_vec fun x y z w ↦ ?_
  rw [reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul]
  -- The second and third double sums agree term-by-term for a factored rank-one four-tensor.
  have hcancel :
      (∑ p, ∑ q, planeCurvature u v ![x, b p, z, b q] *
          planeCurvature u v ![y, b p, w, b q]) =
        ∑ p, ∑ q, planeCurvature u v ![x, b p, w, b q] *
          planeCurvature u v ![y, b p, z, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      simp only [planeCurvature_apply]
      ring
  have hfirst :
      (∑ p, ∑ q, planeCurvature u v ![x, y, b p, b q] *
          planeCurvature u v ![z, w, b p, b q]) =
        (2 * constantCurvature V ![u, v, u, v]) * planeCurvature u v ![x, y, z, w] := by
    have hterm (p q : Fin (Module.finrank ℝ V)) :
        planeCurvature u v ![x, y, b p, b q] * planeCurvature u v ![z, w, b p, b q] =
          planeCurvature u v ![x, y, z, w] *
            (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) ^ 2 := by
      simp only [planeCurvature_apply]
      ring
    simp_rw [hterm, ← Finset.mul_sum, hnorm, mul_comm]
  rw [hcancel, hfirst]
  ring

/-- For an orthonormal pair `u, v` (representing the unit `S² × ℝⁿ⁻²` curvature),
`Q(planeCurvature u v) = 2 • planeCurvature u v`. -/
theorem reactionTensor_planeCurvature_of_orthonormal {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    reactionTensor (planeCurvature u v) = (2 : ℝ) • planeCurvature u v := by
  rw [reactionTensor_planeCurvature, ← scalar_planeCurvature,
    scalar_planeCurvature_of_orthonormal huv]

end ContractionsAndExamples

end FourTensor

end TauCeti
