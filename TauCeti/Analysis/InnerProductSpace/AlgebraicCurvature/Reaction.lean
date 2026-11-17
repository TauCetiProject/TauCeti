/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic

import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# The curvature reaction tensor of the Ricci flow

On a finite-dimensional real inner product space `V`, the *curvature reaction tensor* `Q(r)` of a
four-tensor `r : FourTensor V` is the quadratic expression appearing in Hamilton's curvature
evolution equation under the Ricci flow. In every orthonormal basis `(eᵢ)` of `V`,
$$
Q(r)(u, v, z, w) = \sum_{p, q} r(u, v, e_p, e_q) r(z, w, e_p, e_q)
  + 2 \sum_{p, q} r(u, e_p, z, e_q) r(v, e_p, w, e_q)
  - 2 \sum_{p, q} r(u, e_p, w, e_q) r(v, e_p, z, e_q).
$$

We define its symmetric bilinear polarization `TauCeti.FourTensor.reactionBilin` without choosing
a basis, by iterating the metric trace `TauCeti.bilinFormTrace` over the two contracted slots, and
set `TauCeti.FourTensor.reactionTensor r = reactionBilin r r`. An explicit operator-norm estimate
`‖reactionBilin‖ ≤ 5 * (Module.finrank ℝ V) ^ 2` packages `reactionBilin` as a continuous bilinear
map `FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V`.

This yields:

* basis independence (`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`);
* degree-two homogeneity, polarization, smoothness (`ContDiff ℝ n`), strict Fréchet
  differentiability with derivative `2 • reactionBilin r`, explicit operator-norm and closed-ball
  Lipschitz bounds, and local Lipschitz regularity
  (`TauCeti.FourTensor.locallyLipschitz_reactionTensor`);
* preservation of the algebraic curvature symmetries and first Bianchi identity
  (`TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor` and
  `TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`);
* equivariance under every coisometry `p : V →L[ℝ] W` satisfying `p ∘L p† = id`, specializing to
  orthogonal equivalences `V ≃ₗᵢ[ℝ] W`, adjoints of linear isometries, orthogonal projections onto
  subspaces `P : Submodule ℝ V`, and zero extensions along `WithLp.fstL 2 ℝ V U`;
* explicit evaluations on the constant-curvature tensor of the unit sphere (`Q(I) = 2 (n - 1) I`),
  on the curvature tensor of `S^k × ℝ^(n - k)` pulled back along orthogonal projection onto a
  subspace `P`, and on any rank-one tensor `r(u, v, z, w) = ω(u, v) ω(z, w)`, in particular the
  rank-one curvature tensor of `S² × ℝ^(n - 2)` where `Q(r) = 2 r`.

## Main definitions

* `TauCeti.FourTensor.reactionBilin`: the continuous symmetric bilinear polarization of the
  curvature reaction tensor.
* `TauCeti.FourTensor.reactionTensor`: the quadratic curvature reaction tensor `Q(r)`.

## Main statements

* `TauCeti.FourTensor.reactionBilin_apply_orthonormalBasis` and
  `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: basis-independent orthonormal-basis
  contraction formulas.
* `TauCeti.FourTensor.contDiff_reactionTensor`,
  `TauCeti.FourTensor.hasStrictFDerivAt_reactionTensor`,
  `TauCeti.FourTensor.norm_reactionBilin_le`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`, and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: regularity and Lipschitz estimates.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor`,
  `TauCeti.FourTensor.reactionTensor_mem_algebraicCurvatureSubmodule`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.reactionBilin`: preservation of algebraic curvature
  tensors.
* `TauCeti.FourTensor.reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id`,
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`,
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto`, and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_fstL`: coisometry, orthogonal,
  projection, and zero-extension equivariance.
* `TauCeti.FourTensor.reactionTensor_constantCurvature`,
  `TauCeti.FourTensor.reactionTensor_constantCurvature_orthogonalProjectionOnto`, and
  `TauCeti.FourTensor.reactionTensor_eq_two_smul_of_orthonormal_pair`: explicit evaluations on
  spheres, products with Euclidean space, and rank-one curvature tensors.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 3.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace NNReal

noncomputable section

namespace TauCeti

namespace FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Basis-free construction and bilinear polarization -/

/-- The inner trace over the fourth slot used in the first contraction term
`∑ p, ∑ s, r(u, v, e_p, e_s) q(z, w, e_p, e_s)`. -/
private def reactionFirstInner (r q : FourTensor V) (u v z w p₁ p₂ : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun s₁ s₂ ↦ r ![u, v, p₁, s₁] * q ![z, w, p₂, s₂])
    (fun _ _ _ ↦ by rw [apply_add_fourth, add_mul])
    (fun _ _ _ ↦ by rw [apply_smul_fourth, mul_assoc, smul_eq_mul])
    (fun _ _ _ ↦ by rw [apply_add_fourth, mul_add])
    (fun _ _ _ ↦ by rw [apply_smul_fourth, mul_left_comm, smul_eq_mul])

/-- Basis-free first contraction `∑ p, ∑ s, r(u, v, e_p, e_s) q(z, w, e_p, e_s)`. -/
private def reactionFirstTerm (r q : FourTensor V) (u v z w : V) : ℝ :=
  bilinFormTrace <| LinearMap.mk₂ ℝ
    (fun p₁ p₂ ↦ bilinFormTrace (reactionFirstInner r q u v z w p₁ p₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext s₁ s₂
      simp only [reactionFirstInner, LinearMap.mk₂_apply, LinearMap.add_apply,
        apply_add_third, add_mul])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext s₁ s₂
      simp only [reactionFirstInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_third, mul_assoc])
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext s₁ s₂
      simp only [reactionFirstInner, LinearMap.mk₂_apply, LinearMap.add_apply,
        apply_add_third, mul_add])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext s₁ s₂
      simp only [reactionFirstInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_third, mul_left_comm])

private theorem reactionFirstTerm_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r q : FourTensor V) (u v z w : V) :
    reactionFirstTerm r q u v z w = ∑ p, ∑ s, r ![u, v, b p, b s] * q ![z, w, b p, b s] := by
  simp only [reactionFirstTerm, bilinFormTrace_eq_sum _ b, LinearMap.mk₂_apply, reactionFirstInner]

/-- The inner trace over the fourth slot used in the second contraction term
`∑ p, ∑ s, r(u, e_p, z, e_s) q(v, e_p, w, e_s)`. -/
private def reactionSecondInner (r q : FourTensor V) (u v z w p₁ p₂ : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun s₁ s₂ ↦ r ![u, p₁, z, s₁] * q ![v, p₂, w, s₂])
    (fun _ _ _ ↦ by rw [apply_add_fourth, add_mul])
    (fun _ _ _ ↦ by rw [apply_smul_fourth, mul_assoc, smul_eq_mul])
    (fun _ _ _ ↦ by rw [apply_add_fourth, mul_add])
    (fun _ _ _ ↦ by rw [apply_smul_fourth, mul_left_comm, smul_eq_mul])

/-- Basis-free second contraction `∑ p, ∑ s, r(u, e_p, z, e_s) q(v, e_p, w, e_s)`. The third
contraction is `reactionSecondTerm r q u v w z`. -/
private def reactionSecondTerm (r q : FourTensor V) (u v z w : V) : ℝ :=
  bilinFormTrace <| LinearMap.mk₂ ℝ
    (fun p₁ p₂ ↦ bilinFormTrace (reactionSecondInner r q u v z w p₁ p₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext s₁ s₂
      simp only [reactionSecondInner, LinearMap.mk₂_apply, LinearMap.add_apply,
        apply_add_second, add_mul])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext s₁ s₂
      simp only [reactionSecondInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_second, mul_assoc])
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext s₁ s₂
      simp only [reactionSecondInner, LinearMap.mk₂_apply, LinearMap.add_apply,
        apply_add_second, mul_add])
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext s₁ s₂
      simp only [reactionSecondInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_second, mul_left_comm])

private theorem reactionSecondTerm_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r q : FourTensor V) (u v z w : V) :
    reactionSecondTerm r q u v z w = ∑ p, ∑ s, r ![u, b p, z, b s] * q ![v, b p, w, b s] := by
  simp only [reactionSecondTerm, bilinFormTrace_eq_sum _ b, LinearMap.mk₂_apply,
    reactionSecondInner]

/-- The raw scalar value of the polarized reaction tensor `reactionBilin r q` on `(u, v, z, w)`. -/
private def reactionBilinVal (r q : FourTensor V) (u v z w : V) : ℝ :=
  (1 / 2 : ℝ) * (reactionFirstTerm r q u v z w + reactionFirstTerm q r u v z w) +
    (reactionSecondTerm r q u v z w + reactionSecondTerm q r u v z w) -
    (reactionSecondTerm r q u v w z + reactionSecondTerm q r u v w z)

private theorem reactionBilinVal_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r q : FourTensor V) (u v z w : V) :
    reactionBilinVal r q u v z w =
      (1 / 2 : ℝ) * (∑ p, ∑ s, (r ![u, v, b p, b s] * q ![z, w, b p, b s] +
        q ![u, v, b p, b s] * r ![z, w, b p, b s])) +
      (∑ p, ∑ s, (r ![u, b p, z, b s] * q ![v, b p, w, b s] +
        q ![u, b p, z, b s] * r ![v, b p, w, b s])) -
      (∑ p, ∑ s, (r ![u, b p, w, b s] * q ![v, b p, z, b s] +
        q ![u, b p, w, b s] * r ![v, b p, z, b s])) := by
  simp only [reactionBilinVal, reactionFirstTerm_eq_sum b, reactionSecondTerm_eq_sum b,
    Finset.sum_add_distrib]

/-- Curried four-linear form underlying `reactionBilin r q`. -/
private def reactionBilinLinear₄ (r q : FourTensor V) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ (fun z w ↦ reactionBilinVal r q u v z w)
      (fun z₁ z₂ w ↦ by
        simp only [reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
          apply_add_first, apply_add_third, add_mul, mul_add, Finset.sum_add_distrib]
        ring)
      (fun c z w ↦ by
        simp only [reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V), smul_eq_mul,
          apply_smul_first, apply_smul_third, mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ),
          Finset.mul_sum]
        refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
      (fun z w₁ w₂ ↦ by
        simp only [reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
          apply_add_second, apply_add_third, add_mul, mul_add, Finset.sum_add_distrib]
        ring)
      (fun c z w ↦ by
        simp only [reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V), smul_eq_mul,
          apply_smul_second, apply_smul_third, mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ),
          Finset.mul_sum]
        refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring))
    (fun u₁ u₂ v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
        reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        apply_add_first, add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        apply_smul_first, mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ), Finset.mul_sum]
      refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun u v₁ v₂ ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
        reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        apply_add_first, apply_add_second, add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        apply_smul_first, apply_smul_second, mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ),
        Finset.mul_sum]
      refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- Unbundled bilinear map underlying `reactionBilin`. -/
private def reactionBilinLinear : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.mk₂ ℝ (fun r q ↦ ofLinearMap₄ (reactionBilinLinear₄ r q))
    (fun r₁ r₂ q ↦ by
      ext m
      simp only [ofLinearMap₄_apply, add_apply, reactionBilinLinear₄,
        LinearMap.mk₂_apply, reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c r q ↦ by
      ext m
      simp only [ofLinearMap₄_apply, smul_apply, smul_eq_mul, reactionBilinLinear₄,
        LinearMap.mk₂_apply, reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ), Finset.mul_sum]
      refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun r q₁ q₂ ↦ by
      ext m
      simp only [ofLinearMap₄_apply, add_apply, reactionBilinLinear₄,
        LinearMap.mk₂_apply, reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        add_mul, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c r q ↦ by
      ext m
      simp only [ofLinearMap₄_apply, smul_apply, smul_eq_mul, reactionBilinLinear₄,
        LinearMap.mk₂_apply, reactionBilinVal_eq_sum (stdOrthonormalBasis ℝ V),
        mul_sub, mul_add, mul_left_comm c (1 / 2 : ℝ), Finset.mul_sum]
      refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- Explicit operator-norm bound for `reactionBilinLinear`, used both to package `reactionBilin` as
a continuous bilinear map and to derive `TauCeti.FourTensor.norm_reactionBilin_le`. -/
private theorem norm_reactionBilinLinear_le (r q : FourTensor V) :
    ‖reactionBilinLinear r q‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖q‖ := by
  let b := stdOrthonormalBasis ℝ V
  let n : ℝ := Module.finrank ℝ V
  have hvec (s : FourTensor V) (x₁ x₂ x₃ x₄ : V) :
      ‖s ![x₁, x₂, x₃, x₄]‖ ≤ ‖s‖ * ‖x₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ := by
    have h := s.le_opNorm ![x₁, x₂, x₃, x₄]
    rw [Fin.prod_univ_four] at h
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_assoc] using h
  have hsum_bound (F G : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ)
      (C : ℝ) (hFG : ∀ p s, ‖F p s‖ ≤ C ∧ ‖G p s‖ ≤ C) :
      ‖∑ p, ∑ s, (F p s + G p s)‖ ≤ 2 * (n ^ 2 * C) := by
    calc ‖∑ p, ∑ s, (F p s + G p s)‖
        ≤ ∑ p, ∑ s, (‖F p s‖ + ‖G p s‖) :=
          (norm_sum_le _ _).trans <| Finset.sum_le_sum fun p _ ↦
            (norm_sum_le _ _).trans <| Finset.sum_le_sum fun s _ ↦ norm_add_le _ _
      _ ≤ ∑ _p : Fin (Module.finrank ℝ V), ∑ _s : Fin (Module.finrank ℝ V), (C + C) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun s _ ↦
            add_le_add (hFG p s).1 (hFG p s).2
      _ = 2 * (n ^ 2 * C) := by simp [n, sq]; ring
  have hpair (s t : FourTensor V) (a₁ a₂ c₁ c₂ : V) (p s' : Fin (Module.finrank ℝ V)) :
      ‖s ![a₁, a₂, b p, b s'] * t ![c₁, c₂, b p, b s']‖ ≤
        ‖s‖ * ‖t‖ * (‖a₁‖ * ‖a₂‖ * ‖c₁‖ * ‖c₂‖) := by
    have hs := hvec s a₁ a₂ (b p) (b s')
    have ht := hvec t c₁ c₂ (b p) (b s')
    simp only [b.norm_eq_one, mul_one] at hs ht
    rw [norm_mul]
    calc ‖s ![a₁, a₂, b p, b s']‖ * ‖t ![c₁, c₂, b p, b s']‖
        ≤ (‖s‖ * ‖a₁‖ * ‖a₂‖) * (‖t‖ * ‖c₁‖ * ‖c₂‖) := by gcongr
      _ = ‖s‖ * ‖t‖ * (‖a₁‖ * ‖a₂‖ * ‖c₁‖ * ‖c₂‖) := by ring
  have hpair' (s t : FourTensor V) (a₁ a₂ c₁ c₂ : V) (p s' : Fin (Module.finrank ℝ V)) :
      ‖s ![a₁, b p, c₁, b s'] * t ![a₂, b p, c₂, b s']‖ ≤
        ‖s‖ * ‖t‖ * (‖a₁‖ * ‖a₂‖ * ‖c₁‖ * ‖c₂‖) := by
    have hs := hvec s a₁ (b p) c₁ (b s')
    have ht := hvec t a₂ (b p) c₂ (b s')
    simp only [b.norm_eq_one, mul_one] at hs ht
    rw [norm_mul]
    calc ‖s ![a₁, b p, c₁, b s']‖ * ‖t ![a₂, b p, c₂, b s']‖
        ≤ (‖s‖ * ‖a₁‖ * ‖c₁‖) * (‖t‖ * ‖a₂‖ * ‖c₂‖) := by gcongr
      _ = ‖s‖ * ‖t‖ * (‖a₁‖ * ‖a₂‖ * ‖c₁‖ * ‖c₂‖) := by ring
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hval : reactionBilinLinear r q m = reactionBilinVal r q (m 0) (m 1) (m 2) (m 3) := by
    simp only [reactionBilinLinear, LinearMap.mk₂_apply, ofLinearMap₄_apply, reactionBilinLinear₄]
  rw [hval, reactionBilinVal_eq_sum b, Fin.prod_univ_four]
  set C := ‖r‖ * ‖q‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖)
  have h1 := hsum_bound
    (fun p s ↦ r ![m 0, m 1, b p, b s] * q ![m 2, m 3, b p, b s])
    (fun p s ↦ q ![m 0, m 1, b p, b s] * r ![m 2, m 3, b p, b s]) C fun p s ↦
      ⟨hpair r q (m 0) (m 1) (m 2) (m 3) p s,
        (hpair q r (m 0) (m 1) (m 2) (m 3) p s).trans_eq (by ring)⟩
  have h2 := hsum_bound
    (fun p s ↦ r ![m 0, b p, m 2, b s] * q ![m 1, b p, m 3, b s])
    (fun p s ↦ q ![m 0, b p, m 2, b s] * r ![m 1, b p, m 3, b s]) C fun p s ↦
      ⟨hpair' r q (m 0) (m 1) (m 2) (m 3) p s,
        (hpair' q r (m 0) (m 1) (m 2) (m 3) p s).trans_eq (by ring)⟩
  have h3 := hsum_bound
    (fun p s ↦ r ![m 0, b p, m 3, b s] * q ![m 1, b p, m 2, b s])
    (fun p s ↦ q ![m 0, b p, m 3, b s] * r ![m 1, b p, m 2, b s]) C fun p s ↦
      ⟨(hpair' r q (m 0) (m 1) (m 3) (m 2) p s).trans_eq (by ring),
        (hpair' q r (m 0) (m 1) (m 3) (m 2) p s).trans_eq (by ring)⟩
  have htri : ∀ a c d : ℝ, ‖(1 / 2 : ℝ) * a + c - d‖ ≤ (1 / 2 : ℝ) * ‖a‖ + ‖c‖ + ‖d‖ := by
    intro a c d
    calc ‖(1 / 2 : ℝ) * a + c - d‖
        ≤ ‖(1 / 2 : ℝ) * a + c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ ‖(1 / 2 : ℝ) * a‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖a‖ + ‖c‖ + ‖d‖ := by rw [norm_mul]; norm_num
  refine (htri _ _ _).trans ?_
  linarith

/-- The continuous symmetric bilinear polarization of the curvature reaction tensor `Q`. In every
orthonormal basis `(eᵢ)` of `V`, `reactionBilin r q` is given by
`TauCeti.FourTensor.reactionBilin_apply_orthonormalBasis`, and on the diagonal it equals
`TauCeti.FourTensor.reactionTensor`. -/
def reactionBilin :=
  LinearMap.mkContinuous₂ (reactionBilinLinear (V := V)) (5 * (Module.finrank ℝ V : ℝ) ^ 2)
    norm_reactionBilinLinear_le

private theorem reactionBilin_apply_vec (r q : FourTensor V) (u v z w : V) :
    reactionBilin r q ![u, v, z, w] = reactionBilinVal r q u v z w := by
  simp only [reactionBilin, LinearMap.mkContinuous₂_apply, reactionBilinLinear,
    LinearMap.mk₂_apply, ofLinearMap₄_apply, reactionBilinLinear₄, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

/-- In every orthonormal basis `(eᵢ)`, the bilinear polarization `reactionBilin r q` is given by
the symmetrized double metric contraction of `r` and `q`. -/
theorem reactionBilin_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r q : FourTensor V) (u v z w : V) :
    reactionBilin r q ![u, v, z, w] =
      (1 / 2 : ℝ) * (∑ p, ∑ s, (r ![u, v, b p, b s] * q ![z, w, b p, b s] +
        q ![u, v, b p, b s] * r ![z, w, b p, b s])) +
      (∑ p, ∑ s, (r ![u, b p, z, b s] * q ![v, b p, w, b s] +
        q ![u, b p, z, b s] * r ![v, b p, w, b s])) -
      (∑ p, ∑ s, (r ![u, b p, w, b s] * q ![v, b p, z, b s] +
        q ![u, b p, w, b s] * r ![v, b p, z, b s])) := by
  rw [reactionBilin_apply_vec, reactionBilinVal_eq_sum b]

/-- The bilinear polarization of the curvature reaction tensor is symmetric. -/
theorem reactionBilin_comm (r q : FourTensor V) :
    reactionBilin r q = reactionBilin q r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionBilin_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    reactionBilin_apply_orthonormalBasis (stdOrthonormalBasis ℝ V)]
  refine congrArg₂ (· - ·) (congrArg₂ (· + ·) (congrArg _ ?_) ?_) ?_ <;>
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ add_comm _ _

/-- The curvature reaction tensor `Q(r)` of the Ricci flow curvature evolution equation, defined
without choosing a basis as the diagonal `reactionBilin r r`. In every orthonormal basis `(eᵢ)`,
`Q(r)(u, v, z, w) = ∑_pq r(u, v, e_p, e_q) r(z, w, e_p, e_q) + 2 ∑_pq r(u, e_p, z, e_q)
r(v, e_p, w, e_q) - 2 ∑_pq r(u, e_p, w, e_q) r(v, e_p, z, e_q)`, see
`TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  reactionBilin r r

/-- The diagonal of `reactionBilin` is `reactionTensor`. -/
@[simp]
theorem reactionBilin_self (r : FourTensor V) : reactionBilin r r = reactionTensor r :=
  (rfl)

/-- Basis independence of the curvature reaction tensor: in every orthonormal basis `b` of `V`,
`Q(r)(u, v, z, w)` equals the contraction
`∑_pq r(u, v, b p, b q) r(z, w, b p, b q) + 2 ∑_pq r(u, b p, z, b q) r(v, b p, w, b q)
- 2 ∑_pq r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
      2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) := by
  rw [← reactionBilin_self, reactionBilin_apply_orthonormalBasis b]
  simp only [← two_mul, ← Finset.mul_sum]
  ring

/-! ### Algebraic identities -/

/-- The reaction tensor of zero is zero. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  simp [← reactionBilin_self]

/-- The reaction tensor is even: `Q(-r) = Q(r)`. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  simp [← reactionBilin_self]

/-- The reaction tensor is homogeneous of degree two: `Q(c • r) = c ^ 2 • Q(r)`. -/
@[simp]
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = (c ^ 2) • reactionTensor r := by
  simp [← reactionBilin_self, smul_smul, sq]

/-- Expansion of `reactionTensor` on a sum. -/
theorem reactionTensor_add (r q : FourTensor V) :
    reactionTensor (r + q) = reactionTensor r + (2 : ℝ) • reactionBilin r q + reactionTensor q := by
  simp only [← reactionBilin_self, map_add, add_apply, reactionBilin_comm q r, two_smul]
  abel

/-- Expansion of `reactionTensor` on a difference. -/
theorem reactionTensor_sub (r q : FourTensor V) :
    reactionTensor (r - q) = reactionTensor r - (2 : ℝ) • reactionBilin r q + reactionTensor q := by
  simp only [sub_eq_add_neg, reactionTensor_add, map_neg, reactionTensor_neg, smul_neg]

/-- Difference of two reaction tensors factored through the bilinear polarization:
`Q(r) - Q(q) = reactionBilin (r + q) (r - q)`. -/
theorem reactionTensor_sub_reactionTensor (r q : FourTensor V) :
    reactionTensor r - reactionTensor q = reactionBilin (r + q) (r - q) := by
  simp only [← reactionBilin_self, map_add, map_sub, add_apply, reactionBilin_comm q r]
  abel

/-- Polarization identity recovering `reactionBilin` from `reactionTensor`. -/
theorem reactionBilin_eq_half_sub (r q : FourTensor V) :
    reactionBilin r q =
      (1 / 2 : ℝ) • (reactionTensor (r + q) - reactionTensor r - reactionTensor q) := by
  rw [reactionTensor_add]
  have h : reactionTensor r + (2 : ℝ) • reactionBilin r q + reactionTensor q -
      reactionTensor r - reactionTensor q = (2 : ℝ) • reactionBilin r q := by abel
  rw [h, smul_smul]
  norm_num

/-! ### Regularity and Lipschitz estimates -/

/-- The curvature reaction tensor is `C^n` for every regularity order `n` (in particular smooth and
analytic). -/
@[fun_prop]
theorem contDiff_reactionTensor {n : WithTop ℕ∞} :
    ContDiff ℝ n (reactionTensor (V := V)) :=
  ContDiff.comp_continuousLinearMap
    (g := (ContinuousLinearMap.id ℝ (FourTensor V)).prod (ContinuousLinearMap.id ℝ (FourTensor V)))
    (reactionBilin (V := V)).isBoundedBilinearMap.contDiff

/-- The curvature reaction tensor is continuous. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 0)).continuous

/-- The curvature reaction tensor has strict Fréchet derivative `2 • reactionBilin r` at `r`. -/
theorem hasStrictFDerivAt_reactionTensor (r : FourTensor V) :
    HasStrictFDerivAt reactionTensor ((2 : ℝ) • reactionBilin r) r := by
  have h := (reactionBilin (V := V)).hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id r) (hasStrictFDerivAt_id r)
  have hf' :
      ((reactionBilin (V := V)).precompR (FourTensor V) r
          (ContinuousLinearMap.id ℝ (FourTensor V)) +
        (reactionBilin (V := V)).precompL (FourTensor V)
          (ContinuousLinearMap.id ℝ (FourTensor V)) r) =
      (2 : ℝ) • reactionBilin r := by
    ext q
    simp [reactionBilin_comm q r, two_smul]
  dsimp only [id_eq] at h
  rw [hf'] at h
  exact h

/-- The curvature reaction tensor has Fréchet derivative `2 • reactionBilin r` at `r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt reactionTensor ((2 : ℝ) • reactionBilin r) r :=
  (hasStrictFDerivAt_reactionTensor r).hasFDerivAt

/-- Operator-norm bound `‖reactionBilin‖ ≤ 5 * (Module.finrank ℝ V) ^ 2`. -/
theorem norm_reactionBilin_le :
    ‖reactionBilin (V := V)‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- Quadratic norm bound `‖Q(r)‖ ≤ ‖reactionBilin‖ * ‖r‖ ^ 2`. -/
theorem norm_reactionTensor_le (r : FourTensor V) :
    ‖reactionTensor r‖ ≤ ‖reactionBilin (V := V)‖ * ‖r‖ ^ 2 := by
  rw [← reactionBilin_self, sq, ← mul_assoc]
  exact (reactionBilin (V := V)).le_opNorm₂ r r

/-- Bilinear Lipschitz bound `‖Q(r) - Q(q)‖ ≤ ‖reactionBilin‖ * (‖r‖ + ‖q‖) * ‖r - q‖`. -/
theorem norm_reactionTensor_sub_le (r q : FourTensor V) :
    ‖reactionTensor r - reactionTensor q‖ ≤
      ‖reactionBilin (V := V)‖ * (‖r‖ + ‖q‖) * ‖r - q‖ := by
  rw [reactionTensor_sub_reactionTensor]
  refine ((reactionBilin (V := V)).le_opNorm₂ (r + q) (r - q)).trans ?_
  gcongr
  exact norm_add_le r q

/-- Explicit Lipschitz constant for `reactionTensor` on any closed ball `Metric.closedBall r₀ R`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (r₀ : FourTensor V) (R : ℝ≥0) :
    LipschitzOnWith (2 * ‖reactionBilin (V := V)‖₊ * (‖r₀‖₊ + R))
      reactionTensor (Metric.closedBall r₀ R) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro r hr q hq
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add, coe_nnNorm]
  have hr' : ‖r‖ ≤ ‖r₀‖ + R := by
    have := Metric.mem_closedBall.mp hr
    rw [dist_eq_norm] at this
    linarith [norm_le_insert' r r₀]
  have hq' : ‖q‖ ≤ ‖r₀‖ + R := by
    have := Metric.mem_closedBall.mp hq
    rw [dist_eq_norm] at this
    linarith [norm_le_insert' q r₀]
  refine (norm_reactionTensor_sub_le r q).trans ?_
  have hsum : ‖r‖ + ‖q‖ ≤ 2 * (‖r₀‖ + R) := by linarith
  calc ‖reactionBilin (V := V)‖ * (‖r‖ + ‖q‖) * ‖r - q‖
      ≤ ‖reactionBilin (V := V)‖ * (2 * (‖r₀‖ + R)) * ‖r - q‖ := by gcongr
    _ = 2 * ‖reactionBilin (V := V)‖ * (‖r₀‖ + R) * ‖r - q‖ := by ring

/-- The curvature reaction tensor is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) := fun r ↦
  ⟨2 * ‖reactionBilin (V := V)‖₊ * (‖r‖₊ + 1), Metric.closedBall r (1 : ℝ≥0),
    Metric.closedBall_mem_nhds r zero_lt_one, lipschitzOnWith_reactionTensor_closedBall r 1⟩

/-! ### Preservation of algebraic curvature tensors -/

/-- The reaction tensor of an algebraic curvature tensor is an algebraic curvature tensor: `Q`
preserves both pair antisymmetries, pair interchange, and the first Bianchi identity. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.reactionTensor r) := by
  let b := stdOrthonormalBasis ℝ V
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have h1 : ∑ p, ∑ q, r ![v, u, b p, b q] * r ![z, w, b p, b q] =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hr.antisymm_first v u, neg_mul]
    have h2 : ∑ p, ∑ q, r ![v, b p, z, b q] * r ![u, b p, w, b q] =
        ∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    have h3 : ∑ p, ∑ q, r ![v, b p, w, b q] * r ![u, b p, z, b q] =
        ∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [h1, h2, h3]
    ring
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have h1 : ∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q] =
        -∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] := by
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hr.antisymm_first w z, mul_neg]
    rw [h1]
    ring
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have h1 : ∑ p, ∑ q, r ![z, w, b p, b q] * r ![u, v, b p, b q] =
        ∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    have h2 : ∑ p, ∑ q, r ![z, b p, u, b q] * r ![w, b p, v, b q] =
        ∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q] := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hr.swap_pairs z (b q) u (b p), hr.swap_pairs w (b q) v (b p)]
    have h3 : ∑ p, ∑ q, r ![z, b p, v, b q] * r ![w, b p, u, b q] =
        ∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q] := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hr.swap_pairs z (b q) v (b p), hr.swap_pairs w (b q) u (b p), mul_comm]
    rw [h1, h2, h3]
  · simp only [reactionTensor_apply_orthonormalBasis b]
    have hsub13 (a c p q : V) : r ![a, p, c, q] - r ![c, p, a, q] = r ![a, c, p, q] := by
      linarith [hr.antisymm_first c p a q, hr.antisymm_first c a p q, hr.cyclic_eq_zero a p c q]
    have hsub24 (c w' p q : V) : r ![c, p, w', q] - r ![c, q, w', p] = r ![c, w', p, q] := by
      linarith [hr.antisymm_last c p w' q, hr.antisymm_last c q w' p,
        hr.antisymm_first c q p w', hr.cyclic_eq_zero c p q w', hr.swap_pairs p q c w']
    have hterm (a c d : V) :
        2 * ∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, b p, w, b q] =
          ∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, w, b p, b q] := by
      have hswap : ∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, b p, w, b q] =
          ∑ p, ∑ q, -(r ![a, c, b p, b q] * r ![d, b q, w, b p]) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        rw [hr.antisymm_last a c (b q) (b p), neg_mul]
      calc 2 * ∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, b p, w, b q]
          = (∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, b p, w, b q]) +
            (∑ p, ∑ q, -(r ![a, c, b p, b q] * r ![d, b q, w, b p])) := by rw [← hswap, two_mul]
        _ = ∑ p, ∑ q, r ![a, c, b p, b q] * (r ![d, b p, w, b q] - r ![d, b q, w, b p]) := by
            simp only [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
        _ = ∑ p, ∑ q, r ![a, c, b p, b q] * r ![d, w, b p, b q] :=
            Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [hsub24]
    have hcyc :
        (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
        (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) +
        ((∑ p, ∑ q, r ![v, b p, u, b q] * r ![z, b p, w, b q]) -
        (∑ p, ∑ q, r ![v, b p, w, b q] * r ![z, b p, u, b q])) +
        ((∑ p, ∑ q, r ![z, b p, v, b q] * r ![u, b p, w, b q]) -
        (∑ p, ∑ q, r ![z, b p, w, b q] * r ![u, b p, v, b q])) =
        -(∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, b p, w, b q]) -
        (∑ p, ∑ q, r ![v, z, b p, b q] * r ![u, b p, w, b q]) -
        (∑ p, ∑ q, r ![z, u, b p, b q] * r ![v, b p, w, b q]) := by
      simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      linear_combination
        r ![v, b p, w, b q] * (hsub13 u z (b p) (b q) + hr.antisymm_first u z (b p) (b q)) +
        r ![z, b p, w, b q] * (hsub13 v u (b p) (b q) + hr.antisymm_first v u (b p) (b q)) +
        r ![u, b p, w, b q] * (hsub13 z v (b p) (b q) + hr.antisymm_first z v (b p) (b q))
    linear_combination 2 * hcyc - hterm u v z - hterm v z u - hterm z u v

/-- The submodule of algebraic curvature tensors is invariant under `reactionTensor`. -/
theorem reactionTensor_mem_algebraicCurvatureSubmodule {r : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr (mem_algebraicCurvatureSubmodule.mp hr).reactionTensor

/-- The bilinear polarization of two algebraic curvature tensors is an algebraic curvature
tensor. -/
theorem IsAlgebraicCurvature.reactionBilin {r q : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hq : IsAlgebraicCurvature q) :
    IsAlgebraicCurvature (FourTensor.reactionBilin r q) := by
  rw [reactionBilin_eq_half_sub, ← mem_algebraicCurvatureSubmodule]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_)
  · exact reactionTensor_mem_algebraicCurvatureSubmodule
      (Submodule.add_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
        (mem_algebraicCurvatureSubmodule.mpr hq))
  · exact mem_algebraicCurvatureSubmodule.mpr hr.reactionTensor
  · exact mem_algebraicCurvatureSubmodule.mpr hq.reactionTensor

/-- The submodule of algebraic curvature tensors is closed under `reactionBilin`. -/
theorem reactionBilin_mem_algebraicCurvatureSubmodule {r q : FourTensor V}
    (hr : r ∈ algebraicCurvatureSubmodule V) (hq : q ∈ algebraicCurvatureSubmodule V) :
    reactionBilin r q ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr
    ((mem_algebraicCurvatureSubmodule.mp hr).reactionBilin
      (mem_algebraicCurvatureSubmodule.mp hq))

/-! ### Equivariance under coisometries, isometries, projections, and zero extension -/

section Equivariance

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Pulling back along any coisometry `p : V →L[ℝ] W` (that is, `p ∘L p† = id`) commutes with the
bilinear polarization `reactionBilin`. -/
theorem reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id {p : V →L[ℝ] W}
    (hp : p ∘L p.adjoint = ContinuousLinearMap.id ℝ W) (r q : FourTensor W) :
    reactionBilin (r.compContinuousLinearMap fun _ ↦ p) (q.compContinuousLinearMap fun _ ↦ p) =
      (reactionBilin r q).compContinuousLinearMap fun _ ↦ p := by
  have htrace (B : BilinForm ℝ W) :
      bilinFormTrace (B.compl₁₂ p.toLinearMap p.toLinearMap) = bilinFormTrace B := by
    let b := stdOrthonormalBasis ℝ V
    let c := stdOrthonormalBasis ℝ W
    rw [bilinFormTrace_eq_sum _ b, bilinFormTrace_eq_sum _ c]
    have hinner (k l : Fin (Module.finrank ℝ W)) :
        ∑ i, ⟪c k, p (b i)⟫_ℝ * ⟪c l, p (b i)⟫_ℝ = if k = l then 1 else 0 := by
      have hterm (i : Fin (Module.finrank ℝ V)) :
          ⟪c k, p (b i)⟫_ℝ * ⟪c l, p (b i)⟫_ℝ =
            ⟪p.adjoint (c k), b i⟫_ℝ * ⟪b i, p.adjoint (c l)⟫_ℝ := by
        rw [← ContinuousLinearMap.adjoint_inner_left p, real_inner_comm (p (b i)) (c l),
          ← ContinuousLinearMap.adjoint_inner_right p]
      simp_rw [hterm, b.sum_inner_mul_inner, ContinuousLinearMap.adjoint_inner_left]
      have hcl : p (p.adjoint (c l)) = c l := congr($hp (c l))
      rw [hcl, orthonormal_iff_ite.mp c.orthonormal k l]
    calc ∑ i, (B.compl₁₂ p.toLinearMap p.toLinearMap) (b i) (b i)
        = ∑ i, ∑ k, ∑ l, (⟪c k, p (b i)⟫_ℝ * ⟪c l, p (b i)⟫_ℝ) * B (c k) (c l) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [LinearMap.compl₁₂_apply]
          change B (p (b i)) (p (b i)) = _
          conv_lhs => rw [← c.sum_repr' (p (b i))]
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
      _ = ∑ k, ∑ l, (∑ i, ⟪c k, p (b i)⟫_ℝ * ⟪c l, p (b i)⟫_ℝ) * B (c k) (c l) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ ↦ (Finset.sum_mul ..).symm
      _ = ∑ k, B (c k) (c k) := by simp [hinner]
  have hfirst (r' q' : FourTensor W) (u v z w : V) :
      reactionFirstTerm (r'.compContinuousLinearMap fun _ ↦ p)
        (q'.compContinuousLinearMap fun _ ↦ p) u v z w =
      reactionFirstTerm r' q' (p u) (p v) (p z) (p w) := by
    rw [reactionFirstTerm, reactionFirstTerm, ← htrace]
    congr 1; ext p₁ p₂
    have hinner : reactionFirstInner (r'.compContinuousLinearMap fun _ ↦ p)
        (q'.compContinuousLinearMap fun _ ↦ p) u v z w p₁ p₂ =
        (reactionFirstInner r' q' (p u) (p v) (p z) (p w) (p p₁) (p p₂)).compl₁₂
          p.toLinearMap p.toLinearMap := by
      ext s₁ s₂
      simp only [reactionFirstInner, LinearMap.mk₂_apply, LinearMap.compl₁₂_apply,
        ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec]
    simpa [LinearMap.compl₁₂_apply, hinner] using
      htrace (reactionFirstInner r' q' (p u) (p v) (p z) (p w) (p p₁) (p p₂))
  have hsecond (r' q' : FourTensor W) (u v z w : V) :
      reactionSecondTerm (r'.compContinuousLinearMap fun _ ↦ p)
        (q'.compContinuousLinearMap fun _ ↦ p) u v z w =
      reactionSecondTerm r' q' (p u) (p v) (p z) (p w) := by
    rw [reactionSecondTerm, reactionSecondTerm, ← htrace]
    congr 1; ext p₁ p₂
    have hinner : reactionSecondInner (r'.compContinuousLinearMap fun _ ↦ p)
        (q'.compContinuousLinearMap fun _ ↦ p) u v z w p₁ p₂ =
        (reactionSecondInner r' q' (p u) (p v) (p z) (p w) (p p₁) (p p₂)).compl₁₂
          p.toLinearMap p.toLinearMap := by
      ext s₁ s₂
      simp only [reactionSecondInner, LinearMap.mk₂_apply, LinearMap.compl₁₂_apply,
        ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec]
    simpa [LinearMap.compl₁₂_apply, hinner] using
      htrace (reactionSecondInner r' q' (p u) (p v) (p z) (p w) (p p₁) (p p₂))
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec, reactionBilin_apply_vec, reactionBilin_apply_vec]
  simp only [reactionBilinVal, hfirst, hsecond]

/-- Pulling back along any coisometry `p : V →L[ℝ] W` (`p ∘L p† = id`) commutes with
`reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_of_comp_adjoint_eq_id {p : V →L[ℝ] W}
    (hp : p ∘L p.adjoint = ContinuousLinearMap.id ℝ W) (r : FourTensor W) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ p) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ p :=
  reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id hp r r

/-- Orthogonal equivariance of `reactionBilin`: pullback by a linear isometric equivalence commutes
with `reactionBilin`. -/
theorem reactionBilin_compContinuousLinearMap_linearIsometryEquiv (e : V ≃ₗᵢ[ℝ] W)
    (r q : FourTensor W) :
    reactionBilin
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (q.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilin r q).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  refine reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r q
  have h : e.toLinearIsometry.toContinuousLinearMap = (e : V →L[ℝ] W) := rfl
  rw [h, LinearIsometryEquiv.adjoint_eq_symm]
  ext w
  simp

/-- Orthogonal equivariance of `reactionTensor`: pullback by a linear isometric equivalence
commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv (e : V ≃ₗᵢ[ℝ] W)
    (r : FourTensor W) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionBilin_compContinuousLinearMap_linearIsometryEquiv e r r

/-- Pullback along the adjoint of any linear isometry `f : W →ₗᵢ[ℝ] V` commutes with
`reactionBilin`. -/
theorem reactionBilin_compContinuousLinearMap_adjoint_linearIsometry (f : W →ₗᵢ[ℝ] V)
    (r q : FourTensor W) :
    reactionBilin
        (r.compContinuousLinearMap fun _ ↦ f.toContinuousLinearMap.adjoint)
        (q.compContinuousLinearMap fun _ ↦ f.toContinuousLinearMap.adjoint) =
      (reactionBilin r q).compContinuousLinearMap fun _ ↦ f.toContinuousLinearMap.adjoint := by
  refine reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r q
  simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.one_def] using
    f.adjoint_comp_self

/-- Pullback along the adjoint of any linear isometry `f : W →ₗᵢ[ℝ] V` commutes with
`reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_adjoint_linearIsometry (f : W →ₗᵢ[ℝ] V)
    (r : FourTensor W) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ f.toContinuousLinearMap.adjoint) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ f.toContinuousLinearMap.adjoint :=
  reactionBilin_compContinuousLinearMap_adjoint_linearIsometry f r r

/-- Pulling back a four-tensor on a subspace `P` along the orthogonal projection
`P.orthogonalProjectionOnto` commutes with `reactionBilin`. -/
theorem reactionBilin_compContinuousLinearMap_orthogonalProjectionOnto (P : Submodule ℝ V)
    (r q : FourTensor P) :
    reactionBilin
        (r.compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto)
        (q.compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto) =
      (reactionBilin r q).compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto := by
  refine reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r q
  ext x
  simp [Submodule.adjoint_orthogonalProjectionOnto]

/-- Pulling back a four-tensor on a subspace `P` along the orthogonal projection
`P.orthogonalProjectionOnto` commutes with `reactionTensor`. -/
theorem reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto (P : Submodule ℝ V)
    (r : FourTensor P) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto :=
  reactionBilin_compContinuousLinearMap_orthogonalProjectionOnto P r r

/-- Zero extension from `V` to the `L²` orthogonal sum `WithLp 2 (V × W)` commutes with
`reactionBilin`. -/
theorem reactionBilin_compContinuousLinearMap_fstL (r q : FourTensor V) :
    reactionBilin
        (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V W)
        (q.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V W) =
      (reactionBilin r q).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V W := by
  refine reactionBilin_compContinuousLinearMap_of_comp_adjoint_eq_id ?_ r q
  have hadj (v : V) : (WithLp.fstL 2 ℝ V W).adjoint v = WithLp.toLp 2 (v, (0 : W)) := by
    refine ext_inner_right ℝ fun x ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [WithLp.prod_inner_apply]
  ext v
  simp [hadj]

/-- Zero extension from `V` to the `L²` orthogonal sum `WithLp 2 (V × W)` commutes with
`reactionTensor`: `Q(r ⊕ 0) = Q(r) ⊕ 0`. -/
theorem reactionTensor_compContinuousLinearMap_fstL (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V W) =
      (reactionTensor r).compContinuousLinearMap fun _ ↦ WithLp.fstL 2 ℝ V W :=
  reactionBilin_compContinuousLinearMap_fstL (W := W) r r

end Equivariance

/-! ### Explicit evaluations -/

/-- The reaction tensor of the constant-curvature tensor of the unit sphere is
`2 (n - 1)` times itself: `Q(I) = 2 (n - 1) I`, where `n = Module.finrank ℝ V`. -/
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  let b := stdOrthonormalBasis ℝ V
  have hparseval (x y : V) : ∑ p, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ = ⟪x, y⟫_ℝ := by
    simpa only [real_inner_comm y] using b.sum_inner_mul_inner x y
  have hparseval' (x y : V) : ∑ p, ⟪b p, x⟫_ℝ * ⟪b p, y⟫_ℝ = ⟪x, y⟫_ℝ := by
    simpa only [real_inner_comm (b _) x] using b.sum_inner_mul_inner x y
  have hdelta (p q : Fin (Module.finrank ℝ V)) :
      ⟪b p, b q⟫_ℝ = if p = q then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal p q
  have hterm₁ (u v z w : V) :
      ∑ p, ∑ q, constantCurvature V ![u, v, b p, b q] * constantCurvature V ![z, w, b p, b q] =
        2 * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ) := by
    simp only [constantCurvature_apply]
    have hsplit : ∀ p q,
        (⟪u, b p⟫_ℝ * ⟪v, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪v, b p⟫_ℝ) *
        (⟪z, b p⟫_ℝ * ⟪w, b q⟫_ℝ - ⟪z, b q⟫_ℝ * ⟪w, b p⟫_ℝ) =
        (⟪u, b p⟫_ℝ * ⟪z, b p⟫_ℝ) * (⟪v, b q⟫_ℝ * ⟪w, b q⟫_ℝ) -
        (⟪u, b p⟫_ℝ * ⟪w, b p⟫_ℝ) * (⟪v, b q⟫_ℝ * ⟪z, b q⟫_ℝ) -
        (⟪v, b p⟫_ℝ * ⟪z, b p⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪w, b q⟫_ℝ) +
        (⟪v, b p⟫_ℝ * ⟪w, b p⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪z, b q⟫_ℝ) := fun _ _ ↦ by ring
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hparseval]
    ring
  have hterm₂ (u v z w : V) :
      ∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q] =
        ((Module.finrank ℝ V : ℝ) - 2) * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ) + ⟪u, v⟫_ℝ * ⟪z, w⟫_ℝ := by
    simp only [constantCurvature_apply]
    have hsplit : ∀ p q,
        (⟪u, z⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪u, b q⟫_ℝ * ⟪b p, z⟫_ℝ) *
        (⟪v, w⟫_ℝ * ⟪b p, b q⟫_ℝ - ⟪v, b q⟫_ℝ * ⟪b p, w⟫_ℝ) =
        (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ) * (⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ) -
        ⟪u, z⟫_ℝ * (⟪b p, b q⟫_ℝ * ⟪v, b q⟫_ℝ * ⟪b p, w⟫_ℝ) -
        ⟪v, w⟫_ℝ * (⟪b p, b q⟫_ℝ * ⟪u, b q⟫_ℝ * ⟪b p, z⟫_ℝ) +
        (⟪b p, z⟫_ℝ * ⟪b p, w⟫_ℝ) * (⟪u, b q⟫_ℝ * ⟪v, b q⟫_ℝ) := fun _ _ ↦ by ring
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs1 : ∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪b p, b q⟫_ℝ = (Module.finrank ℝ V : ℝ) := by
      simp [hdelta]
    have hs2 (x y : V) : ∑ p, ∑ q, ⟪b p, b q⟫_ℝ * ⟪x, b q⟫_ℝ * ⟪b p, y⟫_ℝ = ⟪x, y⟫_ℝ := by
      simp [hdelta, b.sum_inner_mul_inner]
    simp_rw [hs1, hs2, hparseval, ← Finset.sum_mul, hparseval']
    ring
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul,
    constantCurvature_apply, hterm₁, hterm₂, hterm₂, real_inner_comm (m 3) (m 2)]
  ring

/-- The reaction tensor of the curvature tensor of `S^k × ℝ^(n - k)`, modeled as the pullback of
`constantCurvature P` along the orthogonal projection onto a subspace `P`, is
`2 (finrank ℝ P - 1)` times itself. -/
theorem reactionTensor_constantCurvature_orthogonalProjectionOnto
    (P : Submodule ℝ V) :
    reactionTensor ((constantCurvature P).compContinuousLinearMap
      fun _ ↦ P.orthogonalProjectionOnto) =
      (2 * ((Module.finrank ℝ P : ℝ) - 1)) •
        ((constantCurvature P).compContinuousLinearMap fun _ ↦ P.orthogonalProjectionOnto) := by
  rw [reactionTensor_compContinuousLinearMap_orthogonalProjectionOnto,
    reactionTensor_constantCurvature]
  ext m
  simp

/-- For any rank-one four-tensor `r(u, v, z, w) = ω(u, v) ω(z, w)`, the second and third
contractions of `Q(r)` cancel identically and `Q(r)` is `∑_pq ω(e_p, e_q)^2` times `r`. -/
theorem reactionTensor_eq_of_apply_eq_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (ω : V → V → ℝ)
    (hr : ∀ u v z w, r ![u, v, z, w] = ω u v * ω z w) :
    reactionTensor r = (∑ p, ∑ q, ω (b p) (b q) ^ 2) • r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionTensor_apply_orthonormalBasis b, smul_apply, smul_eq_mul]
  simp only [hr]
  have h1 : ∑ p, ∑ q, ω (m 0) (m 1) * ω (b p) (b q) * (ω (m 2) (m 3) * ω (b p) (b q)) =
      (∑ p, ∑ q, ω (b p) (b q) ^ 2) * (ω (m 0) (m 1) * ω (m 2) (m 3)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    ring
  have h23 :
      ∑ p, ∑ q, ω (m 0) (b p) * ω (m 2) (b q) * (ω (m 1) (b p) * ω (m 3) (b q)) =
      ∑ p, ∑ q, ω (m 0) (b p) * ω (m 3) (b q) * (ω (m 1) (b p) * ω (m 2) (b q)) :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring
  rw [h1, h23]
  ring

/-- For the rank-one curvature tensor `r(u, v, z, w) = (⟪e₁, u⟫ ⟪e₂, v⟫ - ⟪e₁, v⟫ ⟪e₂, u⟫)
(⟪e₁, z⟫ ⟪e₂, w⟫ - ⟪e₁, w⟫ ⟪e₂, z⟫)` associated to two vectors `e₁, e₂ : V`, the reaction tensor
is `2 (‖e₁‖ ^ 2 * ‖e₂‖ ^ 2 - ⟪e₁, e₂⟫ ^ 2)` times `r`. -/
theorem reactionTensor_eq_of_apply_eq_det_mul_det {r : FourTensor V} (e₁ e₂ : V)
    (hr : ∀ u v z w, r ![u, v, z, w] =
      (⟪e₁, u⟫_ℝ * ⟪e₂, v⟫_ℝ - ⟪e₁, v⟫_ℝ * ⟪e₂, u⟫_ℝ) *
      (⟪e₁, z⟫_ℝ * ⟪e₂, w⟫_ℝ - ⟪e₁, w⟫_ℝ * ⟪e₂, z⟫_ℝ)) :
    reactionTensor r = (2 * (‖e₁‖ ^ 2 * ‖e₂‖ ^ 2 - ⟪e₁, e₂⟫_ℝ ^ 2)) • r := by
  let b := stdOrthonormalBasis ℝ V
  let ω : V → V → ℝ := fun u v ↦ ⟪e₁, u⟫_ℝ * ⟪e₂, v⟫_ℝ - ⟪e₁, v⟫_ℝ * ⟪e₂, u⟫_ℝ
  rw [reactionTensor_eq_of_apply_eq_mul b ω hr]
  congr 1
  have hparseval (x y : V) : ∑ p, ⟪x, b p⟫_ℝ * ⟪y, b p⟫_ℝ = ⟪x, y⟫_ℝ := by
    simpa only [real_inner_comm y] using b.sum_inner_mul_inner x y
  have hsplit : ∀ p q, ω (b p) (b q) ^ 2 =
      (⟪e₁, b p⟫_ℝ * ⟪e₁, b p⟫_ℝ) * (⟪e₂, b q⟫_ℝ * ⟪e₂, b q⟫_ℝ) -
      2 * ((⟪e₁, b p⟫_ℝ * ⟪e₂, b p⟫_ℝ) * (⟪e₁, b q⟫_ℝ * ⟪e₂, b q⟫_ℝ)) +
      (⟪e₂, b p⟫_ℝ * ⟪e₂, b p⟫_ℝ) * (⟪e₁, b q⟫_ℝ * ⟪e₁, b q⟫_ℝ) := fun _ _ ↦ by
    dsimp only [ω]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hparseval, real_inner_self_eq_norm_sq]
  ring

/-- For the rank-one curvature tensor of `S² × ℝ^(n - 2)` associated to an orthonormal pair
`e₁, e₂`, `Q(r) = 2 r`. -/
theorem reactionTensor_eq_two_smul_of_orthonormal_pair {r : FourTensor V} {e₁ e₂ : V}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    (hr : ∀ u v z w, r ![u, v, z, w] =
      (⟪e₁, u⟫_ℝ * ⟪e₂, v⟫_ℝ - ⟪e₁, v⟫_ℝ * ⟪e₂, u⟫_ℝ) *
      (⟪e₁, z⟫_ℝ * ⟪e₂, w⟫_ℝ - ⟪e₁, w⟫_ℝ * ⟪e₂, z⟫_ℝ)) :
    reactionTensor r = (2 : ℝ) • r := by
  rw [reactionTensor_eq_of_apply_eq_det_mul_det e₁ e₂ hr, h₁, h₂, h₁₂]
  norm_num

end FourTensor

end TauCeti
