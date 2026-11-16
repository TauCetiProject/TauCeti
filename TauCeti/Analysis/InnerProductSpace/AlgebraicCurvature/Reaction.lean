/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import TauCeti.Analysis.InnerProductSpace.Trace.Basic

/-!
# The algebraic curvature reaction tensor

Under the Ricci flow, the Riemann curvature four-tensor evolves by a heat equation with a purely
algebraic quadratic reaction term `Q(r)` determined pointwise on each tangent space. On a
finite-dimensional real inner product space `V`, we define the symmetric continuous bilinear
polarization `TauCeti.FourTensor.reactionBilin V` via `TauCeti.bilinFormTrace` (so that it is
manifestly independent of any choice of orthonormal basis) and set
`TauCeti.FourTensor.reactionTensor r = reactionBilin V r r`.

In any orthonormal basis `(eₚ)` of `V`,
```
Q(r)(u, v, z, w) = ∑ₚ ∑_q r(u, v, eₚ, e_q) r(z, w, eₚ, e_q)
                 + 2 ∑ₚ ∑_q r(u, eₚ, z, e_q) r(v, eₚ, w, e_q)
                 - 2 ∑ₚ ∑_q r(u, eₚ, w, e_q) r(v, eₚ, z, e_q).
```
We show that `reactionTensor` and `reactionBilin` preserve the algebraic curvature symmetries
(including the first Bianchi identity), are equivariant under pullback by adjoints of linear
isometries — in particular under linear isometric equivalences (`O(V)`) and zero-extensions — and
are smooth (`C^ω`), with Fréchet derivative `2 • reactionBilin V r` and an explicit Lipschitz
constant on every closed ball. Hamilton's `#` product and the bivector-operator identity
`Q(R) = 2 (R² + R#)` are established in
`TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Sharp`.

## Main definitions

* `TauCeti.FourTensor.reactionBilin`: the symmetric continuous bilinear polarization of the
  algebraic curvature reaction term.
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction tensor `Q(r) = reactionBilin V r r`.

## Main statements

* `TauCeti.FourTensor.reactionTensor_apply_orthonormalBasis`: the three-term formula for `Q(r)` in
  any orthonormal basis.
* `TauCeti.FourTensor.IsAlgebraicCurvature.reactionTensor` and
  `TauCeti.FourTensor.reactionTensor_mem`: `Q` maps `algebraicCurvatureSubmodule V` into itself.
* `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_adjoint` and
  `TauCeti.FourTensor.reactionTensor_compContinuousLinearMap_linearIsometryEquiv`: equivariance
  under adjoints of linear isometries and under `O(V)`.
* `TauCeti.FourTensor.contDiff_reactionTensor`, `TauCeti.FourTensor.continuous_reactionTensor`,
  `TauCeti.FourTensor.hasFDerivAt_reactionTensor`, `TauCeti.FourTensor.norm_reactionBilin_le`,
  `TauCeti.FourTensor.lipschitzOnWith_reactionTensor_closedBall`, and
  `TauCeti.FourTensor.locallyLipschitz_reactionTensor`: regularity, operator-norm, and Lipschitz
  estimates for the reaction ODE.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. 167 (2008), 1079–1097, Section 2.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped ContDiff NNReal RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Basis-free definition of the reaction tensor -/

/-- Outer bilinear form `(p₁, p₂) ↦ tr_q (B₁(p₁, q) B₂(p₂, q))` for double contraction of two
bilinear forms. -/
private def doubleTraceOuter (B₁ B₂ : BilinForm ℝ V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun p₁ p₂ ↦ bilinFormTrace ((LinearMap.mul ℝ ℝ).compl₁₂ (B₁ p₁) (B₂ p₂)))
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; ext _ _; simp)
    (fun _ _ _ ↦ by rw [← map_smul]; congr 1; ext _ _; simp [mul_assoc])
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; ext _ _; simp [mul_add])
    (fun _ _ _ ↦ by rw [← map_smul]; congr 1; ext _ _; simp [mul_left_comm])

/-- Basis-free double metric contraction `∑ p q, B₁(eₚ, e_q) B₂(eₚ, e_q)` of two bilinear forms. -/
private def doubleTrace (B₁ B₂ : BilinForm ℝ V) : ℝ :=
  bilinFormTrace (doubleTraceOuter B₁ B₂)

private theorem doubleTrace_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B₁ B₂ : BilinForm ℝ V) :
    doubleTrace B₁ B₂ = ∑ p, ∑ q, B₁ (b p) (b q) * B₂ (b p) (b q) := by
  simp only [doubleTrace, bilinFormTrace_eq_sum _ b, doubleTraceOuter, LinearMap.mk₂_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply']

private theorem doubleTrace_comp_adjoint {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) (B₁ B₂ : BilinForm ℝ W) :
    doubleTrace
        (B₁.comp (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap
          (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap)
        (B₂.comp (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap
          (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap) =
      doubleTrace B₁ B₂ := by
  rw [doubleTrace, doubleTrace, ← bilinFormTrace_comp_adjoint f]
  congr 1; ext _ _
  simp only [doubleTraceOuter, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply]
  rw [← bilinFormTrace_comp_adjoint f]
  congr 1

private theorem norm_doubleTrace_le {B₁ B₂ : BilinForm ℝ V} {C : ℝ}
    (h : ∀ p q, ‖p‖ = 1 → ‖q‖ = 1 → ‖B₁ p q * B₂ p q‖ ≤ C) :
    ‖doubleTrace B₁ B₂‖ ≤ (Module.finrank ℝ V : ℝ) ^ 2 * C := by
  let b := stdOrthonormalBasis ℝ V
  rw [doubleTrace_eq_sum b]
  calc
    ‖∑ p, ∑ q, B₁ (b p) (b q) * B₂ (b p) (b q)‖
        ≤ ∑ p, ∑ q, ‖B₁ (b p) (b q) * B₂ (b p) (b q)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _p : Fin (Module.finrank ℝ V), ∑ _q : Fin (Module.finrank ℝ V), C :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun q _ ↦
            h (b p) (b q) (b.orthonormal.1 p) (b.orthonormal.1 q)
    _ = (Module.finrank ℝ V : ℝ) ^ 2 * C := by
          simp [Finset.sum_const, nsmul_eq_mul, sq, mul_assoc]

/-- The bilinear slice `(p, q) ↦ r(u, v, p, q)` of a four-tensor. -/
private def sliceLast (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun p q ↦ r ![u, v, p, q])
    (fun _ _ _ ↦ apply_add_third r ..) (fun _ _ _ ↦ by simp [apply_smul_third])
    (fun _ _ _ ↦ apply_add_fourth r ..) (fun _ _ _ ↦ by simp [apply_smul_fourth])

/-- The bilinear slice `(p, q) ↦ r(u, p, z, q)` of a four-tensor. -/
private def sliceEven (r : FourTensor V) (u z : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun p q ↦ r ![u, p, z, q])
    (fun _ _ _ ↦ apply_add_second r ..) (fun _ _ _ ↦ by simp [apply_smul_second])
    (fun _ _ _ ↦ apply_add_fourth r ..) (fun _ _ _ ↦ by simp [apply_smul_fourth])

/-- First quadratic contraction `∑ p q, r(u, v, eₚ, e_q) s(z, w, eₚ, e_q)`. -/
private def contractA (r s : FourTensor V) (u v z w : V) : ℝ :=
  doubleTrace (sliceLast r u v) (sliceLast s z w)

/-- Second quadratic contraction `∑ p q, r(u, eₚ, z, e_q) s(v, eₚ, w, e_q)`. -/
private def contractB (r s : FourTensor V) (u v z w : V) : ℝ :=
  doubleTrace (sliceEven r u z) (sliceEven s v w)

private theorem contractA_comp_adjoint {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) (r s : FourTensor W) (u v z w : V) :
    contractA
        (r.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap)
        u v z w =
      contractA r s
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap u)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap v)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap z)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap w) := by
  rw [contractA, contractA, ← doubleTrace_comp_adjoint f]
  congr 1 <;> (ext _ _; simp only [sliceLast, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec])

private theorem contractB_comp_adjoint {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) (r s : FourTensor W) (u v z w : V) :
    contractB
        (r.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap)
        u v z w =
      contractB r s
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap u)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap v)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap z)
        (ContinuousLinearMap.adjoint f.toContinuousLinearMap w) := by
  rw [contractB, contractB, ← doubleTrace_comp_adjoint f]
  congr 1 <;> (ext _ _; simp only [sliceEven, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec])

/-- Pointwise value of the symmetric bilinear reaction form `reactionBilin V r s`. -/
private def reactionVal (r s : FourTensor V) (u v z w : V) : ℝ :=
  (1 / 2 : ℝ) *
    ((contractA r s u v z w + 2 * contractB r s u v z w - 2 * contractB r s u v w z) +
     (contractA s r u v z w + 2 * contractB s r u v z w - 2 * contractB s r u v w z))

private theorem reactionVal_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    reactionVal r s u v z w =
      (1 / 2 : ℝ) *
        (((∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
          2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
          2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q])) +
         ((∑ p, ∑ q, s ![u, v, b p, b q] * r ![z, w, b p, b q]) +
          2 * (∑ p, ∑ q, s ![u, b p, z, b q] * r ![v, b p, w, b q]) -
          2 * (∑ p, ∑ q, s ![u, b p, w, b q] * r ![v, b p, z, b q]))) := by
  simp only [reactionVal, contractA, contractB, doubleTrace_eq_sum b, sliceLast, sliceEven,
    LinearMap.mk₂_apply]

/-- `reactionVal r s` as a curried four-linear form on `V`. -/
private def reactionLinear (r s : FourTensor V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ (fun z w ↦ reactionVal r s u v z w)
      (fun _ _ _ ↦ by simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first,
        apply_add_third, add_mul, mul_add, Finset.sum_add_distrib]; ring)
      (fun c _ _ ↦ by
        have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, apply_smul_third,
          smul_eq_mul, mul_assoc, hm, ← Finset.mul_sum]; ring)
      (fun _ _ _ ↦ by simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_second,
        apply_add_third, add_mul, mul_add, Finset.sum_add_distrib]; ring)
      (fun c _ _ ↦ by
        have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_second,
          apply_smul_third, smul_eq_mul, mul_assoc, hm, ← Finset.mul_sum]; ring))
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first, add_mul,
      Finset.sum_add_distrib]; ring)
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, mul_assoc,
      ← Finset.mul_sum]; ring)
    (fun _ _ _ ↦ by ext _ _; simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first, apply_add_second, add_mul,
      mul_add, Finset.sum_add_distrib]; ring)
    (fun c _ _ ↦ by
      ext _ _
      have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, apply_smul_second,
        mul_assoc, hm, ← Finset.mul_sum]; ring)

private theorem norm_contractA_le (r s : FourTensor V) (u v z w : V) :
    ‖contractA r s u v z w‖ ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖)) :=
  norm_doubleTrace_le fun p q hp hq ↦ by
    have hr : ‖r ![u, v, p, q]‖ ≤ ‖r‖ * (‖u‖ * ‖v‖) := by
      simpa [Fin.prod_univ_four, hp, hq] using r.le_opNorm ![u, v, p, q]
    have hs : ‖s ![z, w, p, q]‖ ≤ ‖s‖ * (‖z‖ * ‖w‖) := by
      simpa [Fin.prod_univ_four, hp, hq] using s.le_opNorm ![z, w, p, q]
    simp only [sliceLast, LinearMap.mk₂_apply, norm_mul]
    calc ‖r ![u, v, p, q]‖ * ‖s ![z, w, p, q]‖
        ≤ (‖r‖ * (‖u‖ * ‖v‖)) * (‖s‖ * (‖z‖ * ‖w‖)) := by gcongr
      _ = ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by ring

private theorem norm_contractB_le (r s : FourTensor V) (u v z w : V) :
    ‖contractB r s u v z w‖ ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * (‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖)) :=
  norm_doubleTrace_le fun p q hp hq ↦ by
    have hr : ‖r ![u, p, z, q]‖ ≤ ‖r‖ * (‖u‖ * ‖z‖) := by
      simpa [Fin.prod_univ_four, hp, hq] using r.le_opNorm ![u, p, z, q]
    have hs : ‖s ![v, p, w, q]‖ ≤ ‖s‖ * (‖v‖ * ‖w‖) := by
      simpa [Fin.prod_univ_four, hp, hq] using s.le_opNorm ![v, p, w, q]
    simp only [sliceEven, LinearMap.mk₂_apply, norm_mul]
    calc ‖r ![u, p, z, q]‖ * ‖s ![v, p, w, q]‖
        ≤ (‖r‖ * (‖u‖ * ‖z‖)) * (‖s‖ * (‖v‖ * ‖w‖)) := by gcongr
      _ = ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by ring

private def reactionBilinLinear : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V where
  toFun r :=
    { toFun := fun s ↦ ofLinearMap₄ (reactionLinear r s)
      map_add' := fun _ _ ↦ by
        ext _; simp only [ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, add_apply,
          reactionVal_eq_sum (stdOrthonormalBasis ℝ V), add_mul, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c _ ↦ by
        ext _; have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, smul_apply,
          RingHom.id_apply, smul_eq_mul, reactionVal_eq_sum (stdOrthonormalBasis ℝ V),
          mul_assoc, hm, ← Finset.mul_sum]; ring }
  map_add' _ _ := by
    ext _ _; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, ofLinearMap₄_apply,
      reactionLinear, LinearMap.mk₂_apply, add_apply,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c _ := by
    ext _ _; have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, smul_apply, smul_eq_mul,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), mul_assoc, hm, ← Finset.mul_sum]; ring

private theorem norm_reactionBilinLinear_le (r s : FourTensor V) :
    ‖reactionBilinLinear r s‖ ≤ (5 * (Module.finrank ℝ V : ℝ) ^ 2) * ‖r‖ * ‖s‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hval : reactionBilinLinear r s m = reactionVal r s (m 0) (m 1) (m 2) (m 3) := by
    simp [reactionBilinLinear, reactionLinear]
  rw [hval, reactionVal, Fin.prod_univ_four]
  have h1 (a b c : ℝ) : ‖a + 2 * b - 2 * c‖ ≤ ‖a‖ + 2 * ‖b‖ + 2 * ‖c‖ := by
    have hsub := norm_sub_le (a + 2 * b) (2 * c)
    have hadd := norm_add_le a (2 * b)
    simp only [norm_mul, Real.norm_ofNat] at hsub hadd; linarith
  have hhalf (x y : FourTensor V) :
      ‖contractA x y (m 0) (m 1) (m 2) (m 3) + 2 * contractB x y (m 0) (m 1) (m 2) (m 3) -
          2 * contractB x y (m 0) (m 1) (m 3) (m 2)‖ ≤
        5 * (Module.finrank ℝ V : ℝ) ^ 2 * ‖x‖ * ‖y‖ * (‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖) := by
    have hA := norm_contractA_le x y (m 0) (m 1) (m 2) (m 3)
    have hB1 := norm_contractB_le x y (m 0) (m 1) (m 2) (m 3)
    have hB2 := norm_contractB_le x y (m 0) (m 1) (m 3) (m 2)
    have ht := h1 (contractA x y (m 0) (m 1) (m 2) (m 3)) (contractB x y (m 0) (m 1) (m 2) (m 3))
      (contractB x y (m 0) (m 1) (m 3) (m 2))
    linarith [show ‖m 0‖ * ‖m 1‖ * ‖m 3‖ * ‖m 2‖ = ‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖ by ring]
  have htri := (norm_add_le _ _).trans (add_le_add (hhalf r s) (hhalf s r))
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  linarith [show ‖s‖ * ‖r‖ = ‖r‖ * ‖s‖ from mul_comm _ _]

variable (V) in
/-- The symmetric continuous bilinear polarization of the algebraic curvature reaction tensor.
Its diagonal `reactionBilin V r r` is `reactionTensor r`. -/
def reactionBilin :=
  LinearMap.mkContinuous₂ (reactionBilinLinear (V := V)) (5 * (Module.finrank ℝ V : ℝ) ^ 2)
    (norm_reactionBilinLinear_le (V := V))

/-- The quadratic reaction tensor `Q(r) = reactionBilin V r r` of the Ricci flow curvature
evolution equation. -/
def reactionTensor (r : FourTensor V) : FourTensor V :=
  reactionBilin V r r

private theorem reactionBilin_apply_val (r s : FourTensor V) (u v z w : V) :
    reactionBilin V r s ![u, v, z, w] = reactionVal r s u v z w := by
  simp [reactionBilin, reactionBilinLinear, reactionLinear]

/-- In any orthonormal basis `b`, the polarized reaction tensor is the symmetrization of the three
quadratic contractions. -/
theorem reactionBilin_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r s : FourTensor V) (u v z w : V) :
    reactionBilin V r s ![u, v, z, w] =
      (1 / 2 : ℝ) *
        (((∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]) +
          2 * (∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]) -
          2 * (∑ p, ∑ q, r ![u, b p, w, b q] * s ![v, b p, z, b q])) +
         ((∑ p, ∑ q, s ![u, v, b p, b q] * r ![z, w, b p, b q]) +
          2 * (∑ p, ∑ q, s ![u, b p, z, b q] * r ![v, b p, w, b q]) -
          2 * (∑ p, ∑ q, s ![u, b p, w, b q] * r ![v, b p, z, b q]))) := by
  rw [reactionBilin_apply_val, reactionVal_eq_sum b]

/-- In any orthonormal basis `b`, the reaction tensor `Q(r)` is given by
`∑ p q, r(u, v, b p, b q) r(z, w, b p, b q) + 2 ∑ p q, r(u, b p, z, b q) r(v, b p, w, b q)
  - 2 ∑ p q, r(u, b p, w, b q) r(v, b p, z, b q)`. -/
theorem reactionTensor_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (u v z w : V) :
    reactionTensor r ![u, v, z, w] =
      (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) +
        2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) := by
  rw [reactionTensor, reactionBilin_apply_orthonormalBasis b]
  ring

/-! ### Algebraic identities -/

/-- `reactionBilin` is symmetric in its two tensor arguments. -/
theorem reactionBilin_comm (r s : FourTensor V) : reactionBilin V r s = reactionBilin V s r := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionBilin_apply_val, reactionBilin_apply_val, reactionVal, reactionVal]
  ring

/-- The diagonal of `reactionBilin` is `reactionTensor`. -/
@[simp]
theorem reactionBilin_self (r : FourTensor V) : reactionBilin V r r = reactionTensor r :=
  (rfl)

/-- The reaction tensor of `0` is `0`. -/
@[simp]
theorem reactionTensor_zero : reactionTensor (0 : FourTensor V) = 0 := by
  simp [reactionTensor]

/-- The reaction tensor is even: `Q(-r) = Q(r)`. -/
@[simp]
theorem reactionTensor_neg (r : FourTensor V) : reactionTensor (-r) = reactionTensor r := by
  simp only [reactionTensor, map_neg, neg_apply, neg_neg]

/-- The reaction tensor is homogeneous of degree `2`: `Q(c • r) = c ^ 2 • Q(r)`. -/
@[simp]
theorem reactionTensor_smul (c : ℝ) (r : FourTensor V) :
    reactionTensor (c • r) = (c ^ 2) • reactionTensor r := by
  simp only [reactionTensor, map_smul, smul_apply, smul_smul, sq]

/-- Expansion of `reactionTensor` on a sum. -/
theorem reactionTensor_add (r s : FourTensor V) :
    reactionTensor (r + s) =
      reactionTensor r + (2 : ℝ) • reactionBilin V r s + reactionTensor s := by
  simp only [reactionTensor, map_add, add_apply, reactionBilin_comm s r, two_smul]
  abel

/-- Expansion of `reactionTensor` on a difference. -/
theorem reactionTensor_sub (r s : FourTensor V) :
    reactionTensor (r - s) =
      reactionTensor r - (2 : ℝ) • reactionBilin V r s + reactionTensor s := by
  simp only [reactionTensor, map_sub, sub_apply, reactionBilin_comm s r, two_smul]
  abel

/-- Difference-of-squares factorization `Q(r) - Q(s) = reactionBilin V (r + s) (r - s)`. -/
theorem reactionTensor_sub_reactionTensor (r s : FourTensor V) :
    reactionTensor r - reactionTensor s = reactionBilin V (r + s) (r - s) := by
  simp only [reactionTensor, map_add, map_sub, add_apply, reactionBilin_comm s r]
  abel

/-- Polarization identity recovering `reactionBilin` from `reactionTensor`. -/
theorem reactionBilin_eq_polarization (r s : FourTensor V) :
    reactionBilin V r s = (1 / 4 : ℝ) • (reactionTensor (r + s) - reactionTensor (r - s)) := by
  rw [reactionTensor_add, reactionTensor_sub]
  have h : reactionTensor r + (2 : ℝ) • reactionBilin V r s + reactionTensor s -
      (reactionTensor r - (2 : ℝ) • reactionBilin V r s + reactionTensor s) =
      (4 : ℝ) • reactionBilin V r s := by
    module
  rw [h, smul_smul]
  norm_num

/-! ### Preservation of algebraic curvature symmetries -/

/-- If `r` is antisymmetric in its first pair, then `Q(r)` is antisymmetric in its first pair. -/
theorem reactionTensor_antisymm_first {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = -reactionTensor r ![v, u, z, w] := by
  let b := stdOrthonormalBasis ℝ V
  rw [reactionTensor_apply_orthonormalBasis b, reactionTensor_apply_orthonormalBasis b]
  have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      -(∑ p, ∑ q, r ![v, u, b p, b q] * r ![z, w, b p, b q]) := by
    simp_rw [← Finset.sum_neg_distrib, h₁ u v, neg_mul]
  have hB : (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ∑ p, ∑ q, r ![v, b p, w, b q] * r ![u, b p, z, b q] := by simp_rw [mul_comm]
  have hC : (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ∑ p, ∑ q, r ![v, b p, z, b q] * r ![u, b p, w, b q] := by simp_rw [mul_comm]
  rw [hA, hB, hC]; ring

/-- If `r` is antisymmetric in its first pair, then `Q(r)` is antisymmetric in its last pair. -/
theorem reactionTensor_antisymm_last {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = -reactionTensor r ![u, v, w, z] := by
  let b := stdOrthonormalBasis ℝ V
  rw [reactionTensor_apply_orthonormalBasis b, reactionTensor_apply_orthonormalBasis b]
  have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      -(∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q]) := by
    simp_rw [← Finset.sum_neg_distrib, h₁ z w, mul_neg]
  rw [hA]; ring

/-- If `r` is symmetric under pair interchange, then so is `Q(r)`. -/
theorem reactionTensor_swap_pairs {r : FourTensor V}
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = reactionTensor r ![z, w, u, v] := by
  let b := stdOrthonormalBasis ℝ V
  rw [reactionTensor_apply_orthonormalBasis b, reactionTensor_apply_orthonormalBasis b]
  have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      ∑ p, ∑ q, r ![z, w, b p, b q] * r ![u, v, b p, b q] := by simp_rw [mul_comm]
  have hB : (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ∑ p, ∑ q, r ![z, b p, u, b q] * r ![w, b p, v, b q] := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hswap u (b q) z (b p), hswap v (b q) w (b p)]
  have hC : (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ∑ p, ∑ q, r ![z, b p, v, b q] * r ![w, b p, u, b q] := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hswap u (b q) w (b p), hswap v (b q) z (b p), mul_comm]
  rw [hA, hB, hC]

omit [FiniteDimensional ℝ V] in
/-- Bianchi contraction step: for an algebraic curvature tensor `r`,
`2 ∑ p q, (r(x, b p, y, b q) - r(y, b p, x, b q)) r(t, b p, w, b q)` equals
`∑ p q, r(x, y, b p, b q) r(t, w, b p, b q)`. -/
private theorem reactionTensor_bianchi_term {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (x y t w : V) :
    2 * (∑ p, ∑ q, (r ![x, b p, y, b q] - r ![y, b p, x, b q]) * r ![t, b p, w, b q]) =
      ∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, w, b p, b q] := by
  have h1 (p q) : r ![x, b p, y, b q] - r ![y, b p, x, b q] = r ![x, y, b p, b q] := by
    have hc := hr.cyclic_eq_zero x (b p) y (b q)
    rw [hr.antisymm_first (b p) y x (b q), hr.antisymm_first y x (b p) (b q)] at hc; linarith
  have h2 (p q) : r ![t, b p, w, b q] - r ![t, b q, w, b p] = r ![t, w, b p, b q] := by
    have hc := hr.cyclic_eq_zero t (b p) w (b q)
    rw [hr.swap_pairs (b p) w t (b q), hr.antisymm_last t (b q) (b p) w,
      hr.antisymm_first w t (b p) (b q)] at hc; linarith
  have hswap : (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) =
      -(∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b q, w, b p]) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hr.antisymm_last x y (b q) (b p), neg_mul]
  calc
    2 * (∑ p, ∑ q, (r ![x, b p, y, b q] - r ![y, b p, x, b q]) * r ![t, b p, w, b q])
        = (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) +
            (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) := by simp only [h1]; ring
    _ = ∑ p, ∑ q, r ![x, y, b p, b q] * (r ![t, b p, w, b q] - r ![t, b q, w, b p]) := by
          conv_rhs => simp only [mul_sub, Finset.sum_sub_distrib]
          rw [hswap]; ring
    _ = ∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, w, b p, b q] := by simp only [h2]

/-- The reaction tensor of an algebraic curvature tensor is again an algebraic curvature tensor. -/
theorem IsAlgebraicCurvature.reactionTensor {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (reactionTensor r) := by
  refine ⟨reactionTensor_antisymm_first hr.antisymm_first,
    reactionTensor_antisymm_last hr.antisymm_first,
    reactionTensor_swap_pairs hr.swap_pairs, fun u v z w ↦ ?_⟩
  let b := stdOrthonormalBasis ℝ V
  simp only [reactionTensor_apply_orthonormalBasis b]
  have hgroup :
      2 * (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) +
      (2 * (∑ p, ∑ q, r ![v, b p, u, b q] * r ![z, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![v, b p, w, b q] * r ![z, b p, u, b q])) +
      (2 * (∑ p, ∑ q, r ![z, b p, v, b q] * r ![u, b p, w, b q]) -
        2 * (∑ p, ∑ q, r ![z, b p, w, b q] * r ![u, b p, v, b q])) =
      2 * (∑ p, ∑ q, (r ![u, b p, z, b q] - r ![z, b p, u, b q]) * r ![v, b p, w, b q]) +
      2 * (∑ p, ∑ q, (r ![v, b p, u, b q] - r ![u, b p, v, b q]) * r ![z, b p, w, b q]) +
      2 * (∑ p, ∑ q, (r ![z, b p, v, b q] - r ![v, b p, z, b q]) * r ![u, b p, w, b q]) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    have hm (x y t : V) : (∑ p, ∑ q, r ![x, b p, w, b q] * r ![y, b p, t, b q]) =
        ∑ p, ∑ q, r ![y, b p, t, b q] * r ![x, b p, w, b q] := by simp_rw [mul_comm]
    rw [hm u v z, hm v z u, hm z u v]; ring
  have hneg (x y t : V) : (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, w, b p, b q]) =
      -(∑ p, ∑ q, r ![y, x, b p, b q] * r ![t, w, b p, b q]) := by
    simp_rw [← Finset.sum_neg_distrib, hr.antisymm_first x y, neg_mul]
  have h1 := reactionTensor_bianchi_term b hr u z v w
  have h2 := reactionTensor_bianchi_term b hr v u z w
  have h3 := reactionTensor_bianchi_term b hr z v u w
  rw [hneg u z v] at h1; rw [hneg v u z] at h2; rw [hneg z v u] at h3
  linarith

/-- `reactionTensor` maps the submodule of algebraic curvature tensors into itself. -/
theorem reactionTensor_mem {r : FourTensor V} (hr : r ∈ algebraicCurvatureSubmodule V) :
    reactionTensor r ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr
    (IsAlgebraicCurvature.reactionTensor (mem_algebraicCurvatureSubmodule.mp hr))

/-- The polarized reaction tensor preserves `IsAlgebraicCurvature`. -/
theorem IsAlgebraicCurvature.reactionBilin {r s : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hs : IsAlgebraicCurvature s) : IsAlgebraicCurvature (reactionBilin V r s) := by
  rw [reactionBilin_eq_polarization]
  exact mem_algebraicCurvatureSubmodule.mp (Submodule.smul_mem _ _ (Submodule.sub_mem _
    (reactionTensor_mem (Submodule.add_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr hs)))
    (reactionTensor_mem (Submodule.sub_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr hs)))))

/-- `reactionBilin` maps pairs of algebraic curvature tensors into
`algebraicCurvatureSubmodule V`. -/
theorem reactionBilin_mem {r s : FourTensor V} (hr : r ∈ algebraicCurvatureSubmodule V)
    (hs : s ∈ algebraicCurvatureSubmodule V) :
    reactionBilin V r s ∈ algebraicCurvatureSubmodule V :=
  mem_algebraicCurvatureSubmodule.mpr
    (IsAlgebraicCurvature.reactionBilin (mem_algebraicCurvatureSubmodule.mp hr)
      (mem_algebraicCurvatureSubmodule.mp hs))

/-! ### Equivariance under coisometries and linear isometric equivalences -/

/-- `reactionBilin` commutes with pullback along the adjoint of any linear isometry (including
zero-extensions from a subspace and pullbacks by orthogonal equivalences). -/
theorem reactionBilin_compContinuousLinearMap_adjoint {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) (r s : FourTensor W) :
    reactionBilin V
        (r.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap) =
      (reactionBilin W r s).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, compContinuousLinearMap_apply_vec, reactionBilin_apply_val, reactionBilin_apply_val]
  simp only [reactionVal, contractA_comp_adjoint f, contractB_comp_adjoint f]

/-- `reactionTensor` commutes with pullback along the adjoint of any linear isometry. -/
theorem reactionTensor_compContinuousLinearMap_adjoint {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (f : W →ₗᵢ[ℝ] V) (r : FourTensor W) :
    reactionTensor
        (r.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.adjoint f.toContinuousLinearMap :=
  reactionBilin_compContinuousLinearMap_adjoint f r r

/-- `reactionBilin` is equivariant under linear isometric equivalences. -/
theorem reactionBilin_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r s : FourTensor V) :
    reactionBilin W
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        (s.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionBilin V r s).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  have hp : ContinuousLinearMap.adjoint e.symm.toLinearIsometry.toContinuousLinearMap =
      e.toLinearIsometry.toContinuousLinearMap := by
    rw [show e.symm.toLinearIsometry.toContinuousLinearMap = (e.symm : V →L[ℝ] W) by ext _; rfl,
      show e.toLinearIsometry.toContinuousLinearMap = (e : W →L[ℝ] V) by ext _; rfl]
    simpa only [LinearIsometryEquiv.symm_symm] using e.symm.adjoint_eq_symm
  simpa only [hp] using reactionBilin_compContinuousLinearMap_adjoint e.symm.toLinearIsometry r s

/-- `reactionTensor` is equivariant under linear isometric equivalences (in particular under
`O(V)`). -/
theorem reactionTensor_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    reactionTensor (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (reactionTensor r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap :=
  reactionBilin_compContinuousLinearMap_linearIsometryEquiv e r r

/-! ### Regularity and Lipschitz estimates -/

/-- The reaction tensor is smooth (`C^n` for every `n : ℕ∞ω`, including analytic). -/
@[fun_prop]
theorem contDiff_reactionTensor {n : ℕ∞ω} :
    ContDiff ℝ n (reactionTensor (V := V)) := by
  have h : ∀ B : FourTensor V →L[ℝ] FourTensor V →L[ℝ] FourTensor V,
      ContDiff ℝ n (fun r : FourTensor V ↦ B r r) :=
    fun B ↦ (B.isBoundedBilinearMap.contDiff (n := n)).comp (contDiff_id.prodMk contDiff_id)
  exact h (reactionBilin V)

/-- The reaction tensor is continuous. -/
@[fun_prop]
theorem continuous_reactionTensor : Continuous (reactionTensor (V := V)) :=
  (contDiff_reactionTensor (n := 0)).continuous

/-- The Fréchet derivative of `reactionTensor` at `r` is `2 • reactionBilin V r`. -/
theorem hasFDerivAt_reactionTensor (r : FourTensor V) :
    HasFDerivAt (reactionTensor (V := V)) ((2 : ℝ) • reactionBilin V r) r := by
  have h := (reactionBilin V).hasFDerivAt_of_bilinear (hasFDerivAt_id r) (hasFDerivAt_id r)
  have hderiv :
      (reactionBilin V).precompR (FourTensor V) (id r) (ContinuousLinearMap.id ℝ (FourTensor V)) +
        (reactionBilin V).precompL (FourTensor V) (ContinuousLinearMap.id ℝ (FourTensor V))
          (id r) =
      (2 : ℝ) • reactionBilin V r := by
    ext _; simp [reactionBilin_comm, two_smul]
  rwa [hderiv] at h

/-- Explicit operator-norm bound `‖reactionBilin V‖ ≤ 5 * (dim V)²`. -/
theorem norm_reactionBilin_le :
    ‖reactionBilin V‖ ≤ 5 * (Module.finrank ℝ V : ℝ) ^ 2 :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- Operator-norm difference bound `‖Q(r) - Q(s)‖ ≤ ‖reactionBilin V‖ * ‖r + s‖ * ‖r - s‖`. -/
theorem norm_reactionTensor_sub_le (r s : FourTensor V) :
    ‖reactionTensor r - reactionTensor s‖ ≤
      ‖reactionBilin V‖ * ‖r + s‖ * ‖r - s‖ := by
  rw [reactionTensor_sub_reactionTensor]
  exact ContinuousLinearMap.le_opNorm₂ (reactionBilin V) (r + s) (r - s)

/-- `reactionTensor` is Lipschitz on every closed ball `closedBall r₀ R` with explicit constant
`2 * ‖reactionBilin V‖₊ * (‖r₀‖₊ + R)`. -/
theorem lipschitzOnWith_reactionTensor_closedBall (r₀ : FourTensor V) (R : ℝ≥0) :
    LipschitzOnWith (2 * ‖reactionBilin V‖₊ * (‖r₀‖₊ + R))
      (reactionTensor (V := V)) (Metric.closedBall r₀ R) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro r hr s hs
  rw [dist_eq_norm, dist_eq_norm]
  have hbd (x : FourTensor V) (hx : x ∈ Metric.closedBall r₀ R) : ‖x‖ ≤ ‖r₀‖ + R := by
    have hx' : ‖x - r₀‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    linarith [sub_add_cancel x r₀ ▸ norm_add_le (x - r₀) r₀]
  have hsum : ‖r + s‖ ≤ 2 * (‖r₀‖ + R) := by
    linarith [norm_add_le r s, hbd r hr, hbd s hs]
  calc
    ‖reactionTensor r - reactionTensor s‖
        ≤ ‖reactionBilin V‖ * ‖r + s‖ * ‖r - s‖ := norm_reactionTensor_sub_le r s
    _ ≤ ‖reactionBilin V‖ * (2 * (‖r₀‖ + R)) * ‖r - s‖ := by gcongr
    _ = ↑(2 * ‖reactionBilin V‖₊ * (‖r₀‖₊ + R)) * ‖r - s‖ := by push_cast; ring

/-- The reaction tensor is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  fun r₀ ↦ ⟨_, Metric.closedBall r₀ 1, Metric.closedBall_mem_nhds r₀ zero_lt_one,
    lipschitzOnWith_reactionTensor_closedBall r₀ 1⟩

end TauCeti.FourTensor
