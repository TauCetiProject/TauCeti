/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The algebraic curvature reaction tensor and Hamilton's `#` product

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
constant on every closed ball.

On the exterior square `⋀[ℝ]^2 V`, we define Hamilton's symmetric bilinear Lie-algebraic product
`TauCeti.FourTensor.sharpBilin A B` and `TauCeti.FourTensor.sharp A = sharpBilin A A` using the
bivector Lie bracket `TauCeti.twoVectorBracket`,
```
⟪sharpBilin A B ξ, η⟫ = (1 / 2) ∑_α ∑_β ⟪[A ω_α, B ω_β], ξ⟫ ⟪[ω_α, ω_β], η⟫,
```
prove that `sharp 1 = (dim V - 2) • 1`, and establish the bivector-operator identity
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))` for every symmetric endomorphism `A`
of `⋀[ℝ]^2 V`. As immediate checks, `Q(constantCurvature V) = 2 (dim V - 1) • constantCurvature V`
and `Q(bivectorSq e₁ e₂) = 2 • bivectorSq e₁ e₂` for an orthonormal pair `e₁, e₂` (the curvature
tensor of `S² × ℝ^(n - 2)`).

## Main definitions

* `TauCeti.FourTensor.reactionBilin`: the symmetric continuous bilinear polarization of the
  algebraic curvature reaction term.
* `TauCeti.FourTensor.reactionTensor`: the quadratic reaction tensor `Q(r) = reactionBilin V r r`.
* `TauCeti.FourTensor.bivectorSq`: the rank-one algebraic curvature tensor `(e₁ ∧ e₂) ⊗ (e₁ ∧ e₂)`.
* `TauCeti.FourTensor.sharpBilin` and `TauCeti.FourTensor.sharp`: Hamilton's Lie-algebraic `#`
  product on `Module.End ℝ (⋀[ℝ]^2 V)`.

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
* `TauCeti.FourTensor.sharp_one`: `sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) = (dim V - 2) • 1`.
* `TauCeti.FourTensor.ofExteriorEnd_reactionBilin`, `TauCeti.FourTensor.ofExteriorEnd_reaction`,
  `TauCeti.FourTensor.toExteriorEnd_reactionTensor`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.toExteriorEnd_reactionTensor`: the operator identity
  `Q(R) = 2 (R² + R#)`.
* `TauCeti.FourTensor.reactionTensor_constantCurvature` and
  `TauCeti.FourTensor.reactionTensor_bivectorSq_of_orthonormal`: the round-sphere and
  `S² × ℝ^(n - 2)` checks.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. 167 (2008), 1079–1097, Section 2.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
-/

public section

open exteriorPower
open LinearMap (BilinForm)
open scoped ContDiff NNReal RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Basis-free definition of the reaction tensor -/

/-- Inner bilinear form `(q₁, q₂) ↦ r(u, v, p₁, q₁) s(z, w, p₂, q₂)` for the first quadratic
contraction. -/
private def contractAInner (r s : FourTensor V) (u v z w p₁ p₂ : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun q₁ q₂ ↦ r ![u, v, p₁, q₁] * s ![z, w, p₂, q₂])
    (fun _ _ _ ↦ by simp only [apply_add_fourth]; ring)
    (fun _ _ _ ↦ by simp only [apply_smul_fourth, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [apply_add_fourth]; ring)
    (fun _ _ _ ↦ by simp only [apply_smul_fourth, smul_eq_mul]; ring)

/-- Outer bilinear form `(p₁, p₂) ↦ tr_q (r(u, v, p₁, q) s(z, w, p₂, q))`. -/
private def contractAOuter (r s : FourTensor V) (u v z w : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun p₁ p₂ ↦ bilinFormTrace (contractAInner r s u v z w p₁ p₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext _ _
      simp only [contractAInner, LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_third]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext _ _
      simp only [contractAInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_third]; ring)
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext _ _
      simp only [contractAInner, LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_third]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext _ _
      simp only [contractAInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_third]; ring)

/-- First quadratic contraction `∑ p q, r(u, v, eₚ, e_q) s(z, w, eₚ, e_q)`. -/
private def contractA (r s : FourTensor V) (u v z w : V) : ℝ :=
  bilinFormTrace (contractAOuter r s u v z w)

private theorem contractA_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    contractA r s u v z w = ∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q] := by
  simp only [contractA, bilinFormTrace_eq_sum _ b, contractAOuter, contractAInner,
    LinearMap.mk₂_apply]

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
  rw [contractA, contractA, ← bilinFormTrace_comp_adjoint f]
  congr 1
  ext x y
  simp only [contractAOuter, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [← bilinFormTrace_comp_adjoint f]
  congr 1
  ext a c
  simp only [contractAInner, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec]

/-- Inner bilinear form `(q₁, q₂) ↦ r(u, p₁, z, q₁) s(v, p₂, w, q₂)` for the second quadratic
contraction. -/
private def contractBInner (r s : FourTensor V) (u v z w p₁ p₂ : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun q₁ q₂ ↦ r ![u, p₁, z, q₁] * s ![v, p₂, w, q₂])
    (fun _ _ _ ↦ by simp only [apply_add_fourth]; ring)
    (fun _ _ _ ↦ by simp only [apply_smul_fourth, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [apply_add_fourth]; ring)
    (fun _ _ _ ↦ by simp only [apply_smul_fourth, smul_eq_mul]; ring)

/-- Outer bilinear form `(p₁, p₂) ↦ tr_q (r(u, p₁, z, q) s(v, p₂, w, q))`. -/
private def contractBOuter (r s : FourTensor V) (u v z w : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun p₁ p₂ ↦ bilinFormTrace (contractBInner r s u v z w p₁ p₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext _ _
      simp only [contractBInner, LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_second]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext _ _
      simp only [contractBInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_second]; ring)
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; ext _ _
      simp only [contractBInner, LinearMap.mk₂_apply, LinearMap.add_apply, apply_add_second]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; ext _ _
      simp only [contractBInner, LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_smul_second]; ring)

/-- Second quadratic contraction `∑ p q, r(u, eₚ, z, e_q) s(v, eₚ, w, e_q)`. -/
private def contractB (r s : FourTensor V) (u v z w : V) : ℝ :=
  bilinFormTrace (contractBOuter r s u v z w)

private theorem contractB_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (r s : FourTensor V) (u v z w : V) :
    contractB r s u v z w = ∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q] := by
  simp only [contractB, bilinFormTrace_eq_sum _ b, contractBOuter, contractBInner,
    LinearMap.mk₂_apply]

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
  rw [contractB, contractB, ← bilinFormTrace_comp_adjoint f]
  congr 1
  ext x y
  simp only [contractBOuter, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [← bilinFormTrace_comp_adjoint f]
  congr 1
  ext a c
  simp only [contractBInner, LinearMap.mk₂_apply, LinearMap.BilinForm.comp_apply,
    ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply_vec]

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
  simp only [reactionVal, contractA_eq_sum b, contractB_eq_sum b]

/-- `reactionVal r s` as a curried four-linear form on `V`. -/
private def reactionLinear (r s : FourTensor V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ (fun z w ↦ reactionVal r s u v z w)
      (fun z₁ z₂ w ↦ by
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first, apply_add_third,
          add_mul, mul_add, Finset.sum_add_distrib]
        ring)
      (fun c z w ↦ by
        have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, apply_smul_third,
          smul_eq_mul, mul_assoc, hm, ← Finset.mul_sum]
        ring)
      (fun z w₁ w₂ ↦ by
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_second, apply_add_third,
          add_mul, mul_add, Finset.sum_add_distrib]
        ring)
      (fun c z w ↦ by
        have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_second,
          apply_smul_third, smul_eq_mul, mul_assoc, hm, ← Finset.mul_sum]
        ring))
    (fun u₁ u₂ v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
        reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first, add_mul,
        Finset.sum_add_distrib]
      ring)
    (fun c u v ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, mul_assoc,
        ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ ↦ by
      ext z w
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply,
        reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_add_first, apply_add_second, add_mul,
        mul_add, Finset.sum_add_distrib]
      ring)
    (fun c u v ↦ by
      ext z w
      have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, smul_eq_mul,
        reactionVal_eq_sum (stdOrthonormalBasis ℝ V), apply_smul_first, apply_smul_second,
        mul_assoc, hm, ← Finset.mul_sum]
      ring)

private theorem norm_contractA_le (r s : FourTensor V) (u v z w : V) :
    ‖contractA r s u v z w‖ ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
  let b := stdOrthonormalBasis ℝ V
  have hb (i : Fin (Module.finrank ℝ V)) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hterm (t : FourTensor V) (x₀ x₁ x₂ x₃ : V) :
      ‖t ![x₀, x₁, x₂, x₃]‖ ≤ ‖t‖ * (‖x₀‖ * ‖x₁‖ * ‖x₂‖ * ‖x₃‖) := by
    simpa [Fin.prod_univ_four] using t.le_opNorm ![x₀, x₁, x₂, x₃]
  rw [contractA_eq_sum b]
  calc
    ‖∑ p, ∑ q, r ![u, v, b p, b q] * s ![z, w, b p, b q]‖
        ≤ ∑ p, ∑ q, ‖r ![u, v, b p, b q] * s ![z, w, b p, b q]‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _p : Fin (Module.finrank ℝ V), ∑ _q : Fin (Module.finrank ℝ V),
          ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
        refine Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun q _ ↦ ?_
        rw [norm_mul]
        have hr := hterm r u v (b p) (b q)
        have hs := hterm s z w (b p) (b q)
        rw [hb p, hb q, mul_one, mul_one] at hr hs
        calc
          ‖r ![u, v, b p, b q]‖ * ‖s ![z, w, b p, b q]‖
              ≤ (‖r‖ * (‖u‖ * ‖v‖)) * (‖s‖ * (‖z‖ * ‖w‖)) := by gcongr
          _ = ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by ring
    _ = (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
        simp [Finset.sum_const, nsmul_eq_mul, sq]; ring

private theorem norm_contractB_le (r s : FourTensor V) (u v z w : V) :
    ‖contractB r s u v z w‖ ≤
      (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
  let b := stdOrthonormalBasis ℝ V
  have hb (i : Fin (Module.finrank ℝ V)) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hterm (t : FourTensor V) (x₀ x₁ x₂ x₃ : V) :
      ‖t ![x₀, x₁, x₂, x₃]‖ ≤ ‖t‖ * (‖x₀‖ * ‖x₁‖ * ‖x₂‖ * ‖x₃‖) := by
    simpa [Fin.prod_univ_four] using t.le_opNorm ![x₀, x₁, x₂, x₃]
  rw [contractB_eq_sum b]
  calc
    ‖∑ p, ∑ q, r ![u, b p, z, b q] * s ![v, b p, w, b q]‖
        ≤ ∑ p, ∑ q, ‖r ![u, b p, z, b q] * s ![v, b p, w, b q]‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _p : Fin (Module.finrank ℝ V), ∑ _q : Fin (Module.finrank ℝ V),
          ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
        refine Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun q _ ↦ ?_
        rw [norm_mul]
        have hr := hterm r u (b p) z (b q)
        have hs := hterm s v (b p) w (b q)
        rw [hb p, hb q, mul_one, mul_one] at hr hs
        calc
          ‖r ![u, b p, z, b q]‖ * ‖s ![v, b p, w, b q]‖
              ≤ (‖r‖ * (‖u‖ * ‖z‖)) * (‖s‖ * (‖v‖ * ‖w‖)) := by gcongr
          _ = ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by ring
    _ = (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ * (‖u‖ * ‖v‖ * ‖z‖ * ‖w‖) := by
        simp [Finset.sum_const, nsmul_eq_mul, sq]; ring

private def reactionBilinLinear : FourTensor V →ₗ[ℝ] FourTensor V →ₗ[ℝ] FourTensor V where
  toFun r :=
    { toFun := fun s ↦ ofLinearMap₄ (reactionLinear r s)
      map_add' := fun s₁ s₂ ↦ by
        ext m
        simp only [ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, add_apply,
          reactionVal_eq_sum (stdOrthonormalBasis ℝ V), add_mul, mul_add,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c s ↦ by
        ext m
        have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
        simp only [ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, smul_apply,
          RingHom.id_apply, smul_eq_mul, reactionVal_eq_sum (stdOrthonormalBasis ℝ V),
          mul_assoc, hm, ← Finset.mul_sum]
        ring }
  map_add' r₁ r₂ := by
    ext s m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, ofLinearMap₄_apply,
      reactionLinear, LinearMap.mk₂_apply, add_apply,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c r := by
    ext s m
    have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      ofLinearMap₄_apply, reactionLinear, LinearMap.mk₂_apply, smul_apply, smul_eq_mul,
      reactionVal_eq_sum (stdOrthonormalBasis ℝ V), mul_assoc, hm, ← Finset.mul_sum]
    ring

private theorem norm_reactionBilinLinear_le (r s : FourTensor V) :
    ‖reactionBilinLinear r s‖ ≤ (5 * (Module.finrank ℝ V : ℝ) ^ 2) * ‖r‖ * ‖s‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hval : reactionBilinLinear r s m = reactionVal r s (m 0) (m 1) (m 2) (m 3) := by
    simp [reactionBilinLinear, reactionLinear]
  rw [hval, reactionVal, Fin.prod_univ_four]
  have hcomm : ‖m 0‖ * ‖m 1‖ * ‖m 3‖ * ‖m 2‖ = ‖m 0‖ * ‖m 1‖ * ‖m 2‖ * ‖m 3‖ := by ring
  have hrs : (Module.finrank ℝ V : ℝ) ^ 2 * ‖s‖ * ‖r‖ =
      (Module.finrank ℝ V : ℝ) ^ 2 * ‖r‖ * ‖s‖ := by ring
  have hA1 := norm_contractA_le r s (m 0) (m 1) (m 2) (m 3)
  have hA2 := norm_contractA_le s r (m 0) (m 1) (m 2) (m 3)
  have hB1 := norm_contractB_le r s (m 0) (m 1) (m 2) (m 3)
  have hB2 := norm_contractB_le r s (m 0) (m 1) (m 3) (m 2)
  have hB3 := norm_contractB_le s r (m 0) (m 1) (m 2) (m 3)
  have hB4 := norm_contractB_le s r (m 0) (m 1) (m 3) (m 2)
  rw [hrs] at hA2 hB3 hB4
  rw [hcomm] at hB2 hB4
  have h1 (a b c : ℝ) : ‖a + 2 * b - 2 * c‖ ≤ ‖a‖ + 2 * ‖b‖ + 2 * ‖c‖ := by
    have hsub := norm_sub_le (a + 2 * b) (2 * c)
    have hadd := norm_add_le a (2 * b)
    simp only [norm_mul, Real.norm_ofNat] at hsub hadd
    linarith
  have htri := (norm_add_le _ _).trans (add_le_add
    (h1 (contractA r s (m 0) (m 1) (m 2) (m 3)) (contractB r s (m 0) (m 1) (m 2) (m 3))
      (contractB r s (m 0) (m 1) (m 3) (m 2)))
    (h1 (contractA s r (m 0) (m 1) (m 2) (m 3)) (contractB s r (m 0) (m 1) (m 2) (m 3))
      (contractB s r (m 0) (m 1) (m 3) (m 2))))
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  linarith

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
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [h₁ u v (b p) (b q), neg_mul]
  have hB : (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ∑ p, ∑ q, r ![v, b p, w, b q] * r ![u, b p, z, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
  have hC : (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ∑ p, ∑ q, r ![v, b p, z, b q] * r ![u, b p, w, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
  rw [hA, hB, hC]
  ring

/-- If `r` is antisymmetric in its first pair, then `Q(r)` is antisymmetric in its last pair. -/
theorem reactionTensor_antisymm_last {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = -reactionTensor r ![u, v, w, z] := by
  let b := stdOrthonormalBasis ℝ V
  rw [reactionTensor_apply_orthonormalBasis b, reactionTensor_apply_orthonormalBasis b]
  have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      -(∑ p, ∑ q, r ![u, v, b p, b q] * r ![w, z, b p, b q]) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [h₁ z w (b p) (b q), mul_neg]
  rw [hA]
  ring

/-- If `r` is symmetric under pair interchange, then so is `Q(r)`. -/
theorem reactionTensor_swap_pairs {r : FourTensor V}
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) (u v z w : V) :
    reactionTensor r ![u, v, z, w] = reactionTensor r ![z, w, u, v] := by
  let b := stdOrthonormalBasis ℝ V
  rw [reactionTensor_apply_orthonormalBasis b, reactionTensor_apply_orthonormalBasis b]
  have hA : (∑ p, ∑ q, r ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      ∑ p, ∑ q, r ![z, w, b p, b q] * r ![u, v, b p, b q] :=
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
  have hB : (∑ p, ∑ q, r ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      ∑ p, ∑ q, r ![z, b p, u, b q] * r ![w, b p, v, b q] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hswap u (b q) z (b p), hswap v (b q) w (b p)]
  have hC : (∑ p, ∑ q, r ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      ∑ p, ∑ q, r ![z, b p, v, b q] * r ![w, b p, u, b q] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
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
    rw [hr.antisymm_first (b p) y x (b q), hr.antisymm_first y x (b p) (b q)] at hc
    linarith
  have h2 (p q) : r ![t, b p, w, b q] - r ![t, b q, w, b p] = r ![t, w, b p, b q] := by
    have hc := hr.cyclic_eq_zero t (b p) w (b q)
    have hsw : r ![b p, w, t, b q] = -r ![t, b q, w, b p] := by
      rw [hr.swap_pairs, hr.antisymm_last t (b q) (b p) w]
    have hsw2 : r ![w, t, b p, b q] = -r ![t, w, b p, b q] := hr.antisymm_first w t (b p) (b q)
    linarith
  have hswap : (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) =
      -(∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b q, w, b p]) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_last x y (b q) (b p), neg_mul]
  calc
    2 * (∑ p, ∑ q, (r ![x, b p, y, b q] - r ![y, b p, x, b q]) * r ![t, b p, w, b q])
        = (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) +
            (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, b p, w, b q]) := by
          simp only [h1]; ring
    _ = ∑ p, ∑ q, r ![x, y, b p, b q] * (r ![t, b p, w, b q] - r ![t, b q, w, b p]) := by
          conv_rhs => simp only [mul_sub, Finset.sum_sub_distrib]
          rw [hswap]; ring
    _ = ∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, w, b p, b q] := by
          simp only [h2]

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
    have hm (x y t : V) :
        (∑ p, ∑ q, r ![x, b p, w, b q] * r ![y, b p, t, b q]) =
          ∑ p, ∑ q, r ![y, b p, t, b q] * r ![x, b p, w, b q] :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [hm u v z, hm v z u, hm z u v]
    ring
  have hneg (x y t : V) :
      (∑ p, ∑ q, r ![x, y, b p, b q] * r ![t, w, b p, b q]) =
        -(∑ p, ∑ q, r ![y, x, b p, b q] * r ![t, w, b p, b q]) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hr.antisymm_first x y (b p) (b q), neg_mul]
  have h1 := reactionTensor_bianchi_term b hr u z v w
  have h2 := reactionTensor_bianchi_term b hr v u z w
  have h3 := reactionTensor_bianchi_term b hr z v u w
  rw [hneg u z v] at h1
  rw [hneg v u z] at h2
  rw [hneg z v u] at h3
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
  have hadd : r + s ∈ algebraicCurvatureSubmodule V :=
    Submodule.add_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr hs)
  have hsub : r - s ∈ algebraicCurvatureSubmodule V :=
    Submodule.sub_mem _ (mem_algebraicCurvatureSubmodule.mpr hr)
      (mem_algebraicCurvatureSubmodule.mpr hs)
  exact mem_algebraicCurvatureSubmodule.mp
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (reactionTensor_mem hadd)
      (reactionTensor_mem hsub)))

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
  have h1 : (e.symm : V →L[ℝ] W) = e.symm.toLinearIsometry.toContinuousLinearMap := by
    ext x; rfl
  have h2 : (e : W →L[ℝ] V) = e.toLinearIsometry.toContinuousLinearMap := by
    ext x; rfl
  have hp : ContinuousLinearMap.adjoint e.symm.toLinearIsometry.toContinuousLinearMap =
      e.toLinearIsometry.toContinuousLinearMap := by
    rw [← h1, ← h2]
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
      ContDiff ℝ n (fun r : FourTensor V ↦ B r r) := fun B ↦
    (B.isBoundedBilinearMap.contDiff (n := n)).comp (contDiff_id.prodMk contDiff_id)
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
    ext h'
    simp [reactionBilin_comm, two_smul]
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
    calc
      ‖x‖ = ‖(x - r₀) + r₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - r₀‖ + ‖r₀‖ := norm_add_le _ _
      _ ≤ R + ‖r₀‖ := by linarith
      _ = ‖r₀‖ + R := add_comm _ _
  have hsum : ‖r + s‖ ≤ 2 * (‖r₀‖ + R) := by
    calc
      ‖r + s‖ ≤ ‖r‖ + ‖s‖ := norm_add_le r s
      _ ≤ (‖r₀‖ + R) + (‖r₀‖ + R) := add_le_add (hbd r hr) (hbd s hs)
      _ = 2 * (‖r₀‖ + R) := by ring
  calc
    ‖reactionTensor r - reactionTensor s‖
        ≤ ‖reactionBilin V‖ * ‖r + s‖ * ‖r - s‖ := norm_reactionTensor_sub_le r s
    _ ≤ ‖reactionBilin V‖ * (2 * (‖r₀‖ + R)) * ‖r - s‖ := by
          gcongr
    _ = ↑(2 * ‖reactionBilin V‖₊ * (‖r₀‖₊ + R)) * ‖r - s‖ := by
          push_cast; ring

/-- The reaction tensor is locally Lipschitz on `FourTensor V`. -/
theorem locallyLipschitz_reactionTensor : LocallyLipschitz (reactionTensor (V := V)) :=
  fun r₀ ↦ ⟨_, Metric.closedBall r₀ 1, Metric.closedBall_mem_nhds r₀ zero_lt_one,
    lipschitzOnWith_reactionTensor_closedBall r₀ 1⟩

/-! ### Hamilton's `#` product and the bivector-operator identity `Q(R) = 2(R² + R#)` -/

/-- Inner bilinear form `(β₁, β₂) ↦ ⟪[A α₁, B β₁], ξ⟫ ⟪[α₂, β₂], η⟫` on `⋀[ℝ]^2 V`. -/
private def sharpInner (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η α₁ α₂ : ⋀[ℝ]^2 V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  LinearMap.mk₂ ℝ
    (fun β₁ β₂ ↦ ⟪twoVectorBracket (A α₁) (B β₁), ξ⟫ * ⟪twoVectorBracket α₂ β₂, η⟫)
    (fun _ _ _ ↦ by simp only [map_add, inner_add_left]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [map_add, inner_add_left]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)

/-- Outer bilinear form `(α₁, α₂) ↦ tr_β (⟪[A α₁, B β], ξ⟫ ⟪[α₂, β], η⟫)` on `⋀[ℝ]^2 V`. -/
private def sharpOuter (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  LinearMap.mk₂ ℝ (fun α₁ α₂ ↦ bilinFormTrace (sharpInner A B ξ η α₁ α₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1
      refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [sharpInner, LinearMap.mk₂_apply, LinearMap.add_apply, map_add, inner_add_left]
      ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1
      refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [sharpInner, LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul,
        real_inner_smul_left, smul_eq_mul]
      ring)
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1
      refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [sharpInner, LinearMap.mk₂_apply, LinearMap.add_apply, map_add, inner_add_left]
      ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1
      refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [sharpInner, LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul,
        real_inner_smul_left, smul_eq_mul]
      ring)

private def sharpVal (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) : ℝ :=
  (1 / 2 : ℝ) * bilinFormTrace (sharpOuter A B ξ η)

private theorem sharpVal_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V))
    (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    sharpVal A B ξ η =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
  simp only [sharpVal, bilinFormTrace_eq_sum _ e, sharpOuter, sharpInner, LinearMap.mk₂_apply]

private theorem sharpVal_eq_sum_ιMulti {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    sharpVal A B ξ η =
      (1 / 8 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]), η⟫ := by
  have houter := b.sum_bilinForm_ιMulti_two (sharpOuter A B ξ η)
  have hinner (i j : ι) :=
    b.sum_bilinForm_ιMulti_two
      (sharpInner A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j]))
  have h4 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]), η⟫) =
        4 * bilinFormTrace (sharpOuter A B ξ η) := by
    calc
      _ = ∑ i, ∑ j, 2 * bilinFormTrace
            (sharpInner A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hinner i j
      _ = 2 * (∑ i, ∑ j,
            sharpOuter A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) := by
          simp only [sharpOuter, LinearMap.mk₂_apply, Finset.mul_sum]
      _ = 4 * bilinFormTrace (sharpOuter A B ξ η) := by
          rw [houter]; ring
  rw [sharpVal, h4]
  ring

private def sharpForm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  LinearMap.mk₂ ℝ (fun ξ η ↦ sharpVal A B ξ η)
    (fun _ _ _ ↦ by
      simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), inner_add_right, add_mul,
        Finset.sum_add_distrib]
      ring)
    (fun c _ _ ↦ by
      simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), real_inner_smul_right,
        smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      ring)
    (fun _ _ _ ↦ by
      simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), inner_add_right, mul_add,
        Finset.sum_add_distrib])
    (fun c _ _ ↦ by
      have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
      simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), real_inner_smul_right,
        smul_eq_mul, hm, ← Finset.mul_sum])

/-- Hamilton's symmetric bilinear Lie-algebraic `#` product on `Module.End ℝ (⋀[ℝ]^2 V)`,
characterized in any orthonormal basis `e` of `⋀[ℝ]^2 V` by
`⟪sharpBilin A B ξ, η⟫ = (1 / 2) ∑ α β, ⟪[A (e α), B (e β)], ξ⟫ ⟪[e α, e β], η⟫`. -/
def sharpBilin :
    Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun A :=
    { toFun := fun B ↦
        (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 V)).symm.toLinearEquiv.toLinearMap ∘ₗ
          (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ sharpForm A B)
      map_add' := fun B₁ B₂ ↦ by
        refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.coe_toContinuousLinearMap',
          InnerProductSpace.toDual_symm_apply, LinearMap.add_apply, inner_add_left, sharpForm,
          LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_add,
          add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c B ↦ by
        refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.coe_toContinuousLinearMap',
          InnerProductSpace.toDual_symm_apply, LinearMap.smul_apply, RingHom.id_apply,
          real_inner_smul_left, sharpForm, LinearMap.mk₂_apply,
          sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul, mul_assoc, ← Finset.mul_sum]
        ring }
  map_add' A₁ A₂ := by
    refine LinearMap.ext fun B ↦ LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply, inner_add_left,
      sharpForm, LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)),
      map_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c A := by
    refine LinearMap.ext fun B ↦ LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      real_inner_smul_left, sharpForm, LinearMap.mk₂_apply,
      sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul, mul_assoc, ← Finset.mul_sum]
    ring

/-- Hamilton's quadratic `#` operator `A# = sharpBilin A A` on `Module.End ℝ (⋀[ℝ]^2 V)`. -/
def sharp (A : Module.End ℝ (⋀[ℝ]^2 V)) : Module.End ℝ (⋀[ℝ]^2 V) :=
  sharpBilin A A

private theorem inner_sharpBilin_eq_sharpVal (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ = sharpVal A B ξ η := by
  simp [sharpBilin, sharpForm]

/-- Evaluation of `sharpBilin A B` in any orthonormal basis of `⋀[ℝ]^2 V`. -/
theorem inner_sharpBilin_orthonormalBasis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
  rw [inner_sharpBilin_eq_sharpVal, sharpVal_eq_sum e]

/-- `sharpBilin` is symmetric in its two endomorphism arguments. -/
theorem sharpBilin_comm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : sharpBilin A B = sharpBilin B A := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [inner_sharpBilin_orthonormalBasis e, inner_sharpBilin_orthonormalBasis e]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  rw [twoVectorBracket_swap (B (e α)) (A (e β)), twoVectorBracket_swap (e α) (e β),
    inner_neg_left, inner_neg_left, neg_mul_neg]

/-- The diagonal of `sharpBilin` is `sharp`. -/
@[simp]
theorem sharpBilin_self (A : Module.End ℝ (⋀[ℝ]^2 V)) : sharpBilin A A = sharp A :=
  (rfl)

/-- `sharp 0 = 0`. -/
@[simp]
theorem sharp_zero : sharp (0 : Module.End ℝ (⋀[ℝ]^2 V)) = 0 := by
  simp [sharp]

/-- `sharp (-A) = sharp A`. -/
@[simp]
theorem sharp_neg (A : Module.End ℝ (⋀[ℝ]^2 V)) : sharp (-A) = sharp A := by
  simp only [sharp, map_neg, LinearMap.neg_apply, neg_neg]

/-- `sharp (c • A) = c ^ 2 • sharp A`. -/
@[simp]
theorem sharp_smul (c : ℝ) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    sharp (c • A) = (c ^ 2) • sharp A := by
  simp only [sharp, map_smul, LinearMap.smul_apply, smul_smul, sq]

/-- Every rank-one self-adjoint operator on `⋀[ℝ]^2 V` has vanishing `#`-square, since its image
is at most one-dimensional and hence abelian under `twoVectorBracket`. -/
theorem sharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    sharp (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [← sharpBilin_self, inner_sharpBilin_orthonormalBasis (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V))]
  simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, map_smul,
    LinearMap.smul_apply, twoVectorBracket_self, smul_zero, inner_zero_left, zero_mul,
    Finset.sum_const_zero, mul_zero, LinearMap.zero_apply]

private theorem sharpBilin_sum_expand {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (x y : ⋀[ℝ]^2 V) :
    (∑ α, ∑ β, ⟪twoVectorBracket (A (e α)) (B (e β)), x⟫ * ⟪twoVectorBracket (e α) (e β), y⟫) =
      ∑ α, ∑ β, ∑ γ, ∑ δ,
        ⟪e γ, A (e α)⟫ * ⟪e δ, B (e β)⟫ *
          ⟪twoVectorBracket (e γ) (e δ), x⟫ * ⟪twoVectorBracket (e α) (e β), y⟫ := by
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  conv_lhs => rw [← e.sum_repr' (A (e α)), ← e.sum_repr' (B (e β))]
  rw [map_sum, sum_inner, Finset.sum_mul]
  trans ∑ δ, ∑ γ,
      ⟪e γ, A (e α)⟫ * ⟪e δ, B (e β)⟫ *
        ⟪twoVectorBracket (e γ) (e δ), x⟫ * ⟪twoVectorBracket (e α) (e β), y⟫
  · refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [map_smul, real_inner_smul_left, map_sum, LinearMap.sum_apply, sum_inner, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply, real_inner_smul_left]
    ring
  · exact Finset.sum_comm

/-- The `#` product of two symmetric endomorphisms of `⋀[ℝ]^2 V` is symmetric. -/
theorem isSymmetric_sharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) : (sharpBilin A B).IsSymmetric := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  intro ξ η
  rw [real_inner_comm (sharpBilin A B η) ξ, inner_sharpBilin_orthonormalBasis e,
    inner_sharpBilin_orthonormalBasis e]
  congr 1
  rw [sharpBilin_sum_expand e A B ξ η, sharpBilin_sum_expand e A B η ξ]
  calc
    ∑ α, ∑ β, ∑ γ, ∑ δ,
        ⟪e γ, A (e α)⟫ * ⟪e δ, B (e β)⟫ *
          ⟪twoVectorBracket (e γ) (e δ), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫
      = ∑ α, ∑ β, ∑ γ, ∑ δ,
          ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
            ⟪twoVectorBracket (e γ) (e δ), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ :=
        Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦
          Finset.sum_congr rfl fun γ _ ↦ Finset.sum_congr rfl fun δ _ ↦ by
            rw [← hA (e γ) (e α), real_inner_comm (A (e γ)), ← hB (e δ) (e β),
              real_inner_comm (B (e δ))]
    _ = ∑ α, ∑ γ, ∑ β, ∑ δ,
          ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
            ⟪twoVectorBracket (e γ) (e δ), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ γ, ∑ α, ∑ δ, ∑ β,
          ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
            ⟪twoVectorBracket (e γ) (e δ), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ γ, ∑ δ, ∑ α, ∑ β,
          ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
            ⟪twoVectorBracket (e α) (e β), η⟫ * ⟪twoVectorBracket (e γ) (e δ), ξ⟫ := by
        refine Finset.sum_congr rfl fun γ _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun α _ ↦
          Finset.sum_congr rfl fun β _ ↦ by ring

/-- The `#`-square of a symmetric endomorphism of `⋀[ℝ]^2 V` is symmetric. -/
theorem isSymmetric_sharp {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    (sharp A).IsSymmetric :=
  isSymmetric_sharpBilin hA hA

private theorem sum_inner_twoVectorBracket_contract {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ x y : ⋀[ℝ]^2 V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
        (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫)) =
      4 * ⟪twoVectorBracket (A x) (B y), ξ⟫ := by
  have hrepr (η : ⋀[ℝ]^2 V) :
      ∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], η⟫ • ιMulti ℝ 2 ![b i, b j] = (2 : ℝ) • η := by
    simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun b.sum_rankOne_ιMulti_two η
  have hlhs :
      ⟪twoVectorBracket (A (∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], x⟫ • ιMulti ℝ 2 ![b i, b j]))
          (B (∑ k, ∑ l, ⟪ιMulti ℝ 2 ![b k, b l], y⟫ • ιMulti ℝ 2 ![b k, b l])), ξ⟫ =
      ∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫) := by
    rw [map_sum, map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum, map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, real_inner_smul_left,
      map_sum, map_sum, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_sum, map_sum, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, map_smul, real_inner_smul_left]
    ring
  rw [← hlhs, hrepr x, hrepr y, map_smul, map_smul, map_smul, LinearMap.smul_apply,
    map_smul, real_inner_smul_left, real_inner_smul_left]
  ring

/-- First reduction of `2 * ⟪sharpBilin A B ξ, z ∧ w⟫` to a single basis sum over `V`. -/
private theorem two_mul_inner_sharpBilin_ιMulti_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ : ⋀[ℝ]^2 V) (z w : V) :
    2 * ⟪sharpBilin A B ξ, ιMulti ℝ 2 ![z, w]⟫ =
      ∑ q, (⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b q])) (B (ιMulti ℝ 2 ![b q, z])), ξ⟫ -
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b q])) (B (ιMulti ℝ 2 ![b q, w])), ξ⟫) := by
  have hcomm (f : ι → ι → ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, ∑ l, ∑ q, f i j k l q) = ∑ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l q := by
    trans ∑ i, ∑ j, ∑ k, ∑ q, ∑ l, f i j k l q
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    trans ∑ i, ∑ j, ∑ q, ∑ k, ∑ l, f i j k l q
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    trans ∑ i, ∑ q, ∑ j, ∑ k, ∑ l, f i j k l q
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    exact Finset.sum_comm
  have hsum :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]),
            ιMulti ℝ 2 ![z, w]⟫) =
      ∑ q, (4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b q])) (B (ιMulti ℝ 2 ![b q, z])), ξ⟫ -
        4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b q])) (B (ιMulti ℝ 2 ![b q, w])), ξ⟫) := by
    simp_rw [inner_twoVectorBracket_ιMulti_orthonormalBasis b, Finset.mul_sum, mul_sub]
    rw [hcomm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [Finset.sum_sub_distrib, sum_inner_twoVectorBracket_contract b A B ξ]
  rw [inner_sharpBilin_eq_sharpVal, sharpVal_eq_sum_ιMulti b, hsum, ← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ by ring

/-- Contraction of `2 • sharpBilin A B` on pure bivectors in terms of `contractB`. -/
private theorem two_mul_inner_sharpBilin_ιMulti {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (u v z w : V) :
    2 * ⟪sharpBilin A B (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      (contractB (ofExteriorEnd A) (ofExteriorEnd B) u v z w +
        contractB (ofExteriorEnd B) (ofExteriorEnd A) u v z w) -
      (contractB (ofExteriorEnd A) (ofExteriorEnd B) u v w z +
        contractB (ofExteriorEnd B) (ofExteriorEnd A) u v w z) := by
  let b := stdOrthonormalBasis ℝ V
  rw [two_mul_inner_sharpBilin_ιMulti_right b]
  simp_rw [inner_twoVectorBracket_ιMulti_orthonormalBasis b, contractB_eq_sum b,
    ofExteriorEnd_apply]
  have hA' (x y s t : V) :
      ⟪A (ιMulti ℝ 2 ![x, y]), ιMulti ℝ 2 ![s, t]⟫ =
        ⟪A (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by
    rw [hA, real_inner_comm]
  have hB' (x y s t : V) :
      ⟪B (ιMulti ℝ 2 ![y, x]), ιMulti ℝ 2 ![t, s]⟫ =
        ⟪B (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by
    rw [ιMulti_two_swap y x, ιMulti_two_swap t s, map_neg, inner_neg_left, inner_neg_right,
      neg_neg, hB, real_inner_comm]
  simp_rw [hA' w (b _), hA' z (b _), hB' z (b _), hB' w (b _)]
  conv_lhs =>
    simp only [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  conv_rhs => simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring

/-- **Polarized bivector-operator identity**: for symmetric endomorphisms `A, B` of `⋀[ℝ]^2 V`,
`reactionBilin V (ofExteriorEnd A) (ofExteriorEnd B)` equals
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • sharpBilin A B)`. -/
theorem ofExteriorEnd_reactionBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) :
    reactionBilin V (ofExteriorEnd A) (ofExteriorEnd B) =
      ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • sharpBilin A B) := by
  let b := stdOrthonormalBasis ℝ V
  have hcomp (S T : Module.End ℝ (⋀[ℝ]^2 V)) (hS : S.IsSymmetric) (u v z w : V) :
      2 * ⟪(S ∘ₗ T) (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
        contractA (ofExteriorEnd T) (ofExteriorEnd S) u v z w := by
    have hrepr :
        ∑ p, ∑ q, ⟪ιMulti ℝ 2 ![b p, b q], T (ιMulti ℝ 2 ![u, v])⟫ • ιMulti ℝ 2 ![b p, b q] =
          (2 : ℝ) • T (ιMulti ℝ 2 ![u, v]) := by
      simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
        InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun b.sum_rankOne_ιMulti_two (T (ιMulti ℝ 2 ![u, v]))
    rw [LinearMap.comp_apply, hS, ← real_inner_smul_left, ← hrepr, sum_inner]
    simp only [sum_inner, real_inner_smul_left, contractA_eq_sum b, ofExteriorEnd_apply]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    rw [real_inner_comm (T _), real_inner_comm (S _)]
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionBilin_apply_val, reactionVal, ofExteriorEnd_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, real_inner_smul_left]
  have h1 := hcomp A B hA (m 0) (m 1) (m 2) (m 3)
  have h2 := hcomp B A hB (m 0) (m 1) (m 2) (m 3)
  have h3 := two_mul_inner_sharpBilin_ιMulti hA hB (m 0) (m 1) (m 2) (m 3)
  linarith

/-- **Bivector-operator identity** `Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))`
for any symmetric endomorphism `A` of `⋀[ℝ]^2 V`. -/
theorem ofExteriorEnd_reaction {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    reactionTensor (ofExteriorEnd A) = ofExteriorEnd ((2 : ℝ) • (A * A + sharp A)) := by
  rw [reactionTensor, ofExteriorEnd_reactionBilin hA hA]
  congr 1
  ext ξ
  simp [two_smul, smul_add]

/-- On any four-tensor antisymmetric in its first pair and symmetric under pair interchange,
`toExteriorEnd (Q(r)) = 2 • (R² + R#)` with `R = toExteriorEnd r`. -/
theorem toExteriorEnd_reactionTensor {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    toExteriorEnd (reactionTensor r) =
      (2 : ℝ) • (toExteriorEnd r * toExteriorEnd r + sharp (toExteriorEnd r)) := by
  have h₂ (u v z w : V) : r ![u, v, z, w] = -r ![u, v, w, z] := by
    rw [hswap u v z w, h₁ z w u v, hswap w z u v]
  have hsym := isSymmetric_toExteriorEnd hswap
  have hof := ofExteriorEnd_toExteriorEnd_of_antisymm h₁ h₂
  conv_lhs => rw [← hof]
  rw [ofExteriorEnd_reaction hsym, toExteriorEnd_ofExteriorEnd]

/-- For every algebraic curvature tensor `r`, `toExteriorEnd (Q(r)) = 2 • (R² + R#)` with
`R = toExteriorEnd r`. -/
theorem IsAlgebraicCurvature.toExteriorEnd_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    toExteriorEnd (FourTensor.reactionTensor r) =
      (2 : ℝ) • (toExteriorEnd r * toExteriorEnd r + sharp (toExteriorEnd r)) :=
  FourTensor.toExteriorEnd_reactionTensor hr.antisymm_first hr.swap_pairs

/-! ### Explicit evaluations: identity, constant curvature, and rank-one bivectors -/

private theorem contractB_constantCurvature (u v z w : V) :
    contractB (constantCurvature V) (constantCurvature V) u v z w =
      ((Module.finrank ℝ V : ℝ) - 2) * (⟪u, z⟫ * ⟪v, w⟫) + ⟪u, v⟫ * ⟪z, w⟫ := by
  let b := stdOrthonormalBasis ℝ V
  rw [contractB_eq_sum b]
  have hp (x y : V) : ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
    simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner x y
  have hdiag (p) (f : Fin (Module.finrank ℝ V) → ℝ) :
      (∑ q, ⟪b p, b q⟫ * f q) = f p := by
    simp only [b.inner_eq_ite]
    rw [Finset.sum_eq_single p (fun q _ hq ↦ by simp [hq.symm]) (by simp)]
    simp
  simp only [constantCurvature_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ p, ∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) =
      (Module.finrank ℝ V : ℝ) * (⟪u, z⟫ * ⟪v, w⟫) := by
    have hq (p) : (∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
      have h := hdiag p (fun q ↦ ⟪u, z⟫ * (⟪v, w⟫ * ⟪b p, b q⟫))
      rw [show ⟪b p, b p⟫ = 1 by simp, mul_one] at h
      convert h using 2; ring
    simp [hq]
  have h2 : (∑ p, ∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
    have hq (p) : (∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) =
        ⟪u, z⟫ * (⟪v, b p⟫ * ⟪b p, w⟫) := by
      simpa only [mul_assoc] using
        (by convert hdiag p (fun q ↦ ⟪u, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) using 2; ring)
    simp only [hq, ← Finset.mul_sum, hp]
  have h3 : (∑ p, ∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
    have hq (p) : (∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) =
        ⟪v, w⟫ * (⟪u, b p⟫ * ⟪b p, z⟫) := by
      convert hdiag p (fun q ↦ ⟪v, w⟫ * (⟪u, b q⟫ * ⟪b p, z⟫)) using 2; ring
    simp only [hq, ← Finset.mul_sum, hp]; ring
  have h4 : (∑ p, ∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) = ⟪u, v⟫ * ⟪z, w⟫ := by
    have hsplit (p) : (∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) =
        (⟪b p, z⟫ * ⟪b p, w⟫) * ∑ q, ⟪u, b q⟫ * ⟪b q, v⟫ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [real_inner_comm (b q) v]; ring
    simp only [hsplit, hp, ← Finset.sum_mul]
    simpa only [real_inner_comm z, mul_comm] using congrArg (· * ⟪u, v⟫) (hp z w)
  rw [h1, h2, h3, h4]
  ring

/-- `sharp 1 = (dim V - 2) • 1` on `⋀[ℝ]^2 V`, in every dimension `dim V : ℕ`. -/
theorem sharp_one :
    sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  have h2 := two_mul_inner_sharpBilin_ιMulti (V := V) LinearMap.IsSymmetric.one
    LinearMap.IsSymmetric.one u v z w
  rw [sharpBilin_self, ofExteriorEnd_one, contractB_constantCurvature u v z w,
    contractB_constantCurvature u v w z, real_inner_comm w z] at h2
  simp only [LinearMap.smul_apply, one_apply_eq_self, real_inner_smul_left, inner_ιMulti_two]
  linarith

/-- On the constant-curvature tensor, `Q(I) = 2 (dim V - 1) • I`. -/
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  rw [← ofExteriorEnd_one, ofExteriorEnd_reaction LinearMap.IsSymmetric.one, sharp_one, mul_one]
  have h : (2 : ℝ) • ((1 : Module.End ℝ (⋀[ℝ]^2 V)) +
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V))) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    refine LinearMap.ext fun ξ ↦ ?_
    simp only [LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self]
    module
  rw [h, map_smul]

/-- Scaling of `reactionTensor` on a constant-curvature tensor of sectional curvature `κ`. -/
theorem reactionTensor_smul_constantCurvature (κ : ℝ) :
    reactionTensor (κ • constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1) * κ ^ 2) • constantCurvature V := by
  rw [reactionTensor_smul, reactionTensor_constantCurvature, smul_smul]
  ring_nf

/-- The rank-one algebraic curvature tensor `(e₁ ∧ e₂) ⊗ (e₁ ∧ e₂)` associated to a pair of vectors
`e₁, e₂ : V`. For an orthonormal pair `e₁, e₂`, this is the curvature four-tensor of the product
`S² × ℝ^(dim V - 2)`. -/
def bivectorSq (e₁ e₂ : V) : FourTensor V :=
  ofExteriorEnd
    (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![e₁, e₂]) (ιMulti ℝ 2 ![e₁, e₂])).toLinearMap

/-- Evaluation of `bivectorSq e₁ e₂`. -/
@[simp]
theorem bivectorSq_apply (e₁ e₂ u v z w : V) :
    bivectorSq e₁ e₂ ![u, v, z, w] =
      (⟪e₁, u⟫ * ⟪e₂, v⟫ - ⟪e₁, v⟫ * ⟪e₂, u⟫) *
        (⟪e₁, z⟫ * ⟪e₂, w⟫ - ⟪e₁, w⟫ * ⟪e₂, z⟫) := by
  rw [bivectorSq, ofExteriorEnd_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, inner_ιMulti_two, inner_ιMulti_two]

/-- For every pair `e₁, e₂ : V`, `bivectorSq e₁ e₂` is an algebraic curvature tensor (the first
Bianchi identity holds by the Plücker relation). -/
theorem isAlgebraicCurvature_bivectorSq (e₁ e₂ : V) :
    IsAlgebraicCurvature (bivectorSq e₁ e₂) := by
  rw [bivectorSq, isAlgebraicCurvature_ofExteriorEnd_iff]
  refine ⟨fun x y ↦ ?_, fun u v z w ↦ ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm x]
    ring
  · simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, inner_ιMulti_two]
    ring

/-- The reaction tensor of `bivectorSq e₁ e₂` is
`2 (‖e₁‖² ‖e₂‖² - ⟪e₁, e₂⟫²) • bivectorSq e₁ e₂`. -/
theorem reactionTensor_bivectorSq (e₁ e₂ : V) :
    reactionTensor (bivectorSq e₁ e₂) =
      (2 * constantCurvature V ![e₁, e₂, e₁, e₂]) • bivectorSq e₁ e₂ := by
  set α := ιMulti ℝ 2 ![e₁, e₂]
  set T := (InnerProductSpace.rankOne ℝ α α).toLinearMap
  have hTsym : T.IsSymmetric := fun x y ↦ by
    simp only [T, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm x α]
    ring
  have hTsq : T * T = constantCurvature V ![e₁, e₂, e₁, e₂] • T := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [T, α, mul_apply_eq_comp, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, real_inner_smul_right, LinearMap.smul_apply,
      inner_ιMulti_two, constantCurvature_apply]
    rw [smul_smul, mul_comm]
  rw [bivectorSq, ofExteriorEnd_reaction hTsym, hTsq, sharp_rankOne_self α, add_zero, smul_smul,
    map_smul]

/-- For an orthonormal pair `e₁, e₂`, `Q(bivectorSq e₁ e₂) = 2 • bivectorSq e₁ e₂` (the
`S² × ℝ^(dim V - 2)` check). -/
theorem reactionTensor_bivectorSq_of_orthonormal {e₁ e₂ : V} (h : Orthonormal ℝ ![e₁, e₂]) :
    reactionTensor (bivectorSq e₁ e₂) = (2 : ℝ) • bivectorSq e₁ e₂ := by
  rw [reactionTensor_bivectorSq, constantCurvature_apply]
  have h11 : ⟪e₁, e₁⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖e₁‖ = 1 from h.1 0, one_pow]
  have h22 : ⟪e₂, e₂⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖e₂‖ = 1 from h.1 1, one_pow]
  have h12 : ⟪e₁, e₂⟫ = 0 := h.2 (show (0 : Fin 2) ≠ 1 by decide)
  have h21 : ⟪e₂, e₁⟫ = 0 := h.2 (show (1 : Fin 2) ≠ 0 by decide)
  rw [h11, h22, h12, h21]
  norm_num

end TauCeti.FourTensor
