/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Multilinear evaluation and orthonormal-basis bounds for iterated gradients

An iterated gradient `TauCeti.IteratedGradient E j` has `j` outer continuous-linear direction
slots above a vector in `E`. Pairing that vector with one final direction evaluates the field on a
tuple `m : Fin (j + 1) → E` of directions (`TauCeti.IteratedGradient.evalL`). When `E` is complete,
Riesz representation and left uncurrying assemble this evaluation into a linear isometric
equivalence `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ` between
`TauCeti.IteratedGradient E j` and the space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear
maps, sending `TauCeti.iteratedGradientChain f j x` to `iteratedFDeriv ℝ (j + 1) f x` without any
differentiability hypothesis. Consequently, `TauCeti.iteratedGradientChain f k x` and
`iteratedFDeriv ℝ (k + 1) f x` have the same norm (`TauCeti.norm_iteratedGradientChain`) and the
same difference norm
(`TauCeti.norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub`).

Precomposing with a single outer contraction `TauCeti.IteratedGradient.contractL j 1 h` curries `h`
into the first argument of the corresponding continuous multilinear map
(`TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ_contractL_one`). Along a finite orthonormal
basis `b` of `E`, the operator norm of an iterated gradient and the sum of the norms of its basis
entries are comparable with explicit constants (`1` and `(card ι) ^ (j + 1)`).

## Main declarations

* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ`: the linear isometric equivalence
  `IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ)` when `E` is complete.
* `TauCeti.IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain`: under this
  equivalence, `iteratedGradientChain f j x` corresponds to `iteratedFDeriv ℝ (j + 1) f x`.
* `TauCeti.norm_iteratedFDeriv_iteratedGradientChain`, `TauCeti.norm_iteratedGradientChain`,
  `TauCeti.iteratedGradientChain_sub`, and
  `TauCeti.norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub`:
  pointwise norm and difference comparisons between `iteratedGradientChain` and `iteratedFDeriv`.
* `TauCeti.IteratedGradient.norm_le_sum_norm_evalL_apply_orthonormalBasis` and
  `TauCeti.IteratedGradient.sum_norm_evalL_apply_orthonormalBasis_le`: equivalence between the
  operator norm of an iterated gradient and the `ℓ¹` sum of its entries along a finite orthonormal
  basis.
-/

public section

noncomputable section

namespace TauCeti.IteratedGradient

open scoped InnerProductSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any entry of an iterated gradient along vectors of an orthonormal basis has norm at most the
operator norm of the field. -/
theorem norm_evalL_apply_orthonormalBasis_le {ι : Type*} [Fintype ι] (j : ℕ)
    (G : IteratedGradient E j) (b : OrthonormalBasis ι ℝ E) (r : Fin (j + 1) → ι) :
    ‖evalL j (fun k => b (r k)) G‖ ≤ ‖G‖ := by
  refine (norm_evalL_apply_le j (fun k => b (r k)) G).trans_eq ?_
  rw [Finset.prod_eq_one fun k _ => b.orthonormal.1 (r k), mul_one]

/-- The sum of the norms of all entries of `G : IteratedGradient E j` along an orthonormal basis
`b` is at most `(card ι) ^ (j + 1) * ‖G‖`. -/
theorem sum_norm_evalL_apply_orthonormalBasis_le {ι : Type*} [Fintype ι] (j : ℕ)
    (G : IteratedGradient E j) (b : OrthonormalBasis ι ℝ E) :
    ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖ ≤
      (Fintype.card ι : ℝ) ^ (j + 1) * ‖G‖ := by
  calc
    ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖
      ≤ ∑ _r : Fin (j + 1) → ι, ‖G‖ :=
        Finset.sum_le_sum fun r _ => norm_evalL_apply_orthonormalBasis_le j G b r
    _ = (Fintype.card ι : ℝ) ^ (j + 1) * ‖G‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]

end InnerProductSpace

section CompleteSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On a complete real inner product space, `toContinuousMultilinearMap E j` is surjective. -/
theorem toContinuousMultilinearMap_surjective :
    (j : ℕ) → Function.Surjective (toContinuousMultilinearMap E j)
  | 0 => by
      rw [toContinuousMultilinearMap_zero, LinearIsometry.coe_comp,
        ← InnerProductSpace.toLinearIsometry_toDual,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry]
      exact (continuousMultilinearCurryFin1 ℝ E ℝ).symm.surjective.comp
        (InnerProductSpace.toDual ℝ E).surjective
  | j + 1 => by
      let e : IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ) :=
        LinearIsometryEquiv.ofSurjective (toContinuousMultilinearMap E j)
          (toContinuousMultilinearMap_surjective j)
      have h : ⇑(toContinuousMultilinearMap E (j + 1)) =
          ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E) ℝ).symm ∘
            ⇑((ContinuousLinearEquiv.refl ℝ E).arrowCongr e.toContinuousLinearEquiv) := by
        ext G m
        rw [Function.comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply,
          ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
          ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.coe_ofSurjective, toContinuousMultilinearMap_succ_apply]
      rw [h]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1 + 1) => E)
        ℝ).symm.surjective.comp
        ((ContinuousLinearEquiv.refl ℝ E).arrowCongr e.toContinuousLinearEquiv).surjective

/-- On a complete real inner product space, `IteratedGradient E j` is linearly isometric to the
space `E [×(j + 1)]→L[ℝ] ℝ` of scalar continuous multilinear maps in `j + 1` arguments. -/
def toContinuousMultilinearMapₗᵢ (j : ℕ) :
    IteratedGradient E j ≃ₗᵢ[ℝ] (E [×(j + 1)]→L[ℝ] ℝ) :=
  LinearIsometryEquiv.ofSurjective (toContinuousMultilinearMap E j)
    (toContinuousMultilinearMap_surjective E j)

variable {E}

/-- As a function, `toContinuousMultilinearMapₗᵢ E j` agrees with
`toContinuousMultilinearMap E j`. -/
@[simp]
theorem coe_toContinuousMultilinearMapₗᵢ (j : ℕ) :
    ⇑(toContinuousMultilinearMapₗᵢ E j) = toContinuousMultilinearMap E j :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- The underlying linear isometry of `toContinuousMultilinearMapₗᵢ E j` is
`toContinuousMultilinearMap E j`. -/
@[simp]
theorem toLinearIsometry_toContinuousMultilinearMapₗᵢ (j : ℕ) :
    (toContinuousMultilinearMapₗᵢ E j).toLinearIsometry = toContinuousMultilinearMap E j :=
  LinearIsometry.ext fun G => congrFun (coe_toContinuousMultilinearMapₗᵢ j) G

/-- Evaluating `(toContinuousMultilinearMapₗᵢ E j).symm M` along `m` recovers `M m`. -/
@[simp]
theorem evalL_toContinuousMultilinearMapₗᵢ_symm (j : ℕ) (m : Fin (j + 1) → E)
    (M : E [×(j + 1)]→L[ℝ] ℝ) :
    evalL j m ((toContinuousMultilinearMapₗᵢ E j).symm M) = M m := by
  rw [← toContinuousMultilinearMap_apply, ← coe_toContinuousMultilinearMapₗᵢ,
    LinearIsometryEquiv.apply_symm_apply]

/-- Contracting one outer slot of `G` at `h` curries `h` into the first argument of the
corresponding continuous multilinear map. -/
theorem toContinuousMultilinearMapₗᵢ_contractL_one (j : ℕ) (h : E)
    (G : IteratedGradient E (j + 1)) :
    toContinuousMultilinearMapₗᵢ E j (contractL j 1 h G) =
      (toContinuousMultilinearMapₗᵢ E (j + 1) G).curryLeft h := by
  ext m
  rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_apply,
    ContinuousMultilinearMap.curryLeft_apply, coe_toContinuousMultilinearMapₗᵢ,
    toContinuousMultilinearMap_apply, evalL_contractL_one_apply]

/-- Under `toContinuousMultilinearMapₗᵢ`, the classical `j`th iterated-gradient field of any
scalar function `f` at `x` is `iteratedFDeriv ℝ (j + 1) f x`. No differentiability assumption is
needed: both sides use the `fderiv` junk-value convention at each step, vanishing whenever the
preceding stage fails to be differentiable at `x`. -/
theorem toContinuousMultilinearMapₗᵢ_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E) :
    toContinuousMultilinearMapₗᵢ E j (iteratedGradientChain f j x) =
      iteratedFDeriv ℝ (j + 1) f x := by
  induction j generalizing x with
  | zero =>
      ext m
      rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_apply, evalL_zero_apply,
        iteratedGradientChain_zero, iteratedFDeriv_one_apply, gradient, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
  | succ j ih =>
      have hfun : (toContinuousMultilinearMapₗᵢ E j ∘ iteratedGradientChain f j) =
          iteratedFDeriv ℝ (j + 1) f := funext ih
      ext m
      have hfd := congrArg (fun g : E → E [×(j + 1)]→L[ℝ] ℝ => fderiv ℝ g x (m 0) (Fin.tail m)) hfun
      rw [LinearIsometryEquiv.comp_fderiv] at hfd
      rw [coe_toContinuousMultilinearMapₗᵢ, toContinuousMultilinearMap_apply, evalL_succ_apply,
        iteratedGradientChain_succ, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        continuousMultilinearCurryLeftEquiv_symm_apply]
      exact (toContinuousMultilinearMap_apply j
        (fderiv ℝ (iteratedGradientChain f j) x (m 0)) (Fin.tail m)).symm.trans
        ((congrFun (congrArg DFunLike.coe (congrFun (coe_toContinuousMultilinearMapₗᵢ j) _))
          (Fin.tail m)).symm.trans hfd)

/-- Evaluating `iteratedGradientChain f j x` along `m` gives `iteratedFDeriv ℝ (j + 1) f x m`. -/
theorem evalL_iteratedGradientChain (f : E → ℝ) (j : ℕ) (x : E) (m : Fin (j + 1) → E) :
    evalL j m (iteratedGradientChain f j x) = iteratedFDeriv ℝ (j + 1) f x m := by
  rw [← toContinuousMultilinearMap_apply, ← coe_toContinuousMultilinearMapₗᵢ,
    toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

end CompleteSpace

section OrthonormalBasisLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator norm of an iterated gradient is bounded by the sum of the norms of its entries
along a finite orthonormal basis `b`. -/
theorem norm_le_sum_norm_evalL_apply_orthonormalBasis {ι : Type*} [Fintype ι] (j : ℕ)
    (G : IteratedGradient E j) (b : OrthonormalBasis ι ℝ E) :
    ‖G‖ ≤ ∑ r : Fin (j + 1) → ι, ‖evalL j (fun k => b (r k)) G‖ := by
  rw [← (toContinuousMultilinearMap E j).norm_map G]
  convert (toContinuousMultilinearMap E j G).opNorm_le_sum_norm_apply_orthonormalBasis
    (fun _ => b)
  simp only [toContinuousMultilinearMap_apply]

end OrthonormalBasisLowerBound

end TauCeti.IteratedGradient

namespace TauCeti

section Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking `i` further derivatives of the `k`th iterated-gradient field has the same norm as
taking `i + k + 1` derivatives of the original scalar function. No smoothness is needed. -/
theorem norm_iteratedFDeriv_iteratedGradientChain (f : E → ℝ) (i k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (iteratedGradientChain f k) x‖ =
      ‖iteratedFDeriv ℝ (i + k + 1) f x‖ := by
  induction k generalizing i with
  | zero =>
      rw [iteratedGradientChain_zero]
      -- The gradient is the inverse Riesz isometry applied to the Fréchet derivative.
      exact ((InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left
        (fderiv ℝ f) x i).trans norm_iteratedFDeriv_fderiv
  | succ k ih =>
      rw [iteratedGradientChain_succ, norm_iteratedFDeriv_fderiv]
      exact (ih (i + 1)).trans (congrArg
        (fun j => ‖iteratedFDeriv ℝ (j + 1) f x‖) (by omega))

/-- The nested iterated-gradient field has the same norm as the corresponding multilinear
derivative of the scalar function. -/
@[simp]
theorem norm_iteratedGradientChain (f : E → ℝ) (k : ℕ) (x : E) :
    ‖iteratedGradientChain f k x‖ = ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  rw [← (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).norm_map,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

/-- Iterated-gradient fields through order `k + 1` preserve subtraction of scalar functions
that are `C^{k+1}` at the point of evaluation. -/
@[simp]
theorem iteratedGradientChain_sub {f g : E → ℝ} {x : E}
    (k : ℕ) (hf : ContDiffAt ℝ (k + 1) f x) (hg : ContDiffAt ℝ (k + 1) g x) :
    iteratedGradientChain (f - g) k x =
      iteratedGradientChain f k x - iteratedGradientChain g k x := by
  refine (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).injective ?_
  rw [map_sub, IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]
  exact fun_iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hg.of_le (by simp))

/-- The order-`k + 1` iterated-gradient fields of two scalar functions have the same difference
norm at any point as their multilinear derivatives. This identifies the error seminorms in smooth
approximation. -/
theorem norm_iteratedGradientChain_sub_iteratedGradientChain_eq_norm_iteratedFDeriv_sub
    {f g : E → ℝ} {x : E} (k : ℕ) :
    ‖iteratedGradientChain f k x - iteratedGradientChain g k x‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) g x‖ := by
  rw [← (IteratedGradient.toContinuousMultilinearMapₗᵢ E k).norm_map, map_sub,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain,
    IteratedGradient.toContinuousMultilinearMapₗᵢ_iteratedGradientChain]

end Classical

end TauCeti
