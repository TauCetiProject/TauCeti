/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Pointwise bounds for families of Hölder coefficients

Second-order operators on `ℝⁿ = EuclideanSpace ℝ ι` have scalar Hölder coefficients `aⁱʲ` and
`bⁱ` on a metric space `X`. At each point `p : X` they assemble into the matrix `(aⁱʲ(p))` and
the vector `∑ᵢ bⁱ(p) eᵢ`. This file bounds the trace of that matrix and the norm of that vector
by the supremum-plus-Hölder norms of the coefficients, uniformly in `p`, and bounds each
coefficient entrywise in the same way. Along the segment from constant coefficients `M` to `a`,
the coefficient matrix at `p` is the corresponding point of the segment from `M` to `(aⁱʲ(p))`.
It also bounds the Hölder constant of the pairing `∑ᵢⱼ aⁱʲ H(eᵢ, eⱼ)` of a Hölder coefficient
matrix with a Hölder field `H` of bilinear maps, such as a Hessian.

## Main declarations

* `TauCeti.HolderSpace.trace_le_sum_norm`: `tr (aⁱʲ(p)) ≤ ∑ᵢ ‖aⁱⁱ‖`.
* `TauCeti.HolderSpace.norm_sum_apply_smul_single_le_sum_norm`: `‖∑ᵢ bⁱ(p) eᵢ‖ ≤ ∑ᵢ ‖bⁱ‖`.
* `TauCeti.HolderSpace.abs_apply_le_sum_sum_norm`, `TauCeti.HolderSpace.abs_apply_le_sum_norm`:
  the entrywise bounds `|aⁱʲ(p)| ≤ ∑ᵢ ∑ⱼ ‖aⁱʲ‖` and `|bⁱ(p)| ≤ ∑ᵢ ‖bⁱ‖`.
* `TauCeti.HolderSpace.of_lineMap_const_apply`: the matrix of `(1 - t) M + t a` at `p` is
  `(1 - t) M + t (aⁱʲ(p))`.
* `TauCeti.holderOnWith_sum_sum_mul_apply_single`: the Hölder bound for `∑ᵢⱼ aⁱʲ H(eᵢ, eⱼ)` on a
  set, from Hölder constants and bounds of `a` and `H`.
-/

public section

namespace TauCeti.HolderSpace

open scoped NNReal

variable {α : ℝ≥0} {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]

/-- The trace of the coefficient matrix `(aⁱʲ(p))` is at most `∑ᵢ ‖aⁱⁱ‖`. -/
theorem trace_le_sum_norm (a : ι → ι → HolderSpace α X ℝ) (p : X) :
    (Matrix.of fun i j ↦ a i j p).trace ≤ ∑ i, ‖a i i‖ :=
  Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans (norm_apply_le (a i i) _)

/-- The drift vector `∑ᵢ bⁱ(p) eᵢ` has norm at most `∑ᵢ ‖bⁱ‖`. -/
theorem norm_sum_apply_smul_single_le_sum_norm [DecidableEq ι] (b : ι → HolderSpace α X ℝ)
    (p : X) : ‖∑ i, b i p • EuclideanSpace.single i (1 : ℝ)‖ ≤ ∑ i, ‖b i‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by
    simpa [norm_smul] using norm_apply_le (b i) _)

/-- Each drift coefficient is bounded pointwise by the sum of their norms:
`|bⁱ(p)| ≤ ∑ᵢ ‖bⁱ‖`. -/
theorem abs_apply_le_sum_norm (b : ι → HolderSpace α X ℝ) (p : X) (i : ι) :
    |b i p| ≤ ∑ i, ‖b i‖ :=
  (abs_apply_le_norm (b i) p).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (b i)) (Finset.mem_univ i))

/-- Each diffusion coefficient is bounded pointwise by the sum of their norms:
`|aⁱʲ(p)| ≤ ∑ᵢ ∑ⱼ ‖aⁱʲ‖`. -/
theorem abs_apply_le_sum_sum_norm (a : ι → ι → HolderSpace α X ℝ) (p : X) (i j : ι) :
    |a i j p| ≤ ∑ i, ∑ j, ‖a i j‖ :=
  (abs_apply_le_sum_norm (a i) p j).trans
    (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg (a i j))
      (Finset.mem_univ i))

omit [Fintype ι] in
/-- Along the segment from the constant coefficients `M` to `a`, the coefficient matrix at `p` is
`(1 - t) M + t (aⁱʲ(p))`. With `M = 1` this is the segment from the Laplacian or heat operator used
by the method of continuity. -/
theorem of_lineMap_const_apply (M : Matrix ι ι ℝ) (a : ι → ι → HolderSpace α X ℝ) (t : ℝ)
    (p : X) :
    (Matrix.of fun i j ↦ AffineMap.lineMap (fun i j ↦ const (M i j)) a t i j p) =
      AffineMap.lineMap M (Matrix.of fun i j ↦ a i j p) t := by
  ext i j
  simp [AffineMap.lineMap_apply_module]

end TauCeti.HolderSpace

namespace TauCeti

open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [PseudoMetricSpace X]

/-- **Hölder bound for a coefficient matrix paired with a field of bilinear maps.** If the entries
of `a` are `α`-Hölder on a set `s` with constant `L` and bounded by `M` there, and the field `H` of
bilinear maps on `EuclideanSpace ℝ ι` is `α`-Hölder on `s` with constant `J` and bounded by `B`
there, then `∑ᵢⱼ aᵢⱼ H(eᵢ, eⱼ)` is `α`-Hölder on `s` with constant `(card ι)² (M J + B L)`. For
`H = D²u` this is the Hölder bound for `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. -/
theorem holderOnWith_sum_sum_mul_apply_single {α L M J B : ℝ≥0} {s : Set X}
    {a : X → Matrix ι ι ℝ} {H : X → EuclideanSpace ℝ ι [×2]→L[ℝ] ℝ}
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s) (hM : ∀ x ∈ s, ∀ i j, |a x i j| ≤ M)
    (hJ : HolderOnWith J α H s) (hB : ∀ x ∈ s, ‖H x‖ ≤ B) :
    HolderOnWith ((Fintype.card ι : ℝ≥0) ^ 2 * (M * J + B * L)) α
      (fun x => ∑ i, ∑ j, a x i j *
        H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
  have hterm (i j : ι) : HolderOnWith (M * J + B * L) α (fun x => a x i j *
      H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
    have hh : HolderOnWith J α (fun x => H x
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
      simpa using hJ.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j
    have hp := (ContinuousLinearMap.mul ℝ ℝ).holderOnWith_comp₂ (hL i j) hh
      (Mf := M) (Mg := B)
      (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx i j)
      (fun x hx => by
        simpa using ((H x).norm_apply_orthonormalBasis_le (EuclideanSpace.basisFun _ ℝ) i j).trans
          (hB x hx))
    simpa only [ContinuousLinearMap.opNNNorm_mul, one_mul,
      ContinuousLinearMap.mul_apply'] using hp
  -- Sum the entries as Hölder functions on the subtype `s`.
  refine HolderWith.restrict_iff.1 ((HolderWith.sum fun i _ => HolderWith.sum fun j _ =>
    (hterm i j).holderWith).mono (le_of_eq (by simp [Finset.card_univ]; ring)))

end TauCeti
