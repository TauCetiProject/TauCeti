/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Parseval identities for functionals and coisometric contractions

Mathlib (`Mathlib.Analysis.InnerProductSpace.l2Space`) provides the norm-square Parseval identities
for a Hilbert basis (`HilbertBasis.hasSum_norm_inner_sq`, `HilbertBasis.tsum_norm_inner_sq`,
`HilbertBasis.summable_norm_inner_sq`, and `HilbertBasis.tsum_eNorm_inner_sq`). This file supplies
the functional Parseval identity, a Bessel-type summability statement for functionals, finite
coisometric contractions, and a Cauchy–Schwarz bound for Hilbert basis coordinates:

* For a continuous linear functional `A` on a finite orthonormal basis, the squared values
  `‖A (b i)‖ ^ 2` sum to `‖A‖ ^ 2` (`OrthonormalBasis.sum_sq_norm_apply_eq_norm_sq`).
* On finite orthonormal bases, if `f : E → F` has an inner-product-preserving adjoint `g : F → E`
  (`⟪f x, y⟫ = ⟪x, g y⟫` and `⟪g x, g y⟫ = ⟪x, y⟫`), then pulling linear or bilinear maps into an
  inner product space back along `f` preserves their inner-product contractions over orthonormal
  bases.
* For a continuous linear functional `φ` on an orthonormal family in a (possibly incomplete,
  seminormed) inner product space, `‖φ (v i)‖ ^ 2` is summable
  (`Orthonormal.summable_norm_apply_sq`).
* For a Hilbert basis `b`, the products `⟪x, b i⟫ ⟪b i, y⟫` are absolutely summable with sum of
  norms at most `‖x‖ ‖y‖` (`HilbertBasis.tsum_norm_inner_mul_inner_le`).

## Main declarations

* `OrthonormalBasis.sum_sq_norm_apply_eq_norm_sq` — the squared values of a continuous linear
  functional on a finite orthonormal basis sum to the square of its operator norm.
* `OrthonormalBasis.sum_inner_comp_eq_of_inner_eq` — coisometric Parseval contraction of two
  linear maps along a map whose adjoint preserves inner products.
* `OrthonormalBasis.sum_sum_inner_comp_eq_of_inner_eq` — double coisometric Parseval contraction
  of two bilinear maps along a map whose adjoint preserves inner products.
* `HilbertBasis.summable_norm_inner_mul_inner` and `HilbertBasis.tsum_norm_inner_mul_inner_le` —
  the products `⟪x, bᵢ⟫ ⟪bᵢ, y⟫` are absolutely summable, with sum of norms at most `‖x‖ ‖y‖`.
* `Orthonormal.summable_norm_apply_sq` — Bessel's inequality for a functional: the squared values
  of a continuous linear functional on an orthonormal family are summable.
-/

public section

namespace TauCeti

variable {ι : Type*} {𝕜 : Type*} {E : Type*} [RCLike 𝕜]

section Normed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The products `⟪x, bᵢ⟫ ⟪bᵢ, y⟫` of the coordinates of two vectors in a Hilbert basis are
absolutely summable; `HilbertBasis.hasSum_inner_mul_inner` computes their sum. -/
theorem _root_.HilbertBasis.summable_norm_inner_mul_inner (b : _root_.HilbertBasis ι 𝕜 E)
    (x y : E) : Summable fun i ↦ ‖inner 𝕜 x (b i) * inner 𝕜 (b i) y‖ := by
  simpa only [b.repr_apply_apply, norm_mul, norm_inner_symm x] using
    lp.summable_mul (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
      (b.repr x) (b.repr y)

/-- **Cauchy–Schwarz for Hilbert basis coordinates.** `∑ᵢ ‖⟪x, bᵢ⟫ ⟪bᵢ, y⟫‖ ≤ ‖x‖ ‖y‖`. -/
theorem _root_.HilbertBasis.tsum_norm_inner_mul_inner_le (b : _root_.HilbertBasis ι 𝕜 E)
    (x y : E) : ∑' i, ‖inner 𝕜 x (b i) * inner 𝕜 (b i) y‖ ≤ ‖x‖ * ‖y‖ := by
  simpa only [b.repr_apply_apply, b.repr.norm_map, norm_mul, norm_inner_symm x] using
    lp.tsum_mul_le_mul_norm' (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
      (b.repr x) (b.repr y)

/-- **Parseval's identity for a functional.** The squared values of a continuous linear functional
on a finite orthonormal basis sum to the square of its operator norm: by the Riesz representation,
they are the squared coordinates of the representing vector. -/
theorem _root_.OrthonormalBasis.sum_sq_norm_apply_eq_norm_sq [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] 𝕜) :
    ∑ i, ‖A (b i)‖ ^ 2 = ‖A‖ ^ 2 := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  rw [← (InnerProductSpace.toDual 𝕜 E).symm.norm_map A, ← b.sum_sq_norm_inner_left]
  simp_rw [InnerProductSpace.toDual_symm_apply]

/-- **Coisometric Parseval contraction for linear maps.** If `f : E → F` has an
inner-product-preserving adjoint `g : F → E` (`⟪f x, y⟫ = ⟪x, g y⟫` and `⟪g x, g y⟫ = ⟪x, y⟫`),
then pulling two linear maps `φ, ψ : F →ₗ[𝕜] G` back along `f` preserves their inner-product
contraction over orthonormal bases:
`∑ p, ⟪φ (f (bE p)), ψ (f (bE p))⟫ = ∑ a, ⟪φ (bF a), ψ (bF a)⟫`. -/
theorem _root_.OrthonormalBasis.sum_inner_comp_eq_of_inner_eq [Fintype ι] {κ F G : Type*}
    [Fintype κ] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (bE : OrthonormalBasis ι 𝕜 E) (bF : OrthonormalBasis κ 𝕜 F)
    {f : E → F} {g : F → E} (hfg : ∀ x y, inner 𝕜 (f x) y = inner 𝕜 x (g y))
    (hg : ∀ x y, inner 𝕜 (g x) (g y) = inner 𝕜 x y)
    (φ ψ : F →ₗ[𝕜] G) :
    ∑ p, inner 𝕜 (φ (f (bE p))) (ψ (f (bE p))) = ∑ a, inner 𝕜 (φ (bF a)) (ψ (bF a)) := by
  classical
  have hexp (h : F →ₗ[𝕜] G) (p : ι) :
      h (f (bE p)) = ∑ a, inner 𝕜 (g (bF a)) (bE p) • h (bF a) := by
    conv_lhs => rw [← bF.sum_repr' (f (bE p)), map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, ← inner_conj_symm (bF a) (f (bE p)), hfg, inner_conj_symm]
  simp_rw [hexp φ, hexp ψ, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_conj_symm (bE _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  have hsum : ∀ c,
      (∑ p, inner 𝕜 (bE p) (g (bF a)) *
          (inner 𝕜 (g (bF c)) (bE p) * inner 𝕜 (φ (bF a)) (ψ (bF c)))) =
        inner 𝕜 (bF c) (bF a) * inner 𝕜 (φ (bF a)) (ψ (bF c)) := by
    intro c
    have hp : (∑ p, inner 𝕜 (g (bF c)) (bE p) * inner 𝕜 (bE p) (g (bF a))) =
        inner 𝕜 (bF c) (bF a) := by
      rw [bE.sum_inner_mul_inner, hg]
    calc (∑ p, inner 𝕜 (bE p) (g (bF a)) *
            (inner 𝕜 (g (bF c)) (bE p) * inner 𝕜 (φ (bF a)) (ψ (bF c))))
        = (∑ p, inner 𝕜 (g (bF c)) (bE p) * inner 𝕜 (bE p) (g (bF a))) *
            inner 𝕜 (φ (bF a)) (ψ (bF c)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ ↦ by ring
      _ = inner 𝕜 (bF c) (bF a) * inner 𝕜 (φ (bF a)) (ψ (bF c)) := by rw [hp]
  simp_rw [hsum, orthonormal_iff_ite.mp bF.orthonormal]
  simp

/-- **Double coisometric Parseval contraction for bilinear maps.** If `f : E → F` has an
inner-product-preserving adjoint `g : F → E` (`⟪f x, y⟫ = ⟪x, g y⟫` and `⟪g x, g y⟫ = ⟪x, y⟫`),
then pulling two bilinear maps `M, N : F →ₗ[𝕜] F →ₗ[𝕜] G` back along `f` preserves their double
inner-product contraction over orthonormal bases:
`∑ p, ∑ q, ⟪M (f (bE p)) (f (bE q)), N (f (bE p)) (f (bE q))⟫ =
  ∑ a, ∑ c, ⟪M (bF a) (bF c), N (bF a) (bF c)⟫`. -/
theorem _root_.OrthonormalBasis.sum_sum_inner_comp_eq_of_inner_eq [Fintype ι] {κ F G : Type*}
    [Fintype κ] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (bE : OrthonormalBasis ι 𝕜 E) (bF : OrthonormalBasis κ 𝕜 F)
    {f : E → F} {g : F → E} (hfg : ∀ x y, inner 𝕜 (f x) y = inner 𝕜 x (g y))
    (hg : ∀ x y, inner 𝕜 (g x) (g y) = inner 𝕜 x y)
    (M N : F →ₗ[𝕜] F →ₗ[𝕜] G) :
    (∑ p, ∑ q, inner 𝕜 (M (f (bE p)) (f (bE q))) (N (f (bE p)) (f (bE q)))) =
      ∑ a, ∑ c, inner 𝕜 (M (bF a) (bF c)) (N (bF a) (bF c)) := by
  have hinner (p : ι) :
      (∑ q, inner 𝕜 (M (f (bE p)) (f (bE q))) (N (f (bE p)) (f (bE q)))) =
        ∑ c, inner 𝕜 (M (f (bE p)) (bF c)) (N (f (bE p)) (bF c)) :=
    bE.sum_inner_comp_eq_of_inner_eq bF hfg hg (M (f (bE p))) (N (f (bE p)))
  simp_rw [hinner]
  rw [Finset.sum_comm]
  have houter (c : κ) :
      (∑ p, inner 𝕜 (M (f (bE p)) (bF c)) (N (f (bE p)) (bF c))) =
        ∑ a, inner 𝕜 (M (bF a) (bF c)) (N (bF a) (bF c)) :=
    bE.sum_inner_comp_eq_of_inner_eq bF hfg hg (M.flip (bF c)) (N.flip (bF c))
  simp_rw [houter]
  exact Finset.sum_comm

end Normed

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Bessel's inequality for a functional.** The values of a continuous linear functional `φ` on
an orthonormal family are square summable. The space need not be complete, and its seminorm need
not be a norm. -/
theorem _root_.Orthonormal.summable_norm_apply_sq {v : ι → E} (hv : Orthonormal 𝕜 v)
    (φ : StrongDual 𝕜 E) : Summable fun i ↦ ‖φ (v i)‖ ^ 2 := by
  -- Extend `φ` to the completion and represent the extension by a vector `u` (Riesz), so that
  -- `‖φ x‖ = ‖⟪x, u⟫‖`; the claim is then Bessel's inequality for `u` and the image of `v`.
  let u := (InnerProductSpace.toDual 𝕜 (UniformSpace.Completion E)).symm φ.fromCompletion
  have hu (x : E) : ‖φ x‖ = ‖inner 𝕜 (x : UniformSpace.Completion E) u‖ := by
    rw [norm_inner_symm, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.fromCompletion_apply_coe]
  have hv' := hv.comp_linearIsometry (UniformSpace.Completion.toComplₗᵢ (𝕜 := 𝕜))
  simpa only [hu, Function.comp_apply, UniformSpace.Completion.coe_toComplₗᵢ] using
    hv'.inner_products_summable u

end Seminormed

end TauCeti
