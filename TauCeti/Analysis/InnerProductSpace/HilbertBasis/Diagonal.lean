/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Diagonal operators in a Hilbert basis

A Hilbert basis `b : HilbertBasis ι 𝕜 E` identifies `E` isometrically with `ℓ²(ι, 𝕜)` through
`b.repr`. A bounded family `m ∈ ℓ^∞(ι, 𝕜)` then defines the **diagonal operator** `b.diagonal m`
on `E`, which multiplies the `i`-th coordinate by `m i`: it is the diagonal operator
`lp.diagonalCLM m` transported along `b.repr`. The map `m ↦ b.diagonal m` is a unital algebra
homomorphism from `ℓ^∞(ι, 𝕜)` to the bounded operators on `E`, so any two diagonal operators
commute. The operator norm of `b.diagonal m` is the supremum norm of `m`, the operator determines
`m`, and it acts on the basis vectors by `b.diagonal m (b i) = m i • b i`.

Diagonal operators are continuous in their entries for the strong operator topology on bounded
sets: if `m_a → m` pointwise on `ι` and `‖m_a‖ ≤ C`, then `b.diagonal m_a x → b.diagonal m x` for
every `x` (`HilbertBasis.tendsto_diagonal_apply`). Fourier multipliers on `L²` of the torus are
the diagonal operators in the Fourier basis.

## Main declarations

* `HilbertBasis.diagonal`: the algebra homomorphism `m ↦ b.diagonal m`.
* `HilbertBasis.repr_diagonal`: the coordinates of `b.diagonal m x` are `m i * b.repr x i`.
* `HilbertBasis.diagonal_apply_self`: `b.diagonal m (b i) = m i • b i`.
* `HilbertBasis.hasSum_diagonal`: the expansion of `b.diagonal m x` in the basis.
* `HilbertBasis.norm_diagonal`: `‖b.diagonal m‖ = ‖m‖`.
* `HilbertBasis.diagonal_injective`: the entries are determined by the operator.
* `HilbertBasis.tendsto_diagonal_apply`: strong continuity in the entries.
-/

public section

noncomputable section

open Filter Topology
open scoped lp ENNReal

namespace HilbertBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (b : HilbertBasis ι 𝕜 E)

/-- The **diagonal operator** in the Hilbert basis `b` with bounded entries `m : ι → 𝕜`: the
operator multiplying the `i`-th coordinate by `m i`. It is the diagonal operator `lp.diagonalCLM m`
transported along the isometry `b.repr : E ≃ ℓ²(ι, 𝕜)`, and `m ↦ b.diagonal m` is a unital algebra
homomorphism from `ℓ^∞(ι, 𝕜)` to the bounded operators on `E`. -/
def diagonal : ℓ^∞(ι, 𝕜) →ₐ[𝕜] E →L[𝕜] E where
  toFun m := (b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap : ℓ²(ι, 𝕜) →L[𝕜] E) ∘L
    lp.diagonalCLM (p := 2) m ∘L b.repr.toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by
    ext1 x
    simp
  map_mul' m₁ m₂ := by
    ext1 x
    simp [lp.diagonalCLM_mul]
  map_zero' := by
    ext1 x
    simp
  map_add' m₁ m₂ := by
    ext1 x
    simp
  commutes' c := by
    ext1 x
    rw [Algebra.algebraMap_eq_smul_one, lp.diagonalCLM_smul, lp.diagonalCLM_one]
    simp

/-- The coordinates of `b.diagonal m x` are `m i * b.repr x i`. -/
@[simp]
theorem repr_diagonal (m : ℓ^∞(ι, 𝕜)) (x : E) (i : ι) :
    b.repr (b.diagonal m x) i = m i * b.repr x i := by
  simp [diagonal]

/-- A diagonal operator multiplies the basis vector `b i` by `m i`. -/
@[simp]
theorem diagonal_apply_self (m : ℓ^∞(ι, 𝕜)) (i : ι) : b.diagonal m (b i) = m i • b i := by
  classical
  apply b.repr.injective
  ext k
  simp only [repr_diagonal, HilbertBasis.repr_self, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

/-- The expansion of `b.diagonal m x` in the basis: its `i`-th term is `m i * b.repr x i` times
`b i`. -/
theorem hasSum_diagonal (m : ℓ^∞(ι, 𝕜)) (x : E) :
    HasSum (fun i ↦ (m i * b.repr x i) • b i) (b.diagonal m x) := by
  simpa using b.hasSum_repr (b.diagonal m x)

/-- The operator norm of a diagonal operator is the supremum norm of its entries. -/
@[simp]
theorem norm_diagonal (m : ℓ^∞(ι, 𝕜)) : ‖b.diagonal m‖ = ‖m‖ := by
  -- Through the isometry `b.repr`, `b.diagonal m` is the diagonal operator with entries `m`.
  have key : ∀ x, b.repr (b.diagonal m x) = lp.diagonalCLM (p := 2) m (b.repr x) := fun x ↦ by
    ext i
    simp
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m) fun x ↦ ?_) ?_
  · rw [← LinearIsometryEquiv.norm_map b.repr, key, ← lp.norm_diagonalCLM (p := 2) m,
      ← LinearIsometryEquiv.norm_map b.repr x]
    exact ContinuousLinearMap.le_opNorm _ _
  · rw [← lp.norm_diagonalCLM (p := 2) m]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
    rw [← b.repr.apply_symm_apply y, ← key, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.le_opNorm _ _

/-- A diagonal operator determines its entries. -/
theorem diagonal_injective : Function.Injective (b.diagonal : ℓ^∞(ι, 𝕜) → E →L[𝕜] E) := by
  classical
  intro m₁ m₂ h
  ext i
  have h' := congrArg (fun T ↦ b.repr (T (b i)) i) h
  simpa only [repr_diagonal, HilbertBasis.repr_self, lp.single_apply, Pi.single_eq_same,
    mul_one] using h'

/-- Two diagonal operators in the same basis are equal exactly when their entries are equal. -/
@[simp]
theorem diagonal_inj {m₁ m₂ : ℓ^∞(ι, 𝕜)} : b.diagonal m₁ = b.diagonal m₂ ↔ m₁ = m₂ :=
  b.diagonal_injective.eq_iff

/-- Any two diagonal operators in the same basis commute. -/
theorem commute_diagonal (m₁ m₂ : ℓ^∞(ι, 𝕜)) : Commute (b.diagonal m₁) (b.diagonal m₂) :=
  (Commute.all m₁ m₂).map b.diagonal

/-- **Strong continuity of diagonal operators in the entries.** If the entries `m a` are bounded
uniformly by `C` and converge pointwise on `ι` to `m₀`, then `b.diagonal (m a) x → b.diagonal m₀ x`
for every `x`. -/
theorem tendsto_diagonal_apply {α : Type*} {l : Filter α} {m : α → ℓ^∞(ι, 𝕜)} {m₀ : ℓ^∞(ι, 𝕜)}
    {C : ℝ} (hC : ∀ᶠ a in l, ‖m a‖ ≤ C) (hm : ∀ i, Tendsto (fun a ↦ m a i) l (𝓝 (m₀ i)))
    (x : E) : Tendsto (fun a ↦ b.diagonal (m a) x) l (𝓝 (b.diagonal m₀ x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Parseval's identity in the basis `b`.
  have hparseval : ∀ y : E, HasSum (fun i ↦ ‖b.repr y i‖ ^ 2) (‖y‖ ^ 2) := fun y ↦ by
    have h := lp.hasSum_norm (p := 2) (by simp) (b.repr y)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h
  -- The squared distance is the tail-dominated series `∑ᵢ ‖(m a i - m₀ i) xᵢ‖²`.
  have hsq : ∀ a, ‖b.diagonal (m a) x - b.diagonal m₀ x‖ ^ 2 =
      ∑' i, ‖(m a i - m₀ i) * b.repr x i‖ ^ 2 := fun a ↦ by
    rw [← (hparseval _).tsum_eq]
    congr 1
    ext i
    simp [sub_mul]
  have hsum : Summable fun i ↦ ((C + ‖m₀‖) * ‖b.repr x i‖) ^ 2 := by
    simpa [mul_pow] using ((hparseval x).summable.mul_left ((C + ‖m₀‖) ^ 2))
  have hlim : Tendsto (fun a ↦ ∑' i, ‖(m a i - m₀ i) * b.repr x i‖ ^ 2) l (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun a i ↦
        ‖(m a i - m₀ i) * b.repr x i‖ ^ 2) (g := fun _ ↦ (0 : ℝ)) hsum
      (fun i ↦ by
        have h := ((hm i).sub_const (m₀ i)).mul_const (b.repr x i)
        simpa using (h.norm.pow 2))
      (hC.mono fun a ha i ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
        gcongr
        calc ‖m a i - m₀ i‖ ≤ ‖m a i‖ + ‖m₀ i‖ := norm_sub_le _ _
          _ ≤ ‖m a‖ + ‖m₀‖ := add_le_add (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
              (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
          _ ≤ C + ‖m₀‖ := by gcongr)
    simpa using this
  simp_rw [← hsq] at hlim
  have := hlim.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end HilbertBasis
