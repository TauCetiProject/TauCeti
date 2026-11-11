/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fourier multipliers on `L²` of the torus

A bounded function `m : ℤᵈ → ℂ` defines the **Fourier multiplier** `T_m` on `L²(𝕋ᵈ)`, where
`𝕋ᵈ = UnitAddTorus d`: it multiplies the `n`-th Fourier coefficient by `m n`,

`(T_m f)^(n) = m n * f̂(n)`.

The Fourier coefficients identify `L²(𝕋ᵈ)` isometrically with `ℓ²(ℤᵈ)` (Mathlib's Hilbert basis
`UnitAddTorus.mFourierBasis`), and `T_m` is the diagonal operator `lp.diagonalCLM m` transported
along this identification. Symbols are elements of `ℓ^∞(ℤᵈ, ℂ)`, and `m ↦ T_m` is a unital algebra
homomorphism (`TauCeti.UnitAddTorus.fourierMultiplier`): sums, products and scalar multiples of
symbols give the corresponding combinations of operators. In particular any two multipliers
commute. The operator norm of `T_m` is the supremum norm of `m`, the multiplier is determined by its
symbol, and it acts on the Fourier modes by `T_m e_n = m n • e_n`.

Multipliers are continuous in their symbols for the strong operator topology on bounded sets:
if `m_a → m` pointwise on `ℤᵈ` and `‖m_a‖ ≤ C`, then `T_{m_a} f → T_m f` in `L²` for every `f`
(`TauCeti.UnitAddTorus.tendsto_fourierMultiplier_apply`). This is how partial sums of a
decomposition of the identity into multipliers, such as the periodic Littlewood–Paley blocks,
are shown to converge.

## Main declarations

* `TauCeti.UnitAddTorus.fourierMultiplier`: the algebra homomorphism `m ↦ T_m`.
* `TauCeti.UnitAddTorus.mFourierCoeff_fourierMultiplier`: `(T_m f)^(n) = m n * f̂(n)`.
* `TauCeti.UnitAddTorus.fourierMultiplier_mFourierLp`: `T_m e_n = m n • e_n`.
* `TauCeti.UnitAddTorus.norm_fourierMultiplier`: `‖T_m‖ = ‖m‖`.
* `TauCeti.UnitAddTorus.fourierMultiplier_injective`: the symbol is determined by the operator.
* `TauCeti.UnitAddTorus.hasSum_fourierMultiplier`: the Fourier series of `T_m f`.
* `TauCeti.UnitAddTorus.hasSum_norm_sq_mFourierCoeff`: Parseval's identity
  `‖f‖² = ∑ₙ ‖f̂(n)‖²` in `L²(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.tendsto_fourierMultiplier_apply`: strong continuity in the symbol.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 4.3 (multipliers on the torus).
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped lp ENNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- Mathlib's Fourier basis `mFourierBasis` lives on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; use it here so that the multipliers act
-- on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-- **Parseval's identity** in `L²(𝕋ᵈ)`: the squared norm of `f` is the sum of the squared norms of
its Fourier coefficients. -/
theorem hasSum_norm_sq_mFourierCoeff (f : L²(UnitAddTorus d)) :
    HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by simp) (mFourierBasis.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    mFourierBasis_repr] at h
  exact h

/-- The **Fourier multiplier** on `L²(𝕋ᵈ)` with bounded symbol `m : ℤᵈ → ℂ`: the operator
multiplying the `n`-th Fourier coefficient by `m n`. It is the diagonal operator with entries `m`
transported along the Fourier isometry `L²(𝕋ᵈ) ≃ ℓ²(ℤᵈ)`, and `m ↦ T_m` is a unital algebra
homomorphism from `ℓ^∞(ℤᵈ, ℂ)` to the bounded operators. -/
def fourierMultiplier :
    ℓ^∞(d → ℤ, ℂ) →ₐ[ℂ] L²(UnitAddTorus d) →L[ℂ] L²(UnitAddTorus d) where
  toFun m := (mFourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap :
      ℓ²(d → ℤ, ℂ) →L[ℂ] L²(UnitAddTorus d)) ∘L lp.diagonalCLM (p := 2) m ∘L
    mFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by
    ext1 f
    simp
  map_mul' m₁ m₂ := by
    ext1 f
    simp [lp.diagonalCLM_mul]
  map_zero' := by
    ext1 f
    simp
  map_add' m₁ m₂ := by
    ext1 f
    simp
  commutes' c := by
    ext1 f
    rw [Algebra.algebraMap_eq_smul_one, lp.diagonalCLM_smul, lp.diagonalCLM_one]
    simp

/-- The Fourier coefficients of `T_m f`, read through the Fourier isometry `L²(𝕋ᵈ) ≃ ℓ²(ℤᵈ)`. -/
@[simp]
theorem mFourierBasis_repr_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) (f : L²(UnitAddTorus d))
    (n : d → ℤ) :
    mFourierBasis.repr (fourierMultiplier m f) n = m n * mFourierBasis.repr f n := by
  simp [fourierMultiplier]

/-- The Fourier coefficients of `T_m f` are `(T_m f)^(n) = m n * f̂(n)`. -/
@[simp]
theorem mFourierCoeff_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) (f : L²(UnitAddTorus d))
    (n : d → ℤ) :
    mFourierCoeff (fourierMultiplier m f) n = m n * mFourierCoeff f n := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, mFourierBasis_repr_fourierMultiplier]

/-- A Fourier multiplier acts on the Fourier mode `e_n` as multiplication by `m n`. -/
@[simp]
theorem fourierMultiplier_mFourierLp (m : ℓ^∞(d → ℤ, ℂ)) (n : d → ℤ) :
    fourierMultiplier m (mFourierLp 2 n) = m n • mFourierLp 2 n := by
  classical
  rw [← coe_mFourierBasis]
  apply mFourierBasis.repr.injective
  ext k
  simp only [mFourierBasis_repr_fourierMultiplier, HilbertBasis.repr_self, map_smul,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = n
  · subst hk
    simp
  · simp [hk]

/-- The Fourier series of `T_m f`: its `n`-th term is `m n * f̂(n)` times the mode `e_n`. -/
theorem hasSum_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) (f : L²(UnitAddTorus d)) :
    HasSum (fun n ↦ (m n * mFourierCoeff f n) • mFourierLp 2 n) (fourierMultiplier m f) := by
  simpa using hasSum_mFourier_series_L2 (fourierMultiplier m f)

/-- The operator norm of a Fourier multiplier is the supremum norm of its symbol. -/
@[simp]
theorem norm_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) : ‖fourierMultiplier m‖ = ‖m‖ := by
  -- Through the Fourier isometry, `T_m` is the diagonal operator with entries `m`.
  have key : ∀ f, mFourierBasis.repr (fourierMultiplier m f) =
      lp.diagonalCLM (p := 2) m (mFourierBasis.repr f) := fun f ↦ by
    ext n
    simp
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m) fun f ↦ ?_) ?_
  · rw [← LinearIsometryEquiv.norm_map mFourierBasis.repr, key, ← lp.norm_diagonalCLM (p := 2) m,
      ← LinearIsometryEquiv.norm_map mFourierBasis.repr f]
    exact ContinuousLinearMap.le_opNorm _ _
  · rw [← lp.norm_diagonalCLM (p := 2) m]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [← mFourierBasis.repr.apply_symm_apply x, ← key, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.le_opNorm _ _

/-- A Fourier multiplier determines its symbol. -/
theorem fourierMultiplier_injective :
    Function.Injective (fourierMultiplier : ℓ^∞(d → ℤ, ℂ) → _) := by
  classical
  intro m₁ m₂ h
  ext n
  have h' := congrArg (fun T ↦ mFourierBasis.repr (T (mFourierBasis n)) n) h
  simpa only [mFourierBasis_repr_fourierMultiplier, HilbertBasis.repr_self, lp.single_apply,
    Pi.single_eq_same, mul_one] using h'

/-- Two Fourier multipliers are equal exactly when their symbols are equal. -/
@[simp]
theorem fourierMultiplier_inj {m₁ m₂ : ℓ^∞(d → ℤ, ℂ)} :
    fourierMultiplier m₁ = fourierMultiplier m₂ ↔ m₁ = m₂ :=
  fourierMultiplier_injective.eq_iff

/-- Any two Fourier multipliers commute. -/
theorem commute_fourierMultiplier (m₁ m₂ : ℓ^∞(d → ℤ, ℂ)) :
    Commute (fourierMultiplier m₁) (fourierMultiplier m₂) :=
  (Commute.all m₁ m₂).map fourierMultiplier

/-- **Strong continuity of Fourier multipliers in the symbol.** If the symbols `m a` are bounded
uniformly by `C` and converge pointwise on `ℤᵈ` to `m₀`, then `T_{m a} f → T_{m₀} f` in `L²(𝕋ᵈ)`
for every `f`. -/
theorem tendsto_fourierMultiplier_apply {α : Type*} {l : Filter α} {m : α → ℓ^∞(d → ℤ, ℂ)}
    {m₀ : ℓ^∞(d → ℤ, ℂ)} {C : ℝ} (hC : ∀ᶠ a in l, ‖m a‖ ≤ C)
    (hm : ∀ n, Tendsto (fun a ↦ m a n) l (𝓝 (m₀ n))) (f : L²(UnitAddTorus d)) :
    Tendsto (fun a ↦ fourierMultiplier (m a) f) l (𝓝 (fourierMultiplier m₀ f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- The squared distance is the tail-dominated series `∑ₙ ‖(m a n - m₀ n) f̂(n)‖²`.
  have hsq : ∀ a, ‖fourierMultiplier (m a) f - fourierMultiplier m₀ f‖ ^ 2 =
      ∑' n, ‖(m a n - m₀ n) * mFourierCoeff f n‖ ^ 2 := fun a ↦ by
    rw [← (hasSum_norm_sq_mFourierCoeff _).tsum_eq]
    congr 1
    ext n
    rw [← mFourierBasis_repr, map_sub]
    simp [mFourierBasis_repr, sub_mul]
  have hsum : Summable fun n ↦ ((C + ‖m₀‖) * ‖mFourierCoeff f n‖) ^ 2 := by
    simpa [mul_pow] using ((hasSum_norm_sq_mFourierCoeff f).summable.mul_left
      ((C + ‖m₀‖) ^ 2))
  have hlim : Tendsto (fun a ↦ ∑' n, ‖(m a n - m₀ n) * mFourierCoeff f n‖ ^ 2) l (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun a n ↦
        ‖(m a n - m₀ n) * mFourierCoeff f n‖ ^ 2) (g := fun _ ↦ (0 : ℝ)) hsum
      (fun n ↦ by
        have h := ((hm n).sub_const (m₀ n)).mul_const (mFourierCoeff f n)
        simpa using (h.norm.pow 2))
      (hC.mono fun a ha n ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
        gcongr
        calc ‖m a n - m₀ n‖ ≤ ‖m a n‖ + ‖m₀ n‖ := norm_sub_le _ _
          _ ≤ ‖m a‖ + ‖m₀‖ := add_le_add (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
              (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
          _ ≤ C + ‖m₀‖ := by gcongr)
    simpa using this
  simp_rw [← hsq] at hlim
  have := hlim.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end TauCeti.UnitAddTorus
