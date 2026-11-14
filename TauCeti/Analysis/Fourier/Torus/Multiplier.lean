/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Diagonal

/-!
# Fourier multipliers on `L²` of the torus

A bounded function `m : ℤᵈ → ℂ` defines the **Fourier multiplier** `T_m` on `L²(𝕋ᵈ)`, where
`𝕋ᵈ = UnitAddTorus d`: it multiplies the `n`-th Fourier coefficient by `m n`,

`(T_m f)^(n) = m n * f̂(n)`.

The Fourier coefficients identify `L²(𝕋ᵈ)` isometrically with `ℓ²(ℤᵈ)` (Mathlib's Hilbert basis
`UnitAddTorus.mFourierBasis`), and `T_m` is the diagonal operator `mFourierBasis.diagonal m` in
this basis (`HilbertBasis.diagonal`), whose general properties this file specializes. Symbols are
elements of `ℓ^∞(ℤᵈ, ℂ)`, and `m ↦ T_m` is a unital algebra homomorphism
(`TauCeti.UnitAddTorus.fourierMultiplier`): sums, products and scalar multiples of symbols give the
corresponding combinations of operators. In particular any two multipliers
commute. The operator norm of `T_m` is the supremum norm of `m`, the multiplier is determined by its
symbol, and it acts on the Fourier modes by `T_m e_n = m n • e_n`.

Multipliers are continuous in their symbols for the strong operator topology on bounded sets:
if `m_a → m` pointwise on `ℤᵈ` and `‖m_a‖ ≤ C`, then `T_{m_a} f → T_m f` in `L²` for every `f`
(`TauCeti.UnitAddTorus.tendsto_fourierMultiplier_apply`). This is how partial sums of a
decomposition of the identity into multipliers, such as the periodic Littlewood–Paley blocks,
are shown to converge.

## Main declarations

* `TauCeti.UnitAddTorus.fourierMultiplier`: the algebra homomorphism `m ↦ T_m`.
* `TauCeti.UnitAddTorus.fourierMultiplier_eq_diagonal`: `T_m` is `mFourierBasis.diagonal m`.
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
multiplying the `n`-th Fourier coefficient by `m n`. It is the diagonal operator with entries `m` in
the Fourier basis `mFourierBasis`, and `m ↦ T_m` is a unital algebra homomorphism from
`ℓ^∞(ℤᵈ, ℂ)` to the bounded operators. -/
def fourierMultiplier :
    ℓ^∞(d → ℤ, ℂ) →ₐ[ℂ] L²(UnitAddTorus d) →L[ℂ] L²(UnitAddTorus d) :=
  mFourierBasis.diagonal

/-- A Fourier multiplier is the diagonal operator with the same entries in the Fourier basis, so
the general API of `HilbertBasis.diagonal` applies to it. -/
theorem fourierMultiplier_eq_diagonal :
    (fourierMultiplier : ℓ^∞(d → ℤ, ℂ) →ₐ[ℂ] _) = mFourierBasis.diagonal :=
  (rfl)

/-- The Fourier coefficients of `T_m f` are `(T_m f)^(n) = m n * f̂(n)`. -/
@[simp]
theorem mFourierCoeff_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) (f : L²(UnitAddTorus d))
    (n : d → ℤ) :
    mFourierCoeff (fourierMultiplier m f) n = m n * mFourierCoeff f n := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, fourierMultiplier_eq_diagonal,
    HilbertBasis.repr_diagonal]

/-- A Fourier multiplier acts on the Fourier mode `e_n` as multiplication by `m n`. -/
@[simp]
theorem fourierMultiplier_mFourierLp (m : ℓ^∞(d → ℤ, ℂ)) (n : d → ℤ) :
    fourierMultiplier m (mFourierLp 2 n) = m n • mFourierLp 2 n := by
  rw [← coe_mFourierBasis, fourierMultiplier_eq_diagonal, HilbertBasis.diagonal_apply_self]

/-- The Fourier series of `T_m f`: its `n`-th term is `m n * f̂(n)` times the mode `e_n`. -/
theorem hasSum_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) (f : L²(UnitAddTorus d)) :
    HasSum (fun n ↦ (m n * mFourierCoeff f n) • mFourierLp 2 n) (fourierMultiplier m f) := by
  simpa using hasSum_mFourier_series_L2 (fourierMultiplier m f)

/-- The operator norm of a Fourier multiplier is the supremum norm of its symbol. -/
@[simp]
theorem norm_fourierMultiplier (m : ℓ^∞(d → ℤ, ℂ)) : ‖fourierMultiplier m‖ = ‖m‖ :=
  mFourierBasis.norm_diagonal m

/-- A Fourier multiplier determines its symbol. -/
theorem fourierMultiplier_injective :
    Function.Injective (fourierMultiplier : ℓ^∞(d → ℤ, ℂ) → _) :=
  mFourierBasis.diagonal_injective

/-- Two Fourier multipliers are equal exactly when their symbols are equal. -/
@[simp]
theorem fourierMultiplier_inj {m₁ m₂ : ℓ^∞(d → ℤ, ℂ)} :
    fourierMultiplier m₁ = fourierMultiplier m₂ ↔ m₁ = m₂ :=
  fourierMultiplier_injective.eq_iff

/-- Any two Fourier multipliers commute. -/
theorem commute_fourierMultiplier (m₁ m₂ : ℓ^∞(d → ℤ, ℂ)) :
    Commute (fourierMultiplier m₁) (fourierMultiplier m₂) :=
  mFourierBasis.commute_diagonal m₁ m₂

/-- **Strong continuity of Fourier multipliers in the symbol.** If the symbols `m a` are bounded
uniformly by `C` and converge pointwise on `ℤᵈ` to `m₀`, then `T_{m a} f → T_{m₀} f` in `L²(𝕋ᵈ)`
for every `f`. -/
theorem tendsto_fourierMultiplier_apply {α : Type*} {l : Filter α} {m : α → ℓ^∞(d → ℤ, ℂ)}
    {m₀ : ℓ^∞(d → ℤ, ℂ)} {C : ℝ} (hC : ∀ᶠ a in l, ‖m a‖ ≤ C)
    (hm : ∀ n, Tendsto (fun a ↦ m a n) l (𝓝 (m₀ n))) (f : L²(UnitAddTorus d)) :
    Tendsto (fun a ↦ fourierMultiplier (m a) f) l (𝓝 (fourierMultiplier m₀ f)) :=
  mFourierBasis.tendsto_diagonal_apply hC hm f

end TauCeti.UnitAddTorus
