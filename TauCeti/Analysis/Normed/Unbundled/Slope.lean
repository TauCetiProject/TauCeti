/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Numerical slopes of polynomials

Let `K` be a nonarchimedean field and `A` a `K`-algebra. A polynomial `Q : A[X]` has *slope at
most `r`*, for a real cutoff `r > 0`, if for every `K`-algebra map `χ : A → L` into an algebraic
extension `L` of `K` in the universe of `A`, every root of `χ(Q)` has absolute value at least
`r`. The absolute value of a root is its spectral norm over `K`, which is the unique extension of
the norm of `K` when `K` is complete; no embedding into a chosen algebraic closure is involved. For
`r = |p| ^ h` this says that every root has valuation at most `h`. The condition concerns roots of
an annihilating polynomial, not of a Fredholm series `det (1 - T U)`, whose roots are the
reciprocals.

For an affinoid algebra `A` the condition can be tested at finitely many classical points and
then holds for algebraic extensions in every universe; see
`TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_splittingField` and
`TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`.

## Main definitions

* `Polynomial.IsSlopeLE K r Q`: every root of `Q` at every algebraic point, with values in the
  universe of `A`, has absolute value at least `r > 0`.

## References

* E. Urban, *Eigenvarieties for reductive groups*, Ann. of Math. 174 (2011), 1685–1784, §2.3.
-/

public section

open Polynomial

universe v

namespace Polynomial

variable (K : Type*) [NormedField K] {A : Type v} [CommRing A] [Algebra K A]

/-- A polynomial `Q : A[X]` has slope at most `r` over `K` if `r > 0` and, for every `K`-algebra
map `χ : A → L` into an algebraic extension `L` of `K` in the universe of `A`, every root of
`χ(Q)` has spectral norm at least `r`. For `r = |p| ^ h` this says that every root has valuation
at most `h`. Over an affinoid algebra the bound then holds in every universe, by
`TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`. -/
def IsSlopeLE (r : ℝ) (Q : A[X]) : Prop :=
  0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) (α : L),
    (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α

variable {K} {r s : ℝ} {P Q : A[X]}

/-- The defining property of `Polynomial.IsSlopeLE`. -/
theorem isSlopeLE_iff : Q.IsSlopeLE K r ↔
    0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L)
      (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α :=
  Iff.rfl

/-- The cutoff of the slope condition is positive. -/
theorem IsSlopeLE.pos (hQ : Q.IsSlopeLE K r) : 0 < r :=
  hQ.1

/-- Under the slope condition, every root of `χ(Q)` in an algebraic extension has spectral norm
at least the cutoff. -/
theorem IsSlopeLE.le_spectralNorm (hQ : Q.IsSlopeLE K r) {L : Type v} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L} (hα : (Q.map (χ : A →+* L)).IsRoot α) :
    r ≤ spectralNorm K L α :=
  hQ.2 L χ α hα

/-- Lowering a positive cutoff preserves the slope condition. -/
theorem IsSlopeLE.mono (hQ : Q.IsSlopeLE K r) (hs : 0 < s) (hsr : s ≤ r) : Q.IsSlopeLE K s :=
  ⟨hs, fun _ _ _ _ χ _ hα ↦ hsr.trans (hQ.le_spectralNorm χ hα)⟩

/-- The constant polynomial `1` has no roots, so it has slope at most every positive cutoff. -/
@[simp]
theorem isSlopeLE_one_iff : (1 : A[X]).IsSlopeLE K r ↔ 0 < r := by
  simp [isSlopeLE_iff]

/-- `P * Q` has slope at most `r` if and only if both `P` and `Q` do, since the roots of a
product are the roots of its factors. -/
@[simp]
theorem isSlopeLE_mul_iff : (P * Q).IsSlopeLE K r ↔ P.IsSlopeLE K r ∧ Q.IsSlopeLE K r := by
  simp only [isSlopeLE_iff, Polynomial.map_mul, IsRoot, eval_mul, mul_eq_zero]
  exact ⟨fun h ↦ ⟨⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inl hα)⟩,
    ⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inr hα)⟩⟩,
    fun h ↦ ⟨h.1.1, fun L _ _ _ χ α hα ↦ hα.elim (h.1.2 L χ α) (h.2.2 L χ α)⟩⟩

/-- The linear polynomial `X - c` has slope at most `r` when `0 < r ≤ |c|`. -/
theorem isSlopeLE_X_sub_C_algebraMap {c : K} (hr : 0 < r) (hrc : r ≤ ‖c‖) :
    (X - C (algebraMap K A c)).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  obtain rfl : α = algebraMap K L c := by simpa [sub_eq_zero] using hα
  rwa [spectralNorm_extends]

/-- The polynomial `1 - c X`, whose root `c⁻¹` is the reciprocal of that of `X - c`, has slope
at most `r` when `0 < r ≤ |c|⁻¹`. -/
theorem isSlopeLE_one_sub_C_mul_X_algebraMap {c : K} (hr : 0 < r)
    (hrc : r ≤ ‖c‖⁻¹) : (1 - C (algebraMap K A c) * X).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  have hα : 1 - algebraMap K L c * α = 0 := by simpa using hα
  rwa [eq_inv_of_mul_eq_one_right (sub_eq_zero.1 hα).symm, ← map_inv₀, spectralNorm_extends,
    norm_inv]

end Polynomial
