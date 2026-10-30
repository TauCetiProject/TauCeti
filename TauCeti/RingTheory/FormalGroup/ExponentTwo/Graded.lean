/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.RingTheory.FormalGroup.ExponentTwo.Basic
-- Proof-only: homogeneity as an equation in `A[T]`, rescaling, and base change.
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.FormalGroup.Rescale

/-!
# The graded normalised logarithm of a formal group law of exponent two

Let `A` be a commutative ring graded by `𝒜 : ℕ → σ`, and let `F` be a commutative formal group law
over `A` with `[2]_F = 0`. Suppose that `F` is graded with its formal parameter in degree one, so
that the coefficient `aᵢⱼ` of `Xⁱ Yʲ` in `F` has degree `i + j - 1`. This is the grading of the
formal group law of a real orientation, as for unoriented bordism, with homological degrees. Then
the normalised logarithm `g(X) = X + ∑_{i ≥ 1} bᵢ X^(i + 1)` of `F`
(`FormalGroup.exponentTwoLog`) is graded in the same way: `bᵢ` has degree `i`. Conversely, `F` is
graded when its normalised logarithm is, since `F(X, Y) = g⁻¹(g(X) + g(Y))`.

The proof turns homogeneity into an equation. The homomorphism `ψ : A →+* A[T]` sending `a` to the
polynomial `∑ₙ aₙ Tⁿ` of its homogeneous components (`TauCeti.GradedAlgebra.toPolynomial`) sends
an element `a` of degree `n` to `a Tⁿ`. Hence `F` is graded exactly when its base change along `ψ`
is the rescaling `F^T(X, Y) = X + Y + ∑ Tⁱ⁺ʲ⁻¹ aᵢⱼ Xⁱ Yʲ` of `F` (`FormalGroup.rescale`), and `g`
is graded exactly when its base change along `ψ` is the rescaled series `∑ Tⁿ⁻¹ bₙ₋₁ Xⁿ`. Both
series are normalised and additive along the corresponding formal group laws, because `T` is a
nonzerodivisor, so the uniqueness of the normalised logarithm
(`FormalGroup.logarithm_unique_of_nsmulSeries_two_eq_zero`) compares them.

## Main results

* `FormalGroup.forall_coeff_exponentTwoLog_mem_iff`: the normalised logarithm of `F` has its
  coefficient of `Xⁿ` in degree `n - 1` for every `n` exactly when `F` has its coefficient of
  `X^(d 0) Y^(d 1)` in degree `d 0 + d 1 - 1` for every `d`.
* `FormalGroup.coeff_exponentTwoLog_mem`: the coefficient of `Xⁿ` in the normalised logarithm of a
  graded `F` has degree `n - 1`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

section Graded

open TauCeti.GradedAlgebra

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

/-- **The normalised logarithm of a graded formal group law of exponent two is graded.** Let `A`
be graded by `𝒜 : ℕ → σ` and let `F` be a commutative formal group law over `A` with
`[2]_F = 0`. The coefficient of `Xⁿ` in the normalised logarithm of `F` lies in `𝒜 (n - 1)` for
every `n` exactly when the coefficient of `X^(d 0) Y^(d 1)` in `F` lies in `𝒜 (d 0 + d 1 - 1)`
for every `d`. Thus a formal group law with its formal parameter in degree one, such as that of a
real orientation in homological degrees, has a normalised logarithm `X + ∑_{i ≥ 1} bᵢ X^(i + 1)`
with `bᵢ` of degree `i`. -/
theorem forall_coeff_exponentTwoLog_mem_iff (F : FormalGroup A) [F.IsComm]
    (hF : F.nsmulSeries 2 = 0) :
    (∀ n, PowerSeries.coeff n (F.exponentTwoLog hF) ∈ 𝒜 (n - 1)) ↔
      ∀ d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries ∈ 𝒜 (d.degree - 1) := by
  set g := F.exponentTwoLog hF
  set gₜ : PowerSeries (Polynomial A) :=
    PowerSeries.mk fun n ↦ Polynomial.X ^ (n - 1) * PowerSeries.coeff n (g.map Polynomial.C)
  -- `g` is additive along the base change of `F` along `toPolynomial 𝒜`, and `gₜ` along the
  -- rescaling of `F` by `T`.
  have hψ :=
    subst_map_toPowerSeries_map F (toPolynomial 𝒜) (F.subst_toPowerSeries_exponentTwoLog hF)
  have hT := subst_rescale_toPowerSeries_of_smul_eq_rescale (F.map Polynomial.C) (gₛ := gₜ)
    Polynomial.isRegular_X.left (by ext (_ | n) <;> simp [gₜ, g, pow_succ', mul_assoc])
    (subst_map_toPowerSeries_map F Polynomial.C (F.subst_toPowerSeries_exponentTwoLog hF))
  rw [← PowerSeries.map_toPolynomial_eq_mk_iff, ← map_toPolynomial_eq_rescale_iff]
  constructor
  · -- Both formal group laws make the coordinate `g.map (toPolynomial 𝒜)` additive, so they
    -- agree.
    intro h
    let φ : TauCeti.FormalCoordinate (Polynomial A) :=
      ⟨g.map (toPolynomial 𝒜), by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [g],
        by simp [g]⟩
    have e (G : FormalGroup (Polynomial A)) : G.toPowerSeries =
        PowerSeries.subst (PowerSeries.subst G.toPowerSeries φ.toPowerSeries)
          φ⁻¹.toPowerSeries :=
      (φ.subst_inv_subst (.of_constantCoeff_zero G.zero_constantCoeff)).symm
    have heq : PowerSeries.subst (F.map (toPolynomial 𝒜)).toPowerSeries (g.map (toPolynomial 𝒜)) =
        PowerSeries.subst ((F.map Polynomial.C).rescale Polynomial.X).toPowerSeries
          (g.map (toPolynomial 𝒜)) := by
      rw [hψ, h, hT]
    exact FormalGroup.ext <| (e _).trans <|
      (congrArg (PowerSeries.subst · φ⁻¹.toPowerSeries) heq).trans (e _).symm
  · -- Both `g.map (toPolynomial 𝒜)` and `gₜ` are normalised logarithms of the same formal group
    -- law.
    intro h
    rw [h] at hψ
    have h₂ : ((F.map Polynomial.C).rescale Polynomial.X).nsmulSeries 2 = 0 := by
      rw [← h, ← map_nsmulSeries, hF, map_zero]
    refine logarithm_unique_of_nsmulSeries_two_eq_zero _ h₂ ?_ ?_ ?_ hψ ?_ ?_ ?_ hT
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [g]
    · simp [g]
    · intro k hk
      simp [g, coeff_two_pow_exponentTwoLog _ _ hk]
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [g]
    · simp [g]
    · intro k hk
      simp [g, coeff_two_pow_exponentTwoLog _ _ hk]

/-- **The normalised logarithm of a graded formal group law of exponent two is graded.** If the
coefficient of `X^(d 0) Y^(d 1)` in a commutative formal group law `F` with `[2]_F = 0` lies in
`𝒜 (d 0 + d 1 - 1)` for every `d`, then the coefficient of `Xⁿ` in its normalised logarithm lies in
`𝒜 (n - 1)`. -/
theorem coeff_exponentTwoLog_mem (F : FormalGroup A) [F.IsComm] (hF : F.nsmulSeries 2 = 0)
    (h : ∀ d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries ∈ 𝒜 (d.degree - 1)) (n : ℕ) :
    PowerSeries.coeff n (F.exponentTwoLog hF) ∈ 𝒜 (n - 1) :=
  (forall_coeff_exponentTwoLog_mem_iff F hF).2 h n

end Graded

end FormalGroup
