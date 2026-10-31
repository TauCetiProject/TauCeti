/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
import TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The logarithm of a formal group law of exponent two

Let `F` be a commutative formal group law over a commutative ring `R` with `[2]_F(X) = F(X, X) = 0`.
Then `2 = 0` in `R`, since `2` is the linear coefficient of `[2]_F`, so no logarithm in the sense of
`FormalGroup.log` is available. Nevertheless `F` is strictly isomorphic to the additive formal group
law, and there is a canonical choice of isomorphism: there is a unique power series

  `g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{2ᵏ} = 0` for every `k ≥ 1`

such that `g(F(X, Y)) = g(X) + g(Y)`. This is the case `p = 2` of
`FormalGroup.existsUnique_logarithm_of_nsmulSeries_eq_zero`. Formal group laws with `[2]_F = 0`
arise in Quillen's description of unoriented bordism, where `g` is the canonical coordinate; this
file names it and records its characterising properties. No coefficient field and no further
hypothesis on `R` is used: it may have nilpotents or be the zero ring.

## Main definitions

* `FormalGroup.exponentTwoLog`: the normalised logarithm `g` of a commutative formal group law `F`
  with `[2]_F = 0`.

## Main results

* `FormalGroup.subst_toPowerSeries_exponentTwoLog`: `g(F(X, Y)) = g(X) + g(Y)`, and
  `FormalGroup.subst_subst_toPowerSeries_exponentTwoLog`: `g(F(x, y)) = g(x) + g(y)` for
  substitutable `x, y`.
* `FormalGroup.eq_exponentTwoLog`: the normalised logarithm is the unique series `g = X + ⋯`
  without terms of degree `2ᵏ`, `k ≥ 1`, that is additive along `F`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

section ExponentTwoLog

variable [F.IsComm] (hF : F.nsmulSeries 2 = 0)

/-- **The normalised logarithm of a formal group law of exponent two** (Quillen). For a commutative
formal group law `F` with `[2]_F = 0`, this is the unique power series
`g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{2ᵏ} = 0` for every `k ≥ 1` such that
`g(F(X, Y)) = g(X) + g(Y)`; see `FormalGroup.eq_exponentTwoLog`. -/
noncomputable def exponentTwoLog : PowerSeries R :=
  Classical.choose (F.existsUnique_logarithm_of_nsmulSeries_eq_zero Nat.prime_two hF).exists

private theorem exponentTwoLog_spec :
    PowerSeries.constantCoeff (F.exponentTwoLog hF) = 0 ∧
      PowerSeries.coeff 1 (F.exponentTwoLog hF) = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (2 ^ k) (F.exponentTwoLog hF) = 0) ∧
      PowerSeries.subst F.toPowerSeries (F.exponentTwoLog hF) =
        PowerSeries.subst (X 0) (F.exponentTwoLog hF) +
          PowerSeries.subst (X 1) (F.exponentTwoLog hF) :=
  Classical.choose_spec (F.existsUnique_logarithm_of_nsmulSeries_eq_zero Nat.prime_two hF).exists

/-- The normalised logarithm has no constant term. -/
@[simp]
theorem constantCoeff_exponentTwoLog : PowerSeries.constantCoeff (F.exponentTwoLog hF) = 0 :=
  (F.exponentTwoLog_spec hF).1

/-- The normalised logarithm has linear coefficient `1`. -/
@[simp]
theorem coeff_one_exponentTwoLog : PowerSeries.coeff 1 (F.exponentTwoLog hF) = 1 :=
  (F.exponentTwoLog_spec hF).2.1

/-- The normalised logarithm has no term of degree `2ᵏ` for `k ≥ 1`. -/
theorem coeff_two_pow_exponentTwoLog {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff (2 ^ k) (F.exponentTwoLog hF) = 0 :=
  (F.exponentTwoLog_spec hF).2.2.1 k hk

/-- **The normalised logarithm is additive along `F`**: `g(F(X, Y)) = g(X) + g(Y)`. -/
theorem subst_toPowerSeries_exponentTwoLog :
    PowerSeries.subst F.toPowerSeries (F.exponentTwoLog hF) =
      PowerSeries.subst (X 0) (F.exponentTwoLog hF) +
        PowerSeries.subst (X 1) (F.exponentTwoLog hF) :=
  (F.exponentTwoLog_spec hF).2.2.2

/-- **The normalised logarithm is additive along `F`** at any pair of power series `f₀, f₁` that
can be substituted: `g(F(f₀, f₁)) = g(f₀) + g(f₁)`. -/
theorem subst_subst_toPowerSeries_exponentTwoLog {σ : Type*} {f₀ f₁ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) :
    PowerSeries.subst (subst ![f₀, f₁] F.toPowerSeries) (F.exponentTwoLog hF) =
      PowerSeries.subst f₀ (F.exponentTwoLog hF) + PowerSeries.subst f₁ (F.exponentTwoLog hF) := by
  have hf : HasSubst ![f₀, f₁] := hasSubst_finTwo h₀ h₁
  have := congrArg (subst ![f₀, f₁]) (F.subst_toPowerSeries_exponentTwoLog hF)
  rwa [subst_add hf, subst_powerSeriesSubst hf (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst hf (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst hf (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_X hf, subst_X hf] at this

/-- A power series `g = X + ⋯` without terms of degree `2ᵏ`, `k ≥ 1`, that is additive along `F`
is the normalised logarithm. -/
theorem eq_exponentTwoLog {g : PowerSeries R} (h₀ : PowerSeries.constantCoeff g = 0)
    (h₁ : PowerSeries.coeff 1 g = 1) (hp : ∀ k, 0 < k → PowerSeries.coeff (2 ^ k) g = 0)
    (hg : PowerSeries.subst F.toPowerSeries g =
      PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g) :
    g = F.exponentTwoLog hF :=
  (F.existsUnique_logarithm_of_nsmulSeries_eq_zero Nat.prime_two hF).unique ⟨h₀, h₁, hp, hg⟩
    (F.exponentTwoLog_spec hF)

end ExponentTwoLog

end FormalGroup
