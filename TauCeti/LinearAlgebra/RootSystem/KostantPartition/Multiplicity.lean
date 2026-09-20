/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.KostantPartition.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.LinearAlgebra.RootSystem.KostantPartition.Inverse

/-!
# Dividing by the Weyl denominator: the Kostant multiplicity

The Weyl character formula is the identity `ch · Δ = N(λ)` in the integral group algebra `ℤ[M]` of
the weight space, between the formal character of a highest weight module, the Weyl denominator
`Δ = ∏_{α>0}(1 - e^{-α})` (`TauCeti.weylDenominator`) and the Weyl numerator
`N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}` (`TauCeti.weylNumerator`). Dividing by `Δ` recovers the
individual coefficients of `ch`, that is, the individual weight multiplicities; this file performs
that division at the level of the group algebra, where the divisor is not invertible and the
quotient is expressed through the Kostant partition function.

The inverse of `Δ` is the formal series `∑_ν P(ν) e^{-ν}`, whose coefficients are the Kostant
partition function `TauCeti.kostantPartition`. The series is not an element of `ℤ[M]`, so instead
of a product we pair an element of `ℤ[M]` against it and read off the coefficient at `μ`: the
pairing `g ↦ ∑_ν g_ν P(ν - μ)` is a finite sum, and
`TauCeti.sum_coeff_mul_weylDenominator_mul_kostantPartition` says that applying it to `f · Δ`
returns `f_μ`. That is division by `Δ`, coefficient by coefficient.

Applying the pairing to `N(λ)` instead gives the **Kostant multiplicity**
`TauCeti.kostantMultiplicity`, the alternating sum `∑_{w ∈ W} sgn(w) P(w ⬝ λ - μ)`. So the two
computations together turn the character formula into a closed formula for a single multiplicity:
`TauCeti.coeff_eq_kostantMultiplicity_of_mul_weylDenominator_eq_weylNumerator`.

Everything here is combinatorics of the root pairing; no Lie algebra appears, and the Lie-theoretic
reading of these statements — that the multiplicity of the weight `μ` in a finite-dimensional
highest weight module of highest weight `λ` is `∑_{w ∈ W} sgn(w) P(w(λ+ρ) - (μ+ρ))` — is obtained
by feeding in the character formula.

## Main definitions

* `TauCeti.kostantMultiplicity`: the alternating sum `∑_{w ∈ W} sgn(w) P(w ⬝ λ - μ)`.

## Main results

* `TauCeti.sum_coeff_mul_weylDenominator_mul_kostantPartition`: **division by `Δ`**, the pairing of
  `f · Δ` against the partition series at `μ` is the coefficient `f_μ`. It rests on the inversion
  identity `TauCeti.sum_powerset_neg_one_pow_mul_kostantPartition`, transcribed into the group
  algebra as the statement that pairing `Δ` itself against the series gives `1` at `0` and `0`
  elsewhere.
* `TauCeti.sum_coeff_weylNumerator_mul_kostantPartition`: the pairing of `N(λ)` against the
  partition series at `μ` is `TauCeti.kostantMultiplicity`.
* `TauCeti.coeff_eq_kostantMultiplicity_of_mul_weylDenominator_eq_weylNumerator`: **Kostant's
  multiplicity formula**, in the form it takes before a module is named: an element of `ℤ[M]`
  whose product with `Δ` is `N(λ)` has `μ`-th coefficient `∑_{w ∈ W} sgn(w) P(w ⬝ λ - μ)`.

## References

* B. Kostant, *A formula for the multiplicity of a weight*, Trans. Amer. Math. Soc. **93** (1959).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §24.2.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §9.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [CharZero R]
  (P : RootPairing ι R M N) [Finite ι] (b : P.Base)

/-! ## Pairing against the inverse of the Weyl denominator -/

/-- The pairing of `ℤ[M]` against the formal series `∑_ν P(ν) e^{-ν}` inverse to the Weyl
denominator, read at `μ`: it sends `e^x` to `P(x - μ)`. Packaging it as an additive map is what
lets the expansions below be pushed through sums; the public statements spell it out as a
`Finsupp.sum`. -/
private noncomputable def kostantPairing (mu : M) : AddMonoidAlgebra ℤ M →+ ℤ :=
  (Finsupp.linearCombination ℤ fun x ↦ (kostantPartition P b (x - mu) : ℤ)).toAddMonoidHom.comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

private lemma kostantPairing_single (mu x : M) (c : ℤ) :
    kostantPairing P b mu (AddMonoidAlgebra.single x c)
      = c * (kostantPartition P b (x - mu) : ℤ) := by
  simp [kostantPairing, AddMonoidAlgebra.coeff_single]

private lemma kostantPairing_apply (mu : M) (g : AddMonoidAlgebra ℤ M) :
    kostantPairing P b mu g = g.coeff.sum fun x c ↦ c * (kostantPartition P b (x - mu) : ℤ) := by
  simp [kostantPairing, Finsupp.linearCombination_apply]

open Classical in
/-- **The Kostant partition function inverts the Weyl denominator, in the group algebra.** Pairing
`Δ` against the series `∑_ν P(ν) e^{-ν}` gives `1` at `μ = 0` and `0` elsewhere; this is
`TauCeti.sum_powerset_neg_one_pow_mul_kostantPartition` read through the expansion of `Δ` over the
subsets of the positive roots.

It is the `f = 1` case of `TauCeti.sum_coeff_mul_weylDenominator_mul_kostantPartition`, and the
step from which that theorem is derived. -/
private theorem sum_coeff_weylDenominator_mul_kostantPartition (mu : M) :
    ((weylDenominator P b).coeff.sum fun x c ↦ c * (kostantPartition P b (x - mu) : ℤ))
      = if mu = 0 then 1 else 0 := by
  have key := sum_powerset_neg_one_pow_mul_kostantPartition P b (-mu)
  simp only [neg_eq_zero] at key
  rw [← key, ← kostantPairing_apply, weylDenominator_eq_sum_powerset, map_sum]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  have hswap : -∑ i ∈ T, P.root i - mu = -mu - ∑ i ∈ T, P.root i := by abel
  rw [kostantPairing_single, hswap]

/-- **Division by the Weyl denominator.** Pairing `f · Δ` against the series `∑_ν P(ν) e^{-ν}` at
`μ` returns the coefficient of `f` at `μ`.

This is the sense in which `∑_ν P(ν) e^{-ν}` is the inverse of `Δ`: the series is not an element of
`ℤ[M]`, but pairing against it undoes multiplication by `Δ` coefficient by coefficient. -/
theorem sum_coeff_mul_weylDenominator_mul_kostantPartition (f : AddMonoidAlgebra ℤ M) (mu : M) :
    (((f * weylDenominator P b).coeff).sum fun x c ↦ c * (kostantPartition P b (x - mu) : ℤ))
      = f.coeff mu := by
  classical
  -- Expanding the product over the two supports, the inner sum is the pairing of `Δ` itself,
  -- read at the shifted weight `μ - m`, so it is `1` exactly when `m = μ`.
  have inner : ∀ m r, (kostantPairing P b mu ((weylDenominator P b).coeff.sum fun x d ↦
      AddMonoidAlgebra.single (m + x) (r * d))) = if m = mu then r else 0 := by
    intro m r
    have hterm : ((weylDenominator P b).coeff.sum fun x d ↦
        kostantPairing P b mu (AddMonoidAlgebra.single (m + x) (r * d)))
        = (weylDenominator P b).coeff.sum fun x d ↦
            r * d * (kostantPartition P b (x - (mu - m)) : ℤ) :=
      Finsupp.sum_congr fun x _ ↦ by
        have hshift : m + x - mu = x - (mu - m) := by abel
        rw [kostantPairing_single, hshift]
    rw [map_finsuppSum, hterm]
    simp only [mul_assoc, ← Finsupp.mul_sum]
    rw [sum_coeff_weylDenominator_mul_kostantPartition P b (mu - m)]
    rcases eq_or_ne m mu with rfl | h
    · simp
    · have h' : mu - m ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      simp [h, h']
  have expand : (f.coeff.sum fun m r ↦ kostantPairing P b mu
      ((weylDenominator P b).coeff.sum fun x d ↦ AddMonoidAlgebra.single (m + x) (r * d)))
      = f.coeff.sum fun m r ↦ if m = mu then r else 0 :=
    Finsupp.sum_congr fun m _ ↦ inner m _
  rw [← kostantPairing_apply, AddMonoidAlgebra.mul_def, map_finsuppSum, expand,
    Finsupp.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-! ## The Kostant multiplicity -/

section Numerator

variable [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [Fintype P.weylGroup]

/-- **The Kostant multiplicity** `∑_{w ∈ W} sgn(w) P(w ⬝ λ - μ)` of a pair of weights, an
alternating sum of values of the Kostant partition function over the Weyl group. The dot action
`w ⬝ λ = w(λ + ρ) - ρ` makes `w ⬝ λ - μ = w(λ + ρ) - (μ + ρ)`, the shifted difference of Kostant's
formula.

It is the multiplicity of the weight `μ` in the finite-dimensional highest weight module of highest
weight `λ`, as soon as the Weyl character formula is available for that module. -/
noncomputable def kostantMultiplicity (lam mu : M) : ℤ :=
  ∑ w : P.weylGroup, (weylSign P b w : ℤ) *
    (kostantPartition P b (dotAction P b w lam - mu) : ℤ)

/-- The Kostant multiplicity is the alternating sum over the Weyl group, by definition. -/
lemma kostantMultiplicity_def (lam mu : M) : kostantMultiplicity P b lam mu =
    ∑ w : P.weylGroup, (weylSign P b w : ℤ) *
      (kostantPartition P b (dotAction P b w lam - mu) : ℤ) := by
  rw [kostantMultiplicity]

/-- **The Weyl numerator pairs to the Kostant multiplicity.** Each term `sgn(w) e^{w ⬝ λ}` of
`N(λ)` contributes `sgn(w) P(w ⬝ λ - μ)`. -/
theorem sum_coeff_weylNumerator_mul_kostantPartition (lam mu : M) :
    ((weylNumerator P b lam).coeff.sum fun x c ↦ c * (kostantPartition P b (x - mu) : ℤ))
      = kostantMultiplicity P b lam mu := by
  rw [← kostantPairing_apply, weylNumerator_def, map_sum, kostantMultiplicity_def]
  exact Finset.sum_congr rfl fun w _ ↦ kostantPairing_single P b mu _ _

/-- **Kostant's multiplicity formula**, stated before any module is named: an element of `ℤ[M]`
whose product with the Weyl denominator is the Weyl numerator of `λ` has `μ`-th coefficient
`∑_{w ∈ W} sgn(w) P(w ⬝ λ - μ)`.

The hypothesis is exactly the Weyl character formula, so this turns that formula into a closed
expression for one weight multiplicity at a time. -/
theorem coeff_eq_kostantMultiplicity_of_mul_weylDenominator_eq_weylNumerator
    {f : AddMonoidAlgebra ℤ M} {lam : M} (hf : f * weylDenominator P b = weylNumerator P b lam)
    (mu : M) : f.coeff mu = kostantMultiplicity P b lam mu := by
  rw [← sum_coeff_mul_weylDenominator_mul_kostantPartition P b f mu, hf,
    sum_coeff_weylNumerator_mul_kostantPartition]

end Numerator

end TauCeti
