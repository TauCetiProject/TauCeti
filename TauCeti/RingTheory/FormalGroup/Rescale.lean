/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.MvPowerSeries.Rescale
-- Proof-only: the coefficients after swapping the variables.
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Rescaling a formal group law

Let `F(X, Y) = ∑_d a_d X^(d 0) Y^(d 1)` be a one-dimensional formal group law over a commutative
ring `R` and let `s ∈ R`. Multiplying the coefficient of every monomial of total degree `n ≥ 1` by
`s ^ (n - 1)` gives the series

  `F^s(X, Y) = X + Y + ∑_{i, j ≥ 1} s ^ (i + j - 1) aᵢⱼ Xⁱ Yʲ`,

which satisfies `s • F^s(X, Y) = F(s X, s Y)`; when `s` is a nonzerodivisor, this identity
characterises `F^s`. When `s` is a unit, `F^s(X, Y) = s⁻¹ F(s X, s Y)`
is the transport of `F` along the coordinate change `X ↦ s X`. For every `s`, unit or not, `F^s`
is again a formal group law, `FormalGroup.rescale F s`, and it is commutative when `F` is.

This is the action of the multiplicative monoid of `R` on formal group laws
(`FormalGroup.rescale_rescale`). Applied with `s` a polynomial variable to the universal formal
group law, it records the grading of the Lazard ring: the coefficient `aᵢⱼ` is acted on by
`s ^ (i + j - 1)`.

When `s` is a nonzerodivisor, associativity of `F^s` follows from that of `F` by cancelling `s`
from `s • F^s(F^s(X, Y), Z) = F(F(s X, s Y), s Z)`. The general case is the base change of the
case of the polynomial variable `s` over `R[s]`.

## Main definitions

* `FormalGroup.rescale F s`: the formal group law `F^s`, with coefficients `s ^ (i + j - 1) aᵢⱼ`.

## Main results

* `FormalGroup.coeff_rescale`: the coefficient of a monomial of degree `n` in `F^s` is `s ^ (n - 1)`
  times its coefficient in `F`.
* `FormalGroup.smul_rescale`: `s • F^s(X, Y) = F(s X, s Y)`.
* `FormalGroup.map_rescale`: rescaling commutes with base change.
* `FormalGroup.rescale_one` and `FormalGroup.rescale_rescale`: rescaling is an action of the
  multiplicative monoid of `R`.

## References

* M. Hazewinkel, *Formal Groups and Applications*, Chapter I, §1.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The series `∑_d s ^ (|d| - 1) f_d X^d`, with `|d|` the total degree of the monomial `X^d`. -/
private def rescaleSeries (f : MvPowerSeries (Fin 2) R) (s : R) : MvPowerSeries (Fin 2) R :=
  fun d ↦ s ^ (d.degree - 1) * coeff d f

private theorem coeff_rescaleSeries (f : MvPowerSeries (Fin 2) R) (s : R) (d : Fin 2 →₀ ℕ) :
    coeff d (rescaleSeries f s) = s ^ (d.degree - 1) * coeff d f :=
  coeff_apply _ _

private theorem constantCoeff_rescaleSeries {f : MvPowerSeries (Fin 2) R}
    (hf : constantCoeff f = 0) (s : R) : constantCoeff (rescaleSeries f s) = 0 := by
  simpa [hf] using coeff_rescaleSeries f s 0

private theorem smul_rescaleSeries {f : MvPowerSeries (Fin 2) R} (hf : constantCoeff f = 0)
    (s : R) : s • rescaleSeries f s = rescale (fun _ ↦ s) f := by
  ext d
  rcases Nat.eq_zero_or_pos d.degree with h | h
  · simp [(Finsupp.degree_eq_zero_iff d).1 h, constantCoeff_rescaleSeries hf, hf]
  · simp [coeff_rescaleSeries, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply,
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel h]

/-- Associativity transfers from `f` to `g` along `s • g = f(s X, s Y)` when `s` is a
nonzerodivisor. -/
private theorem assoc_of_smul_eq_rescale (F : FormalGroup R) {g : MvPowerSeries (Fin 2) R}
    {s : R} (hs : IsLeftRegular s) (hg : constantCoeff g = 0)
    (h : s • g = rescale (fun _ ↦ s) F.toPowerSeries) :
    g.subst ![g.subst ![X 0, X 1], X 2] =
      (g.subst ![X 0, g.subst ![X 1, X 2]] : MvPowerSeries (Fin 3) R) := by
  have hX (i : Fin 3) : PowerSeries.HasSubst (s • X i : MvPowerSeries (Fin 3) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hreg : IsSMulRegular (MvPowerSeries (Fin 3) R) s := .pi fun _ ↦ hs.isSMulRegular
  -- `IsSMulRegular` is injectivity of `s • ·`, so it suffices to compare both sides times `s`.
  refine hreg (?_ : s • _ = s • _)
  rw [smul_subst_of_smul_eq_rescale h (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hg),
    smul_subst_of_smul_eq_rescale h (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hg)]
  simp only [Matrix.smul_cons, Matrix.smul_empty]
  rw [smul_subst_of_smul_eq_rescale h HasSubst.X_X, smul_subst_of_smul_eq_rescale h HasSubst.X_X]
  simp only [Matrix.smul_cons, Matrix.smul_empty]
  exact F.assoc' (hX 0) (hX 1) (hX 2)

/-- The rescaling of `F` by the polynomial variable, over `R[s]`. -/
private def rescaleGeneric (F : FormalGroup R) : FormalGroup (Polynomial R) where
  toPowerSeries := rescaleSeries (F.map Polynomial.C).toPowerSeries Polynomial.X
  zero_constantCoeff := constantCoeff_rescaleSeries (F.map Polynomial.C).zero_constantCoeff _
  lin_coeff_X := by simp [coeff_rescaleSeries, F.lin_coeff_X]
  lin_coeff_Y := by simp [coeff_rescaleSeries, F.lin_coeff_Y]
  assoc := assoc_of_smul_eq_rescale (F.map Polynomial.C) Polynomial.isRegular_X.left
    (constantCoeff_rescaleSeries (F.map Polynomial.C).zero_constantCoeff _)
    (smul_rescaleSeries (F.map Polynomial.C).zero_constantCoeff _)

/-- Evaluating the generic rescaling at `s` gives the series of coefficients rescaled by `s`. -/
private theorem map_rescaleGeneric (F : FormalGroup R) (s : R) :
    ((rescaleGeneric F).map (Polynomial.evalRingHom s)).toPowerSeries =
      rescaleSeries F.toPowerSeries s := by
  ext d
  simp [rescaleGeneric, coeff_rescaleSeries, mul_comm (coeff d _)]

/-- The **rescaling** `F^s` of a formal group law `F` by `s ∈ R`: the formal group law whose
coefficient of `Xⁱ Yʲ` is `s ^ (i + j - 1)` times that of `F`. It satisfies
`s • F^s(X, Y) = F(s X, s Y)` (`FormalGroup.smul_rescale`), so `F^s(X, Y) = s⁻¹ F(s X, s Y)` when
`s` is a unit. -/
def rescale (F : FormalGroup R) (s : R) : FormalGroup R where
  toPowerSeries := rescaleSeries F.toPowerSeries s
  zero_constantCoeff := constantCoeff_rescaleSeries F.zero_constantCoeff s
  lin_coeff_X := by simp [coeff_rescaleSeries, F.lin_coeff_X]
  lin_coeff_Y := by simp [coeff_rescaleSeries, F.lin_coeff_Y]
  assoc := map_rescaleGeneric F s ▸ ((rescaleGeneric F).map (Polynomial.evalRingHom s)).assoc

variable (F : FormalGroup R) (s : R)

/-- The coefficient of a monomial of total degree `n` in `F^s` is `s ^ (n - 1)` times its
coefficient in `F`. -/
@[simp]
theorem coeff_rescale (d : Fin 2 →₀ ℕ) :
    coeff d (F.rescale s).toPowerSeries = s ^ (d.degree - 1) * coeff d F.toPowerSeries :=
  coeff_rescaleSeries _ _ _

/-- The rescaling satisfies `s • F^s(X, Y) = F(s X, s Y)`. This identity characterises `F^s`
when `s` is a nonzerodivisor, but not in general: for `s = 0` every series satisfies it. -/
theorem smul_rescale :
    s • (F.rescale s).toPowerSeries = MvPowerSeries.rescale (fun _ ↦ s) F.toPowerSeries :=
  smul_rescaleSeries F.zero_constantCoeff s

/-- The rescaling of a commutative formal group law is commutative. -/
instance [F.IsComm] : (F.rescale s).IsComm where
  comm := by
    ext d
    have h := congrArg (coeff d) (IsComm.comm (F := F))
    simp only [coeff_subst_X_one_X_zero] at h ⊢
    simp only [coeff_rescale, ← h]
    congr 2
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_two, add_comm]

/-- Rescaling commutes with base change: `(F^s).map f = (F.map f)^(f s)`. -/
@[simp]
theorem map_rescale (f : R →+* S) : (F.rescale s).map f = (F.map f).rescale (f s) := by
  ext d
  simp

/-- Rescaling by `1` does nothing. -/
@[simp]
theorem rescale_one : F.rescale 1 = F := by
  ext d
  simp

/-- Rescaling is an action of the multiplicative monoid: `(F^s)^t = F^(s t)`. -/
theorem rescale_rescale (t : R) : (F.rescale s).rescale t = F.rescale (s * t) := by
  ext d
  simp only [coeff_rescale]
  ring

end FormalGroup
