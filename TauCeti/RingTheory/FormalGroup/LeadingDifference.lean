/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.RingTheory.FormalGroup.Obstruction
-- Proof-only: lowest-degree components and the linear part of a formal group law.
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# The leading difference of two formal group laws

Let `F` and `G` be commutative formal group laws over a commutative ring `R` that agree below
degree `n`: the difference `F - G` has order at least `n`. This difference is the homomorphism
defect of the series `X` from `F` to `G` (`FormalGroup.homDefect_X`), so by the obstruction
theory of `TauCeti.RingTheory.FormalGroup.Obstruction` its degree-`n` part is `c C_n` for the
Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`
(`FormalGroup.exists_homogeneousComponent_sub_eq_smul_lazardCocycle`).

The multiplication-by-`p` series detect `c` in the degrees `n = pᵏ`, `k ≥ 1`, when `p` is a prime
with `p = 0` in `R`: `c` is the coefficient of `Xⁿ` in `[p]_G - [p]_F`
(`FormalGroup.homogeneousComponent_sub_eq_smul_lazardCocycle`). Hence if these coefficients
agree, `F` and `G` also agree in degree `pᵏ`. Over a field of characteristic `p`, this is the case
whenever both `F` and `G` have height greater than `k`, since then both coefficients vanish
(`FormalGroup.succ_le_order_sub_of_lt_height`).

These results control the degree-by-degree comparison in Lazard's classification of
one-dimensional formal group laws over a separably closed field by their height: when two laws
agree below degree `n`, the obstruction to agreeing in degree `n` is `c C_n`, and it vanishes
automatically when `n = pᵏ` with `k` less than the heights of both laws.

## Main results

* `FormalGroup.exists_homogeneousComponent_sub_eq_smul_lazardCocycle`: if commutative formal group
  laws `F` and `G` agree below degree `n`, the degree-`n` part of `F - G` is `c C_n` for some `c`.
* `FormalGroup.homogeneousComponent_sub_eq_smul_lazardCocycle`: if moreover `p = 0` in `R` and
  `n = pᵏ`, `k ≥ 1`, then `c` is the coefficient of `Xⁿ` in `[p]_G - [p]_F`.
* `FormalGroup.succ_le_order_sub_of_coeff_nsmulSeries_eq`: if commutative formal group laws agree
  below degree `pᵏ` and their `p`-series have the same coefficient in degree `pᵏ`, they agree below
  degree `pᵏ + 1`.
* `FormalGroup.succ_le_order_sub_of_lt_height`: over a field of characteristic `p`, two
  commutative formal group laws of height greater than `k` that agree below degree `pᵏ` agree
  below degree `pᵏ + 1`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Springer (1968), Chapter III.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F G : FormalGroup R) [F.IsComm] [G.IsComm]

/-- **The leading difference of two formal group laws is a multiple of the Lazard cocycle.** If
commutative formal group laws `F` and `G` agree below degree `n`, the degree-`n` part of `F - G`
is `c C_n` for the Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n` and some `c : R`, unique for
`n ≥ 2` by `TauCeti.smul_lazardCocycle_injective`. -/
theorem exists_homogeneousComponent_sub_eq_smul_lazardCocycle {n : ℕ}
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    ∃ c : R, homogeneousComponent n (F.toPowerSeries - G.toPowerSeries) =
      ((c • TauCeti.lazardCocycle n R : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  obtain rfl | hn₀ := eq_or_ne n 0
  · exact ⟨0, by simp [homogeneousComponent_zero, F.zero_constantCoeff, G.zero_constantCoeff]⟩
  rw [← homDefect_X] at hn ⊢
  exact exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle PowerSeries.constantCoeff_X
    hn₀ hn

/-- **The `p`-series detect the leading difference in degree `pᵏ`.** Let `p` be a prime with
`p = 0` in `R`, and let commutative formal group laws `F` and `G` agree below degree `n = pᵏ`,
`k ≥ 1`. Then the degree-`n` part of `F - G` is `c C_n`, where `c` is the coefficient of `Xⁿ` in
`[p]_G - [p]_F`. -/
theorem homogeneousComponent_sub_eq_smul_lazardCocycle {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    {k : ℕ} (hk : k ≠ 0) (hn : (p ^ k : ℕ) ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    homogeneousComponent (p ^ k) (F.toPowerSeries - G.toPowerSeries) =
      ((PowerSeries.coeff (p ^ k) (G.nsmulSeries p - F.nsmulSeries p) •
          TauCeti.lazardCocycle (p ^ k) R : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  rw [← homDefect_X] at hn ⊢
  rw [homogeneousComponent_homDefect_eq_smul_lazardCocycle PowerSeries.constantCoeff_X hp hpR hk hn,
    PowerSeries.X_subst,
    PowerSeries.subst_X (.of_constantCoeff_zero (F.constantCoeff_nsmulSeries p))]

/-- **Agreement propagates through degree `pᵏ` when the `p`-series agree there.** Let `p` be a prime
with `p = 0` in `R`. If commutative formal group laws `F` and `G` agree below degree `pᵏ` and the
coefficients of `X^(pᵏ)` in `[p]_F` and `[p]_G` are equal, then `F` and `G` agree below degree
`pᵏ + 1`. -/
theorem succ_le_order_sub_of_coeff_nsmulSeries_eq {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) {k : ℕ} (hn : (p ^ k : ℕ) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    (h : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p)) :
    ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order := by
  obtain rfl | hk := eq_or_ne k 0
  · -- formal group laws always agree below degree two
    rw [← sub_sub_sub_cancel_right F.toPowerSeries G.toPowerSeries (X 0 + X 1)]
    simpa using le_order_sub
      (two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y)
      (two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y)
  refine succ_le_order_of_homogeneousComponent_eq_zero hn ?_
  rw [F.homogeneousComponent_sub_eq_smul_lazardCocycle G hp hpR hk hn, map_sub, h, sub_self,
    zero_smul, MvPolynomial.coe_zero]

/-- **Formal group laws of large height agree through degree `pᵏ` once they agree below it.** Over
a field of characteristic `p`, if commutative formal group laws `F` and `G` both have height
greater than `k` and agree below degree `pᵏ`, then they agree below degree `pᵏ + 1`. -/
theorem succ_le_order_sub_of_lt_height {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime]
    [CharP K p] (F G : FormalGroup K) [F.IsComm] [G.IsComm] {k : ℕ}
    (hF : (k : ℕ∞) < F.height p) (hG : (k : ℕ∞) < G.height p)
    (hn : (p ^ k : ℕ) ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order :=
  F.succ_le_order_sub_of_coeff_nsmulSeries_eq G hp.out (CharP.cast_eq_zero K p) hn <| by
    rw [F.coeff_nsmulSeries_eq_zero_of_lt_height hF, G.coeff_nsmulSeries_eq_zero_of_lt_height hG]

end FormalGroup
