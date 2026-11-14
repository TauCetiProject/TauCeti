/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Coboundary
import TauCeti.RingTheory.FormalGroup.Hom.Defect
import TauCeti.RingTheory.FormalGroup.Obstruction
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Symmetric 2-cocycles of a formal group law of finite height

Let `p` be a prime with `p = 0` in the commutative ring `R`, and let `F` be a commutative formal
group law over `R` whose `p`-series `[p]_F(X) = v X^(pʰ) + ⋯` has order at least `pʰ` and a unit
coefficient `v` of `X^(pʰ)`. Over a field of characteristic `p` this says that `F` has height
`h`. Following Lubin and Tate, this file shows that the only obstructions for a symmetric
2-cocycle of `F` (`FormalGroup.IsSymmetricCocycle`) to be a coboundary
`g(F(X, Y)) - g(X) - g(Y)` sit in the degrees `pⁱ` with `0 < i < h`.

Let a symmetric 2-cocycle `Γ` vanish below degree `n ≠ 0`; its degree-`n` part is `c C_n` for the
Lazard cocycle `C_n`.

* If `n` is not a power of `p`, then `d_n` is a unit in `R`, and `C_n` is the leading term of the
  coboundary of `d_n⁻¹ Xⁿ`.
* If `n = pᵏ` with `k ≥ h`, choose `g₀ = X + ⋯` whose coboundary vanishes below degree `pʰ`. Its
  degree-`pʰ` part is `-v C_(pʰ)`, by the obstruction theory of
  `TauCeti.RingTheory.FormalGroup.Obstruction`. Since `x ↦ x ^ (p ^ m)` is additive, the coboundary
  of `g₀ ^ (p ^ m)` is the `p ^ m`-th power of that of `g₀`
  (`FormalGroup.homDefect_𝔾ₐ_pow_prime_pow`), with leading term `-v ^ (p ^ m) C_(p^(h + m))`.
* If `n = pⁱ` with `0 < i < h`, no coboundary has a nonzero leading term `c C_n`: the leading term
  of the coboundary of `g` in degree `pⁱ` is read off the coefficient of `X^(pⁱ)` in `g([p]_F(X))`,
  which vanishes because `[p]_F` has order `pʰ > pⁱ`
  (`FormalGroup.homogeneousComponent_homDefect_𝔾ₐ_eq_zero`).

So in every degree outside `{pⁱ : 0 < i < h}` the leading term of a symmetric 2-cocycle is the
leading term of a coboundary
(`FormalGroup.IsSymmetricCocycle.exists_succ_le_order_sub_homDefect_𝔾ₐ`).
The corrections in degree `pᵏ` have order `p^(k - h)`, which still tends to infinity, so they
converge: a symmetric 2-cocycle without constant term and without terms of degree at most `pⁱ` for
`0 < i < h` is a coboundary (`FormalGroup.IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ`). In
particular every symmetric 2-cocycle without constant term of a law of height one is a coboundary
(`FormalGroup.IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ_of_le_order_nsmulSeries_prime`).

More generally, if `Γ : Fin (h - 1) → MvPowerSeries (Fin 2) R` is any family of symmetric
2-cocycles whose `j`-th member vanishes below degree `p^(j + 1)` with leading term a unit multiple
of the Lazard cocycle `C_(p^(j + 1))`, then `Γ` is linearly independent modulo coboundaries
(`FormalGroup.sum_smul_eq_homDefect_𝔾ₐ_iff`) and every symmetric 2-cocycle without constant term
decomposes as `∑ j, c j • Γ j` plus a coboundary for a *unique* tuple `c : Fin (h - 1) → R`
(`FormalGroup.IsSymmetricCocycle.existsUnique_sum_smul_add_homDefect_𝔾ₐ`).

In Lubin–Tate deformation theory, symmetric 2-cocycles modulo coboundaries describe the
first-order deformations of `F`; these results show that the symmetric cohomology modulo
coboundaries is free of rank `h - 1` over `R`, spanned by representatives in degrees `pⁱ`,
`0 < i < h`.

## Main results

* `FormalGroup.homogeneousComponent_homDefect_𝔾ₐ_eq_neg_coeff_subst_nsmulSeries`: in
  characteristic `p`, the degree-`pᵏ` part of a coboundary vanishing below degree `pᵏ` is
  `-c C_(pᵏ)`, for `c` the coefficient of `X^(pᵏ)` in `g([p]_F(X))`.
* `FormalGroup.homogeneousComponent_homDefect_𝔾ₐ_eq_zero`: a coboundary vanishing below degree
  `pⁱ`, where `[p]_F` has order greater than `pⁱ`, also vanishes in degree `pⁱ`.
* `FormalGroup.IsSymmetricCocycle.exists_succ_le_order_sub_homDefect_𝔾ₐ`: in the nonzero degrees
  outside `pⁱ`, `0 < i < h`, the leading term of a symmetric 2-cocycle is that of a coboundary.
* `FormalGroup.IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ`: a symmetric 2-cocycle vanishing to
  order greater than `pⁱ` for every `0 < i < h`, and without constant term, is a coboundary.
* `FormalGroup.IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ_of_le_order_nsmulSeries_prime`: for
  `h = 1`, every symmetric 2-cocycle without constant term is a coboundary.
* `FormalGroup.sum_smul_eq_homDefect_𝔾ₐ_iff`: series of orders `≥ p^(j + 1)` with unit Lazard
  leading coefficients in degrees `p, …, p^(h - 1)` are linearly independent modulo coboundaries.
* `FormalGroup.IsSymmetricCocycle.existsUnique_sum_smul_add_homDefect_𝔾ₐ`: every symmetric
  2-cocycle without constant term decomposes uniquely modulo coboundaries along such a family of
  symmetric 2-cocycles.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1–§2.
* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* M. Hazewinkel, *Formal Groups and Applications*, §22.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] {F : FormalGroup R} {p h : ℕ}

variable [F.IsComm]

/-- **The degree-`pᵏ` part of a coboundary.** Let `p` be a prime with `p = 0` in `R`. If the
coboundary `g(F(X, Y)) - g(X) - g(Y)` of a power series `g` vanishes below degree `pᵏ`, its
degree-`pᵏ` part is `-c C_(pᵏ)`, where `c` is the coefficient of `X^(pᵏ)` in `g([p]_F(X))`. -/
theorem homogeneousComponent_homDefect_𝔾ₐ_eq_neg_coeff_subst_nsmulSeries (hp : p.Prime)
    (hpR : (p : R) = 0) {g : PowerSeries R} {k : ℕ}
    (hgk : ((p ^ k : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order) :
    homogeneousComponent (p ^ k) (F.homDefect 𝔾ₐ g) =
      ↑((-PowerSeries.coeff (p ^ k) (PowerSeries.subst (F.nsmulSeries p) g)) •
        TauCeti.lazardCocycle (p ^ k) R) := by
  -- the coboundary has no constant term, so neither has `g`
  have hg : PowerSeries.constantCoeff g = 0 := by
    simpa using one_le_order_iff_constCoeff_eq_zero.mp
      ((Nat.one_le_cast.mpr (Nat.one_le_pow _ _ hp.pos)).trans hgk)
  rw [homogeneousComponent_homDefect_eq_smul_lazardCocycle hg hp hpR hgk,
    nsmulSeries_𝔾ₐ_eq_zero hpR, PowerSeries.subst_zero, zero_sub, map_neg]

/-- **Coboundaries vanish in the degrees `pⁱ` below the height.** Let `p` be a prime and let
`[p]_F` have order greater than `pⁱ`, so that `p = 0` in `R`. If the coboundary
`g(F(X, Y)) - g(X) - g(Y)` of a power series `g` vanishes below degree `pⁱ`, it also vanishes in
degree `pⁱ`. In particular no coboundary has leading term `c C_(pⁱ)` with `c ≠ 0`. -/
theorem homogeneousComponent_homDefect_𝔾ₐ_eq_zero (hp : p.Prime) {i : ℕ}
    (hF : ((p ^ i : ℕ) : ℕ∞) < (F.nsmulSeries p).order) {g : PowerSeries R}
    (hgi : ((p ^ i : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order) :
    homogeneousComponent (p ^ i) (F.homDefect 𝔾ₐ g) = 0 := by
  have hpR : (p : R) = 0 := F.natCast_eq_zero_of_two_le_order_nsmulSeries <| by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ ((p ^ i : ℕ) : ℕ∞) := Nat.cast_le.mpr (Nat.one_le_pow _ _ hp.pos)
    simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (h1.trans_lt hF)
  have hg : PowerSeries.constantCoeff g = 0 := by
    simpa using one_le_order_iff_constCoeff_eq_zero.mp
      ((Nat.one_le_cast.mpr (Nat.one_le_pow _ _ hp.pos)).trans hgi)
  -- the leading coefficient is minus that of `X^(pⁱ)` in `g([p]_F(X))`, which vanishes
  rw [homogeneousComponent_homDefect_𝔾ₐ_eq_neg_coeff_subst_nsmulSeries hp hpR hgi,
    PowerSeries.coeff_subst_eq_mul (F.constantCoeff_nsmulSeries p) hg hF.le,
    PowerSeries.coeff_of_lt_order _ hF]
  simp

/-- If the coboundary of `g = X + ⋯` vanishes below degree `pʰ`, then the coboundary of
`g ^ (p ^ m)` vanishes below degree `p^(h + m)`, with leading term `-v ^ (p ^ m) C_(p^(h + m))`,
where `v` is the coefficient of `X^(pʰ)` in `[p]_F`. -/
private theorem homogeneousComponent_homDefect_𝔾ₐ_pow (hp : p.Prime) (hpR : (p : R) = 0)
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order) {g : PowerSeries R}
    (hg₀ : PowerSeries.constantCoeff g = 0) (hg₁ : PowerSeries.coeff 1 g = 1)
    (hgh : ((p ^ h : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order) (m : ℕ) :
    ((p ^ (h + m) : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ (g ^ p ^ m)).order ∧
      homogeneousComponent (p ^ (h + m)) (F.homDefect 𝔾ₐ (g ^ p ^ m)) =
        ↑((-PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ p ^ m) •
          TauCeti.lazardCocycle (p ^ (h + m)) R) := by
  have hord : ((p ^ (h + m) : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ (g ^ p ^ m)).order := by
    rw [F.homDefect_𝔾ₐ_pow_prime_pow hp hpR]
    calc ((p ^ (h + m) : ℕ) : ℕ∞) = p ^ m • ((p ^ h : ℕ) : ℕ∞) := by
          rw [nsmul_eq_mul, pow_add]
          push_cast
          ring
      _ ≤ p ^ m • (F.homDefect 𝔾ₐ g).order := nsmul_le_nsmul_right hgh _
      _ ≤ _ := le_order_pow _
  refine ⟨hord, ?_⟩
  -- `y = g([p]_F(X))` vanishes below degree `pʰ`, with coefficient `v` of `X^(pʰ)`
  set y := PowerSeries.subst (F.nsmulSeries p) g
  have hy : PowerSeries.coeff (p ^ h) y = PowerSeries.coeff (p ^ h) (F.nsmulSeries p) := by
    rw [PowerSeries.coeff_subst_eq_mul (F.constantCoeff_nsmulSeries p) hg₀ hF, hg₁]
    simp
  have hyo : ((p ^ h : ℕ) : ℕ∞) ≤ PowerSeries.order y :=
    hF.trans (PowerSeries.le_order_subst_right' (F.constantCoeff_nsmulSeries p) hg₀)
  rw [homogeneousComponent_homDefect_𝔾ₐ_eq_neg_coeff_subst_nsmulSeries hp hpR hord,
    PowerSeries.subst_pow (.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries p)), pow_add,
    PowerSeries.coeff_pow_mul_of_le_order hyo, hy]

/-- **Leading terms of symmetric 2-cocycles outside the degrees `pⁱ`, `0 < i < h`.** Let `p` be a
prime with `p = 0` in `R`, and let `[p]_F` have order at least `pʰ` and a unit coefficient of
`X^(pʰ)`. If a symmetric 2-cocycle `Γ` vanishes below degree `n ≠ 0`, and `n ≠ pⁱ` for
`0 < i < h`, then `Γ` agrees up to degree `n` with the coboundary of some `g` without constant
term: `Γ - (g(F(X, Y)) - g(X) - g(Y))` vanishes below degree `n + 1`. Moreover `g` vanishes below
degree `n / pʰ`, so that these corrections converge. -/
theorem IsSymmetricCocycle.exists_succ_le_order_sub_homDefect_𝔾ₐ (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Γ : MvPowerSeries (Fin 2) R} (hΓ : F.IsSymmetricCocycle Γ) {n : ℕ} (hn₀ : n ≠ 0)
    (hn : ∀ i, 0 < i → i < h → n ≠ p ^ i) (hΓn : n ≤ Γ.order) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ ((n / p ^ h : ℕ) : ℕ∞) ≤ g.order ∧
      ((n + 1 : ℕ) : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ g).order := by
  obtain ⟨c, hc⟩ := hΓ.exists_homogeneousComponent_eq_smul_lazardCocycle hn₀ hΓn
  -- it suffices that the coboundary of `g` vanishes below degree `n` with degree-`n` part `c C_n`
  have hclose (g : PowerSeries R) (hgn : (n : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order)
      (hgc : homogeneousComponent n (F.homDefect 𝔾ₐ g) = ↑(c • TauCeti.lazardCocycle n R)) :
      ((n + 1 : ℕ) : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ g).order :=
    succ_le_order_of_homogeneousComponent_eq_zero (le_order_sub hΓn hgn)
      (by rw [map_sub, hc, hgc, sub_self])
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · -- in degree `1` the leading term vanishes, since `C₁ = 0`
      refine ⟨0, map_zero _, by simp, ?_⟩
      rw [homDefect_zero, sub_zero]
      refine succ_le_order_of_homogeneousComponent_eq_zero hΓn ?_
      rw [hc, pow_zero, TauCeti.lazardCocycle_eq_zero_of_lt_two one_lt_two, smul_zero,
        MvPolynomial.coe_zero]
    -- in degree `p^(h + m)` the leading term is a multiple of that of the coboundary of
    -- `g₀ ^ (p ^ m)`, for `g₀ = X + ⋯` whose coboundary vanishes below degree `pʰ`
    have hkh : h ≤ k := by
      by_contra hlt
      exact hn k hk (by omega) rfl
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkh
    obtain ⟨g₀, hg₀, hg₁, hgh⟩ := exists_le_order_homDefect_of_le_order_nsmulSeries (G := 𝔾ₐ) hp hF
      (by rw [nsmulSeries_𝔾ₐ_eq_zero hpR, PowerSeries.order_zero]; exact le_top)
    obtain ⟨hord, hcomp⟩ := homogeneousComponent_homDefect_𝔾ₐ_pow hp hpR hF hg₀ hg₁ hgh m
    have hu := hv.pow (p ^ m)
    refine ⟨(-c * ↑hu.unit⁻¹) • g₀ ^ p ^ m, ?_, ?_, hclose _ ?_ ?_⟩
    · simp [hg₀, hp.ne_zero]
    · rw [pow_add, Nat.mul_div_cancel_left _ (pow_pos hp.pos h)]
      exact (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (p ^ m) hg₀).trans
        PowerSeries.le_order_smul
    · rw [homDefect_𝔾ₐ_smul]
      exact hord.trans le_order_smul
    · rw [homDefect_𝔾ₐ_smul, map_smul, hcomp, ← MvPolynomial.coe_smul, smul_smul, neg_mul,
        neg_mul_neg, mul_assoc, hu.val_inv_mul, mul_one]
  · -- `d_n` is prime to `p`, and `C_n` is the leading term of the coboundary of `d_n⁻¹ Xⁿ`
    have hd := TauCeti.isUnit_lazardGcd hp hpR hn₀ hpow
    have hXn : (n : ℕ∞) ≤ ((c * ↑hd.unit⁻¹) • PowerSeries.X ^ n : PowerSeries R).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
    refine ⟨(c * ↑hd.unit⁻¹) • PowerSeries.X ^ n, by simp [hn₀], ?_,
      hclose _ (F.le_order_homDefect_𝔾ₐ hXn) ?_⟩
    · exact (Nat.cast_le.mpr (Nat.div_le_self n _)).trans hXn
    · have h := F.homogeneousComponent_homDefect_add_sub (G := 𝔾ₐ) (f := 0) (by simp) hn₀
        (c * ↑hd.unit⁻¹)
      rw [_root_.zero_add, homDefect_zero, sub_zero] at h
      rw [h, ← TauCeti.lazardGcd_nsmul_lazardCocycle hn₀, ← Nat.cast_smul_eq_nsmul R, smul_smul,
        mul_assoc, hd.val_inv_mul, mul_one]

/-- One step towards `IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ`: if `Γ - δg` vanishes below
degree `n ≠ 0`, a correction `e` vanishing below degree `n / pʰ` makes `Γ - δ(g + e)` vanish below
degree `n + 1`. In the degrees `pⁱ`, `0 < i < h`, the correction is zero, since both `Γ` and the
coboundary `δg` vanish there. -/
private theorem IsSymmetricCocycle.exists_succ_le_order_sub_homDefect_𝔾ₐ_add (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Γ : MvPowerSeries (Fin 2) R} (hΓ : F.IsSymmetricCocycle Γ)
    (hΓh : ∀ i, 0 < i → i < h → ((p ^ i : ℕ) : ℕ∞) < Γ.order) {n : ℕ} (hn : n ≠ 0)
    {g : PowerSeries R} (hgn : (n : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ g).order) :
    ∃ e : PowerSeries R, PowerSeries.constantCoeff e = 0 ∧ ((n / p ^ h : ℕ) : ℕ∞) ≤ e.order ∧
      ((n + 1 : ℕ) : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ (g + e)).order := by
  by_cases hpow : ∃ i, 0 < i ∧ i < h ∧ n = p ^ i
  · obtain ⟨i, hi₀, hih, rfl⟩ := hpow
    refine ⟨0, map_zero _, by simp, ?_⟩
    have hδ : ((p ^ i : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order := by
      simpa using le_order_sub (hΓh i hi₀ hih).le hgn
    rw [_root_.add_zero]
    refine succ_le_order_of_homogeneousComponent_eq_zero hgn ?_
    rw [map_sub, homogeneousComponent_of_lt_order_eq_zero (hΓh i hi₀ hih),
      homogeneousComponent_homDefect_𝔾ₐ_eq_zero hp
        ((Nat.cast_lt.mpr (Nat.pow_lt_pow_right hp.one_lt hih)).trans_le hF) hδ, sub_zero]
  · push Not at hpow
    obtain ⟨e, he₀, he, hlt⟩ := (hΓ.sub (F.isSymmetricCocycle_homDefect_𝔾ₐ g)
      ).exists_succ_le_order_sub_homDefect_𝔾ₐ hp hpR hF hv hn hpow hgn
    exact ⟨e, he₀, he, by rwa [homDefect_𝔾ₐ_add, ← sub_sub]⟩

/-- Successive approximations to a series whose coboundary is a given cocycle: step `n` adds the
correction `e (n + 1) g` to the current approximation `g`. -/
private noncomputable def approx (e : ℕ → PowerSeries R → PowerSeries R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => approx e n + e (n + 1) (approx e n)

/-- **Lubin–Tate: symmetric 2-cocycles of order beyond the degrees `pⁱ`, `0 < i < h`, are
coboundaries.** Let `p` be a prime with `p = 0` in `R`, and let `F` be a commutative formal group
law whose `p`-series has order at least `pʰ` and a unit coefficient of `X^(pʰ)`, for instance a
law of height `h` over a field of characteristic `p`. Let `Γ` be a symmetric 2-cocycle of `F`
without constant term that vanishes to order greater than `pⁱ` for every `0 < i < h`. Then
`Γ = g(F(X, Y)) - g(X) - g(Y)` for a power series `g` without constant term. -/
theorem IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ (hp : p.Prime) (hpR : (p : R) = 0)
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Γ : MvPowerSeries (Fin 2) R} (hΓ : F.IsSymmetricCocycle Γ) (hΓ₀ : constantCoeff Γ = 0)
    (hΓh : ∀ i, 0 < i → i < h → ((p ^ i : ℕ) : ℕ∞) < Γ.order) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ Γ = F.homDefect 𝔾ₐ g := by
  choose! e he using fun (n : ℕ) (g : PowerSeries R) (hn : n ≠ 0)
    (hgn : (n : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ g).order) ↦
    hΓ.exists_succ_le_order_sub_homDefect_𝔾ₐ_add hp hpR hF hv hΓh hn hgn
  -- the approximations: `Γ - δ(approx e n)` vanishes below degree `n + 1`
  have key (n : ℕ) : PowerSeries.constantCoeff (approx e n) = 0 ∧
      ((n + 1 : ℕ) : ℕ∞) ≤ (Γ - F.homDefect 𝔾ₐ (approx e n)).order := by
    induction n with
    | zero =>
      rw [approx, homDefect_zero, sub_zero, Nat.zero_add, Nat.cast_one,
        one_le_order_iff_constCoeff_eq_zero]
      exact ⟨map_zero _, hΓ₀⟩
    | succ n ih =>
      obtain ⟨he₀, -, hlt⟩ := he (n + 1) (approx e n) n.succ_ne_zero ih.2
      exact ⟨by rw [approx, map_add, ih.1, he₀, _root_.add_zero], hlt⟩
  -- the corrections after step `a` vanish below degree `a / pʰ`
  have hstab (a k : ℕ) : ((a / p ^ h : ℕ) : ℕ∞) ≤ (approx e (a + k) - approx e a).order := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := (he (a + k + 1) (approx e (a + k)) (by omega) (key _).2).2.1
      rw [show approx e (a + (k + 1)) - approx e a =
        e (a + k + 1) (approx e (a + k)) + (approx e (a + k) - approx e a) by
          rw [← add_assoc, approx]
          abel]
      refine (le_min (hk.trans' ?_) ih).trans (PowerSeries.min_order_le_order_add _ _)
      exact Nat.cast_le.mpr (Nat.div_le_div_right (by omega))
  -- the limit of the approximations along the multiples of `pʰ`
  obtain ⟨g, hlim⟩ := PowerSeries.exists_forall_le_order_sub
    (f := fun m ↦ approx e (m * p ^ h)) fun m ↦ by
      have := hstab (m * p ^ h) (p ^ h)
      rwa [Nat.mul_div_cancel _ (pow_pos hp.pos h), ← Nat.succ_mul] at this
  refine ⟨g, ?_, ?_⟩
  · have h₁ := PowerSeries.coeff_of_lt_order 0 ((hlim 1).trans_lt' (by simp))
    rwa [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (key _).1, sub_zero] at h₁
  · -- `Γ - δg` vanishes below every degree
    refine sub_eq_zero.mp (order_eq_top_iff.mp (top_le_iff.mp
      (ENat.forall_natCast_le_iff_le.mp fun m _ ↦ ?_)))
    have hdiff := F.le_order_homDefect_𝔾ₐ (hlim m)
    rw [homDefect_𝔾ₐ_sub] at hdiff
    have h := le_order_sub ((key (m * p ^ h)).2.trans' (Nat.cast_le.mpr ?_)) hdiff
    · rwa [sub_sub_sub_cancel_right] at h
    · nlinarith [Nat.one_le_pow h p hp.pos]

/-- **Height-one rigidity for symmetric 2-cocycles.** If `p` is a prime and `[p]_F` has order at
least `p` with a unit coefficient of `Xᵖ` (for instance when `F` has height `1` over a field of
characteristic `p`), every symmetric 2-cocycle of `F` without constant term is a coboundary. -/
theorem IsSymmetricCocycle.exists_eq_homDefect_𝔾ₐ_of_le_order_nsmulSeries_prime (hp : p.Prime)
    (hF : (p : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff p (F.nsmulSeries p)))
    {Γ : MvPowerSeries (Fin 2) R} (hΓ : F.IsSymmetricCocycle Γ) (hΓ₀ : constantCoeff Γ = 0) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ Γ = F.homDefect 𝔾ₐ g := by
  have hpR : (p : R) = 0 :=
    F.natCast_eq_zero_of_two_le_order_nsmulSeries ((Nat.cast_le.mpr hp.two_le).trans hF)
  exact hΓ.exists_eq_homDefect_𝔾ₐ (h := 1) hp hpR (by simpa using hF) (by simpa using hv) hΓ₀
    fun _ hi₀ hi₁ ↦ by omega

/-- **Linear independence of Lazard-leading cocycle representatives modulo coboundaries.** Let `p`
be a prime and `[p]_F` have order at least `pʰ`. Suppose `Γ : Fin (h - 1) → MvPowerSeries (Fin 2) R`
has `Γ j` of order at least `p^(j + 1)` with degree-`p^(j + 1)` homogeneous component `u j • C` for
units `u j`. Then a linear combination `∑ j, c j • Γ j` is a coboundary `F.homDefect 𝔾ₐ g` if and
only if `c = 0`. -/
theorem sum_smul_eq_homDefect_𝔾ₐ_iff (hp : p.Prime)
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    {Γ : Fin (h - 1) → MvPowerSeries (Fin 2) R} {u : Fin (h - 1) → R}
    (hΓ_ord : ∀ j, ((p ^ (j.1 + 1) : ℕ) : ℕ∞) ≤ (Γ j).order)
    (hΓ_comp : ∀ j, homogeneousComponent (p ^ (j.1 + 1)) (Γ j) =
      ↑(u j • TauCeti.lazardCocycle (p ^ (j.1 + 1)) R))
    (hu : ∀ j, IsUnit (u j)) {c : Fin (h - 1) → R} :
    (∃ g : PowerSeries R, ∑ j, c j • Γ j = F.homDefect 𝔾ₐ g) ↔ c = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun hc ↦ ⟨0, by simp [hc]⟩⟩
  suffices ∀ k : ℕ, (hk : k < h - 1) → c ⟨k, hk⟩ = 0 by
    funext ⟨k, hk⟩
    exact this k hk
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    -- Every term `c j • Γ j` has order at least `p^(k + 1)`: either `j < k` and `c j = 0`, or
    -- `k ≤ j` and `Γ j` has order `≥ p^(j + 1) ≥ p^(k + 1)`.
    have hterm_ord (j : Fin (h - 1)) : ((p ^ (k + 1) : ℕ) : ℕ∞) ≤ (c j • Γ j).order := by
      rcases lt_or_ge j.1 k with hlt | hge
      · rw [ih j.1 hlt j.2, zero_smul, order_zero]
        exact le_top
      · exact ((Nat.cast_le.mpr (Nat.pow_le_pow_right hp.pos (by omega))).trans (hΓ_ord j)).trans
          le_order_smul
    have hsum_ord : ((p ^ (k + 1) : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order := by
      rw [← hg]
      exact le_order fun d hd ↦ by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j _ ↦ coeff_of_lt_order (hd.trans_le (hterm_ord j))
    -- The coboundary vanishes in degree `p^(k + 1)` because `p^(k + 1) < pʰ`.
    have hrhs : homogeneousComponent (p ^ (k + 1)) (F.homDefect 𝔾ₐ g) = 0 :=
      F.homogeneousComponent_homDefect_𝔾ₐ_eq_zero hp
        ((Nat.cast_lt.mpr (Nat.pow_lt_pow_right hp.one_lt (by omega))).trans_le hF) hsum_ord
    -- On the left, only `j = ⟨k, hk⟩` contributes in degree `p^(k + 1)`.
    have hlhs := congrArg (homogeneousComponent (p ^ (k + 1))) hg
    rw [hrhs, map_sum, Finset.sum_eq_single ⟨k, hk⟩] at hlhs
    · rw [map_smul, hΓ_comp ⟨k, hk⟩, ← MvPolynomial.coe_smul, smul_smul,
        MvPolynomial.coe_eq_zero_iff, TauCeti.smul_lazardCocycle_eq_zero_iff
          (hp.two_le.trans (Nat.le_self_pow k.succ_ne_zero p))] at hlhs
      exact (hu ⟨k, hk⟩).mul_left_eq_zero.mp hlhs
    · intro j _ hj
      rcases lt_trichotomy j.1 k with hlt | heq | hgt
      · simp [ih j.1 hlt j.2]
      · exact absurd (Fin.ext heq) hj
      · refine homogeneousComponent_of_lt_order_eq_zero ?_
        exact ((Nat.cast_lt.mpr (Nat.pow_lt_pow_right hp.one_lt (by omega))).trans_le
          (hΓ_ord j)).trans_le le_order_smul
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- Pushing the order of `Ψ - δg` across an interval `[n, n + d)` containing no obstruction degree
`pⁱ`, `0 < i < h`. -/
private theorem IsSymmetricCocycle.exists_add_le_order_sub_homDefect_𝔾ₐ (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Ψ : MvPowerSeries (Fin 2) R} (hΨ : F.IsSymmetricCocycle Ψ) {n : ℕ} (hn₀ : n ≠ 0)
    (hΨn : (n : ℕ∞) ≤ Ψ.order) (d : ℕ)
    (hd : ∀ m, n ≤ m → m < n + d → ∀ i, 0 < i → i < h → m ≠ p ^ i) :
    ∃ e : PowerSeries R, PowerSeries.constantCoeff e = 0 ∧
      ((n + d : ℕ) : ℕ∞) ≤ (Ψ - F.homDefect 𝔾ₐ e).order := by
  induction d with
  | zero => exact ⟨0, map_zero _, by simpa using hΨn⟩
  | succ d ih =>
    obtain ⟨e₁, he₁₀, hord₁⟩ := ih fun m hnm hm ↦ hd m hnm (by omega)
    obtain ⟨e₂, he₂₀, -, hord₂⟩ := (hΨ.sub (F.isSymmetricCocycle_homDefect_𝔾ₐ e₁)
      ).exists_succ_le_order_sub_homDefect_𝔾ₐ hp hpR hF hv (by omega)
        (hd (n + d) (by omega) (by omega)) hord₁
    refine ⟨e₁ + e₂, by rw [map_add, he₁₀, he₂₀, _root_.add_zero], ?_⟩
    rwa [homDefect_𝔾ₐ_add, ← sub_sub, ← Nat.add_assoc]

/-- **Lubin–Tate basis theorem for symmetric 2-cocycles.** Let `p` be a prime with `p = 0` in `R`,
and let `F` be a commutative formal group law whose `p`-series has order at least `pʰ` with a unit
coefficient of `X^(pʰ)`. Given symmetric 2-cocycles `Γ : Fin (h - 1) → MvPowerSeries (Fin 2) R`
without constant term such that `Γ j` vanishes below degree `p^(j + 1)` with leading term
`u j • C_(p^(j + 1))` for a unit `u j`, every symmetric 2-cocycle `Φ` of `F` without constant term
decomposes as `∑ j, c j • Γ j + F.homDefect 𝔾ₐ g` for a *unique* coefficient tuple
`c : Fin (h - 1) → R` and some `g : PowerSeries R` without constant term. -/
theorem IsSymmetricCocycle.existsUnique_sum_smul_add_homDefect_𝔾ₐ (hp : p.Prime)
    (hpR : (p : R) = 0) (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hv : IsUnit (PowerSeries.coeff (p ^ h) (F.nsmulSeries p)))
    {Γ : Fin (h - 1) → MvPowerSeries (Fin 2) R} {u : Fin (h - 1) → R}
    (hΓ : ∀ j, F.IsSymmetricCocycle (Γ j))
    (hΓ_ord : ∀ j, ((p ^ (j.1 + 1) : ℕ) : ℕ∞) ≤ (Γ j).order)
    (hΓ_comp : ∀ j, homogeneousComponent (p ^ (j.1 + 1)) (Γ j) =
      ↑(u j • TauCeti.lazardCocycle (p ^ (j.1 + 1)) R))
    (hu : ∀ j, IsUnit (u j)) {Φ : MvPowerSeries (Fin 2) R} (hΦ : F.IsSymmetricCocycle Φ)
    (hΦ₀ : constantCoeff Φ = 0) :
    ∃! c : Fin (h - 1) → R, ∃ g : PowerSeries R,
      PowerSeries.constantCoeff g = 0 ∧ Φ = ∑ j, c j • Γ j + F.homDefect 𝔾ₐ g := by
  -- Uniqueness of `c` follows directly from linear independence modulo coboundaries.
  have huniq (c₁ c₂ : Fin (h - 1) → R)
      (h₁ : ∃ g, PowerSeries.constantCoeff g = 0 ∧ Φ = ∑ j, c₁ j • Γ j + F.homDefect 𝔾ₐ g)
      (h₂ : ∃ g, PowerSeries.constantCoeff g = 0 ∧ Φ = ∑ j, c₂ j • Γ j + F.homDefect 𝔾ₐ g) :
      c₁ = c₂ := by
    obtain ⟨g₁, -, hg₁⟩ := h₁
    obtain ⟨g₂, -, hg₂⟩ := h₂
    have hsub : ∑ j, (c₁ j - c₂ j) • Γ j = F.homDefect 𝔾ₐ (g₂ - g₁) := by
      simp only [sub_smul, Finset.sum_sub_distrib, homDefect_𝔾ₐ_sub]
      linear_combination hg₂ - hg₁
    have h0 := (F.sum_smul_eq_homDefect_𝔾ₐ_iff hp hF hΓ_ord hΓ_comp hu).mp ⟨g₂ - g₁, hsub⟩
    funext j
    exact sub_eq_zero.mp (congrFun h0 j)
  -- For `h = 0`, `Fin (0 - 1)` is empty and `exists_eq_homDefect_𝔾ₐ` applies directly.
  obtain rfl | hh := Nat.eq_zero_or_pos h
  · obtain ⟨g, hg₀, rfl⟩ := hΦ.exists_eq_homDefect_𝔾ₐ (h := 0) hp hpR hF hv hΦ₀
      fun _ _ hi ↦ by omega
    exact ⟨0, ⟨g, hg₀, by simp⟩, fun c hc ↦ (huniq c 0 hc ⟨g, hg₀, by simp⟩)⟩
  -- For `h ≥ 1`, clear degrees up to `p^(h - 1)` inductively by subtracting coboundaries between
  -- powers of `p` and multiples of `Γ ⟨k, hk⟩` at each degree `p^(k + 1)`.
  have hstep : ∀ k ≤ h - 1, ∃ (c : Fin (h - 1) → R) (g : PowerSeries R),
      PowerSeries.constantCoeff g = 0 ∧
        ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (Φ - ∑ j, c j • Γ j - F.homDefect 𝔾ₐ g).order := by
    intro k hk
    induction k with
    | zero => exact ⟨0, 0, map_zero _, by simpa using hΦ.two_le_order hΦ₀⟩
    | succ k ih =>
      obtain ⟨c, g, hg₀, hord⟩ := ih (by omega)
      set Ψ₀ := Φ - ∑ j, c j • Γ j - F.homDefect 𝔾ₐ g
      have hΨ₀ : F.IsSymmetricCocycle Ψ₀ :=
        (hΦ.sub (.sum _ fun j _ ↦ (hΓ j).smul (c j))).sub (F.isSymmetricCocycle_homDefect_𝔾ₐ g)
      have hle : p ^ k + 1 ≤ p ^ (k + 1) := Nat.succ_le_of_lt (Nat.pow_lt_pow_right hp.one_lt
        (Nat.lt_succ_self k))
      obtain ⟨e, he₀, hord₁⟩ := hΨ₀.exists_add_le_order_sub_homDefect_𝔾ₐ hp hpR hF hv (by omega)
        hord (p ^ (k + 1) - (p ^ k + 1)) fun m hlo hhi i _ _ hmi ↦ by
          rw [Nat.add_sub_cancel' hle] at hhi
          rcases le_or_gt i k with hik | hik
          · exact absurd (hmi ▸ Nat.pow_le_pow_right hp.pos hik) (by omega)
          · have hik' : k + 1 ≤ i := hik
            exact absurd (hmi ▸ Nat.pow_le_pow_right hp.pos hik') (by omega)
      rw [Nat.add_sub_cancel' hle] at hord₁
      have hΨ₁ : F.IsSymmetricCocycle (Ψ₀ - F.homDefect 𝔾ₐ e) :=
        hΨ₀.sub (F.isSymmetricCocycle_homDefect_𝔾ₐ e)
      obtain ⟨a, ha⟩ := hΨ₁.exists_homogeneousComponent_eq_smul_lazardCocycle
        (pow_ne_zero _ hp.ne_zero) hord₁
      let j₀ : Fin (h - 1) := ⟨k, by omega⟩
      let d : R := a * ↑(hu j₀).unit⁻¹
      let c' : Fin (h - 1) → R := fun j ↦ c j + if j = j₀ then d else 0
      refine ⟨c', g + e, by rw [map_add, hg₀, he₀, _root_.add_zero], ?_⟩
      have hsum : ∑ j, c' j • Γ j = ∑ j, c j • Γ j + d • Γ j₀ := by
        simp [c', add_smul, Finset.sum_add_distrib]
      have hrew : Φ - ∑ j, c' j • Γ j - F.homDefect 𝔾ₐ (g + e) =
          (Ψ₀ - F.homDefect 𝔾ₐ e) - d • Γ j₀ := by
        rw [hsum, homDefect_𝔾ₐ_add]
        dsimp only [Ψ₀]
        abel
      rw [hrew]
      refine succ_le_order_of_homogeneousComponent_eq_zero
        (le_order_sub hord₁ ((hΓ_ord j₀).trans le_order_smul)) ?_
      rw [map_sub, ha, map_smul, hΓ_comp j₀, ← MvPolynomial.coe_smul, smul_smul,
        mul_assoc, (hu j₀).val_inv_mul, mul_one, sub_self]
  obtain ⟨c, g₁, hg₁₀, hord⟩ := hstep (h - 1) le_rfl
  set Ψ := Φ - ∑ j, c j • Γ j - F.homDefect 𝔾ₐ g₁
  have hΨ : F.IsSymmetricCocycle Ψ :=
    (hΦ.sub (.sum _ fun j _ ↦ (hΓ j).smul (c j))).sub (F.isSymmetricCocycle_homDefect_𝔾ₐ g₁)
  have hΨ₀ : constantCoeff Ψ = 0 :=
    one_le_order_iff_constCoeff_eq_zero.mp ((Nat.cast_le.mpr (by omega)).trans hord)
  obtain ⟨g₂, hg₂₀, hg₂⟩ := hΨ.exists_eq_homDefect_𝔾ₐ hp hpR hF hv hΨ₀ fun i _ hih ↦ by
    refine lt_of_lt_of_le (Nat.cast_lt.mpr ?_) hord
    exact Nat.lt_succ_of_le (Nat.pow_le_pow_right hp.pos (by omega))
  have hex : ∃ g, PowerSeries.constantCoeff g = 0 ∧ Φ = ∑ j, c j • Γ j + F.homDefect 𝔾ₐ g := by
    refine ⟨g₁ + g₂, by rw [map_add, hg₁₀, hg₂₀, _root_.add_zero], ?_⟩
    rw [homDefect_𝔾ₐ_add]
    linear_combination hg₂
  exact ⟨c, hex, fun c' hc' ↦ huniq c' c hc' hex⟩

end FormalGroup
