/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Height
-- Proof-only: substitution into a formal group law, the symmetric 2-cocycle lemma, and orders
-- and lowest-degree components of substitutions.
import TauCeti.RingTheory.FormalGroup.AddInv
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The leading difference of two formal group laws

Let `F` and `G` be formal group laws over a commutative ring `R` that agree below degree `n`: the
difference `F - G` has order at least `n`. In degree `n`, the terms of degree at least two of `F`
and `G` only see the linear parts `X + Y` of their arguments, so comparing the degree-`n` parts of
`F(F(X, Y), Z) = F(X, F(Y, Z))` and `G(G(X, Y), Z) = G(X, G(Y, Z))` shows that the degree-`n` part
`Δ` of `F - G` is an additive 2-cocycle:

  `Δ(X, Y) + Δ(X + Y, Z) = Δ(X, Y + Z) + Δ(Y, Z)`.

When `F` and `G` are commutative, `Δ` is also symmetric, so by the symmetric 2-cocycle lemma it is
`c C_n` for the Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`
(`FormalGroup.exists_homogeneousComponent_sub_eq_smul_lazardCocycle`).

The multiplication-by-`p` series detect `c` in the degrees `n = pᵏ`, `k ≥ 1`, when `p` is a prime
with `p = 0` in `R`. The degree-`n` part of `[p]_F(X) - [p]_G(X)` is
`c ∑_{j < p} C_n(j X, X) = -c Xⁿ`, so the coefficients of `Xⁿ` in `[p]_G` and `[p]_F` differ by
exactly `c` (`FormalGroup.coeff_nsmulSeries_sub_coeff_nsmulSeries`). Hence if these coefficients
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
* `FormalGroup.coeff_nsmulSeries_sub_coeff_nsmulSeries`: if moreover `p = 0` in `R` and `n = pᵏ`,
  `k ≥ 1`, then `c` is the coefficient of `Xⁿ` in `[p]_G - [p]_F`.
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

variable {R : Type*} [CommRing R] (F G : FormalGroup R)

section Leading

variable {F G}

/-- A pair of series without constant coefficient has entries without constant coefficient. -/
private theorem constantCoeff_pair_eq_zero {τ : Type*} {x y : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (i : Fin 2) :
    constantCoeff (![x, y] i) = 0 := by
  fin_cases i <;> simp [hx, hy]

/-- `F(x, y) - G(x', y') = (F - G)(x, y) + (G(x, y) - G(x', y'))`. -/
private theorem subst_pair_sub_subst_pair_eq {τ : Type*} {x y x' y' : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    F.toPowerSeries.subst ![x, y] - G.toPowerSeries.subst ![x', y'] =
      (F.toPowerSeries - G.toPowerSeries).subst ![x, y] +
        (G.toPowerSeries.subst ![x, y] - G.toPowerSeries.subst ![x', y']) := by
  rw [subst_sub (hasSubst_of_constantCoeff_zero (constantCoeff_pair_eq_zero hx hy))]
  ring

/-- If `x - x'` and `y - y'` have order at least `n`, so does `F(x, y) - G(x', y')`, provided
`F - G` does. -/
private theorem le_order_subst_pair_sub_subst_pair {τ : Type*} {n : ℕ}
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) {x y x' y' : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (hx' : constantCoeff x' = 0)
    (hy' : constantCoeff y' = 0) (hxx' : n ≤ (x - x').order) (hyy' : n ≤ (y - y').order) :
    (n : ℕ∞) ≤ (F.toPowerSeries.subst ![x, y] - G.toPowerSeries.subst ![x', y']).order := by
  have hxy₀ := constantCoeff_pair_eq_zero hx hy
  have hxy₀' := constantCoeff_pair_eq_zero hx' hy'
  have hxy := hasSubst_of_constantCoeff_zero hxy₀
  rw [subst_pair_sub_subst_pair_eq hx hy]
  refine le_order_add ?_ (le_order_subst_sub_subst hxy (hasSubst_of_constantCoeff_zero hxy₀')
    hxy₀' (fun i ↦ by fin_cases i <;> simpa) _)
  calc (n : ℕ∞) = 1 * n := (one_mul _).symm
    _ ≤ _ := (mul_le_mul' (le_iInf fun i ↦ one_le_order_iff_constCoeff_eq_zero.mpr (hxy₀ i))
      hn).trans (le_order_subst hxy _)

/-- **The degree-`n` part of `F(x, y) - G(x', y')`.** If `F - G`, `x - x'` and `y - y'` have
order at least `n ≠ 0`, then the degree-`n` part of
`F(x, y) - G(x', y') = (F - G)(x, y) + (G(x, y) - G(x', y'))` is
`Δ(lx, ly) + (x - x')ₙ + (y - y')ₙ`, where `Δ` is the degree-`n` part of `F - G` and `lx`, `ly`
are the linear parts of `x`, `y`. -/
private theorem homogeneousComponent_subst_pair_sub_subst_pair {τ : Type*} {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) {x y x' y' : MvPowerSeries τ R}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (hx' : constantCoeff x' = 0)
    (hy' : constantCoeff y' = 0) (hxx' : n ≤ (x - x').order) (hyy' : n ≤ (y - y').order)
    {lx ly : MvPolynomial τ R} (hlx : homogeneousComponent 1 x = lx)
    (hly : homogeneousComponent 1 y = ly) :
    homogeneousComponent n (F.toPowerSeries.subst ![x, y] - G.toPowerSeries.subst ![x', y']) =
      (MvPolynomial.aeval ![lx, ly]
          (homogeneousComponentPoly n (F.toPowerSeries - G.toPowerSeries)) :
        MvPowerSeries τ R) + homogeneousComponent n (x - x') + homogeneousComponent n (y - y') := by
  have hxy₀ := constantCoeff_pair_eq_zero hx hy
  have hxy₀' := constantCoeff_pair_eq_zero hx' hy'
  have hxy := hasSubst_of_constantCoeff_zero hxy₀
  rw [subst_pair_sub_subst_pair_eq hx hy, map_add,
    homogeneousComponent_subst_eq_coe_aeval hn hxy hxy₀ (l := ![lx, ly])
      (fun i ↦ by fin_cases i <;> simp [hlx, hly]),
    homogeneousComponent_subst_sub_subst hn₀ hxy (hasSubst_of_constantCoeff_zero hxy₀') hxy₀'
      (fun i ↦ by fin_cases i <;> simpa),
    Fin.sum_univ_two, G.lin_coeff_X, G.lin_coeff_Y, one_smul, one_smul, add_assoc]
  -- `![x, y] 0 - ![x', y'] 0` and `![x, y] 1 - ![x', y'] 1` reduce to `x - x'` and `y - y'`
  rfl

/-- The degree-`n` part of `F - G` is an additive 2-cocycle when `F - G` has order at least
`n ≠ 0`. -/
private theorem isAddCocycle₂_leadingDiff {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    (homogeneousComponentPoly n (F.toPowerSeries - G.toPowerSeries)).IsAddCocycle₂ := by
  have hX (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
  have hX₀ (i : Fin 3) := constantCoeff_X (R := R) i
  have hc (H : FormalGroup R) (i j : Fin 3) :
      constantCoeff (H.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo (hX i) (hX j))
      (fun s ↦ by fin_cases s <;> simp) H.toPowerSeries, H.zero_constantCoeff, map_zero]
  have hl (H : FormalGroup R) (i j : Fin 3) :
      homogeneousComponent 1 (H.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j]) =
        ((MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin 3) R) :
          MvPowerSeries (Fin 3) R) := by
    rw [homogeneousComponent_one_subst_pair H.zero_constantCoeff H.lin_coeff_X H.lin_coeff_Y
      (hX₀ i) (hX₀ j), homogeneousComponent_one_X, homogeneousComponent_one_X]
    simp
  have hXl (i : Fin 3) : homogeneousComponent 1 (X i : MvPowerSeries (Fin 3) R) =
      ((MvPolynomial.X i : MvPolynomial (Fin 3) R) : MvPowerSeries (Fin 3) R) := by
    rw [homogeneousComponent_one_X, MvPolynomial.coe_X]
  -- the degree-`n` part of `F(X i, X j) - G(X i, X j)` is `Δ(X i, X j)`
  have hpair (i j : Fin 3) :
      (n : ℕ∞) ≤ (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j] -
        G.toPowerSeries.subst ![X i, X j]).order ∧
      homogeneousComponent n (F.toPowerSeries.subst ![(X i : MvPowerSeries (Fin 3) R), X j] -
        G.toPowerSeries.subst ![X i, X j]) =
        ((MvPolynomial.aeval ![MvPolynomial.X i, MvPolynomial.X j]
          (homogeneousComponentPoly n (F.toPowerSeries - G.toPowerSeries)) :
          MvPolynomial (Fin 3) R) : MvPowerSeries (Fin 3) R) := by
    refine ⟨le_order_subst_pair_sub_subst_pair hn (hX₀ i) (hX₀ j) (hX₀ i) (hX₀ j) (by simp)
      (by simp), ?_⟩
    rw [homogeneousComponent_subst_pair_sub_subst_pair hn₀ hn (hX₀ i) (hX₀ j) (hX₀ i) (hX₀ j)
      (by simp) (by simp) (hXl i) (hXl j)]
    simp
  -- both sides of associativity, `F(F(X, Y), Z) - G(G(X, Y), Z)` and
  -- `F(X, F(Y, Z)) - G(X, G(Y, Z))`, have degree-`n` part read off from `Δ`
  have hL := homogeneousComponent_subst_pair_sub_subst_pair hn₀ hn (hc F 0 1) (hX₀ 2) (hc G 0 1)
    (hX₀ 2) (hpair 0 1).1 (by simp) (hl F 0 1) (hXl 2)
  have hR := homogeneousComponent_subst_pair_sub_subst_pair hn₀ hn (hX₀ 0) (hc F 1 2) (hX₀ 0)
    (hc G 1 2) (by simp) (hpair 1 2).1 (hXl 0) (hl F 1 2)
  rw [(hpair 0 1).2, sub_self, map_zero, _root_.add_zero] at hL
  rw [(hpair 1 2).2, sub_self, map_zero, _root_.add_zero] at hR
  rw [F.assoc' (hX 0) (hX 1) (hX 2), G.assoc' (hX 0) (hX 1) (hX 2), hR] at hL
  rw [MvPolynomial.isAddCocycle₂_iff]
  refine MvPolynomial.coe_inj.mp ?_
  rw [MvPolynomial.coe_add, MvPolynomial.coe_add, add_comm]
  exact hL.symm

/-- The degree-`n` part of `F - G` is symmetric when `F` and `G` are commutative and `F - G` has
order at least `n`. -/
private theorem isSymmetric_leadingDiff [F.IsComm] [G.IsComm] {n : ℕ}
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    (homogeneousComponentPoly n (F.toPowerSeries - G.toPowerSeries)).IsSymmetric := by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have h10 := hasSubst_finTwo (hX 1) (hX 0)
  have hsymm : (F.toPowerSeries - G.toPowerSeries).subst ![X 1, X 0] =
      F.toPowerSeries - G.toPowerSeries := by
    rw [subst_sub h10, F.comm' (hX 1) (hX 0), G.comm' (hX 1) (hX 0), finTwo_X_eq_X, subst_self]
    rfl
  refine MvPolynomial.isSymmetric_of_aeval_swap (MvPolynomial.coe_inj.mp ?_)
  rw [← homogeneousComponent_subst_eq_coe_aeval hn h10 (fun i ↦ by fin_cases i <;> simp)
    (fun i ↦ by fin_cases i <;> simp [homogeneousComponent_one_X]), hsymm,
    coe_homogeneousComponentPoly]

end Leading

/-- **The leading difference of two formal group laws is a multiple of the Lazard cocycle.** If
commutative formal group laws `F` and `G` agree below degree `n`, the degree-`n` part of `F - G`
is `c C_n` for the Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n` and some `c : R`, unique for
`n ≥ 2` by `TauCeti.smul_lazardCocycle_injective`. -/
theorem exists_homogeneousComponent_sub_eq_smul_lazardCocycle [F.IsComm] [G.IsComm] {n : ℕ}
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) :
    ∃ c : R, homogeneousComponent n (F.toPowerSeries - G.toPowerSeries) =
      ((c • TauCeti.lazardCocycle n R : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  obtain rfl | hn₀ := eq_or_ne n 0
  · refine ⟨0, ?_⟩
    rw [homogeneousComponent_zero, map_sub, F.zero_constantCoeff, G.zero_constantCoeff, sub_zero,
      map_zero, zero_smul, MvPolynomial.coe_zero]
  obtain ⟨c, hc⟩ := TauCeti.exists_eq_smul_lazardCocycle hn₀
    (isHomogeneous_homogeneousComponentPoly n _) (isSymmetric_leadingDiff hn)
    (isAddCocycle₂_leadingDiff hn₀ hn)
  exact ⟨c, by rw [← coe_homogeneousComponentPoly]; exact congrArg _ hc⟩

/-- The multiplication series of formal group laws agreeing below degree `n ≠ 0` agree below
degree `n`, and the degree-`n` part of `[m]_F(X) - [m]_G(X)` is `∑_{j < m} Δ(j X, X)`, where `Δ`
is the degree-`n` part of `F - G`. -/
private theorem nsmulSeries_sub_nsmulSeries {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n ≤ (F.toPowerSeries - G.toPowerSeries).order) (m : ℕ) :
    (n : ℕ∞) ≤ MvPowerSeries.order (F.nsmulSeries m - G.nsmulSeries m) ∧
      homogeneousComponent n (F.nsmulSeries m - G.nsmulSeries m : MvPowerSeries Unit R) =
        ((∑ j ∈ Finset.range m, MvPolynomial.aeval
          ![(j : MvPolynomial Unit R) * MvPolynomial.X (), MvPolynomial.X ()]
            (homogeneousComponentPoly n (F.toPowerSeries - G.toPowerSeries)) :
          MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- the linear part of `[m]_F` is `m X`
    have hlin : homogeneousComponent 1 (F.nsmulSeries m : MvPowerSeries Unit R) =
        (((m : MvPolynomial Unit R) * MvPolynomial.X () : MvPolynomial Unit R) :
          MvPowerSeries Unit R) := by
      have hm : ((m : MvPolynomial Unit R) : MvPowerSeries Unit R) = m :=
        map_natCast MvPolynomial.coeToMvPowerSeries.ringHom m
      simp [homogeneousComponent_one_eq_C_mul_X, ← PowerSeries.coeff_def, hm]
    have hX : homogeneousComponent 1 (PowerSeries.X : MvPowerSeries Unit R) =
        ((MvPolynomial.X () : MvPolynomial Unit R) : MvPowerSeries Unit R) :=
      (homogeneousComponent_one_X (R := R) ()).trans (MvPolynomial.coe_X _).symm
    rw [F.nsmulSeries_succ, G.nsmulSeries_succ]
    refine ⟨le_order_subst_pair_sub_subst_pair hn (F.constantCoeff_nsmulSeries m)
      PowerSeries.constantCoeff_X (G.constantCoeff_nsmulSeries m) PowerSeries.constantCoeff_X ih.1
      (by simp), ?_⟩
    rw [homogeneousComponent_subst_pair_sub_subst_pair hn₀ hn (F.constantCoeff_nsmulSeries m)
      PowerSeries.constantCoeff_X (G.constantCoeff_nsmulSeries m) PowerSeries.constantCoeff_X ih.1
      (by simp) hlin hX, ih.2, sub_self, map_zero, _root_.add_zero, Finset.sum_range_succ,
      MvPolynomial.coe_add, add_comm]

/-- **The `p`-series detect the leading difference in degree `pᵏ`.** Let `p` be a prime with
`p = 0` in `R`, and let `F` and `G` agree below degree `n = pᵏ`, `k ≥ 1`, with degree-`n` part of
`F - G` equal to `c C_n`. Then the coefficients of `Xⁿ` in `[p]_G` and `[p]_F` differ by `c`: the
degree-`n` part of `[p]_F(X) - [p]_G(X)` is `c ∑_{j < p} C_n(j X, X) = -c Xⁿ`. -/
theorem coeff_nsmulSeries_sub_coeff_nsmulSeries {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    {k : ℕ} (hk : k ≠ 0) (hn : (p ^ k : ℕ) ≤ (F.toPowerSeries - G.toPowerSeries).order) {c : R}
    (hc : homogeneousComponent (p ^ k) (F.toPowerSeries - G.toPowerSeries) =
      ((c • TauCeti.lazardCocycle (p ^ k) R : MvPolynomial (Fin 2) R) :
        MvPowerSeries (Fin 2) R)) :
    PowerSeries.coeff (p ^ k) (G.nsmulSeries p) - PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
      c := by
  have hP : homogeneousComponentPoly (p ^ k) (F.toPowerSeries - G.toPowerSeries) =
      c • TauCeti.lazardCocycle (p ^ k) R :=
    MvPolynomial.coe_inj.mp ((coe_homogeneousComponentPoly _ _).trans hc)
  have h := (nsmulSeries_sub_nsmulSeries F G (pow_ne_zero k hp.ne_zero) hn p).2
  simp_rw [hP, _root_.map_smul] at h
  rw [← Finset.smul_sum, TauCeti.sum_aeval_natCast_mul_lazardCocycle hp
    (by rw [← map_natCast (MvPolynomial.C (σ := Unit)), hpR, map_zero]) hk] at h
  have h' := congrArg (MvPowerSeries.coeff (Finsupp.single () (p ^ k))) h
  rw [coeff_homogeneousComponent, Finsupp.degree_single, ite_eq_left rfl] at h'
  have h'' : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) -
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p) = -c := by
    simpa [MvPolynomial.coeff_X_pow] using h'
  linear_combination -h''

/-- **Agreement propagates through degree `pᵏ` when the `p`-series agree there.** Let `p` be a prime
with `p = 0` in `R`. If commutative formal group laws `F` and `G` agree below degree `pᵏ` and the
coefficients of `X^(pᵏ)` in `[p]_F` and `[p]_G` are equal, then `F` and `G` agree below degree
`pᵏ + 1`. -/
theorem succ_le_order_sub_of_coeff_nsmulSeries_eq [F.IsComm] [G.IsComm] {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) = 0) {k : ℕ} (hn : (p ^ k : ℕ) ≤ (F.toPowerSeries - G.toPowerSeries).order)
    (h : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p)) :
    ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order := by
  obtain rfl | hk := eq_or_ne k 0
  · -- formal group laws always agree below degree two
    rw [show F.toPowerSeries - G.toPowerSeries = (F.toPowerSeries - (X 0 + X 1)) -
      (G.toPowerSeries - (X 0 + X 1)) by ring]
    exact le_order_sub
      (two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y)
      (two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y)
  obtain ⟨c, hc⟩ := F.exists_homogeneousComponent_sub_eq_smul_lazardCocycle G hn
  have hc₀ : c = 0 := by
    rw [← F.coeff_nsmulSeries_sub_coeff_nsmulSeries G hp hpR hk hn hc, h, sub_self]
  refine succ_le_order_of_homogeneousComponent_eq_zero hn ?_
  rw [hc, hc₀, zero_smul, MvPolynomial.coe_zero]

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
