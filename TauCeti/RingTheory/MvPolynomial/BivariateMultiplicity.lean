/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.MvPolynomial.Monad
import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Multiplicity estimates for bivariate polynomials on planar point sets

Let `R` be a characteristic-zero unique factorization domain and `P ⊆ R × R` be a finite set of
points whose second coordinates are pairwise distinct and on which every nonzero bivariate
polynomial `H ∈ R[X₀, X₁]` of total degree `k` vanishes at no more than `N * k` points. If a
nonzero polynomial `F ∈ R[X₀, X₁]` of bidegree `(d₀, d₁)` satisfies
`((∂/∂X₀)^[j] F)(y, x) = 0` for all `(y, x) ∈ P` and all `0 ≤ j < N`, then

`N * #P ≤ 2 * d₀ * d₁ + N * (d₀ + d₁)`.

The proof inducts on the irreducible factorization of `F` using the capped fiber multiplicity
`cappedFiberMult N y x F` (equal to `N` when the vertical fiber `F(Y, x)` vanishes identically, and
to `min N (rootMultiplicity y (F(Y, x)))` otherwise), which is subadditive on products while the
right-hand side `2 * d₀ * d₁ + N * (d₀ + d₁)` is superadditive in `(d₀, d₁)`. On an irreducible
factor `G` of positive `X₀`-degree, `Polynomial.rootMultiplicity_map_evalRingHom_le_of_irreducible`
bounds each fiber multiplicity by `1` plus the root multiplicity of `x` in `Res_Y(G, ∂_Y G)`, a
nonzero univariate polynomial of degree at most `2 * d₀ * d₁`; summing over the distinct second
coordinates `x` and applying the zero-count hypothesis to `G` yields the bound.

Applied to the `N × N` conjugate grid `{(x + y θ, x - y θ) : x, y ∈ S}` (`#S = N`) for an element
`θ ∈ R` linearly independent from `1` over `ℤ`, Schwartz–Zippel after the invertible linear
substitution `(X₀, X₁) ↦ (X₀ + θ X₁, X₀ - θ X₁)` supplies the zero-count hypothesis, forcing
`F = 0` whenever `2 * d₀ * d₁ + N * (d₀ + d₁) < N ^ 3`.

## Main results

* `MvPolynomial.mul_card_le_of_forall_eval_iterate_pderiv_eq_zero`: the general bivariate jet
  multiplicity estimate
  `N * #P ≤ 2 * F.degreeOf 0 * F.degreeOf 1 + N * (F.degreeOf 0 + F.degreeOf 1)`.
* `MvPolynomial.card_conjugate_grid_eval_eq_zero_le`: Schwartz–Zippel bound on a conjugate grid
  `{(x + y θ, x - y θ) : x, y ∈ S}`.
* `MvPolynomial.eq_zero_of_forall_eval_iterate_pderiv_eq_zero_conjugate_grid`: vanishing criterion
  for a bivariate polynomial whose `X₀`-jets of order `< #S` vanish on a conjugate grid when
  `2 * d₀ * d₁ + #S * (d₀ + d₁) < #S ^ 3`.

## References

* [B. Green, *On Landau–Siegel zeros*][green2026], Proposition 3.1 and Appendix A.
-/

public section

open scoped Finset Matrix Polynomial Polynomial.Bivariate

namespace MvPolynomial

section Bridge

variable {R : Type*} [CommRing R]

/-- Equivalence `R[X₀, X₁] ≃ₐ[R] R[X][Y]` sending `X₀` to the outer variable `Y` and `X₁` to the
inner variable `C X`. -/
private noncomputable def toBivariateSwap (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] R[X][Y] :=
  (renameEquiv R (Equiv.swap (0 : Fin 2) 1)).trans (Polynomial.Bivariate.equivMvPolynomial R).symm

@[simp]
private theorem toBivariateSwap_X_zero :
    toBivariateSwap R (X 0) = Y := by
  simp [toBivariateSwap]

@[simp]
private theorem toBivariateSwap_X_one :
    toBivariateSwap R (X 1) = Polynomial.C Polynomial.X := by
  simp [toBivariateSwap]

@[simp]
private theorem toBivariateSwap_C (r : R) :
    toBivariateSwap R (C r) = Polynomial.C (Polynomial.C r) := by
  simp [toBivariateSwap]

private theorem toBivariateSwap_monomial (m : Fin 2 →₀ ℕ) (c : R) :
    toBivariateSwap R (monomial m c) =
      Polynomial.monomial (m 0) (Polynomial.monomial (m 1) c) := by
  have hm : monomial m c = C c * X 0 ^ m 0 * X 1 ^ m 1 := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    ring
  rw [hm, map_mul, map_mul, map_pow, map_pow, toBivariateSwap_C, toBivariateSwap_X_zero,
    toBivariateSwap_X_one, mul_right_comm, ← Polynomial.C_pow, ← Polynomial.C_mul,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_pow_eq_monomial]

private theorem eval_map_evalRingHom_toBivariateSwap (F : MvPolynomial (Fin 2) R) (x y : R) :
    ((toBivariateSwap R F).map (Polynomial.evalRingHom x)).eval y = eval ![y, x] F := by
  let φ : MvPolynomial (Fin 2) R →+* R :=
    (Polynomial.evalRingHom y).comp
      ((Polynomial.mapRingHom (Polynomial.evalRingHom x)).comp (toBivariateSwap R).toRingHom)
  change φ F = eval ![y, x] F
  congr 1
  refine ringHom_ext (fun r ↦ by simp [φ]) fun i ↦ ?_
  fin_cases i <;> simp [φ]

private theorem toBivariateSwap_pderiv_zero (F : MvPolynomial (Fin 2) R) :
    toBivariateSwap R (pderiv 0 F) = Polynomial.derivative (toBivariateSwap R F) := by
  apply (Polynomial.Bivariate.equivMvPolynomial R).injective
  rw [← Polynomial.Bivariate.pderiv_one_equivMvPolynomial]
  simp only [toBivariateSwap, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, renameEquiv_apply]
  exact (pderiv_rename (R := R) (Equiv.swap (0 : Fin 2) 1).injective 0 F).symm

private theorem toBivariateSwap_iterate_pderiv_zero (j : ℕ) (F : MvPolynomial (Fin 2) R) :
    toBivariateSwap R ((pderiv 0)^[j] F) = Polynomial.derivative^[j] (toBivariateSwap R F) := by
  induction j generalizing F with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', toBivariateSwap_pderiv_zero, ih]

private theorem natDegree_toBivariateSwap_le (F : MvPolynomial (Fin 2) R) :
    (toBivariateSwap R F).natDegree ≤ F.degreeOf 0 := by
  classical
  conv_lhs => rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [toBivariateSwap_monomial]
  exact (Polynomial.natDegree_monomial_le _).trans (monomial_le_degreeOf 0 hm)

private theorem natDegree_coeff_toBivariateSwap_le (F : MvPolynomial (Fin 2) R) (i : ℕ) :
    ((toBivariateSwap R F).coeff i).natDegree ≤ F.degreeOf 1 := by
  classical
  have hcoeff : (toBivariateSwap R F).coeff i =
      ∑ m ∈ F.support, (toBivariateSwap R (monomial m (F.coeff m))).coeff i := by
    conv_lhs => rw [F.as_sum, map_sum, ← Polynomial.lcoeff_apply, map_sum]
    rfl
  rw [hcoeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [toBivariateSwap_monomial, Polynomial.coeff_monomial, Finsupp.single_apply]
  split_ifs
  · exact (Polynomial.natDegree_monomial_le _).trans (monomial_le_degreeOf 1 hm)
  · simp

private theorem totalDegree_le_add_degreeOf (F : MvPolynomial (Fin 2) R) :
    F.totalDegree ≤ F.degreeOf 0 + F.degreeOf 1 := by
  refine Finset.sup_le fun m hm ↦ ?_
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  exact Nat.add_le_add (monomial_le_degreeOf 0 hm) (monomial_le_degreeOf 1 hm)

end Bridge

section MultiplicityBound

/-- Sum of root multiplicities of `q : R[X]` along a finite set of points with distinct second
coordinates is at most `q.natDegree`. -/
private theorem sum_rootMultiplicity_le_natDegree_of_injOn {R : Type*} [CommRing R] [IsDomain R]
    {P : Finset (R × R)} (hP : Set.InjOn Prod.snd (P : Set (R × R))) (q : R[X]) :
    ∑ p ∈ P, Polynomial.rootMultiplicity p.2 q ≤ q.natDegree := by
  classical
  rw [← Finset.sum_image (f := fun x ↦ Polynomial.rootMultiplicity x q) hP]
  simp_rw [← Polynomial.count_roots]
  calc
    ∑ x ∈ P.image Prod.snd, Multiset.count x q.roots
      = ∑ x ∈ P.image Prod.snd ∩ q.roots.toFinset, Multiset.count x q.roots := by
        refine (Finset.sum_subset Finset.inter_subset_left fun x hx hnot ↦ ?_).symm
        rw [Finset.mem_inter, not_and, Multiset.mem_toFinset] at hnot
        exact Multiset.count_eq_zero.mpr (hnot hx)
    _ ≤ ∑ x ∈ q.roots.toFinset, Multiset.count x q.roots :=
        Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = Multiset.card q.roots := q.roots.toFinset_sum_count_eq
    _ ≤ q.natDegree := q.card_roots'

/-- Fiber multiplicity of `F` in `X₀` at `(y, x)`, capped at `N` (and equal to `N` if the vertical
fiber vanishes identically). -/
private noncomputable def cappedFiberMult {R : Type*} [CommRing R] (N : ℕ) (y x : R)
    (F : MvPolynomial (Fin 2) R) : ℕ := by
  classical
  let q := (toBivariateSwap R F).map (Polynomial.evalRingHom x)
  exact if q = 0 then N else min N (Polynomial.rootMultiplicity y q)

private theorem cappedFiberMult_le {R : Type*} [CommRing R] (N : ℕ) (y x : R)
    (F : MvPolynomial (Fin 2) R) :
    cappedFiberMult N y x F ≤ N := by
  classical
  dsimp [cappedFiberMult]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem cappedFiberMult_mul_le {R : Type*} [CommRing R] [IsDomain R] (N : ℕ) (y x : R)
    (A B : MvPolynomial (Fin 2) R) :
    cappedFiberMult N y x (A * B) ≤ cappedFiberMult N y x A + cappedFiberMult N y x B := by
  classical
  let qA := (toBivariateSwap R A).map (Polynomial.evalRingHom x)
  let qB := (toBivariateSwap R B).map (Polynomial.evalRingHom x)
  by_cases hA : qA = 0
  · have hA_eq : cappedFiberMult N y x A = N := by simp [cappedFiberMult, qA, hA]
    linarith [cappedFiberMult_le N y x (A * B), Nat.zero_le (cappedFiberMult N y x B)]
  by_cases hB : qB = 0
  · have hB_eq : cappedFiberMult N y x B = N := by simp [cappedFiberMult, qB, hB]
    linarith [cappedFiberMult_le N y x (A * B), Nat.zero_le (cappedFiberMult N y x A)]
  have hAB : qA * qB ≠ 0 := mul_ne_zero hA hB
  have hAB_eq : cappedFiberMult N y x (A * B) =
      min N (Polynomial.rootMultiplicity y qA + Polynomial.rootMultiplicity y qB) := by
    have hrm := Polynomial.rootMultiplicity_mul hAB (x := y)
    simp [cappedFiberMult, qA, qB, hA, hB, hrm]
  have hA_eq : cappedFiberMult N y x A = min N (Polynomial.rootMultiplicity y qA) := by
    simp [cappedFiberMult, qA, hA]
  have hB_eq : cappedFiberMult N y x B = min N (Polynomial.rootMultiplicity y qB) := by
    simp [cappedFiberMult, qB, hB]
  omega

private theorem cappedFiberMult_eq_of_forall_eval_iterate_pderiv_eq_zero {R : Type*} [CommRing R]
    [IsDomain R] [CharZero R] {N : ℕ} {y x : R} {F : MvPolynomial (Fin 2) R}
    (hvan : ∀ j < N, eval ![y, x] ((pderiv 0)^[j] F) = 0) :
    cappedFiberMult N y x F = N := by
  classical
  let q : R[X] := (toBivariateSwap R F).map (Polynomial.evalRingHom x)
  by_cases hq : q = 0
  · simp [cappedFiberMult, q, hq]
  suffices N ≤ Polynomial.rootMultiplicity y q by
    simp [cappedFiberMult, q, hq, this]
  rw [Polynomial.le_rootMultiplicity_iff hq]
  -- Each iterated `X₀`-derivative corresponds to `j! * (q.taylor y).coeff j`.
  have hiter_map : ∀ j, ((Polynomial.derivative^[j] (toBivariateSwap R F)).map
      (Polynomial.evalRingHom x)) = Polynomial.derivative^[j] q := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ← Polynomial.derivative_map, ih]
  have htaylor : ∀ j < N, (q.taylor y).coeff j = 0 := by
    intro j hj
    have hj0 := hvan j hj
    rw [← eval_map_evalRingHom_toBivariateSwap, toBivariateSwap_iterate_pderiv_zero, hiter_map,
      ← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, Polynomial.eval_smul,
      ← Polynomial.taylor_coeff, nsmul_eq_mul] at hj0
    exact (mul_eq_zero.mp hj0).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
  have hdvd_t : Polynomial.X ^ N ∣ q.taylor y := Polynomial.X_pow_dvd_iff.mpr htaylor
  have hdvd_q := _root_.map_dvd (Polynomial.taylorAlgHom (-y)) hdvd_t
  simpa [Polynomial.taylor_taylor, sub_eq_add_neg] using hdvd_q

private theorem sum_cappedFiberMult_le_of_natDegree_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {N : ℕ} {P : Finset (R × R)} (hP : Set.InjOn Prod.snd (P : Set (R × R)))
    {G : MvPolynomial (Fin 2) R} (hG : G ≠ 0) (hdeg : (toBivariateSwap R G).natDegree = 0) :
    ∑ p ∈ P, cappedFiberMult N p.1 p.2 G ≤
      2 * G.degreeOf 0 * G.degreeOf 1 + N * (G.degreeOf 0 + G.degreeOf 1) := by
  classical
  let g : R[X][Y] := toBivariateSwap R G
  let c : R[X] := g.coeff 0
  have hgc : g = Polynomial.C c := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hc0 : c ≠ 0 := fun hc ↦ hG ((toBivariateSwap R).injective (by simp [g, hgc, hc]))
  have hle_pt : ∀ p ∈ P, cappedFiberMult N p.1 p.2 G ≤
      Polynomial.rootMultiplicity p.2 c * N := by
    intro p _
    by_cases hr : Polynomial.IsRoot c p.2
    · calc
        cappedFiberMult N p.1 p.2 G ≤ N := cappedFiberMult_le N p.1 p.2 G
        _ = 1 * N := (one_mul N).symm
        _ ≤ Polynomial.rootMultiplicity p.2 c * N :=
            Nat.mul_le_mul_right N ((Polynomial.rootMultiplicity_pos hc0).mpr hr)
    · have hmap : g.map (Polynomial.evalRingHom p.2) = Polynomial.C (c.eval p.2) := by simp [hgc]
      have hne : g.map (Polynomial.evalRingHom p.2) ≠ 0 := by
        rw [hmap, Ne, Polynomial.C_eq_zero]; exact hr
      have hrm : Polynomial.rootMultiplicity p.1 (g.map (Polynomial.evalRingHom p.2)) = 0 :=
        Polynomial.rootMultiplicity_eq_zero fun hroot ↦ hr (by simpa [hmap] using hroot)
      simp [cappedFiberMult, g, hne, hrm]
  calc
    ∑ p ∈ P, cappedFiberMult N p.1 p.2 G
      ≤ ∑ p ∈ P, Polynomial.rootMultiplicity p.2 c * N := Finset.sum_le_sum hle_pt
    _ = (∑ p ∈ P, Polynomial.rootMultiplicity p.2 c) * N := (Finset.sum_mul _ _ _).symm
    _ ≤ c.natDegree * N :=
        Nat.mul_le_mul_right N (sum_rootMultiplicity_le_natDegree_of_injOn hP c)
    _ ≤ G.degreeOf 1 * N :=
        Nat.mul_le_mul_right N (natDegree_coeff_toBivariateSwap_le G 0)
    _ ≤ 2 * G.degreeOf 0 * G.degreeOf 1 + N * (G.degreeOf 0 + G.degreeOf 1) := by nlinarith

private theorem sum_cappedFiberMult_le_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CharZero R] [DecidableEq R] {N : ℕ} {P : Finset (R × R)}
    (hP : Set.InjOn Prod.snd (P : Set (R × R)))
    (hSZ : ∀ H : MvPolynomial (Fin 2) R, H ≠ 0 →
      #{p ∈ P | eval ![p.1, p.2] H = 0} ≤ N * H.totalDegree)
    {G : MvPolynomial (Fin 2) R} (hG : Irreducible G) :
    ∑ p ∈ P, cappedFiberMult N p.1 p.2 G ≤
      2 * G.degreeOf 0 * G.degreeOf 1 + N * (G.degreeOf 0 + G.degreeOf 1) := by
  by_cases hdeg : (toBivariateSwap R G).natDegree = 0
  · exact sum_cappedFiberMult_le_of_natDegree_eq_zero hP hG.ne_zero hdeg
  · let g : R[X][Y] := toBivariateSwap R G
    have hg_irr : Irreducible g := hG.map (toBivariateSwap R)
    have hdeg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hdeg
    let res : R[X] := Polynomial.resultant g g.derivative
    have hpt : ∀ p ∈ P, cappedFiberMult N p.1 p.2 G ≤
        (if eval ![p.1, p.2] G = 0 then 1 else 0) + Polynomial.rootMultiplicity p.2 res := by
      intro p _
      have hne := Polynomial.map_evalRingHom_ne_zero_of_irreducible hg_irr hdeg_pos p.2
      by_cases hev : eval ![p.1, p.2] G = 0
      · simp only [cappedFiberMult, g, hne, ↓reduceIte, hev]
        exact (min_le_right _ _).trans
          (Polynomial.rootMultiplicity_map_evalRingHom_le_of_irreducible hg_irr hdeg_pos p.2 p.1)
      · have hrm : Polynomial.rootMultiplicity p.1 (g.map (Polynomial.evalRingHom p.2)) = 0 := by
          refine Polynomial.rootMultiplicity_eq_zero fun hr ↦ hev ?_
          rwa [← eval_map_evalRingHom_toBivariateSwap]
        simp [cappedFiberMult, g, hne, hev, hrm]
    calc
      ∑ p ∈ P, cappedFiberMult N p.1 p.2 G
        ≤ ∑ p ∈ P, ((if eval ![p.1, p.2] G = 0 then 1 else 0) +
            Polynomial.rootMultiplicity p.2 res) := Finset.sum_le_sum hpt
      _ = #{p ∈ P | eval ![p.1, p.2] G = 0} + ∑ p ∈ P, Polynomial.rootMultiplicity p.2 res := by
          rw [Finset.sum_add_distrib, Finset.sum_boole]; simp
      _ ≤ N * G.totalDegree + res.natDegree :=
          Nat.add_le_add (hSZ G hG.ne_zero) (sum_rootMultiplicity_le_natDegree_of_injOn hP res)
      _ ≤ N * (G.degreeOf 0 + G.degreeOf 1) + 2 * G.degreeOf 0 * G.degreeOf 1 := by
          refine Nat.add_le_add (Nat.mul_le_mul_left N (totalDegree_le_add_degreeOf G)) ?_
          exact (Polynomial.natDegree_resultant_derivative_le
            (natDegree_coeff_toBivariateSwap_le G)).trans
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (natDegree_toBivariateSwap_le G)))
      _ = 2 * G.degreeOf 0 * G.degreeOf 1 + N * (G.degreeOf 0 + G.degreeOf 1) := add_comm _ _

/-- **Bivariate jet multiplicity bound.** Over a characteristic-zero UFD `R`, let `P` be a finite
set of points in `R × R` with pairwise distinct second coordinates such that every nonzero
`H : MvPolynomial (Fin 2) R` vanishes at no more than `N * H.totalDegree` points of `P`. If a
nonzero polynomial `F : MvPolynomial (Fin 2) R` satisfies `((pderiv 0)^[j] F)(p.1, p.2) = 0` for all
`p ∈ P` and `j < N`, then
`N * #P ≤ 2 * F.degreeOf 0 * F.degreeOf 1 + N * (F.degreeOf 0 + F.degreeOf 1)`. -/
theorem mul_card_le_of_forall_eval_iterate_pderiv_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CharZero R] [DecidableEq R] {N : ℕ} {P : Finset (R × R)}
    (hP : Set.InjOn Prod.snd (P : Set (R × R)))
    (hSZ : ∀ H : MvPolynomial (Fin 2) R, H ≠ 0 →
      #{p ∈ P | eval ![p.1, p.2] H = 0} ≤ N * H.totalDegree)
    {F : MvPolynomial (Fin 2) R} (hF : F ≠ 0)
    (hvan : ∀ p ∈ P, ∀ j < N, eval ![p.1, p.2] ((pderiv 0)^[j] F) = 0) :
    N * #P ≤ 2 * F.degreeOf 0 * F.degreeOf 1 + N * (F.degreeOf 0 + F.degreeOf 1) := by
  -- Induct on the irreducible factorization of `F` for the capped multiplicity sum.
  have hsum : ∀ Q : MvPolynomial (Fin 2) R, Q ≠ 0 →
      ∑ p ∈ P, cappedFiberMult N p.1 p.2 Q ≤
        2 * Q.degreeOf 0 * Q.degreeOf 1 + N * (Q.degreeOf 0 + Q.degreeOf 1) := by
    intro Q hQ
    induction Q using WfDvdMonoid.induction_on_irreducible with
    | zero => exact absurd rfl hQ
    | unit Q hu =>
      have h0 : ∀ p ∈ P, cappedFiberMult N p.1 p.2 Q = 0 := by
        intro p _
        have hu_ev : IsUnit (eval ![p.1, p.2] Q) := hu.map (eval ![p.1, p.2])
        have hne_ev : eval ![p.1, p.2] Q ≠ 0 := hu_ev.ne_zero
        have hne_fib : (toBivariateSwap R Q).map (Polynomial.evalRingHom p.2) ≠ 0 := fun h ↦
          hne_ev (by rw [← eval_map_evalRingHom_toBivariateSwap, h, Polynomial.eval_zero])
        have hrm : Polynomial.rootMultiplicity p.1
            ((toBivariateSwap R Q).map (Polynomial.evalRingHom p.2)) = 0 :=
          Polynomial.rootMultiplicity_eq_zero fun hr ↦
            hne_ev (by rwa [← eval_map_evalRingHom_toBivariateSwap])
        simp [cappedFiberMult, hne_fib, hrm]
      simp [Finset.sum_eq_zero h0]
    | mul B A hB hA ihB =>
      have hA0 : A ≠ 0 := hA.ne_zero
      calc
        ∑ p ∈ P, cappedFiberMult N p.1 p.2 (A * B)
          ≤ ∑ p ∈ P, (cappedFiberMult N p.1 p.2 A + cappedFiberMult N p.1 p.2 B) :=
            Finset.sum_le_sum fun p _ ↦ cappedFiberMult_mul_le N p.1 p.2 A B
        _ = (∑ p ∈ P, cappedFiberMult N p.1 p.2 A) + ∑ p ∈ P, cappedFiberMult N p.1 p.2 B :=
            Finset.sum_add_distrib
        _ ≤ (2 * A.degreeOf 0 * A.degreeOf 1 + N * (A.degreeOf 0 + A.degreeOf 1)) +
            (2 * B.degreeOf 0 * B.degreeOf 1 + N * (B.degreeOf 0 + B.degreeOf 1)) :=
            Nat.add_le_add (sum_cappedFiberMult_le_of_irreducible hP hSZ hA) (ihB hB)
        _ ≤ 2 * (A * B).degreeOf 0 * (A * B).degreeOf 1 +
            N * ((A * B).degreeOf 0 + (A * B).degreeOf 1) := by
            rw [degreeOf_mul_eq hA0 hB, degreeOf_mul_eq hA0 hB]
            nlinarith
  have hF_sum : ∑ p ∈ P, cappedFiberMult N p.1 p.2 F = N * #P := by
    rw [Finset.sum_congr rfl fun p hp ↦
      cappedFiberMult_eq_of_forall_eval_iterate_pderiv_eq_zero (hvan p hp),
      Finset.sum_const, smul_eq_mul, mul_comm]
  exact hF_sum ▸ hsum F hF

end MultiplicityBound

section ConjugateGrid

private theorem linearSubst_conjugate_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {θ : R} (hθ : θ ≠ 0) {H : MvPolynomial (Fin 2) R} (hH : H ≠ 0) :
    linearSubst !![(1 : R), θ; 1, -θ] H ≠ 0 := by
  let M : Matrix (Fin 2) (Fin 2) R := !![1, θ; 1, -θ]
  let M' : Matrix (Fin 2) (Fin 2) R := !![θ, θ; 1, -1]
  have h2θ : (2 : R) * θ ≠ 0 := mul_ne_zero two_ne_zero hθ
  have hMM' : M * M' = Matrix.diagonal (fun _ ↦ (2 : R) * θ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M, M'] <;> ring
  intro hzero
  obtain ⟨m, hm⟩ := support_nonempty.mpr hH
  have hres : rescale (fun _ : Fin 2 ↦ (2 : R) * θ) H = 0 := by
    rw [← linearSubst_diagonal, ← hMM', linearSubst_mul_apply, hzero, map_zero]
  have hc : (rescale (fun _ : Fin 2 ↦ (2 : R) * θ) H).coeff m = 0 := by rw [hres]; rfl
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, mul_eq_zero,
    mul_eq_zero] at hc
  rcases hc with (hc | hc) | hc
  · exact pow_ne_zero _ h2θ hc
  · exact pow_ne_zero _ h2θ hc
  · exact mem_support_iff.mp hm hc

/-- **Schwartz–Zippel on a conjugate grid.** Over a characteristic-zero domain `R`, for `θ ≠ 0` and
any finite subset `S ⊆ R`, a nonzero bivariate polynomial `H : MvPolynomial (Fin 2) R` vanishes at
no more than `#S * H.totalDegree` pairs `(s₁, s₂) ∈ S ×ˢ S` along `(s₁ + s₂ * θ, s₁ - s₂ * θ)`. -/
theorem card_conjugate_grid_eval_eq_zero_le {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [DecidableEq R] {θ : R} (hθ : θ ≠ 0) (S : Finset R) {H : MvPolynomial (Fin 2) R}
    (hH : H ≠ 0) :
    #{q ∈ S ×ˢ S | eval ![q.1 + q.2 * θ, q.1 - q.2 * θ] H = 0} ≤ #S * H.totalDegree := by
  obtain rfl | hSne := S.eq_empty_or_nonempty
  · simp
  let M : Matrix (Fin 2) (Fin 2) R := !![1, θ; 1, -θ]
  let H' : MvPolynomial (Fin 2) R := linearSubst M H
  have hH' : H' ≠ 0 := linearSubst_conjugate_ne_zero hθ hH
  have hdeg : H'.totalDegree ≤ H.totalDegree := by
    have hlin : ∀ i : Fin 2, (∑ j : Fin 2, C (M i j) * X j).totalDegree ≤ 1 := fun i ↦
      (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦
        (totalDegree_mul _ _).trans (by simp))
    simpa [H', linearSubst_eq_aeval] using totalDegree_bind₁_le hlin H
  have hcard_eq : #{q ∈ S ×ˢ S | eval ![q.1 + q.2 * θ, q.1 - q.2 * θ] H = 0} =
      #{f ∈ Fintype.piFinset (fun _ : Fin 2 ↦ S) | eval f H' = 0} := by
    refine Finset.card_bij (fun q _ ↦ ![q.1, q.2]) ?_ ?_ ?_
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqS, hq0⟩
      rcases Finset.mem_product.mp hqS with ⟨hq1, hq2⟩
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ by fin_cases i <;> assumption,
        ?_⟩
      have hvec : M *ᵥ ![q.1, q.2] = ![q.1 + q.2 * θ, q.1 - q.2 * θ] := by
        ext i; fin_cases i <;> simp [M, Matrix.mulVec, dotProduct] <;> ring
      rwa [eval_linearSubst, hvec]
    · exact fun _ _ _ _ h ↦ Prod.ext (congr_fun h 0) (congr_fun h 1)
    · intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfS, hf0⟩
      refine ⟨(f 0, f 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mp hfS 0, Fintype.mem_piFinset.mp hfS 1⟩, ?_⟩, ?_⟩
      · have hvec : M *ᵥ f = ![f 0 + f 1 * θ, f 0 - f 1 * θ] := by
          ext i; fin_cases i <;> simp [M, Matrix.mulVec, dotProduct] <;> ring
        rwa [eval_linearSubst, hvec] at hf0
      · ext i; fin_cases i <;> rfl
  have hsz := schwartz_zippel_totalDegree hH' S
  have hSposQ : (0 : NNRat) < (#S : NNRat) := by exact_mod_cast hSne.card_pos
  have hmul : (#{f ∈ Fintype.piFinset (fun _ : Fin 2 ↦ S) | eval f H' = 0} : NNRat) ≤
      (#S : NNRat) * H'.totalDegree := by
    have h1 := (div_le_iff₀ (pow_pos hSposQ 2)).mp hsz
    have h2 : (H'.totalDegree : NNRat) / #S * (#S : NNRat) ^ 2 = (#S : NNRat) * H'.totalDegree := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hSposQ.ne', mul_comm]
    rwa [h2] at h1
  exact (hcard_eq.trans_le (by exact_mod_cast hmul)).trans (Nat.mul_le_mul_left #S hdeg)

/-- **Vanishing criterion on a conjugate grid.** Let `R` be a characteristic-zero UFD and `θ ∈ R` be
`ℤ`-linearly independent from `1` (`∀ a b : ℤ, (a : R) + (b : R) * θ = 0 → a = 0 ∧ b = 0`). For any
finite set of integers `S`, if `F : MvPolynomial (Fin 2) R` satisfies
`((pderiv 0)^[j] F)(x + y θ, x - y θ) = 0` for all `x, y ∈ S` and `j < #S`, and
`2 * F.degreeOf 0 * F.degreeOf 1 + #S * (F.degreeOf 0 + F.degreeOf 1) < #S ^ 3`, then `F = 0`. -/
theorem eq_zero_of_forall_eval_iterate_pderiv_eq_zero_conjugate_grid {R : Type*} [CommRing R]
    [IsDomain R] [UniqueFactorizationMonoid R] [CharZero R] {θ : R}
    (hθ : ∀ a b : ℤ, (a : R) + (b : R) * θ = 0 → a = 0 ∧ b = 0)
    (S : Finset ℤ) {F : MvPolynomial (Fin 2) R}
    (hdeg : 2 * F.degreeOf 0 * F.degreeOf 1 + #S * (F.degreeOf 0 + F.degreeOf 1) < #S ^ 3)
    (hvan : ∀ x ∈ S, ∀ y ∈ S, ∀ j < #S,
      eval ![(x : R) + (y : R) * θ, (x : R) - (y : R) * θ] ((pderiv 0)^[j] F) = 0) :
    F = 0 := by
  classical
  by_contra hF
  have hθ_ne : θ ≠ 0 := fun h0 ↦ by
    have := (hθ 0 1 (by simp [h0])).2
    omega
  let φ : ℤ × ℤ → R × R := fun q ↦ ((q.1 : R) + (q.2 : R) * θ, (q.1 : R) - (q.2 : R) * θ)
  have hφ_snd_inj : Function.Injective (fun q : ℤ × ℤ ↦ (φ q).2) := by
    intro q₁ q₂ h
    have hrel : ((q₁.1 - q₂.1 : ℤ) : R) + ((q₂.2 - q₁.2 : ℤ) : R) * θ = 0 := by
      dsimp [φ] at h
      push_cast
      linear_combination h
    obtain ⟨h1, h2⟩ := hθ _ _ hrel
    exact Prod.ext (by omega) (by omega)
  have hφ_inj : Function.Injective φ := fun q₁ q₂ h ↦ hφ_snd_inj (congr_arg Prod.snd h)
  let P : Finset (R × R) := (S ×ˢ S).image φ
  have hP_card : #P = #S ^ 2 := by
    rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_product, sq]
  have hP_snd : Set.InjOn Prod.snd (P : Set (R × R)) := by
    intro p₁ hp₁ p₂ hp₂ hsnd
    rcases Finset.mem_image.mp hp₁ with ⟨q₁, _, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨q₂, _, rfl⟩
    rw [hφ_snd_inj hsnd]
  let SR : Finset R := S.image Int.cast
  have hSR_card : #SR = #S := Finset.card_image_of_injective _ Int.cast_injective
  have hSZ : ∀ H : MvPolynomial (Fin 2) R, H ≠ 0 →
      #{p ∈ P | eval ![p.1, p.2] H = 0} ≤ #S * H.totalDegree := by
    intro H hH
    have hsub : P ⊆ (SR ×ˢ SR).image (fun q : R × R ↦ (q.1 + q.2 * θ, q.1 - q.2 * θ)) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
      exact Finset.mem_image.mpr ⟨((q.1 : R), (q.2 : R)),
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq1, Finset.mem_image_of_mem _ hq2⟩, rfl⟩
    calc
      #{p ∈ P | eval ![p.1, p.2] H = 0}
        ≤ #{p ∈ (SR ×ˢ SR).image (fun q : R × R ↦ (q.1 + q.2 * θ, q.1 - q.2 * θ)) |
            eval ![p.1, p.2] H = 0} := Finset.card_le_card (Finset.filter_subset_filter _ hsub)
      _ ≤ #{q ∈ SR ×ˢ SR | eval ![q.1 + q.2 * θ, q.1 - q.2 * θ] H = 0} := by
          rw [Finset.filter_image]
          exact Finset.card_image_le
      _ ≤ #SR * H.totalDegree := card_conjugate_grid_eval_eq_zero_le hθ_ne SR hH
      _ = #S * H.totalDegree := by rw [hSR_card]
  have hvanP : ∀ p ∈ P, ∀ j < #S, eval ![p.1, p.2] ((pderiv 0)^[j] F) = 0 := by
    intro p hp j hj
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
    exact hvan q.1 hq1 q.2 hq2 j hj
  have hle := mul_card_le_of_forall_eval_iterate_pderiv_eq_zero hP_snd hSZ hF hvanP
  rw [hP_card, ← pow_succ'] at hle
  exact not_lt_of_ge hle hdeg

end ConjugateGrid

end MvPolynomial
