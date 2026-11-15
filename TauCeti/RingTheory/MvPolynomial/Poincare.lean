/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# The polynomial Poincaré lemma in degree one

Over a commutative `ℚ`-algebra semiring `R` and a finite variable type `σ`, a family
`P : σ → MvPolynomial σ R` is the formal gradient `i ↦ pderiv i Q` of a polynomial `Q` if and only
if its mixed partial derivatives agree, `pderiv j (P i) = pderiv i (P j)`. When every `P i` has
total degree at most `m`, `Q` may be chosen of total degree at most `m + 1`; over a commutative
`ℚ`-algebra ring, prescribing `constantCoeff Q` makes `Q` unique.

The construction decomposes `P` into homogeneous components. Partial differentiation shifts
homogeneous components by one degree (`MvPolynomial.homogeneousComponent_pderiv`), so closedness
passes to each homogeneous piece. When every `P i` is homogeneous of degree `d` and closed,
differentiating `∑ i, X i * P i` along `X j` gives `P j + ∑ i, X i * pderiv i (P j) = (d + 1) • P j`
by Euler's homogeneous identity (`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`), and dividing by
`d + 1` produces a homogeneous potential of degree `d + 1`. Uniqueness up to constants holds over
any commutative ring with `HasUniqueDiv` (`MvPolynomial.pderiv.ext`), inherited from
`MvPowerSeries.pderiv.ext`.

## Main results

* `MvPolynomial.homogeneousComponent_pderiv`: taking the degree-`d` homogeneous component after
  `pderiv i` is `pderiv i` of the degree-`(d + 1)` homogeneous component.
* `MvPolynomial.pderiv.ext`: over a commutative ring with `HasUniqueDiv`, a polynomial is
  determined by its formal partial derivatives and its constant coefficient.
* `MvPolynomial.forall_pderiv_eq_zero_iff`: all formal partial derivatives of `φ` vanish if and
  only if `φ` is constant.
* `MvPolynomial.pderiv_sum_X_mul_of_isHomogeneous`: for a closed family of degree-`d` homogeneous
  polynomials, `pderiv j (∑ i, X i * P i) = (d + 1) • P j`.
* `MvPolynomial.exists_isHomogeneous_pderiv_eq`: homogeneous polynomial Poincaré lemma.
* `MvPolynomial.exists_mem_restrictTotalDegree_pderiv_eq`: bounded-degree polynomial Poincaré
  lemma.
* `MvPolynomial.existsUnique_mem_restrictTotalDegree_pderiv_eq`: unique bounded-degree potential
  with prescribed constant coefficient.
* `MvPolynomial.exists_pderiv_eq_iff`: exactness characterization for polynomial one-forms.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer (1982), §4.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.3.
-/

public section

namespace MvPolynomial

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

/-- The degree-`d` homogeneous component of `pderiv i φ` is `pderiv i` of the degree-`(d + 1)`
homogeneous component of `φ`. -/
theorem homogeneousComponent_pderiv (d : ℕ) (i : σ) (φ : MvPolynomial σ R) :
    homogeneousComponent d (pderiv i φ) = pderiv i (homogeneousComponent (d + 1) φ) := by
  ext m
  have hdeg : (m + Finsupp.single i 1).degree = m.degree + 1 := by simp
  rw [coeff_homogeneousComponent, coeff_pderiv, coeff_pderiv, coeff_homogeneousComponent, hdeg]
  split_ifs <;> simp_all

/-- If `pderiv j φ = pderiv i ψ`, then the same compatibility holds between their degree-`d`
homogeneous components for every `d`. -/
theorem pderiv_homogeneousComponent_eq_of_pderiv_eq {i j : σ} {φ ψ : MvPolynomial σ R}
    (h : pderiv j φ = pderiv i ψ) (d : ℕ) :
    pderiv j (homogeneousComponent d φ) = pderiv i (homogeneousComponent d ψ) := by
  cases d with
  | zero => simp
  | succ d => rw [← homogeneousComponent_pderiv, ← homogeneousComponent_pderiv, h]

/-- **Euler's radial primitive identity.** If `P : σ → MvPolynomial σ R` is a closed family of
homogeneous polynomials of degree `d`, then `pderiv j (∑ i, X i * P i) = (d + 1) • P j`. -/
theorem pderiv_sum_X_mul_of_isHomogeneous [Fintype σ] {d : ℕ} {P : σ → MvPolynomial σ R}
    (hP : ∀ i, (P i).IsHomogeneous d) (hclosed : ∀ i j, pderiv j (P i) = pderiv i (P j))
    (j : σ) :
    pderiv j (∑ i, X i * P i) = (d + 1) • P j := by
  classical
  calc pderiv j (∑ i, X i * P i)
      = ∑ i, (pderiv j (X i) * P i + X i * pderiv j (P i)) := by
          simp only [map_sum, pderiv_mul]
    _ = ∑ i, pderiv j (X i) * P i + ∑ i, X i * pderiv i (P j) := by
          rw [Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hclosed i j]
    _ = P j + d • P j := by
          rw [(hP j).sum_X_mul_pderiv]
          simp [pderiv_X, Pi.single_apply]
    _ = (d + 1) • P j := (succ_nsmul' (P j) d).symm

end CommSemiring

section UniqueDiv

variable {σ R : Type*} [CommRing R] [HasUniqueDiv R]

/-- Over a commutative ring with `HasUniqueDiv`, a multivariate polynomial is uniquely determined
by its formal partial derivatives and its constant coefficient. -/
theorem pderiv.ext {φ ψ : MvPolynomial σ R}
    (hD : ∀ i, pderiv i φ = pderiv i ψ) (hc : constantCoeff φ = constantCoeff ψ) :
    φ = ψ := by
  apply coe_injective σ R
  apply MvPowerSeries.pderiv.ext
  · intro i
    rw [MvPowerSeries.pderiv_coe, MvPowerSeries.pderiv_coe, hD i]
  · simpa only [← MvPowerSeries.coeff_zero_eq_constantCoeff, coeff_coe,
      ← constantCoeff_eq] using hc

/-- If all formal partial derivatives of `φ` vanish, then `φ` equals its constant term. -/
theorem eq_C_constantCoeff_of_forall_pderiv_eq_zero {φ : MvPolynomial σ R}
    (hφ : ∀ i, pderiv i φ = 0) :
    φ = C (constantCoeff φ) :=
  pderiv.ext (fun i ↦ by rw [hφ i, pderiv_C]) (by simp)

/-- Over a commutative ring with `HasUniqueDiv`, all formal partial derivatives of `φ` vanish if
and only if `φ` is constant. -/
theorem forall_pderiv_eq_zero_iff {φ : MvPolynomial σ R} :
    (∀ i, pderiv i φ = 0) ↔ ∃ c : R, φ = C c :=
  ⟨fun h ↦ ⟨constantCoeff φ, eq_C_constantCoeff_of_forall_pderiv_eq_zero h⟩,
    fun ⟨_, hc⟩ _ ↦ hc ▸ pderiv_C⟩

/-- Two polynomials with the same formal partial derivatives differ by the constant given by the
difference of their constant coefficients. -/
theorem sub_eq_C_of_forall_pderiv_eq {φ ψ : MvPolynomial σ R}
    (hD : ∀ i, pderiv i φ = pderiv i ψ) :
    φ - ψ = C (constantCoeff φ - constantCoeff ψ) := by
  simpa only [map_sub] using
    eq_C_constantCoeff_of_forall_pderiv_eq_zero (φ := φ - ψ) fun i ↦ by simp [hD i]

end UniqueDiv

section AlgebraRatSemiring

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- **Homogeneous polynomial Poincaré lemma.** Over a commutative `ℚ`-algebra semiring and finitely
many variables, a closed family of degree-`d` homogeneous polynomials is the formal gradient of a
homogeneous polynomial of degree `d + 1`. -/
theorem exists_isHomogeneous_pderiv_eq [Finite σ] {d : ℕ} {P : σ → MvPolynomial σ R}
    (hP : ∀ i, (P i).IsHomogeneous d) (hclosed : ∀ i j, pderiv j (P i) = pderiv i (P j)) :
    ∃ Q : MvPolynomial σ R, Q.IsHomogeneous (d + 1) ∧ ∀ i, pderiv i Q = P i := by
  let := Fintype.ofFinite σ
  set c : R := algebraMap ℚ R (d + 1 : ℚ)⁻¹
  refine ⟨c • ∑ i, X i * P i, ?_, fun j ↦ ?_⟩
  · refine (homogeneousSubmodule σ R (d + 1)).smul_mem c ?_
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [mem_homogeneousSubmodule]
    simpa only [add_comm 1 d] using (isHomogeneous_X R i).mul (hP i)
  · have hcancel : c * (d + 1 : R) = 1 := by
      have hne : (d + 1 : ℚ) ≠ 0 := by positivity
      calc c * (d + 1 : R)
          = algebraMap ℚ R ((d + 1 : ℚ)⁻¹ * (d + 1 : ℚ)) := by simp [c]
        _ = 1 := by rw [inv_mul_cancel₀ hne, map_one]
    rw [(pderiv j).map_smul, pderiv_sum_X_mul_of_isHomogeneous hP hclosed j,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, Nat.cast_add, Nat.cast_one, hcancel, one_smul]

/-- **Bounded-degree polynomial Poincaré lemma.** Over a commutative `ℚ`-algebra semiring and
finitely many variables, if every `P i` has total degree at most `m` and
`pderiv j (P i) = pderiv i (P j)` for all `i` and `j`, then there exists `Q` of total degree at most
`m + 1` with `pderiv i Q = P i` for every `i`. -/
theorem exists_mem_restrictTotalDegree_pderiv_eq [Finite σ] {m : ℕ} {P : σ → MvPolynomial σ R}
    (hP : ∀ i, P i ∈ restrictTotalDegree σ R m)
    (hclosed : ∀ i j, pderiv j (P i) = pderiv i (P j)) :
    ∃ Q ∈ restrictTotalDegree σ R (m + 1), ∀ i, pderiv i Q = P i := by
  have hcomp (d : ℕ) : ∃ Q : MvPolynomial σ R,
      Q.IsHomogeneous (d + 1) ∧ ∀ i, pderiv i Q = homogeneousComponent d (P i) :=
    exists_isHomogeneous_pderiv_eq (fun i ↦ homogeneousComponent_isHomogeneous d (P i))
      (fun i j ↦ pderiv_homogeneousComponent_eq_of_pderiv_eq (hclosed i j) d)
  choose Q hQhom hQpderiv using hcomp
  refine ⟨∑ d ∈ Finset.range (m + 1), Q d, ?_, fun i ↦ ?_⟩
  · refine Submodule.sum_mem _ fun d hd ↦ ?_
    have hdle : d + 1 ≤ m + 1 := Nat.succ_le_succ (Finset.mem_range_succ_iff.mp hd)
    exact homogeneousSubmodule_le_restrictTotalDegree σ R hdle (hQhom d)
  · rw [map_sum]
    simp_rw [hQpderiv]
    have hdeg : (P i).totalDegree ≤ m := (mem_restrictTotalDegree σ m (P i)).mp (hP i)
    calc ∑ d ∈ Finset.range (m + 1), homogeneousComponent d (P i)
        = ∑ d ∈ Finset.range ((P i).totalDegree + 1), homogeneousComponent d (P i) := by
            refine (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdeg)) ?_).symm
            intro d _ hd
            exact homogeneousComponent_eq_zero d (P i) (by simp at hd; omega)
      _ = P i := sum_homogeneousComponent (P i)

/-- **Exactness of polynomial one-forms.** Over a commutative `ℚ`-algebra semiring and finitely many
variables, a family `P : σ → MvPolynomial σ R` is the formal gradient of a polynomial if and only
if `pderiv j (P i) = pderiv i (P j)` for all `i` and `j`. -/
theorem exists_pderiv_eq_iff [Finite σ] (P : σ → MvPolynomial σ R) :
    (∃ Q : MvPolynomial σ R, ∀ i, pderiv i Q = P i) ↔
      ∀ i j, pderiv j (P i) = pderiv i (P j) := by
  constructor
  · rintro ⟨Q, hQ⟩ i j
    rw [← hQ i, ← hQ j, pderiv_comm]
  · intro hclosed
    let := Fintype.ofFinite σ
    set m := Finset.univ.sup fun i ↦ (P i).totalDegree
    have hP : ∀ i, P i ∈ restrictTotalDegree σ R m := fun i ↦
      (mem_restrictTotalDegree σ m (P i)).mpr (Finset.le_sup (f := fun i ↦ (P i).totalDegree)
        (Finset.mem_univ i))
    obtain ⟨Q, -, hQ⟩ := exists_mem_restrictTotalDegree_pderiv_eq hP hclosed
    exact ⟨Q, hQ⟩

end AlgebraRatSemiring

section AlgebraRatRing

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

/-- A closed family of polynomials of total degree at most `m` admits a unique potential of total
degree at most `m + 1` with any prescribed constant coefficient. -/
theorem existsUnique_mem_restrictTotalDegree_pderiv_eq [Finite σ] {m : ℕ}
    {P : σ → MvPolynomial σ R} (hP : ∀ i, P i ∈ restrictTotalDegree σ R m)
    (hclosed : ∀ i j, pderiv j (P i) = pderiv i (P j)) (c : R) :
    ∃! Q : MvPolynomial σ R,
      Q ∈ restrictTotalDegree σ R (m + 1) ∧ (∀ i, pderiv i Q = P i) ∧ constantCoeff Q = c := by
  have : HasUniqueDiv R := .of_module_rat R
  obtain ⟨Q₀, hQ₀deg, hQ₀⟩ := exists_mem_restrictTotalDegree_pderiv_eq hP hclosed
  set Q := Q₀ + C (c - constantCoeff Q₀)
  have hQdeg : Q ∈ restrictTotalDegree σ R (m + 1) := by
    refine Submodule.add_mem _ hQ₀deg ?_
    rw [mem_restrictTotalDegree, totalDegree_C]
    exact Nat.zero_le _
  have hQp : ∀ i, pderiv i Q = P i := fun i ↦ by simp [Q, hQ₀ i]
  have hQc : constantCoeff Q = c := by simp [Q]
  refine ⟨Q, ⟨hQdeg, hQp, hQc⟩, ?_⟩
  rintro Q' ⟨-, hQ'p, hQ'c⟩
  exact pderiv.ext (fun i ↦ (hQ'p i).trans (hQp i).symm) (hQ'c.trans hQc.symm)

/-- Over a commutative `ℚ`-algebra ring and finitely many variables, every closed polynomial family
has a unique polynomial potential with any prescribed constant coefficient. -/
theorem existsUnique_pderiv_eq [Finite σ] {P : σ → MvPolynomial σ R}
    (hclosed : ∀ i j, pderiv j (P i) = pderiv i (P j)) (c : R) :
    ∃! Q : MvPolynomial σ R, (∀ i, pderiv i Q = P i) ∧ constantCoeff Q = c := by
  have : HasUniqueDiv R := .of_module_rat R
  obtain ⟨Q₀, hQ₀⟩ := (exists_pderiv_eq_iff P).mpr hclosed
  set Q := Q₀ + C (c - constantCoeff Q₀)
  have hQp : ∀ i, pderiv i Q = P i := fun i ↦ by simp [Q, hQ₀ i]
  have hQc : constantCoeff Q = c := by simp [Q]
  exact ⟨Q, ⟨hQp, hQc⟩, fun Q' ⟨hQ'p, hQ'c⟩ ↦
    pderiv.ext (fun i ↦ (hQ'p i).trans (hQp i).symm) (hQ'c.trans hQc.symm)⟩

end AlgebraRatRing

-- Sanity checks:
-- (1) In two variables, `(X 1, X 0)` is closed with potential `X 0 * X 1` of degree `≤ 2`.
-- (2) `(-X 1, X 0)` is not closed and has no polynomial potential over `ℚ`.
-- (3) In one variable at degree `0`, `P = 3` gives the unique constant-free potential `3 * X 0`.
-- (4) In zero variables, the empty family has unique constant-prescribed potential `C c`.
-- (5) `[Finite σ]` is sharp: over `σ = ℕ`, `P _ = 1` is closed of degree `0` with no potential.
example :
    let P : Fin 2 → MvPolynomial (Fin 2) ℚ := ![X 1, X 0]
    (∀ i, pderiv i (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) = P i) ∧
      (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ∈ restrictTotalDegree (Fin 2) ℚ 2 := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i <;> simp
  · rw [mem_restrictTotalDegree]
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])

example :
    ¬ ∃ Q : MvPolynomial (Fin 2) ℚ, ∀ i, pderiv i Q = (![-X 1, X 0] : Fin 2 → _) i := by
  rw [exists_pderiv_eq_iff]
  intro h
  have h01 := congrArg constantCoeff (h 0 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_neg,
    pderiv_X_self, map_one] at h01
  norm_num at h01

example :
    ∃! Q : MvPolynomial (Fin 1) ℚ,
      Q ∈ restrictTotalDegree (Fin 1) ℚ 1 ∧ (∀ i, pderiv i Q = C 3) ∧ constantCoeff Q = 0 :=
  existsUnique_mem_restrictTotalDegree_pderiv_eq
    (fun _ ↦ by rw [mem_restrictTotalDegree, totalDegree_C])
    (fun i j ↦ by fin_cases i; fin_cases j; rfl) 0

example (c : ℚ) :
    ∃! Q : MvPolynomial (Fin 0) ℚ,
      Q ∈ restrictTotalDegree (Fin 0) ℚ 1 ∧ (∀ i : Fin 0, pderiv i Q = 0) ∧ constantCoeff Q = c :=
  existsUnique_mem_restrictTotalDegree_pderiv_eq (fun i ↦ i.elim0) (fun i ↦ i.elim0) c

example :
    (∀ i j : ℕ, pderiv j (1 : MvPolynomial ℕ ℚ) = pderiv i (1 : MvPolynomial ℕ ℚ)) ∧
      ¬ ∃ Q : MvPolynomial ℕ ℚ, ∀ i : ℕ, pderiv i Q = 1 := by
  refine ⟨fun _ _ ↦ by simp, ?_⟩
  rintro ⟨Q, hQ⟩
  set n : ℕ := Q.vars.sup id + 1
  have hn : n ∉ Q.vars := fun hmem ↦
    Nat.lt_irrefl _ (Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem))
  have hzero : pderiv n Q = 0 := pderiv_eq_zero_of_notMem_vars hn
  have hone : pderiv n Q = 1 := hQ n
  exact one_ne_zero (hone.symm.trans hzero)

end MvPolynomial
