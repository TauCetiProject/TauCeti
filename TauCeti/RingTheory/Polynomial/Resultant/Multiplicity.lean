/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.Polynomial.Bivariate
import TauCeti.Algebra.Polynomial.Bivariate.SchwartzZippel
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Resultant degree bounds and bivariate root multiplicities

For bivariate polynomials `f, g : R[X][X]` whose coefficients in the inner indeterminate have
degrees at most `df` and `dg`, the resultant `f.resultant g m n` has degree at most
`m * dg + n * df`. In particular, for `Q : R[X][X]` of outer degree `d₁` and inner degree `d₂`,
`Q.resultant Q.derivative` has degree at most `2 * d₁ * d₂`.

Over an integral domain `R`, if `Q : R[X][X]` has nonzero formal derivative resultant
`Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)`, then at every point `(α, β) ∈ R × R`
the fiber multiplicity `(Q.map (evalRingHom β)).rootMultiplicity α` is bounded by
`1 + (Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)).rootMultiplicity β`. After shifting
the outer coordinate by `C α`, a fiber root of multiplicity `m ≥ 2` makes `X - C β` divide the
first `m` coefficients of the shifted polynomial and hence the first `m - 1` coefficients of its
derivative, so `X - C β` divides each of the first `m - 1` rows of the Sylvester matrix, and hence
`(X - C β) ^ (m - 1)` divides its determinant.

Over a characteristic-zero field `K`, unique factorization in `K[X][X]` combines this resultant
bound with a point-set zero bound to estimate high-order vanishing along fibers with distinct
base coordinates (`Polynomial.card_mul_le_of_pow_dvd_map_evalRingHom`), together with its
specialization to planar grids via the Schwartz–Zippel lemma
(`Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`).

## Main results

* `Polynomial.natDegree_resultant_le`, `Polynomial.natDegree_resultant_deriv_le`: degree bounds
  for resultants of bivariate polynomials.
* `Polynomial.rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero`: the Sylvester-row
  bound on fiber root multiplicities over any integral domain.
* `Squarefree.rootMultiplicity_map_evalRingHom_le`,
  `Irreducible.rootMultiplicity_map_evalRingHom_le`: fiber multiplicity bounds in characteristic
  zero.
* `Polynomial.card_mul_le_of_pow_dvd_map_evalRingHom`: bivariate multiplicity bound along
  fibers with injective base coordinates.
* `Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`: vanishing criterion on
  planar grids under an invertible linear or affine change of coordinates.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon **2610.00311** (2026), Proposition 4.1 and
  Appendix A.
-/

public section

open scoped Finset

namespace Polynomial

section DegreeBounds

/-- **Degree bound for bivariate resultants.** If the coefficients of `f, g : R[X][X]` have
degrees at most `df` and `dg`, then `f.resultant g m n` has degree at most `m * dg + n * df`. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R] (f g : R[X][X]) (m n df dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ df) (hg : ∀ i, (g.coeff i).natDegree ≤ dg) :
    (f.resultant g m n).natDegree ≤ m * dg + n * df := by
  let e : Fin (m + n) → ℕ := fun j ↦ if (j : ℕ) < m then dg else df
  have hcol (i j : Fin (m + n)) : (sylvester f g m n i j).natDegree ≤ e j := by
    by_cases hj : (j : ℕ) < m
    · rw [sylvester_apply_of_lt _ _ i j hj]
      simp only [e, hj, ↓reduceIte]
      split_ifs <;> [exact hg _; simp]
    · rw [sylvester_apply_of_le _ _ i j (Nat.le_of_not_lt hj)]
      simp only [e, hj, ↓reduceIte]
      split_ifs <;> [exact hf _; simp]
  refine (Matrix.natDegree_det_le_of_natDegree_le (sylvester f g m n) e hcol).trans ?_
  have hsum : ∑ j : Fin (m + n), e j = m * dg + n * df := by
    rw [Fin.sum_univ_add]
    have hleft : ∑ j : Fin m, e (Fin.castAdd n j) = m * dg := by simp [e]
    have hright : ∑ j : Fin n, e (Fin.natAdd m j) = n * df := by
      simp [e, Nat.not_lt.mpr (Nat.le_add_right m _)]
    rw [hleft, hright]
  exact hsum.le

/-- The resultant of `Q : R[X][X]` and its outer derivative has degree at most
`2 * Q.natDegree * (Bivariate.swap Q).natDegree`. -/
theorem natDegree_resultant_deriv_le {R : Type*} [CommRing R] (Q : R[X][X]) :
    (Q.resultant Q.derivative).natDegree ≤
      2 * Q.natDegree * (Bivariate.swap Q).natDegree := by
  set d := (Bivariate.swap Q).natDegree
  have hQ : ∀ i, (Q.coeff i).natDegree ≤ d := Bivariate.natDegree_coeff_le_natDegree_swap Q
  have hQ' (i : ℕ) : (Q.derivative.coeff i).natDegree ≤ d := by
    rw [coeff_derivative]
    exact (natDegree_mul_le.trans (by simp)).trans (hQ (i + 1))
  calc (Q.resultant Q.derivative).natDegree
      ≤ Q.natDegree * d + Q.derivative.natDegree * d :=
        natDegree_resultant_le Q Q.derivative _ _ d d hQ hQ'
    _ ≤ Q.natDegree * d + Q.natDegree * d := by
        gcongr
        exact (natDegree_derivative_le Q).trans (Nat.sub_le _ _)
    _ = 2 * Q.natDegree * d := by ring

end DegreeBounds

section ResultantMultiplicity

/-- **Resultant bound on fiber root multiplicities.** Over an integral domain `R`, if `Q : R[X][X]`
has nonzero formal derivative resultant `Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)`,
then the multiplicity of `α` as a root of the specialized polynomial `Q.map (evalRingHom β)` is at
most one more than the multiplicity of `β` as a root of that resultant. -/
theorem rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero {R : Type*} [CommRing R]
    [IsDomain R] {Q : R[X][X]}
    (hres : Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1) ≠ 0) (α β : R) :
    (Q.map (evalRingHom β)).rootMultiplicity α ≤
      1 + (Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)).rootMultiplicity β := by
  set φ : R[X] →+* R := evalRingHom β
  set m := (Q.map φ).rootMultiplicity α
  rcases le_or_gt m 1 with hm1 | hm1
  · omega
  have hmap0 : Q.map φ ≠ 0 := by
    rintro h0
    simp [m, h0] at hm1
  set d := Q.natDegree
  have hmd : m ≤ d := by
    have hdvd := pow_rootMultiplicity_dvd (Q.map φ) α
    have hm_deg := natDegree_le_of_dvd hdvd hmap0
    rw [natDegree_pow, natDegree_X_sub_C, mul_one] at hm_deg
    exact hm_deg.trans natDegree_map_le
  -- Shift the outer variable by `C α` so the multiple root moves to `0`.
  set P : R[X][X] := taylor (C α) Q
  have htrail : (P.map φ).natTrailingDegree = m := by
    simp only [P, map_taylor, φ, coe_evalRingHom, eval_C]
    exact natTrailingDegree_taylor (Q.map (evalRingHom β)) α
  have hdvd_P {k : ℕ} (hk : k < m) : X - C β ∣ P.coeff k := by
    rw [dvd_iff_isRoot, IsRoot.def]
    have hk0 := coeff_eq_zero_of_lt_natTrailingDegree (htrail.symm ▸ hk)
    rwa [coeff_map] at hk0
  have hdvd_P' {k : ℕ} (hk : k < m - 1) : X - C β ∣ P.derivative.coeff k := by
    rw [coeff_derivative]
    exact dvd_mul_of_dvd_left (hdvd_P (by omega)) _
  -- Every entry in the first `m - 1` rows of `sylvester P P.derivative d (d - 1)` is a multiple
  -- of `X - C β`.
  let s : Finset (Fin (d + (d - 1))) :=
    Finset.univ.image (Fin.castLE (by omega : m - 1 ≤ d + (d - 1)))
  have hs_card : s.card = m - 1 := by
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_fin]
  have hdvd_res : (X - C β) ^ (m - 1) ∣ Q.resultant Q.derivative d (d - 1) := by
    rw [← resultant_taylor_deriv Q (C α), resultant, ← hs_card]
    have hprod : (X - C β) ^ s.card =
        ∏ i : Fin (d + (d - 1)), if i ∈ s then X - C β else 1 := by
      rw [Fintype.prod_ite_mem]
      simp
    rw [hprod]
    refine Matrix.prod_dvd_det_of_dvd_row _ _ fun i j ↦ ?_
    split_ifs with hi
    · rcases Finset.mem_image.mp hi with ⟨i₀, -, rfl⟩
      exact dvd_sylvester_of_dvd_coeff (fun _ hk ↦ hdvd_P (by omega)) (fun _ hk ↦ hdvd_P' hk)
        i₀.isLt
    · exact one_dvd _
  have hle := (le_rootMultiplicity_iff hres).mpr hdvd_res
  omega

/-- **Resultant multiplicity bound for squarefree bivariate polynomials.** Over a GCD domain `R`
of characteristic zero, if `Q : R[X][X]` is squarefree, then
`(Q.map (evalRingHom β)).rootMultiplicity α ≤ 1 + (Q.resultant Q.derivative).rootMultiplicity β`
for all `α, β : R`. -/
theorem _root_.Squarefree.rootMultiplicity_map_evalRingHom_le {R : Type*} [CommRing R]
    [IsDomain R] [IsGCDMonoid R] [CharZero R] {Q : R[X][X]} (hQ : Squarefree Q) (α β : R) :
    (Q.map (evalRingHom β)).rootMultiplicity α ≤
      1 + (Q.resultant Q.derivative).rootMultiplicity β := by
  have hres :
      Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1) = Q.resultant Q.derivative := by
    rw [← natDegree_derivative]
  rw [← hres]
  exact rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero
    (hres ▸ hQ.resultant_deriv_ne_zero) α β

/-- **Resultant multiplicity bound for irreducible bivariate polynomials** (Green, Appendix A). -/
theorem _root_.Irreducible.rootMultiplicity_map_evalRingHom_le {R : Type*} [CommRing R]
    [IsDomain R] [IsGCDMonoid R] [CharZero R] {Q : R[X][X]} (hQ : Irreducible Q) (α β : R) :
    (Q.map (evalRingHom β)).rootMultiplicity α ≤
      1 + (Q.resultant Q.derivative).rootMultiplicity β :=
  hQ.squarefree.rootMultiplicity_map_evalRingHom_le α β

end ResultantMultiplicity

section BivariateMultiplicityBound

/-- The fiber root multiplicity of `P : R[X][X]` at `(α, β)`, capped at `N` (equal to `N` when the
fiber polynomial `P.map (evalRingHom β)` vanishes identically). -/
private noncomputable def cappedFiberMult {R : Type*} [CommRing R] (α β : R)
    (N : ℕ) (P : R[X][X]) : ℕ :=
  (P.map (evalRingHom β)).cappedRootMultiplicity α N

private theorem cappedFiberMult_of_isUnit {R : Type*} [CommRing R] [IsDomain R] (α β : R)
    (N : ℕ) {u : R[X][X]} (hu : IsUnit u) : cappedFiberMult α β N u = 0 :=
  cappedRootMultiplicity_of_isUnit (hu.map (mapRingHom (evalRingHom β))) α N

private theorem cappedFiberMult_mul_le {R : Type*} [CommRing R] [IsDomain R] (α β : R) (N : ℕ)
    (A B : R[X][X]) :
    cappedFiberMult α β N (A * B) ≤ cappedFiberMult α β N A + cappedFiberMult α β N B := by
  rw [cappedFiberMult, Polynomial.map_mul]
  exact cappedRootMultiplicity_mul_le _ _ α N

/-- The bivariate multiplicity bound on a single irreducible factor `Q : K[X][X]`. -/
private theorem sum_cappedFiberMult_le_of_irreducible {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    {Q : K[X][X]} (hQ : Irreducible Q) :
    ∑ i : ι, cappedFiberMult (α i) (β i) N Q ≤
      N * (Q.natDegree + (Bivariate.swap Q).natDegree) +
        2 * Q.natDegree * (Bivariate.swap Q).natDegree := by
  classical
  rcases Nat.eq_zero_or_pos Q.natDegree with hdeg0 | hdeg
  · obtain ⟨q, rfl⟩ := natDegree_eq_zero.mp hdeg0
    have hq0 : q ≠ 0 := fun h ↦ hQ.ne_zero (by simp [h])
    have hswap : (Bivariate.swap (C q : K[X][X])).natDegree = q.natDegree := by
      rw [Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]
    let Z := Finset.univ.filter fun i : ι ↦ q.eval (β i) = 0
    have hterm (i : ι) : cappedFiberMult (α i) (β i) N (C q) = if i ∈ Z then N else 0 := by
      by_cases h0 : q.eval (β i) = 0
      · simp [cappedFiberMult, Z, h0]
      · simp [cappedFiberMult, Z, h0, cappedRootMultiplicity_C]
    have hZ : Z.card ≤ q.natDegree := by
      calc Z.card = ∑ i ∈ Z, 1 := by simp
        _ ≤ ∑ i ∈ Z, q.rootMultiplicity (β i) := Finset.sum_le_sum fun i hi ↦
            Nat.succ_le_of_lt ((rootMultiplicity_pos hq0).mpr (Finset.mem_filter.mp hi).2)
        _ ≤ q.natDegree := q.sum_rootMultiplicity_comp_le_natDegree Z hβ.injOn
    calc ∑ i : ι, cappedFiberMult (α i) (β i) N (C q)
        = ∑ i : ι, if i ∈ Z then N else 0 := Finset.sum_congr rfl fun i _ ↦ hterm i
      _ = N * Z.card := by rw [Fintype.sum_ite_mem]; simp [mul_comm]
      _ ≤ N * q.natDegree := Nat.mul_le_mul_left N hZ
      _ = N * ((C q : K[X][X]).natDegree + (Bivariate.swap (C q : K[X][X])).natDegree) +
            2 * (C q : K[X][X]).natDegree * (Bivariate.swap (C q : K[X][X])).natDegree := by
          rw [natDegree_C, hswap]
          ring
  · let Z := Finset.univ.filter fun i : ι ↦ (Q.map (evalRingHom (β i))).eval (α i) = 0
    have hne (i : ι) : Q.map (evalRingHom (β i)) ≠ 0 := hQ.map_evalRingHom_ne_zero hdeg _
    have hout (i : ι) (hi : i ∉ Z) : cappedFiberMult (α i) (β i) N Q = 0 := by
      have hnroot : ¬ (Q.map (evalRingHom (β i))).IsRoot (α i) := by
        simpa [Z, IsRoot.def] using hi
      simp [cappedFiberMult, cappedRootMultiplicity_of_ne_zero (hne i),
        rootMultiplicity_eq_zero hnroot]
    have hin (i : ι) : cappedFiberMult (α i) (β i) N Q ≤
        1 + (Q.resultant Q.derivative).rootMultiplicity (β i) := by
      rw [cappedFiberMult, cappedRootMultiplicity_of_ne_zero (hne i)]
      exact (min_le_right _ _).trans (hQ.rootMultiplicity_map_evalRingHom_le (α i) (β i))
    calc ∑ i : ι, cappedFiberMult (α i) (β i) N Q
        = ∑ i ∈ Z, cappedFiberMult (α i) (β i) N Q :=
          (Finset.sum_subset (Finset.subset_univ Z) fun i _ hi ↦ hout i hi).symm
      _ ≤ ∑ i ∈ Z, (1 + (Q.resultant Q.derivative).rootMultiplicity (β i)) :=
          Finset.sum_le_sum fun i _ ↦ hin i
      _ = Z.card + ∑ i ∈ Z, (Q.resultant Q.derivative).rootMultiplicity (β i) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ N * (Q.natDegree + (Bivariate.swap Q).natDegree) +
            (Q.resultant Q.derivative).natDegree :=
          add_le_add (hzero Q hQ.ne_zero)
            ((Q.resultant Q.derivative).sum_rootMultiplicity_comp_le_natDegree Z hβ.injOn)
      _ ≤ N * (Q.natDegree + (Bivariate.swap Q).natDegree) +
            2 * Q.natDegree * (Bivariate.swap Q).natDegree :=
          Nat.add_le_add_left (natDegree_resultant_deriv_le Q) _

/-- **Bivariate multiplicity estimate** (Green, Proposition 4.1). Let `(α i, β i)` be a finite
family of points in `K × K` over a characteristic-zero field `K`, with `β` injective, such that
every nonzero bivariate polynomial `H : K[X][X]` vanishes at no more than
`N * (H.natDegree + (Bivariate.swap H).natDegree)` of the points. If `F ≠ 0` vanishes to order at
least `N` in the outer coordinate along every fiber `X = β i`, then
`Fintype.card ι * N ≤ N * (F.natDegree + (Bivariate.swap F).natDegree) +
  2 * F.natDegree * (Bivariate.swap F).natDegree`. -/
theorem card_mul_le_of_pow_dvd_map_evalRingHom {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    {F : K[X][X]} (hF : F ≠ 0)
    (hmult : ∀ i : ι, (X - C (α i)) ^ N ∣ F.map (evalRingHom (β i))) :
    Fintype.card ι * N ≤
      N * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  have hsum_F : Fintype.card ι * N = ∑ i : ι, cappedFiberMult (α i) (β i) N F := by
    have hpt (i : ι) : cappedFiberMult (α i) (β i) N F = N :=
      cappedRootMultiplicity_eq_self_iff.mpr (hmult i)
    simp [hpt]
  rw [hsum_F]
  suffices hgen : ∀ P : K[X][X], P ≠ 0 →
      ∑ i : ι, cappedFiberMult (α i) (β i) N P ≤
        N * (P.natDegree + (Bivariate.swap P).natDegree) +
          2 * P.natDegree * (Bivariate.swap P).natDegree from hgen F hF
  intro P
  refine UniqueFactorizationMonoid.induction_on_prime P (fun h ↦ absurd rfl h) (fun u hu _ ↦ ?_)
    (fun a p ha0 hp ih _ ↦ ?_)
  · simp [cappedFiberMult_of_isUnit _ _ N hu]
  · have hp0 : p ≠ 0 := hp.ne_zero
    have hdeg_z : (p * a).natDegree = p.natDegree + a.natDegree := natDegree_mul hp0 ha0
    have hswap_a : Bivariate.swap a ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr ha0
    have hswap_p : Bivariate.swap p ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr hp0
    have hdeg_y : (Bivariate.swap (p * a)).natDegree =
        (Bivariate.swap p).natDegree + (Bivariate.swap a).natDegree := by
      rw [map_mul, natDegree_mul hswap_p hswap_a]
    have hp_bound := sum_cappedFiberMult_le_of_irreducible hβ hzero hp.irreducible
    have ha_bound := ih ha0
    calc ∑ i : ι, cappedFiberMult (α i) (β i) N (p * a)
        ≤ ∑ i : ι, (cappedFiberMult (α i) (β i) N p + cappedFiberMult (α i) (β i) N a) :=
          Finset.sum_le_sum fun i _ ↦ cappedFiberMult_mul_le (α i) (β i) N p a
      _ = (∑ i : ι, cappedFiberMult (α i) (β i) N p) +
            ∑ i : ι, cappedFiberMult (α i) (β i) N a := Finset.sum_add_distrib
      _ ≤ N * ((p * a).natDegree + (Bivariate.swap (p * a)).natDegree) +
            2 * (p * a).natDegree * (Bivariate.swap (p * a)).natDegree := by
          rw [hdeg_z, hdeg_y]
          nlinarith

/-- **Planar grid vanishing criterion.** Let `S` be a finite subset of a characteristic-zero field
`K`, and let `L₁, L₂ : MvPolynomial (Fin 2) K` have total degree at most `1` such that substitution
`aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K` is injective and `L₂` takes distinct
values on `S ×ˢ S`. If `F : K[X][X]` vanishes to order at least `#S` in the outer coordinate at
`(L₁(x, y), L₂(x, y))` for all `x, y ∈ S`, and
`#S * (F.natDegree + (Bivariate.swap F).natDegree) +
  2 * F.natDegree * (Bivariate.swap F).natDegree < #S ^ 3`, then `F = 0`. -/
theorem eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube {K : Type*} [Field K] [CharZero K]
    (S : Finset K) {L₁ L₂ : MvPolynomial (Fin 2) K}
    (hL₁ : L₁.totalDegree ≤ 1) (hL₂ : L₂.totalDegree ≤ 1)
    (hinj_hom : Function.Injective (aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K))
    (hinj_β : ∀ x₁ ∈ S, ∀ y₁ ∈ S, ∀ x₂ ∈ S, ∀ y₂ ∈ S,
      MvPolynomial.eval ![x₁, y₁] L₂ = MvPolynomial.eval ![x₂, y₂] L₂ → x₁ = x₂ ∧ y₁ = y₂)
    {F : K[X][X]}
    (hmult : ∀ x ∈ S, ∀ y ∈ S,
      (X - C (MvPolynomial.eval ![x, y] L₁)) ^ S.card ∣
        F.map (evalRingHom (MvPolynomial.eval ![x, y] L₂)))
    (hdeg : S.card * (F.natDegree + (Bivariate.swap F).natDegree) +
      2 * F.natDegree * (Bivariate.swap F).natDegree < S.card ^ 3) :
    F = 0 := by
  classical
  by_contra hF
  let α : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.val, p.2.val] L₁
  let β : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.val, p.2.val] L₂
  have hβ : Function.Injective β := fun p q hpq ↦ by
    obtain ⟨hx, hy⟩ :=
      hinj_β p.1.val p.1.property p.2.val p.2.property q.1.val q.1.property q.2.val q.2.property hpq
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hzero (H : K[X][X]) (hH : H ≠ 0) :
      #{p : ↥S × ↥S | (H.map (evalRingHom (β p))).eval (α p) = 0} ≤
        S.card * (H.natDegree + (Bivariate.swap H).natDegree) :=
    card_grid_eval_eq_zero_le hL₁ hL₂ hinj_hom hH
  have hbound := card_mul_le_of_pow_dvd_map_evalRingHom hβ hzero hF
    (fun p ↦ hmult p.1.val p.1.property p.2.val p.2.property)
  have hcard : Fintype.card (↥S × ↥S) * S.card = S.card ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_coe]
    ring
  omega

end BivariateMultiplicityBound

end Polynomial
