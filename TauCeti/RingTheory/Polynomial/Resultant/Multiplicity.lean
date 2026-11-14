/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Resultant degree bounds and bivariate root multiplicities

For bivariate polynomials `f, g : R[X][X]` whose coefficients in the inner indeterminate have
degrees at most `df` and `dg`, the resultant `f.resultant g m n` has degree at most
`m * dg + n * df`. In particular, for `Q : R[X][X]` of outer degree `d₁` and inner degree `d₂`,
`Q.resultant Q.derivative` has degree at most `2 * d₁ * d₂`.

Over an integral domain `R`, if `Q : R[X][X]` has positive outer degree and its formal derivative
resultant `Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)` is nonzero, then at every point
`(α, β) ∈ R × R` the fiber multiplicity `(Q.map (evalRingHom β)).rootMultiplicity α` is bounded by
`1 + (Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)).rootMultiplicity β`. After shifting
the outer coordinate by `C α`, a fiber root of multiplicity `m ≥ 2` makes `X - C β` divide the
first `m` coefficients of the shifted polynomial and hence the first `m - 1` coefficients of its
derivative, so `(X - C β) ^ (m - 1)` divides the first `m - 1` rows of the Sylvester matrix.

Over a characteristic-zero field `K`, unique factorization in `K[X][X]` combines this resultant
bound with a point-set zero bound to estimate high-order vanishing along fibers with distinct
base coordinates (`Polynomial.card_mul_le_of_pow_dvd_map_evalRingHom`), together with its
specialization to planar grids via the Schwartz–Zippel lemma
(`Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`).

## Main results

* `Polynomial.Bivariate.coeff_coeff_swap`, `Polynomial.Bivariate.natDegree_swap_le_iff`:
  `Bivariate.swap` transposes bivariate coefficients, so `(Bivariate.swap Q).natDegree` is the
  least upper bound on the degrees of the coefficients of `Q`.
* `Polynomial.natDegree_resultant_le`, `Polynomial.natDegree_resultant_deriv_le`: degree bounds
  for resultants of bivariate polynomials.
* `Polynomial.rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero`: the Sylvester-row
  bound on fiber root multiplicities over any integral domain.
* `Squarefree.resultant_deriv_ne_zero`, `Squarefree.rootMultiplicity_map_evalRingHom_le`,
  `Irreducible.rootMultiplicity_map_evalRingHom_le`: nonvanishing of `Q.resultant Q.derivative`
  and the resulting fiber multiplicity bound in characteristic zero.
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

section SwapAndDegree

namespace Bivariate

/-- Swapping the two indeterminates of `R[X][X]` transposes the coefficient table. -/
@[simp]
theorem coeff_coeff_swap {R : Type*} [CommSemiring R] (Q : R[X][X]) (m n : ℕ) :
    ((swap Q).coeff m).coeff n = (Q.coeff n).coeff m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [(monomial k).map_add, map_add, coeff_add, coeff_add, coeff_add, ha, hb]
      simp [coeff_monomial]
    | monomial l r =>
      rw [swap_monomial_monomial, coeff_monomial, coeff_monomial]
      by_cases hlm : l = m <;> by_cases hkn : k = n <;> simp [hlm, hkn]

/-- The outer degree of `Bivariate.swap Q` bounds the degree of every coefficient of `Q`. -/
theorem natDegree_swap_le_iff {R : Type*} [CommSemiring R] {Q : R[X][X]} {d : ℕ} :
    (swap Q).natDegree ≤ d ↔ ∀ n, (Q.coeff n).natDegree ≤ d := by
  refine ⟨fun h n ↦ natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ ?_,
    fun h ↦ natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ ?_⟩
  · rw [← coeff_coeff_swap, natDegree_le_iff_coeff_eq_zero.mp h m hm, coeff_zero]
  · ext n
    rw [coeff_zero, coeff_coeff_swap, natDegree_le_iff_coeff_eq_zero.mp (h n) m hm]

/-- Every coefficient of `Q : R[X][X]` has degree at most `(Bivariate.swap Q).natDegree`. -/
theorem natDegree_coeff_le_natDegree_swap {R : Type*} [CommSemiring R] (Q : R[X][X]) (n : ℕ) :
    (Q.coeff n).natDegree ≤ (swap Q).natDegree :=
  natDegree_swap_le_iff.mp le_rfl n

end Bivariate

/-- **Degree bound for bivariate resultants.** If the coefficients of `f, g : R[X][X]` have
degrees at most `df` and `dg`, then `f.resultant g m n` has degree at most `m * dg + n * df`. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R] (f g : R[X][X]) (m n df dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ df) (hg : ∀ i, (g.coeff i).natDegree ≤ dg) :
    (f.resultant g m n).natDegree ≤ m * dg + n * df := by
  let e : Fin (m + n) → ℕ := Fin.addCases (fun _ ↦ dg) (fun _ ↦ df)
  have hcol (i j : Fin (m + n)) : (sylvester f g m n i j).natDegree ≤ e j := by
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, e]
      split_ifs <;> [exact hg _; simp]
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, e]
      split_ifs <;> [exact hf _; simp]
  refine (Matrix.natDegree_det_le_of_natDegree_le (sylvester f g m n) e hcol).trans ?_
  simp [e, Fin.sum_univ_add]

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

end SwapAndDegree

section ResultantMultiplicity

/-- Translating the indeterminate preserves the formal resultant `Res_{d, d - 1}(f, f')` over any
commutative ring, without canceling the leading coefficient. -/
private theorem resultant_taylor_deriv_eq {S : Type*} [CommRing S] (f : S[X]) (a : S) :
    (taylor a f).resultant (taylor a f).derivative f.natDegree (f.natDegree - 1) =
      f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  have hder : (taylor a f).derivative = taylor a f.derivative := by
    simp [taylor_apply, derivative_comp]
  rw [hder]
  calc
    resultant (taylor a f) (taylor a f.derivative) f.natDegree (f.natDegree - 1)
      = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          resultant (taylor a f) (taylor a f.derivative) := by
        conv_lhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ (by simp), coeff_taylor_natDegree]
        simp only [natDegree_taylor]
    _ = f.leadingCoeff ^ (f.natDegree - 1 - f.derivative.natDegree) *
          resultant f f.derivative := by rw [resultant_taylor]
    _ = resultant f f.derivative f.natDegree (f.natDegree - 1) := by
        conv_rhs => rw [← Nat.add_sub_of_le (natDegree_derivative_le f)]
        rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]

/-- If `r` divides every entry in a set `s` of rows of a square matrix `M`, then `r ^ #s` divides
`M.det`. -/
private theorem pow_card_dvd_det_of_forall_dvd_row {S ι : Type*} [CommRing S] [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι S} {r : S} {s : Finset ι}
    (h : ∀ i ∈ s, ∀ j, r ∣ M i j) : r ^ s.card ∣ M.det := by
  classical
  have hrow (i : ι) (j : ι) : ∃ c : S, M i j = (if i ∈ s then r else 1) * c := by
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h i hi j
      exact ⟨c, by simp [hi, hc]⟩
    · exact ⟨M i j, by simp [hi]⟩
  choose B hB using hrow
  have hM : M = Matrix.diagonal (fun i ↦ if i ∈ s then r else 1) * Matrix.of B := by
    ext i j
    simpa [Matrix.diagonal_mul] using hB i j
  refine ⟨(Matrix.of B).det, ?_⟩
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **Resultant bound on fiber root multiplicities.** Over an integral domain `R`, if `Q : R[X][X]`
has positive outer degree and nonzero formal derivative resultant
`Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1)`, then the multiplicity of `α` as a root of
the specialized polynomial `Q.map (evalRingHom β)` is at most one more than the multiplicity of `β`
as a root of that resultant. -/
theorem rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero {R : Type*} [CommRing R]
    [IsDomain R] {Q : R[X][X]} (hQ : 0 < Q.natDegree)
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
  have hPmap : P.map φ = (Q.map φ).comp (X + C α) := by
    simp [P, taylor_apply, map_comp, φ]
  have htrail : (P.map φ).natTrailingDegree = m := by
    rw [hPmap, ← rootMultiplicity_eq_natTrailingDegree]
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
  have hs_dvd (i : Fin (d + (d - 1))) (hi : i ∈ s) (j : Fin (d + (d - 1))) :
      X - C β ∣ sylvester P P.derivative d (d - 1) i j := by
    rcases Finset.mem_image.mp hi with ⟨i₀, -, rfl⟩
    have hi₀ : (i₀ : ℕ) < m - 1 := i₀.isLt
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castLE]
      split_ifs <;> [exact hdvd_P' (by omega); exact dvd_zero _]
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_castLE]
      split_ifs <;> [exact hdvd_P (by omega); exact dvd_zero _]
  have hdvd_res : (X - C β) ^ (m - 1) ∣ Q.resultant Q.derivative d (d - 1) := by
    rw [← resultant_taylor_deriv_eq Q (C α), ← hs_card]
    exact pow_card_dvd_det_of_forall_dvd_row hs_dvd
  have hle := (le_rootMultiplicity_iff hres).mpr hdvd_res
  omega

/-- Over a characteristic-zero integral domain, the derivative of a polynomial of positive degree
has degree `p.natDegree - 1`. -/
private theorem natDegree_derivative_eq_sub_one {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    {p : D[X]} (hp : 0 < p.natDegree) : p.derivative.natDegree = p.natDegree - 1 := by
  refine le_antisymm (natDegree_derivative_le p) (le_natDegree_of_ne_zero ?_)
  rw [coeff_derivative, Nat.sub_add_cancel hp, coeff_natDegree, ← Nat.cast_add_one]
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp0)
    (Nat.cast_ne_zero.mpr (by omega : p.natDegree - 1 + 1 ≠ 0))

/-- A squarefree polynomial of positive degree over a GCD domain of characteristic zero has
nonzero resultant with its derivative. -/
theorem _root_.Squarefree.resultant_deriv_ne_zero {D : Type*} [CommRing D] [IsDomain D]
    [IsGCDMonoid D] [CharZero D] {p : D[X]} (hp : Squarefree p) (hdeg : 0 < p.natDegree) :
    p.resultant p.derivative ≠ 0 := by
  rw [resultant, natDegree_derivative_eq_sub_one hdeg, ← resultant,
    resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg)]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hp.ne_zero))
    hp.discr_ne_zero

/-- **Resultant multiplicity bound for squarefree bivariate polynomials.** Over a GCD domain `R`
of characteristic zero, if `Q : R[X][X]` is squarefree of positive outer degree, then
`(Q.map (evalRingHom β)).rootMultiplicity α ≤ 1 + (Q.resultant Q.derivative).rootMultiplicity β`
for all `α, β : R`. -/
theorem _root_.Squarefree.rootMultiplicity_map_evalRingHom_le {R : Type*} [CommRing R]
    [IsDomain R] [IsGCDMonoid R] [CharZero R] {Q : R[X][X]} (hQ : Squarefree Q)
    (hdeg : 0 < Q.natDegree) (α β : R) :
    (Q.map (evalRingHom β)).rootMultiplicity α ≤
      1 + (Q.resultant Q.derivative).rootMultiplicity β := by
  have hder : Q.derivative.natDegree = Q.natDegree - 1 := natDegree_derivative_eq_sub_one hdeg
  have hres :
      Q.resultant Q.derivative Q.natDegree (Q.natDegree - 1) = Q.resultant Q.derivative := by
    rw [← hder]
  rw [← hres]
  exact rootMultiplicity_map_evalRingHom_le_of_resultant_ne_zero hdeg
    (hres ▸ hQ.resultant_deriv_ne_zero hdeg) α β

/-- **Resultant multiplicity bound for irreducible bivariate polynomials** (Green, Appendix A). -/
theorem _root_.Irreducible.rootMultiplicity_map_evalRingHom_le {R : Type*} [CommRing R]
    [IsDomain R] [IsGCDMonoid R] [CharZero R] {Q : R[X][X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) (α β : R) :
    (Q.map (evalRingHom β)).rootMultiplicity α ≤
      1 + (Q.resultant Q.derivative).rootMultiplicity β :=
  hQ.squarefree.rootMultiplicity_map_evalRingHom_le hdeg α β

end ResultantMultiplicity

section BivariateMultiplicityBound

/-- The fiber root multiplicity of `P : K[X][X]` at `(α, β)`, capped at `N` (equal to `N` when the
fiber polynomial `P.map (evalRingHom β)` vanishes identically). -/
private noncomputable def cappedFiberMult {K : Type*} [Field K] (α β : K) (N : ℕ)
    (P : K[X][X]) : ℕ :=
  letI := Classical.propDecidable
  if P.map (evalRingHom β) = 0 then N else min N ((P.map (evalRingHom β)).rootMultiplicity α)

private theorem cappedFiberMult_of_isUnit {K : Type*} [Field K] (α β : K) (N : ℕ)
    {u : K[X][X]} (hu : IsUnit u) : cappedFiberMult α β N u = 0 := by
  obtain ⟨p, hp, rfl⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hp
  have hmap : (C (C c) : K[X][X]).map (evalRingHom β) = C c := by simp
  have hc0 : (C c : K[X]) ≠ 0 := C_ne_zero.mpr hc.ne_zero
  simp [cappedFiberMult, hmap, hc0, rootMultiplicity_C]

private theorem cappedFiberMult_mul_le {K : Type*} [Field K] (α β : K) (N : ℕ)
    (A B : K[X][X]) :
    cappedFiberMult α β N (A * B) ≤ cappedFiberMult α β N A + cappedFiberMult α β N B := by
  dsimp [cappedFiberMult]
  rw [Polynomial.map_mul]
  by_cases hA : A.map (evalRingHom β) = 0
  · simp [hA]
  by_cases hB : B.map (evalRingHom β) = 0
  · simp [hB]
  have hAB : A.map (evalRingHom β) * B.map (evalRingHom β) ≠ 0 := mul_ne_zero hA hB
  simp only [hA, hB, hAB, ↓reduceIte, rootMultiplicity_mul hAB]
  omega

/-- Over a field, the sum of root multiplicities of a polynomial over any image of an injective
map is at most its degree. -/
private theorem sum_rootMultiplicity_le_natDegree {K ι : Type*} [Field K] (s : Finset ι)
    {β : ι → K} (hβ : Function.Injective β) (p : K[X]) :
    ∑ i ∈ s, p.rootMultiplicity (β i) ≤ p.natDegree := by
  classical
  calc ∑ i ∈ s, p.rootMultiplicity (β i)
      = ∑ b ∈ s.image β, p.rootMultiplicity b :=
        (Finset.sum_image (f := fun b ↦ p.rootMultiplicity b) fun _ _ _ _ h ↦ hβ h).symm
    _ = ∑ b ∈ s.image β, p.roots.count b := by simp_rw [count_roots]
    _ ≤ ∑ b ∈ (s.image β ∪ p.roots.toFinset), p.roots.count b :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ b ∈ p.roots.toFinset, p.roots.count b := by
        refine (Finset.sum_subset Finset.subset_union_right fun b _ hb ↦ ?_).symm
        exact Multiset.count_eq_zero.mpr (Multiset.mem_toFinset.not.mp hb)
    _ = p.roots.card := p.roots.toFinset_sum_count_eq
    _ ≤ p.natDegree := card_roots' p

/-- An irreducible bivariate polynomial of positive outer degree cannot vanish identically on any
vertical fiber `X = β`. -/
private theorem map_evalRingHom_ne_zero_of_irreducible {K : Type*} [Field K] {Q : K[X][X]}
    (hQ : Irreducible Q) (hdeg : 0 < Q.natDegree) (β : K) :
    Q.map (evalRingHom β) ≠ 0 := by
  intro h0
  have hdvd : C (X - C β) ∣ Q := by
    rw [C_dvd_iff_dvd_coeff]
    intro k
    rw [dvd_iff_isRoot, IsRoot.def]
    have hk0 : (Q.map (evalRingHom β)).coeff k = 0 := by simp [h0]
    rwa [coeff_map] at hk0
  obtain ⟨R₀, hQR⟩ := hdvd
  rcases hQ.isUnit_or_isUnit hQR with hu | hu
  · exact not_isUnit_X_sub_C β (isUnit_C.mp hu)
  · have hR₀ : R₀.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hQ0 : Q.natDegree ≤ 0 := by
      rw [hQR]
      exact natDegree_mul_le.trans (by simp [hR₀])
    omega

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
      by_cases h0 : q.eval (β i) = 0 <;> simp [cappedFiberMult, Z, h0, rootMultiplicity_C]
    have hZ : Z.card ≤ q.natDegree := by
      calc Z.card = ∑ i ∈ Z, 1 := by simp
        _ ≤ ∑ i ∈ Z, q.rootMultiplicity (β i) := Finset.sum_le_sum fun i hi ↦
            Nat.succ_le_of_lt ((rootMultiplicity_pos hq0).mpr (Finset.mem_filter.mp hi).2)
        _ ≤ q.natDegree := sum_rootMultiplicity_le_natDegree Z hβ q
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      Finset.sum_const_zero, add_zero, smul_eq_mul, natDegree_C, hswap, zero_add, mul_zero,
      zero_mul, add_zero, mul_comm]
    exact Nat.mul_le_mul_left N hZ
  · let Z := Finset.univ.filter fun i : ι ↦ (Q.map (evalRingHom (β i))).eval (α i) = 0
    have hout (i : ι) (hi : i ∉ Z) : cappedFiberMult (α i) (β i) N Q = 0 := by
      have hne : Q.map (evalRingHom (β i)) ≠ 0 := map_evalRingHom_ne_zero_of_irreducible hQ hdeg _
      have hnroot : ¬ (Q.map (evalRingHom (β i))).IsRoot (α i) := by
        simpa [Z, IsRoot.def] using hi
      simp [cappedFiberMult, hne, rootMultiplicity_eq_zero hnroot]
    have hin (i : ι) : cappedFiberMult (α i) (β i) N Q ≤
        1 + (Q.resultant Q.derivative).rootMultiplicity (β i) := by
      have hne : Q.map (evalRingHom (β i)) ≠ 0 := map_evalRingHom_ne_zero_of_irreducible hQ hdeg _
      simp only [cappedFiberMult, hne, ↓reduceIte]
      exact (min_le_right _ _).trans (hQ.rootMultiplicity_map_evalRingHom_le hdeg (α i) (β i))
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
            (sum_rootMultiplicity_le_natDegree Z hβ (Q.resultant Q.derivative))
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
    have hpt (i : ι) : cappedFiberMult (α i) (β i) N F = N := by
      dsimp [cappedFiberMult]
      split_ifs with h0
      · rfl
      · exact min_eq_left ((le_rootMultiplicity_iff h0).mpr (hmult i))
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

/-- Substituting two polynomials of total degree at most `1` into `H : R[X][X]` produces a
multivariate polynomial of total degree at most `H.natDegree + (Bivariate.swap H).natDegree`. -/
private theorem totalDegree_aevalAeval_le {R σ : Type*} [CommSemiring R]
    {L₁ L₂ : MvPolynomial σ R} (hL₁ : L₁.totalDegree ≤ 1) (hL₂ : L₂.totalDegree ≤ 1)
    (H : R[X][X]) :
    (aevalAeval L₂ L₁ H).totalDegree ≤ H.natDegree + (Bivariate.swap H).natDegree := by
  conv_lhs => rw [H.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
  have hk_le : k ≤ H.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hpow₁ : (L₁ ^ k).totalDegree ≤ H.natDegree :=
    (MvPolynomial.totalDegree_pow L₁ k).trans ((Nat.mul_le_mul_left k hL₁).trans (by simpa))
  have hcoeff : (aeval L₂ (H.coeff k)).totalDegree ≤ (Bivariate.swap H).natDegree := by
    conv_lhs => rw [(H.coeff k).as_sum_range_C_mul_X_pow]
    rw [map_sum]
    refine MvPolynomial.totalDegree_finsetSum_le fun j hj ↦ ?_
    have hj_le : j ≤ (Bivariate.swap H).natDegree :=
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans
        (Bivariate.natDegree_coeff_le_natDegree_swap H k)
    rw [map_mul, map_pow, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
    exact (MvPolynomial.totalDegree_smul_le _ _).trans
      ((MvPolynomial.totalDegree_pow L₂ j).trans ((Nat.mul_le_mul_left j hL₂).trans (by simpa)))
  exact (add_le_add hcoeff hpow₁).trans (by omega)

/-- Evaluating `aevalAeval L₂ L₁ H` at `f : σ → R` agrees with specializing `H` at
`MvPolynomial.eval f L₂` and `MvPolynomial.eval f L₁`. -/
private theorem eval_aevalAeval {R σ : Type*} [CommSemiring R] (f : σ → R)
    (L₁ L₂ : MvPolynomial σ R) (H : R[X][X]) :
    MvPolynomial.eval f (aevalAeval L₂ L₁ H) =
      (H.map (evalRingHom (MvPolynomial.eval f L₂))).eval (MvPolynomial.eval f L₁) := by
  rw [map_evalRingHom_eval, ← coe_aevalAeval_eq_evalEval]
  have hhom : (MvPolynomial.aeval f).comp (aevalAeval L₂ L₁) =
      aevalAeval (MvPolynomial.eval f L₂) (MvPolynomial.eval f L₁) :=
    (aevalAevalEquiv R R).symm.injective (by simp)
  simpa using AlgHom.congr_fun hhom H

/-- Schwartz–Zippel zero-count bound for `aevalAeval L₂ L₁ H` over `S × S`. -/
private theorem card_grid_eval_eq_zero_le {K : Type*} [Field K] [DecidableEq K]
    {S : Finset K} (hS0 : 0 < S.card) {L₁ L₂ : MvPolynomial (Fin 2) K}
    (hL₁ : L₁.totalDegree ≤ 1) (hL₂ : L₂.totalDegree ≤ 1)
    (hinj_hom : Function.Injective (aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K))
    {H : K[X][X]} (hH : H ≠ 0) :
    #{p : ↥S × ↥S |
        (H.map (evalRingHom (MvPolynomial.eval ![p.1.1, p.2.1] L₂))).eval
          (MvPolynomial.eval ![p.1.1, p.2.1] L₁) = 0} ≤
      S.card * (H.natDegree + (Bivariate.swap H).natDegree) := by
  set P : MvPolynomial (Fin 2) K := aevalAeval L₂ L₁ H
  have hP0 : P ≠ 0 := fun h ↦ hH (hinj_hom (h.trans (map_zero _).symm))
  let emb : ↥S × ↥S → Fin 2 → K := fun p ↦ ![p.1.1, p.2.1]
  have hemb_inj : Function.Injective emb := fun p q h ↦
    Prod.ext (Subtype.ext (congrFun h 0)) (Subtype.ext (congrFun h 1))
  have hsub : (Finset.univ.filter fun p : ↥S × ↥S ↦
        (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
          (MvPolynomial.eval (emb p) L₁) = 0).image emb ⊆
      (Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun f ↦ MvPolynomial.eval f P = 0 := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨p, hp, rfl⟩
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Fintype.mem_piFinset.mpr fun i ↦ by fin_cases i <;> simp [emb, p.1.2, p.2.2], ?_⟩
    rw [eval_aevalAeval]
    exact hp.2
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP0 S
  have hcard_le : #{f ∈ Fintype.piFinset fun _ : Fin 2 ↦ S | MvPolynomial.eval f P = 0} ≤
      S.card * P.totalDegree := by
    have hS_pos : (0 : NNRat) < S.card := mod_cast hS0
    have hmul := mul_le_mul_of_nonneg_right hsz (pow_pos hS_pos 2).le
    have hrhs : (P.totalDegree : NNRat) / S.card * (S.card : NNRat) ^ 2 =
        S.card * P.totalDegree := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hS_pos.ne', mul_comm]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hS_pos.ne'), hrhs] at hmul
    exact_mod_cast hmul
  calc #{p : ↥S × ↥S |
          (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
            (MvPolynomial.eval (emb p) L₁) = 0}
      = ((Finset.univ.filter fun p : ↥S × ↥S ↦
          (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
            (MvPolynomial.eval (emb p) L₁) = 0).image emb).card :=
        (Finset.card_image_of_injective _ hemb_inj).symm
    _ ≤ #{f ∈ Fintype.piFinset fun _ : Fin 2 ↦ S | MvPolynomial.eval f P = 0} :=
        Finset.card_le_card hsub
    _ ≤ S.card * P.totalDegree := hcard_le
    _ ≤ S.card * (H.natDegree + (Bivariate.swap H).natDegree) :=
        Nat.mul_le_mul_left _ (totalDegree_aevalAeval_le hL₁ hL₂ H)

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
  have hS0 : 0 < S.card := by
    by_contra h0
    simp [Nat.eq_zero_of_not_pos h0] at hdeg
  let α : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.1, p.2.1] L₁
  let β : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.1, p.2.1] L₂
  have hβ : Function.Injective β := fun p q hpq ↦ by
    obtain ⟨hx, hy⟩ := hinj_β p.1.1 p.1.2 p.2.1 p.2.2 q.1.1 q.1.2 q.2.1 q.2.2 hpq
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hzero (H : K[X][X]) (hH : H ≠ 0) :
      #{p : ↥S × ↥S | (H.map (evalRingHom (β p))).eval (α p) = 0} ≤
        S.card * (H.natDegree + (Bivariate.swap H).natDegree) :=
    card_grid_eval_eq_zero_le hS0 hL₁ hL₂ hinj_hom hH
  have hbound := card_mul_le_of_pow_dvd_map_evalRingHom hβ hzero hF
    (fun p ↦ hmult p.1.1 p.1.2 p.2.1 p.2.2)
  have hcard : Fintype.card (↥S × ↥S) * S.card = S.card ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_coe]
    ring
  omega

end BivariateMultiplicityBound

end Polynomial
