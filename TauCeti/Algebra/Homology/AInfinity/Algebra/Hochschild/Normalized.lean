/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Complex
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate

/-!
# Normalized Hochschild cochains of a strictly unital `A∞` algebra

Let `e` be a strict unit of an `A∞` algebra `A`.  A suspended Hochschild cochain
`F : Tᶜ(sA) ⟶ sA` is **normalized** when it vanishes on every word one of whose letters is `e`,
that is on the degenerate words `ReducedTensorWords.degenerateWords`.

The Taylor map `m` of `A` is not normalized, since `m₂(e, a) = a`; nevertheless the Hochschild
differential `[m, F] = m{F} - (-1)^q F{m}` of a normalized cochain `F` of degree `q` is normalized
again (`StrictUnit.degenerateWords_le_ker_hochschildDifferential`).  On a word `z` with the unit in
position `j`, all terms vanish except four: in `F{m}` the collapses of the two-letter blocks
`[e, a]` and `[a, e]` around position `j`, and in `m{F}` the collapses `m₂(e, F(⋯))` and
`m₂(F(⋯), e)` of everything but the unit, possible only when `j` is the first or the last
position.  When the unit is interior the two collapses in `F{m}` produce the same word with
opposite signs; at either end the surviving collapse in `F{m}` cancels the one in `m{F}`.  Brace
and Gerstenhaber bracket preserve normalized cochains as well, for any homogeneous `e`
(`ReducedTensorWords.degenerateWords_le_ker_gerstenhaberBracket`).

Thus the normalized cochains form a subcomplex `PositiveHochschild.normalizedComplex` of the
positive-arity Hochschild complex, closed under the Gerstenhaber bracket.  Whether its inclusion
`PositiveHochschild.normalizedComplexι` is a quasi-isomorphism is not addressed here.

## Main definitions

* `TauCeti.AInfinityAlgebra.PositiveHochschild.normalizedCochains`: the normalized cochains of
  a given degree.
* `TauCeti.AInfinityAlgebra.PositiveHochschild.normalizedComplex`: the normalized Hochschild
  complex of a strictly unital `A∞` algebra.
* `TauCeti.AInfinityAlgebra.PositiveHochschild.normalizedComplexι`: its inclusion into the
  positive-arity Hochschild complex.
* `TauCeti.AInfinityAlgebra.PositiveHochschild.normalizedBracket`: the Gerstenhaber bracket of
  normalized cochains.

## Main results

* `TauCeti.AInfinityAlgebra.StrictUnit.degenerateWords_le_ker_hochschildDifferential`: the
  Hochschild differential preserves normalized cochains.

## References

* M. Gerstenhaber, *The cohomology structure of an associative ring*, Annals of Mathematics 78
  (1963), 267--288.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

noncomputable section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 : AInfinityAlgebra R A} {e : A}

namespace StrictUnit

/-! ### The Hochschild differential of a normalized cochain -/

variable {q : ℤ} {F : ReducedTensorWords R A →ₗ[R] A}

/-- The `m{F}` half of the Hochschild differential of a normalized cochain on a homogeneous word
with the unit at position `j`: only the collapses of all letters but a unit at either end
survive. -/
private theorem taylor_gradedCoderiv_of_tprod (h : 𝒜.StrictUnit e)
    (hFe : degenerateWords R A e ≤ LinearMap.ker F) {n : ℕ} (x : Fin (n + 1) → A)
    (𝒟 : Fin (n + 1) → ℤ) (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1))
    (hj : x j = e) (h𝒟j : 𝒟 j = -1) :
    𝒜.taylor (gradedCoderiv (𝒜.grading.shift 1) F q
        (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then negOnePowCast R q • F (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then 𝒜.grading.koszulTwist 1 (F (subword R x 0 n)) else 0) := by
  rw [gradedCoderiv_of_tprod_of_homogeneous _ F q _ x 𝒟 hx]
  simp only [map_sum, map_smul]
  have hjn := j.isLt
  -- Identify each summand, indexed by a position `p` and a block length `d`.
  have hterm : ∀ p ∈ Finset.range (n + 1), ∀ d ∈ Finset.range (n + 1 + 1),
      (((q * ∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
          𝒜.taylor (splice R x 0 (n + 1) p d (F (subword R x p d))) =
        (if p = 1 ∧ d = n ∧ (j.1 = 0 ∧ 0 < n) then negOnePowCast R q • F (subword R x 1 n)
          else 0) +
        (if p = 0 ∧ d = n ∧ (j.1 = n ∧ 0 < n) then
          𝒜.grading.koszulTwist 1 (F (subword R x 0 n)) else 0) := by
    intro p hp d hd
    rw [Finset.mem_range] at hp hd
    by_cases hfit : 0 < d ∧ p + d ≤ n + 1
    swap
    · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
        ite_eq_right, add_zero]
    by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
    · -- The collapsed block contains the unit, so `F` kills it.
      simp (disch := omega) only [LinearMap.mem_ker.mp (hFe (subword_mem_degenerateWords x hfit.2
        ⟨j, hblock.1, hblock.2, hj⟩)), splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
    obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R x hfit.1 hfit.2
      (F (subword R x p d)) hblock
    by_cases hlen : n + 1 + 1 - d = 2
    swap
    · -- The spliced word contains the unit and does not have two letters.
      simp (disch := omega) only [hy,
        h.taylor_of_tprod_eq_zero ⟨n + 1 + 1 - d, by omega⟩ hlen y ⟨k, hk.trans hj⟩, smul_zero,
        ite_eq_right, add_zero]
    obtain rfl : n = d := by omega
    rcases Nat.lt_or_ge p 1 with hp0 | hp1
    · -- Everything but a final unit collapses.
      obtain rfl : p = 0 := by omega
      have hjn' : j = Fin.last n := Fin.ext (by rw [Fin.val_last]; omega)
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
      rw [splice_collapse_init_eq R hfit.1, ← hjn', hj, h.taylor_of_two_unit_right]
      simp
    · -- Everything but an initial unit collapses.
      obtain rfl : p = 1 := by omega
      have hj0 : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero]
      rw [splice_collapse_tail_eq R hfit.1, ← hj0, hj, h.taylor_of_two_unit_left]
      congr 1
      rw [Finset.sum_range_one, dite_eq_left (by omega), ← negOnePowCast_eq_intCast]
      have h𝒟0 : 𝒟 ⟨0, by omega⟩ = -1 := by rw [← h𝒟j, hj0]; rfl
      rw [h𝒟0, mul_neg_one, negOnePowCast_neg]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦ hterm p hp d hd]
  -- Each of the two families of terms is supported at a single pair `(p, d)`.
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- The `F{m}` half of the Hochschild differential of a normalized cochain on a homogeneous word
with the unit at position `j`: only the collapses of the two-letter blocks `[e, a]` and `[a, e]`
around the unit survive. -/
private theorem apply_barDifferential_of_tprod (h : 𝒜.StrictUnit e)
    (hFe : degenerateWords R A e ≤ LinearMap.ker F) {n : ℕ} (x : Fin (n + 1) → A)
    (𝒟 : Fin (n + 1) → ℤ) (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1))
    (hj : x j = e) :
    F (𝒜.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 + 1 ≤ n then
        negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          F (splice R x 0 (n + 1) j.1 2
            (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0)) else 0) +
      (if 1 ≤ j.1 then
        negOnePowCast R (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
          F (splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩)) else 0) := by
  have hjn := j.isLt
  rw [barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ x 𝒟 hx]
  simp only [map_sum, map_smul, one_mul]
  -- Identify each summand, indexed by a position `p` and a block length `d`.
  have hterm : ∀ p ∈ Finset.range (n + 1), ∀ d ∈ Finset.range (n + 1 + 1),
      (((∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
          F (splice R x 0 (n + 1) p d (𝒜.taylor (subword R x p d))) =
        (if p = j.1 ∧ d = 2 ∧ j.1 + 1 ≤ n then
          negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
            F (splice R x 0 (n + 1) j.1 2
              (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0)) else 0) +
        (if p = j.1 - 1 ∧ d = 2 ∧ 1 ≤ j.1 then
          negOnePowCast R
              (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
            negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
            F (splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩)) else 0) := by
    intro p hp d hd
    rw [Finset.mem_range] at hp hd
    by_cases hfit : 0 < d ∧ p + d ≤ n + 1
    swap
    · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
        ite_eq_right, add_zero]
    by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
    swap
    · -- The unit survives in the spliced word, which `F` kills.
      obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R x hfit.1 hfit.2
        (𝒜.taylor (subword R x p d)) hblock
      simp (disch := omega) only [hy,
        LinearMap.mem_ker.mp
          (hFe (of_tprod_mem_degenerateWords ⟨n + 1 + 1 - d, by omega⟩ y ⟨k, hk.trans hj⟩)),
        smul_zero, ite_eq_right, add_zero]
    by_cases hd2 : d = 2
    swap
    · -- The collapsed block contains the unit and does not have two letters.
      have hzero : 𝒜.taylor (subword R x p d) = 0 := by
        rw [subword_eq_of_tprod R x hfit.1 hfit.2]
        exact h.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩ hd2 _
          ⟨⟨j.1 - p, by dsimp only; omega⟩, by
            rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
      simp (disch := omega) only [hzero, splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
    subst hd2
    rcases Nat.lt_or_ge p j.1 with hpj | hpj
    · -- The block `[a, e]` collapses to the Koszul twist of `a`.
      obtain rfl : p = j.1 - 1 := by omega
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
      rw [subword_two_eq R x hfit.2]
      have hj' : (⟨j.1 - 1 + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
      rw [hj', hj, h.taylor_of_two_unit_right,
        𝒜.grading.koszulTwist_one_apply_of_mem
          (by simpa [InternalGrading.shift_piece] using hx ⟨j.1 - 1, by omega⟩),
        splice_smul, map_smul]
      simp only [negOnePowCast_eq_intCast]
    · -- The block `[e, a]` collapses to `a`.
      obtain rfl : p = j.1 := by omega
      simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero]
      rw [subword_two_eq R x hfit.2, Fin.eta, hj, h.taylor_of_two_unit_left,
        negOnePowCast_eq_intCast, dite_eq_left (by omega)]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦ hterm p hp d hd]
  -- Each of the two families of terms is supported at a single pair `(p, d)`.
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- The Hochschild differential of a normalized cochain vanishes on a homogeneous word containing
the unit. -/
private theorem hochschildDifferential_of_tprod_eq_zero (h : 𝒜.StrictUnit e)
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q)
    (hFe : degenerateWords R A e ≤ LinearMap.ker F) {n : ℕ} (x : Fin (n + 1) → A)
    (𝒟 : Fin (n + 1) → ℤ) (hx : ∀ i, x i ∈ (𝒜.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1))
    (hj : x j = e) (h𝒟j : 𝒟 j = -1) :
    𝒜.hochschildDifferential q F (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x)) = 0 := by
  have hjn := j.isLt
  rw [hochschildDifferential_eq_brace_sub, LinearMap.sub_apply, LinearMap.smul_apply, brace_def,
    brace_def, LinearMap.comp_apply, LinearMap.comp_apply, ← barDifferential_def,
    taylor_gradedCoderiv_of_tprod h hFe x 𝒟 hx j hj h𝒟j,
    apply_barDifferential_of_tprod h hFe x 𝒟 hx j hj]
  -- The partial sums of the degrees of the letters.
  set S : ℕ → ℤ := fun p ↦ ∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0
    with hS
  have hSsucc (p : ℕ) (hp : p < n + 1) : S (p + 1) = S p + 𝒟 ⟨p, hp⟩ := by
    simp only [hS, Finset.sum_range_succ, dite_eq_left hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos j.1 with hj0 | hj0
  · -- A unit in the first position: the collapse `m₂(e, F(⋯))` cancels that of `[e, a]`.
    have hW : splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0) =
        subword R x 1 n := by
      rw [dite_eq_left (by omega)]
      exact splice_two_succ_eq_subword R hn hj0 x
    simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero]
    rw [hW, hj0, Finset.sum_range_zero, negOnePowCast_zero, one_smul, sub_self]
  rcases Nat.lt_or_ge j.1 n with hjlt | hjge
  · -- An interior unit: the collapses of `[a, e]` and `[e, a]` cancel.
    have hW : splice R x 0 (n + 1) j.1 2 (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0) =
        splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩) := by
      rw [dite_eq_left (by omega)]
      exact splice_two_succ_eq_splice_two_pred R hj0 hjlt x
    simp (disch := omega) only [ite_eq_right, ite_eq_left, add_zero]
    rw [hW, smul_smul, ← negOnePowCast_add, ← add_smul]
    have hsign : negOnePowCast R (S j.1) +
        negOnePowCast R (S (j.1 - 1) + (𝒟 ⟨j.1 - 1, by omega⟩ + 1)) = 0 := by
      have := hSsucc (j.1 - 1) (by omega)
      rw [Nat.sub_add_cancel hj0] at this
      rw [this, ← add_assoc, negOnePowCast_add (R := R) _ 1, negOnePowCast_one, mul_neg_one,
        add_neg_cancel]
    simp only [hS] at hsign
    rw [hsign, zero_smul, smul_zero, sub_zero]
  · -- A unit in the last position: the collapse `m₂(F(⋯), e)` cancels that of `[a, e]`.
    obtain hjn' : j.1 = n := by omega
    have hW : splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩) = subword R x 0 n :=
      splice_two_pred_eq_subword R hn (by omega) x
    -- The value of `F` on the first `n` letters has degree `S n + q` after suspension.
    have hdeg : F (subword R x 0 n) ∈ 𝒜.grading.piece (S n + q + 1) := by
      have hsub := subword_mem_gradedPiece x (fun i ↦ if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0)
        (fun i ↦ by simpa only [Fin.is_lt, dite_true, Fin.eta] using hx i) 0 n (by omega)
      simpa [InternalGrading.shift_piece, hS] using hF.map_mem hsub
    simp (disch := omega) only [ite_eq_right, ite_eq_left, zero_add]
    rw [hW, smul_smul, ← negOnePowCast_add, 𝒜.grading.koszulTwist_one_apply_of_mem hdeg,
      ← negOnePowCast_eq_intCast, smul_smul, ← negOnePowCast_add, ← sub_smul]
    have hSn : S n = S (j.1 - 1) + 𝒟 ⟨j.1 - 1, by omega⟩ := by
      rw [← hSsucc]
      congr 1
      omega
    -- The two coefficients agree: both are `(-1)^(S n + q + 1)`.
    convert zero_smul R (F (subword R x 0 n)) using 2
    rw [sub_eq_zero]
    congr 1
    simp only [hS] at hSn ⊢
    rw [hSn]
    ring

/-- **The Hochschild differential preserves normalized cochains.**  If `e` is a strict unit and
the cochain `F` of degree `q` vanishes on every word containing `e`, so does its Hochschild
differential `[m, F]`. -/
theorem degenerateWords_le_ker_hochschildDifferential (h : 𝒜.StrictUnit e)
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q)
    (hFe : degenerateWords R A e ≤ LinearMap.ker F) :
    degenerateWords R A e ≤ LinearMap.ker (𝒜.hochschildDifferential q F) := by
  rw [degenerateWords_le_iff_of_mem_piece _ h.mem_shift_one_piece]
  rintro ⟨_ | n, hN⟩ x 𝒟 j hx hj h𝒟j
  · omega
  · exact h.hochschildDifferential_of_tprod_eq_zero hF hFe x 𝒟 hx j hj h𝒟j

end StrictUnit

/-! ### The normalized Hochschild complex -/

namespace PositiveHochschild

variable (𝒜) in
/-- The **normalized** cochains of degree `p` relative to `e`: the positive-arity suspended
Hochschild cochains of degree `p` which vanish on every word one of whose letters is `e`. -/
def normalizedCochains (e : A) (p : ℤ) : Submodule R (cochains 𝒜 p) :=
  (LinearMap.ker (LinearMap.lcomp R A (degenerateWords R A e).subtype)).comap
    (cochains 𝒜 p).subtype

/-- A cochain is normalized exactly when it vanishes on the degenerate words. -/
@[simp]
theorem mem_normalizedCochains {p : ℤ} {F : cochains 𝒜 p} :
    F ∈ normalizedCochains 𝒜 e p ↔
      degenerateWords R A e ≤ LinearMap.ker (F : ReducedTensorWords R A →ₗ[R] A) := by
  rw [normalizedCochains, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.lcomp_apply']
  constructor
  · intro hF z hz
    exact LinearMap.congr_fun hF ⟨z, hz⟩
  · intro hF
    ext ⟨z, hz⟩
    exact hF hz

/-- The Hochschild differential of a strictly unital `A∞` algebra restricted to normalized
cochains. -/
def normalizedD (h : 𝒜.StrictUnit e) (p q : ℤ) (hpq : p + 1 = q) :
    normalizedCochains 𝒜 e p →ₗ[R] normalizedCochains 𝒜 e q :=
  (d 𝒜 p q hpq).restrict fun F hF ↦ by
    rw [mem_normalizedCochains, coe_d]
    exact h.degenerateWords_le_ker_hochschildDifferential ((mem_cochains 𝒜).mp F.2)
      (mem_normalizedCochains.mp hF)

@[simp]
theorem coe_normalizedD (h : 𝒜.StrictUnit e) (p q : ℤ) (hpq : p + 1 = q)
    (F : normalizedCochains 𝒜 e p) :
    (normalizedD h p q hpq F : cochains 𝒜 q) = d 𝒜 p q hpq F := (rfl)

/-- The normalized Hochschild differential squares to zero. -/
@[simp]
theorem normalizedD_normalizedD (h : 𝒜.StrictUnit e) (p q r : ℤ) (hpq : p + 1 = q)
    (hqr : q + 1 = r) (F : normalizedCochains 𝒜 e p) :
    normalizedD h q r hqr (normalizedD h p q hpq F) = 0 := by
  ext1
  simp

variable (𝒜) in
/-- The **normalized Hochschild complex** of a strictly unital `A∞` algebra: the normalized
positive-arity suspended Hochschild cochains, with differential `[m, -]`. -/
abbrev normalizedComplex (h : 𝒜.StrictUnit e) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (normalizedCochains 𝒜 e p))
    (fun p ↦ ModuleCat.ofHom (normalizedD h p (p + 1) rfl)) (fun p ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext (normalizedD_normalizedD h p (p + 1) (p + 1 + 1) rfl rfl))

/-- The adjacent differential of the normalized complex is the normalized Hochschild
differential. -/
@[simp]
theorem normalizedComplex_d (h : 𝒜.StrictUnit e) (p q : ℤ) (hpq : p + 1 = q) :
    (normalizedComplex 𝒜 h).d p q = ModuleCat.ofHom (normalizedD h p q hpq) := by
  subst q
  exact CochainComplex.of_d (fun p ↦ ModuleCat.of R (normalizedCochains 𝒜 e p))
    (fun p ↦ ModuleCat.ofHom (normalizedD h p (p + 1) rfl)) p

variable (𝒜) in
/-- The inclusion of the normalized Hochschild complex into the positive-arity Hochschild
complex. -/
def normalizedComplexι (h : 𝒜.StrictUnit e) : normalizedComplex 𝒜 h ⟶ complex 𝒜 :=
  CochainComplex.ofHom (fun p ↦ ModuleCat.ofHom (normalizedCochains 𝒜 e p).subtype) fun p ↦ by
    rw [complex_d 𝒜 p (p + 1) rfl, normalizedComplex_d h p (p + 1) rfl]
    rfl

@[simp]
theorem normalizedComplexι_f_apply (h : 𝒜.StrictUnit e) (p : ℤ)
    (F : normalizedCochains 𝒜 e p) : (normalizedComplexι 𝒜 h).f p F = F := (rfl)

instance (h : 𝒜.StrictUnit e) : CategoryTheory.Mono (normalizedComplexι 𝒜 h) := by
  refine HomologicalComplex.mono_of_mono_f _ fun p ↦ ?_
  rw [ModuleCat.mono_iff_injective]
  exact Subtype.val_injective

/-- The Gerstenhaber bracket of normalized cochains, relative to a homogeneous element `e`, is
normalized. -/
def normalizedBracket {E : ℤ} (he : e ∈ 𝒜.grading.piece E) {p q n : ℤ} (hn : p + q = n) :
    normalizedCochains 𝒜 e p →ₗ[R] normalizedCochains 𝒜 e q →ₗ[R] normalizedCochains 𝒜 e n :=
  LinearMap.mk₂ R
    (fun F G ↦ ⟨bracket 𝒜 hn F G, by
      rw [mem_normalizedCochains, coe_bracket]
      exact degenerateWords_le_ker_gerstenhaberBracket _ p q
        (E := E - 1) (by rwa [InternalGrading.shift_piece, sub_add_cancel])
        (mem_normalizedCochains.mp F.2) (mem_normalizedCochains.mp G.2)⟩)
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))
    (fun _ _ _ ↦ Subtype.ext (by simp))

@[simp]
theorem coe_normalizedBracket {E : ℤ} (he : e ∈ 𝒜.grading.piece E) {p q n : ℤ} (hn : p + q = n)
    (F : normalizedCochains 𝒜 e p) (G : normalizedCochains 𝒜 e q) :
    (normalizedBracket he hn F G : cochains 𝒜 n) = bracket 𝒜 hn F G := (rfl)

end PositiveHochschild

end TauCeti.AInfinityAlgebra
