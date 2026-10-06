/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.QuadraticForm.Real
import TauCeti.Algebra.Quaternion.Split
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

/-!
# The real Clifford algebras `Cliff(p, q)` and the base entries of the Bott table

Over `ℂ` a nondegenerate quadratic form is determined by its rank, so there is one Clifford algebra
in each dimension. Over `ℝ` this fails: a nondegenerate real form is classified by its signature
`(p, q)`, and the resulting algebras `Cliff(p, q)` run through matrix algebras over `ℝ`, `ℂ` and
`ℍ` in a pattern periodic modulo `8`. This file introduces the family of forms that the pattern is
indexed by, the coordinate isometries for switching signatures, and the four small entries that
fix the indexing convention.

`TauCeti.realCliffordForm p q` is the diagonal form on `Fin (p + q) → ℝ` with `+1` in the first `p`
coordinates and `-1` in the last `q`, written as a `QuadraticMap.weightedSumSquares` against the
sign vector `TauCeti.realCliffordWeight p q`. It is nondegenerate
(`TauCeti.nondegenerate_realCliffordForm`), and its Clifford algebra has dimension `2 ^ (p + q)`
(`TauCeti.finrank_cliffordAlgebra_realCliffordForm`).
The compact form `realCliffordForm n 0` is positive definite
(`TauCeti.posDef_realCliffordForm_zero`) and equals the standard sum-of-squares form
(`TauCeti.realCliffordForm_zero_eq_weightedSumSquares_one`).
Negating the form swaps the two signature indices through
`TauCeti.realCliffordFormNegIsometry`; its coordinate action is given by
`TauCeti.realCliffordFormNegIsometry_pos_of_neg` and
`TauCeti.realCliffordFormNegIsometry_neg_of_pos`.

The sign convention — generators of the *first* `p` coordinates square to `+1` — is not universal:
sources that make the first generators square to `-1` index the periodicity table by
`(p - q) mod 8` where this one uses `(q - p) mod 8`. The convention is therefore fixed here by
four explicit small identifications:

* `Cliff(1,0) ≅ ℝ × ℝ` — `TauCeti.realCliffordOneZeroEquivProd`;
* `Cliff(0,1) ≅ ℂ` — `TauCeti.realCliffordZeroOneEquivComplex`;
* `Cliff(0,2) ≅ ℍ` — `TauCeti.realCliffordZeroTwoEquivQuaternion`;
* `Cliff(1,1) ≅ M₂(ℝ)` — `TauCeti.realCliffordOneOneEquivMatrix`.

The middle two are Mathlib's `CliffordAlgebraComplex.equiv` and `CliffordAlgebraQuaternion.equiv`
transported along an isometry, since the forms Mathlib uses there are exactly the `(0,1)` and
`(0,2)` signature forms in disguise. The last is the same transport for the split quaternions
`ℍ[ℝ,1,-1]`, followed by their splitting `TauCeti.QuaternionAlgebra.oneEquivMatrix`. The first is
built here from the universal property: a single generator squaring to `+1` splits the algebra into
two copies of `ℝ`. The constructed algebra map is proved *surjective* by exhibiting explicit
preimages, and injectivity is then forced by the dimension count `2 ^ (p + q)`, which is the general
mechanism the complex structure theorem uses as well.

## Implementation notes

`Cliff(p, q)` is spelled `CliffordAlgebra (realCliffordForm p q)` throughout rather than being
given an abbreviation, so that every lemma about a general `CliffordAlgebra` applies to it without
unfolding.

Most scaffolding of the four constructions remains `private`. The one- and two-dimensional
coordinate isometries are public because later low-dimensional reductions compose them, while the
public algebra interface consists of the four `AlgEquiv`s and the lemmas computing them on a
generator.

All four identifications are bundled `AlgEquiv`s rather than the `Nonempty` existence statements
the roadmap asks for, and each comes with a lemma computing it on a generator: it is the
equivalences and their values, not their bare existence, that the Bott-periodicity step
`Cliff(p+1, q+1) ≅ Cliff(p, q) ⊗ M₂(ℝ)` will consume.

## Main definitions

* `TauCeti.realCliffordWeight` and `TauCeti.realCliffordForm`: the signature `(p, q)` sign vector
  and the diagonal real quadratic form it weights.
* `TauCeti.realCliffordFormNegIsometry`: the isometry from the negated `(p, q)` form to the
  `(q, p)` form, with coordinate equations `..._pos_of_neg` and `..._neg_of_pos`.
* `TauCeti.realCliffordSplitIsometry`: the shared splitter into two standard signature blocks.
* `TauCeti.realCliffordPositiveSplitIsometry`: the isometry which separates the last positive
  coordinate from a standard signature form.
* `TauCeti.realBottSplitIsometry`: the two-coordinate specialization of the same signature
  splitter, separating a hyperbolic plane.
* `TauCeti.realCliffordSignSwitchStandardIsometry`: the isometry which puts a sign-switched form
  with one positive line back into standard signature coordinates.
* `TauCeti.realCliffordZeroOneIsometry` and `TauCeti.realCliffordZeroTwoIsometry`: the coordinate
  isometries used in the complex and quaternion base entries.
* `TauCeti.realCliffordOneZeroEquivProd`, `TauCeti.realCliffordZeroOneEquivComplex`,
  `TauCeti.realCliffordZeroTwoEquivQuaternion`, `TauCeti.realCliffordOneOneEquivMatrix`: the four
  base entries of the Bott table, each with a `..._ι` lemma computing it on a generator.

## Main results

* `TauCeti.equivalent_realSignatureForm_realCliffordForm`: the orthogonal-sum and coordinate
  presentations of the real normal form are isometric.
* `TauCeti.nondegenerate_realCliffordForm`: the signature forms are nondegenerate.
* `TauCeti.realCliffordForm_zero_eq_weightedSumSquares_one`: the compact signature form is the
  standard real sum-of-squares form.
* `TauCeti.finrank_cliffordAlgebra_realCliffordForm`:
  `finrank ℝ (CliffordAlgebra (realCliffordForm p q)) = 2 ^ (p + q)`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 7, "The real forms `Cliff(p, q)`".
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter I, §4.
-/

public section

open Module QuadraticMap

open scoped Quaternion

namespace TauCeti

/-! ### The real quadratic form of a signature -/

/-- The sign vector of signature `(p, q)`: `+1` on the first `p` coordinates of `Fin (p + q)` and
`-1` on the last `q`. -/
def realCliffordWeight (p q : ℕ) (i : Fin (p + q)) : ℝ := if (i : ℕ) < p then 1 else -1

/-- The real quadratic form of signature `(p, q)`: the diagonal form
`x ↦ ∑ᵢ₌₀^{p-1} xᵢ² - ∑ᵢ₌ₚ^{p+q-1} xᵢ²` on `Fin (p + q) → ℝ`. Its Clifford algebra is the real
Clifford algebra `Cliff(p, q)`. -/
def realCliffordForm (p q : ℕ) : QuadraticForm ℝ (Fin (p + q) → ℝ) :=
  weightedSumSquares ℝ (realCliffordWeight p q)

/-- The coordinate signature form is the weighted sum of squares for `realCliffordWeight`. -/
theorem realCliffordForm_def (p q : ℕ) :
    realCliffordForm p q = weightedSumSquares ℝ (realCliffordWeight p q) := (rfl)

@[simp]
theorem realCliffordWeight_of_lt {p q : ℕ} {i : Fin (p + q)} (hi : (i : ℕ) < p) :
    realCliffordWeight p q i = 1 :=
  ite_eq_left hi

@[simp]
theorem realCliffordWeight_of_le {p q : ℕ} {i : Fin (p + q)} (hi : p ≤ (i : ℕ)) :
    realCliffordWeight p q i = -1 :=
  ite_eq_right (not_lt.2 hi)

/-- The orthogonal-sum and coordinate presentations of the real normal form of signature `(p, q)`
are isometric. -/
theorem equivalent_realSignatureForm_realCliffordForm (p q : ℕ) :
    (_root_.QuadraticForm.realSignatureForm p q).Equivalent (realCliffordForm p q) := by
  have hweight : realCliffordWeight p q ∘ finSumFinEquiv =
      Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1 := by
    funext x
    cases x <;> simp
  rw [_root_.QuadraticForm.realSignatureForm_def, realCliffordForm_def]
  exact _root_.QuadraticForm.equivalent_weightedSumSquares_of_comp_eq finSumFinEquiv hweight

@[simp]
theorem realCliffordWeight_mul_self (p q : ℕ) (i : Fin (p + q)) :
    realCliffordWeight p q i * realCliffordWeight p q i = 1 := by
  unfold realCliffordWeight
  split <;> norm_num

@[simp]
theorem realCliffordWeight_ne_zero (p q : ℕ) (i : Fin (p + q)) :
    realCliffordWeight p q i ≠ 0 := by
  intro h
  simpa [h] using realCliffordWeight_mul_self p q i

@[simp]
theorem realCliffordForm_apply (p q : ℕ) (v : Fin (p + q) → ℝ) :
    realCliffordForm p q v = ∑ i, realCliffordWeight p q i * (v i * v i) := by
  simp [realCliffordForm]

/-- The positive-definite signature form is the standard real sum-of-squares form. -/
theorem realCliffordForm_zero_eq_weightedSumSquares_one (n : ℕ) :
    realCliffordForm n 0 = weightedSumSquares ℝ (1 : Fin n → ℝ) := by
  ext x
  simp only [realCliffordForm_apply, weightedSumSquares_apply, Pi.one_apply, one_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [realCliffordWeight_of_lt (by omega), one_mul]

/-- The signature forms are nondegenerate: a weighted sum of squares whose weights are all regular
is nondegenerate, and every signature weight is `±1`. -/
theorem nondegenerate_realCliffordForm (p q : ℕ) : (realCliffordForm p q).Nondegenerate :=
  QuadraticMap.nondegenerate_weightedSumSquares fun i ↦
    (realCliffordWeight_ne_zero p q i).isUnit.isRegular

/-- The standard signature form with no negative coordinates is positive definite. -/
theorem posDef_realCliffordForm_zero (n : ℕ) : (realCliffordForm n 0).PosDef := by
  intro v hv
  rw [realCliffordForm_apply]
  refine Finset.sum_pos' (fun i _ ↦ ?_) ?_
  · rw [realCliffordWeight_of_lt (by omega), one_mul]
    exact mul_self_nonneg (v i)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [realCliffordWeight_of_lt (by omega), one_mul]
    exact mul_self_pos.mpr hi

/-- Every coordinate unit vector has value one for the compact real Clifford form. -/
@[simp]
theorem realCliffordForm_zero_single_one (n : ℕ) (i : Fin n) :
    realCliffordForm n 0 (Pi.single i 1) = 1 := by
  classical
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  rw [QuadraticMap.weightedSumSquares_apply]
  simp only [Pi.one_apply, one_smul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The real Clifford algebra of signature `(p, q)` has dimension `2 ^ (p + q)`, as every Clifford
algebra of a space of that dimension does. This is the count that forces the surjections built
below to be isomorphisms. -/
@[simp]
theorem finrank_cliffordAlgebra_realCliffordForm (p q : ℕ) :
    finrank ℝ (CliffordAlgebra (realCliffordForm p q)) = 2 ^ (p + q) := by
  rw [CliffordAlgebra.finrank_eq_two_pow, Module.finrank_pi, Fintype.card_fin]

private theorem neg_realCliffordWeight_finAddFlip (p q : ℕ) (i : Fin (q + p)) :
    -realCliffordWeight p q (finAddFlip i) = realCliffordWeight q p i := by
  induction i using Fin.addCases <;> simp [realCliffordWeight]

/-- Negating a real signature form swaps its positive and negative coordinates. -/
def realCliffordFormNegIsometry (p q : ℕ) :
    (-(realCliffordForm p q)).IsometryEquiv (realCliffordForm q p) where
  __ := LinearEquiv.funCongrLeft ℝ ℝ finAddFlip
  map_app' x := by
    rw [realCliffordForm_apply, neg_apply, realCliffordForm_apply, ← Finset.sum_neg_distrib,
      ← (finAddFlip : Fin (q + p) ≃ Fin (p + q)).sum_comp]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← neg_realCliffordWeight_finAddFlip, neg_mul, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- `realCliffordFormNegIsometry` reads each coordinate through the block swap `finAddFlip`. -/
@[simp]
theorem realCliffordFormNegIsometry_apply (p q : ℕ) (x : Fin (p + q) → ℝ) (i : Fin (q + p)) :
    realCliffordFormNegIsometry p q x i = x (finAddFlip i) := by
  simp [realCliffordFormNegIsometry, ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Negated negative coordinates become positive coordinates under
`realCliffordFormNegIsometry`. -/
theorem realCliffordFormNegIsometry_pos_of_neg (p q : ℕ)
    (x : Fin (p + q) → ℝ) (i : Fin q) :
    realCliffordFormNegIsometry p q x (Fin.castAdd p i) = x (Fin.natAdd p i) := by
  rw [realCliffordFormNegIsometry_apply, finAddFlip_apply_castAdd]

/-- Negated positive coordinates become negative coordinates under
`realCliffordFormNegIsometry`. -/
theorem realCliffordFormNegIsometry_neg_of_pos (p q : ℕ)
    (x : Fin (p + q) → ℝ) (i : Fin p) :
    realCliffordFormNegIsometry p q x (Fin.natAdd q i) = x (Fin.castAdd q i) := by
  rw [realCliffordFormNegIsometry_apply, finAddFlip_apply_natAdd]

/-! ### Standard signature coordinate isometries -/

private def realCliffordSplitIndexEquiv (p₁ p₂ q₁ q₂ : ℕ) :
    Fin ((p₁ + p₂) + (q₁ + q₂)) ≃ Fin (p₁ + q₁) ⊕ Fin (p₂ + q₂) :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm) |>.trans
    (Equiv.sumSumSumComm (Fin p₁) (Fin p₂) (Fin q₁) (Fin q₂)) |>.trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

private def realCliffordSplitLinearEquiv (p₁ p₂ q₁ q₂ : ℕ) :
    (Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) ≃ₗ[ℝ]
      (Fin (p₁ + q₁) → ℝ) × (Fin (p₂ + q₂) → ℝ) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin ((p₁ + p₂) + (q₁ + q₂)) ↦ ℝ)
      (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ)

private theorem realCliffordSplitIndexEquiv_symm_inl_pos
    (p₁ p₂ q₁ q₂ : ℕ) (i : Fin p₁) :
    (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm
        (Sum.inl (finSumFinEquiv (Sum.inl i))) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) := by
  simp [realCliffordSplitIndexEquiv]

private theorem realCliffordSplitIndexEquiv_symm_inl_neg
    (p₁ p₂ q₁ q₂ : ℕ) (i : Fin q₁) :
    (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm
        (Sum.inl (finSumFinEquiv (Sum.inr i))) =
      finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))) := by
  simp [realCliffordSplitIndexEquiv]

private theorem realCliffordSplitIndexEquiv_symm_inr_pos
    (p₁ p₂ q₁ q₂ : ℕ) (i : Fin p₂) :
    (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm
        (Sum.inr (finSumFinEquiv (Sum.inl i))) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) := by
  simp [realCliffordSplitIndexEquiv]

private theorem realCliffordSplitIndexEquiv_symm_inr_neg
    (p₁ p₂ q₁ q₂ : ℕ) (i : Fin q₂) :
    (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm
        (Sum.inr (finSumFinEquiv (Sum.inr i))) =
      finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))) := by
  simp [realCliffordSplitIndexEquiv]

private theorem realCliffordSplitWeight_inl (p₁ p₂ q₁ q₂ : ℕ)
    (i : Fin (p₁ + q₁)) :
    realCliffordWeight (p₁ + p₂) (q₁ + q₂)
        ((realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm (Sum.inl i)) =
      realCliffordWeight p₁ q₁ i := by
  rw [← finSumFinEquiv.apply_symm_apply i]
  rcases finSumFinEquiv.symm i with i | i
  · have hi : (i : ℕ) < p₁ + p₂ := by omega
    simp [realCliffordSplitIndexEquiv, realCliffordWeight, hi]
  · simp [realCliffordSplitIndexEquiv, realCliffordWeight]

private theorem realCliffordSplitWeight_inr (p₁ p₂ q₁ q₂ : ℕ)
    (i : Fin (p₂ + q₂)) :
    realCliffordWeight (p₁ + p₂) (q₁ + q₂)
        ((realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm (Sum.inr i)) =
      realCliffordWeight p₂ q₂ i := by
  rw [← finSumFinEquiv.apply_symm_apply i]
  rcases finSumFinEquiv.symm i with i | i
  · simp [realCliffordSplitIndexEquiv, realCliffordWeight]
  · simp [realCliffordSplitIndexEquiv, realCliffordWeight]

private theorem realCliffordSplitLinearEquiv_fst (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin (p₁ + q₁)) :
    (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).1 i =
      x ((realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm (Sum.inl i)) := by
  simp [realCliffordSplitLinearEquiv]

private theorem realCliffordSplitLinearEquiv_snd (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin (p₂ + q₂)) :
    (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).2 i =
      x ((realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm (Sum.inr i)) := by
  simp [realCliffordSplitLinearEquiv]

/-- Splits a standard real signature form into two standard signature blocks. -/
def realCliffordSplitIsometry (p₁ p₂ q₁ q₂ : ℕ) :
    (realCliffordForm (p₁ + p₂) (q₁ + q₂)).IsometryEquiv
      ((realCliffordForm p₁ q₁).prod (realCliffordForm p₂ q₂)) :=
  { realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ with
    map_app' := by
      intro x
      rw [QuadraticMap.prod_apply, realCliffordForm_apply, realCliffordForm_apply,
        realCliffordForm_apply]
      let y := realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x
      calc
        (∑ i, realCliffordWeight p₁ q₁ i * (y.1 i * y.1 i)) +
            ∑ i, realCliffordWeight p₂ q₂ i * (y.2 i * y.2 i) =
          ∑ s : Fin (p₁ + q₁) ⊕ Fin (p₂ + q₂), Sum.elim
            (fun i => realCliffordWeight p₁ q₁ i * (y.1 i * y.1 i))
            (fun i => realCliffordWeight p₂ q₂ i * (y.2 i * y.2 i)) s :=
              (Fintype.sum_sum_type (Sum.elim
                (fun i => realCliffordWeight p₁ q₁ i * (y.1 i * y.1 i))
                (fun i => realCliffordWeight p₂ q₂ i * (y.2 i * y.2 i)))).symm
        _ = ∑ i, realCliffordWeight (p₁ + p₂) (q₁ + q₂) i * (x i * x i) := by
          refine Fintype.sum_equiv (realCliffordSplitIndexEquiv p₁ p₂ q₁ q₂).symm _ _ ?_
          rintro (i | i)
          · simp [y, realCliffordSplitLinearEquiv, realCliffordSplitWeight_inl]
          · simp [y, realCliffordSplitLinearEquiv, realCliffordSplitWeight_inr] }

/-- The first output block receives the first positive-coordinate block. -/
@[simp]
theorem realCliffordSplitIsometry_fst_pos (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin p₁) :
    (realCliffordSplitIsometry p₁ p₂ q₁ q₂ x).1 (Fin.castAdd q₁ i) =
      x (Fin.castAdd (q₁ + q₂) (Fin.castAdd p₂ i)) := by
  -- The bundled-isometry coercion does not expose the underlying linear equivalence with `dsimp`.
  change (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).1 _ = _
  rw [realCliffordSplitLinearEquiv_fst, ← finSumFinEquiv_apply_left,
    realCliffordSplitIndexEquiv_symm_inl_pos]
  congr 1

/-- The first output block receives the first negative-coordinate block. -/
@[simp]
theorem realCliffordSplitIsometry_fst_neg (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin q₁) :
    (realCliffordSplitIsometry p₁ p₂ q₁ q₂ x).1 (Fin.natAdd p₁ i) =
      x (Fin.natAdd (p₁ + p₂) (Fin.castAdd q₂ i)) := by
  -- The bundled-isometry coercion does not expose the underlying linear equivalence with `dsimp`.
  change (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).1 _ = _
  rw [realCliffordSplitLinearEquiv_fst, ← finSumFinEquiv_apply_right,
    realCliffordSplitIndexEquiv_symm_inl_neg]
  congr 1

/-- The second output block receives the second positive-coordinate block. -/
@[simp]
theorem realCliffordSplitIsometry_snd_pos (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin p₂) :
    (realCliffordSplitIsometry p₁ p₂ q₁ q₂ x).2 (Fin.castAdd q₂ i) =
      x (Fin.castAdd (q₁ + q₂) (Fin.natAdd p₁ i)) := by
  -- The bundled-isometry coercion does not expose the underlying linear equivalence with `dsimp`.
  change (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).2 _ = _
  rw [realCliffordSplitLinearEquiv_snd, ← finSumFinEquiv_apply_left,
    realCliffordSplitIndexEquiv_symm_inr_pos]
  congr 1

/-- The second output block receives the second negative-coordinate block. -/
@[simp]
theorem realCliffordSplitIsometry_snd_neg (p₁ p₂ q₁ q₂ : ℕ)
    (x : Fin ((p₁ + p₂) + (q₁ + q₂)) → ℝ) (i : Fin q₂) :
    (realCliffordSplitIsometry p₁ p₂ q₁ q₂ x).2 (Fin.natAdd p₂ i) =
      x (Fin.natAdd (p₁ + p₂) (Fin.natAdd q₁ i)) := by
  -- The bundled-isometry coercion does not expose the underlying linear equivalence with `dsimp`.
  change (realCliffordSplitLinearEquiv p₁ p₂ q₁ q₂ x).2 _ = _
  rw [realCliffordSplitLinearEquiv_snd, ← finSumFinEquiv_apply_right,
    realCliffordSplitIndexEquiv_symm_inr_neg]
  congr 1

private def realCliffordOnePositiveIsometry :
    (realCliffordForm 1 0).IsometryEquiv (QuadraticMap.sq (R := ℝ) (A := ℝ)) :=
  { LinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ) with
    map_app' := by
      intro x
      rw [QuadraticMap.sq_apply, realCliffordForm_apply, Fin.sum_univ_one]
      simp [realCliffordWeight] }

/-- The coordinate isometry which splits the last positive coordinate from a real signature. -/
def realCliffordPositiveSplitIsometry (p q : ℕ) :
    (realCliffordForm (p + 1) q).IsometryEquiv
      ((realCliffordForm p q).prod (QuadraticMap.sq (R := ℝ) (A := ℝ))) :=
  (realCliffordSplitIsometry p 1 q 0).trans
    ((QuadraticMap.IsometryEquiv.refl (realCliffordForm p q)).prod
      realCliffordOnePositiveIsometry)

/-- The positive coordinates retained by `realCliffordPositiveSplitIsometry`. -/
@[simp]
theorem realCliffordPositiveSplitIsometry_fst_pos (p q : ℕ)
    (v : Fin ((p + 1) + q) → ℝ) (i : Fin p) :
    (realCliffordPositiveSplitIsometry p q v).1 (Fin.castAdd q i) =
      v (Fin.castAdd q i.castSucc) := by
  -- The composed-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 1 q 0 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_pos]
  congr 1

/-- The negative coordinates retained by `realCliffordPositiveSplitIsometry`. -/
@[simp]
theorem realCliffordPositiveSplitIsometry_fst_neg (p q : ℕ)
    (v : Fin ((p + 1) + q) → ℝ) (i : Fin q) :
    (realCliffordPositiveSplitIsometry p q v).1 (Fin.natAdd p i) =
      v (Fin.natAdd (p + 1) i) := by
  -- The composed-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 1 q 0 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_neg]
  congr 1

/-- The last positive coordinate extracted by `realCliffordPositiveSplitIsometry`. -/
@[simp]
theorem realCliffordPositiveSplitIsometry_snd (p q : ℕ)
    (v : Fin ((p + 1) + q) → ℝ) :
    (realCliffordPositiveSplitIsometry p q v).2 =
      v (Fin.castAdd q (Fin.last p)) := by
  -- The composed-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 1 q 0 v).2 0 = _
  convert realCliffordSplitIsometry_snd_pos p 1 q 0 v (0 : Fin 1) using 1 <;>
    congr

/-- The coordinate isometry which separates the last positive and negative coordinates of the
signature form as a hyperbolic plane. -/
def realBottSplitIsometry (p q : ℕ) :
    (realCliffordForm (p + 1) (q + 1)).IsometryEquiv
      ((realCliffordForm p q).prod (realCliffordForm 1 1)) :=
  realCliffordSplitIsometry p 1 q 1

/-- The positive coordinates retained by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_fst_pos (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) (i : Fin p) :
    (realBottSplitIsometry p q v).1 (Fin.castAdd q i) =
      v (Fin.castAdd (q + 1) i.castSucc) := by
  -- The bundled-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 1 q 1 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_pos]
  congr 1

/-- The negative coordinates retained by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_fst_neg (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) (i : Fin q) :
    (realBottSplitIsometry p q v).1 (Fin.natAdd p i) =
      v (Fin.natAdd (p + 1) i.castSucc) := by
  -- The bundled-isometry coercion does not expose the shared splitter with `dsimp`.
  change (realCliffordSplitIsometry p 1 q 1 v).1 _ = _
  rw [realCliffordSplitIsometry_fst_neg]
  congr 1

/-- The last positive coordinate extracted by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_snd_zero (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) :
    (realBottSplitIsometry p q v).2 0 =
      v (Fin.castAdd (q + 1) (Fin.last p)) := by
  convert realCliffordSplitIsometry_snd_pos p 1 q 1 v (0 : Fin 1) using 1 <;>
    congr

/-- The last negative coordinate extracted by `realBottSplitIsometry`. -/
@[simp]
theorem realBottSplitIsometry_snd_one (p q : ℕ)
    (v : Fin ((p + 1) + (q + 1)) → ℝ) :
    (realBottSplitIsometry p q v).2 1 =
      v (Fin.natAdd (p + 1) (Fin.last q)) := by
  convert realCliffordSplitIsometry_snd_neg p 1 q 1 v (0 : Fin 1) using 1 <;>
    congr

/-- The coordinate isometry which turns the sign-switched form into the standard signature. -/
def realCliffordSignSwitchStandardIsometry (p q : ℕ) :
    ((-(realCliffordForm p q)).prod (QuadraticMap.sq (R := ℝ) (A := ℝ))).IsometryEquiv
      (realCliffordForm (q + 1) p) :=
  ((realCliffordFormNegIsometry p q).prod
    (QuadraticMap.IsometryEquiv.refl (QuadraticMap.sq (R := ℝ) (A := ℝ)))).trans
      (realCliffordPositiveSplitIsometry q p).symm

private theorem realCliffordSignSwitchStandardIsometry_split (p q : ℕ)
    (x : Fin (p + q) → ℝ) (r : ℝ) :
    realCliffordPositiveSplitIsometry q p
        (realCliffordSignSwitchStandardIsometry p q (x, r)) =
      (realCliffordFormNegIsometry p q x, r) := by
  rw [realCliffordSignSwitchStandardIsometry]
  exact (realCliffordPositiveSplitIsometry q p).apply_symm_apply _

/-- Negated negative coordinates become positive coordinates under
`realCliffordSignSwitchStandardIsometry`. -/
@[simp]
theorem realCliffordSignSwitchStandardIsometry_pos_of_neg (p q : ℕ)
    (x : Fin (p + q) → ℝ) (r : ℝ) (i : Fin q) :
    realCliffordSignSwitchStandardIsometry p q (x, r)
        (Fin.castAdd p (Fin.castSucc i)) = x (Fin.natAdd p i) := by
  have h := congrFun (congrArg Prod.fst (realCliffordSignSwitchStandardIsometry_split p q x r))
    (Fin.castAdd p i)
  simpa only [realCliffordPositiveSplitIsometry_fst_pos,
    realCliffordFormNegIsometry_pos_of_neg] using h

/-- The new positive line is the last positive coordinate under
`realCliffordSignSwitchStandardIsometry`. -/
@[simp]
theorem realCliffordSignSwitchStandardIsometry_last_pos (p q : ℕ)
    (x : Fin (p + q) → ℝ) (r : ℝ) :
    realCliffordSignSwitchStandardIsometry p q (x, r)
        (Fin.castAdd p (Fin.last q)) = r := by
  have h := congrArg Prod.snd (realCliffordSignSwitchStandardIsometry_split p q x r)
  simpa only [realCliffordPositiveSplitIsometry_snd] using h

/-- Negated positive coordinates become negative coordinates under
`realCliffordSignSwitchStandardIsometry`. -/
@[simp]
theorem realCliffordSignSwitchStandardIsometry_neg_of_pos (p q : ℕ)
    (x : Fin (p + q) → ℝ) (r : ℝ) (i : Fin p) :
    realCliffordSignSwitchStandardIsometry p q (x, r)
        (Fin.natAdd (q + 1) i) = x (Fin.castAdd q i) := by
  have h := congrFun (congrArg Prod.fst (realCliffordSignSwitchStandardIsometry_split p q x r))
    (Fin.natAdd q i)
  simpa only [realCliffordPositiveSplitIsometry_fst_neg,
    realCliffordFormNegIsometry_neg_of_pos] using h

/-! ### The four base entries, in coordinates -/

@[simp]
theorem realCliffordForm_one_zero_apply (v : Fin (1 + 0) → ℝ) :
    realCliffordForm 1 0 v = v 0 * v 0 := by
  rw [realCliffordForm_apply]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_zero_one_apply (v : Fin (0 + 1) → ℝ) :
    realCliffordForm 0 1 v = -(v 0 * v 0) := by
  rw [realCliffordForm_apply]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_zero_two_apply (v : Fin (0 + 2) → ℝ) :
    realCliffordForm 0 2 v = -(v 0 * v 0) + -(v 1 * v 1) := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_one_one_apply (v : Fin (1 + 1) → ℝ) :
    realCliffordForm 1 1 v = v 0 * v 0 - v 1 * v 1 := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  simp [realCliffordWeight]
  ring

/-! ### `Cliff(1,0) ≅ ℝ × ℝ` -/

/-- The algebra map `Cliff(1,0) → ℝ × ℝ` sending the generator `e` to `(1, -1)`. This is legitimate
because `(1, -1)` squares to `1 = Q e`, and it is the pair of the two characters `e ↦ 1` and
`e ↦ -1` of `ℝ[e]/(e² - 1)`. -/
private def realCliffordOneZeroToProd :
    CliffordAlgebra (realCliffordForm 1 0) →ₐ[ℝ] ℝ × ℝ :=
  CliffordAlgebra.lift _
    ⟨(LinearMap.proj 0).prod (-LinearMap.proj 0), fun v => by
      ext <;> simp [realCliffordForm_one_zero_apply]⟩

/-- The value of `realCliffordOneZeroToProd` on a generator. -/
private theorem realCliffordOneZeroToProd_ι (v : Fin (1 + 0) → ℝ) :
    realCliffordOneZeroToProd (CliffordAlgebra.ι _ v) = (v 0, -v 0) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- `realCliffordOneZeroToProd` is surjective: the two characters of `ℝ[e]/(e² - 1)` separate
`(1, 0)` and `(0, 1)`, so every pair is hit by an explicit combination of `1` and the generator.
With the dimension count `finrank_cliffordAlgebra_realCliffordForm` this makes it bijective. -/
private theorem realCliffordOneZeroToProd_surjective :
    Function.Surjective realCliffordOneZeroToProd := by
  rintro ⟨a, b⟩
  refine ⟨algebraMap ℝ _ ((a + b) / 2)
      + ((a - b) / 2) • CliffordAlgebra.ι (realCliffordForm 1 0) (Pi.single 0 1), ?_⟩
  ext <;> simp [realCliffordOneZeroToProd_ι] <;> ring

/-- `realCliffordOneZeroToProd` is bijective: it is surjective, and both sides have dimension `2`,
so surjectivity forces injectivity. -/
private theorem realCliffordOneZeroToProd_bijective :
    Function.Bijective realCliffordOneZeroToProd :=
  OrzechProperty.bijective_of_surjective_of_finrank_le realCliffordOneZeroToProd.toLinearMap
    realCliffordOneZeroToProd_surjective (by rw [finrank_cliffordAlgebra_realCliffordForm]; simp)

/-- **`Cliff(1,0) ≅ ℝ × ℝ`**, the first base entry of the real periodicity table: a single
generator squaring to `+1` splits the algebra. -/
noncomputable def realCliffordOneZeroEquivProd :
    CliffordAlgebra (realCliffordForm 1 0) ≃ₐ[ℝ] ℝ × ℝ :=
  AlgEquiv.ofBijective realCliffordOneZeroToProd realCliffordOneZeroToProd_bijective

/-- `realCliffordOneZeroEquivProd` sends the generator of the coordinate `v` to the pair
`(v 0, -v 0)`: the two characters of `ℝ[e]/(e² - 1)` read off the two components. -/
@[simp]
theorem realCliffordOneZeroEquivProd_ι (v : Fin (1 + 0) → ℝ) :
    realCliffordOneZeroEquivProd (CliffordAlgebra.ι _ v) = (v 0, -v 0) := by
  rw [realCliffordOneZeroEquivProd, AlgEquiv.ofBijective_apply, realCliffordOneZeroToProd_ι]

/-! ### `Cliff(0,1) ≅ ℂ` -/

/-- The signature `(0,1)` form is Mathlib's `CliffordAlgebraComplex.Q`, `r ↦ -r²`, read on the
one-dimensional space `Fin (0 + 1) → ℝ`. -/
def realCliffordZeroOneIsometry :
    (realCliffordForm 0 1).IsometryEquiv CliffordAlgebraComplex.Q :=
  ⟨(LinearEquiv.funUnique (Fin 1) ℝ ℝ : (Fin (0 + 1) → ℝ) ≃ₗ[ℝ] ℝ), fun v => by
    simp [realCliffordForm_zero_one_apply]⟩

/-- `realCliffordZeroOneIsometry` reads off the single coordinate. -/
@[simp]
theorem realCliffordZeroOneIsometry_apply (v : Fin (0 + 1) → ℝ) :
    realCliffordZeroOneIsometry v = v 0 := by
  simp [realCliffordZeroOneIsometry, ← IsometryEquiv.coe_toLinearEquiv,
    LinearEquiv.funUnique_apply]

/-- **`Cliff(0,1) ≅ ℂ`**, the second base entry of the real periodicity table: a single generator
squaring to `-1` is a square root of `-1`. -/
noncomputable def realCliffordZeroOneEquivComplex :
    CliffordAlgebra (realCliffordForm 0 1) ≃ₐ[ℝ] ℂ :=
  (CliffordAlgebra.equivOfIsometry realCliffordZeroOneIsometry).trans
    CliffordAlgebraComplex.equiv

/-- `realCliffordZeroOneEquivComplex` sends the generator of the coordinate `v` to the purely
imaginary complex number `v 0 • Complex.I`. -/
@[simp]
theorem realCliffordZeroOneEquivComplex_ι (v : Fin (0 + 1) → ℝ) :
    realCliffordZeroOneEquivComplex (CliffordAlgebra.ι _ v) = v 0 • Complex.I := by
  rw [realCliffordZeroOneEquivComplex, AlgEquiv.trans_apply, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  simp only [IsometryEquiv.toIsometry_apply, realCliffordZeroOneIsometry_apply,
    CliffordAlgebraComplex.equiv_apply, CliffordAlgebraComplex.toComplex_ι, Complex.real_smul]

/-! ### `Cliff(0,2) ≅ ℍ` -/

/-- The signature `(0,2)` form is Mathlib's `CliffordAlgebraQuaternion.Q (-1) (-1)` read on
`Fin (0 + 2) → ℝ` instead of on `ℝ × ℝ`. -/
def realCliffordZeroTwoIsometry :
    (realCliffordForm 0 2).IsometryEquiv (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1)) :=
  ⟨(LinearEquiv.finTwoArrow ℝ ℝ : (Fin (0 + 2) → ℝ) ≃ₗ[ℝ] ℝ × ℝ), fun v => by
    simp [realCliffordForm_zero_two_apply]⟩

/-- `realCliffordZeroTwoIsometry` reads off the two coordinates. -/
@[simp]
theorem realCliffordZeroTwoIsometry_apply (v : Fin (0 + 2) → ℝ) :
    realCliffordZeroTwoIsometry v = (v 0, v 1) := by
  simp [realCliffordZeroTwoIsometry, ← IsometryEquiv.coe_toLinearEquiv,
    LinearEquiv.finTwoArrow_apply]

/-- **`Cliff(0,2) ≅ ℍ`**, the third base entry of the real periodicity table: two anticommuting
generators squaring to `-1` are the quaternion units `i` and `j`. -/
noncomputable def realCliffordZeroTwoEquivQuaternion :
    CliffordAlgebra (realCliffordForm 0 2) ≃ₐ[ℝ] ℍ[ℝ] :=
  (CliffordAlgebra.equivOfIsometry realCliffordZeroTwoIsometry).trans
    CliffordAlgebraQuaternion.equiv

/-- `realCliffordZeroTwoEquivQuaternion` sends the generator of the coordinate `v` to the imaginary
quaternion `v 0 * i + v 1 * j`. -/
@[simp]
theorem realCliffordZeroTwoEquivQuaternion_ι (v : Fin (0 + 2) → ℝ) :
    realCliffordZeroTwoEquivQuaternion (CliffordAlgebra.ι _ v) = ⟨0, v 0, v 1, 0⟩ := by
  rw [realCliffordZeroTwoEquivQuaternion, AlgEquiv.trans_apply,
    CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  simp only [IsometryEquiv.toIsometry_apply, CliffordAlgebraQuaternion.equiv_apply,
    CliffordAlgebraQuaternion.toQuaternion_ι, realCliffordZeroTwoIsometry_apply]

/-- The `(0,2)` real Clifford-algebra equivalence identifies Clifford conjugation with quaternion
conjugation. -/
@[simp]
theorem realCliffordZeroTwoEquivQuaternion_star
    (x : CliffordAlgebra (realCliffordForm 0 2)) :
    realCliffordZeroTwoEquivQuaternion (star x) =
      star (realCliffordZeroTwoEquivQuaternion x) := by
  simp only [realCliffordZeroTwoEquivQuaternion, AlgEquiv.trans_apply,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_star,
    CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_star]

/-! ### `Cliff(1,1) ≅ M₂(ℝ)` -/

/-- The `(1,1)` signature form is Mathlib's quaternion form `CliffordAlgebraQuaternion.Q 1 (-1)`
after negating the second coordinate. -/
private noncomputable def realCliffordOneOneIsometry :
    (realCliffordForm 1 1).IsometryEquiv
      (CliffordAlgebraQuaternion.Q (1 : ℝ) ((-1 : ℝˣ) : ℝ)) :=
  ⟨(LinearEquiv.finTwoArrow ℝ ℝ : (Fin (1 + 1) → ℝ) ≃ₗ[ℝ] ℝ × ℝ).trans
      ((LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.neg ℝ)), fun v => by
    simp [realCliffordForm_one_one_apply]
    ring⟩

private theorem realCliffordOneOneIsometry_apply (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneIsometry v = (v 0, -v 1) :=
  rfl

/-- **`Cliff(1,1) ≅ M₂(ℝ)`**, the fourth base entry of the real periodicity table and the seed of
the periodicity step `Cliff(p+1, q+1) ≅ Cliff(p, q) ⊗ M₂(ℝ)`: Mathlib's
`CliffordAlgebraQuaternion.equiv` onto the split quaternions `ℍ[ℝ,1,-1]`, transported along
`realCliffordOneOneIsometry` and followed by the splitting
`TauCeti.QuaternionAlgebra.oneEquivMatrix`. -/
noncomputable def realCliffordOneOneEquivMatrix :
    CliffordAlgebra (realCliffordForm 1 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  ((CliffordAlgebra.equivOfIsometry realCliffordOneOneIsometry).trans
    CliffordAlgebraQuaternion.equiv).trans (QuaternionAlgebra.oneEquivMatrix (-1 : ℝˣ))

/-- `realCliffordOneOneEquivMatrix` sends the generator of the coordinate `v` to
`!![v 0, v 1; -v 1, -v 0]`, the combination `v 0 • !![1, 0; 0, -1] + v 1 • !![0, 1; -1, 0]` of the
images of the `+1` and `-1` generators. -/
@[simp]
theorem realCliffordOneOneEquivMatrix_ι (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneEquivMatrix (CliffordAlgebra.ι _ v) = !![v 0, v 1; -v 1, -v 0] := by
  simp only [realCliffordOneOneEquivMatrix, AlgEquiv.trans_apply,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι,
    IsometryEquiv.toIsometry_apply, realCliffordOneOneIsometry_apply,
    CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_ι,
    QuaternionAlgebra.oneEquivMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end TauCeti
