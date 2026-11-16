/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Quadratic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.HigherRank
import TauCeti.NumberTheory.QuadraticForm.Global.LowRank
import TauCeti.NumberTheory.QuadraticForm.Global.Quaternary

/-!
# The Hasse–Minkowski theorem for quadratic forms over number fields

Let `K` be a number field in any universe. This file proves the local-to-global principles of
Hasse and Minkowski for quadratic forms on finite-dimensional `K`-vector spaces, with no
nondegeneracy hypothesis on any form:

* **Isotropy** (O'Meara 66:1; Milne, Chapter VIII, Theorem 3.5(b)): a quadratic form is isotropic
  over `K` if and only if it is isotropic at every finite and every real place.
* **Scalar representation** (O'Meara 66:3 in rank one): a quadratic form represents a scalar
  `a : K` if and only if it represents `a` at every finite and every real place (including `a = 0`).
* **Form representation** (O'Meara 66:3): a quadratic form `Q` admits an injective isometry into a
  quadratic form `R` on a finite-dimensional space if and only if it does so at every finite and
  every real place (finite-dimensionality of the domain of `Q` follows from local representation).
* **Isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3): two quadratic forms are
  isometric over `K` if and only if they are isometric at every finite and every real place.

## Proof outline

The binary and lower-rank isotropy cases come from
`QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two`. For ternary forms,
diagonalization and scaling reduce to `⟨1, -d⟩ ⊥ ⟨-a⟩`; when `d` is a square the binary summand
is already isotropic, and otherwise local isotropy translates via
`QuadraticForm.isLocallyIsotropic_smul_sq_prod_iff` into local representation of `a` by
`⟨1, -d⟩`, which the quadratic Hasse norm theorem
(`TauCeti.ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion`) upgrades to a global
representation. Quaternary descent
(`QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary`) and the higher-rank induction
step (`QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank`) then close
isotropy in all dimensions.

Scalar representation follows for regular forms by applying isotropy to `⟨-a⟩ ⊥ Q`, and for
arbitrary forms by splitting off the radical (`QuadraticForm.exists_equivalent_zero_radical_prod`).
Representation of a regular form `Q` by a regular form `R` proceeds by induction on the dimension
of `Q`, splitting off a common nonzero value `⟨c⟩` and applying Witt cancellation for
representation (`TauCeti.isRepresentedBy_of_prod_isRepresentedBy_prod`) at each place. For
arbitrary forms `Q` and `R`, splitting off their radicals reduces first to embedding the regular
part of `Q` into the regular part of `R` (with regular complement `S`), then cancelling that
regular part locally to embed the radical of `Q` into `R.radical ⊥ S`; the excess radical
dimension embeds into `S` by induction on the Witt index via isotropy and hyperbolic-plane
splitting. Finally, isometry follows immediately from form representation between spaces of equal
finite dimension (`QuadraticForm.LocallyEquivalent.finrank_eq`).

## Main results

* `QuadraticForm.IsLocallyIsotropic.not_anisotropic`,
  `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic`: Hasse–Minkowski for isotropy.
* `QuadraticForm.LocallyRepresentsScalar.represents`,
  `QuadraticForm.represents_iff_locallyRepresentsScalar`: Hasse–Minkowski for scalar
  representation.
* `QuadraticForm.LocallyRepresents.isRepresentedBy`,
  `QuadraticForm.isRepresentedBy_iff_locallyRepresents`: Hasse–Minkowski for representation of
  forms.
* `QuadraticForm.LocallyEquivalent.equivalent`,
  `QuadraticForm.equivalent_iff_locallyEquivalent`: Hasse–Minkowski for isometry.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1, 66:3, and 66:4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 3.1, Theorem 3.5(b),
  Proposition 3.7, and Theorem 6.3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti
open scoped TensorProduct

universe u v w

namespace QuadraticForm

section Isotropy

variable {K : Type u} [Field K] [NumberField K]

/-- **Quadratic Hasse norm adapter.** For a nonsquare `d : K` and a nonzero scalar `a : K`, local
representation of `a` by `⟨1, -d⟩` implies global representation. -/
private theorem represents_weightedSumSquares_one_neg_of_locallyRepresentsScalar
    {d : K} (hd : ¬IsSquare d) {a : K} (ha : a ≠ 0)
    (hloc : LocallyRepresentsScalar (weightedSumSquares K ![(1 : K), -d]) a) :
    Represents (weightedSumSquares K ![(1 : K), -d]) a := by
  have hnorm : ∃ x y : K, (Units.mk0 a ha : K) = x ^ 2 - d * y ^ 2 := by
    rw [ClassFieldTheory.exists_sq_sub_mul_sq_iff_forall_completion hd (Units.mk0 a ha)]
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hv := (represents_iff _ _).mp <|
        (atFinitePlaceWeightedSumSquares v ![(1 : K), -d]).represents_iff _ |>.mp
          (((locallyRepresentsScalar_iff _ _).mp hloc).1 v)
      obtain ⟨u, hu⟩ := hv
      refine ⟨u 0, u 1, ?_⟩
      simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, map_one, map_neg, smul_eq_mul, Units.val_mk0] at hu ⊢
      linear_combination -hu
    · rcases w.isReal_or_isComplex with hw | hw
      · have hw' := (represents_iff _ _).mp <|
          (atRealPlaceWeightedSumSquares ⟨w, hw⟩ ![(1 : K), -d]).represents_iff _ |>.mp
            (((locallyRepresentsScalar_iff _ _).mp hloc).2 ⟨w, hw⟩)
        obtain ⟨u, hu⟩ := hw'
        let e : w.Completion ≃+* ℝ := Completion.ringEquivRealOfIsReal hw
        have he (x : K) : e (algebraMap K w.Completion x) = embedding_of_isReal hw x := by
          simp [e, Completion.algebraMap_apply_eq_coe]
        refine ⟨e.symm (u 0), e.symm (u 1), e.injective ?_⟩
        simp only [map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, he, Units.val_mk0]
        simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, map_one, map_neg, smul_eq_mul] at hu
        linear_combination -hu
      · let e : w.Completion ≃+* ℂ := Completion.ringEquivComplexOfIsComplex hw
        obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (e (algebraMap K w.Completion a))
        refine ⟨e.symm z, 0, e.injective ?_⟩
        simp only [e, zero_pow two_ne_zero, mul_zero, sub_zero, pow_two, map_mul,
          RingEquiv.apply_symm_apply, Units.val_mk0, hz]
  obtain ⟨x, y, hxy⟩ := hnorm
  refine (represents_iff _ _).mpr ⟨![x, y], ?_⟩
  simp only [weightedSumSquares_fin_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Units.val_mk0] at hxy
  linear_combination -hxy

/-- Scaling a locally isotropic quadratic form by any scalar produces a locally isotropic form. -/
private theorem isLocallyIsotropic_smul {M : Type*} [AddCommGroup M] [Module K M]
    {Q : _root_.QuadraticForm K M} (c : K) (h : Q.IsLocallyIsotropic) :
    (c • Q).IsLocallyIsotropic := by
  refine (isLocallyIsotropic_iff _).mpr ⟨fun v hani => ?_, fun w hani => ?_⟩
  · refine ((isLocallyIsotropic_iff _).mp h).1 v fun x hx => hani x ?_
    rw [atFinitePlace_smul, _root_.smul_apply, hx, smul_zero]
  · refine ((isLocallyIsotropic_iff _).mp h).2 w fun x hx => hani x ?_
    rw [atRealPlace_smul, _root_.smul_apply, hx, smul_zero]

/-- **Ternary Hasse–Minkowski for diagonal forms.** Every locally isotropic diagonal regular form
of rank three over a number field is isotropic. -/
private theorem not_anisotropic_presentedForm_three {w : Fin 3 → Kˣ}
    (hloc : (presentedForm ⟨3, w⟩).IsLocallyIsotropic) :
    ¬(presentedForm ⟨3, w⟩).Anisotropic := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  set a₀ := w 0
  set d : K := -((a₀⁻¹ * w 1 : Kˣ) : K)
  set a : K := -((a₀⁻¹ * w 2 : Kˣ) : K)
  have ha : a ≠ 0 := neg_ne_zero.mpr (a₀⁻¹ * w 2).ne_zero
  set B : _root_.QuadraticForm K (Fin 2 → K) := weightedSumSquares K ![(1 : K), -d]
  have hB : B.Nondegenerate := by
    refine nondegenerate_weightedSumSquares fun i => ?_
    fin_cases i
    · exact isRegular_one
    · simpa [d] using (a₀⁻¹ * w 1).isUnit.isRegular
  -- Scaling `⟨w 0, w 1, w 2⟩` by `(w 0)⁻¹` yields `⟨-a⟩ ⊥ ⟨1, -d⟩`.
  let e : (((a₀⁻¹ : Kˣ) : K) • presentedForm ⟨3, w⟩).IsometryEquiv
      (((-a) • (sq : _root_.QuadraticForm K K)).prod B) :=
    { toFun := fun x => (x 2, ![x 0, x 1])
      invFun := fun y => ![y.2 0, y.2 1, y.1]
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun r x => by ext <;> simp
      left_inv := fun x => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨t, u⟩ => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)
      map_app' := fun x => by
        have hmul : (a₀ : K)⁻¹ * (a₀ : K) = 1 := inv_mul_cancel₀ a₀.ne_zero
        simp only [B, d, a, QuadraticMap.prod_apply, _root_.smul_apply, sq_apply,
          weightedSumSquares_fin_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Units.val_mul, Units.val_inv_eq_inv_val, smul_eq_mul, neg_neg, one_mul]
        rw [presentedForm_apply, Fin.sum_univ_three]
        linear_combination (x 0 * x 0) * hmul.symm }
  -- Transport local isotropy along scaling and `e`, then deduce global isotropy of `⟨-a⟩ ⊥ B`.
  have hP_loc : IsLocallyIsotropic (((-a) • (sq : _root_.QuadraticForm K K)).prod B) :=
    (QuadraticForm.QuadraticMap.Equivalent.isLocallyIsotropic_iff ⟨e⟩).mp
      (isLocallyIsotropic_smul _ hloc)
  have hP_iso : ¬(((-a) • (sq : _root_.QuadraticForm K K)).prod B).Anisotropic := by
    by_cases hd : IsSquare d
    · obtain ⟨s, hs⟩ := hd
      refine (isRepresentedBy_prod_right _ B).not_anisotropic ?_
      rw [not_anisotropic_iff_exists]
      refine ⟨![s, 1], by intro h0; have h1 := congrFun h0 1; simp at h1, by simp [B, hs]⟩
    · have hB_rep : Represents B a :=
        represents_weightedSumSquares_one_neg_of_locallyRepresentsScalar hd ha
          ((B.isLocallyIsotropic_smul_sq_prod_iff hB a).mp hP_loc)
      refine not_anisotropic_prod_of_represents_neg (a := -a)
        ((represents_iff _ _).mpr ⟨1, by simp⟩) ?_ (neg_ne_zero.mpr ha)
      simpa only [neg_neg] using hB_rep
  intro hani
  refine hP_iso <| (Equivalent.anisotropic_iff ⟨e⟩).mp fun x hx => hani x ?_
  simp only [_root_.smul_apply, smul_eq_mul, mul_eq_zero, Units.ne_zero, false_or] at hx
  exact hx

/-- Every locally isotropic diagonal regular form over a number field is isotropic, proved by
strong induction on the rank across all number fields in a fixed universe. -/
private theorem not_anisotropic_presentedForm_aux :
    ∀ n : ℕ, ∀ (L : Type u) [Field L] [NumberField L] (p : RegularFormPresentation L),
      p.1 = n → (presentedForm p).IsLocallyIsotropic → ¬(presentedForm p).Anisotropic := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro L _ _ p hp hloc
    let _ : Invertible (2 : L) := invertibleOfNonzero two_ne_zero
    by_cases h2 : n ≤ 2
    · exact (not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two (presentedForm p)
        (by simpa [hp] using h2)).mpr hloc
    by_cases h3 : n = 3
    · rcases p with ⟨m, w⟩
      obtain rfl : m = 3 := hp.trans h3
      exact not_anisotropic_presentedForm_three hloc
    by_cases h4 : n = 4
    · exact not_anisotropic_of_isLocallyIsotropic_quaternary (nondegenerate_presentedForm p)
        (by simpa [hp] using h4) hloc fun E _ _ q hq hqloc =>
          ih 3 (by omega) E q hq hqloc
    · exact not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank
        (nondegenerate_presentedForm p) (by rw [Module.finrank_fin_fun]; omega) hloc
        fun q hq hqloc => ih q.1 (by rw [Module.finrank_fin_fun] at hq; omega) L q rfl hqloc

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Hasse–Minkowski theorem for isotropy** (O'Meara 66:1; Milne, Chapter VIII, Theorem 3.5(b)):
a quadratic form on a finite-dimensional vector space over a number field that is isotropic at
every finite and every real place is isotropic over `K`. No nondegeneracy hypothesis is needed. -/
theorem IsLocallyIsotropic.not_anisotropic {Q : _root_.QuadraticForm K V}
    (h : Q.IsLocallyIsotropic) : ¬Q.Anisotropic := by
  intro hA
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨p, hQp⟩ := exists_presentedForm_equivalent Q hA.nondegenerate
  exact not_anisotropic_presentedForm_aux p.1 K p rfl
    ((QuadraticForm.QuadraticMap.Equivalent.isLocallyIsotropic_iff hQp).mp h)
    (hQp.anisotropic_iff.mp hA)

/-- **Hasse–Minkowski theorem for isotropy** (O'Meara 66:1; Milne, Chapter VIII, Theorem 3.5(b)):
a quadratic form on a finite-dimensional vector space over a number field is isotropic if and only
if it is isotropic at every finite and every real place. No nondegeneracy hypothesis is needed. -/
theorem not_anisotropic_iff_isLocallyIsotropic (Q : _root_.QuadraticForm K V) :
    ¬Q.Anisotropic ↔ Q.IsLocallyIsotropic :=
  ⟨Q.isLocallyIsotropic_of_not_anisotropic, IsLocallyIsotropic.not_anisotropic⟩

end Isotropy

section Representation

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Hasse–Minkowski theorem for scalar representation** (O'Meara 66:3 in rank one), for regular
forms. -/
private theorem represents_of_locallyRepresentsScalar_of_nondegenerate [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) {a : K}
    (h : Q.LocallyRepresentsScalar a) : Represents Q a := by
  by_cases ha : a = 0
  · subst ha
    exact represents_zero Q
  · have hiso : ¬(Q.prod ((-a) • (sq : _root_.QuadraticForm K K))).Anisotropic := by
      have hcomm : (Q.prod ((-a) • (sq : _root_.QuadraticForm K K))).Equivalent
          (((-a) • (sq : _root_.QuadraticForm K K)).prod Q) :=
        ⟨IsometryEquiv.prodComm Q _⟩
      exact hcomm.anisotropic_iff.not.mpr h.isLocallyIsotropic_smul_sq_prod.not_anisotropic
    exact mem_unitValueSet.mp
      ((mem_unitValueSet_iff_not_anisotropic_prod Q hQ (Units.mk0 a ha)).mpr hiso)

/-- **Hasse–Minkowski theorem for scalar representation** (O'Meara 66:3 in rank one): a quadratic
form on a finite-dimensional vector space over a number field represents a scalar `a` if it
represents `a` at every finite and every real place. Neither nondegeneracy nor `a ≠ 0` is needed.
-/
theorem LocallyRepresentsScalar.represents [FiniteDimensional K V] {Q : _root_.QuadraticForm K V}
    {a : K} (h : Q.LocallyRepresentsScalar a) : Represents Q a := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨C, -, hC, hQe⟩ := Q.exists_equivalent_zero_radical_prod
  let QC : _root_.QuadraticForm K C := Q.restrict C
  have hzero_loc : LocallyRepresentsScalar
      ((0 : _root_.QuadraticForm K Q.radical).prod QC) a :=
    (QuadraticForm.QuadraticMap.Equivalent.locallyRepresentsScalar_iff hQe a).mp h
  have hC_loc : QC.LocallyRepresentsScalar a := by
    refine (locallyRepresentsScalar_iff QC a).mpr ⟨fun v => ?_, fun w => ?_⟩
    · obtain ⟨⟨r, x⟩, hx⟩ := (represents_iff _ _).mp <|
        (atFinitePlaceProd _ _ v).represents_iff _ |>.mp
          (((locallyRepresentsScalar_iff _ _).mp hzero_loc).1 v)
      refine (represents_iff _ _).mpr ⟨x, ?_⟩
      simpa [atFinitePlace_def, baseChange_zero] using hx
    · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
      obtain ⟨⟨r, x⟩, hx⟩ := (represents_iff _ _).mp <|
        (atRealPlaceProd _ _ w).represents_iff _ |>.mp
          (((locallyRepresentsScalar_iff _ _).mp hzero_loc).2 w)
      refine (represents_iff _ _).mpr ⟨x, ?_⟩
      simpa [atRealPlace_def, baseChange_zero] using hx
  exact (restrict_isRepresentedBy Q C).represents
    (represents_of_locallyRepresentsScalar_of_nondegenerate hC hC_loc)

/-- **Hasse–Minkowski theorem for scalar representation** (O'Meara 66:3 in rank one): a quadratic
form on a finite-dimensional vector space over a number field represents a scalar `a` if and only
if it represents `a` at every finite and every real place. Neither nondegeneracy nor `a ≠ 0` is
needed. -/
theorem represents_iff_locallyRepresentsScalar [FiniteDimensional K V]
    (Q : _root_.QuadraticForm K V) (a : K) :
    Represents Q a ↔ Q.LocallyRepresentsScalar a :=
  ⟨LocallyRepresentsScalar.of_represents, LocallyRepresentsScalar.represents⟩

/-- A vector with nonzero quadratic value `c` embeds the rank-one form `⟨c⟩` into `Q`. -/
private theorem isRepresentedBy_smul_sq_of_apply_eq {F : Type*} [Field F]
    {M : Type*} [AddCommGroup M] [Module F M]
    {Q : _root_.QuadraticForm F M} {x : M} {c : F} (hx : Q x = c) (hc : c ≠ 0) :
    (c • (sq : _root_.QuadraticForm F F)).IsRepresentedBy Q := by
  have hx_ne : x ≠ 0 := fun h0 => hc (by simpa [h0] using hx.symm)
  exact (isRepresentedBy_iff _ Q).mpr ⟨LinearMap.toSpanSingleton F M x,
    fun _ _ hxy => smul_left_injective F hx_ne hxy,
    fun t => by simp [← hx, Q.map_smul, smul_eq_mul, mul_comm]⟩

/-- Local Witt cancellation for representation: a regular finite-dimensional summand cancels from
a local representation of orthogonal sums. -/
private theorem locallyRepresents_of_prod_locallyRepresents_prod
    {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₀ : _root_.QuadraticForm K V₀} (hQ₀ : Q₀.Nondegenerate)
    {Q₁ : _root_.QuadraticForm K V₁} {Q₂ : _root_.QuadraticForm K V₂}
    (h : LocallyRepresents (Q₀.prod Q₁) (Q₀.prod Q₂)) :
    Q₁.LocallyRepresents Q₂ := by
  refine (locallyRepresents_iff Q₁ Q₂).mpr ⟨fun v => ?_, fun w => ?_⟩
  · let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
    refine isRepresentedBy_of_prod_isRepresentedBy_prod (Nondegenerate.atFinitePlace hQ₀ v) ?_
    exact (Equivalent.isRepresentedBy_congr ⟨atFinitePlaceProd Q₀ Q₁ v⟩
      ⟨atFinitePlaceProd Q₀ Q₂ v⟩).mp (((locallyRepresents_iff _ _).mp h).1 v)
  · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    refine isRepresentedBy_of_prod_isRepresentedBy_prod (Nondegenerate.atRealPlace hQ₀ w) ?_
    exact (Equivalent.isRepresentedBy_congr ⟨atRealPlaceProd Q₀ Q₁ w⟩
      ⟨atRealPlaceProd Q₀ Q₂ w⟩).mp (((locallyRepresents_iff _ _).mp h).2 w)

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3), when both forms are
regular, proved by induction on the dimension of the represented form. -/
private theorem isRepresentedBy_of_locallyRepresents_of_nondegenerate_aux :
    ∀ n : ℕ, ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W},
      Module.finrank K V = n → Q.Nondegenerate → R.Nondegenerate →
      Q.LocallyRepresents R → Q.IsRepresentedBy R := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ W _ _ _ Q R hV _ _ _
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    exact (isRepresentedBy_iff Q R).mpr
      ⟨0, Function.injective_of_subsingleton _, fun x => by simp [Subsingleton.elim x 0]⟩
  | succ n ih =>
    intro V _ _ _ W _ _ _ Q R hV hQ hR hloc
    let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨v₀, hv₀⟩ := hQ.exists_isUnit
    set c : K := Q v₀
    have hc : c ≠ 0 := hv₀.ne_zero
    let L : _root_.QuadraticForm K K := c • QuadraticMap.sq
    have hline_nd : L.Nondegenerate := nondegenerate_smul_sq hc
    have hR_c : Represents R c :=
      (hloc.locallyRepresentsScalar
        (LocallyRepresentsScalar.of_represents ((represents_iff Q c).mpr ⟨v₀, rfl⟩))).represents
    obtain ⟨w₀, hw₀⟩ := (represents_iff R c).mp hR_c
    -- Split `⟨c⟩` off both `Q` and `R` with regular complements `Q|_P` and `R|_S`.
    obtain ⟨P, hP, hQP⟩ :=
      (isRepresentedBy_smul_sq_of_apply_eq rfl hc).exists_equivalent_prod hline_nd hQ
    obtain ⟨S, hS, hRS⟩ :=
      (isRepresentedBy_smul_sq_of_apply_eq hw₀ hc).exists_equivalent_prod hline_nd hR
    let QP : _root_.QuadraticForm K P := Q.restrict P
    let RS : _root_.QuadraticForm K S := R.restrict S
    have hPrank : Module.finrank K P = n := by
      obtain ⟨e⟩ := hQP
      have hdim := e.toLinearEquiv.finrank_eq
      rw [hV, Module.finrank_prod, Module.finrank_self] at hdim
      omega
    have hPS_loc : QP.LocallyRepresents RS :=
      locallyRepresents_of_prod_locallyRepresents_prod hline_nd <|
        (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr hQP hRS).mp hloc
    obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff QP RS).mp (ih hPrank hP hS hPS_loc)
    have hprod_rep : (L.prod QP).IsRepresentedBy (L.prod RS) :=
      (isRepresentedBy_iff _ _).mpr ⟨LinearMap.id.prodMap f,
        Prod.map_injective.mpr ⟨Function.injective_id, hf⟩,
        fun ⟨x, y⟩ => by simp [QuadraticMap.prod_apply, hfQ]⟩
    exact (hQP.isRepresentedBy_congr hRS).mpr hprod_rep

/-- Any zero quadratic form on a finite-dimensional space is isometric to the zero form on a
space of the same dimension. -/
private theorem zero_equivalent_zero_of_finrank_eq {F : Type*} [Field F]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module F M₁] [FiniteDimensional F M₁]
    [AddCommGroup M₂] [Module F M₂] [FiniteDimensional F M₂]
    (h : Module.finrank F M₁ = Module.finrank F M₂) :
    (0 : _root_.QuadraticForm F M₁).Equivalent (0 : _root_.QuadraticForm F M₂) :=
  ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq M₁ M₂ h
     map_app' := fun _ => rfl }⟩

/-- A zero quadratic form on a finite-dimensional space is represented by the zero form on any
finite-dimensional space of at least as large dimension. -/
private theorem zero_isRepresentedBy_zero_of_finrank_le {F : Type*} [Field F]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module F M₁] [FiniteDimensional F M₁]
    [AddCommGroup M₂] [Module F M₂] [FiniteDimensional F M₂]
    (h : Module.finrank F M₁ ≤ Module.finrank F M₂) :
    (0 : _root_.QuadraticForm F M₁).IsRepresentedBy (0 : _root_.QuadraticForm F M₂) := by
  let b₁ := Module.finBasis F M₁
  let b₂ := Module.finBasis F M₂
  let f : M₁ →ₗ[F] M₂ :=
    (Fintype.linearCombination F (b₂ ∘ Fin.castLE h)).comp b₁.equivFun.toLinearMap
  have hf : Function.Injective f :=
    (linearIndependent_iff_injective_fintypeLinearCombination.mp
      (b₂.linearIndependent.comp (Fin.castLE h) (Fin.castLE_injective h))).comp
      b₁.equivFun.injective
  exact (isRepresentedBy_iff _ _).mpr ⟨f, hf, fun _ => rfl⟩

/-- Cancelling a hyperbolic plane from an embedding of a totally isotropic space into `H ⊥ Q`
reduces its dimension by one. -/
private theorem zero_fin_isRepresentedBy_of_hyperbolicPlane_prod {F : Type*} [Field F]
    [Invertible (2 : F)] {M : Type*} [AddCommGroup M] [Module F M]
    {Q : _root_.QuadraticForm F M} (hQ : Q.Nondegenerate) {k : ℕ}
    (h : (0 : _root_.QuadraticForm F (Fin (k + 1) → F)).IsRepresentedBy
      ((hyperbolicPlane F).prod Q)) :
    (0 : _root_.QuadraticForm F (Fin k → F)).IsRepresentedBy Q := by
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp h
  let HQ : _root_.QuadraticForm F ((Fin 2 → F) × M) := (hyperbolicPlane F).prod Q
  have hHQ : HQ.Nondegenerate := nondegenerate_hyperbolicPlane.prod hQ
  have hsingle : (Pi.single (0 : Fin (k + 1)) (1 : F) : Fin (k + 1) → F) ≠ 0 := fun h0 => by
    have h1 := congrFun h0 0; simp at h1
  let x := f (Pi.single 0 1)
  have hx : x ≠ 0 := fun h0 => hsingle (hf (h0.trans (map_zero f).symm))
  have hxQ : HQ x = 0 := hfQ (Pi.single 0 1)
  obtain ⟨y, hyQ, hxy⟩ :=
    exists_isotropic_polar_eq_one_of_radical_eq_bot hHQ.radical_eq_bot hx hxQ
  let P := LinearMap.BilinForm.orthogonal HQ.polarBilin (Submodule.span F ({x, y} : Set _))
  have hQP : Q.Equivalent (HQ.restrict P) :=
    equivalent_of_equivalent_prod nondegenerate_hyperbolicPlane
      (HQ.equivalent_hyperbolicPlane_prod_restrict_orthogonal hxQ hyQ hxy)
  let φ : (Fin (k + 1) → F) →ₗ[F] F := (HQ.polarBilin y).comp f
  have hker_dim : k ≤ Module.finrank F (LinearMap.ker φ) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : Module.finrank F (LinearMap.range φ) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range φ)
    rw [Module.finrank_fin_fun] at hsum; omega
  have hker_mem : ∀ v : LinearMap.ker φ, f v ∈ P := by
    intro v
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb => by simp [ha, hb])
      (fun _ _ _ ha => by simp [ha]) hu
    rintro z (rfl | rfl)
    · dsimp only [x, HQ]
      rw [polarBilin_apply_apply, polar, ← map_add, hfQ, hfQ, hfQ]; simp
    · exact v.2
  let g : LinearMap.ker φ →ₗ[F] P := (f.comp (LinearMap.ker φ).subtype).codRestrict P hker_mem
  have hker_P : (0 : _root_.QuadraticForm F (LinearMap.ker φ)).IsRepresentedBy (HQ.restrict P) :=
    (isRepresentedBy_iff _ _).mpr ⟨g, fun _ _ hv => Subtype.ext (hf (congrArg Subtype.val hv)),
      fun v => hfQ v.1⟩
  exact ((zero_isRepresentedBy_zero_of_finrank_le (by simpa using hker_dim)).trans hker_P).trans
    hQP.symm.isRepresentedBy

/-- Projecting an embedding of a zero form into `0_Z ⊥ T` onto `T` drops its dimension by at most
`dim Z`. -/
private theorem zero_fin_isRepresentedBy_of_zero_isRepresentedBy_zero_prod
    {F : Type*} [Field F]
    {U Z M : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]
    [AddCommGroup M] [Module F M]
    {T : _root_.QuadraticForm F M} {k : ℕ}
    (hk : k + Module.finrank F Z ≤ Module.finrank F U)
    (h : (0 : _root_.QuadraticForm F U).IsRepresentedBy
      ((0 : _root_.QuadraticForm F Z).prod T)) :
    (0 : _root_.QuadraticForm F (Fin k → F)).IsRepresentedBy T := by
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp h
  let g : U →ₗ[F] M := (LinearMap.snd F Z M).comp f
  have hker_le : Module.finrank F (LinearMap.ker g) ≤ Module.finrank F Z := by
    let p : LinearMap.ker g →ₗ[F] Z := (LinearMap.fst F Z M).comp (f.comp (LinearMap.ker g).subtype)
    have hp : Function.Injective p := fun x y hxy =>
      Subtype.ext (hf (Prod.ext hxy (x.2.trans y.2.symm)))
    exact LinearMap.finrank_le_finrank_of_injective hp
  have hrange_ge : k ≤ Module.finrank F (LinearMap.range g) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker g
    omega
  have hzero_range : (0 : _root_.QuadraticForm F (Fin k → F)).IsRepresentedBy
      (0 : _root_.QuadraticForm F (LinearMap.range g)) :=
    zero_isRepresentedBy_zero_of_finrank_le (by simpa using hrange_ge)
  have hrange_T : (0 : _root_.QuadraticForm F (LinearMap.range g)).IsRepresentedBy T :=
    (isRepresentedBy_iff _ _).mpr ⟨(LinearMap.range g).subtype, Subtype.coe_injective, by
      rintro ⟨_, u, rfl⟩
      simpa [g, QuadraticMap.prod_apply] using hfQ u⟩
  exact hzero_range.trans hrange_T

/-- The hyperbolic plane base-changes to the hyperbolic plane over any field extension of
characteristic not two. -/
private theorem baseChange_hyperbolicPlane_equivalent {F : Type*} [Field F]
    {A : Type*} [Field A] [Algebra F A] [Invertible (2 : F)] [Invertible (2 : A)] :
    ((hyperbolicPlane F).baseChange A).Equivalent (hyperbolicPlane A) := by
  have h1 : hyperbolicPlane F = weightedSumSquares F ![(1 : F), -1] := by
    rw [← presentedForm_one_neg_one, presentedForm_eq_weightedSumSquares_coe]
    congr 1; ext i; fin_cases i <;> simp
  have h2 : weightedSumSquares A (fun i : Fin 2 => algebraMap F A (![(1 : F), -1] i)) =
      hyperbolicPlane A := by
    rw [← presentedForm_one_neg_one, presentedForm_eq_weightedSumSquares_coe]
    congr 1; ext i; fin_cases i <;> simp
  rw [h1, ← h2]
  exact ⟨baseChangeWeightedSumSquares (A := A) ![(1 : F), -1]⟩

/-- After scalar extension to a field `A`, cancelling a hyperbolic plane from an embedding of a
totally isotropic space reduces its dimension by one. -/
private theorem zero_fin_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
    {F : Type*} [Field F] {A : Type*} [Field A] [Algebra F A]
    [Invertible (2 : F)] [Invertible (2 : A)]
    {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {Q : _root_.QuadraticForm F M} (hQ : Q.Nondegenerate) {k : ℕ}
    (h : ((0 : _root_.QuadraticForm F (Fin (k + 1) → F)).baseChange A).IsRepresentedBy
      (QuadraticForm.baseChange A ((hyperbolicPlane F).prod Q))) :
    ((0 : _root_.QuadraticForm F (Fin k → F)).baseChange A).IsRepresentedBy (Q.baseChange A) := by
  have h0 : ((0 : _root_.QuadraticForm F (Fin (k + 1) → F)).baseChange A).Equivalent
      (0 : _root_.QuadraticForm A (Fin (k + 1) → A)) := by
    rw [baseChange_zero]; exact zero_equivalent_zero_of_finrank_eq (by simp)
  have h1 : ((0 : _root_.QuadraticForm F (Fin k → F)).baseChange A).Equivalent
      (0 : _root_.QuadraticForm A (Fin k → A)) := by
    rw [baseChange_zero]; exact zero_equivalent_zero_of_finrank_eq (by simp)
  have hH : (QuadraticForm.baseChange A ((hyperbolicPlane F).prod Q)).Equivalent
      ((hyperbolicPlane A).prod (Q.baseChange A)) :=
    Equivalent.trans ⟨baseChangeProd (A := A) (hyperbolicPlane F) Q⟩
      (baseChange_hyperbolicPlane_equivalent.prod (.refl _))
  exact h1.isRepresentedBy.trans <|
    zero_fin_isRepresentedBy_of_hyperbolicPlane_prod (Nondegenerate.baseChange hQ)
      ((h0.isRepresentedBy_congr hH).mp h)

/-- A zero form on `Fin k → K` that is locally represented by a diagonal regular form is globally
represented by it, proved by induction on `k` via isotropy and hyperbolic-plane splitting. -/
private theorem zero_fin_isRepresentedBy_presentedForm :
    ∀ k : ℕ, ∀ (p : RegularFormPresentation K),
      LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm p) →
      (0 : _root_.QuadraticForm K (Fin k → K)).IsRepresentedBy (presentedForm p) := by
  intro k
  induction k with
  | zero =>
    intro p _
    exact (isRepresentedBy_iff _ _).mpr
      ⟨0, Function.injective_of_subsingleton _, fun x => by simp [Subsingleton.elim x 0]⟩
  | succ k ih =>
    intro p hloc
    let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    have hzero_iso : ¬(0 : _root_.QuadraticForm K (Fin (k + 1) → K)).Anisotropic := by
      rw [not_anisotropic_iff_exists]
      refine ⟨Pi.single 0 1, fun h0 => ?_, rfl⟩
      have h1 := congrFun h0 0; simp at h1
    have hp_iso : ¬(presentedForm p).Anisotropic :=
      (hloc.isLocallyIsotropic (isLocallyIsotropic_of_not_anisotropic _ hzero_iso)).not_anisotropic
    obtain ⟨q, hq⟩ :=
      exists_hyperbolicPlane_prod_equivalent (presentedForm p) (nondegenerate_presentedForm p)
        hp_iso
    have hprod_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin (k + 1) → K))
        ((hyperbolicPlane K).prod (presentedForm q)) :=
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl _) hq).mp hloc
    have hq_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm q) := by
      refine (locallyRepresents_iff _ _).mpr ⟨fun v => ?_, fun w => ?_⟩
      · let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
        rw [atFinitePlace_def, atFinitePlace_def]
        exact zero_fin_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (nondegenerate_presentedForm q)
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).1 v)
      · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_fin_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (nondegenerate_presentedForm q)
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).2 w)
    obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp (ih q hq_loc)
    let hline : K →ₗ[K] (Fin 2 → K) :=
      { toFun := fun t => ![t, t]
        map_add' := fun a b => by ext i; fin_cases i <;> rfl
        map_smul' := fun r a => by ext i; fin_cases i <;> rfl }
    have hline_inj : Function.Injective hline := fun a b hab => by
      simpa [hline] using congrFun hab (0 : Fin 2)
    have hprod_rep : ((0 : _root_.QuadraticForm K K).prod
        (0 : _root_.QuadraticForm K (Fin k → K))).IsRepresentedBy
        ((hyperbolicPlane K).prod (presentedForm q)) :=
      (isRepresentedBy_iff _ _).mpr ⟨hline.prodMap f,
        Prod.map_injective.mpr ⟨hline_inj, hf⟩,
        fun ⟨t, x⟩ => by simp [QuadraticMap.prod_apply, hline, hyperbolicPlane_apply, hfQ]⟩
    have hzero_split : (0 : _root_.QuadraticForm K (Fin (k + 1) → K)).Equivalent
        ((0 : _root_.QuadraticForm K K).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (K × (Fin k → K))
           map_app' := fun _ => by simp [QuadraticMap.prod_apply] }⟩
    exact (hzero_split.isRepresentedBy_congr hq).mpr hprod_rep

/-- After scalar extension to a field `A`, projecting an embedding of `0_U` into `0_Z ⊥ T` onto `T`
produces an embedding of `0_{Fin k}` where `k + dim Z = dim U`. -/
private theorem zero_fin_baseChange_isRepresentedBy_of_zero_prod
    {F : Type*} [Field F] {A : Type*} [Field A] [Algebra F A] [Invertible (2 : F)]
    {U Z M : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]
    [AddCommGroup M] [Module F M]
    {T : _root_.QuadraticForm F M} {k : ℕ}
    (hk : k + Module.finrank F Z = Module.finrank F U)
    (h : ((0 : _root_.QuadraticForm F U).baseChange A).IsRepresentedBy
      (QuadraticForm.baseChange A ((0 : _root_.QuadraticForm F Z).prod T))) :
    ((0 : _root_.QuadraticForm F (Fin k → F)).baseChange A).IsRepresentedBy (T.baseChange A) := by
  have h0 : ((0 : _root_.QuadraticForm F (Fin k → F)).baseChange A).Equivalent
      (0 : _root_.QuadraticForm A (Fin k → A)) := by
    rw [baseChange_zero]; exact zero_equivalent_zero_of_finrank_eq (by simp)
  have hstep : ((0 : _root_.QuadraticForm F U).baseChange A).IsRepresentedBy
      (((0 : _root_.QuadraticForm F Z).baseChange A).prod (T.baseChange A)) :=
    h.trans (Equivalent.isRepresentedBy ⟨baseChangeProd (A := A) _ T⟩)
  rw [baseChange_zero, baseChange_zero] at hstep
  exact h0.isRepresentedBy.trans <|
    zero_fin_isRepresentedBy_of_zero_isRepresentedBy_zero_prod (by simp [hk]) hstep

/-- A zero form locally represented by `0_Z ⊥ T` (with `T` regular) is globally represented by
`0_Z ⊥ T`. -/
private theorem zero_isRepresentedBy_zero_prod_of_locallyRepresents
    {U : Type v} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {Z : Type w} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    {M : Type w} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {T : _root_.QuadraticForm K M} (hT : T.Nondegenerate)
    (hloc : LocallyRepresents (0 : _root_.QuadraticForm K U)
      ((0 : _root_.QuadraticForm K Z).prod T)) :
    (0 : _root_.QuadraticForm K U).IsRepresentedBy ((0 : _root_.QuadraticForm K Z).prod T) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  by_cases hle : Module.finrank K U ≤ Module.finrank K Z
  · exact (zero_isRepresentedBy_zero_of_finrank_le hle).trans (isRepresentedBy_prod_left _ T)
  · set k := Module.finrank K U - Module.finrank K Z
    have hk : k + Module.finrank K Z = Module.finrank K U := Nat.sub_add_cancel (by omega)
    have hT_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) T := by
      refine (locallyRepresents_iff _ T).mpr ⟨fun v => ?_, fun w => ?_⟩
      · rw [atFinitePlace_def, atFinitePlace_def]
        exact zero_fin_baseChange_isRepresentedBy_of_zero_prod hk
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hloc).1 v)
      · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_fin_baseChange_isRepresentedBy_of_zero_prod hk
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hloc).2 w)
    obtain ⟨p, hp⟩ := exists_presentedForm_equivalent T hT
    have hp_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm p) :=
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl _) hp).mp hT_loc
    obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp
      ((zero_fin_isRepresentedBy_presentedForm k p hp_loc).trans hp.symm.isRepresentedBy)
    have hsplit : (0 : _root_.QuadraticForm K U).Equivalent
        ((0 : _root_.QuadraticForm K Z).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (Z × (Fin k → K))
           map_app' := fun _ => by simp [QuadraticMap.prod_apply] }⟩
    exact hsplit.isRepresentedBy.trans <|
      (isRepresentedBy_iff _ _).mpr ⟨LinearMap.id.prodMap f,
        Prod.map_injective.mpr ⟨Function.injective_id, hf⟩,
        fun ⟨z, x⟩ => by simp [QuadraticMap.prod_apply, hfQ]⟩

/-- After scalar extension to a field `A`, projecting an embedding of a regular form `Q₁` into
`0_Z ⊥ R₂` onto `R₂` remains an injective isometry. -/
private theorem baseChange_isRepresentedBy_of_zero_prod
    {F : Type*} [Field F] {A : Type*} [Field A] [Algebra F A] [Invertible (2 : F)]
    {M₁ Z M₂ : Type*} [AddCommGroup M₁] [Module F M₁] [FiniteDimensional F M₁]
    [AddCommGroup Z] [Module F Z] [AddCommGroup M₂] [Module F M₂]
    {Q₁ : _root_.QuadraticForm F M₁} (hQ₁ : Q₁.Nondegenerate) {R₂ : _root_.QuadraticForm F M₂}
    (h : (Q₁.baseChange A).IsRepresentedBy
      (QuadraticForm.baseChange A ((0 : _root_.QuadraticForm F Z).prod R₂))) :
    (Q₁.baseChange A).IsRepresentedBy (R₂.baseChange A) := by
  have hstep := h.trans (Equivalent.isRepresentedBy ⟨baseChangeProd (A := A) _ R₂⟩)
  obtain ⟨f, -, hfQ⟩ := (isRepresentedBy_iff _ _).mp hstep
  let g : (Q₁.baseChange A) →qᵢ (R₂.baseChange A) :=
    { toLinearMap := (LinearMap.snd _ _ _).comp f
      map_app' := fun x => by simpa [baseChange_zero] using hfQ x }
  exact (isRepresentedBy_iff _ _).mpr ⟨g.toLinearMap,
    g.injective_of_radical_eq_bot (Nondegenerate.baseChange hQ₁).radical_eq_bot, g.map_app⟩

/-- A quadratic space locally represented by a finite-dimensional quadratic space over a number
field is itself finite-dimensional. -/
private theorem finiteDimensional_of_locallyRepresents {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyRepresents R) : FiniteDimensional K V := by
  let v : HeightOneSpectrum (𝓞 K) := Classical.arbitrary _
  obtain ⟨f, hf, -⟩ := (isRepresentedBy_iff _ _).mp (((locallyRepresents_iff Q R).mp h).1 v)
  have : Module.Finite (v.adicCompletion K) (v.adicCompletion K ⊗[K] V) :=
    Module.Finite.of_injective f hf
  let b := Module.Basis.ofVectorSpace K V
  have : Finite (Module.Basis.ofVectorSpaceIndex K V) :=
    Module.Finite.finite_basis (b.baseChange (v.adicCompletion K))
  exact Module.Finite.of_basis b

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3): a quadratic form over a
number field is represented by a finite-dimensional quadratic form `R` if it is locally represented
by `R` at every finite and every real place. No nondegeneracy hypothesis is needed on either form,
and finite-dimensionality of `V` follows from local representation. -/
theorem LocallyRepresents.isRepresentedBy {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyRepresents R) :
    Q.IsRepresentedBy R := by
  have : FiniteDimensional K V := finiteDimensional_of_locallyRepresents h
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨C₁, -, hC₁, hQe⟩ := Q.exists_equivalent_zero_radical_prod
  obtain ⟨C₂, -, hC₂, hRe⟩ := R.exists_equivalent_zero_radical_prod
  let Q₁ : _root_.QuadraticForm K C₁ := Q.restrict C₁
  let R₂ : _root_.QuadraticForm K C₂ := R.restrict C₂
  -- Step 1: embed the regular part `Q₁` of `Q` into the regular part `R₂` of `R`.
  have hQ₁_zero_loc : Q₁.LocallyRepresents ((0 : _root_.QuadraticForm K R.radical).prod R₂) :=
    (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl Q₁) hRe).mp
      ((LocallyRepresents.of_isRepresentedBy (restrict_isRepresentedBy Q C₁)).trans h)
  have hQ₁R₂_loc : Q₁.LocallyRepresents R₂ := by
    refine (locallyRepresents_iff Q₁ R₂).mpr ⟨fun v => ?_, fun w => ?_⟩
    · rw [atFinitePlace_def, atFinitePlace_def]
      exact baseChange_isRepresentedBy_of_zero_prod hC₁
        (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hQ₁_zero_loc).1 v)
    · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
      rw [atRealPlace_def, atRealPlace_def]
      exact baseChange_isRepresentedBy_of_zero_prod hC₁
        (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hQ₁_zero_loc).2 w)
  have hQ₁R₂ : Q₁.IsRepresentedBy R₂ :=
    isRepresentedBy_of_locallyRepresents_of_nondegenerate_aux
      (Module.finrank K C₁) rfl hC₁ hC₂ hQ₁R₂_loc
  -- Step 2: split `Q₁` off `R₂`, cancel `Q₁` locally, and embed `Q.radical` into `R.radical ⊥ S`.
  obtain ⟨S, hS, hR₂S⟩ := hQ₁R₂.exists_equivalent_prod hC₁ hC₂
  let R_S : _root_.QuadraticForm K S := R₂.restrict S
  have hQ_split : Q.Equivalent (Q₁.prod (0 : _root_.QuadraticForm K Q.radical)) :=
    hQe.trans ⟨IsometryEquiv.prodComm _ Q₁⟩
  have hR_split : R.Equivalent (Q₁.prod ((0 : _root_.QuadraticForm K R.radical).prod R_S)) :=
    hRe.trans <| ((Equivalent.refl _).prod hR₂S).trans <|
      ⟨(IsometryEquiv.prodAssoc _ Q₁ R_S).symm.trans <|
        ((IsometryEquiv.prodComm _ Q₁).prod (.refl R_S)).trans <|
          IsometryEquiv.prodAssoc Q₁ _ R_S⟩
  have hrad_loc : LocallyRepresents (0 : _root_.QuadraticForm K Q.radical)
      ((0 : _root_.QuadraticForm K R.radical).prod R_S) :=
    locallyRepresents_of_prod_locallyRepresents_prod hC₁ <|
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr hQ_split hR_split).mp h
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff _ _).mp
    (zero_isRepresentedBy_zero_prod_of_locallyRepresents hS hrad_loc)
  have hprod_rep : (Q₁.prod (0 : _root_.QuadraticForm K Q.radical)).IsRepresentedBy
      (Q₁.prod ((0 : _root_.QuadraticForm K R.radical).prod R_S)) :=
    (isRepresentedBy_iff _ _).mpr ⟨LinearMap.id.prodMap f,
      Prod.map_injective.mpr ⟨Function.injective_id, hf⟩,
      fun ⟨x, y⟩ => by simpa [QuadraticMap.prod_apply, R_S] using hfQ y⟩
  exact (hQ_split.isRepresentedBy_congr hR_split).mpr hprod_rep

/-- **Hasse–Minkowski theorem for representation of forms** (O'Meara 66:3): a quadratic form `Q`
over a number field admits an injective isometry into a finite-dimensional quadratic form `R` if
and only if it does so at every finite and every real place. No nondegeneracy hypothesis is needed
on either form, and finite-dimensionality of `V` follows from local representation. -/
theorem isRepresentedBy_iff_locallyRepresents (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) :
    Q.IsRepresentedBy R ↔ Q.LocallyRepresents R :=
  ⟨LocallyRepresents.of_isRepresentedBy, LocallyRepresents.isRepresentedBy⟩

/-- **Hasse–Minkowski theorem for isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3):
two quadratic forms on finite-dimensional spaces over a number field that are isometric at every
finite and every real place are isometric over `K`. No nondegeneracy hypothesis is needed. -/
theorem LocallyEquivalent.equivalent [FiniteDimensional K V] {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) : Q.Equivalent R := by
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff Q R).mp h.locallyRepresents.isRepresentedBy
  exact ⟨{ toLinearEquiv := LinearEquiv.ofBijective f
             ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.finrank_eq).mp hf⟩
           map_app' := hfQ }⟩

/-- **Hasse–Minkowski theorem for isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3):
two quadratic forms on finite-dimensional spaces over a number field are isometric if and only if
they are isometric at every finite and every real place. No nondegeneracy hypothesis is needed. -/
theorem equivalent_iff_locallyEquivalent [FiniteDimensional K V] (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent, LocallyEquivalent.equivalent⟩

end Representation

end QuadraticForm
