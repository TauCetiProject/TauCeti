/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic
import TauCeti.NumberTheory.HilbertSymbol.Basic
import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
import TauCeti.NumberTheory.QuadraticForm.Global.Cancellation
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
* **Isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3): a quadratic form `Q` is
  isometric over `K` to a quadratic form `R` on a finite-dimensional space if and only if they are
  isometric at every finite and every real place (finite-dimensionality of the domain of `Q`
  follows from local equivalence).

## Proof outline

The binary and lower-rank isotropy cases come from
`QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two`. For ternary forms,
scaling reduces to `⟨1, -d, -a⟩`, whose local isotropy translates via the Hilbert symbol
(`TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares` and
`TauCeti.mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one`) into local representation of `a`
by `⟨1, -d⟩`, which
`QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`
upgrades to a global representation. Quaternary descent
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

/-- **Ternary Hasse–Minkowski for diagonal forms.** Every locally isotropic diagonal regular form
of rank three over a number field is isotropic. -/
private theorem not_anisotropic_presentedForm_three {w : Fin 3 → Kˣ}
    (hloc : (presentedForm ⟨3, w⟩).IsLocallyIsotropic) :
    ¬(presentedForm ⟨3, w⟩).Anisotropic := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  set a₀ := w 0
  set d : Kˣ := -(a₀⁻¹ * w 1)
  set a : Kˣ := -(a₀⁻¹ * w 2)
  have hscale : (((a₀⁻¹ : Kˣ) : K) • presentedForm ⟨3, w⟩) =
      weightedSumSquares K ![1, -(d : K), -(a : K)] := by
    ext x
    rw [_root_.smul_apply, presentedForm_apply, weightedSumSquares_apply,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Matrix.cons_val,
      d, a, Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, smul_eq_mul, neg_neg,
      one_mul]
    rw [mul_add, mul_add, ← mul_assoc, inv_mul_cancel₀ a₀.ne_zero]
    ring
  have hloc' : IsLocallyIsotropic (weightedSumSquares K ![1, -(d : K), -(a : K)]) :=
    hscale ▸ isLocallyIsotropic_smul _ hloc
  have hloc_bin : LocallyRepresentsScalar (weightedSumSquares K ![(1 : K), -(d : K)]) (a : K) := by
    refine (locallyRepresentsScalar_iff _ _).mpr ⟨fun v ↦ ?_, fun w' ↦ ?_⟩
    · let _ : Invertible (2 : v.adicCompletion K) :=
        (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
      have hv := (QuadraticMap.Equivalent.anisotropic_iff
        ⟨atFinitePlaceWeightedSumSquares v ![1, -(d : K), -(a : K)]⟩).not.mp
          (((isLocallyIsotropic_iff _).mp hloc').1 v)
      have hv' : ¬(weightedSumSquares (v.adicCompletion K)
          ![1, -(v.unitAtFinitePlace d : v.adicCompletion K),
            -(v.unitAtFinitePlace a : v.adicCompletion K)]).Anisotropic := by
        simpa [show (fun i : Fin 3 ↦
            algebraMap K (v.adicCompletion K) (![1, -(d : K), -(a : K)] i)) =
            ![1, -(v.unitAtFinitePlace d : v.adicCompletion K),
              -(v.unitAtFinitePlace a : v.adicCompletion K)] by
          ext i; fin_cases i <;> simp [d, a]] using hv
      have hsym := (hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares
        (v.unitAtFinitePlace d) (v.unitAtFinitePlace a)).mpr hv'
      have hbin := (mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one
        (v.unitAtFinitePlace d) (v.unitAtFinitePlace a)).mpr hsym
      rw [mem_unitValueSet] at hbin
      refine (atFinitePlaceWeightedSumSquares v ![(1 : K), -(d : K)]).represents_iff _ |>.mpr ?_
      simpa [show (fun i : Fin 2 ↦
          algebraMap K (v.adicCompletion K) (![(1 : K), -(d : K)] i)) =
          ![1, -(v.unitAtFinitePlace d : v.adicCompletion K)] by
        ext i; fin_cases i <;> simp [d]] using hbin
    · have hw := (QuadraticMap.Equivalent.anisotropic_iff
        ⟨atRealPlaceWeightedSumSquares w' ![1, -(d : K), -(a : K)]⟩).not.mp
          (((isLocallyIsotropic_iff _).mp hloc').2 w')
      have hw' : ¬(weightedSumSquares ℝ
          ![1, -(unitAtRealPlace w' d : ℝ), -(unitAtRealPlace w' a : ℝ)]).Anisotropic := by
        simpa [show (fun i : Fin 3 ↦
            embedding_of_isReal w'.2 (![1, -(d : K), -(a : K)] i)) =
            ![1, -(unitAtRealPlace w' d : ℝ), -(unitAtRealPlace w' a : ℝ)] by
          ext i; fin_cases i <;> simp [d, a]] using hw
      have hsym := (hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares
        (unitAtRealPlace w' d) (unitAtRealPlace w' a)).mpr hw'
      have hbin := (mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one
        (unitAtRealPlace w' d) (unitAtRealPlace w' a)).mpr hsym
      rw [mem_unitValueSet] at hbin
      refine (atRealPlaceWeightedSumSquares w' ![(1 : K), -(d : K)]).represents_iff _ |>.mpr ?_
      simpa [show (fun i : Fin 2 ↦
          embedding_of_isReal w'.2 (![(1 : K), -(d : K)] i)) =
          ![1, -(unitAtRealPlace w' d : ℝ)] by
        ext i; fin_cases i <;> simp [d]] using hbin
  have hrep : a ∈ unitValueSet (weightedSumSquares K ![(1 : K), -(d : K)]) :=
    mem_unitValueSet.mpr
      ((represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar
        (d : K) (a : K)).mpr hloc_bin)
  have hiso : ¬(weightedSumSquares K ![1, -(d : K), -(a : K)]).Anisotropic :=
    (hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares d a).mp
      ((mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one d a).mp hrep)
  intro hani
  refine hiso fun x hx ↦ hani x ?_
  have hxs : (((a₀⁻¹ : Kˣ) : K) • presentedForm ⟨3, w⟩) x = 0 := hscale.symm ▸ hx
  simpa [_root_.smul_apply, smul_eq_mul, Units.ne_zero] using hxs

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
    -- Split `⟨c⟩` off both `Q` and `R` with regular complements `Q|_P` and `R|_S`.
    obtain ⟨P, hP, hQP⟩ :=
      (((represents_iff Q c).mpr ⟨v₀, rfl⟩).isRepresentedBy_smul_sq hc).exists_equivalent_prod
        hline_nd hQ
    obtain ⟨S, hS, hRS⟩ :=
      (hR_c.isRepresentedBy_smul_sq hc).exists_equivalent_prod hline_nd hR
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
    have hprod_rep : (L.prod QP).IsRepresentedBy (L.prod RS) :=
      (IsRepresentedBy.refl L).prod (ih hPrank hP hS hPS_loc)
    exact (hQP.isRepresentedBy_congr hRS).mpr hprod_rep

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
      · rw [atFinitePlace_def, atFinitePlace_def]
        exact zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).1 v)
          (by simp)
      · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_baseChange_isRepresentedBy_of_hyperbolicPlane_prod
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hprod_loc).2 w)
          (by simp)
    have hline_rep : (0 : _root_.QuadraticForm K K).IsRepresentedBy (hyperbolicPlane K) := by
      simpa using isRepresentedBy_smul_sq_of_apply_eq (Q := hyperbolicPlane K) (x := ![1, 1])
        (c := 0) (by simp [hyperbolicPlane_apply])
        (by intro h; have h0 := congrFun h 0; simp at h0)
    have hprod_rep : ((0 : _root_.QuadraticForm K K).prod
        (0 : _root_.QuadraticForm K (Fin k → K))).IsRepresentedBy
        ((hyperbolicPlane K).prod (presentedForm q)) :=
      hline_rep.prod (ih q hq_loc)
    have hzero_split : (0 : _root_.QuadraticForm K (Fin (k + 1) → K)).Equivalent
        ((0 : _root_.QuadraticForm K K).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (K × (Fin k → K))
           map_app' := fun _ => by simp [QuadraticMap.prod_apply] }⟩
    exact (hzero_split.isRepresentedBy_congr hq).mpr hprod_rep

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
        exact zero_baseChange_isRepresentedBy_of_zero_prod
          (by simpa only [atFinitePlace_def] using ((locallyRepresents_iff _ _).mp hloc).1 v)
          (by simp [hk])
      · let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        rw [atRealPlace_def, atRealPlace_def]
        exact zero_baseChange_isRepresentedBy_of_zero_prod
          (by simpa only [atRealPlace_def] using ((locallyRepresents_iff _ _).mp hloc).2 w)
          (by simp [hk])
    obtain ⟨p, hp⟩ := exists_presentedForm_equivalent T hT
    have hp_loc : LocallyRepresents (0 : _root_.QuadraticForm K (Fin k → K)) (presentedForm p) :=
      (QuadraticForm.QuadraticMap.Equivalent.locallyRepresents_congr (.refl _) hp).mp hT_loc
    have hT_rep : (0 : _root_.QuadraticForm K (Fin k → K)).IsRepresentedBy T :=
      (zero_fin_isRepresentedBy_presentedForm k p hp_loc).trans hp.symm.isRepresentedBy
    have hsplit : (0 : _root_.QuadraticForm K U).Equivalent
        ((0 : _root_.QuadraticForm K Z).prod (0 : _root_.QuadraticForm K (Fin k → K))) :=
      (zero_equivalent_zero_of_finrank_eq (by simp [Module.finrank_prod]; omega)).trans <|
        ⟨{ toLinearEquiv := LinearEquiv.refl K (Z × (Fin k → K))
           map_app' := fun _ => by simp [QuadraticMap.prod_apply] }⟩
    exact hsplit.isRepresentedBy.trans ((IsRepresentedBy.refl _).prod hT_rep)

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
  have hprod_rep : (Q₁.prod (0 : _root_.QuadraticForm K Q.radical)).IsRepresentedBy
      (Q₁.prod ((0 : _root_.QuadraticForm K R.radical).prod R_S)) :=
    (IsRepresentedBy.refl Q₁).prod (zero_isRepresentedBy_zero_prod_of_locallyRepresents hS hrad_loc)
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
two quadratic forms over a number field, with target space finite-dimensional, that are isometric at
every finite and every real place are isometric over `K` (finite-dimensionality of `V` follows from
local equivalence). No nondegeneracy hypothesis is needed. -/
theorem LocallyEquivalent.equivalent {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (h : Q.LocallyEquivalent R) : Q.Equivalent R := by
  have : FiniteDimensional K V := finiteDimensional_of_locallyRepresents h.locallyRepresents
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff Q R).mp h.locallyRepresents.isRepresentedBy
  exact ⟨{ toLinearEquiv := LinearEquiv.ofBijective f
             ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.finrank_eq).mp hf⟩
           map_app' := hfQ }⟩

/-- **Hasse–Minkowski theorem for isometry** (O'Meara 66:4; Milne, Chapter VIII, Theorem 6.3):
two quadratic forms over a number field, with target space finite-dimensional, are isometric if and
only if they are isometric at every finite and every real place (finite-dimensionality of `V`
follows from local equivalence). No nondegeneracy hypothesis is needed. -/
theorem equivalent_iff_locallyEquivalent (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent, LocallyEquivalent.equivalent⟩

end Representation

end QuadraticForm
