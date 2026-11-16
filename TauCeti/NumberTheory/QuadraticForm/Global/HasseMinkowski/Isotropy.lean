/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.NumberTheory.QuadraticForm.Global.AnisotropicPlaces
import TauCeti.NumberTheory.QuadraticForm.Global.HasseMinkowski.Norm
import TauCeti.NumberTheory.QuadraticForm.Global.HigherRank
import TauCeti.NumberTheory.QuadraticForm.Global.LowRank
import TauCeti.NumberTheory.QuadraticForm.Global.Quaternary

/-!
# The Hasse–Minkowski theorem for isotropy

Over a number field `K`, a quadratic form `Q` on a `K`-vector space `V` is isotropic if and only
if it is isotropic at every finite and every real place of `K`. No nondegeneracy or
finite-dimensionality hypothesis is required.

The proof assembles the complete rank induction:
* **Rank at most two**: proved in `TauCeti.NumberTheory.QuadraticForm.Global.LowRank` from the
  global square theorem.
* **Rank three**: scaling a regular diagonal ternary form `⟨w₀, w₁, w₂⟩` by `w₁⁻¹` brings it to
  `⟨-a, 1, -d⟩`, whose isotropy over any field of characteristic not two is equivalent to
  representation of `a` by the binary norm form `⟨1, -d⟩`; the ternary theorem then follows
  directly from the Hasse norm theorem for binary norm forms
  (`QuadraticForm.represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar`).
* **Rank four**: plugging the ternary theorem (over arbitrary number fields, including the
  quadratic discriminant splitting field) into
  `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_quaternary` closes the quaternary case.
* **Rank at least five**: induction via
  `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank`.
* **Infinite dimension**: when `V` is infinite-dimensional, choose five linearly independent
  vectors together with the finite supports of real-place isotropic vectors across the finitely
  many real places of `K`. The restriction of `Q` to their span is finite-dimensional of rank at
  least five—hence automatically isotropic at every finite place—and isotropic at every real place,
  so the finite-dimensional theorem produces a global isotropic vector.

An anisotropic form over a field of characteristic not two is automatically nondegenerate, so
nondegeneracy drops out of every statement as well.

## Main results

* `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic`: the **Hasse–Minkowski theorem for
  isotropy** in arbitrary (finite or infinite) dimension, without nondegeneracy.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), Theorem 66:1.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, Theorem 8.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter VI, Principle 3.1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti
open scoped TensorProduct

universe u v

namespace QuadraticForm

/-- Over a field where `2` is invertible, the ternary diagonal form `⟨-a, 1, -d⟩` is isotropic if
and only if the binary norm form `⟨1, -d⟩` represents `a`. -/
private theorem not_anisotropic_weightedSumSquares_neg_one_neg_iff
    {F : Type*} [Field F] [Invertible (2 : F)] (a d : Fˣ) :
    ¬ (QuadraticMap.weightedSumSquares F ![-(a : F), 1, -(d : F)]).Anisotropic ↔
      QuadraticMap.Represents (QuadraticMap.weightedSumSquares F ![1, -(d : F)]) (a : F) := by
  let w : Fin 3 → Fˣ := ![-a, 1, -d]
  have h3 : presentedForm ⟨3, w⟩ =
      QuadraticMap.weightedSumSquares F ![-(a : F), 1, -(d : F)] := by
    ext x
    rw [presentedForm_apply, QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    fin_cases i <;> simp [w]
  have h2 : presentedForm ⟨2, fun i ↦ w i.succ⟩ =
      QuadraticMap.weightedSumSquares F ![1, -(d : F)] := by
    ext x
    rw [presentedForm_apply, QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    fin_cases i <;> simp [w]
  rw [← h3, not_anisotropic_presentedForm_succ_iff w, h2, QuadraticMap.mem_unitValueSet]
  simp [w]

variable {K : Type u} [Field K] [NumberField K]

/-- Local isotropy of the normalized ternary form `⟨-a, 1, -d⟩` translates directly to local
scalar representation of `a` by the binary norm form `⟨1, -d⟩`. -/
private theorem locallyRepresentsScalar_one_neg_of_isLocallyIsotropic (a d : Kˣ)
    (hloc : IsLocallyIsotropic (QuadraticMap.weightedSumSquares K ![-(a : K), 1, -(d : K)])) :
    LocallyRepresentsScalar (QuadraticMap.weightedSumSquares K ![1, -(d : K)]) (a : K) := by
  rw [locallyRepresentsScalar_iff]
  refine ⟨fun v ↦ ?_, fun wp ↦ ?_⟩
  · let : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hv := ((isLocallyIsotropic_iff _).mp hloc).1 v
    rw [QuadraticMap.Equivalent.anisotropic_iff
      ⟨atFinitePlaceWeightedSumSquares v ![-(a : K), 1, -(d : K)]⟩] at hv
    have h3 : (fun i : Fin 3 ↦ algebraMap K (v.adicCompletion K) (![-(a : K), 1, -(d : K)] i)) =
        ![-(v.unitAtFinitePlace a : v.adicCompletion K), 1,
          -(v.unitAtFinitePlace d : v.adicCompletion K)] := by
      funext i
      fin_cases i <;> simp
    rw [h3, not_anisotropic_weightedSumSquares_neg_one_neg_iff] at hv
    rw [(atFinitePlaceWeightedSumSquares v ![1, -(d : K)]).represents_iff]
    have h2 : (fun i : Fin 2 ↦ algebraMap K (v.adicCompletion K) (![1, -(d : K)] i)) =
        ![1, -(v.unitAtFinitePlace d : v.adicCompletion K)] := by
      funext i
      fin_cases i <;> simp
    simpa only [h2, HeightOneSpectrum.unitAtFinitePlace_apply] using hv
  · have hwp := ((isLocallyIsotropic_iff _).mp hloc).2 wp
    rw [QuadraticMap.Equivalent.anisotropic_iff
      ⟨atRealPlaceWeightedSumSquares wp ![-(a : K), 1, -(d : K)]⟩] at hwp
    have h3 : (fun i : Fin 3 ↦ embedding_of_isReal wp.2 (![-(a : K), 1, -(d : K)] i)) =
        ![-(unitAtRealPlace wp a : ℝ), 1, -(unitAtRealPlace wp d : ℝ)] := by
      funext i
      fin_cases i <;> simp
    rw [h3, not_anisotropic_weightedSumSquares_neg_one_neg_iff] at hwp
    rw [(atRealPlaceWeightedSumSquares wp ![1, -(d : K)]).represents_iff]
    have h2 : (fun i : Fin 2 ↦ embedding_of_isReal wp.2 (![1, -(d : K)] i)) =
        ![1, -(unitAtRealPlace wp d : ℝ)] := by
      funext i
      fin_cases i <;> simp
    simpa only [h2, unitAtRealPlace_apply] using hwp

/-- **Ternary Hasse–Minkowski for regular diagonal forms.** -/
private theorem not_anisotropic_presentedForm_three (w : Fin 3 → Kˣ)
    (hloc : (presentedForm ⟨3, w⟩).IsLocallyIsotropic) :
    ¬ (presentedForm ⟨3, w⟩).Anisotropic := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let u : Kˣ := (w 1)⁻¹
  let a : Kˣ := -(w 0 * u)
  let d : Kˣ := -(w 2 * u)
  have hscale : QuadraticMap.weightedSumSquares K ![-(a : K), 1, -(d : K)] =
      (u : K) • presentedForm ⟨3, w⟩ := by
    ext x
    rw [_root_.smul_apply, presentedForm_apply, QuadraticMap.weightedSumSquares_apply]
    have hw1 : (w 1 : K) ≠ 0 := (w 1).ne_zero
    simp [Fin.sum_univ_three, a, d, u]
    field_simp [hw1]
  have hloc' : IsLocallyIsotropic (QuadraticMap.weightedSumSquares K ![-(a : K), 1, -(d : K)]) := by
    refine (isLocallyIsotropic_iff _).mpr ⟨fun v ↦ ?_, fun wp ↦ ?_⟩
    · rw [hscale, atFinitePlace_smul, QuadraticMap.anisotropic_smul_iff (u.isUnit.map _)]
      exact ((isLocallyIsotropic_iff _).mp hloc).1 v
    · rw [hscale, atRealPlace_smul, QuadraticMap.anisotropic_smul_iff (u.isUnit.map _)]
      exact ((isLocallyIsotropic_iff _).mp hloc).2 wp
  have hrep : QuadraticMap.Represents (QuadraticMap.weightedSumSquares K ![1, -(d : K)]) (a : K) :=
    (represents_weightedSumSquares_one_neg_iff_locallyRepresentsScalar (d : K) (a : K)).mpr
      (locallyRepresentsScalar_one_neg_of_isLocallyIsotropic a d hloc')
  have hiso := (not_anisotropic_weightedSumSquares_neg_one_neg_iff a d).mpr hrep
  rwa [hscale, QuadraticMap.anisotropic_smul_iff u.isUnit] at hiso

/-- **Quaternary Hasse–Minkowski for regular diagonal forms.** -/
private theorem not_anisotropic_presentedForm_four (w : Fin 4 → Kˣ)
    (hloc : (presentedForm ⟨4, w⟩).IsLocallyIsotropic) :
    ¬ (presentedForm ⟨4, w⟩).Anisotropic := by
  refine not_anisotropic_of_isLocallyIsotropic_quaternary (nondegenerate_presentedForm _)
    (by simp) hloc fun L _ _ ⟨n, w'⟩ hn hploc ↦ ?_
  dsimp only at hn
  subst hn
  exact not_anisotropic_presentedForm_three w' hploc

/-- Hasse–Minkowski for regular diagonal forms of any finite rank `n`. -/
private theorem not_anisotropic_presentedForm_of_isLocallyIsotropic
    (n : ℕ) (w : Fin n → Kˣ) (hloc : (presentedForm ⟨n, w⟩).IsLocallyIsotropic) :
    ¬ (presentedForm ⟨n, w⟩).Anisotropic := by
  induction n with
  | zero =>
    exact (not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two _ (by simp)).mpr hloc
  | succ n ih =>
    rcases lt_or_ge (n + 1) 5 with hlt | hge
    · match n, hlt with
      | 0, _ =>
        exact (not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two _ (by simp)).mpr hloc
      | 1, _ =>
        exact (not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two _ (by simp)).mpr hloc
      | 2, _ => exact not_anisotropic_presentedForm_three w hloc
      | 3, _ => exact not_anisotropic_presentedForm_four w hloc
    · exact not_anisotropic_of_isLocallyIsotropic_of_five_le_finrank
        (nondegenerate_presentedForm _) (by simp [hge]) hloc fun ⟨m, w'⟩ hm hmloc ↦ by
          have hmn : m = n := by simpa using hm
          subst hmn
          exact ih w' hmloc

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Finite-dimensional Hasse–Minkowski for isotropy (without nondegeneracy). -/
private theorem not_anisotropic_of_isLocallyIsotropic_finiteDimensional [FiniteDimensional K V]
    (Q : _root_.QuadraticForm K V) (hloc : Q.IsLocallyIsotropic) : ¬ Q.Anisotropic := by
  intro hA
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨⟨n, w⟩, hQw⟩ := exists_presentedForm_equivalent Q hA.nondegenerate
  exact not_anisotropic_presentedForm_of_isLocallyIsotropic n w
    ((QuadraticMap.Equivalent.isLocallyIsotropic_iff hQw).mp hloc) (hQw.anisotropic_iff.mp hA)

/-- A nonzero isotropic vector at a real place is supported on a finite subset of `V`, so the
restriction of `Q` to any submodule containing that subset remains isotropic at that real
place. -/
private theorem exists_finset_not_anisotropic_atRealPlace_restrict
    (Q : _root_.QuadraticForm K V) (w : {w : InfinitePlace K // w.IsReal})
    (hw : ¬ (Q.atRealPlace w).Anisotropic) :
    ∃ S : Finset V, ∀ U : Submodule K V, (S : Set V) ⊆ U →
      ¬ (atRealPlace (Q.restrict U) w).Anisotropic := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  rw [atRealPlace_def, QuadraticMap.not_anisotropic_iff_exists] at hw
  obtain ⟨x, hx0, hQx⟩ := hw
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨T.image Prod.snd, fun U hTU ↦ ?_⟩
  rw [atRealPlace_def, QuadraticMap.not_anisotropic_iff_exists]
  let y : ℝ ⊗[K] U :=
    T.attach.sum fun p ↦ p.1.1 ⊗ₜ[K] ⟨p.1.2, hTU (Finset.mem_image_of_mem Prod.snd p.2)⟩
  let f := QuadraticMap.Isometry.baseChange
    (⟨U.subtype, fun _ ↦ rfl⟩ : (Q.restrict U : _root_.QuadraticForm K U) →qᵢ Q) ℝ
  have hf : f y = x := by
    rw [hT, map_sum, ← Finset.sum_attach T]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    exact QuadraticMap.Isometry.baseChange_tmul _ _ _
  exact ⟨y, fun hy ↦ hx0 (by rw [← hf, hy, map_zero]), by rw [← f.map_app y, hf, hQx]⟩

/-- **The Hasse–Minkowski theorem for isotropy.** A quadratic form on an arbitrary (finite- or
infinite-dimensional) vector space over a number field is isotropic if and only if it is isotropic
at every finite and every real place of `K`. -/
theorem not_anisotropic_iff_isLocallyIsotropic (Q : _root_.QuadraticForm K V) :
    ¬ Q.Anisotropic ↔ Q.IsLocallyIsotropic := by
  refine ⟨Q.isLocallyIsotropic_of_not_anisotropic, fun hloc ↦ ?_⟩
  by_cases hfin : FiniteDimensional K V
  · exact not_anisotropic_of_isLocallyIsotropic_finiteDimensional Q hloc
  -- In infinite dimension, restrict to a finite-dimensional subspace of rank at least five that
  -- contains the finite support of an isotropic vector at each of the finitely many real places.
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (R := K) (M := V) (n := 5)
    ((Cardinal.natCast_le_aleph0 (n := 5)).trans
      (not_lt.mp (hfin ∘ Module.rank_lt_aleph0_iff.mp)))
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal},
      ∃ S : Finset V, ∀ U : Submodule K V, (S : Set V) ⊆ U →
        ¬ (atRealPlace (Q.restrict U) w).Anisotropic :=
    fun w ↦ exists_finset_not_anisotropic_atRealPlace_restrict Q w
      (((isLocallyIsotropic_iff Q).mp hloc).2 w)
  choose S hS using hreal
  let U : Submodule K V := Submodule.span K (Set.range v ∪ ⋃ w, (S w : Set V))
  have hfinU : FiniteDimensional K U := Module.Finite.span_of_finite K
    ((Set.finite_range v).union (Set.finite_iUnion fun w ↦ (S w).finite_toSet))
  have h5 : 5 ≤ Module.finrank K U := by
    let f : (Fin 5 → K) →ₗ[K] U :=
      Fintype.linearCombination K fun i ↦ (⟨v i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩ : U)
    have hf : Function.Injective f := by
      refine Function.Injective.of_comp (f := U.subtype) ?_
      have hcomp : (U.subtype : U → V) ∘ f = Fintype.linearCombination K v := by
        ext c
        simp [f, Fintype.linearCombination_apply]
      rw [hcomp]
      exact hv.fintypeLinearCombination_injective
    simpa [Module.finrank_fin_fun] using LinearMap.finrank_le_finrank_of_injective hf
  have hUloc : IsLocallyIsotropic (Q.restrict U) :=
    (isLocallyIsotropic_iff _).mpr
      ⟨fun vp ↦ not_anisotropic_atFinitePlace_of_five_le_finrank (Q.restrict U) h5 vp,
        fun w ↦ hS w U (Set.Subset.trans (Set.subset_iUnion (fun w' ↦ (S w' : Set V)) w)
          (Set.subset_union_right.trans Submodule.subset_span))⟩
  exact (Q.restrict_isRepresentedBy U).not_anisotropic
    (not_anisotropic_of_isLocallyIsotropic_finiteDimensional (Q.restrict U) hUloc)

end QuadraticForm
