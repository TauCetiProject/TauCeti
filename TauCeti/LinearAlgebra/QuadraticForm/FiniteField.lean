/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.FieldTheory.Finite.Extension
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.MvPolynomial
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Isotropy and scalar representation of quadratic forms over finite fields

Over any finite field `K` (of arbitrary characteristic, including characteristic two), every
quadratic form on a vector space of dimension at least three is isotropic: pulling back to a
three-dimensional coordinate subspace expresses the form as a homogeneous polynomial of total
degree at most two in three variables with `0` as a root, so the Chevalley–Warning theorem gives
at least `ringChar K ≥ 2` roots. Conversely, the norm form of a quadratic field extension of `K`
defines an anisotropic quadratic form on `Fin 2 → K` in every characteristic.

Combining three-dimensional isotropy with the scalar-representation criterion for forms of trivial
quadratic radical (`QuadraticMap.mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot`)
shows that every quadratic form with trivial radical (in particular, every nondegenerate form) on a
space of dimension at least two over `K` represents every scalar in `K`, again in arbitrary
characteristic. Every diagonal binary form with unit weights `⟨a, b⟩` is likewise universal over
`K`: in characteristic different from two it is nondegenerate, while in characteristic two every
scalar is already a square.

## Main results

* `QuadraticForm.not_anisotropic_of_finite`: every quadratic form on a space of dimension at least
  three over a finite field is isotropic (valid in all characteristics).
* `QuadraticForm.exists_anisotropic_fin_two_of_finite`: over every finite field there exists an
  anisotropic quadratic form on `Fin 2 → K` (valid in all characteristics).
* `QuadraticForm.represents_of_radical_eq_bot_of_two_le_finrank_of_finite` and
  `QuadraticForm.represents_of_two_le_finrank_of_finite`: every quadratic form with trivial radical
  (or nondegenerate) in dimension at least two over a finite field represents every scalar.
* `QuadraticForm.unitValueSet_eq_top_of_radical_eq_bot_of_two_le_finrank_of_finite` and
  `QuadraticForm.unitValueSet_eq_top_of_two_le_finrank_of_finite`: its represented-unit value set is
  `⊤`.
* `QuadraticForm.represents_weightedSumSquares_two_of_finite` and
  `QuadraticForm.unitValueSet_weightedSumSquares_two_of_finite`: every binary diagonal form with
  unit weights over a finite field represents every scalar.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter I, §2.2, Corollary 2 (Chevalley–Warning).
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3, Theorem 3.3 and
  Chapter XI, §6, Example 6.2 (2).
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  Example 7.21 (characteristic-free isotropy and binary norm forms).
-/

public section

open MvPolynomial QuadraticMap

namespace QuadraticForm

/-- Every quadratic form on a vector space of dimension at least three over a finite field (of
arbitrary characteristic) is isotropic, by the Chevalley–Warning theorem applied to the polynomial
representation of a three-dimensional coordinate pullback. -/
theorem not_anisotropic_of_finite
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (h : 3 ≤ Module.finrank K W) : ¬ Q.Anisotropic := by
  classical
  cases nonempty_fintype K
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  intro hQ
  let b := Module.finBasis K W
  let f : (Fin 3 → K) →ₗ[K] W := Fintype.linearCombination K (b ∘ Fin.castLE h)
  have hf : Function.Injective f :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h)).fintypeLinearCombination_injective
  have hQ' : (Q.comp f).Anisotropic := hQ.comp f hf
  let P : MvPolynomial (Fin 3) K := (Q.comp f).toMvPolynomial
  have hdeg : P.totalDegree < Fintype.card (Fin 3) := by
    simpa using Nat.lt_succ_of_le (Q.comp f).totalDegree_toMvPolynomial_le
  have hdvd : ringChar K ∣ Fintype.card { x : Fin 3 → K // eval x P = 0 } :=
    char_dvd_card_solutions (ringChar K) hdeg
  have hzero : (0 : Fin 3 → K) ∈ { x : Fin 3 → K | eval x P = 0 } := by
    simp [P]
  have hpos : 0 < Fintype.card { x : Fin 3 → K // eval x P = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hp : 2 ≤ ringChar K := (CharP.char_is_prime K (ringChar K)).two_le
  have hcard : 1 < Fintype.card { x : Fin 3 → K // eval x P = 0 } :=
    Nat.lt_of_lt_of_le (by omega) (hp.trans (Nat.le_of_dvd hpos hdvd))
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩ := Fintype.one_lt_card_iff.mp hcard
  have hx0 : x = 0 := hQ' x (by simpa [P] using hx)
  have hy0 : y = 0 := hQ' y (by simpa [P] using hy)
  exact hne (Subtype.ext (hx0.trans hy0.symm))

/-- Over every finite field `K` (of arbitrary characteristic), there exists an anisotropic
quadratic form on `Fin 2 → K`, realized as the norm form `x₀² + Tr(θ) x₀ x₁ + N(θ) x₁²` of a
quadratic field extension of `K`. -/
theorem exists_anisotropic_fin_two_of_finite (K : Type*) [Field K] [Finite K] :
    ∃ Q : QuadraticForm K (Fin 2 → K), Q.Anisotropic := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hfin : Module.finrank K (FiniteField.Extension K (ringChar K) 2) = 2 :=
    FiniteField.finrank_extension K (ringChar K) 2
  have : Algebra.IsQuadraticExtension K (FiniteField.Extension K (ringChar K) 2) :=
    { toFree := inferInstance
      finrank_eq_two' := hfin }
  obtain ⟨θ, hθ⟩ :=
    Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K
      (FiniteField.Extension K (ringChar K) 2)
  let Q : QuadraticForm K (Fin 2 → K) :=
    QuadraticMap.proj 0 0 +
      Algebra.trace K (FiniteField.Extension K (ringChar K) 2) θ • QuadraticMap.proj 0 1 +
      Algebra.norm K θ • QuadraticMap.proj 1 1
  refine ⟨Q, fun v hv ↦ ?_⟩
  have hnorm :
      Algebra.norm K
        (algebraMap K (FiniteField.Extension K (ringChar K) 2) (v 0) +
          algebraMap K (FiniteField.Extension K (ringChar K) 2) (v 1) * θ) = 0 := by
    rw [Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul]
    simp only [Q, add_apply, smul_apply, QuadraticMap.proj_apply, smul_eq_mul] at hv
    linear_combination hv
  have hzero := Algebra.norm_eq_zero_iff.mp hnorm
  have hv1 : v 1 = 0 := by
    by_contra hv1
    refine hθ ⟨(v 1)⁻¹ * -v 0, ?_⟩
    have hmul :
        algebraMap K (FiniteField.Extension K (ringChar K) 2) (v 1) * θ =
          algebraMap K (FiniteField.Extension K (ringChar K) 2) (-v 0) := by
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_right hzero
    rw [map_mul, ← hmul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hv1, map_one, one_mul]
  have hv0 : v 0 = 0 := by
    simpa [hv1] using hzero
  ext i
  fin_cases i
  · exact hv0
  · exact hv1

/-- Over a finite field (of arbitrary characteristic), every quadratic form with trivial quadratic
radical on a space of dimension at least two represents every scalar: adjoining the negative line
produces a form in dimension at least three, which is isotropic by `not_anisotropic_of_finite`. -/
theorem represents_of_radical_eq_bot_of_two_le_finrank_of_finite
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (hQ : Q.radical = ⊥) (h : 2 ≤ Module.finrank K W) (c : K) :
    Q.Represents c := by
  by_cases hc : c = 0
  · subst hc
    exact QuadraticMap.represents_zero Q
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  let u : Kˣ := Units.mk0 c hc
  suffices u ∈ Q.unitValueSet by simpa [u, mem_unitValueSet] using this
  rw [mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot Q hQ u]
  apply not_anisotropic_of_finite
  rw [Module.finrank_prod, Module.finrank_self]
  omega

/-- Over a finite field (of arbitrary characteristic), the represented-unit value set of any
quadratic form with trivial radical in dimension at least two is all of `Kˣ`. -/
@[simp]
theorem unitValueSet_eq_top_of_radical_eq_bot_of_two_le_finrank_of_finite
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (hQ : Q.radical = ⊥) (h : 2 ≤ Module.finrank K W) :
    Q.unitValueSet = ⊤ :=
  eq_top_iff.mpr fun u _ ↦
    mem_unitValueSet.mpr (Q.represents_of_radical_eq_bot_of_two_le_finrank_of_finite hQ h u)

/-- Over a finite field (of arbitrary characteristic), every nondegenerate quadratic form on a
space of dimension at least two represents every scalar. -/
theorem represents_of_two_le_finrank_of_finite
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (h : 2 ≤ Module.finrank K W) (c : K) :
    Q.Represents c :=
  Q.represents_of_radical_eq_bot_of_two_le_finrank_of_finite hQ.radical_eq_bot h c

/-- Over a finite field (of arbitrary characteristic), the represented-unit value set of any
nondegenerate quadratic form in dimension at least two is all of `Kˣ`. -/
@[simp]
theorem unitValueSet_eq_top_of_two_le_finrank_of_finite
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (h : 2 ≤ Module.finrank K W) :
    Q.unitValueSet = ⊤ :=
  Q.unitValueSet_eq_top_of_radical_eq_bot_of_two_le_finrank_of_finite hQ.radical_eq_bot h

/-- Over a finite field (of arbitrary characteristic), every binary diagonal form `⟨a, b⟩` with
unit weights represents every scalar in `K`. -/
theorem represents_weightedSumSquares_two_of_finite
    {K : Type*} [Field K] [Finite K] (a b : Kˣ) (c : K) :
    Represents (weightedSumSquares K ![(a : K), (b : K)]) c := by
  by_cases hchar : ringChar K = 2
  · cases nonempty_fintype K
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hchar ((↑a⁻¹ : K) * c)
    refine (represents_iff _ _).mpr ⟨![r, 0], ?_⟩
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul, mul_zero, add_zero, ← hr]
    exact Units.mul_inv_cancel_left a c
  · have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
    let : Invertible (2 : K) := invertibleOfNonzero h2
    have hnd : (weightedSumSquares K ![(a : K), (b : K)]).Nondegenerate :=
      QuadraticMap.nondegenerate_weightedSumSquares fun i ↦ by
        fin_cases i
        · exact a.isUnit.isRegular
        · exact b.isUnit.isRegular
    exact represents_of_two_le_finrank_of_finite _ hnd (by simp) c

/-- Over a finite field (of arbitrary characteristic), the represented-unit value set of a binary
diagonal form `⟨a, b⟩` with unit weights is all of `Kˣ`. -/
@[simp]
theorem unitValueSet_weightedSumSquares_two_of_finite
    {K : Type*} [Field K] [Finite K] (a b : Kˣ) :
    unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) = ⊤ :=
  eq_top_iff.mpr fun u _ ↦
    mem_unitValueSet.mpr (represents_weightedSumSquares_two_of_finite a b u)

end QuadraticForm
