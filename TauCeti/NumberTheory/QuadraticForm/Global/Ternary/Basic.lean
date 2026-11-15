/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.NormForm
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The ternary case of the Hasse–Minkowski theorem

Let `Q` be a regular ternary quadratic form over a number field `K`. This file proves that `Q` is
isotropic over `K` if and only if it is isotropic at every finite and every real place of `K`.

For a normalized diagonal ternary form `⟨1, -a, -b⟩` with `a, b ∈ Kˣ`, isotropy over any field of
characteristic different from two is equivalent to positivity of the Hilbert symbol `(a, b)`
(`TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares`), which in turn expresses
representation of `b` by the binary norm plane `⟨1, -a⟩`. Because the canonical diagonal
localizations identify `(⟨1, -a, -b⟩)_v` and `(⟨1, -a, -b⟩)_w` with the corresponding ternary
forms over `K_v` and `ℝ`, local isotropy of `⟨1, -a, -b⟩` translates place by place into local
positivity of `(a, b)`, and `TauCeti.hilbertSymbol_eq_one_iff_forall` closes the local-to-global
equivalence.

An arbitrary regular ternary form `Q` over `K` is diagonalized as `⟨u₀, u₁, u₂⟩` with unit weights
and rescaled by `u₀⁻¹` to the normalized form `⟨1, -a, -b⟩` where `a = -u₀⁻¹ u₁` and
`b = -u₀⁻¹ u₂`; both global anisotropy and `QuadraticForm.IsLocallyIsotropic` are invariant under
isometry and nonzero global scaling.

## Main results

* `QuadraticForm.not_anisotropic_weightedSumSquares_one_neg_neg_iff_isLocallyIsotropic`: the
  local-to-global isotropy equivalence for `⟨1, -a, -b⟩` with `a, b ∈ Kˣ`.
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_ternary` and
  `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_ternary`: the Hasse–Minkowski isotropy
  theorem for arbitrary regular three-dimensional quadratic forms over a number field.
* `QuadraticForm.anisotropic_iff_not_isLocallyIsotropic_ternary`: contrapositive characterization
  of global anisotropy in dimension three.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1, the case of dimension
  three.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §1.1, Proposition 2, and
  Chapter IV, §3.2, Theorem 8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  QuadraticMap

universe u v

namespace QuadraticForm

section Ternary

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- At a finite place `v`, the localization of `⟨1, -a, -b⟩` is isotropic if and only if the local
Hilbert symbol `(a_v, b_v)_v` is `1`. -/
theorem not_anisotropic_atFinitePlace_weightedSumSquares_one_neg_neg_iff
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    ¬ (atFinitePlace (weightedSumSquares K ![1, -(a : K), -(b : K)]) v).Anisotropic ↔
      TauCeti.hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let : Invertible (2 : v.adicCompletion K) :=
    (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  rw [(Equivalent.anisotropic_iff
    ⟨atFinitePlaceWeightedSumSquares v ![1, -(a : K), -(b : K)]⟩)]
  have hcoeff : (fun i : Fin 3 =>
      algebraMap K (v.adicCompletion K) (![1, -(a : K), -(b : K)] i)) =
      ![1, -((v.unitAtFinitePlace a : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        -((v.unitAtFinitePlace b : (v.adicCompletion K)ˣ) : v.adicCompletion K)] := by
    funext i
    fin_cases i <;> simp [unitAtFinitePlace_apply]
  rw [hcoeff, ← TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares]

/-- At a real place `w`, the localization of `⟨1, -a, -b⟩` is isotropic if and only if the real
Hilbert symbol `(a_w, b_w)_w` is `1`. -/
theorem not_anisotropic_atRealPlace_weightedSumSquares_one_neg_neg_iff
    (w : {w : InfinitePlace K // w.IsReal}) (a b : Kˣ) :
    ¬ (atRealPlace (weightedSumSquares K ![1, -(a : K), -(b : K)]) w).Anisotropic ↔
      TauCeti.hilbertSymbol (TauCeti.unitAtRealPlace w a) (TauCeti.unitAtRealPlace w b) = 1 := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [(Equivalent.anisotropic_iff
    ⟨atRealPlaceWeightedSumSquares w ![1, -(a : K), -(b : K)]⟩)]
  have hcoeff : (fun i : Fin 3 =>
      embedding_of_isReal w.2 (![1, -(a : K), -(b : K)] i)) =
      ![1, -((TauCeti.unitAtRealPlace w a : ℝˣ) : ℝ),
        -((TauCeti.unitAtRealPlace w b : ℝˣ) : ℝ)] := by
    funext i
    fin_cases i <;> simp [TauCeti.unitAtRealPlace_apply]
  rw [hcoeff, ← TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares]

/-- **The ternary Hasse–Minkowski theorem for `⟨1, -a, -b⟩`.** For units `a, b ∈ Kˣ` of a number
field `K`, the diagonal ternary form `⟨1, -a, -b⟩` is isotropic over `K` if and only if it is
isotropic at every finite and every real place. -/
theorem not_anisotropic_weightedSumSquares_one_neg_neg_iff_isLocallyIsotropic (a b : Kˣ) :
    ¬ (weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic ↔
      IsLocallyIsotropic (weightedSumSquares K ![1, -(a : K), -(b : K)]) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [← TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares,
    TauCeti.hilbertSymbol_eq_one_iff_forall, isLocallyIsotropic_iff]
  exact and_congr
    (forall_congr' fun v =>
      (not_anisotropic_atFinitePlace_weightedSumSquares_one_neg_neg_iff v a b).symm)
    (forall_congr' fun w =>
      (not_anisotropic_atRealPlace_weightedSumSquares_one_neg_neg_iff w a b).symm)

/-- **The ternary case of the Hasse–Minkowski theorem.** A regular three-dimensional quadratic form
over a number field `K` that is isotropic at every finite and every real place is isotropic over
`K`. -/
theorem not_anisotropic_of_isLocallyIsotropic_ternary
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 3)
    (hloc : Q.IsLocallyIsotropic) : ¬ Q.Anisotropic := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hQw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  let σ : Fin 3 ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  have hre : (weightedSumSquares K w).Equivalent
      (weightedSumSquares K ![(w (σ 0) : K), (w (σ 1) : K), (w (σ 2) : K)]) := by
    rw [weightedSumSquares_units]
    refine (TauCeti.equivalent_weightedSumSquares_comp (fun i => (w i : K)) σ).trans ?_
    have hfun : ((fun i => (w i : K)) ∘ σ) =
        ![(w (σ 0) : K), (w (σ 1) : K), (w (σ 2) : K)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
  have hQter : Q.Equivalent
      (weightedSumSquares K ![(w (σ 0) : K), (w (σ 1) : K), (w (σ 2) : K)]) :=
    hQw.trans hre
  let u₀ : Kˣ := w (σ 0)
  let a : Kˣ := -(u₀⁻¹ * w (σ 1))
  let b : Kˣ := -(u₀⁻¹ * w (σ 2))
  have hscale : weightedSumSquares K ![(u₀ : K), (w (σ 1) : K), (w (σ 2) : K)] =
      (u₀ : K) • weightedSumSquares K ![1, -(a : K), -(b : K)] := by
    rw [smul_weightedSumSquares]
    congr 1
    funext i
    fin_cases i <;> simp [u₀, a, b]
  rw [hQter.anisotropic_iff, hscale, anisotropic_smul_iff u₀.isUnit]
  have hloc' : IsLocallyIsotropic (weightedSumSquares K ![1, -(a : K), -(b : K)]) := by
    rw [← isLocallyIsotropic_smul_iff u₀.ne_zero, ← hscale,
      ← QuadraticMap.Equivalent.isLocallyIsotropic_iff hQter]
    exact hloc
  exact (not_anisotropic_weightedSumSquares_one_neg_neg_iff_isLocallyIsotropic a b).mpr hloc'

/-- **The ternary Hasse–Minkowski equivalence.** A regular three-dimensional quadratic form over a
number field is isotropic if and only if it is isotropic at every finite and every real place. -/
theorem not_anisotropic_iff_isLocallyIsotropic_ternary
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 3) :
    ¬ Q.Anisotropic ↔ Q.IsLocallyIsotropic :=
  ⟨isLocallyIsotropic_of_not_anisotropic Q, not_anisotropic_of_isLocallyIsotropic_ternary hQ hrank⟩

/-- A regular three-dimensional quadratic form over a number field is anisotropic if and only if
it is anisotropic at some finite or real place. -/
theorem anisotropic_iff_not_isLocallyIsotropic_ternary
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 3) :
    Q.Anisotropic ↔ ¬ Q.IsLocallyIsotropic :=
  (not_iff_comm.mp (not_anisotropic_iff_isLocallyIsotropic_ternary hQ hrank)).symm

end Ternary

section Examples

/-- **Worked example.** Over `ℚ`, the ternary form `⟨1, 1, -2⟩` (`x² + y² - 2 z²`) is both
globally isotropic (at `(1, 1, 1)`) and locally isotropic everywhere. -/
example : ¬ (weightedSumSquares ℚ ![(1 : ℚ), 1, -2]).Anisotropic ∧
    IsLocallyIsotropic (weightedSumSquares ℚ ![(1 : ℚ), 1, -2]) := by
  have hiso : ¬ (weightedSumSquares ℚ ![(1 : ℚ), 1, -2]).Anisotropic := by
    rw [not_anisotropic_iff_exists]
    refine ⟨![1, 1, 1], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      norm_num at h0
    · norm_num [weightedSumSquares_apply, Fin.sum_univ_three]
  exact ⟨hiso, isLocallyIsotropic_of_not_anisotropic _ hiso⟩

end Examples

end QuadraticForm
