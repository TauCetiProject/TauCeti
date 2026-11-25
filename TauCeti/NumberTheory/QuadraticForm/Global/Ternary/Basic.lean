/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.NormForm

/-!
# The ternary case of the Hasse–Minkowski theorem

Let `Q` be a ternary quadratic form over a number field `K`. This file proves that `Q` is isotropic
over `K` as soon as it is isotropic at every finite and every real place of `K`.

For a normalized diagonal ternary form `⟨1, -a, -b⟩` with `a, b ∈ Kˣ`, isotropy over any field of
characteristic different from two is equivalent to positivity of the Hilbert symbol `(a, b)`
(`TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares`), which in turn expresses
representation of `b` by the binary norm plane `⟨1, -a⟩`. Because the canonical diagonal
localizations identify `(⟨1, -a, -b⟩)_v` and `(⟨1, -a, -b⟩)_w` with the corresponding ternary
forms over `K_v` and `ℝ`, local isotropy of `⟨1, -a, -b⟩` translates place by place into local
positivity of `(a, b)`, and `TauCeti.hilbertSymbol_eq_one_iff_forall_places` closes the
local-to-global equivalence.

An arbitrary three-dimensional form `Q` over `K` that is anisotropic is automatically nondegenerate
(since `2 ≠ 0` in a number field), hence diagonalizes via `TauCeti.exists_presentedForm_equivalent`
as `⟨w 0, w 1, w 2⟩` with unit weights and rescales by `(w 0)⁻¹` to `⟨1, -a, -b⟩` where
`a = -(w 0)⁻¹ * w 1` and `b = -(w 0)⁻¹ * w 2`; both global anisotropy and
`QuadraticForm.IsLocallyIsotropic` are invariant under isometry and nonzero global scaling.

## Main results

* `QuadraticForm.not_anisotropic_weightedSumSquares_one_neg_neg_iff_isLocallyIsotropic`: the
  local-to-global isotropy equivalence for `⟨1, -a, -b⟩` with `a, b ∈ Kˣ`.
* `QuadraticForm.not_anisotropic_of_isLocallyIsotropic_ternary`: the Hasse–Minkowski isotropy
  theorem for arbitrary three-dimensional quadratic forms over a number field. The rank-independent
  equivalence is `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic`.

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
theorem not_anisotropic_atFinitePlace_weightedSumSquares_one_neg_neg_iff_hilbertSymbol_eq_one
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

omit [NumberField K] in
/-- At a real place `w`, the localization of `⟨1, -a, -b⟩` is isotropic if and only if the real
Hilbert symbol `(a_w, b_w)_w` is `1`. -/
theorem not_anisotropic_atRealPlace_weightedSumSquares_one_neg_neg_iff_hilbertSymbol_eq_one
    (w : {w : InfinitePlace K // w.IsReal}) (a b : Kˣ) :
    ¬ (atRealPlace (weightedSumSquares K ![1, -(a : K), -(b : K)]) w).Anisotropic ↔
      TauCeti.hilbertSymbol (TauCeti.unitAtRealPlace w a) (TauCeti.unitAtRealPlace w b) = 1 := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [(Equivalent.anisotropic_iff
    ⟨atRealPlaceWeightedSumSquares w ![1, -(a : K), -(b : K)]⟩)]
  have hcoeff : (fun i : Fin 3 =>
      embedding_of_isReal w.property (![1, -(a : K), -(b : K)] i)) =
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
    TauCeti.hilbertSymbol_eq_one_iff_forall_places, isLocallyIsotropic_iff]
  exact and_congr
    (forall_congr' fun v =>
      (not_anisotropic_atFinitePlace_weightedSumSquares_one_neg_neg_iff_hilbertSymbol_eq_one
        v a b).symm)
    (forall_congr' fun w =>
      (not_anisotropic_atRealPlace_weightedSumSquares_one_neg_neg_iff_hilbertSymbol_eq_one
        w a b).symm)

/-- **The ternary case of the Hasse–Minkowski theorem.** A three-dimensional quadratic form over a
number field `K` that is isotropic at every finite and every real place is isotropic over `K`. -/
theorem not_anisotropic_of_isLocallyIsotropic_ternary
    {Q : _root_.QuadraticForm K V} (hrank : Module.finrank K V = 3)
    (hloc : Q.IsLocallyIsotropic) : ¬ Q.Anisotropic := by
  intro hA
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨⟨n, w⟩, ⟨e⟩⟩ := TauCeti.exists_presentedForm_equivalent Q hA.nondegenerate
  obtain rfl : n = 3 := by simpa [hrank] using e.toLinearEquiv.finrank_eq.symm
  let a : Kˣ := -((w 0)⁻¹ * w 1)
  let b : Kˣ := -((w 0)⁻¹ * w 2)
  have hscale : TauCeti.presentedForm ⟨3, w⟩ =
      (w 0 : K) • weightedSumSquares K ![1, -(a : K), -(b : K)] := by
    rw [TauCeti.presentedForm_eq_weightedSumSquares_coe, smul_weightedSumSquares]
    congr 1
    funext i
    fin_cases i <;> simp [a, b]
  have hloc' : IsLocallyIsotropic (weightedSumSquares K ![1, -(a : K), -(b : K)]) := by
    rw [← isLocallyIsotropic_smul_iff (w 0).ne_zero, ← hscale,
      ← QuadraticMap.Equivalent.isLocallyIsotropic_iff ⟨e⟩]
    exact hloc
  rw [QuadraticMap.Equivalent.anisotropic_iff ⟨e⟩, hscale, anisotropic_smul_iff (w 0).isUnit] at hA
  exact (not_anisotropic_weightedSumSquares_one_neg_neg_iff_isLocallyIsotropic a b).mpr hloc' hA

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
