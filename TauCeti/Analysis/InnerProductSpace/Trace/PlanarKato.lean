/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Bilinear
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import Mathlib.Tactic.Ring

/-!
# The planar Kato equality for trace-free Codazzi tensors

`OrthonormalBasis.planar_kato_identity_of_codazzi` states
`∑ᵢ (2 ⟪S, D eᵢ⟫_HS)² = 2 ⟪S, S⟫_HS · D.bilinearHilbertSchmidtEnergy`
for a symmetric trace-free endomorphism `S` of a real plane and a symmetric trace-free
endomorphism-valued map `D` satisfying `D u v = D v u`.

For the scalar second fundamental form `S = A` and its covariant derivative `D = ∇A` on a
minimal surface in ℝ³, this reads `|∇|A|²|² = 2 |A|² |∇A|²`. Hence
`|∇|A||² = |∇A|² / 2` wherever `A ≠ 0`, the sharp Kato equality used in the
surface-dimensional Simons formula. The energy uses the existing full two-slot tensor norm,
summed over an orthonormal basis in each input.

## References

* R. Schoen, L. Simon and S.-T. Yau, *Curvature estimates for minimal hypersurfaces*,
  Acta Math. **134** (1975), 275–288, §1, equations (1.29)–(1.33), for the underlying sharp
  Kato estimate and its use in Simons' inequality (1.34).
  https://doi.org/10.1007/BF02392104

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/InnerProductSpace/Trace/PlanarCodazzi.lean` in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory)
(commit `4f5bbcbfa5d49bbeb92fbcbf68f501a23bc56b0f`).
-/

public noncomputable section

open Module
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem planar_coefficient_identity (a : Fin 2 → Fin 2 → ℝ)
    (t : Fin 2 → Fin 2 → Fin 2 → ℝ) (ha : ∀ i j, a i j = a j i)
    (hatrace : a 0 0 + a 1 1 = 0) (htlast : ∀ i j k, t i j k = t i k j)
    (htfirst : ∀ i j k, t i j k = t j i k) (httrace : ∀ i, t i 0 0 + t i 1 1 = 0) :
    (∑ i, (2 * ∑ j, ∑ k, a j k * t i j k) ^ 2) =
      2 * (∑ i, ∑ j, a i j ^ 2) * (∑ i, ∑ j, ∑ k, t i j k ^ 2) := by
  have ha10 : a 1 0 = a 0 1 := ha 1 0
  have ha11 : a 1 1 = -a 0 0 := eq_neg_of_add_eq_zero_right hatrace
  have ht010 : t 0 1 0 = t 0 0 1 := htlast 0 1 0
  have ht011 : t 0 1 1 = -t 0 0 0 := eq_neg_of_add_eq_zero_right (httrace 0)
  have ht100 : t 1 0 0 = t 0 0 1 := (htfirst 1 0 0).trans ht010
  have ht101 : t 1 0 1 = -t 0 0 0 := (htfirst 1 0 1).trans ht011
  have ht110 : t 1 1 0 = -t 0 0 0 := (htlast 1 1 0).trans ht101
  have ht111 : t 1 1 1 = -t 0 0 1 := by
    rw [eq_neg_of_add_eq_zero_right (httrace 1), ht100]
  simp only [Fin.sum_univ_two, ha10, ha11, ht010, ht011, ht100, ht101, ht110, ht111]
  ring

/-- For a symmetric trace-free endomorphism `S` of a real plane and an endomorphism-valued
map `D` with symmetric trace-free values and `D u v = D v u`, the exact Kato contraction is
`∑ᵢ (2 ⟪S, D eᵢ⟫_HS)² = 2 ⟪S, S⟫_HS · D.bilinearHilbertSchmidtEnergy`.
For `S = A` and `D = ∇A` on a minimal surface in ℝ³, this gives
`|∇|A|²|² = 2 |A|² |∇A|²`, hence `|∇|A||² = |∇A|² / 2` wherever `A ≠ 0`. -/
theorem planar_kato_identity_of_codazzi (b : OrthonormalBasis (Fin 2) ℝ V)
    (S : V →L[ℝ] V) (D : V →L[ℝ] (V →L[ℝ] V)) (hS : S.toLinearMap.IsSymmetric)
    (hStrace : LinearMap.trace ℝ V S.toLinearMap = 0)
    (hD : ∀ w, (D w).toLinearMap.IsSymmetric)
    (hDtrace : ∀ w, LinearMap.trace ℝ V (D w).toLinearMap = 0)
    (hCodazzi : ∀ u v, D u v = D v u) :
    (∑ i, (2 * S.hilbertSchmidtInner (D (b i))) ^ 2) =
      2 * S.hilbertSchmidtInner S * D.bilinearHilbertSchmidtEnergy := by
  have htrace (A : V →L[ℝ] V) :
      inner ℝ (A (b 0)) (b 0) + inner ℝ (A (b 1)) (b 1) =
        LinearMap.trace ℝ V A.toLinearMap := by
    rw [LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_two]
    simp only [ContinuousLinearMap.coe_coe, real_inner_comm (A (b 0)),
      real_inner_comm (A (b 1))]
  have h := planar_coefficient_identity
    (fun i j ↦ inner ℝ (S (b i)) (b j))
    (fun i j k ↦ inner ℝ (D (b i) (b j)) (b k))
    (fun i j ↦ (hS (b i) (b j)).trans (real_inner_comm _ _))
    ((htrace S).trans hStrace)
    (fun i j k ↦ (hD (b i) (b j) (b k)).trans (real_inner_comm _ _))
    (fun i j k ↦ congrArg (fun v ↦ inner ℝ v (b k)) (hCodazzi (b i) (b j)))
    (fun i ↦ (htrace (D (b i))).trans (hDtrace (b i)))
  simpa only [ContinuousLinearMap.hilbertSchmidtInner_eq_sum_sum_inner_mul_inner _ _ b b,
    ContinuousLinearMap.bilinearHilbertSchmidtEnergy_eq_sum b b,
    ← b.sum_sq_inner_left, pow_two] using h

end OrthonormalBasis
