/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.TwistedInequalities
import TauCeti.Algebra.BigOperators.AlternatingSum
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric

/-!
# The Euler characteristic from a Morse–Bott function

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i j : S j → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), the piece `S j` having
index `λ_j` (`TauCeti.IsMorseBottFamily.index`). This file proves

`χ(M) = ∑ⱼ (-1)^{λ_j} χ(S j)`

(`TauCeti.IsMorseBottFamily.eulerChar_eq_sum_neg_one_pow_index_mul_eulerChar`), with no
orientability assumption on the negative normal bundles. For a Morse function every piece is a
point, of Euler characteristic `1`, and this is the signed count of critical points
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar`). For the height
function `[x : y : z] ↦ (x² + y²) / (x² + y² + z²)` on the real projective plane, with a minimum at
a point and a critical circle of index `1`, it reads `1 = χ(pt) - χ(S¹)`.

Euler's equality for the twisted Morse–Bott counts
(`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber`)
computes `χ(M)` as `∑ⱼ (-1)^{λ_j} χ(S j; o(ν⁻ j))`, where `χ(S j; o(ν⁻ j))` is the alternating sum
of the dimensions of the homology of `S j` with coefficients in the orientation local system of its
negative normal bundle `ν⁻ j`. Every fibre of an orientation local system has rank one, so this
twisted Euler characteristic is the ordinary one
(`TauCeti.IsMorseBottFamily.finsum_neg_one_pow_mul_twistedBettiNumber`, from
`TauCeti.VectorBundleOrientationCover.finsum_finrank_twistedHomology_signLocalSystem`). The twist
therefore matters for the Morse–Bott inequalities but not for the Euler characteristic: on the real
projective plane over `ℚ` the circle contributes nothing to the twisted counts, and nothing to the
alternating sum either, since `χ(S¹) = 0`.

The pieces and `M` are of finite CW type, being compact boundaryless manifolds
(`TauCeti.FiniteCWType.of_isManifold`); the statements take these instances as arguments, and since
`TauCeti.FiniteCWType` is a proposition they apply to `eulerChar` formed with any instance. As in
`TauCeti.Geometry.Manifold.Morse.Bott.TwistedInequalities`, the manifolds lie in `Type`.

## Main results

In the namespace `TauCeti.IsMorseBottFamily`:

* `eventually_twistedBettiNumber_eq_zero`: the twisted Betti numbers of a piece vanish in all large
  degrees.
* `finsum_neg_one_pow_mul_twistedBettiNumber`: the twisted Euler characteristic of a piece is its
  Euler characteristic.
* `eulerChar_eq_sum_neg_one_pow_index_mul_eulerChar`: `χ(M) = ∑ⱼ (-1)^{λ_j} χ(S j)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
-/

public section

noncomputable section

open Bundle Filter Module Set
open TauCeti.VectorBundleOrientationCover TauCeti.LocalCoefficientSystem
open scoped ContDiff Manifold

namespace TauCeti.IsMorseBottFamily

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι] {E' H' : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  (h : IsMorseBottFamily i f)

/-! ### The twisted Euler characteristic of a piece -/

section Twisted

variable {P : ι → Type*} [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)]
  [∀ j, FiniteDimensional ℝ (P j)] (hn : (∞ : ℕ∞ω) ≠ 0)
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
  {r : ι → ℕ}
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
  (K : Type) [Field K]

include hV

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Betti numbers of a piece vanish in large degrees.** If the piece `S j` has finite
CW type, as a compact manifold does, then `dim Hₖ(S j; o(ν⁻ j) ⊗ K) = 0` for all large `k`. -/
theorem eventually_twistedBettiNumber_eq_zero (j : ι) [FiniteCWType (S j)] :
    ∀ᶠ k in atTop, h.twistedBettiNumber hn hdim g hV K j k = 0 := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ := (hV j).fiberBundle
  have := (hV j).vectorBundle
  simp only [twistedBettiNumber_def]
  exact (eventually_isZero_twistedHomology_of_finiteCWType (S j) _).mono fun _ ↦
    ModuleCat.finrank_eq_zero_of_isZero

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Euler characteristic of a piece is its Euler characteristic.** If the piece
`S j` has finite CW type, as a compact manifold does, then
`∑ₖ (-1)ᵏ dim Hₖ(S j; o(ν⁻ j) ⊗ K) = χ(S j)`, whether or not the negative normal bundle `ν⁻ j` is
orientable. -/
theorem finsum_neg_one_pow_mul_twistedBettiNumber (j : ι) [FiniteCWType (S j)] :
    ∑ᶠ k : ℕ, (-1 : ℤ) ^ k * h.twistedBettiNumber hn hdim g hV K j k = eulerChar (S j) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ := (hV j).fiberBundle
  have := (hV j).vectorBundle
  simp only [twistedBettiNumber_def]
  exact finsum_finrank_twistedHomology_signLocalSystem _

end Twisted

/-! ### The Euler characteristic of `M` -/

/-- **The Euler characteristic of a manifold from a Morse–Bott function.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold `M`, the
piece `S j` having index `λ_j`. Then `χ(M) = ∑ⱼ (-1)^{λ_j} χ(S j)`. No orientation of the negative
normal bundles is assumed. -/
theorem eulerChar_eq_sum_neg_one_pow_index_mul_eulerChar [FiniteCWType M]
    [∀ j, FiniteCWType (S j)] :
    eulerChar M = ∑ j, (-1 : ℤ) ^ h.index j * eulerChar (S j) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hdim (j : ι) := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ E - finrank ℝ (E' j))
  let _ (j : ι) := (i j).normalSpaceFiberBundle hn (hdim j)
  let _ (j : ι) := (i j).normalSpaceVectorBundle hn (hdim j)
  have (j : ι) : CompactSpace (S j) := h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  -- Choose smooth fibre metrics on the normal bundles; the negative normal spaces then form
  -- bundles of rank the indices of the pieces.
  let g (j : ι) := ((i j).nonempty_contMDiffRiemannianMetric_normalSpace hn (hdim j)).some
  have hV (j : ι) :=
    (h.isNondegenerateCriticalSubmanifold j).hasLocalSubbundleFrames_negativeNormalSpace hn
      h.contMDiff (hdim j) (g j) (h.manifoldMorseIndex_eq_index hn j)
  -- From some degree `N` on, all twisted Betti numbers of all pieces vanish.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_all.2 fun j ↦
    h.eventually_twistedBettiNumber_eq_zero hn hdim g hV ℚ j)
  set n := finrank ℝ E + N + ∑ j, h.index j
  have hrN (j : ι) : h.index j + N ≤ n + 1 := by
    have := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (h.index j)) (Finset.mem_univ j)
    omega
  rw [eulerChar_eq_finsum_finrank_singularHomology M ℚ,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) fun k hk ↦ ?_]
  · simp only [← bettiNumber_def]
    rw [h.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber hn hdim g hV ℚ
      (by omega)]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum,
      mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sum_range_ite_neg_one_pow_mul_eq_neg_one_pow_mul_finsum
      (t := fun m ↦ (h.twistedBettiNumber hn hdim g hV ℚ j m : ℤ)) (fun m hm ↦ by simp [hN m hm j])
      (hrN j),
      h.finsum_neg_one_pow_mul_twistedBettiNumber hn hdim g hV ℚ j]
  · simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hk ⊢
    by_contra hkn
    refine hk ?_
    rw [← bettiNumber_def, bettiNumber_eq_zero_of_finrank_lt (I := I) (M := M) ℚ (by omega),
      Nat.cast_zero, mul_zero]

end TauCeti.IsMorseBottFamily
