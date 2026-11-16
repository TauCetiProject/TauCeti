/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.MapCLM

/-!
# Multiplication by matrix-valued functions on Besov spaces

Let `F` and `G` be finite-dimensional complex normed spaces, `s ∈ ℝ`, and let
`A : E → (F →L[ℂ] G)` be a smooth matrix-valued function of temperate growth whose derivatives of
order at most `N` are bounded, for a natural number `N > |s|`. Multiplication by `A` maps the
inhomogeneous Besov space `B^s_{p,q}(E; F)` boundedly to `B^s_{p,q}(E; G)` for all
`1 ≤ p, q ≤ ∞` (`TauCeti.BesovSpace.mulLeftCLM`), with operator norm at most `C M`, where `M`
bounds the derivatives of `A` of order at most `N` and `C` depends only on the bump function `φ`,
on `s`, on `N` and on `F` and `G`, not on `p` or `q`
(`TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`). If `A x` is invertible for every `x` and its
inverse has the same properties, multiplication by `A` is an isomorphism
`B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)` (`TauCeti.BesovSpace.mulLeftEquiv`). These are the changes of
frame under which Besov norms of sections of vector bundles are compared in local
trivializations, including the Hölder–Zygmund scale `B^s_{∞,∞}`.

The proof reduces to the scalar case `TauCeti.BesovSpace.smulLeftCLM`. In a basis `(L k)` of the
finite-dimensional space `F →L[ℂ] G`, `A x = ∑ k, c k x • L k`, the coordinates `c k` are scalar
functions with derivatives bounded by a constant multiple of those of `A`, and
`A u = ∑ k, L k (c k u)` (`TemperedDistribution.mulLeftCLM_eq_sum`). A constant operator `L`
acts on the blocks of `u`, since the Littlewood–Paley blocks act on the test functions, so it maps
`B^s_{p,q}(E; F)` to `B^s_{p,q}(E; G)` with norm at most `‖L‖` (`TauCeti.BesovSpace.postcomp`).

## Main declarations

* `TauCeti.BesovSpace.postcomp`: a continuous linear map `L : F →L[ℂ] G` applied to the values,
  `B^s_{p,q}(E; F) →L[ℂ] B^s_{p,q}(E; G)`, of norm at most `‖L‖`.
* `TemperedDistribution.MemBesov.mulLeftCLM`: `B^s_{p,q}` is stable under multiplication by
  matrix-valued functions of temperate growth with bounded derivatives of order at most
  `⌊|s|⌋₊ + 1`.
* `TauCeti.BesovSpace.mulLeftCLM`: the multiplication as a bounded operator, with its tempered
  distribution `TauCeti.BesovSpace.toDistr_mulLeftCLM` and its norm bound
  `TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`.
* `TauCeti.BesovSpace.mulLeftCLM_comp_mulLeftCLM`, `TauCeti.BesovSpace.mulLeftCLM_const`: the
  multiplications compose as the functions do, and constant functions act by `postcomp`.
* `TauCeti.BesovSpace.mulLeftEquiv`: multiplication by a pointwise invertible function.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (smooth functions as
  pointwise multipliers of Besov spaces).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

namespace TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

omit [CompleteSpace F] [CompleteSpace G] in
/-- Applying a continuous linear map `L` to the values of `u` commutes with the Littlewood–Paley
blocks. -/
theorem littlewoodPaleyBlock_postcomp (L : F →L[ℂ] G) (j : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock G φ j (PointwiseConvergenceCLM.postcomp _ L u) =
      PointwiseConvergenceCLM.postcomp _ L (littlewoodPaleyBlock F φ j u) := by
  simp only [littlewoodPaleyBlock_eq_fourierMultiplierCLM, postcomp_fourierMultiplierCLM]

/-- The `Lᵖ` function `L ∘ f` has the tempered distribution obtained by applying `L` to the values
of the tempered distribution of `f`. -/
private theorem toTemperedDistribution_compLp (L : F →L[ℂ] G) (f : Lp F p (volume : Measure E)) :
    ((L.compLp f : Lp G p (volume : Measure E)) : 𝓢'(E, G)) =
      PointwiseConvergenceCLM.postcomp _ L (f : 𝓢'(E, F)) := by
  ext ψ
  rw [Lp.toTemperedDistribution_compLp_apply, postcomp_apply_apply]

/-- **Constant operators on Besov spaces.** If `u ∈ B^s_{p,q}(E; F)` and `L : F →L[ℂ] G`, then
`L u ∈ B^s_{p,q}(E; G)`. -/
theorem MemBesov.postcomp {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (L : F →L[ℂ] G) :
    MemBesov φ s p q (PointwiseConvergenceCLM.postcomp _ L u) := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨fun j ↦ L.compLp (f j), fun j ↦ ?_,
    (hmem.const_mul ‖L‖).mono fun j ↦ ?_⟩
  · rw [littlewoodPaleyBlock_postcomp, hf j, toTemperedDistribution_compLp]
  · rw [Real.norm_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ (s * j) * ‖L.compLp (f j)‖ ≤ (2 : ℝ) ^ (s * j) * (‖L‖ * ‖f j‖) := by
          gcongr
          exact L.norm_compLp_le (f j)
      _ = ‖L‖ * ((2 : ℝ) ^ (s * j) * ‖f j‖) := by ring

end TemperedDistribution

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Constant operators -/

omit [CompleteSpace F] [CompleteSpace G] in
/-- `ContinuousLinearMap.compLpL` is the bundled form of `ContinuousLinearMap.compLp`. -/
private theorem compLpL_apply (L : F →L[ℂ] G) (f : Lp F p (volume : Measure E)) :
    L.compLpL p volume f = L.compLp f :=
  (rfl)

/-- The weighted blocks of `L u`: `L` applied to the weighted blocks of `u`. -/
private def postcompWeightedBlocks (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  lp.ampliation ℕ q (L.compLpL p (volume : Measure E)) u.weightedBlocks

private theorem coe_postcompWeightedBlocks_apply (L : F →L[ℂ] G) (u : BesovSpace F φ s p q)
    (j : ℕ) :
    (postcompWeightedBlocks L u j : 𝓢'(E, G)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) •
      littlewoodPaleyBlock G φ j (PointwiseConvergenceCLM.postcomp _ L u.toDistr) := by
  rw [postcompWeightedBlocks, lp.ampliation_apply_apply, compLpL_apply,
    toTemperedDistribution_compLp, u.coe_weightedBlocks_apply, map_smul,
    littlewoodPaleyBlock_postcomp]

/-- `L u` as an element of `B^s_{p,q}(E; G)`. -/
private def postcompAux (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) : BesovSpace G φ s p q :=
  ⟨PointwiseConvergenceCLM.postcomp _ L u.toDistr, postcompWeightedBlocks L u,
    coe_postcompWeightedBlocks_apply L u⟩

private theorem weightedBlocks_postcompAux (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcompAux L u).weightedBlocks = postcompWeightedBlocks L u :=
  (rfl)

private theorem norm_postcompAux_le (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    ‖postcompAux L u‖ ≤ ‖L‖ * ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks, weightedBlocks_postcompAux,
    postcompWeightedBlocks]
  exact (lp.ampliation ℕ q (L.compLpL p (volume : Measure E))).le_of_opNorm_le
    ((lp.norm_ampliation_le _).trans L.norm_compLpL_le) u.weightedBlocks

variable (φ s p q) in
/-- **Constant operators on Besov spaces.** A continuous linear map `L : F →L[ℂ] G`, applied to
the values, as a bounded operator `B^s_{p,q}(E; F) → B^s_{p,q}(E; G)`. It acts on the weighted
blocks by `L`, so its norm is at most `‖L‖` (`TauCeti.BesovSpace.norm_postcomp_le`). -/
def postcomp (L : F →L[ℂ] G) : BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  LinearMap.mkContinuous
    { toFun := postcompAux L
      map_add' u v := ext (map_add (PointwiseConvergenceCLM.postcomp _ L) u.toDistr v.toDistr)
      map_smul' c u := ext (map_smul (PointwiseConvergenceCLM.postcomp _ L) c u.toDistr) }
    ‖L‖ (norm_postcompAux_le L)

@[simp]
theorem toDistr_postcomp (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcomp φ s p q L u).toDistr = PointwiseConvergenceCLM.postcomp _ L u.toDistr :=
  (rfl)

/-- The norm of `TauCeti.BesovSpace.postcomp L` is at most `‖L‖`. -/
theorem norm_postcomp_le (L : F →L[ℂ] G) : ‖postcomp (E := E) φ s p q L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

/-- Applying `L` and then `M` to the values is applying `M ∘ L`. -/
theorem postcomp_comp (M : G →L[ℂ] H) (L : F →L[ℂ] G) :
    postcomp (E := E) φ s p q M ∘L postcomp φ s p q L = postcomp φ s p q (M.comp L) := by
  ext1 u
  ext1
  ext ψ
  simp only [ContinuousLinearMap.comp_apply, toDistr_postcomp, postcomp_apply_apply]

@[simp]
theorem postcomp_id : postcomp (E := E) φ s p q (ContinuousLinearMap.id ℂ F) = .id ℂ _ := by
  ext1 u
  ext1
  ext ψ
  simp only [toDistr_postcomp, postcomp_apply_apply, ContinuousLinearMap.id_apply]

/-! ### Matrix-valued functions -/

section Matrix

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- The `k`-th coordinate in the standard basis of `F →L[ℂ] G`, as a real-linear functional. -/
private def coordCLM (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) : (F →L[ℂ] G) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj k).comp
    (Module.finBasis ℂ (F →L[ℂ] G)).equivFunL.toContinuousLinearMap).restrictScalars ℝ

omit [CompleteSpace F] [CompleteSpace G] in
private theorem coordCLM_apply (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) (L : F →L[ℂ] G) :
    coordCLM k L = (Module.finBasis ℂ (F →L[ℂ] G)).equivFun L k :=
  (rfl)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- A function is the combination of the basis of `F →L[ℂ] G` with its coordinates. -/
private theorem eq_sum_coordCLM (A : E → F →L[ℂ] G) (x : E) :
    A x = ∑ k, coordCLM k (A x) • Module.finBasis ℂ (F →L[ℂ] G) k := by
  simp [coordCLM_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  [CompleteSpace G] in
/-- The derivatives of the coordinates of `A` are bounded by those of `A`. -/
private theorem norm_iteratedFDeriv_coordCLM_comp_le {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (coordCLM k ∘ A) x‖ ≤ ‖coordCLM k‖ * ‖iteratedFDeriv ℝ n A x‖ :=
  (coordCLM k).norm_iteratedFDeriv_comp_left (hA.1.contDiffAt) (mod_cast le_top)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  [CompleteSpace G] in
/-- Bounded derivatives of `A` give bounded derivatives of its coordinates. -/
private theorem exists_norm_iteratedFDeriv_coordCLM_comp_le {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) {N : ℕ}
    (hbd : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) :
    ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (coordCLM k ∘ A) x‖ ≤ C := fun n hn ↦ by
  obtain ⟨C, hC⟩ := hbd n hn
  exact ⟨‖coordCLM k‖ * C, fun x ↦ (norm_iteratedFDeriv_coordCLM_comp_le hA k n x).trans
    (mul_le_mul_of_nonneg_left (hC x) (by positivity))⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  [CompleteSpace G] in
/-- The product `A u` as the sum `∑ k, L k (c k u)` over the basis `(L k)` of `F →L[ℂ] G`, with
the coordinates `c k` of `A`. -/
private theorem mulLeftCLM_eq_sum_coordCLM {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) :
    TemperedDistribution.mulLeftCLM A = ∑ k, PointwiseConvergenceCLM.postcomp _
      (Module.finBasis ℂ (F →L[ℂ] G) k) ∘L TemperedDistribution.smulLeftCLM F (coordCLM k ∘ A) :=
  mulLeftCLM_eq_sum Finset.univ (fun k _ ↦ (coordCLM k).hasTemperateGrowth.comp hA) _
    (eq_sum_coordCLM A)

variable (φ s p q) in
/-- **Multiplication by a matrix-valued function on Besov spaces.** For a function
`A : E → (F →L[ℂ] G)` of temperate growth whose derivatives of order at most `⌊|s|⌋₊ + 1` are
bounded, the multiplication `u ↦ A u` (`TemperedDistribution.mulLeftCLM`) as a bounded operator
`B^s_{p,q}(E; F) → B^s_{p,q}(E; G)`. Its norm is bounded by a constant depending only on `φ`, `s`,
`N`, `F` and `G` times a bound for the derivatives of `A` of order at most `N`, for any natural
number `N > |s|` (`TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`). -/
def mulLeftCLM (A : E → F →L[ℂ] G) (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  ∑ k, postcomp φ s p q (Module.finBasis ℂ (F →L[ℂ] G) k) ∘L
    smulLeftCLM F φ s p q (coordCLM k ∘ A) ((coordCLM k).hasTemperateGrowth.comp hA)
      (exists_norm_iteratedFDeriv_coordCLM_comp_le hA hbd k)

@[simp]
theorem toDistr_mulLeftCLM {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    (mulLeftCLM φ s p q A hA hbd u).toDistr = TemperedDistribution.mulLeftCLM A u.toDistr := by
  rw [mulLeftCLM_eq_sum_coordCLM hA, ← toDistrCLM_apply, mulLeftCLM, sum_apply, map_sum,
    sum_apply]
  simp

end Matrix

end TauCeti.BesovSpace

namespace TemperedDistribution

open TauCeti

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Matrix-valued multipliers of Besov spaces.** If `u ∈ B^s_{p,q}(E; F)` and
`A : E → (F →L[ℂ] G)` is a function of temperate growth whose derivatives of order at most
`⌊|s|⌋₊ + 1`, the least natural number exceeding `|s|`, are bounded, then
`A u ∈ B^s_{p,q}(E; G)`. -/
theorem MemBesov.mulLeftCLM {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    MemBesov φ s p q (TemperedDistribution.mulLeftCLM A u) := by
  rw [← hu.toDistr_toBesovSpace, ← BesovSpace.toDistr_mulLeftCLM hA hbd]
  exact BesovSpace.memBesov_toDistr _

end TemperedDistribution

namespace TauCeti.BesovSpace

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F G) in
/-- **The norm of a matrix-valued multiplier of Besov spaces.** Let `N` be a natural number with
`|s| < N`. There is `C`, depending only on `φ`, `s`, `N`, `F` and `G`, with the following
property. If the derivatives of order at most `N` of `A : E → (F →L[ℂ] G)` are bounded by `M`,
then multiplication by `A` has operator norm at most `C M` from `B^s_{p,q}(E; F)` to
`B^s_{p,q}(E; G)` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_mulLeftCLM_le (φ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {A : E → F →L[ℂ] G}
      (hA : A.HasTemperateGrowth)
      (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) {M : ℝ},
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ M) →
      ‖mulLeftCLM φ s p q A hA hbd‖ ≤ C * M := by
  obtain ⟨C, hC, hmul⟩ := exists_norm_smulLeftCLM_le (F := F) (s := s) φ hN
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  refine ⟨C * ∑ k, ‖b k‖ * ‖coordCLM k‖, by positivity,
    fun {p q} _ _ A hA hbd M hAM ↦ ?_⟩
  -- Each term `L k (c k u)` has norm at most `‖L k‖ C ‖c k‖_{C^N}`, and the derivatives of the
  -- coordinate `c k` are bounded by `‖coordCLM k‖ M`.
  calc ‖mulLeftCLM φ s p q A hA hbd‖
      ≤ ∑ k, ‖postcomp φ s p q (b k) ∘L smulLeftCLM F φ s p q (coordCLM k ∘ A)
          ((coordCLM k).hasTemperateGrowth.comp hA)
          (exists_norm_iteratedFDeriv_coordCLM_comp_le hA hbd k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖b k‖ * (C * (‖coordCLM k‖ * M)) := by
        refine Finset.sum_le_sum fun k _ ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        refine mul_le_mul (norm_postcomp_le _) (hmul _ _ fun n hn x ↦ ?_) (norm_nonneg _)
          (norm_nonneg _)
        exact (norm_iteratedFDeriv_coordCLM_comp_le hA k n x).trans
          (mul_le_mul_of_nonneg_left (hAM n hn x) (by positivity))
    _ = C * (∑ k, ‖b k‖ * ‖coordCLM k‖) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **Constant functions.** Multiplication by a constant `L` is `TauCeti.BesovSpace.postcomp`. -/
theorem mulLeftCLM_const (L : F →L[ℂ] G)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ n (fun _ : E ↦ L) x‖ ≤ C) :
    mulLeftCLM φ s p q (fun _ : E ↦ L) (.const L) hbd = postcomp φ s p q L := by
  ext1 u
  ext1
  rw [toDistr_mulLeftCLM, TemperedDistribution.mulLeftCLM_const, toDistr_postcomp]

/-- **Composition.** For `A : E → (F →L[ℂ] G)` and `B : E → (G →L[ℂ] H)`, multiplying by `A` and
then by `B` is multiplying by the pointwise composition `x ↦ B x ∘ A x`. -/
theorem mulLeftCLM_comp_mulLeftCLM [FiniteDimensional ℂ H] {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] H} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hB : B.HasTemperateGrowth)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : (fun x ↦ (B x).comp (A x)).HasTemperateGrowth)
    (hbdBA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ (B x).comp (A x)) x‖ ≤ C) :
    mulLeftCLM φ s p q B hB hbdB ∘L mulLeftCLM φ s p q A hA hbdA =
      mulLeftCLM φ s p q (fun x ↦ (B x).comp (A x)) hBA hbdBA := by
  ext1 u
  ext1
  rw [ContinuousLinearMap.comp_apply, toDistr_mulLeftCLM, toDistr_mulLeftCLM, toDistr_mulLeftCLM,
    ← ContinuousLinearMap.comp_apply (TemperedDistribution.mulLeftCLM B),
    TemperedDistribution.mulLeftCLM_comp_mulLeftCLM hA hB]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  [CompleteSpace G] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G] in
/-- The derivatives of a constant function are bounded. -/
private theorem exists_norm_iteratedFDeriv_const_le (L : F →L[ℂ] G) (N : ℕ) :
    ∀ n ≤ N, ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ n (fun _ : E ↦ L) x‖ ≤ C := fun n _ ↦
  ⟨‖L‖, fun x ↦ by
    rcases n with _ | n
    · simp
    · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]⟩

omit [FiniteDimensional ℂ G] in
/-- Multiplication by the identity is the identity. -/
private theorem mulLeftCLM_eq_id {C : E → F →L[ℂ] F} (hC : ∀ x, C x = .id ℂ F)
    (hC' : C.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ M, ∀ x, ‖iteratedFDeriv ℝ n C x‖ ≤ M) :
    mulLeftCLM φ s p q C hC' hbd = .id ℂ _ := by
  obtain rfl : C = fun _ ↦ .id ℂ F := funext hC
  rw [mulLeftCLM_const, postcomp_id]

variable (φ s p q) in
/-- **Invertible matrix-valued functions.** If `A : E → (F →L[ℂ] G)` and
`A' : E → (G →L[ℂ] F)` are pointwise inverse to each other, both of temperate growth with bounded
derivatives of order at most `⌊|s|⌋₊ + 1`, then multiplication by `A` is an isomorphism
`B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)` with inverse the multiplication by `A'`. -/
def mulLeftEquiv {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace G φ s p q :=
  have hL : (fun x ↦ (A' x).comp (A x)) = fun _ ↦ .id ℂ F := funext hleft
  have hR : (fun x ↦ (A x).comp (A' x)) = fun _ ↦ .id ℂ G := funext hright
  ContinuousLinearEquiv.equivOfInverse' (mulLeftCLM φ s p q A hA hbdA)
    (mulLeftCLM φ s p q A' hA' hbdA')
    ((mulLeftCLM_comp_mulLeftCLM hA' hbdA' hA hbdA (by rw [hR]; exact .const _)
      (by rw [hR]; exact exists_norm_iteratedFDeriv_const_le _ _)).trans
      (mulLeftCLM_eq_id hright _ _))
    ((mulLeftCLM_comp_mulLeftCLM hA hbdA hA' hbdA' (by rw [hL]; exact .const _)
      (by rw [hL]; exact exists_norm_iteratedFDeriv_const_le _ _)).trans
      (mulLeftCLM_eq_id hleft _ _))

@[simp]
theorem coe_mulLeftEquiv {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    (mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright : _ →L[ℂ] _) =
      mulLeftCLM φ s p q A hA hbdA :=
  (rfl)

@[simp]
theorem coe_mulLeftEquiv_symm {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    ((mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright).symm : _ →L[ℂ] _) =
      mulLeftCLM φ s p q A' hA' hbdA' :=
  (rfl)

end TauCeti.BesovSpace
