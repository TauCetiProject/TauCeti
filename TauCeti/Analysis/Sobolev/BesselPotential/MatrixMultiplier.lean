/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp

/-!
# Multiplication by functions with bounded derivatives on `H^s` for every real `s`

Let `g : E → ℂ` be a function of temperate growth whose iterated derivatives of order at most
`⌈|s|⌉` are bounded. This file proves that multiplication by `g` is a bounded operator on the
Hilbert Bessel-potential space `H^s = H^{s,2}(E, F)`, for every real order `s`, including negative
orders, where the elements of `H^s` are genuine tempered distributions. Unlike multiplication by a
Schwartz function (`BesselPotentialSpace.smulLeftCLM`), the multiplier need not decay: constant
functions, bounded smooth functions and the entries of transition matrices of vector bundles
in charts are allowed.

The matrix-valued version follows: for finite-dimensional complex Hilbert spaces `F` and `G` and
`A : E → (F →L[ℂ] G)` of temperate growth with bounded derivatives of order at most `⌈|s|⌉`,
multiplication `u ↦ (x ↦ A x (u x))` extends to a bounded operator `H^s(E, F) → H^s(E, G)`.
These are the estimates that make localization by cutoff functions and changes of frame bounded
on the Sobolev scale of a vector bundle.

## The argument

* **Nonnegative integer orders.** Multiplication by `g` maps `H^k` into itself
  (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`), so by the closed
  graph theorem (`BesselPotentialSpace.continuous_of_continuous_toDistr`) it is bounded on `H^k`.
* **Negative integer orders.** By duality: with `v = J^{-2k} (g u)`, which realizes the `H^{-k}`
  norm of `g u` in the `L²` pairing, `‖g u‖²_{H^{-k}} = ∫ ⟪g u, v⟫ = ∫ ⟪u, conj g v⟫`, and the
  conjugate `conj g` is bounded on `H^k`.
* **Real orders.** Between two consecutive integers by the interpolation theorem for the Hilbert
  scale (`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`).
* **Distributions.** The bounded extension agrees with Mathlib's multiplication of tempered
  distributions `TemperedDistribution.smulLeftCLM` on the dense subspace of Schwartz functions,
  hence everywhere.
* **Matrices.** Expanding `A` in a basis `(Lᵢ)` of `F →L[ℂ] G`, multiplication by `A` is the sum
  of the scalar multiplications by the coordinates of `A` followed by the constant maps `Lᵢ`.

## Main results

* `SchwartzMap.hasSobolevExtension_smulLeftCLM`: multiplication by `g` extends to a bounded operator
  `H^s(E, F) → H^s(E, F)`, for every real `s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil`: if `f ∈ H^s`
  then `g f ∈ H^s`, for every real `s`.
* `SchwartzMap.hasSobolevExtension_bilinLeftCLM_apply`: multiplication by a matrix-valued `A`
  extends to a bounded operator `H^s(E, F) → H^s(E, G)`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Applied Mathematical Sciences 115,
  Springer, 2011, Chapter 4, §1 and §2 (multiplication operators on `H^s` and duality).
* J. Bergh and J. Löfström, *Interpolation Spaces*, Grundlehren 223, Springer, 1976, §6.4
  (multipliers on Bessel-potential spaces by interpolation).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BesselPotentialSpace ComplexConjugate InnerProductSpace

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Multiplication by a function with bounded derivatives up to order `k` is bounded on `H^k`, on
Schwartz functions: it preserves `H^k`, so the closed graph theorem applies. -/
private theorem exists_norm_smulLeftCLM_le_natCast (k : ℕ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM k 2 (smulLeftCLM F g u)‖ ≤
      C * ‖toBesselPotentialSpaceCLM k 2 u‖ := by
  have hmem (f : H^{(k : ℝ), 2}(E, F)) :
      MemSobolev (k : ℝ) 2 (TemperedDistribution.smulLeftCLM F g f.toDistr) :=
    f.memSobolev_toDistr.smulLeftCLM_of_norm_iteratedFDeriv_le (by norm_num) (by simp) hg hbd
  let L : H^{(k : ℝ), 2}(E, F) →ₗ[ℂ] H^{(k : ℝ), 2}(E, F) :=
    { toFun f := (hmem f).toBesselPotentialSpace
      map_add' f f' := BesselPotentialSpace.ext (by simp)
      map_smul' c f := BesselPotentialSpace.ext (by simp) }
  have hL : Continuous L :=
    BesselPotentialSpace.continuous_of_continuous_toDistr (L.restrictScalars ℝ) <|
    ((TemperedDistribution.smulLeftCLM F g).continuous.comp
      BesselPotentialSpace.continuous_toDistr).congr fun f ↦ by simp [L]
  let T : H^{(k : ℝ), 2}(E, F) →L[ℂ] H^{(k : ℝ), 2}(E, F) := ⟨L, hL⟩
  refine ⟨‖T‖, norm_nonneg _, fun u ↦ ?_⟩
  have hT : T (toBesselPotentialSpaceCLM k 2 u) =
      toBesselPotentialSpaceCLM k 2 (smulLeftCLM F g u) :=
    BesselPotentialSpace.ext (by
      simp [T, L, toDistr_toBesselPotentialSpaceCLM, smulLeftCLM_toTemperedDistributionCLM_eq])
  rw [← hT]
  exact T.le_opNorm _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The conjugate of a function with bounded derivatives has the same derivative bounds. -/
private theorem norm_iteratedFDeriv_conj (g : E → ℂ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ conj (g y)) x‖ = ‖iteratedFDeriv ℝ n g x‖ :=
  Complex.conjLIE.norm_iteratedFDeriv_comp_left g x n

/-- Multiplication by a function with bounded derivatives up to order `k` is bounded on `H^{-k}`,
on Schwartz functions. The test function `v = J^{-2k} (g u)` realizes the `H^{-k}` norm of `g u`
in the `L²` pairing, and `∫ ⟪g u, v⟫ = ∫ ⟪u, conj g v⟫` is bounded by the `H^k` bound for
`conj g`. -/
private theorem exists_norm_smulLeftCLM_le_neg_natCast (k : ℕ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM (-k) 2 (smulLeftCLM F g u)‖ ≤
      C * ‖toBesselPotentialSpaceCLM (-k) 2 u‖ := by
  set g' : E → ℂ := fun x ↦ conj (g x)
  have hg' : g'.HasTemperateGrowth := Complex.conjCLE.hasTemperateGrowth.comp hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_smulLeftCLM_le_natCast (F := F) k hg' fun n hn ↦ by
    obtain ⟨C, hC⟩ := hbd n hn
    exact ⟨C, fun x ↦ (norm_iteratedFDeriv_conj g n x).trans_le (hC x)⟩
  refine ⟨C, hC0, fun u ↦ ?_⟩
  set w := smulLeftCLM F g u
  set v := besselPotentialCLM ((-2 * k : ℝ) : ℂ) w
  set N := ‖toBesselPotentialSpaceCLM (-k) 2 w‖
  have hvN : ‖toBesselPotentialSpaceCLM k 2 v‖ = N := by
    rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
      show (k : ℝ) + -2 * k = -k by ring]
  have hvL :
      (toBesselPotentialSpaceCLM k 2 v).toLp = (toBesselPotentialSpaceCLM (-k) 2 w).toLp := by
    rw [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
      toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
      besselPotentialCLM_besselPotentialCLM_apply,
      show ((-2 * k : ℝ) : ℂ) + (k : ℝ) = ((-k : ℝ) : ℂ) by push_cast; ring]
  have hpair : ∫ x, ⟪w x, v x⟫_ℂ = ((N ^ 2 : ℝ) : ℂ) := by
    rw [← inner_toLp_toBesselPotentialSpaceCLM_neg (k : ℝ), hvL, inner_self_eq_norm_sq_to_K,
      BesselPotentialSpace.norm_toLp_eq]
    norm_cast
  -- Move the multiplier to the other side of the pairing.
  have hmove : ∫ x, ⟪w x, v x⟫_ℂ = ∫ x, ⟪u x, smulLeftCLM F g' v x⟫_ℂ := by
    congr 1
    funext x
    simp only [w, smulLeftCLM_apply_apply hg, smulLeftCLM_apply_apply hg', inner_smul_left,
      inner_smul_right, g']
  have hle : N ^ 2 ≤ ‖toBesselPotentialSpaceCLM (-k) 2 u‖ * (C * N) := by
    have h := norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm (k : ℝ) u
      (smulLeftCLM F g' v)
    rw [← hmove, hpair, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    exact h.trans (by gcongr; exact (hC v).trans_eq (by rw [hvN]))
  -- `N ^ 2 ≤ C ‖u‖ N`, so `N ≤ C ‖u‖`.
  rcases (norm_nonneg _ : 0 ≤ N).eq_or_lt with h0 | h0
  · exact h0.symm.trans_le (by positivity)
  · nlinarith

/-- Multiplication by a function with bounded derivatives up to order `|j|` is bounded on `H^j`,
for every integer `j`, on Schwartz functions. -/
private theorem exists_norm_smulLeftCLM_le_intCast (j : ℤ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hbd : ∀ n ≤ j.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM j 2 (smulLeftCLM F g u)‖ ≤
      C * ‖toBesselPotentialSpaceCLM j 2 u‖ := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [Int.cast_natCast]
    exact exists_norm_smulLeftCLM_le_natCast k hg (by simpa using hbd)
  · rw [Int.cast_neg, Int.cast_natCast]
    exact exists_norm_smulLeftCLM_le_neg_natCast k hg (by simpa using hbd)

/-- An integer between `-⌈|s|⌉` and `⌈|s|⌉` has absolute value at most `⌈|s|⌉`. -/
private theorem natAbs_le_natCeil_abs {s : ℝ} {j : ℤ} (h₀ : -⌈|s|⌉ ≤ j) (h₁ : j ≤ ⌈|s|⌉) :
    j.natAbs ≤ ⌈|s|⌉₊ := by
  have hc := Int.natCast_ceil_eq_ceil (abs_nonneg s)
  omega

/-- **Multipliers with bounded derivatives on `H^s`, for every real `s`.** If `g` has temperate
growth and its iterated derivatives of order at most `⌈|s|⌉` are bounded, then multiplication by
`g` on Schwartz functions extends to a bounded operator `H^s(E, F) → H^s(E, F)`. -/
theorem hasSobolevExtension_smulLeftCLM (s : ℝ) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    HasSobolevExtension (smulLeftCLM F g) s s := by
  rw [hasSobolevExtension_iff_exists_norm_le]
  have hlow : -⌈|s|⌉ ≤ ⌊s⌋ := by
    rw [← Int.floor_neg]
    exact Int.floor_mono (neg_abs_le s)
  have hhigh : ⌈s⌉ ≤ ⌈|s|⌉ := Int.ceil_mono (le_abs_self s)
  have hfloor := exists_norm_smulLeftCLM_le_intCast (F := F) ⌊s⌋ hg fun n hn ↦
    hbd n (hn.trans (natAbs_le_natCeil_abs hlow ((Int.floor_le_ceil s).trans hhigh)))
  by_cases hs : (⌊s⌋ : ℝ) = s
  · obtain ⟨C, hC0, hC⟩ := hfloor
    exact ⟨C, hC0, by rwa [hs] at hC⟩
  -- Otherwise `⌊s⌋ < s < ⌊s⌋ + 1`, and `s` interpolates between these two integer orders.
  have hlt : (⌊s⌋ : ℝ) < s := (Int.floor_le s).lt_of_ne hs
  have hceil : ⌊s⌋ + 1 ≤ ⌈s⌉ := Int.lt_ceil.2 hlt
  obtain ⟨C₀, hC₀0, hC₀⟩ := hfloor
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_smulLeftCLM_le_intCast (F := F) (⌊s⌋ + 1) hg fun n hn ↦
    hbd n (hn.trans (natAbs_le_natCeil_abs (by omega) (by omega)))
  set θ := s - ⌊s⌋
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [Int.lt_floor_add_one s]⟩
  have hθs : (1 - θ) * (⌊s⌋ : ℝ) + θ * ((⌊s⌋ + 1 : ℤ) : ℝ) = s := by
    push_cast
    ring
  refine ⟨C₀ ^ (1 - θ) * C₁ ^ θ, by positivity, fun u ↦ ?_⟩
  have h := norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm
    (T := (smulLeftCLM F g).toLinearMap) hC₀0 hC₁0 hC₀ hC₁ hθ u
  rwa [hθs] at h

section Matrix

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- **Matrix multipliers with bounded derivatives on `H^s`, for every real `s`.** Let `F` and `G`
be finite-dimensional complex Hilbert spaces and `A : E → (F →L[ℂ] G)` a function of temperate
growth whose iterated derivatives of order at most `⌈|s|⌉` are bounded. Then the multiplication
`u ↦ (x ↦ A x (u x))` of Schwartz functions extends to a bounded operator
`H^s(E, F) → H^s(E, G)`. -/
theorem hasSobolevExtension_bilinLeftCLM_apply (s : ℝ) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    HasSobolevExtension (bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA) s s := by
  -- Expand `A` in a basis `(Lᵢ)` of `F →L[ℂ] G`, with coordinate functionals `ℓᵢ`.
  let b := Module.finBasis ℂ (F →L[ℂ] G)
  let ℓ : Fin (Module.finrank ℂ (F →L[ℂ] G)) → (F →L[ℂ] G) →L[ℂ] ℂ :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hℓA (i) : (fun x ↦ ℓ i (A x)).HasTemperateGrowth :=
    ((ℓ i).restrictScalars ℝ).hasTemperateGrowth.comp hA
  have hsum : bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA =
      ∑ i, (postcompCLM (b i)).comp (smulLeftCLM F fun x ↦ ℓ i (A x)) := by
    ext u x
    have key (i) : smulLeftCLM F (fun x ↦ ℓ i (A x)) u x = ℓ i (A x) • u x :=
      smulLeftCLM_apply_apply (hℓA i) u x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.apply_apply, FunLike.coe_sum,
      Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, postcompCLM_apply, key,
      map_smul]
    simp only [ℓ, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr (A x)]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
  rw [hsum]
  refine Finset.sum_induction _ (fun T ↦ HasSobolevExtension T s s)
    (fun _ _ ↦ HasSobolevExtension.add) (hasSobolevExtension_zero s s) fun i _ ↦ ?_
  refine HasSobolevExtension.comp (hasSobolevExtension_iff.2
    ⟨BesselPotentialSpace.postcomp E s 2 (b i), ?_⟩)
    (hasSobolevExtension_smulLeftCLM s (hℓA i) fun n hn ↦ ?_)
  · ext1 u
    exact (toBesselPotentialSpaceCLM_postcompCLM (b i) u).symm
  · obtain ⟨C, hC⟩ := hbd n hn
    exact ⟨‖(ℓ i).restrictScalars ℝ‖ * C, fun x ↦
      (((ℓ i).restrictScalars ℝ).norm_iteratedFDeriv_comp_left hA.1.contDiffAt
        (mod_cast le_top)).trans (by gcongr; exact hC x)⟩

end Matrix

end SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **Multipliers with bounded derivatives preserve `H^s`, for every real `s`.** If `g` has
temperate growth and its iterated derivatives of order at most `⌈|s|⌉` are bounded, then
`g f ∈ H^s` for every tempered distribution `f ∈ H^s`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil {s : ℝ} {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) : MemSobolev s 2 (smulLeftCLM F g f) := by
  obtain ⟨T, hT⟩ := SchwartzMap.hasSobolevExtension_iff.1
    (SchwartzMap.hasSobolevExtension_smulLeftCLM (F := F) s hg hbd)
  -- The extension acts on the underlying tempered distributions as multiplication by `g`: both
  -- sides are continuous and agree on the dense subspace of Schwartz functions.
  have hdist : (fun U : H^{s}(E, F) ↦ (T U).toDistr) = fun U ↦ smulLeftCLM F g U.toDistr := by
    refine (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (E := E) (F := F) s (p := 2)
      ENNReal.ofNat_ne_top).equalizer
      (BesselPotentialSpace.continuous_toDistr.comp T.continuous)
      ((smulLeftCLM F g).continuous.comp BesselPotentialSpace.continuous_toDistr) ?_
    funext u
    have hu : T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
        SchwartzMap.toBesselPotentialSpaceCLM s 2 (SchwartzMap.smulLeftCLM F g u) :=
      congrArg (fun L ↦ L u) hT
    simp [hu, smulLeftCLM_toTemperedDistributionCLM_eq]
  have h := congrFun hdist hf.toBesselPotentialSpace
  simp only [MemSobolev.toBesselPotentialSpace_toDistr] at h
  rw [← h]
  exact BesselPotentialSpace.memSobolev_toDistr _

end TemperedDistribution
