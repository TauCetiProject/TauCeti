/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.OrderInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp

/-!
# Multiplication by functions with bounded derivatives on `H^{s,p}` for every real `s`

Let `g : E → ℂ` be a function whose iterated derivatives of order at most `⌈|s|⌉` are bounded.
This file proves that multiplication by `g` is a bounded operator on the
Hilbert Bessel-potential space `H^s = H^{s,2}(E, F)`, for every real order `s`, including negative
orders, where the elements of `H^s` are genuine tempered distributions, and that it preserves the
Bessel-potential spaces `H^{s,p}` of tempered distributions for every real `s` and `1 < p < ∞`.
Unlike multiplication by a Schwartz function (`BesselPotentialSpace.smulLeftCLM`), the multiplier
need not decay: smooth functions whose derivatives up to order `⌈|s|⌉` are bounded, such as
constants and cut-off entries of transition matrices of vector bundles, are allowed. If `g` does
not have temperate growth, multiplication by `g` is the junk value `0`.

The matrix-valued versions follow for finite-dimensional complex Hilbert spaces `F` and `G`. For
`A : E → (F →L[ℂ] G)` of temperate growth with bounded derivatives of order at most `⌈|s|⌉`, the
pointwise multiplication `u ↦ (x ↦ A x (u x))` of Schwartz functions extends to a bounded operator
`H^s(E, F) → H^s(E, G)` (`SchwartzMap.hasSobolevExtension_bilinLeftCLM_apply`). On tempered
distributions, for `A : E → (F →L[ℂ] G)` of class `C^{⌈|s|⌉}` with bounded derivatives of order at
most `⌈|s|⌉`, `TemperedDistribution.mulLeftCLM A` preserves `H^{s,p}` for `1 < p < ∞`
(`TemperedDistribution.MemSobolev.mulLeftCLM_of_norm_iteratedFDeriv_le_natCeil`); this is
multiplication by `A` when `A` has temperate growth, and a junk value otherwise (see
`TemperedDistribution.mulLeftCLM`). These are the estimates that make localization by cutoff
functions and changes of frame bounded on the Sobolev scale of a vector bundle.

## The argument

* **Integer orders.** Multiplication by `g` maps `H^{k,p}` into itself for every integer `k` and
  `1 < p < ∞` (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast`),
  so for `p = 2`, by the closed graph theorem
  (`BesselPotentialSpace.continuous_of_continuous_toDistr`), it is bounded on `H^k`.
* **Real orders.** Between two consecutive integers by the interpolation theorem for the Hilbert
  scale (`SchwartzMap.HasSobolevExtension.interpolate`) for the bounded extension on Schwartz
  functions, and by the complex interpolation of the spaces `H^{s,p}`
  (`TemperedDistribution.MemSobolev.map_of_memSobolev_of_memSobolev`, applied through
  `TemperedDistribution.MemSobolev.map_of_forall_intCast`) for tempered distributions.
* **Matrices.** Expanding `A` in a basis `(Lᵢ)` of `F →L[ℂ] G`, multiplication by `A` is the sum
  of the scalar multiplications by the coordinates of `A` followed by the constant maps `Lᵢ`.

## Main results

* `SchwartzMap.hasSobolevExtension_smulLeftCLM`: multiplication by `g` extends to a bounded operator
  `H^s(E, F) → H^s(E, F)`, for every real `s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil`: for
  `1 < p < ∞`, if `f ∈ H^{s,p}` then `g f ∈ H^{s,p}`, for every real `s`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_schwartzMap`: in particular a Schwartz function
  multiplies `H^{s,p}` into itself, for every real `s`.
* `SchwartzMap.hasSobolevExtension_bilinLeftCLM_apply`: multiplication by a matrix-valued `A` of
  temperate growth with bounded derivatives extends to a bounded operator `H^s(E, F) → H^s(E, G)`.
* `TemperedDistribution.MemSobolev.mulLeftCLM_of_norm_iteratedFDeriv_le_natCeil`: for `A` of class
  `C^{⌈|s|⌉}` with bounded derivatives up to order `⌈|s|⌉` and `1 < p < ∞`, if `f ∈ H^{s,p}` then
  `TemperedDistribution.mulLeftCLM A f ∈ H^{s,p}`, for every real `s` (multiplication by `A` when
  `A` has temperate growth, and a junk value otherwise).

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Applied Mathematical Sciences 115,
  Springer, 2011, Chapter 4, §1 and §2 (multiplication operators on `H^s`).
* J. Bergh and J. Löfström, *Interpolation Spaces*, Grundlehren 223, Springer, 1976, §6.4
  (multipliers on Bessel-potential spaces by interpolation).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Multiplication by a function with bounded derivatives up to order `|j|` is bounded on `H^j`,
for every integer `j`, on Schwartz functions: it preserves `H^j`, so the closed graph theorem
applies. -/
private theorem hasSobolevExtension_smulLeftCLM_intCast (j : ℤ) {g : E → ℂ}
    (hbd : ∀ n ≤ j.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    HasSobolevExtension (smulLeftCLM F g) j j := by
  have hmem (f : H^{(j : ℝ), 2}(E, F)) :
      MemSobolev (j : ℝ) 2 (TemperedDistribution.smulLeftCLM F g f.toDistr) :=
    f.memSobolev_toDistr.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast (by norm_num) (by simp) hbd
  let L : H^{(j : ℝ), 2}(E, F) →ₗ[ℂ] H^{(j : ℝ), 2}(E, F) :=
    { toFun f := (hmem f).toBesselPotentialSpace
      map_add' f f' := BesselPotentialSpace.ext (by simp)
      map_smul' c f := BesselPotentialSpace.ext (by simp) }
  have hL : Continuous L :=
    BesselPotentialSpace.continuous_of_continuous_toDistr (L.restrictScalars ℝ) <|
    ((TemperedDistribution.smulLeftCLM F g).continuous.comp
      BesselPotentialSpace.continuous_toDistr).congr fun f ↦ by simp [L]
  refine hasSobolevExtension_iff.2 ⟨⟨L, hL⟩, ContinuousLinearMap.ext fun u ↦ ?_⟩
  exact BesselPotentialSpace.ext (by
    simp [L, toDistr_toBesselPotentialSpaceCLM, smulLeftCLM_toTemperedDistributionCLM_eq])

/-- **Multipliers with bounded derivatives on `H^s`, for every real `s`.** If the iterated
derivatives of `g` of order at most `⌈|s|⌉` are bounded, then multiplication by `g` on Schwartz
functions extends to a bounded operator `H^s(E, F) → H^s(E, F)`. If `g` does not have temperate
growth, this multiplication is the junk value `0`. -/
theorem hasSobolevExtension_smulLeftCLM (s : ℝ) {g : E → ℂ}
    (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    HasSobolevExtension (smulLeftCLM F g) s s := by
  have hc := Int.natCast_ceil_eq_ceil (abs_nonneg s)
  have hlow : -⌈|s|⌉ ≤ ⌊s⌋ := by
    rw [← Int.floor_neg]
    exact Int.floor_mono (neg_abs_le s)
  have hhigh : ⌈s⌉ ≤ ⌈|s|⌉ := Int.ceil_mono (le_abs_self s)
  have hfc := Int.floor_le_ceil s
  have hfloor := hasSobolevExtension_smulLeftCLM_intCast (F := F) ⌊s⌋ fun n hn ↦
    hbd n (hn.trans (by omega))
  by_cases hs : (⌊s⌋ : ℝ) = s
  · rwa [hs] at hfloor
  -- Otherwise `⌊s⌋ < s < ⌊s⌋ + 1`, and `s` interpolates between these two integer orders.
  have hlt : (⌊s⌋ : ℝ) < s := (Int.floor_le s).lt_of_ne hs
  have hceil : ⌊s⌋ + 1 ≤ ⌈s⌉ := Int.lt_ceil.2 hlt
  have hsucc := hasSobolevExtension_smulLeftCLM_intCast (F := F) (⌊s⌋ + 1) fun n hn ↦
    hbd n (hn.trans (by omega))
  set θ := s - ⌊s⌋
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [Int.lt_floor_add_one s]⟩
  have hθs : (1 - θ) * (⌊s⌋ : ℝ) + θ * ((⌊s⌋ + 1 : ℤ) : ℝ) = s := by
    push_cast
    ring
  have h := hfloor.interpolate hsucc hθ
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
  -- Expand `A` in a basis `(bᵢ)` of `F →L[ℂ] G`, with coordinate functionals `ℓᵢ`.
  let b := Module.finBasis ℂ (F →L[ℂ] G)
  let ℓ : Fin (Module.finrank ℂ (F →L[ℂ] G)) → (F →L[ℂ] G) →L[ℂ] ℂ :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hℓA (i) : (fun x ↦ ℓ i (A x)).HasTemperateGrowth :=
    hA.continuousLinearMap_comp (ℓ i)
  rw [bilinLeftCLM_apply_eq_sum Finset.univ (fun i _ ↦ hℓA i) b hA fun x ↦ by simp [ℓ]]
  refine Finset.sum_induction _ (fun T ↦ HasSobolevExtension T s s)
    (fun _ _ ↦ HasSobolevExtension.add) (hasSobolevExtension_zero s s) fun i _ ↦ ?_
  refine HasSobolevExtension.comp (hasSobolevExtension_iff.2
    ⟨BesselPotentialSpace.postcomp E s 2 (b i), ?_⟩)
    (hasSobolevExtension_smulLeftCLM s
      ((ℓ i).exists_bound_iteratedFDeriv_comp_left (hA.1.of_le (mod_cast le_top)) hbd))
  ext1 u
  exact (toBesselPotentialSpaceCLM_postcompCLM (b i) u).symm

end Matrix

end SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Multipliers with bounded derivatives preserve `H^{s,p}`, for every real `s`.** Let
`1 < p < ∞`. If the iterated derivatives of `g` of order at most `⌈|s|⌉` are bounded, then
`g f ∈ H^{s,p}` for every tempered distribution `f ∈ H^{s,p}`. If `g` does not have temperate
growth, `g f` is the junk value `0`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil (hp : 1 < p) (hp_top : p ≠ ∞)
    {s : ℝ} {g : E → ℂ}
    (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : MemSobolev s p (smulLeftCLM F g f) :=
  hf.map_of_forall_intCast hp hp_top _ fun _ hk _ hu ↦
    hu.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top fun n hn ↦ hbd n (hn.trans hk)

/-- **Schwartz multipliers preserve `H^{s,p}`, for every real `s`.** For `1 < p < ∞`,
multiplication by a Schwartz function maps `H^{s,p}` into itself. -/
theorem MemSobolev.smulLeftCLM_schwartzMap (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ} (ψ : 𝓢(E, ℂ))
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : MemSobolev s p (smulLeftCLM F ψ f) :=
  hf.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil hp hp_top
    fun n _ ↦ ⟨_, ψ.norm_iteratedFDeriv_le_seminorm ℝ n⟩

/-- **Matrix multipliers with bounded derivatives preserve `H^{s,p}`, for every real `s`.** Let
`1 < p < ∞`, let `F` and `G` be finite-dimensional and let `A : E → (F →L[ℂ] G)` be `⌈|s|⌉` times
continuously differentiable, with bounded iterated derivatives of order at most `⌈|s|⌉`. Then
`mulLeftCLM A f ∈ H^{s,p}(E, G)` for every tempered distribution `f ∈ H^{s,p}(E, F)`. This is
multiplication by `A` when `A` has temperate growth; otherwise `mulLeftCLM A` is a junk value (see
`TemperedDistribution.mulLeftCLM`). -/
theorem MemSobolev.mulLeftCLM_of_norm_iteratedFDeriv_le_natCeil [FiniteDimensional ℂ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [FiniteDimensional ℂ G]
    (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ} {A : E → F →L[ℂ] G} (hA : ContDiff ℝ ⌈|s|⌉₊ A)
    (hbd : ∀ n ≤ ⌈|s|⌉₊, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (mulLeftCLM A f) :=
  -- Each scalar function `ℓ ∘ A` inherits the derivative bounds of `A`.
  MemSobolev.mulLeftCLM_of_forall_smulLeftCLM fun ℓ ↦
    hf.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil hp hp_top
      (ℓ.exists_bound_iteratedFDeriv_comp_left hA hbd)

end TemperedDistribution
