/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density.Lp

/-!
# Reconstruction and density in the Sobolev spaces of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over their sources and
cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. The Sobolev space `H^s` of `A`
(`TauCeti.SquareChartPartition.sobolevSpace`) is the closed subspace of the Hilbert sum
`⨁ᵢⱼ H^s(E, ℂ)` made of the tuples of localizations `χᵢ Tᵢⱼ` of the real functionals `T` on the
bundle tests of `V` that are `H^s` with respect to `A`.

This file shows that the **reconstruction** `(uᵢⱼ) ↦ (s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ))`
(`TauCeti.SquareChartPartition.reconstruction`) of an arbitrary tuple in `⨁ᵢⱼ H^s(E, ℂ)` is `H^s`
with respect to `A` (`TauCeti.SquareChartPartition.memSobolev_reconstruction`), so that localizing
it is a bounded projection of `⨁ᵢⱼ H^s(E, ℂ)` onto `H^s`
(`TauCeti.SquareChartPartition.sobolevReconstruction`, which fixes the elements of `H^s`,
`TauCeti.SquareChartPartition.sobolevReconstruction_coe`). Since Schwartz functions are dense in
`H^s(E, ℂ)`, the functionals reconstructed from tuples of Schwartz functions are dense in `H^s`
(`TauCeti.SquareChartPartition.denseRange_sobolevReconstruction_toBesselPotentialSpaceCLM`). They
are `H^t` with respect to `A` for every `t`
(`TauCeti.SquareChartPartition.memSobolev_reconstruction_schwartzMap`): they are the functionals
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ`, integrals of the chart readings of `s` against smooth rapidly decreasing
functions. Consequently, for `r ≤ s`, the
inclusion `H^s ⊆ H^r` has dense range
(`TauCeti.SquareChartPartition.denseRange_inclusion`). Identifying these reconstructions with
the functionals given by smooth sections of `V` is not done here.

## The argument

The regularity of reconstructions is the case `p = 2` of the corresponding statement for the
Bessel-potential spaces `H^{s,p}` of `A`
(`TauCeti.SquareChartPartition.memBesselPotential_reconstruction`), proved by reading the
reconstruction of each single entry in the charts of `A`. The reconstruction then defines a linear
map from `⨁ᵢⱼ H^s(E, ℂ)` to the Banach space `H^s`, which is continuous by the closed graph theorem:
the functional represented by an element of either space depends continuously on it, test by test.
No Sobolev estimate for changes of chart is needed.

## Main declarations

* `TauCeti.SquareChartPartition.memSobolev_reconstruction`: the reconstruction of a tuple of `H^s`
  tempered distributions is `H^s` with respect to `A`.
* `TauCeti.SquareChartPartition.sobolevReconstruction`: the reconstruction as a bounded operator
  from `⨁ᵢⱼ H^s(E, ℂ)` onto `H^s`, and `TauCeti.SquareChartPartition.sobolevReconstruction_coe`: it
  fixes the elements of `H^s`.
* `TauCeti.SquareChartPartition.memSobolev_reconstruction_schwartzMap`: reconstructions of tuples
  of Schwartz functions are `H^t` for every `t`.
* `TauCeti.SquareChartPartition.denseRange_sobolevReconstruction_toBesselPotentialSpaceCLM`: they
  are dense in `H^s`.
* `TauCeti.SquareChartPartition.denseRange_inclusion`: the inclusion `H^s ⊆ H^r` has dense range.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (Sobolev spaces on manifolds).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection Distribution
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

variable [MeasurableSpace E] [BorelSpace E]

/-! ### The reconstruction as a bounded projection -/

/-- **Reconstructions of `H^s` tuples are `H^s`.** For tempered distributions `vᵢⱼ` in
`H^s(E, ℂ)`, one for each chart and each basis vector of the model fibre, the reconstructed
functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)` is `H^s` with respect to `A`, although its localizations need not
be the `vᵢⱼ`. This is the case `p = 2` of
`TauCeti.SquareChartPartition.memBesselPotential_reconstruction`. -/
theorem memSobolev_reconstruction {s : ℝ} {v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)}
    (hv : ∀ k, TemperedDistribution.MemSobolev s 2 (v k)) :
    A.MemSobolev s (A.reconstruction v) :=
  A.memBesselPotential_two_iff_memSobolev.1
    (A.memBesselPotential_reconstruction ENNReal.one_lt_two ENNReal.ofNat_ne_top hv)

variable (s : ℝ)

/-- The reconstruction of a tuple in `⨁ᵢⱼ H^s(E, ℂ)`, as an element of the Sobolev space. -/
private def reconstructionLinearMap :
    (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) →ₗ[ℝ] A.sobolevSpace s where
  toFun u := A.ofMemSobolev s (A.memSobolev_reconstruction fun k ↦ (u k).memSobolev_toDistr)
  map_add' u u' := A.toDistribution_injective s <| by
    ext φ
    simp [reconstruction_apply, Finset.sum_add_distrib]
  map_smul' a u := A.toDistribution_injective s <| by
    ext φ
    simp [reconstruction_apply, Finset.mul_sum, BesselPotentialSpace.toDistr_real_smul]

/-- The **reconstruction** of a tuple `u` in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)`, as a bounded
operator into the Sobolev space `H^s` of `A`: the element of `H^s` representing the functional
`s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)` (`TauCeti.SquareChartPartition.toDistribution_sobolevReconstruction`). It
fixes the elements of `H^s` (`TauCeti.SquareChartPartition.sobolevReconstruction_coe`), so it is a
bounded projection of the Hilbert sum onto `H^s`. -/
def sobolevReconstruction :
    (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) →L[ℝ] A.sobolevSpace s :=
  ⟨A.reconstructionLinearMap s, (A.reconstructionLinearMap s).continuous_of_injective_comp_eq
    (f := fun u φ ↦ A.reconstruction (fun l ↦ (u l).toDistr) φ)
    (continuous_pi fun φ ↦ by
      simp only [reconstruction_apply]
      exact continuous_finsetSum _ fun k _ ↦ continuous_re.comp
        ((ContinuousEvalConst.continuous_eval_const _).comp
          (BesselPotentialSpace.continuous_toDistr.comp (PiLp.continuous_apply 2 _ k))))
    (continuous_pi (A.continuous_toDistribution_apply s))
    (DFunLike.coe_injective.comp (A.toDistribution_injective s))
    fun u ↦ congrArg DFunLike.coe (A.toDistribution_ofMemSobolev s _)⟩

/-- The reconstruction represents the functional `s ↦ ∑ᵢⱼ Re uᵢⱼ (sᵢⱼ)`. -/
@[simp]
theorem toDistribution_sobolevReconstruction
    (u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) :
    A.toDistribution s (A.sobolevReconstruction s u) = A.reconstruction fun k ↦ (u k).toDistr :=
  A.toDistribution_ofMemSobolev s _

/-- The reconstruction fixes the elements of the Sobolev space: an element of `H^s` is the tuple
of localizations of the functional it represents. -/
@[simp]
theorem sobolevReconstruction_coe (u : A.sobolevSpace s) : A.sobolevReconstruction s u = u :=
  A.toDistribution_injective s (by rw [toDistribution_sobolevReconstruction, toDistribution_apply])

/-- The reconstruction maps the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` onto the Sobolev space `H^s`. -/
theorem sobolevReconstruction_surjective : Function.Surjective (A.sobolevReconstruction s) :=
  fun u ↦ ⟨u, A.sobolevReconstruction_coe s u⟩

/-! ### Density -/

/-- **Reconstructions of Schwartz tuples lie in every `H^t`.** The functional
`s ↦ ∑ᵢⱼ Re ∫ fᵢⱼ sᵢⱼ` reconstructed from Schwartz functions `fᵢⱼ` is `H^t` with respect to `A`
for every `t`. -/
theorem memSobolev_reconstruction_schwartzMap (t : ℝ)
    (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.MemSobolev t (A.reconstruction fun k ↦ (f k : 𝓢'(E, ℂ))) :=
  A.memSobolev_reconstruction fun k ↦ by
    simpa using
      (SchwartzMap.toBesselPotentialSpaceCLM (E := E) (F := ℂ) t 2 (f k)).memSobolev_toDistr

/-- The element of `H^s` representing the reconstruction of a tuple of Schwartz functions. -/
theorem sobolevReconstruction_toBesselPotentialSpaceCLM
    (f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ)) :
    A.sobolevReconstruction s
        (WithLp.toLp 2 fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2 (f k)) =
      A.ofMemSobolev s (A.memSobolev_reconstruction_schwartzMap s f) :=
  A.toDistribution_injective s (by simp)

/-- **Density of reconstructions of Schwartz tuples.** The functionals reconstructed from tuples
of Schwartz functions are dense in the Sobolev space `H^s` of `A`. -/
theorem denseRange_sobolevReconstruction_toBesselPotentialSpaceCLM :
    DenseRange fun f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ) ↦
      A.sobolevReconstruction s
        (WithLp.toLp 2 fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2 (f k)) := by
  have hpi : DenseRange fun f : ι × Fin (Module.finrank ℝ F) → 𝓢(E, ℂ) ↦
      (WithLp.toLp 2 fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2 (f k) :
        PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) :=
    (PiLp.homeomorph 2 _).symm.surjective.denseRange.comp
      (DenseRange.piMap fun _ ↦ SchwartzMap.denseRange_toBesselPotentialSpaceCLM s
        ENNReal.ofNat_ne_top)
      (PiLp.homeomorph 2 _).symm.continuous
  exact (A.sobolevReconstruction_surjective s).denseRange.comp hpi
    (A.sobolevReconstruction s).continuous

/-- **Density of the smaller Sobolev spaces.** For `r ≤ s`, the inclusion `H^s ⊆ H^r` of the
Sobolev spaces of `A` has dense range: the reconstructions of Schwartz tuples lie in its range. -/
theorem denseRange_inclusion {r : ℝ} (h : r ≤ s) : DenseRange (A.inclusion h) :=
  (A.denseRange_sobolevReconstruction_toBesselPotentialSpaceCLM r).mono <| by
    rintro _ ⟨f, rfl⟩
    refine ⟨A.sobolevReconstruction s
      (WithLp.toLp 2 fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2 (f k)), ?_⟩
    simp only [sobolevReconstruction_toBesselPotentialSpaceCLM, inclusion_ofMemSobolev]

end SquareChartPartition

end TauCeti
