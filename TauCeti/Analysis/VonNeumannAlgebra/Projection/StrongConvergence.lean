/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.VonNeumannAlgebra.Projection.Basic

/-!
# Strong operator convergence of monotone and antitone nets of projections

A monotone family `p : ι → M.Projection` in a concrete von Neumann algebra `M` converges strongly
(pointwise on `H`, and hence in `H →Lₚₜ[ℂ] H`) along `atTop` to its lattice supremum `⨆ i, p i`.
Passing to orthocomplements yields strong operator convergence of any antitone family of projections
to its lattice infimum `⨅ i, p i`.

## Main declarations

* `VonNeumannAlgebra.Projection.tendsto_iSup_of_monotone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iSup_of_monotone`: strong
  operator convergence of monotone families of projections to their supremum.
* `VonNeumannAlgebra.Projection.tendsto_iInf_of_antitone`,
  `VonNeumannAlgebra.Projection.tendsto_toPointwiseConvergenceCLM_iInf_of_antitone`: strong
  operator convergence of antitone families of projections to their infimum.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Lemma 5.1.4.
* M. Takesaki, *Theory of Operator Algebras I*, Lemma II.3.6.
-/

public section

open Filter
open scoped Topology

namespace VonNeumannAlgebra.Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- **Monotone strong convergence of projections.** A monotone family of projections in `M`
converges strongly (pointwise on `H`) along `atTop` to its lattice supremum. -/
theorem tendsto_iSup_of_monotone {ι : Type*} [Preorder ι] {p : ι → M.Projection}
    (hp : Monotone p) (ξ : H) :
    Tendsto (fun i => (p i : H →L[ℂ] H) ξ) atTop
      (𝓝 (((⨆ i, p i : M.Projection) : H →L[ℂ] H) ξ)) := by
  have hU : Monotone (fun i => (p i : H →L[ℂ] H).range) :=
    fun _ _ hij => le_iff_range_le.1 (hp hij)
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun i => (p i : H →L[ℂ] H).range) hU ξ
  simpa only [starProjection_range, coe_iSup] using ht

/-- **Monotone strong-operator convergence of projections.** A monotone family of projections in
`M` converges in `H →Lₚₜ[ℂ] H` along `atTop` to its lattice supremum. -/
theorem tendsto_toPointwiseConvergenceCLM_iSup_of_monotone {ι : Type*} [Preorder ι]
    {p : ι → M.Projection} (hp : Monotone p) :
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (p i))
      atTop
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((⨆ i, p i : M.Projection) : H →L[ℂ] H))) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 (tendsto_iSup_of_monotone hp)

/-- **Antitone strong convergence of projections.** An antitone family of projections in `M`
converges strongly (pointwise on `H`) along `atTop` to its lattice infimum. -/
theorem tendsto_iInf_of_antitone {ι : Type*} [Preorder ι] {p : ι → M.Projection}
    (hp : Antitone p) (ξ : H) :
    Tendsto (fun i => (p i : H →L[ℂ] H) ξ) atTop
      (𝓝 (((⨅ i, p i : M.Projection) : H →L[ℂ] H) ξ)) := by
  have hpc : Monotone (fun i => (p i)ᶜ) := fun _ _ hij => compl_le_compl_iff.2 (hp hij)
  have ht := tendsto_const_nhds (x := ξ).sub (tendsto_iSup_of_monotone hpc ξ)
  rw [← compl_iInf] at ht
  have hsub : ∀ q : M.Projection, ξ - ((qᶜ : M.Projection) : H →L[ℂ] H) ξ = (q : H →L[ℂ] H) ξ :=
    fun q => by simp [coe_compl]
  simpa only [hsub] using ht

/-- **Antitone strong-operator convergence of projections.** An antitone family of projections in
`M` converges in `H →Lₚₜ[ℂ] H` along `atTop` to its lattice infimum. -/
theorem tendsto_toPointwiseConvergenceCLM_iInf_of_antitone {ι : Type*} [Preorder ι]
    {p : ι → M.Projection} (hp : Antitone p) :
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (p i))
      atTop
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        ((⨅ i, p i : M.Projection) : H →L[ℂ] H))) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 (tendsto_iInf_of_antitone hp)

end VonNeumannAlgebra.Projection
