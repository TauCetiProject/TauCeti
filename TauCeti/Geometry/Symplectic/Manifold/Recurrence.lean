/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Conservative
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure

/-!
# Poincaré recurrence on compact symplectic manifolds

Let `σ` be a symplectic form on a compact manifold `M` of dimension `2 * n`. Its Liouville measure
`|σⁿ / n!|` (`TauCeti.SmoothTwoForm.liouvilleMeasure`) is locally finite, hence finite on the
compact manifold `M`, and is preserved by every symplectomorphism
(`Homeomorph.measurePreserving_liouvilleMeasure`) and by every time-`t` map of a complete
Hamiltonian flow
(`TauCeti.SmoothTwoForm.IsSymplectic.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure`).
So these maps are conservative, and the Poincaré recurrence theorem applies to them:

* almost every point, for the Liouville measure, returns infinitely often to each of its
  neighbourhoods (`Homeomorph.ae_frequently_iterate_mem_of_mpullback_eq`,
  `TauCeti.SmoothTwoForm.IsSymplectic.ae_frequently_iterate_globalFlowDiffeomorph_mem`);
* since `σ` is nondegenerate, every nonempty open set has positive Liouville measure, so every
  nonempty open set `U` contains a point returning to `U` infinitely often
  (`Homeomorph.exists_mem_frequently_iterate_mem_of_mpullback_eq`,
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_mem_frequently_iterate_globalFlowDiffeomorph_mem`).

For a map preserving `σ`, the almost-everywhere statement needs neither nondegeneracy nor
closedness of `σ`: it holds for the measure `|σⁿ / n!|` of any two-form preserved by the map, and
the open-set statement needs nondegeneracy but not closedness. Compactness of `M` is needed for the
measure to be finite; a translation of `ℝ²` preserves the area form and no point returns. A
compact manifold is second countable, as the recurrence to neighbourhoods requires, and a
nondegenerate two-form forces the dimension to be even, so the open-set statements carry no
dimension parameter.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 16.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 5.3.
-/

public section

noncomputable section

open Filter Module MeasureTheory Set Topology
open scoped ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] {σ : TauCeti.SmoothTwoForm I M} {U : Set M}

namespace Homeomorph

open TauCeti

variable {Φ : M ≃ₜ M}

/-- **Poincaré recurrence for maps preserving a two-form.** On a compact manifold, if a
differentiable homeomorphism `Φ` satisfies `Φ^* σ = σ`, then almost every point, for the Liouville
measure of `σ`, returns infinitely often under `Φ` to each of its neighbourhoods. -/
theorem ae_frequently_iterate_mem_of_mpullback_eq [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    [Fact (finrank ℝ E = 2 * n)] (hΦ : MDifferentiable I I Φ) (h : mpullback I I Φ σ.1 = σ.1) :
    ∀ᵐ x ∂σ.liouvilleMeasure n, ∀ s ∈ 𝓝 x, ∃ᶠ k in atTop, Φ^[k] x ∈ s :=
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  (Φ.measurePreserving_liouvilleMeasure hΦ h).conservative.ae_frequently_mem_of_mem_nhds

/-- **Poincaré recurrence for symplectomorphisms.** On a compact manifold with a nondegenerate
two-form `σ`, if a differentiable homeomorphism `Φ` satisfies `Φ^* σ = σ`, then every nonempty open
set `U` contains a point returning to `U` infinitely often under `Φ`. -/
theorem exists_mem_frequently_iterate_mem_of_mpullback_eq (hσ : σ.IsNondegenerate)
    (hΦ : MDifferentiable I I Φ) (h : mpullback I I Φ σ.1 = σ.1) (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ U, ∃ᶠ k in atTop, Φ^[k] x ∈ U := by
  borelize M
  obtain ⟨n, hn⟩ := (hσ.symplecticFormAt hne.some).even_finrank
  have : Fact (finrank ℝ E = 2 * n) := ⟨by rw [two_mul]; exact hn⟩
  have := hσ.isOpenPosMeasure_liouvilleMeasure (n := n)
  exact (Φ.measurePreserving_liouvilleMeasure (n := n) hΦ
    h).conservative.exists_mem_frequently_iterate_mem_of_isOpen hU hne

end Homeomorph

namespace TauCeti.SmoothTwoForm.IsSymplectic

variable [T2Space M] [I.Boundaryless] {f : M → ℝ}

/-- **Poincaré recurrence for Hamiltonian flows.** On a compact symplectic manifold, for a smooth
function `f` with complete Hamiltonian vector field, almost every point, for the Liouville measure,
returns infinitely often to each of its neighbourhoods under the time-`t` map of the Hamiltonian
flow of `f`. -/
theorem ae_frequently_iterate_globalFlowDiffeomorph_mem [MeasurableSpace M] [BorelSpace M]
    {n : ℕ} [Fact (finrank ℝ E = 2 * n)] (hσ : σ.IsSymplectic) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField f)) (t : ℝ) :
    ∀ᵐ x ∂σ.liouvilleMeasure n, ∀ s ∈ 𝓝 x, ∃ᶠ k in atTop,
      (globalFlowDiffeomorph hc le_top
        (hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)) t)^[k] x ∈
          s :=
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  (hσ.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure hf hc
    t).conservative.ae_frequently_mem_of_mem_nhds

/-- **Poincaré recurrence for Hamiltonian flows, open-set form.** On a compact symplectic manifold,
for a smooth function `f` with complete Hamiltonian vector field, every nonempty open set `U`
contains a point returning to `U` infinitely often under the time-`t` map of the Hamiltonian flow
of `f`. -/
theorem exists_mem_frequently_iterate_globalFlowDiffeomorph_mem (hσ : σ.IsSymplectic)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (σ.hamiltonianVectorField f)) (t : ℝ)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∃ᶠ k in atTop,
      (globalFlowDiffeomorph hc le_top
        (hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)) t)^[k] x ∈
          U := by
  borelize M
  obtain ⟨n, hn⟩ := (hσ.isNondegenerate.symplecticFormAt hne.some).even_finrank
  have : Fact (finrank ℝ E = 2 * n) := ⟨by rw [two_mul]; exact hn⟩
  have := hσ.isNondegenerate.isOpenPosMeasure_liouvilleMeasure (n := n)
  exact (hσ.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure (n := n) hf hc
    t).conservative.exists_mem_frequently_iterate_mem_of_isOpen hU hne

end TauCeti.SmoothTwoForm.IsSymplectic
