/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical

/-!
# Examples: the holomorphic canonical bundle of a complex manifold

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, with `E` finite-dimensional. Its canonical
bundle `TauCeti.CanonicalBundle 𝓘(ℂ, E) M`, with fibres the complex top-degree forms on the
tangent spaces, is a holomorphic line bundle with no further input:

* Mathlib's instance for bundles of continuous alternating maps makes it a holomorphic vector
  bundle;
* its fibres are complex lines (`TauCeti.CanonicalBundle.finrank_eq_one`);
* the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of every chart is a holomorphic section over the source of
  the chart (`TauCeti.CanonicalBundle.contMDiffOn_coordForm`) which vanishes nowhere there
  (`TauCeti.CanonicalBundle.coordForm_ne_zero`).
-/

open Bundle Module TauCeti
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

-- The canonical bundle of a complex manifold is a holomorphic vector bundle.
example : ContMDiffVectorBundle ∞ (E [⋀^Fin (finrank ℂ E)]→L[ℂ] ℂ)
    (CanonicalBundle 𝓘(ℂ, E) M) 𝓘(ℂ, E) :=
  inferInstance

-- Its fibres are complex lines.
example (x : M) : finrank ℂ (CanonicalBundle 𝓘(ℂ, E) M x) = 1 :=
  CanonicalBundle.finrank_eq_one x

-- The coordinate form of a chart is holomorphic on the source of the chart.
example (x₀ : M) (b : Basis (Fin (finrank ℂ E)) ℂ E) :
    ContMDiffOn 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E [⋀^Fin (finrank ℂ E)]→L[ℂ] ℂ)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin (finrank ℂ E)]→L[ℂ] ℂ) x
        (CanonicalBundle.coordForm 𝓘(ℂ, E) x₀ b x))
      (chartAt E x₀).source :=
  CanonicalBundle.contMDiffOn_coordForm x₀ b

-- It vanishes nowhere on the source of the chart.
example {x₀ x : M} (b : Basis (Fin (finrank ℂ E)) ℂ E) (hx : x ∈ (chartAt E x₀).source) :
    CanonicalBundle.coordForm 𝓘(ℂ, E) x₀ b x ≠ 0 :=
  CanonicalBundle.coordForm_ne_zero hx
