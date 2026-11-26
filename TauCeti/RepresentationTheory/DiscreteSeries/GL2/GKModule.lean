/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.DiscreteSeries.GL2
public import TauCeti.RepresentationTheory.GL2.CompactWeight.Orthogonal

/-!
# The discrete series of `GL₂(ℝ)` as a `(𝔤𝔩₂(ℂ), O(2))`-module

The weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2` of the discrete series `D_k(μ)` form a symmetric set, so
`D_k(μ)` is stable under the action `TauCeti.CompactWeightModule.orthogonalRep` of `O(2)` on the
compact weights: a rotation `r_θ` acts on `v_ℓ` by `e^{iℓθ}`, and a reflection interchanges the two
rays. This makes `D_k(μ)` a `(𝔤𝔩₂(ℂ), O(2))`-submodule of the module of all compact weights, hence a
`(𝔤𝔩₂(ℂ), O(2))`-module.

## Main definitions

* `TauCeti.discreteSeriesGKSubmodule k μ`: `D_k(μ)` as a `(𝔤𝔩₂(ℂ), O(2))`-submodule of
  `TauCeti.CompactWeightModule.gkModule k μ`.
* `TauCeti.discreteSeriesGKModule k μ`: the `(𝔤𝔩₂(ℂ), O(2))`-module `D_k(μ)`, on which `O(2)`
  acts by `TauCeti.CompactWeightModule.orthogonalRep`
  (`TauCeti.discreteSeriesGKModule_ρ_apply_coe`).

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- **The discrete series `D_k(μ)` as a `(𝔤𝔩₂(ℂ), O(2))`-submodule** of the module of all compact
weights: `O(2)` preserves its symmetric set of weights. -/
def discreteSeriesGKSubmodule (k : ℕ) (μ : ℂ) :
    GKSubmodule (CompactWeightModule.gkModule (k : ℂ) μ) where
  toLieSubmodule := discreteSeries k μ
  apply_mem g _ hv := mem_discreteSeries_iff.2 <| by
    rw [CompactWeightModule.gkModule_ρ]
    exact CompactWeightModule.equivFinsupp_orthogonalRep_mem_supported
      (fun _ ↦ neg_mem_discreteSeriesWeights_iff) g (mem_discreteSeries_iff.1 hv)

/-- The underlying Lie submodule of `TauCeti.discreteSeriesGKSubmodule k μ` is `D_k(μ)`. -/
@[simp]
theorem toLieSubmodule_discreteSeriesGKSubmodule (k : ℕ) (μ : ℂ) :
    (discreteSeriesGKSubmodule k μ).toLieSubmodule = discreteSeries k μ :=
  (rfl)

/-- **The `(𝔤𝔩₂(ℂ), O(2))`-module `D_k(μ)`**: the discrete series with the action of `O(2)` by
`r_θ v_ℓ = e^{iℓθ} v_ℓ` and `A v_ℓ = v_{-ℓ}`, covariant for the conjugation action of `O(2)` on
`𝔤𝔩₂(ℂ)`. -/
def discreteSeriesGKModule (k : ℕ) (μ : ℂ) :
    GKModule (orthogonalAd (Fin 2)) (discreteSeries k μ) :=
  (CompactWeightModule.gkModule (k : ℂ) μ).submodule (discreteSeriesGKSubmodule k μ)

/-- `O(2)` acts on `TauCeti.discreteSeriesGKModule k μ` by
`TauCeti.CompactWeightModule.orthogonalRep`. -/
@[simp]
theorem discreteSeriesGKModule_ρ_apply_coe (k : ℕ) (μ : ℂ) (g : Matrix.orthogonalGroup (Fin 2) ℝ)
    (v : discreteSeries k μ) :
    ((discreteSeriesGKModule k μ).ρ g v : CompactWeightModule (k : ℂ) μ) =
      CompactWeightModule.orthogonalRep (k : ℂ) μ g v :=
  (GKModule.submodule_ρ_apply_coe (M := CompactWeightModule.gkModule (k : ℂ) μ)
    (N := discreteSeriesGKSubmodule k μ) g v).trans (by rw [CompactWeightModule.gkModule_ρ])

end TauCeti
