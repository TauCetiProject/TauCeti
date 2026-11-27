/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.DiscreteSeries.GL2.GKModule
public import TauCeti.RepresentationTheory.GL2.CompactWeight.Admissible

/-!
# Admissibility of the discrete series of `GL₂(ℝ)`

The discrete series `D_k(μ)` is a `(𝔤𝔩₂(ℂ), O(2))`-submodule of the module of all compact weights,
whose `O(2)`-action has finite multiplicities
(`TauCeti.CompactWeightModule.hasFiniteMultiplicities_orthogonalRep`). Hence `D_k(μ)` is an
admissible `(𝔤𝔩₂(ℂ), O(2))`-module. For `k ≥ 1` it is moreover irreducible
(`TauCeti.isIrreducible_discreteSeriesGKModule`), hence finitely generated over `𝔤𝔩₂(ℂ)`, so it is
a Harish-Chandra module.

## Main results

* `TauCeti.hasFiniteMultiplicities_discreteSeriesGKModule`: `D_k(μ)` is an admissible
  `(𝔤𝔩₂(ℂ), O(2))`-module.
* `TauCeti.isHarishChandraModule_discreteSeriesGKModule`: for `k ≥ 1`, `D_k(μ)` is a
  Harish-Chandra module: admissible and finitely generated over `𝔤𝔩₂(ℂ)`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

open Representation

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- **`D_k(μ)` is admissible**: its `O(2)`-action has finite multiplicities, as a
`(𝔤𝔩₂(ℂ), O(2))`-submodule of the compact weights. -/
theorem hasFiniteMultiplicities_discreteSeriesGKModule (k : ℕ) (μ : ℂ) :
    (discreteSeriesGKModule k μ).ρ.HasFiniteMultiplicities := by
  -- `discreteSeriesGKModule` is not exposed, so its action is identified with that of the
  -- compact weights through `discreteSeriesGKModule_ρ_apply_coe` rather than by unfolding.
  let ι : IntertwiningMap (discreteSeriesGKModule k μ).ρ
      (CompactWeightModule.orthogonalRep (k : ℂ) μ) :=
    ⟨(discreteSeries k μ).incl.toLinearMap, fun g ↦ LinearMap.ext fun v ↦
      discreteSeriesGKModule_ρ_apply_coe k μ g v⟩
  exact CompactWeightModule.hasFiniteMultiplicities_orthogonalRep.of_injective ι
    Subtype.val_injective

/-- **`D_k(μ)` is a Harish-Chandra module** for `k ≥ 1`: it is admissible and, being irreducible,
finitely generated over `𝔤𝔩₂(ℂ)`. -/
theorem isHarishChandraModule_discreteSeriesGKModule {k : ℕ} (hk : 1 ≤ k) (μ : ℂ) :
    (discreteSeriesGKModule k μ).IsHarishChandraModule :=
  (isIrreducible_discreteSeriesGKModule hk μ).isHarishChandraModule_iff.2
    (hasFiniteMultiplicities_discreteSeriesGKModule k μ)

end TauCeti
