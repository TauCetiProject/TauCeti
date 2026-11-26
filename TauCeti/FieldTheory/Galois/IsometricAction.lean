/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Galois groups acting by isometries

Let `L/K` be an algebraic extension and give `L` a metric for which every `K`-automorphism is an
isometry, for instance the spectral norm of an algebraic extension of a complete nonarchimedean
field. Then the action `Gal(L/K) × L → L` is jointly continuous for the Krull topology on
`Gal(L/K)` and the metric topology on `L`. The orbit map `σ ↦ σ x` of each `x ∈ L` is locally
constant, because `x` is fixed by the open subgroup fixing `K(x)`, and the isometries make the
action equicontinuous in the point.

Joint continuity on `L` then passes to its completion
(`UniformSpace.Completion.continuousSMul_of_isIsometricSMul`): `Gal(L/K)` acts jointly
continuously by isometries on the completion of `L`. This is the continuous Galois action on a
completed algebraic closure, such as `ℂ_p`, on which continuous Galois cohomology is computed.

## Main results

* `AlgEquiv.continuousSMul_of_isIsometricSMul`: for an algebraic extension `L/K` with a metric
  on `L` preserved by `Gal(L/K)`, the action of `Gal(L/K)` on `L` is jointly continuous.

## References

* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1.
-/

public section

/-- **A Galois group acting by isometries acts continuously.** For an algebraic extension `L/K`
and a metric on `L` for which every `K`-automorphism is an isometry, the action
`Gal(L/K) × L → L` is jointly continuous for the Krull topology. -/
instance AlgEquiv.continuousSMul_of_isIsometricSMul {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsIntegral K L] [PseudoEMetricSpace L] [IsIsometricSMul Gal(L/K) L] :
    ContinuousSMul Gal(L/K) L :=
  ⟨continuous_prod_of_continuous_lipschitzWith' _ 1 (fun σ ↦ (isometry_smul L σ).lipschitzWith)
    fun x ↦ (Algebra.IsIntegral.isIntegral (R := K) x).isLocallyConstant_apply.continuous⟩
