/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Topology.Algebra.Projectivization.Action
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The Möbius action on the projective line is jointly continuous

The groups `GL(2, 𝕜)` and `PSL(2, 𝕜)` act on the projective line `OnePoint 𝕜` by Möbius
transformations `z ↦ (a * z + b) / (c * z + d)`, including at `∞`, through the identification
`OnePoint.equivProjectivization` of `OnePoint 𝕜` with `ℙ 𝕜 (Fin 2 → 𝕜)`. For a proper nontrivially
normed field `𝕜`, such as `ℂ`, this identification is a homeomorphism
(`OnePoint.diffeomorphProjectivization`), and on `ℙ 𝕜 (Fin 2 → 𝕜)` both actions are jointly
continuous (`Projectivization.instContinuousSMul` and `Projectivization.instContinuousSMulPSL`).
Hence the Möbius transformation `g • z` depends jointly continuously on the matrix `g` and the
point `z` of the projective line, for `g` in `GL(2, 𝕜)` with its topology as a unit group, or in
`PSL(2, 𝕜)` with its quotient topology.

For `𝕜 = ℂ` this is the continuous action of `PSL(2, ℂ)` on the Riemann sphere. Each single
transformation is moreover holomorphic (`OnePoint.instContMDiffConstSMul`).

## Main results

* `OnePoint.instContinuousSMulGL`: `GL(2, 𝕜)` acts jointly continuously on `OnePoint 𝕜`.
* `OnePoint.instContinuousSMulPSL`: `PSL(2, 𝕜)` acts jointly continuously on `OnePoint 𝕜`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
-/

public section

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **The Möbius action of `GL(2, 𝕜)` on the projective line is jointly continuous**: the point
`g • z` of `OnePoint 𝕜` depends continuously on the pair `(g, z)`, including at `∞`. -/
instance instContinuousSMulGL : ContinuousSMul (GL (Fin 2) 𝕜) (OnePoint 𝕜) :=
  (diffeomorphProjectivization 𝕜 0).toHomeomorph.isInducing.continuousSMul continuous_id
    fun {_ x} ↦ by simpa using equivProjectivization_smul x

/-- **The Möbius action of `PSL(2, 𝕜)` on the projective line is jointly continuous**, for the
quotient topology of `PSL(2, 𝕜) = SL(2, 𝕜) ⧸ {±1}`. For `𝕜 = ℂ` this is the continuous action of
`PSL(2, ℂ)` on the Riemann sphere. -/
instance instContinuousSMulPSL : ContinuousSMul PSL(2, 𝕜) (OnePoint 𝕜) :=
  (diffeomorphProjectivization 𝕜 0).toHomeomorph.isInducing.continuousSMul continuous_id
    fun {g x} ↦ by
      -- The action on `OnePoint 𝕜` is transported from `ℙ 𝕜 (Fin 2 → 𝕜)` along
      -- `equivProjectivization 𝕜` (`OnePoint.instMulActionPSL`).
      simp [Equiv.smul_def]

end OnePoint
