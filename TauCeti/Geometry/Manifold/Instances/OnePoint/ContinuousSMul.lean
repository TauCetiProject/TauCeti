/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Topology.Algebra.Projectivization.Action
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.Cocompact

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

A sequence of Möbius transformations can leave every compact subset of `PSL(2, 𝕜)` only by
degenerating. Lift `g n` to matrices `A n` of determinant one. After dividing each by a suitable
scalar, a subsequence converges to a nonzero matrix `B` of determinant zero
(`Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact`). So `B` has
rank one, with a kernel line `a` and an image line `b`
(`Projectivization.exists_mk_eq_and_mk_mulVec_eq_of_det_eq_zero`), and `g n • z` converges to
`b` for every `z ≠ a`, by the limit theorem `Projectivization.tendsto_smul_of_tendsto_smul_coe`.
This holds even along moving points: if `z n → z₀ ≠ a` then `g n • z n → b` along the
subsequence (`OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`), so that the
transformations converge to the constant map `b` away from the point `a`. For instance the
dilations `z ↦ n z` converge to `∞` away from `0`.

## Main results

* `OnePoint.instContinuousSMulGL`: `GL(2, 𝕜)` acts jointly continuously on `OnePoint 𝕜`.
* `OnePoint.instContinuousSMulPSL`: `PSL(2, 𝕜)` acts jointly continuously on `OnePoint 𝕜`.
* `OnePoint.exists_tendsto_psl_smul_of_tendsto_cocompact`: a sequence of Möbius transformations
  escaping to infinity has a subsequence converging to a constant `b` away from a point `a`, even
  along moving points.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
* A. Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer, 1983
  (sequences of Möbius transformations).
-/

public section

open Filter Topology Matrix
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
    fun {_ x} ↦ by simpa using equivProjectivization_psl_smul x

/-- **Escaping sequences of Möbius transformations.** If a sequence `g n` of Möbius
transformations leaves every compact subset of `PSL(2, 𝕜)`, a subsequence converges to a constant
`b` away from a point `a`, even along moving points: whenever `z n → z₀ ≠ a`, the points
`g (φ n) • z n` converge to `b`. -/
theorem exists_tendsto_psl_smul_of_tendsto_cocompact {g : ℕ → PSL(2, 𝕜)}
    (hg : Tendsto g atTop (cocompact PSL(2, 𝕜))) :
    ∃ (φ : ℕ → ℕ) (a b : OnePoint 𝕜), StrictMono φ ∧
      ∀ ⦃z : ℕ → OnePoint 𝕜⦄ ⦃z₀ : OnePoint 𝕜⦄, z₀ ≠ a → Tendsto z atTop (𝓝 z₀) →
        Tendsto (fun n ↦ g (φ n) • z n) atTop (𝓝 b) := by
  choose A hA using fun n ↦ QuotientGroup.mk_surjective (g n)
  obtain ⟨m, φ, B, hφ, hB, hdet, hCB⟩ :=
    Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact hg hA
  obtain ⟨a, b, ha, hb⟩ := Projectivization.exists_mk_eq_and_mk_mulVec_eq_of_det_eq_zero hB hdet
  let e := (diffeomorphProjectivization 𝕜 0).toHomeomorph
  refine ⟨φ, e.symm a, e.symm b, hφ, fun z z₀ hz₀ hz ↦ ?_⟩
  -- On the projective line the transformations act through the matrices `A n`, and
  -- `(m n)⁻¹ • A n → B`, so `Projectivization.tendsto_smul_of_tendsto_smul_coe` applies.
  have hBz : B *ᵥ (e z₀).rep ≠ 0 := fun h ↦ hz₀ <| by
    rw [← (ha _ (e z₀).rep_ne_zero).1 h, Projectivization.mk_rep, Homeomorph.symm_apply_apply]
  have hlim := Projectivization.tendsto_smul_of_tendsto_smul_coe
    (C := fun n ↦ (A (φ n) : GL (Fin 2) 𝕜)) (c := fun n ↦ (m (φ n))⁻¹) hCB
    ((e.continuous.tendsto z₀).comp hz)
    ((Projectivization.mem_linearProjectionDomain_iff _).2 hBz)
  have hlp : Projectivization.linearProjection B.mulVecLin (e z₀) = b := by
    rw [← Projectivization.mk_rep (e z₀), Projectivization.linearProjection_mk _ _ hBz]
    exact hb _ hBz
  rw [hlp] at hlim
  refine ((e.symm.continuous.tendsto b).comp hlim).congr fun n ↦ ?_
  simp only [Function.comp_apply, ← hA (φ n)]
  exact e.injective (by simpa [e] using (equivProjectivization_smul (z n)).symm)

end OnePoint
