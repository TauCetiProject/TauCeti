/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.HalfSqRadius
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Duistermaat–Heckman measure of the weight model

The Duistermaat–Heckman measure of a Hamiltonian torus action is the pushforward of the Liouville
measure by the moment map. This file computes it for the linear model `ℂ^ι` of
`TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic`, whose moment map is
`μ(q, p) = -½ Σ_i (q_i² + p_i²) α_i` for weights `α_i ∈ 𝔱*`. The Liouville measure `|ωⁿ / n!|` of
the standard form `ω = Σ dq_i ∧ dp_i` is Lebesgue measure in the coordinates `(q, p)`, so the
results are stated for the pushforward of `volume` on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.

Since `μ` is the linear map `a ↦ Σ_i a_i (-α_i)` applied to the moment map `(|z_i|² / 2)_i` of the
reversed rotation action `z_i ↦ exp(-i θ_i) z_i` (`TauCeti.weightMomentMap_eq_linearCombination`),
and the latter pushes Lebesgue measure to `(2π)^|ι|` times Lebesgue measure on the closed positive
orthant (`TauCeti.map_volume_pi_half_sq_add_sq`), for arbitrary weights the pushforward of
Lebesgue measure by `μ` is `(2π)^|ι|` times the image of Lebesgue measure on the orthant under that
linear map (`TauCeti.map_volume_weightMomentMap`).

When the negated weights form a basis `b` of `𝔱*`, so that `μ = ½ Σ_i (q_i² + p_i²) b_i` is the
moment map of the action `z_i ↦ exp(-i b_i(ξ)) z_i`, this pushforward is `(2π)^|ι|` times the Haar
measure `b.addHaar` (which gives the parallelepiped spanned by `b` measure one) restricted to the
cone `{ν | ∀ i, 0 ≤ b.repr ν i}` (`Module.Basis.map_volume_weightMomentMap_neg`); that cone is the
image of `μ` (`Module.Basis.range_weightMomentMap_neg`). If `b` is a `ℤ`-basis of the weight
lattice of a torus, `b.addHaar` is the Lebesgue measure on `𝔱*` for which the weight lattice has
covolume one. For the standard torus `ℝ^ι / (2πℤ)^ι` acting on `ℂ^ι` by
`z_j ↦ exp(-i θ_j) z_j`, with moment map `μ_j = |z_j|² / 2`, this is the statement that the
Duistermaat–Heckman measure is `(2π)^|ι|` times Lebesgue measure on the positive orthant. Near a
fixed point of a symplectic toric manifold the action is modelled on this one, so this is also the
local form of the Duistermaat–Heckman measure there.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* Victor Guillemin, *Moment maps and combinatorial invariants of Hamiltonian `T^n`-spaces*,
  Progress in Mathematics 122, Birkhäuser (1994), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

variable {ι : Type*} [Fintype ι] {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

namespace TauCeti

variable [MeasurableSpace (StrongDual ℝ 𝔱)] [BorelSpace (StrongDual ℝ 𝔱)]

/-- **The Duistermaat–Heckman measure of the weight model.** For arbitrary weights `α`, the moment
map `μ = -½ Σ_i (q_i² + p_i²) α_i` pushes Lebesgue measure on `ℂ^ι` to `(2π)^|ι|` times the image
of Lebesgue measure on the closed positive orthant under `a ↦ Σ_i a_i (-α_i)`. -/
theorem map_volume_weightMomentMap (α : ι → StrongDual ℝ 𝔱) :
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)).map (weightMomentMap α) =
      ENNReal.ofReal (2 * π) ^ Fintype.card ι •
        (volume.restrict (univ.pi fun _ ↦ Ici (0 : ℝ))).map
          (Fintype.linearCombination ℝ (-α)) := by
  have hL : Measurable (Fintype.linearCombination ℝ (-α)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hp := PiLp.volume_preserving_ofLp ι
  have hP : MeasurePreserving (Prod.map WithLp.ofLp WithLp.ofLp)
      (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) volume :=
    hp.prod hp
  have hfun : weightMomentMap α = Fintype.linearCombination ℝ (-α) ∘
      (fun x : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2) ∘
        Prod.map WithLp.ofLp WithLp.ofLp :=
    funext (weightMomentMap_eq_linearCombination α)
  rw [hfun, ← Measure.map_map hL (by fun_prop), ← Measure.map_map (by fun_prop) hP.measurable,
    hP.map_eq, map_volume_pi_half_sq_add_sq, Measure.map_smul]
  exact hL.aemeasurable

end TauCeti

namespace Module.Basis

open TauCeti

variable [MeasurableSpace (StrongDual ℝ 𝔱)] [BorelSpace (StrongDual ℝ 𝔱)]

/-- **The Duistermaat–Heckman measure of the weight model with a basis of negated weights.** If
`b` is a basis of `𝔱*`, the moment map `μ = ½ Σ_i (q_i² + p_i²) b_i` of the action
`z_i ↦ exp(-i b_i(ξ)) z_i` pushes Lebesgue measure on `ℂ^ι` to `(2π)^|ι|` times the Haar measure
normalized by `b`, restricted to the cone `{ν | ∀ i, 0 ≤ b.repr ν i}`, which is the image of `μ`
(`Module.Basis.range_weightMomentMap_neg`). -/
theorem map_volume_weightMomentMap_neg (b : Basis ι ℝ (StrongDual ℝ 𝔱)) :
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)).map (weightMomentMap (-⇑b)) =
      ENNReal.ofReal (2 * π) ^ Fintype.card ι • b.addHaar.restrict {ν | ∀ i, 0 ≤ b.repr ν i} := by
  have : FiniteDimensional ℝ (StrongDual ℝ 𝔱) := b.finiteDimensional_of_finite
  rw [map_volume_weightMomentMap, neg_neg]
  congr 1
  let L := b.equivFun.symm.toContinuousLinearEquiv
  have hL : (Fintype.linearCombination ℝ ⇑b : (ι → ℝ) → StrongDual ℝ 𝔱) = L :=
    funext fun a ↦ (b.equivFun_symm_apply a).symm
  have hmap : (Pi.basisFun ℝ ι).map L.toLinearEquiv = b := by
    classical
    ext i : 1
    rw [Basis.map_apply, Pi.basisFun_apply]
    -- `L` is `b.equivFun.symm`, repackaged as a continuous linear equivalence.
    exact Basis.equivFun_symm_single b i
  have hvol : (volume : Measure (ι → ℝ)).map L = b.addHaar := by
    rw [← Module.Basis.addHaar_basisFun, Module.Basis.map_addHaar, hmap]
  have hS : L ⁻¹' {ν | ∀ i, 0 ≤ b.repr ν i} = univ.pi fun _ ↦ Ici 0 := by
    ext a
    simp only [mem_preimage, mem_ofPred_eq, mem_univ_pi, mem_Ici, L,
      LinearEquiv.coe_toContinuousLinearEquiv', ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hSm : MeasurableSet {ν : StrongDual ℝ 𝔱 | ∀ i, 0 ≤ b.repr ν i} := by
    rw [← L.symm.preimage_symm_preimage {ν | ∀ i, 0 ≤ b.repr ν i}, L.symm_symm, hS]
    exact L.symm.continuous.measurable (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici)
  rw [hL, ← hvol, Measure.restrict_map L.continuous.measurable hSm, hS]

end Module.Basis
