/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Geometry.Lie.Subgroup.Units
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Analytic.Order
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Topology
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.InvariantDerivation
import TauCeti.Geometry.Lie.Exponential.Matrix.Coordinate

/-!
# The Lie algebra of the real points of a closed subgroup of `GLₙ`

Let `G ⊆ GLₙ` be a closed subgroup scheme over `ℝ`, cut out by a Hopf ideal `I` of the coordinate
Hopf algebra `O(GLₙ)`. Its real points `G(ℝ) = TauCeti.GeneralLinear.hopfIdealPointsSubgroup n I ℝ`
form a closed subgroup of `GLₙ(ℝ)` (`TauCeti.GeneralLinear.isClosed_hopfIdealPointsSubgroup`),
hence a Lie group by the closed-subgroup theorem, with Lie algebra the matrices `X` whose whole
exponential line `t ↦ exp (t • X)` lies in `G(ℝ)` (`Subgroup.linearLieAlgebra`,
`Subgroup.linearLieSubalgebra`). On the other hand `G` has its algebraic Lie algebra
`Lie(G) ⊆ 𝔤𝔩ₙ(ℝ)`: the tangent vectors at the identity, that is the counit-valued derivations of
`O(GLₙ)`, which vanish on `I` (`TauCeti.HopfIdeal.lieSubalgebra`), read as matrices by
`TauCeti.GeneralLinear.tangentMatrix`. This file proves that the two Lie algebras agree
(`TauCeti.GeneralLinear.linearLieSubalgebra_hopfIdealPointsSubgroup`): the Lie algebra of the Lie
group `G(ℝ)` is the Lie algebra of the algebraic group `G`.

The comparison goes through the exponential curve `t ↦ exp (t • X)` of the matrix `X` of a tangent
vector `d`, read as a curve of real points of `GLₙ`. Its coordinate functions `t ↦ f (exp (t • X))`,
for `f ∈ O(GLₙ)`, are real-analytic, and the curve is an integral curve of the left-invariant
vector field `D` of `d` (`TauCeti.Bialgebra.leftInvariantDerivation`): the derivative of
`t ↦ f (exp (t • X))` is `t ↦ (D f) (exp (t • X))`
(`TauCeti.GeneralLinear.analyticAt_generalLinearToPoint_expUnit_apply`,
`TauCeti.GeneralLinear.hasDerivAt_generalLinearToPoint_expUnit_apply`).

* If `d` vanishes on `I`, then `D` maps `I` into itself. So for `f ∈ I` every derivative of the
  analytic function `t ↦ f (exp (t • X))` at `t = 0` is the value at the identity of some
  `Dᵐ f ∈ I`, which is zero. The function therefore vanishes identically, and
  `exp (t • X) ∈ G(ℝ)` for all `t`.
* Conversely, if `exp (t • X) ∈ G(ℝ)` for all `t` and `f ∈ I`, then `t ↦ f (exp (t • X))` vanishes,
  and its derivative at `0` is `d f`.

## Main results

* `TauCeti.GeneralLinear.expUnit_smul_mem_hopfIdealPointsSubgroup`: the exponential line of a
  vector of `Lie(G)` lies in the real points of `G`.
* `TauCeti.GeneralLinear.forall_expUnit_smul_mem_hopfIdealPointsSubgroup_iff`: the exponential
  line of a tangent vector lies in the real points of `G` exactly when the vector lies in `Lie(G)`.
* `TauCeti.GeneralLinear.linearLieSubalgebra_hopfIdealPointsSubgroup`: the Lie algebra of the Lie
  group `G(ℝ)` is the image of `Lie(G)` under the tangent-matrix equivalence.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. I,
  2nd ed., Cambridge University Press (2023), §3.1, p. 136, the comparison of Lie algebras before
  Theorem 3.12.
* A. Borel, *Linear algebraic groups*, 2nd ed., Springer GTM 126 (1991), §I.3.
-/

public section

open scoped Matrix.Norms.Operator

noncomputable section

attribute [local instance] TauCeti.normedAlgebraRatOfReal

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.GeneralLinear

open WithConv

variable {n : ℕ}

variable (I : HopfIdeal ℝ (coordinateHopfAlgebra ℝ n))

/-- Along the exponential curve, the coordinate functions of the elements of a Hopf ideal vanish at
`0`: the identity is a point of every closed subgroup. -/
private theorem generalLinearToPoint_expUnit_zero_eq_zero (X : Matrix (Fin n) (Fin n) ℝ)
    {f : coordinateHopfAlgebra ℝ n} (hf : f ∈ I) :
    (generalLinearToPoint (R := ℝ) n (expUnit ((0 : ℝ) • X))).ofConv f = 0 := by
  have h := (hopfIdealPointsSubgroup n I ℝ).one_mem
  rw [mem_hopfIdealPointsSubgroup_iff] at h
  simpa only [zero_smul, expUnit_zero, pointsMulEquiv_symm_apply] using h f hf

/-- **The exponential line of a vector of the Lie algebra lies in the real points.** For a closed
subgroup `G` of `GLₙ` over `ℝ` cut out by a Hopf ideal `I`, and a tangent vector `d` at the identity
vanishing on `I`, with matrix `X`, `exp (t • X) ∈ G(ℝ)` for every real `t`. -/
theorem expUnit_smul_mem_hopfIdealPointsSubgroup
    {d : Derivation ℝ (coordinateHopfAlgebra ℝ n)
      (Bialgebra.CounitAlgebra ℝ (coordinateHopfAlgebra ℝ n) ℝ)}
    (hd : d ∈ I.lieSubalgebra (B := ℝ)) (t : ℝ) :
    expUnit (t • tangentMatrix n d) ∈ hopfIdealPointsSubgroup n I ℝ := by
  set X := tangentMatrix n d
  set D := Bialgebra.leftInvariantDerivation d
  rw [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_symm_apply]
  intro f hf
  -- Differentiation along the curve intertwines `D` with `deriv`, and `D` preserves `I`, so every
  -- derivative at `0` of the analytic function `u ↦ f (exp (u • X))` is the value at the identity
  -- of some `Dᵐ f ∈ I`, hence zero, and the function vanishes identically.
  let F (g : coordinateHopfAlgebra ℝ n) (u : ℝ) :=
    (generalLinearToPoint (R := ℝ) n (expUnit (u • X))).ofConv g
  have hsemi : Function.Semiconj F D deriv := fun g ↦
    (funext fun u ↦ (hasDerivAt_generalLinearToPoint_expUnit_apply d g u).deriv).symm
  have hmaps : Set.MapsTo D I I := fun _ ↦ I.leftInvariantDerivation_mem hd
  have htop : analyticOrderAt (F f) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m ↦
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (analyticAt_generalLinearToPoint_expUnit_apply X f 0)).2 fun i _ ↦ ?_
    rw [iteratedDeriv_eq_iterate, ← hsemi.iterate_right i f]
    exact generalLinearToPoint_expUnit_zero_eq_zero I X (hmaps.iterate i hf)
  exact congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0
    (analyticAt_generalLinearToPoint_expUnit_apply X f)).1 htop) t

/-- **The exponential line of a tangent vector lies in the real points of a closed subgroup
exactly when the vector lies in its Lie algebra.** For a closed subgroup `G` of `GLₙ` over `ℝ` cut
out by a Hopf ideal `I`, and a tangent vector `d` at the identity of `GLₙ` with matrix `X`,
`exp (t • X) ∈ G(ℝ)` for every real `t` if and only if `d` vanishes on `I`. -/
theorem forall_expUnit_smul_mem_hopfIdealPointsSubgroup_iff
    (d : Derivation ℝ (coordinateHopfAlgebra ℝ n)
      (Bialgebra.CounitAlgebra ℝ (coordinateHopfAlgebra ℝ n) ℝ)) :
    (∀ t : ℝ, expUnit (t • tangentMatrix n d) ∈ hopfIdealPointsSubgroup n I ℝ) ↔
      d ∈ I.lieSubalgebra (B := ℝ) := by
  refine ⟨fun h ↦ (HopfIdeal.mem_lieSubalgebra_iff I d).2 fun f hf ↦ ?_,
    expUnit_smul_mem_hopfIdealPointsSubgroup I⟩
  -- The derivative at `0` of the vanishing function `u ↦ f (exp (u • X))` is `d f`.
  have hzero : (fun u : ℝ ↦
      (generalLinearToPoint (R := ℝ) n (expUnit (u • tangentMatrix n d))).ofConv f) = 0 :=
    funext fun u ↦ by
      have hu := h u
      rw [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_symm_apply] at hu
      exact hu f hf
  have hderiv := hasDerivAt_generalLinearToPoint_expUnit_apply d f 0
  rw [hzero] at hderiv
  have h0 := hderiv.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  rw [zero_smul, expUnit_zero, generalLinearToPoint_one, AlgHom.convOne_apply,
    Bialgebra.counit_leftInvariantDerivation, Algebra.algebraMap_self_apply] at h0
  exact (Bialgebra.CounitAlgebra.algEquivSelf ℝ _ ℝ).injective (h0.trans (map_zero _).symm)

/-- **The Lie algebra of the real points of a closed subgroup of `GLₙ` is its algebraic Lie
algebra.** For a closed subgroup `G` of `GLₙ` over `ℝ` cut out by a Hopf ideal `I`, a matrix `X`
lies in the Lie algebra of the closed subgroup `G(ℝ)` of `GLₙ(ℝ)` exactly when `X` is the matrix of
a tangent vector at the identity vanishing on `I`. -/
theorem linearLieSubalgebra_hopfIdealPointsSubgroup :
    (hopfIdealPointsSubgroup n I ℝ).linearLieSubalgebra =
      (I.lieSubalgebra (B := ℝ)).map (tangentLieEquivMatrix (R := ℝ) n).toLieHom := by
  ext X
  obtain ⟨d, rfl⟩ := (tangentLieEquivMatrix (R := ℝ) n).surjective X
  rw [Subgroup.mem_linearLieSubalgebra_iff (isClosed_hopfIdealPointsSubgroup n I),
    LieSubalgebra.mem_map]
  simp only [LieEquiv.coe_toLieHom, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [tangentLieEquivMatrix_apply, Subgroup.mem_linearLieAlgebra_iff]
  exact forall_expUnit_smul_mem_hopfIdealPointsSubgroup_iff I d

end TauCeti.GeneralLinear
