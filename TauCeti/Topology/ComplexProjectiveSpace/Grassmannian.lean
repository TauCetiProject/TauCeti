/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import TauCeti.Topology.Grassmannian.Infinite.Basic
public import TauCeti.Topology.Grassmannian.Projectivization

/-!
# Complex projective spaces as the finite stages of `CP∞`

The sphere-quotient model `CPⁿ` of complex projective space
(`TauCeti.ComplexProjectiveSpace n`), which carries the CW structure, is homeomorphic to the
rank-one finite Grassmannian `Gr₁(ℂⁿ⁺¹)`
(`TauCeti.ComplexProjectiveSpace.homeomorphFiniteGrassmannian`): compose
`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization` with
`TauCeti.finiteGrassmannian.projectivizationHomeomorph`. The class of a unit vector `x` goes to
the line `ℂ ∙ x`.

The infinite complex projective space `CP∞` is the rank-one infinite Grassmannian
`TauCeti.infiniteGrassmannian ℂ 1`, the union of the finite stages `Gr₁(ℂᵐ)` with the final
topology. Composing with the stage inclusions gives the closed embeddings
`TauCeti.ComplexProjectiveSpace.toInfiniteGrassmannian n : CPⁿ → CP∞`, sending the class of `x` to
the line spanned by `x` in `ℕ →₀ ℂ`
(`TauCeti.ComplexProjectiveSpace.coe_toInfiniteGrassmannian_mk`). Their images exhaust `CP∞`
(`TauCeti.ComplexProjectiveSpace.iUnion_range_toInfiniteGrassmannian`), and `CP⁰` goes to the
basepoint (`TauCeti.ComplexProjectiveSpace.toInfiniteGrassmannian_zero`).

These are the finite-stage carriers through which the cellular homology of `CPⁿ` computes the
homology of `CP∞`.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.homeomorphFiniteGrassmannian`: `CPⁿ ≃ₜ Gr₁(ℂⁿ⁺¹)`.
* `TauCeti.ComplexProjectiveSpace.toInfiniteGrassmannian`: the stage `CPⁿ → CP∞`, a closed
  embedding (`TauCeti.ComplexProjectiveSpace.isClosedEmbedding_toInfiniteGrassmannian`).
* `TauCeti.ComplexProjectiveSpace.iUnion_range_toInfiniteGrassmannian`: the stages cover `CP∞`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5 and §14 (`CP∞` as the union of the
  `CPⁿ`).
-/

public section

noncomputable section

open Set Metric

namespace TauCeti.ComplexProjectiveSpace

variable (n : ℕ)

/-- **`CPⁿ` is the rank-one finite Grassmannian of `ℂⁿ⁺¹`**: the class of a unit vector goes to
the line it spans (`TauCeti.ComplexProjectiveSpace.coe_homeomorphFiniteGrassmannian_mk`). -/
def homeomorphFiniteGrassmannian : ComplexProjectiveSpace n ≃ₜ finiteGrassmannian ℂ 1 (n + 1) :=
  (homeomorphProjectivization n).trans (finiteGrassmannian.projectivizationHomeomorph ℂ (n + 1))

/-- The homeomorphism `CPⁿ ≃ₜ Gr₁(ℂⁿ⁺¹)` sends the class of a unit vector `x` to the line
`ℂ ∙ x`. -/
@[simp]
theorem coe_homeomorphFiniteGrassmannian_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (homeomorphFiniteGrassmannian n (mk n x)).val =
      Submodule.span ℂ {WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1)))} := by
  rw [homeomorphFiniteGrassmannian, Homeomorph.trans_apply, homeomorphProjectivization_mk,
    finiteGrassmannian.coe_projectivizationHomeomorph, Projectivization.submodule_mk]

/-- The inverse of `CPⁿ ≃ₜ Gr₁(ℂⁿ⁺¹)` sends the line `ℂ ∙ x` of a unit vector `x` to its class. -/
@[simp]
theorem homeomorphFiniteGrassmannian_symm_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (h : Module.finrank ℂ
      (Submodule.span ℂ {WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1)))}) = 1) :
    (homeomorphFiniteGrassmannian n).symm
        ⟨Submodule.span ℂ {WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1)))}, h⟩ = mk n x :=
  (homeomorphFiniteGrassmannian n).symm_apply_eq.2
    (Subtype.ext (coe_homeomorphFiniteGrassmannian_mk n x).symm)

/-- **The stage `CPⁿ → CP∞`**: the line of `ℂⁿ⁺¹` represented by a point of `CPⁿ`, viewed in
`ℕ →₀ ℂ` through the coordinate inclusion. -/
def toInfiniteGrassmannian : C(ComplexProjectiveSpace n, infiniteGrassmannian ℂ 1) :=
  finiteGrassmannian.toInfiniteContinuousMap.comp
    (homeomorphFiniteGrassmannian n : C(ComplexProjectiveSpace n, finiteGrassmannian ℂ 1 (n + 1)))

/-- The stage `CPⁿ → CP∞` is the comparison with `Gr₁(ℂⁿ⁺¹)` followed by the stage inclusion. -/
theorem toInfiniteGrassmannian_apply (p : ComplexProjectiveSpace n) :
    toInfiniteGrassmannian n p = (homeomorphFiniteGrassmannian n p).toInfinite :=
  (rfl)

/-- The stage `CPⁿ → CP∞` as a function: `toInfinite ∘ homeomorphFiniteGrassmannian n`. -/
theorem coe_toInfiniteGrassmannian :
    ⇑(toInfiniteGrassmannian n) =
      finiteGrassmannian.toInfinite ∘ homeomorphFiniteGrassmannian n :=
  funext (toInfiniteGrassmannian_apply n)

/-- The stage `CPⁿ → CP∞` sends the class of a unit vector `x` to the line spanned by `x` in
`ℕ →₀ ℂ`. -/
@[simp]
theorem coe_toInfiniteGrassmannian_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (toInfiniteGrassmannian n (mk n x)).val = Submodule.span ℂ
      {Finsupp.coordinateInclusion (R := ℂ) (n + 1)
        (WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))))} := by
  rw [toInfiniteGrassmannian_apply, finiteGrassmannian.coe_toInfinite,
    coe_homeomorphFiniteGrassmannian_mk, Submodule.map_span, Set.image_singleton]

/-- The stage `CPⁿ → CP∞` is a closed embedding. -/
theorem isClosedEmbedding_toInfiniteGrassmannian :
    Topology.IsClosedEmbedding (toInfiniteGrassmannian n) :=
  coe_toInfiniteGrassmannian n ▸ finiteGrassmannian.isClosedEmbedding_toInfinite.comp
    (homeomorphFiniteGrassmannian n).isClosedEmbedding

/-- The range of the stage `CPⁿ → CP∞` is the range of the finite Grassmannian `Gr₁(ℂⁿ⁺¹)`: the
lines of functions vanishing from coordinate `n + 1` on
(`TauCeti.finiteGrassmannian.mem_range_toInfinite_iff`). -/
theorem range_toInfiniteGrassmannian :
    range (toInfiniteGrassmannian n) =
      range (finiteGrassmannian.toInfinite : finiteGrassmannian ℂ 1 (n + 1) → _) :=
  coe_toInfiniteGrassmannian n ▸ (homeomorphFiniteGrassmannian n).surjective.range_comp _

/-- **The stages `CPⁿ` exhaust `CP∞`.** -/
theorem iUnion_range_toInfiniteGrassmannian :
    ⋃ n, range (toInfiniteGrassmannian n) = univ := by
  refine eq_univ_of_forall fun W ↦ mem_iUnion.2 ?_
  obtain ⟨m, V, rfl⟩ := infiniteGrassmannian.exists_toInfinite_eq W
  rw [← finiteGrassmannian.toInfinite_ambientStabilization V]
  exact ⟨m, by rw [range_toInfiniteGrassmannian]; exact mem_range_self _⟩

/-- `CP⁰` is the basepoint of `CP∞`, the line of the first coordinate vector. -/
theorem toInfiniteGrassmannian_zero (p : ComplexProjectiveSpace 0) :
    toInfiniteGrassmannian 0 p = infiniteGrassmannian.basepoint ℂ 1 := by
  refine Subtype.ext ?_
  rw [toInfiniteGrassmannian_apply, finiteGrassmannian.coe_toInfinite,
    finiteGrassmannian.coe_eq_top, infiniteGrassmannian.coe_basepoint, Submodule.map_top,
    Finsupp.range_coordinateInclusion]

end TauCeti.ComplexProjectiveSpace
