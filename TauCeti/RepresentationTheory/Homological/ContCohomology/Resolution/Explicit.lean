/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cohomology

/-!
# Explicit low-degree classes of cocycles on contracted complexes

Let `X` be a discrete topological representation of `G` and let `J` be a complex of topological
representations with a contraction `c : TopRep.ResolutionContraction X J`, whose retraction
`proj : J⁰ → X` and homotopies `hom n : Jⁿ⁺¹ → Jⁿ` need not be equivariant. An invariant cocycle
`z` of `J` has a class `c.cohomologyClass z` in Mathlib's continuous cohomology, the class of the
homogeneous cocycle into which the comparison with the coinduced resolution carries `z`. In
degrees one and two this file writes that class as the class of an explicit continuous
inhomogeneous cocycle:

```text
H¹:  g ↦ g • proj (g⁻¹ • hom₀ z),
H²:  (g, h) ↦ (g h) • proj (h⁻¹ • hom₀ (g⁻¹ • hom₁ z)).
```

This is how a class defined through a contraction, such as the class of the tensor power of a
cocycle on a tensor-induced resolution in Evens' multiplicative transfer, is compared with a class
given by an explicit cocycle formula. For a contraction built by
`TopRep.ResolutionContraction.ofGraded` from maps `π` and `h` on a total module, `simp` rewrites
these formulas in terms of `π` and `h` through `ofGraded_proj_apply`, `ofGraded_hom_apply` and
`gradedCochainComplex_ρ_apply`.

The first step does not involve contractions: a homogeneous `1`- or `2`-cocycle `a` of a discrete
`X` has the inhomogeneous form `TopRep.inhomogeneousCocycle1`, respectively
`TopRep.inhomogeneousCocycle2`, and the explicit comparisons carry its class to the class of `a`
(`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass` and its degree-two
companion, in `CohomologyComparison.lean`). This file applies that to the homogeneous cocycle
obtained from `z` through the comparison with the coinduced resolution.

## Main definitions

* `TopRep.ResolutionContraction.explicitCocycle1`, `TopRep.ResolutionContraction.explicitCocycle2`:
  the explicit inhomogeneous cocycles of an invariant `1`- or `2`-cocycle of a contracted complex.

## Main results

* `TopRep.ResolutionContraction.explicitCocycle1_apply` and
  `TopRep.ResolutionContraction.explicitCocycle2_apply`: the formulas above.
* `TopRep.ResolutionContraction.explicitH1AddEquivContinuousCohomologyOfDiscrete_explicitCocycle1`
  and its degree-two companion
  `TopRep.ResolutionContraction.explicitH2AddEquivContinuousCohomologyOfDiscrete_explicitCocycle2`:
  the explicit cocycles represent the classes of the invariant cocycles.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  passage between homogeneous and inhomogeneous cochains.
* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.3.7.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5.
-/

public section

open CategoryTheory TauCeti.ContCohomology

namespace TopRep

universe u v

attribute [local instance] TopRep.distribMulAction

variable {k : Type v} [Ring k] [TopologicalSpace k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : TopRep.{u} k G} [DiscreteTopology X.V] [ContinuousSMul G X.V]

/-! ### Cocycles on contracted complexes -/

namespace ResolutionContraction

variable {J : CochainComplex (TopRep.{u} k G) ℕ} (c : ResolutionContraction.{v, u, u} X J)

/-- The explicit inhomogeneous `1`-cocycle of an invariant `1`-cocycle `z` of a complex contracted
onto a discrete `X`: `g ↦ g • proj (g⁻¹ • hom₀ z)` (`explicitCocycle1_apply`). Its class is the
class of `z` (`explicitH1AddEquivContinuousCohomologyOfDiscrete_explicitCocycle1`). -/
noncomputable def explicitCocycle1 (z : (J.X 1).ρ.invariants)
    (hz : (J.d 1 2).hom (z : (J.X 1).V) = 0) : Z1 G X.V :=
  X.inhomogeneousCocycle1 ((c.comparison.f 1).hom.mapInvariants z)
    (c.d_mapInvariants_comparison_f z hz)

/-- The explicit cocycle of an invariant `1`-cocycle `z` is `g ↦ g • proj (g⁻¹ • hom₀ z)`. -/
@[simp]
theorem explicitCocycle1_apply (z : (J.X 1).ρ.invariants)
    (hz : (J.d 1 2).hom (z : (J.X 1).V) = 0) (g : G) :
    (c.explicitCocycle1 z hz : G → X.V) g =
      X.ρ g (c.proj ((J.X 0).ρ g⁻¹ (c.hom 0 (z : (J.X 1).V)))) := by
  refine (X.inhomogeneousCocycle1_apply _ _ g).trans ?_
  -- Unfold the comparison twice: `F¹ z 1 = F⁰ (hom₀ z)` and `F⁰ w g = g • proj (g⁻¹ • w)`.
  refine (congrArg (fun F ↦ F g) (c.comparison_f_succ_apply_apply 0 z 1)).trans ?_
  refine (c.comparison_f_zero_apply_apply _ g).trans ?_
  simp

/-- **The class of an invariant `1`-cocycle in explicit coordinates.** The degree-one comparison
carries the class of the explicit cocycle `g ↦ g • proj (g⁻¹ • hom₀ z)` to the class of `z` in
`H¹(G, X)`. -/
theorem explicitH1AddEquivContinuousCohomologyOfDiscrete_explicitCocycle1
    (z : (J.X 1).ρ.invariants) (hz : (J.d 1 2).hom (z : (J.X 1).V) = 0) :
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete (c.explicitCocycle1 z hz : H1 G X.V) =
      c.cohomologyClass z hz := by
  rw [cohomologyClass_def]
  exact X.explicitH1AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass _ _ _
    (X.inhomogeneousCocycle1_apply _ _)

section LocallyCompact

variable [LocallyCompactSpace G]

/-- The explicit inhomogeneous `2`-cocycle of an invariant `2`-cocycle `z` of a complex contracted
onto a discrete `X`: `(g, h) ↦ (g h) • proj (h⁻¹ • hom₀ (g⁻¹ • hom₁ z))`
(`explicitCocycle2_apply`). Its class is the class of `z`
(`explicitH2AddEquivContinuousCohomologyOfDiscrete_explicitCocycle2`). -/
noncomputable def explicitCocycle2 (z : (J.X 2).ρ.invariants)
    (hz : (J.d 2 3).hom (z : (J.X 2).V) = 0) : Z2 G X.V :=
  X.inhomogeneousCocycle2 ((c.comparison.f 2).hom.mapInvariants z)
    (c.d_mapInvariants_comparison_f z hz)

/-- The explicit cocycle of an invariant `2`-cocycle `z` is
`(g, h) ↦ (g h) • proj (h⁻¹ • hom₀ (g⁻¹ • hom₁ z))`. -/
@[simp]
theorem explicitCocycle2_apply (z : (J.X 2).ρ.invariants)
    (hz : (J.d 2 3).hom (z : (J.X 2).V) = 0) (g h : G) :
    (c.explicitCocycle2 z hz : G × G → X.V) (g, h) =
      X.ρ (g * h)
        (c.proj ((J.X 0).ρ h⁻¹ (c.hom 0 ((J.X 1).ρ g⁻¹ (c.hom 1 (z : (J.X 2).V)))))) := by
  refine (X.inhomogeneousCocycle2_apply _ _ g h).trans ?_
  -- Unfold the comparison three times: `F² z 1 = F¹ (hom₁ z)`, then
  -- `F¹ w g = F⁰ (g • hom₀ (g⁻¹ • w))` and `F⁰ w' (g h) = (g h) • proj ((g h)⁻¹ • w')`.
  refine (congrArg (fun F ↦ F g (g * h)) (c.comparison_f_succ_apply_apply 1 z 1)).trans ?_
  refine (congrArg (fun F ↦ F (g * h)) (c.comparison_f_succ_apply_apply 0 _ g)).trans ?_
  refine (c.comparison_f_zero_apply_apply _ (g * h)).trans ?_
  simp only [inv_one, map_one, one_apply_eq_self]
  rw [← mul_apply_eq_comp ((J.X 0).ρ (g * h)⁻¹), ← map_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel, mul_one]

/-- **The class of an invariant `2`-cocycle in explicit coordinates.** The degree-two comparison
carries the class of the explicit cocycle `(g, h) ↦ (g h) • proj (h⁻¹ • hom₀ (g⁻¹ • hom₁ z))` to
the class of `z` in `H²(G, X)`. -/
theorem explicitH2AddEquivContinuousCohomologyOfDiscrete_explicitCocycle2
    (z : (J.X 2).ρ.invariants) (hz : (J.d 2 3).hom (z : (J.X 2).V) = 0) :
    X.explicitH2AddEquivContinuousCohomologyOfDiscrete (c.explicitCocycle2 z hz : H2 G X.V) =
      c.cohomologyClass z hz := by
  rw [cohomologyClass_def]
  exact X.explicitH2AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass _ _ _
    (X.inhomogeneousCocycle2_apply _ _)

end LocallyCompact

end ResolutionContraction

end TopRep
