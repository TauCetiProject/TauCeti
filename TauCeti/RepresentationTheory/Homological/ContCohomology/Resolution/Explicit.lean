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
`X` has the inhomogeneous form `g ↦ a (1, g)`, respectively `(g, h) ↦ a (1, g, g * h)`, and the
explicit comparisons `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete` carry the class of any explicit cocycle
of that form to the class of `a`. For the trivial `𝔽₂` coefficients, the corresponding statements
through the transport `TauCeti.ofDiscreteModule_trivialF2` are
`TauCeti.ContCohomology.eqToHom_explicitH1AddEquivContinuousCohomology_eq_cochainClass` and its
degree-two companion.

## Main definitions

* `TopRep.inhomogeneousCocycle1`, `TopRep.inhomogeneousCocycle2`: the inhomogeneous forms of
  homogeneous `1`- and `2`-cocycles of a discrete representation.
* `TopRep.ResolutionContraction.explicitCocycle1`, `TopRep.ResolutionContraction.explicitCocycle2`:
  the explicit inhomogeneous cocycles of an invariant `1`- or `2`-cocycle of a contracted complex.

## Main results

* `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass` and
  `TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass`: an explicit cocycle
  and a homogeneous cocycle agreeing at `(1, g)`, respectively `(1, g, g * h)`, have the same class.
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
  [IsTopologicalGroup G] (X : TopRep.{u} k G) [DiscreteTopology X.V] [ContinuousSMul G X.V]

/-! ### Homogeneous cocycles in inhomogeneous coordinates -/

/-- The continuous inhomogeneous `1`-cocycle `g ↦ a (1, g)` of a homogeneous `1`-cocycle `a` of a
discrete representation `X`. -/
noncomputable def inhomogeneousCocycle1 (a : (homogeneousCochains X).X 1)
    (ha : ((homogeneousCochains X).d 1 2).hom a = 0) : Z1 G X.V :=
  (cocycleEquiv1 G X.V).symm ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X 1).inv
    ((homogeneousCochains X).cyclesMkOfEq a 2 (CochainComplex.next ℕ 1) ha))

/-- The inhomogeneous form of a homogeneous `1`-cocycle `a` takes the value `a (1, g)` at `g`. -/
@[simp]
theorem inhomogeneousCocycle1_apply (a : (homogeneousCochains X).X 1)
    (ha : ((homogeneousCochains X).d 1 2).hom a = 0) (g : G) :
    (X.inhomogeneousCocycle1 a ha : G → X.V) g = a.val 1 g := by
  rw [inhomogeneousCocycle1, cocycleEquiv1_symm_apply,
    ← iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply]
  have key := (ofDiscreteModuleCocyclesRestrictScalarsIntIso X 1).inv_hom_id_apply
  -- `key` is stated on the carrier of `restrictScalarsInt.obj (cocycles X 1)`, which is the carrier
  -- of `cocycles X 1` only up to unfolding, so it is rewritten with `erw`.
  erw [key]
  rw [HomologicalComplex.iCycles_cyclesMkOfEq]

/-- **Explicit degree-one classes are canonical cochain classes.** If a continuous inhomogeneous
`1`-cocycle `c` of a discrete `X` is `g ↦ a (1, g)` for a homogeneous `1`-cocycle `a`, the
degree-one comparison carries the class of `c` to the class of `a`. -/
theorem explicitH1AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass (c : Z1 G X.V)
    (a : (homogeneousCochains X).X 1) (ha : ((homogeneousCochains X).d 1 2).hom a = 0)
    (hca : ∀ g, (c : G → X.V) g = a.val 1 g) :
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete (c : H1 G X.V) = X.cochainClass 1 a ha := by
  obtain rfl : c = X.inhomogeneousCocycle1 a ha :=
    Subtype.ext (funext fun g ↦ (hca g).trans (X.inhomogeneousCocycle1_apply a ha g).symm)
  rw [explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
    explicitH1AddEquivContinuousCohomology_apply, inhomogeneousCocycle1, AddEquiv.apply_symm_apply,
    ofDiscreteModuleRestrictScalarsIntEquiv_π]
  have key := (ofDiscreteModuleCocyclesRestrictScalarsIntIso X 1).inv_hom_id_apply
  -- `key` is stated on the carrier of `restrictScalarsInt.obj (cocycles X 1)`, which is the carrier
  -- of `cocycles X 1` only up to unfolding, so it is rewritten with `erw`.
  erw [key]
  exact (cochainClass_def X 1 a ha).symm

section LocallyCompact

variable [LocallyCompactSpace G]

/-- The continuous inhomogeneous `2`-cocycle `(g, h) ↦ a (1, g, g * h)` of a homogeneous
`2`-cocycle `a` of a discrete representation `X`. -/
noncomputable def inhomogeneousCocycle2 (a : (homogeneousCochains X).X 2)
    (ha : ((homogeneousCochains X).d 2 3).hom a = 0) : Z2 G X.V :=
  (cocycleEquiv2 G X.V).symm ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X 2).inv
    ((homogeneousCochains X).cyclesMkOfEq a 3 (CochainComplex.next ℕ 2) ha))

/-- The inhomogeneous form of a homogeneous `2`-cocycle `a` takes the value `a (1, g, g * h)` at
`(g, h)`. -/
@[simp]
theorem inhomogeneousCocycle2_apply (a : (homogeneousCochains X).X 2)
    (ha : ((homogeneousCochains X).d 2 3).hom a = 0) (g h : G) :
    (X.inhomogeneousCocycle2 a ha : G × G → X.V) (g, h) = a.val 1 g (g * h) := by
  rw [inhomogeneousCocycle2, cocycleEquiv2_symm_apply,
    ← iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_two_apply]
  have key := (ofDiscreteModuleCocyclesRestrictScalarsIntIso X 2).inv_hom_id_apply
  -- As in degree one, `key` lives on the carrier of `restrictScalarsInt.obj (cocycles X 2)`.
  erw [key]
  rw [HomologicalComplex.iCycles_cyclesMkOfEq]

/-- **Explicit degree-two classes are canonical cochain classes.** If a continuous inhomogeneous
`2`-cocycle `c` of a discrete `X` is `(g, h) ↦ a (1, g, g * h)` for a homogeneous `2`-cocycle `a`,
the degree-two comparison carries the class of `c` to the class of `a`. -/
theorem explicitH2AddEquivContinuousCohomologyOfDiscrete_eq_cochainClass (c : Z2 G X.V)
    (a : (homogeneousCochains X).X 2) (ha : ((homogeneousCochains X).d 2 3).hom a = 0)
    (hca : ∀ g h, (c : G × G → X.V) (g, h) = a.val 1 g (g * h)) :
    X.explicitH2AddEquivContinuousCohomologyOfDiscrete (c : H2 G X.V) = X.cochainClass 2 a ha := by
  obtain rfl : c = X.inhomogeneousCocycle2 a ha :=
    Subtype.ext (funext fun p ↦ (hca p.1 p.2).trans (X.inhomogeneousCocycle2_apply a ha _ _).symm)
  rw [explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
    explicitH2AddEquivContinuousCohomology_apply, inhomogeneousCocycle2, AddEquiv.apply_symm_apply,
    ofDiscreteModuleRestrictScalarsIntEquiv_π]
  have key := (ofDiscreteModuleCocyclesRestrictScalarsIntIso X 2).inv_hom_id_apply
  -- As in degree one, `key` lives on the carrier of `restrictScalarsInt.obj (cocycles X 2)`.
  erw [key]
  exact (cochainClass_def X 2 a ha).symm

end LocallyCompact

/-! ### Cocycles on contracted complexes -/

namespace ResolutionContraction

variable {X} {J : CochainComplex (TopRep.{u} k G) ℕ} (c : ResolutionContraction.{v, u, u} X J)

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
