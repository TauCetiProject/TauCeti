/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Basic

/-!
# Continuous inhomogeneous cochains compute continuous cohomology

Let `G` be a locally compact topological group, for instance a profinite group, and let `X` be a
topological representation of `G` whose action map `G × X → X` is jointly continuous. Mathlib
defines the continuous cohomology `continuousCohomology n X` as the cohomology of the homogeneous
cochains `TopRep.homogeneousCochains X`, the `G`-invariant elements of the iterated function spaces
`C(G, C(G, …, C(G, X)))`. This file identifies that complex, after forgetting topologies, with the
classical complex `TopRep.continuousInhomogeneousCochains X hX` of continuous functions `C(Gⁿ, X)`
with the inhomogeneous differential, and hence identifies the cohomology of the latter with the
underlying modules of continuous cohomology. No compactness or discreteness is assumed of the
coefficients.

In degree `n` the identification `TopRep.homogeneousCochainsLinearEquiv` is dehomogenization: a
homogeneous cochain `F` is sent to its values `g ↦ F (1, g₀, g₀ g₁, …, g₀ ⋯ gₙ₋₁)` at the partial
products of a tuple, and the inverse sends `f` to its homogeneous partner
`x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)`. Local compactness of `G` is what makes the values of an
iterated continuous function at tuples a continuous function on `Gⁿ⁺¹`; joint continuity of the
action is what makes the homogeneous partner continuous.

For discrete coefficients, the additive comparisons `TauCeti.ContCohomology.cochainEquiv0`,
`cochainEquiv1` and `cochainEquiv2` of degrees `0`, `1` and `2` use the same formulas.

## Main definitions

* `TopRep.homogeneousCochainsLinearEquiv`: homogeneous `n`-cochains are continuous functions on
  `Gⁿ`, through dehomogenization.
* `TopRep.continuousInhomogeneousCochainsIso`: the isomorphism of complexes between the continuous
  inhomogeneous cochains and the homogeneous cochains with their topology forgotten.
* `TopRep.continuousInhomogeneousCochainsHomologyIso`: the cohomology of the continuous
  inhomogeneous cochains is the underlying module of continuous cohomology.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I §2.
* K. Rubin, *Euler Systems*, Appendix B, §2, Definition 2.1.
-/

public section

namespace TopRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] {X : TopRep.{max v w} k G}
 

/-- **Dehomogenization of continuous cochains.** Over a locally compact group, and for a
representation whose action map `G × X → X` is jointly continuous, a homogeneous `n`-cochain `F`
corresponds to the continuous function `g ↦ F (1, g₀, g₀ g₁, …, g₀ ⋯ gₙ₋₁)` on `Gⁿ`, the values of
`F` at the partial products of `g`. The inverse sends a continuous function `f` on `Gⁿ` to its
homogeneous partner `x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)`. -/
noncomputable def homogeneousCochainsLinearEquiv (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) : (homogeneousCochains X).X n ≃ₗ[k] C(Fin n → G, X.V) where
  toFun F :=
    { toFun g := resolutionEval X (n + 1) F.val (Fin.partialProd g)
      continuous_toFun := (continuous_resolutionEval X (n + 1) F.val).comp
        (continuous_pi fun i ↦ Continuous.finPartialProd (fun j ↦ continuous_apply j) i) }
  map_add' F F' := by ext g; simp
  map_smul' c F := by ext g; simp
  invFun f := ⟨homogenization hX n f, ρ_homogenization hX n f⟩
  left_inv F := by
    refine Subtype.ext (resolutionEval_injective X (n + 1) (funext fun x ↦ ?_))
    rw [resolutionEval_homogenization]
    conv_rhs => rw [← Fin.partialProd_left_inv x]
    exact (resolutionEval_mul_left_of_forall_ρ_eq F.property _ _).symm
  right_inv f := ContinuousMap.ext (resolutionEval_homogenization_partialProd hX n f)

/-- Dehomogenization evaluates a homogeneous cochain at partial products. Not a `simp` lemma:
`simp` first rewrites the carrier `(homogeneousCochains X).X n` in its implicit arguments. -/
theorem homogeneousCochainsLinearEquiv_apply (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) (F : (homogeneousCochains X).X n) (g : Fin n → G) :
    homogeneousCochainsLinearEquiv hX n F g = resolutionEval X (n + 1) F.val (Fin.partialProd g) :=
  (rfl)

/-- The inverse of dehomogenization is the homogeneous partner `TopRep.homogenization`. -/
theorem coe_homogeneousCochainsLinearEquiv_symm_apply
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) (f : C(Fin n → G, X.V)) :
    ((homogeneousCochainsLinearEquiv hX n).symm f).val = homogenization hX n f :=
  (rfl)

/-- Dehomogenization carries the differential of the homogeneous cochains to the inhomogeneous
differential. -/
theorem homogeneousCochainsLinearEquiv_d (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) (F : (homogeneousCochains X).X n) :
    homogeneousCochainsLinearEquiv hX (n + 1) (((homogeneousCochains X).d n (n + 1)).hom F) =
      continuousInhomogeneousCochainsD hX n (homogeneousCochainsLinearEquiv hX n F) := by
  ext g
  rw [homogeneousCochainsLinearEquiv_apply, homogeneousCochains.d_apply]
  exact resolutionEval_d_partialProd hX F.property (fun _ ↦ rfl) g

variable (X) in
/-- **Continuous inhomogeneous cochains are homogeneous cochains.** Over a locally compact group,
and for a representation whose action map `G × X → X` is jointly continuous, dehomogenization is
an isomorphism of complexes of `k`-modules between the continuous inhomogeneous cochains
`C(Gⁿ, X)` and Mathlib's homogeneous cochains with their topology forgotten. -/
noncomputable def continuousInhomogeneousCochainsIso
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    continuousInhomogeneousCochains X hX ≅
      ((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).obj
        (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (homogeneousCochainsLinearEquiv hX n).toModuleIso.symm) <| by
      rintro n _ rfl
      ext f : 2
      refine (homogeneousCochainsLinearEquiv hX (n + 1)).injective ?_
      -- Both sides are composites in `ModuleCat`; their values are the dehomogenized differential
      -- of the homogeneous partner of `f` and the inhomogeneous differential of `f`.
      exact (homogeneousCochainsLinearEquiv_d hX n _).trans <|
        (congrArg _ ((homogeneousCochainsLinearEquiv hX n).apply_symm_apply f)).trans (by simp)

variable (X) in
/-- **Continuous inhomogeneous cochains compute continuous cohomology.** Over a locally compact
group, and for a representation whose action map `G × X → X` is jointly continuous, the `n`-th
cohomology of the continuous inhomogeneous cochains `C(Gⁿ, X)` is the underlying `k`-module of
Mathlib's continuous cohomology `continuousCohomology n X`. -/
noncomputable def continuousInhomogeneousCochainsHomologyIso
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (continuousInhomogeneousCochains X hX).homology n ≅
      (forget₂ (TopModuleCat k) (ModuleCat k)).obj (continuousCohomology n X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (continuousInhomogeneousCochainsIso X hX) ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso (forget₂ (TopModuleCat k) (ModuleCat k))

end TopRep
