/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pullback
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic

/-!
# Naturality and restriction compatibility of explicit Shapiro maps

The explicit Shapiro maps commute with a commuting square of subgroup inclusions and
compatible coefficient maps. The square on coinduced coefficients uses
`TauCeti.DiscreteCoind.pullback`, so coefficient naturality and restriction to an
intermediate subgroup are instances of the same theorem in each of degrees zero, one and two.

The forward maps restrict to the subgroup and evaluate at `1`. Consequently the squares
hold before any closedness hypothesis is imposed; closedness and profiniteness are needed
only when interpreting these maps as Shapiro isomorphisms.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, second edition, (1.6.4),
  with the footnote on p. 61 distinguishing their `Ind` from genuine induction.
* Ribes–Zalesskii, *Profinite Groups*, second edition, Theorem 6.10.5.
-/

public section

namespace TauCeti.ContCohomology

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  {U : Subgroup G} {V : Subgroup H}
  {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction U A] [DistribMulAction V B]
  (φ : H →ₜ* G) (ψ : V →ₜ* U) (hcomm : ∀ v : V, φ v = (ψ v : G))
  (f : A →+ B) (hf : ∀ (v : V) (a : A), f (ψ v • a) = v • f a)

/-- Shapiro in degree zero commutes with compatible subgroup and coefficient pullback. -/
theorem explicitShapiro0_pullback [ContinuousMul G] [ContinuousMul H]
    (x : H0 G (DiscreteCoind G U A)) :
    explicitShapiro0 H V B
      (explicitMap0 G (DiscreteCoind G U A) (φ : H →* G)
        (DiscreteCoind.pullback φ ψ hcomm f hf)
        (DiscreteCoind.pullback_smul φ ψ hcomm f hf) x) =
      explicitMap0 U A (ψ : V →* U) f hf (explicitShapiro0 G U A x) := by
  apply Subtype.ext
  simp [coe_explicitMap0]

section PositiveDegrees

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [CompactSpace G] [CompactSpace H]
  [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
  [ContinuousSMul U A] [ContinuousSMul V B]

/-- The forward degree-one Shapiro map commutes with compatible subgroup and coefficient
pullback, without requiring either subgroup to be closed. -/
theorem explicitShapiroMap1_pullback (x : H1 G (DiscreteCoind G U A)) :
    explicitShapiroMap1 H V B
      (explicitMap1 G (DiscreteCoind G U A) H (DiscreteCoind H V B) φ
        (DiscreteCoind.pullback φ ψ hcomm f hf) (continuous_of_discreteTopology)
        (DiscreteCoind.pullback_smul φ ψ hcomm f hf) x) =
      explicitMap1 U A V B ψ f (continuous_of_discreteTopology) hf
        (explicitShapiroMap1 G U A x) := by
  -- The degree-one forward Shapiro maps are abbreviations of compatible-pair maps.
  exact explicitMap1_explicitMap1_of_comp_eq G (DiscreteCoind G U A)
    H (DiscreteCoind H V B) φ (DiscreteCoind.pullback φ ψ hcomm f hf)
    continuous_of_discreteTopology (DiscreteCoind.pullback_smul φ ψ hcomm f hf)
    V B (ContinuousMonoidHom.subgroupSubtype V) (DiscreteCoind.eval H V B)
    DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul H V B)
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)
    ψ f continuous_of_discreteTopology hf
    (by ext v; exact hcomm v) (DiscreteCoind.eval_comp_pullback φ ψ hcomm f hf) x

/-- The forward degree-two Shapiro map commutes with compatible subgroup and coefficient
pullback, without requiring either subgroup to be closed. -/
theorem explicitShapiroMap2_pullback (x : H2 G (DiscreteCoind G U A)) :
    explicitShapiroMap2 H V B
      (explicitMap2 G (DiscreteCoind G U A) H (DiscreteCoind H V B) φ
        (DiscreteCoind.pullback φ ψ hcomm f hf) (continuous_of_discreteTopology)
        (DiscreteCoind.pullback_smul φ ψ hcomm f hf) x) =
      explicitMap2 U A V B ψ f (continuous_of_discreteTopology) hf
        (explicitShapiroMap2 G U A x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [explicitShapiroMap2_mk, explicitMap2_mk]
    apply congrArg (fun z : Z2 V B => (z : H2 V B))
    ext p
    rcases p with ⟨v, w⟩
    simp [cocyclesMap2_apply, shapiroCocycles2_apply, hcomm]

end PositiveDegrees

end TauCeti.ContCohomology
