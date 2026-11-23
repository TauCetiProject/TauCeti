/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology
public import TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit

/-!
# Finite ramification of continuous first Galois cohomology

A continuous cocycle of the absolute Galois group of a number field with discrete coefficients
vanishes on an open normal subgroup. Its fixed field is a finite extension, and away from that
extension's ramified support every local inertia group maps into the subgroup. Thus localization
of a continuous first cohomology class is unramified at all but finitely many finite places.
The local coefficient groups and the embeddings of separable closures may be chosen arbitrarily.

## Main results

* `IntermediateField.explicitMap1_mem_unramifiedH1_of_notMem_ramifiedSupport`: a class
  restricting to zero over a finite subextension is unramified outside its ramified support.
* `TauCeti.ContCohomology.eventually_explicitMap1_mem_unramifiedH1`: localization of a class with
  discrete global coefficients is unramified at all but finitely many finite places.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, Chapter I, §4, Lemma 4.8.
-/

public section

open IsDedekindDomain
open scoped NumberField AdicCompletionExtension

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] [NumberField K]

namespace IntermediateField

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- A class whose restriction to a finite subextension's fixing subgroup vanishes localizes to
an unramified class at every place outside that extension's ramified support. -/
theorem explicitMap1_mem_unramifiedH1_of_notMem_ramifiedSupport [IsTopologicalAddGroup M]
    (E : IntermediateField K (SeparableClosure K)) [NumberField E]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ NumberField.ramifiedSupport K E)
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup (v.adicCompletion K)) N]
    [ContinuousSMul (AbsoluteGaloisGroup (v.adicCompletion K)) N]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (g : AbsoluteGaloisGroup (v.adicCompletion K)) (m : M),
      f (absoluteGaloisGroupMap τ g • m) = g • f m)
    {c : H1 (AbsoluteGaloisGroup K) M}
    (hc : explicitRes1 (AbsoluteGaloisGroup K) M E.fixingSubgroup c = 0) :
    explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup (v.adicCompletion K)) N
      (absoluteGaloisGroupMap τ) f hf hequiv c ∈ unramifiedH1 (v.adicCompletion K) N := by
  rw [mem_unramifiedH1_iff]
  apply (absoluteGaloisGroupMap τ).explicitRes1_explicitMap1_eq_zero_of_map_le f hf hequiv _ hc
  rintro _ ⟨g, hg, rfl⟩
  exact E.absoluteGaloisGroupMap_mem_fixingSubgroup_of_notMem_ramifiedSupport v hv τ hg

end IntermediateField

namespace TauCeti.ContCohomology

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
  [DiscreteTopology M]
  {N : HeightOneSpectrum (𝓞 K) → Type*}
  [∀ v, AddCommGroup (N v)] [∀ v, TopologicalSpace (N v)]
  [∀ v, IsTopologicalAddGroup (N v)]
  [∀ v, DistribMulAction (AbsoluteGaloisGroup (v.adicCompletion K)) (N v)]
  [∀ v, ContinuousSMul (AbsoluteGaloisGroup (v.adicCompletion K)) (N v)]

/-- Every continuous first Galois cohomology class with discrete global coefficients over a
number field localizes to unramified classes at all but finitely many finite places. This allows
arbitrary local coefficients, which need not be discrete, equivariant coefficient maps, and
embeddings of separable closures. -/
theorem eventually_explicitMap1_mem_unramifiedH1
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (f : ∀ v, M →+ N v)
    (hequiv : ∀ v (g : AbsoluteGaloisGroup (v.adicCompletion K)) (m : M),
      f v (absoluteGaloisGroupMap (τ v) g • m) = g • f v m)
    (c : H1 (AbsoluteGaloisGroup K) M) :
    ∀ᶠ v in Filter.cofinite,
      explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup (v.adicCompletion K))
        (N v) (absoluteGaloisGroupMap (τ v)) (f v) continuous_of_discreteTopology (hequiv v) c ∈
          unramifiedH1 (v.adicCompletion K) (N v) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_explicitRes1_eq_zero c
  let E := IntermediateField.fixedField U.toSubgroup
  have : FiniteDimensional K E := finiteDimensional_fixedField_toSubgroup U.toOpenSubgroup
  have : NumberField E := _root_.NumberField.of_module_finite K E
  have hfix : U.toSubgroup = E.fixingSubgroup :=
    toSubgroup_eq_fixingSubgroup_of_fixedField_eq (U := U.toOpenSubgroup) rfl
  rw [hfix] at hU
  filter_upwards [(NumberField.ramifiedSupport K E).finite_toSet.compl_mem_cofinite] with v hv
  exact E.explicitMap1_mem_unramifiedH1_of_notMem_ramifiedSupport v hv (τ v) (f v)
    continuous_of_discreteTopology (hequiv v) hU

end TauCeti.ContCohomology
