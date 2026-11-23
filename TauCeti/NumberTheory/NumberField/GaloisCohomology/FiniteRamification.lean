/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# Finite ramification of continuous first Galois cohomology

A continuous cocycle of the absolute Galois group of a number field with discrete coefficients
vanishes on an open normal subgroup. Its fixed field is a finite extension, and away from that
extension's ramified support every local inertia group maps into the subgroup. Thus localization
of a continuous first cohomology class is unramified at all but finitely many finite places.
The local coefficient groups and the embeddings of separable closures may be chosen arbitrarily.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, second edition, Chapter I, §4, Lemma 4.8.
-/

public section

open IsDedekindDomain
open scoped NumberField AdicCompletionExtension

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- Away from the ramified support of a finite subextension of `Kˢ/K`, every local inertia
element fixes that subextension, for any embedding of separable closures. -/
theorem NumberField.absoluteGaloisGroupMap_mem_fixingSubgroup_of_notMem_ramifiedSupport
    (E : IntermediateField K (SeparableClosure K)) [NumberField E]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ NumberField.ramifiedSupport K E)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    {g : AbsoluteGaloisGroup (v.adicCompletion K)}
    (hg : g ∈ separableClosureInertiaSubgroup (v.adicCompletion K)) :
    absoluteGaloisGroupMap τ g ∈ E.fixingSubgroup := by
  obtain ⟨w, hw, τ', hτ⟩ := exists_algHom_adicCompletion_eq E v
    (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K)))
  have := hw
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    NumberField.isUnramifiedAway_ramifiedSupport v hv w.asIdeal
  have : IsUnramified (v.adicCompletion K) (w.adicCompletion E) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt v w
  have hrange : τ'.fieldRange ≤
      maximalUnramifiedExtension (v.adicCompletion K)
        (SeparableClosure (v.adicCompletion K)) := by
    rw [τ'.fieldRange_eq_unramifiedExtension]
    exact unramifiedExtension_le_maximalUnramifiedExtension _ _ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hτx : τ x = τ' (algebraMap E (w.adicCompletion E) ⟨x, hx⟩) := hτ ⟨x, hx⟩
  have hxur : τ x ∈ maximalUnramifiedExtension (v.adicCompletion K)
      (SeparableClosure (v.adicCompletion K)) := by
    rw [hτx]
    exact hrange (AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩)
  exact τ.injective ((absoluteGaloisGroupMap_commutes τ g x).trans
    (mem_separableClosureInertiaSubgroup_iff.mp hg _ hxur))

namespace ContCohomology

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction (AbsoluteGaloisGroup K) M]
  [ContinuousSMul (AbsoluteGaloisGroup K) M]
  {N : HeightOneSpectrum (𝓞 K) → Type*}
  [∀ v, AddCommGroup (N v)] [∀ v, TopologicalSpace (N v)]
  [∀ v, IsTopologicalAddGroup (N v)]
  [∀ v, DistribMulAction (AbsoluteGaloisGroup (v.adicCompletion K)) (N v)]
  [∀ v, ContinuousSMul (AbsoluteGaloisGroup (v.adicCompletion K)) (N v)]

/-- Every continuous first Galois cohomology class over a number field localizes to unramified
classes at all but finitely many finite places. This allows arbitrary local coefficients,
continuous equivariant coefficient maps, and embeddings of separable closures. -/
theorem eventually_explicitMap1_mem_unramifiedH1
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (f : ∀ v, M →+ N v) (hf : ∀ v, Continuous (f v))
    (hequiv : ∀ v (g : AbsoluteGaloisGroup (v.adicCompletion K)) (m : M),
      f v (absoluteGaloisGroupMap (τ v) g • m) = g • f v m)
    (c : H1 (AbsoluteGaloisGroup K) M) :
    ∀ᶠ v in Filter.cofinite,
      explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup (v.adicCompletion K))
        (N v) (absoluteGaloisGroupMap (τ v)) (f v) (hf v) (hequiv v) c ∈
          unramifiedH1 (v.adicCompletion K) (N v) := by
  induction c using QuotientAddGroup.induction_on with
  | _ z =>
    obtain ⟨U, hU⟩ := exists_openNormalSubgroup_apply_eq_zero (AbsoluteGaloisGroup K) M z
    let E := IntermediateField.fixedField U.toSubgroup
    have : FiniteDimensional K E := finiteDimensional_fixedField_toSubgroup U.toOpenSubgroup
    have : NumberField E := _root_.NumberField.of_module_finite K E
    have hfix : U.toSubgroup = E.fixingSubgroup :=
      toSubgroup_eq_fixingSubgroup_of_fixedField_eq (U := U.toOpenSubgroup) rfl
    filter_upwards [(NumberField.ramifiedSupport K E).finite_toSet.compl_mem_cofinite] with v hv
    rw [explicitMap1_mk]
    apply mk_mem_unramifiedH1_of_forall_mem_separableClosureInertiaSubgroup
    intro g hg
    rw [cocyclesMap1_apply]
    have hgE := NumberField.absoluteGaloisGroupMap_mem_fixingSubgroup_of_notMem_ramifiedSupport
      E v hv (τ v) hg
    rw [← hfix] at hgE
    rw [hU _ hgE, map_zero]

end ContCohomology
end TauCeti
