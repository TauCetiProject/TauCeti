/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional spaces of divisor sections

For a divisor `D` on a compact connected Riemann surface, the global sections of `𝒪_D`
form a finite-dimensional complex vector space. The result applies to arbitrary divisors,
including those imposing zeros as well as allowing poles.

A section has a principal part at each point where `D` permits a pole, with at most
`max (D x) 0` coefficients. The resulting linear map has finite-dimensional target. Its
kernel embeds into the constants: a meromorphic function with no principal parts is
holomorphic everywhere and hence constant by the maximum principle. In particular,
`dim 𝒪_D(X) ≤ 1 + ∑ x ∈ D.support, (D x).toNat`.

This supplies finiteness of the degree-zero section spaces entering the Euler characteristic
of a divisor sheaf, without using Riemann–Roch or a meromorphic map to the sphere.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §§14 and 16
  (finiteness and divisor section spaces).
* The principal-part splitting is `TauCeti.meromorphicGerms.principalPart`; the embedding
  into meromorphic functions is `TauCeti.RiemannSurface.divisorSections.toMeromorphic`.
-/

public noncomputable section

open Filter Function Polynomial TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.divisorSections

open TauCeti.AlgebraicGeometry (WeilDivisor)
open TauCeti.meromorphicGerms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The principal part of a section in the preferred chart at a point. -/
private def localPrincipalPart (D : WeilDivisor X) (x : X) :
    divisorSections D ⊤ →ₗ[ℂ] ℂ[X] where
  toFun f := principalPart (meromorphicGerms.mk ((fun y ↦ f.1 ⟨y, trivial⟩) ∘ (chartAt ℂ x).symm)
    ((meromorphicAt_def _ _).mp (isDivisorSectionAt f x).meromorphicAt))
  map_add' f g := by
    rw [← map_add, ← mk_add]
    -- Addition of sections is inherited from the submodule of functions, hence pointwise.
    rfl
  map_smul' c f := by
    rw [← principalPart_smul, ← mk_smul]
    -- Scalar multiplication of sections is likewise pointwise, including after chart composition.
    rfl

private lemma localPrincipalPart_natDegree_le (D : WeilDivisor X) (f : divisorSections D ⊤)
    (x : X) : (localPrincipalPart D x f).natDegree ≤ (D x).toNat := by
  dsimp only [localPrincipalPart, LinearMap.coe_mk, AddHom.coe_mk]
  apply natDegree_principalPart_mk_le
  rw [← meromorphicOrderAt_def]
  exact le_trans (by exact_mod_cast neg_le_neg (Int.self_le_toNat (D x)))
    (isDivisorSectionAt f x).neg_le_meromorphicOrderAt

/-- Only the possibly nonzero coefficients of the principal parts are retained. -/
private def principalParts (D : WeilDivisor X) :
    divisorSections D ⊤ →ₗ[ℂ] (∀ x : D.support, Fin (D x).toNat → ℂ) :=
  LinearMap.pi fun x ↦ LinearMap.pi fun i ↦
    (Polynomial.lcoeff ℂ (i.val + 1)).comp (localPrincipalPart D x)

private lemma localPrincipalPart_eq_zero_of_mem_ker (D : WeilDivisor X)
    (f : (principalParts D).ker) (x : X) : localPrincipalPart D x f.1 = 0 := by
  classical
  ext n
  rcases n with _ | n
  · exact coeff_zero_principalPart _
  · by_cases hn : n + 1 ≤ (D x).toNat
    · have hx : x ∈ D.support := by
        apply Finsupp.mem_support_iff.mpr
        intro h
        simp [h] at hn
      have h := congrFun (congrFun f.2 ⟨x, hx⟩)
        ⟨n, by dsimp only [Subtype.coe_mk]; omega⟩
      simpa only [principalParts, LinearMap.pi_apply, LinearMap.comp_apply,
        Polynomial.lcoeff_apply, Pi.zero_apply, Polynomial.coeff_zero] using h
    · exact coeff_eq_zero_of_natDegree_lt
        ((localPrincipalPart_natDegree_le D f.1 x).trans_lt (by omega))

variable [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

private lemma toMeromorphic_mem_constants_of_mem_ker (D : WeilDivisor X) [CompactSpace X]
    (f : (principalParts D).ker) :
    toMeromorphic D f.1 ∈ (Algebra.linearMap ℂ (MeromorphicFunction X)).range := by
  apply LinearMap.mem_range.mpr
  apply MeromorphicFunction.exists_algebraMap_eq_of_forall_ne_infty
  intro x
  rw [← MeromorphicFunction.order_nonneg_iff, order_toMeromorphic, meromorphicOrderAt_def]
  exact (principalPart_mk_eq_zero_iff
    ((meromorphicAt_def _ _).mp (isDivisorSectionAt f.1 x).meromorphicAt)).mp
    (localPrincipalPart_eq_zero_of_mem_ker D f x)

/-- On the kernel, the meromorphic image lands in the one-dimensional space of constants. -/
private def kernelToConstants (D : WeilDivisor X) [CompactSpace X] :
    (principalParts D).ker →ₗ[ℂ] (Algebra.linearMap ℂ (MeromorphicFunction X)).range :=
  ((toMeromorphic D).comp (principalParts D).ker.subtype).codRestrict _
    (toMeromorphic_mem_constants_of_mem_ker D)

private lemma kernelToConstants_injective (D : WeilDivisor X) [CompactSpace X] :
    Injective (kernelToConstants D) := by
  intro f g h
  apply Subtype.ext
  exact toMeromorphic_injective D (congrArg Subtype.val h)

/-- Global sections of a divisor sheaf on a compact connected Riemann surface form a
finite-dimensional complex vector space. -/
instance instFiniteDimensional [CompactSpace X] (D : WeilDivisor X) :
    FiniteDimensional ℂ (divisorSections D ⊤) := by
  classical
  have hkerFinite : FiniteDimensional ℂ (principalParts D).ker :=
    FiniteDimensional.of_injective (kernelToConstants D) (kernelToConstants_injective D)
  -- Mathlib's comap instance combines the finite-dimensional kernel and target.
  have htopFinite : FiniteDimensional ℂ
      ((⊤ : Submodule ℂ (∀ x : D.support, Fin (D x).toNat → ℂ)).comap (principalParts D)) :=
    inferInstance
  rw [Submodule.comap_top] at htopFinite
  exact Submodule.topEquiv.finiteDimensional

/-- The dimension of the global section space is at most one plus the total number of
allowed principal-part coefficients. Negative coefficients of `D` impose zeros and do not
increase this bound. -/
theorem finrank_le_one_add_sum_toNat [CompactSpace X] (D : WeilDivisor X) :
    Module.finrank ℂ (divisorSections D ⊤) ≤ 1 + ∑ x ∈ D.support, (D x).toNat := by
  classical
  have hker := LinearMap.finrank_le_finrank_of_injective (kernelToConstants_injective D)
  have hconst : Module.finrank ℂ (Algebra.linearMap ℂ (MeromorphicFunction X)).range = 1 := by
    rw [LinearMap.finrank_range_of_inj (FaithfulSMul.algebraMap_injective ℂ
      (MeromorphicFunction X)), Module.finrank_self]
  have hrange := (principalParts D).range.finrank_le
  rw [Module.finrank_pi_fintype] at hrange
  simp only [Module.finrank_pi, Fintype.card_fin] at hrange
  rw [hconst] at hker
  have hdim := (principalParts D).finrank_range_add_finrank_ker
  rw [Finset.sum_coe_sort D.support (fun x ↦ (D x).toNat)] at hrange
  omega

end TauCeti.RiemannSurface.divisorSections

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

/-- The native sheaf's global section space is finite-dimensional, so it can be used directly
in cohomological dimension calculations. -/
instance finiteDimensional_divisorSheaf_globalSections {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [CompactSpace X]
    (D : WeilDivisor X) :
    FiniteDimensional ℂ ((divisorSheaf D).obj.obj (Opposite.op ⊤)) :=
  (divisorSheafSectionsEquiv D ⊤).symm.finiteDimensional

end TauCeti.RiemannSurface
