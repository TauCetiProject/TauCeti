/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Indicator
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Connected.Clopen

/-!
# Riesz idempotents

For an element `a` of a complex Banach algebra and a clopen part `u` of its spectrum,
`TauCeti.rieszIdempotent a u` is the holomorphic calculus of `a` applied to the germ which is
`1` near `u` and `0` near the rest of the spectrum. Classically it is written as the resolvent
integral `(2πi)⁻¹ ∮ (z - a)⁻¹ dz` over a cycle around `u` alone; here it comes from the germ
calculus, whose contour formula (`TauCeti.holomorphicCalculus_ofFun_eq_integral`) integrates the
locally constant indicator against the resolvent over a cycle around the whole spectrum.

The Riesz idempotents of `a` represent the Boolean algebra of clopen parts of its spectrum
faithfully by commuting idempotents: meets go to products, complements to `1 - ·`, `⊤` to `1`,
disjoint finite joins to sums, and only `⊥` goes to `0` (`TauCeti.rieszIdempotent_eq_zero_iff`).
In particular a finite partition of the spectrum into clopen parts gives orthogonal idempotents
with sum `1` (`TauCeti.sum_rieszIdempotent_eq_one`). Every element commuting with `a` commutes
with its Riesz idempotents (`Commute.rieszIdempotent_right`).

For a bounded operator `T` on a complex Banach space, the ranges of the Riesz idempotents of a
clopen part and of its complement are complementary closed subspaces, each invariant under every
operator commuting with `T`. Consequently an operator whose spectrum is not preconnected has a
nonzero proper closed hyperinvariant subspace, the range of the Riesz idempotent of a nontrivial
clopen part (`exists_isClosed_ne_bot_ne_top_forall_commute_mem_invtSubmodule_of_not_isPreconnected`
in the `ContinuousLinearMap` namespace).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4, Corollary 2.4.6.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.11 and VII.6.
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped Real

namespace TauCeti

open Contour

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The **Riesz idempotent** of `a` for a clopen part `u` of its spectrum: the holomorphic
calculus of `a` at the germ that is `1` near `u` and `0` near the rest of the spectrum. -/
def rieszIdempotent (a : A) (u : Clopens (spectrum ℂ a)) : A :=
  holomorphicCalculus a (holomorphicGerms.indicator u)

@[simp]
theorem holomorphicCalculus_indicator (a : A) (u : Clopens (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.indicator u) = rieszIdempotent a u := (rfl)

/-- Riesz idempotents are idempotent. -/
theorem isIdempotentElem_rieszIdempotent (a : A) (u : Clopens (spectrum ℂ a)) :
    IsIdempotentElem (rieszIdempotent a u) :=
  (holomorphicGerms.isIdempotentElem_indicator u).map (holomorphicCalculus a)

@[simp]
theorem rieszIdempotent_top (a : A) : rieszIdempotent a ⊤ = 1 := by
  rw [← holomorphicCalculus_indicator, holomorphicGerms.indicator_top, map_one]

@[simp]
theorem rieszIdempotent_bot (a : A) : rieszIdempotent a ⊥ = 0 := by
  rw [← holomorphicCalculus_indicator, holomorphicGerms.indicator_bot, map_zero]

/-- The Riesz idempotent of a meet is the product of the Riesz idempotents. -/
theorem rieszIdempotent_inf (a : A) (u v : Clopens (spectrum ℂ a)) :
    rieszIdempotent a (u ⊓ v) = rieszIdempotent a u * rieszIdempotent a v := by
  simp only [← holomorphicCalculus_indicator, holomorphicGerms.indicator_inf, map_mul]

/-- The Riesz idempotent of a complementary part is one minus the Riesz idempotent. -/
theorem rieszIdempotent_compl (a : A) (u : Clopens (spectrum ℂ a)) :
    rieszIdempotent a uᶜ = 1 - rieszIdempotent a u := by
  simp only [← holomorphicCalculus_indicator, holomorphicGerms.indicator_compl, map_sub, map_one]

/-- The Riesz idempotent of a join, by inclusion–exclusion. -/
theorem rieszIdempotent_sup (a : A) (u v : Clopens (spectrum ℂ a)) :
    rieszIdempotent a (u ⊔ v) =
      rieszIdempotent a u + rieszIdempotent a v - rieszIdempotent a u * rieszIdempotent a v := by
  simp only [← holomorphicCalculus_indicator, holomorphicGerms.indicator_sup, map_sub, map_add,
    map_mul]

/-- The Riesz idempotent of a join of disjoint parts is the sum of the Riesz idempotents. -/
theorem rieszIdempotent_sup_of_disjoint (a : A) {u v : Clopens (spectrum ℂ a)}
    (huv : Disjoint u v) :
    rieszIdempotent a (u ⊔ v) = rieszIdempotent a u + rieszIdempotent a v := by
  simp only [← holomorphicCalculus_indicator, holomorphicGerms.indicator_sup_of_disjoint huv,
    map_add]

/-- Riesz idempotents of disjoint parts are orthogonal. -/
theorem rieszIdempotent_mul_rieszIdempotent_of_disjoint (a : A) {u v : Clopens (spectrum ℂ a)}
    (huv : Disjoint u v) : rieszIdempotent a u * rieszIdempotent a v = 0 := by
  rw [← rieszIdempotent_inf, huv.eq_bot, rieszIdempotent_bot]

/-- Riesz idempotents of the same element commute. -/
theorem commute_rieszIdempotent_rieszIdempotent (a : A) (u v : Clopens (spectrum ℂ a)) :
    Commute (rieszIdempotent a u) (rieszIdempotent a v) := by
  rw [Commute, SemiconjBy, ← rieszIdempotent_inf, ← rieszIdempotent_inf, inf_comm]

/-- The Riesz idempotent of a finite join of pairwise disjoint parts is the sum of their Riesz
idempotents. -/
theorem rieszIdempotent_finset_sup (a : A) {ι : Type*} (I : Finset ι)
    (u : ι → Clopens (spectrum ℂ a)) (hu : (I : Set ι).PairwiseDisjoint u) :
    rieszIdempotent a (I.sup u) = ∑ i ∈ I, rieszIdempotent a (u i) := by
  simp only [← holomorphicCalculus_indicator, holomorphicGerms.indicator_finset_sup I u hu,
    map_sum]

/-- The Riesz idempotents of a finite partition of the spectrum into clopen parts sum to `1`. -/
theorem sum_rieszIdempotent_eq_one (a : A) {ι : Type*} (I : Finset ι)
    (u : ι → Clopens (spectrum ℂ a)) (hu : (I : Set ι).PairwiseDisjoint u) (hI : I.sup u = ⊤) :
    ∑ i ∈ I, rieszIdempotent a (u i) = 1 := by
  rw [← rieszIdempotent_finset_sup a I u hu, hI, rieszIdempotent_top]

/-- The Riesz idempotent of a part is zero only for the empty part. -/
@[simp]
theorem rieszIdempotent_eq_zero_iff {a : A} {u : Clopens (spectrum ℂ a)} :
    rieszIdempotent a u = 0 ↔ u = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rieszIdempotent_bot a⟩
  by_contra hu
  obtain ⟨x, hx⟩ : (u : Set (spectrum ℂ a)).Nonempty :=
    nonempty_iff_ne_empty.mpr fun h' ↦ hu (Clopens.ext h')
  -- The germ equal to `1` near `u` and to `z - x` near the rest of the spectrum has no zero on
  -- the spectrum, while the calculus sends it to `a - x`.
  set p : Polynomial ℂ := Polynomial.X - Polynomial.C (x : ℂ)
  set g := holomorphicGerms.ofFun (fun z ↦ p.eval z)
    ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ (spectrum ℂ a)))
  have hw : IsUnit (holomorphicGerms.indicator u + g * holomorphicGerms.indicator uᶜ) := by
    rw [holomorphicGerms.isUnit_iff]
    intro y hy
    by_cases hyu : (⟨y, hy⟩ : spectrum ℂ a) ∈ (u : Set (spectrum ℂ a))
    · simp [g, hyu]
    · have hyx : y ≠ x := fun h ↦ hyu <| by
        rwa [show (⟨y, hy⟩ : spectrum ℂ a) = x from Subtype.ext h]
      simp [g, p, hyu, sub_ne_zero.mpr hyx]
  have hunit := hw.map (holomorphicCalculus a)
  rw [map_add, map_mul, holomorphicCalculus_polynomial, holomorphicCalculus_indicator,
    holomorphicCalculus_indicator, rieszIdempotent_compl, h] at hunit
  refine spectrum.mem_iff.mp x.2 ?_
  simpa [p] using hunit.neg

/-- The Riesz idempotent of a part is one only for the whole spectrum. -/
@[simp]
theorem rieszIdempotent_eq_one_iff {a : A} {u : Clopens (spectrum ℂ a)} :
    rieszIdempotent a u = 1 ↔ u = ⊤ := by
  rw [← compl_eq_bot, ← rieszIdempotent_eq_zero_iff, rieszIdempotent_compl, sub_eq_zero, eq_comm]

/-- Distinct clopen parts of the spectrum have distinct Riesz idempotents. -/
theorem rieszIdempotent_injective (a : A) : Function.Injective (rieszIdempotent a) := by
  have hle {u v : Clopens (spectrum ℂ a)} (h : rieszIdempotent a u = rieszIdempotent a v) :
      u ≤ v := by
    rw [← disjoint_compl_right_iff, disjoint_iff, ← rieszIdempotent_eq_zero_iff,
      rieszIdempotent_inf, rieszIdempotent_compl, mul_sub, mul_one, h,
      (isIdempotentElem_rieszIdempotent a v).eq, sub_self]
  exact fun u v h ↦ le_antisymm (hle h) (hle h.symm)

@[simp]
theorem rieszIdempotent_inj {a : A} {u v : Clopens (spectrum ℂ a)} :
    rieszIdempotent a u = rieszIdempotent a v ↔ u = v :=
  (rieszIdempotent_injective a).eq_iff

end TauCeti

open TauCeti

/-- Every element commuting with `a` commutes with the Riesz idempotents of `a`. -/
theorem Commute.rieszIdempotent_right {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {a b : A} (hb : Commute b a) (u : Clopens (spectrum ℂ a)) :
    Commute b (rieszIdempotent a u) := by
  obtain ⟨f, hf, hfu⟩ := holomorphicGerms.exists_ofFun_eq (holomorphicGerms.indicator u)
  have hU : IsOpen {z | AnalyticAt ℂ f z} := isOpen_analyticAt ℂ f
  have hfU : DifferentiableOn ℂ f {z | AnalyticAt ℂ f z} :=
    fun z hz ↦ hz.differentiableAt.differentiableWithinAt
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one hU hf
  rw [← holomorphicCalculus_indicator, ← hfu,
    holomorphicCalculus_ofFun_eq_integral a hU hf f hfU Γ hΓ hn hw]
  refine (hb.integral_smul_resolvent_right
    (hfU.continuousOn.mono fun z hz ↦ (Contour.Cycle.isIn_iff.mp hΓ hz).1) ?_).smul_right _
  exact Contour.Cycle.isIn_iff.mpr fun z hz ↦
    spectrum.mem_resolventSet_iff.mpr (spectrum.notMem_iff.mp (Contour.Cycle.isIn_iff.mp hΓ hz).2)

namespace TauCeti

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- An element commutes with its Riesz idempotents. -/
theorem commute_rieszIdempotent (a : A) (u : Clopens (spectrum ℂ a)) :
    Commute a (rieszIdempotent a u) :=
  (Commute.refl a).rieszIdempotent_right u

end TauCeti

namespace ContinuousLinearMap

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The range of a Riesz idempotent of `T` is invariant under every operator commuting with
`T`. -/
theorem range_rieszIdempotent_mem_invtSubmodule {S T : E →L[ℂ] E} (hST : Commute S T)
    (u : Clopens (spectrum ℂ T)) : (rieszIdempotent T u).range ∈ invtSubmodule S.toLinearMap :=
  ((IsIdempotentElem.commute_iff (isIdempotentElem_rieszIdempotent T u)).mp
    (hST.rieszIdempotent_right u).symm).1

/-- The ranges of the Riesz idempotents of a clopen part of the spectrum and of its complement
are complementary subspaces. -/
theorem isCompl_range_rieszIdempotent (T : E →L[ℂ] E) (u : Clopens (spectrum ℂ T)) :
    IsCompl (rieszIdempotent T u).range (rieszIdempotent T uᶜ).range := by
  have hP := IsIdempotentElem.toLinearMap (isIdempotentElem_rieszIdempotent T u)
  rw [rieszIdempotent_compl]
  rw [toLinearMap_sub, toLinearMap_one,
    ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP]
  exact LinearMap.IsIdempotentElem.isCompl hP

/-- **An operator with disconnected spectrum has a hyperinvariant subspace**: if the spectrum of
an operator `T` on a complex Banach space is not preconnected, then `T` has a nonzero proper
closed subspace invariant under every operator commuting with `T`, namely the range of the
Riesz idempotent of a nontrivial clopen part of the spectrum. -/
theorem exists_isClosed_ne_bot_ne_top_forall_commute_mem_invtSubmodule_of_not_isPreconnected
    {T : E →L[ℂ] E} (hT : ¬IsPreconnected (spectrum ℂ T)) :
    ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧ M ≠ ⊥ ∧ M ≠ ⊤ ∧
      ∀ S : E →L[ℂ] E, Commute S T → M ∈ invtSubmodule S.toLinearMap := by
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen] at hT
  simp only [not_forall, not_or] at hT
  obtain ⟨c, hc, hc0, hc1⟩ := hT
  set u : Clopens (spectrum ℂ T) := ⟨c, hc⟩
  have hP := isIdempotentElem_rieszIdempotent T u
  refine ⟨(rieszIdempotent T u).range, IsIdempotentElem.isClosed_range hP, ?_, ?_,
    fun S hS ↦ range_rieszIdempotent_mem_invtSubmodule hS u⟩
  · intro hbot
    rw [LinearMap.range_eq_bot, ← toLinearMap_zero, coe_inj, rieszIdempotent_eq_zero_iff] at hbot
    exact hc0 (by simpa [u] using congrArg SetLike.coe hbot)
  · intro htop
    rw [LinearMap.range_eq_top] at htop
    have h1 : rieszIdempotent T u = 1 := ext fun x ↦ by
      obtain ⟨y, rfl⟩ := htop x
      exact congrFun (congrArg DFunLike.coe hP.eq) y
    exact hc1 (by simpa [u] using congrArg SetLike.coe (rieszIdempotent_eq_one_iff.mp h1))

end ContinuousLinearMap
