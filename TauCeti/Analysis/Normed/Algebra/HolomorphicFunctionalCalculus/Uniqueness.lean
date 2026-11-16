/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic

import TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyRiemannSum
import TauCeti.Analysis.Contour.Cycle.Winding

/-!
# Uniqueness of the holomorphic functional calculus

For an element `a` of a complex Banach algebra `A`, `holomorphicCalculus a` is the unique unital
complex-algebra homomorphism `holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ
to `a` whose compositions with `HolomorphicFunctions.toGerm` are continuous on every open
neighbourhood of `spectrum ℂ a` for the compact-open topology (`holomorphicCalculus_unique`,
`eq_holomorphicCalculus_iff`).

On any open neighbourhood `U` of `spectrum ℂ a`, choosing a null-homologous cycle `Γ` in
`U \ spectrum ℂ a` winding once around `spectrum ℂ a` and shrinking to the open winding-one region
`V ≤ U` avoiding `Cycle.trace Γ` places every restriction `restrict hVU f` in the compact-open
closure of the span of Cauchy kernels (`restrict_mem_closure_span_cauchyKernel`), where any unital
homomorphism sending `id` to `a` is forced to agree with `resolvent a`.

No normalization of `‖(1 : A)‖` or nontriviality of `A` is assumed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Set TopologicalSpace Topology

namespace TauCeti

open Contour HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Uniqueness of the holomorphic functional calculus.** Any unital complex-algebra homomorphism
on `holomorphicGerms (spectrum ℂ a)` sending the coordinate germ to `a` whose restriction to every
open neighbourhood of `spectrum ℂ a` is continuous for the compact-open topology coincides with
`holomorphicCalculus a`. -/
theorem holomorphicCalculus_unique (a : A) (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U),
      Continuous (Φ.comp (toGerm ha))) :
    Φ = holomorphicCalculus a := by
  apply holomorphicGerms.algHom_ext
  intro U ha f
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  let V : Opens ℂ := ⟨(U : Set ℂ) ∩ {z | z ∉ Cycle.trace Γ ∧ Cycle.windingNumber z Γ = 1},
    U.isOpen.inter (Cycle.isOpen_setOf_notMem_trace_and_windingNumber_eq Γ 1)⟩
  have hVU : V ≤ U := inter_subset_left
  have haV : spectrum ℂ a ⊆ V := fun z hz ↦
    ⟨ha hz, fun hzΓ ↦ (Cycle.isIn_iff.mp hΓ hzΓ).2 hz, hw z hz⟩
  have hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ) :=
    disjoint_left.mpr fun _ hzV hzΓ ↦ hzV.2.1 hzΓ
  have hwV : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1 := fun _ hzV ↦ hzV.2.2
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  let ΦV : holomorphicFunctions V →ₐ[ℂ] A := Φ.comp (toGerm haV)
  have hΦV_id : ΦV (of V id differentiableOn_id) = a := by
    simpa only [ΦV, AlgHom.comp_apply, toGerm_of] using hΦ_id
  let S : Set (holomorphicFunctions V) :=
    {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)}
  have hS : Set.EqOn ΦV.toLinearMap (holomorphicCalculusOn a V haV).toLinearMap S := by
    rintro _ ⟨w, hm, rfl⟩
    simp only [AlgHom.toLinearMap_apply]
    rw [algHom_cauchyKernel_eq_resolvent ΦV hΦV_id, holomorphicCalculusOn_cauchyKernel]
  have hmem := restrict_mem_closure_span_cauchyKernel hVU f Γ hΓU hn hVΓ hwV
  have heqV : ΦV (restrict hVU f) = holomorphicCalculusOn a V haV (restrict hVU f) :=
    (LinearMap.eqOn_span' hS).closure (hΦ_cont V haV) (continuous_holomorphicCalculusOn a V haV)
      hmem
  simpa only [ΦV, AlgHom.comp_apply, toGerm_restrict, holomorphicCalculusOn_restrict,
    holomorphicCalculus_toGerm] using heqV

/-- Characterization of `holomorphicCalculus a` by the coordinate condition and open-domain
continuity. -/
theorem eq_holomorphicCalculus_iff (a : A) (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A) :
    Φ = holomorphicCalculus a ↔
      Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha)) := by
  refine ⟨?_, fun ⟨hid, hcont⟩ ↦ holomorphicCalculus_unique a Φ hid hcont⟩
  rintro rfl
  refine ⟨holomorphicCalculus_id a, fun U ha ↦ ?_⟩
  have hcomp : (holomorphicCalculus a).comp (toGerm ha) = holomorphicCalculusOn a U ha := by
    ext f
    exact holomorphicCalculus_toGerm a U ha f
  rw [hcomp]
  exact continuous_holomorphicCalculusOn a U ha

end TauCeti
