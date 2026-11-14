/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.Homotopy.Path

/-!
# Exactness of locally potential one-forms on simply connected domains

Combining the homotopy invariance of the continuous path integral `localPotentialIntegral` with
`SimplyConnectedSpace.paths_homotopic` shows that on a simply connected domain `s` in a real normed
space `E`, the continuous path integral of a covector field `φ` carrying local potentials depends
only on endpoints and vanishes around every loop. Integrating from a basepoint therefore produces a
global `C¹` potential on `s` (`TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected`).

Because every connected component of an open subset of a locally connected space is open and
disjoint from the remaining components, the same result glues componentwise on any open domain whose
connected components are simply connected, with the empty domain taking the zero potential
(`TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn`). Neither
completeness of `E` or `F` nor finite-dimensionality is needed.

## Main results

* `TauCeti.HasLocalPotentials.localPotentialIntegral_eq_of_simplyConnected`: path independence of
  `localPotentialIntegral` on a simply connected domain.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_loop_eq_zero_of_simplyConnected`: vanishing of
  loop integrals on a simply connected domain.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_eq_zero_of_simplyConnected`: existence of a global
  `C¹` potential pinned to `0` at a chosen basepoint `x₀ ∈ s` and given by path integration.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected`: existence of a global `C¹`
  potential on a simply connected domain.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn`:
  componentwise existence of a global `C¹` potential when every connected component of `s` is simply
  connected (taking `0` on the empty domain).
* `StarConvex.exists_hasFDerivAt` and `Convex.exists_hasFDerivAt`: global `C¹` potentials on
  star-convex and convex open sets (including `∅`).
* `TauCeti.forall_hasFDerivAt_const_iff`: the global potentials of a constant covector `L` on `E`
  are `x ↦ L x + c` and no others.

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, Section 2.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (Theorem 11.49) and
  Chapter 16 (Theorem 16.25).
-/

public section

open Set Metric Filter
open scoped Topology ContDiff unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {φ : E → E →L[ℝ] F}

/-- On a simply connected domain, the continuous path integral of a locally potential covector field
depends only on the endpoints of the path. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ) {a b : E}
    {γ₀ γ₁ : Path a b} (hγ₀ : ∀ t, γ₀ t ∈ s) (hγ₁ : ∀ t, γ₁ t ∈ s) :
    localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁ := by
  obtain ⟨H, hH⟩ :=
    Path.exists_homotopy_forall_mem_of_isSimplyConnected ‹SimplyConnectedSpace s› hγ₀ hγ₁
  exact hφ.localPotentialIntegral_eq_of_homotopy H hH

/-- On a simply connected domain, the continuous path integral of a locally potential covector field
around any loop vanishes. -/
theorem HasLocalPotentials.localPotentialIntegral_loop_eq_zero_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ) {a : E}
    {ℓ : Path a a} (hℓ : ∀ t, ℓ t ∈ s) :
    localPotentialIntegral φ ℓ = 0 := by
  rw [hφ.localPotentialIntegral_eq_of_simplyConnected hℓ (γ₁ := .refl a)
    (fun _ ↦ ℓ.source ▸ hℓ 0), localPotentialIntegral_refl]

/-- **Basepoint-pinned exactness on simply connected domains.** On a simply connected domain `s`
with `x₀ ∈ s`, every covector field `φ` carrying local potentials on `s` has an ambient potential
`g : E → F`, `C¹` on `s`, vanishing at `x₀`, with derivative `φ x` at every `x ∈ s` and value
`localPotentialIntegral φ η` along every path `η : Path x₀ x` in `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_eq_zero_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ) {x₀ : E} (hx₀ : x₀ ∈ s) :
    ∃ g : E → F, g x₀ = 0 ∧ ContDiffOn ℝ 1 g s ∧ (∀ x ∈ s, HasFDerivAt g (φ x) x) ∧
      ∀ x ∈ s, ∀ (η : Path x₀ x), (∀ t, η t ∈ s) → g x = localPotentialIntegral φ η := by
  have hs : IsSimplyConnected s := ‹SimplyConnectedSpace s›
  exact hφ.exists_hasFDerivAt_of_forall_localPotentialIntegral_loop_eq_zero hx₀ hs.isPathConnected
    fun _ hℓ ↦ hφ.localPotentialIntegral_loop_eq_zero_of_simplyConnected hℓ

/-- **Exactness of locally potential one-forms on simply connected domains.** On a simply connected
open set `s` in a real normed space `E`, every continuous covector field `φ` with local potentials
on `s` admits an ambient `g : E → F`, `C¹` on `s`, with Fréchet derivative `φ x` at every
`x ∈ s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  have hs : IsSimplyConnected s := ‹SimplyConnectedSpace s›
  obtain ⟨g, -, hg, hd, -⟩ :=
    hφ.exists_hasFDerivAt_eq_zero_of_simplyConnected hs.nonempty.some_mem
  exact ⟨g, hg, hd⟩

/-- **Componentwise exactness on open sets with simply connected components.** If `φ` has local
potentials on `s` and every connected component of `s` is simply connected, then `φ` admits a global
ambient potential `g : E → F`, `C¹` on `s`, with Fréchet derivative `φ x` at every `x ∈ s` (taking
the zero potential when `s` is empty). -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn
    (hφ : HasLocalPotentials s φ)
    (hcomp : ∀ x ∈ s, IsSimplyConnected (connectedComponentIn s x)) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  classical
  let pot (U : Set E) : E → F :=
    if h : HasLocalPotentials U φ ∧ IsSimplyConnected U then
      (have := h.2.simplyConnectedSpace; h.1.exists_hasFDerivAt_of_simplyConnected).choose
    else 0
  have hderiv : ∀ x ∈ s, HasFDerivAt (fun y ↦ pot (connectedComponentIn s y) y) (φ x) x := by
    intro x hx
    let U := connectedComponentIn s x
    have hU_open : IsOpen U := hφ.isOpen.connectedComponentIn
    have hxU : x ∈ U := mem_connectedComponentIn hx
    have hU : HasLocalPotentials U φ ∧ IsSimplyConnected U :=
      ⟨hφ.mono hU_open (connectedComponentIn_subset s x), hcomp x hx⟩
    have hpot : ∀ z ∈ U, HasFDerivAt (pot U) (φ z) z := by
      simp only [pot, hU]
      exact (have := hU.2.simplyConnectedSpace
        hU.1.exists_hasFDerivAt_of_simplyConnected).choose_spec.2
    have heq : (fun y ↦ pot (connectedComponentIn s y) y) =ᶠ[𝓝 x] pot U := by
      filter_upwards [hU_open.mem_nhds hxU] with y hy
      simp only [U, connectedComponentIn_eq hy]
    exact (hpot x hxU).congr_of_eventuallyEq heq
  exact ⟨fun x ↦ pot (connectedComponentIn s x) x, hφ.contDiffOn_of_hasFDerivAt hderiv, hderiv⟩

/-- On a star-convex open set (possibly empty), every covector field with local potentials admits a
global `C¹` potential. -/
theorem _root_.StarConvex.exists_hasFDerivAt {x₀ : E} (hs : StarConvex ℝ x₀ s)
    (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, contDiffOn_empty, by simp⟩
  · have := hs.contractibleSpace hne
    exact hφ.exists_hasFDerivAt_of_simplyConnected

/-- On a convex open set (possibly empty), every covector field with local potentials admits a
global `C¹` potential. -/
theorem _root_.Convex.exists_hasFDerivAt (hs : Convex ℝ s) (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, contDiffOn_empty, by simp⟩
  · exact (hs.starConvex hx₀).exists_hasFDerivAt hφ

/-- A map `g : E → F` has constant Fréchet derivative `L` everywhere on `E` if and only if it is
`x ↦ L x + c` for some `c : F`. -/
theorem forall_hasFDerivAt_const_iff {g : E → F} {L : E →L[ℝ] F} :
    (∀ x : E, HasFDerivAt g L x) ↔ ∃ c : F, g = fun x ↦ L x + c := by
  refine ⟨fun hd ↦ ?_, fun ⟨c, hc⟩ x ↦ hc ▸ L.hasFDerivAt.add_const c⟩
  obtain ⟨c, hc⟩ := exists_eqOn_add_const_of_hasFDerivAt isOpen_univ isPreconnected_univ
    (fun x _ ↦ hd x) (fun _ _ ↦ L.hasFDerivAt)
  exact ⟨c, funext fun x ↦ hc (mem_univ x)⟩

end TauCeti
