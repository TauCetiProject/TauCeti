/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.LocallyConnected
import TauCeti.Topology.Homotopy.Path

/-!
# Global potentials of locally exact covector fields on simply connected domains

A covector field `φ : E → E →L[ℝ] F` with local potentials (`TauCeti.HasLocalPotentials`) on a
simply connected open subset `s` of a real normed space `E` admits a global `C¹` potential
`g : E → F` satisfying `HasFDerivAt g (φ w) w` at every `w ∈ s`, without assuming finite
dimensionality of `E` or completeness of `F`. More generally, a global `C¹` potential exists
whenever every connected component of `s` is simply connected (including the empty domain).

## Main results

* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_of_isSimplyConnected`,
  `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_of_simplyConnected`: path independence
  of `localPotentialCurveIntegral` in a simply connected domain.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected`,
  `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_loop_eq_zero_of_simplyConnected`:
  vanishing of `localPotentialCurveIntegral` along every continuous loop in a simply connected
  domain.
* `TauCeti.exists_hasFDerivAt_of_simplyConnected`,
  `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected`: existence of a global `C¹`
  potential on a simply connected domain.
* `TauCeti.exists_hasFDerivAt_eq_of_simplyConnected`: existence and uniqueness on `s` of a global
  `C¹` potential taking a prescribed value at a base point.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_forall_isSimplyConnected_connectedComponentIn`:
  existence of a global `C¹` potential when every connected component of `s` is simply connected.

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §3 (existence of primitives on simply connected domains).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §4.3 (exactness of locally exact
  differentials on simply connected regions).
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b x₀ : E} {s : Set E} {φ : E → E →L[ℝ] F}

/-- On a simply connected domain (`IsSimplyConnected s`), `localPotentialCurveIntegral` depends
only on the endpoints of the path. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s)
    {p q : Path a b} (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    localPotentialCurveIntegral φ p = localPotentialCurveIntegral φ q := by
  obtain ⟨K, hK⟩ := Path.exists_homotopy_forall_mem_of_isSimplyConnected hs hp hq
  exact hφ.localPotentialCurveIntegral_eq_of_homotopy K fun ⟨t, x⟩ ↦ hK t x

/-- On a simply connected domain (`[SimplyConnectedSpace s]`), `localPotentialCurveIntegral`
depends only on the endpoints of the path. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ)
    {p q : Path a b} (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    localPotentialCurveIntegral φ p = localPotentialCurveIntegral φ q :=
  hφ.localPotentialCurveIntegral_eq_of_isSimplyConnected ‹SimplyConnectedSpace s› hp hq

/-- Every continuous loop inside a simply connected domain (`IsSimplyConnected s`) has zero
local-potential curve integral. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s)
    (η : Path a a) (hη : ∀ t, η t ∈ s) :
    localPotentialCurveIntegral φ η = 0 := by
  have ha : a ∈ s := η.source ▸ hη 0
  rw [hφ.localPotentialCurveIntegral_eq_of_isSimplyConnected hs hη (p := η) (q := Path.refl a)
      (fun _ ↦ ha),
    localPotentialCurveIntegral_refl]

/-- Every continuous loop inside a simply connected domain (`[SimplyConnectedSpace s]`) has zero
local-potential curve integral. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_loop_eq_zero_of_simplyConnected
    [SimplyConnectedSpace s] (hφ : HasLocalPotentials s φ)
    (η : Path a a) (hη : ∀ t, η t ∈ s) :
    localPotentialCurveIntegral φ η = 0 :=
  hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected ‹SimplyConnectedSpace s› η hη

/-- On a simply connected domain (`IsSimplyConnected s`), `localPotentialPrimitive s φ x₀ y` equals
the curve integral along any path in `s` from `x₀` to `y`. -/
theorem HasLocalPotentials.localPotentialPrimitive_eq_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) {y : E}
    (γ : Path x₀ y) (hγ : ∀ t, γ t ∈ s) :
    localPotentialPrimitive s φ x₀ y = localPotentialCurveIntegral φ γ :=
  hφ.localPotentialPrimitive_eq
    (fun η hη ↦ hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected hs η hη) γ hγ

/-- On a simply connected domain containing `x₀`, `localPotentialPrimitive s φ x₀` vanishes at
`x₀`. -/
theorem HasLocalPotentials.localPotentialPrimitive_self_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) (hx₀ : x₀ ∈ s) :
    localPotentialPrimitive s φ x₀ x₀ = 0 :=
  hφ.localPotentialPrimitive_self hx₀ fun η hη ↦
    hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected hs η hη

/-- On a simply connected domain containing `x₀`, `localPotentialPrimitive s φ x₀` is `C¹` on
`s`. -/
theorem HasLocalPotentials.contDiffOn_localPotentialPrimitive_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) (hx₀ : x₀ ∈ s) :
    ContDiffOn ℝ 1 (localPotentialPrimitive s φ x₀) s :=
  hφ.contDiffOn_localPotentialPrimitive
    (fun y hy ↦ hs.isPathConnected.joinedIn x₀ hx₀ y hy)
    (fun η hη ↦ hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected hs η hη)

/-- On a simply connected domain containing `x₀`, `localPotentialPrimitive s φ x₀` has Fréchet
derivative `φ w` at every `w ∈ s`. -/
theorem HasLocalPotentials.hasFDerivAt_localPotentialPrimitive_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) (hx₀ : x₀ ∈ s)
    {w : E} (hw : w ∈ s) :
    HasFDerivAt (localPotentialPrimitive s φ x₀) (φ w) w :=
  hφ.hasFDerivAt_localPotentialPrimitive
    (fun η hη ↦ hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected hs η hη)
    (hs.isPathConnected.joinedIn x₀ hx₀ w hw)

/-- On a simply connected domain (`IsSimplyConnected s`), every covector field with local
potentials admits a global `C¹` potential. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w :=
  (hφ.exists_hasFDerivAt_iff_forall_loop_eq_zero hs.isPathConnected).mpr fun _ _ η hη ↦
    hφ.localPotentialCurveIntegral_loop_eq_zero_of_isSimplyConnected hs η hη

/-- Every covector field with local potentials on a simply connected domain admits a global `C¹`
potential. -/
theorem exists_hasFDerivAt_of_simplyConnected [SimplyConnectedSpace s]
    (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w :=
  hφ.exists_hasFDerivAt_of_isSimplyConnected ‹SimplyConnectedSpace s›

/-- On a simply connected domain containing `x₀`, a covector field with local potentials admits a
global `C¹` potential taking a prescribed value `y₀` at `x₀`, unique on `s`. -/
theorem exists_hasFDerivAt_eq_of_simplyConnected [SimplyConnectedSpace s]
    (hφ : HasLocalPotentials s φ) (hx₀ : x₀ ∈ s) (y₀ : F) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ g x₀ = y₀ ∧ (∀ w ∈ s, HasFDerivAt g (φ w) w) ∧
      ∀ g' : E → F, (∀ w ∈ s, HasFDerivAt g' (φ w) w) → g' x₀ = y₀ → EqOn g' g s := by
  have hs : IsSimplyConnected s := ‹SimplyConnectedSpace s›
  have hc := hφ.contDiffOn_localPotentialPrimitive_of_isSimplyConnected hs hx₀
  have h0 := hφ.localPotentialPrimitive_self_of_isSimplyConnected hs hx₀
  have hd : ∀ w ∈ s,
      HasFDerivAt (fun z ↦ localPotentialPrimitive s φ x₀ z + y₀) (φ w) w := fun w hw ↦ by
    simpa only [add_zero] using
      (hφ.hasFDerivAt_localPotentialPrimitive_of_isSimplyConnected hs hx₀ hw).add_const y₀
  refine ⟨fun w ↦ localPotentialPrimitive s φ x₀ w + y₀, hc.add contDiffOn_const, by simp [h0],
    hd, fun g' hd' hg'₀ ↦ ?_⟩
  exact hφ.isOpen.eqOn_of_fderiv_eq hs.isPathConnected.isConnected.isPreconnected
    (fun w hw ↦ (hd' w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd' w hw).fderiv.trans (hd w hw).fderiv.symm)
    hx₀ (by simp [hg'₀, h0])

/-- If every connected component of `s` is simply connected (including when `s` is empty), then
every covector field with local potentials on `s` admits a global `C¹` potential on `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_isSimplyConnected_connectedComponentIn
    (hφ : HasLocalPotentials s φ)
    (hcomp : ∀ x ∈ s, IsSimplyConnected (connectedComponentIn s x)) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w := by
  let 𝓒 : Set (Set E) := connectedComponentIn s '' s
  have hC_ex : ∀ C : 𝓒, ∃ g : E → F, ContDiffOn ℝ 1 g C.1 ∧ ∀ w ∈ C.1, HasFDerivAt g (φ w) w := by
    intro C
    obtain ⟨x, hx, hCx⟩ := C.2
    have hC_open : IsOpen C.1 := hCx ▸ hφ.isOpen.connectedComponentIn
    have hC_sub : C.1 ⊆ s := hCx ▸ connectedComponentIn_subset s x
    have hC_sc : IsSimplyConnected C.1 := hCx ▸ hcomp x hx
    exact (hφ.mono hC_open hC_sub).exists_hasFDerivAt_of_isSimplyConnected hC_sc
  choose gC hgC_cont hgC_deriv using hC_ex
  let g : E → F := by
    classical
    exact fun w ↦ if hw : w ∈ s then gC ⟨connectedComponentIn s w, ⟨w, hw, rfl⟩⟩ w else 0
  have heq_comp : ∀ x (hx : x ∈ s),
      EqOn g (gC ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩) (connectedComponentIn s x) := by
    intro x hx y hy
    have hys : y ∈ s := connectedComponentIn_subset s x hy
    have hcomp_eq : connectedComponentIn s y = connectedComponentIn s x :=
      (connectedComponentIn_eq hy).symm
    have hsub_eq : (⟨connectedComponentIn s y, ⟨y, hys, rfl⟩⟩ : 𝓒) =
        ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩ :=
      Subtype.ext hcomp_eq
    dsimp only [g]
    rw [dite_eq_left hys, hsub_eq]
  refine ⟨g, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hnhds : connectedComponentIn s x ∈ 𝓝 x :=
      hφ.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx)
    have hev : g =ᶠ[𝓝 x] gC ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩ :=
      Filter.eventuallyEq_of_mem hnhds (heq_comp x hx)
    exact ((hgC_cont ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩).contDiffAt hnhds
      |>.congr_of_eventuallyEq hev).contDiffWithinAt
  · have hnhds : connectedComponentIn s x ∈ 𝓝 x :=
      hφ.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx)
    have hev : g =ᶠ[𝓝 x] gC ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩ :=
      Filter.eventuallyEq_of_mem hnhds (heq_comp x hx)
    exact (hgC_deriv ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩ x
      (mem_connectedComponentIn hx)).congr_of_eventuallyEq hev

end TauCeti
