/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Global potentials on simply connected domains

Every continuous covector field `φ : E → E →L[ℝ] F` carrying local `C¹` potentials on a simply
connected domain `s` in a real normed space `E` admits a global `C¹` potential `g : E → F` on `s`
with derivative `φ x` at every `x ∈ s`. Because the potential is constructed from the continuous
path integral `TauCeti.localPotentialIntegral` and its homotopy invariance, neither finite
dimensionality of `E` nor completeness of `E` or `F` is assumed.

More generally, if every connected component of `s` is simply connected, gluing potentials across
the open connected components produces a global `C¹` potential on `s`, taking the zero function
when `s` is empty.

## Main results

* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected`: a covector field with local
  potentials on a simply connected set `s` has a global `C¹` potential on `s`.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected`: the subtype-typeclass form
  under `[SimplyConnectedSpace s]`.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_forall_isSimplyConnected_connectedComponentIn`:
  componentwise extension to domains whose connected components are all simply connected.
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A covector field with local potentials on a simply connected domain `s` has a global `C¹`
potential on `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected {s : Set E}
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  obtain ⟨x₀, hx₀⟩ := hs.nonempty
  refine (hφ.exists_hasFDerivAt_iff_forall_loop_eq_zero hs.isPathConnected hx₀).mpr fun ℓ hℓ ↦ ?_
  obtain ⟨H, hH⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hs).2 x₀ ℓ hℓ
  rw [localPotentialIntegral_eq_of_homotopy hφ H fun t u ↦ hH (t, u), localPotentialIntegral_refl]

/-- A covector field with local potentials on a domain `s` with `[SimplyConnectedSpace s]` has a
global `C¹` potential on `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected {s : Set E}
    [SimplyConnectedSpace s] {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x :=
  hφ.exists_hasFDerivAt_of_isSimplyConnected ‹_›

/-- If `φ` has local potentials on `s` and every connected component of `s` is simply connected,
then `φ` admits a global `C¹` potential on `s` (equal to `0` outside `s`, hence `0` when
`s = ∅`). -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_isSimplyConnected_connectedComponentIn
    {s : Set E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ)
    (hsc : ∀ x ∈ s, IsSimplyConnected (connectedComponentIn s x)) :
    ∃ g : E → F, (∀ x ∉ s, g x = 0) ∧ ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  classical
  let Comp := {C : Set E // ∃ x ∈ s, C = connectedComponentIn s x}
  have hComp : ∀ C : Comp,
      ∃ g : E → F, ContDiffOn ℝ 1 g C.1 ∧ ∀ y ∈ C.1, HasFDerivAt g (φ y) y := by
    rintro ⟨_, x, hx, rfl⟩
    exact (hφ.mono hφ.isOpen.connectedComponentIn (connectedComponentIn_subset s x))
      |>.exists_hasFDerivAt_of_isSimplyConnected (hsc x hx)
  choose gComp hgComp hdComp using hComp
  let g : E → F := fun y ↦
    if hy : y ∈ s then gComp ⟨connectedComponentIn s y, y, hy, rfl⟩ y else 0
  have heq_on_comp (x : E) (hx : x ∈ s) :
      g =ᶠ[𝓝 x] gComp ⟨connectedComponentIn s x, x, hx, rfl⟩ := by
    filter_upwards [hφ.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx)] with y hy
    have hys : y ∈ s := connectedComponentIn_subset s x hy
    have hCeq : (⟨connectedComponentIn s y, y, hys, rfl⟩ : Comp) =
        ⟨connectedComponentIn s x, x, hx, rfl⟩ :=
      Subtype.ext (connectedComponentIn_eq hy).symm
    simp [g, hys, hCeq]
  refine ⟨g, fun x hx ↦ by simp [g, hx], fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hnhds := hφ.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx)
    exact ((hgComp ⟨connectedComponentIn s x, x, hx, rfl⟩ |>.contDiffAt hnhds).congr_of_eventuallyEq
      (heq_on_comp x hx)).contDiffWithinAt
  · exact (hdComp ⟨connectedComponentIn s x, x, hx, rfl⟩ x
      (mem_connectedComponentIn hx)).congr_of_eventuallyEq (heq_on_comp x hx)

end TauCeti
