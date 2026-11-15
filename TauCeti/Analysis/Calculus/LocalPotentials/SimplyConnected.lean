/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Global potentials on simply connected domains

Every continuous covector field `φ : E → E →L[ℝ] F` with local `C¹` potentials on a simply
connected open subset `s` of a real normed space `E` admits a global `C¹` potential `g : E → F`
whose Fréchet derivative at each point `x ∈ s` is `φ x`
(`TauCeti.exists_hasFDerivAt_of_simplyConnected`). Neither completeness of `E` or `F`, nor finite
dimensionality of `E`, nor differentiability of `φ` is required: simple connectivity contracts
every loop in `s` relative to its basepoint, so all loop integrals vanish by the cell-subdivision
homotopy invariance of `TauCeti.localPotentialIntegral`, and path-independent integration from a
basepoint constructs `g`.

Because a real normed space is locally connected, every connected component of an open domain
`s ⊆ E` is open (`IsOpen.connectedComponentIn`). Applying `exists_hasFDerivAt_of_simplyConnected`
independently on each connected component yields a global `C¹` potential whenever every connected
component of `s` is simply connected
(`TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn`),
taking the zero potential outside `s` and in particular on the empty domain.

## Main declarations

* `TauCeti.exists_hasFDerivAt_of_simplyConnected`: global `C¹` potential on a simply connected
  domain carrying local potentials.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn`:
  global `C¹` potential (vanishing outside `s`) when each connected component of `s` is simply
  connected.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §1.3 & §4.2 (the
  monodromy construction of global primitives from local primitives on simply connected domains).
-/

public section

open Set Metric Filter
open scoped Topology ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Exactness on simply connected domains.** A covector field `φ : E → E →L[ℝ] F` with local
`C¹` potentials on a simply connected domain `s ⊆ E` admits an ambient potential `g : E → F` that
is `C¹` on `s` and has Fréchet derivative `φ x` at every `x ∈ s`. No completeness of `E` or `F`,
finite dimensionality, or differentiability of `φ` is needed. -/
theorem exists_hasFDerivAt_of_simplyConnected {s : Set E} [SimplyConnectedSpace s]
    {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ x ∈ s, HasFDerivAt g (φ x) x := by
  have hs : IsSimplyConnected s := ‹SimplyConnectedSpace s›
  obtain ⟨x₀, hx₀⟩ := hs.nonempty
  obtain ⟨hpc, hhom⟩ := isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hs
  obtain ⟨g, -, hg, hd, -⟩ :=
    hφ.exists_hasFDerivAt_of_forall_loop_localPotentialIntegral_eq_zero hpc hx₀ fun γ hγ ↦ by
      obtain ⟨H, hH⟩ := hhom x₀ γ hγ
      exact hφ.localPotentialIntegral_loop_eq_zero_of_homotopy_refl H hH
  exact ⟨g, hg, hd⟩

/-- **Componentwise exactness on open domains with simply connected components.** If `φ` has local
`C¹` potentials on `s` and every connected component of `s` is simply connected, then `φ` admits a
global `C¹` potential `g : E → F` on `s` that vanishes outside `s` (hence equals `0` when
`s = ∅`). -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn
    {s : Set E} {φ : E → E →L[ℝ] F} (hφ : HasLocalPotentials s φ)
    (hc : ∀ x ∈ s, IsSimplyConnected (connectedComponentIn s x)) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ (∀ x ∈ s, HasFDerivAt g (φ x) x) ∧ ∀ x ∉ s, g x = 0 := by
  classical
  let Comp := {C : Set E // ∃ x ∈ s, C = connectedComponentIn s x}
  have hex (C : Comp) :
      ∃ g : E → F, ContDiffOn ℝ 1 g C.1 ∧ ∀ y ∈ C.1, HasFDerivAt g (φ y) y := by
    obtain ⟨x, hx, hC⟩ := C.2
    have hC_open : IsOpen C.1 := hC ▸ hφ.isOpen.connectedComponentIn
    have hC_sub : C.1 ⊆ s := hC ▸ connectedComponentIn_subset s x
    have : SimplyConnectedSpace C.1 := (hC ▸ hc x hx).simplyConnectedSpace
    exact exists_hasFDerivAt_of_simplyConnected (hφ.mono hC_open hC_sub)
  choose gComp hgComp hdComp using hex
  let g : E → F := fun y ↦
    if hy : y ∈ s then gComp ⟨connectedComponentIn s y, y, hy, rfl⟩ y else 0
  have hlocal {x : E} (hx : x ∈ s) :
      ContDiffAt ℝ 1 g x ∧ HasFDerivAt g (φ x) x := by
    let Cx : Comp := ⟨connectedComponentIn s x, x, hx, rfl⟩
    have hmem_nhds : connectedComponentIn s x ∈ 𝓝 x :=
      hφ.isOpen.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx)
    have heq : g =ᶠ[𝓝 x] gComp Cx := by
      filter_upwards [hmem_nhds] with y hy
      have hys : y ∈ s := connectedComponentIn_subset s x hy
      have hCeq : (⟨connectedComponentIn s y, y, hys, rfl⟩ : Comp) = Cx :=
        Subtype.ext (connectedComponentIn_eq hy).symm
      simp only [g, hys, ↓reduceDIte, hCeq]
    exact ⟨((hgComp Cx).contDiffAt hmem_nhds).congr_of_eventuallyEq heq,
      (hdComp Cx x (mem_connectedComponentIn hx)).congr_of_eventuallyEq heq⟩
  exact ⟨g, fun x hx ↦ (hlocal hx).1.contDiffWithinAt, fun x hx ↦ (hlocal hx).2,
    fun x hx ↦ by simp [g, hx]⟩

end TauCeti
