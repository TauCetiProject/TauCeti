/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Global potentials on simply connected open sets

Let `φ : E → E →L[ℝ] F` be a covector field with `HasLocalPotentials s φ` on an open subset `s`
of a real normed space `E`, with values in an arbitrary real normed space `F` (no completeness of
`E` or `F`, and no finite-dimensionality of `E`, is assumed).

Using `localPotentialIntegral` and its homotopy invariance, we establish:

* `TauCeti.HasLocalPotentials.contDiffOn_of_hasFDerivAt`: any function whose Fréchet derivative on
  `s` equals `φ` is automatically `C¹` on `s`.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero`: on a nonempty connected
  open set `s`, `φ` admits a global `C¹` potential if and only if `localPotentialIntegral φ γ = 0`
  for every loop `γ` in `s` based at a chosen point `x₀ ∈ s`.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected` and
  `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected`: on a simply connected open
  set `s`, every covector field with local potentials admits a global `C¹` potential.
* `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_forall_connectedComponentIn`: the same holds
  on any open set (possibly empty or disconnected) whose connected components are simply connected.
-/

public section

open Set Metric Filter unitInterval
open scoped Topology ContDiff Convex

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {φ : E → E →L[ℝ] F}

private theorem locallyPathConnectedSpace_of_normedSpace : LocallyPathConnectedSpace E :=
  .of_bases (fun _ ↦ Metric.nhds_basis_ball) fun x _ hr ↦
    (convex_ball x _).isPathConnected (nonempty_ball.mpr hr)

private theorem path_trans_mem {X : Type*} [TopologicalSpace X] {s : Set X}
    {a b c : X} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : ∀ t, γ₁ t ∈ s) (h₂ : ∀ t, γ₂ t ∈ s) (t : I) : (γ₁.trans γ₂) t ∈ s := by
  have ht : (γ₁.trans γ₂) t ∈ range γ₁ ∪ range γ₂ := by
    rw [← Path.trans_range]; exact mem_range_self t
  rcases ht with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hv ▸ h₁ v
  · exact hv ▸ h₂ v

/-- Any global potential of a covector field with local `C¹` potentials is automatically `C¹` on
`s`, because on each local potential ball it differs from a `C¹` local potential by a constant. -/
theorem HasLocalPotentials.contDiffOn_of_hasFDerivAt (hφ : HasLocalPotentials s φ) {g : E → F}
    (hg : ∀ w ∈ s, HasFDerivAt g (φ w) w) : ContDiffOn ℝ 1 g s := by
  intro w hw
  obtain ⟨r, hr, hrs, gw, hgw_cont, hgw_deriv⟩ := hasLocalPotentials_iff.mp hφ w hw
  have heq : EqOn g (fun y ↦ gw y + (g w - gw w)) (ball w r) := fun y hy ↦ by
    have hsub := isOpen_ball.sub_eq_sub_of_hasFDerivAt (convex_ball w r).isPreconnected
      (fun z hz ↦ hg z (hrs hz)) hgw_deriv (mem_ball_self hr) hy
    calc
      g y = g y - g w + g w := (sub_add_cancel _ _).symm
      _ = gw y - gw w + g w := by rw [hsub]
      _ = gw y + (g w - gw w) := by abel
  exact ((hgw_cont.add contDiffOn_const).congr heq).contDiffAt
    (ball_mem_nhds w hr) |>.contDiffWithinAt

/-- On a preconnected open domain carrying local potentials for `φ`, if every loop at a basepoint
`x₀ ∈ s` has zero `localPotentialIntegral`, then `localPotentialIntegral φ` depends only on the
endpoints of paths in `s`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ) (hs : IsPreconnected s) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hloop : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0)
    {a b : E} {γ₁ γ₂ : Path a b} (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ γ₁ = localPotentialIntegral φ γ₂ := by
  have := locallyPathConnectedSpace_of_normedSpace (E := E)
  have hpc : IsPathConnected s := hφ.isOpen.isConnected_iff_isPathConnected.mp ⟨⟨x₀, hx₀⟩, hs⟩
  have ha : a ∈ s := γ₁.source ▸ hγ₁ 0
  let α : Path x₀ a := (hpc.joinedIn x₀ hx₀ a ha).somePath
  have hα : ∀ t, α t ∈ s := (hpc.joinedIn x₀ hx₀ a ha).somePath_mem
  have hα₁ : ∀ t, (α.trans γ₁) t ∈ s := path_trans_mem hα hγ₁
  have hα₂ : ∀ t, (α.trans γ₂) t ∈ s := path_trans_mem hα hγ₂
  have hzero : localPotentialIntegral φ ((α.trans γ₁).trans (α.trans γ₂).symm) = 0 :=
    hloop _ (path_trans_mem hα₁ fun t ↦ hα₂ (σ t))
  rw [hφ.localPotentialIntegral_trans (α.trans γ₁) (α.trans γ₂).symm hα₁ (fun t ↦ hα₂ (σ t)),
    localPotentialIntegral_symm, hφ.localPotentialIntegral_trans α γ₁ hα hγ₁,
    hφ.localPotentialIntegral_trans α γ₂ hα hγ₂, add_neg_eq_zero] at hzero
  exact add_left_cancel hzero

/-- On a preconnected open domain carrying local potentials for `φ`, vanishing of
`localPotentialIntegral φ` on every loop based at `x₀ ∈ s` produces a global `C¹` potential
vanishing at `x₀`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ) (hs : IsPreconnected s) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hloop : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ g x₀ = 0 ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w := by
  classical
  have := locallyPathConnectedSpace_of_normedSpace (E := E)
  have hpc : IsPathConnected s := hφ.isOpen.isConnected_iff_isPathConnected.mp ⟨⟨x₀, hx₀⟩, hs⟩
  let g : E → F := fun x ↦
    if hx : x ∈ s then localPotentialIntegral φ (hpc.joinedIn x₀ hx₀ x hx).somePath else 0
  have hg₀ : g x₀ = 0 := by
    simp only [g, hx₀, ↓reduceDIte]
    exact hloop _ (hpc.joinedIn x₀ hx₀ x₀ hx₀).somePath_mem
  have hpath {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
      localPotentialIntegral φ γ = g b - g a := by
    have ha : a ∈ s := γ.source ▸ hγ 0
    have hb : b ∈ s := γ.target ▸ hγ 1
    let αa := (hpc.joinedIn x₀ hx₀ a ha).somePath
    let αb := (hpc.joinedIn x₀ hx₀ b hb).somePath
    have hαa : ∀ t, αa t ∈ s := (hpc.joinedIn x₀ hx₀ a ha).somePath_mem
    have hαb : ∀ t, αb t ∈ s := (hpc.joinedIn x₀ hx₀ b hb).somePath_mem
    have heq := hφ.localPotentialIntegral_eq_of_forall_loop_eq_zero hs hx₀ hloop
      (path_trans_mem hαa hγ) hαb
    rw [hφ.localPotentialIntegral_trans αa γ hαa hγ] at heq
    simp only [g, ha, hb, ↓reduceDIte]
    exact eq_sub_of_add_eq' heq
  have hderiv (w : E) (hw : w ∈ s) : HasFDerivAt g (φ w) w := by
    obtain ⟨r, hr, hrs, gw, -, hgw_deriv⟩ := hasLocalPotentials_iff.mp hφ w hw
    have hev : g =ᶠ[𝓝 w] fun y ↦ gw y + (g w - gw w) := by
      filter_upwards [ball_mem_nhds w hr] with y hy
      have hseg_ball : ∀ t, Path.segment w y t ∈ ball w r :=
        range_subset_iff.mp (Path.range_segment w y ▸
          (convex_ball w r).segment_subset (mem_ball_self hr) hy)
      have h₁ := hpath (Path.segment w y) fun t ↦ hrs (hseg_ball t)
      have h₂ := localPotentialIntegral_of_hasFDerivAt isOpen_ball hseg_ball hgw_deriv
      have hsub : g y - g w = gw y - gw w := h₁.symm.trans h₂
      calc
        g y = g y - g w + g w := (sub_add_cancel _ _).symm
        _ = gw y - gw w + g w := by rw [hsub]
        _ = gw y + (g w - gw w) := by abel
    exact ((hgw_deriv w (mem_ball_self hr)).add_const (g w - gw w)).congr_of_eventuallyEq hev
  exact ⟨g, hφ.contDiffOn_of_hasFDerivAt hderiv, hg₀, hderiv⟩

/-- On a preconnected open domain carrying local potentials for `φ` and containing `x₀`, `φ` admits
a global `C¹` potential if and only if every loop in `s` based at `x₀` has zero
`localPotentialIntegral`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_loop_eq_zero
    (hφ : HasLocalPotentials s φ) (hs : IsPreconnected s) {x₀ : E} (hx₀ : x₀ ∈ s) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w) ↔
      ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ s) → localPotentialIntegral φ γ = 0 := by
  constructor
  · rintro ⟨g, -, hg⟩ γ hγ
    rw [localPotentialIntegral_of_hasFDerivAt hφ.isOpen hγ hg, sub_self]
  · intro hloop
    obtain ⟨g, hg_cont, -, hg_deriv⟩ :=
      hφ.exists_hasFDerivAt_of_forall_loop_eq_zero hs hx₀ hloop
    exact ⟨g, hg_cont, hg_deriv⟩

/-- A covector field with local potentials on a simply connected open subset `s` of a real normed
space admits a global `C¹` potential on `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected
    (hφ : HasLocalPotentials s φ) (hs : IsSimplyConnected s) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w := by
  obtain ⟨hpc, hnull⟩ := isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hs
  obtain ⟨x₀, hx₀⟩ := hpc.nonempty
  rw [hφ.exists_hasFDerivAt_iff_forall_loop_eq_zero hpc.isConnected.isPreconnected hx₀]
  intro γ hγ
  obtain ⟨F, hF⟩ := hnull x₀ γ hγ
  rw [hφ.localPotentialIntegral_eq_of_homotopy F hF, localPotentialIntegral_refl]

/-- Typeclass-hypothesis version of `HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected`:
a covector field with local potentials on an open set `s` with `[SimplyConnectedSpace s]` admits a
global `C¹` potential on `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_simplyConnected
    (hφ : HasLocalPotentials s φ) [SimplyConnectedSpace s] :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w :=
  hφ.exists_hasFDerivAt_of_isSimplyConnected ‹SimplyConnectedSpace s›

/-- A covector field with local potentials on an open set `s` whose connected components in `s` are
simply connected admits a global `C¹` potential on `s` (taking the zero potential when `s = ∅`). -/
theorem HasLocalPotentials.exists_hasFDerivAt_of_forall_connectedComponentIn
    (hφ : HasLocalPotentials s φ)
    (hsc : ∀ x ∈ s, IsSimplyConnected (connectedComponentIn s x)) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w := by
  classical
  have := locallyPathConnectedSpace_of_normedSpace (E := E)
  have hcomp_pot (c : connectedComponentIn s '' s) :
      ∃ G : E → F, ∀ w ∈ c.1, HasFDerivAt G (φ w) w := by
    obtain ⟨x, hx, hcx⟩ := c.2
    have hc_open : IsOpen c.1 := hcx ▸ hφ.isOpen.connectedComponentIn
    have hc_sub : c.1 ⊆ s := hcx ▸ connectedComponentIn_subset s x
    have hc_sc : IsSimplyConnected c.1 := hcx ▸ hsc x hx
    obtain ⟨G, -, hG⟩ := (hφ.mono hc_open hc_sub).exists_hasFDerivAt_of_isSimplyConnected hc_sc
    exact ⟨G, hG⟩
  choose G hG using hcomp_pot
  let g : E → F := fun x ↦
    if hx : x ∈ s then G ⟨connectedComponentIn s x, ⟨x, hx, rfl⟩⟩ x else 0
  have hderiv (w : E) (hw : w ∈ s) : HasFDerivAt g (φ w) w := by
    let cw : connectedComponentIn s '' s := ⟨connectedComponentIn s w, ⟨w, hw, rfl⟩⟩
    have hnhds : connectedComponentIn s w ∈ 𝓝 w :=
      connectedComponentIn_mem_nhds (hφ.isOpen.mem_nhds hw)
    have hev : g =ᶠ[𝓝 w] G cw := by
      filter_upwards [hnhds] with y hy
      have hys : y ∈ s := connectedComponentIn_subset s w hy
      have heq : (⟨connectedComponentIn s y, ⟨y, hys, rfl⟩⟩ : connectedComponentIn s '' s) = cw :=
        Subtype.ext (connectedComponentIn_eq hy).symm
      simp only [g, hys, ↓reduceDIte, heq]
    exact (hG cw w (mem_connectedComponentIn hw)).congr_of_eventuallyEq hev
  exact ⟨g, hφ.contDiffOn_of_hasFDerivAt hderiv, hderiv⟩

end TauCeti
