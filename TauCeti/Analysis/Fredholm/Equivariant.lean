/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Topology.Algebra.Module.InvariantComplement

/-!
# Equivariant Fredholm packages

Let a finite group `G`, whose order is invertible in the scalar field, act on `E` and on `F` by
continuous linear maps, and let `u : E →L[𝕜] F` be a Fredholm operator intertwining the two
actions. The kernel of `u` and its range are then invariant, and averaging projections over `G`
(`Submodule.ClosedComplemented.exists_isTopCompl_forall_mapsTo`) gives them invariant topological
complements. So `u` has a Fredholm package whose four summands are `G`-invariant
(`ContinuousLinearMap.IsFredholm.exists_fredholmPackage_forall_mapsTo`).

This is the linear input of the equivariant Lyapunov–Schmidt reduction in
`TauCeti.Analysis.Fredholm.NormalForm.Equivariant`.

## Main results

* `ContinuousLinearMap.mapsTo_ker_of_comp_eq_comp`,
  `ContinuousLinearMap.mapsTo_range_of_comp_eq_comp`: an operator intertwining two maps has
  invariant kernel and range.
* `ContinuousLinearMap.IsFredholm.exists_fredholmPackage_forall_mapsTo`: an equivariant Fredholm
  operator has a Fredholm package with invariant summands.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory, Vol. I*,
  Applied Mathematical Sciences 51, Springer, 1985, Chapter VII, §3 (the equivariant
  Lyapunov–Schmidt reduction).
-/

public section

open Set

namespace ContinuousLinearMap

section Intertwining

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E]
  [Module R F] [TopologicalSpace E] [TopologicalSpace F]
  {u : E →L[R] F} {σ : E →L[R] E} {τ : F →L[R] F}

/-- If `u` intertwines `σ` with `τ`, then `σ` preserves the kernel of `u`. -/
theorem mapsTo_ker_of_comp_eq_comp (h : u ∘L σ = τ ∘L u) : MapsTo σ u.ker u.ker := fun x hx ↦ by
  simp only [SetLike.mem_coe, LinearMap.mem_ker, coe_coe] at hx ⊢
  rw [← comp_apply, h, comp_apply, hx, map_zero]

/-- If `u` intertwines `σ` with `τ`, then `τ` preserves the range of `u`. -/
theorem mapsTo_range_of_comp_eq_comp (h : u ∘L σ = τ ∘L u) : MapsTo τ u.range u.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, congr($h x)⟩

end Intertwining

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 E] [ContinuousSMul 𝕜 F]

/-- **Equivariant Fredholm packages.** Let a finite group `G`, whose order is invertible in `𝕜`,
act on `E` and on `F` by continuous linear maps, and let `u` be a Fredholm operator intertwining
the two actions. Then `u` has a Fredholm package whose four summands are invariant under the
actions. -/
theorem IsFredholm.exists_fredholmPackage_forall_mapsTo {G : Type*} [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : 𝕜)) {u : E →L[𝕜] F} (hu : u.IsFredholm)
    (ρ : G →* E →L[𝕜] E) (ρ' : G →* F →L[𝕜] F) (hρ : ∀ g x, u (ρ g x) = ρ' g (u x)) :
    ∃ pkg : FredholmPackage u, ∀ g,
      MapsTo (ρ g) pkg.decDom.X₀ pkg.decDom.X₀ ∧ MapsTo (ρ g) pkg.decDom.X₁ pkg.decDom.X₁ ∧
        MapsTo (ρ' g) pkg.decCodom.X₀ pkg.decCodom.X₀ ∧
          MapsTo (ρ' g) pkg.decCodom.X₁ pkg.decCodom.X₁ := by
  have hker (g : G) := mapsTo_ker_of_comp_eq_comp (ext (hρ g))
  have hrange (g : G) := mapsTo_range_of_comp_eq_comp (ext (hρ g))
  obtain ⟨dom₁, h_dom, h_dom₁⟩ :=
    hu.closedComplemented_ker.exists_isTopCompl_forall_mapsTo hG ρ hker
  obtain ⟨codom₀, h_codom, h_codom₀⟩ :=
    hu.closedComplemented_range.exists_isTopCompl_forall_mapsTo hG ρ' hrange
  exact ⟨hu.fredholmPackage h_dom h_codom, fun g ↦ ⟨hker g, h_dom₁ g, h_codom₀ g, hrange g⟩⟩

end ContinuousLinearMap
