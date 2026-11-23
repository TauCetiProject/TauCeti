/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Poincare

/-!
# Local primitives of closed `1`-forms via the Poincaré lemma

By the Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`), a closed `C^r` `1`-form (`1 ≤ r`) with
complete coefficients on a finite-dimensional Hausdorff smooth manifold admits a `C^r` primitive
near every point (`TauCeti.exists_contMDiff_isPrimitiveOn`). Consequently, the projection of
`TauCeti.PrimitiveSpace φ` is a covering map (`TauCeti.PrimitiveSpace.isCoveringMap_proj`), and
continuous maps into `PrimitiveSpace φ` run locally along translates of `C^r` local primitives
(`TauCeti.PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq`).

## Main declarations

* `TauCeti.exists_contMDiff_isPrimitiveOn`: local `C^r` primitives for closed `C^r` `1`-forms.
* `TauCeti.PrimitiveSpace.isCoveringMap_proj`: `PrimitiveSpace φ` is a covering space when `φ` is
  closed.
* `TauCeti.PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq`: near each parameter, a
  continuous map into `PrimitiveSpace φ` runs along the graph of a translate of a `C^r` local
  primitive.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
* Allen Hatcher, *Algebraic Topology*, Section 1.3 (covering spaces).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]
  {φ : RoughForm I M F 1}

/-- By the Poincaré lemma, a closed `C^r` `1`-form has a `C^r` primitive near every point. -/
theorem exists_contMDiff_isPrimitiveOn {r : ℕ∞} (hr : 1 ≤ r)
    (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) (x : M) :
    ∃ g : M → F, ContMDiff I 𝓘(ℝ, F) r g ∧ ∃ U, x ∈ U ∧ IsPrimitiveOn φ g U := by
  obtain ⟨U, hU, ψ, hψ, hdψ⟩ :=
    exists_mextDeriv_eq_nhds hr hφ (x := x) (Eventually.of_forall fun y ↦ congrFun hclosed y)
  rw [RoughForm.eq_ofFunction ψ] at hψ hdψ
  have hg := isSmoothForm_ofFunction_iff.mp hψ
  refine ⟨_, hg, interior U, mem_interior_iff_mem_nhds.mpr hU, isOpen_interior,
    (hg.mdifferentiable (by simpa using (zero_lt_one.trans_le hr).ne')).mdifferentiableOn,
    fun y hy ↦ hdψ y (interior_subset hy)⟩

namespace PrimitiveSpace

/-- Projecting `PrimitiveSpace φ` to the point is a covering map when `φ` is closed. Over an open
set `U` carrying a primitive `g`, the sheets are the graphs of the translates `g + c`. -/
theorem isCoveringMap_proj {r : ℕ∞} (hr : 1 ≤ r) (hφ : IsSmoothForm I r φ)
    (hclosed : mextDeriv φ = 0) : IsCoveringMap (proj φ) :=
  isCoveringMap_proj_of_forall_exists_isPrimitiveOn fun x ↦
    let ⟨g, _, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
    ⟨g, U, hxU, hgU⟩

/-- **Lifts run along local primitives.** Near each parameter `t`, a continuous map `Γ` into
`PrimitiveSpace φ`, for a closed `C^r` form `φ` (`1 ≤ r`), runs along the graph of a translate
`g + c` of a `C^r` primitive `g` of `φ` on an open set `U` containing the point at `t`. -/
theorem exists_isPrimitiveOn_eventually_value_eq {r : ℕ∞} (hr : 1 ≤ r)
    (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) {X : Type*} [TopologicalSpace X]
    {Γ : X → PrimitiveSpace φ} {t : X} (hΓ : ContinuousAt Γ t) :
    ∃ g : M → F, ContMDiff I 𝓘(ℝ, F) r g ∧ ∃ U, proj φ (Γ t) ∈ U ∧ IsPrimitiveOn φ g U ∧
      ∃ c : F, ∀ᶠ s in 𝓝 t, proj φ (Γ s) ∈ U ∧ value φ (Γ s) = g (proj φ (Γ s)) + c := by
  obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed (proj φ (Γ t))
  exact ⟨g, hg, U, hxU, hgU, _, eventually_value_eq_add_const hΓ hgU hxU⟩

end PrimitiveSpace

end TauCeti
