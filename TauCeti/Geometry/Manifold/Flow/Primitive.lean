/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DirectionalPrimitive
public import TauCeti.Geometry.Manifold.Flow.Straightening
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local primitives along a nonvanishing vector field

Near a regular point of a smooth vector field `v`, the transport equation `dh(v) = b` has a
smooth solution, normalized to zero on a local transverse slice. The slice is the zero set
of a smooth real function `s` with `ds(v) = 1`. No completeness of `v` is required.

Straighten the field, extend the coordinate expression of `b` smoothly near the chosen point,
and integrate along the constant coordinate direction. This construction is useful for the
Reeb-direction equation in strict contact-Moser arguments. The right-hand side may take values
in any complete real normed space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.22.
* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*, Proposition 43.18.
-/

public noncomputable section

open Set Filter Topology Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Local solvability of the transport equation.** Near a point where a smooth vector field
`v` does not vanish, every smooth `b` has a smooth primitive `h` with `dh(v) = b`, vanishing on a
local transverse slice. The slice is described by `s = 0`, with `s x = 0` and `ds(v) = 1`.
The data need only be smooth on a neighbourhood of the point. -/
theorem exists_contMDiffOn_mvfderiv_apply_eq_of_ne_zero
    {v : (y : M) → TangentSpace I y} {b : M → F} {U : Set M} {x : M}
    (hv : ContMDiffOn I I.tangent ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) U)
    (hb : ContMDiffOn I 𝓘(ℝ, F) ∞ b U) (hU : U ∈ 𝓝 x) (hx : v x ≠ 0) :
    ∃ (V : Set M) (h : M → F) (s : M → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContMDiffOn I 𝓘(ℝ, F) ∞ h V ∧ ContMDiffOn I 𝓘(ℝ) ∞ s V ∧ s x = 0 ∧
      (∀ y ∈ V, mvfderiv I h y (v y) = b y) ∧
      (∀ y ∈ V, mvfderiv I s y (v y) = 1) ∧
      (∀ y ∈ V, s y = 0 → h y = 0) := by
  obtain ⟨e, u, he, hxe, hu, hvu⟩ :=
    exists_chart_mfderiv_eq_const (m := (⊤ : ℕ∞)) (n := ∞) (by simp) (by simp) hv hU hx
  let c := e.extend I
  have hcs : c.source = e.source := e.extend_source
  have hcl (y : M) (hy : y ∈ e.source) : c.symm (c y) = y := e.extend_left_inv hy
  have hcu (y : M) (hy : y ∈ e.source) :
      mfderiv I 𝓘(ℝ, E) c y (v y) = u := hvu y hy
  have hxc : x ∈ c.source := by simpa [c, e.extend_source] using hxe
  have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source := by
    simpa only [c, e.extend_source] using e.contMDiffOn_extend he
  have hci : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target := by
    simpa only [c, e.extend_target'] using contMDiffOn_extend_symm he
  -- Extend only the right-hand side; the vector field has already been straightened.
  let W := c.target ∩ c.symm ⁻¹' interior U
  have hWo : IsOpen W :=
    e.continuousOn_extend_symm.isOpen_inter_preimage e.isOpen_extend_target isOpen_interior
  have hxcW : c x ∈ W :=
    ⟨c.map_source hxc, by simpa only [mem_preimage, c.left_inv hxc] using
      mem_interior_iff_mem_nhds.2 hU⟩
  have hbW : ContDiffOn ℝ ∞ (b ∘ c.symm) W :=
    ((hb.mono interior_subset).comp (hci.mono inter_subset_left) fun y hy ↦ hy.2).contDiffOn
  obtain ⟨B, hB, -, hBb⟩ := hbW.exists_contDiff_eventuallyEq_of_finiteDimensional
    (hWo.mem_nhds hxcW)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
  let P := directionalPrimitive u ℓ (c x) B
  have hP : ContDiff ℝ ∞ P := contDiff_directionalPrimitive u ℓ (c x) hB
  let h : M → F := P ∘ c
  let s : M → ℝ := fun y ↦ ℓ (c y - c x)
  have hmatch : ∀ᶠ y in 𝓝 x, B (c y) = b y := by
    have hcc := hc.continuousOn.continuousAt (e.isOpen_extend_source.mem_nhds hxc)
    filter_upwards [hcc.tendsto.eventually hBb,
      e.open_source.mem_nhds hxe] with y hy hye
    simpa only [comp_apply, hcl y hye] using hy
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.1
    (Filter.Eventually.and hmatch (Filter.Eventually.and (e.open_source.mem_nhds hxe) hU))
  have hVc : V ⊆ c.source := fun y hy ↦ by
    rw [hcs]
    exact (hV hy).2.1
  have hcV := hc.mono hVc
  have hs : ContMDiffOn I 𝓘(ℝ) ∞ s V :=
    ℓ.contDiff.contMDiff.comp_contMDiffOn (hcV.sub contMDiffOn_const)
  refine ⟨V, h, s, hVo, hxV, fun y hy ↦ (hV hy).2.2,
    hP.contMDiff.comp_contMDiffOn hcV, hs, by simp [s], ?_, ?_, ?_⟩
  · intro y hy
    have hcy := (hcV y hy).contMDiffAt (hVo.mem_nhds hy)
    rw [mvfderiv_comp_apply_of_differentiableAt
      (hP.differentiable (by simp) _) (hcy.mdifferentiableAt (by simp)),
      mvfderiv_apply_eq_mfderiv_apply, hcu y ((hV hy).2.1),
      fderiv_directionalPrimitive_apply u ℓ (c x) hℓ (hB.of_le (by simp))]
    exact (hV hy).1
  · intro y hy
    have hcy := (hcV y hy).contMDiffAt (hVo.mem_nhds hy)
    have hsc : s = (fun z : E ↦ ℓ (z - c x)) ∘ c := (rfl)
    have hlin : HasFDerivAt (fun z : E ↦ ℓ (z - c x)) ℓ (c y) := by
      convert ℓ.hasFDerivAt.comp (c y) ((hasFDerivAt_id (c y)).sub_const (c x)) using 1 <;>
        simp [Function.comp_def]
    rw [hsc, mvfderiv_comp_apply_of_differentiableAt hlin.differentiableAt
      (hcy.mdifferentiableAt (by simp)), hlin.fderiv,
      mvfderiv_apply_eq_mfderiv_apply, hcu y ((hV hy).2.1)]
    exact hℓ
  · intro y _ hy
    exact directionalPrimitive_eq_zero u ℓ (c x) B hy

end TauCeti
