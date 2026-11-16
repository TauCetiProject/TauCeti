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

On a finite-dimensional boundaryless manifold, near a point where a `C^m` vector field `v`
(`1 ≤ m`) does not vanish, the transport equation `dh(v) = b` has a `C^m` solution for every `b`
that is `C^m` near the point, with values in a complete real normed space. The solution is
normalized to zero on a local transverse slice, the zero set of a `C^m` real function `s` with
`ds(v) = 1`, and along that slice its differential is `ds ⊗ b`. No completeness of `v` is
required.

Straighten the field, extend the coordinate expression of `b` to the whole model space
(`exists_contDiff_comp_extend_eventuallyEq`), and integrate along the constant coordinate
direction. This construction is useful for the Reeb-direction equation in strict contact-Moser
arguments.

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
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Extending a coordinate expression.** On a finite-dimensional boundaryless manifold, a
function `b` which is `C^m` on a neighbourhood of `x`, read in a `C^m` chart `e` around `x`,
agrees near `x` with a globally `C^m` function on the model space composed with the extended
chart. -/
theorem exists_contDiff_comp_extend_eventuallyEq {m : ℕ∞} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I m M) {b : M → F}
    {U : Set M} {x : M} (hxe : x ∈ e.source) (hb : ContMDiffOn I 𝓘(ℝ, F) m b U)
    (hU : U ∈ 𝓝 x) :
    ∃ B : E → F, ContDiff ℝ m B ∧ B ∘ e.extend I =ᶠ[𝓝 x] b := by
  let c := e.extend I
  let W := c.target ∩ c.symm ⁻¹' interior U
  have hWo : IsOpen W :=
    e.continuousOn_extend_symm.isOpen_inter_preimage e.isOpen_extend_target isOpen_interior
  have hxc : x ∈ c.source := by rwa [e.extend_source]
  have hxW : c x ∈ W :=
    ⟨c.map_source hxc, by simpa only [mem_preimage, c.left_inv hxc] using
      mem_interior_iff_mem_nhds.2 hU⟩
  have hci : ContMDiffOn 𝓘(ℝ, E) I m c.symm c.target := by
    simpa only [c, e.extend_target'] using contMDiffOn_extend_symm he
  have hbW : ContDiffOn ℝ m (b ∘ c.symm) W :=
    ((hb.mono interior_subset).comp (hci.mono inter_subset_left) fun y hy ↦ hy.2).contDiffOn
  obtain ⟨B, hB, -, hBb⟩ := hbW.exists_contDiff_eventuallyEq_of_finiteDimensional
    (hWo.mem_nhds hxW)
  refine ⟨B, hB, ?_⟩
  filter_upwards [(e.continuousAt_extend (I := I) hxe).tendsto.eventually hBb,
    e.extend_source_mem_nhds (I := I) hxe] with y hy hyc
  simpa only [c, comp_apply, (e.extend I).left_inv hyc] using hy

/-- **Local solvability of the transport equation.** Let `M` be a finite-dimensional boundaryless
manifold, `v` a `C^m` vector field with `1 ≤ m` that does not vanish at `x`, and `b` a function
with values in a complete real normed space that is `C^m` on a neighbourhood `U` of `x`. Then on
an open neighbourhood `V ⊆ U` of `x` there are `C^m` functions `h` and `s` with `dh(v) = b`,
`ds(v) = 1` and `s x = 0`, such that `h` vanishes on the transverse slice `s = 0` and its
differential there is `ds ⊗ b`. -/
theorem exists_contMDiffOn_mvfderiv_apply_eq_of_ne_zero {m : ℕ∞} {n : ℕ∞ω} (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) [IsManifold I 1 M] [IsManifold I n M] [CompleteSpace F]
    {v : (y : M) → TangentSpace I y} {b : M → F} {U : Set M} {x : M}
    (hv : ContMDiffOn I I.tangent m (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) U)
    (hb : ContMDiffOn I 𝓘(ℝ, F) m b U) (hU : U ∈ 𝓝 x) (hx : v x ≠ 0) :
    ∃ (V : Set M) (h : M → F) (s : M → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContMDiffOn I 𝓘(ℝ, F) m h V ∧ ContMDiffOn I 𝓘(ℝ) m s V ∧ s x = 0 ∧
      (∀ y ∈ V, mvfderiv I h y (v y) = b y) ∧
      (∀ y ∈ V, mvfderiv I s y (v y) = 1) ∧
      (∀ y ∈ V, s y = 0 → h y = 0) ∧
      (∀ y ∈ V, s y = 0 → mvfderiv I h y = (mvfderiv I s y).smulRight (b y)) := by
  have hm1 : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hm1).ne'
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  obtain ⟨e, u, he, hxe, hu, hvu⟩ :=
    exists_chart_mfderiv_eq_const hm hmn BoundarylessManifold.isInteriorPoint hv hU hx
  let c := e.extend I
  have hcu (y : M) (hy : y ∈ e.source) : mfderiv I 𝓘(ℝ, E) c y (v y) = u := by
    have hvy := hvu y hy
    rwa [← e.extend_coe] at hvy
  obtain ⟨B, hB, hBb⟩ := exists_contDiff_comp_extend_eventuallyEq he hxe hb hU
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
  let P := directionalPrimitive u ℓ (c x) B
  have hP : ContDiff ℝ m P := contDiff_directionalPrimitive u ℓ (c x) hB
  have hB1 : ContDiff ℝ 1 B := hB.of_le hm1
  let h : M → F := P ∘ c
  let s : M → ℝ := fun y ↦ ℓ (c y - c x)
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.1
    (Filter.Eventually.and hBb (Filter.Eventually.and (e.open_source.mem_nhds hxe) hU))
  have hcV : ContMDiffOn I 𝓘(ℝ, E) m c V :=
    (e.contMDiffOn_extend he).mono fun y hy ↦ (hV hy).2.1
  have hcd (y : M) (hy : y ∈ V) : MDifferentiableAt I 𝓘(ℝ, E) c y :=
    ((hcV y hy).contMDiffAt (hVo.mem_nhds hy)).mdifferentiableAt hm0
  have hlin (z : E) : HasFDerivAt (fun z : E ↦ ℓ (z - c x)) ℓ z := by
    convert ℓ.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (c x)) using 1 <;>
      simp [Function.comp_def]
  -- Both derivatives are read through the derivative of the chart.
  have hds (y : M) (hy : y ∈ V) (w : TangentSpace I y) :
      mvfderiv I s y w = ℓ (mfderiv I 𝓘(ℝ, E) c y w) := by
    have hsc : s = (fun z : E ↦ ℓ (z - c x)) ∘ c := (rfl)
    rw [hsc, mvfderiv_comp_apply_of_differentiableAt (hlin _).differentiableAt (hcd y hy),
      (hlin _).fderiv, mvfderiv_apply_eq_mfderiv_apply]
  have hdh (y : M) (hy : y ∈ V) (w : TangentSpace I y) :
      mvfderiv I h y w = fderiv ℝ P (c y) (mfderiv I 𝓘(ℝ, E) c y w) := by
    rw [mvfderiv_comp_apply_of_differentiableAt (hP.differentiable hm0 _) (hcd y hy),
      mvfderiv_apply_eq_mfderiv_apply]
  refine ⟨V, h, s, hVo, hxV, fun y hy ↦ (hV hy).2.2, hP.contMDiff.comp_contMDiffOn hcV,
    ℓ.contDiff.contMDiff.comp_contMDiffOn (hcV.sub contMDiffOn_const), by simp [s], ?_, ?_,
    fun y _ hy ↦ directionalPrimitive_eq_zero u ℓ (c x) B hy, ?_⟩
  · intro y hy
    rw [hdh y hy, hcu y (hV hy).2.1, fderiv_directionalPrimitive_apply u ℓ (c x) hℓ hB1]
    exact (hV hy).1
  · intro y hy
    rw [hds y hy, hcu y (hV hy).2.1, hℓ]
  · intro y hy hsy
    ext w
    rw [hdh y hy, fderiv_directionalPrimitive_of_eq_zero u ℓ (c x) hℓ hB1 hsy]
    change ℓ (mfderiv I 𝓘(ℝ, E) c y w) • B (c y) = mvfderiv I s y w • b y
    rw [hds y hy]
    exact congrArg _ (hV hy).1

end TauCeti
