/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Complex
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Involutivity of the eigenbundles of an almost complex structure

Let `J` be a smooth almost complex structure on a finite-dimensional manifold `M`. Its
complex-linear extension to the complexified tangent spaces `ℂ ⊗[ℝ] T_x M` splits them into the
`i`-eigenspaces `T^(1,0)_x M` and the `-i`-eigenspaces `T^(0,1)_x M`. These eigenbundles are
complex distributions, and this file proves that each of them is involutive for the complex Lie
bracket of complex vector fields exactly when the Nijenhuis tensor `N_J` vanishes. Involutivity of
`T^(0,1) M` is the form of the integrability condition used in the Newlander–Nirenberg theorem
(not proved here), which says that `J` is induced by a complex atlas exactly when `N_J = 0`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.isInvolutiveComplexDistribution_eigenspace_I_iff`:
  `T^(1,0) M` is involutive exactly when `N_J = 0`.
* `TauCeti.SmoothAlmostComplexStructure.isInvolutiveComplexDistribution_eigenspace_neg_I_iff`:
  `T^(0,1) M` is involutive exactly when `N_J = 0`.

## Implementation notes

The local sections of `T^(1,0) M` are the complex vector fields `X - i J X` for real vector fields
`X` (`TauCeti.AlmostComplexStructure.one_tmul_add_I_tmul_mem_eigenspace_baseChange_I_iff`). With
`B = [X, Y]`, `A = [JX, JY]`, `C = [JX, Y]` and `D = [X, JY]`, the complex Lie bracket of
`X - i J X` and `Y - i J Y` is `(B - A) - i (C + D)`, which is again of this form exactly when
`J (B - A) = C + D`; applying `J`, this says `A - B - J C - J D = 0`, that is,
`N_J(X, Y) = 0`. The case of `T^(0,1) M` is the case of `T^(1,0) M` for the almost complex
structure `-J` (`TauCeti.AlmostComplexStructure.eigenspace_neg_baseChange_I`), which has the same
Nijenhuis tensor.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Vol. II,
  Interscience, 1969, Chapter IX, Section 2.
-/

public section

open Set Filter Module.End VectorField
open scoped ContDiff Manifold TensorProduct Topology

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

/-- The complex Lie bracket of the sections `X - i J X` and `Y - i J Y` of `T^(1,0) M` lies in
`T^(1,0)_x M` exactly when `N_J(X, Y)` vanishes at `x`. -/
private lemma complexMlieBracket_mem_eigenspace_I_iff {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    complexMlieBracket I (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] X y + Complex.I ⊗ₜ[ℝ] (-J) y (X y))
        (fun y ↦ (1 : ℂ) ⊗ₜ[ℝ] Y y + Complex.I ⊗ₜ[ℝ] (-J) y (Y y)) x ∈
      eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I ↔
      J.nijenhuis x (X x) (Y x) = 0 := by
  -- `(-J) X` is the negative of the vector field `J X`, so the brackets involving it are
  -- negatives of brackets of `X`, `Y`, `J X` and `J Y`.
  have hneg (V : Π x : M, TangentSpace I x) :
      (fun y ↦ (-J) y (V y)) = -fun y ↦ J y (V y) :=
    funext fun y ↦ J.neg_apply y (V y)
  rw [complexMlieBracket_one_tmul_add_I_tmul, hneg, hneg]
  simp only [mlieBracket_neg_left, mlieBracket_neg_right]
  rw [AlmostComplexStructure.one_tmul_add_I_tmul_mem_eigenspace_baseChange_I_iff,
    J.nijenhuis_apply hX hY]
  simp only [almostComplexStructureAt_toLinearMap, ContinuousLinearMap.coe_coe, map_sub, map_neg]
  -- Write `A = [JX, JY]`, `B = [X, Y]`, `C = [JX, Y]` and `D = [X, JY]` at `x`. The bracket lies
  -- in `T^(1,0)_x` iff `-D - C = -J (B - A)`; applying `J` turns this into `N_J(X, Y) = 0`.
  constructor
  · intro h
    have hJ := congrArg (J x) h
    simp only [map_add, map_neg, map_sub, apply_apply] at hJ
    linear_combination (norm := module) hJ
  · intro h
    have hJ := congrArg (J x) h
    simp only [map_sub, apply_apply, map_zero] at hJ
    linear_combination (norm := module) -hJ

/-- **Integrability of `T^(1,0)`.** The eigenbundle `T^(1,0) M` of the `i`-eigenspaces of the
complexified almost complex structure is involutive exactly when the Nijenhuis tensor of `J`
vanishes. -/
theorem isInvolutiveComplexDistribution_eigenspace_I_iff :
    IsInvolutiveComplexDistribution I
        (fun x ↦ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I) ↔
      J.nijenhuis = 0 := by
  constructor
  · intro hD
    ext x v w
    -- Extend `v` and `w` to vector fields `X` and `Y` differentiable on an open neighbourhood `U`
    -- of `x`; then `X - i J X` and `Y - i J Y` are differentiable sections of `T^(1,0) M` on `U`.
    obtain ⟨s, hs, hXs⟩ := FiberBundle.exists_mdifferentiableOn_extend I E v
    obtain ⟨t, ht, hYt⟩ := FiberBundle.exists_mdifferentiableOn_extend I E w
    obtain ⟨U, hUst, hU, hxU⟩ := mem_nhds_iff.1 (inter_mem hs ht)
    set X := FiberBundle.extend E v
    set Y := FiberBundle.extend E w
    have hX : MDiff[U] (T% X) := hXs.mono (hUst.trans inter_subset_left)
    have hY : MDiff[U] (T% Y) := hYt.mono (hUst.trans inter_subset_right)
    have hJ {V : Π x : M, TangentSpace I x} (hV : MDiff[U] (T% V)) :
        MDiff[U] (T% fun y ↦ (-J) y (V y)) := fun y hy ↦
      ((-J).mdifferentiableAt_apply mdifferentiableAt_id
        ((hV y hy).mdifferentiableAt (hU.mem_nhds hy))).mdifferentiableWithinAt
    have hmem (V : Π x : M, TangentSpace I x) (y : M) :
        (1 : ℂ) ⊗ₜ[ℝ] V y + Complex.I ⊗ₜ[ℝ] (-J) y (V y) ∈
          eigenspace ((J.almostComplexStructureAt y).toLinearMap.baseChange ℂ) Complex.I :=
      (AlmostComplexStructure.one_tmul_add_I_tmul_mem_eigenspace_baseChange_I_iff _ _ _).2
        (by simp)
    have hbr := hD.complexMlieBracket_mem hU (by simpa using hX) (by simpa using hJ hX)
      (by simpa using hY) (by simpa using hJ hY) (fun y _ ↦ hmem X y) (fun y _ ↦ hmem Y y) hxU
    rw [J.complexMlieBracket_mem_eigenspace_I_iff ((hX x hxU).mdifferentiableAt (hU.mem_nhds hxU))
      ((hY x hxU).mdifferentiableAt (hU.mem_nhds hxU))] at hbr
    simpa [X, Y] using hbr
  · intro hN
    rw [isInvolutiveComplexDistribution_iff]
    intro U hU Z W hZre _ hWre _ hZ hW x hx
    -- On `U`, a section of `T^(1,0) M` is `X - i J X` for its real part `X`.
    have hsec {V : Π x : M, ℂ ⊗[ℝ] TangentSpace I x}
        (hV : ∀ y ∈ U, V y ∈
          eigenspace ((J.almostComplexStructureAt y).toLinearMap.baseChange ℂ) Complex.I) :
        ∀ᶠ y in 𝓝 x, V y = (1 : ℂ) ⊗ₜ[ℝ] realPart (TangentSpace I y) (V y) +
          Complex.I ⊗ₜ[ℝ] (-J) y (realPart (TangentSpace I y) (V y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have h := hV y hy
      rw [← one_tmul_realPart_add_I_tmul_imaginaryPart _ (V y),
        AlmostComplexStructure.one_tmul_add_I_tmul_mem_eigenspace_baseChange_I_iff] at h
      conv_lhs => rw [← one_tmul_realPart_add_I_tmul_imaginaryPart _ (V y), h]
      simp
    rw [complexMlieBracket_congr (hsec hZ) (hsec hW)]
    refine (J.complexMlieBracket_mem_eigenspace_I_iff
      ((hZre x hx).mdifferentiableAt (hU.mem_nhds hx))
      ((hWre x hx).mdifferentiableAt (hU.mem_nhds hx))).2 ?_
    simp [hN]

/-- **Integrability of `T^(0,1)`.** The eigenbundle `T^(0,1) M` of the `-i`-eigenspaces of the
complexified almost complex structure is involutive exactly when the Nijenhuis tensor of `J`
vanishes. -/
theorem isInvolutiveComplexDistribution_eigenspace_neg_I_iff :
    IsInvolutiveComplexDistribution I
        (fun x ↦
          eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I)) ↔
      J.nijenhuis = 0 := by
  -- `T^(0,1) M` for `J` is `T^(1,0) M` for `-J`, which has the same Nijenhuis tensor.
  have h (x : M) :
      eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I) =
        eigenspace (((-J).almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I := by
    rw [neg_almostComplexStructureAt, AlmostComplexStructure.eigenspace_neg_baseChange_I]
  rw [funext h, (-J).isInvolutiveComplexDistribution_eigenspace_I_iff, funext J.nijenhuis_neg]

end TauCeti.SmoothAlmostComplexStructure
