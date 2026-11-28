/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.ExtChartAt.Comp
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Critical points under local diffeomorphisms

Let `π : M → M'` be a `C^n` local diffeomorphism and let `f : M' → ℝ`. Since the differential
of `π` is invertible, the chain rule shows that `x` is a critical point of `f ∘ π` exactly when
`π x` is a critical point of `f`; this holds for any models, with or without boundary.

For nondegeneracy, let `M` and `M'` be boundaryless. In the preferred charts at `x` and `π x`, the
coordinate expression of `f ∘ π` is that of `f` composed with the coordinate expression of `π`,
whose derivative at the chart image of `x` is invertible, and nondegeneracy is invariant under
such a change of coordinates; the two models may differ. The Morse index of a critical point is
invariant under the same change of coordinates, so it is unchanged under composition with `π`. The
models may also differ for the kernel of the critical Hessian at a critical point, which the
second-order chain rule shows the differential of `π` carries onto the kernel for `f`.

This is how Morse data is lifted to a covering space: the critical points of `f ∘ π` are the
preimages of those of `f`, with the same nondegeneracy and indices.

## Main results

* `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff`: `x` is a nondegenerate
  critical point of `f ∘ π` exactly when `π x` is one of `f`, for local diffeomorphisms between
  boundaryless manifolds with possibly different models.
* `IsLocalDiffeomorphAt.manifoldMorseIndex_comp`: at a critical point the Morse index of `f ∘ π`
  at `x` is that of `f` at `π x`, again for possibly different models.
* `IsLocalDiffeomorphAt.ker_criticalHessian_eq_map`: at a critical point the differential of `π`
  carries the kernel of the critical Hessian of `f ∘ π` onto that of `f`.
* `IsLocalDiffeomorph.criticalPoints_comp`: the critical set of `f ∘ π`, for a local
  diffeomorphism `π`, is the preimage under `π` of that of `f`.
* `TauCeti.IsMorse.comp_isLocalDiffeomorph`: a Morse function pulls back to a Morse function along
  a smooth local diffeomorphism, possibly between different models, for instance to every open
  submanifold.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open Filter Function Set Topology TauCeti
open scoped ContDiff Manifold

namespace IsLocalDiffeomorphAt

section Models

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞} {π : M → M'} {x : M}

/-- **Nondegeneracy under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at `x`
with `2 ≤ n`, between boundaryless manifolds possibly modelled on different spaces, then `x` is a
nondegenerate critical point of `f ∘ π` exactly when `π x` is a nondegenerate critical point of
`f`. -/
theorem isManifoldNondegenerateCriticalPoint_comp_iff
    (hπ : IsLocalDiffeomorphAt I I' n π x) (hn : 2 ≤ n) {f : M' → ℝ} :
    IsManifoldNondegenerateCriticalPoint I (f ∘ π) x ↔
      IsManifoldNondegenerateCriticalPoint I' f (π x) := by
  have hn0 : n ≠ 0 := (two_pos.trans_le hn).ne'
  by_cases hf : ContMDiffAt I' 𝓘(ℝ) 2 f (π x)
  swap
  · exact iff_of_false (fun h ↦ hf ((hπ.contMDiffAt_comp_iff hn).1 h.contMDiffAt))
      fun h ↦ hf h.contMDiffAt
  have hy : writtenInExtChartAt I I' x π (extChartAt I x x) = extChartAt I' (π x) (π x) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)
  -- Near the chart image of `x`, the coordinate expression of `f ∘ π` is that of `f` composed
  -- with the coordinate expression of `π`, whose derivative there is the invertible `dπ`.
  have heq := (hπ.mdifferentiableAt hn0).continuousAt.comp_comp_extChartAt_symm_eventuallyEq
    (I := I) (I' := I') f
  rw [isManifoldNondegenerateCriticalPoint_iff, isManifoldNondegenerateCriticalPoint_iff, ← hy,
    ← isNondegenerateCriticalPoint_comp_iff (hy ▸ hf.contDiffAt_comp_extChartAt_symm)
      (hπ.contMDiffAt.of_le hn).contDiffAt_writtenInExtChartAt
      (hπ.isInvertible_fderiv_writtenInExtChartAt hn0)]
  exact heq.isNondegenerateCriticalPoint_iff

/-- **The kernel of the critical Hessian under a local diffeomorphism.** If `π` is a `C^n` local
diffeomorphism at `x` with `2 ≤ n`, and `π x` is a critical point of a function `f` which is `C²`
there, then the differential of `π` at `x` carries the kernel of the critical Hessian of `f ∘ π`
at `x` onto the kernel of the critical Hessian of `f` at `π x`. This is how a degenerate direction,
such as the tangent direction of a Morse–Bott critical submanifold, is read on a covering space. -/
theorem ker_criticalHessian_eq_map
    (hπ : IsLocalDiffeomorphAt I I' n π x) (hn : 2 ≤ n) {f : M' → ℝ}
    (hf : ContMDiffAt I' 𝓘(ℝ) 2 f (π x)) (hcrit : π x ∈ criticalPoints I' f) :
    (criticalHessian I' f (π x)).ker =
      (criticalHessian I (f ∘ π) x).ker.map (mfderiv I I' π x).toLinearMap := by
  have hD := hπ.isInvertible_mfderiv (two_pos.trans_le hn).ne'
  -- The second-order chain rule at the critical point `π x`.
  have hcomp (u w : TangentSpace I x) : criticalHessian I (f ∘ π) x u w =
      criticalHessian I' f (π x) (mfderiv I I' π x u) (mfderiv I I' π x w) :=
    criticalHessian_comp_apply rfl hf (hπ.contMDiffAt.of_le hn) hcrit u w
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hv
    obtain ⟨u, rfl⟩ := hD.surjective v
    refine ⟨u, ContinuousLinearMap.ext fun w ↦ ?_, rfl⟩
    rw [hcomp, hv, zero_apply, zero_apply]
  · rintro ⟨u, hu, rfl⟩
    refine ContinuousLinearMap.ext fun w ↦ ?_
    obtain ⟨w, rfl⟩ := hD.surjective w
    rw [← hcomp, hu, zero_apply, zero_apply]

/-- **The Morse index under a local diffeomorphism.** If `π` is a `C^n` local diffeomorphism at
`x` with `2 ≤ n`, between boundaryless manifolds possibly modelled on different spaces, and `π x` is
a critical point of a function `f` which is `C²` there, then the Morse index of `f ∘ π` at `x` is
the Morse index of `f` at `π x`. -/
theorem manifoldMorseIndex_comp
    (hπ : IsLocalDiffeomorphAt I I' n π x) (hn : 2 ≤ n) {f : M' → ℝ}
    (hf : ContMDiffAt I' 𝓘(ℝ) 2 f (π x)) (hcrit : π x ∈ criticalPoints I' f) :
    manifoldMorseIndex I (f ∘ π) x = manifoldMorseIndex I' f (π x) := by
  have hn0 : n ≠ 0 := (two_pos.trans_le hn).ne'
  have hy : writtenInExtChartAt I I' x π (extChartAt I x x) = extChartAt I' (π x) (π x) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)
  have hcrit' : fderiv ℝ (f ∘ (extChartAt I' (π x)).symm)
      (writtenInExtChartAt I I' x π (extChartAt I x x)) = 0 := by
    rw [hy, ← mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact mem_criticalPoints.1 hcrit
  -- As for nondegeneracy, the coordinate expression of `f ∘ π` is that of `f` composed with the
  -- coordinate expression of `π`, a change of coordinates with invertible derivative.
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, morseIndex_congr_of_eventuallyEq
      ((hπ.mdifferentiableAt hn0).continuousAt.comp_comp_extChartAt_symm_eventuallyEq
        (I := I) (I' := I') f),
    morseIndex_comp (hy ▸ hf.contDiffAt_comp_extChartAt_symm)
      (hπ.contMDiffAt.of_le hn).contDiffAt_writtenInExtChartAt hcrit'
      (hπ.isInvertible_fderiv_writtenInExtChartAt hn0), hy]

end Models

end IsLocalDiffeomorphAt

namespace IsLocalDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}
  {π : M → M'}

/-- **Critical points under a local diffeomorphism.** If `π : M → M'` is a `C^n` local
diffeomorphism with `1 ≤ n`, the critical set of `f ∘ π` is the preimage under `π` of the critical
set of `f`. -/
theorem criticalPoints_comp (hπ : IsLocalDiffeomorph I I' n π) (hn : 1 ≤ n) {f : M' → ℝ} :
    criticalPoints I (f ∘ π) = π ⁻¹' criticalPoints I' f :=
  ext fun x ↦ (hπ x).mem_criticalPoints_comp_iff hn

end IsLocalDiffeomorph

namespace TauCeti

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M']
  {π : M → M'} {f : M' → ℝ}

/-- **Morse functions pull back along local diffeomorphisms.** If `π` is a smooth local
diffeomorphism between boundaryless manifolds, possibly modelled on different spaces, and `f` is a
Morse function, then `f ∘ π` is a Morse function. In particular the restriction of a Morse function
to an open submanifold is a Morse function. -/
theorem IsMorse.comp_isLocalDiffeomorph (hf : IsMorse I' f) (hπ : IsLocalDiffeomorph I I' ∞ π) :
    IsMorse I (f ∘ π) := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints] at hf ⊢
  refine ⟨((contMDiffOn_univ.1 hf.1).comp hπ.contMDiff).contMDiffOn, fun x _ hx ↦ ?_⟩
  have hx' : π x ∈ criticalPoints I' f := ((hπ x).mem_criticalPoints_comp_iff (by simp)).1 hx
  exact ((hπ x).isManifoldNondegenerateCriticalPoint_comp_iff (by simp)).2
    (hf.2 _ (mem_univ _) hx')

end TauCeti
