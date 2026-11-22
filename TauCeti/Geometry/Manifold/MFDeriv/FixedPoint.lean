/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.LinearAlgebra.Matrix.Charpoly.DetSign
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Dynamics.FixedPoints.Topology
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.LinearAlgebra.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.DiscreteSubset

/-!
# Nondegenerate fixed points of maps of manifolds

A fixed point `x` of a map `f : M → M` is **nondegenerate** (`TauCeti.IsNondegenerateFixedPt`)
when `f` is differentiable at `x` and `1` is not an eigenvalue of its differential
`df_x : T_x M → T_x M`: the only tangent vector fixed by `df_x` is zero. In finite dimensions this
says that `df_x - 1` is invertible, or that the graph of `f` meets the diagonal of `M × M`
transversally at `(x, x)`. For the time-one map of a
time-dependent Hamiltonian this is the nondegeneracy of a 1-periodic orbit, the hypothesis under
which the orbits generate the Hamiltonian Floer complex.

When `M` is modelled on a finite-dimensional space over a complete field, a nondegenerate fixed
point is isolated among the fixed points
(`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`): in a chart at `x` the coordinate
expression `g` of `f` has `g - id` with injective derivative at `x`, so `g z ≠ z` for `z ≠ x` close
to `x`, because an injective linear map of a finite-dimensional space is bounded below. Without
finite dimensionality, injectivity of `df_x - 1` does not imply isolation. The argument is carried
out within the range of the model with corners, so it also applies at boundary points.
Consequently a compact set of nondegenerate fixed points is discrete, hence finite
(`IsCompact.finite_of_isNondegenerateFixedPt`). In particular a continuous self-map of such a
compact manifold all of whose fixed points are nondegenerate has only finitely many fixed points
(`TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`), since its fixed-point set is closed,
hence compact.

Nondegeneracy is invariant under conjugation by a diffeomorphism
(`Diffeomorph.isNondegenerateFixedPt_iff_of_semiconj`): if `Φ ∘ f = g ∘ Φ`, the differential of
`Φ` at `x` identifies the vectors fixed by `df_x` with those fixed by `dg_{Φ x}`.

At a fixed point the differential of `f^[n]` is `(df_x) ^ n`, so `x` is a nondegenerate fixed point
of `f^[n]` exactly when `(df_x) ^ n` fixes no nonzero vector. For a periodic point of period `k`,
the differential of `f^[k]` is the return map of its orbit, and its `m`-th power is the return map
of the `m`-fold cover. A map is nondegenerate up to period `N`
(`TauCeti.IsNondegenerateUpToPeriod`) when every periodic orbit of period at most `N` is
nondegenerate. On a compact manifold such a map has finitely many periodic points of each period
at most `N`. A vector with `D v = -v` is fixed by `D ^ 2`, so nondegeneracy up to period `2 * N`
excludes both eigenvalues `1` and `-1` from the return maps of all covers of period at most `N`.

The differential `df_x` at a fixed point `x` maps `T_x M` to `T_{f x} M`; transporting its target
along `f x = x` makes it an endomorphism of `T_x M`, the **fixed-point derivative**
`TauCeti.fixedPointDerivative`. Over `ℝ`, on a manifold without boundary, the sign of
`det (1 - df_x)` is the local contribution of a nondegenerate fixed point to the Lefschetz
fixed-point formula; at a boundary fixed point this identification can fail. When `f` is
differentiable at `x`, the fixed-point derivative of `f^[n]` at `x` is the `n`-th power of that of
`f` (`TauCeti.fixedPointDerivative_iterate`), and in finite dimensions `x` is a nondegenerate fixed
point exactly when `det (1 - df_x) ≠ 0` (`TauCeti.isNondegenerateFixedPt_iff_det_id_sub_ne_zero`).
Without differentiability `mfderiv` is zero, so then `det (1 - df_x) = 1` although `x` is not
nondegenerate.
Read in the extended chart at any point `x'` whose chart contains `x`, the derivative of `f` at the
fixed point is `df_x` conjugated by the derivative of the transition map
(`ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm`), so `det (1 - df_x)` can be
computed in any chart, also on manifolds with boundary or corners
(`TauCeti.det_id_sub_fderivWithin_extChartAt_comp_extChartAt_symm`).

The **Lefschetz determinant** `TauCeti.fixedPointDet I f x = det (1 - df_x)` names this scalar for
every point `x`, reading `df_x` as an endomorphism of the model space; over `ℝ` the **Lefschetz
sign** `TauCeti.fixedPointSign I f x` is `1` when it is positive and `-1` otherwise. These are the
local terms of the Lefschetz fixed-point formula `∑_{f x = x} sgn det (1 - df_x) = L(f)` for a map
of a compact manifold all of whose fixed points are nondegenerate, and, through the iterates
`f^[k]`, of the dynamical zeta function. Both are unchanged when `f` is conjugated by a
diffeomorphism, even only near the fixed point (`Diffeomorph.fixedPointDet_eq_of_semiconj`). At a
fixed point with differential `D`, the sign of `f^[k]` is `(-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`, where
`i₊` and `i₋` count the real eigenvalues of `D` in `(1, ∞)` and in `(-∞, -1)`
(`TauCeti.fixedPointSign_iterate`).

## Main definitions

* `TauCeti.IsNondegenerateFixedPt I f x`: `x` is a fixed point of `f`, `f` is differentiable at
  `x`, and `df_x` fixes no nonzero tangent vector.
* `TauCeti.IsNondegenerateUpToPeriod I f N`: every periodic point of positive period `k ≤ N` is a
  nondegenerate fixed point of `f^[k]`.
* `TauCeti.fixedPointDerivative I f x`: the differential of `f` at a fixed point `x`, as an
  endomorphism of `T_x M`.
* `TauCeti.fixedPointDet I f x`: the Lefschetz determinant `det (1 - df_x)`.
* `TauCeti.fixedPointSign I f x`: over `ℝ`, the Lefschetz sign, `1` if `det (1 - df_x) > 0` and
  `-1` otherwise.

## Main results

* `Diffeomorph.isNondegenerateFixedPt_iff_of_semiconj`: nondegeneracy is invariant under
  conjugation by a diffeomorphism.
* `TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`: on a manifold modelled on a
  finite-dimensional space over a complete field, nondegenerate fixed points are isolated.
* `IsCompact.finite_of_isNondegenerateFixedPt`: on a manifold modelled on a finite-dimensional
  space over a complete field, a compact set of nondegenerate fixed points is finite.
* `TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`: on a compact manifold modelled on a
  finite-dimensional space over a complete field, a continuous map whose fixed points are all
  nondegenerate has finitely many fixed points.
* `TauCeti.isNondegenerateFixedPt_iterate_iff`: at a fixed point with differential `D`, the point is
  a nondegenerate fixed point of `f^[n]` exactly when `D ^ n` fixes no nonzero vector.
* `TauCeti.IsNondegenerateFixedPt.eq_zero_of_pow_apply_eq_smul`: at a nondegenerate fixed point of
  `f^[m * j]`, no `ε` with `ε ^ j = 1` is an eigenvalue of `D ^ m`.
* `TauCeti.IsNondegenerateUpToPeriod.finite_ptsOfPeriod`,
  `TauCeti.IsNondegenerateUpToPeriod.finite_setOf_isPeriodicPt`: finitely many periodic points of
  period at most `N` on a compact manifold.
* `TauCeti.IsNondegenerateUpToPeriod.eq_zero_of_pow_apply_eq_smul`,
  `TauCeti.IsNondegenerateUpToPeriod.det_smul_one_sub_pow_ne_zero`: nondegeneracy up to period
  `N` excludes every `ε` with `ε ^ j = 1` as an eigenvalue of the return map of the `m`-fold cover
  of an orbit of period `k` when `k * m * j ≤ N`. For `j = 2`, nondegeneracy up to period `2 * N`
  excludes the eigenvalues `±1` of the return maps of all covers of period at most `N`.
* `TauCeti.fixedPointDerivative_iterate`: at a fixed point where `f` is differentiable, the
  fixed-point derivative of `f^[n]` is the `n`-th power of that of `f`.
* `TauCeti.det_id_sub_fixedPointDerivative_apply_iterate`: for a periodic point `x` of period `n`
  of a map differentiable along its orbit, `det (1 - d(f^[n]))` is the same at every point
  `f^[j] x` of the orbit.
* `HasFDerivAt.isNondegenerateFixedPt_iff_injective_id_sub`: on a normed space, a fixed point at
  which `f` has derivative `D` is nondegenerate exactly when `1 - D` is injective.
* `HasFDerivAt.isNondegenerateFixedPt_iff_isInvertible_id_sub`: in finite dimensions, exactly when
  `1 - D` is invertible.
* `TauCeti.IsNondegenerateFixedPt.isInvertible_id_sub_fderiv`: so `1 - Df(x)` is invertible at a
  nondegenerate fixed point of a map of a finite-dimensional normed space.
* `TauCeti.IsNondegenerateFixedPt.det_one_sub_fderiv_ne_zero`: on a finite-dimensional normed
  space, `det (1 - df_x) ≠ 0` at a nondegenerate fixed point `x`.
* `TauCeti.isNondegenerateFixedPt_iff_det_id_sub_ne_zero`: in finite dimensions, a fixed point at
  which `f` is differentiable is nondegenerate exactly when `det (1 - df_x) ≠ 0`.
* `TauCeti.det_id_sub_fderivWithin_extChartAt_comp_extChartAt_symm`: `det (1 - df_x)` at a fixed
  point can be computed in any chart.
* `TauCeti.isNondegenerateFixedPt_iff_injective_sub_id_of_hasFDerivWithinAt`: so can
  nondegeneracy, as injectivity of `B - 1` for the derivative `B` of the coordinate expression.
* `TauCeti.fixedPointDet_ne_zero_iff`: in finite dimensions, a fixed point at which `f` is
  differentiable is nondegenerate exactly when its Lefschetz determinant is nonzero.
* `Diffeomorph.fixedPointDet_eq_of_semiconj`, `Diffeomorph.fixedPointSign_eq_of_semiconj`: the
  Lefschetz determinant and sign are invariant under local conjugation by a diffeomorphism.
* `TauCeti.fixedPointSign_eq_sign`: where `det (1 - df_x) ≠ 0`, the Lefschetz sign is its sign.
* `TauCeti.fixedPointSign_iterate`, `TauCeti.IsNondegenerateFixedPt.fixedPointSign_eq`: the
  Lefschetz signs of the iterates of a map at a fixed point, from the real eigenvalues of its
  differential.

## References

* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 3, §4
  (Lefschetz fixed points: nondegeneracy, isolation and finiteness on compact manifolds, and the
  local Lefschetz number, the sign of the determinant of `df_x - I`).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1 (nondegenerate fixed points of Hamiltonian symplectomorphisms).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {f : M → M} {x : M}

variable (I) in
/-- A **nondegenerate fixed point** of `f : M → M` is a fixed point `x` at which `f` is
differentiable and `1` is not an eigenvalue of the differential: `df_x v = v` only for `v = 0`.
In finite dimensions this says that `df_x - 1` is invertible. -/
def IsNondegenerateFixedPt (f : M → M) (x : M) : Prop :=
  IsFixedPt f x ∧ MDifferentiableAt I I f x ∧ ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0

/-- The defining characterization of a nondegenerate fixed point. -/
theorem isNondegenerateFixedPt_iff :
    IsNondegenerateFixedPt I f x ↔
      IsFixedPt f x ∧ MDifferentiableAt I I f x ∧
        ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0 :=
  Iff.rfl

namespace IsNondegenerateFixedPt

/-- A nondegenerate fixed point is a fixed point. -/
theorem isFixedPt (h : IsNondegenerateFixedPt I f x) : IsFixedPt f x :=
  h.1

/-- A map is differentiable at each of its nondegenerate fixed points. -/
theorem mdifferentiableAt (h : IsNondegenerateFixedPt I f x) : MDifferentiableAt I I f x :=
  h.2.1

/-- At a nondegenerate fixed point, the only tangent vector fixed by the differential is zero. -/
theorem eq_zero_of_mfderiv_apply_eq (h : IsNondegenerateFixedPt I f x) {v : TangentSpace I x}
    (hv : mfderiv I I f x v = v) : v = 0 :=
  h.2.2 v hv

/-- Being a nondegenerate fixed point only depends on the germ of the map at the point. -/
theorem congr_of_eventuallyEq {g : M → M} (h : IsNondegenerateFixedPt I f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsNondegenerateFixedPt I g x :=
  ⟨hfg.eq_of_nhds.trans h.isFixedPt, h.mdifferentiableAt.congr_of_eventuallyEq hfg,
    fun v hv ↦ h.eq_zero_of_mfderiv_apply_eq <| by
      -- `tangentSpaceCast` between the tangent spaces at `g x` and `f x` is the identity of `E`.
      rw [hfg.mfderiv_eq] at hv
      exact hv⟩

end IsNondegenerateFixedPt

/-- **Nondegeneracy is invariant under conjugation by a diffeomorphism.** If a diffeomorphism `Φ`
intertwines `f` and `g`, `Φ ∘ f = g ∘ Φ`, then `Φ x` is a nondegenerate fixed point of `g` exactly
when `x` is a nondegenerate fixed point of `f`: the differential of `Φ` at `x` carries the vectors
fixed by `df_x` bijectively to those fixed by `dg_{Φ x}`. -/
theorem _root_.Diffeomorph.isNondegenerateFixedPt_iff_of_semiconj {F H' N : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
    [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {g : N → N}
    (h : Semiconj Φ f g) :
    IsNondegenerateFixedPt J g (Φ x) ↔ IsNondegenerateFixedPt I f x := by
  have hcomp : (Φ : M → N) ∘ f = g ∘ Φ := funext h
  have hfix : IsFixedPt g (Φ x) ↔ IsFixedPt f x := by
    rw [IsFixedPt, IsFixedPt, ← h x]
    exact Φ.injective.eq_iff
  have hdiff : MDifferentiableAt J J g (Φ x) ↔ MDifferentiableAt I I f x := by
    rw [← Φ.mdifferentiableAt_comp_diffeomorph_iff hn, ← hcomp, Φ.mdifferentiableAt_comp_iff hn]
  -- The differentials are maps between the model spaces `E` and `F`, the tangent spaces of `M`
  -- and `N` at every point; stating them so lets `f x = x` be substituted without transport.
  -- Differentiating `Φ ∘ f = g ∘ Φ` at `x` gives `dg ∘ dΦ = dΦ ∘ df`.
  have hder : ((mfderiv J J g (Φ x)).comp (mfderiv I J Φ x) : E →L[𝕜] F) =
      (mfderiv I J Φ (f x)).comp (mfderiv I I f x) := by
    refine (Φ.mfderiv_comp_diffeomorph hn g x).symm.trans ?_
    rw [← hcomp]
    exact Φ.mfderiv_diffeomorph_comp hn f x
  have hl (w : E) : (mfderiv J I Φ.symm (Φ x) (mfderiv I J Φ x w) : E) = w :=
    Φ.mfderiv_symm_apply_mfderiv_apply hn x w
  have hr (v : F) : (mfderiv I J Φ x (mfderiv J I Φ.symm (Φ x) v) : F) = v :=
    Φ.mfderiv_apply_mfderiv_symm_apply hn x v
  have hinj : Injective (mfderiv I J Φ x : E → F) := fun a b hab ↦ by rw [← hl a, hab, hl b]
  -- At a fixed point of `f`, `dg (dΦ w) = dΦ (df w)` for every `w`.
  have hfg (hfx : f x = x) (w : E) :
      (mfderiv J J g (Φ x) (mfderiv I J Φ x w) : F) = mfderiv I J Φ x (mfderiv I I f x w) := by
    have hΦ : (mfderiv I J Φ (f x) : E →L[𝕜] F) = mfderiv I J Φ x := by rw [hfx]
    rw [hΦ] at hder
    exact congrArg (fun A : E →L[𝕜] F ↦ A w) hder
  constructor
  · rintro ⟨hgx, hgd, hg⟩
    have hfx : f x = x := (hfix.1 hgx).eq
    refine ⟨hfix.1 hgx, hdiff.1 hgd, fun w hw ↦ ?_⟩
    have hw' : (mfderiv I I f x w : E) = w := hw
    exact hinj ((hg _ ((hfg hfx w).trans (congrArg _ hw'))).trans (map_zero _).symm)
  · rintro ⟨hfx, hfd, hf⟩
    refine ⟨hfix.2 hfx, hdiff.2 hfd, fun v hv ↦ ?_⟩
    -- Every tangent vector at `Φ x` is `dΦ w` for a tangent vector `w` at `x`.
    obtain ⟨w, rfl⟩ : ∃ w : E, (mfderiv I J Φ x w : F) = v := ⟨_, hr v⟩
    have hw : (mfderiv I I f x w : E) = w := hinj ((hfg hfx w).symm.trans hv)
    exact (congrArg (mfderiv I J Φ x) (hf w hw)).trans (map_zero _)

namespace IsNondegenerateFixedPt

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **Nondegenerate fixed points are isolated.** On a manifold modelled on a finite-dimensional
space over a complete field, if `x` is a nondegenerate fixed point of `f`, then no point `y ≠ x`
close to `x` is fixed by `f`. The manifold may have boundary or corners. -/
theorem eventually_not_isFixedPt (h : IsNondegenerateFixedPt I f x) :
    ∀ᶠ y in 𝓝[≠] x, ¬IsFixedPt f y := by
  have hf := h.mdifferentiableAt
  set φ := extChartAt I x
  have hfx : f x = x := h.isFixedPt
  have hφ : extChartAt I (f x) = φ := by rw [hfx]
  -- In the chart at `x`, the coordinate expression `g` of `f` has derivative `D = df_x` within
  -- `range I`, so `z ↦ g z - z` has derivative `D - 1`, which is injective.
  set D : E →L[𝕜] E := mfderiv I I f x
  have hg : HasFDerivWithinAt (fun z ↦ φ (f (φ.symm z)) - z) (D - ContinuousLinearMap.id 𝕜 E)
      (range I) (φ x) := by
    have h2 := hf.hasMFDerivAt.2
    simp only [writtenInExtChartAt, hφ] at h2
    exact h2.sub (hasFDerivWithinAt_id _ _)
  have hinj : Injective (D - ContinuousLinearMap.id 𝕜 E) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h.eq_zero_of_mfderiv_apply_eq (sub_eq_zero.1 hv)
  obtain ⟨K, -, hK⟩ :=
    (D - ContinuousLinearMap.id 𝕜 E).toLinearMap.injective_iff_antilipschitz.1 hinj
  have hne := hg.eventually_ne (c := 0) ⟨K, hK⟩
  -- The chart sends points `y ≠ x` near `x` to points `≠ φ x` of `range I`.
  have hsource : (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)
  have htends : Tendsto φ (𝓝[≠] x) (𝓝[range I \ {φ x}] (φ x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt x).tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hsource, self_mem_nhdsWithin] with y hy hyx
    exact ⟨extChartAt_target_subset_range x ((extChartAt I x).map_source hy),
      fun hφy ↦ hyx ((extChartAt I x).injOn hy (mem_extChartAt_source x) hφy)⟩
  have hfsource : f ⁻¹' (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (hf.continuousAt.preimage_mem_nhds
      (by rw [hfx]; exact extChartAt_source_mem_nhds x))
  filter_upwards [htends.eventually hne, hsource, hfsource] with y hy hys _ hfix
  apply hy
  rw [(extChartAt I x).left_inv hys, hfix.eq, sub_self]

end IsNondegenerateFixedPt

/-- **Finiteness of compact sets of nondegenerate fixed points.** On a manifold modelled on a
finite-dimensional space, a compact set all of whose points are nondegenerate fixed points of `f`
is finite, since each of its points is isolated among the fixed points of `f`. -/
theorem _root_.IsCompact.finite_of_isNondegenerateFixedPt [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {s : Set M} (hs : IsCompact s)
    (h : ∀ x ∈ s, IsNondegenerateFixedPt I f x) : s.Finite :=
  hs.finite <| isDiscrete_iff_nhdsNE.2 fun x hx ↦ inf_principal_eq_bot.2 <|
    (h x hx).eventually_not_isFixedPt.mono fun y hy hys ↦ hy (h y hys).isFixedPt

/-- **Finiteness of nondegenerate fixed points.** A continuous self-map of a compact manifold,
modelled on a finite-dimensional space, all of whose fixed points are nondegenerate has only
finitely many fixed points. -/
theorem finite_fixedPoints_of_isNondegenerateFixedPt [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [CompactSpace M] [T2Space M] (hf : Continuous f)
    (h : ∀ x ∈ fixedPoints f, IsNondegenerateFixedPt I f x) : (fixedPoints f).Finite :=
  (isClosed_fixedPoints hf).isCompact.finite_of_isNondegenerateFixedPt h

/-! ### Iterates

At a fixed point `x` of `f` the chain rule makes the differential of the iterate `f^[n]` the
`n`-th power of `df_x` (`HasMFDerivAt.iterate`). For a periodic point of period `k`, applied to
`f^[k]`, this says that the return map of the `m`-fold cover of the periodic orbit is the `m`-th
power of the return map of the orbit. -/

/-- At a fixed point `x` of `f` with differential `D`, the point `x` is a nondegenerate fixed point
of `f^[n]` exactly when `D ^ n` fixes no nonzero tangent vector. -/
theorem isNondegenerateFixedPt_iterate_iff {D : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hD : HasMFDerivAt I I f x D) (hx : IsFixedPt f x) {n : ℕ} :
    IsNondegenerateFixedPt I f^[n] x ↔ ∀ v : TangentSpace I x, (D ^ n) v = v → v = 0 := by
  have hDn := hD.iterate hx.eq n
  rw [isNondegenerateFixedPt_iff, hDn.mfderiv]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx.iterate n, hDn.mdifferentiableAt, h⟩⟩

namespace IsNondegenerateFixedPt

/-- **Roots of unity are not eigenvalues at a nondegenerate fixed point of an iterate.** Let `f`
fix `x` with differential `D`. If `x` is a nondegenerate fixed point of `f^[m * j]` and
`ε ^ j = 1`, then `(D ^ m) v = ε • v` only for `v = 0`. For `j = 2` this excludes both eigenvalues
`1` and `-1` of `D ^ m`. -/
theorem eq_zero_of_pow_apply_eq_smul {D : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hD : HasMFDerivAt I I f x D) (hx : IsFixedPt f x) {m j : ℕ}
    (h : IsNondegenerateFixedPt I f^[m * j] x) {ε : 𝕜} (hε : ε ^ j = 1) {v : TangentSpace I x}
    (hv : (D ^ m) v = ε • v) : v = 0 := by
  refine (isNondegenerateFixedPt_iterate_iff hD hx).1 h v ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · exact map_zero _
  have hev : Module.End.HasEigenvector (↑(D ^ m) : TangentSpace I x →ₗ[𝕜] TangentSpace I x) ε v :=
    ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hj := hev.pow_apply j
  rw [← ContinuousLinearMap.toLinearMap_pow, hε, one_smul] at hj
  rwa [pow_mul]

/-- A fixed point of `f` at which `f` is differentiable is nondegenerate as soon as it is a
nondegenerate fixed point of some iterate `f^[n]`. -/
theorem of_iterate (hf : MDifferentiableAt I I f x) (hx : IsFixedPt f x) {n : ℕ}
    (h : IsNondegenerateFixedPt I f^[n] x) : IsNondegenerateFixedPt I f x := by
  -- Name the differential with the endomorphism type that `HasMFDerivAt.iterate` expects.
  let D : TangentSpace I x →L[𝕜] TangentSpace I x := mfderiv I I f x
  have hD : HasMFDerivAt I I f x D := hf.hasMFDerivAt
  rw [← one_mul n] at h
  refine ⟨hx, hf, fun v hv ↦ h.eq_zero_of_pow_apply_eq_smul hD hx (one_pow n) ?_⟩
  rwa [pow_one, one_smul]

end IsNondegenerateFixedPt

/-! ### Nondegeneracy up to a period

A map is nondegenerate up to period `N` when every periodic orbit of period at most `N` is
nondegenerate. On a compact manifold such a map has finitely many periodic points of each of these
periods. Since the return map of the `m`-fold cover of an orbit of period `k` is the `m`-th power of
the return map of the orbit, nondegeneracy up to period `2 * N` also excludes the eigenvalue `-1`
from the return maps of all covers of period at most `N`. In the count of pseudoholomorphic tori in
a symplectic suspension, these two eigenvalues govern the normal operators twisted by the trivial
and by the nontrivial sign character along the orbit. -/

variable (I) in
/-- A map `f : M → M` is **nondegenerate up to period `N`** when every periodic point of `f` with a
positive period `k ≤ N` is a nondegenerate fixed point of `f^[k]`: the return map of no periodic
orbit of period at most `N` has the eigenvalue `1`. A map that is nondegenerate up to every period
is called strongly nondegenerate. -/
def IsNondegenerateUpToPeriod (f : M → M) (N : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄, 0 < k → k ≤ N → ∀ ⦃x : M⦄, IsPeriodicPt f k x → IsNondegenerateFixedPt I f^[k] x

/-- The defining characterization of nondegeneracy up to a period. -/
theorem isNondegenerateUpToPeriod_iff {N : ℕ} :
    IsNondegenerateUpToPeriod I f N ↔
      ∀ ⦃k : ℕ⦄, 0 < k → k ≤ N → ∀ ⦃x : M⦄, IsPeriodicPt f k x →
        IsNondegenerateFixedPt I f^[k] x :=
  Iff.rfl

/-- Every map is nondegenerate up to period `0`. -/
@[simp]
theorem isNondegenerateUpToPeriod_zero : IsNondegenerateUpToPeriod I f 0 :=
  fun _ hk hk0 ↦ absurd hk (by omega)

namespace IsNondegenerateUpToPeriod

variable {N : ℕ}

/-- Nondegeneracy up to period `N` implies nondegeneracy up to every smaller period. -/
theorem mono (h : IsNondegenerateUpToPeriod I f N) {N' : ℕ} (hN : N' ≤ N) :
    IsNondegenerateUpToPeriod I f N' :=
  fun _ hk hkN _ hx ↦ h hk (hkN.trans hN) hx

/-- A periodic point of positive period `k ≤ N` of a map nondegenerate up to period `N` is a
nondegenerate fixed point of `f^[k]`. -/
theorem isNondegenerateFixedPt (h : IsNondegenerateUpToPeriod I f N) {k : ℕ} (hk : 0 < k)
    (hkN : k ≤ N) (hx : IsPeriodicPt f k x) : IsNondegenerateFixedPt I f^[k] x :=
  h hk hkN hx

/-- **Covers of nondegenerate orbits and roots of unity.** Let `f` be nondegenerate up to period
`N`, let `x` be a periodic point of period `k > 0`, and let `D` be the differential of `f^[k]` at
`x`, the return map of its orbit. If `k * m * j ≤ N` with `m, j > 0` and `ε ^ j = 1`, then
`(D ^ m) v = ε • v` forces `v = 0`: the return map `D ^ m` of the `m`-fold cover does not have the
eigenvalue `ε`. For `j = 2`, nondegeneracy up to period `2 * N` excludes both eigenvalues `1` and
`-1` of the return maps of all covers of period `k * m ≤ N`. -/
theorem eq_zero_of_pow_apply_eq_smul (h : IsNondegenerateUpToPeriod I f N) {k m j : ℕ}
    (hk : 0 < k) (hm : 0 < m) (hj : 0 < j) (hkmj : k * m * j ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D) {ε : 𝕜}
    (hε : ε ^ j = 1) {v : TangentSpace I x} (hv : (D ^ m) v = ε • v) : v = 0 := by
  have hnd := h (by positivity) (by rwa [← mul_assoc]) (hx.mul_const (m * j))
  rw [iterate_mul] at hnd
  exact hnd.eq_zero_of_pow_apply_eq_smul hD hx.isFixedPt hε hv

/-- **Covers of nondegenerate orbits.** Let `f` be nondegenerate up to period `N`, let `x` be a
periodic point of period `k > 0`, and let `D` be the differential of `f^[k]` at `x`, the return map
of its orbit. If `k * m ≤ N` with `m > 0`, then the return map `D ^ m` of the `m`-fold cover fixes
no nonzero tangent vector. -/
theorem eq_zero_of_pow_apply_eq (h : IsNondegenerateUpToPeriod I f N) {k m : ℕ} (hk : 0 < k)
    (hm : 0 < m) (hkm : k * m ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D)
    {v : TangentSpace I x} (hv : (D ^ m) v = v) : v = 0 :=
  h.eq_zero_of_pow_apply_eq_smul hk hm one_pos (by rwa [mul_one]) hx hD (one_pow 1)
    (by rwa [one_smul])

/-- **Determinant form of `TauCeti.IsNondegenerateUpToPeriod.eq_zero_of_pow_apply_eq_smul`.** If
`f` is nondegenerate up to period `N`, `x` has period `k > 0` and `D` is the
differential of `f^[k]` at `x`, then `det (ε - D ^ m) ≠ 0` for `ε ^ j = 1`, `m, j > 0` and
`k * m * j ≤ N`. For `j = 2`, nondegeneracy up to period `2 * N` gives `det (±1 - D ^ m) ≠ 0` for
all covers of period `k * m ≤ N`. In infinite dimension `LinearMap.det` is `1`, so the statement
holds by convention. -/
theorem det_smul_one_sub_pow_ne_zero
    (h : IsNondegenerateUpToPeriod I f N) {k m j : ℕ} (hk : 0 < k) (hm : 0 < m) (hj : 0 < j)
    (hkmj : k * m * j ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D) {ε : 𝕜}
    (hε : ε ^ j = 1) :
    LinearMap.det
      ((ε • 1 - D ^ m : TangentSpace I x →L[𝕜] TangentSpace I x) :
        TangentSpace I x →ₗ[𝕜] TangentSpace I x) ≠ 0 := by
  by_cases hfin : Module.Finite 𝕜 (TangentSpace I x)
  swap
  · rw [LinearMap.det_eq_one_of_not_module_finite hfin]
    exact one_ne_zero
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, eq_bot_iff]
  intro v hv
  refine (Submodule.mem_bot 𝕜).2 (h.eq_zero_of_pow_apply_eq_smul hk hm hj hkmj hx hD hε ?_)
  simpa [sub_eq_zero, eq_comm (b := ε • v), ← ContinuousLinearMap.toLinearMap_pow] using hv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [CompactSpace M] [T2Space M]

/-- **Finiteness of nondegenerate periodic points.** On a compact manifold modelled on a
finite-dimensional space over a complete field, a continuous map nondegenerate up to period `N`
has only finitely many periodic points of each positive period `k ≤ N`. -/
theorem finite_ptsOfPeriod (h : IsNondegenerateUpToPeriod I f N) (hf : Continuous f) {k : ℕ}
    (hk : 0 < k) (hkN : k ≤ N) : (ptsOfPeriod f k).Finite :=
  -- `ptsOfPeriod f k` is by definition the fixed-point set of `f^[k]`.
  finite_fixedPoints_of_isNondegenerateFixedPt (hf.iterate k) fun _ hx ↦ h hk hkN hx

/-- On a compact manifold modelled on a finite-dimensional space over a complete field, a
continuous map nondegenerate up to period `N` has only finitely many points of some positive
period at most `N`. -/
theorem finite_setOf_isPeriodicPt (h : IsNondegenerateUpToPeriod I f N) (hf : Continuous f) :
    {x | ∃ k, 0 < k ∧ k ≤ N ∧ IsPeriodicPt f k x}.Finite := by
  refine ((Set.finite_Icc 1 N).biUnion fun k hk ↦ h.finite_ptsOfPeriod hf hk.1 hk.2).subset ?_
  rintro x ⟨k, hk, hkN, hx⟩
  exact Set.mem_biUnion ⟨hk, hkN⟩ hx

end IsNondegenerateUpToPeriod

/-! ### The fixed-point derivative

At a fixed point `x` of `f` the differential `df_x : T_x M → T_{f x} M` becomes an endomorphism of
`T_x M` once its target is transported along `f x = x`. In a chart at another point `x'`, the
derivative of the coordinate expression of `f` at the fixed point is this endomorphism conjugated by
the derivative of the transition map, so `det (1 - df_x)`, and over `ℝ` its sign, is intrinsic. -/

variable (I) in
/-- The **fixed-point derivative** of `f : M → M` at a fixed point `x`: the differential
`df_x : T_x M → T_{f x} M`, viewed as an endomorphism of `T_x M` by transporting its target along
`f x = x`. Over `ℝ`, at a nondegenerate fixed point in the interior of the manifold, the sign of
`det (1 - df_x)` is the contribution of `x` to the Lefschetz fixed-point formula. -/
noncomputable def fixedPointDerivative (f : M → M) (x : {x // f x = x}) :
    TangentSpace I x.val →ₗ[𝕜] TangentSpace I x.val :=
  (x.property ▸ mfderiv I I f x.val).toLinearMap

/-- The fixed-point derivative of `f` at `x` acts as the differential `df_x`. -/
@[simp]
theorem fixedPointDerivative_apply (x : {x // f x = x}) (v : TangentSpace I x.val) :
    fixedPointDerivative I f x v = mfderiv I I f x.val v := by
  obtain ⟨x, hx⟩ := x
  -- Transport along any equation `y = x` acts trivially on the underlying tangent vectors.
  have key : ∀ {y : M} (h : y = x) (L : TangentSpace I x →L[𝕜] TangentSpace I y)
      (v : TangentSpace I x), (h ▸ L) v = L v := by
    rintro y rfl L v
    rfl
  exact key hx _ v

/-- If `f` has differential `D` at a fixed point `x`, then its fixed-point derivative at `x` is
`D`. -/
theorem _root_.HasMFDerivAt.fixedPointDerivative_eq {x : {x // f x = x}}
    {D : TangentSpace I x.val →L[𝕜] TangentSpace I x.val} (hD : HasMFDerivAt I I f x.val D) :
    fixedPointDerivative I f x = D :=
  LinearMap.ext fun v ↦ by rw [fixedPointDerivative_apply, hD.mfderiv]; rfl

/-- On a normed space, with its trivial chart, the fixed-point derivative acts as the Fréchet
derivative. -/
theorem fixedPointDerivative_modelSpace_apply (f : E → E) (x : {x // f x = x})
    (v : TangentSpace 𝓘(𝕜, E) x.val) :
    fixedPointDerivative 𝓘(𝕜, E) f x v = fderiv 𝕜 f x.val v := by
  rw [fixedPointDerivative_apply, mfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity of the model space.
  rfl

/-- On a normed space, with its trivial chart, `det (1 - df_x)` at a fixed point is computed from
the Fréchet derivative. -/
theorem det_id_sub_fixedPointDerivative_modelSpace (f : E → E) (x : {x // f x = x}) :
    LinearMap.det (LinearMap.id - fixedPointDerivative 𝓘(𝕜, E) f x) =
      LinearMap.det (LinearMap.id - (fderiv 𝕜 f x.val : E →ₗ[𝕜] E)) := by
  congr 2
  exact LinearMap.ext (fixedPointDerivative_modelSpace_apply f x)

/-- **Nondegeneracy on a normed space.** If `f` has Fréchet derivative `D` at a fixed point `x`
of a normed space, with its trivial chart, then `x` is nondegenerate exactly when `1 - D` is
injective. -/
theorem _root_.HasFDerivAt.isNondegenerateFixedPt_iff_injective_id_sub {f : E → E}
    {D : E →L[𝕜] E} {x : E} (hD : HasFDerivAt f D x) (hx : IsFixedPt f x) :
    IsNondegenerateFixedPt 𝓘(𝕜, E) f x ↔ Injective (ContinuousLinearMap.id 𝕜 E - D) := by
  rw [TauCeti.isNondegenerateFixedPt_iff, hD.hasMFDerivAt.mfderiv, injective_iff_map_eq_zero]
  simp only [hx, hD.hasMFDerivAt.mdifferentiableAt, true_and, sub_apply,
    ContinuousLinearMap.id_apply]
  -- The tangent space `TangentSpace 𝓘(𝕜, E) x` is `E` by definition.
  exact forall_congr' fun v ↦ imp_congr_left
    ⟨fun h ↦ sub_eq_zero.2 h.symm, fun h ↦ (sub_eq_zero.1 h).symm⟩

/-- **Nondegeneracy on a finite-dimensional space.** If `f` has Fréchet derivative `D` at a fixed
point `x` of a finite-dimensional normed space over a complete field, with its trivial chart, then
`x` is nondegenerate exactly when `1 - D` is invertible. -/
theorem _root_.HasFDerivAt.isNondegenerateFixedPt_iff_isInvertible_id_sub [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {f : E → E} {D : E →L[𝕜] E} {x : E} (hD : HasFDerivAt f D x)
    (hx : IsFixedPt f x) :
    IsNondegenerateFixedPt 𝓘(𝕜, E) f x ↔ (ContinuousLinearMap.id 𝕜 E - D).IsInvertible := by
  rw [hD.isNondegenerateFixedPt_iff_injective_id_sub hx]
  refine ⟨fun h ↦ ⟨(LinearEquiv.ofInjectiveEndo _ h).toContinuousLinearEquiv, by ext; simp⟩, ?_⟩
  rintro ⟨e, he⟩
  exact he ▸ e.injective

/-- At a nondegenerate fixed point `x` of a map `f` of a finite-dimensional normed space over a
complete field, with its trivial chart, the operator `1 - Df(x)` is invertible. -/
theorem IsNondegenerateFixedPt.isInvertible_id_sub_fderiv [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {f : E → E} {x : E} (h : IsNondegenerateFixedPt 𝓘(𝕜, E) f x) :
    (ContinuousLinearMap.id 𝕜 E - fderiv 𝕜 f x).IsInvertible :=
  ((mdifferentiableAt_iff_differentiableAt.1 h.mdifferentiableAt).hasFDerivAt
    |>.isNondegenerateFixedPt_iff_isInvertible_id_sub h.isFixedPt).1 h

/-- **The fixed-point derivative of an iterate.** If `f` is differentiable at a fixed point `x`,
the fixed-point derivative of `f^[n]` at `x` is the `n`-th power of that of `f`. -/
theorem fixedPointDerivative_iterate (x : {x // f x = x}) (hf : MDifferentiableAt I I f x.val)
    (n : ℕ) :
    fixedPointDerivative I f^[n] ⟨x.val, IsFixedPt.iterate x.property n⟩ =
      fixedPointDerivative I f x ^ n := by
  let D : TangentSpace I x.val →L[𝕜] TangentSpace I x.val := mfderiv I I f x.val
  have hD : HasMFDerivAt I I f x.val D := hf.hasMFDerivAt
  rw [(hD.iterate x.property n).fixedPointDerivative_eq, hD.fixedPointDerivative_eq,
    ContinuousLinearMap.toLinearMap_pow]

/-- **The return maps of the covers of a periodic orbit.** If `x` is a periodic point of `f` of
period `d` and `f^[d]` is differentiable at `x`, the fixed-point derivative of `f^[d * n]` at `x`,
the return map of the `n`-fold cover of the orbit, is the `n`-th power of the return map
`d(f^[d])_x`. -/
theorem fixedPointDerivative_iterate_mul {d : ℕ} (hx : IsPeriodicPt f d x)
    (hf : MDifferentiableAt I I f^[d] x) (n : ℕ) :
    fixedPointDerivative I f^[d * n] ⟨x, (hx.mul_const n).eq⟩ =
      fixedPointDerivative I f^[d] ⟨x, hx.eq⟩ ^ n := by
  -- Transport the fixed-point derivative along the equation `f^[d * n] = (f^[d])^[n]`.
  have key : ∀ (g : M → M) (hg : g = f^[d]^[n]) (p : g x = x),
      fixedPointDerivative I g ⟨x, p⟩ = fixedPointDerivative I f^[d]^[n] ⟨x, hg ▸ p⟩ := by
    rintro _ rfl _
    rfl
  rw [key _ (iterate_mul f d n)]
  exact fixedPointDerivative_iterate ⟨x, hx.eq⟩ hf n

/-- **The return determinant depends only on the map and the point.** The determinant
`det (1 - d(g)_y)` at a fixed point `y` of `g` is unchanged when `g` and `y` are replaced by equal
ones, whatever the proofs that they are fixed. -/
theorem det_id_sub_fixedPointDerivative_congr {g g' : M → M} {y y' : M} (p : g y = y)
    (p' : g' y' = y') (hg : g = g') (hy : y = y') :
    LinearMap.det (LinearMap.id - fixedPointDerivative I g ⟨y, p⟩) =
      LinearMap.det (LinearMap.id - fixedPointDerivative I g' ⟨y', p'⟩) := by
  subst hg hy
  rfl

/-- **The return determinant at the next point of a periodic orbit.** Let `x` be a periodic point
of `f` of period `n + 1`, with `f` differentiable at `x` and `f^[n]` differentiable at `f x`.
Then `det (1 - d(f^[n + 1]))` is the same at `f x` as at `x`. Writing `X = df_x` and
`Y = d(f^[n])_(f x)`, the two return maps are `X Y` and `Y X`, and
`det (1 - X Y) = det (1 - Y X)` (`LinearMap.det_one_sub_comp_comm`). No invertibility of `df_x`
is needed. -/
theorem det_id_sub_fixedPointDerivative_iterate_succ_apply [FiniteDimensional 𝕜 E] {n : ℕ}
    (hx : IsPeriodicPt f (n + 1) x) (hf : MDifferentiableAt I I f x)
    (hfn : MDifferentiableAt I I f^[n] (f x)) :
    LinearMap.det (LinearMap.id - fixedPointDerivative I f^[n + 1] ⟨f x, hx.apply.eq⟩) =
      LinearMap.det (LinearMap.id - fixedPointDerivative I f^[n + 1] ⟨x, hx.eq⟩) := by
  have hx' : f^[n] (f x) = x := (iterate_succ_apply f n x).symm.trans hx.eq
  -- The tangent spaces along the orbit are all the model space `E`.
  let X : E →L[𝕜] E := mfderiv I I f x
  let Y : E →L[𝕜] E := mfderiv I I f^[n] (f x)
  have hX : HasMFDerivAt I I f x X := hf.hasMFDerivAt
  have hY : HasMFDerivAt I I f^[n] (f x) Y := hfn.hasMFDerivAt
  have hX' : HasMFDerivAt I I f (f^[n] (f x)) X := by rw [hx']; exact hX
  -- At `x`, `f^[n + 1] = f^[n] ∘ f`; at `f x`, `f^[n + 1] = f ∘ f^[n]`.
  have h₀ : HasMFDerivAt I I f^[n + 1] x (Y.comp X) := by
    rw [iterate_succ]
    exact hY.comp x hX
  have h₁ : HasMFDerivAt I I f^[n + 1] (f x) (X.comp Y) := by
    rw [iterate_succ']
    exact hX'.comp (f x) hY
  rw [h₁.fixedPointDerivative_eq, h₀.fixedPointDerivative_eq]
  -- The goal lives on the tangent spaces at `x` and `f x`, both `E`; there `↑(X ∘L Y)` is
  -- `↑X ∘ₗ ↑Y` (`ContinuousLinearMap.toLinearMap_comp`) and `LinearMap.id` is `1`, by `rfl`.
  exact LinearMap.det_one_sub_comp_comm (R := 𝕜) (X : E →ₗ[𝕜] E) Y

/-- **The return determinant is constant along a periodic orbit.** If `x` is a periodic point of
period `n` of a map `f` differentiable at every point of the orbit of `x`, then
`det (1 - d(f^[n]))` is the same at every point `f^[j] x` of that orbit. Over `ℝ`, the points of
the orbit therefore have the same Lefschetz sign as fixed points of `f^[n]`. -/
theorem det_id_sub_fixedPointDerivative_apply_iterate [FiniteDimensional 𝕜 E] {n : ℕ}
    (hx : IsPeriodicPt f n x) (hf : ∀ m, MDifferentiableAt I I f (f^[m] x)) (j : ℕ) :
    LinearMap.det (LinearMap.id -
        fixedPointDerivative I f^[n] ⟨f^[j] x, (hx.apply_iterate j).eq⟩) =
      LinearMap.det (LinearMap.id - fixedPointDerivative I f^[n] ⟨x, hx.eq⟩) := by
  rcases n with _ | n
  · -- The iterate `f^[0]` is the identity, whose fixed-point derivative is the identity.
    rw [(hasMFDerivAt_id (f^[j] x)).fixedPointDerivative_eq,
      (hasMFDerivAt_id x).fixedPointDerivative_eq]
    rfl
  induction j with
  | zero => rfl
  | succ j ih =>
    -- Move from `f^[j + 1] x = f (f^[j] x)` back to `f^[j] x`, then use the induction hypothesis.
    rw [det_id_sub_fixedPointDerivative_congr _ (hx.apply_iterate j).apply.eq rfl
      (iterate_succ_apply' f j x), ← ih]
    refine det_id_sub_fixedPointDerivative_iterate_succ_apply (hx.apply_iterate j) (hf j)
      (mdifferentiableAt_iterate fun m _ ↦ ?_)
    rw [← iterate_succ_apply' f j x, ← iterate_add_apply]
    exact hf _

/-- **Nondegeneracy as a determinant condition.** On a manifold modelled on a finite-dimensional
space, a fixed point `x` at which `f` is differentiable is nondegenerate exactly when
`det (1 - df_x) ≠ 0`. -/
theorem isNondegenerateFixedPt_iff_det_id_sub_ne_zero [FiniteDimensional 𝕜 E]
    (x : {x // f x = x}) (hf : MDifferentiableAt I I f x.val) :
    IsNondegenerateFixedPt I f x.val ↔
      LinearMap.det (LinearMap.id - fixedPointDerivative I f x) ≠ 0 := by
  -- The tangent space is the model space `E`.
  have : FiniteDimensional 𝕜 (TangentSpace I x.val) := ‹FiniteDimensional 𝕜 E›
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
  simp only [LinearMap.sub_apply, LinearMap.id_apply, fixedPointDerivative_apply]
  exact ⟨fun h v hv ↦ h.eq_zero_of_mfderiv_apply_eq (sub_eq_zero.1 hv).symm,
    fun h ↦ ⟨x.property, hf, fun v hv ↦ h v (sub_eq_zero.2 hv.symm)⟩⟩

/-- **Nondegeneracy gives a nonzero determinant.** At a nondegenerate fixed point `x` of a self-map
`f` of a finite-dimensional normed space, with its trivial chart, `det (1 - df_x) ≠ 0`. -/
theorem IsNondegenerateFixedPt.det_one_sub_fderiv_ne_zero [FiniteDimensional 𝕜 E] {f : E → E}
    {x : E} (h : IsNondegenerateFixedPt 𝓘(𝕜, E) f x) : (1 - fderiv 𝕜 f x).det ≠ 0 := by
  have hdet := (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x, h.isFixedPt⟩
    h.mdifferentiableAt).1 h
  rw [det_id_sub_fixedPointDerivative_modelSpace] at hdet
  -- `ContinuousLinearMap.det` is the determinant of the underlying linear map, and `1` is `id`.
  simpa [ContinuousLinearMap.det, Module.End.one_eq_id] using hdet

/-- On a compact manifold over a complete field (whose model space is then finite-dimensional when
the manifold is nonempty), a continuous map that is differentiable at its fixed points, with
`det (1 - df_x) ≠ 0` at each of them, has only finitely many fixed points. -/
theorem finite_fixedPoints_of_det_id_sub_ne_zero [CompleteSpace 𝕜]
    [CompactSpace M] [T2Space M] (hf : Continuous f)
    (hdf : ∀ x : {x // f x = x}, MDifferentiableAt I I f x.val)
    (h : ∀ x : {x // f x = x}, LinearMap.det (LinearMap.id - fixedPointDerivative I f x) ≠ 0) :
    (fixedPoints f).Finite := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact Set.toFinite _
  have : FiniteDimensional 𝕜 E := FiniteDimensional.of_locallyCompact_manifold (M := M) I
  exact finite_fixedPoints_of_isNondegenerateFixedPt hf fun x hx ↦
    (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x, hx⟩ (hdf ⟨x, hx⟩)).2 (h ⟨x, hx⟩)

/-- **`det (1 - df_x)` is intrinsic.** If `f` is continuous at a fixed point `x`, then in any
extended chart whose source contains `x`, the derivative of the coordinate expression of `f` at `x`
within the range of the model has the same `det (1 - ·)` as the fixed-point derivative of `f` at
`x`: the two endomorphisms are conjugate by the derivative of the transition map. Over `ℝ`, at a
nondegenerate fixed point in the interior of the manifold, the sign of this determinant is the local
Lefschetz number. -/
theorem det_id_sub_fderivWithin_extChartAt_comp_extChartAt_symm [IsManifold I 1 M] {x' : M}
    (x : {x // f x = x}) (hf : ContinuousAt f x.val)
    (hx' : x.val ∈ (extChartAt I x').source) :
    LinearMap.det (LinearMap.id -
        (fderivWithin 𝕜 (extChartAt I x' ∘ f ∘ (extChartAt I x').symm) (range I)
          (extChartAt I x' x.val) : E →ₗ[𝕜] E)) =
      LinearMap.det (LinearMap.id - fixedPointDerivative I f x) := by
  obtain ⟨x, hx⟩ := x
  let D : E →L[𝕜] E := mfderiv I I f x
  set T := tangentCoordChange I x x' x
  set T' := tangentCoordChange I x' x x
  -- The derivatives `T` and `T'` of the transition maps between the charts at `x` and `x'` are
  -- mutually inverse, so they form a linear equivalence `e`.
  have hTT' : (T : E →ₗ[𝕜] E) ∘ₗ (T' : E →ₗ[𝕜] E) = LinearMap.id := LinearMap.ext fun v ↦
    (tangentCoordChange_comp ⟨⟨hx', mem_extChartAt_source x⟩, hx'⟩).trans
      (tangentCoordChange_self hx')
  have hT'T : (T' : E →ₗ[𝕜] E) ∘ₗ (T : E →ₗ[𝕜] E) = LinearMap.id := LinearMap.ext fun v ↦
    (tangentCoordChange_comp ⟨⟨mem_extChartAt_source x, hx'⟩, mem_extChartAt_source x⟩).trans
      (tangentCoordChange_self (mem_extChartAt_source x))
  let e : E ≃ₗ[𝕜] E := .ofLinearMap _ _ hTT' hT'T
  -- In the chart at `x'`, the derivative of `f` at `x` is `T ∘ D ∘ T'`.
  have hchart : fderivWithin 𝕜 (extChartAt I x' ∘ f ∘ (extChartAt I x').symm) (range I)
      (extChartAt I x' x) = T ∘L D ∘L T' := by
    have hT₀ : tangentCoordChange I (f x) x' (f x) = T := by rw [hx]
    rw [hf.fderivWithin_extChartAt_comp_extChartAt_symm hx' (by rwa [hx]), hT₀]
    -- `D` is `mfderiv I I f x` by definition.
    rfl
  -- So `1 - T ∘ D ∘ T'` is the conjugate of `1 - D` by `e`.
  have hconj : LinearMap.id - ((T ∘L D ∘L T' : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      (e : E →ₗ[𝕜] E) ∘ₗ (LinearMap.id - (D : E →ₗ[𝕜] E)) ∘ₗ (e.symm : E →ₗ[𝕜] E) := by
    ext v
    simpa [e] using congr(($hTT'.symm) v)
  rw [hchart, hconj, LinearMap.det_conj]
  -- Both sides are `det (1 - D)`, computed on `E` and on `T_x M`, which is `E` by definition.
  congr 2
  exact LinearMap.ext fun v ↦ (fixedPointDerivative_apply (I := I) (f := f) ⟨x, hx⟩ v).symm

/-- **Nondegeneracy read in a chart.** Let `x` be a fixed point of `f`, at which `f` is
differentiable, lying in the extended chart at `x'`. If the coordinate expression of `f` in that
chart has derivative `B` at `x` within the range of the model, then `x` is nondegenerate exactly
when `B - 1` is injective. The manifold may have boundary or corners. -/
theorem isNondegenerateFixedPt_iff_injective_sub_id_of_hasFDerivWithinAt [FiniteDimensional 𝕜 E]
    [IsManifold I 1 M] {x' : M} (hx : IsFixedPt f x) (hf : MDifferentiableAt I I f x)
    (hsrc : x ∈ (extChartAt I x').source) {B : E →L[𝕜] E}
    (hB : HasFDerivWithinAt (extChartAt I x' ∘ f ∘ (extChartAt I x').symm) B (range I)
      (extChartAt I x' x)) :
    IsNondegenerateFixedPt I f x ↔ Injective (B - ContinuousLinearMap.id 𝕜 E) := by
  have hfd : fderivWithin 𝕜 (extChartAt I x' ∘ f ∘ (extChartAt I x').symm) (range I)
      (extChartAt I x' x) = B :=
    hB.fderivWithin (I.uniqueDiffOn _
      (extChartAt_target_subset_range x' ((extChartAt I x').map_source hsrc)))
  have : FiniteDimensional 𝕜 (TangentSpace I x) := ‹FiniteDimensional 𝕜 E›
  rw [isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x, hx⟩ hf,
    ← det_id_sub_fderivWithin_extChartAt_comp_extChartAt_symm ⟨x, hx⟩ hf.continuousAt hsrc, hfd, Ne,
    LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot',
    injective_iff_map_eq_zero]
  -- Both sides say that `B` fixes no nonzero vector.
  refine forall_congr' fun w ↦ imp_congr_left ?_
  rw [← neg_eq_zero]
  simp

/-! ### The Lefschetz determinant and sign of a fixed point

The local contribution of a nondegenerate fixed point `x` of `f` to the Lefschetz fixed-point
formula is the sign of `det (1 - df_x)`. The determinant `TauCeti.fixedPointDet I f x` reads the
differential `df_x : T_x M → T_{f x} M` as an endomorphism of the model space, which is both tangent
spaces; at a fixed point this is the fixed-point derivative, so the value is intrinsic there. Over
`ℝ`, `TauCeti.fixedPointSign I f x` is `1` when this determinant is positive and `-1` otherwise.
Both are invariant under conjugation by a diffeomorphism, and at a fixed point the signs of the
iterates `f^[k]` are determined by the real eigenvalues of `df_x` outside `[-1, 1]`. -/

variable (I) in
/-- The **Lefschetz determinant** `det (1 - df_x)` of `f : M → M` at `x`, where the differential
`df_x = mfderiv I I f x` is read as an endomorphism of the model space `E`, which is both `T_x M`
and `T_{f x} M`. At a fixed point this is the determinant of `1` minus the fixed-point derivative
(`TauCeti.fixedPointDet_eq_det_id_sub_fixedPointDerivative`), which does not depend on the chart
(`TauCeti.det_id_sub_fderivWithin_extChartAt_comp_extChartAt_symm`). Where `f` is not
differentiable, `mfderiv` is zero and the value is `1`
(`TauCeti.fixedPointDet_of_not_mdifferentiableAt`). -/
noncomputable def fixedPointDet (f : M → M) (x : M) : 𝕜 :=
  LinearMap.det (M := E) (LinearMap.id - (mfderiv I I f x).toLinearMap)

/-- The defining formula of `TauCeti.fixedPointDet`. -/
theorem fixedPointDet_def :
    fixedPointDet I f x = LinearMap.det (M := E) (LinearMap.id - (mfderiv I I f x).toLinearMap) :=
  (rfl)

/-- If `f` has differential `D` at `x`, then `TauCeti.fixedPointDet I f x` is `det (1 - D)`. -/
theorem _root_.HasMFDerivAt.fixedPointDet_eq
    {D : TangentSpace I x →L[𝕜] TangentSpace I (f x)} (hD : HasMFDerivAt I I f x D) :
    fixedPointDet I f x = LinearMap.det (M := E) (LinearMap.id - D.toLinearMap) := by
  rw [fixedPointDet_def, hD.mfderiv]

/-- Where `f` is not differentiable, its differential is zero, so `det (1 - df_x) = 1`. -/
theorem fixedPointDet_of_not_mdifferentiableAt (hf : ¬MDifferentiableAt I I f x) :
    fixedPointDet I f x = 1 := by
  rw [fixedPointDet_def, mfderiv_zero_of_not_mdifferentiableAt hf,
    ContinuousLinearMap.toLinearMap_zero]
  -- The zero map `T_x M → T_{f x} M` is the zero endomorphism of `E`.
  exact (congrArg LinearMap.det (sub_zero (LinearMap.id (R := 𝕜) (M := E)))).trans LinearMap.det_id

/-- Maps that agree near `x` have the same Lefschetz determinant at `x`. -/
theorem _root_.Filter.EventuallyEq.fixedPointDet_eq {g : M → M} (h : g =ᶠ[𝓝 x] f) :
    fixedPointDet I g x = fixedPointDet I f x := by
  by_cases hf : MDifferentiableAt I I f x
  · rw [(hf.hasMFDerivAt.congr_of_eventuallyEq_abuse h).fixedPointDet_eq,
      hf.hasMFDerivAt.fixedPointDet_eq]
    -- Both sides are `det (1 - df_x)`; on the left `df_x` is typed as a map into `T_{g x} M`, on
    -- the right into `T_{f x} M`, and both tangent spaces are `E` by definition.
    rfl
  · rw [fixedPointDet_of_not_mdifferentiableAt hf, fixedPointDet_of_not_mdifferentiableAt
      fun hg ↦ hf (hg.congr_of_eventuallyEq h.symm)]

/-- At a fixed point `x`, `TauCeti.fixedPointDet I f x` is the determinant of `1` minus the
fixed-point derivative of `f` at `x`. -/
theorem fixedPointDet_eq_det_id_sub_fixedPointDerivative (x : {x // f x = x}) :
    fixedPointDet I f x.1 = LinearMap.det (LinearMap.id - fixedPointDerivative I f x) := by
  rw [fixedPointDet_def]
  -- Both sides are `det (1 - df_x)`, computed on `E` and on `T_x M`, which is `E` by definition.
  congr 2
  exact LinearMap.ext fun v ↦ (fixedPointDerivative_apply (I := I) (f := f) x v).symm

/-- On a normed space, with its trivial chart, `TauCeti.fixedPointDet` is computed from the Fréchet
derivative. -/
theorem fixedPointDet_modelSpace (f : E → E) (x : E) :
    fixedPointDet 𝓘(𝕜, E) f x = LinearMap.det (LinearMap.id - (fderiv 𝕜 f x : E →ₗ[𝕜] E)) := by
  rw [fixedPointDet_def, mfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity of the model space.
  rfl

/-- **The Lefschetz determinant of an iterate.** If `f` is differentiable at a fixed point `x`,
then `det (1 - d(f^[n])_x) = det (1 - (df_x) ^ n)`. -/
theorem fixedPointDet_iterate (hx : IsFixedPt f x) (hf : MDifferentiableAt I I f x) (n : ℕ) :
    fixedPointDet I f^[n] x =
      LinearMap.det (LinearMap.id - fixedPointDerivative I f ⟨x, hx⟩ ^ n) := by
  rw [fixedPointDet_eq_det_id_sub_fixedPointDerivative (I := I) ⟨x, hx.iterate n⟩,
    fixedPointDerivative_iterate ⟨x, hx⟩ hf n]

/-- **Nondegeneracy as a determinant condition.** On a manifold modelled on a finite-dimensional
space, a fixed point `x` at which `f` is differentiable is nondegenerate exactly when
`det (1 - df_x) ≠ 0`. -/
theorem fixedPointDet_ne_zero_iff [FiniteDimensional 𝕜 E] (hx : IsFixedPt f x)
    (hf : MDifferentiableAt I I f x) :
    fixedPointDet I f x ≠ 0 ↔ IsNondegenerateFixedPt I f x :=
  (fixedPointDet_eq_det_id_sub_fixedPointDerivative (I := I) ⟨x, hx⟩).symm ▸
    (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x, hx⟩ hf).symm

/-- At a nondegenerate fixed point, on a manifold modelled on a finite-dimensional space,
`det (1 - df_x) ≠ 0`. -/
theorem IsNondegenerateFixedPt.fixedPointDet_ne_zero [FiniteDimensional 𝕜 E]
    (h : IsNondegenerateFixedPt I f x) : fixedPointDet I f x ≠ 0 :=
  (fixedPointDet_ne_zero_iff h.isFixedPt h.mdifferentiableAt).2 h

section Conjugation

variable {E' G N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 E' G} [TopologicalSpace N] [ChartedSpace G N] {g : N → N}
  {n : WithTop ℕ∞}

/-- If `g ∘ Φ = Φ ∘ f` near `x`, then `g = Φ ∘ f ∘ Φ⁻¹` near `Φ x`. -/
private theorem eventuallyEq_comp_comp_symm (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (hg : ∀ᶠ y in 𝓝 x, g (Φ y) = Φ (f y)) : g =ᶠ[𝓝 (Φ x)] Φ ∘ f ∘ Φ.symm := by
  have ht : Tendsto Φ.symm (𝓝 (Φ x)) (𝓝 x) := by
    simpa using Φ.symm.continuous.tendsto (Φ x)
  exact (ht.eventually hg).mono fun z hz ↦ by simpa using hz

/-- The differential of `Φ ∘ f ∘ Φ⁻¹` at `Φ x`, for a fixed point `x` of `f` at which `f` is
differentiable, is the conjugate `dΦ_x ∘ df_x ∘ (dΦ_x)⁻¹`, so it has the same `det (1 - ·)`. -/
private theorem fixedPointDet_comp_comp_symm (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (hx : IsFixedPt f x) (hf : MDifferentiableAt I I f x) :
    fixedPointDet J (Φ ∘ f ∘ Φ.symm) (Φ x) = fixedPointDet I f x := by
  -- Read the differentials `A = dΦ_x`, `B = d(Φ⁻¹)_(Φ x)` and `D = df_x` as linear maps between the
  -- model spaces `E` and `E'`, which are the tangent spaces at every point.
  let A : E →L[𝕜] E' := mfderiv I J Φ x
  let B : E' →L[𝕜] E := mfderiv J I Φ.symm (Φ x)
  let D : E →L[𝕜] E := mfderiv I I f x
  have hsx : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  have hA (y : M) (hy : y = x) : HasMFDerivAt I J Φ y A := by
    subst hy
    exact (Φ.mdifferentiable hn y).hasMFDerivAt
  have hB : HasMFDerivAt J I Φ.symm (Φ x) B := (Φ.symm.mdifferentiable hn (Φ x)).hasMFDerivAt
  have hD (y : M) (hy : y = x) : HasMFDerivAt I I f y D := by
    subst hy
    exact hf.hasMFDerivAt
  -- `A` and `B` are mutually inverse, by the chain rule for `Φ⁻¹ ∘ Φ = id` and `Φ ∘ Φ⁻¹ = id`.
  have hBA : (B : E' →ₗ[𝕜] E) ∘ₗ (A : E →ₗ[𝕜] E') = LinearMap.id := by
    have h := (hB.comp x (hA x rfl)).mfderiv
    rw [show Φ.symm ∘ Φ = id from funext Φ.symm_apply_apply, mfderiv_id] at h
    exact LinearMap.ext fun v ↦ (DFunLike.congr_fun h v).symm
  have hAB : (A : E →ₗ[𝕜] E') ∘ₗ (B : E' →ₗ[𝕜] E) = LinearMap.id := by
    have h := ((hA _ hsx).comp (Φ x) hB).mfderiv
    rw [show Φ ∘ Φ.symm = id from funext Φ.apply_symm_apply, mfderiv_id] at h
    exact LinearMap.ext fun w ↦ (DFunLike.congr_fun h w).symm
  let e : E ≃ₗ[𝕜] E' := .ofLinearMap _ _ hAB hBA
  -- By the chain rule the differential of `Φ ∘ f ∘ Φ⁻¹` at `Φ x` is `A ∘ D ∘ B`, and
  -- `1 - A ∘ D ∘ B` is the conjugate of `1 - D` by `e`.
  have hF : HasMFDerivAt J J (Φ ∘ f ∘ Φ.symm) (Φ x) (A.comp (D.comp B)) :=
    (hA _ (by simp [hsx, hx.eq])).comp (Φ x) ((hD _ hsx).comp (Φ x) hB)
  have hconj : LinearMap.id - ((A.comp (D.comp B) : E' →L[𝕜] E') : E' →ₗ[𝕜] E') =
      (e : E →ₗ[𝕜] E') ∘ₗ (LinearMap.id - (D : E →ₗ[𝕜] E)) ∘ₗ (e.symm : E' →ₗ[𝕜] E) := by
    ext w
    simpa [e] using (DFunLike.congr_fun hAB w).symm
  rw [hF.fixedPointDet_eq, (hD x rfl).fixedPointDet_eq]
  -- `hconj` is stated on `E'`, the goal on the tangent space at `Φ x`, which is `E'` by definition.
  exact (congrArg LinearMap.det hconj).trans (LinearMap.det_conj _ e)

/-- **Conjugation invariance of the Lefschetz determinant.** Let `Φ : M ≃ N` be a `C^n`
diffeomorphism, `n ≠ 0`, and `x` a fixed point of `f : M → M`. If `g : N → N` satisfies
`g ∘ Φ = Φ ∘ f` near `x`, then `det (1 - dg_(Φ x)) = det (1 - df_x)`: the differentials are
conjugate by `dΦ_x`. Charts are the local case, and `g = Φ ∘ f ∘ Φ⁻¹` the global one. -/
theorem _root_.Diffeomorph.fixedPointDet_eq_of_semiconj (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (hx : IsFixedPt f x) (hg : ∀ᶠ y in 𝓝 x, g (Φ y) = Φ (f y)) :
    fixedPointDet J g (Φ x) = fixedPointDet I f x := by
  rw [(eventuallyEq_comp_comp_symm Φ hg).fixedPointDet_eq]
  by_cases hf : MDifferentiableAt I I f x
  · exact fixedPointDet_comp_comp_symm Φ hn hx hf
  · -- Otherwise `Φ ∘ f ∘ Φ⁻¹` is not differentiable at `Φ x` either, since `f = Φ⁻¹ ∘ g ∘ Φ`.
    have hF : ¬MDifferentiableAt J J (Φ ∘ f ∘ Φ.symm) (Φ x) := fun hF ↦ hf <| by
      have h₁ : MDifferentiableAt J I (Φ.symm ∘ Φ ∘ f ∘ Φ.symm) (Φ x) :=
        MDifferentiableAt.comp (Φ x) (Φ.symm.mdifferentiable hn _) hF
      have h₂ := MDifferentiableAt.comp x h₁ (Φ.mdifferentiable hn x)
      rwa [show (Φ.symm ∘ Φ ∘ f ∘ Φ.symm) ∘ Φ = f from funext fun y ↦ by simp] at h₂
    rw [fixedPointDet_of_not_mdifferentiableAt hf, fixedPointDet_of_not_mdifferentiableAt hF]

end Conjugation

section Sign

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → M} {x : M}

variable (I) in
/-- The **Lefschetz sign** of `f : M → M` at `x`: `1` when `det (1 - df_x)`
(`TauCeti.fixedPointDet`) is positive and `-1` otherwise. At a nondegenerate fixed point in the
interior of the manifold it is the contribution of `x` to the Lefschetz fixed-point formula, the
sign of `det (1 - df_x)` (`TauCeti.fixedPointSign_eq_sign`). -/
noncomputable def fixedPointSign (f : M → M) (x : M) : ℤ :=
  if 0 < fixedPointDet I f x then 1 else -1

/-- The Lefschetz sign is `1` where `det (1 - df_x) > 0`. -/
@[simp]
theorem fixedPointSign_of_pos (h : 0 < fixedPointDet I f x) : fixedPointSign I f x = 1 := by
  simp [fixedPointSign, h]

/-- The Lefschetz sign is `-1` where `det (1 - df_x) ≤ 0`. -/
@[simp]
theorem fixedPointSign_of_nonpos (h : fixedPointDet I f x ≤ 0) : fixedPointSign I f x = -1 := by
  simp [fixedPointSign, h.not_gt]

/-- The Lefschetz sign is `1` exactly where `det (1 - df_x) > 0`. -/
theorem fixedPointSign_eq_one_iff : fixedPointSign I f x = 1 ↔ 0 < fixedPointDet I f x := by
  by_cases h : 0 < fixedPointDet I f x <;> simp [fixedPointSign, h]

/-- The Lefschetz sign is `-1` exactly where `det (1 - df_x) ≤ 0`. -/
theorem fixedPointSign_eq_neg_one_iff :
    fixedPointSign I f x = -1 ↔ fixedPointDet I f x ≤ 0 := by
  rcases lt_or_ge 0 (fixedPointDet I f x) with h | h
  · simp [h, h.not_ge]
  · simp [h]

/-- When `det (1 - df_x) ≠ 0`, for instance at a nondegenerate fixed point of a map of a manifold
modelled on a finite-dimensional space, the Lefschetz sign is the sign of `det (1 - df_x)`. -/
theorem fixedPointSign_eq_sign (h : fixedPointDet I f x ≠ 0) :
    fixedPointSign I f x = SignType.sign (fixedPointDet I f x) := by
  rcases h.lt_or_gt with h | h
  · simp [fixedPointSign_of_nonpos h.le, sign_neg h]
  · simp [fixedPointSign_of_pos h, sign_pos h]

/-- **Conjugation invariance of the Lefschetz sign.** If `g ∘ Φ = Φ ∘ f` near a fixed point `x` of
`f`, for a `C^n` diffeomorphism `Φ`, `n ≠ 0`, then `g` and `f` have the same Lefschetz sign at
`Φ x` and `x`. -/
theorem _root_.Diffeomorph.fixedPointSign_eq_of_semiconj {E' G N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace G] {J : ModelWithCorners ℝ E' G} [TopologicalSpace N]
    [ChartedSpace G N] {g : N → N} {n : WithTop ℕ∞} (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (hx : IsFixedPt f x) (hg : ∀ᶠ y in 𝓝 x, g (Φ y) = Φ (f y)) :
    fixedPointSign J g (Φ x) = fixedPointSign I f x := by
  rw [fixedPointSign, Φ.fixedPointDet_eq_of_semiconj hn hx hg, fixedPointSign]

/-- **The Lefschetz signs of the iterates.** Let `x` be a fixed point of `f`, on a manifold modelled
on a finite-dimensional real space, at which `f` has differential `D`, and write `i₊` and `i₋` for
the numbers of real eigenvalues of `D` in `(1, ∞)` and in `(-∞, -1)`, with algebraic multiplicity.
If `det (1 - d(f^[k])_x) ≠ 0`, then the Lefschetz sign of `f^[k]` at `x` is
`(-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`. -/
theorem fixedPointSign_iterate [FiniteDimensional ℝ E] (hx : IsFixedPt f x) {D : E →L[ℝ] E}
    (hD : HasMFDerivAt I I f x D) {k : ℕ} (hk : fixedPointDet I f^[k] x ≠ 0) :
    fixedPointSign I f^[k] x =
      (-1) ^ (((D : Module.End ℝ E).charpoly.roots.filter (1 < ·)).card) *
        (-1) ^ ((k + 1) * ((D : Module.End ℝ E).charpoly.roots.filter (· < -1)).card) := by
  have hdet : fixedPointDet I f^[k] x = LinearMap.det (1 - (D : Module.End ℝ E) ^ k) := by
    rw [(hD.iterate hx k).fixedPointDet_eq, Module.End.one_eq_id,
      ← ContinuousLinearMap.toLinearMap_pow]
    -- The differential `D ^ k` of `f^[k]` is typed on `T_x M`, which is `E` by definition.
    rfl
  rw [fixedPointSign_eq_sign hk, hdet, LinearMap.sign_det_one_sub_pow _ k (hdet ▸ hk)]
  simp

/-- **The Lefschetz sign of a nondegenerate fixed point** `x` of a map `f` of a manifold modelled on
a finite-dimensional real space, with differential `D` at `x`, is `(-1) ^ i₊`, where `i₊` is the
number of real eigenvalues of `D` in `(1, ∞)`, counted with algebraic multiplicity. -/
theorem IsNondegenerateFixedPt.fixedPointSign_eq [FiniteDimensional ℝ E]
    (h : IsNondegenerateFixedPt I f x) {D : E →L[ℝ] E} (hD : HasMFDerivAt I I f x D) :
    fixedPointSign I f x = (-1) ^ (((D : Module.End ℝ E).charpoly.roots.filter (1 < ·)).card) := by
  have h₁ := fixedPointSign_iterate h.isFixedPt hD (k := 1) (by simpa using h.fixedPointDet_ne_zero)
  rw [Function.iterate_one] at h₁
  rw [h₁, pow_mul]
  simp

end Sign

end TauCeti
