/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Vector fields transverse to a map

A vector field `Z` on a manifold `M` is **transverse along** a map `ι : S → M`
(`TauCeti.IsTransverseAlong`) when at every point `s` of `S` the vector `Z (ι s)` is not tangent
to `ι`: it does not lie in the range of the differential `dι_s`. When `ι` is an embedded
hypersurface, so that this range has codimension one, this is transversality of `Z` to the
hypersurface in the usual sense: `Z (ι s)` and the tangent space of the hypersurface at `s` span
the tangent space of `M` at `ι s`. A transverse vector field does not vanish along `ι`
(`TauCeti.IsTransverseAlong.ne_zero`).

For a regular level `f⁻¹(c)` of a scalar function, with its preferred atlas
`TauCeti.regularLevelChartedSpace`, the tangent space at `x` is the kernel of `df_x`
(`TauCeti.range_mfderiv_coe_regularLevel`). So a vector field is transverse along the
inclusion of the level exactly when `df(Z) ≠ 0` at every point of the level
(`TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`). This is how transversality to the
hypersurfaces of symplectic geometry (energy levels, boundaries of domains, cosphere bundles) is
checked in practice.

A vector field crossing a level of `f` in the direction of increasing `f`, `df(Z) > 0`, leaves the
sublevel set there: a point where `df` does not vanish is not a local maximum, by Fermat's theorem,
so every point of the level is a limit of points where `f` is larger
(`TauCeti.mem_closure_setOf_lt_of_mvfderiv_pos`). Hence the frontier of the sublevel set `{f ≤ c}`
is exactly the level `f⁻¹(c)` when `df(Z) > 0` along it
(`TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`). This identifies the boundary of a domain whose
boundary is crossed outwards by a vector field, as for Liouville domains.

Conversely, every nonzero tangent vector is transverse to some hypersurface through its base point
(`TauCeti.exists_hypersurface_notMem_range_mfderiv`): in a chart, take an affine hyperplane through
the point not containing the vector. Flowing a vector field out of such a hypersurface is the usual
way to build coordinates adapted to the field, as in the Reeb normal form of a contact form.

## Main definitions

* `TauCeti.IsTransverseAlong`: `Z (ι s)` is outside the range of `dι_s` for every `s`.

## Main results

* `TauCeti.isTransverseAlong_coe_scalarRegularLevel_iff`: transversality along a regular level is
  the nonvanishing of `df(Z)` on the level.
* `TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`: the frontier of a sublevel set whose level is
  crossed outwards by a vector field is the level.
* `TauCeti.exists_hypersurface_notMem_range_mfderiv`: a nonzero tangent vector is transverse to a
  hypersurface through its base point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 5
  (vector fields transverse to a hypersurface).
-/

public section

open Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

variable (J) in
/-- A vector field `Z` on `M` is **transverse along** a map `ι : S → M` when at every point `s`
the vector `Z (ι s)` is not tangent to `ι`, that is, not in the range of the differential `dι_s`.
For an embedded hypersurface this is transversality of `Z` to the hypersurface. -/
def IsTransverseAlong (Z : (x : M) → TangentSpace I x) (ι : S → M) : Prop :=
  ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range

/-- The defining characterization of a vector field transverse along a map. -/
theorem isTransverseAlong_iff {Z : (x : M) → TangentSpace I x} {ι : S → M} :
    IsTransverseAlong J Z ι ↔ ∀ s, Z (ι s) ∉ (mfderiv J I ι s).range :=
  Iff.rfl

/-- A vector field transverse along `ι` does not vanish at the points of the image of `ι`. -/
theorem IsTransverseAlong.ne_zero {Z : (x : M) → TangentSpace I x} {ι : S → M}
    (h : IsTransverseAlong J Z ι) (s : S) : Z (ι s) ≠ 0 :=
  fun h0 ↦ h s (h0 ▸ Submodule.zero_mem _)

/-! ### Vector fields crossing a level outwards -/

section Crossing

variable [I.Boundaryless]

/-- **A direction increasing a function leaves its sublevel set.** If a tangent vector `v` at a
point `x` of a boundaryless manifold satisfies `df_x(v) > 0`, then `x` lies in the closure of the
set `{y | f x < f y}`: otherwise `x` would be a local maximum of `f`, hence a critical point by
Fermat's theorem (`IsLocalMax.mem_criticalPoints`), and `df_x` would vanish. -/
theorem mem_closure_setOf_lt_of_mvfderiv_pos {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (hpos : 0 < mvfderiv I f x v) : x ∈ closure {y | f x < f y} := by
  by_contra h
  rw [mem_closure_iff_frequently, not_frequently] at h
  have hmax : IsLocalMax f x := h.mono fun y hy ↦ not_lt.1 hy
  simp [mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))] at hpos

/-- **The frontier of a sublevel set crossed outwards by a vector field.** Let `f` be continuous,
and let `Z` be a vector field with `df(Z) > 0` along the level `f⁻¹(c)`. Then the frontier of the
sublevel set `{f ≤ c}` is exactly the level `f⁻¹(c)`. -/
theorem frontier_setOf_le_eq_of_mvfderiv_pos {Z : (x : M) → TangentSpace I x} {f : M → ℝ}
    {c : ℝ} (hfc : Continuous f) (hpos : ∀ x, f x = c → 0 < mvfderiv I f x (Z x)) :
    frontier {x | f x ≤ c} = {x | f x = c} := by
  refine (frontier_le_subset_eq hfc continuous_const).antisymm fun x (hx : f x = c) ↦ ?_
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hx.le, closure_mono (fun y hy ↦ by simpa [← hx] using hy)
    (mem_closure_setOf_lt_of_mvfderiv_pos (hpos x hx))⟩

end Crossing

/-! ### A hypersurface transverse to a tangent vector -/

section Hypersurface

variable [I.Boundaryless] [FiniteDimensional ℝ E] {n : ℕ∞} [IsManifold I n M]

/-- **A hypersurface transverse to a tangent vector.** Every nonzero tangent vector `v` at a point
`x₀` of a finite-dimensional boundaryless `C^n` manifold, `1 ≤ n`, is transverse to a `C^n`
hypersurface through `x₀`: there are a hyperplane `K` of the model space and a `C^n` map
`ι : K → M` with `ι 0 = x₀`, injective differential at `0`, and `v` outside the range of that
differential. -/
theorem exists_hypersurface_notMem_range_mfderiv (hn : 1 ≤ n) {x₀ : M} {v : TangentSpace I x₀}
    (hv : v ≠ 0) :
    ∃ (K : Submodule ℝ E) (ι : K → M), ContMDiff 𝓘(ℝ, K) I n ι ∧ ι 0 = x₀ ∧
      Function.Injective (mfderiv 𝓘(ℝ, K) I ι 0) ∧ v ∉ (mfderiv 𝓘(ℝ, K) I ι 0).range ∧
      finrank ℝ K + 1 = finrank ℝ E := by
  have : IsManifold I 1 M := IsManifold.of_le (n := n) (by exact_mod_cast hn)
  set e := extChartAt I x₀
  -- The hyperplane: the kernel of a continuous linear form that does not vanish on `v`.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ E, ℓ v ≠ 0 := SeparatingDual.exists_ne_zero hv
  set K := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)
  have hdim : finrank ℝ K + 1 = finrank ℝ E :=
    Module.Dual.finrank_ker_add_one_of_ne_zero fun h ↦
      hℓ (by rw [← ContinuousLinearMap.coe_coe, h]; rfl)
  -- A ball around `e x₀` in the chart target, and a bump function on `K` supported in it.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (extChartAt_target_mem_nhds (I := I) x₀)
  let χ : ContDiffBump (0 : K) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set c : K → E := fun k ↦ χ k • (k : E)
  have hc : ContDiff ℝ n c := χ.contDiff.smul K.subtypeL.contDiff
  have hcr (k : K) : e x₀ + c k ∈ e.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    by_cases hk : χ k = 0
    · simp [c, hk, hr]
    have hkr : k ∈ Metric.ball (0 : K) r := χ.support_eq ▸ hk
    calc ‖c k‖ ≤ ‖k‖ := by
          simpa [c, norm_smul, abs_of_nonneg χ.nonneg] using
            mul_le_of_le_one_left (norm_nonneg k) χ.le_one
      _ < r := by simpa using hkr
  set ι : K → M := fun k ↦ e.symm (e x₀ + c k)
  have hι : ContMDiff 𝓘(ℝ, K) I n ι :=
    (contMDiffOn_extChartAt_symm x₀).comp_contMDiff
      (contMDiff_iff_contDiff.2 (contDiff_const.add hc)) hcr
  have hι₀ : ι 0 = x₀ := by simp [ι, c, e]
  -- Near `0`, the chart reads `ι` as the translate `k ↦ e x₀ + k`, so `dι₀` is the inclusion.
  have hdι (w : K) : mfderiv 𝓘(ℝ, K) I ι 0 w = (w : E) := by
    have heq : e ∘ ι =ᶠ[𝓝 0] fun k ↦ e x₀ + (k : E) := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : K) (half_pos hr)] with k hk
      have hχ : χ k = 1 := χ.one_of_mem_closedBall hk
      simpa [ι, c, hχ] using e.right_inv (by simpa [c, hχ] using hcr k)
    have hlin : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) (e ∘ ι) 0 w = (w : E) := by
      have hd : HasFDerivAt (fun k : K ↦ e x₀ + (k : E)) K.subtypeL 0 :=
        K.subtypeL.hasFDerivAt.const_add (e x₀)
      rw [heq.mfderiv_eq, mfderiv_eq_fderiv, hd.fderiv]
      -- The tangent identifications of the model spaces are the identity.
      rfl
    have he : MDifferentiableAt I 𝓘(ℝ, E) e x₀ :=
      mdifferentiableAt_extChartAt (mem_chart_source H x₀)
    have h := (mfderiv_comp_apply_of_eq 0 he (hι.mdifferentiableAt (by
      exact_mod_cast (zero_lt_one.trans_le hn).ne')) hι₀ w).symm.trans hlin
    rwa [mfderiv_extChartAt_eq_id] at h
  refine ⟨K, ι, hι, hι₀, fun w w' h ↦ Subtype.ext ((hdι w).symm.trans (h.trans (hdι w'))), ?_,
    hdim⟩
  rintro ⟨w, hw⟩
  -- A tangent vector of `K` at `0` is an element of `K`, which `ℓ` kills.
  let k : K := w
  have hkv : (k : E) = v := (hdι k).symm.trans hw
  exact hℓ (by rw [← hkv]; exact k.2)

end Hypersurface

variable {f : M → ℝ} {c : ℝ} [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ) f c)

/-- **Transversality to a regular level.** A vector field `Z` is transverse along the inclusion of
a regular level `f⁻¹(c)`, with its preferred atlas `TauCeti.regularLevelChartedSpace`,
exactly when `df(Z) ≠ 0` at every point of the level. -/
theorem isTransverseAlong_coe_scalarRegularLevel_iff {Z : (x : M) → TangentSpace I x} :
    letI := regularLevelChartedSpace (n := finrank ℝ E - 1) hf hreg (by rw [finrank_self])
    IsTransverseAlong 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) Z (Subtype.val : {x : M // f x = c} → M) ↔
      ∀ x, f x = c → mfderiv I 𝓘(ℝ) f x (Z x) ≠ 0 := by
  let := regularLevelChartedSpace (n := finrank ℝ E - 1) hf hreg (by rw [finrank_self])
  simp only [isTransverseAlong_iff, range_mfderiv_coe_regularLevel hf hreg (by rw [finrank_self]),
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Subtype.forall]

end TauCeti
