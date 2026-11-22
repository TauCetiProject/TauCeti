/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex.Perturbation
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation

/-!
# Counting periodic points of a perturbed map by the fixed-point index

Let `φ` be a self-map of a finite-dimensional real normed space `E`, `k > 0`, and `W ⊆ E` a set
from which every orbit of `φ` stays away until time `k`: `φ^[j] y ∉ W` for `y ∈ W` and
`0 < j < k`. Let `U ⊆ W` be open and suppose that the points of `U` fixed by `φ^[k]` form a
compact set. They may be degenerate, as for a family of periodic orbits, and they need not be
isolated.

This file shows that the periodic points of a perturbed map `φ ∘ ψ` count them, with the
fixed-point index `ContinuousMap.fixedPointIndex` of `φ^[k]` on `U`, independently of the
perturbation `ψ` (`TauCeti.exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex`):

there are an open neighbourhood `V ⊆ U` of these fixed points and `δ > 0` such that, for every
`ψ` continuous on `V`, moving the points of `V` by less than `δ` and fixing every point outside
`W`, if the fixed points of `(φ ∘ ψ)^[k]` in `V` are nondegenerate, then they are finitely many
and `∑ sign det (1 - d((φ ∘ ψ)^[k])_x)` over them is the index of `φ^[k]` on `U`.

The perturbation acts on `φ` itself, not on its iterate, so for `k > 1` it is not small in the
sense of `ContinuousMap.exists_pos_forall_fixedPointIndex_eq` a priori. The orbit condition makes
it so: a point `x` with `ψ x ∈ W` has its later orbit points `φ^[j] (ψ x)`, `0 < j < k`, outside
`W`, where `ψ` is the identity, so `(φ ∘ ψ)^[k] x = φ^[k] (ψ x)`
(`Function.iterate_comp_apply_eq_iterate_apply`). Uniform continuity of `φ^[k]` near the compact
closure of `V` then makes `(φ ∘ ψ)^[k]` uniformly close to `φ^[k]` on `V`.

Localized Hamiltonian perturbations of an area-preserving map have this form
(`TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`), which is how a
degenerate return map is replaced by one with nondegenerate periodic points without changing the
signed count.

## Main results

* `TauCeti.exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex`: the signed count of
  the nondegenerate periodic points of every small localized perturbation is the fixed-point
  index.

## References

* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5.
-/

public section

open Function Metric Set Topology TopologicalSpace
open scoped Manifold

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The periodic points of a localized perturbation are counted by the fixed-point index.**
Let `φ : E → E` and `k > 0`, and let `W` be a set such that `φ^[j] y ∉ W` for `y ∈ W` and
`0 < j < k`. Let `f : U → E` be `φ^[k]` on an open set `U ⊆ W`, with compact fixed set. There are
an open set `V ⊆ U` containing every fixed point of `f`, with compact closure contained in `U`, and
`δ > 0` with the following property. Let `ψ` be continuous on `V`, with `‖ψ w - w‖ < δ` on `V` and
`ψ w = w` outside `W`, such that every fixed point of `(φ ∘ ψ)^[k]` in `V` is nondegenerate. Then
these fixed points are finitely many, and the sum of `sign det (1 - d((φ ∘ ψ)^[k])_x)` over them is
the fixed-point index of `f`. -/
theorem exists_pos_forall_sum_sign_det_iterate_comp_eq_fixedPointIndex {φ : E → E} {k : ℕ}
    (hk : 0 < k) {W : Set E} (hret : ∀ y ∈ W, ∀ j, 0 < j → j < k → φ^[j] y ∉ W) {U : Opens E}
    (hUW : (U : Set E) ⊆ W)
    (f : C(U, E)) (hf : ∀ z, f z = φ^[k] z) (hfix : IsCompact {z | f z = z}) :
    ∃ V : Opens E, V ≤ U ∧ (∀ z, f z = z → (z : E) ∈ V) ∧ IsCompact (closure (V : Set E)) ∧
      closure (V : Set E) ⊆ U ∧ ∃ δ > 0, ∀ ψ : E → E, ContinuousOn ψ V →
        (∀ w ∈ V, ‖ψ w - w‖ < δ) → (∀ w ∉ W, ψ w = w) →
        (∀ z : V, (φ ∘ ψ)^[k] z = z → IsNondegenerateFixedPt 𝓘(ℝ, E) (φ ∘ ψ)^[k] z) →
        ∃ hfin : {z : V | (φ ∘ ψ)^[k] z = z}.Finite,
          ∑ z ∈ hfin.toFinset, (SignType.sign (1 - fderiv ℝ (φ ∘ ψ)^[k] z).det : ℤ) =
            f.fixedPointIndex := by
  obtain ⟨V, hVU, hfV, hVc, hVcU, δ, hδ, hstab⟩ := f.exists_pos_forall_fixedPointIndex_eq hfix
  -- `φ^[k]` is `f` on `U`, so it is continuous at the points of `U`, and uniformly continuous near
  -- `closure V`.
  have hcont (y : E) (hy : y ∈ U) : ContinuousAt φ^[k] y :=
    (continuousOn_iff_continuous_domRestrict.2 (f.continuous.congr hf)).continuousAt
      (U.isOpen.mem_nhds hy)
  obtain ⟨η, hη, hηφ⟩ := Metric.mem_uniformity_dist.1 (hVc.uniformContinuousAt_of_continuousAt
    φ^[k] (fun y hy ↦ hcont y (hVcU hy)) (dist_mem_uniformity hδ))
  obtain ⟨η', hη', hη'U⟩ := hVc.exists_cthickening_subset_open U.isOpen hVcU
  refine ⟨V, hVU, hfV, hVc, hVcU, min η η', lt_min hη hη', fun ψ hψc hψδ hψW hnd ↦ ?_⟩
  -- Each point of `V` is moved by `ψ` into `U`, where the perturbed iterate is `φ^[k] ∘ ψ`.
  have hψV (w : E) (hw : w ∈ V) : dist w (ψ w) < min η η' := by
    rw [dist_comm, dist_eq_norm]
    exact hψδ w hw
  have hψmem (w : E) (hw : w ∈ V) : ψ w ∈ U :=
    hη'U (mem_cthickening_of_dist_le (ψ w) w η' _ (subset_closure hw)
      (by rw [dist_comm]; exact ((hψV w hw).trans_le (min_le_right _ _)).le))
  have hiter (w : E) (hw : w ∈ V) : (φ ∘ ψ)^[k] w = φ^[k] (ψ w) :=
    iterate_comp_apply_eq_iterate_apply hk fun j hj hjk ↦
      hψW _ (hret _ (hUW (hψmem w hw)) j hj hjk)
  -- The perturbed iterate, as a continuous map on `V`.
  let g : C(V, E) := ⟨fun z ↦ (φ ∘ ψ)^[k] z, by
    refine continuousOn_iff_continuous_domRestrict.1 (ContinuousOn.congr ?_ hiter)
    exact fun w hw ↦ ((hcont _ (hψmem w hw)).comp_continuousWithinAt (hψc w hw))⟩
  have hgf (z : V) : ‖g z - f (inclusion hVU z)‖ < δ := by
    -- `g z` is `(φ ∘ ψ)^[k] z` by definition.
    have hgz : g z = φ^[k] (ψ z) := hiter z z.property
    rw [← dist_eq_norm, dist_comm, hgz, hf]
    exact hηφ (hψV z z.property |>.trans_le (min_le_left _ _)) (subset_closure z.property)
  obtain ⟨hgc, hgi⟩ := hstab g hgf
  -- At the fixed points of `g`, the perturbed iterate has derivatives with `det (1 - D) ≠ 0`.
  have hD (z : V) (hz : g z = z) : HasFDerivAt (φ ∘ ψ)^[k] (fderiv ℝ (φ ∘ ψ)^[k] z) z :=
    (mdifferentiableAt_iff_differentiableAt.1 (hnd z hz).mdifferentiableAt).hasFDerivAt
  have hdet (z : V) (hz : g z = z) := (hnd z hz).det_one_sub_fderiv_ne_zero
  have hfin := g.finite_setOf_apply_eq hgc (fun _ ↦ rfl) hD hdet
  exact ⟨hfin, (g.fixedPointIndex_eq_sum_sign_det hfin (fun _ ↦ rfl) hD hdet).symm.trans hgi⟩

end TauCeti
