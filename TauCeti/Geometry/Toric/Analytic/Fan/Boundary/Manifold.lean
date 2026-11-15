/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.NormalForm
public import Mathlib.Geometry.Manifold.SmoothEmbedding

import TauCeti.Data.Fin.Sum
import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Intersection

/-!
# Complex manifolds on toric orbit closures and boundary components

The closure of the torus orbit of a cone `σ` of a regular toric fan realization, with its
original subspace topology, admits a complex manifold structure of dimension `rank N - dim σ`,
and its inclusion into the realization is a holomorphic smooth embedding. This orbit closure is
the intersection of the boundary components of the rays of `σ`
(`TauCeti.Toric.Fan.iInter_analyticBoundaryComponent_eq_closure_analyticConeOrbit`), so the
boundary components meet in closed embedded complex submanifolds of the expected codimension.

For a ray, the orbit closure is the boundary component itself: each ray-indexed boundary
component admits a complex manifold structure of dimension one less than the rank of the
lattice, with holomorphic smooth embedding into the realization. Combined with
`TauCeti.Toric.Fan.isClosed_analyticBoundaryComponent`, this identifies the components as
closed embedded complex hypersurfaces, including at intersections with other components.

The atlas is induced by the coordinate-hyperplane normal form of the toric boundary, in which
the orbit closure of `σ` is the common zero locus of the coordinates of the rays of `σ`, using
`TauCeti.linearSliceChartedSpace`. No choice of a basis of the lattice is required from callers.

## Main declarations

* `TauCeti.Toric.Fan.exists_isManifold_closure_analyticConeOrbit_isSmoothEmbedding`: orbit
  closures are closed embedded complex submanifolds of codimension `dim σ`.
* `TauCeti.Toric.Fan.exists_isManifold_analyticBoundaryComponent_isSmoothEmbedding`: boundary
  components are closed embedded complex hypersurfaces.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2 and 4.1.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- Near each point of the closure of the orbit of a cone `σ` with `k` rays, a holomorphic chart
of the realization flattens the closure onto the zero locus of the last `k` coordinates. -/
private theorem exists_sliceChart_closure_analyticConeOrbit (σ : Φ.cones) {k : ℕ}
    (hk : Nat.card {ρ : Φ.Ray // ρ.toCone ≤ σ} = k) (x : closure (Φ.analyticConeOrbit hΦ σ)) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ (_ : ((Fin (Module.finrank ℤ N - k) → ℂ) × (Fin k → ℂ)) ≃L[ℂ]
          (Fin (Module.finrank ℤ N) → ℂ))
      (e : PartialDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
        𝓘(ℂ, (Fin (Module.finrank ℤ N - k) → ℂ) × (Fin k → ℂ))
        (Φ.analyticRealization hΦ) ((Fin (Module.finrank ℤ N - k) → ℂ) × (Fin k → ℂ)) ω),
      (x : Φ.analyticRealization hΦ) ∈ e.source ∧
        ∀ y ∈ e.source, y ∈ closure (Φ.analyticConeOrbit hΦ σ) ↔ (e y).2 = 0 := by
  classical
  let := Φ.analyticChartedSpace hΦ
  let n := Module.finrank ℤ N
  let r : Fin k ≃ {ρ : Φ.Ray // ρ.toCone ≤ σ} := ((Finite.equivFin _).trans (finCongr hk)).symm
  have hmem (y : Φ.analyticRealization hΦ) : y ∈ closure (Φ.analyticConeOrbit hΦ σ) ↔
      ∀ a, y ∈ Φ.analyticBoundaryComponent hΦ (r a).1 := by
    simp only [← Φ.iInter_analyticBoundaryComponent_eq_closure_analyticConeOrbit hΦ σ,
      mem_iInter]
    exact ⟨fun h a ↦ h _ (r a).2, fun h ρ hρ ↦ by simpa using h (r.symm ⟨ρ, hρ⟩)⟩
  obtain ⟨s, j, e, hx, hs, he⟩ :=
    Φ.exists_partialDiffeomorph_analyticBoundaryComponent_normalForm hΦ x ω
  -- Every ray of `σ` passes through `x`, so the normal form assigns it a coordinate, and the
  -- orbit closure is the common zero locus of these `k` coordinates.
  have hs' (a : Fin k) : (r a).1 ∈ s := (hs _).mp ((hmem x).mp x.2 a)
  let j' : Fin k ↪ Fin n :=
    ⟨fun a ↦ j ⟨(r a).1, hs' a⟩,
      fun a b h ↦ r.injective (Subtype.ext (congrArg (Subtype.val : s → Φ.Ray) (j.injective h)))⟩
  have heS (y) (hy : y ∈ e.source) :
      y ∈ closure (Φ.analyticConeOrbit hΦ σ) ↔ ∀ a, e y (j' a) = 0 := by
    rw [hmem]
    exact forall_congr' fun a ↦ (he y hy (r a).1).trans (exists_prop_of_true (hs' a))
  -- Split the coordinates of `ℂ ^ n` into the `k` coordinates of the rays of `σ`, which become
  -- the transverse coordinates, and the remaining `n - k` coordinates.
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ℂ) ≃L[ℂ] (Fin (n - k) → ℂ) × (Fin k → ℂ),
      ∀ v a, (L v).2 a = v (j' a) := by
    obtain ⟨l, c, hc⟩ := j'.exists_equiv_sum_fin
    obtain rfl : l = n - k := by
      have := Fintype.card_congr c
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    refine ⟨((LinearEquiv.funCongrLeft ℂ ℂ ((Equiv.sumComm _ _).trans c)).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ)).toContinuousLinearEquiv, fun v a ↦ ?_⟩
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply,
      LinearEquiv.sumArrowLequivProdArrow_apply_snd, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr, hc]
  let D : PartialDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, (Fin (n - k) → ℂ) × (Fin k → ℂ))
      (Fin n → ℂ) ((Fin (n - k) → ℂ) × (Fin k → ℂ)) ω :=
    PartialDiffeomorph.ofOpenPartialHomeomorph L.toHomeomorph.toOpenPartialHomeomorph
      (by simpa using L.contDiff.contDiffOn)
      (by simpa using L.symm.contDiff.contDiffOn)
  refine ⟨L.symm, e.trans D, ?_, fun y hy ↦ ?_⟩
  · simpa [D] using hx
  · have hD : ((e.trans D) y).2 = (L (e y)).2 := by
      simp [D, PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv]
    rw [heS y hy.1, hD, funext_iff]
    simp only [hL, Pi.zero_apply]

/-- The closure of the torus orbit of a cone `σ`, on its actual subtype with the subspace
topology, admits a complex manifold structure of dimension `rank N - dim σ` for which the
inclusion is a holomorphic smooth embedding. This closure is the intersection of the boundary
components of the rays of `σ`, so these components meet in a closed embedded complex submanifold
of the expected codimension. -/
theorem exists_isManifold_closure_analyticConeOrbit_isSmoothEmbedding (σ : Φ.cones) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ C : ChartedSpace (Fin (Module.finrank ℤ N -
          Module.finrank ℝ (Submodule.span ℝ (σ.1 : Set V))) → ℂ)
        (closure (Φ.analyticConeOrbit hΦ σ)),
      letI := C
      IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N -
          Module.finrank ℝ (Submodule.span ℝ (σ.1 : Set V))) → ℂ) ω
          (closure (Φ.analyticConeOrbit hΦ σ)) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N -
            Module.finrank ℝ (Submodule.span ℝ (σ.1 : Set V))) → ℂ)
          𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) ω
          (Subtype.val : closure (Φ.analyticConeOrbit hΦ σ) → Φ.analyticRealization hΦ) := by
  let := Φ.analyticChartedSpace hΦ
  have := Φ.isManifold_analyticRealization hΦ ω
  -- The fan rays contained in `σ` are the rays of the regular, hence simplicial, cone `σ`, so
  -- there are exactly `dim σ` of them.
  have hk : Nat.card {ρ : Φ.Ray // ρ.toCone ≤ σ} =
      Module.finrank ℝ (Submodule.span ℝ (σ.1 : Set V)) := by
    rw [Nat.card_congr (Φ.rayEquiv σ)]
    exact (finrank_span_face_eq_card_rays_of_isSimplicial
      (((isRegular_iff.mp hΦ) σ.1 σ.2).isSimplicial Φ.lattice) ⟨σ.1, .refl _⟩).symm
  choose A e hcover hslice using Φ.exists_sliceChart_closure_analyticConeOrbit hΦ σ hk
  let q (x : closure (Φ.analyticConeOrbit hΦ σ)) := (e x).toOpenPartialHomeomorph
  have hq (x) : IsSliceChart (q x) (univ ×ˢ {0}) (closure (Φ.analyticConeOrbit hΦ σ)) := by
    apply isSliceChart_iff.2
    intro y hy
    simpa only [q, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and] using hslice x y hy
  refine ⟨linearSliceChartedSpace q hq hcover, ?_, ?_⟩
  · exact isManifold_linearSliceChartedSpace q hq
      (fun x z hz ↦ (e x).contMDiffOn.contMDiffAt ((e x).open_source.mem_nhds hz))
      (fun x z hz ↦ (e x).symm.contMDiffOn.contMDiffAt ((e x).open_target.mem_nhds hz)) hcover
  · exact isSmoothEmbedding_subtypeVal_linearSliceChartedSpace q hq A
      (fun x ↦ (e x).contMDiffOn) (fun x ↦ (e x).symm.contMDiffOn) hcover

/-- Each invariant boundary component, on its actual subtype with the subspace topology, admits
a complex manifold structure of dimension `rank N - 1` for which the inclusion is a holomorphic
smooth embedding. This includes points where several boundary components intersect. -/
theorem exists_isManifold_analyticBoundaryComponent_isSmoothEmbedding (ρ : Φ.Ray) :
    letI := Φ.analyticChartedSpace hΦ
    ∃ C : ChartedSpace (Fin (Module.finrank ℤ N - 1) → ℂ)
        (Φ.analyticBoundaryComponent hΦ ρ),
      letI := C
      IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ) ω
          (Φ.analyticBoundaryComponent hΦ ρ) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (Module.finrank ℤ N - 1) → ℂ)
          𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) ω
          (Subtype.val : Φ.analyticBoundaryComponent hΦ ρ → Φ.analyticRealization hΦ) := by
  have h := Φ.exists_isManifold_closure_analyticConeOrbit_isSmoothEmbedding hΦ ρ.toCone
  rwa [Ray.finrank_span, ← analyticBoundaryComponent_def] at h

end TauCeti.Toric.Fan
