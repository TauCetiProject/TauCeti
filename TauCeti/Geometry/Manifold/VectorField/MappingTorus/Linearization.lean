/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus

/-!
# The linearized suspension flow of a mapping torus

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with quotient map
`q : (t, x) ↦ [t, x]`, projection `p : Y_φ → ℝ / ℤ`, suspension flow `Φ_s : [t, x] ↦ [t + s, x]`
and vector field `T = ∂_t`. This file computes the differential of the suspension flow, the
linearized flow, in the splitting `T Y_φ = ℝ T ⊕ V` with `V = ker dp`.

At `[t, x]` every tangent vector is `dq (b, v) = b T + d(ι_t) v`, where `ι_t : x ↦ [t, x]` is the
inclusion of the fibre at height `t` (`TauCeti.SmoothMappingTorus.mfderiv_uncurry_mk_apply`). On
the cover `ℝ × M` the flow is the translation `(t, x) ↦ (t + s, x)`, whose differential is the
identity, so `dΦ_s (dq_(t, x) w) = dq_(t + s, x) w`
(`TauCeti.SmoothMappingTorus.mfderiv_flow_mfderiv_uncurry_mk`). Hence the linearized flow is block
diagonal:

* it fixes the field, `dΦ_s T = T` (`TauCeti.SmoothMappingTorus.mfderiv_flow_timeVectorField`);
* it preserves `dp`, so it maps `V` to `V`
  (`TauCeti.SmoothMappingTorus.mfderiv_flow_mem_ker_mfderiv_proj_iff`);
* on `V` it moves fibre vectors along the fibres, `dΦ_s (d(ι_t) v) = d(ι_(t + s)) v`
  (`TauCeti.SmoothMappingTorus.mfderiv_flow_mfderiv_mk`).

The seam identity `[t + k, x] = [t, φ^k x]` differentiates to
`d(ι_(t + k)) v = d(ι_t) (dφ^k v)` (`TauCeti.SmoothMappingTorus.mfderiv_mk_add_intCast`, in
`TauCeti.Geometry.Manifold.Instances.MappingTorus`). So at an integer time `k` the vertical block
of the linearized flow, read in the fibre at height `t`, is the differential of `φ^k`:
`dΦ_k (d(ι_t) v) = d(ι_t) (dφ^k v)`
(`TauCeti.SmoothMappingTorus.mfderiv_flow_intCast_mfderiv_mk`). At a periodic point `x` of period
`d`, the time-`d` map fixes `[t, x]`, and its linearization on `V` is the linearized return map of
the closed orbit through `[t, x]`. It has no eigenvalue `1` exactly when `x` is a nondegenerate
fixed point of `φ^d` (`TauCeti.SmoothMappingTorus.isNondegenerateFixedPt_iterate_iff_mfderiv_flow`).
The flow also preserves the time form and every fiber form, `Φ_s^* dt = dt` and `Φ_s^* σ_v = σ_v`
(`TauCeti.SmoothMappingTorus.mpullback_flow_timeForm`,
`TauCeti.SmoothMappingTorus.mpullback_flow_fiberForm`, in
`TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus`), so the linearized return map preserves
the restriction of `σ_v` to `V`. No compactness of `M` is needed.

## Main results

* `TauCeti.SmoothMappingTorus.mfderiv_uncurry_mk_apply`: `dq (b, v) = b T + d(ι_t) v`.
* `TauCeti.SmoothMappingTorus.mfderiv_uncurry_mk_add_intCast`: the tangent seam identity
  `dq_(t + k, x) (b, v) = dq_(t, φ^k x) (b, dφ^k v)`.
* `TauCeti.SmoothMappingTorus.mfderiv_flow_mfderiv_uncurry_mk`: the flow lifts to the translation
  of the cover, `dΦ_s ∘ dq_(t, x) = dq_(t + s, x)`.
* `TauCeti.SmoothMappingTorus.mfderiv_flow_timeVectorField`: `dΦ_s T = T`.
* `TauCeti.SmoothMappingTorus.mfderiv_proj_mfderiv_flow`,
  `TauCeti.SmoothMappingTorus.mfderiv_flow_mem_ker_mfderiv_proj_iff`: `dp ∘ dΦ_s = dp`, so `dΦ_s`
  preserves the vertical tangent spaces.
* `TauCeti.SmoothMappingTorus.mfderiv_flow_mfderiv_mk`,
  `TauCeti.SmoothMappingTorus.mfderiv_flow_intCast_mfderiv_mk`: the vertical block of the
  linearized flow, and its value `dφ^k` at integer times.
* `TauCeti.SmoothMappingTorus.isNondegenerateFixedPt_iterate_iff_mfderiv_flow`: the closed orbit
  through a periodic point `x` of period `d` has a vertical linearized return map without
  eigenvalue `1` exactly when `x` is a nondegenerate fixed point of `φ^d`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the linearized return map of a closed orbit
  of the suspension flow is the differential of the return map of `φ`).
-/

public section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The differential of the quotient map -/

/-- The differential of the quotient map `q : (t, x) ↦ [t, x]` splits along `T Y_φ = ℝ T ⊕ V`:
`dq (b, v) = b T + d(ι_t) v`, where `ι_t : x ↦ [t, x]` is the inclusion of the fibre at
height `t`. -/
theorem mfderiv_uncurry_mk_apply (t : ℝ) (x : M) (b : ℝ) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
        ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)) =
      b • timeVectorField φ (mk φ t x) + mfderiv I (𝓘(ℝ).prod I) (mk φ t) x v := by
  -- The differential of `q` read on pairs `(b, v)`, a linear map on `T_t ℝ × T_x M`.
  let L := (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)).comp
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)).symm.toContinuousLinearMap
  have hL (a : TangentSpace 𝓘(ℝ) t × TangentSpace I x) :
      L a = mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
        ((Manifold.tangentSpaceProdEquiv (t, x)).symm a) := (rfl)
  have hsplit : ((b, v) : TangentSpace 𝓘(ℝ) t × TangentSpace I x) =
      b • ((1, 0) : TangentSpace 𝓘(ℝ) t × TangentSpace I x) + (0, v) := by
    refine Prod.ext ?_ (by simp)
    simp only [Prod.fst_add, Prod.smul_fst, add_zero]
    -- Tangent vectors of `ℝ` are real numbers, on which `b • 1` is `b * 1`.
    exact (mul_one b).symm
  rw [timeVectorField_mk, mfderiv_mk_apply φ (by simp), ← hL, ← hL, ← hL, hsplit, map_add,
    map_smul]
  -- `L` is a `let`-bound name for the composite, so `L a` is `dq` applied to the vector of
  -- `T_(t, x) (ℝ × M)` with components `a`, by definition.
  rfl

/-- The seam identity for the differential of the quotient map `q : (t, x) ↦ [t, x]`:
`dq_(t + k, x) (b, v) = dq_(t, φ^k x) (b, dφ^k_x v)`. -/
theorem mfderiv_uncurry_mk_add_intCast (t : ℝ) (k : ℤ) (x : M) (b : ℝ) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t + k, x)
        ((Manifold.tangentSpaceProdEquiv (t + k, x)).symm (b, v)) =
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, (φ ^ k) x)
        ((Manifold.tangentSpaceProdEquiv (t, (φ ^ k) x)).symm (b, mfderiv I I (φ ^ k) x v)) := by
  rw [mfderiv_uncurry_mk_apply, mfderiv_uncurry_mk_apply, mfderiv_mk_add_intCast, mk_add_intCast]

/-! ### The linearized flow -/

/-- The suspension flow lifts to the translation `(t, x) ↦ (t + s, x)` of `ℝ × M`, whose
differential is the identity: `dΦ_s (dq_(t, x) (b, v)) = dq_(t + s, x) (b, v)`. -/
theorem mfderiv_flow_mfderiv_uncurry_mk (s t : ℝ) (x : M) (b : ℝ) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) (mk φ t x)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) =
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t + s, x)
        ((Manifold.tangentSpaceProdEquiv (t + s, x)).symm (b, v)) := by
  have hadd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (· + s) t :=
    (differentiableAt_id.add_const s).mdifferentiableAt
  -- The translation of `ℝ × M` has the identity as differential.
  have htr : mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + s) id) (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)) =
        (Manifold.tangentSpaceProdEquiv (t + s, x)).symm (b, v) := by
    rw [Manifold.mfderiv_prodMap_apply hadd mdifferentiableAt_id, mfderiv_id, mfderiv_eq_fderiv,
      fderiv_add_const, fderiv_fun_id]
    -- The derivative of the identity of `ℝ`, read in the tangent lines of `ℝ`, is the identity.
    rfl
  rw [← mfderiv_comp_apply_of_eq (t, x) (y := mk φ t x)
    ((contMDiff_flow φ s _).mdifferentiableAt (by simp))
    ((contMDiff_uncurry_mk φ _).mdifferentiableAt (by simp)) rfl, flow_comp_uncurry_mk,
    mfderiv_comp_apply_of_eq (t, x) (y := (t + s, x))
      ((contMDiff_uncurry_mk φ _).mdifferentiableAt (by simp))
      (hadd.prodMap mdifferentiableAt_id) rfl, htr]

/-- The linearized suspension flow fixes the field `T`: `dΦ_s T = T`. -/
@[simp]
theorem mfderiv_flow_timeVectorField (s : ℝ) (y : SmoothMappingTorus φ) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) y (timeVectorField φ y) =
      timeVectorField φ (flow φ s y) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  rw [uncurry_apply_pair, flow_mk, timeVectorField_mk, timeVectorField_mk]
  exact mfderiv_flow_mfderiv_uncurry_mk φ s t x 1 0

/-- The linearized suspension flow moves fibre vectors along the fibres:
`dΦ_s (d(ι_t) v) = d(ι_(t + s)) v`, where `ι_t : x ↦ [t, x]`. -/
@[simp]
theorem mfderiv_flow_mfderiv_mk (s t : ℝ) (x : M) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) (mk φ t x)
        (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x v) =
      mfderiv I (𝓘(ℝ).prod I) (mk φ (t + s)) x v := by
  rw [mfderiv_mk_apply φ (by simp), mfderiv_mk_apply φ (by simp)]
  exact mfderiv_flow_mfderiv_uncurry_mk φ s t x 0 v

/-- At an integer time `k`, the linearized suspension flow acts on the fibre at height `t` as the
differential of `φ^k`: `dΦ_k (d(ι_t) v) = d(ι_t) (dφ^k v)`. -/
theorem mfderiv_flow_intCast_mfderiv_mk (k : ℤ) (t : ℝ) (x : M) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ k) (mk φ t x)
        (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x v) =
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) ((φ ^ k) x) (mfderiv I I (φ ^ k) x v) := by
  rw [mfderiv_flow_mfderiv_mk, mfderiv_mk_add_intCast]

/-- The linearized suspension flow preserves the differential of the projection to the circle:
`dp (dΦ_s w) = dp w`. -/
@[simp]
theorem mfderiv_proj_mfderiv_flow (s : ℝ) (y : SmoothMappingTorus φ)
    (w : TangentSpace (𝓘(ℝ).prod I) y) :
    mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (flow φ s y)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) y w) =
      mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y w := by
  rw [← mfderiv_comp_apply_of_eq y ((contMDiff_proj φ _).mdifferentiableAt (by simp))
    ((contMDiff_flow φ s y).mdifferentiableAt (by simp)) rfl, proj_comp_flow,
    mfderiv_comp_apply_of_eq y (y := proj φ y)
      ((mdifferentiable_add_right (I := 𝓘(ℝ)) (a := (s : UnitAddCircle))) _)
      ((contMDiff_proj φ y).mdifferentiableAt (by simp)) rfl, AddCircle.mfderiv_add_right]
  -- The translation of the circle has the identity of `ℝ` as differential.
  rfl

/-- The linearized suspension flow preserves the vertical tangent spaces `V = ker dp`. -/
theorem mfderiv_flow_mem_ker_mfderiv_proj_iff (s : ℝ) (y : SmoothMappingTorus φ)
    (w : TangentSpace (𝓘(ℝ).prod I) y) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) y w ∈
        (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (flow φ s y)).ker ↔
      w ∈ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mfderiv_proj_mfderiv_flow]
  -- The two zeros live in the tangent lines of the circle at different points, both `ℝ`.
  exact Iff.rfl

/-- **The linearized return map of a closed orbit.** Let `x` be a periodic point of `φ` of
period `d`, so that the time-`d` map of the suspension flow fixes `[t, x]`. Its differential
there fixes no nonzero vertical vector exactly when `x` is a nondegenerate fixed point of `φ^d`:
the vertical block of the linearized return map of the closed orbit through `[t, x]` is `dφ^d_x`. -/
theorem isNondegenerateFixedPt_iterate_iff_mfderiv_flow (t : ℝ) {d : ℕ} {x : M}
    (hx : IsPeriodicPt φ d x) :
    IsNondegenerateFixedPt I (⇑φ)^[d] x ↔
      ∀ w ∈ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (mk φ t x)).ker,
        mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ d) (mk φ t x) w = w → w = 0 := by
  have hflow (v : TangentSpace I x) :
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ d) (mk φ t x)
          (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x v) =
        mfderiv I (𝓘(ℝ).prod I) (mk φ t) x (mfderiv I I (⇑φ)^[d] x v) := by
    rw [mfderiv_flow_mfderiv_mk, mfderiv_mk_add_natCast, hx.eq]
  have hinj := injective_mfderiv_mk φ (n := ∞) (by simp) t x
  have hdiff : MDifferentiableAt I I (⇑φ)^[d] x := by
    rw [← Diffeomorph.coe_pow]
    exact (φ ^ d).mdifferentiable (by simp) x
  rw [isNondegenerateFixedPt_iff, ← range_mfderiv_mk]
  refine ⟨fun ⟨_, _, h⟩ w hw hfix ↦ ?_, fun h ↦ ⟨hx, hdiff, fun v hv ↦ hinj ?_⟩⟩
  · obtain ⟨v, rfl⟩ := hw
    rw [ContinuousLinearMap.coe_coe] at hfix ⊢
    rw [hflow] at hfix
    rw [h v (hinj hfix), map_zero]
  · refine (h _ ⟨v, rfl⟩ ?_).trans (map_zero _).symm
    rw [ContinuousLinearMap.coe_coe, hflow, hv]

end SmoothMappingTorus

end TauCeti
