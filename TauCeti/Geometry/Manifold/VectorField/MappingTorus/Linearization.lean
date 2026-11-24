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
`d(ι_(t + k)) v = d(ι_t) (dφ^k v)` (`TauCeti.SmoothMappingTorus.mfderiv_mk_add_intCast`). So at an
integer time `k` the vertical block of the linearized flow, read in the fibre at height `t`, is
the differential of `φ^k`: `dΦ_k (d(ι_t) v) = d(ι_t) (dφ^k v)`
(`TauCeti.SmoothMappingTorus.mfderiv_flow_intCast_mfderiv_mk`). At a periodic point `x` of period
`d`, the time-`d` map fixes `[t, x]`, and its linearization on `V` is the linearized return map of
the closed orbit through `[t, x]`. It has no eigenvalue `1` exactly when `x` is a nondegenerate
fixed point of `φ^d` (`TauCeti.SmoothMappingTorus.isNondegenerateFixedPt_iterate_iff`). The flow
also preserves the time form and every fiber form, `Φ_s^* dt = dt` and `Φ_s^* σ_v = σ_v`
(`TauCeti.SmoothMappingTorus.mpullback_flow_timeForm`,
`TauCeti.SmoothMappingTorus.mpullback_flow_fiberForm`), so the linearized return map preserves the
restriction of `σ_v` to `V`. No compactness of `M` is needed.

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
* `TauCeti.SmoothMappingTorus.isNondegenerateFixedPt_iterate_iff`: the closed orbit through a
  periodic point `x` of period `d` has a vertical linearized return map without eigenvalue `1`
  exactly when `x` is a nondegenerate fixed point of `φ^d`.
* `TauCeti.SmoothMappingTorus.mpullback_flow_timeForm`,
  `TauCeti.SmoothMappingTorus.mpullback_flow_fiberForm`,
  `TauCeti.SmoothMappingTorus.eval₂_fiberForm_mfderiv_flow`: the flow preserves the time form and
  every fiber form.

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

/-! ### Seam identities for the differential of the quotient map -/

/-- The seam identity `[t + k, x] = [t, φ^k x]` for the differentials of the fibre inclusions:
`d(ι_(t + k))_x = d(ι_t)_(φ^k x) ∘ dφ^k_x`. -/
theorem mfderiv_mk_add_intCast (t : ℝ) (k : ℤ) (x : M) (v : TangentSpace I x) :
    mfderiv I (𝓘(ℝ).prod I) (mk φ (t + k)) x v =
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) ((φ ^ k) x) (mfderiv I I (φ ^ k) x v) := by
  have h : mk φ (t + k) = mk φ t ∘ (φ ^ k) := funext fun y ↦ mk_add_intCast φ t k y
  rw [h]
  exact mfderiv_comp_apply_of_eq x ((contMDiff_mk φ t _).mdifferentiableAt (by simp))
    ((φ ^ k).mdifferentiable (by simp) x) rfl v

/-- The seam identity `[t + j, x] = [t, φ^[j] x]` for the differentials of the fibre inclusions,
for a natural number `j`. -/
theorem mfderiv_mk_add_natCast (t : ℝ) (j : ℕ) (x : M) (v : TangentSpace I x) :
    mfderiv I (𝓘(ℝ).prod I) (mk φ (t + j)) x v =
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) ((⇑φ)^[j] x) (mfderiv I I (⇑φ)^[j] x v) := by
  have h := mfderiv_mk_add_intCast φ t j x v
  rwa [Int.cast_natCast, zpow_natCast, Diffeomorph.coe_pow] at h

/-- The seam identity `[t + 1, x] = [t, φ x]` for the differentials of the fibre inclusions:
`d(ι_(t + 1))_x = d(ι_t)_(φ x) ∘ dφ_x`. -/
theorem mfderiv_mk_add_one (t : ℝ) (x : M) (v : TangentSpace I x) :
    mfderiv I (𝓘(ℝ).prod I) (mk φ (t + 1)) x v =
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) (φ x) (mfderiv I I φ x v) := by
  have h := mfderiv_mk_add_natCast φ t 1 x v
  rwa [Nat.cast_one, Function.iterate_one] at h

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
  have hcomm : flow φ s ∘ uncurry (mk φ) = uncurry (mk φ) ∘ Prod.map (· + s) id :=
    funext fun p ↦ flow_mk φ s p.1 p.2
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
    ((contMDiff_uncurry_mk φ _).mdifferentiableAt (by simp)) rfl, hcomm,
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
  have hcomm : proj φ ∘ flow φ s = (· + (s : UnitAddCircle)) ∘ proj φ :=
    funext fun z ↦ proj_flow φ s z
  have hproj : MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y :=
    (contMDiff_proj φ y).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply_of_eq y ((contMDiff_proj φ _).mdifferentiableAt (by simp))
    ((contMDiff_flow φ s y).mdifferentiableAt (by simp)) rfl, hcomm,
    mfderiv_comp_apply_of_eq y (y := proj φ y)
      ((mdifferentiable_add_right (I := 𝓘(ℝ)) (a := (s : UnitAddCircle))) _)
      hproj rfl, AddCircle.mfderiv_add_right]
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
theorem isNondegenerateFixedPt_iterate_iff (t : ℝ) {d : ℕ} {x : M} (hx : IsPeriodicPt φ d x) :
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

/-! ### Invariant forms -/

/-- The suspension flow preserves the time form: `Φ_s^* dt = dt`. -/
@[simp]
theorem mpullback_flow_timeForm (s : ℝ) :
    SmoothForm.mpullback (flow φ s) (contMDiff_flow φ s) (timeForm φ) = timeForm φ := by
  have hcomm : proj φ ∘ flow φ s = (· + (s : UnitAddCircle)) ∘ proj φ :=
    funext fun z ↦ proj_flow φ s z
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, timeForm_def, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_flow φ s).mdifferentiable (by simp))
      ((contMDiff_proj φ).mdifferentiable (by simp)), hcomm,
    mpullback_comp ((contMDiff_proj φ).mdifferentiable (by simp)) mdifferentiable_add_right,
    AddCircle.mpullback_add_right_timeForm]

/-- The suspension flow preserves every fiber form: `Φ_s^* σ_v = σ_v`. -/
@[simp]
theorem mpullback_flow_fiberForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {σ : SmoothForm I M F k} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ} (s : ℝ) :
    SmoothForm.mpullback (flow φ s) (contMDiff_flow φ s) (fiberForm φ σ hσ) =
      fiberForm φ σ hσ := by
  have hcomm : flow φ s ∘ uncurry (mk φ) = uncurry (mk φ) ∘ Prod.map (· + s) id :=
    funext fun p ↦ flow_mk φ s p.1 p.2
  have hadd : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (· + s) := (contDiff_id.add contDiff_const).contMDiff
  have htr : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ (Prod.map (· + s) id : ℝ × M → ℝ × M) :=
    hadd.prodMap contMDiff_id
  rw [eq_fiberForm_iff, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hcomm]
  rw [SmoothForm.mpullback_comp _ _ htr (contMDiff_uncurry_mk φ), LinearMap.comp_apply,
    mpullback_uncurry_mk_fiberForm, SmoothForm.mpullback_prodMap_mpullback_snd hadd contMDiff_id,
    SmoothForm.mpullback_id, LinearMap.id_apply]

/-- The linearized suspension flow preserves the fiber form of every two-form `σ` preserved by `φ`:
`σ_v(dΦ_s w, dΦ_s w') = σ_v(w, w')`. -/
theorem eval₂_fiberForm_mfderiv_flow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {σ : SmoothForm I M F 2} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ} (s : ℝ)
    (y : SmoothMappingTorus φ) (w w' : TangentSpace (𝓘(ℝ).prod I) y) :
    (fiberForm φ σ hσ).eval₂ (flow φ s y)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) y w)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (flow φ s) y w') =
      (fiberForm φ σ hσ).eval₂ y w w' := by
  have h := congrArg (fun β ↦ SmoothBundleForm.eval₂ β y w w')
    (mpullback_flow_fiberForm φ (hσ := hσ) s)
  simpa only [SmoothForm.eval₂_mpullback] using h

end SmoothMappingTorus

end TauCeti
