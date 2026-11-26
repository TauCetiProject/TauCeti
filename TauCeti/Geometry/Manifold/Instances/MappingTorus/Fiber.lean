/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Submersion
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The fibres of a smooth mapping torus

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a `C^n` diffeomorphism, `n ≥ 1`, of a locally compact Hausdorff
manifold modelled on a finite-dimensional space with boundaryless model, and let
`p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]`, be the projection of its smooth mapping torus
`Y_φ = (ℝ × M) / ((t + 1, x) ∼ (t, φ x))` to the circle. Since `p` is a submersion, every point
`θ` of the circle is a regular value, and the fibre `p⁻¹ θ = {y // p y = θ}` carries the
regular-fibre atlas (`TauCeti.SmoothMappingTorus.fiberChartedSpace`), for which it is an embedded
`C^n` submanifold of `Y_φ` whose tangent spaces are the vertical spaces `ker dp`.

This file identifies these fibres with `M`, and computes the change of identification and the
return map of the suspension flow.

* For a lift `t ∈ ℝ` of `θ`, the fibre inclusion `ι_t : x ↦ [t, x]` is a `C^n` diffeomorphism of
  `M` onto `p⁻¹ θ` (`TauCeti.SmoothMappingTorus.fiberDiffeomorph`).
* Two lifts of `θ` differ by an integer `k`, and the identifications differ by the iterate `φ ^ k`:
  `ι_(t + k) = ι_t ∘ φ ^ k`, so `ι_t⁻¹ ∘ ι_(t + k) = φ ^ k` and `ι_(t + k)⁻¹ ∘ ι_t = φ ^ (-k)`
  (`TauCeti.SmoothMappingTorus.fiberDiffeomorph_trans_symm_fiberDiffeomorph_add_intCast`).
* The time-`s` map of the suspension flow `[t, x] ↦ [t + s, x]` restricts to a `C^n`
  diffeomorphism `p⁻¹ θ → p⁻¹ (θ + s)` (`TauCeti.SmoothMappingTorus.fiberFlow`), carrying `ι_t` to
  `ι_(t + s)`. For `s = 1` the fibre returns to itself, and in the chart `ι_t` the time-one map is
  `φ`: `ι_t⁻¹ ∘ flow_1 ∘ ι_t = φ`
  (`TauCeti.SmoothMappingTorus.fiberDiffeomorph_trans_fiberFlow_one_trans_symm`). So `φ` is the
  first-return map of the suspension flow to any fibre, read in any chosen lift.

No compactness of `M` is needed.

## Main definitions

* `TauCeti.SmoothMappingTorus.fiberChartedSpace`: the regular-fibre atlas on a fibre of `p`.
* `TauCeti.SmoothMappingTorus.fiberDiffeomorph`: the identification of `M` with the fibre over
  the class of `t`, by `x ↦ [t, x]`.
* `TauCeti.SmoothMappingTorus.fiberFlow`: the restriction of the time-`s` map of the suspension
  flow to a diffeomorphism between fibres.

## Main results

* `TauCeti.SmoothMappingTorus.isRegularValue_proj`: every point of the circle is a regular value
  of the projection.
* `TauCeti.SmoothMappingTorus.range_mfderiv_coe_fiber`: the tangent spaces of a fibre are the
  vertical spaces `ker dp`.
* `TauCeti.SmoothMappingTorus.fiberDiffeomorph_add_intCast`,
  `TauCeti.SmoothMappingTorus.exists_fiberDiffeomorph_trans_symm_fiberDiffeomorph_eq_zpow`:
  the change of lift is an iterate of `φ`.
* `TauCeti.SmoothMappingTorus.fiberDiffeomorph_trans_fiberFlow`: the flow carries the inclusion
  at time `t` to the inclusion at time `t + s`.
* `TauCeti.SmoothMappingTorus.fiberDiffeomorph_trans_fiberFlow_one_trans_symm`: the first-return
  map of the suspension flow to a fibre is `φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 5 (regular level sets) and Chapter 21 (quotients by
  discrete group actions).
-/

public noncomputable section

open Function Manifold Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M] {n : ℕ∞ω} [IsManifold I n M] (φ : M ≃ₘ^n⟮I, I⟯ M)

/-- Every point of the circle is a regular value of the projection `[t, x] ↦ [t]` of a `C^n`
mapping torus, `n ≥ 1`, since this projection is a submersion. -/
theorem isRegularValue_proj (hn : 1 ≤ n) (θ : UnitAddCircle) :
    IsRegularValue (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) θ :=
  isRegularValue_iff.2 fun y _ ↦ isRegularPoint_iff.2
    ((isSubmersion_proj φ).surjective_mfderiv (ENat.one_le_iff_ne_zero_withTop.mp hn) y)

variable [FiniteDimensional ℝ E] [I.Boundaryless] (hn : 1 ≤ n)

/-- The model space of the fibres of the mapping torus, of dimension `dim M`. -/
local notation "F" => Fin (finrank ℝ (ℝ × E) - finrank ℝ ℝ) → ℝ

/-! ### The regular-fibre atlas -/

/-- The regular-fibre atlas on the fibre `{y // p y = θ}` of the projection `p : Y_φ → ℝ / ℤ` of
a `C^n` mapping torus, `n ≥ 1`. It keeps the subspace topology and is not a global instance. -/
@[instance_reducible]
def fiberChartedSpace (θ : UnitAddCircle) :
    ChartedSpace F {y : SmoothMappingTorus φ // proj φ y = θ} :=
  regularFiberChartedSpace hn (contMDiff_proj φ) BoundarylessManifold.isInteriorPoint
    (isRegularValue_proj φ hn θ)

/-- The fibre atlas is the regular-fibre atlas of the projection. This equation allows reuse of
the regular-fibre API without unfolding the fibre atlas. -/
theorem fiberChartedSpace_eq_regularFiberChartedSpace (θ : UnitAddCircle) :
    fiberChartedSpace φ hn θ =
      regularFiberChartedSpace hn (contMDiff_proj φ) BoundarylessManifold.isInteriorPoint
        (isRegularValue_proj φ hn θ) :=
  (rfl)

/-- A fibre of the mapping torus, with its regular-fibre atlas, is a `C^n` manifold. -/
theorem isManifold_fiber (θ : UnitAddCircle) :
    letI := fiberChartedSpace φ hn θ
    IsManifold 𝓘(ℝ, F) n {y : SmoothMappingTorus φ // proj φ y = θ} :=
  isManifold_regularFiber hn (contMDiff_proj φ) BoundarylessManifold.isInteriorPoint
    (isRegularValue_proj φ hn θ)

/-- The inclusion of a fibre of the mapping torus, with its regular-fibre atlas, is a `C^n`
smooth embedding. -/
theorem isSmoothEmbedding_coe_fiber (θ : UnitAddCircle) :
    letI := fiberChartedSpace φ hn θ
    IsSmoothEmbedding 𝓘(ℝ, F) (𝓘(ℝ).prod I) n
      (Subtype.val : {y : SmoothMappingTorus φ // proj φ y = θ} → SmoothMappingTorus φ) :=
  isSmoothEmbedding_coe_regularFiber hn (contMDiff_proj φ) BoundarylessManifold.isInteriorPoint
    (isRegularValue_proj φ hn θ)

/-- The tangent spaces of a fibre of the mapping torus are the vertical spaces: the tangent image
of the fibre inclusion at `y` is the kernel of the differential of the projection at `y`. -/
theorem range_mfderiv_coe_fiber (θ : UnitAddCircle) :
    letI := fiberChartedSpace φ hn θ
    ∀ y : {y : SmoothMappingTorus φ // proj φ y = θ},
      (mfderiv 𝓘(ℝ, F) (𝓘(ℝ).prod I) Subtype.val y).range =
        (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y.val).ker :=
  range_mfderiv_coe_regularFiber hn (contMDiff_proj φ) BoundarylessManifold.isInteriorPoint
    (isRegularValue_proj φ hn θ)

/-- A map into a fibre of the mapping torus is `C^n` exactly when it is `C^n` as a map into the
mapping torus. -/
private theorem contMDiff_fiber_iff {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    {θ : UnitAddCircle} {f : N → {y : SmoothMappingTorus φ // proj φ y = θ}} :
    letI := fiberChartedSpace φ hn θ
    ContMDiff I' 𝓘(ℝ, F) n f ↔ ContMDiff I' (𝓘(ℝ).prod I) n fun z ↦ (f z).val := by
  let := fiberChartedSpace φ hn θ
  exact (isSmoothEmbedding_coe_fiber φ hn θ).contMDiff_iff_comp

/-! ### The identification of the fibres with `M` -/

variable {θ θ' : UnitAddCircle}

omit [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [FiniteDimensional ℝ E]
  [I.Boundaryless] in
/-- The fibre inclusion `x ↦ [t, x]` is a bijection of `M` onto the fibre over the class of `t`. -/
private theorem bijective_mk_fiber (t : ℝ) (ht : (t : UnitAddCircle) = θ) :
    Bijective fun x : M ↦
      (⟨mk φ t x, (proj_mk φ t x).trans ht⟩ : {y : SmoothMappingTorus φ // proj φ y = θ}) := by
  refine ⟨fun x x' h ↦ mk_injective φ t (congrArg Subtype.val h), fun y ↦ ?_⟩
  have hy : y.val ∈ Set.range (mk φ t) := by
    rw [range_mk, Set.mem_preimage, Set.mem_singleton_iff, y.property, ht]
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- **The fibres of the mapping torus.** For a lift `t ∈ ℝ` of a point `θ` of the circle, the fibre
inclusion `x ↦ [t, x]` is a `C^n` diffeomorphism of `M` onto the fibre over `θ`, with its
regular-fibre atlas. -/
def fiberDiffeomorph (t : ℝ) (ht : (t : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    M ≃ₘ^n⟮I, 𝓘(ℝ, F)⟯ {y : SmoothMappingTorus φ // proj φ y = θ} := by
  letI := fiberChartedSpace φ hn θ
  let e := Equiv.ofBijective _ (bijective_mk_fiber φ t ht)
  have he : ∀ y, mk φ t (e.symm y) = y.val := fun y ↦
    congrArg Subtype.val (e.apply_symm_apply y)
  refine { e with
    contMDiff_toFun := (contMDiff_fiber_iff φ hn).2 (contMDiff_mk φ t)
    contMDiff_invFun := ?_ }
  have he' : mk φ t ∘ e.symm = Subtype.val := funext he
  rw [(isSmoothEmbedding_mk φ t).contMDiff_iff_comp, he']
  exact (isSmoothEmbedding_coe_fiber φ hn θ).contMDiff

/-- The identification `ι_t` of `M` with a fibre sends `x` to `[t, x]`. -/
@[simp]
theorem coe_fiberDiffeomorph_apply (t : ℝ) (ht : (t : UnitAddCircle) = θ) (x : M) :
    letI := fiberChartedSpace φ hn θ
    (fiberDiffeomorph φ hn t ht x : SmoothMappingTorus φ) = mk φ t x :=
  (rfl)

/-- The inverse of `ι_t` sends a point `y` of the fibre to the point `x` of `M` with
`[t, x] = y`. -/
@[simp]
theorem mk_fiberDiffeomorph_symm_apply (t : ℝ) (ht : (t : UnitAddCircle) = θ)
    (y : {y : SmoothMappingTorus φ // proj φ y = θ}) :
    letI := fiberChartedSpace φ hn θ
    mk φ t ((fiberDiffeomorph φ hn t ht).symm y) = y := by
  let := fiberChartedSpace φ hn θ
  rw [← coe_fiberDiffeomorph_apply φ hn t ht, Diffeomorph.apply_symm_apply]

/-- **Change of lift.** The inclusions of `M` as the fibre over `θ` for the lifts `t` and `t + k`
differ by the iterate `φ ^ k`: `ι_(t + k) = ι_t ∘ φ ^ k`. -/
theorem fiberDiffeomorph_add_intCast (t : ℝ) (k : ℤ) (ht : (t : UnitAddCircle) = θ)
    (htk : ((t + k : ℝ) : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    fiberDiffeomorph φ hn (t + k) htk = (φ ^ k).trans (fiberDiffeomorph φ hn t ht) := by
  let := fiberChartedSpace φ hn θ
  ext x
  simp

/-- **Change of lift.** For the lifts `t` and `t + k` of `θ`, the transition `ι_t⁻¹ ∘ ι_(t + k)`
between the two identifications of `M` with the fibre over `θ` is the iterate `φ ^ k`. -/
theorem fiberDiffeomorph_trans_symm_fiberDiffeomorph_add_intCast (t : ℝ) (k : ℤ)
    (ht : (t : UnitAddCircle) = θ) (htk : ((t + k : ℝ) : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    (fiberDiffeomorph φ hn (t + k) htk).trans (fiberDiffeomorph φ hn t ht).symm = φ ^ k := by
  let := fiberChartedSpace φ hn θ
  ext x
  simp [fiberDiffeomorph_add_intCast φ hn t k ht htk]

/-- **Change of lift.** Any two lifts `t` and `t'` of `θ` differ by an integer `k`, and the
transition `ι_t⁻¹ ∘ ι_t'` between the two identifications of `M` with the fibre over `θ` is the
iterate `φ ^ k`. -/
theorem exists_fiberDiffeomorph_trans_symm_fiberDiffeomorph_eq_zpow (t t' : ℝ)
    (ht : (t : UnitAddCircle) = θ) (ht' : (t' : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    ∃ k : ℤ, t' = t + k ∧
      (fiberDiffeomorph φ hn t' ht').trans (fiberDiffeomorph φ hn t ht).symm = φ ^ k := by
  have h0 : ((t' - t : ℝ) : UnitAddCircle) = 0 := by rw [AddCircle.coe_sub, ht, ht', sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 h0
  obtain rfl : t' = t + k := by
    rw [zsmul_eq_mul, mul_one] at hk
    linarith
  exact ⟨k, rfl, fiberDiffeomorph_trans_symm_fiberDiffeomorph_add_intCast φ hn t k ht ht'⟩

/-! ### The suspension flow between fibres -/

/-- The time-`s` map of the suspension flow, restricted to a `C^n` diffeomorphism from the fibre
over `θ` to the fibre over `θ' = θ + s`. -/
def fiberFlow (s : ℝ) (h : θ + s = θ') :
    letI := fiberChartedSpace φ hn θ
    letI := fiberChartedSpace φ hn θ'
    {y : SmoothMappingTorus φ // proj φ y = θ} ≃ₘ^n⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯
      {y : SmoothMappingTorus φ // proj φ y = θ'} := by
  letI := fiberChartedSpace φ hn θ
  letI := fiberChartedSpace φ hn θ'
  have hs : θ' + ((-s : ℝ) : UnitAddCircle) = θ := by
    rw [← h, AddCircle.coe_neg, add_neg_cancel_right]
  exact {
    toFun y := ⟨flow φ s y, by rw [proj_flow, y.property, h]⟩
    invFun y := ⟨flow φ (-s) y, by rw [proj_flow, y.property, hs]⟩
    left_inv y := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    right_inv y := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
    contMDiff_toFun := (contMDiff_fiber_iff φ hn).2 <|
      (contMDiff_flow φ s).comp (isSmoothEmbedding_coe_fiber φ hn θ).contMDiff
    contMDiff_invFun := (contMDiff_fiber_iff φ hn).2 <|
      (contMDiff_flow φ (-s)).comp (isSmoothEmbedding_coe_fiber φ hn θ').contMDiff }

/-- The restricted flow acts on the points of the fibre as the suspension flow does. -/
@[simp]
theorem coe_fiberFlow_apply (s : ℝ) (h : θ + s = θ')
    (y : {y : SmoothMappingTorus φ // proj φ y = θ}) :
    letI := fiberChartedSpace φ hn θ
    letI := fiberChartedSpace φ hn θ'
    (fiberFlow φ hn s h y : SmoothMappingTorus φ) = flow φ s y :=
  (rfl)

/-- The inverse of the restricted time-`s` map is the time-`(-s)` map of the suspension flow. -/
@[simp]
theorem coe_fiberFlow_symm_apply (s : ℝ) (h : θ + s = θ')
    (y : {y : SmoothMappingTorus φ // proj φ y = θ'}) :
    letI := fiberChartedSpace φ hn θ
    letI := fiberChartedSpace φ hn θ'
    ((fiberFlow φ hn s h).symm y : SmoothMappingTorus φ) = flow φ (-s) y :=
  (rfl)

/-- The restricted flows compose as the flow does: following the time-`s` map from `θ` by the
time-`r` map from `θ + s` is the time-`(s + r)` map. -/
theorem fiberFlow_trans_fiberFlow {θ'' : UnitAddCircle} (s r : ℝ) (h : θ + s = θ')
    (h' : θ' + r = θ'') (h'' : θ + ((s + r : ℝ) : UnitAddCircle) = θ'') :
    letI := fiberChartedSpace φ hn θ
    letI := fiberChartedSpace φ hn θ'
    letI := fiberChartedSpace φ hn θ''
    (fiberFlow φ hn s h).trans (fiberFlow φ hn r h') = fiberFlow φ hn (s + r) h'' := by
  let := fiberChartedSpace φ hn θ
  let := fiberChartedSpace φ hn θ'
  let := fiberChartedSpace φ hn θ''
  ext y
  simp only [Diffeomorph.coe_trans, comp_apply, coe_fiberFlow_apply]
  rw [add_comm, Flow.map_add]

/-- The suspension flow carries the inclusion of `M` at time `t` to the inclusion at time `t + s`:
`flow_s ∘ ι_t = ι_(t + s)`. -/
theorem fiberDiffeomorph_trans_fiberFlow (t s : ℝ) (ht : (t : UnitAddCircle) = θ)
    (h : θ + s = θ') (hts : ((t + s : ℝ) : UnitAddCircle) = θ') :
    letI := fiberChartedSpace φ hn θ
    letI := fiberChartedSpace φ hn θ'
    (fiberDiffeomorph φ hn t ht).trans (fiberFlow φ hn s h) =
      fiberDiffeomorph φ hn (t + s) hts := by
  let := fiberChartedSpace φ hn θ
  let := fiberChartedSpace φ hn θ'
  ext x
  simp

/-- The time-`k` map of the suspension flow, for an integer `k`, returns each fibre to itself, and
in the identification `ι_t` of `M` with the fibre it is the iterate `φ ^ k`:
`flow_k ∘ ι_t = ι_t ∘ φ ^ k`. -/
theorem fiberDiffeomorph_trans_fiberFlow_intCast (t : ℝ) (k : ℤ) (ht : (t : UnitAddCircle) = θ)
    (h : θ + ((k : ℝ) : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    (fiberDiffeomorph φ hn t ht).trans (fiberFlow φ hn k h) =
      (φ ^ k).trans (fiberDiffeomorph φ hn t ht) := by
  let := fiberChartedSpace φ hn θ
  ext x
  simp

/-- **The first-return map of the suspension flow is `φ`.** The time-one map of the suspension
flow returns the fibre over `θ` to itself, and in the identification `ι_t` of `M` with that fibre,
for any lift `t` of `θ`, it is `φ`: `ι_t⁻¹ ∘ flow_1 ∘ ι_t = φ`. -/
theorem fiberDiffeomorph_trans_fiberFlow_one_trans_symm (t : ℝ) (ht : (t : UnitAddCircle) = θ)
    (h : θ + ((1 : ℝ) : UnitAddCircle) = θ) :
    letI := fiberChartedSpace φ hn θ
    (fiberDiffeomorph φ hn t ht).trans
      ((fiberFlow φ hn 1 h).trans (fiberDiffeomorph φ hn t ht).symm) = φ := by
  let := fiberChartedSpace φ hn θ
  ext x
  apply (fiberDiffeomorph φ hn t ht).injective
  ext
  simp

end TauCeti.SmoothMappingTorus
