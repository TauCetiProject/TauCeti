/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Analysis.ODE.InwardFlow
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.Boundary.Model
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Flowing the boundary inward

Let `M` be a smooth manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)` and `v` a vector
field on `M` which is smooth near a boundary point `a` and points inward there, in the sense that
`-v a` points outward (`TauCeti.IsOutwardPointing`). Then the integral curves of `v` through the
points near `a` exist forward in time for a uniform positive time `ε`, depend smoothly on the
initial point and time on `U × [0, ε)`, and lie in the interior of `M` at every positive time
(`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`).

Mathlib's existence theorem for integral curves applies only at interior points, where the
coordinate field is defined on an open set of the model vector space. At a boundary point the
coordinate field lives only on the closed half-space. In the preferred chart at `a` the statement
is `TauCeti.ODE.exists_contDiffOn_localFlow_upperHalfSpace`, which extends the field across the
boundary hyperplane and shows that the forward flow of an inward field never leaves the
half-space. The boundary-normal coordinates `TauCeti.euclideanFinConsEquiv` identify the model
half-space of `𝓡∂ (n + 1)` with that of `ℝ × (Fin n → ℝ)`.

Flowing the whole boundary along a global inward field, such as the negative of the outward field
of `TauCeti.exists_isOutwardPointingField`, is the classical construction of a collar.

## Main results

* `TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`: an inward-pointing smooth
  vector field has smooth local forward integral curves through the points near a boundary point,
  which enter the interior at once.
* `TauCeti.exists_contDiffOn_chartFlow_of_isOutwardPointing_neg`: the same flow read in the
  preferred chart at `a`, as the forward part of a smooth local flow defined at negative times too.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.24.
-/

public section

open Bundle Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

open HalfSpaceExtension in
/-- **Local flows of inward-pointing fields on the Euclidean half-space.** The form of
`TauCeti.ODE.exists_contDiffOn_localFlow_upperHalfSpace` for the model half-space
`{x | 0 ≤ x 0}` of `𝓡∂ (n + 1)`: a field `C^(k+1)` on the part of a neighbourhood `s` of `a` in the
half-space, pointing strictly inward at `a`, has a local flow jointly `C^(k+1)` on `U × (-ε, ε)`,
with strictly increasing zeroth coordinate along each curve through `U`, whose forward curves
through points of `U` in the half-space stay in `s` and in the half-space and are integral curves
of the field there. -/
theorem exists_contDiffOn_localFlow_euclideanHalfSpace {n : ℕ} {k : ℕ∞}
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {a : EuclideanSpace ℝ (Fin (n + 1))} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hv : ContDiffOn ℝ (k + 1) v (s ∩ {x | 0 ≤ x 0})) (hs : s ∈ 𝓝 a) (ha : 0 ≤ a 0)
    (hva : 0 < v a 0) :
    ∃ Φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1)), ∃ U ∈ 𝓝 a,
      ∃ ε > 0, ContDiffOn ℝ (k + 1) (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Φ p.1 p.2)
        (U ×ˢ Ioo (-ε) ε) ∧
      (∀ x, Φ x 0 = x) ∧ (∀ x t u, Φ x (t + u) = Φ (Φ x t) u) ∧
      (∀ x ∈ U, StrictMonoOn (fun t ↦ Φ x t 0) (Ioo (-ε) ε)) ∧
      ∀ x ∈ U ∩ {x | 0 ≤ x 0}, ∀ t ∈ Ico 0 ε,
        Φ x t ∈ s ∩ {x | 0 ≤ x 0} ∧ HasDerivAt (Φ x) (v (Φ x t)) t := by
  -- Boundary-normal coordinates carry the half-space onto `upperHalfSpace`.
  let L := euclideanFinConsEquiv (rfl : n = n)
  have hL0 (y : ℝ × (Fin n → ℝ)) : L y 0 = y.1 := euclideanFinConsEquiv_apply_zero rfl y
  have hLs0 (x : EuclideanSpace ℝ (Fin (n + 1))) : (L.symm x).1 = x 0 :=
    euclideanFinConsEquiv_symm_apply_fst rfl x
  have hLa : L (L.symm a) = a := L.apply_symm_apply a
  have hv' : ContDiffOn ℝ (k + 1) (fun y ↦ L.symm (v (L y)))
      (L ⁻¹' s ∩ upperHalfSpace (Fin n → ℝ)) :=
    L.symm.contDiff.comp_contDiffOn (hv.comp L.contDiff.contDiffOn fun y hy ↦
      ⟨hy.1, by simpa [hL0] using hy.2⟩)
  obtain ⟨Φ, U, hU, ε, hε, hΦ, hΦ0, hΦadd, hmono, hcurve⟩ :=
    ODE.exists_contDiffOn_localFlow_upperHalfSpace hv'
      (L.continuous.continuousAt.preimage_mem_nhds (by rwa [hLa]))
      (by simpa [hLs0] using ha) (by simpa [hLs0, hLa] using hva)
  refine ⟨fun x t ↦ L (Φ (L.symm x) t), L.symm ⁻¹' U,
    L.symm.continuous.continuousAt.preimage_mem_nhds hU, ε, hε,
    L.contDiff.comp_contDiffOn (hΦ.comp (L.symm.contDiff.prodMap contDiff_id).contDiffOn
      fun p hp ↦ hp), fun x ↦ by simp [hΦ0], fun x t u ↦ by simp [hΦadd], fun x hx ↦ ?_, ?_⟩
  · simpa [hL0] using hmono _ hx
  · rintro x ⟨hxU, hx⟩ t ht
    obtain ⟨⟨hs, hH⟩, hd⟩ := hcurve _ ⟨hxU, by simpa [hLs0] using hx⟩ t ht
    refine ⟨⟨hs, by simpa [hL0] using hH⟩, ?_⟩
    have hd' := L.hasFDerivAt.comp_hasDerivAt t hd
    simp only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] at hd'
    exact hd'

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- The field `v` read in the preferred chart at `a` is smooth on the part in the model half-space
of an open neighbourhood `O` of the chart point of `a`, which lies in the chart target over a
neighbourhood `V` of `a` on which `v` is smooth. -/
private theorem exists_isOpen_contDiffOn_chartField
    (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) {a : M} {V : Set M}
    (hv : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (fun x ↦ (⟨x, v x⟩ :
      TangentBundle (𝓡∂ (n + 1)) M)) V)
    (hV : V ∈ 𝓝 a) :
    ∃ O, IsOpen O ∧ extChartAt (𝓡∂ (n + 1)) a a ∈ O ∧
      O ∩ {z | 0 ≤ z 0} ⊆ (extChartAt (𝓡∂ (n + 1)) a).target ∩
        (extChartAt (𝓡∂ (n + 1)) a).symm ⁻¹' V ∧
      ContDiffOn ℝ ∞ (fun z ↦ tangentCoordChange (𝓡∂ (n + 1))
        ((extChartAt (𝓡∂ (n + 1)) a).symm z) a ((extChartAt (𝓡∂ (n + 1)) a).symm z)
        (v ((extChartAt (𝓡∂ (n + 1)) a).symm z))) (O ∩ {z | 0 ≤ z 0}) := by
  let φ := extChartAt (𝓡∂ (n + 1)) a
  have hdom : φ.target ∩ φ.symm ⁻¹' V ∈ 𝓝[range (𝓡∂ (n + 1))] (φ a) := by
    refine inter_mem (extChartAt_target_mem_nhdsWithin a) ?_
    simpa only [preimage_univ, univ_inter] using
      extChartAt_preimage_mem_nhdsWithin (I := 𝓡∂ (n + 1)) (s := univ) (nhdsWithin_univ a ▸ hV)
  obtain ⟨O, hO, haO, hOdom⟩ := mem_nhdsWithin.mp hdom
  have hOdom' : O ∩ {z | 0 ≤ z 0} ⊆ φ.target ∩ φ.symm ⁻¹' V := fun z hz ↦
    hOdom ⟨hz.1, by simpa [range_modelWithCornersEuclideanHalfSpace] using hz.2⟩
  have : IsManifold (𝓡∂ (n + 1)) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡∂ (n + 1)) ∞ M)
  refine ⟨O, hO, haO, hOdom', ((Manifold.contDiffOn_trivializationAt_extChartAt_symm (n := ∞) v a
    hv).mono hOdom').congr fun z _ ↦ ?_⟩
  exact (TangentBundle.trivializationAt_snd_eq_tangentCoordChange _).symm

/-- **The chart flow of an inward field.** Let `v` be a vector field smooth on a neighbourhood `V`
of a boundary point `a` of a manifold modeled on `𝓡∂ (n + 1)`, pointing inward at `a`, and let `φ`
be the extended chart at `a`. Then there is a local flow `Ψ` of `v` read in `φ`, jointly smooth on
`U × (-ε, ε)` for a neighbourhood `U` of `φ a`, which starts at the identity and whose zeroth
coordinate increases strictly in time. For `z ∈ U` in the half-space, the forward curve
`t ↦ Ψ z t` stays in the chart target over `V` and is an integral curve of `v` when read back on
`M`. The velocity of `t ↦ Ψ (φ a) t` at time zero points strictly inward. -/
theorem exists_contDiffOn_chartFlow_of_isOutwardPointing_neg
    (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) {a : M} {V : Set M}
    (hv : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (fun x ↦ (⟨x, v x⟩ :
      TangentBundle (𝓡∂ (n + 1)) M)) V)
    (hV : V ∈ 𝓝 a) (ha : IsOutwardPointing a (-v a)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      ∃ U ∈ 𝓝 (extChartAt (𝓡∂ (n + 1)) a a), ∃ ε > 0,
        ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ q.1 q.2)
          (U ×ˢ Ioo (-ε) ε) ∧ (∀ z, Ψ z 0 = z) ∧
        (∀ z ∈ U, StrictMonoOn (fun t ↦ Ψ z t 0) (Ioo (-ε) ε)) ∧
        (∀ z ∈ U, 0 ≤ z 0 → ∀ t ∈ Ico 0 ε, Ψ z t ∈ (extChartAt (𝓡∂ (n + 1)) a).target ∩
          (extChartAt (𝓡∂ (n + 1)) a).symm ⁻¹' V) ∧
        (∀ z ∈ U, 0 ≤ z 0 →
          IsMIntegralCurveOn ((extChartAt (𝓡∂ (n + 1)) a).symm ∘ Ψ z) v (Ico 0 ε)) ∧
        ∃ w₀, HasDerivAt (Ψ (extChartAt (𝓡∂ (n + 1)) a a)) w₀ 0 ∧ 0 < w₀ 0 := by
  let φ := extChartAt (𝓡∂ (n + 1)) a
  let w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun z ↦
    tangentCoordChange (𝓡∂ (n + 1)) (φ.symm z) a (φ.symm z) (v (φ.symm z))
  obtain ⟨O, hO, haO, hOdom, hw⟩ := exists_isOpen_contDiffOn_chartField v hv hV
  -- Inwardness at `a` is positivity of the zeroth coordinate of the chart field.
  have hwa : 0 < w (φ a) 0 := by
    simp only [w]
    rw [φ.left_inv (mem_extChartAt_source a)]
    exact (isOutwardPointing_neg_iff_tangentCoordChange (isOutwardPointing_iff.mp ha).1
      (mem_extChartAt_source a) (v a)).mp ha
  have hφa0 : 0 ≤ φ a 0 := by
    have h := extChartAt_target_subset_range (I := 𝓡∂ (n + 1)) a
      (mem_extChartAt_target (I := 𝓡∂ (n + 1)) a)
    rwa [range_modelWithCornersEuclideanHalfSpace] at h
  -- The local flow `Ψ` of the coordinate field, extended across the boundary hyperplane.
  obtain ⟨Ψ, U, hU, ε, hε, hΨ, hΨ0, -, hmono, hcurve⟩ :=
    exists_contDiffOn_localFlow_euclideanHalfSpace (k := ⊤) (hw.of_le (by simp))
      (hO.mem_nhds haO) hφa0 hwa
  refine ⟨Ψ, U, hU, ε, hε, by simpa using hΨ, hΨ0, hmono,
    fun z hz hz0 t ht ↦ hOdom (hcurve z ⟨hz, hz0⟩ t ht).1, fun z hz hz0 ↦ ?_, w (φ a), ?_, hwa⟩
  · exact IsMIntegralCurveOn.of_extChartAt_symm_of_hasDerivWithinAt
      (fun t ht ↦ (hcurve z ⟨hz, hz0⟩ t ht).2.hasDerivWithinAt)
      fun t ht ↦ (hOdom (hcurve z ⟨hz, hz0⟩ t ht).1).1
  · have h := (hcurve (φ a) ⟨mem_of_mem_nhds hU, hφa0⟩ 0 (left_mem_Ico.2 hε)).2
    rw [hΨ0] at h
    exact h

/-- **Flowing the boundary inward.** Let `v` be a vector field smooth on a neighbourhood of a
boundary point `a` of a manifold modeled on `𝓡∂ (n + 1)`, and pointing inward at `a`. Then there
are a neighbourhood `U` of `a`, a time `ε > 0` and a family `Φ x t`, jointly smooth on `U × [0, ε)`,
such that for every `x ∈ U` the curve `t ↦ Φ x t` starts at `x`, is an integral curve of `v` on
`[0, ε)`, and lies in the interior of `M` at every time `0 < t < ε`. -/
theorem exists_contMDiffOn_localFlow_of_isOutwardPointing_neg
    (v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) {a : M} {V : Set M}
    (hv : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (fun x ↦ (⟨x, v x⟩ :
      TangentBundle (𝓡∂ (n + 1)) M)) V)
    (hV : V ∈ 𝓝 a) (ha : IsOutwardPointing a (-v a)) :
    ∃ U ∈ 𝓝 a, ∃ ε > 0, ∃ Φ : M → ℝ → M,
      ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ)) (𝓡∂ (n + 1)) ∞ (fun p : M × ℝ ↦ Φ p.1 p.2)
        (U ×ˢ Ico 0 ε) ∧
      ∀ x ∈ U, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v (Ico 0 ε) ∧
        ∀ t ∈ Ioo 0 ε, Φ x t ∈ (𝓡∂ (n + 1)).interior M := by
  let φ := extChartAt (𝓡∂ (n + 1)) a
  have hrange (z : EuclideanSpace ℝ (Fin (n + 1))) : z ∈ range (𝓡∂ (n + 1)) ↔ 0 ≤ z 0 := by
    simp [range_modelWithCornersEuclideanHalfSpace]
  obtain ⟨Ψ, U', hU', ε, hε, hΨ', hΨ0, hmono, hdomain', hcurve, -⟩ :=
    exists_contDiffOn_chartFlow_of_isOutwardPointing_neg v hv hV ha
  let U := φ.source ∩ φ ⁻¹' U'
  have hU : U ∈ 𝓝 a := inter_mem (extChartAt_source_mem_nhds a)
    ((continuousAt_extChartAt a).preimage_mem_nhds hU')
  have hstart (x : M) (hx : x ∈ U) : φ x ∈ U' ∧ 0 ≤ φ x 0 :=
    ⟨hx.2, (hrange _).mp (extChartAt_target_subset_range a (φ.map_source hx.1))⟩
  have hdomain (x : M) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ico 0 ε) :
      Ψ (φ x) t ∈ φ.target ∩ φ.symm ⁻¹' V := hdomain' _ (hstart x hx).1 (hstart x hx).2 t ht
  refine ⟨U, hU, ε, hε, fun x t ↦ φ.symm (Ψ (φ x) t), ?_, fun x hx ↦ ⟨?_, ?_, fun t ht ↦ ?_⟩⟩
  · -- Smoothness: the chart, then the coordinate flow, then the inverse chart.
    have hchart : ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)) × ℝ) ∞
        (fun p : M × ℝ ↦ (φ p.1, p.2)) (U ×ˢ Ico 0 ε) :=
      ((contMDiffOn_extChartAt (n := ∞)).comp contMDiff_fst.contMDiffOn fun p hp ↦ by
        rw [mem_preimage, ← extChartAt_source (𝓡∂ (n + 1))]
        exact hp.1.1).prodMk_space contMDiff_snd.contMDiffOn
    have hflow := hΨ'.contMDiffOn.comp hchart fun p hp ↦ ⟨hp.1.2, by linarith [hp.2.1], hp.2.2⟩
    exact (contMDiffOn_extChartAt_symm a).comp hflow fun p hp ↦ (hdomain p.1 hp.1 p.2 hp.2).1
  · simp only [hΨ0]
    exact φ.left_inv hx.1
  · exact hcurve _ (hstart x hx).1 (hstart x hx).2
  · -- At positive times the zeroth chart coordinate is positive, so the point is interior.
    have hpos : 0 < Ψ (φ x) t 0 := by
      have h := hmono _ (hstart x hx).1 ⟨neg_lt_zero.mpr hε, hε⟩ ⟨by linarith [ht.1], ht.2⟩ ht.1
      simp only [hΨ0] at h
      exact (hstart x hx).2.trans_lt h
    refine (ModelWithCorners.isInteriorPoint_extChartAt_symm_iff (k := ∞) (by simp) a
      (hdomain x hx t (Ioo_subset_Ico_self ht)).1).mpr ?_
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpos

end TauCeti
