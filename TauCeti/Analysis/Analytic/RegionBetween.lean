/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Order.RegionBetween
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic interpolation between bands

Affine interpolation between strictly ordered analytic endpoint functions is analytic. If the
base map has an analytic inverse, the interpolation gives an analytic isomorphism between the
open bands: its inverse is the interpolation with the base map inverted and the endpoint pairs
exchanged. We use the same `TauCeti.regionBetweenMap` as for continuous closed-band extensions,
so the analytic maps on the interiors agree with their continuous boundary extensions.

`OpenPartialHomeomorph.regionBetween` supplies the underlying open partial homeomorphism;
`OpenPartialHomeomorph.analyticOnNhd_regionBetween` and
`OpenPartialHomeomorph.analyticOnNhd_regionBetween_symm` prove analyticity in both directions.
No finite-dimensionality or completeness hypothesis on the real normed base spaces is needed.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §2, Lemma 13.
-/

public section

open Set Filter

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Band interpolation is analytic wherever the base map and endpoint functions are analytic
and the source endpoints are distinct. Target endpoints need not be distinct for this assertion. -/
theorem analyticAt_regionBetweenMap {g : E → F} {φ φ' : E → ℝ} {ψ ψ' : F → ℝ}
    {p : E × ℝ} (hg : AnalyticAt ℝ g p.1) (hφ : AnalyticAt ℝ φ p.1)
    (hφ' : AnalyticAt ℝ φ' p.1) (hψ : AnalyticAt ℝ ψ (g p.1))
    (hψ' : AnalyticAt ℝ ψ' (g p.1)) (hne : φ p.1 ≠ φ' p.1) :
    AnalyticAt ℝ (regionBetweenMap g φ φ' ψ ψ') p := by
  have hg₁ := hg.comp (analyticAt_fst : AnalyticAt ℝ (Prod.fst : E × ℝ → E) p)
  have hφ₁ := hφ.comp (analyticAt_fst : AnalyticAt ℝ (Prod.fst : E × ℝ → E) p)
  have hφ₁' := hφ'.comp (analyticAt_fst : AnalyticAt ℝ (Prod.fst : E × ℝ → E) p)
  have hψ₁ := hψ.comp_of_eq hg₁ rfl
  have hψ₁' := hψ'.comp_of_eq hg₁ rfl
  have h := hg₁.prod (hψ₁.add (((analyticAt_snd.sub hφ₁).div (hφ₁'.sub hφ₁)
    (sub_ne_zero.mpr hne.symm)).mul (hψ₁'.sub hψ₁)))
  exact h.congr (Eventually.of_forall fun q ↦
    (regionBetweenMap_apply g φ φ' ψ ψ' q.1 q.2).symm)

/-- Analytic base and endpoint maps give an analytic interpolation map on an open band. Only
the source endpoints must be strictly ordered; target ordering is needed for invertibility,
not for analyticity. -/
theorem analyticOnNhd_regionBetweenMap {g : E → F} {φ φ' : E → ℝ} {ψ ψ' : F → ℝ}
    {s : Set E} {t : Set F} (hg : AnalyticOnNhd ℝ g s)
    (hφ : AnalyticOnNhd ℝ φ s) (hφ' : AnalyticOnNhd ℝ φ' s)
    (hψ : AnalyticOnNhd ℝ ψ t) (hψ' : AnalyticOnNhd ℝ ψ' t) (hgst : MapsTo g s t) :
    AnalyticOnNhd ℝ (regionBetweenMap g φ φ' ψ ψ') (regionBetween φ φ' s) := by
  intro p hp
  exact analyticAt_regionBetweenMap (hg _ hp.1) (hφ _ hp.1) (hφ' _ hp.1)
    (hψ _ (hgst hp.1)) (hψ' _ (hgst hp.1)) (hp.2.1.trans hp.2.2).ne

end TauCeti

namespace OpenPartialHomeomorph

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (e : OpenPartialHomeomorph E F) {φ φ' : E → ℝ} {ψ ψ' : F → ℝ}
  (he : AnalyticOnNhd ℝ e e.source) (he' : AnalyticOnNhd ℝ e.symm e.target)
  (hφ : AnalyticOnNhd ℝ φ e.source) (hφ' : AnalyticOnNhd ℝ φ' e.source)
  (hψ : AnalyticOnNhd ℝ ψ e.target) (hψ' : AnalyticOnNhd ℝ ψ' e.target)
  (hφφ' : ∀ x ∈ e.source, φ x < φ' x) (hψψ' : ∀ y ∈ e.target, ψ y < ψ' y)

include he in
/-- The open-band lift of an analytic base isomorphism is analytic. -/
theorem analyticOnNhd_regionBetween :
    AnalyticOnNhd ℝ
      (e.regionBetween φ φ' ψ ψ' hφ.continuousOn hφ'.continuousOn hψ.continuousOn
        hψ'.continuousOn hφφ' hψψ')
      (_root_.regionBetween φ φ' e.source) := by
  rw [coe_regionBetween]
  exact analyticOnNhd_regionBetweenMap he hφ hφ' hψ hψ' e.mapsTo

include he' in
/-- The inverse of the open-band lift is analytic: it interpolates in the reverse direction
using the inverse base map. -/
theorem analyticOnNhd_regionBetween_symm :
    AnalyticOnNhd ℝ
      (e.regionBetween φ φ' ψ ψ' hφ.continuousOn hφ'.continuousOn hψ.continuousOn
        hψ'.continuousOn hφφ' hψψ').symm
      (_root_.regionBetween ψ ψ' e.target) := by
  rw [coe_regionBetween_symm]
  exact analyticOnNhd_regionBetweenMap he' hψ hψ' hφ hφ' e.symm.mapsTo

end OpenPartialHomeomorph
