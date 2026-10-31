/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.Analysis.Convex.Sequence.Derivative
public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# Active coefficients and finite Newton faces

If the weighted coefficient norms of a nonzero series are bounded at `b ^ τ`, then at every
smaller radius `b ^ σ` its Newton polygon has a finite face. Its absolute endpoints are the
first and last indices attaining the Gauss norm. The extra radius is essential: at a
convergence boundary a finite set of active coefficients can lie on an infinite polygon ray.

`PowerSeries.isFiniteFace_newtonPolygon_iff` identifies finite faces with the existing
`IsLowestDominant` and `IsDistinguished` predicates, without introducing new active-index
definitions. The one-sided derivatives of the real supporting value are the negatives of
these indices; a positive-width face gives a corner. Boundedness at the larger radius
suffices, so restrictedness there is more than is needed. Completeness is not required.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §§3–4.
-/

public section

open TauCeti Set

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : PowerSeries K)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {σ τ : ℝ}

include hb hv

/-- Below a radius with bounded weighted coefficients, the Newton polygon of a nonzero
series has a finite nonempty face. -/
theorem exists_isFiniteFace_newtonPolygon_of_hasGaussNorm
    (hf : f.HasGaussNorm norm (b ^ τ)) (hf0 : f ≠ 0) (hστ : σ < τ) :
    ∃ l u : ℕ, IsFiniteFace (f.newtonPolygon v) σ l u := by
  have hr : f.IsRestricted (b ^ σ) := hf.isRestricted_of_abs_lt (by
    rw [abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)]
    exact (Real.rpow_lt_rpow_left_iff hb).mpr hστ)
  obtain ⟨d, hd⟩ := supportingValue_ne_bot_iff.mp
    ((hasGaussNorm_iff_supportingValue_ne_bot f v hb hv τ).mp hf)
  have he := f.isLowerConvexEnvelope_newtonPolygon
    (isAdmissible_iff.mpr ⟨d, τ, hd⟩)
  have htransfer {s e : ℝ} (hs : IsSupportingLine (fun n => v (f.coeff n)) s e) :
      IsSupportingLine (f.newtonPolygon v) s e := by
    rw [isSupportingLine_iff, he.supportingValue_eq]
    exact isSupportingLine_iff.mp hs
  obtain ⟨c, i, hc, hi⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv hr hf0
  exact (f.isConvexSeq_newtonPolygon v).exists_isFiniteFace_of_finite_supportingFace
    (htransfer hc) ((htransfer (isSupportingLine_iff_forall.mpr hd)).finite_supportingFace hστ c)
    ⟨i, he.supportingFace_subset hc hi⟩

/-- A finite Newton face identifies the first and last active coefficients even at a
convergence boundary. Only bounded weighted coefficients at the given radius are needed. -/
theorem isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon
    (hG : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) u f := by
  have he := f.isLowerConvexEnvelope_newtonPolygon
    (isAdmissible_iff_exists_supportingValue_ne_bot.mpr
      ⟨σ, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp hG⟩)
  obtain ⟨c, hc, hcf⟩ := hface.exists_intercept
  have hcval : c = -Real.logb b (f.gaussNorm norm (b ^ σ)) := EReal.coe_injective
    ((supportingValue_eq_coe_of_mem_supportingFace hc
      (hcf.symm.subset ⟨le_rfl, hface.left_le_right⟩)).symm.trans
      (supportingValue_newtonPolygon_eq_neg_logb_gaussNorm f v hb hv hG hf0))
  have hc' : IsSupportingLine (fun n => v (f.coeff n)) σ c := by
    rw [isSupportingLine_iff, ← he.supportingValue_eq]
    exact isSupportingLine_iff.mp hc
  have hl : IsLeast (supportingFace (fun n => v (f.coeff n)) σ c) l :=
    (he.isLeast_supportingFace_iff hc').mp
      ⟨hcf.symm.subset ⟨le_rfl, hface.left_le_right⟩, fun n hn => (hcf.subset hn).1⟩
  have hu : IsGreatest (supportingFace (fun n => v (f.coeff n)) σ c) u := by
    refine ⟨?_, fun n hn => (hcf.subset (he.supportingFace_subset hc' hn)).2⟩
    rw [mem_supportingFace, ← he.eq_right_of_isFiniteFace hface]
    exact mem_supportingFace.mp (hcf.symm.subset ⟨hface.left_le_right, le_rfl⟩)
  rw [hcval] at hl hu
  exact ⟨(isLowestDominant_iff_isLeast_supportingFace f v hb hv hG hf0 l).mpr hl,
    (isDistinguished_iff_isGreatest_supportingFace f v hb hv hG hf0 u).mpr hu⟩

/-- At a radius strictly below one with bounded weighted coefficients, the finite Newton
face has endpoints `l, u` exactly when these are the first and last active coefficients. -/
theorem isFiniteFace_newtonPolygon_iff (hf : f.HasGaussNorm norm (b ^ τ))
    (hf0 : f ≠ 0) (hστ : σ < τ) {l u : ℕ} :
    IsFiniteFace (f.newtonPolygon v) σ l u ↔
      TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) u f := by
  have hr : f.IsRestricted (b ^ σ) := hf.isRestricted_of_abs_lt (by
    rw [abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)]
    exact (Real.rpow_lt_rpow_left_iff hb).mpr hστ)
  have hG := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hr
  have hactive {i j : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ i j) :=
    isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv hG hf0 hface
  refine ⟨hactive, fun ⟨hl, hu⟩ => ?_⟩
  obtain ⟨l', u', hface⟩ :=
    exists_isFiniteFace_newtonPolygon_of_hasGaussNorm f v hb hv hf hf0 hστ
  obtain ⟨hl', hu'⟩ := hactive hface
  obtain rfl := hl.unique hl'
  obtain rfl := hu.unique hu'
  exact hface

/-- The left derivative of the real Newton supporting value is minus the first active
coefficient index. The radius is strictly below one with bounded weighted coefficients. -/
theorem hasDerivWithinAt_supportingValue_newtonPolygon_left
    (hf : f.HasGaussNorm norm (b ^ τ)) (hστ : σ < τ) {l : ℕ}
    (hl : TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f) :
    HasDerivWithinAt (fun s => (supportingValue (f.newtonPolygon v) s).toReal)
      (-(l : ℝ)) (Iic σ) σ := by
  obtain ⟨i, j, hface⟩ :=
    exists_isFiniteFace_newtonPolygon_of_hasGaussNorm f v hb hv hf hl.ne_zero hστ
  have hi := ((isFiniteFace_newtonPolygon_iff f v hb hv hf hl.ne_zero hστ).mp hface).1
  obtain rfl := hl.unique hi
  exact hface.hasDerivWithinAt_supportingValue_toReal_left (f.isConvexSeq_newtonPolygon v)

/-- The right derivative of the real Newton supporting value is minus the last active
coefficient index. The radius is strictly below one with bounded weighted coefficients. -/
theorem hasDerivWithinAt_supportingValue_newtonPolygon_right
    (hf : f.HasGaussNorm norm (b ^ τ)) (hστ : σ < τ) {u : ℕ}
    (hu : TauCeti.PowerSeries.IsDistinguished (b ^ σ) u f) :
    HasDerivWithinAt (fun s => (supportingValue (f.newtonPolygon v) s).toReal)
      (-(u : ℝ)) (Ici σ) σ := by
  obtain ⟨i, j, hface⟩ :=
    exists_isFiniteFace_newtonPolygon_of_hasGaussNorm f v hb hv hf hu.ne_zero hστ
  have hj := ((isFiniteFace_newtonPolygon_iff f v hb hv hf hu.ne_zero hστ).mp hface).2
  obtain rfl := hu.unique hj
  exact hface.hasDerivWithinAt_supportingValue_toReal_right (f.isConvexSeq_newtonPolygon v)

/-- In the interior of the boundedness range, the real Newton supporting value is
differentiable exactly when its first and last active coefficients coincide. -/
theorem differentiableAt_supportingValue_newtonPolygon_iff
    (hf : f.HasGaussNorm norm (b ^ τ)) (hστ : σ < τ) {l u : ℕ}
    (hl : TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l f)
    (hu : TauCeti.PowerSeries.IsDistinguished (b ^ σ) u f) :
    DifferentiableAt ℝ (fun s => (supportingValue (f.newtonPolygon v) s).toReal) σ ↔ l = u := by
  have hface := (isFiniteFace_newtonPolygon_iff f v hb hv hf hl.ne_zero hστ).mpr ⟨hl, hu⟩
  exact hface.differentiableAt_supportingValue_toReal_iff (f.isConvexSeq_newtonPolygon v)

end PowerSeries

namespace Polynomial

/-- At every radius, the endpoints of a nonzero polynomial's Newton face are exactly the
first and last indices attaining its Gauss norm. -/
theorem isFiniteFace_newtonPolygon_iff {K : Type*} [NormedDivisionRing K] (p : K[X])
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hp : p ≠ 0) (σ : ℝ) {l u : ℕ} :
    IsFiniteFace (p.newtonPolygon v) σ l u ↔
      TauCeti.PowerSeries.IsLowestDominant (b ^ σ) l (p : PowerSeries K) ∧
      TauCeti.PowerSeries.IsDistinguished (b ^ σ) u (p : PowerSeries K) := by
  rw [← p.newtonPolygon_coe v]
  exact PowerSeries.isFiniteFace_newtonPolygon_iff (p : PowerSeries K) v hb hv
    (τ := σ + 1) (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      (TauCeti.PowerSeries.isRestricted_polynomial p))
    (by simpa using hp) (by linarith)

end Polynomial
