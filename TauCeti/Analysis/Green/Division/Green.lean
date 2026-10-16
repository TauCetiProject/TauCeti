/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Basic
public import TauCeti.Analysis.Green.BoundaryChain.CurveIntegral

/-!
# Green's theorem for independent finite directional divisions

Each division contributes one directional identity. Geometric null-chain certificates compare
its actual boundary with a common boundary presentation, modulo the unused coordinate. The
vertical and horizontal divisions need not have the same cells, parametrizations, or edges.
The field assumptions are continuity, existence of the used fiber derivatives, and cellwise
area integrability of those derivatives. The curve-integral specialization also assumes arcwise
circulation integrability. No Fréchet differentiability or continuity of the derivatives is needed.

## References

* Mohammad Abdulaziz and Lawrence C. Paulson,
  [*An Isabelle/HOL formalisation of Green's Theorem*](https://isa-afp.org/entries/Green.html),
  Archive of Formal Proofs, 2018: the directional division and path-equivalence formulation.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Division

variable {d : Coordinate} {D U : Set ℂ}

/-- Summing the cell identities gives directional Green and genuine gauge integrability on
the finite division boundary. Cellwise area integrability is promoted to the whole region. -/
theorem integrable_and_integral_boundary (V : Division d D) {P R : ℂ → ℝ}
    (hP : ContinuousOn P D)
    (hdP : ∀ K ∈ V.cells, ∀ x ∈ Icc K.a K.b,
      ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
        HasDerivAt (fun y ↦ P (d.graph (fun _ ↦ y) x)) (R (d.graph (fun _ ↦ y) x)) y)
    (hR : ∀ K ∈ V.cells, IntegrableOn R (K.region d)) :
    BoundaryChain.Integrable d.proj P V.boundary ∧ IntegrableOn R D ∧
      BoundaryChain.integral d.proj P V.boundary =
        -(d.orientation : ℝ) * ∫ z in D, R z := by
  have hc (K : GraphCell) (hK : K ∈ V.cells) :=
    K.integrable_and_integral_boundary d (hP.mono (V.region_subset hK)) (hdP K hK) (hR K hK)
  refine ⟨?_, V.integrableOn_iff.mpr hR, ?_⟩
  · rw [boundary_def]
    exact BoundaryChain.Integrable.sum V.cells (fun K ↦ K.boundary d)
      (fun K hK ↦ (hc K hK).1)
  · rw [boundary_def, map_sum]
    have hs := Finset.sum_congr (s₁ := V.cells) rfl (fun K hK ↦ (hc K hK).2)
    rw [hs]
    rw [← Finset.mul_sum, ← V.integral_eq_sum hR]

/-- Full Green from separate type-I and type-II divisions and geometric comparisons to a
common boundary. Gauge boundary integrability and integrability of the directional curl are
conclusions. In particular no equality of boundary integrals is assumed. -/
theorem integrable_and_integral_add_integral_eq_integral_sub
    (V : Division .re D) (H : Division .im D) {c : BoundaryChain}
    (hV : BoundaryChain.NullChain .re U (V.boundary - c))
    (hH : BoundaryChain.NullChain .im U (H.boundary - c)) (hDU : D ⊆ U)
    {P Q RP RQ : ℂ → ℝ} (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    (hdP : ∀ K ∈ V.cells, ∀ x ∈ Icc K.a K.b,
      ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
        HasDerivAt (fun y ↦ P ⟨x, y⟩) (RP ⟨x, y⟩) y)
    (hdQ : ∀ K ∈ H.cells, ∀ y ∈ Icc K.a K.b,
      ∀ x ∈ Ioo (K.lowerFun y) (K.upperFun y),
        HasDerivAt (fun x ↦ Q ⟨x, y⟩) (RQ ⟨x, y⟩) x)
    (hRP : ∀ K ∈ V.cells, IntegrableOn RP (K.region .re))
    (hRQ : ∀ K ∈ H.cells, IntegrableOn RQ (K.region .im)) :
    BoundaryChain.Integrable Complex.reCLM P c ∧ BoundaryChain.Integrable Complex.imCLM Q c ∧
      IntegrableOn (fun z ↦ RQ z - RP z) D ∧
      BoundaryChain.integral Complex.reCLM P c + BoundaryChain.integral Complex.imCLM Q c =
        ∫ z in D, RQ z - RP z := by
  have hdx := V.integrable_and_integral_boundary (hP.mono hDU)
    (by simpa only [Coordinate.graph_re_apply] using hdP) hRP
  have hdy := H.integrable_and_integral_boundary (hQ.mono hDU)
    (by simpa only [Coordinate.graph_im_apply] using hdQ) hRQ
  have hcx := (hV.integrable_iff hP).mp hdx.1
  have hcy := (hH.integrable_iff hQ).mp hdy.1
  simp only [Coordinate.proj_re, Coordinate.orientation_re, Int.cast_one, neg_one_mul] at hdx hcx
  simp only [Coordinate.proj_im, Coordinate.orientation_im, Int.cast_neg, Int.cast_one,
    neg_neg, one_mul] at hdy hcy
  refine ⟨hcx, hcy, hdy.2.1.sub hdx.2.1, ?_⟩
  have hx := hV.integral_eq hP
  have hy := hH.integral_eq hQ
  simp only [Coordinate.proj_re] at hx
  simp only [Coordinate.proj_im] at hy
  rw [← hx, ← hy, hdx.2.2, hdy.2.2, integral_sub hdy.2.1 hdx.2.1]
  ring

/-- The Bochner specialization retains genuine integrability of the circulation on every
supported arc and concludes the identity for Mathlib's existing curve integral. -/
theorem integrableOn_and_linearCombination_curveIntegral_eq_integral_sub
    (V : Division .re D) (H : Division .im D) {c : BoundaryChain}
    (hV : BoundaryChain.NullChain .re U (V.boundary - c))
    (hH : BoundaryChain.NullChain .im U (H.boundary - c)) (hDU : D ⊆ U)
    {P Q RP RQ : ℂ → ℝ} (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    (hdP : ∀ K ∈ V.cells, ∀ x ∈ Icc K.a K.b,
      ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
        HasDerivAt (fun y ↦ P ⟨x, y⟩) (RP ⟨x, y⟩) y)
    (hdQ : ∀ K ∈ H.cells, ∀ y ∈ Icc K.a K.b,
      ∀ x ∈ Ioo (K.lowerFun y) (K.upperFun y),
        HasDerivAt (fun x ↦ Q ⟨x, y⟩) (RQ ⟨x, y⟩) x)
    (hRP : ∀ K ∈ V.cells, IntegrableOn RP (K.region .re))
    (hRQ : ∀ K ∈ H.cells, IntegrableOn RQ (K.region .im))
    (hc : ∀ γ ∈ c.support,
      IntervalIntegrable (circulationFun P Q γ.2.2.extend) volume 0 1) :
    IntegrableOn (fun z ↦ RQ z - RP z) D ∧
      Finsupp.linearCombination ℤ (fun γ : Arc ↦ curveIntegral (oneForm P Q) γ.2.2) c =
        ∫ z in D, RQ z - RP z := by
  have h := integrable_and_integral_add_integral_eq_integral_sub V H hV hH hDU hP hQ hdP hdQ hRP hRQ
  exact ⟨h.2.2.1, (BoundaryChain.integral_add_eq_curveIntegral h.1 h.2.1 hc).symm.trans h.2.2.2⟩

end TauCeti.Green.Division
