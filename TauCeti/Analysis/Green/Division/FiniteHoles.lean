/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Green

/-!
# Finite holes and equivalent boundary presentations

Green's theorem applies directly to the perforated region. The field is only required to be
regular on that region, including its boundary; no extension into the holes is assumed.
Geometric null-chain certificates compare independent directional divisions with the actual
outer-minus-inner boundary, and can transport the result to an equivalent presentation.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

namespace BoundaryChain

/-- Geometric comparisons compose by actual cancellation of the intermediate chain. -/
theorem NullChain.trans {d : Coordinate} {U : Set ℂ} {c e f : BoundaryChain}
    (hce : NullChain d U (c - e)) (hef : NullChain d U (e - f)) :
    NullChain d U (c - f) := by
  convert hce.add hef using 1
  abel

end BoundaryChain

namespace Division

/-- Green on a region with any finite family of holes. The inner contours carry the negative
orientation in the actual integer chain. All field hypotheses concern the perforated region,
and both directional integrabilities are conclusions of the independent cell divisions. -/
theorem green_finite_holes {ι : Type*} (s : Finset ι) (Ω : Set ℂ) (holes : ι → Set ℂ)
    (outer : BoundaryChain) (inner : ι → BoundaryChain)
    (houter : BoundaryChain.boundary outer = 0)
    (hinner : ∀ i ∈ s, BoundaryChain.boundary (inner i) = 0)
    (V : Division .re (Ω \ ⋃ i ∈ s, holes i))
    (H : Division .im (Ω \ ⋃ i ∈ s, holes i))
    (hV : BoundaryChain.NullChain .re (Ω \ ⋃ i ∈ s, holes i)
      (V.boundary - (outer - ∑ i ∈ s, inner i)))
    (hH : BoundaryChain.NullChain .im (Ω \ ⋃ i ∈ s, holes i)
      (H.boundary - (outer - ∑ i ∈ s, inner i)))
    {P Q RP RQ : ℂ → ℝ} (hP : ContinuousOn P (Ω \ ⋃ i ∈ s, holes i))
    (hQ : ContinuousOn Q (Ω \ ⋃ i ∈ s, holes i))
    (hdP : ∀ K ∈ V.cells, ∀ x ∈ Icc K.a K.b,
      ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
        HasDerivAt (fun y ↦ P ⟨x, y⟩) (RP ⟨x, y⟩) y)
    (hdQ : ∀ K ∈ H.cells, ∀ y ∈ Icc K.a K.b,
      ∀ x ∈ Ioo (K.lowerFun y) (K.upperFun y),
        HasDerivAt (fun x ↦ Q ⟨x, y⟩) (RQ ⟨x, y⟩) x)
    (hRP : ∀ K ∈ V.cells, IntegrableOn RP (K.region .re))
    (hRQ : ∀ K ∈ H.cells, IntegrableOn RQ (K.region .im)) :
    BoundaryChain.boundary (outer - ∑ i ∈ s, inner i) = 0 ∧
    BoundaryChain.Integrable Complex.reCLM P (outer - ∑ i ∈ s, inner i) ∧
      BoundaryChain.Integrable Complex.imCLM Q (outer - ∑ i ∈ s, inner i) ∧
      IntegrableOn (fun z ↦ RQ z - RP z) (Ω \ ⋃ i ∈ s, holes i) ∧
      BoundaryChain.integral Complex.reCLM P (outer - ∑ i ∈ s, inner i) +
        BoundaryChain.integral Complex.imCLM Q (outer - ∑ i ∈ s, inner i) =
        ∫ z in Ω \ ⋃ i ∈ s, holes i, RQ z - RP z := by
  refine ⟨?_, green V H hV hH Subset.rfl hP hQ hdP hdQ hRP hRQ⟩
  simp only [map_sub, map_sum, houter]
  rw [Finset.sum_eq_zero hinner, sub_zero]

/-- A geometric replacement of the common boundary preserves Green, including genuine
integrability of the replacement. Its certificates can be built from graph subdivision,
reparametrization, reversal, and cancellation, with the field defined only on the region. -/
theorem green_equivalent_boundary {D : Set ℂ} (V : Division .re D) (H : Division .im D)
    {c e : BoundaryChain}
    (hV : BoundaryChain.NullChain .re D (V.boundary - c))
    (hH : BoundaryChain.NullChain .im D (H.boundary - c))
    (hce : BoundaryChain.NullChain .re D (c - e))
    (hce' : BoundaryChain.NullChain .im D (c - e))
    {P Q RP RQ : ℂ → ℝ} (hP : ContinuousOn P D) (hQ : ContinuousOn Q D)
    (hdP : ∀ K ∈ V.cells, ∀ x ∈ Icc K.a K.b,
      ∀ y ∈ Ioo (K.lowerFun x) (K.upperFun x),
        HasDerivAt (fun y ↦ P ⟨x, y⟩) (RP ⟨x, y⟩) y)
    (hdQ : ∀ K ∈ H.cells, ∀ y ∈ Icc K.a K.b,
      ∀ x ∈ Ioo (K.lowerFun y) (K.upperFun y),
        HasDerivAt (fun x ↦ Q ⟨x, y⟩) (RQ ⟨x, y⟩) x)
    (hRP : ∀ K ∈ V.cells, IntegrableOn RP (K.region .re))
    (hRQ : ∀ K ∈ H.cells, IntegrableOn RQ (K.region .im)) :
    BoundaryChain.Integrable Complex.reCLM P e ∧ BoundaryChain.Integrable Complex.imCLM Q e ∧
      IntegrableOn (fun z ↦ RQ z - RP z) D ∧
      BoundaryChain.integral Complex.reCLM P e + BoundaryChain.integral Complex.imCLM Q e =
        ∫ z in D, RQ z - RP z := by
  exact green V H (hV.trans hce) (hH.trans hce') Subset.rfl hP hQ hdP hdQ hRP hRQ

end Division
end TauCeti.Green
