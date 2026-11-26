/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Box
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Complex.Euclidean.Plane
import TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Planar
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# Rellich compactness on the unit square box

The unit square box `TauCeti.PDE.boxDomain 0 1` in `EuclideanSpace ℝ (Fin 2)` is carried onto
`TauCeti.openUnitSquare` by the affine isometry reading off the two coordinates. The open unit
square is a Lipschitz domain (`TauCeti.isLipschitzDomainWith_openUnitSquare`), so the
Rellich–Kondrachov theorem for Lipschitz domains
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`) makes
the value map `W^{1,p} → Lᵖ` on the box compact.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_boxDomain_zero_one`: the value map
  `W^{1,p}((0, 1)²) → Lᵖ((0, 1)²)` is compact.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.W1p

/-- **Rellich compactness on the unit square.** For `1 ≤ p ≤ ∞`, the value map
`W^{1,p}((0, 1)²) → Lᵖ((0, 1)²)` is compact. The square is a Lipschitz domain
(`TauCeti.isLipschitzDomainWith_openUnitSquare`). -/
theorem isCompactOperator_valueL_boxDomain_zero_one {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    IsCompactOperator (valueL (mu := volume)
      (Omega := PDE.boxDomain (0 : Fin 2 → ℝ) 1) (p := p)) := by
  -- The coordinates `x ↦ (x₀, x₁)` carry the box onto `openUnitSquare`.
  set e : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
    (Complex.orthonormalBasisOneI.repr.symm.trans Complex.equivRealProdL2).toAffineIsometryEquiv
  have he : openUnitSquare = e.symm ⁻¹' (PDE.boxDomain (0 : Fin 2 → ℝ) 1) := by
    ext y
    simp [e, mem_openUnitSquare, Fin.forall_fin_two]
  have hb : Bornology.IsBounded openUnitSquare := by
    rw [he]
    exact e.symm.isometry.antilipschitzWith.isBounded_preimage (PDE.isBounded_boxDomain _ _)
  exact isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv
    (Ω := ⟨openUnitSquare, isOpen_openUnitSquare⟩) isLipschitzDomainWith_openUnitSquare hb e he

end TauCeti.W1p
