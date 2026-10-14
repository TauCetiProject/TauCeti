/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.Algebra.Group.Units.Basic

/-!
# Unimodular symmetric forms over Henselian local rings

Over a Henselian local ring with finite residue field and two invertible, symmetric forms
with unit Gram determinant are classified by their rank and their determinant modulo squares.
The determinant may be computed in any caller-provided basis. The conclusion is an isometry
over the coefficient ring, preserving the bilinear forms themselves.

Diagonalization over the local ring gives an orthogonal basis with unit coefficients. The
unit diagonal classification then identifies the forms. This applies to `ℤ_p` for odd `p`,
including forms which arise by localizing an integral lattice that is unimodular only at `p`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module QuadraticMap
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {R M N : Type*} [CommRing R]
  [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Unimodular classification at odd residue characteristic.** Symmetric forms with unit Gram
determinants on modules with bases of the same size are integrally isometric exactly when the
product of those determinants is a square. The bases and hence the determinant representatives
are arbitrary; positive rank is not required. -/
theorem IsSymm.equivalent_iff_isSquare_det_mul_det
    {B : BilinForm R M} {C : BilinForm R N} (hB : B.IsSymm) (hC : C.IsSymm)
    (h2 : IsUnit (2 : R)) {n : ℕ} (b : Basis (Fin n) R M) (c : Basis (Fin n) R N)
    (hBdet : IsUnit (B.toMatrix b).det) (hCdet : IsUnit (C.toMatrix c).det) :
    B.Equivalent C ↔ IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) := by
  classical
  let := h2.invertible
  constructor
  · exact fun h ↦ h.isSquare_det_mul_det b c
  · intro hdet
    -- Orthogonal diagonalization retains an explicit determinant change-of-basis equation.
    obtain ⟨w, hw, d, hd⟩ := hB.exists_equivalent_weightedSumSquares_of_isUnit_det h2 b hBdet
    obtain ⟨v, hv, e, he⟩ := hC.exists_equivalent_weightedSumSquares_of_isUnit_det h2 c hCdet
    have hsq : IsSquare ((∏ i, w i) * ∏ i, v i) := by
      rw [← TauCeti.isSquare_units_val_iff]
      have h := hdet.mul (IsSquare.sq (d * e))
      convert h using 1
      simp only [Units.val_mul, Units.coe_prod, hd, he]
      ring
    have hdiag := (TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
      h2 w v).mpr hsq
    exact (hB.equivalent_iff_toQuadraticMap_equivalent hC).mpr
      (hw.trans (hdiag.trans hv.symm))

end LinearMap.BilinForm
