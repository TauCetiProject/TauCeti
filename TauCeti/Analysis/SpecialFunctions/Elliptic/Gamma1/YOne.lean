/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.TateNormalForm
public import TauCeti.AlgebraicGeometry.ModularCurve.YOne.FieldPoints

/-!
# The analytic orbits and the complex points of `Y₁(N)`

For `N ≥ 4`, the Tate normal form classification of `Γ₁(N) \ ℍ` and the field-point
classification of `Y₁(N)` give `TauCeti.gamma1QuotientEquivYOnePoints`, a bijection onto
`Spec ℂ ⟶ Y₁(N)`. Its coordinates are the holomorphic Tate coefficients of `(E_z, 1/N)`.
This is a bijection of sets; no complex structure or biholomorphism is constructed here.

The two classifications, with their references, are in the imported modules.
-/

public section

open UpperHalfPlane CongruenceSubgroup

namespace TauCeti

variable (N : ℕ) [NeZero N]

open _root_.CategoryTheory _root_.AlgebraicGeometry TauCeti.AlgebraicGeometry.UniversalTate in
/-- **`Γ₁(N) \ ℍ` and the complex points of `Y₁(N)`.** For `N ≥ 4`, sending `z` to the point of
the fine moduli scheme `Y₁(N)` with coordinates the Tate normal form coefficients `(a(z), b(z))`
of `E_z = ℂ / (ℤ z + ℤ)` with the point `1 / N` induces a bijection from `Γ₁(N) \ ℍ` onto the
morphisms `Spec ℂ ⟶ Y₁(N)`. -/
noncomputable def gamma1QuotientEquivYOnePoints (hN : 4 ≤ N) :
    MulAction.orbitRel.Quotient (Gamma1 N) ℍ ≃ (Spec (.of ℂ) ⟶ yOne.{0} N) :=
  (gamma1QuotientEquivTateNormalForm N hN).trans (yOnePointsEquiv ℂ N).symm

open TauCeti.AlgebraicGeometry.UniversalTate in
/-- Reading the Tate coefficients of the analytic-to-scheme comparison recovers the Tate
normal form classification on every orbit. -/
@[simp]
theorem yOnePointsEquiv_gamma1QuotientEquivYOnePoints (hN : 4 ≤ N)
    (q : MulAction.orbitRel.Quotient (Gamma1 N) ℍ) :
    yOnePointsEquiv ℂ N (gamma1QuotientEquivYOnePoints N hN q) =
      gamma1QuotientEquivTateNormalForm N hN q :=
  (yOnePointsEquiv ℂ N).apply_symm_apply _

open TauCeti.AlgebraicGeometry.UniversalTate in
/-- The point of `Y₁(N)` attached to `z ∈ ℍ` has coordinates the Tate normal form coefficients
`(a(z), b(z))` of `(E_z, 1 / N)`: by `coe_yOnePointsEquiv_apply`, its ring homomorphism
`ℤ[A, B][Δ⁻¹] →+* ℂ` sends `A` to `a(z)` and `B` to `b(z)`. -/
theorem yOnePointsEquiv_gamma1QuotientEquivYOnePoints_mk (hN : 4 ≤ N) (z : ℍ) :
    yOnePointsEquiv ℂ N (gamma1QuotientEquivYOnePoints N hN ⟦z⟧) =
      ⟨(z.pointedWeierstrassCurve N).tateNormalFormCoeffs,
        tateNormalFormCoeffs_pointedWeierstrassCurve_mem_tateNormalFormExactOrder hN z⟩ := by
  rw [yOnePointsEquiv_gamma1QuotientEquivYOnePoints]
  exact Subtype.ext (coe_gamma1QuotientEquivTateNormalForm_mk hN z)

end TauCeti
