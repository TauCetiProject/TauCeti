/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TateNormalForm
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.Moduli
import TauCeti.Analysis.SpecialFunctions.Elliptic.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.DivisionValues
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted

/-!
# The Tate normal form of `(E_z, 1 / N)`

For `z` in the upper half-plane and `N ≥ 4`, the complex elliptic curve `E_z = ℂ / (ℤ z + ℤ)`
with the point `1 / N` of exact order `N` has a Tate normal form
`Y² + a(z) XY + b(z) Y = X³ + b(z) X²`, with `1 / N` going to `(0, 0)`. This file shows that
`z ↦ (a(z), b(z))` is a holomorphic map from `ℍ` to the pairs `(a, b)` for which the Tate normal
form is elliptic and `(0, 0)` has exact order `N`
(`TauCeti.PointedWeierstrassCurve.tateNormalFormExactOrder`), and that it induces a bijection from
`Γ₁(N) \ ℍ` onto them (`TauCeti.gamma1QuotientEquivTateNormalForm`). The comparison with the
complex points of the scheme `Y₁(N)` is in `TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.YOne`.

* **The coefficients.** For a lattice `Λ` and `w ∈ ℂ`, write `x = ℘(w; Λ)`, `y = ℘'(w; Λ)` and
  `Q = Ψ₃(x) = 3 x⁴ - (3 / 2) g₂ x² - 3 g₃ x - g₂² / 16` for the value of the `3`-division
  polynomial. The Tate normal form coefficients of the curve of `Λ` with the point of `w` are
  `a = 2 Q (3 x² - g₂ / 4) / y⁴` and `b = Q³ / y⁸`
  (`PeriodPair.tateNormalFormCoeffs_mk_weierstrassPoint`); for `(E_z, 1 / N)` this is
  `UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve`.
* **Holomorphy.** `g₂` and `g₃` are holomorphic in `z`, and so are the division values of `℘`
  (`TauCeti.EisensteinSeries.mdifferentiable_weierstrassP_periodPair_div`) and of `℘'`
  (`TauCeti.EisensteinSeries.mdifferentiable_derivWeierstrassP_periodPair_div`). For `N ≥ 3` the
  value `℘'(1 / N)` does not vanish (`UpperHalfPlane.derivWeierstrassP_periodPair_one_div_ne_zero`),
  so `a` and `b` are holomorphic; for `N < 3` they vanish identically.
* **The bijection.** It is the composite of the moduli bijection
  `TauCeti.gamma1QuotientEquivExactOrder` with the classification of points of order `N ≥ 4` by
  their Tate normal form, `TauCeti.PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm`.
  Hence `(a(z), b(z)) = (a(z'), b(z'))` exactly when `z' ∈ Γ₁(N) z`
  (`UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve_eq_iff`): `a` and `b` are
  `Γ₁(N)`-invariant holomorphic functions on `ℍ` that separate the `Γ₁(N)`-orbits.

## Main definitions

* `TauCeti.gamma1QuotientEquivTateNormalForm N hN`: for `N ≥ 4`, the bijection from `Γ₁(N) \ ℍ`
  to the pairs `(a, b)` whose Tate normal form is elliptic with `(0, 0)` of exact order `N`, sending
  the orbit of `z` to the Tate normal form coefficients of `(E_z, 1 / N)`.


## Main results

* `PeriodPair.tateNormalFormCoeffs_mk_weierstrassPoint`: the Tate normal form coefficients of the
  curve of a lattice with the point of `w`, in terms of `℘(w)`, `℘'(w)`, `g₂` and `Ψ₃(℘(w))`.
* `UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve`: the same formula for
  `(E_z, 1 / N)`.
* `UpperHalfPlane.derivWeierstrassP_periodPair_one_div_ne_zero`: for `N ≥ 3`, `℘'(1 / N) ≠ 0`.
* `UpperHalfPlane.mdifferentiable_fst_tateNormalFormCoeffs_pointedWeierstrassCurve`,
  `UpperHalfPlane.mdifferentiable_snd_tateNormalFormCoeffs_pointedWeierstrassCurve`: the
  coefficients are holomorphic on `ℍ`.
* `UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve_smul`: the coefficients are
  `Γ₁(N)`-invariant.
* `UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve_eq_iff`: for `N ≥ 4` the
  coefficients at `z` and `z'` agree exactly when `z' ∈ Γ₁(N) z`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §§1.5 and 7.7.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

public section

open Complex UpperHalfPlane CongruenceSubgroup TauCeti ModularForm PeriodPair
open scoped MatrixGroups Manifold

namespace PeriodPair

/-- **The Tate normal form coefficients of a uniformized pointed curve.** For a lattice `Λ` and
`w ∈ ℂ`, with `x = ℘(w)`, `y = ℘'(w)` and `Q = Ψ₃(x)` the value of the `3`-division polynomial of
the curve of `Λ`, the coefficients of the curve with the point of `w` are
`a = 2 Q (3 x² - g₂ / 4) / y⁴` and `b = Q³ / y⁸`. For `w ∈ Λ` both sides are `(0, 0)`. -/
theorem tateNormalFormCoeffs_mk_weierstrassPoint (L : PeriodPair) (w : ℂ) :
    (⟨L.weierstrassCurve, L.weierstrassPoint w⟩ : PointedWeierstrassCurve ℂ).tateNormalFormCoeffs =
      (2 * L.weierstrassCurve.Ψ₃.eval (℘[L] w) * (3 * ℘[L] w ^ 2 - L.g₂ / 4) / ℘'[L] w ^ 4,
        L.weierstrassCurve.Ψ₃.eval (℘[L] w) ^ 3 / ℘'[L] w ^ 8) := by
  by_cases hw : w ∈ L.lattice
  · simp [L.weierstrassPoint_of_mem hw, L.derivWeierstrassP_coe ⟨w, hw⟩]
  rw [L.weierstrassPoint_of_notMem hw, PointedWeierstrassCurve.tateNormalFormCoeffs_mk_some]
  simp only [WeierstrassCurve.evalEval_ψ₂_of_isCharNeTwoNF, WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₂_of_isShortNF, weierstrassCurve_a₄, Prod.mk.injEq]
  constructor <;> ring

end PeriodPair

namespace UpperHalfPlane

variable {N : ℕ}

/-- For `N ≥ 3`, the value `℘'(1 / N; ℤ z + ℤ)` does not vanish. -/
theorem derivWeierstrassP_periodPair_one_div_ne_zero (hN : 3 ≤ N) (z : ℍ) :
    ℘'[z.periodPair] (1 / N) ≠ 0 := by
  have : NeZero N := ⟨by omega⟩
  rw [Ne, derivWeierstrassP_eq_zero_iff, two_mul, ← two_nsmul,
    ← nsmul_weierstrassPoint_eq_zero_iff]
  exact nsmul_ne_zero_of_lt_addOrderOf two_ne_zero
    (by rw [addOrderOf_weierstrassPoint_one_div]; omega)

/-- **The Tate normal form coefficients of `(E_z, 1 / N)`.** With `x = ℘(1 / N)`, `y = ℘'(1 / N)`
and `Q = Ψ₃(x)` the value of the `3`-division polynomial of `E_z`, the coefficients are
`a = 2 Q (3 x² - g₂ / 4) / y⁴` and `b = Q³ / y⁸`. -/
theorem tateNormalFormCoeffs_pointedWeierstrassCurve (z : ℍ) :
    (z.pointedWeierstrassCurve N).tateNormalFormCoeffs =
      (2 * z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) *
          (3 * ℘[z.periodPair] (1 / N) ^ 2 - z.periodPair.g₂ / 4) / ℘'[z.periodPair] (1 / N) ^ 4,
        z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) ^ 3 /
          ℘'[z.periodPair] (1 / N) ^ 8) := by
  rw [pointedWeierstrassCurve_def, tateNormalFormCoeffs_mk_weierstrassPoint]

/-- For `N < 3` the point `1 / N` is a half-period of `ℤ z + ℤ`, and the coefficients vanish. -/
private theorem tateNormalFormCoeffs_pointedWeierstrassCurve_of_lt_three (hN : N < 3) (z : ℍ) :
    (z.pointedWeierstrassCurve N).tateNormalFormCoeffs = (0, 0) := by
  have h : ℘'[z.periodPair] (1 / N) = 0 := by
    have h₁ : (1 : ℂ) ∈ z.periodPair.lattice := by simpa using z.periodPair.ω₂_mem_lattice
    rw [derivWeierstrassP_eq_zero_iff]
    interval_cases N
    · simp
    · convert add_mem h₁ h₁ using 1
      norm_num
    · simpa using h₁
  rw [tateNormalFormCoeffs_pointedWeierstrassCurve, h]
  simp

/-- The division value `℘'(1 / N; ℤ z + ℤ)` is holomorphic. -/
private theorem mdifferentiable_derivWeierstrassP_periodPair_one_div :
    MDiff fun z : ℍ ↦ ℘'[z.periodPair] (1 / N) := by
  simpa using EisensteinSeries.mdifferentiable_derivWeierstrassP_periodPair_div (N := N) ![0, 1]

/-- The division value `℘(1 / N; ℤ z + ℤ)` is holomorphic. -/
private theorem mdifferentiable_weierstrassP_periodPair_one_div :
    MDiff fun z : ℍ ↦ ℘[z.periodPair] (1 / N) := by
  simpa using EisensteinSeries.mdifferentiable_weierstrassP_periodPair_div (N := N) ![0, 1]

/-- The value `Ψ₃(℘(1 / N)) = 3 x⁴ - (3 / 2) g₂ x² - 3 g₃ x - g₂² / 16` of the `3`-division
polynomial of `E_z` at `x = ℘(1 / N)` is holomorphic in `z`. -/
private theorem mdifferentiable_eval_Ψ₃_weierstrassP_one_div :
    MDiff fun z : ℍ ↦ z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) := by
  have hx := mdifferentiable_weierstrassP_periodPair_one_div (N := N)
  have hg₂ := mdifferentiable_g₂_periodPair
  have hg₃ := mdifferentiable_g₃_periodPair
  have h (z : ℍ) : z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) =
      3 * ℘[z.periodPair] (1 / N) ^ 4 - 3 / 2 * z.periodPair.g₂ * ℘[z.periodPair] (1 / N) ^ 2 -
        3 * z.periodPair.g₃ * ℘[z.periodPair] (1 / N) - z.periodPair.g₂ ^ 2 / 16 := by
    simp [WeierstrassCurve.eval_Ψ₃]
    ring
  rw [funext h]
  exact (((mdifferentiable_const.mul (hx.pow 4)).sub
    ((mdifferentiable_const.mul hg₂).mul (hx.pow 2))).sub
      ((mdifferentiable_const.mul hg₃).mul hx)).sub
        ((hg₂.pow 2).div mdifferentiable_const fun _ ↦ by norm_num)

/-- The first Tate normal form coefficient `a(z)` of `(E_z, 1 / N)` is holomorphic on `ℍ`. For
`N < 3` it is identically `0`. -/
theorem mdifferentiable_fst_tateNormalFormCoeffs_pointedWeierstrassCurve :
    MDiff fun z : ℍ ↦ (z.pointedWeierstrassCurve N).tateNormalFormCoeffs.1 := by
  obtain hN | hN := lt_or_ge N 3
  · simpa [tateNormalFormCoeffs_pointedWeierstrassCurve_of_lt_three hN] using mdifferentiable_const
  simp only [tateNormalFormCoeffs_pointedWeierstrassCurve]
  exact ((mdifferentiable_const.mul mdifferentiable_eval_Ψ₃_weierstrassP_one_div).mul
    ((mdifferentiable_const.mul (mdifferentiable_weierstrassP_periodPair_one_div.pow 2)).sub
      (mdifferentiable_g₂_periodPair.div mdifferentiable_const fun _ ↦ by norm_num))).div
    (mdifferentiable_derivWeierstrassP_periodPair_one_div.pow 4)
    fun z ↦ pow_ne_zero 4 (derivWeierstrassP_periodPair_one_div_ne_zero hN z)

/-- The second Tate normal form coefficient `b(z)` of `(E_z, 1 / N)` is holomorphic on `ℍ`. For
`N < 3` it is identically `0`. -/
theorem mdifferentiable_snd_tateNormalFormCoeffs_pointedWeierstrassCurve :
    MDiff fun z : ℍ ↦ (z.pointedWeierstrassCurve N).tateNormalFormCoeffs.2 := by
  obtain hN | hN := lt_or_ge N 3
  · simpa [tateNormalFormCoeffs_pointedWeierstrassCurve_of_lt_three hN] using mdifferentiable_const
  simp only [tateNormalFormCoeffs_pointedWeierstrassCurve]
  exact (mdifferentiable_eval_Ψ₃_weierstrassP_one_div.pow 3).div
    (mdifferentiable_derivWeierstrassP_periodPair_one_div.pow 8)
    fun z ↦ pow_ne_zero 8 (derivWeierstrassP_periodPair_one_div_ne_zero hN z)

/-- **The Tate normal form coefficients are `Γ₁(N)`-invariant**: those of `(E_{γ z}, 1 / N)` and
`(E_z, 1 / N)` agree for `γ ∈ Γ₁(N)`. -/
theorem tateNormalFormCoeffs_pointedWeierstrassCurve_smul_of_mem {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 N) (z : ℍ) :
    ((γ • z).pointedWeierstrassCurve N).tateNormalFormCoeffs =
      (z.pointedWeierstrassCurve N).tateNormalFormCoeffs := by
  obtain rfl | hN := eq_zero_or_neZero N
  · simp [tateNormalFormCoeffs_pointedWeierstrassCurve_of_lt_three]
  obtain ⟨C, hC⟩ := exists_smul_pointedWeierstrassCurve_eq_iff.mpr ⟨γ, hγ, rfl⟩
  rw [← hC, PointedWeierstrassCurve.tateNormalFormCoeffs_smul]

/-- **The Tate normal form coefficients are `Γ₁(N)`-invariant**: those of `(E_{γ z}, 1 / N)` and
`(E_z, 1 / N)` agree for `γ : Γ₁(N)`. -/
@[simp]
theorem tateNormalFormCoeffs_pointedWeierstrassCurve_smul (γ : Gamma1 N) (z : ℍ) :
    ((γ • z).pointedWeierstrassCurve N).tateNormalFormCoeffs =
      (z.pointedWeierstrassCurve N).tateNormalFormCoeffs :=
  tateNormalFormCoeffs_pointedWeierstrassCurve_smul_of_mem γ.property z

/-- For `N ≥ 4`, the Tate normal form coefficients of `(E_z, 1 / N)` are those of an elliptic curve
on which `(0, 0)` has exact order `N`. -/
theorem tateNormalFormCoeffs_pointedWeierstrassCurve_mem_tateNormalFormExactOrder (hN : 4 ≤ N)
    (z : ℍ) :
    (z.pointedWeierstrassCurve N).tateNormalFormCoeffs ∈
      PointedWeierstrassCurve.tateNormalFormExactOrder ℂ N :=
  have : NeZero N := ⟨by omega⟩
  PointedWeierstrassCurve.tateNormalFormCoeffs_mem_tateNormalFormExactOrder hN
    (pointedWeierstrassCurve_mem_exactOrder z)

end UpperHalfPlane

namespace TauCeti

variable {N : ℕ}

variable (N) in
/-- **`Γ₁(N) \ ℍ` and the Tate normal forms of level `N`.** For `N ≥ 4`, sending `z` to the
Tate normal form coefficients `(a, b)` of `E_z = ℂ / (ℤ z + ℤ)` with the point `1 / N` induces a
bijection from `Γ₁(N) \ ℍ` onto the pairs `(a, b)` for which `Y² + aXY + bY = X³ + bX²` is
elliptic and `(0, 0)` has exact order `N`. -/
noncomputable def gamma1QuotientEquivTateNormalForm (hN : 4 ≤ N) :
    MulAction.orbitRel.Quotient (Gamma1 N) ℍ ≃
      PointedWeierstrassCurve.tateNormalFormExactOrder ℂ N :=
  have : NeZero N := ⟨by omega⟩
  (gamma1QuotientEquivExactOrder N).trans
    (PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm ℂ hN)

/-- `gamma1QuotientEquivTateNormalForm` is the moduli bijection `gamma1QuotientEquivExactOrder`
followed by the classification of points of order `N ≥ 4` by their Tate normal form. -/
theorem gamma1QuotientEquivTateNormalForm_def [NeZero N] (hN : 4 ≤ N) :
    gamma1QuotientEquivTateNormalForm N hN = (gamma1QuotientEquivExactOrder N).trans
      (PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm ℂ hN) :=
  (rfl)

@[simp]
theorem coe_gamma1QuotientEquivTateNormalForm_mk (hN : 4 ≤ N) (z : ℍ) :
    (gamma1QuotientEquivTateNormalForm N hN ⟦z⟧ : ℂ × ℂ) =
      (z.pointedWeierstrassCurve N).tateNormalFormCoeffs := by
  have : NeZero N := ⟨by omega⟩
  rw [gamma1QuotientEquivTateNormalForm_def, Equiv.trans_apply, gamma1QuotientEquivExactOrder_mk,
    PointedWeierstrassCurve.coe_exactOrderQuotientEquivTateNormalForm_mk]


end TauCeti

namespace UpperHalfPlane

variable {N : ℕ}

/-- **The Tate normal form coefficients separate the `Γ₁(N)`-orbits.** For `N ≥ 4`, the
coefficients of the Tate normal form of `(E_z, 1 / N)` and `(E_{z'}, 1 / N)` agree exactly when
`z' = γ z` for some `γ ∈ Γ₁(N)`. In particular they are `Γ₁(N)`-invariant functions on `ℍ`. -/
theorem tateNormalFormCoeffs_pointedWeierstrassCurve_eq_iff (hN : 4 ≤ N) {z z' : ℍ} :
    (z.pointedWeierstrassCurve N).tateNormalFormCoeffs =
        (z'.pointedWeierstrassCurve N).tateNormalFormCoeffs ↔
      ∃ γ ∈ Gamma1 N, γ • z = z' := by
  rw [eq_comm, ← coe_gamma1QuotientEquivTateNormalForm_mk hN,
    ← coe_gamma1QuotientEquivTateNormalForm_mk hN, Subtype.coe_inj,
    (gamma1QuotientEquivTateNormalForm N hN).apply_eq_iff_eq, Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨γ, hγ⟩ ↦ ⟨γ, γ.property, hγ⟩, fun ⟨γ, hγ, h⟩ ↦ ⟨⟨γ, hγ⟩, h⟩⟩

end UpperHalfPlane
