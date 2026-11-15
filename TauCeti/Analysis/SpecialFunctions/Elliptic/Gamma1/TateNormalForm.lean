/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TateNormalForm
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.Moduli
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted

/-!
# The Tate normal form of `(E_z, 1 / N)`

For `z` in the upper half-plane and `N ≥ 4`, the complex elliptic curve `E_z = ℂ / (ℤ z + ℤ)`
with the point `1 / N` of exact order `N` has a Tate normal form
`Y² + a(z) XY + b(z) Y = X³ + b(z) X²`, with `1 / N` going to `(0, 0)`. This file shows that
`z ↦ (a(z), b(z))` is a holomorphic map from `ℍ` to the pairs `(a, b)` for which the Tate normal
form is elliptic and `(0, 0)` has exact order `N`
(`TauCeti.PointedWeierstrassCurve.tateNormalFormExactOrder`), and that it induces a bijection from
`Γ₁(N) \ ℍ` onto them (`TauCeti.gamma1QuotientEquivTateNormalForm`). In the coordinates of the
plane model `Spec ℤ[A, B][Δ⁻¹]` these pairs describe the complex points of the fine moduli scheme
`Y₁(N)`, so this is the analytic map `Γ₁(N) \ ℍ → Y₁(N)(ℂ)`; the complex structure of `Y₁(N)(ℂ)`
and the comparison with the scheme are not made here.

* **The coefficients.** With `x = ℘(1 / N; ℤ z + ℤ)`, `y = ℘'(1 / N; ℤ z + ℤ)` and
  `Q = Ψ₃(x) = 3 x⁴ - (3 / 2) g₂ x² - 3 g₃ x - g₂² / 16` the value of the `3`-division polynomial,
  `a(z) = 2 Q (3 x² - g₂ / 4) / y⁴` and `b(z) = Q³ / y⁸`
  (`UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve`).
* **Holomorphy.** `g₂ = (4 π⁴ / 3) E₄` and `g₃ = (8 π⁶ / 27) E₆` are holomorphic; so are the
  division values of `℘`, which are the weight-two Eisenstein series of a residue class, and those
  of `℘'`, which are `-2 N³` times the weight-three Eisenstein series
  `∑_{v ≡ (b₀, b₁) mod N} (v₀ z + v₁)⁻³`
  (`UpperHalfPlane.mdifferentiable_derivWeierstrassP_periodPair_div`). For `N ≥ 3` the point `1 / N`
  is not `2`-torsion, so `y` does not vanish and `a`, `b` are holomorphic.
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

* `UpperHalfPlane.mdifferentiable_derivWeierstrassP_periodPair_div`: the division values
  `z ↦ ℘'((b₀ z + b₁) / N; ℤ z + ℤ)` are holomorphic on `ℍ`.
* `UpperHalfPlane.tateNormalFormCoeffs_pointedWeierstrassCurve`: the coefficients of the Tate normal
  form of `(E_z, 1 / N)` in terms of `℘(1 / N)`, `℘'(1 / N)`, `g₂` and `g₃`.
* `UpperHalfPlane.mdifferentiable_tateNormalFormCoeffs_fst_pointedWeierstrassCurve`,
  `UpperHalfPlane.mdifferentiable_tateNormalFormCoeffs_snd_pointedWeierstrassCurve`: for `N ≥ 3`
  the coefficients are holomorphic on `ℍ`.
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

namespace TauCeti.UpperHalfPlane

/-- **The division values of `℘'` are holomorphic**: for `b ∈ ℤ²`, the function
`z ↦ ℘'((b₀ z + b₁) / M; ℤ z + ℤ)` is holomorphic on `ℍ`. For `M ≠ 0` it is `-2 M³` times the
weight-three Eisenstein series `∑_{v ≡ b mod M} (v₀ z + v₁)⁻³` of the residue class of `b`. -/
theorem mdifferentiable_derivWeierstrassP_periodPair_div (M : ℕ) (b : Fin 2 → ℤ) :
    MDiff fun z : ℍ ↦ ℘'[z.periodPair] (((b 0 : ℂ) * z + b 1) / M) := by
  rcases eq_or_ne M 0 with rfl | hM
  · simpa [PeriodPair.derivWeierstrassP_zero] using
      (mdifferentiable_const : MDiff fun _ : ℍ ↦ (0 : ℂ))
  have : NeZero M := ⟨hM⟩
  have hM₀ : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have h (z : ℍ) : ℘'[z.periodPair] (((b 0 : ℂ) * z + b 1) / M) = -2 * (M : ℂ) ^ 3 *
      EisensteinSeries.weightedEisensteinSeries (Pi.single (((↑) : ℤ → ZMod M) ∘ b) 1) 3 z := by
    rw [EisensteinSeries.weightedEisensteinSeries_single_eq_tsum,
      ← (hasSum_derivWeierstrassP_periodPair z _).tsum_eq,
      ← (Equiv.neg (Fin 2 → ℤ)).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun y ↦ ?_
    -- the term of `-y` is `-2 M³ (v₀ z + v₁)⁻³` at `v = b + M y`
    have hv : ((b 0 : ℂ) * z + b 1) / M - ((-y) 0 * (z : ℂ) + (-y) 1) =
        (((b + M • y) 0 : ℤ) * (z : ℂ) + ((b + M • y) 1 : ℤ)) / M := by
      simp only [Pi.add_apply, Pi.neg_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      push_cast
      field_simp
      ring
    rw [Equiv.neg_apply, hv, EisensteinSeries.eisSummand, zpow_neg, div_pow, div_div_eq_mul_div]
    norm_cast
  rw [funext h, ← EisensteinSeries.coe_weightedEisensteinSeriesSIF]
  exact mdifferentiable_const.mul
    (EisensteinSeries.weightedEisensteinSeries_mdifferentiable _ (by norm_num))

end TauCeti.UpperHalfPlane

namespace UpperHalfPlane

variable {N : ℕ}

/-- For `N ≥ 3`, the point `1 / N` of `E_z` is not `2`-torsion, so `℘'(1 / N)` does not vanish. -/
theorem derivWeierstrassP_periodPair_one_div_ne_zero (hN : 3 ≤ N) (z : ℍ) :
    ℘'[z.periodPair] (1 / N) ≠ 0 := by
  have : NeZero N := ⟨by omega⟩
  have hP := addOrderOf_weierstrassPoint_one_div (N := N) z
  have hmem : (1 / N : ℂ) ∉ z.periodPair.lattice := by
    rw [← PeriodPair.weierstrassPoint_eq_zero_iff, ← AddMonoid.addOrderOf_eq_one_iff, hP]
    omega
  intro h₀
  rw [PeriodPair.weierstrassPoint_of_notMem _ hmem] at hP
  have hns := z.periodPair.nonsingular_weierstrassP hmem
  have h₂ : WeierstrassCurve.Affine.Point.some _ _ hns + .some _ _ hns = 0 :=
    (WeierstrassCurve.Affine.Point.some_add_self_eq_zero_iff hns).mpr (by
      simp only [WeierstrassCurve.Affine.evalEval_polynomialY, PeriodPair.weierstrassCurve_a₁,
        PeriodPair.weierstrassCurve_a₃, h₀]
      ring)
  rw [← two_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hP] at h₂
  have := Nat.le_of_dvd two_pos h₂
  omega

/-- **The Tate normal form coefficients of `(E_z, 1 / N)`.** With `x = ℘(1 / N)`, `y = ℘'(1 / N)`
and `Q = Ψ₃(x)` the value of the `3`-division polynomial of `E_z`, the coefficients are
`a = 2 Q (3 x² - g₂ / 4) / y⁴` and `b = Q³ / y⁸`. -/
theorem tateNormalFormCoeffs_pointedWeierstrassCurve (hN : 2 ≤ N) (z : ℍ) :
    (z.pointedWeierstrassCurve N).tateNormalFormCoeffs =
      (2 * z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) *
          (3 * ℘[z.periodPair] (1 / N) ^ 2 - z.periodPair.g₂ / 4) / ℘'[z.periodPair] (1 / N) ^ 4,
        z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) ^ 3 /
          ℘'[z.periodPair] (1 / N) ^ 8) := by
  have : NeZero N := ⟨by omega⟩
  have hmem : (1 / N : ℂ) ∉ z.periodPair.lattice := by
    rw [← PeriodPair.weierstrassPoint_eq_zero_iff, ← AddMonoid.addOrderOf_eq_one_iff,
      addOrderOf_weierstrassPoint_one_div]
    omega
  rw [pointedWeierstrassCurve_def, PeriodPair.weierstrassPoint_of_notMem _ hmem,
    PointedWeierstrassCurve.tateNormalFormCoeffs_mk_some]
  simp only [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY,
    PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃,
    PeriodPair.weierstrassCurve_a₄, Prod.mk.injEq]
  constructor <;> ring

/-- The division value `℘'(1 / N; ℤ z + ℤ)` is holomorphic. -/
private theorem mdifferentiable_derivWeierstrassP_periodPair_one_div :
    MDiff fun z : ℍ ↦ ℘'[z.periodPair] (1 / N) := by
  simpa using TauCeti.UpperHalfPlane.mdifferentiable_derivWeierstrassP_periodPair_div N ![0, 1]

/-- The division value `℘(1 / N; ℤ z + ℤ)` is holomorphic. -/
private theorem mdifferentiable_weierstrassP_periodPair_one_div [NeZero N] :
    MDiff fun z : ℍ ↦ ℘[z.periodPair] (1 / N) := by
  simpa using EisensteinSeries.mdifferentiable_weierstrassP_periodPair_div (N := N) ![0, 1]

/-- The value `Ψ₃(℘(1 / N)) = 3 x⁴ - (3 / 2) g₂ x² - 3 g₃ x - g₂² / 16` of the `3`-division
polynomial of `E_z` at `x = ℘(1 / N)` is holomorphic in `z`. -/
private theorem mdifferentiable_eval_Ψ₃_weierstrassP_one_div [NeZero N] :
    MDiff fun z : ℍ ↦ z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) := by
  have hx := mdifferentiable_weierstrassP_periodPair_one_div (N := N)
  have hg₂ := mdifferentiable_g₂_periodPair
  have hg₃ := mdifferentiable_g₃_periodPair
  have h (z : ℍ) : z.periodPair.weierstrassCurve.Ψ₃.eval (℘[z.periodPair] (1 / N)) =
      3 * ℘[z.periodPair] (1 / N) ^ 4 - 3 / 2 * z.periodPair.g₂ * ℘[z.periodPair] (1 / N) ^ 2 -
        3 * z.periodPair.g₃ * ℘[z.periodPair] (1 / N) - z.periodPair.g₂ ^ 2 / 16 := by
    simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
      PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄,
      PeriodPair.weierstrassCurve_a₆, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  rw [funext h]
  exact (((mdifferentiable_const.mul (hx.pow 4)).sub
    ((mdifferentiable_const.mul hg₂).mul (hx.pow 2))).sub
      ((mdifferentiable_const.mul hg₃).mul hx)).sub
        ((hg₂.pow 2).div mdifferentiable_const fun _ ↦ by norm_num)

/-- For `N ≥ 3`, the first Tate normal form coefficient `a(z)` of `(E_z, 1 / N)` is holomorphic on
`ℍ`. -/
theorem mdifferentiable_tateNormalFormCoeffs_fst_pointedWeierstrassCurve (hN : 3 ≤ N) :
    MDiff fun z : ℍ ↦ (z.pointedWeierstrassCurve N).tateNormalFormCoeffs.1 := by
  have : NeZero N := ⟨by omega⟩
  simp only [tateNormalFormCoeffs_pointedWeierstrassCurve (by omega : 2 ≤ N)]
  exact ((mdifferentiable_const.mul mdifferentiable_eval_Ψ₃_weierstrassP_one_div).mul
    ((mdifferentiable_const.mul (mdifferentiable_weierstrassP_periodPair_one_div.pow 2)).sub
      (mdifferentiable_g₂_periodPair.div mdifferentiable_const fun _ ↦ by norm_num))).div
    (mdifferentiable_derivWeierstrassP_periodPair_one_div.pow 4)
    fun z ↦ pow_ne_zero 4 (derivWeierstrassP_periodPair_one_div_ne_zero hN z)

/-- For `N ≥ 3`, the second Tate normal form coefficient `b(z)` of `(E_z, 1 / N)` is holomorphic on
`ℍ`. -/
theorem mdifferentiable_tateNormalFormCoeffs_snd_pointedWeierstrassCurve (hN : 3 ≤ N) :
    MDiff fun z : ℍ ↦ (z.pointedWeierstrassCurve N).tateNormalFormCoeffs.2 := by
  have : NeZero N := ⟨by omega⟩
  simp only [tateNormalFormCoeffs_pointedWeierstrassCurve (by omega : 2 ≤ N)]
  exact (mdifferentiable_eval_Ψ₃_weierstrassP_one_div.pow 3).div
    (mdifferentiable_derivWeierstrassP_periodPair_one_div.pow 8)
    fun z ↦ pow_ne_zero 8 (derivWeierstrassP_periodPair_one_div_ne_zero hN z)

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
  haveI : NeZero N := ⟨by omega⟩
  (gamma1QuotientEquivExactOrder N).trans
    (PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm ℂ hN)

@[simp]
theorem gamma1QuotientEquivTateNormalForm_mk (hN : 4 ≤ N) (z : ℍ) :
    (gamma1QuotientEquivTateNormalForm N hN ⟦z⟧ : ℂ × ℂ) =
      (z.pointedWeierstrassCurve N).tateNormalFormCoeffs := by
  rw [gamma1QuotientEquivTateNormalForm, Equiv.trans_apply, gamma1QuotientEquivExactOrder_mk,
    PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm_mk]

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
  rw [eq_comm, ← gamma1QuotientEquivTateNormalForm_mk hN, ← gamma1QuotientEquivTateNormalForm_mk hN,
    Subtype.coe_inj, (gamma1QuotientEquivTateNormalForm N hN).apply_eq_iff_eq, Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨γ, hγ⟩ ↦ ⟨γ, γ.2, hγ⟩, fun ⟨γ, hγ, h⟩ ↦ ⟨⟨γ, hγ⟩, h⟩⟩

end UpperHalfPlane
