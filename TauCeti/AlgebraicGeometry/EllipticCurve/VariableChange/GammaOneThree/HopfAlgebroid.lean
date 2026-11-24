/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.Algebra.MvPolynomial.Invertible
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.GammaOneThree.Representable
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
import Mathlib.RingTheory.Trace.Basic

/-!
# The `Γ₁(3)` Weierstrass Hopf algebroid

Over any commutative base ring `R`, let `A' = BaseRing R = R[a₁, a₃]` be the coefficient ring of
the universal curve `universalCurve R = gammaOneThreeForm a₁ a₃` (`Y² + a₁XY + a₃Y = X³`) in
`Γ₁(3)` normal form, and let `Γ' = UniversalArrowRing R = ArrowRing (a₁ R) (a₃ R)` be the quotient
of `A'[r, s, t]` cutting out strict changes of variables `C = ⟨1, r, s, t⟩` whose target `C • W`
again has `a₂ = a₄ = a₆ = 0`.

`R`-algebra homomorphisms `UniversalArrowRing R →ₐ[R] S` classify pairs of a curve in `Γ₁(3)`
normal form over `S` and a strict `Γ₁(3)` change of variables out of it (`arrowEquiv`). This file
constructs the Hopf algebroid structure on `(BaseRing R, UniversalArrowRing R)` — Bauer's §7
presentation prior to specializing `a₃ = 1` or inverting `3` — together with the canonical
Hopf-algebroid morphism `(toBaseRing R, toUniversalArrowRing R)` from the level-one Weierstrass
Hopf algebroid `(ℤ[a₁, a₂, a₃, a₄, a₆], ℤ[a₁, ⋯, a₆][u, u⁻¹, r, s, t])`.

Because `toUniversalArrowRing R` specializes the scaling coordinate `u` to `1`, every integral
modular form `f` of level one (of arbitrary weight `k`) pulls back to an ungraded Hopf-algebroid
invariant in `invariantSubalgebra R = H⁰(A', Γ')`
(`rightUnit_toBaseRing_of_isIntegralModularForm`); in particular `c₄`, `c₆`, and `Δ` of
`universalCurve R` are `Γ'`-invariant. When `3` is invertible in `R`, the `Algebra.trace` transfer
commutes with the coproduct (`trace_coproduct`) and carries `rightUnit R (3 * a₁ R * a₃ R)` and
`rightUnit R (27 * a₃ R ^ 2)` to `2 * (universalCurve R).c₄` and `2 * (universalCurve R).c₆`.

## Main definitions

* `TauCeti.GammaOneThreeHopfAlgebroid.BaseRing R`: the polynomial ring `R[a₁, a₃]`.
* `TauCeti.GammaOneThreeHopfAlgebroid.universalCurve R`: the universal `Γ₁(3)` curve over
  `BaseRing R`.
* `TauCeti.GammaOneThreeHopfAlgebroid.UniversalArrowRing R`: the arrow algebra `Γ'` over
  `BaseRing R`.
* `TauCeti.GammaOneThreeHopfAlgebroid.rightUnit R`, `counit R`, `coproduct R`, `conjugation R`:
  the Hopf-algebroid structure maps `η_R`, `ε`, `Δ`, `c` (together with the `R`-algebra enhancement
  `rightUnitAlgHom R`).
* `TauCeti.GammaOneThreeHopfAlgebroid.invariantSubalgebra R`: the `R`-subalgebra `H⁰(A', Γ')` of
  elements `x ∈ BaseRing R` with `η_R x = η_L x`.
* `TauCeti.GammaOneThreeHopfAlgebroid.toBaseRing R`, `toUniversalArrowRing R`: the comparison
  morphism from `TauCeti.WeierstrassHopfAlgebroid`.

## Main results

* `rightUnit_a₁`, `rightUnit_a₃`, `rightUnit_three_mul_a₃`: explicit right-unit coordinate
  formulas on `a₁`, `a₃`, and `3a₃`.
* `counit_comp_algebraMap`, `counit_comp_rightUnit`: unit–counit identities.
* `coproduct_comp_algebraMap`, `coproduct_comp_rightUnit`, `coproduct_r`, `coproduct_s`,
  `coproduct_t`, `coproduct_eq_shearEquiv_comp_map`: left/right unit compatibility, explicit
  coordinate formulas (`Δr = r₁ + r₂`, `Δs = s₁ + s₂`, `Δt = t₁ + t₂ + s₁r₂`), and factorization
  through the groupoid shearing equivalence `ArrowRing.shearEquiv`.
* `pushoutLift_counit_id_comp_coproduct`, `pushoutLift_id_counit_comp_coproduct`,
  `coproduct_coassoc`: left/right counit laws and coassociativity.
* `conjugation_comp_algebraMap`, `conjugation_comp_rightUnit`, `conjugation_comp_conjugation`,
  `counit_comp_conjugation`, `pushoutLift_conjugation_id_comp_coproduct`,
  `pushoutLift_id_conjugation_comp_coproduct`: involution and antipode identities.
* `toUniversalArrowRing_comp_algebraMap`, `toUniversalArrowRing_comp_rightUnit`,
  `counit_comp_toUniversalArrowRing`, `conjugation_comp_toUniversalArrowRing`,
  `coproduct_comp_toUniversalArrowRing`: `(toBaseRing R, toUniversalArrowRing R)` is a morphism of
  Hopf algebroids.
* `rightUnit_toBaseRing_of_isIntegralModularForm`, `rightUnit_c₄`, `rightUnit_c₆`, `rightUnit_Δ`:
  level-one integral modular forms pull back to `H⁰(A', Γ')`.
* `trace_coproduct`, `trace_rightUnit_three_mul_a₁_mul_a₃`,
  `trace_rightUnit_twentySeven_mul_a₃_sq`: coproduct compatibility and right-unit values of the
  rank-`8` trace transfer when `[Invertible (3 : R)]`.

## Provenance

The Hopf-algebroid structure maps, `pushoutLift` statement idioms, theorem layout, and
`ArrowRing.ringHom_ext` proof strategy closely adapt `TauCeti.WeierstrassHopfAlgebroid` in
`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/HopfAlgebroid.lean` from the level-one
Weierstrass groupoid to strict `Γ₁(3)` normal-form arrows.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* Christian Carrick, J. Davies and S. van Nigtevecht, *The descent spectral sequence for topological
  modular forms*, arXiv:2412.01640v2, §4.2.
-/

public section

noncomputable section

namespace TauCeti.GammaOneThreeHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve TauCeti.WeierstrassChange

variable (R : Type*) [CommRing R]

/-! ### The base ring `A' = R[a₁, a₃]` and arrow ring `Γ'` -/

/-- The base ring `A' = R[a₁, a₃]` of the `Γ₁(3)` Hopf algebroid over `R`, with `X 0 = a₁` and
`X 1 = a₃`. -/
abbrev BaseRing : Type _ :=
  MvPolynomial (Fin 2) R

/-- The universal coefficient `a₁ = X 0` in `BaseRing R`. -/
def a₁ : BaseRing R :=
  X 0

/-- Explicit polynomial definition `a₁ R = X 0`. -/
theorem a₁_def : a₁ R = X 0 :=
  (rfl)

/-- The universal coefficient `a₃ = X 1` in `BaseRing R`. -/
def a₃ : BaseRing R :=
  X 1

/-- Explicit polynomial definition `a₃ R = X 1`. -/
theorem a₃_def : a₃ R = X 1 :=
  (rfl)

/-- The universal `Γ₁(3)` normal-form curve `Y² + a₁XY + a₃Y = X³` over `BaseRing R`. -/
def universalCurve : WeierstrassCurve (BaseRing R) :=
  gammaOneThreeForm (a₁ R) (a₃ R)

/-- Explicit definition of `universalCurve R` as `gammaOneThreeForm (a₁ R) (a₃ R)`. -/
theorem universalCurve_def : universalCurve R = gammaOneThreeForm (a₁ R) (a₃ R) :=
  (rfl)

@[simp]
theorem universalCurve_a₁ : (universalCurve R).a₁ = a₁ R := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_a₁ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₂ : (universalCurve R).a₂ = 0 := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_a₂ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₃ : (universalCurve R).a₃ = a₃ R := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_a₃ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₄ : (universalCurve R).a₄ = 0 := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_a₄ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₆ : (universalCurve R).a₆ = 0 := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_a₆ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_c₄ : (universalCurve R).c₄ = a₁ R ^ 4 - 24 * a₁ R * a₃ R := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_c₄ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_c₆ :
    (universalCurve R).c₆ = -a₁ R ^ 6 + 36 * a₁ R ^ 3 * a₃ R - 216 * a₃ R ^ 2 := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_c₆ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_Δ : (universalCurve R).Δ = a₁ R ^ 3 * a₃ R ^ 3 - 27 * a₃ R ^ 4 := by
  rw [universalCurve_def]
  exact gammaOneThreeForm_Δ (a₁ R) (a₃ R)

/-- A ring homomorphism out of `BaseRing R` is determined by its restriction to `R` and its values
on `a₁ R` and `a₃ R`. -/
theorem baseRing_ringHom_ext {S : Type*} [CommRing S] {f g : BaseRing R →+* S}
    (hR : f.comp (algebraMap R _) = g.comp (algebraMap R _))
    (h₁ : f (a₁ R) = g (a₁ R)) (h₃ : f (a₃ R) = g (a₃ R)) : f = g :=
  MvPolynomial.ringHom_ext' hR fun i ↦ by fin_cases i <;> assumption

/-- The arrow ring `Γ'` of the `Γ₁(3)` Hopf algebroid over `R`. -/
abbrev UniversalArrowRing : Type _ :=
  ArrowRing (a₁ R) (a₃ R)

/-- The coordinate `r` in `UniversalArrowRing R`. -/
abbrev r : UniversalArrowRing R :=
  ArrowRing.r

/-- The coordinate `s` in `UniversalArrowRing R`. -/
abbrev s : UniversalArrowRing R :=
  ArrowRing.s

/-- The coordinate `t` in `UniversalArrowRing R`. -/
abbrev t : UniversalArrowRing R :=
  ArrowRing.t

/-- The universal strict `Γ₁(3)` change of variables `⟨1, r, s, t⟩` over `UniversalArrowRing R`. -/
abbrev universalChange : VariableChange (UniversalArrowRing R) :=
  ArrowRing.universalChange (a₁ R) (a₃ R)

private theorem isStrictGammaOneThreeChange_eval₂Hom {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    IsStrictGammaOneThreeChange
      (eval₂Hom (algebraMap R S) ![p.val.1.1, p.val.1.2] (a₁ R))
      (eval₂Hom (algebraMap R S) ![p.val.1.1, p.val.1.2] (a₃ R)) p.val.2 := by
  simpa [a₁_def, a₃_def] using p.property

private def mkArrowAlgHom {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    UniversalArrowRing R →ₐ[R] S :=
  AlgHom.mk
    (ArrowRing.lift ⟨(eval₂Hom (algebraMap R S) ![p.val.1.1, p.val.1.2], p.val.2),
      isStrictGammaOneThreeChange_eval₂Hom R p⟩)
    fun x ↦ by
      rw [RingHom.toFun_eq_coe,
        IsScalarTower.algebraMap_apply R (BaseRing R) (UniversalArrowRing R),
        ArrowRing.lift_algebraMap]
      exact eval₂Hom_C _ _ x

@[simp]
private theorem coe_ringHom_mkArrowAlgHom {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (mkArrowAlgHom R p : UniversalArrowRing R →+* S) =
      ArrowRing.lift ⟨(eval₂Hom (algebraMap R S) ![p.val.1.1, p.val.1.2], p.val.2),
        isStrictGammaOneThreeChange_eval₂Hom R p⟩ :=
  rfl

@[simp]
private theorem mkArrowAlgHom_apply {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2})
    (y : UniversalArrowRing R) :
    mkArrowAlgHom R p y = (mkArrowAlgHom R p : UniversalArrowRing R →+* S) y :=
  rfl

/-- **`R`-algebra homomorphisms `UniversalArrowRing R →ₐ[R] S` classify strict `Γ₁(3)` arrows**
over `S`. -/
def arrowEquiv (S : Type*) [CommRing S] [Algebra R S] :
    (UniversalArrowRing R →ₐ[R] S) ≃
      {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2} where
  toFun k := ⟨((k (algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R)),
      k (algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R))),
    (universalChange R).map (k : UniversalArrowRing R →+* S)),
    (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R)).map
      (k : UniversalArrowRing R →+* S)⟩
  invFun := mkArrowAlgHom R
  left_inv k := by
    apply AlgHom.toRingHom_injective
    refine ArrowRing.ringHom_ext (baseRing_ringHom_ext R (RingHom.ext fun x ↦ ?_) ?_ ?_) ?_
    · simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply R (BaseRing R) (UniversalArrowRing R),
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, coe_ringHom_mkArrowAlgHom, ArrowRing.lift_algebraMap,
        RingHom.coe_coe]
      simp [a₁_def]
    · simp only [RingHom.comp_apply, coe_ringHom_mkArrowAlgHom, ArrowRing.lift_algebraMap,
        RingHom.coe_coe]
      simp [a₃_def]
    · simp
  right_inv p := by
    refine Subtype.ext (Prod.ext (Prod.ext ?_ ?_) ?_)
    · simp only [mkArrowAlgHom_apply, coe_ringHom_mkArrowAlgHom, ArrowRing.lift_algebraMap]
      simp [a₁_def]
    · simp only [mkArrowAlgHom_apply, coe_ringHom_mkArrowAlgHom, ArrowRing.lift_algebraMap]
      simp [a₃_def]
    · simp

@[simp]
theorem arrowEquiv_apply {S : Type*} [CommRing S] [Algebra R S] (k : UniversalArrowRing R →ₐ[R] S) :
    arrowEquiv R S k =
      ⟨((k (algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R)),
          k (algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R))),
        (universalChange R).map (k : UniversalArrowRing R →+* S)),
        (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R)).map
          (k : UniversalArrowRing R →+* S)⟩ :=
  (rfl)

@[simp]
theorem arrowEquiv_symm_algebraMap_a₁ {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (arrowEquiv R S).symm p (algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R)) = p.val.1.1 :=
  congrArg (fun q ↦ q.val.1.1) ((arrowEquiv R S).right_inv p)

@[simp]
theorem arrowEquiv_symm_algebraMap_a₃ {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (arrowEquiv R S).symm p (algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R)) = p.val.1.2 :=
  congrArg (fun q ↦ q.val.1.2) ((arrowEquiv R S).right_inv p)

@[simp]
theorem universalChange_map_arrowEquiv_symm {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (universalChange R).map
      (((arrowEquiv R S).symm p : UniversalArrowRing R →ₐ[R] S) : UniversalArrowRing R →+* S) =
      p.val.2 :=
  congrArg (fun q ↦ q.val.2) ((arrowEquiv R S).right_inv p)

@[simp]
theorem arrowEquiv_symm_r {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (arrowEquiv R S).symm p (r R) = p.val.2.r := by
  simpa only [VariableChange.map_r, RingHom.coe_coe, ArrowRing.universalChange_r] using
    congrArg VariableChange.r (universalChange_map_arrowEquiv_symm R p)

@[simp]
theorem arrowEquiv_symm_s {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (arrowEquiv R S).symm p (s R) = p.val.2.s := by
  simpa only [VariableChange.map_s, RingHom.coe_coe, ArrowRing.universalChange_s] using
    congrArg VariableChange.s (universalChange_map_arrowEquiv_symm R p)

@[simp]
theorem arrowEquiv_symm_t {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGammaOneThreeChange p.1.1 p.1.2 p.2}) :
    (arrowEquiv R S).symm p (t R) = p.val.2.t := by
  simpa only [VariableChange.map_t, RingHom.coe_coe, ArrowRing.universalChange_t] using
    congrArg VariableChange.t (universalChange_map_arrowEquiv_symm R p)

/-- The **right unit** `η_R : BaseRing R →ₐ[R] UniversalArrowRing R` as an `R`-algebra
homomorphism, classifying the target `universalChange R • universalCurve R` of the universal strict
`Γ₁(3)` arrow. -/
def rightUnitAlgHom : BaseRing R →ₐ[R] UniversalArrowRing R :=
  aeval ![algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) + 2 * s R,
    algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R) +
      r R * algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) + 2 * t R]

/-- The **right unit** `η_R : BaseRing R →+* UniversalArrowRing R` as a ring homomorphism; the left
unit `η_L` is `algebraMap (BaseRing R) (UniversalArrowRing R)`. -/
def rightUnit : BaseRing R →+* UniversalArrowRing R :=
  (rightUnitAlgHom R).toRingHom

@[simp]
theorem coe_rightUnitAlgHom :
    (rightUnitAlgHom R : BaseRing R →+* UniversalArrowRing R) = rightUnit R :=
  (rfl)

@[simp]
theorem rightUnitAlgHom_apply (x : BaseRing R) : rightUnitAlgHom R x = rightUnit R x :=
  (rfl)

@[simp]
theorem rightUnit_C (c : R) : rightUnit R (C c) = algebraMap R (UniversalArrowRing R) c := by
  rw [← rightUnitAlgHom_apply]
  exact (rightUnitAlgHom R).commutes c

theorem rightUnit_algebraMap (c : R) :
    rightUnit R (algebraMap R (BaseRing R) c) = algebraMap R (UniversalArrowRing R) c := by
  rw [← rightUnitAlgHom_apply]
  exact (rightUnitAlgHom R).commutes c

@[simp]
theorem rightUnit_comp_C :
    (rightUnit R).comp C = algebraMap R (UniversalArrowRing R) :=
  RingHom.ext (rightUnit_C R)

theorem rightUnit_comp_algebraMap :
    (rightUnit R).comp (algebraMap R (BaseRing R)) = algebraMap R (UniversalArrowRing R) :=
  RingHom.ext (rightUnit_algebraMap R)

/-- Explicit right-unit formula on `a₁`: `η_R(a₁) = η_L(a₁) + 2s`. -/
@[simp]
theorem rightUnit_a₁ :
    rightUnit R (a₁ R) = algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) + 2 * s R := by
  conv_lhs =>
    rw [← rightUnitAlgHom_apply, rightUnitAlgHom]
    arg 2
    rw [a₁_def]
  simp

/-- Explicit right-unit formula on `a₃`: `η_R(a₃) = η_L(a₃) + r η_L(a₁) + 2t`. -/
@[simp]
theorem rightUnit_a₃ :
    rightUnit R (a₃ R) =
      algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R) +
        r R * algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) + 2 * t R := by
  conv_lhs =>
    rw [← rightUnitAlgHom_apply, rightUnitAlgHom]
    arg 2
    rw [a₃_def]
  simp

/-- Denominator-free expansion of `rightUnit R (3 * a₃ R)` onto `{1, s, s², t}` over any
commutative ring `R`. -/
theorem rightUnit_three_mul_a₃ :
    rightUnit R (3 * a₃ R) =
      algebraMap (BaseRing R) (UniversalArrowRing R) (3 * a₃ R) +
        algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R ^ 2) * s R +
        algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) * s R ^ 2 +
        6 * t R := by
  rw [map_mul, map_ofNat, rightUnit_a₃, map_mul, map_ofNat, map_pow]
  linear_combination
    algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R) *
      ArrowRing.three_mul_r (a₁ := a₁ R) (a₃ := a₃ R)

/-- Pushing `universalCurve R` along `rightUnit R` gives `universalChange R • universalCurve R`. -/
@[simp]
theorem map_rightUnit_universalCurve :
    (universalCurve R).map (rightUnit R) =
      universalChange R • (universalCurve R).map
        (algebraMap (BaseRing R) (UniversalArrowRing R)) := by
  rw [universalCurve_def, map_gammaOneThreeForm, map_gammaOneThreeForm,
    (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R)).smul_eq]
  simp

/-- `ArrowRing.target (a₁ R) (a₃ R)` coincides with `(universalCurve R).map (rightUnit R)`. -/
theorem target_eq_map_rightUnit :
    ArrowRing.target (a₁ R) (a₃ R) = (universalCurve R).map (rightUnit R) := by
  rw [map_rightUnit_universalCurve, universalCurve_def, ArrowRing.target_def]

/-- The `R`-subalgebra `H⁰(A', Γ')` of Hopf-algebroid invariants in `BaseRing R`, defined as the
equalizer of `rightUnitAlgHom R` and the left unit
`IsScalarTower.toAlgHom R (BaseRing R) (UniversalArrowRing R)`. -/
def invariantSubalgebra : Subalgebra R (BaseRing R) :=
  AlgHom.equalizer (rightUnitAlgHom R)
    (IsScalarTower.toAlgHom R (BaseRing R) (UniversalArrowRing R))

@[simp]
theorem mem_invariantSubalgebra {x : BaseRing R} :
    x ∈ invariantSubalgebra R ↔
      rightUnit R x = algebraMap (BaseRing R) (UniversalArrowRing R) x :=
  Iff.rfl

/-! ### Counit, coproduct and conjugation -/

/-- The **counit** `ε : UniversalArrowRing R →+* BaseRing R`, classifying the identity strict
arrows. -/
def counit : UniversalArrowRing R →+* BaseRing R :=
  ArrowRing.lift ⟨(RingHom.id (BaseRing R), 1), IsStrictGammaOneThreeChange.one _ _⟩

/-- `ε η_L = id`: the source of an identity strict arrow is the original curve. -/
@[simp]
theorem counit_comp_algebraMap :
    (counit R).comp (algebraMap (BaseRing R) (UniversalArrowRing R)) = RingHom.id (BaseRing R) := by
  rw [counit]
  exact ArrowRing.lift_comp_algebraMap _

@[simp]
theorem counit_algebraMap (x : BaseRing R) :
    counit R (algebraMap (BaseRing R) (UniversalArrowRing R) x) = x :=
  RingHom.congr_fun (counit_comp_algebraMap R) x

@[simp]
theorem universalChange_map_counit : (universalChange R).map (counit R) = 1 := by
  rw [counit]
  exact ArrowRing.map_lift _

@[simp]
theorem counit_r : counit R (r R) = 0 := by
  rw [counit]
  exact ArrowRing.lift_r _

@[simp]
theorem counit_s : counit R (s R) = 0 := by
  rw [counit]
  exact ArrowRing.lift_s _

@[simp]
theorem counit_t : counit R (t R) = 0 := by
  rw [counit]
  exact ArrowRing.lift_t _

/-- `ε η_R = id`: the target of an identity strict arrow is the original curve. -/
@[simp]
theorem counit_comp_rightUnit : (counit R).comp (rightUnit R) = RingHom.id (BaseRing R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap,
      IsScalarTower.algebraMap_apply R (BaseRing R) (UniversalArrowRing R), counit_algebraMap,
      RingHom.id_apply]
  · simp [map_ofNat]
  · simp [map_ofNat]

@[simp]
theorem counit_rightUnit (x : BaseRing R) : counit R (rightUnit R x) = x :=
  RingHom.congr_fun (counit_comp_rightUnit R) x

/-- The tensor square `Γ' ⊗_{A'} Γ'`, realized as
`ArrowRing (rightUnit R (a₁ R)) (rightUnit R (a₃ R))` over `UniversalArrowRing R`. -/
abbrev TensorSquare : Type _ :=
  ArrowRing (rightUnit R (a₁ R)) (rightUnit R (a₃ R))

/-- The **coproduct** `Δ : UniversalArrowRing R →+* TensorSquare R`, classifying composition
`C₂ * C₁` of strict `Γ₁(3)` arrows. -/
def coproduct : UniversalArrowRing R →+* TensorSquare R :=
  ArrowRing.lift ⟨((algebraMap (UniversalArrowRing R) (TensorSquare R)).comp
      (algebraMap (BaseRing R) (UniversalArrowRing R)),
    ArrowRing.universalChange (rightUnit R (a₁ R)) (rightUnit R (a₃ R)) *
      (universalChange R).map (algebraMap (UniversalArrowRing R) (TensorSquare R))),
    ArrowRing.isStrictGammaOneThreeChange_universalChange_mul_map
      (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R))
      (by simp) (by simp)⟩

/-- `Δ η_L = (η_L ⊗ 1) η_L`: the source of a composite arrow is the source of its first factor. -/
@[simp]
theorem coproduct_comp_algebraMap :
    (coproduct R).comp (algebraMap (BaseRing R) (UniversalArrowRing R)) =
      (algebraMap (UniversalArrowRing R) (TensorSquare R)).comp
        (algebraMap (BaseRing R) (UniversalArrowRing R)) := by
  rw [coproduct]
  exact ArrowRing.lift_comp_algebraMap _

@[simp]
theorem coproduct_algebraMap (x : BaseRing R) :
    coproduct R (algebraMap (BaseRing R) (UniversalArrowRing R) x) =
      algebraMap (UniversalArrowRing R) (TensorSquare R)
        (algebraMap (BaseRing R) (UniversalArrowRing R) x) :=
  RingHom.congr_fun (coproduct_comp_algebraMap R) x

@[simp]
theorem universalChange_map_coproduct :
    (universalChange R).map (coproduct R) =
      ArrowRing.universalChange (rightUnit R (a₁ R)) (rightUnit R (a₃ R)) *
        (universalChange R).map (algebraMap (UniversalArrowRing R) (TensorSquare R)) := by
  rw [coproduct]
  exact ArrowRing.map_lift _

/-- `Δr = r₁ + r₂` in `TensorSquare R`. -/
theorem coproduct_r :
    coproduct R (r R) =
      algebraMap (UniversalArrowRing R) (TensorSquare R) (r R) +
        ArrowRing.map (rightUnit R) (r R) := by
  have h := congrArg VariableChange.r (universalChange_map_coproduct R)
  simp only [VariableChange.map_r, VariableChange.map_u, ArrowRing.universalChange_r,
    VariableChange.mul_def, ArrowRing.universalChange_u, map_one, Units.val_one, one_pow,
    mul_one] at h
  rw [ArrowRing.mapOfEq_r]
  linear_combination h

/-- `Δs = s₁ + s₂` in `TensorSquare R`. -/
theorem coproduct_s :
    coproduct R (s R) =
      algebraMap (UniversalArrowRing R) (TensorSquare R) (s R) +
        ArrowRing.map (rightUnit R) (s R) := by
  have h := congrArg VariableChange.s (universalChange_map_coproduct R)
  simp only [VariableChange.map_s, VariableChange.map_u, ArrowRing.universalChange_s,
    VariableChange.mul_def, ArrowRing.universalChange_u, map_one, Units.val_one, one_mul] at h
  rw [ArrowRing.mapOfEq_s]
  linear_combination h

/-- `Δt = t₁ + t₂ + s₁r₂` in `TensorSquare R`. -/
theorem coproduct_t :
    coproduct R (t R) =
      algebraMap (UniversalArrowRing R) (TensorSquare R) (t R) +
        ArrowRing.map (rightUnit R) (t R) +
        algebraMap (UniversalArrowRing R) (TensorSquare R) (s R) *
          ArrowRing.map (rightUnit R) (r R) := by
  have h := congrArg VariableChange.t (universalChange_map_coproduct R)
  simp only [VariableChange.map_t, VariableChange.map_u, VariableChange.map_s,
    ArrowRing.universalChange_u, ArrowRing.universalChange_r, ArrowRing.universalChange_s,
    ArrowRing.universalChange_t, VariableChange.mul_def, map_one, Units.val_one, one_pow,
    mul_one] at h
  rw [ArrowRing.mapOfEq_t, ArrowRing.mapOfEq_r]
  linear_combination h

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem coproduct_comp_rightUnit :
    (coproduct R).comp (rightUnit R) =
      (ArrowRing.map (rightUnit R)).comp (rightUnit R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap,
      IsScalarTower.algebraMap_apply R (BaseRing R) (UniversalArrowRing R), coproduct_algebraMap,
      ArrowRing.mapOfEq_algebraMap]
  · simp only [RingHom.comp_apply, rightUnit_a₁, map_add, map_mul, map_ofNat, coproduct_algebraMap,
      coproduct_s, ArrowRing.mapOfEq_algebraMap, ArrowRing.mapOfEq_s]
    ring
  · simp only [RingHom.comp_apply, rightUnit_a₃, map_add, map_mul, map_ofNat, coproduct_algebraMap,
      coproduct_r, coproduct_t, ArrowRing.mapOfEq_algebraMap, ArrowRing.mapOfEq_r,
      ArrowRing.mapOfEq_t, rightUnit_a₁]
    ring

@[simp]
theorem coproduct_rightUnit (x : BaseRing R) :
    coproduct R (rightUnit R x) = ArrowRing.map (rightUnit R) (rightUnit R x) :=
  RingHom.congr_fun (coproduct_comp_rightUnit R) x

/-- If `k : TensorSquare R →+* S` classifies a composable pair of strict `Γ₁(3)` arrows, then
`k ∘ Δ` classifies their composite. -/
theorem universalChange_map_comp_coproduct {S : Type*} [CommRing S] (k : TensorSquare R →+* S) :
    (universalChange R).map (k.comp (coproduct R)) =
      (universalChange R).map (k.comp (ArrowRing.map (rightUnit R))) *
        (universalChange R).map (k.comp (algebraMap (UniversalArrowRing R) (TensorSquare R))) := by
  simp [← VariableChange.map_map]

/-- The coproduct equals the groupoid shearing equivalence composed with scalar extension along the
left unit: `Δ = shearEquiv ∘ map η_L`. -/
theorem coproduct_eq_shearEquiv_comp_map :
    coproduct R =
      (ArrowRing.shearEquiv (a₁' := rightUnit R (a₁ R)) (a₃' := rightUnit R (a₃ R))
        (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R))
        (by simp) (by simp) :
          ArrowRing (algebraMap (BaseRing R) (UniversalArrowRing R) (a₁ R))
            (algebraMap (BaseRing R) (UniversalArrowRing R) (a₃ R)) →+* TensorSquare R).comp
        (ArrowRing.map (algebraMap (BaseRing R) (UniversalArrowRing R))) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- **Left counit law** `(ε ⊗ id) Δ = id`. -/
theorem pushoutLift_counit_id_comp_coproduct :
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨((algebraMap (BaseRing R) (UniversalArrowRing R)).comp (counit R),
        RingHom.id (UniversalArrowRing R)), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
      (coproduct R) = RingHom.id (UniversalArrowRing R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Right counit law** `(id ⊗ ε) Δ = id`. -/
theorem pushoutLift_id_counit_comp_coproduct :
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨(RingHom.id (UniversalArrowRing R), (rightUnit R).comp (counit R)), by
        rw [RingHom.comp_assoc, counit_comp_algebraMap, RingHom.comp_id, RingHom.id_comp]⟩).comp
      (coproduct R) = RingHom.id (UniversalArrowRing R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- The triple tensor product `Γ' ⊗_{A'} Γ' ⊗_{A'} Γ'`. -/
abbrev TensorCube : Type _ :=
  ArrowRing (B := TensorSquare R)
    (ArrowRing.map (rightUnit R) (rightUnit R (a₁ R)))
    (ArrowRing.map (rightUnit R) (rightUnit R (a₃ R)))

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the coproduct. -/
theorem coproduct_coassoc :
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨((algebraMap (TensorSquare R) (TensorCube R)).comp (coproduct R),
        ArrowRing.mapOfEq ((ArrowRing.map (rightUnit R)).comp (rightUnit R)) rfl rfl), by
        dsimp only
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit,
          ArrowRing.mapOfEq_comp_algebraMap]⟩).comp (coproduct R) =
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨((algebraMap (TensorSquare R) (TensorCube R)).comp
          (algebraMap (UniversalArrowRing R) (TensorSquare R)),
        (ArrowRing.map (ArrowRing.map (rightUnit R))).comp (coproduct R)),
        RingHom.ext fun x ↦ by simp⟩).comp (coproduct R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp only [universalChange_map_comp_coproduct, ArrowRing.pushoutLiftOfEq_comp_mapOfEq,
    ArrowRing.pushoutLiftOfEq_comp_algebraMap]
  simp only [ArrowRing.mapOfEq_comp_algebraMap, ← VariableChange.map_map,
    ArrowRing.universalChange_map_mapOfEq, mul_assoc]

/-- The **conjugation** `c : UniversalArrowRing R →+* UniversalArrowRing R`, classifying the inverse
strict arrow `C⁻¹ : C • W → W`. -/
def conjugation : UniversalArrowRing R →+* UniversalArrowRing R :=
  ArrowRing.lift ⟨(rightUnit R, (universalChange R)⁻¹), by
    simpa using (ArrowRing.isStrictGammaOneThreeChange_universalChange (a₁ R) (a₃ R)).inv⟩

/-- `c η_L = η_R`: the source of `C⁻¹` is the target of `C`. -/
@[simp]
theorem conjugation_comp_algebraMap :
    (conjugation R).comp (algebraMap (BaseRing R) (UniversalArrowRing R)) = rightUnit R := by
  rw [conjugation]
  exact ArrowRing.lift_comp_algebraMap _

@[simp]
theorem conjugation_algebraMap (x : BaseRing R) :
    conjugation R (algebraMap (BaseRing R) (UniversalArrowRing R) x) = rightUnit R x :=
  RingHom.congr_fun (conjugation_comp_algebraMap R) x

@[simp]
theorem universalChange_map_conjugation :
    (universalChange R).map (conjugation R) = (universalChange R)⁻¹ := by
  rw [conjugation]
  exact ArrowRing.map_lift _

/-- Conjugation negates the horizontal translation coordinate: `c(r) = -r`. -/
@[simp]
theorem conjugation_r : conjugation R (r R) = -r R := by
  have h := congrArg VariableChange.r (universalChange_map_conjugation R)
  simp only [VariableChange.map_r, ArrowRing.universalChange_u, ArrowRing.universalChange_r,
    VariableChange.inv_def, inv_one, Units.val_one, one_pow, mul_one] at h
  exact h

/-- Conjugation negates the shear coordinate: `c(s) = -s`. -/
@[simp]
theorem conjugation_s : conjugation R (s R) = -s R := by
  have h := congrArg VariableChange.s (universalChange_map_conjugation R)
  simp only [VariableChange.map_s, ArrowRing.universalChange_u, ArrowRing.universalChange_s,
    VariableChange.inv_def, inv_one, Units.val_one, mul_one] at h
  exact h

/-- Conjugation sends `t` to `-t + r * s`, with the cross-term `r * s` arising from inverting
`(x, y) ↦ (x + r, y + sx + t)`. -/
@[simp]
theorem conjugation_t : conjugation R (t R) = -t R + r R * s R := by
  have h := congrArg VariableChange.t (universalChange_map_conjugation R)
  simp only [VariableChange.map_t, ArrowRing.universalChange_u, ArrowRing.universalChange_r,
    ArrowRing.universalChange_s, ArrowRing.universalChange_t, VariableChange.inv_def,
    inv_one, Units.val_one, one_pow, mul_one] at h
  linear_combination h

/-- `c η_R = η_L`: the target of `C⁻¹` is the source of `C`. -/
@[simp]
theorem conjugation_comp_rightUnit :
    (conjugation R).comp (rightUnit R) = algebraMap (BaseRing R) (UniversalArrowRing R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap,
      IsScalarTower.algebraMap_apply R (BaseRing R) (UniversalArrowRing R), conjugation_algebraMap]
  · simp only [RingHom.comp_apply, rightUnit_a₁, map_add, map_mul, map_ofNat,
      conjugation_algebraMap, conjugation_s]
    ring
  · simp only [RingHom.comp_apply, rightUnit_a₃, map_add, map_mul, map_ofNat,
      conjugation_algebraMap, conjugation_r, conjugation_t, rightUnit_a₁]
    ring

@[simp]
theorem conjugation_rightUnit (x : BaseRing R) :
    conjugation R (rightUnit R x) = algebraMap (BaseRing R) (UniversalArrowRing R) x :=
  RingHom.congr_fun (conjugation_comp_rightUnit R) x

/-- `c ∘ c = id`: conjugation is an involution on `UniversalArrowRing R`. -/
@[simp]
theorem conjugation_comp_conjugation :
    (conjugation R).comp (conjugation R) = RingHom.id (UniversalArrowRing R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem conjugation_conjugation (x : UniversalArrowRing R) :
    conjugation R (conjugation R x) = x :=
  RingHom.congr_fun (conjugation_comp_conjugation R) x

/-- `ε ∘ c = ε`: inverting an identity arrow yields the identity arrow. -/
@[simp]
theorem counit_comp_conjugation : (counit R).comp (conjugation R) = counit R := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem counit_conjugation (x : UniversalArrowRing R) :
    counit R (conjugation R x) = counit R x :=
  RingHom.congr_fun (counit_comp_conjugation R) x

/-- **Left antipode law** `μ (c ⊗ id) Δ = η_R ε`. -/
theorem pushoutLift_conjugation_id_comp_coproduct :
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨(conjugation R, RingHom.id (UniversalArrowRing R)), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp (coproduct R) =
      (rightUnit R).comp (counit R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Right antipode law** `μ (id ⊗ c) Δ = η_L ε`. -/
theorem pushoutLift_id_conjugation_comp_coproduct :
    (ArrowRing.pushoutLift (rightUnit R)
      ⟨(RingHom.id (UniversalArrowRing R), conjugation R), by
        rw [conjugation_comp_algebraMap, RingHom.id_comp]⟩).comp (coproduct R) =
      (algebraMap (BaseRing R) (UniversalArrowRing R)).comp (counit R) := by
  refine ArrowRing.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-! ### Comparison morphism from the level-one Weierstrass Hopf algebroid -/

/-- The base map `A = ℤ[a₁, a₂, a₃, a₄, a₆] →+* BaseRing R`, specializing `Universal.curve` to
`universalCurve R = gammaOneThreeForm a₁ a₃`. -/
def toBaseRing : MvPolynomial Coeff ℤ →+* BaseRing R :=
  (universalCurve R).specialize

/-- Explicit unfolding of `toBaseRing R` as `(universalCurve R).specialize`. -/
theorem toBaseRing_def : toBaseRing R = (universalCurve R).specialize :=
  (rfl)

@[simp]
theorem toBaseRing_X_A₁ : toBaseRing R (X .A₁) = a₁ R := by
  rw [toBaseRing_def]
  simp

@[simp]
theorem toBaseRing_X_A₂ : toBaseRing R (X .A₂) = 0 := by
  rw [toBaseRing_def]
  simp

@[simp]
theorem toBaseRing_X_A₃ : toBaseRing R (X .A₃) = a₃ R := by
  rw [toBaseRing_def]
  simp

@[simp]
theorem toBaseRing_X_A₄ : toBaseRing R (X .A₄) = 0 := by
  rw [toBaseRing_def]
  simp

@[simp]
theorem toBaseRing_X_A₆ : toBaseRing R (X .A₆) = 0 := by
  rw [toBaseRing_def]
  simp

@[simp]
theorem map_toBaseRing_curve :
    WeierstrassCurve.map Universal.curve (toBaseRing R) = universalCurve R := by
  rw [toBaseRing_def]
  exact map_specialize _

@[simp]
theorem toBaseRing_c₄ : toBaseRing R Universal.curve.c₄ = (universalCurve R).c₄ := by
  rw [toBaseRing_def]
  exact specialize_c₄ _

@[simp]
theorem toBaseRing_c₆ : toBaseRing R Universal.curve.c₆ = (universalCurve R).c₆ := by
  rw [toBaseRing_def]
  exact specialize_c₆ _

@[simp]
theorem toBaseRing_Δ : toBaseRing R Universal.curve.Δ = (universalCurve R).Δ := by
  rw [toBaseRing_def]
  exact specialize_Δ _

/-- The arrow map `Γ = A[u, u⁻¹, r, s, t] →+* UniversalArrowRing R`, specializing `Universal.curve`
to `universalCurve R` and the universal variable change to `⟨1, r, s, t⟩`. -/
def toUniversalArrowRing : WeierstrassHopfAlgebroid.ArrowRing →+* UniversalArrowRing R :=
  ChangeRing.lift
    ((algebraMap (BaseRing R) (UniversalArrowRing R)).comp (toBaseRing R), universalChange R)

/-- Explicit unfolding of `toUniversalArrowRing R` via `ChangeRing.lift`. -/
theorem toUniversalArrowRing_def :
    toUniversalArrowRing R =
      ChangeRing.lift
        ((algebraMap (BaseRing R) (UniversalArrowRing R)).comp (toBaseRing R), universalChange R) :=
  (rfl)

/-- `(toBaseRing R, toUniversalArrowRing R)` intertwines the left units. -/
@[simp]
theorem toUniversalArrowRing_comp_algebraMap :
    (toUniversalArrowRing R).comp
      (algebraMap (MvPolynomial Coeff ℤ) WeierstrassHopfAlgebroid.ArrowRing) =
      (algebraMap (BaseRing R) (UniversalArrowRing R)).comp (toBaseRing R) := by
  rw [toUniversalArrowRing_def]
  exact ChangeRing.lift_comp_algebraMap _

@[simp]
theorem toUniversalArrowRing_algebraMap (f : MvPolynomial Coeff ℤ) :
    toUniversalArrowRing R
      (algebraMap (MvPolynomial Coeff ℤ) WeierstrassHopfAlgebroid.ArrowRing f) =
      algebraMap (BaseRing R) (UniversalArrowRing R) (toBaseRing R f) :=
  RingHom.congr_fun (toUniversalArrowRing_comp_algebraMap R) f

@[simp]
theorem universalChange_map_toUniversalArrowRing :
    (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map (toUniversalArrowRing R) =
      universalChange R := by
  rw [toUniversalArrowRing_def]
  exact ChangeRing.map_lift _

@[simp]
theorem toUniversalArrowRing_algebraMap_X (i : Fin 4) :
    toUniversalArrowRing R
      (algebraMap (MvPolynomial (Fin 4) (MvPolynomial Coeff ℤ))
        WeierstrassHopfAlgebroid.ArrowRing (X i)) =
      ![1, r R, s R, t R] i := by
  rw [toUniversalArrowRing_def]
  simp

@[simp]
theorem toUniversalArrowRing_universalChange_u_inv :
    toUniversalArrowRing R
      ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u⁻¹ :
        WeierstrassHopfAlgebroid.ArrowRingˣ) = 1 := by
  rw [toUniversalArrowRing_def]
  simp

/-- `(toBaseRing R, toUniversalArrowRing R)` intertwines the right units. -/
@[simp]
theorem toUniversalArrowRing_comp_rightUnit :
    (toUniversalArrowRing R).comp WeierstrassHopfAlgebroid.rightUnit =
      (rightUnit R).comp (toBaseRing R) :=
  Universal.map_curve_injective (by
    simp only [WeierstrassHopfAlgebroid.map_comp_rightUnit]
    simp [← WeierstrassCurve.map_map])

@[simp]
theorem toUniversalArrowRing_rightUnit (f : MvPolynomial Coeff ℤ) :
    toUniversalArrowRing R (WeierstrassHopfAlgebroid.rightUnit f) =
      rightUnit R (toBaseRing R f) :=
  RingHom.congr_fun (toUniversalArrowRing_comp_rightUnit R) f

/-- `(toBaseRing R, toUniversalArrowRing R)` intertwines the counits. -/
@[simp]
theorem counit_comp_toUniversalArrowRing :
    (counit R).comp (toUniversalArrowRing R) =
      (toBaseRing R).comp WeierstrassHopfAlgebroid.counit := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- `(toBaseRing R, toUniversalArrowRing R)` intertwines the conjugations. -/
@[simp]
theorem conjugation_comp_toUniversalArrowRing :
    (conjugation R).comp (toUniversalArrowRing R) =
      (toUniversalArrowRing R).comp WeierstrassHopfAlgebroid.conjugation := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- `(toBaseRing R, toUniversalArrowRing R)` intertwines the coproducts. -/
theorem coproduct_comp_toUniversalArrowRing :
    (coproduct R).comp (toUniversalArrowRing R) =
      (ChangeRing.pushoutLift WeierstrassHopfAlgebroid.rightUnit
        ⟨((algebraMap (UniversalArrowRing R) (TensorSquare R)).comp (toUniversalArrowRing R),
          (ArrowRing.map (rightUnit R)).comp (toUniversalArrowRing R)),
          RingHom.ext fun f ↦ by simp⟩).comp WeierstrassHopfAlgebroid.coproduct := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  rw [WeierstrassHopfAlgebroid.universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Every integral modular form of level one pulls back to an invariant of
`(BaseRing R, UniversalArrowRing R)`**: because `toUniversalArrowRing R` sends the scaling
coordinate `u` to `1`, the factor `u⁻ᵏ` in `WeierstrassCurve.isIntegralModularForm_iff_rightUnit`
becomes `1`. -/
theorem rightUnit_toBaseRing_of_isIntegralModularForm {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : IsIntegralModularForm k f) :
    rightUnit R (toBaseRing R f) =
      algebraMap (BaseRing R) (UniversalArrowRing R) (toBaseRing R f) := by
  simpa using congrArg (toUniversalArrowRing R) (isIntegralModularForm_iff_rightUnit.mp hf)

/-- Pullback of any level-one integral modular form lies in `invariantSubalgebra R`. -/
theorem toBaseRing_mem_invariantSubalgebra_of_isIntegralModularForm {k : ℕ}
    {f : MvPolynomial Coeff ℤ} (hf : IsIntegralModularForm k f) :
    toBaseRing R f ∈ invariantSubalgebra R :=
  (mem_invariantSubalgebra R).mpr (rightUnit_toBaseRing_of_isIntegralModularForm R hf)

/-- The invariant `c₄` of `universalCurve R` is fixed by `rightUnit R`. -/
theorem rightUnit_c₄ :
    rightUnit R (universalCurve R).c₄ =
      algebraMap (BaseRing R) (UniversalArrowRing R) (universalCurve R).c₄ := by
  rw [← toBaseRing_c₄]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_c₄

/-- The invariant `c₆` of `universalCurve R` is fixed by `rightUnit R`. -/
theorem rightUnit_c₆ :
    rightUnit R (universalCurve R).c₆ =
      algebraMap (BaseRing R) (UniversalArrowRing R) (universalCurve R).c₆ := by
  rw [← toBaseRing_c₆]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_c₆

/-- The discriminant `Δ` of `universalCurve R` is fixed by `rightUnit R`. -/
theorem rightUnit_Δ :
    rightUnit R (universalCurve R).Δ =
      algebraMap (BaseRing R) (UniversalArrowRing R) (universalCurve R).Δ := by
  rw [← toBaseRing_Δ]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_Δ

/-- `(universalCurve R).c₄` belongs to `invariantSubalgebra R = H⁰(A', Γ')`. -/
theorem c₄_mem_invariantSubalgebra : (universalCurve R).c₄ ∈ invariantSubalgebra R :=
  (mem_invariantSubalgebra R).mpr (rightUnit_c₄ R)

/-- `(universalCurve R).c₆` belongs to `invariantSubalgebra R = H⁰(A', Γ')`. -/
theorem c₆_mem_invariantSubalgebra : (universalCurve R).c₆ ∈ invariantSubalgebra R :=
  (mem_invariantSubalgebra R).mpr (rightUnit_c₆ R)

/-- `(universalCurve R).Δ` belongs to `invariantSubalgebra R = H⁰(A', Γ')`. -/
theorem Δ_mem_invariantSubalgebra : (universalCurve R).Δ ∈ invariantSubalgebra R :=
  (mem_invariantSubalgebra R).mpr (rightUnit_Δ R)

/-! ### Coproduct compatibility and right-unit values of the rank-`8` trace transfer -/

section UniversalTrace

variable [Invertible (3 : R)]

/-- **Hopf-algebroid trace identity**: tracing `coproduct R y` along the left
`UniversalArrowRing R`-algebra structure of `TensorSquare R` equals `η_L (trace y)`. -/
theorem trace_coproduct (y : UniversalArrowRing R) :
    Algebra.trace (UniversalArrowRing R) (TensorSquare R) (coproduct R y) =
      algebraMap (BaseRing R) (UniversalArrowRing R)
        (Algebra.trace (BaseRing R) (UniversalArrowRing R) y) := by
  simp [coproduct_eq_shearEquiv_comp_map, Algebra.trace_eq_of_algEquiv, ArrowRing.trace_map]

/-- In `UniversalArrowRing R`, the trace of `rightUnit R (a₁ R)` vanishes. -/
theorem trace_rightUnit_a₁ :
    Algebra.trace (BaseRing R) (UniversalArrowRing R) (rightUnit R (a₁ R)) = 0 := by
  have h : rightUnit R (a₁ R) = (ArrowRing.target (a₁ R) (a₃ R)).a₁ := by
    rw [target_eq_map_rightUnit, WeierstrassCurve.map_a₁, universalCurve_a₁]
  rw [h]
  exact ArrowRing.trace_target_a₁

/-- In `UniversalArrowRing R`, the trace of `rightUnit R (a₃ R)` vanishes. -/
theorem trace_rightUnit_a₃ :
    Algebra.trace (BaseRing R) (UniversalArrowRing R) (rightUnit R (a₃ R)) = 0 := by
  have h : rightUnit R (a₃ R) = (ArrowRing.target (a₁ R) (a₃ R)).a₃ := by
    rw [target_eq_map_rightUnit, WeierstrassCurve.map_a₃, universalCurve_a₃]
  rw [h]
  exact ArrowRing.trace_target_a₃

/-- **`Tr(η_R(3 a₁ a₃)) = 2c₄`** in `(BaseRing R, UniversalArrowRing R)`. -/
theorem trace_rightUnit_three_mul_a₁_mul_a₃ :
    Algebra.trace (BaseRing R) (UniversalArrowRing R) (rightUnit R (3 * a₁ R * a₃ R)) =
      2 * (universalCurve R).c₄ := by
  have h : rightUnit R (3 * a₁ R * a₃ R) =
      3 * (ArrowRing.target (a₁ R) (a₃ R)).a₁ * (ArrowRing.target (a₁ R) (a₃ R)).a₃ := by
    rw [target_eq_map_rightUnit, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      universalCurve_a₁, universalCurve_a₃, map_mul, map_mul, map_ofNat]
  rw [h, universalCurve_def]
  exact ArrowRing.trace_three_mul_target_a₁_mul_target_a₃

/-- **`Tr(η_R(27 a₃²)) = 2c₆`** in `(BaseRing R, UniversalArrowRing R)`. -/
theorem trace_rightUnit_twentySeven_mul_a₃_sq :
    Algebra.trace (BaseRing R) (UniversalArrowRing R) (rightUnit R (27 * a₃ R ^ 2)) =
      2 * (universalCurve R).c₆ := by
  have h : rightUnit R (27 * a₃ R ^ 2) = 27 * (ArrowRing.target (a₁ R) (a₃ R)).a₃ ^ 2 := by
    rw [target_eq_map_rightUnit, WeierstrassCurve.map_a₃, universalCurve_a₃, map_mul, map_pow,
      map_ofNat]
  rw [h, universalCurve_def]
  exact ArrowRing.trace_twentySeven_mul_target_a₃_sq

end UniversalTrace

end TauCeti.GammaOneThreeHopfAlgebroid

end
