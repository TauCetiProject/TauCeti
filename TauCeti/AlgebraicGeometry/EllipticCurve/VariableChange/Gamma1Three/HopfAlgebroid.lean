/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Gamma1Three.Representable
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid

/-!
# The `Γ₁(3)` Weierstrass Hopf algebroid

Over any commutative base ring `R`, let `A' = BaseRing R = R[a₁, a₃]` be the coefficient ring of
the universal curve `universalCurve R = gamma1ThreeNormalForm a₁ a₃` (`Y² + a₁XY + a₃Y = X³`) in
`Γ₁(3)` normal form, and let `Γ' = ArrowRing R = ArrowRingOf (BaseRing R) a₁ a₃` be the quotient
of `A'[r, s, t]` cutting out strict changes of variables `C = ⟨1, r, s, t⟩` whose target `C • W`
again has `a₂ = a₄ = a₆ = 0`.

`R`-algebra homomorphisms `ArrowRing R →ₐ[R] S` classify pairs of a curve in `Γ₁(3)` normal form
over `S` and a strict `Γ₁(3)` change of variables out of it (`arrowEquiv`). This file constructs
the Hopf algebroid structure on `(BaseRing R, ArrowRing R)` — Bauer's §7 presentation prior to
specializing `a₃ = 1` or inverting `3` — together with the canonical Hopf-algebroid morphism
`(toBaseRing R, toArrowRing R)` from the level-one Weierstrass Hopf algebroid
`(ℤ[a₁, a₂, a₃, a₄, a₆], ℤ[a₁, ⋯, a₆][u, u⁻¹, r, s, t])`.

Because `toArrowRing R` specializes the scaling coordinate `u` to `1`, every integral modular form
`f` of level one (of arbitrary weight `k`) pulls back to an ungraded Hopf-algebroid invariant in
`invariantSubalgebra R = H⁰(A', Γ')` (`rightUnit_toBaseRing_of_isIntegralModularForm`); in
particular `c₄`, `c₆` and `Δ` of `universalCurve R` are `Γ'`-invariant.

## Main definitions

* `TauCeti.Gamma1ThreeHopfAlgebroid.BaseRing R`: the polynomial ring `R[a₁, a₃]`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.universalCurve R`: the universal `Γ₁(3)` curve over
  `BaseRing R`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.ArrowRing R`: the arrow algebra `Γ'` over `BaseRing R`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.rightUnit R`, `counit R`, `coproduct R`, `conjugation R`:
  the Hopf-algebroid structure maps `η_R`, `ε`, `Δ`, `c` (together with the `R`-algebra enhancement
  `rightUnitAlgHom R`).
* `TauCeti.Gamma1ThreeHopfAlgebroid.invariantSubalgebra R`: the `R`-subalgebra `H⁰(A', Γ')` of
  elements `x ∈ BaseRing R` with `η_R x = η_L x`.
* `TauCeti.Gamma1ThreeHopfAlgebroid.toBaseRing R`, `toArrowRing R`: the comparison morphism from
  `TauCeti.WeierstrassHopfAlgebroid`.

## Main results

* `counit_comp_algebraMap`, `counit_comp_rightUnit`: unit–counit identities.
* `coproduct_r`, `coproduct_s`, `coproduct_t`, `coproduct_eq_shearEquiv_comp_map`: explicit
  formulas for `Δ` (`Δr = r₁ + r₂`, `Δs = s₁ + s₂`, `Δt = t₁ + t₂ + s₁r₂`) and its factorization
  through the groupoid shearing equivalence `ArrowRingOf.shearEquiv`.
* `pushoutLift_counit_id_comp_coproduct`, `pushoutLift_id_counit_comp_coproduct`,
  `coproduct_coassoc`: left/right counit laws and coassociativity.
* `conjugation_comp_algebraMap`, `conjugation_comp_rightUnit`, `conjugation_comp_conjugation`,
  `counit_comp_conjugation`, `pushoutLift_conjugation_id_comp_coproduct`,
  `pushoutLift_id_conjugation_comp_coproduct`: involution and antipode identities.
* `toArrowRing_comp_algebraMap`, `toArrowRing_comp_rightUnit`, `counit_comp_toArrowRing`,
  `conjugation_comp_toArrowRing`, `coproduct_comp_toArrowRing`: `(toBaseRing R, toArrowRing R)` is
  a morphism of Hopf algebroids.
* `rightUnit_toBaseRing_of_isIntegralModularForm`, `rightUnit_c₄`, `rightUnit_c₆`, `rightUnit_Δ`:
  level-one integral modular forms pull back to `H⁰(A', Γ')`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* K. Carrick, J. Davies and S. van Nigtevecht, *Topological modular forms with level structure:
  deformations, transfers, and differentials*, §4.2.
-/

public section

noncomputable section

namespace TauCeti.Gamma1ThreeHopfAlgebroid

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
  gamma1ThreeNormalForm (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₁ : (universalCurve R).a₁ = a₁ R :=
  gamma1ThreeNormalForm_a₁ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₂ : (universalCurve R).a₂ = 0 :=
  gamma1ThreeNormalForm_a₂ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₃ : (universalCurve R).a₃ = a₃ R :=
  gamma1ThreeNormalForm_a₃ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₄ : (universalCurve R).a₄ = 0 :=
  gamma1ThreeNormalForm_a₄ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_a₆ : (universalCurve R).a₆ = 0 :=
  gamma1ThreeNormalForm_a₆ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_c₄ : (universalCurve R).c₄ = a₁ R ^ 4 - 24 * a₁ R * a₃ R :=
  gamma1ThreeNormalForm_c₄ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_c₆ :
    (universalCurve R).c₆ = -a₁ R ^ 6 + 36 * a₁ R ^ 3 * a₃ R - 216 * a₃ R ^ 2 :=
  gamma1ThreeNormalForm_c₆ (a₁ R) (a₃ R)

@[simp]
theorem universalCurve_Δ : (universalCurve R).Δ = a₁ R ^ 3 * a₃ R ^ 3 - 27 * a₃ R ^ 4 :=
  gamma1ThreeNormalForm_Δ (a₁ R) (a₃ R)

/-- A ring homomorphism out of `BaseRing R` is determined by its restriction to `R` and its values
on `a₁ R` and `a₃ R`. -/
theorem baseRing_ringHom_ext {S : Type*} [CommRing S] {f g : BaseRing R →+* S}
    (hR : f.comp (algebraMap R _) = g.comp (algebraMap R _))
    (h₁ : f (a₁ R) = g (a₁ R)) (h₃ : f (a₃ R) = g (a₃ R)) : f = g :=
  MvPolynomial.ringHom_ext' hR fun i ↦ by fin_cases i <;> assumption

/-- The arrow ring `Γ'` of the `Γ₁(3)` Hopf algebroid over `R`. -/
abbrev ArrowRing : Type _ :=
  ArrowRingOf (BaseRing R) (a₁ R) (a₃ R)

/-- The coordinate `r` in `ArrowRing R`. -/
abbrev r : ArrowRing R :=
  ArrowRingOf.r (BaseRing R) (a₁ R) (a₃ R)

/-- The coordinate `s` in `ArrowRing R`. -/
abbrev s : ArrowRing R :=
  ArrowRingOf.s (BaseRing R) (a₁ R) (a₃ R)

/-- The coordinate `t` in `ArrowRing R`. -/
abbrev t : ArrowRing R :=
  ArrowRingOf.t (BaseRing R) (a₁ R) (a₃ R)

/-- The universal strict `Γ₁(3)` change of variables `⟨1, r, s, t⟩` over `ArrowRing R`. -/
abbrev universalChange : VariableChange (ArrowRing R) :=
  ArrowRingOf.universalChange (BaseRing R) (a₁ R) (a₃ R)

private def mkArrowAlgHom {S : Type*} [CommRing S] [Algebra R S]
    (p : {p : (S × S) × VariableChange S // IsStrictGamma1ThreeChange p.1.1 p.1.2 p.2}) :
    ArrowRing R →ₐ[R] S :=
  let f : BaseRing R →+* S := eval₂Hom (algebraMap R S) ![p.1.1.1, p.1.1.2]
  have hf₁ : f (a₁ R) = p.1.1.1 := by simp [f, a₁]
  have hf₃ : f (a₃ R) = p.1.1.2 := by simp [f, a₃]
  have hp : IsStrictGamma1ThreeChange (f (a₁ R)) (f (a₃ R)) p.1.2 := by
    rw [hf₁, hf₃]
    exact p.2
  AlgHom.mk (ArrowRingOf.lift ⟨(f, p.1.2), hp⟩) fun x ↦ by
    change ArrowRingOf.lift ⟨(f, p.1.2), hp⟩ (algebraMap R (ArrowRing R) x) = algebraMap R S x
    rw [IsScalarTower.algebraMap_apply R (BaseRing R) (ArrowRing R), ArrowRingOf.lift_algebraMap]
    exact eval₂Hom_C _ _ x

/-- **`R`-algebra homomorphisms `ArrowRing R →ₐ[R] S` classify strict `Γ₁(3)` arrows** over `S`. -/
def arrowEquiv (S : Type*) [CommRing S] [Algebra R S] :
    (ArrowRing R →ₐ[R] S) ≃
      {p : (S × S) × VariableChange S // IsStrictGamma1ThreeChange p.1.1 p.1.2 p.2} where
  toFun k := ⟨((k (algebraMap (BaseRing R) (ArrowRing R) (a₁ R)),
      k (algebraMap (BaseRing R) (ArrowRing R) (a₃ R))),
    (universalChange R).map k.toRingHom),
    (ArrowRingOf.isStrictGamma1ThreeChange_universalChange (BaseRing R) (a₁ R) (a₃ R)).map
      k.toRingHom⟩
  invFun := mkArrowAlgHom R
  left_inv k := by
    apply AlgHom.toRingHom_injective
    refine ArrowRingOf.ringHom_ext (baseRing_ringHom_ext R (RingHom.ext fun x ↦ ?_) ?_ ?_) ?_
    · simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R (BaseRing R) (ArrowRing R),
        RingHom.coe_coe, AlgHom.commutes]
    · change ArrowRingOf.lift _ (algebraMap (BaseRing R) (ArrowRing R) (a₁ R)) =
        k (algebraMap (BaseRing R) (ArrowRing R) (a₁ R))
      rw [ArrowRingOf.lift_algebraMap]
      simp [a₁]
    · change ArrowRingOf.lift _ (algebraMap (BaseRing R) (ArrowRing R) (a₃ R)) =
        k (algebraMap (BaseRing R) (ArrowRing R) (a₃ R))
      rw [ArrowRingOf.lift_algebraMap]
      simp [a₃]
    · exact ArrowRingOf.map_lift _
  right_inv p := by
    refine Subtype.ext (Prod.ext (Prod.ext ?_ ?_) ?_)
    · change ArrowRingOf.lift _ (algebraMap (BaseRing R) (ArrowRing R) (a₁ R)) = p.1.1.1
      rw [ArrowRingOf.lift_algebraMap]
      simp [a₁]
    · change ArrowRingOf.lift _ (algebraMap (BaseRing R) (ArrowRing R) (a₃ R)) = p.1.1.2
      rw [ArrowRingOf.lift_algebraMap]
      simp [a₃]
    · exact ArrowRingOf.map_lift _

/-- The **right unit** `η_R : BaseRing R →ₐ[R] ArrowRing R` as an `R`-algebra homomorphism,
classifying the target `universalChange R • universalCurve R` of the universal strict `Γ₁(3)`
arrow. -/
def rightUnitAlgHom : BaseRing R →ₐ[R] ArrowRing R :=
  aeval ![algebraMap (BaseRing R) (ArrowRing R) (a₁ R) + 2 * s R,
    algebraMap (BaseRing R) (ArrowRing R) (a₃ R) +
      algebraMap (BaseRing R) (ArrowRing R) (a₁ R) * r R + 2 * t R]

/-- The **right unit** `η_R : BaseRing R →+* ArrowRing R` as a ring homomorphism; the left unit
`η_L` is `algebraMap (BaseRing R) (ArrowRing R)`. -/
def rightUnit : BaseRing R →+* ArrowRing R :=
  (rightUnitAlgHom R).toRingHom

@[simp]
theorem coe_rightUnitAlgHom : (rightUnitAlgHom R : BaseRing R →+* ArrowRing R) = rightUnit R :=
  (rfl)

@[simp]
theorem rightUnitAlgHom_apply (x : BaseRing R) : rightUnitAlgHom R x = rightUnit R x :=
  (rfl)

@[simp]
theorem rightUnit_C (c : R) : rightUnit R (C c) = algebraMap R (ArrowRing R) c :=
  (rightUnitAlgHom R).commutes c

theorem rightUnit_algebraMap_R (c : R) :
    rightUnit R (algebraMap R (BaseRing R) c) = algebraMap R (ArrowRing R) c :=
  (rightUnitAlgHom R).commutes c

@[simp]
theorem rightUnit_comp_C :
    (rightUnit R).comp C = algebraMap R (ArrowRing R) :=
  RingHom.ext (rightUnit_C R)

theorem rightUnit_comp_algebraMap_R :
    (rightUnit R).comp (algebraMap R (BaseRing R)) = algebraMap R (ArrowRing R) :=
  RingHom.ext (rightUnit_algebraMap_R R)

@[simp]
theorem rightUnit_a₁ :
    rightUnit R (a₁ R) = algebraMap (BaseRing R) (ArrowRing R) (a₁ R) + 2 * s R := by
  simp [rightUnit, rightUnitAlgHom, a₁]

@[simp]
theorem rightUnit_a₃ :
    rightUnit R (a₃ R) =
      algebraMap (BaseRing R) (ArrowRing R) (a₃ R) +
        algebraMap (BaseRing R) (ArrowRing R) (a₁ R) * r R + 2 * t R := by
  simp [rightUnit, rightUnitAlgHom, a₃]

/-- Pushing `universalCurve R` along `rightUnit R` gives `universalChange R • universalCurve R`. -/
@[simp]
theorem map_rightUnit_universalCurve :
    (universalCurve R).map (rightUnit R) =
      universalChange R • (universalCurve R).map (algebraMap (BaseRing R) (ArrowRing R)) := by
  rw [universalCurve, map_gamma1ThreeNormalForm, map_gamma1ThreeNormalForm,
    (ArrowRingOf.isStrictGamma1ThreeChange_universalChange (BaseRing R) (a₁ R) (a₃ R)).smul_eq]
  simp

/-- The `R`-subalgebra `H⁰(A', Γ')` of Hopf-algebroid invariants in `BaseRing R`, defined as the
equalizer of `rightUnitAlgHom R` and the left unit `IsScalarTower.toAlgHom R (BaseRing R) _`. -/
def invariantSubalgebra : Subalgebra R (BaseRing R) :=
  AlgHom.equalizer (rightUnitAlgHom R) (IsScalarTower.toAlgHom R (BaseRing R) (ArrowRing R))

@[simp]
theorem mem_invariantSubalgebra {x : BaseRing R} :
    x ∈ invariantSubalgebra R ↔
      rightUnit R x = algebraMap (BaseRing R) (ArrowRing R) x :=
  Iff.rfl

/-! ### Counit, coproduct and conjugation -/

/-- The **counit** `ε : ArrowRing R →+* BaseRing R`, classifying the identity strict arrows. -/
def counit : ArrowRing R →+* BaseRing R :=
  ArrowRingOf.lift ⟨(RingHom.id (BaseRing R), 1), IsStrictGamma1ThreeChange.one _ _⟩

@[simp]
theorem counit_comp_algebraMap :
    (counit R).comp (algebraMap (BaseRing R) (ArrowRing R)) = RingHom.id (BaseRing R) :=
  ArrowRingOf.lift_comp_algebraMap _

@[simp]
theorem counit_algebraMap (x : BaseRing R) :
    counit R (algebraMap (BaseRing R) (ArrowRing R) x) = x :=
  RingHom.congr_fun (counit_comp_algebraMap R) x

@[simp]
theorem universalChange_map_counit : (universalChange R).map (counit R) = 1 :=
  ArrowRingOf.map_lift _

@[simp]
theorem counit_r : counit R (r R) = 0 :=
  ArrowRingOf.lift_r _

@[simp]
theorem counit_s : counit R (s R) = 0 :=
  ArrowRingOf.lift_s _

@[simp]
theorem counit_t : counit R (t R) = 0 :=
  ArrowRingOf.lift_t _

@[simp]
theorem counit_comp_rightUnit : (counit R).comp (rightUnit R) = RingHom.id (BaseRing R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap_R,
      IsScalarTower.algebraMap_apply R (BaseRing R) (ArrowRing R), counit_algebraMap,
      RingHom.id_apply]
  · simp [map_ofNat]
  · simp [map_ofNat]

@[simp]
theorem counit_rightUnit (x : BaseRing R) : counit R (rightUnit R x) = x :=
  RingHom.congr_fun (counit_comp_rightUnit R) x

/-- The tensor square `Γ' ⊗_{A'} Γ'`, realized as `ArrowRingOf (ArrowRing R) (η_R a₁) (η_R a₃)`. -/
abbrev TensorSquare : Type _ :=
  ArrowRingOf (ArrowRing R) (rightUnit R (a₁ R)) (rightUnit R (a₃ R))

/-- The **coproduct** `Δ : ArrowRing R →+* TensorSquare R`, classifying composition `C₂ * C₁` of
strict `Γ₁(3)` arrows. -/
def coproduct : ArrowRing R →+* TensorSquare R :=
  ArrowRingOf.lift ⟨((algebraMap (ArrowRing R) (TensorSquare R)).comp
      (algebraMap (BaseRing R) (ArrowRing R)),
    ArrowRingOf.universalChange (ArrowRing R) (rightUnit R (a₁ R)) (rightUnit R (a₃ R)) *
      (universalChange R).map (algebraMap (ArrowRing R) (TensorSquare R))), by
    have h₁ := (ArrowRingOf.isStrictGamma1ThreeChange_universalChange
      (BaseRing R) (a₁ R) (a₃ R)).map (algebraMap (ArrowRing R) (TensorSquare R))
    refine h₁.mul ?_
    have ha₁ : algebraMap (ArrowRing R) (TensorSquare R) (algebraMap (BaseRing R) (ArrowRing R)
        (a₁ R)) + 2 * ((universalChange R).map (algebraMap (ArrowRing R) (TensorSquare R))).s =
        algebraMap (ArrowRing R) (TensorSquare R) (rightUnit R (a₁ R)) := by
      simp [map_ofNat]
    have ha₃ : algebraMap (ArrowRing R) (TensorSquare R) (algebraMap (BaseRing R) (ArrowRing R)
        (a₃ R)) + algebraMap (ArrowRing R) (TensorSquare R) (algebraMap (BaseRing R) (ArrowRing R)
          (a₁ R)) * ((universalChange R).map (algebraMap (ArrowRing R) (TensorSquare R))).r +
        2 * ((universalChange R).map (algebraMap (ArrowRing R) (TensorSquare R))).t =
        algebraMap (ArrowRing R) (TensorSquare R) (rightUnit R (a₃ R)) := by
      simp [map_ofNat]
    rw [ha₁, ha₃]
    exact ArrowRingOf.isStrictGamma1ThreeChange_universalChange (ArrowRing R) _ _⟩

@[simp]
theorem coproduct_comp_algebraMap :
    (coproduct R).comp (algebraMap (BaseRing R) (ArrowRing R)) =
      (algebraMap (ArrowRing R) (TensorSquare R)).comp (algebraMap (BaseRing R) (ArrowRing R)) :=
  ArrowRingOf.lift_comp_algebraMap _

@[simp]
theorem coproduct_algebraMap (x : BaseRing R) :
    coproduct R (algebraMap (BaseRing R) (ArrowRing R) x) =
      algebraMap (ArrowRing R) (TensorSquare R) (algebraMap (BaseRing R) (ArrowRing R) x) :=
  RingHom.congr_fun (coproduct_comp_algebraMap R) x

@[simp]
theorem universalChange_map_coproduct :
    (universalChange R).map (coproduct R) =
      ArrowRingOf.universalChange (ArrowRing R) (rightUnit R (a₁ R)) (rightUnit R (a₃ R)) *
        (universalChange R).map (algebraMap (ArrowRing R) (TensorSquare R)) :=
  ArrowRingOf.map_lift _

/-- `Δr = r₁ + r₂` in `TensorSquare R`. -/
theorem coproduct_r :
    coproduct R (r R) =
      algebraMap (ArrowRing R) (TensorSquare R) (r R) +
        ArrowRingOf.map (rightUnit R) (r R) := by
  have h := congrArg VariableChange.r (universalChange_map_coproduct R)
  simp only [VariableChange.map_r, VariableChange.map_u, ArrowRingOf.universalChange_r,
    VariableChange.mul_def, ArrowRingOf.universalChange_u, map_one, Units.val_one, one_pow,
    mul_one] at h
  rw [ArrowRingOf.mapOfEq_r]
  linear_combination h

/-- `Δs = s₁ + s₂` in `TensorSquare R`. -/
theorem coproduct_s :
    coproduct R (s R) =
      algebraMap (ArrowRing R) (TensorSquare R) (s R) +
        ArrowRingOf.map (rightUnit R) (s R) := by
  have h := congrArg VariableChange.s (universalChange_map_coproduct R)
  simp only [VariableChange.map_s, VariableChange.map_u, ArrowRingOf.universalChange_s,
    VariableChange.mul_def, ArrowRingOf.universalChange_u, map_one, Units.val_one, one_mul] at h
  rw [ArrowRingOf.mapOfEq_s]
  linear_combination h

/-- `Δt = t₁ + t₂ + s₁r₂` in `TensorSquare R`. -/
theorem coproduct_t :
    coproduct R (t R) =
      algebraMap (ArrowRing R) (TensorSquare R) (t R) +
        ArrowRingOf.map (rightUnit R) (t R) +
        algebraMap (ArrowRing R) (TensorSquare R) (s R) *
          ArrowRingOf.map (rightUnit R) (r R) := by
  have h := congrArg VariableChange.t (universalChange_map_coproduct R)
  simp only [VariableChange.map_t, VariableChange.map_u, VariableChange.map_s,
    ArrowRingOf.universalChange_u, ArrowRingOf.universalChange_r, ArrowRingOf.universalChange_s,
    ArrowRingOf.universalChange_t, VariableChange.mul_def, map_one, Units.val_one, one_pow,
    mul_one] at h
  rw [ArrowRingOf.mapOfEq_t, ArrowRingOf.mapOfEq_r]
  linear_combination h

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem coproduct_comp_rightUnit :
    (coproduct R).comp (rightUnit R) =
      (ArrowRingOf.map (rightUnit R)).comp (rightUnit R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap_R,
      IsScalarTower.algebraMap_apply R (BaseRing R) (ArrowRing R), coproduct_algebraMap,
      ArrowRingOf.mapOfEq_algebraMap]
  · simp only [RingHom.comp_apply, rightUnit_a₁, map_add, map_mul, map_ofNat, coproduct_algebraMap,
      coproduct_s, ArrowRingOf.mapOfEq_algebraMap, ArrowRingOf.mapOfEq_s]
    ring
  · simp only [RingHom.comp_apply, rightUnit_a₃, map_add, map_mul, map_ofNat, coproduct_algebraMap,
      coproduct_r, coproduct_t, ArrowRingOf.mapOfEq_algebraMap, ArrowRingOf.mapOfEq_r,
      ArrowRingOf.mapOfEq_t, rightUnit_a₁]
    ring

@[simp]
theorem coproduct_rightUnit (x : BaseRing R) :
    coproduct R (rightUnit R x) = ArrowRingOf.map (rightUnit R) (rightUnit R x) :=
  RingHom.congr_fun (coproduct_comp_rightUnit R) x

/-- If `k : TensorSquare R →+* S` classifies a composable pair of strict `Γ₁(3)` arrows, then
`k ∘ Δ` classifies their composite. -/
theorem universalChange_map_comp_coproduct {S : Type*} [CommRing S] (k : TensorSquare R →+* S) :
    (universalChange R).map (k.comp (coproduct R)) =
      (universalChange R).map (k.comp (ArrowRingOf.map (rightUnit R))) *
        (universalChange R).map (k.comp (algebraMap (ArrowRing R) (TensorSquare R))) := by
  simp [← VariableChange.map_map]

/-- The coproduct equals the groupoid shearing equivalence composed with scalar extension along the
left unit: `Δ = shearEquiv ∘ map η_L`. -/
theorem coproduct_eq_shearEquiv_comp_map :
    coproduct R =
      (ArrowRingOf.shearEquiv
        (ArrowRingOf.isStrictGamma1ThreeChange_universalChange (BaseRing R) (a₁ R) (a₃ R))
        (by simp) (by simp)).toRingHom.comp
        (ArrowRingOf.map (algebraMap (BaseRing R) (ArrowRing R))) := by
  rw [ArrowRingOf.shearEquiv_toRingHom]
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- **Left counit law** `(ε ⊗ id) Δ = id`. -/
theorem pushoutLift_counit_id_comp_coproduct :
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨((algebraMap (BaseRing R) (ArrowRing R)).comp (counit R),
        RingHom.id (ArrowRing R)), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
      (coproduct R) = RingHom.id (ArrowRing R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Right counit law** `(id ⊗ ε) Δ = id`. -/
theorem pushoutLift_id_counit_comp_coproduct :
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨(RingHom.id (ArrowRing R), (rightUnit R).comp (counit R)), by
        rw [RingHom.comp_assoc, counit_comp_algebraMap, RingHom.comp_id, RingHom.id_comp]⟩).comp
      (coproduct R) = RingHom.id (ArrowRing R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- The triple tensor product `Γ' ⊗_{A'} Γ' ⊗_{A'} Γ'`. -/
abbrev TensorCube : Type _ :=
  ArrowRingOf (TensorSquare R)
    (ArrowRingOf.map (rightUnit R) (rightUnit R (a₁ R)))
    (ArrowRingOf.map (rightUnit R) (rightUnit R (a₃ R)))

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the coproduct. -/
theorem coproduct_coassoc :
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨((algebraMap (TensorSquare R) (TensorCube R)).comp (coproduct R),
        ArrowRingOf.mapOfEq ((ArrowRingOf.map (rightUnit R)).comp (rightUnit R)) rfl rfl), by
        dsimp only
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit,
          ArrowRingOf.mapOfEq_comp_algebraMap]⟩).comp (coproduct R) =
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨((algebraMap (TensorSquare R) (TensorCube R)).comp
          (algebraMap (ArrowRing R) (TensorSquare R)),
        (ArrowRingOf.map (ArrowRingOf.map (rightUnit R))).comp (coproduct R)),
        RingHom.ext fun x ↦ by simp⟩).comp (coproduct R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp only [universalChange_map_comp_coproduct, ArrowRingOf.pushoutLiftOfEq_comp_mapOfEq,
    ArrowRingOf.pushoutLiftOfEq_comp_algebraMap]
  simp only [ArrowRingOf.mapOfEq_comp_algebraMap, ← VariableChange.map_map,
    ArrowRingOf.universalChange_map_mapOfEq, mul_assoc]

/-- The **conjugation** `c : ArrowRing R →+* ArrowRing R`, classifying the inverse strict arrow
`C⁻¹ : C • W → W`. -/
def conjugation : ArrowRing R →+* ArrowRing R :=
  ArrowRingOf.lift ⟨(rightUnit R, (universalChange R)⁻¹), by
    simpa using (ArrowRingOf.isStrictGamma1ThreeChange_universalChange
      (BaseRing R) (a₁ R) (a₃ R)).inv⟩

@[simp]
theorem conjugation_comp_algebraMap :
    (conjugation R).comp (algebraMap (BaseRing R) (ArrowRing R)) = rightUnit R :=
  ArrowRingOf.lift_comp_algebraMap _

@[simp]
theorem conjugation_algebraMap (x : BaseRing R) :
    conjugation R (algebraMap (BaseRing R) (ArrowRing R) x) = rightUnit R x :=
  RingHom.congr_fun (conjugation_comp_algebraMap R) x

@[simp]
theorem universalChange_map_conjugation :
    (universalChange R).map (conjugation R) = (universalChange R)⁻¹ :=
  ArrowRingOf.map_lift _

@[simp]
theorem conjugation_r : conjugation R (r R) = -r R := by
  have h := congrArg VariableChange.r (universalChange_map_conjugation R)
  simp only [VariableChange.map_r, ArrowRingOf.universalChange_u, ArrowRingOf.universalChange_r,
    VariableChange.inv_def, inv_one, Units.val_one, one_pow, mul_one] at h
  exact h

@[simp]
theorem conjugation_s : conjugation R (s R) = -s R := by
  have h := congrArg VariableChange.s (universalChange_map_conjugation R)
  simp only [VariableChange.map_s, ArrowRingOf.universalChange_u, ArrowRingOf.universalChange_s,
    VariableChange.inv_def, inv_one, Units.val_one, mul_one] at h
  exact h

@[simp]
theorem conjugation_t : conjugation R (t R) = -t R + r R * s R := by
  have h := congrArg VariableChange.t (universalChange_map_conjugation R)
  simp only [VariableChange.map_t, ArrowRingOf.universalChange_u, ArrowRingOf.universalChange_r,
    ArrowRingOf.universalChange_s, ArrowRingOf.universalChange_t, VariableChange.inv_def,
    inv_one, Units.val_one, one_pow, mul_one] at h
  linear_combination h

@[simp]
theorem conjugation_comp_rightUnit :
    (conjugation R).comp (rightUnit R) = algebraMap (BaseRing R) (ArrowRing R) := by
  refine baseRing_ringHom_ext R (RingHom.ext fun c ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, rightUnit_algebraMap_R,
      IsScalarTower.algebraMap_apply R (BaseRing R) (ArrowRing R), conjugation_algebraMap]
  · simp [map_ofNat]
    ring
  · simp [map_ofNat]
    ring

@[simp]
theorem conjugation_rightUnit (x : BaseRing R) :
    conjugation R (rightUnit R x) = algebraMap (BaseRing R) (ArrowRing R) x :=
  RingHom.congr_fun (conjugation_comp_rightUnit R) x

@[simp]
theorem conjugation_comp_conjugation :
    (conjugation R).comp (conjugation R) = RingHom.id (ArrowRing R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem conjugation_conjugation (x : ArrowRing R) : conjugation R (conjugation R x) = x :=
  RingHom.congr_fun (conjugation_comp_conjugation R) x

@[simp]
theorem counit_comp_conjugation : (counit R).comp (conjugation R) = counit R := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem counit_conjugation (x : ArrowRing R) : counit R (conjugation R x) = counit R x :=
  RingHom.congr_fun (counit_comp_conjugation R) x

/-- **Left antipode law** `μ (c ⊗ id) Δ = η_R ε`. -/
theorem pushoutLift_conjugation_id_comp_coproduct :
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨(conjugation R, RingHom.id (ArrowRing R)), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp (coproduct R) =
      (rightUnit R).comp (counit R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Right antipode law** `μ (id ⊗ c) Δ = η_L ε`. -/
theorem pushoutLift_id_conjugation_comp_coproduct :
    (ArrowRingOf.pushoutLift (rightUnit R)
      ⟨(RingHom.id (ArrowRing R), conjugation R), by
        rw [conjugation_comp_algebraMap, RingHom.id_comp]⟩).comp (coproduct R) =
      (algebraMap (BaseRing R) (ArrowRing R)).comp (counit R) := by
  refine ArrowRingOf.ringHom_ext (RingHom.ext fun x ↦ by simp) ?_
  rw [universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-! ### Comparison morphism from the level-one Weierstrass Hopf algebroid -/

/-- The base map `A = ℤ[a₁, a₂, a₃, a₄, a₆] →+* BaseRing R`, specializing `Universal.curve` to
`universalCurve R = gamma1ThreeNormalForm a₁ a₃`. -/
def toBaseRing : MvPolynomial Coeff ℤ →+* BaseRing R :=
  (universalCurve R).specialize

@[simp]
theorem map_toBaseRing_curve :
    WeierstrassCurve.map Universal.curve (toBaseRing R) = universalCurve R :=
  map_specialize _

@[simp]
theorem toBaseRing_c₄ : toBaseRing R Universal.curve.c₄ = (universalCurve R).c₄ :=
  specialize_c₄ _

@[simp]
theorem toBaseRing_c₆ : toBaseRing R Universal.curve.c₆ = (universalCurve R).c₆ :=
  specialize_c₆ _

@[simp]
theorem toBaseRing_Δ : toBaseRing R Universal.curve.Δ = (universalCurve R).Δ :=
  specialize_Δ _

/-- The arrow map `Γ = A[u, u⁻¹, r, s, t] →+* ArrowRing R`, specializing `Universal.curve` to
`universalCurve R` and the universal variable change to `⟨1, r, s, t⟩`. -/
def toArrowRing : WeierstrassHopfAlgebroid.ArrowRing →+* ArrowRing R :=
  ChangeRing.lift
    ((algebraMap (BaseRing R) (ArrowRing R)).comp (toBaseRing R), universalChange R)

@[simp]
theorem toArrowRing_comp_algebraMap :
    (toArrowRing R).comp (algebraMap (MvPolynomial Coeff ℤ) WeierstrassHopfAlgebroid.ArrowRing) =
      (algebraMap (BaseRing R) (ArrowRing R)).comp (toBaseRing R) :=
  ChangeRing.lift_comp_algebraMap _

@[simp]
theorem toArrowRing_algebraMap (f : MvPolynomial Coeff ℤ) :
    toArrowRing R (algebraMap (MvPolynomial Coeff ℤ) WeierstrassHopfAlgebroid.ArrowRing f) =
      algebraMap (BaseRing R) (ArrowRing R) (toBaseRing R f) :=
  RingHom.congr_fun (toArrowRing_comp_algebraMap R) f

@[simp]
theorem universalChange_map_toArrowRing :
    (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map (toArrowRing R) = universalChange R :=
  ChangeRing.map_lift _

/-- `(toBaseRing R, toArrowRing R)` intertwines the right units. -/
@[simp]
theorem toArrowRing_comp_rightUnit :
    (toArrowRing R).comp WeierstrassHopfAlgebroid.rightUnit =
      (rightUnit R).comp (toBaseRing R) := by
  refine Universal.map_curve_injective ?_
  dsimp only
  rw [WeierstrassHopfAlgebroid.map_comp_rightUnit, universalChange_map_toArrowRing,
    toArrowRing_comp_algebraMap, ← WeierstrassCurve.map_map, map_toBaseRing_curve,
    ← map_rightUnit_universalCurve, ← map_toBaseRing_curve, WeierstrassCurve.map_map]

@[simp]
theorem toArrowRing_rightUnit (f : MvPolynomial Coeff ℤ) :
    toArrowRing R (WeierstrassHopfAlgebroid.rightUnit f) = rightUnit R (toBaseRing R f) :=
  RingHom.congr_fun (toArrowRing_comp_rightUnit R) f

/-- `(toBaseRing R, toArrowRing R)` intertwines the counits. -/
@[simp]
theorem counit_comp_toArrowRing :
    (counit R).comp (toArrowRing R) = (toBaseRing R).comp WeierstrassHopfAlgebroid.counit := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- `(toBaseRing R, toArrowRing R)` intertwines the conjugations. -/
@[simp]
theorem conjugation_comp_toArrowRing :
    (conjugation R).comp (toArrowRing R) =
      (toArrowRing R).comp WeierstrassHopfAlgebroid.conjugation := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  simp [← VariableChange.map_map]

/-- `(toBaseRing R, toArrowRing R)` intertwines the coproducts. -/
theorem coproduct_comp_toArrowRing :
    (coproduct R).comp (toArrowRing R) =
      (ChangeRing.pushoutLift WeierstrassHopfAlgebroid.rightUnit
        ⟨((algebraMap (ArrowRing R) (TensorSquare R)).comp (toArrowRing R),
          (ArrowRingOf.map (rightUnit R)).comp (toArrowRing R)),
          RingHom.ext fun f ↦ by simp⟩).comp WeierstrassHopfAlgebroid.coproduct := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun f ↦ by simp) ?_
  rw [WeierstrassHopfAlgebroid.universalChange_map_comp_coproduct]
  simp [← VariableChange.map_map]

/-- **Every integral modular form of level one pulls back to an invariant of
`(BaseRing R, ArrowRing R)`**: because `toArrowRing R` sends the scaling coordinate `u` to `1`, the
factor `u⁻ᵏ` in `WeierstrassCurve.isIntegralModularForm_iff_rightUnit` becomes `1`. -/
theorem rightUnit_toBaseRing_of_isIntegralModularForm {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : IsIntegralModularForm k f) :
    rightUnit R (toBaseRing R f) = algebraMap (BaseRing R) (ArrowRing R) (toBaseRing R f) := by
  have h := congrArg (toArrowRing R) (isIntegralModularForm_iff_rightUnit.mp hf)
  rw [toArrowRing_rightUnit, map_mul, map_pow, toArrowRing_algebraMap] at h
  have hu : toArrowRing R ↑(ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u⁻¹ = 1 := by
    simp [toArrowRing]
  rw [hu, one_pow, one_mul] at h
  exact h

/-- Pullback of any level-one integral modular form lies in `invariantSubalgebra R`. -/
theorem toBaseRing_mem_invariantSubalgebra_of_isIntegralModularForm {k : ℕ}
    {f : MvPolynomial Coeff ℤ} (hf : IsIntegralModularForm k f) :
    toBaseRing R f ∈ invariantSubalgebra R :=
  rightUnit_toBaseRing_of_isIntegralModularForm R hf

theorem rightUnit_c₄ :
    rightUnit R (universalCurve R).c₄ =
      algebraMap (BaseRing R) (ArrowRing R) (universalCurve R).c₄ := by
  rw [← toBaseRing_c₄]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_c₄

theorem rightUnit_c₆ :
    rightUnit R (universalCurve R).c₆ =
      algebraMap (BaseRing R) (ArrowRing R) (universalCurve R).c₆ := by
  rw [← toBaseRing_c₆]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_c₆

theorem rightUnit_Δ :
    rightUnit R (universalCurve R).Δ =
      algebraMap (BaseRing R) (ArrowRing R) (universalCurve R).Δ := by
  rw [← toBaseRing_Δ]
  exact rightUnit_toBaseRing_of_isIntegralModularForm R isIntegralModularForm_Δ

theorem c₄_mem_invariantSubalgebra : (universalCurve R).c₄ ∈ invariantSubalgebra R :=
  rightUnit_c₄ R

theorem c₆_mem_invariantSubalgebra : (universalCurve R).c₆ ∈ invariantSubalgebra R :=
  rightUnit_c₆ R

theorem Δ_mem_invariantSubalgebra : (universalCurve R).Δ ∈ invariantSubalgebra R :=
  rightUnit_Δ R

end TauCeti.Gamma1ThreeHopfAlgebroid

end
