/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The first weighted Weierstrass cobar differentials

For the Weierstrass Hopf algebroid `(A, Γ)`, this file constructs the first two
cobar differentials with coefficients in the weight-`k` character `χ = u⁻ᵏ`.
Weights range over all integers, including negative tensor powers of the Hodge line.

An arrow goes from `W` to `C • W`. In the ring of composable pairs, the left
factor is the first arrow and the right factor is the second. With this order,

* `d₀(f) = η_R(f) - χ η_L(f)`;
* `d₁(a) = right(a) - Δ(a) + right(χ) left(a)`.

We prove `d₁ d₀ = 0` and package these maps as a short complex of abelian groups.
Its degree-zero kernel, in nonnegative weight, is exactly the module of integral
modular forms. Every degree-one cocycle vanishes on identity arrows, so the
unnormalized and normalized degree-one cocycle conditions agree. These are only
the first two differentials: no higher cobar terms or stack-cohomology comparison
are asserted here.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*,
  Appendix A1.2 (the cobar complex).
-/

public noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve WeierstrassChange WeierstrassChange.ChangeRing

/-- The weight-`k` character on arrows, with the inverse-power convention `u⁻ᵏ`. -/
def weightCharacter (k : ℤ) : ArrowRingˣ :=
  (universalChange (MvPolynomial Coeff ℤ)).u ^ (-k)

/-- The value of the character is an inverse power of the universal scaling unit. -/
theorem weightCharacter_def (k : ℤ) :
    weightCharacter k = (universalChange (MvPolynomial Coeff ℤ)).u ^ (-k) := (rfl)

@[simp]
theorem weightCharacter_zero : weightCharacter 0 = 1 := by
  simp [weightCharacter]

/-- Tensoring weights multiplies their characters. -/
theorem weightCharacter_add (k l : ℤ) :
    weightCharacter (k + l) = weightCharacter k * weightCharacter l := by
  simp only [weightCharacter, neg_add, zpow_add]

/-- On identity arrows the weight character is trivial. -/
@[simp]
theorem counit_weightCharacter (k : ℤ) : counit (weightCharacter k) = 1 := by
  have h : Units.map counit.toMonoidHom
      (universalChange (MvPolynomial Coeff ℤ)).u = 1 :=
    congrArg VariableChange.u universalChange_map_counit
  have h' : Units.map counit.toMonoidHom (weightCharacter k) = 1 := by
    rw [weightCharacter, map_zpow, h, one_zpow]
  exact congrArg Units.val h'

/-- The character of a composite is the product of the characters of its two arrows. -/
theorem coproduct_weightCharacter (k : ℤ) :
    coproduct (weightCharacter k) =
      ChangeRing.map rightUnit (weightCharacter k) *
        algebraMap ArrowRing (ChangeRing ArrowRing) (weightCharacter k) := by
  have h : Units.map coproduct.toMonoidHom
      (universalChange (MvPolynomial Coeff ℤ)).u =
        (universalChange ArrowRing).u *
          Units.map (algebraMap ArrowRing (ChangeRing ArrowRing)).toMonoidHom
            (universalChange (MvPolynomial Coeff ℤ)).u :=
    congrArg VariableChange.u universalChange_map_coproduct
  have hr : Units.map (ChangeRing.map rightUnit).toMonoidHom
      (universalChange (MvPolynomial Coeff ℤ)).u = (universalChange ArrowRing).u :=
    congrArg VariableChange.u (universalChange_map_map rightUnit)
  have h' : Units.map coproduct.toMonoidHom (weightCharacter k) =
      Units.map (ChangeRing.map rightUnit).toMonoidHom (weightCharacter k) *
        Units.map (algebraMap ArrowRing (ChangeRing ArrowRing)).toMonoidHom
          (weightCharacter k) := by
    simp only [weightCharacter, map_zpow, h, hr, mul_zpow]
  exact congrArg Units.val h'

/-- Specialization of the weight character on an arbitrary arrow. -/
@[simp]
theorem weightCharacter_specialize (k : ℤ) {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : VariableChange R) :
    lift (W.specialize, C) (weightCharacter k) = (C.u ^ (-k) : Rˣ) := by
  have h : Units.map (lift (W.specialize, C)).toMonoidHom
      (universalChange (MvPolynomial Coeff ℤ)).u = C.u :=
    congrArg VariableChange.u (map_lift (W.specialize, C))
  have h' : Units.map (lift (W.specialize, C)).toMonoidHom (weightCharacter k) =
      C.u ^ (-k) := by rw [weightCharacter, map_zpow, h]
  exact congrArg Units.val h'

/-- The first cobar differential for the weight-`k` coefficient line. -/
def cobarD₀ (k : ℤ) : MvPolynomial Coeff ℤ →ₗ[ℤ] ArrowRing :=
  rightUnit.toAddMonoidHom.toIntLinearMap -
    (LinearMap.mulLeft ℤ (weightCharacter k : ArrowRing)).comp
      (algebraMap (MvPolynomial Coeff ℤ) ArrowRing).toAddMonoidHom.toIntLinearMap

/-- The degree-zero cobar differential is the defect of the transformation law. -/
@[simp]
theorem cobarD₀_apply (k : ℤ) (f : MvPolynomial Coeff ℤ) :
    cobarD₀ k f = rightUnit f - weightCharacter k *
      algebraMap (MvPolynomial Coeff ℤ) ArrowRing f := (rfl)

/-- The second cobar differential, with the right factor representing the second arrow. -/
def cobarD₁ (k : ℤ) : ArrowRing →ₗ[ℤ] ChangeRing ArrowRing :=
  (ChangeRing.map rightUnit).toAddMonoidHom.toIntLinearMap -
    coproduct.toAddMonoidHom.toIntLinearMap +
    (LinearMap.mulLeft ℤ (ChangeRing.map rightUnit (weightCharacter k))).comp
      (algebraMap ArrowRing (ChangeRing ArrowRing)).toAddMonoidHom.toIntLinearMap

/-- A degree-one cocycle obeys the twisted additive composition law. -/
@[simp]
theorem cobarD₁_apply (k : ℤ) (a : ArrowRing) :
    cobarD₁ k a = ChangeRing.map rightUnit a - coproduct a +
      ChangeRing.map rightUnit (weightCharacter k) *
        algebraMap ArrowRing (ChangeRing ArrowRing) a := (rfl)

/-- On a curve and a change of variables, the first differential evaluates to the
failure of the weight transformation law. -/
theorem cobarD₀_specialize (k : ℤ) {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : VariableChange R) (f : MvPolynomial Coeff ℤ) :
    lift (W.specialize, C) (cobarD₀ k f) =
      (C • W).specialize f - (C.u ^ (-k) : Rˣ) * W.specialize f := by
  have hright : (lift (W.specialize, C)).comp rightUnit = (C • W).specialize := by
    simpa only [map_lift, lift_comp_algebraMap, map_specialize] using
      comp_rightUnit (lift (W.specialize, C))
  simp only [cobarD₀_apply, map_sub, map_mul, weightCharacter_specialize, lift_algebraMap]
  rw [← RingHom.comp_apply, hright]

/-- Evaluation on two successive coordinate changes pins the arrow order and the twist
in the degree-one cocycle equation. -/
theorem cobarD₁_specialize (k : ℤ) {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C₁ C₂ : VariableChange R) (a : ArrowRing) :
    lift (lift (W.specialize, C₁), C₂) (cobarD₁ k a) =
      lift ((C₁ • W).specialize, C₂) a - lift (W.specialize, C₂ * C₁) a +
        (C₂.u ^ (-k) : Rˣ) * lift (W.specialize, C₁) a := by
  let e := lift (lift (W.specialize, C₁), C₂)
  have hright : e.comp (ChangeRing.map rightUnit) = lift ((C₁ • W).specialize, C₂) := by
    refine ringHom_ext ?_ ?_
    · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc]
      simp only [e, lift_comp_algebraMap]
      simpa only [map_lift, lift_comp_algebraMap, map_specialize] using
        comp_rightUnit (lift (W.specialize, C₁))
    · simp [e, ← VariableChange.map_map]
  have hcomp : e.comp coproduct = lift (W.specialize, C₂ * C₁) := by
    refine ringHom_ext (RingHom.ext fun f ↦ by simp [e]) ?_
    rw [universalChange_map_comp_coproduct, hright]
    simp [e]
  have hr (x : ArrowRing) : e (ChangeRing.map rightUnit x) =
      lift ((C₁ • W).specialize, C₂) x := RingHom.congr_fun hright x
  have hc (x : ArrowRing) : e (coproduct x) = lift (W.specialize, C₂ * C₁) x :=
    RingHom.congr_fun hcomp x
  simp only [cobarD₁_apply, map_add, map_sub, map_mul, hr, hc,
    weightCharacter_specialize, e, lift_algebraMap]

/-- The two successive weighted cobar differentials compose to zero. -/
@[simp↓]
theorem cobarD₁_cobarD₀ (k : ℤ) (f : MvPolynomial Coeff ℤ) :
    cobarD₁ k (cobarD₀ k f) = 0 := by
  simp only [cobarD₁_apply, cobarD₀_apply, map_sub, map_mul,
    coproduct_rightUnit, coproduct_algebraMap, coproduct_weightCharacter,
    map_algebraMap]
  ring

/-- The weighted cobar sequence in degrees zero, one and two. Its native short-complex
homology is the degree-one cobar cohomology; no truncation claim in higher degrees is made.
This is an abbreviation so its three module carriers reduce when forming cocycles. -/
abbrev cobarShortComplex (k : ℤ) : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  CategoryTheory.ShortComplex.moduleCatMk (cobarD₀ k) (cobarD₁ k)
    (LinearMap.ext (cobarD₁_cobarD₀ k))

/-- The degree-zero cocycle condition is precisely the weight transformation law. -/
theorem cobarD₀_natCast_eq_zero_iff (k : ℕ) (f : MvPolynomial Coeff ℤ) :
    cobarD₀ (k : ℤ) f = 0 ↔ IsIntegralModularForm k f := by
  rw [isIntegralModularForm_iff_rightUnit, cobarD₀_apply, sub_eq_zero]
  simp [weightCharacter, zpow_neg, zpow_natCast]

/-- The degree-zero kernel is the module of integral modular forms of the specified weight. -/
theorem ker_cobarD₀_natCast (k : ℕ) :
    LinearMap.ker (cobarD₀ (k : ℤ)) =
      TauCeti.WeierstrassCurve.integralModularFormSubmodule k := by
  ext f
  simpa only [LinearMap.mem_ker,
    TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule] using
    cobarD₀_natCast_eq_zero_iff k f

/-- Every degree-one cocycle is normalized: it vanishes on identity arrows. -/
theorem counit_eq_zero_of_cobarD₁_eq_zero {k : ℤ} {a : ArrowRing}
    (ha : cobarD₁ k a = 0) : counit a = 0 := by
  have h := cobarD₁_specialize k Universal.curve 1 1 a
  rw [ha, map_zero] at h
  have hc : lift (RingHom.id (MvPolynomial Coeff ℤ), 1) = counit :=
    ringHom_ext (by simp) (by simp)
  simpa [Universal.specialize_curve, hc] using h.symm

end TauCeti.WeierstrassHopfAlgebroid
