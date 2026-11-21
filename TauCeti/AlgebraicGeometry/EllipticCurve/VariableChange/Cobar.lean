/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Nerve

/-!
# The cobar construction of the Weierstrass Hopf algebroid

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `Γ = A[u, u⁻¹, r, s, t]` be the rings of objects and arrows
of the Weierstrass Hopf algebroid. Its cobar construction is the cosimplicial commutative ring
`[n] ↦ Γ^{⊗_A n}`, whose alternating coface complex is the cobar complex computing
`Ext_Γ(A, A)`. This file constructs it and compares it with the groupoid of Weierstrass curves.

The `n`-fold tensor power `Γ ⊗_A ⋯ ⊗_A Γ` is the ring `cobarRing n`, obtained from `A` by
adjoining `n` times the coordinates `u, u⁻¹, r, s, t` of a change of variables
(`TauCeti.WeierstrassChange.ChangeRing`). A homomorphism `cobarRing n →+* R` is therefore a
Weierstrass curve `W` over `R` together with `n` changes of variables `C₀, …, Cₙ₋₁` over `R`
(`cobarRingEquiv`), that is, a string `W → C₀ • W → C₁ • C₀ • W → ⋯` of `n` composable arrows
of the action groupoid of `VariableChange R` on `WeierstrassCurve R` (`cobarNerveEquiv`). These
are the `n`-simplices of the nerve of that groupoid. The structure maps `cobarMap` of the
cosimplicial ring `cobarObject` are defined so that this identification is natural in `[n]`
(`cobarNerveEquiv_comp_cobarMap`) and in `R` (`cobarNerveEquiv_comp`): the cobar construction
corepresents the nerve of the Weierstrass groupoid, as a functor of the coefficient ring. Every
coefficient ring is allowed, including rings with nilpotents and the zero ring.

In every degree the structure maps are given by explicit formulas: the last coface is the
inclusion `algebraMap` of the first factors, the last codegeneracy is the counit on the last
factor, the coface merging the last two arrows is a coproduct on the last two factors, and the
other cofaces and codegeneracies are `ChangeRing.map` of those one degree lower. In low degrees
these are the structure maps of the Hopf algebroid: the two cofaces `A → Γ` are
the right unit `η_R` and the left unit `η_L`, the codegeneracy `Γ → A` is the counit `ε`, and the
three cofaces `Γ → Γ ⊗_A Γ` are the inclusion `ChangeRing.map η_R` of the second factor, the
coproduct `Δ` and the inclusion `algebraMap` of the first factor. These are the cofaces of the
unnormalised cobar complex of `(A, Γ)` with coefficients in `A`, whose `n`-cochains are
`Γ^{⊗_A n}`; here every coface is the one dual to the corresponding face of the nerve. The
alternating coface complex is `cobarComplex`, with differential `∑ᵢ (-1)ⁱ δⁱ`. Its differential
in degree `0` is `η_R - η_L`, and its degree `0` cocycles are the integral modular forms of
weight `0`.

The file also constructs the first two weighted cobar differentials, with coefficients in the
weight-`k` character `χ = u⁻ᵏ` for every integer `k`, including negative tensor powers of the
Hodge line. An arrow goes from `W` to `C • W`; in the ring of composable pairs the left factor is
the first arrow and the right factor is the second. With this order,

* `d₀(f) = η_R(f) - χ η_L(f)`;
* `d₁(a) = right(a) - Δ(a) + right(χ) left(a)`.

We prove `d₁ d₀ = 0` and package these maps as a short complex of abelian groups. Its
degree-zero kernel, in nonnegative weight, is exactly the module of integral modular forms. Every
degree-one cocycle vanishes on identity arrows, so the unnormalized and normalized degree-one
cocycle conditions agree. At weight `0` these are the formulas of the differentials of
`cobarComplex` in degrees `0` and `1`.

These differentials extend to the cobar complex of weight `k` in every degree. A cochain is read
as a section of `ω^k` trivialized at the last curve of a string, so the weight-`k` structure map
of `f : [m] ⟶ [n]` is `cobarMap f` followed by multiplication with the character `u⁻ᵏ` of the
change of variables from the curve `W_{f m}` to the last curve `W_n` (`cobarWeight`). These
weights form a cocycle because the character is multiplicative under the coproduct, so the
weight-`k` structure maps form a cosimplicial abelian group `weightedCobarObject k`, with
alternating coface complex `weightedCobarComplex k`. Its differentials in degrees `0` and `1` are
`cobarD₀ k` and `cobarD₁ k`, and in weight `0` its structure maps are those of `cobarObject`.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.cobarRing`: the ring `Γ^{⊗_A n}`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarNerveEquiv`: homomorphisms `Γ^{⊗_A n} →+* R` classify
  strings of `n` composable arrows of Weierstrass curves over `R`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarObject`: the cosimplicial commutative ring
  `[n] ↦ Γ^{⊗_A n}`, with structure maps `cobarMap`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarComplex`: its alternating coface complex.
* `TauCeti.WeierstrassHopfAlgebroid.weightCharacter`: the weight-`k` character `u⁻ᵏ` on arrows.
* `TauCeti.WeierstrassHopfAlgebroid.cobarD₀`, `TauCeti.WeierstrassHopfAlgebroid.cobarD₁`,
  `TauCeti.WeierstrassHopfAlgebroid.cobarShortComplex`: the first two weighted cobar
  differentials and their short complex.
* `TauCeti.WeierstrassHopfAlgebroid.weightedCobarObject`,
  `TauCeti.WeierstrassHopfAlgebroid.weightedCobarComplex`: the weight-`k` cosimplicial abelian
  group `[n] ↦ Γ^{⊗_A n}`, with structure maps `weightedCobarMap k`, and its cobar complex.

## Main results

* `cobarNerveEquiv_comp_cobarMap`: precomposition with the structure map of `f : [m] ⟶ [n]` is
  the simplicial operator of `f` on the nerve of the Weierstrass groupoid;
  `cobarRingEquiv_comp_cobarMap` is the same statement in coordinates.
* `cobarMap_δ_last`, `cobarMap_δ_castSucc_castSucc`, `cobarMap_δ_castSucc_last`,
  `cobarMap_σ_last`, `cobarMap_σ_castSucc`: the cofaces and codegeneracies in every degree.
* `cobarMap_δ_zero_eq_rightUnit`, `cobarMap_δ_one_eq_algebraMap`, `cobarMap_σ_zero_eq_counit`:
  the cofaces `A → Γ` are `η_R` and `η_L`, and the codegeneracy `Γ → A` is `ε`.
* `cobarMap_δ_zero_eq_map_rightUnit`, `cobarMap_δ_one_eq_coproduct`,
  `cobarMap_δ_two_eq_algebraMap`: the cofaces `Γ → Γ ⊗_A Γ` are the inclusion of the second
  factor, the coproduct `Δ` and the inclusion of the first factor.
* `cobarComplex_d_hom_apply`: the differential of the cobar complex is `∑ᵢ (-1)ⁱ δⁱ`;
  `cobarComplex_d_zero_one_hom_apply` and `cobarComplex_d_one_two_hom_apply` make it explicit in
  degrees `0` and `1`, where it is `η_R - η_L` and `x ↦ 1 ⊗ x - Δ x + x ⊗ 1`.
* `WeierstrassCurve.isIntegralModularForm_zero_iff_cobarComplex_d_zero_one_hom_apply_eq_zero`:
  the degree `0` cocycles of the cobar complex are the integral modular forms of weight `0`.
* `cobarD₁_cobarD₀`: the two weighted cobar differentials compose to zero;
  `cobarD₀_specialize` and `cobarD₁_specialize` evaluate them on curves and changes of variables.
* `ker_cobarD₀_natCast`: in weight `k ≥ 0`, the degree-zero weighted cocycles are the integral
  modular forms of weight `k`.
* `counit_eq_zero_of_cobarD₁_eq_zero`: every degree-one weighted cocycle is normalized.
* `cobarWeight_comp`: the weights of the structure maps are a cocycle, so `weightedCobarMap_comp`
  holds and `weightedCobarObject k` is a cosimplicial object.
* `weightedCobarComplex_d_hom_apply`: the differential of the weight-`k` cobar complex is
  `∑ᵢ (-1)ⁱ δⁱ`; `weightedCobarComplex_d_zero_one_hom_apply` and
  `weightedCobarComplex_d_one_two_hom_apply` identify it in degrees `0` and `1` with `cobarD₀ k`
  and `cobarD₁ k`.
* `WeierstrassCurve.isIntegralModularForm_iff_weightedCobarComplex_d_zero_one_hom_apply_eq_zero`:
  for `k ≥ 0`, the degree `0` cocycles of the weight-`k` cobar complex are the integral modular
  forms of weight `k`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.2
  (the cobar complex of a Hopf algebroid, Definition A1.2.11).
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3 (the Weierstrass Hopf algebroid and
  its cobar complex).
-/

public section

noncomputable section

universe u

/-! ### The first weighted cobar differentials -/

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

open CategoryTheory MvPolynomial Simplicial

namespace TauCeti.WeierstrassHopfAlgebroid

open _root_.WeierstrassCurve TauCeti.WeierstrassChange TauCeti.WeierstrassChange.ChangeRing
  TauCeti.ActionGroupoid

/-! ### The rings `Γ^{⊗_A n}` -/

/-- The ring `Γ^{⊗_A n} = Γ ⊗_A ⋯ ⊗_A Γ` of strings of `n` composable arrows of the Weierstrass
Hopf algebroid: `A = ℤ[a₁, ⋯, a₆]` for `n = 0`, and `cobarRing n` with the coordinates
`u, u⁻¹, r, s, t` of one more change of variables adjoined for `n + 1`. The adjoined coordinates
are those of the last arrow. So `cobarRing 1` is `ArrowRing` and `cobarRing 2` is
`ChangeRing ArrowRing`, the ring `Γ ⊗_A Γ` of the coproduct. -/
abbrev cobarRing : ℕ → CommRingCat.{0}
  | 0 => CommRingCat.of (MvPolynomial Coeff ℤ)
  | n + 1 => CommRingCat.of (ChangeRing (cobarRing n))

variable (R : Type u) [CommRing R]

/-- Homomorphisms `Γ^{⊗_A n} →+* R` classify a Weierstrass curve `W` over `R` with `n` changes of
variables `C₀, …, Cₙ₋₁` over `R`: the string of composable arrows
`W → C₀ • W → C₁ • C₀ • W → ⋯`. -/
def cobarRingEquiv : (n : ℕ) → (cobarRing n →+* R) ≃ WeierstrassCurve R × (Fin n → VariableChange R)
  | 0 =>
    { toFun k := (WeierstrassCurve.map Universal.curve k, Fin.elim0)
      invFun p := p.1.specialize
      left_inv k := by
        -- Beta-reduce the goal produced by `Function.LeftInverse`.
        beta_reduce
        rw [specialize_map, Universal.specialize_curve, RingHom.comp_id]
      right_inv p := Prod.ext (map_specialize p.1) (funext fun i ↦ i.elim0) }
  | n + 1 => lift.symm.trans <| ((cobarRingEquiv n).prodCongr (Equiv.refl _)).trans <|
      (Equiv.prodAssoc _ _ _).trans <| Equiv.prodCongr (Equiv.refl _) <|
        (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ VariableChange R)

/-- A homomorphism `k : A →+* R` classifies the specialization of the universal curve along `k`,
with no arrows. -/
theorem cobarRingEquiv_zero_apply (k : cobarRing 0 →+* R) :
    cobarRingEquiv R 0 k = (WeierstrassCurve.map Universal.curve k, Fin.elim0) :=
  (rfl)

/-- The homomorphism `A →+* R` classifying a curve `W` is the specialization `W.specialize`. -/
theorem cobarRingEquiv_zero_symm_apply (p : WeierstrassCurve R × (Fin 0 → VariableChange R)) :
    (cobarRingEquiv R 0).symm p = p.1.specialize :=
  (rfl)

/-- The string classified by `k : Γ^{⊗_A (n + 1)} →+* R` consists of the string classified by the
restriction of `k` to the first `n` factors, followed by the change of variables classified by `k`
on the last factor. -/
theorem cobarRingEquiv_succ_apply (n : ℕ) (k : cobarRing (n + 1) →+* R) :
    cobarRingEquiv R (n + 1) k =
      ((cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).1,
        Fin.snoc (cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).2
          ((universalChange (cobarRing n)).map k)) := by
  simp [cobarRingEquiv]

/-- The homomorphism `Γ^{⊗_A (n + 1)} →+* R` classifying a string of `n + 1` arrows restricts on the
first `n` factors to the homomorphism classifying its first `n` arrows, and classifies its last
change of variables on the last factor. -/
theorem cobarRingEquiv_succ_symm_apply (n : ℕ)
    (p : WeierstrassCurve R × (Fin (n + 1) → VariableChange R)) :
    (cobarRingEquiv R (n + 1)).symm p =
      lift ((cobarRingEquiv R n).symm (p.1, Fin.init p.2), p.2 (Fin.last n)) :=
  (rfl)

variable {R} in
/-- The classification of `cobarRingEquiv` is natural in the coefficient ring: composing with
`φ : R →+* S` base changes the curve and every change of variables along `φ`. -/
theorem cobarRingEquiv_comp {S : Type*} [CommRing S] (φ : R →+* S) :
    ∀ (n : ℕ) (k : cobarRing n →+* R), cobarRingEquiv S n (φ.comp k) =
      ((cobarRingEquiv R n k).1.map φ, fun i ↦ ((cobarRingEquiv R n k).2 i).map φ)
  | 0, k => Prod.ext (WeierstrassCurve.map_map Universal.curve k φ).symm (funext fun i ↦ i.elim0)
  | n + 1, k => by
    rw [cobarRingEquiv_succ_apply, cobarRingEquiv_succ_apply, RingHom.comp_assoc,
      cobarRingEquiv_comp φ n, ← VariableChange.map_map]
    exact Prod.ext rfl (Fin.comp_snoc (fun C : VariableChange R ↦ C.map φ) _ _).symm

/-- The curve classified by `k : Γ^{⊗_A (n + 1)} →+* R` is the curve classified by the restriction
of `k` to the first `n` factors. -/
@[simp]
theorem cobarRingEquiv_succ_apply_fst (n : ℕ) (k : cobarRing (n + 1) →+* R) :
    (cobarRingEquiv R (n + 1) k).1 =
      (cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).1 := by
  rw [cobarRingEquiv_succ_apply]

/-- The first `n` changes of variables classified by `k : Γ^{⊗_A (n + 1)} →+* R` are those
classified by the restriction of `k` to the first `n` factors. -/
@[simp]
theorem cobarRingEquiv_succ_apply_snd_castSucc (n : ℕ) (k : cobarRing (n + 1) →+* R)
    (i : Fin n) :
    (cobarRingEquiv R (n + 1) k).2 i.castSucc =
      (cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).2 i := by
  rw [cobarRingEquiv_succ_apply]
  exact Fin.snoc_castSucc (α := fun _ ↦ VariableChange R) _ _ _

/-- The last change of variables classified by `k : Γ^{⊗_A (n + 1)} →+* R` is the image of the
universal change of variables of the last factor. -/
@[simp]
theorem cobarRingEquiv_succ_apply_snd_last (n : ℕ) (k : cobarRing (n + 1) →+* R) :
    (cobarRingEquiv R (n + 1) k).2 (Fin.last n) = (universalChange (cobarRing n)).map k := by
  rw [cobarRingEquiv_succ_apply]
  exact Fin.snoc_last (α := fun _ ↦ VariableChange R) _ _

/-! ### Strings of composable arrows -/

/-- **The cobar rings corepresent the nerve of the Weierstrass groupoid**: homomorphisms
`Γ^{⊗_A n} →+* R` classify strings of `n` composable arrows of the action groupoid of the changes
of variables over `R` on the Weierstrass curves over `R`, the `n`-simplices of its nerve. -/
def cobarNerveEquiv (n : ℕ) : (cobarRing n →+* R) ≃
    ComposableArrows (ActionCategory (VariableChange R) (WeierstrassCurve R)) n :=
  (cobarRingEquiv R n).trans (nerveEquiv _ _ n).symm

/-- The string classified by `k` is the string with the curve and the changes of variables
classified by `k` under `cobarRingEquiv`. -/
theorem cobarNerveEquiv_apply (n : ℕ) (k : cobarRing n →+* R) :
    cobarNerveEquiv R n k = (nerveEquiv _ _ n).symm (cobarRingEquiv R n k) :=
  (rfl)

/-- The homomorphism classifying a string is the one classifying its first curve and its
consecutive changes of variables under `cobarRingEquiv`. -/
theorem cobarNerveEquiv_symm_apply (n : ℕ)
    (F : ComposableArrows (ActionCategory (VariableChange R) (WeierstrassCurve R)) n) :
    (cobarNerveEquiv R n).symm F = (cobarRingEquiv R n).symm (nerveEquiv _ _ n F) :=
  (rfl)

/-- In the coordinates of `TauCeti.ActionGroupoid.nerveEquiv`, the string classified by `k` has
the curve and the changes of variables classified by `k` under `cobarRingEquiv`. -/
theorem nerveEquiv_cobarNerveEquiv (n : ℕ) (k : cobarRing n →+* R) :
    nerveEquiv _ _ n (cobarNerveEquiv R n k) = cobarRingEquiv R n k :=
  (nerveEquiv _ _ n).apply_symm_apply _

variable {R} in
/-- The classification of `cobarNerveEquiv` is natural in the coefficient ring: composing with
`φ : R →+* S` applies the functor induced by base change along `φ`. -/
theorem cobarNerveEquiv_comp {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ)
    (k : cobarRing n →+* R) :
    cobarNerveEquiv S n (φ.comp k) =
      ((ActionCategory.map (VariableChange.mapHom φ) (mapMulActionHom φ)).mapComposableArrows
        n).obj (cobarNerveEquiv R n k) := by
  apply (nerveEquiv _ _ n).injective
  simp only [nerveEquiv_cobarNerveEquiv, nerveEquiv_mapComposableArrows_obj, cobarRingEquiv_comp,
    mapMulActionHom_apply, VariableChange.mapHom_apply]

variable {R} in
/-- The homomorphism classifying the base change of a string along `φ : R →+* S` is the
composite of `φ` with the homomorphism classifying the string. -/
theorem cobarNerveEquiv_symm_mapComposableArrows_obj {S : Type*} [CommRing S] (φ : R →+* S)
    (n : ℕ) (F : ComposableArrows (ActionCategory (VariableChange R) (WeierstrassCurve R)) n) :
    (cobarNerveEquiv S n).symm
        (((ActionCategory.map (VariableChange.mapHom φ) (mapMulActionHom φ)).mapComposableArrows
          n).obj F) =
      φ.comp ((cobarNerveEquiv R n).symm F) := by
  rw [Equiv.symm_apply_eq, cobarNerveEquiv_comp, Equiv.apply_symm_apply]

/-! ### The cosimplicial ring -/

/-- The structure map `Γ^{⊗_A m} →+* Γ^{⊗_A n}` of `f : [m] ⟶ [n]` of the cobar construction. It
classifies the image of the universal string of `n` composable arrows under the simplicial
operator of `f` on the nerve (`cobarNerveEquiv_cobarMap`). -/
def cobarMap {m n : SimplexCategory} (f : m ⟶ n) : cobarRing m.len →+* cobarRing n.len :=
  (cobarNerveEquiv _ m.len).symm
    ((nerve _).map f.op (cobarNerveEquiv _ n.len (RingHom.id (cobarRing n.len))))

/-- The structure map `cobarMap f` classifies the image of the universal string under the
simplicial operator of `f : [m] ⟶ [n]` on the nerve of the Weierstrass groupoid. -/
theorem cobarNerveEquiv_cobarMap {m n : SimplexCategory} (f : m ⟶ n) :
    cobarNerveEquiv _ m.len (cobarMap f) =
      (nerve _).map f.op (cobarNerveEquiv _ n.len (RingHom.id (cobarRing n.len))) :=
  Equiv.apply_symm_apply _ _

/-- Precomposing with `cobarMap f` acts on strings of composable arrows by the simplicial operator
of `f : [m] ⟶ [n]` on the nerve of the Weierstrass groupoid. -/
theorem cobarNerveEquiv_comp_cobarMap {m n : SimplexCategory} (f : m ⟶ n)
    (k : cobarRing n.len →+* R) :
    cobarNerveEquiv R m.len (k.comp (cobarMap f)) =
      (nerve _).map f.op (cobarNerveEquiv R n.len k) := by
  have hk : cobarNerveEquiv R n.len k =
      ((ActionCategory.map (VariableChange.mapHom k) (mapMulActionHom k)).mapComposableArrows
        n.len).obj (cobarNerveEquiv _ n.len (RingHom.id (cobarRing n.len))) := by
    rw [← cobarNerveEquiv_comp, RingHom.comp_id]
  rw [cobarNerveEquiv_comp, cobarNerveEquiv_cobarMap, hk]
  -- The functor induced by `k` commutes with the simplicial operators of the nerve.
  exact Functor.assoc _ _ _

/-- The homomorphism classifying the image of a string under the simplicial operator of
`f : [m] ⟶ [n]` is the composite of `cobarMap f` with the homomorphism classifying the string. -/
theorem cobarNerveEquiv_symm_nerve_map {m n : SimplexCategory} (f : m ⟶ n)
    (F : ComposableArrows (ActionCategory (VariableChange R) (WeierstrassCurve R)) n.len) :
    (cobarNerveEquiv R m.len).symm ((nerve _).map f.op F) =
      ((cobarNerveEquiv R n.len).symm F).comp (cobarMap f) :=
  (Equiv.symm_apply_eq _).mpr <| by rw [cobarNerveEquiv_comp_cobarMap, Equiv.apply_symm_apply]

/-- The structure map of the identity is the identity. -/
@[simp]
theorem cobarMap_id (n : SimplexCategory) : cobarMap (𝟙 n) = RingHom.id (cobarRing n.len) := by
  apply (cobarNerveEquiv _ n.len).injective
  rw [cobarNerveEquiv_cobarMap, op_id]
  exact (nerve _).map_id_apply _ _

/-- The structure maps compose contravariantly to the simplicial operators. -/
@[simp]
theorem cobarMap_comp {l m n : SimplexCategory} (f : l ⟶ m) (g : m ⟶ n) :
    cobarMap (f ≫ g) = (cobarMap g).comp (cobarMap f) := by
  apply (cobarNerveEquiv _ l.len).injective
  rw [cobarNerveEquiv_comp_cobarMap, cobarNerveEquiv_cobarMap, cobarNerveEquiv_cobarMap, op_comp]
  exact (nerve _).map_comp_apply _ _ _

/-- **The cobar construction of the Weierstrass Hopf algebroid**: the cosimplicial commutative
ring `[n] ↦ Γ^{⊗_A n}`, with structure maps `cobarMap`. -/
@[expose]
def cobarObject : CosimplicialObject CommRingCat.{0} where
  obj n := cobarRing n.len
  map f := CommRingCat.ofHom (cobarMap f)
  map_id n := by
    ext1
    rw [CommRingCat.hom_ofHom, cobarMap_id, CommRingCat.hom_id]
  map_comp f g := by
    ext1
    rw [CommRingCat.hom_ofHom, cobarMap_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom]

/-- The objects of `cobarObject` are the rings `Γ^{⊗_A n}`. -/
theorem cobarObject_obj (n : SimplexCategory) : cobarObject.obj n = cobarRing n.len :=
  (rfl)

/-- The structure maps of `cobarObject` are the homomorphisms `cobarMap`. -/
@[simp]
theorem cobarObject_map_hom {m n : SimplexCategory} (f : m ⟶ n) :
    (cobarObject.map f).hom = cobarMap f :=
  (rfl)

/-- The cofaces of `cobarObject` are the homomorphisms `cobarMap (δ i)`. -/
@[simp]
theorem cobarObject_δ_hom {n : ℕ} (i : Fin (n + 2)) :
    (cobarObject.δ i).hom = cobarMap (SimplexCategory.δ i) :=
  (rfl)

/-- The codegeneracies of `cobarObject` are the homomorphisms `cobarMap (σ i)`. -/
@[simp]
theorem cobarObject_σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (cobarObject.σ i).hom = cobarMap (SimplexCategory.σ i) :=
  (rfl)

/-- **The structure maps in coordinates.** Let `k : Γ^{⊗_A n} →+* R` classify the string
`W → C₀ • W → C₁ • C₀ • W → ⋯` and write `Dⱼ = Cⱼ₋₁ ⋯ C₀` for the composite change of variables
from the first to the `j`-th curve. Then `k ∘ cobarMap f` classifies the string with first curve
`D_{f 0} • W` and changes of variables `D_{f (i + 1)} D_{f i}⁻¹`. -/
theorem cobarRingEquiv_comp_cobarMap {m n : SimplexCategory} (f : m ⟶ n)
    (k : cobarRing n.len →+* R) :
    cobarRingEquiv R m.len (k.comp (cobarMap f)) =
      ((Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
          (f.toOrderHom 0)).unop • (cobarRingEquiv R n.len k).1,
        fun i ↦ (Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
            (f.toOrderHom i.succ)).unop *
          (Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
            (f.toOrderHom i.castSucc)).unop⁻¹) := by
  rw [← nerveEquiv_cobarNerveEquiv, cobarNerveEquiv_comp_cobarMap, cobarNerveEquiv_apply,
    nerveEquiv_nerve_map_nerveEquiv_symm]

/-- `cobarRingEquiv_comp_cobarMap` for the universal string: `cobarMap f` classifies the string
with first curve `D_{f 0} • W` and changes of variables `D_{f (i + 1)} D_{f i}⁻¹`, where `W` and
`Dⱼ` are the universal curve and composite changes of variables over `Γ^{⊗_A n}`. -/
theorem cobarRingEquiv_cobarMap {m n : SimplexCategory} (f : m ⟶ n) :
    cobarRingEquiv _ m.len (cobarMap f) =
      ((Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv _ n.len (RingHom.id _)).2 i))
          (f.toOrderHom 0)).unop • (cobarRingEquiv _ n.len (RingHom.id (cobarRing n.len))).1,
        fun i ↦ (Fin.partialProd
            (fun i ↦ MulOpposite.op ((cobarRingEquiv _ n.len (RingHom.id _)).2 i))
            (f.toOrderHom i.succ)).unop *
          (Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv _ n.len (RingHom.id _)).2 i))
            (f.toOrderHom i.castSucc)).unop⁻¹) := by
  rw [← cobarRingEquiv_comp_cobarMap, RingHom.id_comp]

/-! ### The cofaces and codegeneracies -/

/-- The last coface `δⁿ⁺¹ : Γ^{⊗_A n} → Γ^{⊗_A (n + 1)}` is the inclusion `algebraMap` of the first
`n` factors, classifying the first `n` arrows of a string of `n + 1` composable arrows. -/
@[simp]
theorem cobarMap_δ_last (n : ℕ) :
    cobarMap (SimplexCategory.δ (Fin.last (n + 1))) =
      algebraMap (cobarRing n) (cobarRing (n + 1)) := by
  apply (cobarRingEquiv _ n).injective
  rw [cobarRingEquiv_cobarMap]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.succAbove_last,
      Fin.castSucc_zero, Fin.partialProd_zero, MulOpposite.unop_one, one_smul]
    exact cobarRingEquiv_succ_apply_fst _ n (RingHom.id _)
  · simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.succAbove_last,
      Fin.castSucc_succ, Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_op,
      mul_inv_cancel_right]
    exact cobarRingEquiv_succ_apply_snd_castSucc _ n (RingHom.id _) i

/-- A coface `δⁱ : Γ^{⊗_A (n + 1)} → Γ^{⊗_A (n + 2)}` with `i ≤ n` is `ChangeRing.map` of the
coface `δⁱ : Γ^{⊗_A n} → Γ^{⊗_A (n + 1)}`: it does not involve the last arrow. -/
@[simp]
theorem cobarMap_δ_castSucc_castSucc (n : ℕ) (i : Fin (n + 1)) :
    cobarMap (SimplexCategory.δ i.castSucc.castSucc) =
      ChangeRing.map (cobarMap (SimplexCategory.δ i.castSucc)) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · have h := congrArg cobarMap (SimplexCategory.δ_comp_δ (Fin.le_last i.castSucc)).symm
    simp only [cobarMap_comp, Fin.succ_last, cobarMap_δ_last] at h
    rw [ChangeRing.map_comp_algebraMap]
    exact h
  · rw [universalChange_map_map, ← cobarRingEquiv_succ_apply_snd_last, cobarRingEquiv_cobarMap]
    simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      Fin.succ_last, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
      Fin.succAbove_ne_last_last (Fin.castSucc_ne_last _), Fin.castSucc_succAbove_castSucc]
    rw [← Fin.succ_last (n + 1), Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_op,
      mul_inv_cancel_right, cobarRingEquiv_succ_apply_snd_last, VariableChange.map_id]

/-- The coface `δⁿ⁺¹ : Γ^{⊗_A (n + 1)} → Γ^{⊗_A (n + 2)}` multiplies the last two arrows: it
classifies the string whose first `n` arrows come from the first `n` factors and whose last
change of variables is the composite of the last two. -/
@[simp]
theorem cobarMap_δ_castSucc_last (n : ℕ) :
    cobarMap (SimplexCategory.δ (Fin.last (n + 1)).castSucc) =
      lift ((algebraMap (cobarRing (n + 1)) (cobarRing (n + 2))).comp
          (algebraMap (cobarRing n) (cobarRing (n + 1))),
        universalChange (cobarRing (n + 1)) *
          (universalChange (cobarRing n)).map
            (algebraMap (cobarRing (n + 1)) (cobarRing (n + 2)))) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · have h := congrArg cobarMap (SimplexCategory.δ_comp_δ_self (i := Fin.last (n + 1)))
    simp only [cobarMap_comp, Fin.succ_last, cobarMap_δ_last] at h
    rw [lift_comp_algebraMap]
    exact h
  · rw [map_lift, ← cobarRingEquiv_succ_apply_snd_last, cobarRingEquiv_cobarMap]
    simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      Fin.succ_last, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
      Fin.succAbove_ne_last_last (Fin.castSucc_ne_last _), Fin.castSucc_succAbove_castSucc,
      Fin.succAbove_last]
    rw [← Fin.succ_last (n + 1), Fin.partialProd_succ, ← Fin.succ_last n, ← Fin.succ_castSucc,
      Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_op, mul_assoc, mul_inv_cancel_right, Fin.succ_last,
      cobarRingEquiv_succ_apply_snd_last, cobarRingEquiv_succ_apply_snd_castSucc,
      cobarRingEquiv_succ_apply_snd_last, VariableChange.map_id, RingHom.id_comp]

/-- The last codegeneracy `σⁿ : Γ^{⊗_A (n + 1)} → Γ^{⊗_A n}` is the identity on the first `n`
factors and the counit on the last: it classifies the string extended by an identity arrow. -/
@[simp]
theorem cobarMap_σ_last (n : ℕ) :
    cobarMap (SimplexCategory.σ (Fin.last n)) = lift (RingHom.id (cobarRing n), 1) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · have h := congrArg cobarMap (SimplexCategory.δ_comp_σ_succ (i := Fin.last n))
    simp only [cobarMap_comp, cobarMap_id, Fin.succ_last, cobarMap_δ_last] at h
    rw [lift_comp_algebraMap]
    exact h
  · rw [map_lift, ← cobarRingEquiv_succ_apply_snd_last, cobarRingEquiv_cobarMap]
    simp [SimplexCategory.σ]

/-- A codegeneracy `σⁱ : Γ^{⊗_A (n + 2)} → Γ^{⊗_A (n + 1)}` with `i ≤ n` is `ChangeRing.map` of
the codegeneracy `σⁱ : Γ^{⊗_A (n + 1)} → Γ^{⊗_A n}`: it does not involve the last arrow. -/
@[simp]
theorem cobarMap_σ_castSucc (n : ℕ) (i : Fin (n + 1)) :
    cobarMap (SimplexCategory.σ i.castSucc) = ChangeRing.map (cobarMap (SimplexCategory.σ i)) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · have h := congrArg cobarMap (SimplexCategory.δ_comp_σ_of_gt (Fin.castSucc_lt_last i))
    simp only [cobarMap_comp, Fin.succ_last, cobarMap_δ_last] at h
    rw [ChangeRing.map_comp_algebraMap]
    exact h
  · rw [universalChange_map_map, ← cobarRingEquiv_succ_apply_snd_last, cobarRingEquiv_cobarMap]
    simp only [SimplexCategory.σ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      Fin.succ_last, Fin.predAboveOrderHom_coe, Fin.predAbove_right_last,
      Fin.castSucc_predAbove_castSucc]
    rw [← Fin.succ_last n, Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_op,
      mul_inv_cancel_right, cobarRingEquiv_succ_apply_snd_last, VariableChange.map_id]

/-! ### Comparison with the Hopf algebroid structure maps -/

/-- A homomorphism `k : Γ →+* R` classifies the string consisting of the single arrow
`arrowEquiv R k`. -/
theorem cobarRingEquiv_one_apply (k : ArrowRing →+* R) :
    cobarRingEquiv R 1 k = ((arrowEquiv R k).1, fun _ ↦ (arrowEquiv R k).2) := by
  rw [cobarRingEquiv_succ_apply, cobarRingEquiv_zero_apply, arrowEquiv_apply]
  exact Prod.ext rfl (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl)

/-- The coface `δ⁰ : A → Γ` of the cobar construction is the right unit `η_R`, classifying the
target of an arrow. -/
@[simp]
theorem cobarMap_δ_zero_eq_rightUnit : cobarMap (SimplexCategory.δ (n := 0) 0) = rightUnit := by
  apply (cobarRingEquiv _ 0).injective
  rw [cobarRingEquiv_cobarMap, cobarRingEquiv_one_apply, cobarRingEquiv_zero_apply]
  refine Prod.ext ?_ (funext fun i ↦ i.elim0)
  simp [SimplexCategory.δ, Fin.partialProd, List.ofFn_succ, map_rightUnit]

/-- The coface `δ¹ : A → Γ` of the cobar construction is the left unit `η_L = algebraMap`,
classifying the source of an arrow. -/
@[simp]
theorem cobarMap_δ_one_eq_algebraMap :
    cobarMap (SimplexCategory.δ (n := 0) 1) = algebraMap (MvPolynomial Coeff ℤ) ArrowRing :=
  cobarMap_δ_last 0

/-- The codegeneracy `σ⁰ : Γ → A` of the cobar construction is the counit `ε`, classifying the
identity arrows. -/
@[simp]
theorem cobarMap_σ_zero_eq_counit : cobarMap (SimplexCategory.σ (n := 0) 0) = counit := by
  refine (cobarMap_σ_last 0).trans (ringHom_ext ?_ ?_)
  · rw [lift_comp_algebraMap, counit_comp_algebraMap]
  · rw [map_lift, universalChange_map_counit]

/-- The coface `δ⁰ : Γ → Γ ⊗_A Γ` of the cobar construction is the inclusion `ChangeRing.map η_R`
of the second factor, classifying the second arrow of a composable pair. -/
@[simp]
theorem cobarMap_δ_zero_eq_map_rightUnit :
    cobarMap (SimplexCategory.δ (n := 1) 0) = ChangeRing.map rightUnit :=
  (cobarMap_δ_castSucc_castSucc 0 0).trans (congrArg ChangeRing.map cobarMap_δ_zero_eq_rightUnit)

/-- The coface `δ¹ : Γ → Γ ⊗_A Γ` of the cobar construction is the coproduct `Δ`, classifying the
composite of a composable pair. -/
@[simp]
theorem cobarMap_δ_one_eq_coproduct : cobarMap (SimplexCategory.δ (n := 1) 1) = coproduct := by
  refine (cobarMap_δ_castSucc_last 0).trans (ringHom_ext ?_ ?_)
  · rw [lift_comp_algebraMap, coproduct_comp_algebraMap]
  · rw [map_lift, universalChange_map_coproduct]

/-- The coface `δ² : Γ → Γ ⊗_A Γ` of the cobar construction is the inclusion `algebraMap` of the
first factor, classifying the first arrow of a composable pair. -/
@[simp]
theorem cobarMap_δ_two_eq_algebraMap :
    cobarMap (SimplexCategory.δ (n := 1) 2) = algebraMap ArrowRing (ChangeRing ArrowRing) :=
  cobarMap_δ_last 1

/-! ### The cobar complex -/

/-- **The cobar complex** of the Weierstrass Hopf algebroid with coefficients in
`A = ℤ[a₁, ⋯, a₆]`: the alternating coface complex of `cobarObject`, with `n`-cochains
`Γ^{⊗_A n}` and differential `∑ᵢ (-1)ⁱ δⁱ`. -/
@[expose]
def cobarComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj
    (cobarObject ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- The `n`-cochains of the cobar complex are the additive group of `Γ^{⊗_A n}`. -/
theorem cobarComplex_X (n : ℕ) : cobarComplex.X n = AddCommGrpCat.of (cobarRing n) :=
  (rfl)

/-- The differential of the alternating coface complex of a cosimplicial additive group, evaluated
at a cochain, is the alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the cofaces. -/
private theorem alternatingCofaceMapComplex_d_hom_apply (X : CosimplicialObject AddCommGrpCat.{0})
    (n : ℕ) (x : X.obj ⦋n⦌) :
    (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj X).d n (n + 1)).hom x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i).hom x := by
  have h : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj X).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X n :=
    CochainComplex.of_d (fun n ↦ X.obj (SimplexCategory.mk n)) _ n
  rw [h]
  -- Restate the goal with the morphism typed by the cosimplicial object, not the complex.
  change (AlgebraicTopology.AlternatingCofaceMapComplex.objD X n).hom x = _
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  -- Evaluating a morphism of additive groups is additive in the morphism.
  refine (congrArg (fun g : X.obj ⦋n⦌ →+ X.obj ⦋n + 1⦌ ↦ g x)
    (map_sum AddCommGrpCat.homAddEquiv _ Finset.univ)).trans ?_
  refine (AddMonoidHom.finsetSum_apply _ _ x).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [map_zsmul]
  rfl

/-- The differential `Γ^{⊗_A n} → Γ^{⊗_A (n + 1)}` of the cobar complex is the alternating sum
`∑ᵢ (-1)ⁱ δⁱ` of the cofaces. -/
theorem cobarComplex_d_hom_apply (n : ℕ) (x : cobarRing n) :
    (cobarComplex.d n (n + 1)).hom x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cobarMap (SimplexCategory.δ i) x :=
  -- The forgetful functors to additive groups keep the underlying functions of the cofaces.
  alternatingCofaceMapComplex_d_hom_apply
    (cobarObject ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) n x

/-- The differential `A → Γ` of the cobar complex in degree `0` is `η_R - η_L`. -/
theorem cobarComplex_d_zero_one_hom_apply (x : MvPolynomial Coeff ℤ) :
    (cobarComplex.d 0 1).hom x = rightUnit x - algebraMap (MvPolynomial Coeff ℤ) ArrowRing x := by
  have h := cobarComplex_d_hom_apply 0 x
  rw [Fin.sum_univ_two, cobarMap_δ_zero_eq_rightUnit, cobarMap_δ_one_eq_algebraMap] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    ← sub_eq_add_neg] at h
  exact h

/-- The differential `Γ → Γ ⊗_A Γ` of the cobar complex in degree `1` is
`x ↦ 1 ⊗ x - Δ x + x ⊗ 1`. -/
theorem cobarComplex_d_one_two_hom_apply (x : ArrowRing) :
    (cobarComplex.d 1 2).hom x =
      ChangeRing.map rightUnit x - coproduct x + algebraMap ArrowRing (ChangeRing ArrowRing) x := by
  have h := cobarComplex_d_hom_apply 1 x
  rw [Fin.sum_univ_three, cobarMap_δ_zero_eq_map_rightUnit, cobarMap_δ_one_eq_coproduct,
    cobarMap_δ_two_eq_algebraMap] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul,
    neg_one_sq, ← sub_eq_add_neg] at h
  exact h

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open TauCeti.WeierstrassHopfAlgebroid

/-- The degree `0` cocycles of the cobar complex of the Weierstrass Hopf algebroid are the
integral modular forms of weight `0`. -/
theorem isIntegralModularForm_zero_iff_cobarComplex_d_zero_one_hom_apply_eq_zero
    (f : MvPolynomial Coeff ℤ) :
    IsIntegralModularForm 0 f ↔ (cobarComplex.d 0 1).hom f = 0 := by
  rw [cobarComplex_d_zero_one_hom_apply, isIntegralModularForm_iff_rightUnit, pow_zero, one_mul]
  exact sub_eq_zero.symm

end WeierstrassCurve


/-! ### The weighted cobar complex -/

namespace TauCeti.WeierstrassHopfAlgebroid

open CategoryTheory MvPolynomial Simplicial _root_.WeierstrassCurve TauCeti.WeierstrassChange

/-- The twist of the weight-`k` structure map of `f : [m] ⟶ [n]`: the weight-`k` character `u⁻ᵏ`
of the composite change of variables from the curve `W_{f m}` to the last curve `W_n` of the
universal string over `Γ^{⊗_A n}`. A cochain is read as a section of `ω^k` trivialized at the last
curve of a string, and this factor transports it from `W_{f m}` to `W_n`. -/
def cobarWeight (k : ℤ) {m n : SimplexCategory} (f : m ⟶ n) : cobarRing n.len :=
  cobarMap (SimplexCategory.mkOfLe (f.toOrderHom (Fin.last m.len)) (Fin.last n.len)
    (Fin.le_last _)) (weightCharacter k : ArrowRing)

/-- A map `f : [m] ⟶ [n]` keeping the last vertex has trivial weight. -/
theorem cobarWeight_eq_one (k : ℤ) {m n : SimplexCategory} {f : m ⟶ n}
    (hf : f.toOrderHom (Fin.last m.len) = Fin.last n.len) : cobarWeight k f = 1 := by
  -- The edge from the last vertex to itself factors through `[0]` by the codegeneracy `σ⁰`.
  have h : SimplexCategory.mkOfLe (f.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _) =
        SimplexCategory.σ (n := 0) 0 ≫ SimplexCategory.const ⦋0⦌ n (Fin.last n.len) :=
    SimplexCategory.Hom.ext_one_left _ _ hf
  rw [cobarWeight, h, cobarMap_comp, RingHom.comp_apply, cobarMap_σ_zero_eq_counit,
    counit_weightCharacter, map_one]

@[simp]
theorem cobarWeight_id (k : ℤ) (n : SimplexCategory) : cobarWeight k (𝟙 n) = 1 :=
  cobarWeight_eq_one k rfl

/-- In weight `0` every weight is trivial. -/
@[simp]
theorem cobarWeight_zero {m n : SimplexCategory} (f : m ⟶ n) : cobarWeight 0 f = 1 := by
  rw [cobarWeight, weightCharacter_zero, Units.val_one, map_one]

/-- **The weights are a cocycle**: transporting from `W_{g (f l)}` to `W_{g m}` and then to `W_n` is
transporting from `W_{g (f l)}` to `W_n`. This is the multiplicativity of the weight character
under the coproduct, `coproduct_weightCharacter`. -/
theorem cobarWeight_comp (k : ℤ) {l m n : SimplexCategory} (f : l ⟶ m) (g : m ⟶ n) :
    cobarWeight k (f ≫ g) = cobarMap g (cobarWeight k f) * cobarWeight k g := by
  -- The three edges between `g (f l)`, `g m` and `n` are the faces of one `2`-simplex `T`.
  let T := SimplexCategory.mkOfLeComp (g.toOrderHom (f.toOrderHom (Fin.last l.len)))
    (g.toOrderHom (Fin.last m.len)) (Fin.last n.len)
    (g.toOrderHom.monotone (Fin.le_last _)) (Fin.le_last _)
  have h₀ : SimplexCategory.mkOfLe (g.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _) = SimplexCategory.δ (n := 1) 0 ≫ T :=
    SimplexCategory.Hom.ext_one_left _ _
  have h₁ : SimplexCategory.mkOfLe ((f ≫ g).toOrderHom (Fin.last l.len)) (Fin.last n.len)
      (Fin.le_last _) = SimplexCategory.δ (n := 1) 1 ≫ T :=
    SimplexCategory.Hom.ext_one_left _ _
  have h₂ : SimplexCategory.mkOfLe (f.toOrderHom (Fin.last l.len)) (Fin.last m.len)
      (Fin.le_last _) ≫ g = SimplexCategory.δ (n := 1) 2 ≫ T :=
    SimplexCategory.Hom.ext_one_left _ _
  rw [cobarWeight, cobarWeight, cobarWeight, ← RingHom.comp_apply, ← cobarMap_comp, h₀, h₁, h₂]
  simp only [cobarMap_comp, RingHom.comp_apply, cobarMap_δ_zero_eq_map_rightUnit,
    cobarMap_δ_one_eq_coproduct, cobarMap_δ_two_eq_algebraMap, coproduct_weightCharacter, map_mul]
  exact mul_comm _ _

/-- The weight-`k` structure map `Γ^{⊗_A m} → Γ^{⊗_A n}` of `f : [m] ⟶ [n]`: the structure map
`cobarMap f` followed by multiplication with the weight `cobarWeight k f`. -/
def weightedCobarMap (k : ℤ) {m n : SimplexCategory} (f : m ⟶ n) :
    cobarRing m.len →+ cobarRing n.len :=
  (AddMonoidHom.mulLeft (cobarWeight k f)).comp (cobarMap f).toAddMonoidHom

@[simp]
theorem weightedCobarMap_apply (k : ℤ) {m n : SimplexCategory} (f : m ⟶ n)
    (x : cobarRing m.len) : weightedCobarMap k f x = cobarWeight k f * cobarMap f x :=
  (rfl)

@[simp]
theorem weightedCobarMap_id (k : ℤ) (n : SimplexCategory) :
    weightedCobarMap k (𝟙 n) = AddMonoidHom.id (cobarRing n.len) := by
  ext x
  rw [weightedCobarMap_apply, cobarWeight_id, cobarMap_id, one_mul, RingHom.id_apply,
    AddMonoidHom.id_apply]

/-- The weight-`k` structure maps compose contravariantly to the simplicial operators. -/
@[simp]
theorem weightedCobarMap_comp (k : ℤ) {l m n : SimplexCategory} (f : l ⟶ m) (g : m ⟶ n) :
    weightedCobarMap k (f ≫ g) = (weightedCobarMap k g).comp (weightedCobarMap k f) := by
  ext x
  rw [AddMonoidHom.comp_apply, weightedCobarMap_apply, weightedCobarMap_apply,
    weightedCobarMap_apply, cobarWeight_comp, cobarMap_comp, RingHom.comp_apply, map_mul]
  ring

/-- In weight `0` the weighted structure maps are the structure maps `cobarMap`. -/
theorem weightedCobarMap_zero {m n : SimplexCategory} (f : m ⟶ n) :
    weightedCobarMap 0 f = (cobarMap f).toAddMonoidHom := by
  ext x
  rw [weightedCobarMap_apply, cobarWeight_zero, one_mul, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass]

/-- **The weight-`k` cobar construction** of the Weierstrass Hopf algebroid: the cosimplicial
abelian group `[n] ↦ Γ^{⊗_A n}` of cochains with coefficients in `ω^k`, with structure maps
`weightedCobarMap k`. In weight `0` these are the structure maps of `cobarObject`. -/
@[expose]
def weightedCobarObject (k : ℤ) : CosimplicialObject AddCommGrpCat.{0} where
  obj n := AddCommGrpCat.of (cobarRing n.len)
  map f := AddCommGrpCat.ofHom (weightedCobarMap k f)
  map_id n := by
    ext1
    rw [AddCommGrpCat.hom_ofHom, weightedCobarMap_id, AddCommGrpCat.hom_id]
  map_comp f g := by
    ext1
    rw [AddCommGrpCat.hom_ofHom, weightedCobarMap_comp, AddCommGrpCat.hom_comp,
      AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_ofHom]

/-- The objects of `weightedCobarObject k` are the additive groups of the rings `Γ^{⊗_A n}`. -/
theorem weightedCobarObject_obj (k : ℤ) (n : SimplexCategory) :
    (weightedCobarObject k).obj n = AddCommGrpCat.of (cobarRing n.len) :=
  (rfl)

/-- The structure maps of `weightedCobarObject k` are the weight-`k` structure maps. -/
@[simp]
theorem weightedCobarObject_map_hom (k : ℤ) {m n : SimplexCategory} (f : m ⟶ n) :
    ((weightedCobarObject k).map f).hom = weightedCobarMap k f :=
  (rfl)

/-- The cofaces of `weightedCobarObject k` are the weight-`k` structure maps of the `δ i`. -/
@[simp]
theorem weightedCobarObject_δ_hom (k : ℤ) {n : ℕ} (i : Fin (n + 2)) :
    ((weightedCobarObject k).δ i).hom = weightedCobarMap k (SimplexCategory.δ i) :=
  (rfl)

/-- The codegeneracies of `weightedCobarObject k` are the weight-`k` structure maps of the
`σ i`. -/
@[simp]
theorem weightedCobarObject_σ_hom (k : ℤ) {n : ℕ} (i : Fin (n + 1)) :
    ((weightedCobarObject k).σ i).hom = weightedCobarMap k (SimplexCategory.σ i) :=
  (rfl)

/-- **The cobar complex of weight `k`** of the Weierstrass Hopf algebroid, with coefficients in the
`k`-th power `ω^k` of the Hodge line: the alternating coface complex of `weightedCobarObject k`,
with `n`-cochains `Γ^{⊗_A n}` and differential `∑ᵢ (-1)ⁱ δⁱ` of the weight-`k` cofaces. In degrees
`0` and `1` its differentials are `cobarD₀ k` and `cobarD₁ k`. -/
@[expose]
def weightedCobarComplex (k : ℤ) : CochainComplex AddCommGrpCat.{0} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj (weightedCobarObject k)

/-- The `n`-cochains of the weight-`k` cobar complex are the additive group of `Γ^{⊗_A n}`. -/
theorem weightedCobarComplex_X (k : ℤ) (n : ℕ) :
    (weightedCobarComplex k).X n = AddCommGrpCat.of (cobarRing n) :=
  (rfl)

/-- The differential `Γ^{⊗_A n} → Γ^{⊗_A (n + 1)}` of the weight-`k` cobar complex is the
alternating sum `∑ᵢ (-1)ⁱ δⁱ` of the weight-`k` cofaces. -/
theorem weightedCobarComplex_d_hom_apply (k : ℤ) (n : ℕ) (x : cobarRing n) :
    ((weightedCobarComplex k).d n (n + 1)).hom x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • weightedCobarMap k (SimplexCategory.δ i) x :=
  -- The cofaces of `weightedCobarObject k` are the maps `weightedCobarMap k (δ i)`.
  alternatingCofaceMapComplex_d_hom_apply (weightedCobarObject k) n x

/-- The differential `A → Γ` of the weight-`k` cobar complex in degree `0` is the first weighted
cobar differential `f ↦ η_R(f) - u⁻ᵏ η_L(f)`. -/
theorem weightedCobarComplex_d_zero_one_hom_apply (k : ℤ) (x : MvPolynomial Coeff ℤ) :
    ((weightedCobarComplex k).d 0 1).hom x = cobarD₀ k x := by
  have h₀ : cobarWeight k (SimplexCategory.δ (n := 0) 0) = 1 := cobarWeight_eq_one k rfl
  -- The coface `δ¹` keeps the first vertex, so its weight is that of the universal arrow.
  have h₁ : cobarWeight k (SimplexCategory.δ (n := 0) 1) = weightCharacter k := by
    rw [cobarWeight, show SimplexCategory.mkOfLe _ _ _ = 𝟙 ⦋1⦌ from
      SimplexCategory.Hom.ext_one_left _ _, cobarMap_id, RingHom.id_apply]
  rw [weightedCobarComplex_d_hom_apply, Fin.sum_univ_two, weightedCobarMap_apply,
    weightedCobarMap_apply, h₀, h₁, cobarMap_δ_zero_eq_rightUnit, cobarMap_δ_one_eq_algebraMap,
    cobarD₀_apply]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_mul,
    ← sub_eq_add_neg]
  -- The two sides differ only in spelling `Γ` as `cobarRing 1` or `ArrowRing`.
  rfl

/-- The differential `Γ → Γ ⊗_A Γ` of the weight-`k` cobar complex in degree `1` is the second
weighted cobar differential `a ↦ 1 ⊗ a - Δ a + (1 ⊗ u⁻ᵏ)(a ⊗ 1)`. -/
theorem weightedCobarComplex_d_one_two_hom_apply (k : ℤ) (x : ArrowRing) :
    ((weightedCobarComplex k).d 1 2).hom x = cobarD₁ k x := by
  have h₀ : cobarWeight k (SimplexCategory.δ (n := 1) 0) = 1 := cobarWeight_eq_one k rfl
  have h₁ : cobarWeight k (SimplexCategory.δ (n := 1) 1) = 1 := cobarWeight_eq_one k rfl
  -- The coface `δ²` forgets the second arrow, so its weight is that of the second arrow.
  have h₂ : cobarWeight k (SimplexCategory.δ (n := 1) 2) =
      ChangeRing.map rightUnit (weightCharacter k : ArrowRing) := by
    rw [cobarWeight, show SimplexCategory.mkOfLe _ _ _ = SimplexCategory.δ (n := 1) 0 from
      SimplexCategory.Hom.ext_one_left _ _, cobarMap_δ_zero_eq_map_rightUnit]
  rw [weightedCobarComplex_d_hom_apply, Fin.sum_univ_three, weightedCobarMap_apply,
    weightedCobarMap_apply, weightedCobarMap_apply, h₀, h₁, h₂, cobarMap_δ_zero_eq_map_rightUnit,
    cobarMap_δ_one_eq_coproduct, cobarMap_δ_two_eq_algebraMap, cobarD₁_apply]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul,
    neg_one_sq, one_mul, ← sub_eq_add_neg]
  -- The two sides differ only in spelling `Γ ⊗_A Γ` as `cobarRing 2` or `ChangeRing ArrowRing`.
  rfl

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open TauCeti.WeierstrassHopfAlgebroid

/-- **The degree `0` cocycles of the weight-`k` cobar complex are the integral modular forms of
weight `k`**, for `k ≥ 0`. -/
theorem isIntegralModularForm_iff_weightedCobarComplex_d_zero_one_hom_apply_eq_zero (k : ℕ)
    (f : MvPolynomial Coeff ℤ) :
    IsIntegralModularForm k f ↔ ((weightedCobarComplex k).d 0 1).hom f = 0 := by
  rw [weightedCobarComplex_d_zero_one_hom_apply]
  exact (cobarD₀_natCast_eq_zero_iff k f).symm

end WeierstrassCurve
