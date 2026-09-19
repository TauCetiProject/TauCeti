/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm

/-!
# Pulling a divisor back along an isogeny

An isogeny embeds `F(W₂)` in `F(W₁)` as a finite extension, and the conorm of that extension is
the pullback of divisors: the coefficient of `φ* D` at a place `P'` is `e(P' ∣ P)` times the
coefficient of `D` at the place below it. Nothing about curves enters beyond the embedding being
finite, which is what the degree of an isogeny says.

The one fact the divisor construction of the Weil pairing needs of this is that it carries
principal divisors to principal divisors: `φ*(div z)` is the divisor of the pulled-back function.
That is what lets a function with a prescribed divisor be pulled back and its divisor read off.

## Conventions

The algebra structure on `F(W₁)` over `F(W₂)` is not an instance — it depends on `φ` — so it is
taken as a parameter together with the hypothesis that its structure map is `fieldPullback`, the
form `TauCeti.Isogeny.degree_eq_finrank` and `TauCeti.Isogeny.finiteDimensional_functionField`
already use. A caller supplies it with `let _ := φ.fieldPullback.toRingHom.toAlgebra`.

## Main definitions

* `TauCeti.Isogeny.divisorPullback`: **the pullback of a divisor along an isogeny**.

## Main results

* `TauCeti.Isogeny.coeff_divisorPullback` and `TauCeti.Isogeny.mem_support_divisorPullback_iff`:
  the coefficient formula and the support, the characteristic API of the pullback.
* `TauCeti.Isogeny.divisorPullback_ofPoint`: the pullback of a point divisor is its fibre,
  weighted by the ramification indices.
* `TauCeti.Isogeny.divisorPullback_mono`, `TauCeti.Isogeny.isEffective_divisorPullback` and
  `TauCeti.Isogeny.divisorPullback_injective`: it is monotone, preserves effectivity, and is
  injective.
* `TauCeti.Isogeny.divisorPullback_principal`: **it carries `div z` to the divisor of the
  pulled-back function**, and `TauCeti.Isogeny.linearlyEquivalent_divisorPullback` that it
  respects linear equivalence.
* `TauCeti.Isogeny.divisorPullback_id`: **the identity law** — `id* D = D`.
* `TauCeti.Isogeny.divisorPullback_comp`: **it is contravariantly functorial** — pulling back
  along a composite is pulling back twice, in the reverse order.
* `TauCeti.Isogeny.divisorPullbackClassGroup` and
  `TauCeti.Isogeny.divisorPullbackClassGroup_divisorClass`: the induced map on divisor classes,
  and its value on the class of a divisor, with the identity and composition laws
  `TauCeti.Isogeny.divisorPullbackClassGroup_id` and
  `TauCeti.Isogeny.divisorPullbackClassGroup_comp`.

Each is the corresponding `TauCeti.Divisor.conorm` result read through the isogeny; the definition
is opaque outside this module, so the wrappers are what a consumer has.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 3.1.8 and
  Proposition 3.1.9.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3.
-/

public section

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)
  [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

/-- **The pullback of a divisor along an isogeny**: the conorm of the finite extension of function
fields that the isogeny induces. -/
noncomputable def divisorPullback :
    Divisor F W₂.FunctionField →+ Divisor F W₁.FunctionField :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm F W₁.FunctionField

/-! ### The coefficients and the support

These three read the place below `P'`, so the base-field tower and the finiteness of the extension
have to be in scope for their statements to elaborate, not just for their proofs. Both follow from
`h`, so they are installed while the statement elaborates rather than quantified: a caller that can
supply `h` should not have to supply them a second time. -/

section Coefficients

/-- **The defining coefficient formula**: the coefficient of `φ* D` at a place `P'` of `F(W₁)` is
`e(P' ∣ P)` times the coefficient of `D` at the place `P` below it. -/
@[simp]
theorem coeff_divisorPullback (D : Divisor F W₂.FunctionField)
    (P' : Place F W₁.FunctionField) :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    (φ.divisorPullback h D).coeff P' =
      Place.ramificationIdx W₂.FunctionField P' *
        D.coeff (P'.restrict F W₂.FunctionField) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.coeff_conorm ..

/-- A place of `F(W₁)` lies in the support of `φ* D` exactly when the place below it lies in the
support of `D`: the ramification indices are positive, so nothing cancels. -/
@[grind =]
theorem mem_support_divisorPullback_iff {D : Divisor F W₂.FunctionField}
    {P' : Place F W₁.FunctionField} :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    P' ∈ (φ.divisorPullback h D).support ↔ P'.restrict F W₂.FunctionField ∈ D.support :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.mem_support_conorm_iff ..

/-- **The pullback of a point divisor is its fibre**, the places above `P` weighted by their
ramification indices — geometrically `φ⁻¹(P)` with multiplicity. -/
theorem divisorPullback_ofPoint (P : Place F W₂.FunctionField) :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    φ.divisorPullback h (WeilDivisor.ofPoint P) =
      WeilDivisor.ofFinsetWithMultiplicity
        (Place.finite_setOf_restrict_eq (k' := F) (F' := W₁.FunctionField) F
          W₂.FunctionField P).toFinset
        (Place.ramificationIdx W₂.FunctionField) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_ofPoint ..

end Coefficients

/-- The pullback is monotone: it multiplies coefficients by positive ramification indices. -/
theorem divisorPullback_mono : Monotone (φ.divisorPullback h) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_mono ..

/-- The pullback of an effective divisor is effective. -/
theorem isEffective_divisorPullback {D : Divisor F W₂.FunctionField} (hD : D.IsEffective) :
    (φ.divisorPullback h D).IsEffective :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.isEffective_conorm F W₁.FunctionField hD

/-- **The pullback is injective**: every place of `F(W₂)` is the restriction of a place of
`F(W₁)`, and the ramification indices are nonzero. -/
theorem divisorPullback_injective : Function.Injective (φ.divisorPullback h) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_injective F W₁.FunctionField W₁.isFunctionField

/-- **An isogeny carries `div z` to the divisor of the pulled-back function** (Stichtenoth,
Proposition 3.1.9). This is the step the divisor construction of the Weil pairing runs on: a
function with a prescribed divisor pulls back to one whose divisor is the pullback. -/
theorem divisorPullback_principal (z : W₂.FunctionFieldˣ) :
    φ.divisorPullback h (Divisor.principal W₂.isFunctionField z) =
      Divisor.principal W₁.isFunctionField
        (Units.map (algebraMap W₂.FunctionField W₁.FunctionField : _ →* _) z) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm_principal F W₁.FunctionField W₂.isFunctionField W₁.isFunctionField z

/-- **The pullback respects linear equivalence** (Stichtenoth, Proposition 3.1.9), so it descends
to divisor classes. -/
theorem linearlyEquivalent_divisorPullback {A B : Divisor F W₂.FunctionField}
    (hAB : (Place.orderSystem W₂.isFunctionField).LinearlyEquivalent A B) :
    (Place.orderSystem W₁.isFunctionField).LinearlyEquivalent
      (φ.divisorPullback h A) (φ.divisorPullback h B) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.linearlyEquivalent_conorm F W₁.FunctionField W₂.isFunctionField W₁.isFunctionField hAB

/-! ### Functoriality and divisor classes -/

section Comp

variable {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
  [Algebra W₃.FunctionField W₂.FunctionField] [Algebra W₃.FunctionField W₁.FunctionField]
  (hψ : ∀ z, algebraMap W₃.FunctionField W₂.FunctionField z = ψ.fieldPullback z)
  (hc : ∀ z, algebraMap W₃.FunctionField W₁.FunctionField z = (ψ.comp φ).fieldPullback z)

include h hψ hc in
/-- The three pullbacks of a composite form a scalar tower, `F(W₃) ⊆ F(W₂) ⊆ F(W₁)`. -/
private theorem isScalarTower_of_comp :
    IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun z ↦ by
    simp [hc, hψ, h, comp_fieldPullback]

/-- **Pulling back along a composite is pulling back twice**, in the reverse order (Stichtenoth,
Definition 3.1.8): the conorm is transitive in a tower, and the three function-field embeddings
form one. -/
@[simp]
theorem divisorPullback_comp (D : Divisor F W₃.FunctionField) :
    φ.divisorPullback h (ψ.divisorPullback hψ D) = (ψ.comp φ).divisorPullback hc D :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback ψ hψ
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback (ψ.comp φ) hc
  haveI := isScalarTower_of_comp φ h ψ hψ hc
  haveI := φ.finiteDimensional_functionField h
  haveI := ψ.finiteDimensional_functionField hψ
  Divisor.conorm_conorm (k₀ := F) (F₀ := W₃.FunctionField) (k₁ := F) (F₁ := W₂.FunctionField)
    (k₂ := F) (F₂ := W₁.FunctionField) D

end Comp

section Id

/-- **The identity law**: pulling back along `Isogeny.id` changes nothing. -/
-- Proof: `divisorPullback_comp` at `φ = ψ = id` is pulling back once along `id.comp id = id`,
-- and `divisorPullback_injective` cancels the outer pullback.
@[simp]
theorem divisorPullback_id {W : WeierstrassCurve.Affine F}
    [Algebra W.FunctionField W.FunctionField]
    (hid : ∀ z, algebraMap W.FunctionField W.FunctionField z = (Isogeny.id W).fieldPullback z)
    (D : Divisor F W.FunctionField) :
    (Isogeny.id W).divisorPullback hid D = D := by
  have hc : ∀ z, algebraMap W.FunctionField W.FunctionField z =
      ((Isogeny.id W).comp (Isogeny.id W)).fieldPullback z := by
    simpa only [Isogeny.id_comp] using hid
  refine divisorPullback_injective (Isogeny.id W) hid ?_
  rw [divisorPullback_comp (Isogeny.id W) hid (Isogeny.id W) hid hc D]
  simp only [Isogeny.id_comp]

end Id

/-- **The pullback on divisor classes**: the pullback carries principal divisors to principal
divisors, so it descends to a homomorphism `Cl(F(W₂)) →+ Cl(F(W₁))`. -/
noncomputable def divisorPullbackClassGroup :
    (Place.orderSystem W₂.isFunctionField).ClassGroup →+
      (Place.orderSystem W₁.isFunctionField).ClassGroup :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conormClassGroup F W₁.FunctionField W₂.isFunctionField W₁.isFunctionField

/-- **The pullback on classes is the pullback on divisors**, which is what makes the descent
usable: a class given by a divisor is carried to the class of its pullback. -/
@[simp]
theorem divisorPullbackClassGroup_divisorClass (D : Divisor F W₂.FunctionField) :
    φ.divisorPullbackClassGroup h ((Place.orderSystem W₂.isFunctionField).divisorClass D) =
      (Place.orderSystem W₁.isFunctionField).divisorClass (φ.divisorPullback h D) :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conormClassGroup_divisorClass F W₁.FunctionField W₂.isFunctionField
    W₁.isFunctionField D

/-- **The identity law on classes.** -/
@[simp]
theorem divisorPullbackClassGroup_id {W : WeierstrassCurve.Affine F}
    [Algebra W.FunctionField W.FunctionField]
    (hid : ∀ z, algebraMap W.FunctionField W.FunctionField z = (Isogeny.id W).fieldPullback z) :
    (Isogeny.id W).divisorPullbackClassGroup hid = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun c ↦ ?_
  obtain ⟨D, rfl⟩ := (Place.orderSystem W.isFunctionField).divisorClass_surjective c
  rw [divisorPullbackClassGroup_divisorClass, divisorPullback_id, AddMonoidHom.id_apply]

/-- **Contravariant functoriality on classes**, the quotient of `divisorPullback_comp`. -/
@[simp]
theorem divisorPullbackClassGroup_comp {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
    [Algebra W₃.FunctionField W₂.FunctionField] [Algebra W₃.FunctionField W₁.FunctionField]
    (hψ : ∀ z, algebraMap W₃.FunctionField W₂.FunctionField z = ψ.fieldPullback z)
    (hc : ∀ z, algebraMap W₃.FunctionField W₁.FunctionField z = (ψ.comp φ).fieldPullback z) :
    (φ.divisorPullbackClassGroup h).comp (ψ.divisorPullbackClassGroup hψ) =
      (ψ.comp φ).divisorPullbackClassGroup hc := by
  refine AddMonoidHom.ext fun c ↦ ?_
  obtain ⟨D, rfl⟩ := (Place.orderSystem W₃.isFunctionField).divisorClass_surjective c
  rw [AddMonoidHom.comp_apply, divisorPullbackClassGroup_divisorClass,
    divisorPullbackClassGroup_divisorClass, divisorPullbackClassGroup_divisorClass,
    divisorPullback_comp]

end TauCeti.Isogeny

end
