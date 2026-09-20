/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting

/-!
# A separable isogeny is unramified

A separable isogeny `φ : W₁ → W₂` of elliptic curves makes `F(W₁)` a finite separable extension of
the pulled-back function field `F(W₂)`, and both fields have genus one.  The Hurwitz genus formula

`2g₁ - 2 = n · (2g₂ - 2) + deg Diff(F(W₁)/F(W₂))`

therefore reads `0 = 0 + deg Diff`.  The different divisor is effective, so a vanishing degree
forces it to vanish, and a vanishing different exponent forces the ramification index to be `1`:
**every** place of `F(W₁)` is unramified over `F(W₂)`, with no exceptional locus.

Ramification is what separates the fundamental identity `∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = deg φ`
from a count of the fibre of `P`.  With `e ≡ 1` the identity becomes `∑_{P' ∣ P} f(P' ∣ P) = deg φ`
at every place. Over a separably closed field of constants, the vanishing different also makes
each relative residue extension separable, hence trivial, so `P` has exactly `deg φ` places above
it.

## Main results

* `TauCeti.Isogeny.different_eq_zero`: the different divisor of a separable isogeny vanishes.
* `TauCeti.Isogeny.ramificationIdx_eq_one`: **a separable isogeny is unramified** — `e(P' ∣ P) = 1`
  at every place `P'` of `F(W₁)`.
* `TauCeti.Isogeny.sum_relativeDegree_eq_degree`: the fundamental identity with the ramification
  indices removed, `∑_{P' ∣ P} f(P' ∣ P) = deg φ`.
* `TauCeti.Isogeny.isSplitCompletely` and `TauCeti.Isogeny.ncard_setOf_restrict_eq_degree`: over
  a separably closed field of constants every place splits completely, so it has exactly
  `deg φ` places above it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.5.9 and III.4.10.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Theorem 3.1.11,
  Remark 3.4.4 and Theorem 3.4.13.
-/

public section

namespace TauCeti

private theorem Place.relativeDegree_eq_one_of_isSepClosed_of_differentExponent_eq_zero
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] (P' : Place k F')
    [IsSepClosed (P'.restrict k F).ResidueField]
    (hd : P'.differentExponent k F = 0) : P'.relativeDegree k F = 1 := by
  have htame : P'.IsTame k F :=
    (P'.ramificationIdx_eq_differentExponent_add_one_iff k F).mp <| by
      have := P'.ramificationIdx_le_differentExponent_add_one k F
      have := P'.ramificationIdx_pos F
      omega
  have hsep := (P'.isTame_iff k F).mp htame |>.1
  let _ : IsScalarTower k (P'.restrict k F).integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F',
      ← IsScalarTower.algebraMap_apply k (P'.restrict k F).integers F,
      ← IsScalarTower.algebraMap_apply k F F']
  have hconstants : ∀ c : k, algebraMap k F' c ∈
      integralClosure (P'.restrict k F).integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k (integralClosure (P'.restrict k F).integers F') :=
    ((algebraMap k F').codRestrict _ hconstants).toAlgebra
  let _ : IsScalarTower k (integralClosure (P'.restrict k F).integers F') F' :=
    .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra (P'.restrict k F).ResidueField
      (integralClosure (P'.restrict k F).integers F' ⧸
        (P'.centerIntegralClosure k F).asIdeal) :=
    Ideal.Quotient.algebraOfLiesOver (P'.centerIntegralClosure k F).asIdeal
      (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
  let _ : Algebra.IsSeparable (P'.restrict k F).ResidueField
      (integralClosure (P'.restrict k F).integers F' ⧸
        (P'.centerIntegralClosure k F).asIdeal) := hsep
  have hsepClosed : IsSepClosed (P'.restrict k F).ResidueField := inferInstance
  let _ : (P'.centerIntegralClosure k F).asIdeal.IsMaximal :=
    (P'.centerIntegralClosure k F).isPrime.isMaximal
      (P'.centerIntegralClosure k F).ne_bot
  let _ : Field ((P'.restrict k F).integers ⧸
      IsLocalRing.maximalIdeal (P'.restrict k F).integers) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
  let _ : Field (integralClosure (P'.restrict k F).integers F' ⧸
      (P'.centerIntegralClosure k F).asIdeal) :=
    Ideal.Quotient.field (P'.centerIntegralClosure k F).asIdeal
  let _ : IsSepClosed ((P'.restrict k F).integers ⧸
      IsLocalRing.maximalIdeal (P'.restrict k F).integers) :=
    ⟨hsepClosed.splits_of_separable⟩
  rw [P'.relativeDegree_eq_inertiaDeg_center (R := (P'.restrict k F).integers) k F
    (P'.algebraMap_mem_integers_of_mem_integralClosure k F)]
  rw [← P'.centerIntegralClosure_def k F]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
      (P'.centerIntegralClosure k F).asIdeal,
    Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsSepClosed.algebraMap_bijective _ _

namespace Isogeny

open AlgebraicGeometry WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **The different divisor of a separable isogeny vanishes.** -/
@[simp]
theorem different_eq_zero :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    haveI := φ.isSeparable_functionField h
    Divisor.different F W₁.FunctionField W₂.isFunctionField = 0 := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  have := φ.isSeparable_functionField h
  have hzero : Divisor.degree (Divisor.different F W₁.FunctionField W₂.isFunctionField) = 0 := by
    have hg := hurwitz_genus_formula_geometricDegree (k := F) (k' := F)
      W₂.isFunctionField W₁.isFunctionField (isIntegrallyClosedIn_functionField W₂)
      (isIntegrallyClosedIn_functionField W₁)
    rw [genus_functionField, genus_functionField] at hg
    norm_num at hg
    omega
  exact (Divisor.eq_of_le_of_degree_eq W₁.isFunctionField
    (Divisor.zero_le_different F W₁.FunctionField W₂.isFunctionField)
    (by rw [map_zero, hzero])).symm

include φ h in
/-- **A separable isogeny is unramified**: every place of `F(W₁)` has ramification index `1` over
the place of `F(W₂)` below it (Silverman III.4.10(c)). -/
@[simp]
theorem ramificationIdx_eq_one (P' : Place F W₁.FunctionField) :
    Place.ramificationIdx W₂.FunctionField P' = 1 := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  have := φ.isSeparable_functionField h
  have hd := (Divisor.different_eq_zero_iff F W₁.FunctionField W₂.isFunctionField).mp
    (different_eq_zero φ h) P'
  have hle := Place.ramificationIdx_le_differentExponent_add_one F W₂.FunctionField P'
  have hpos := Place.ramificationIdx_pos W₂.FunctionField P'
  omega

/-- **The fundamental identity for a separable isogeny**: the relative degrees of the places above
a place `P` of `F(W₂)` sum to `deg φ`, the ramification indices of `∑ e · f = deg φ` having all
been removed by `ramificationIdx_eq_one`.

The fibre of `P` is its finite set of places, `TauCeti.Place.finite_setOf_restrict_eq`. -/
theorem sum_relativeDegree_eq_degree (P : Place F W₂.FunctionField) :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    ∑ P' ∈ (Place.finite_setOf_restrict_eq (k' := F) (F' := W₁.FunctionField) F
      W₂.FunctionField P).toFinset, Place.relativeDegree F W₂.FunctionField P' = φ.degree := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  have := φ.isSeparable_functionField h
  rw [φ.degree_eq_finrank h,
    ← Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable F W₂.FunctionField P
      fun P' ↦ (Place.finite_setOf_restrict_eq (k' := F) (F' := W₁.FunctionField) F
        W₂.FunctionField P).mem_toFinset]
  exact Finset.sum_congr rfl fun P' _ ↦ by rw [ramificationIdx_eq_one φ h P', one_mul]

include φ h in
/-- **Over a separably closed field of constants every place splits completely in a separable
isogeny** (Silverman III.4.10(a) in its place-theoretic form). -/
theorem isSplitCompletely [IsSepClosed F] (P : Place F W₂.FunctionField) :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    P.IsSplitCompletely (k' := F) (F' := W₁.FunctionField) := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  have := φ.isSeparable_functionField h
  rw [Place.isSplitCompletely_iff_forall_ramificationIdx_eq_one_and_relativeDegree_eq_one]
  intro P' _
  have hd := (Divisor.different_eq_zero_iff F W₁.FunctionField W₂.isFunctionField).mp
    (different_eq_zero φ h) P'
  have := (P'.restrict F W₂.FunctionField).finiteDimensional_residueField W₂.isFunctionField
  let _ : IsSepClosed (P'.restrict F W₂.FunctionField).ResidueField :=
    Algebra.IsAlgebraic.isSepClosed (F := F)
      (E := (P'.restrict F W₂.FunctionField).ResidueField)
  exact ⟨ramificationIdx_eq_one φ h P',
    P'.relativeDegree_eq_one_of_isSepClosed_of_differentExponent_eq_zero hd⟩

/-- **A separable isogeny over a separably closed field of constants has exactly `deg φ`
places above every place**, the count form of `Isogeny.isSplitCompletely` read against the degree
of the isogeny rather than against the degree of the field extension. -/
@[simp]
theorem ncard_setOf_restrict_eq_degree [IsSepClosed F] (P : Place F W₂.FunctionField) :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    {P' : Place F W₁.FunctionField | P'.restrict F W₂.FunctionField = P}.ncard = φ.degree := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  rw [φ.degree_eq_finrank h, ← Place.isSplitCompletely_def]
  exact isSplitCompletely φ h P

end Isogeny

end TauCeti
