/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.FieldTheory.FunctionField.ConstantField
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring

/-!
# Existence of extensions of places

Every place of an algebraic function field extends across an integral field extension. More
generally, the base field may also grow by an integral extension: a valuation trivial on the
smaller base field is automatically trivial on the larger one. For an extension of algebraic
function fields with `F' / F` finite, both integrality hypotheses are automatic, the one on the
base fields because the base extension is then finite. The same argument shows that the places
above a place `P` see the whole integral closure of its valuation ring: an element regular at
all of them is integral over `𝒪_P`.

The proof dominates the local valuation ring of the original place by a valuation subring of the
larger function field. Locality ensures that the resulting valuation subring is proper. Since
valuation subrings are integrally closed, it contains the enlarged base field, so it defines a
place whose restriction is the original place.

## Main results

* `TauCeti.Place.restrict_surjective`: every place downstairs is the restriction of a place
  upstairs (Stichtenoth, Proposition 3.1.7).
* `TauCeti.Place.restrict_surjective_of_finiteDimensional`: the same statement for an extension
  of algebraic function fields, where both integrality hypotheses are theorems rather than
  hypotheses.
* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`: the integral closure of the
  valuation ring `𝒪_P` in the larger field is the intersection of the valuation rings of the
  places above `P` (Stichtenoth, Section III.2).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.7 and Section III.2.
-/

public section

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
section Integral

variable [Algebra.IsIntegral k k'] [Algebra.IsIntegral F F']

/-- **Existence of extensions of places** (Stichtenoth, Proposition 3.1.7): if both the field
extension and the base-field extension are integral, every place of `F / k` is the restriction
of a place of `F' / k'`. -/
theorem restrict_surjective (hF' : IsFunctionField k' F') :
    Function.Surjective (fun P' : Place k' F' ↦ restrict k F P') := by
  intro P
  let f : P.integers →+* F' := (algebraMap F F').comp P.integers.subtype
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  have hA_ne_top : A ≠ ⊤ := by
    obtain ⟨t, ht⟩ := P.exists_isUniformizer
    have hord : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at hord
    have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
    let t₀ : P.integers := ⟨t, htmem⟩
    intro htop
    have hmap0 : f t₀ ≠ 0 := by simp [f, t₀, ht0]
    have hinv : (f t₀)⁻¹ ∈ A := htop.symm ▸ ValuationSubring.mem_top _
    have hunit : IsUnit ((f.codRestrict A.toSubring hA) t₀) := by
      rw [isUnit_iff_exists_inv]
      exact ⟨⟨(f t₀)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hmap0)⟩
    have htunit : IsUnit t₀ := hlocal.map_nonunit t₀ hunit
    have htord0 : P.ord t = 0 := by
      simpa only [t₀] using P.isUnit_iff_ord_eq_zero ht0 |>.mp htunit
    exact one_ne_zero (hord.symm.trans htord0)
  have hkA : ∀ c : k, algebraMap k F' c ∈ A := by
    intro c
    have hc := hA ⟨algebraMap k F c, P.algebraMap_mem_integers c⟩
    simpa only [f, RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype,
      ValuationSubring.mem_toSubring, IsScalarTower.algebraMap_apply k F F'] using hc
  let _ : Algebra k A.toLocalSubring.toSubring :=
    ((algebraMap k F').codRestrict A.toLocalSubring.toSubring hkA).toAlgebra
  let _ : IsScalarTower k A.toLocalSubring.toSubring F' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hk'A : ∀ c : k', algebraMap k' F' c ∈ A := by
    intro c
    apply LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring
    exact (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let P' : Place k' F' := ofValuationSubring hF' hk'A hA_ne_top
  refine ⟨P', (restrict_eq_iff_integers_le k F P' P).mpr ?_⟩
  intro x hx
  have hP'_integers : P'.integers = A := by
    dsimp only [P']
    exact integers_ofValuationSubring hF' hk'A hA_ne_top
  rw [hP'_integers]
  have hAx := hA ⟨x, hx⟩
  simpa only [f, RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype,
    ValuationSubring.mem_toSubring] using hAx

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The integral closure of `𝒪_P` is the intersection of the valuation rings above `P`**
(Stichtenoth, Section III.2): an element of `F'` is integral over the valuation ring of a place
`P` of `F / k` exactly when it is regular at every place of `F' / k'` lying over `P`.

An element outside the integral closure is separated from it by a valuation subring of `F'`; that
subring contains the base field `k'`, whose elements are integral over `k`, and it contains
`𝒪_P`, so it is the valuation ring of a place lying over `P`. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers (hF' : IsFunctionField k' F')
    (P : Place k F) {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  refine ⟨fun hx P' hP' ↦ P'.mem_integers_of_isIntegral (fun a ↦ ?_) hx, fun h ↦ ?_⟩
  · subst hP'
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  by_contra hx
  have hxB : x ∉ (integralClosure P.integers F').toSubring := hx
  obtain ⟨V, hBV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hxB
  have : IsScalarTower k P.integers F' :=
    .of_algebraMap_eq fun c ↦ IsScalarTower.algebraMap_apply k F F' c
  have hk'V : ∀ c : k', algebraMap k' F' c ∈ V := fun c ↦ hBV
    ((Algebra.IsIntegral.isIntegral (R := k) c).map (IsScalarTower.toAlgHom k k' F')).tower_top
  have hV : V ≠ ⊤ := fun hV ↦ hxV (hV ▸ ValuationSubring.mem_top _)
  have hP' : (ofValuationSubring hF' hk'V hV).restrict k F = P := by
    refine (restrict_eq_iff_integers_le k F _ P).mpr fun f hf ↦ ?_
    rw [integers_ofValuationSubring]
    exact hBV (isIntegral_algebraMap (x := (⟨f, hf⟩ : P.integers)))
  exact hxV (integers_ofValuationSubring hF' hk'V hV ▸ h _ hP')
end Integral

/-- **Existence of extensions of places for an extension of function fields** (Stichtenoth,
Proposition 3.1.7): every place of `F / k` is the restriction of a place of `F' / k'`.

Unlike `TauCeti.Place.restrict_surjective`, this asks nothing of the base extension: `k' / k` is
finite by `TauCeti.IsFunctionField.finiteDimensional_baseExtension`.  Neither statement subsumes
the other, since `TauCeti.Place.restrict_surjective` allows an infinite algebraic extension
`F' / F`. -/
theorem restrict_surjective_of_finiteDimensional [FiniteDimensional F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') :
    Function.Surjective (fun P' : Place k' F' ↦ restrict k F P') :=
  have := hF.finiteDimensional_baseExtension hF'
  have := Algebra.IsIntegral.of_finite k k'
  have := Algebra.IsIntegral.of_finite F F'
  restrict_surjective hF'

end Place

end TauCeti
