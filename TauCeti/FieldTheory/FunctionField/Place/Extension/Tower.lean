/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Towers of extensions of places

Restriction of places is functorial through a tower of algebraic field extensions. The
ramification index and relative residue degree are multiplicative in the same tower. These are
the tower statements in Stichtenoth, *Algebraic Function Fields and Codes*, Proposition 3.1.6.

The constants are allowed to grow with the function fields. Thus the setup contains parallel
towers `k₀ → k₁ → k₂` and `F₀ → F₁ → F₂`, with each `Fᵢ` an algebra over `kᵢ` and the
expected commuting scalar towers. No function-field, finite-dimensionality, separability, or
perfectness hypothesis is needed: restriction uses only integrality of the field extensions,
and the degree identity is the ordinary finrank tower formula for the residue fields.

## Main results

* `TauCeti.Place.restrict_restrict`: restricting first to `F₁` and then to `F₀` agrees with
  restricting directly to `F₀`.
* `TauCeti.Place.ramificationIdx_restrict_mul`: ramification indices multiply in a tower.
* `TauCeti.Place.relativeDegree_restrict_mul`: relative residue degrees multiply in a tower.
* `TauCeti.Place.isSeparable_residueField_restrict_top` and
  `TauCeti.Place.isSeparable_residueField_restrict_bot`: a separable residue extension stays
  separable on each step of the tower.

## Mathematical context

Multiplicativity in towers for extensions of places is Stichtenoth, Proposition 3.1.6. The
restriction identity also supplies the functoriality needed to define induced places and to
construct dual isogenies.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6.
-/

public section

namespace TauCeti

namespace Place

universe u₀ u₁ u₂ v₀ v₁ v₂

variable {k₀ : Type u₀} {k₁ : Type u₁} {k₂ : Type u₂}
variable {F₀ : Type v₀} {F₁ : Type v₁} {F₂ : Type v₂}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
variable [Algebra.IsIntegral F₀ F₁] [Algebra.IsIntegral F₁ F₂]

/-- **Restriction of places is functorial in a tower**: restricting a place of `F₂ / k₂`
first to `F₁ / k₁` and then to `F₀ / k₀` gives its direct restriction to `F₀ / k₀`.

This is the normalized-place form of transitivity of valuation restriction. -/
@[simp]
theorem restrict_restrict (P : Place k₂ F₂) :
    (P.restrict k₁ F₁).restrict k₀ F₀ =
      @restrict k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P
        (Algebra.IsIntegral.trans F₁) := by
  let _ : Algebra.IsIntegral F₀ F₂ := Algebra.IsIntegral.trans F₁
  rw [restrict_eq_iff_integers_le]
  intro x hx
  rw [mem_integers_restrict_iff]
  rw [← IsScalarTower.algebraMap_apply F₀ F₁ F₂]
  exact (mem_integers_restrict_iff k₀ F₀ P x).mp hx

omit [Algebra.IsIntegral F₀ F₁] in
/-- **Ramification indices are multiplicative in towers** (Stichtenoth, Proposition 3.1.6):
`e(P₂ / F₀) = e(P₂ / F₁) e(P₂|F₁ / F₀)`. Only `F₂ / F₁` needs to be algebraic;
the restrictions to `F₀` may be trivial, in which case both corresponding indices vanish. -/
theorem ramificationIdx_restrict_mul (P : Place k₂ F₂) :
    P.ramificationIdx F₀ =
      P.ramificationIdx F₁ * (P.restrict k₁ F₁).ramificationIdx F₀ := by
  rw [ramificationIdx_def, ramificationIdx_def, ramificationIdx_def]
  apply Valuation.ordIndex_eq_mul_of_forall_ord_eq _ _
    (e := Valuation.ordIndex (P.valuation.comap (algebraMap F₁ F₂)))
  intro x
  have hP (y : F₂) : Valuation.ord P.valuation y = P.ord y := by
    rw [Valuation.ord_def, P.ord_def]
  have hP₁ (y : F₁) : Valuation.ord (P.restrict k₁ F₁).valuation y =
      (P.restrict k₁ F₁).ord y := by
    rw [Valuation.ord_def, (P.restrict k₁ F₁).ord_def]
  rw [Valuation.ord_comap, Valuation.ord_comap,
    IsScalarTower.algebraMap_apply F₀ F₁ F₂, hP, hP₁, ord_algebraMap_restrict k₁ F₁ P,
    ramificationIdx_def]

/-- Read through the identification `(P ∩ F₁) ∩ F₀ = P ∩ F₀` of `TauCeti.Place.restrict_restrict`,
the residue-field map of the twice-restricted place `(P ∩ F₁) ∩ F₀` into `F₂_P` is the
residue-field map of `P ∩ F₀`.  The algebra structure of `𝒪_P` over `𝒪_{(P ∩ F₁) ∩ F₀}` is
arbitrary here, as long as it factors through `𝒪_{P ∩ F₁}`. -/
private theorem algebraMap_comp_cast_restrict_restrict (P : Place k₂ F₂)
    [Algebra ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers]
    [IsLocalHom (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers)]
    [IsScalarTower ((P.restrict k₁ F₁).restrict k₀ F₀).integers (P.restrict k₁ F₁).integers
      P.integers] :
    letI : Algebra.IsIntegral F₀ F₂ := Algebra.IsIntegral.trans F₁
    (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField P.ResidueField).comp
        (RingEquiv.cast (R := fun Q : Place k₀ F₀ ↦ Q.ResidueField)
          (restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P).symm : _ →+* _) =
      algebraMap (P.restrict k₀ F₀).ResidueField P.ResidueField := by
  let _ : Algebra.IsIntegral F₀ F₂ := Algebra.IsIntegral.trans F₁
  let h := restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  have cast_residue (Q : Place k₀ F₀) (hQ : Q = P.restrict k₀ F₀)
      (x : (P.restrict k₀ F₀).integers) (y : Q.integers) (hy : (y : F₀) = x) :
      RingEquiv.cast (R := fun R : Place k₀ F₀ ↦ R.ResidueField) hQ.symm
          (IsLocalRing.residue (P.restrict k₀ F₀).integers x) =
        IsLocalRing.residue Q.integers y := by
    subst Q
    have hxy : y = x := Subtype.ext hy
    subst y
    rfl
  let y : ((P.restrict k₁ F₁).restrict k₀ F₀).integers := ⟨x, by rw [h]; exact x.2⟩
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [cast_residue _ h x y rfl, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue, IsScalarTower.algebraMap_apply _
      (P.restrict k₁ F₁).integers P.integers]
  refine congrArg (IsLocalRing.residue P.integers) (Subtype.ext ?_)
  simp only [coe_algebraMap_integers, IsScalarTower.algebraMap_apply F₀ F₁ F₂]
  -- `y` and `x` have the same representative in `F₀`.
  rfl

/-- **Relative residue degrees are multiplicative in towers** (Stichtenoth, Proposition 3.1.6):
`f(P₂ / P₀) = f(P₂ / P₁) f(P₁ / P₀)` for the restrictions `P₁` and `P₀` of `P₂`. -/
theorem relativeDegree_restrict_mul (P : Place k₂ F₂) :
    @relativeDegree k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P
        (Algebra.IsIntegral.trans F₁) =
      P.relativeDegree k₁ F₁ * (P.restrict k₁ F₁).relativeDegree k₀ F₀ := by
  let _ : Algebra.IsIntegral F₀ F₂ := Algebra.IsIntegral.trans F₁
  rw [relativeDegree_def, relativeDegree_def, relativeDegree_def]
  let _ : Algebra ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers :=
    ((algebraMap (P.restrict k₁ F₁).integers P.integers).comp
      (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).integers
        (P.restrict k₁ F₁).integers)).toAlgebra
  let _ : IsLocalHom
      (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers) :=
    RingHom.isLocalHom_comp _ _
  let _ : IsScalarTower ((P.restrict k₁ F₁).restrict k₀ F₀).integers
      (P.restrict k₁ F₁).integers P.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfinrank : Module.finrank (P.restrict k₀ F₀).ResidueField P.ResidueField =
      Module.finrank ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField P.ResidueField := by
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.cast (R := fun Q : Place k₀ F₀ ↦ Q.ResidueField)
        (restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P).symm)
      (RingEquiv.refl P.ResidueField) ?_
    exact (algebraMap_comp_cast_restrict_restrict P).trans (RingHom.id_comp _).symm
  rw [hfinrank]
  simpa only [mul_comm] using
    (Module.finrank_mul_finrank
      ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField
      (P.restrict k₁ F₁).ResidueField P.ResidueField).symm

/-- Separability of the residue extension of `P` over `F₀` passes to both steps of the tower of
residue fields through `P ∩ F₁`, the bottom step read at the twice-restricted place
`(P ∩ F₁) ∩ F₀`. -/
private theorem isSeparable_residueField_restrict_and (P : Place k₂ F₂)
    [Algebra.IsSeparable
      (@restrict k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P (Algebra.IsIntegral.trans F₁)).ResidueField
      P.ResidueField] :
    Algebra.IsSeparable (P.restrict k₁ F₁).ResidueField P.ResidueField ∧
      Algebra.IsSeparable ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField
        (P.restrict k₁ F₁).ResidueField := by
  let _ : Algebra ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers :=
    ((algebraMap (P.restrict k₁ F₁).integers P.integers).comp
      (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).integers
        (P.restrict k₁ F₁).integers)).toAlgebra
  let _ : IsLocalHom
      (algebraMap ((P.restrict k₁ F₁).restrict k₀ F₀).integers P.integers) :=
    RingHom.isLocalHom_comp _ _
  let _ : IsScalarTower ((P.restrict k₁ F₁).restrict k₀ F₀).integers
      (P.restrict k₁ F₁).integers P.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsSeparable ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField P.ResidueField := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (RingEquiv.cast (R := fun Q : Place k₀ F₀ ↦ Q.ResidueField)
        (restrict_restrict (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P).symm)
      (RingEquiv.refl P.ResidueField) ?_
    exact (algebraMap_comp_cast_restrict_restrict P).trans (RingHom.id_comp _).symm
  exact ⟨Algebra.isSeparable_tower_top_of_isSeparable
      ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField _ _,
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField⟩

variable (k₀ F₀) in
/-- **Separability of residue extensions passes to the top of a tower**: if the residue extension
of `P` over `F₀` is separable, so is its residue extension over `F₁`. -/
theorem isSeparable_residueField_restrict_top (P : Place k₂ F₂)
    [Algebra.IsSeparable
      (@restrict k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P (Algebra.IsIntegral.trans F₁)).ResidueField
      P.ResidueField] :
    Algebra.IsSeparable (P.restrict k₁ F₁).ResidueField P.ResidueField :=
  (isSeparable_residueField_restrict_and (k₀ := k₀) (F₀ := F₀) (k₁ := k₁) (F₁ := F₁) P).1

/-- **Separability of residue extensions passes to the bottom of a tower**: if the residue
extension of `P` over `F₀` is separable, so is the residue extension of `P ∩ F₁` over `F₀`. -/
theorem isSeparable_residueField_restrict_bot (P : Place k₂ F₂)
    [Algebra.IsSeparable
      (@restrict k₀ k₂ F₀ F₂ _ _ _ _ _ _ _ _ _ _ _ P (Algebra.IsIntegral.trans F₁)).ResidueField
      P.ResidueField] :
    Algebra.IsSeparable ((P.restrict k₁ F₁).restrict k₀ F₀).ResidueField
      (P.restrict k₁ F₁).ResidueField :=
  (isSeparable_residueField_restrict_and P).2

end Place

end TauCeti

end
