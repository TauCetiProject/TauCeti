/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# The automorphism group of the function field of an elliptic curve

Let `W` be an elliptic curve over a field `F`, with function field `F(W)`. Two kinds of
`F`-automorphisms of `F(W)` are already at hand: the pullbacks `τ_P^*` of the translations by the
points of `W` (`WeierstrassCurve.Affine.translationHom`, a faithful action of the point group), and
the automorphisms of the curve fixing the point at infinity, which are the changes of variables
`C = (u, r, s, t)` with `C • W = W` (the finite group `W.autGroup`), acting on functions by the
substitution `x ↦ u²x + r`, `y ↦ u³y + u²sx + t`. This file proves that together they are all of
`Aut(F(W) / F)`, as a semidirect product: the translations form a normal subgroup `T`, the
automorphisms of the curve are the stabilizer of the place at infinity and a complement to `T`, so

`Aut(F(W) / F) ⧸ T ≃* Aut(E, O)`,

a finite group. Since the point group is the degree-zero divisor class group of `F(W)`
(`WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass`), the translations are a copy of
`Cl⁰(F(W))` of finite index in the automorphism group.

The proof has three steps.
* An automorphism fixing the place at infinity restricts to a coordinate pullback that maps
  infinity to infinity (`TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace`),
  hence to an isogeny of degree one from `W` to itself, which is a change of variables
  (`TauCeti.Isogeny.exists_variableChangeIsogeny_eq_of_degree_eq_one`).
* An arbitrary automorphism moves the place at infinity to a degree-one place, the place of a point
  `R`, and the translation by `-R` moves it back; a translation fixing the place at infinity is
  the identity. So the two subgroups are complementary.
* A change of variables carries translations to translations, `τ_P^* ∘ ψ = ψ ∘ τ_{P'}^*`
  (`WeierstrassCurve.Affine.exists_translation_comp_fieldPullback_variableChangeIsogeny`). With
  commutativity of the translations this gives normality.

## Main definitions

* `WeierstrassCurve.Affine.autGroupToAlgEquiv`: the action of `W.autGroup` on `F(W)`.
* `WeierstrassCurve.Affine.quotientRangeTranslationHomMulEquiv`: `Aut(F(W) / F) ⧸ T ≃* Aut(E, O)`.

## Main results

* `WeierstrassCurve.Affine.stabilizer_infinity_eq_range_autGroupToAlgEquiv`: the automorphisms
  fixing the place at infinity are the changes of variables fixing `W`.
* `WeierstrassCurve.Affine.isComplement'_stabilizer_infinity_range_translationHom`: every
  automorphism is uniquely a change of variables followed by a translation.
* `WeierstrassCurve.Affine.normal_range_translationHom`: the translations form a normal subgroup.
* `WeierstrassCurve.Affine.index_range_translationHom` and
  `WeierstrassCurve.Affine.finiteIndex_range_translationHom`: its index is `#Aut(E, O)`, which is
  finite.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 6.14.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3 and III.10.
-/

public section

open TauCeti TauCeti.Isogeny WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

section Automorphism

open MulAction

variable (W : Affine F)

/-- The pullback of a change of variables fixing `W` is an automorphism of the function field:
the isogeny has degree one. -/
private theorem bijective_fieldPullback_variableChangeIsogeny {C : VariableChange F}
    (h : C • W = W) : Function.Bijective (variableChangeIsogeny C h).fieldPullback :=
  ⟨RingHom.injective _, (degree_eq_one_iff _).1 (degree_variableChangeIsogeny _ _)⟩

/-- **The automorphisms of the curve act on the function field.** A change of variables
`C = (u, r, s, t)` fixing `W` is an automorphism of the curve fixing the point at infinity; it acts
on the function field by substitution, sending a function `f(x, y)` to
`f(u²x + r, u³y + u²sx + t)`. This is the function-field pullback of the isogeny of `C⁻¹`. -/
noncomputable def autGroupToAlgEquiv : W.autGroup →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun C := AlgEquiv.ofBijective
    (variableChangeIsogeny (C⁻¹ : W.autGroup).1 (mem_stabilizer_iff.mp (C⁻¹).2)).fieldPullback
    (bijective_fieldPullback_variableChangeIsogeny W _)
  map_one' := AlgEquiv.ext fun z ↦ by simp
  map_mul' C D := AlgEquiv.ext fun z ↦ by
    rw [AlgEquiv.mul_apply, AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply,
      AlgEquiv.ofBijective_apply, ← AlgHom.comp_apply, ← comp_fieldPullback,
      variableChangeIsogeny_comp]
    simp only [mul_inv_rev, Subgroup.coe_mul]

/-- The automorphism of a change of variables `C` fixing `W` is the function-field pullback of the
isogeny of `C⁻¹`. -/
theorem autGroupToAlgEquiv_apply (C : W.autGroup) (z : W.FunctionField) :
    autGroupToAlgEquiv W C z =
      (variableChangeIsogeny (C⁻¹ : W.autGroup).1
        (mem_stabilizer_iff.mp (C⁻¹).2)).fieldPullback z :=
  (rfl)

/-- **A change of variables substitutes into `x`**: the automorphism of `C = (u, r, s, t)` sends
the coordinate function `x` to `u²x + r`. -/
@[simp]
theorem autGroupToAlgEquiv_apply_genericX (C : W.autGroup) :
    autGroupToAlgEquiv W C (genericX W) =
      algebraMap F W.FunctionField (C.1.u : F) ^ 2 * genericX W +
        algebraMap F W.FunctionField C.1.r := by
  simp [autGroupToAlgEquiv_apply, genericX_def, CoordinateRing.mk, AdjoinRoot.mk_C,
    ← IsScalarTower.algebraMap_apply]

/-- **A change of variables substitutes into `y`**: the automorphism of `C = (u, r, s, t)` sends
the coordinate function `y` to `u³y + u²sx + t`. -/
@[simp]
theorem autGroupToAlgEquiv_apply_genericY (C : W.autGroup) :
    autGroupToAlgEquiv W C (genericY W) =
      algebraMap F W.FunctionField (C.1.u : F) ^ 3 * genericY W +
        algebraMap F W.FunctionField (C.1.u : F) ^ 2 * algebraMap F W.FunctionField C.1.s *
          genericX W + algebraMap F W.FunctionField C.1.t := by
  simp [autGroupToAlgEquiv_apply, genericX_def, genericY_def, CoordinateRing.mk,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← IsScalarTower.algebraMap_apply]

/-- **Distinct changes of variables give distinct automorphisms of the function field.** -/
theorem autGroupToAlgEquiv_injective : Function.Injective (autGroupToAlgEquiv W) := fun C D h ↦ by
  have hφ : variableChangeIsogeny (C⁻¹ : W.autGroup).1 (mem_stabilizer_iff.mp (C⁻¹).2) =
      variableChangeIsogeny (D⁻¹ : W.autGroup).1 (mem_stabilizer_iff.mp (D⁻¹).2) :=
    Isogeny.ext <| AlgHom.ext fun z ↦ by
      rw [← fieldPullback_algebraMap, ← fieldPullback_algebraMap, ← autGroupToAlgEquiv_apply,
        ← autGroupToAlgEquiv_apply, h]
  exact inv_injective (Subtype.ext ((variableChangeIsogeny_inj _ _ _ _).mp hφ))

/-- The place at infinity is fixed by `σ⁻¹` exactly when its valuation, restricted along `σ`, is
equivalent to itself: the place-level and the valuation-level forms of `σ(O) = O`. -/
private theorem inv_smul_infinity_eq_iff (σ : W.FunctionField ≃ₐ[F] W.FunctionField) :
    σ⁻¹ • Place.infinity W = Place.infinity W ↔
      (W.infinityPlace.comap (σ : W.FunctionField →ₐ[F] W.FunctionField).toRingHom).IsEquiv
        W.infinityPlace := by
  have hval : (σ⁻¹ • Place.infinity W).valuation =
      W.infinityPlace.comap (σ : W.FunctionField →ₐ[F] W.FunctionField).toRingHom :=
    Valuation.ext fun z ↦ by
      rw [Place.valuation_smul, Place.valuation_infinity, AlgEquiv.aut_inv, AlgEquiv.symm_symm,
        Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
  refine ⟨fun h ↦ ?_, fun h ↦ Place.eq_of_isEquiv ?_⟩
  · rw [← hval, h, Place.valuation_infinity]
  · rwa [hval, Place.valuation_infinity]

variable [W.IsElliptic]

/-- **The automorphisms of the function field fixing the place at infinity are the automorphisms
of the elliptic curve**: the stabilizer of the place at infinity is the image of
`autGroupToAlgEquiv`. An automorphism fixing infinity restricts to a degree-one isogeny of `W` to
itself, which is a change of variables. -/
theorem stabilizer_infinity_eq_range_autGroupToAlgEquiv :
    stabilizer (W.FunctionField ≃ₐ[F] W.FunctionField) (Place.infinity W) =
      (autGroupToAlgEquiv W).range := by
  ext σ
  rw [mem_stabilizer_iff, eq_comm, ← inv_smul_eq_iff, inv_smul_infinity_eq_iff,
    ← CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace]
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- `σ` restricts to a degree-one isogeny `φ`, which is the isogeny of a change of variables
    let φ : Isogeny W W := ⟨_, h⟩
    have hφ : φ.fieldPullback = σ := (φ.fieldPullback_unique σ fun _ ↦ rfl).symm
    obtain ⟨C, hC, hCφ⟩ := exists_variableChangeIsogeny_eq_of_degree_eq_one φ
      ((degree_eq_one_iff φ).2 (hφ ▸ σ.surjective))
    refine ⟨(⟨C, mem_stabilizer_iff.mpr hC⟩ : W.autGroup)⁻¹, AlgEquiv.ext fun z ↦ ?_⟩
    rw [autGroupToAlgEquiv_apply]
    simp only [inv_inv]
    rw [hCφ, hφ, AlgEquiv.coe_toAlgHom]
  · rintro ⟨C, rfl⟩
    rw [CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace]
    exact isEquiv_comap_infinityPlace (variableChangeIsogeny _ _)

variable [DecidableEq F]

/-- **The translation by `P` carries the place at infinity to the place of `-P`.** -/
@[simp]
theorem translation_smul_infinity (P : W.Point) :
    translation W (Point.equivBaseChangeSelf W P) • Place.infinity W =
      (pointEquivDegreeOnePlace W (-P)).1 := by
  rw [← coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def,
    translation_smul_pointEquivDegreeOnePlace, zero_sub]

/-- Distinct rational points translate the place at infinity to distinct places. -/
theorem translation_smul_infinity_injective :
    Function.Injective fun P : (W⁄F).toAffine.Point ↦ translation W P • Place.infinity W := by
  intro P Q h
  obtain ⟨P, rfl⟩ := (Point.equivBaseChangeSelf W).surjective P
  obtain ⟨Q, rfl⟩ := (Point.equivBaseChangeSelf W).surjective Q
  simp only [translation_smul_infinity] at h
  exact congrArg (Point.equivBaseChangeSelf W)
    (neg_injective ((pointEquivDegreeOnePlace W).injective (Subtype.ext h)))

/-- Every automorphism of the function field is an automorphism of the elliptic curve followed by
a translation. -/
private theorem exists_mem_stabilizer_mul_translation_eq
    (σ : W.FunctionField ≃ₐ[F] W.FunctionField) :
    ∃ a ∈ stabilizer (W.FunctionField ≃ₐ[F] W.FunctionField) (Place.infinity W),
      ∃ P : W.Point, a * translation W (Point.equivBaseChangeSelf W P) = σ := by
  -- `σ⁻¹` moves the place at infinity to the place of a point `R`, and so does `τ_{-R}`
  obtain ⟨R, hR⟩ := (pointEquivDegreeOnePlace W).surjective
    ⟨σ⁻¹ • Place.infinity W, by rw [Place.degree_smul, Place.degree_infinity]⟩
  have hτ : (translation W (Point.equivBaseChangeSelf W R))⁻¹ • Place.infinity W =
      σ⁻¹ • Place.infinity W := by
    rw [← translation_neg, ← map_neg, translation_smul_infinity, neg_neg, hR]
  refine ⟨σ * (translation W (Point.equivBaseChangeSelf W R))⁻¹, ?_, R, inv_mul_cancel_right _ _⟩
  rw [mem_stabilizer_iff, mul_smul, hτ, smul_inv_smul]

/-- **The automorphisms of the elliptic curve and the translations are complementary** in the
automorphism group of the function field: every automorphism is uniquely an automorphism fixing
the place at infinity followed by a translation. -/
theorem isComplement'_stabilizer_infinity_range_translationHom :
    Subgroup.IsComplement' (stabilizer (W.FunctionField ≃ₐ[F] W.FunctionField) (Place.infinity W))
      (translationHom W).range := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · -- a translation fixing the place at infinity is the translation by `0`
    refine Subgroup.disjoint_def.mpr fun {σ} hσ ⟨P, hP⟩ ↦ ?_
    obtain ⟨Q, hQ⟩ := (Point.equivBaseChangeSelf W).surjective (Multiplicative.toAdd P)
    rw [← hP, translationHom_apply, ← hQ] at hσ ⊢
    rw [mem_stabilizer_iff, translation_smul_infinity, ← coe_pointEquivDegreeOnePlace_zero,
      ← Point.zero_def] at hσ
    rw [neg_eq_zero.mp ((pointEquivDegreeOnePlace W).injective (Subtype.ext hσ)), map_zero,
      translation_zero]
  · refine Set.eq_univ_of_forall fun σ ↦ ?_
    obtain ⟨a, ha, P, h⟩ := exists_mem_stabilizer_mul_translation_eq W σ
    exact Set.mem_mul.mpr
      ⟨a, ha, _, ⟨Multiplicative.ofAdd (Point.equivBaseChangeSelf W P), by simp⟩, h⟩

/-- **The translations have index `#Aut(E, O)`** in the automorphism group of the function field. -/
theorem index_range_translationHom : (translationHom W).range.index = Nat.card W.autGroup := by
  rw [(isComplement'_stabilizer_infinity_range_translationHom W).index_eq_card,
    stabilizer_infinity_eq_range_autGroupToAlgEquiv]
  exact (Nat.card_congr (MonoidHom.ofInjective (autGroupToAlgEquiv_injective W)).toEquiv).symm

/-- **The translations have finite index** in the automorphism group of the function field, the
automorphism group of an elliptic curve being finite. -/
instance finiteIndex_range_translationHom : (translationHom W).range.FiniteIndex :=
  ⟨by rw [index_range_translationHom]; exact Nat.card_pos.ne'⟩

/-- **An automorphism of the elliptic curve conjugates a translation to a translation.** -/
theorem exists_autGroupToAlgEquiv_mul_translation_mul_inv_eq (C : W.autGroup)
    (P : (W⁄F).toAffine.Point) : ∃ P' : (W⁄F).toAffine.Point,
      autGroupToAlgEquiv W C * translation W P * (autGroupToAlgEquiv W C)⁻¹ = translation W P' := by
  obtain ⟨P', hP'⟩ :=
    exists_translation_comp_fieldPullback_variableChangeIsogeny (mem_stabilizer_iff.mp C.2) P
  -- the inverse of the automorphism of `C` is the pullback of the isogeny of `C`
  have hinv (z : W.FunctionField) : (autGroupToAlgEquiv W C)⁻¹ z =
      (variableChangeIsogeny C.1 (mem_stabilizer_iff.mp C.2)).fieldPullback z := by
    rw [← map_inv, autGroupToAlgEquiv_apply]
    simp only [inv_inv]
  have hcomm : translation W P * (autGroupToAlgEquiv W C)⁻¹ =
      (autGroupToAlgEquiv W C)⁻¹ * translation W P' :=
    AlgEquiv.ext fun z ↦ by simpa [hinv] using AlgHom.congr_fun hP' z
  exact ⟨P', by rw [mul_assoc, hcomm, mul_inv_cancel_left]⟩

/-- **The translations form a normal subgroup** of the automorphism group of the function field. -/
instance normal_range_translationHom : (translationHom W).range.Normal where
  conj_mem n hn σ := by
    obtain ⟨a, ha, P, rfl⟩ := exists_mem_stabilizer_mul_translation_eq W σ
    rw [stabilizer_infinity_eq_range_autGroupToAlgEquiv] at ha
    obtain ⟨C, rfl⟩ := ha
    obtain ⟨Q, rfl⟩ := hn
    -- translations commute, so conjugating by `a * τ_P` is conjugating by `a`
    set τ := translationHom W (Multiplicative.ofAdd (Point.equivBaseChangeSelf W P))
    have hτ : translation W (Point.equivBaseChangeSelf W P) = τ := by simp [τ]
    have hc : τ * translationHom W Q * τ⁻¹ = translationHom W Q := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_inv_cancel_comm]
    obtain ⟨P', hP'⟩ := exists_autGroupToAlgEquiv_mul_translation_mul_inv_eq W C
      (Multiplicative.toAdd Q)
    refine ⟨Multiplicative.ofAdd P', ?_⟩
    calc translationHom W (Multiplicative.ofAdd P')
        = autGroupToAlgEquiv W C * (τ * translationHom W Q * τ⁻¹) *
            (autGroupToAlgEquiv W C)⁻¹ := by
          rw [hc, translationHom_apply, translationHom_apply, toAdd_ofAdd, hP']
      _ = autGroupToAlgEquiv W C * τ * translationHom W Q * (autGroupToAlgEquiv W C * τ)⁻¹ := by
          group
      _ = _ := by rw [hτ]

/-- **The automorphism group of the function field modulo the translations is the automorphism
group of the elliptic curve**: `Aut(F(W) / F) ⧸ T ≃* Aut(E, O)`, a finite group. Each class
contains exactly one automorphism fixing the place at infinity, and that automorphism is a change of
variables. -/
noncomputable def quotientRangeTranslationHomMulEquiv :
    (W.FunctionField ≃ₐ[F] W.FunctionField) ⧸ (translationHom W).range ≃* W.autGroup :=
  (isComplement'_stabilizer_infinity_range_translationHom W).QuotientMulEquiv.trans
    ((MulEquiv.subgroupCongr (stabilizer_infinity_eq_range_autGroupToAlgEquiv W)).trans
      (MonoidHom.ofInjective (autGroupToAlgEquiv_injective W)).symm)

/-- The inverse of `quotientRangeTranslationHomMulEquiv` sends a change of variables to the class
of its automorphism of the function field. -/
@[simp]
theorem quotientRangeTranslationHomMulEquiv_symm_apply (C : W.autGroup) :
    (quotientRangeTranslationHomMulEquiv W).symm C = (autGroupToAlgEquiv W C : _ ⧸ _) := by
  have h := isComplement'_stabilizer_infinity_range_translationHom W
  have hS := stabilizer_infinity_eq_range_autGroupToAlgEquiv W
  have hC : (MulEquiv.subgroupCongr hS).symm
      (MonoidHom.ofInjective (autGroupToAlgEquiv_injective W) C) =
        ⟨autGroupToAlgEquiv W C, hS.symm ▸ ⟨C, rfl⟩⟩ :=
    Subtype.ext (by simp [MonoidHom.ofInjective_apply])
  simp only [quotientRangeTranslationHomMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    Subgroup.IsComplement'.QuotientMulEquiv_symm_apply, Equiv.symm_apply_eq, hC]
  -- both the automorphism and its chosen representative fix infinity and have the same class
  exact (Subgroup.isComplement_subgroup_right_iff_bijective.mp h).1
    (h.quotientGroupMk_leftQuotientEquiv _).symm

/-- `quotientRangeTranslationHomMulEquiv` sends the class of the automorphism of a change of
variables back to the change of variables. -/
@[simp]
theorem quotientRangeTranslationHomMulEquiv_mk (C : W.autGroup) :
    quotientRangeTranslationHomMulEquiv W (autGroupToAlgEquiv W C : _ ⧸ _) = C := by
  rw [← quotientRangeTranslationHomMulEquiv_symm_apply, MulEquiv.apply_symm_apply]

end Automorphism

end WeierstrassCurve.Affine
