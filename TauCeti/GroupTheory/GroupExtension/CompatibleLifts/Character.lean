/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Basic
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# Characters in the kernel of compatible lifts

A character of the quotient of a central extension acts on the middle group by multiplying
each element by its character value in the included kernel. These twists account for every
compatible lift lying over the identity, so the compatible lifts form an extension
`1 → (G →* N) → S.compatibleLifts ρ → compatibleLiftsLiftableSubgroup S ρ → 1` of the liftable
subgroup by the characters of the quotient. Conjugation by a lift over `a` acts on characters by
`χ ↦ χ ∘ (ρ a)⁻¹`.

## Main definitions

* `GroupExtension.compatibleLiftsCharacterTwist`: a character of the quotient as a compatible
  lift over the identity.
* `GroupExtension.compatibleLiftsKernelCharacter`: the character of a lift over the identity,
  recovered from its displacement in the included kernel; it is multiplicative
  (`compatibleLiftsKernelCharacter_mul`, `compatibleLiftsKernelCharacter_one`).
* `GroupExtension.compatibleLiftsKernelEquiv`: the kernel of the projection is the group of
  characters of the quotient.
* `GroupExtension.compatibleLiftsExtension`: the extension of the liftable subgroup by `G →* N`.
* `GroupExtension.compatibleLiftsExtensionOfSurjective`: the same extension over all of `A` when
  every acting-group element admits a lift.

## Main results

* `GroupExtension.range_compatibleLiftsCharacterTwist`: the character twists are exactly the
  lifts over the identity.
* `GroupExtension.conj_compatibleLiftsCharacterTwist`: conjugation by a lift pulls a character
  back along the inverse quotient action; `compatibleLiftsExtension_conjAct` and
  `compatibleLiftsExtensionOfSurjective_conjAct` state this as the kernel action of the two
  extensions.
* `GroupExtension.existsUnique_eq_mul_compatibleLiftsCharacterTwist` and
  `GroupExtension.existsUnique_compatibleLiftsToMulAut_eq_inl_mul`: two lifts of the same
  acting-group element differ by a unique character twist.
-/

public section

namespace GroupExtension

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : S.inl.range ≤ Subgroup.center E)

/-- Characters define compatible lifts with acting-group coordinate equal to one. -/
def compatibleLiftsCharacterTwist : (G →* N) →* S.compatibleLifts ρ where
  toFun χ := ⟨(characterTwist S hcentral χ, 1), by
    rw [mem_compatibleLifts]
    constructor
    · exact characterTwist_inl S hcentral χ
    · intro e
      simp⟩
  map_one' := compatibleLifts_ext S ρ (by simp) (by simp)
  map_mul' χ ψ := compatibleLifts_ext S ρ (by simp) (by simp)

@[simp]
theorem compatibleLiftsToMulAut_compatibleLiftsCharacterTwist (χ : G →* N) :
    compatibleLiftsToMulAut S ρ (compatibleLiftsCharacterTwist S ρ hcentral χ) =
      characterTwist S hcentral χ :=
  compatibleLiftsToMulAut_mk S ρ _ _ _

@[simp]
theorem compatibleLiftsProjection_compatibleLiftsCharacterTwist (χ : G →* N) :
    compatibleLiftsProjection S ρ (compatibleLiftsCharacterTwist S ρ hcentral χ) = 1 :=
  compatibleLiftsProjection_mk S ρ _ _ _

/-- The displacement of a lift over the identity, expressed in the included kernel. -/
private noncomputable def kernelDeviation (x : (compatibleLiftsProjection S ρ).ker) (e : E) : N :=
  (MonoidHom.ofInjective S.inl_injective).symm
    ⟨compatibleLiftsToMulAut S ρ x.val e * e⁻¹, by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, rightHom_compatibleLiftsToMulAut,
        MonoidHom.mem_ker.mp x.property, map_one, MulAut.one_apply, mul_inv_cancel]⟩

private theorem inl_kernelDeviation (x : (compatibleLiftsProjection S ρ).ker) (e : E) :
    S.inl (kernelDeviation S ρ x e) = compatibleLiftsToMulAut S ρ x.val e * e⁻¹ :=
  MonoidHom.apply_ofInjective_symm S.inl_injective _

/-- The displacement is multiplicative because the included kernel is central. -/
private noncomputable def kernelDeviationHom
    (x : (compatibleLiftsProjection S ρ).ker) : E →* N where
  toFun := kernelDeviation S ρ x
  map_one' := by
    apply S.inl_injective
    simp [inl_kernelDeviation]
  map_mul' e f := by
    apply S.inl_injective
    rw [map_mul, inl_kernelDeviation, inl_kernelDeviation, inl_kernelDeviation, map_mul,
      mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp (hcentral ⟨kernelDeviation S ρ x f, rfl⟩) e⁻¹
    rw [inl_kernelDeviation] at hc
    calc
      compatibleLiftsToMulAut S ρ x.val e * compatibleLiftsToMulAut S ρ x.val f * (f⁻¹ * e⁻¹) =
          compatibleLiftsToMulAut S ρ x.val e *
            ((compatibleLiftsToMulAut S ρ x.val f * f⁻¹) * e⁻¹) := by
        simp only [mul_assoc]
      _ =
        compatibleLiftsToMulAut S ρ x.val e *
          (e⁻¹ * (compatibleLiftsToMulAut S ρ x.val f * f⁻¹)) := by
        rw [hc]
      _ =
        (compatibleLiftsToMulAut S ρ x.val e * e⁻¹) * (compatibleLiftsToMulAut S ρ x.val f * f⁻¹) :=
        (mul_assoc _ _ _).symm

@[simp]
private theorem kernelDeviationHom_apply (x : (compatibleLiftsProjection S ρ).ker) (e : E) :
    kernelDeviationHom S ρ hcentral x e = kernelDeviation S ρ x e :=
  (rfl)

private theorem ker_rightHom_le_ker_kernelDeviationHom (x : (compatibleLiftsProjection S ρ).ker) :
    S.rightHom.ker ≤ (kernelDeviationHom S ρ hcentral x).ker := by
  intro e he
  rw [← S.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, rfl⟩ := he
  rw [MonoidHom.mem_ker, kernelDeviationHom_apply]
  apply S.inl_injective
  rw [inl_kernelDeviation, compatibleLiftsToMulAut_inl, mul_inv_cancel, map_one]

/-- Recover the quotient character of a lift over the identity by descending its displacement. -/
noncomputable def compatibleLiftsKernelCharacter
    (x : (compatibleLiftsProjection S ρ).ker) : G →* N :=
  S.rightHom.liftOfSurjective S.rightHom_surjective
    ⟨kernelDeviationHom S ρ hcentral x, ker_rightHom_le_ker_kernelDeviationHom S ρ hcentral x⟩

private theorem compatibleLiftsKernelCharacter_rightHom
    (x : (compatibleLiftsProjection S ρ).ker) (e : E) :
    compatibleLiftsKernelCharacter S ρ hcentral x (S.rightHom e) = kernelDeviation S ρ x e := by
  simp [compatibleLiftsKernelCharacter]

@[simp]
theorem inl_compatibleLiftsKernelCharacter_rightHom
    (x : (compatibleLiftsProjection S ρ).ker) (e : E) :
    S.inl (compatibleLiftsKernelCharacter S ρ hcentral x (S.rightHom e)) =
      compatibleLiftsToMulAut S ρ x.val e * e⁻¹ := by
  rw [compatibleLiftsKernelCharacter_rightHom, inl_kernelDeviation]

/-- The recovered character can be evaluated on any set-theoretic section. -/
theorem inl_compatibleLiftsKernelCharacter_section
    (x : (compatibleLiftsProjection S ρ).ker) (σ : S.Section) (g : G) :
    S.inl (compatibleLiftsKernelCharacter S ρ hcentral x g) =
      compatibleLiftsToMulAut S ρ x.val (σ g) * (σ g)⁻¹ := by
  simpa only [Section.rightHom_section] using
    inl_compatibleLiftsKernelCharacter_rightHom S ρ hcentral x (σ g)

/-- Character twists, with their codomain restricted to the kernel of the projection. -/
def compatibleLiftsCharacterTwistToKernel : (G →* N) →* (compatibleLiftsProjection S ρ).ker :=
  (compatibleLiftsCharacterTwist S ρ hcentral).codRestrict _
    (fun χ => compatibleLiftsProjection_compatibleLiftsCharacterTwist S ρ hcentral χ)

@[simp]
theorem coe_compatibleLiftsCharacterTwistToKernel (χ : G →* N) :
    (compatibleLiftsCharacterTwistToKernel S ρ hcentral χ : S.compatibleLifts ρ) =
      compatibleLiftsCharacterTwist S ρ hcentral χ :=
  (rfl)

@[simp]
theorem compatibleLiftsKernelCharacter_compatibleLiftsCharacterTwistToKernel (χ : G →* N) :
    compatibleLiftsKernelCharacter S ρ hcentral
      (compatibleLiftsCharacterTwistToKernel S ρ hcentral χ) = χ := by
  ext g
  obtain ⟨e, rfl⟩ := S.rightHom_surjective g
  apply S.inl_injective
  rw [inl_compatibleLiftsKernelCharacter_rightHom, coe_compatibleLiftsCharacterTwistToKernel,
    compatibleLiftsToMulAut_compatibleLiftsCharacterTwist, characterTwist_apply,
    mul_inv_cancel_right]

theorem compatibleLiftsCharacterTwist_injective : Function.Injective
    (compatibleLiftsCharacterTwist S ρ hcentral) := by
  intro χ ψ h
  apply Function.LeftInverse.injective
    (compatibleLiftsKernelCharacter_compatibleLiftsCharacterTwistToKernel S ρ hcentral)
  apply Subtype.ext
  rw [coe_compatibleLiftsCharacterTwistToKernel, coe_compatibleLiftsCharacterTwistToKernel]
  exact h

@[simp]
theorem compatibleLiftsCharacterTwist_compatibleLiftsKernelCharacter
    (x : (compatibleLiftsProjection S ρ).ker) :
    compatibleLiftsCharacterTwist S ρ hcentral (compatibleLiftsKernelCharacter S ρ hcentral x) =
      x.val := by
  apply compatibleLifts_ext S ρ
  · apply MulEquiv.ext
    intro e
    rw [compatibleLiftsToMulAut_compatibleLiftsCharacterTwist, characterTwist_apply,
      inl_compatibleLiftsKernelCharacter_rightHom, inv_mul_cancel_right]
  · rw [compatibleLiftsProjection_compatibleLiftsCharacterTwist]
    exact (MonoidHom.mem_ker.mp x.property).symm

/-- The character twists are exactly the compatible lifts over the identity. -/
theorem range_compatibleLiftsCharacterTwist :
    (compatibleLiftsCharacterTwist S ρ hcentral).range = (compatibleLiftsProjection S ρ).ker := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨χ, rfl⟩
    exact compatibleLiftsProjection_compatibleLiftsCharacterTwist S ρ hcentral χ
  · intro hx
    exact ⟨compatibleLiftsKernelCharacter S ρ hcentral ⟨x, hx⟩,
      compatibleLiftsCharacterTwist_compatibleLiftsKernelCharacter S ρ hcentral ⟨x, hx⟩⟩

/-- The full kernel of compatible lifts is the group of characters of the quotient. The inverse
is the descended displacement `compatibleLiftsKernelCharacter`, with no choice of a normalized
section. -/
noncomputable def compatibleLiftsKernelEquiv : (G →* N) ≃* (compatibleLiftsProjection S ρ).ker where
  toFun := compatibleLiftsCharacterTwistToKernel S ρ hcentral
  invFun := compatibleLiftsKernelCharacter S ρ hcentral
  left_inv := compatibleLiftsKernelCharacter_compatibleLiftsCharacterTwistToKernel S ρ hcentral
  right_inv x := Subtype.ext <| by
    rw [coe_compatibleLiftsCharacterTwistToKernel,
      compatibleLiftsCharacterTwist_compatibleLiftsKernelCharacter]
  map_mul' := (compatibleLiftsCharacterTwistToKernel S ρ hcentral).map_mul

@[simp]
theorem compatibleLiftsKernelEquiv_apply (χ : G →* N) :
    compatibleLiftsKernelEquiv S ρ hcentral χ =
      compatibleLiftsCharacterTwistToKernel S ρ hcentral χ :=
  (rfl)

@[simp]
theorem compatibleLiftsKernelEquiv_symm_apply (x : (compatibleLiftsProjection S ρ).ker) :
    (compatibleLiftsKernelEquiv S ρ hcentral).symm x =
      compatibleLiftsKernelCharacter S ρ hcentral x :=
  (rfl)

/-- The kernel character of a product of lifts over the identity is the product of their kernel
characters. -/
@[simp]
theorem compatibleLiftsKernelCharacter_mul (x y : (compatibleLiftsProjection S ρ).ker) :
    compatibleLiftsKernelCharacter S ρ hcentral (x * y) =
      compatibleLiftsKernelCharacter S ρ hcentral x *
        compatibleLiftsKernelCharacter S ρ hcentral y :=
  (compatibleLiftsKernelEquiv S ρ hcentral).symm.map_mul x y

/-- The kernel character of the identity lift is the trivial character. -/
@[simp]
theorem compatibleLiftsKernelCharacter_one :
    compatibleLiftsKernelCharacter S ρ hcentral 1 = 1 :=
  (compatibleLiftsKernelEquiv S ρ hcentral).symm.map_one

/-- The group extension of the liftable subgroup by the characters of the quotient: the
compatible lifts project onto precisely those acting-group elements that have lifts. -/
noncomputable def compatibleLiftsExtension :
    GroupExtension (G →* N) (S.compatibleLifts ρ) (compatibleLiftsLiftableSubgroup S ρ) :=
  GroupExtension.ofMulEquivKer (compatibleLiftsProjection S ρ).rangeRestrict_surjective
    ((compatibleLiftsKernelEquiv S ρ hcentral).trans
      (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict (compatibleLiftsProjection S ρ)).symm))

@[simp]
theorem compatibleLiftsExtension_rightHom :
    (compatibleLiftsExtension S ρ hcentral).rightHom = compatibleLiftsToLiftable S ρ := by
  rw [compatibleLiftsExtension, GroupExtension.ofMulEquivKer_rightHom]

@[simp]
theorem compatibleLiftsExtension_inl :
    (compatibleLiftsExtension S ρ hcentral).inl = compatibleLiftsCharacterTwist S ρ hcentral := by
  rw [compatibleLiftsExtension, GroupExtension.ofMulEquivKer_inl]
  refine MonoidHom.ext fun χ => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, compatibleLiftsKernelEquiv_apply,
    coe_compatibleLiftsCharacterTwistToKernel]

/-- When every acting-group element admits a lift, the same kernel describes an extension
over the whole acting group. -/
noncomputable def compatibleLiftsExtensionOfSurjective
    (h : Function.Surjective (compatibleLiftsProjection S ρ)) :
    GroupExtension (G →* N) (S.compatibleLifts ρ) A :=
  GroupExtension.ofMulEquivKer h (compatibleLiftsKernelEquiv S ρ hcentral)

@[simp]
theorem compatibleLiftsExtensionOfSurjective_rightHom
    (h : Function.Surjective (compatibleLiftsProjection S ρ)) :
    (compatibleLiftsExtensionOfSurjective S ρ hcentral h).rightHom =
      compatibleLiftsProjection S ρ := by
  rw [compatibleLiftsExtensionOfSurjective, GroupExtension.ofMulEquivKer_rightHom]

@[simp]
theorem compatibleLiftsExtensionOfSurjective_inl
    (h : Function.Surjective (compatibleLiftsProjection S ρ)) :
    (compatibleLiftsExtensionOfSurjective S ρ hcentral h).inl =
      compatibleLiftsCharacterTwist S ρ hcentral := by
  rw [compatibleLiftsExtensionOfSurjective, GroupExtension.ofMulEquivKer_inl]
  refine MonoidHom.ext fun χ => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    compatibleLiftsKernelEquiv_apply, coe_compatibleLiftsCharacterTwistToKernel]

/-- The kernel action of compatible lifts is the inverse-pullback action on characters. -/
theorem conj_compatibleLiftsCharacterTwist (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * compatibleLiftsCharacterTwist S ρ hcentral χ * x⁻¹ =
      compatibleLiftsCharacterTwist S ρ hcentral
        (χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom) := by
  apply compatibleLifts_ext S ρ
  · simpa only [map_mul, map_inv, compatibleLiftsToMulAut_compatibleLiftsCharacterTwist] using
      compatibleLiftsToMulAut_conj_characterTwist S ρ hcentral x χ
  · simp only [map_mul, map_inv, compatibleLiftsProjection_compatibleLiftsCharacterTwist, mul_one,
      mul_inv_cancel]

/-- The kernel action of the compatible-lift extension pulls a character back along the inverse
quotient action. -/
theorem compatibleLiftsExtension_conjAct (x : S.compatibleLifts ρ) (χ : G →* N) :
    (compatibleLiftsExtension S ρ hcentral).conjAct x χ =
      χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom := by
  apply (compatibleLiftsExtension S ρ hcentral).inl_injective
  rw [inl_conjAct_comm, compatibleLiftsExtension_inl, conj_compatibleLiftsCharacterTwist]

/-- The kernel action of the extension over the whole acting group, as for
`compatibleLiftsExtension_conjAct`. -/
theorem compatibleLiftsExtensionOfSurjective_conjAct
    (h : Function.Surjective (compatibleLiftsProjection S ρ)) (x : S.compatibleLifts ρ)
    (χ : G →* N) :
    (compatibleLiftsExtensionOfSurjective S ρ hcentral h).conjAct x χ =
      χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom := by
  apply (compatibleLiftsExtensionOfSurjective S ρ hcentral h).inl_injective
  rw [inl_conjAct_comm, compatibleLiftsExtensionOfSurjective_inl,
    conj_compatibleLiftsCharacterTwist]

/-- Two lifts of the same acting-group element differ by a unique source character twist. -/
theorem existsUnique_eq_mul_compatibleLiftsCharacterTwist (x y : S.compatibleLifts ρ)
    (h : compatibleLiftsProjection S ρ x = compatibleLiftsProjection S ρ y) :
    ∃! χ : G →* N, y = x * compatibleLiftsCharacterTwist S ρ hcentral χ := by
  let z : (compatibleLiftsProjection S ρ).ker := ⟨x⁻¹ * y, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]⟩
  have hz := compatibleLiftsCharacterTwist_compatibleLiftsKernelCharacter S ρ hcentral z
  refine ⟨compatibleLiftsKernelCharacter S ρ hcentral z, ?_, ?_⟩
  · dsimp only
    rw [hz]
    exact (mul_inv_cancel_left x y).symm
  · intro ψ hψ
    apply compatibleLiftsCharacterTwist_injective S ρ hcentral
    apply mul_left_cancel (a := x)
    rw [← hψ, hz]
    exact (mul_inv_cancel_left x y).symm

/-- A source character twist multiplies the image of each element by its original character
value, since a compatible lift fixes the included kernel. -/
theorem compatibleLiftsToMulAut_mul_compatibleLiftsCharacterTwist_apply (x : S.compatibleLifts ρ)
    (χ : G →* N) (e : E) :
    compatibleLiftsToMulAut S ρ (x * compatibleLiftsCharacterTwist S ρ hcentral χ) e =
      S.inl (χ (S.rightHom e)) * compatibleLiftsToMulAut S ρ x e := by
  rw [map_mul, MulAut.mul_apply, compatibleLiftsToMulAut_compatibleLiftsCharacterTwist,
    characterTwist_apply, map_mul, compatibleLiftsToMulAut_inl]

include hcentral in
/-- Two lifts of the same acting-group element differ pointwise by a unique quotient character. -/
theorem existsUnique_compatibleLiftsToMulAut_eq_inl_mul (x y : S.compatibleLifts ρ)
    (h : compatibleLiftsProjection S ρ x = compatibleLiftsProjection S ρ y) :
    ∃! χ : G →* N, ∀ e, compatibleLiftsToMulAut S ρ y e =
      S.inl (χ (S.rightHom e)) * compatibleLiftsToMulAut S ρ x e := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_eq_mul_compatibleLiftsCharacterTwist S ρ hcentral x y h
  refine ⟨χ, ?_, ?_⟩
  · intro e
    rw [hχ, compatibleLiftsToMulAut_mul_compatibleLiftsCharacterTwist_apply]
  · intro ψ hψ
    apply huniq ψ
    apply compatibleLifts_ext S ρ
    · apply MulEquiv.ext
      intro e
      rw [compatibleLiftsToMulAut_mul_compatibleLiftsCharacterTwist_apply]
      exact hψ e
    · rw [map_mul, compatibleLiftsProjection_compatibleLiftsCharacterTwist, mul_one]
      exact h.symm

/-- Moving a source twist past a lift replaces its character by inverse pullback. -/
theorem mul_compatibleLiftsCharacterTwist_eq_compatibleLiftsCharacterTwist_mul
    (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * compatibleLiftsCharacterTwist S ρ hcentral χ =
      compatibleLiftsCharacterTwist S ρ hcentral
        (χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom) * x := by
  rw [← conj_compatibleLiftsCharacterTwist]
  simp only [inv_mul_cancel_right]

end GroupExtension
