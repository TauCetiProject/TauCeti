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
compatible lift lying over the identity.
-/

public section

namespace GroupExtension

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : S.inl.range ≤ Subgroup.center E)

/-- Characters define compatible lifts with acting-group coordinate equal to one. -/
def compatibleLiftsCharacter : (G →* N) →* S.compatibleLifts ρ where
  toFun χ := ⟨(twist S hcentral χ, 1), by
    rw [mem_compatibleLifts]
    constructor
    · exact twist_inl S hcentral χ
    · intro e
      simp⟩
  map_one' := by
    apply compatibleLifts_ext S ρ
    · ext e
      simp [compatibleLiftsToMulAut_apply]
    · simp only [compatibleLiftsProjection_apply, OneMemClass.coe_one, Prod.snd_one]
  map_mul' χ ψ := by
    apply compatibleLifts_ext S ρ
    · ext e
      simp [compatibleLiftsToMulAut_apply, mul_assoc]
    · simp [compatibleLiftsProjection_apply]

@[simp]
theorem compatibleLiftsToMulAut_character (χ : G →* N) :
    compatibleLiftsToMulAut S ρ (compatibleLiftsCharacter S ρ hcentral χ) = twist S hcentral χ :=
  compatibleLiftsToMulAut_apply S ρ _

@[simp]
theorem compatibleLiftsProjection_character (χ : G →* N) :
    compatibleLiftsProjection S ρ (compatibleLiftsCharacter S ρ hcentral χ) = 1 :=
  compatibleLiftsProjection_apply S ρ _

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
def compatibleLiftsCharacterToKernel : (G →* N) →* (compatibleLiftsProjection S ρ).ker :=
  (compatibleLiftsCharacter S ρ hcentral).codRestrict _
    (fun χ => compatibleLiftsProjection_character S ρ hcentral χ)

@[simp]
theorem coe_compatibleLiftsCharacterToKernel (χ : G →* N) :
    (compatibleLiftsCharacterToKernel S ρ hcentral χ : S.compatibleLifts ρ) =
      compatibleLiftsCharacter S ρ hcentral χ :=
  (rfl)

@[simp]
theorem compatibleLiftsKernelCharacter_characterToKernel (χ : G →* N) :
    compatibleLiftsKernelCharacter S ρ hcentral (compatibleLiftsCharacterToKernel S ρ hcentral χ) =
      χ := by
  ext g
  obtain ⟨e, rfl⟩ := S.rightHom_surjective g
  apply S.inl_injective
  rw [inl_compatibleLiftsKernelCharacter_rightHom, coe_compatibleLiftsCharacterToKernel,
    compatibleLiftsToMulAut_character, twist_apply,
    mul_inv_cancel_right]

theorem compatibleLiftsCharacter_injective : Function.Injective
    (compatibleLiftsCharacter S ρ hcentral) := by
  intro χ ψ h
  apply Function.LeftInverse.injective
    (compatibleLiftsKernelCharacter_characterToKernel S ρ hcentral)
  exact Subtype.ext h

@[simp]
theorem compatibleLiftsCharacter_kernelCharacter (x : (compatibleLiftsProjection S ρ).ker) :
    compatibleLiftsCharacter S ρ hcentral (compatibleLiftsKernelCharacter S ρ hcentral x) =
      x.val := by
  apply compatibleLifts_ext S ρ
  · apply MulEquiv.ext
    intro e
    rw [compatibleLiftsToMulAut_character, twist_apply,
      inl_compatibleLiftsKernelCharacter_rightHom, inv_mul_cancel_right]
  · rw [compatibleLiftsProjection_character]
    exact (MonoidHom.mem_ker.mp x.property).symm

/-- The full kernel of compatible lifts is the group of characters of the quotient. The inverse
is the descended displacement `compatibleLiftsKernelCharacter`, with no choice of a normalized
section. -/
noncomputable def compatibleLiftsKernelEquiv : (G →* N) ≃* (compatibleLiftsProjection S ρ).ker where
  toFun := compatibleLiftsCharacterToKernel S ρ hcentral
  invFun := compatibleLiftsKernelCharacter S ρ hcentral
  left_inv := compatibleLiftsKernelCharacter_characterToKernel S ρ hcentral
  right_inv x := Subtype.ext (compatibleLiftsCharacter_kernelCharacter S ρ hcentral x)
  map_mul' := (compatibleLiftsCharacterToKernel S ρ hcentral).map_mul

@[simp]
theorem compatibleLiftsKernelEquiv_apply (χ : G →* N) :
    compatibleLiftsKernelEquiv S ρ hcentral χ = compatibleLiftsCharacterToKernel S ρ hcentral χ :=
  (rfl)

@[simp]
theorem compatibleLiftsKernelEquiv_symm_apply (x : (compatibleLiftsProjection S ρ).ker) :
    (compatibleLiftsKernelEquiv S ρ hcentral).symm x =
      compatibleLiftsKernelCharacter S ρ hcentral x :=
  (rfl)

/-- The native extension over precisely those acting-group elements that have lifts. -/
noncomputable def compatibleLiftsExtension :
    GroupExtension (G →* N) (S.compatibleLifts ρ) (compatibleLiftsLiftableSubgroup S ρ) :=
  GroupExtension.ofMulEquivKer (compatibleLiftsToLiftable_surjective S ρ)
    ((compatibleLiftsKernelEquiv S ρ hcentral).trans
      (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict (compatibleLiftsProjection S ρ)).symm))

@[simp]
theorem compatibleLiftsExtension_rightHom :
    (compatibleLiftsExtension S ρ hcentral).rightHom = compatibleLiftsToLiftable S ρ := by
  rw [compatibleLiftsExtension, GroupExtension.ofMulEquivKer_rightHom]

@[simp]
theorem compatibleLiftsExtension_inl (χ : G →* N) :
    (compatibleLiftsExtension S ρ hcentral).inl χ = compatibleLiftsCharacter S ρ hcentral χ := by
  rw [compatibleLiftsExtension, GroupExtension.ofMulEquivKer_inl]
  -- The transported kernel equivalence preserves the underlying compatible lift.
  rfl

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
    (h : Function.Surjective (compatibleLiftsProjection S ρ)) (χ : G →* N) :
    (compatibleLiftsExtensionOfSurjective S ρ hcentral h).inl χ =
      compatibleLiftsCharacter S ρ hcentral χ := by
  rw [compatibleLiftsExtensionOfSurjective, GroupExtension.ofMulEquivKer_inl]
  -- Kernel restriction changes only the membership proof.
  rfl

/-- The kernel action of compatible lifts is the inverse-pullback action on characters. -/
theorem conj_compatibleLiftsCharacter (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * compatibleLiftsCharacter S ρ hcentral χ * x⁻¹ =
      compatibleLiftsCharacter S ρ hcentral
        (χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom) := by
  apply compatibleLifts_ext S ρ
  · simpa only [map_mul, map_inv,
    compatibleLiftsToMulAut_character] using compatibleLiftsToMulAut_conj_twist S ρ hcentral x χ
  · simp only [map_mul, map_inv, compatibleLiftsProjection_character, mul_one, mul_inv_cancel]

/-- Two lifts of the same acting-group element differ by a unique source character twist. -/
theorem existsUnique_eq_mul_compatibleLiftsCharacter (x y : S.compatibleLifts ρ)
    (h : compatibleLiftsProjection S ρ x = compatibleLiftsProjection S ρ y) :
    ∃! χ : G →* N, y = x * compatibleLiftsCharacter S ρ hcentral χ := by
  let z : (compatibleLiftsProjection S ρ).ker := ⟨x⁻¹ * y, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]⟩
  have hz := compatibleLiftsCharacter_kernelCharacter S ρ hcentral z
  refine ⟨compatibleLiftsKernelCharacter S ρ hcentral z, ?_, ?_⟩
  · dsimp only
    rw [hz]
    exact (mul_inv_cancel_left x y).symm
  · intro ψ hψ
    apply compatibleLiftsCharacter_injective S ρ hcentral
    apply mul_left_cancel (a := x)
    rw [← hψ, hz]
    exact (mul_inv_cancel_left x y).symm

/-- A source character twist multiplies the image of each element by its original character
value, since a compatible lift fixes the included kernel. -/
theorem compatibleLiftsToMulAut_mul_character (x : S.compatibleLifts ρ) (χ : G →* N) (e : E) :
    compatibleLiftsToMulAut S ρ (x * compatibleLiftsCharacter S ρ hcentral χ) e =
      S.inl (χ (S.rightHom e)) * compatibleLiftsToMulAut S ρ x e := by
  rw [map_mul, MulAut.mul_apply, compatibleLiftsToMulAut_character, twist_apply, map_mul,
    compatibleLiftsToMulAut_inl]

include hcentral in
/-- Two lifts of the same acting-group element differ pointwise by a unique quotient character. -/
theorem existsUnique_compatibleLiftsToMulAut_eq_inl_mul (x y : S.compatibleLifts ρ)
    (h : compatibleLiftsProjection S ρ x = compatibleLiftsProjection S ρ y) :
    ∃! χ : G →* N, ∀ e, compatibleLiftsToMulAut S ρ y e =
      S.inl (χ (S.rightHom e)) * compatibleLiftsToMulAut S ρ x e := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_eq_mul_compatibleLiftsCharacter S ρ hcentral x y h
  refine ⟨χ, ?_, ?_⟩
  · intro e
    rw [hχ, compatibleLiftsToMulAut_mul_character]
  · intro ψ hψ
    apply huniq ψ
    apply compatibleLifts_ext S ρ
    · apply MulEquiv.ext
      intro e
      rw [compatibleLiftsToMulAut_mul_character]
      exact hψ e
    · rw [map_mul, compatibleLiftsProjection_character, mul_one]
      exact h.symm

/-- Moving a source twist past a lift replaces its character by inverse pullback. -/
theorem mul_compatibleLiftsCharacter_eq_character_mul (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * compatibleLiftsCharacter S ρ hcentral χ =
      compatibleLiftsCharacter S ρ hcentral
        (χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom) * x := by
  rw [← conj_compatibleLiftsCharacter]
  simp only [inv_mul_cancel_right]

end GroupExtension
