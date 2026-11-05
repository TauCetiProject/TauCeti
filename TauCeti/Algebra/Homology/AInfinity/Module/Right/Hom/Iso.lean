/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Category
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Isomorphisms of right A-infinity modules

A morphism of right `A∞` modules over a fixed algebra is an *isomorphism* when it has a two-sided
inverse morphism.  This happens exactly when its linear part `f₁` is bijective.

The bar map `F` of a module morphism `f : M ⟶ N` is a morphism of cofree bar comodules
`sM ⊗ Tᶜ(sA) ⟶ sN ⊗ Tᶜ(sA)`, the cofree lift of its Taylor map.  On a word `x ⊗ a₁ ⋯ aₙ` it applies
the Taylor map to every prefix `x ⊗ a₁ ⋯ a_k` and keeps the suffix `a_{k+1} ⋯ aₙ`; the term
`k = 0` is `f₁ x ⊗ a₁ ⋯ aₙ`, and the others have shorter algebra words.  If `f₁` is bijective, the
comodule endomorphism `G = (f₁⁻¹ ⊗ 1) F` of the source is therefore `1 + K` with `K` the cofree
lift of a map vanishing on the empty algebra word.  Such a cofree lift strictly shortens algebra
words, so it is locally nilpotent
(`TauCeti.TensorWords.exists_pow_cofreeLift_apply_eq_zero`) and `G` is invertible, with
inverse again a comodule endomorphism of degree zero.  The bar map of the inverse module morphism
`TauCeti.AInfinityRightModuleHom.inverse` is `G⁻¹ (f₁⁻¹ ⊗ 1)`, and its linear part is the inverse
of `f₁`.

Every isomorphism is a quasi-isomorphism.  Between modules with zero unary operation the converse
holds, which gives the uniqueness of minimal models of modules; see
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Basic`.

## Main definitions

* `TauCeti.AInfinityRightModuleHom.barEquiv`: the bar map of a module morphism with bijective
  linear part, as a linear equivalence.
* `TauCeti.AInfinityRightModuleHom.inverse`: the inverse of a module morphism with bijective
  linear part.
* `TauCeti.AInfinityRightModuleHom.IsIso`: a module morphism with a two-sided inverse.

## Main results

* `TauCeti.AInfinityRightModuleHom.barMap_inverse`: the bar map of the inverse is the inverse of
  `TauCeti.AInfinityRightModuleHom.barEquiv`.
* `TauCeti.AInfinityRightModuleHom.inverse_comp_cancel` and
  `TauCeti.AInfinityRightModuleHom.comp_inverse_cancel`: the inverse is a two-sided inverse, and
  `TauCeti.AInfinityRightModuleHom.linearPart_inverse`: its linear part is the inverse linear
  equivalence.
* `TauCeti.AInfinityRightModuleHom.eq_inverse_of_comp_eq_id_left` and
  `TauCeti.AInfinityRightModuleHom.eq_inverse_of_comp_eq_id_right`: any one-sided inverse is the
  inverse.
* `TauCeti.AInfinityRightModuleHom.isIso_iff_linearPart_bijective`: a module morphism is an
  isomorphism exactly when its linear part is bijective.
* `TauCeti.AInfinityRightModuleHom.IsIso.isQuasiIso`: an isomorphism is a quasi-isomorphism.
* `TauCeti.AInfinityRightModuleCat.isIso_iff`: for modules bundled in the category
  `TauCeti.AInfinityRightModuleCat`, the predicate `IsIso` is Mathlib's `CategoryTheory.IsIso`.

The algebra counterpart is `TauCeti.AInfinityHom.inverse`, in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso`, whose interface is followed here.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-! ### The inverse of a morphism with bijective linear part -/

section Inverse

variable (f : AInfinityRightModuleHom MM NN) (hf : Function.Bijective f.linearPart)

/-- The comodule endomorphism `(f₁⁻¹ ⊗ 1) F` of the source bar comodule, for `F` the bar map of
a module morphism with bijective linear part `f₁`. -/
private noncomputable def unipotentBarHom :
    Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A) :=
  (Comodule.Hom.cofreeMap (C := TensorWords R A)
    (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap).comp f.barHom

/-- The difference between the Taylor map of `(f₁⁻¹ ⊗ 1) F` and that of the identity. -/
private noncomputable def unipotentTaylorDiff : (M ⊗[R] TensorWords R A) →ₗ[R] M :=
  (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap ∘ₗ f.taylor -
    (TensorProduct.rid R M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M

private theorem unipotentTaylorDiff_tmul_one (x : M) :
    unipotentTaylorDiff f hf (x ⊗ₜ[R] (1 : TensorWords R A)) = 0 := by
  simp [unipotentTaylorDiff, ← linearPart_apply, TensorWords.counit_eq_counit,
    TensorWords.counit_one]

/-- The endomorphism `(f₁⁻¹ ⊗ 1) F` is the identity plus the cofree lift of a map vanishing on the
empty algebra word. -/
private theorem unipotentBarHom_toLinearMap :
    (unipotentBarHom f hf).toLinearMap = 1 +
      (Comodule.Hom.cofreeLift (C := TensorWords R A) (unipotentTaylorDiff f hf)).toLinearMap := by
  have hF : f.barHom = Comodule.Hom.cofreeLift (C := TensorWords R A) f.taylor :=
    Comodule.Hom.toLinearMap_injective f.barMap_eq_cofreeLift
  have hid := Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp (R := R)
    (C := TensorWords R A) (Comodule.Hom.id R (TensorWords R A) (M ⊗[R] TensorWords R A))
  rw [Comodule.Hom.id_toLinearMap, LinearMap.comp_id] at hid
  -- The Taylor map of `(f₁⁻¹ ⊗ 1) F` is the Taylor map of the identity plus the difference.
  have hsplit : (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap ∘ₗ f.taylor =
      unipotentTaylorDiff f hf + (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M := by
    rw [unipotentTaylorDiff, sub_add_cancel]
  rw [unipotentBarHom, hF, Comodule.Hom.cofreeMap_comp_cofreeLift, hsplit,
    Comodule.Hom.cofreeLift_add, hid, Comodule.Hom.add_toLinearMap, Comodule.Hom.id_toLinearMap,
    add_comm, Module.End.one_eq_id]

private theorem isUnit_unipotentBarHom : IsUnit (unipotentBarHom f hf).toLinearMap := by
  rw [unipotentBarHom_toLinearMap]
  exact Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (TensorWords.exists_pow_cofreeLift_apply_eq_zero _
      (unipotentTaylorDiff_tmul_one f hf))

/-- The bar map of the inverse, `G⁻¹ (f₁⁻¹ ⊗ 1)` with `G = (f₁⁻¹ ⊗ 1) F`. -/
private noncomputable def inverseBarHom :
    Comodule.Hom R (TensorWords R A) (N ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A) :=
  (unipotentBarHom f hf).ringInverse.comp
    (Comodule.Hom.cofreeMap (C := TensorWords R A)
      (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap)

private theorem inverseBarHom_comp_barMap :
    (inverseBarHom f hf).toLinearMap ∘ₗ f.barMap = LinearMap.id := by
  have h := Ring.inverse_mul_cancel _ (isUnit_unipotentBarHom f hf)
  rw [Module.End.mul_eq_comp, Module.End.one_eq_id] at h
  rw [inverseBarHom, Comodule.Hom.comp_toLinearMap, LinearMap.comp_assoc,
    Comodule.Hom.ringInverse_toLinearMap]
  exact h

private theorem barMap_comp_inverseBarHom :
    f.barMap ∘ₗ (inverseBarHom f hf).toLinearMap = LinearMap.id := by
  set e := LinearEquiv.ofBijective f.linearPart hf
  have h := Ring.mul_inverse_cancel _ (isUnit_unipotentBarHom f hf)
  rw [Module.End.mul_eq_comp, Module.End.one_eq_id] at h
  -- `(f₁ ⊗ 1) (f₁⁻¹ ⊗ 1) = 1`.
  have he : e.toLinearMap.rTensor (TensorWords R A) ∘ₗ
      e.symm.toLinearMap.rTensor (TensorWords R A) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, e.comp_symm, LinearMap.rTensor_id]
  -- `F = (f₁ ⊗ 1) G`.
  have hF : f.barMap = e.toLinearMap.rTensor (TensorWords R A) ∘ₗ
      (unipotentBarHom f hf).toLinearMap := by
    rw [unipotentBarHom, Comodule.Hom.comp_toLinearMap, Comodule.Hom.cofreeMap_toLinearMap,
      ← LinearMap.comp_assoc, he, LinearMap.id_comp]
  rw [hF, inverseBarHom, Comodule.Hom.comp_toLinearMap, Comodule.Hom.ringInverse_toLinearMap,
    Comodule.Hom.cofreeMap_toLinearMap]
  simp only [← LinearMap.comp_assoc] at h ⊢
  rw [LinearMap.comp_assoc _ (unipotentBarHom f hf).toLinearMap, h, LinearMap.comp_id, he]

/-- The bar map of a module morphism with bijective linear part, as a linear equivalence. -/
noncomputable def barEquiv : (M ⊗[R] TensorWords R A) ≃ₗ[R] N ⊗[R] TensorWords R A :=
  LinearEquiv.ofLinearMap f.barMap (inverseBarHom f hf).toLinearMap
    (barMap_comp_inverseBarHom f hf) (inverseBarHom_comp_barMap f hf)

/-- The linear equivalence `barEquiv` acts as the bar map. -/
@[simp]
theorem barEquiv_apply (z : M ⊗[R] TensorWords R A) : f.barEquiv hf z = f.barHom z := (rfl)

/-- The underlying linear map of `barEquiv` is the bar map. -/
theorem coe_barEquiv : (f.barEquiv hf).toLinearMap = f.barMap :=
  LinearMap.ext (f.barEquiv_apply hf)

private theorem isHomogeneous_inverseBarHom :
    LinearMap.IsHomogeneous (inverseBarHom f hf).toLinearMap
      (AInfinityRightModule.barGrading AA NN.grading).piece
      (AInfinityRightModule.barGrading AA MM.grading).piece 0 :=
  LinearMap.IsHomogeneous.linearEquiv_symm (e := f.barEquiv hf) f.isHomogeneous_barMap

/-- The **inverse** of a module morphism with bijective linear part.  Its bar map is the inverse of
the bar map of the morphism, which is again a degree-zero comodule morphism intertwining the bar
differentials. -/
noncomputable def inverse : AInfinityRightModuleHom NN MM where
  barHom := inverseBarHom f hf
  isHomogeneous_barMap := isHomogeneous_inverseBarHom f hf
  barDifferential_comp_barMap := by
    set V := (inverseBarHom f hf).toLinearMap
    calc MM.barDifferential ∘ₗ V = (V ∘ₗ f.barMap) ∘ₗ MM.barDifferential ∘ₗ V := by
          rw [inverseBarHom_comp_barMap, LinearMap.id_comp]
      _ = V ∘ₗ (NN.barDifferential ∘ₗ f.barMap) ∘ₗ V := by
          rw [f.barDifferential_comp_barMap]
          simp only [LinearMap.comp_assoc]
      _ = V ∘ₗ NN.barDifferential := by
          rw [LinearMap.comp_assoc, barMap_comp_inverseBarHom, LinearMap.comp_id]

/-- The bar map of the inverse is the inverse of `barEquiv`. -/
@[simp]
theorem barMap_inverse : (f.inverse hf).barMap = (f.barEquiv hf).symm.toLinearMap := (rfl)

/-- The inverse of `barEquiv` undoes the bar map. -/
@[simp]
theorem barEquiv_symm_barMap (z : M ⊗[R] TensorWords R A) :
    (f.barEquiv hf).symm (f.barHom z) = z := by
  rw [← barEquiv_apply f hf, LinearEquiv.symm_apply_apply]

/-- The bar map undoes the inverse of `barEquiv`. -/
@[simp]
theorem barMap_barEquiv_symm (w : N ⊗[R] TensorWords R A) :
    f.barHom ((f.barEquiv hf).symm w) = w := by
  rw [← barEquiv_apply f hf, LinearEquiv.apply_symm_apply]

/-- The inverse is a left inverse. -/
@[simp]
theorem inverse_comp_cancel : (f.inverse hf).comp f = AInfinityRightModuleHom.id MM :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id]
    exact inverseBarHom_comp_barMap f hf

/-- The inverse is a right inverse. -/
@[simp]
theorem comp_inverse_cancel : f.comp (f.inverse hf) = AInfinityRightModuleHom.id NN :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id]
    exact barMap_comp_inverseBarHom f hf

include hf in
/-- The bar map of a module morphism with bijective linear part is bijective. -/
theorem barMap_bijective_of_linearPart_bijective : Function.Bijective f.barMap := by
  rw [← f.coe_barEquiv hf]
  exact (f.barEquiv hf).bijective

/-- The linear part of the inverse is the inverse of the linear part. -/
@[simp]
theorem linearPart_inverse :
    (f.inverse hf).linearPart = (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap := by
  have h := congrArg linearPart (f.inverse_comp_cancel hf)
  rw [linearPart_comp, linearPart_id] at h
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply, ← LinearMap.comp_apply, h,
    LinearMap.id_apply]

/-- The linear part of the inverse is bijective. -/
theorem linearPart_inverse_bijective : Function.Bijective (f.inverse hf).linearPart := by
  rw [linearPart_inverse]
  exact (LinearEquiv.ofBijective f.linearPart hf).symm.bijective

end Inverse

/-! ### Uniqueness and normal forms of the inverse -/

/-- A left inverse of a module morphism with bijective linear part is its inverse. -/
theorem eq_inverse_of_comp_eq_id_left {f : AInfinityRightModuleHom MM NN}
    {g : AInfinityRightModuleHom NN MM} (hf : Function.Bijective f.linearPart)
    (h : g.comp f = AInfinityRightModuleHom.id MM) : g = f.inverse hf := by
  rw [← comp_id g, ← comp_inverse_cancel f hf, ← comp_assoc, h, id_comp]

/-- A right inverse of a module morphism with bijective linear part is its inverse. -/
theorem eq_inverse_of_comp_eq_id_right {f : AInfinityRightModuleHom MM NN}
    {g : AInfinityRightModuleHom NN MM} (hf : Function.Bijective f.linearPart)
    (h : f.comp g = AInfinityRightModuleHom.id NN) : g = f.inverse hf := by
  rw [← id_comp g, ← inverse_comp_cancel f hf, comp_assoc, h, comp_id]

/-- The inverse of the identity is the identity. -/
@[simp]
theorem inverse_id (MM : AInfinityRightModule AA M)
    (h : Function.Bijective (AInfinityRightModuleHom.id MM).linearPart) :
    (AInfinityRightModuleHom.id MM).inverse h = AInfinityRightModuleHom.id MM :=
  (eq_inverse_of_comp_eq_id_left h (comp_id _)).symm

/-- The inverse of the inverse is the original morphism. -/
@[simp]
theorem inverse_inverse (f : AInfinityRightModuleHom MM NN) (hf : Function.Bijective f.linearPart)
    (h : Function.Bijective (f.inverse hf).linearPart) : (f.inverse hf).inverse h = f :=
  (eq_inverse_of_comp_eq_id_left h (comp_inverse_cancel f hf)).symm

/-- The inverse of a composite is the composite of the inverses in the reverse order. -/
@[simp]
theorem inverse_comp (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN)
    (hg : Function.Bijective g.linearPart) (hf : Function.Bijective f.linearPart)
    (h : Function.Bijective (g.comp f).linearPart) :
    (g.comp f).inverse h = (f.inverse hf).comp (g.inverse hg) :=
  (eq_inverse_of_comp_eq_id_left h (by
    rw [comp_assoc, ← comp_assoc (g.inverse hg), inverse_comp_cancel, id_comp,
      inverse_comp_cancel])).symm

/-! ### Isomorphisms -/

/-- A morphism of right `A∞` modules is an **isomorphism** when it has a two-sided inverse
morphism. -/
def IsIso (f : AInfinityRightModuleHom MM NN) : Prop :=
  ∃ g : AInfinityRightModuleHom NN MM,
    g.comp f = AInfinityRightModuleHom.id MM ∧ f.comp g = AInfinityRightModuleHom.id NN

-- The body of `IsIso` is not exposed, so later modules can neither destructure an `IsIso`
-- hypothesis nor build one by anonymous constructor; this restatement is their access to it.
/-- A module morphism is an isomorphism exactly when it has a two-sided inverse. -/
theorem isIso_def (f : AInfinityRightModuleHom MM NN) :
    f.IsIso ↔ ∃ g : AInfinityRightModuleHom NN MM,
      g.comp f = AInfinityRightModuleHom.id MM ∧ f.comp g = AInfinityRightModuleHom.id NN :=
  Iff.rfl

/-- The identity module morphism is an isomorphism. -/
@[simp]
theorem isIso_id (MM : AInfinityRightModule AA M) : (AInfinityRightModuleHom.id MM).IsIso :=
  ⟨AInfinityRightModuleHom.id MM, comp_id _, comp_id _⟩

/-- Isomorphisms of right `A∞` modules are closed under composition. -/
theorem IsIso.comp {g : AInfinityRightModuleHom NN PP} {f : AInfinityRightModuleHom MM NN}
    (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g', hg₁, id_comp, hf₁]
  · rw [comp_assoc, ← comp_assoc f, hf₂, id_comp, hg₂]

/-- A module morphism with bijective linear part is an isomorphism. -/
theorem isIso_of_linearPart_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : f.IsIso :=
  ⟨f.inverse hf, f.inverse_comp_cancel hf, f.comp_inverse_cancel hf⟩

/-- The inverse of a module morphism with bijective linear part is an isomorphism. -/
theorem isIso_inverse (f : AInfinityRightModuleHom MM NN) (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).IsIso :=
  ⟨f, f.comp_inverse_cancel hf, f.inverse_comp_cancel hf⟩

/-- The linear part of an isomorphism is bijective. -/
theorem IsIso.linearPart_bijective {f : AInfinityRightModuleHom MM NN} (h : f.IsIso) :
    Function.Bijective f.linearPart := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  refine Function.bijective_iff_has_inverse.2 ⟨g.linearPart, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₁, linearPart_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₂, linearPart_id, LinearMap.id_apply]

/-- A module morphism is an isomorphism exactly when its linear part is bijective. -/
theorem isIso_iff_linearPart_bijective (f : AInfinityRightModuleHom MM NN) :
    f.IsIso ↔ Function.Bijective f.linearPart :=
  ⟨IsIso.linearPart_bijective, f.isIso_of_linearPart_bijective⟩

/-- An isomorphism of right `A∞` modules is a quasi-isomorphism. -/
theorem IsIso.isQuasiIso {f : AInfinityRightModuleHom MM NN} (h : f.IsIso) : f.IsQuasiIso := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hg₁, cohomologyMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hg₂, cohomologyMap_id, LinearMap.id_apply]

end AInfinityRightModuleHom

namespace AInfinityRightModuleCat

/-- A morphism of bundled right `A∞` modules is an isomorphism in the category of right `A∞`
modules exactly when it is an isomorphism of right `A∞` modules. -/
theorem isIso_iff {M N : AInfinityRightModuleCat.{uR, uA, uM} AA} (f : M ⟶ N) :
    CategoryTheory.IsIso f ↔ AInfinityRightModuleHom.IsIso f := by
  -- Both notions of inverse are compared through bar maps, where categorical composition and
  -- identities are `barMap_comp` and `barMap_id`.
  refine ⟨fun _ ↦ ⟨CategoryTheory.inv f, ?_, ?_⟩, fun ⟨g, hg₁, hg₂⟩ ↦ ⟨g, ?_, ?_⟩⟩ <;>
    refine AInfinityRightModuleHom.barMap_injective ?_
  · rw [AInfinityRightModuleHom.barMap_comp, ← barMap_comp, CategoryTheory.IsIso.hom_inv_id,
      barMap_id, AInfinityRightModuleHom.barMap_id]
  · rw [AInfinityRightModuleHom.barMap_comp, ← barMap_comp, CategoryTheory.IsIso.inv_hom_id,
      barMap_id, AInfinityRightModuleHom.barMap_id]
  · rw [barMap_comp, ← AInfinityRightModuleHom.barMap_comp, hg₁, barMap_id,
      AInfinityRightModuleHom.barMap_id]
  · rw [barMap_comp, ← AInfinityRightModuleHom.barMap_comp, hg₂, barMap_id,
      AInfinityRightModuleHom.barMap_id]

end AInfinityRightModuleCat

end TauCeti
