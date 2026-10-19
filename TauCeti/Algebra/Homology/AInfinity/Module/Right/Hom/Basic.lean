/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Basic

/-!
# Morphisms of right A-infinity modules

A morphism of right `A∞` modules over a fixed algebra is a degree-zero morphism of their
cofree bar comodules commuting with the bar differentials. Its Taylor map is obtained by
applying the coalgebra counit. Cofreeness makes this map determine the morphism, and makes
commutation with the differentials equivalent to the suspended Taylor-component equation.
Thus `AInfinityRightModuleHom.ofTaylor` constructs a morphism from a degree-zero Taylor map
satisfying that equation, without requiring a separate bar map. The construction uses
`Comodule.Hom.cofreeEquiv` and `Comodule.Hom.cofreeLift`; its bar/Taylor interface parallels
`AInfinityHom` for algebra morphisms.

Identities and composition use comodule morphisms. Taylor components and the unary chain map
are developed in `TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Components`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN uP uQ

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

/-- A morphism of right `A∞` modules over a fixed algebra, represented by a degree-zero
morphism of the cofree bar comodules intertwining their differentials. -/
structure AInfinityRightModuleHom (MM : AInfinityRightModule AA M)
    (NN : AInfinityRightModule AA N) where
  /-- The induced morphism of cofree bar comodules. -/
  barHom : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A)
  /-- The bar map preserves the total suspended degree. -/
  isHomogeneous_barMap : LinearMap.IsHomogeneous barHom.toLinearMap
    (AInfinityRightModule.barGrading AA MM.grading).piece
    (AInfinityRightModule.barGrading AA NN.grading).piece 0
  /-- The bar map intertwines the module bar differentials. -/
  barDifferential_comp_barMap :
    NN.barDifferential ∘ₗ barHom.toLinearMap = barHom.toLinearMap ∘ₗ MM.barDifferential

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-- The underlying linear map of the bar-comodule morphism. -/
abbrev barMap (f : AInfinityRightModuleHom MM NN) := f.barHom.toLinearMap

/-- The intertwining of the module bar differentials, applied to an element. -/
@[simp]
theorem barDifferential_barMap (f : AInfinityRightModuleHom MM NN)
    (z : M ⊗[R] TensorWords R A) :
    NN.barDifferential (f.barHom z) = f.barHom (MM.barDifferential z) :=
  LinearMap.congr_fun f.barDifferential_comp_barMap z

/-- The suspended Taylor map: apply the coalgebra counit after the bar map. -/
noncomputable def taylor (f : AInfinityRightModuleHom MM NN) :
    (M ⊗[R] TensorWords R A) →ₗ[R] N :=
  (TensorProduct.rid R N).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ f.barMap

theorem taylor_def (f : AInfinityRightModuleHom MM NN) :
    f.taylor = (TensorProduct.rid R N).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ f.barMap := (rfl)

/-- The Taylor map preserves suspended degree. -/
theorem isHomogeneous_taylor (f : AInfinityRightModuleHom MM NN) :
    LinearMap.IsHomogeneous f.taylor (AInfinityRightModule.barGrading AA MM.grading).piece
      (NN.grading.shift 1).piece 0 := by
  rw [taylor_def]
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  have hz := f.isHomogeneous_barMap.map_mem hx
  rw [AInfinityRightModule.barGrading_piece, add_zero] at hz
  exact (TensorWords.isHomogeneous_rid_comp_lTensor_counit (NN.grading.shift 1)
    (AA.grading.shift 1)).map_mem hz

/-- The bar map is the cofree lift of its Taylor map. -/
theorem barMap_eq_cofreeLift (f : AInfinityRightModuleHom MM NN) :
    f.barMap = (Comodule.Hom.cofreeLift (C := TensorWords R A) f.taylor).toLinearMap := by
  have h := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
    (P := M ⊗[R] TensorWords R A)).symm_apply_apply f.barHom
  rw [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.cofreeEquiv_symm_apply] at h
  exact congrArg Comodule.Hom.toLinearMap h.symm

/-- Morphisms are determined by their underlying bar maps. -/
theorem barMap_injective : Function.Injective (barMap : AInfinityRightModuleHom MM NN → _) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
  have hfg : f = g := Comodule.Hom.toLinearMap_injective h
  subst g
  rfl

/-- Morphisms are determined by their suspended Taylor maps. -/
@[ext]
theorem ext {f g : AInfinityRightModuleHom MM NN} (h : f.taylor = g.taylor) : f = g := by
  apply barMap_injective
  rw [f.barMap_eq_cofreeLift, g.barMap_eq_cofreeLift, h]

/-- The suspended module-morphism equation, expressed on Taylor maps. -/
@[simp]
theorem taylor_comp_barMap (f : AInfinityRightModuleHom MM NN) :
    NN.taylor ∘ₗ f.barMap = f.taylor ∘ₗ MM.barDifferential := by
  rw [AInfinityRightModule.taylor_def, taylor_def]
  simp only [LinearMap.comp_assoc, f.barDifferential_comp_barMap]

/-- For a degree-zero bar-comodule map, differential compatibility can be checked after applying
the coalgebra counit. This is the full suspended component equation. -/
theorem barDifferential_comp_iff
    (F : Comodule.Hom R (TensorWords R A)
      (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (hF : LinearMap.IsHomogeneous F.toLinearMap
      (AInfinityRightModule.barGrading AA MM.grading).piece
      (AInfinityRightModule.barGrading AA NN.grading).piece 0) :
    NN.barDifferential ∘ₗ F.toLinearMap = F.toLinearMap ∘ₗ MM.barDifferential ↔
      NN.taylor ∘ₗ F.toLinearMap =
        ((TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ F.toLinearMap) ∘ₗ
            MM.barDifferential := by
  constructor
  · intro h
    rw [AInfinityRightModule.taylor_def]
    simp only [LinearMap.comp_assoc, h]
  · intro h
    let K := F.coderivationComm
      (AInfinityRightModule.barGrading AA MM.grading)
      (AInfinityRightModule.barGrading AA NN.grading) hF MM.barDifferential NN.barDifferential
      MM.isGradedCoderivation_barDifferential NN.isGradedCoderivation_barDifferential
    have hK : K = 0 := (Comodule.Hom.eq_zero_iff_counit K).2 (by
      simp only [AInfinityRightModule.taylor_def, LinearMap.comp_assoc] at h
      simp only [K, Comodule.Hom.coderivationComm_toLinearMap, mul_zero, Int.negOnePow_zero,
        Units.val_one, Int.cast_one, one_smul, LinearMap.comp_sub]
      exact sub_eq_zero.mpr h)
    have := congrArg Comodule.Hom.toLinearMap hK
    simpa only [K, Comodule.Hom.coderivationComm_toLinearMap,
      mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      Comodule.Hom.zero_toLinearMap, sub_eq_zero] using this

/-- The cofree lift of a Taylor map of degree `r` is a map of cofree bar comodules of degree
`r`. -/
theorem isHomogeneous_cofreeLift {r : ℤ}
    {F : (M ⊗[R] TensorWords R A) →ₗ[R] N}
    (hF : LinearMap.IsHomogeneous F (AInfinityRightModule.barGrading AA MM.grading).piece
      (NN.grading.shift 1).piece r) :
    LinearMap.IsHomogeneous (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap
      (AInfinityRightModule.barGrading AA MM.grading).piece
      (AInfinityRightModule.barGrading AA NN.grading).piece r := by
  let W := TensorWords.grading (AA.grading.shift 1)
  have hG (G : InternalGrading R M) : AInfinityRightModule.barGrading AA G =
      (G.shift 1).tensorProduct W := by
    ext p
    rw [AInfinityRightModule.barGrading_piece]
  have hH : AInfinityRightModule.barGrading AA NN.grading =
      (NN.grading.shift 1).tensorProduct W := by
    ext p
    rw [AInfinityRightModule.barGrading_piece]
  rw [Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact, hG, hH]
  rw [hG] at hF
  have hρ := (InternalGrading.isHomogeneous_assoc_symm (MM.grading.shift 1) W W).comp
    ((LinearMap.isHomogeneous_id (MM.grading.shift 1).piece).tensorProduct
      (TensorWords.isHomogeneous_deconcatenation (AA.grading.shift 1)))
  have h := (hF.tensorProduct (LinearMap.isHomogeneous_id W.piece)).comp hρ
  simp only [add_zero, zero_add] at h
  exact h

/-- Construct a module morphism from a degree-zero Taylor map satisfying the suspended component
equation. Cofreeness supplies the bar map and reduces its differential law to this equation. -/
noncomputable def ofTaylor (F : (M ⊗[R] TensorWords R A) →ₗ[R] N)
    (hF : LinearMap.IsHomogeneous F (AInfinityRightModule.barGrading AA MM.grading).piece
      (NN.grading.shift 1).piece 0)
    (h : NN.taylor ∘ₗ (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap =
      F ∘ₗ MM.barDifferential) : AInfinityRightModuleHom MM NN where
  barHom := Comodule.Hom.cofreeLift F
  isHomogeneous_barMap := isHomogeneous_cofreeLift hF
  barDifferential_comp_barMap := (barDifferential_comp_iff _ (isHomogeneous_cofreeLift hF)).2
    (by
      have hret := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
        (P := M ⊗[R] TensorWords R A)).apply_symm_apply F
      rw [Comodule.Hom.cofreeEquiv_symm_apply, Comodule.Hom.cofreeEquiv_apply] at hret
      rw [hret]
      exact h)

/-- The bar map of the constructed morphism is the cofree lift. -/
@[simp]
theorem barMap_ofTaylor (F : (M ⊗[R] TensorWords R A) →ₗ[R] N) (hF h) :
    (ofTaylor (MM := MM) (NN := NN) F hF h).barMap =
      (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap := (rfl)

/-- The constructed morphism has the prescribed Taylor map. -/
@[simp]
theorem taylor_ofTaylor (F : (M ⊗[R] TensorWords R A) →ₗ[R] N) (hF h) :
    (ofTaylor (MM := MM) (NN := NN) F hF h).taylor = F := by
  have hret := (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
    (P := M ⊗[R] TensorWords R A)).apply_symm_apply F
  rw [Comodule.Hom.cofreeEquiv_symm_apply, Comodule.Hom.cofreeEquiv_apply] at hret
  rw [taylor_def, barMap_ofTaylor]
  exact hret

/-- Every morphism is recovered from its Taylor map and component equation. -/
@[simp]
theorem ofTaylor_self (f : AInfinityRightModuleHom MM NN) :
    ofTaylor f.taylor f.isHomogeneous_taylor
      (by rw [← f.barMap_eq_cofreeLift]; exact f.taylor_comp_barMap) = f :=
  ext (taylor_ofTaylor _ _ _)

/-- The identity module morphism. -/
protected noncomputable def id (MM : AInfinityRightModule AA M) :
    AInfinityRightModuleHom MM MM where
  barHom := Comodule.Hom.id R (TensorWords R A) (M ⊗[R] TensorWords R A)
  isHomogeneous_barMap := LinearMap.isHomogeneous_id _
  barDifferential_comp_barMap := by simp

@[simp]
theorem barMap_id (MM : AInfinityRightModule AA M) :
    (AInfinityRightModuleHom.id MM).barMap = LinearMap.id := (rfl)

/-- The Taylor map of the identity is the counit projection onto the module factor. -/
@[simp]
theorem taylor_id (MM : AInfinityRightModule AA M) :
    (AInfinityRightModuleHom.id MM).taylor = (TensorProduct.rid R M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M := by
  rw [taylor_def, barMap_id, LinearMap.comp_id]

/-- Composition of module morphisms is composition of bar-comodule maps. -/
noncomputable def comp (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN) :
    AInfinityRightModuleHom MM PP where
  barHom := g.barHom.comp f.barHom
  isHomogeneous_barMap := by simpa using g.isHomogeneous_barMap.comp f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    simp only [Comodule.Hom.comp_toLinearMap]
    rw [← LinearMap.comp_assoc, g.barDifferential_comp_barMap, LinearMap.comp_assoc,
      f.barDifferential_comp_barMap, LinearMap.comp_assoc]

@[simp]
theorem barMap_comp (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN) :
    (g.comp f).barMap = g.barMap ∘ₗ f.barMap := (rfl)

/-- Taylor components of a composite are obtained by applying the second Taylor map to the
first bar map. -/
@[simp]
theorem taylor_comp (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN) :
    (g.comp f).taylor = g.taylor ∘ₗ f.barMap := by
  simp only [taylor_def, barMap_comp, LinearMap.comp_assoc]

/-- The identity module morphism is a right identity for composition. -/
@[simp]
theorem comp_id (f : AInfinityRightModuleHom MM NN) :
    f.comp (AInfinityRightModuleHom.id MM) = f :=
  barMap_injective (by simp)

/-- The identity module morphism is a left identity for composition. -/
@[simp]
theorem id_comp (f : AInfinityRightModuleHom MM NN) :
    (AInfinityRightModuleHom.id NN).comp f = f :=
  barMap_injective (by simp)

/-- Composition of module morphisms is associative. -/
@[simp]
theorem comp_assoc {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    {QQ : AInfinityRightModule AA Q} (h : AInfinityRightModuleHom PP QQ)
    (g : AInfinityRightModuleHom NN PP) (f : AInfinityRightModuleHom MM NN) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  barMap_injective (by simp only [barMap_comp, LinearMap.comp_assoc])

end AInfinityRightModuleHom

end TauCeti
