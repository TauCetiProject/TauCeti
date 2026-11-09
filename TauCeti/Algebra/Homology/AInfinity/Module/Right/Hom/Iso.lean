/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import Mathlib.CategoryTheory.Iso
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Category
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.CofreeHom

/-!
# Isomorphisms of right A-infinity modules

A morphism of right `A∞` modules over a fixed algebra is an *isomorphism* when it has a two-sided
inverse morphism.  This happens exactly when its linear part `f₁` is bijective.  Indeed the bar
map of a module morphism is a morphism of cofree comodules `sM ⊗ Tᶜ(sA) ⟶ sN ⊗ Tᶜ(sA)` which is
`f₁ ⊗ 1` up to a map shortening the algebra words, so it is bijective as soon as `f₁` is (see
`TauCeti.Comodule.Hom.bijective_of_apply_tmul_one`).  Its inverse is again a degree-zero
comodule morphism intertwining the bar differentials; this is the inverse module morphism
`TauCeti.AInfinityRightModuleHom.inverse`, whose linear part is the inverse of `f₁`.

Every isomorphism is a quasi-isomorphism.  Between modules with vanishing unary operation, the
converse holds: their cohomology is the module itself, so a quasi-isomorphism has bijective
linear part.  This is the step needed to compare two minimal models of the same right `A∞`
module: a quasi-isomorphism between them is an isomorphism.

## Main definitions

* `TauCeti.AInfinityRightModuleHom.barEquiv`: the bar map of a module morphism with bijective
  linear part, as a linear equivalence.
* `TauCeti.AInfinityRightModuleHom.inverse`: the inverse of a module morphism with bijective
  linear part.
* `TauCeti.AInfinityRightModuleHom.IsIso`: a module morphism with a two-sided inverse.

## Main results

* `TauCeti.AInfinityRightModuleHom.inverse_comp_cancel` and
  `TauCeti.AInfinityRightModuleHom.comp_inverse_cancel`: the inverse is a two-sided inverse, and
  `TauCeti.AInfinityRightModuleHom.linearPart_inverse`: its linear part is the inverse linear
  equivalence.
* `TauCeti.AInfinityRightModuleHom.isIso_iff_linearPart_bijective`: a module morphism is an
  isomorphism exactly when its linear part is bijective.
* `TauCeti.AInfinityRightModuleHom.IsIso.isQuasiIso`: an isomorphism is a quasi-isomorphism.
* `TauCeti.AInfinityRightModuleHom.isQuasiIso_iff_isIso`: between modules with vanishing unary
  operation, quasi-isomorphisms are exactly the isomorphisms.
* `TauCeti.AInfinityRightModuleCat.isIso_iff_linearPart_bijective`: the same criterion for
  isomorphisms in the category of right `A∞` modules.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* K. Lefèvre-Hasegawa, *Sur les A∞-catégories*, thèse de doctorat, Université Paris 7 (2003),
  Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-! ### The inverse of a morphism with bijective linear part -/

/-- The bar map of a module morphism with bijective linear part is bijective. -/
theorem barMap_bijective_of_linearPart_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective f.barMap :=
  f.barHom.bijective_of_apply_tmul_one hf f.barMap_tmul_one

/-- The bar map of a module morphism with bijective linear part, as a linear equivalence of bar
constructions. -/
noncomputable def barEquiv (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (M ⊗[R] TensorWords R A) ≃ₗ[R] (N ⊗[R] TensorWords R A) :=
  LinearEquiv.ofBijective f.barMap (f.barMap_bijective_of_linearPart_bijective hf)

/-- The linear equivalence `barEquiv f hf` applies the bar map of `f`. -/
@[simp]
theorem barEquiv_apply (f : AInfinityRightModuleHom MM NN) (hf : Function.Bijective f.linearPart)
    (z : M ⊗[R] TensorWords R A) : f.barEquiv hf z = f.barHom z := (rfl)

/-- The inverse of `barEquiv f hf` undoes the bar map of `f`. -/
@[simp]
theorem barEquiv_symm_barMap (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) (z : M ⊗[R] TensorWords R A) :
    (f.barEquiv hf).symm (f.barHom z) = z := by
  rw [← barEquiv_apply f hf, LinearEquiv.symm_apply_apply]

/-- The bar map of `f` undoes the inverse of `barEquiv f hf`. -/
@[simp]
theorem barMap_barEquiv_symm (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) (w : N ⊗[R] TensorWords R A) :
    f.barHom ((f.barEquiv hf).symm w) = w := by
  rw [← barEquiv_apply f hf, LinearEquiv.apply_symm_apply]

/-- The inverse of a module morphism with bijective linear part: its bar map is the inverse of
the bar map, which is again a degree-zero comodule morphism intertwining the bar differentials. -/
noncomputable def inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : AInfinityRightModuleHom NN MM where
  barHom := f.barHom.inverse (f.barMap_bijective_of_linearPart_bijective hf)
  isHomogeneous_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap]
    exact LinearMap.IsHomogeneous.linearEquiv_symm f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap]
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨z, rfl⟩ := (f.barEquiv hf).surjective w
    -- `Comodule.Hom.inverse_toLinearMap` exhibits the inverse bar map as `(f.barEquiv hf).symm`.
    change MM.barDifferential ((f.barEquiv hf).symm _) = (f.barEquiv hf).symm _
    rw [barEquiv_apply, barDifferential_barMap, barEquiv_symm_barMap, barEquiv_symm_barMap]

/-- The bar map of the inverse is the inverse of the bar map. -/
@[simp]
theorem barMap_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).barMap = (f.barEquiv hf).symm.toLinearMap :=
  Comodule.Hom.inverse_toLinearMap _ _

/-- The inverse is a left inverse. -/
@[simp]
theorem inverse_comp_cancel (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).comp f = AInfinityRightModuleHom.id MM :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barEquiv_symm_barMap hf)

/-- The inverse is a right inverse. -/
@[simp]
theorem comp_inverse_cancel (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    f.comp (f.inverse hf) = AInfinityRightModuleHom.id NN :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barMap_barEquiv_symm hf)

/-- The linear part of the inverse is the inverse of the linear part. -/
@[simp]
theorem linearPart_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).linearPart = (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap := by
  have h := congrArg linearPart (f.inverse_comp_cancel hf)
  rw [linearPart_comp, linearPart_id] at h
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply, ← LinearMap.comp_apply, h,
    LinearMap.id_apply]

/-- The linear part of the inverse is bijective. -/
theorem linearPart_inverse_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective (f.inverse hf).linearPart := by
  rw [linearPart_inverse]
  exact (LinearEquiv.ofBijective f.linearPart hf).symm.bijective

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
theorem inverse_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) (h : Function.Bijective (f.inverse hf).linearPart) :
    (f.inverse hf).inverse h = f :=
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
module morphism. -/
def IsIso (f : AInfinityRightModuleHom MM NN) : Prop :=
  ∃ g : AInfinityRightModuleHom NN MM, g.comp f = AInfinityRightModuleHom.id MM ∧
    f.comp g = AInfinityRightModuleHom.id NN

-- The body of `IsIso` is not exposed, so later modules can neither destructure an `IsIso`
-- hypothesis nor build one by anonymous constructor; this restatement is their access to it.
/-- A module morphism is an isomorphism exactly when it has a two-sided inverse. -/
theorem isIso_def (f : AInfinityRightModuleHom MM NN) :
    f.IsIso ↔ ∃ g : AInfinityRightModuleHom NN MM, g.comp f = AInfinityRightModuleHom.id MM ∧
      f.comp g = AInfinityRightModuleHom.id NN :=
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
theorem isIso_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : (f.inverse hf).IsIso :=
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

/-! ### Modules with vanishing unary operation -/

/-- Between right `A∞` modules with vanishing unary operation, a module morphism is a
quasi-isomorphism exactly when its linear part is bijective. -/
theorem isQuasiIso_iff_linearPart_bijective (hM : MM.differential = 0)
    (hN : NN.differential = 0) (f : AInfinityRightModuleHom MM NN) :
    f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  have hcM (x : M) : x ∈ MM.cycles := by
    rw [AInfinityRightModule.mem_cycles, hM, LinearMap.zero_apply]
  have hcN (y : N) : y ∈ NN.cycles := by
    rw [AInfinityRightModule.mem_cycles, hN, LinearMap.zero_apply]
  have hbM (x : M) : x ∈ MM.boundaries ↔ x = 0 := by
    simp [hM, eq_comm]
  have hbN (y : N) : y ∈ NN.boundaries ↔ y = 0 := by
    simp [hN, eq_comm]
  rw [isQuasiIso_iff]
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦
      (hbM x).1 (hi x (hcM x) ((hbN _).2 hx)), fun y ↦ ?_⟩
    obtain ⟨x, -, hx⟩ := hs y (hcN y)
    exact ⟨x, (sub_eq_zero.1 ((hbN _).1 hx)).symm⟩
  · rintro ⟨hi, hs⟩
    refine ⟨fun x _ hx ↦ (hbM x).2 ((injective_iff_map_eq_zero _).1 hi x ((hbN _).1 hx)),
      fun y _ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, hcM x, (hbN _).2 (sub_self _)⟩

/-- Between right `A∞` modules with vanishing unary operation, quasi-isomorphisms are exactly the
isomorphisms. -/
theorem isQuasiIso_iff_isIso (hM : MM.differential = 0) (hN : NN.differential = 0)
    (f : AInfinityRightModuleHom MM NN) : f.IsQuasiIso ↔ f.IsIso := by
  rw [isQuasiIso_iff_linearPart_bijective hM hN, isIso_iff_linearPart_bijective]

/-- A quasi-isomorphism between right `A∞` modules with vanishing unary operation is an
isomorphism. -/
theorem IsQuasiIso.isIso (hM : MM.differential = 0) (hN : NN.differential = 0)
    {f : AInfinityRightModuleHom MM NN} (hf : f.IsQuasiIso) : f.IsIso :=
  (isQuasiIso_iff_isIso hM hN f).1 hf

end AInfinityRightModuleHom

namespace AInfinityRightModuleCat

variable {M N : AInfinityRightModuleCat.{uR, uA, uM} AA}

/-- A morphism in the category of right `A∞` modules is an isomorphism exactly when its linear
part is bijective. -/
theorem isIso_iff_linearPart_bijective (f : M ⟶ N) :
    CategoryTheory.IsIso f ↔ Function.Bijective (AInfinityRightModuleHom.linearPart f) := by
  rw [← AInfinityRightModuleHom.isIso_iff_linearPart_bijective,
    AInfinityRightModuleHom.isIso_def]
  constructor
  · intro h
    refine ⟨CategoryTheory.inv f, ?_, ?_⟩
    · rw [← comp_def, CategoryTheory.IsIso.hom_inv_id, id_def]
    · rw [← comp_def, CategoryTheory.IsIso.inv_hom_id, id_def]
  · rintro ⟨g, hg₁, hg₂⟩
    exact ⟨g, by rw [comp_def, hg₁, id_def], by rw [comp_def, hg₂, id_def]⟩

end AInfinityRightModuleCat

end TauCeti
