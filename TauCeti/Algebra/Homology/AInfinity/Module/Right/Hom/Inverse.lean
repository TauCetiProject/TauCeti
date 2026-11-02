/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology

/-!
# Inverses of right A-infinity module morphisms

A morphism of right A-infinity modules has a two-sided inverse precisely when its unary
component is bijective. This property is recorded by `TauCeti.AInfinityRightModuleHom.IsIso`.
The inverse bar map is the inverse of the original comodule map;
word-length triangularity establishes its bijectivity. The inverse preserves degree and
commutes with the bar differentials, so it is again a module morphism.

In particular such a morphism is a quasi-isomorphism. No field, finite-dimensionality,
completion or bound on the higher components is needed. Between minimal modules, whose unary
differentials vanish, quasi-isomorphisms have actual two-sided inverses. For general modules,
bijectivity of the unary component is stronger than being a quasi-isomorphism.

The inverse and its normal forms parallel the algebra API in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 4.
-/

public section

open scoped TensorProduct

namespace TauCeti.AInfinityRightModuleHom

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A}
  {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}

attribute [local instance] Comodule.cofree

/-- A module morphism with bijective unary component has a bijective bar map. -/
theorem barMap_bijective_of_linearPart_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective f.barMap :=
  TensorWords.bijective_of_tmul_one_eq f.barHom f.linearPart hf f.barMap_tmul_one

/-- The inverse of a right A-infinity module morphism whose unary component is bijective. -/
noncomputable def inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : AInfinityRightModuleHom NN MM where
  barHom := f.barHom.inverse (f.barMap_bijective_of_linearPart_bijective hf)
  isHomogeneous_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap]
    exact f.isHomogeneous_barMap.linearEquiv_symm
  barDifferential_comp_barMap := by
    apply LinearMap.ext
    intro z
    apply (f.barMap_bijective_of_linearPart_bijective hf).1
    simp only [LinearMap.comp_apply, Comodule.Hom.coe_toLinearMap,
      ← f.barDifferential_barMap, Comodule.Hom.apply_inverse_apply]

/-- The inverse module morphism has the inverse bar map. -/
@[simp]
theorem barMap_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).barMap =
      (LinearEquiv.ofBijective f.barMap (f.barMap_bijective_of_linearPart_bijective hf)).symm :=
  Comodule.Hom.inverse_toLinearMap f.barHom (f.barMap_bijective_of_linearPart_bijective hf)

/-- The constructed inverse is a left inverse. -/
@[simp]
theorem inverse_comp_cancel (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).comp f = AInfinityRightModuleHom.id MM := by
  apply barMap_injective
  apply LinearMap.ext
  intro z
  simp only [barMap_comp, barMap_id, barMap_inverse, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply, LinearMap.id_apply]

/-- The constructed inverse is a right inverse. -/
@[simp]
theorem comp_inverse_cancel (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    f.comp (f.inverse hf) = AInfinityRightModuleHom.id NN := by
  apply barMap_injective
  apply LinearMap.ext
  intro z
  simp only [barMap_comp, barMap_id, barMap_inverse, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, LinearMap.id_apply]

/-- The unary component of the inverse is the inverse of the unary component. -/
@[simp]
theorem linearPart_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).linearPart = (LinearEquiv.ofBijective f.linearPart hf).symm := by
  have h := linearPart_comp_eq_id_of_comp_eq_id (f.inverse_comp_cancel hf)
  ext y
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply,
    ← LinearMap.comp_apply, h, LinearMap.id_apply]

/-- The unary component of the inverse is bijective. -/
theorem linearPart_inverse_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective (f.inverse hf).linearPart := by
  rw [linearPart_inverse]
  exact (LinearEquiv.ofBijective f.linearPart hf).symm.bijective

/-- A left inverse of a module morphism with bijective unary component is its inverse. -/
theorem eq_inverse_of_comp_eq_id_left {f : AInfinityRightModuleHom MM NN}
    {g : AInfinityRightModuleHom NN MM} (hf : Function.Bijective f.linearPart)
    (h : g.comp f = AInfinityRightModuleHom.id MM) : g = f.inverse hf := by
  rw [← comp_id g, ← comp_inverse_cancel f hf, ← comp_assoc, h, id_comp]

/-- A right inverse of a module morphism with bijective unary component is its inverse. -/
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

/-- Inverting twice gives the original module morphism. -/
@[simp]
theorem inverse_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart)
    (h : Function.Bijective (f.inverse hf).linearPart) : (f.inverse hf).inverse h = f :=
  (eq_inverse_of_comp_eq_id_left h (comp_inverse_cancel f hf)).symm

/-- The inverse of a composite is the composite of the inverses in reverse order. -/
@[simp]
theorem inverse_comp {P : Type*} [AddCommGroup P] [Module R P]
    {PP : AInfinityRightModule AA P} (g : AInfinityRightModuleHom NN PP)
    (f : AInfinityRightModuleHom MM NN)
    (hg : Function.Bijective g.linearPart) (hf : Function.Bijective f.linearPart)
    (h : Function.Bijective (g.comp f).linearPart) :
    (g.comp f).inverse h = (f.inverse hf).comp (g.inverse hg) :=
  (eq_inverse_of_comp_eq_id_left h (by
    rw [comp_assoc, ← comp_assoc (g.inverse hg), inverse_comp_cancel, id_comp,
      inverse_comp_cancel])).symm

/-- A right A-infinity module morphism is an isomorphism when it has a two-sided inverse. -/
def IsIso (f : AInfinityRightModuleHom MM NN) : Prop :=
  ∃ g : AInfinityRightModuleHom NN MM,
    g.comp f = AInfinityRightModuleHom.id MM ∧ f.comp g = AInfinityRightModuleHom.id NN

/-- A module morphism is an isomorphism exactly when it has a two-sided inverse. -/
theorem isIso_def (f : AInfinityRightModuleHom MM NN) :
    f.IsIso ↔ ∃ g : AInfinityRightModuleHom NN MM,
      g.comp f = AInfinityRightModuleHom.id MM ∧
      f.comp g = AInfinityRightModuleHom.id NN :=
  Iff.rfl

/-- The identity module morphism is an isomorphism. -/
@[simp]
theorem isIso_id (MM : AInfinityRightModule AA M) : (AInfinityRightModuleHom.id MM).IsIso :=
  ⟨AInfinityRightModuleHom.id MM, comp_id _, comp_id _⟩

/-- Isomorphisms of right A-infinity modules are closed under composition. -/
theorem IsIso.comp {P : Type*} [AddCommGroup P] [Module R P]
    {PP : AInfinityRightModule AA P} {g : AInfinityRightModuleHom NN PP}
    {f : AInfinityRightModuleHom MM NN} (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g', hg₁, id_comp, hf₁]
  · rw [comp_assoc, ← comp_assoc f, hf₂, id_comp, hg₂]

/-- A module morphism with bijective unary component is an isomorphism. -/
theorem isIso_of_linearPart_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : f.IsIso :=
  ⟨f.inverse hf, f.inverse_comp_cancel hf, f.comp_inverse_cancel hf⟩

/-- The inverse of a module morphism with bijective unary component is an isomorphism. -/
theorem isIso_inverse (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : (f.inverse hf).IsIso :=
  ⟨f, f.comp_inverse_cancel hf, f.inverse_comp_cancel hf⟩

/-- The unary component of an isomorphism of right A-infinity modules is bijective. -/
theorem IsIso.linearPart_bijective {f : AInfinityRightModuleHom MM NN} (h : f.IsIso) :
    Function.Bijective f.linearPart := by
  obtain ⟨g, hgf, hfg⟩ := h
  apply Function.bijective_iff_has_inverse.2
  refine ⟨g.linearPart, fun x ↦ ?_, fun y ↦ ?_⟩
  · exact LinearMap.congr_fun (linearPart_comp_eq_id_of_comp_eq_id hgf) x
  · exact LinearMap.congr_fun (linearPart_comp_eq_id_of_comp_eq_id hfg) y

/-- A module morphism is an isomorphism exactly when its unary component is bijective. -/
theorem isIso_iff_linearPart_bijective (f : AInfinityRightModuleHom MM NN) :
    f.IsIso ↔ Function.Bijective f.linearPart :=
  ⟨IsIso.linearPart_bijective, f.isIso_of_linearPart_bijective⟩

/-- A module morphism with bijective unary component is a quasi-isomorphism. -/
theorem isQuasiIso_of_linearPart_bijective (f : AInfinityRightModuleHom MM NN)
    (hf : Function.Bijective f.linearPart) : f.IsQuasiIso := by
  apply (isQuasiIso_def f).2
  apply Function.bijective_iff_has_inverse.2
  refine ⟨(f.inverse hf).cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, inverse_comp_cancel,
      cohomologyMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, comp_inverse_cancel,
      cohomologyMap_id, LinearMap.id_apply]

/-- An isomorphism of right A-infinity modules is a quasi-isomorphism. -/
theorem IsIso.isQuasiIso {f : AInfinityRightModuleHom MM NN} (h : f.IsIso) : f.IsQuasiIso :=
  f.isQuasiIso_of_linearPart_bijective h.linearPart_bijective

/-- Between modules with zero unary differentials, a quasi-isomorphism has bijective unary
component. Thus minimal modules admit actual inverses rather than only homotopy inverses. -/
theorem isQuasiIso_iff_linearPart_bijective_of_differential_eq_zero
    (f : AInfinityRightModuleHom MM NN) (hM : MM.differential = 0)
    (hN : NN.differential = 0) : f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  rw [isQuasiIso_iff, Function.Bijective, injective_iff_map_eq_zero]
  simp only [AInfinityRightModule.cycles_def, AInfinityRightModule.boundaries_def,
    hM, hN, LinearMap.ker_zero, LinearMap.range_zero, Submodule.mem_top,
    Submodule.mem_bot, true_implies, true_and, sub_eq_zero]
  simp only [Function.Surjective, eq_comm]

/-- Every quasi-isomorphism between minimal right A-infinity modules has a two-sided inverse. -/
theorem isIso_iff_isQuasiIso_of_differential_eq_zero
    (f : AInfinityRightModuleHom MM NN) (hM : MM.differential = 0)
    (hN : NN.differential = 0) :
    f.IsIso ↔ f.IsQuasiIso := by
  rw [isIso_iff_linearPart_bijective,
    isQuasiIso_iff_linearPart_bijective_of_differential_eq_zero f hM hN]

end TauCeti.AInfinityRightModuleHom
