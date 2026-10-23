/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential

/-!
# Strict morphisms preserve the bar differential split

A strict morphism commutes separately with the unary and higher parts of the bar differential.
Thus it respects the perturbation of the letterwise differential used in homological transfer.
This separate compatibility is specific to strict morphisms; arbitrary higher morphisms need
not preserve tensor length.
-/

public section

namespace TauCeti.AInfinityStrictHom

open ReducedTensorWords

universe uR uA uB

variable {R : Type uR} [CommRing R]
  {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- A strict morphism intertwines the unary bar differentials. -/
theorem unaryBarDifferential_comp_barMap (f : AInfinityStrictHom 𝒜 ℬ) :
    ℬ.unaryBarDifferential ∘ₗ f.barMap = f.barMap ∘ₗ 𝒜.unaryBarDifferential := by
  have hF : IsCoalgHom R f.barMap := by
    rw [barMap_def]
    exact isCoalgHom_map f.toLinearMap
  refine hF.comp_eq_comp_of_letter_comp_eq
    f.isHomogeneous_barMap 𝒜.isGradedCoderivation_unaryBarDifferential
      ℬ.isGradedCoderivation_unaryBarDifferential ?_
  simp only [← LinearMap.comp_assoc]
  rw [AInfinityAlgebra.letter_comp_unaryBarDifferential, barMap_def, letter_comp_map]
  simp only [LinearMap.comp_assoc]
  rw [AInfinityAlgebra.letter_comp_unaryBarDifferential]
  apply LinearMap.ext
  intro x
  have hℓ := LinearMap.congr_fun (letter_comp_map (R := R) f.toLinearMap) x
  simp only [LinearMap.comp_apply] at hℓ
  simp only [LinearMap.comp_apply, AInfinityAlgebra.taylor_ofLetter, hℓ, coe_toLinearMap]
  exact (f.map_m_one (letter R A x)).symm

/-- A strict morphism intertwines the higher bar perturbations. -/
theorem higherBarDifferential_comp_barMap (f : AInfinityStrictHom 𝒜 ℬ) :
    ℬ.higherBarDifferential ∘ₗ f.barMap = f.barMap ∘ₗ 𝒜.higherBarDifferential := by
  have h := f.barDifferential_comp_barMap
  have h₁ := f.unaryBarDifferential_comp_barMap
  simp only [AInfinityAlgebra.barDifferential_eq_unary_add_higher,
    LinearMap.add_comp, LinearMap.comp_add, h₁] at h
  apply LinearMap.ext
  intro x
  exact add_left_cancel (LinearMap.congr_fun h x)

end TauCeti.AInfinityStrictHom
