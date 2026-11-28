/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Exact category of finite maximal Cohen–Macaulay modules

Over a local ring `R`, the finite maximal Cohen–Macaulay `R`-modules form an object property
`TauCeti.IsFiniteMaximalCohenMacaulay R` of `ModuleCat R` that contains zero and is closed under
isomorphisms, extensions, and binary products (and, over a Noetherian local ring, retracts).
Thus the full subcategory `TauCeti.MaximalCohenMacaulayModuleCat R` carries the induced exact
structure `TauCeti.MaximalCohenMacaulayModuleCat.exactStructure R`.

## References

* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Cambridge Univ. Press (1993), Section 2.1.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4.
-/

public section

universe v u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace TauCeti

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The object property on `ModuleCat R` selecting the finite maximal Cohen–Macaulay modules. -/
def IsFiniteMaximalCohenMacaulay : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Finite R M ∧ Module.IsMaximalCohenMacaulay R M

/-- Unfolds `TauCeti.IsFiniteMaximalCohenMacaulay`. -/
@[simp]
theorem isFiniteMaximalCohenMacaulay_iff (M : ModuleCat.{v} R) :
    IsFiniteMaximalCohenMacaulay.{v} R M ↔
      Module.Finite R M ∧ Module.IsMaximalCohenMacaulay R M := Iff.rfl

variable {R}

/-- Every zero `R`-module is a finite maximal Cohen–Macaulay module. -/
theorem isFiniteMaximalCohenMacaulay_of_isZero {M : ModuleCat.{v} R} (hM : IsZero M) :
    IsFiniteMaximalCohenMacaulay.{v} R M :=
  have := ModuleCat.subsingleton_of_isZero hM
  ⟨inferInstance, Module.isMaximalCohenMacaulay_of_subsingleton⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    isFiniteMaximalCohenMacaulay_of_isZero (ModuleCat.isZero_of_subsingleton _)⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).IsClosedUnderIsomorphisms where
  of_iso e hX :=
    have := hX.1
    ⟨Module.Finite.equiv e.toLinearEquiv, e.toLinearEquiv.isMaximalCohenMacaulay_iff.1 hX.2⟩

/-- Over a Cohen–Macaulay local ring, every finite projective `R`-module is maximal
Cohen–Macaulay. -/
theorem isFiniteMaximalCohenMacaulay_of_projective (hR : Module.IsCohenMacaulay R R)
    (M : ModuleCat.{v} R) [Module.Finite R M] [Projective M] :
    IsFiniteMaximalCohenMacaulay.{v} R M :=
  have : Module.Projective R M := (IsProjective.iff_projective M).2 inferInstance
  ⟨inferInstance, hR.isMaximalCohenMacaulay_of_projective M⟩

/-- Finite maximal Cohen–Macaulay modules over a local ring are closed under extensions. -/
theorem IsFiniteMaximalCohenMacaulay.isExtensionClosed :
    (ExactStructure.abelian (ModuleCat.{v} R)).IsExtensionClosed
      (IsFiniteMaximalCohenMacaulay.{v} R) where
  prop_X₂ {S} hS h₁ h₃ := by
    have hSE := (ExactStructure.abelian_conflation S).1 hS
    have := h₁.1; have := h₃.1
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hSE.exact
    have hsurj := (ModuleCat.epi_iff_surjective S.g).1 hSE.epi_g
    exact ⟨Module.Finite.of_exact hex hsurj,
      h₁.2.of_exact_middle hex ((ModuleCat.mono_iff_injective S.f).1 hSE.mono_f) hsurj h₃.2⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).IsClosedUnderBinaryProducts :=
  IsFiniteMaximalCohenMacaulay.isExtensionClosed.isClosedUnderBinaryProducts

/-- Any retract of a finite maximal Cohen–Macaulay module over a Noetherian local ring is again
finite and maximal Cohen–Macaulay. -/
theorem IsFiniteMaximalCohenMacaulay.of_retract [IsNoetherianRing R] {M N : ModuleCat.{v} R}
    (hN : IsFiniteMaximalCohenMacaulay.{v} R N) (r : Retract M N) :
    IsFiniteMaximalCohenMacaulay.{v} R M := by
  have := hN.1
  have hr : Function.Surjective r.r.hom :=
    Function.LeftInverse.surjective fun x ↦ ConcreteCategory.congr_hom r.retract x
  let s : (ShortComplex.mk (Limits.kernel.ι r.r) r.r (Limits.kernel.condition r.r)).Splitting :=
    .ofExactOfSection _ (ShortComplex.exact_kernel r.r) r.i r.retract inferInstance
  have hprod := (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have : Module.Finite R M := .of_surjective r.r.hom hr
  rw [isFiniteMaximalCohenMacaulay_iff, Module.isMaximalCohenMacaulay_iff_ringKrullDim_le_depth]
  refine ⟨‹_›, hN.2.ringKrullDim_le_depth.trans ?_⟩
  rw [depth_eq_of_linearEquiv hprod, depth_prod, WithBot.coe_inf]
  exact inf_le_right

instance [IsNoetherianRing R] : (IsFiniteMaximalCohenMacaulay.{v} R).IsStableUnderRetracts where
  of_retract r hN := hN.of_retract r

/-- The additive full subcategory of finitely generated maximal Cohen–Macaulay `R`-modules. -/
abbrev MaximalCohenMacaulayModuleCat (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R] :=
  (IsFiniteMaximalCohenMacaulay.{v} R).FullSubcategory

namespace MaximalCohenMacaulayModuleCat

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The exact structure on finite maximal Cohen–Macaulay `R`-modules inherited from
`ModuleCat R`. -/
noncomputable def exactStructure : ExactStructure (MaximalCohenMacaulayModuleCat.{v} R) :=
  (ExactStructure.abelian (ModuleCat.{v} R)).fullSubcategory
    (IsFiniteMaximalCohenMacaulay.{v} R) IsFiniteMaximalCohenMacaulay.isExtensionClosed

/-- Conflations in `MaximalCohenMacaulayModuleCat R` are the short exact sequences in
`ModuleCat R`. -/
@[simp]
theorem exactStructure_conflation_iff (S : ShortComplex (MaximalCohenMacaulayModuleCat.{v} R)) :
    (exactStructure.{v} R).Conflation S ↔
      (S.map (IsFiniteMaximalCohenMacaulay.{v} R).ι).ShortExact := by
  rw [exactStructure, ExactStructure.fullSubcategory_conflation_iff,
    ExactStructure.abelian_conflation]

end MaximalCohenMacaulayModuleCat
end TauCeti
