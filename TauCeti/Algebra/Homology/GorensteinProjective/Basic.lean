/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed

/-!
# The additive category of Gorenstein-projective modules

The direct sum of two complete resolutions is again a complete resolution. Consequently,
Gorenstein-projective modules contain the zero module and are closed under binary biproducts.
Their full subcategory of modules is therefore additive; this is the ambient category on which
the inherited exact structure and the Frobenius structure will be constructed.

## Main declarations

* `TauCeti.IsGorensteinProjective.biprod`: binary biproducts preserve
  Gorenstein-projectivity.
* `TauCeti.GorensteinProjectiveModuleCat`: the additive full subcategory of
  Gorenstein-projective modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- Every zero module is Gorenstein-projective. -/
theorem isGorensteinProjective_of_isZero {M : ModuleCat.{v} A} (hM : IsZero M) :
    IsGorensteinProjective A M := by
  have := ModuleCat.subsingleton_of_isZero hM
  have : Module.Finite A M := inferInstance
  have := hM.projective
  exact isGorensteinProjective_of_projective M

/-- A binary biproduct of Gorenstein-projective modules is Gorenstein-projective. -/
theorem IsGorensteinProjective.biprod {M N : ModuleCat.{v} A}
    (hM : IsGorensteinProjective A M) (hN : IsGorensteinProjective A N) :
    IsGorensteinProjective A (M ⊞ N) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isGorensteinProjective_iff M).mp hM
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := (isGorensteinProjective_iff N).mp hN
  let F := HomologicalComplex.cyclesFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0
  let _ : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let _ : PreservesBiproductsOfShape WalkingPair F := inferInstance
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  apply (isGorensteinProjective_iff (M ⊞ N)).mpr
  exact ⟨P ⊞ Q, hP.biprod hQ,
    ⟨F.mapBiprod P Q ≪≫ biprod.mapIso eP eQ⟩⟩

instance : (IsGorensteinProjective.{v} A).ContainsZero where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    isGorensteinProjective_of_isZero (ModuleCat.isZero_of_subsingleton _)⟩

instance : (IsGorensteinProjective.{v} A).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ ↦
    IsGorensteinProjective.biprod

/-- The additive category of finitely generated Gorenstein-projective `A`-modules. -/
abbrev GorensteinProjectiveModuleCat (A : Type u) [Ring A] :=
  (IsGorensteinProjective.{v} A).FullSubcategory

end TauCeti
