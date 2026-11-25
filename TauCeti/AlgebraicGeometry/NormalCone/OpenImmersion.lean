/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.NormalCone.NormalSheaf
public import TauCeti.AlgebraicGeometry.RelativeSpec.Trivial

/-!
# Normal cones of open immersions and of empty sources

For an open immersion `i : X ⟶ Y`, for instance the identity, the ideal sheaf of `X` in the open
`i.coborderRange` is zero, so the normal cone algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` is `𝒪_X` in degree zero and
vanishes in positive degrees, and the conormal sheaf `I/I²` vanishes
(`AlgebraicGeometry.Scheme.Hom.isZero_conormal`). Hence both the normal cone
`C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` and the normal sheaf `N_X Y = Spec_X (Sym (I/I²))` project
isomorphically onto `X` (`isIso_normalConeToBase`, `isIso_normalSheafToBase`). The symmetric
algebra of a zero sheaf is `𝒪_X` in degree zero and vanishes in positive degrees
(`TauCeti.AlgebraicGeometry.isZero_gradedSymmetricAlgebra_obj_X`), since its multiplications
`Symⁿ F ⊗ F ⟶ Symⁿ⁺¹ F` are epimorphisms.

An immersion with empty source has empty normal cone and empty normal sheaf, since both lie over
the source.

These are Checks of the normal cone in SchemeAndStackFoundations §5.5 (Fulton, *Intersection
Theory*, §4.1).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_normalConeToBase`: the normal cone of an open immersion
  projects isomorphically onto the source.
* `AlgebraicGeometry.Scheme.Hom.isIso_normalSheafToBase`: so does its normal sheaf.
* `AlgebraicGeometry.Scheme.Hom.isEmpty_normalCone` and
  `AlgebraicGeometry.Scheme.Hom.isEmpty_normalSheaf`: an immersion with empty source has empty
  normal cone and empty normal sheaf.
* `TauCeti.AlgebraicGeometry.isZero_gradedSymmetricAlgebra_obj_X`: the symmetric powers of
  positive degree of a zero sheaf vanish.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1.
-/

public section

open CategoryTheory Limits MonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The symmetric powers `Symⁿ F` of positive degree of a zero quasicoherent sheaf `F` vanish:
the multiplication `Symⁿ⁻¹ F ⊗ F ⟶ Symⁿ F` is an epimorphism out of a zero sheaf. -/
theorem isZero_gradedSymmetricAlgebra_obj_X {F : QuasicoherentSheaf X} (hF : IsZero F.obj)
    {n : ℕ} (hn : n ≠ 0) : IsZero (((gradedSymmetricAlgebra X).obj F).obj.X n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  set A := ((gradedSymmetricAlgebra X).obj F).obj
  have h1 : IsZero (A.X 1) := hF.of_iso (gradedSymmetricAlgebraXOneIso F)
  have h : IsZero (A.X m ⊗ A.X 1) := by
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.whiskerLeft_id, h1.eq_of_src (𝟙 _) 0,
      MonoidalPreadditive.whiskerLeft_zero]
  -- The epimorphism instance is passed explicitly: instance search does not find it for the
  -- multiplication as elaborated here.
  exact @IsZero.of_epi _ _ _ _ _ _ (epi_mul_gradedSymmetricAlgebra F m 1) h

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (i : X ⟶ Y)

/-- **The normal cone of an open immersion is its source.** For an open immersion `i`, for
instance the identity, the projection `C_X Y ⟶ X` of the normal cone is an isomorphism: the
normal cone algebra is `𝒪_X` in degree zero and vanishes in positive degrees. -/
instance isIso_normalConeToBase [IsOpenImmersion i] : IsIso i.normalConeToBase := by
  have := GradedQuasicoherentAlgebra.isIso_one_toQuasicoherentAlgebra i.normalConeAlgebra
    fun _ hn ↦ i.isZero_normalConeAlgebra_obj_X hn
  rw [normalConeToBase_eq_relativeSpecToBase]
  exact CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one _

/-- **The normal sheaf of an open immersion is its source.** For an open immersion `i`, for
instance the identity, the projection `N_X Y ⟶ X` of the normal sheaf `Spec_X (Sym (I/I²))` is an
isomorphism: the conormal sheaf vanishes, so its symmetric algebra is `𝒪_X`. -/
instance isIso_normalSheafToBase [IsOpenImmersion i] : IsIso i.normalSheafToBase := by
  have := GradedQuasicoherentAlgebra.isIso_one_toQuasicoherentAlgebra
    ((gradedSymmetricAlgebra X).obj i.conormal)
    fun _ hn ↦ isZero_gradedSymmetricAlgebra_obj_X i.isZero_conormal_obj hn
  rw [normalSheafToBase_eq_relativeSpecToBase]
  exact CategoryTheory.CommMon.isIso_relativeSpecToBase_of_isIso_one _

/-- An immersion with empty source has empty normal cone, which lies over the source. -/
instance isEmpty_normalCone [IsImmersion i] [IsEmpty X] : IsEmpty i.normalCone :=
  ⟨fun x ↦ isEmptyElim (i.normalConeToBase x)⟩

/-- An immersion with empty source has empty normal sheaf, which lies over the source. -/
instance isEmpty_normalSheaf [IsImmersion i] [IsEmpty X] : IsEmpty i.normalSheaf :=
  ⟨fun x ↦ isEmptyElim (i.normalSheafToBase x)⟩

end AlgebraicGeometry.Scheme.Hom
