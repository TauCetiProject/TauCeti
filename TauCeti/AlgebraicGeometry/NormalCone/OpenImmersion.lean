/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.NormalCone.NormalSheaf
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties

/-!
# Normal cones of open immersions

For an open immersion `i : X ⟶ Y`, for instance the identity, the ideal sheaf of `X` in the open
`i.coborderRange` is zero, so the normal cone algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` is `𝒪_X` in degree zero and
vanishes in positive degrees, and the conormal sheaf `I/I²` vanishes
(`AlgebraicGeometry.Scheme.Hom.isZero_conormal`), so that its symmetric algebra is also `𝒪_X` in
degree zero and vanishes in positive degrees
(`TauCeti.AlgebraicGeometry.isZero_gradedSymmetricAlgebra_obj_X`). Hence both the normal cone
`C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` and the normal sheaf `N_X Y = Spec_X (Sym (I/I²))` project
isomorphically onto `X` (`isIso_normalConeToBase`, `isIso_normalSheafToBase`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_normalConeToBase`: the normal cone of an open immersion
  projects isomorphically onto the source.
* `AlgebraicGeometry.Scheme.Hom.isIso_normalSheafToBase`: so does its normal sheaf.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1.
-/

public section

open CategoryTheory Limits

universe u

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

end AlgebraicGeometry.Scheme.Hom
