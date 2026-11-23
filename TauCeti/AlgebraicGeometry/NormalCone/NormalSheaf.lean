/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Surjective
public import TauCeti.AlgebraicGeometry.NormalCone.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.ClosedImmersion
public import TauCeti.AlgebraicGeometry.VectorBundle.LinearScheme

/-!
# The normal sheaf and the closed embedding of the normal cone

Let `i : X ⟶ Y` be an immersion, with ideal sheaf `I` of the closed immersion
`j = i.liftCoborder` of `X` into the open `i.coborderRange` of `Y`. The *normal sheaf* of `i` is the
relative spectrum

`N_X Y = Spec_X (Sym (I/I²))`

of the symmetric algebra of the conormal sheaf `I/I²`, the linear scheme `𝕍(I/I²)` of the conormal
sheaf (`normalSheafOver_eq_linearSpec`). It is the abelian cone `C(I/I²)` of Behrend and Fantechi
and, for a regular immersion, Fulton's normal bundle.

The identity of `I/I²`, which is the degree-one component of the normal cone algebra
`⨁ₙ Iⁿ/Iⁿ⁺¹`, extends to a morphism of graded algebras

`Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`

(`symmetricAlgebraToNormalConeAlgebra`), and this morphism is surjective: the Rees algebra
`⨁ₙ Iⁿ` is generated in degree one (`IdealSheafData.isGeneratedInDegreeOne_reesAlgebra`), so
`Sym I ⟶ ⨁ₙ Iⁿ` is surjective, and the normal cone algebra is its pullback along `j`, as is
`Sym (I/I²) = Sym (j^* I)`. Taking relative spectra, the normal cone is a closed subscheme of the
normal sheaf:

`C_X Y ↪ N_X Y`

over `X` (`isClosedImmersion_normalConeToNormalSheaf`), the relative spectrum of the morphism of
direct sums underlying `symmetricAlgebraToNormalConeAlgebra`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.symmetricAlgebraToNormalConeAlgebra i`: the surjection of graded
  algebras `Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`.
* `AlgebraicGeometry.Scheme.Hom.normalSheafOver i`: the normal sheaf `Spec_X (Sym (I/I²))`, as an
  affine scheme over `X`, and `AlgebraicGeometry.Scheme.Hom.normalSheaf i` with its projection
  `AlgebraicGeometry.Scheme.Hom.normalSheafToBase i`.
* `AlgebraicGeometry.Scheme.Hom.normalConeToNormalSheafOver i` and
  `AlgebraicGeometry.Scheme.Hom.normalConeToNormalSheaf i`: the embedding `C_X Y ⟶ N_X Y` of the
  normal cone into the normal sheaf, over `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.epi_toQuasicoherentAlgebra_map_symmetricAlgebraToNormalConeAlgebra`:
  the morphism of direct sums `⨁ₙ Symⁿ (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.isClosedImmersion_normalConeToNormalSheaf`: the normal cone is a
  closed subscheme of the normal sheaf.
* `AlgebraicGeometry.Scheme.Hom.normalConeToNormalSheaf_normalSheafToBase`: the embedding is a
  morphism over `X`.

## References

* K. Behrend and B. Fantechi, *The intrinsic normal cone*, Invent. Math. 128 (1997), §1, where
  the normal sheaf `N_{X/Y} = C(I/I²)` and the closed embedding `C_{X/Y} ↪ N_{X/Y}` appear.
* W. Fulton, *Intersection Theory*, 2nd ed., §4.1 and Appendix B.6.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry GradedQuasicoherentAlgebra

noncomputable section

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]

/-- The morphism of graded algebras `Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` extending the identification of the
conormal sheaf `I/I²` with the degree-one component of the normal cone algebra
(`conormal_eq_degreeOne`). It is surjective
(`epi_toQuasicoherentAlgebra_map_symmetricAlgebraToNormalConeAlgebra`). -/
def symmetricAlgebraToNormalConeAlgebra :
    (gradedSymmetricAlgebra X).obj i.conormal ⟶ i.normalConeAlgebra :=
  gradedSymmetricAlgebraLift (eqToHom i.conormal_eq_degreeOne)

/-- `Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` is the extension to the symmetric algebra of the identification of
`I/I²` with the degree-one component of the normal cone algebra. -/
theorem symmetricAlgebraToNormalConeAlgebra_def :
    i.symmetricAlgebraToNormalConeAlgebra =
      gradedSymmetricAlgebraLift (eqToHom i.conormal_eq_degreeOne) :=
  (rfl)

/-- In degree one, `Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` is the identification `Sym¹ (I/I²) ≅ I/I²` followed by
the identification of `I/I²` with the degree-one component of the normal cone algebra. -/
@[simp]
theorem degreeOne_map_symmetricAlgebraToNormalConeAlgebra :
    degreeOne.map i.symmetricAlgebraToNormalConeAlgebra =
      (gradedSymmetricAlgebraDegreeOneIso X).hom.app i.conormal ≫
        eqToHom i.conormal_eq_degreeOne :=
  ((gradedSymmetricAlgebraDegreeOneIso X).app i.conormal).inv_comp_eq.mp
    (gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift _)

/-- **`Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` is surjective.** The morphism of direct sums
`⨁ₙ Symⁿ (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹` is an epimorphism of module sheaves: it is the pullback along
`j = i.liftCoborder` of `⨁ₙ Symⁿ I ⟶ ⨁ₙ Iⁿ`, which is surjective because the Rees algebra is
generated in degree one. -/
instance epi_toQuasicoherentAlgebra_map_symmetricAlgebraToNormalConeAlgebra :
    Epi (toQuasicoherentAlgebra.map i.symmetricAlgebraToNormalConeAlgebra).hom.hom.hom := by
  have h : Epi (toQuasicoherentAlgebra.map
      (gradedSymmetricAlgebraLift (𝟙 (degreeOne.obj i.normalConeAlgebra)))).hom.hom.hom := by
    rw [normalConeAlgebra_def]
    exact epi_toQuasicoherentAlgebra_map_gradedSymmetricAlgebraLift_pullback _ _
      (epi_toQuasicoherentAlgebra_map_gradedSymmetricAlgebraLift _
        i.liftCoborder.ker.isGeneratedInDegreeOne_reesAlgebra)
  -- The extension of the identification `I/I² = (⨁ₙ Iⁿ/Iⁿ⁺¹)₁` is the extension of the identity.
  have key {F : QuasicoherentSheaf X} (e : F = degreeOne.obj i.normalConeAlgebra) :
      Epi (toQuasicoherentAlgebra.map (gradedSymmetricAlgebraLift (eqToHom e))).hom.hom.hom := by
    subst e
    exact h
  exact key _

/-- The normal sheaf `N_X Y = Spec_X (Sym (I/I²))` of an immersion `i : X ⟶ Y`, as an affine
scheme over `X`: the relative spectrum of the symmetric algebra of the conormal sheaf. -/
@[expose]
def normalSheafOver : AffineSchemeOver X :=
  (relativeSpec X).obj (op ((symmetricAlgebra X).obj i.conormal))

/-- The normal sheaf over `X` is the relative spectrum of the symmetric algebra of the conormal
sheaf. -/
theorem normalSheafOver_def :
    i.normalSheafOver = (relativeSpec X).obj (op ((symmetricAlgebra X).obj i.conormal)) :=
  (rfl)

/-- The normal sheaf over `X` is the linear scheme `𝕍(I/I²)` of the conormal sheaf, with its
grading forgotten. -/
theorem normalSheafOver_eq_linearSpec :
    i.normalSheafOver =
      (QuasicoherentLinearScheme.forget X).obj ((linearSpec X).obj (op i.conormal)) :=
  (rfl)

/-- The normal sheaf `N_X Y = Spec_X (Sym (I/I²))` of an immersion `i : X ⟶ Y`. -/
@[expose]
def normalSheaf : Scheme.{u} :=
  i.normalSheafOver.left

/-- The projection `N_X Y ⟶ X` of the normal sheaf. -/
@[expose]
def normalSheafToBase : i.normalSheaf ⟶ X :=
  i.normalSheafOver.hom

/-- The normal sheaf is the relative spectrum of the symmetric algebra of the conormal sheaf. -/
theorem normalSheaf_eq_relativeSpec :
    i.normalSheaf = ((symmetricAlgebra X).obj i.conormal).obj.relativeSpec :=
  (rfl)

/-- The projection of the normal sheaf is the structure morphism of the relative spectrum. -/
theorem normalSheafToBase_eq_relativeSpecToBase :
    i.normalSheafToBase = ((symmetricAlgebra X).obj i.conormal).obj.relativeSpecToBase :=
  (rfl)

/-- The projection of the normal sheaf is affine. -/
instance isAffineHom_normalSheafToBase : IsAffineHom i.normalSheafToBase :=
  inferInstanceAs (IsAffineHom i.normalSheafOver.hom)

/-- The embedding `C_X Y ⟶ N_X Y` of the normal cone into the normal sheaf, as a morphism of affine
schemes over `X`: the relative spectrum of `Sym (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`. -/
def normalConeToNormalSheafOver : i.normalConeOver ⟶ i.normalSheafOver :=
  (relativeSpec X).map (toQuasicoherentAlgebra.map i.symmetricAlgebraToNormalConeAlgebra).op

/-- The embedding of the normal cone into the normal sheaf, over `X`, is the relative spectrum of
the morphism of direct sums `⨁ₙ Symⁿ (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`. -/
theorem normalConeToNormalSheafOver_def :
    i.normalConeToNormalSheafOver =
      (relativeSpec X).map (toQuasicoherentAlgebra.map i.symmetricAlgebraToNormalConeAlgebra).op :=
  (rfl)

/-- The embedding `C_X Y ⟶ N_X Y` of the normal cone into the normal sheaf. -/
def normalConeToNormalSheaf : i.normalCone ⟶ i.normalSheaf :=
  i.normalConeToNormalSheafOver.left

/-- The underlying scheme morphism of the embedding over `X` is `normalConeToNormalSheaf`. -/
@[simp]
theorem normalConeToNormalSheafOver_left :
    i.normalConeToNormalSheafOver.left = i.normalConeToNormalSheaf :=
  (rfl)

/-- The embedding of the normal cone into the normal sheaf is the relative spectrum of the
morphism of direct sums `⨁ₙ Symⁿ (I/I²) ⟶ ⨁ₙ Iⁿ/Iⁿ⁺¹`. -/
theorem normalConeToNormalSheaf_eq_relativeSpecMap :
    i.normalConeToNormalSheaf =
      CommMon.relativeSpecMap
        (toQuasicoherentAlgebra.map i.symmetricAlgebraToNormalConeAlgebra).hom :=
  (rfl)

/-- The embedding of the normal cone into the normal sheaf is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem normalConeToNormalSheaf_normalSheafToBase :
    i.normalConeToNormalSheaf ≫ i.normalSheafToBase = i.normalConeToBase :=
  CommMon.relativeSpecMap_relativeSpecToBase _

/-- **The normal cone is a closed subscheme of the normal sheaf.** For an immersion `i : X ⟶ Y`,
the embedding `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹) ⟶ Spec_X (Sym (I/I²)) = N_X Y` is a closed immersion. -/
instance isClosedImmersion_normalConeToNormalSheaf :
    IsClosedImmersion i.normalConeToNormalSheaf := by
  rw [normalConeToNormalSheaf_eq_relativeSpecMap]
  exact CommMon.isClosedImmersion_relativeSpecMap_of_epi _

end

end AlgebraicGeometry.Scheme.Hom
