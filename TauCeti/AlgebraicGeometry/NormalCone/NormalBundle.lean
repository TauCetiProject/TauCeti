/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.NormalCone.NormalSheaf
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.FunctorOfPoints

/-!
# The normal bundle as the total space of the dual of the conormal sheaf

Let `i : X ⟶ Y` be an immersion with conormal sheaf `I/I²`. Its normal sheaf is the relative
spectrum `N_X Y = Spec_X (Sym (I/I²))` (`AlgebraicGeometry.Scheme.Hom.normalSheafOver`). When
`I/I²` is finite locally free, as it is for a regular immersion, `N_X Y` is the vector bundle whose
sheaf of sections is the dual conormal sheaf `(I/I²)^∨`: it is the geometric total space
`𝕍((I/I²)^∨) = Spec_X (Sym (I/I²)^∨∨)` of `(I/I²)^∨` (`totalSpaceScheme`), by finite locally free
biduality `I/I² ≅ (I/I²)^∨∨` (`FiniteLocallyFreeSheaf.evalIso`). This is Fulton's normal bundle.

Consequently, for a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ N_X Y` over `X` are the global
sections of the pullback `q^* ((I/I²)^∨)` of the dual conormal sheaf (`normalSheafHomEquiv`),
naturally in `T` (`normalSheafHomEquiv_comp`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.normalSheafOverIsoTotalSpaceScheme`: if the conormal sheaf of `i`
  is the finite locally free sheaf `E`, the normal sheaf `Spec_X (Sym (I/I²))` is the total space
  of `E^∨`, as affine schemes over `X`.
* `AlgebraicGeometry.Scheme.Hom.normalSheafHomEquiv`: points of the normal sheaf over `X` are
  sections of the pullback of the dual conormal sheaf `E^∨`, naturally in the scheme over `X`
  (`AlgebraicGeometry.Scheme.Hom.normalSheafHomEquiv_comp`).

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1 and Appendix B.7.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

noncomputable section

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]

/-- **The normal bundle is the total space of the dual of the conormal sheaf.** If the conormal
sheaf `I/I²` of an immersion `i` is the finite locally free sheaf `E`, the normal sheaf
`Spec_X (Sym (I/I²))` is the total space `𝕍(E^∨) = Spec_X (Sym E^∨∨)` of the dual `E^∨`, as affine
schemes over `X`. It is the relative spectrum of the symmetric algebra of the biduality
isomorphism `E^∨∨ ≅ E ≅ I/I²`. -/
def normalSheafOverIsoTotalSpaceScheme (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) :
    i.normalSheafOver ≅ (totalSpaceScheme X).obj (dual E) :=
  (relativeSpec X).mapIso
    ((symmetricAlgebra X).mapIso ((toQuasicoherent X).mapIso (evalIso E).symm ≪≫ e)).op

/-- The isomorphism of the normal sheaf with the total space of `E^∨` is the relative spectrum of
the symmetric algebra of `E^∨∨ ≅ E ≅ I/I²`. -/
theorem normalSheafOverIsoTotalSpaceScheme_def (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) :
    i.normalSheafOverIsoTotalSpaceScheme E e = (relativeSpec X).mapIso
      ((symmetricAlgebra X).mapIso ((toQuasicoherent X).mapIso (evalIso E).symm ≪≫ e)).op :=
  (rfl)

/-- **Points of the normal sheaf are sections of the dual conormal sheaf.** If the conormal sheaf
of `i` is the finite locally free sheaf `E`, then for a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ N_X Y` over `X` are global sections `𝒪_T ⟶ q^* E^∨` of the pullback of the dual conormal
sheaf `E^∨`. -/
def normalSheafHomEquiv (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj i.normalSheafOver) ≃
      (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (dual E).obj) :=
  ((Iso.refl T).homCongr
    ((MorphismProperty.Over.forget _ _ X).mapIso (i.normalSheafOverIsoTotalSpaceScheme E e))).trans
    (totalSpaceHomEquiv (dual E) T)

/-- The section of a `T`-point `t : T ⟶ N_X Y` over `X` is the section of its image in the total
space of `E^∨`. -/
theorem normalSheafHomEquiv_apply (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj i.normalSheafOver) :
    i.normalSheafHomEquiv E e T t = totalSpaceHomEquiv (dual E) T
      (t ≫ (MorphismProperty.Over.forget _ _ X).map
        (i.normalSheafOverIsoTotalSpaceScheme E e).hom) := by
  simp [normalSheafHomEquiv]

/-- The `T`-point over `X` of a section `s` of `q^* E^∨` is the point of the total space of `E^∨`
given by `s`, followed by the inverse of the comparison isomorphism. -/
theorem normalSheafHomEquiv_symm_apply (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (dual E).obj) :
    (i.normalSheafHomEquiv E e T).symm s = (totalSpaceHomEquiv (dual E) T).symm s ≫
      (MorphismProperty.Over.forget _ _ X).map (i.normalSheafOverIsoTotalSpaceScheme E e).inv := by
  simp [normalSheafHomEquiv]

/-- **Naturality of the section correspondence in the scheme over `X`.** For a morphism
`g : T' ⟶ T` over `X`, the section of the `T'`-point `g ≫ t` of the normal sheaf is the pullback
along `g` of the section of `t`: the section `𝒪_{T'} ≅ g^* 𝒪_T ⟶ g^* q^* E^∨ ≅ q'^* E^∨`, through
the identification of the pulled-back structure sheaf and the composition isomorphism of
pullback. -/
theorem normalSheafHomEquiv_comp (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj i.normalSheafOver) :
    i.normalSheafHomEquiv E e T' (g ≫ t) =
      (Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map (i.normalSheafHomEquiv E e T t) ≫
          (Scheme.Modules.pullbackComp g.left T.hom).hom.app (dual E).obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (dual E).obj := by
  rw [normalSheafHomEquiv_apply, normalSheafHomEquiv_apply, Category.assoc,
    totalSpaceHomEquiv_comp]

/-- The point of the pulled-back section: precomposing the `T`-point of a section `s` of
`q^* E^∨` with `g : T' ⟶ T` over `X` gives the `T'`-point of the section
`𝒪_{T'} ≅ g^* 𝒪_T ⟶ g^* q^* E^∨ ≅ q'^* E^∨`. -/
theorem comp_normalSheafHomEquiv_symm_apply (E : FiniteLocallyFreeSheaf X)
    (e : (toQuasicoherent X).obj E ≅ i.conormal) {T' T : Over X} (g : T' ⟶ T)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (dual E).obj) :
    g ≫ (i.normalSheafHomEquiv E e T).symm s =
      (i.normalSheafHomEquiv E e T').symm ((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map s ≫
          (Scheme.Modules.pullbackComp g.left T.hom).hom.app (dual E).obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (dual E).obj) := by
  rw [Equiv.eq_symm_apply, normalSheafHomEquiv_comp, Equiv.apply_symm_apply]

end

end AlgebraicGeometry.Scheme.Hom
