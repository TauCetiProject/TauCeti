/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra
public import TauCeti.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback

/-!
# The conormal sheaf and the normal cone

Let `i : X ⟶ Y` be an immersion. It factors as a closed immersion `j = i.liftCoborder` of `X` into
the open subscheme `U = i.coborderRange` of `Y`, the largest open in which `X` is closed, followed
by the inclusion `U ⟶ Y`. Let `I = ker j ⊆ 𝒪_U` be the ideal sheaf of `X` in `U`; for a closed
immersion `U = Y` and `I` is the ideal sheaf of `X` in `Y`. Pulling back the Rees algebra
`⨁ₙ Iⁿ` of `I` along `j` gives the graded quasi-coherent `𝒪_X`-algebra

`j^* (⨁ₙ Iⁿ) = ⨁ₙ j^* Iⁿ = ⨁ₙ Iⁿ/Iⁿ⁺¹`,

the *normal cone algebra* of `i`, which is the associated graded algebra of `I`, read as an
algebra on `X`. Its degree-zero component is `j^* I⁰ = j^* 𝒪_U = 𝒪_X`
(`isIso_one_normalConeAlgebra`) and its degree-one component is the *conormal sheaf*
`j^* I = I/I²` of `i` (Stacks, Tag 01R1). The *normal cone* of `i` is the relative spectrum

`C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`,

an affine scheme over `X`; this is Fulton's normal cone.

The normal cone is the linear approximation of `Y` along `X` used in intersection theory: the
deformation to the normal cone degenerates `i` to the zero section `X ⟶ C_X Y`, and for a regular
immersion `C_X Y` is the normal bundle `Spec_X (Sym (I/I²))`, a vector bundle whose dual is the
conormal sheaf.

Working in `U` rather than `Y` makes these constructions correct for every immersion: the ideal
sheaf `ker i ⊆ 𝒪_Y` of the scheme-theoretic image restricts to `I` on `U` when `i` is
quasi-compact, but need not do so in general. For a quasi-compact immersion, in particular a closed
immersion, the components are therefore the pullbacks `i^* (ker i)ⁿ` along `i` itself
(`normalConeAlgebraObjXIsoPullbackKerPow`, `conormalObjIsoPullbackKer`).

Defining the normal cone algebra as a pullback of the Rees algebra makes it a graded
quasi-coherent algebra on `X` directly, with its algebra structure transported from that of
`⨁ₙ Iⁿ` by the strong monoidal pullback of quasi-coherent sheaves.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra i`: the graded quasi-coherent `𝒪_X`-algebra
  `⨁ₙ j^* Iⁿ = ⨁ₙ Iⁿ/Iⁿ⁺¹`.
* `AlgebraicGeometry.Scheme.Hom.conormal i`: the conormal sheaf `j^* I = I/I²`, as a
  quasi-coherent sheaf on `X`.
* `AlgebraicGeometry.Scheme.Hom.normalConeOver i`: the normal cone `Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`, as an
  affine scheme over `X`.
* `AlgebraicGeometry.Scheme.Hom.normalCone i` and
  `AlgebraicGeometry.Scheme.Hom.normalConeToBase i`: the normal cone and its projection to `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra_obj_X`: the homogeneous components of the
  normal cone algebra are the pullbacks `j^* Iⁿ`.
* `AlgebraicGeometry.Scheme.Hom.conormal_obj`: the conormal sheaf is the pullback `j^* I`, and
  `AlgebraicGeometry.Scheme.Hom.conormal_eq_degreeOne`: it is the degree-one component of the
  normal cone algebra.
* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebraObjXIsoPullbackKerPow` and
  `AlgebraicGeometry.Scheme.Hom.conormalObjIsoPullbackKer`: for a quasi-compact immersion, for
  instance a closed immersion, these components are `i^* (ker i)ⁿ` and `i^* (ker i)`.
* `AlgebraicGeometry.Scheme.Hom.isIso_one_normalConeAlgebra`: the unit `𝒪_X ⟶ j^* I⁰` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isAffineHom_normalConeToBase`: the projection of the normal cone
  is affine.
* `AlgebraicGeometry.Scheme.Hom.isZero_conormal`: an open immersion, for instance an
  isomorphism, has zero conormal sheaf; more generally all positive-degree components of its
  normal cone algebra vanish (`isZero_normalConeAlgebra_obj_X`).

## References

* W. Fulton, *Intersection Theory*, 2nd ed., §4.1 and Appendix B.6.
* [The Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1): the conormal sheaf
  of an immersion.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

noncomputable section

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]

/-- The normal cone algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of an immersion `i : X ⟶ Y`, where `I` is the ideal sheaf
of the closed immersion `j = i.liftCoborder` of `X` into the open `i.coborderRange` of `Y`: the
pullback `⨁ₙ j^* Iⁿ` along `j` of the Rees algebra `⨁ₙ Iⁿ` (`normalConeAlgebra_def`), i.e. the
associated graded algebra of `I`, as an algebra on `X`. -/
def normalConeAlgebra : GradedQuasicoherentAlgebra X :=
  (GradedQuasicoherentAlgebra.pullback i.liftCoborder).obj i.liftCoborder.ker.reesAlgebra

/-- The normal cone algebra is the pullback along `i.liftCoborder` of the Rees algebra of the
ideal sheaf `ker i.liftCoborder`. -/
theorem normalConeAlgebra_def :
    i.normalConeAlgebra =
      (GradedQuasicoherentAlgebra.pullback i.liftCoborder).obj i.liftCoborder.ker.reesAlgebra :=
  (rfl)

/-- The homogeneous components of the normal cone algebra are the pullbacks `j^* Iⁿ` of the
powers of the ideal sheaf `I = ker j` of `j = i.liftCoborder`. -/
@[simp]
theorem normalConeAlgebra_obj_X (n : ℕ) :
    i.normalConeAlgebra.obj.X n =
      (Scheme.Modules.pullback i.liftCoborder).obj (i.liftCoborder.ker ^ n).sheaf := by
  rw [normalConeAlgebra_def, GradedQuasicoherentAlgebra.pullback_obj_obj_X,
    IdealSheafData.reesAlgebra_obj_X]

/-- The unit `𝒪_X ⟶ j^* I⁰` of the normal cone algebra is an isomorphism: `I⁰ = 𝒪_U`, so the
degree-zero component `j^* I⁰` of the normal cone algebra is `j^* 𝒪_U = 𝒪_X`. -/
instance isIso_one_normalConeAlgebra : IsIso i.normalConeAlgebra.obj.toMon.one :=
  inferInstanceAs (IsIso ((GradedQuasicoherentAlgebra.pullback i.liftCoborder).obj
    i.liftCoborder.ker.reesAlgebra).obj.toMon.one)

/-- The conormal sheaf `j^* I = I/I²` of an immersion `i : X ⟶ Y`, where `I` is the ideal sheaf
of the closed immersion `j = i.liftCoborder` (Stacks, Tag 01R1), as a quasi-coherent sheaf on `X`.
It is the degree-one component of the normal cone algebra (`conormal_eq_degreeOne`). -/
def conormal : QuasicoherentSheaf X :=
  (GradedQuasicoherentAlgebra.degree 1).obj i.normalConeAlgebra

/-- The conormal sheaf is the degree-one component of the normal cone algebra. -/
theorem conormal_eq_degreeOne :
    i.conormal = GradedQuasicoherentAlgebra.degreeOne.obj i.normalConeAlgebra :=
  (rfl)

/-- The underlying module of the conormal sheaf is the pullback `j^* I` of the ideal sheaf
`I = ker j` of `j = i.liftCoborder`. -/
@[simp]
theorem conormal_obj :
    i.conormal.obj = (Scheme.Modules.pullback i.liftCoborder).obj i.liftCoborder.ker.sheaf := by
  rw [conormal_eq_degreeOne, GradedQuasicoherentAlgebra.degree_obj_obj, normalConeAlgebra_obj_X,
    pow_one]

section QuasiCompact

variable [QuasiCompact i]

/-- For a quasi-compact immersion `i`, for instance a closed immersion, the homogeneous components
of the normal cone algebra are the pullbacks `i^* (ker i)ⁿ` of the powers of the ideal sheaf of
`i`: the ideal sheaf `I` of `j = i.liftCoborder` is the restriction of `ker i`
(`ker_liftCoborder`), and pulling an ideal sheaf back along an open immersion is restricting
it. -/
def normalConeAlgebraObjXIsoPullbackKerPow (n : ℕ) :
    i.normalConeAlgebra.obj.X n ≅ (Scheme.Modules.pullback i).obj (i.ker ^ n).sheaf :=
  eqToIso (by rw [normalConeAlgebra_obj_X, ker_liftCoborder, ← IdealSheafData.comap_pow]) ≪≫
    (Scheme.Modules.pullback i.liftCoborder).mapIso
      (asIso ((i.ker ^ n).pullbackSheafHom i.coborderRange.ι)).symm ≪≫
    (Scheme.Modules.pullbackComp i.liftCoborder i.coborderRange.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr i.liftCoborder_ι).app _

/-- For a quasi-compact immersion `i`, for instance a closed immersion, the conormal sheaf is the
pullback `i^* (ker i)` of the ideal sheaf of `i`. -/
def conormalObjIsoPullbackKer : i.conormal.obj ≅ (Scheme.Modules.pullback i).obj i.ker.sheaf :=
  eqToIso (by rw [conormal_eq_degreeOne, GradedQuasicoherentAlgebra.degree_obj_obj]) ≪≫
    i.normalConeAlgebraObjXIsoPullbackKerPow 1 ≪≫ eqToIso (by rw [pow_one])

end QuasiCompact

/-- The normal cone `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` of an immersion `i : X ⟶ Y`, as an affine scheme
over `X`: the relative spectrum of the normal cone algebra (`normalConeOver_def`). -/
@[expose]
def normalConeOver : AffineSchemeOver X :=
  (relativeSpec X).obj
    (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra))

/-- The normal cone over `X` is the relative spectrum of the direct-sum algebra underlying the
normal cone algebra. -/
theorem normalConeOver_def :
    i.normalConeOver =
      (relativeSpec X).obj
        (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra)) :=
  rfl

/-- The normal cone `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` of an immersion `i : X ⟶ Y`. -/
@[expose]
def normalCone : Scheme.{u} :=
  i.normalConeOver.left

/-- The projection `C_X Y ⟶ X` of the normal cone. -/
@[expose]
def normalConeToBase : i.normalCone ⟶ X :=
  i.normalConeOver.hom

/-- The normal cone is the relative spectrum of the direct-sum algebra underlying the normal cone
algebra. -/
theorem normalCone_eq_relativeSpec :
    i.normalCone =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpec :=
  rfl

/-- The projection of the normal cone is the structure morphism of the relative spectrum. -/
theorem normalConeToBase_eq_relativeSpecToBase :
    i.normalConeToBase =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpecToBase :=
  rfl

/-- The projection of the normal cone is affine. -/
instance isAffineHom_normalConeToBase : IsAffineHom i.normalConeToBase :=
  inferInstanceAs (IsAffineHom i.normalConeOver.hom)

end

variable {X Y : Scheme.{u}} (i : X ⟶ Y)

/-- For an open immersion `i`, for instance an isomorphism, the positive-degree components
`j^* Iⁿ` of the normal cone algebra vanish: `j = i.liftCoborder` is then an open immersion as
well, and its ideal sheaf `I` has no nonzero sections over the image of `j`. -/
theorem isZero_normalConeAlgebra_obj_X [IsOpenImmersion i] {n : ℕ} (hn : n ≠ 0) :
    IsZero (i.normalConeAlgebra.obj.X n) := by
  rw [normalConeAlgebra_obj_X]
  set j := i.liftCoborder
  have : IsOpenImmersion (j ≫ i.coborderRange.ι) := by rw [i.liftCoborder_ι]; infer_instance
  have : IsOpenImmersion j := .of_comp j i.coborderRange.ι
  -- Pullback along the open immersion `j` is restriction, so it suffices that every section of
  -- `Iⁿ` over an open `j ''ᵁ U` in the image of `j` vanishes.
  refine IsZero.of_iso ?_ ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm
  refine (IsZero.iff_id_eq_zero _).mpr
    (Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
  change @Eq Γ((j.ker ^ n).sheaf, j ''ᵁ U) t 0
  have hle : j.ker ^ n ≤ j.ker := fun V ↦ by
    rw [IdealSheafData.ideal_pow, Pi.pow_apply]
    exact Ideal.pow_le_self hn
  have h0 := j.mem_ker_sections_iff.mp
    (IdealSheafData.sections_mono hle _ ((j.ker ^ n).sheafι_app_mem (j ''ᵁ U) t))
  have hinj : Function.Injective (j.app (j ''ᵁ U)) := by
    have := (ConcreteCategory.bijective_of_isIso (j.appIso U).hom).1
    rw [j.appIso_hom] at this
    exact fun a b hab ↦ this (by simp only [ConcreteCategory.comp_apply, hab])
  have h1 : (j.ker ^ n).sheafι.app (j ''ᵁ U) t = 0 := hinj (h0.trans (map_zero _).symm)
  exact (j.ker ^ n).sheafι_app_injective _ (h1.trans (map_zero _).symm)

/-- An open immersion, for instance an isomorphism, has zero conormal sheaf, as a sheaf of
modules. -/
theorem isZero_conormal_obj [IsOpenImmersion i] : IsZero i.conormal.obj := by
  rw [conormal_eq_degreeOne, GradedQuasicoherentAlgebra.degree_obj_obj]
  exact i.isZero_normalConeAlgebra_obj_X one_ne_zero

/-- An open immersion, for instance an isomorphism, has zero conormal sheaf. -/
theorem isZero_conormal [IsOpenImmersion i] : IsZero i.conormal :=
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ i.isZero_conormal_obj

end AlgebraicGeometry.Scheme.Hom
