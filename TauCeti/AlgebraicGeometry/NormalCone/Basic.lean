/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback

/-!
# The conormal sheaf and the normal cone

Let `i : X ⟶ Y` be a morphism of schemes with ideal sheaf `I = ker i ⊆ 𝒪_Y`; the case of interest
is a closed immersion, where `X = V(I)`. Pulling back the Rees algebra `⨁ₙ Iⁿ` of `I` along `i`
gives the graded quasi-coherent `𝒪_X`-algebra

`i^* (⨁ₙ Iⁿ) = ⨁ₙ i^* Iⁿ`,

the *normal cone algebra* of `i`. For a closed immersion `i^* Iⁿ = Iⁿ ⊗ 𝒪_Y/I = Iⁿ/Iⁿ⁺¹`, so this
is the associated graded algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of `I`, read as an algebra on `X`. Its
degree-zero component is `𝒪_X` (`isIso_one_normalConeAlgebra`) and its degree-one component is
the *conormal sheaf* `i^* I = I/I²` of `i`. The *normal cone* of `i` is the relative spectrum

`C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`,

an affine scheme over `X`.

Defining the associated graded algebra as a pullback of the Rees algebra makes it a graded
quasi-coherent algebra on `X` directly, with its algebra structure transported from that of
`⨁ₙ Iⁿ` by the strong monoidal pullback of quasi-coherent sheaves.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra i`: the graded quasi-coherent `𝒪_X`-algebra
  `⨁ₙ i^* Iⁿ = ⨁ₙ Iⁿ/Iⁿ⁺¹`.
* `AlgebraicGeometry.Scheme.Hom.conormal i`: the conormal sheaf `i^* I = I/I²`, as a quasi-coherent
  sheaf on `X`.
* `AlgebraicGeometry.Scheme.Hom.normalConeOver i`: the normal cone `Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)`, as an
  affine scheme over `X`.
* `AlgebraicGeometry.Scheme.Hom.normalCone i` and `AlgebraicGeometry.Scheme.Hom.normalConeProj i`:
  the normal cone and its projection to `X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalConeAlgebra_obj_X`: the homogeneous components of the
  normal cone algebra are the pullbacks `i^* Iⁿ`.
* `AlgebraicGeometry.Scheme.Hom.conormal_obj`: the conormal sheaf is the pullback `i^* I`, and
  `AlgebraicGeometry.Scheme.Hom.conormal_eq_degreeOne`: it is the degree-one component of the
  normal cone algebra.
* `AlgebraicGeometry.Scheme.Hom.isIso_one_normalConeAlgebra`: the unit `𝒪_X ⟶ i^* I⁰` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isAffineHom_normalConeProj`: the projection of the normal cone is
  affine.
* `AlgebraicGeometry.Scheme.Hom.isZero_conormal_of_isIso`: an isomorphism has zero conormal sheaf.

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

variable {X Y : Scheme.{u}} (i : X ⟶ Y)

/-- The normal cone algebra `⨁ₙ i^* Iⁿ` of a morphism `i : X ⟶ Y` with ideal sheaf `I = ker i`:
the pullback along `i` of the Rees algebra `⨁ₙ Iⁿ`. For a closed immersion, `i^* Iⁿ = Iⁿ/Iⁿ⁺¹`,
so this is the associated graded algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of `I`, as an algebra on `X`. -/
@[expose]
def normalConeAlgebra : GradedQuasicoherentAlgebra X :=
  (GradedQuasicoherentAlgebra.pullback i).obj i.ker.reesAlgebra

/-- The homogeneous components of the normal cone algebra are the pullbacks `i^* Iⁿ` of the
powers of the ideal sheaf `I = ker i`. -/
@[simp]
theorem normalConeAlgebra_obj_X (n : ℕ) :
    i.normalConeAlgebra.obj.X n = (Scheme.Modules.pullback i).obj (i.ker ^ n).sheaf := by
  rw [normalConeAlgebra, GradedQuasicoherentAlgebra.pullback_obj_obj_X,
    IdealSheafData.reesAlgebra_obj_X]

/-- The unit `𝒪_X ⟶ i^* I⁰` of the normal cone algebra is an isomorphism: the degree-zero
component of `⨁ₙ Iⁿ/Iⁿ⁺¹` is `𝒪_X`. -/
instance isIso_one_normalConeAlgebra : IsIso i.normalConeAlgebra.obj.toMon.one := by
  rw [normalConeAlgebra, GradedQuasicoherentAlgebra.pullback_obj_one]
  have : IsIso ((Scheme.Modules.pullback i).map i.ker.reesAlgebra.obj.toMon.one) :=
    Functor.map_isIso _ _
  -- The transport `eqToHom` is stated in the category of graded components, where instance
  -- search does not find `IsIso (eqToHom _)`, so it is supplied through `eqToIso`.
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this
    (eqToIso (GradedQuasicoherentAlgebra.pullback_obj_obj_X i _ 0).symm).isIso_hom)

/-- The conormal sheaf `i^* I` of a morphism `i : X ⟶ Y` with ideal sheaf `I = ker i`, as a
quasi-coherent sheaf on `X`. It is the degree-one component of the normal cone algebra
(`conormal_eq_degreeOne`). For a closed immersion, `i^* I = I/I²` (Stacks, Tag 01R1). -/
@[expose]
def conormal : QuasicoherentSheaf X :=
  (GradedQuasicoherentAlgebra.degree 1).obj i.normalConeAlgebra

/-- The conormal sheaf is the degree-one component of the normal cone algebra. -/
theorem conormal_eq_degreeOne :
    i.conormal = GradedQuasicoherentAlgebra.degreeOne.obj i.normalConeAlgebra :=
  rfl

/-- The underlying module of the conormal sheaf is the pullback `i^* I` of the ideal sheaf
`I = ker i`. -/
@[simp]
theorem conormal_obj : i.conormal.obj = (Scheme.Modules.pullback i).obj i.ker.sheaf := by
  rw [conormal, GradedQuasicoherentAlgebra.degree_obj_obj, normalConeAlgebra_obj_X, pow_one]

/-- The normal cone `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` of a morphism `i : X ⟶ Y`, as an affine scheme
over `X`: the relative spectrum of the normal cone algebra. -/
@[expose]
def normalConeOver : AffineSchemeOver X :=
  (relativeSpec X).obj
    (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj i.normalConeAlgebra))

/-- The normal cone `C_X Y = Spec_X (⨁ₙ Iⁿ/Iⁿ⁺¹)` of a morphism `i : X ⟶ Y`. -/
@[expose]
def normalCone : Scheme.{u} :=
  i.normalConeOver.left

/-- The projection `C_X Y ⟶ X` of the normal cone. -/
@[expose]
def normalConeProj : i.normalCone ⟶ X :=
  i.normalConeOver.hom

/-- The normal cone is the relative spectrum of the direct-sum algebra underlying the normal cone
algebra. -/
theorem normalCone_eq :
    i.normalCone =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpec :=
  rfl

/-- The projection of the normal cone is the structure morphism of the relative spectrum. -/
theorem normalConeProj_eq :
    i.normalConeProj =
      (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj
        i.normalConeAlgebra).obj.relativeSpecToBase :=
  rfl

/-- The projection of the normal cone is affine. -/
instance isAffineHom_normalConeProj : IsAffineHom i.normalConeProj :=
  inferInstanceAs (IsAffineHom i.normalConeOver.hom)

/-- An isomorphism has zero conormal sheaf: its ideal sheaf is `⊥`, whose sections vanish. -/
theorem isZero_conormal_of_isIso [IsIso i] : IsZero i.conormal.obj := by
  rw [conormal_obj, i.ker_eq_bot_of_isIso]
  -- Pullback is a left adjoint, so it preserves the zero object.
  refine (IsZero.isInitial ?_).isInitialObj (Scheme.Modules.pullback i) |>.isZero
  refine IsZero.of_mono_eq_zero (⊥ : Y.IdealSheafData).sheafι ?_
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  -- A section of `⊥` restricts to zero on every affine open, hence is zero.
  have ht := (⊥ : Y.IdealSheafData).sheafι_app_mem U t
  refine Y.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨V, hVU, hxV, ?_⟩
  have := (⊥ : Y.IdealSheafData).map_mem_sections (homOfLE hVU) ht
  rw [IdealSheafData.sections_eq_ideal _ ⟨V, hV⟩, IdealSheafData.ideal_bot, Pi.bot_apply,
    Ideal.mem_bot] at this
  exact this.trans (map_zero _).symm

end

end AlgebraicGeometry.Scheme.Hom
