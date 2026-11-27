/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Banding
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Cover
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Local
public import TauCeti.CategoryTheory.Sites.Whiskering

/-!
# The coefficients of a banding are the intrinsic central sections

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a gerbe for a Grothendieck topology `J` and `b` an
`A`-banding of `F` by a sheaf of abelian groups `A`. Every coefficient `a ∈ A(U)` gives an intrinsic
central section `c_b(U)(a) ∈ ZF(U)` (`AbelianBanding.centerFromBanding`, `BandCenter/Banding.lean`).
This file shows that `c_b(U) : A(U) →* ZF(U)` is a group isomorphism for every `U`, including those
over which the fibre of `F` is empty (`AbelianBanding.centerFromBandingEquiv`).

* **Injectivity** (`AbelianBanding.centerFromBanding_injective`): on a covering sieve over whose
  arrows the fibre is nonempty, `c_b` evaluates to band automorphisms of the restricted
  coefficients, and `A` is separated.
* **Local coefficients** (`AbelianBanding.localCoefficient`): for any sieve `R` on `U` with an
  object `x_f` over the source of each arrow `f ∈ R`, the coefficients
  `a_f = b(V, x_f)⁻¹ (ev_(f, x_f)(z))` of a section `z ∈ ZF(U)` recover the restrictions of `z`
  (`AbelianBanding.centerFromBanding_localCoefficient`) and form a compatible family
  (`AbelianBanding.localCoefficient_compatible`), with no compatibility between the chosen
  objects and no cover condition.
* **Surjectivity** (`AbelianBanding.centerFromBanding_surjective`): on a covering sieve with local
  objects, the local coefficients glue in the sheaf `A`, and the glued coefficient maps to `z`
  since central sections are separated. When an object `x` over `U` is given, the preimage of `z`
  is `b(U, x)⁻¹ (ev_(𝟙, x)(z))` directly (`AbelianBanding.centerFromBanding_surjective_of_object`).

This is the sectionwise part of the comparison between the coefficient sheaf of a banding and the
intrinsic band in the varying-base step of the Stacks Project, Lemma 8.11.8 (06NY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `localCoefficient`: the family `a_f` of local coefficients of a central section.
* `centerFromBandingEquiv`: the group isomorphism `A(U) ≃* ZF(U)` with forward map `c_b(U)`.

## Main results

* `centerFromBanding_injective`, `centerFromBanding_surjective`,
  `centerFromBanding_surjective_of_object`.
* `centerFromBanding_mulEquiv_symm_evaluation`: `c_b(V)(b(V, x)⁻¹ (ev_(f, x)(z))) = r_f(z)`.
* `centerFromBanding_localCoefficient`, `localCoefficient_compatible`.
* `centerFromBandingEquiv_symm_restrict`,
  `centerFromBandingEquiv_symm_restrict_eq_mulEquiv_symm_evaluation`: the inverse commutes with
  restriction, and its restriction along `f` is the local coefficient at any object over the source
  of `f`.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)

/-- The **local coefficients** of a central section `z ∈ ZF(U)` along a sieve `R` on `U`, given an
object `x_f` over the source of every arrow `f ∈ R`: the coefficient `b(V, x_f)⁻¹ (ev_(f, x_f)(z))`
at `f : V ⟶ U`. -/
noncomputable def localCoefficient {U : C} (R : Sieve U)
    (xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V))) (z : IntrinsicBandSections F U) :
    Presieve.FamilyOfElements (A.obj ⋙ forget AddCommGrpCat) R.arrows :=
  fun V f hf ↦ Multiplicative.toAdd
    ((b.mulEquiv V (xs f hf)).symm (IntrinsicBandSections.evaluation f (xs f hf) z))

theorem localCoefficient_apply {U : C} (R : Sieve U)
    (xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V))) (z : IntrinsicBandSections F U)
    {V : C} (f : V ⟶ U) (hf : R f) :
    b.localCoefficient R xs z f hf =
      Multiplicative.toAdd
        ((b.mulEquiv V (xs f hf)).symm (IntrinsicBandSections.evaluation f (xs f hf) z)) :=
  (rfl)

variable [F.IsGerbe J]

/-- **The coefficient map of a banding is injective** at every `U`, even when the fibre of `F`
over `U` is empty. -/
theorem centerFromBanding_injective (U : C) : Function.Injective (b.centerFromBanding U) := by
  intro a a' h
  obtain ⟨R, hR, hne⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
  have hA := (A.isSheaf_obj_comp (forget AddCommGrpCat)).isSeparated R hR
  refine Multiplicative.toAdd.injective (hA.ext fun V f hf ↦ ?_)
  obtain ⟨x⟩ := hne f hf
  have hx := congrArg (IntrinsicBandSections.evaluation f x) h
  rw [evaluation_centerFromBanding, evaluation_centerFromBanding] at hx
  exact congrArg Multiplicative.toAdd ((b.mulEquiv V x).injective hx)

/-- **Recovering a restriction from a local coefficient.** For `f : V ⟶ U`, an object `x` over `V`
and `z ∈ ZF(U)`, the central section of the coefficient `b(V, x)⁻¹ (ev_(f, x)(z))` is the
restriction `r_f(z)`. -/
theorem centerFromBanding_mulEquiv_symm_evaluation {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op V)))
    (z : IntrinsicBandSections F U) :
    b.centerFromBanding V ((b.mulEquiv V x).symm (IntrinsicBandSections.evaluation f x z)) =
      restrict f z := by
  refine evaluation_injective (J := J) x ?_
  rw [evaluation_centerFromBanding, evaluation_restrict, Category.id_comp]
  simp

/-- **Surjectivity at an object.** If `x` is an object over `U`, every `z ∈ ZF(U)` is the
central section of the coefficient `b(U, x)⁻¹ (ev_(𝟙, x)(z))`. -/
theorem centerFromBanding_surjective_of_object {U : C} (x : F.obj (.mk (op U))) :
    Function.Surjective (b.centerFromBanding U) :=
  fun z ↦ ⟨_, (b.centerFromBanding_mulEquiv_symm_evaluation (𝟙 U) x z).trans (restrict_id z)⟩

/-- **Local recovery.** The central section of the local coefficient at `f ∈ R` is `r_f(z)`. -/
theorem centerFromBanding_localCoefficient {U : C} (R : Sieve U)
    (xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V))) (z : IntrinsicBandSections F U)
    {V : C} (f : V ⟶ U) (hf : R f) :
    b.centerFromBanding V (Multiplicative.ofAdd (b.localCoefficient R xs z f hf)) =
      restrict f z :=
  b.centerFromBanding_mulEquiv_symm_evaluation f (xs f hf) z

/-- **The local coefficients are compatible**, with no compatibility between the chosen objects,
no fibre products and no cover condition on `R`. -/
theorem localCoefficient_compatible {U : C} (R : Sieve U)
    (xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V))) (z : IntrinsicBandSections F U) :
    (b.localCoefficient R xs z).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  refine Multiplicative.ofAdd.injective (b.centerFromBanding_injective Z ?_)
  refine (b.restrict_centerFromBanding g₁ (.ofAdd (b.localCoefficient R xs z f₁ h₁))).symm.trans
    (Eq.trans ?_ (b.restrict_centerFromBanding g₂ (.ofAdd (b.localCoefficient R xs z f₂ h₂))))
  rw [centerFromBanding_localCoefficient, centerFromBanding_localCoefficient, restrict_comp,
    restrict_comp, comm]

/-- **The coefficient map of a banding is surjective** at every `U`, even when the fibre of `F`
over `U` is empty: the local coefficients of a section on a covering sieve with local objects glue
in the sheaf `A`. -/
theorem centerFromBanding_surjective (U : C) : Function.Surjective (b.centerFromBanding U) := by
  intro z
  obtain ⟨R, hR, hne⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
  let xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V)) := fun _ f hf ↦ (hne f hf).some
  have hA := A.isSheaf_obj_comp (forget AddCommGrpCat) R hR
  have hc := b.localCoefficient_compatible R xs z
  refine ⟨Multiplicative.ofAdd (hA.amalgamate _ hc), eq_of_restrict_eq hR fun V f hf ↦ ?_⟩
  rw [restrict_centerFromBanding, ← b.centerFromBanding_localCoefficient R xs z f hf]
  exact congrArg (fun t ↦ b.centerFromBanding V (Multiplicative.ofAdd t))
    (hA.valid_glue hc f hf)

/-- **The coefficients of a banding are the intrinsic central sections**: the group isomorphism
`A(U) ≃* ZF(U)` whose forward map is `c_b(U)`. -/
noncomputable def centerFromBandingEquiv (U : C) :
    Multiplicative (A.obj.obj (op U)) ≃* IntrinsicBandSections F U :=
  MulEquiv.ofBijective (b.centerFromBanding U)
    ⟨b.centerFromBanding_injective U, b.centerFromBanding_surjective U⟩

@[simp]
theorem centerFromBandingEquiv_apply (U : C) (a : Multiplicative (A.obj.obj (op U))) :
    b.centerFromBandingEquiv U a = b.centerFromBanding U a :=
  (rfl)

@[simp]
theorem centerFromBanding_centerFromBandingEquiv_symm (U : C) (z : IntrinsicBandSections F U) :
    b.centerFromBanding U ((b.centerFromBandingEquiv U).symm z) = z :=
  (b.centerFromBandingEquiv U).apply_symm_apply z

@[simp]
theorem centerFromBandingEquiv_symm_centerFromBanding (U : C)
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.centerFromBandingEquiv U).symm (b.centerFromBanding U a) = a :=
  (b.centerFromBandingEquiv U).symm_apply_apply a

/-- **The inverse commutes with restriction**: the coefficient of `r_f(z)` is the restriction of
the coefficient of `z`. -/
theorem centerFromBandingEquiv_symm_restrict {U V : C} (f : V ⟶ U)
    (z : IntrinsicBandSections F U) :
    (b.centerFromBandingEquiv V).symm (restrict f z) =
      Multiplicative.ofAdd (A.obj.map f.op ((b.centerFromBandingEquiv U).symm z).toAdd) := by
  rw [MulEquiv.symm_apply_eq, centerFromBandingEquiv_apply, ← restrict_centerFromBanding,
    centerFromBanding_centerFromBandingEquiv_symm]

/-- **The inverse restricts to the local coefficients**: for `f : V ⟶ U` and any object `x` over
`V`, the coefficient of `r_f(z)` is `b(V, x)⁻¹ (ev_(f, x)(z))`. -/
theorem centerFromBandingEquiv_symm_restrict_eq_mulEquiv_symm_evaluation {U V : C} (f : V ⟶ U)
    (x : F.obj (.mk (op V))) (z : IntrinsicBandSections F U) :
    (b.centerFromBandingEquiv V).symm (restrict f z) =
      (b.mulEquiv V x).symm (IntrinsicBandSections.evaluation f x z) := by
  rw [MulEquiv.symm_apply_eq, centerFromBandingEquiv_apply,
    centerFromBanding_mulEquiv_symm_evaluation]

end CategoryTheory.Pseudofunctor.AbelianBanding
