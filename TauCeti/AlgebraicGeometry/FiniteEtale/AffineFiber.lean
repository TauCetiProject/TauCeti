/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Geometric fibres of spectra of finite étale algebras

Let `R` be a commutative ring and `Ω` a separably closed field which is an `R`-algebra, so that
`x : Spec Ω ⟶ Spec R` is a geometric point of `Spec R`. For a finite étale `R`-algebra `A`, the
geometric fibre of `Spec A ⟶ Spec R` at `x` is the finite set `A →ₐ[R] Ω` of `Ω`-valued points
of `A`, naturally in `A`: a point of the fibre is a lift of `x` to `Spec A`, and such lifts are
spectra of `R`-algebra maps `A → Ω`. In other words, the composite of the spectrum functor
`TauCeti.FiniteEtaleScheme.spec R` with the geometric fibre functor at `x` is Mathlib's fibre
functor `CommAlgCat.FiniteEtale.fiber R Ω` on finite étale algebras
(`TauCeti.FiniteEtaleScheme.specCompFiberIso`).

This computes geometric fibres, and hence actions of étale fundamental groups, on finite étale
covers given by explicit algebras over an affine base, without passing through the
classification of finite étale schemes over `Spec Ω`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.algSpecCompCoyonedaIso`: lifts of `x` to the spectrum of a finite
  étale `R`-algebra `A` are the `R`-algebra maps `A →ₐ[R] Ω`, naturally in `A`.
* `TauCeti.FiniteEtaleScheme.specCompFiberIso`: the geometric fibre at `x` of `Spec A` is
  `A →ₐ[R] Ω`, naturally in the finite étale `R`-algebra `A`.

## Main results

* `TauCeti.FiniteEtaleScheme.algSpec_map_specCompFiberIso_hom_app`: the algebra map attached to a
  point of the fibre has the corresponding lift of `x` as its spectrum.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace TauCeti.FiniteEtaleScheme

variable (R : CommRingCat.{u}) (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- The lifts of the point `Spec Ω ⟶ Spec R` to the spectrum of a finite étale `R`-algebra `A`
are the `R`-algebra maps `A →ₐ[R] Ω`, naturally in `A`. This is
`TauCeti.AlgebraicGeometry.algSpecHomEquivAlgHom` on finite étale algebras. -/
noncomputable def algSpecCompCoyonedaIso :
    (CommAlgCat.finiteEtale R).ι.op ⋙ algSpec R ⋙
        coyoneda.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) ≅
      CommAlgCat.FiniteEtale.fiber R Ω ⋙ FintypeCat.incl :=
  NatIso.ofComponents
    (fun A ↦ (AlgebraicGeometry.algSpecHomEquivAlgHom A.unop.obj (.of R Ω)).toIso)
    fun {A B} f ↦ by
      ext g
      suffices AlgebraicGeometry.algSpecHomEquivAlgHom B.unop.obj (.of R Ω)
          (g ≫ (algSpec _).map f.unop.hom.op) =
            (AlgebraicGeometry.algSpecHomEquivAlgHom A.unop.obj (.of R Ω) g).comp
              f.unop.hom.hom by
        simpa
      exact AlgebraicGeometry.algSpecHomEquivAlgHom_comp (A := A.unop.obj) (B := .of R Ω)
        f.unop.hom g

/-- The components of `algSpecCompCoyonedaIso` are `algSpecHomEquivAlgHom`. -/
theorem algSpecCompCoyonedaIso_hom_app_apply (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ)
    (g : ((CommAlgCat.finiteEtale R).ι.op ⋙ algSpec R ⋙
        coyoneda.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))).obj A) :
    (algSpecCompCoyonedaIso R Ω).hom.app A g =
      AlgebraicGeometry.algSpecHomEquivAlgHom A.unop.obj (.of R Ω) g :=
  (rfl)

variable [IsSepClosed Ω]

/-- The underlying isomorphism of types of `specCompFiberIso`. -/
private noncomputable def specCompFiberCompInclIso :
    (spec R ⋙ fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) ⋙ FintypeCat.incl ≅
      CommAlgCat.FiniteEtale.fiber R Ω ⋙ FintypeCat.incl :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (spec R) (fiberCompInclIso _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    -- `spec R` followed by the inclusion into `Over (Spec R)` is `algSpec R` (`spec_comp_ι`).
    Functor.isoWhiskerRight (eqToIso (spec_comp_ι R)) _ ≪≫ Functor.associator _ _ _ ≪≫
    algSpecCompCoyonedaIso R Ω

/-- **The geometric fibre of the spectrum of a finite étale algebra is its set of
`Ω`-points.** For a separably closed `R`-algebra `Ω`, the geometric fibre at
`Spec Ω ⟶ Spec R` of the spectrum of a finite étale `R`-algebra `A` is the finite set
`A →ₐ[R] Ω`, naturally in `A`. A point of the fibre goes to the `R`-algebra map whose spectrum
is the corresponding lift of the geometric point (`algSpec_map_specCompFiberIso_hom_app`). -/
noncomputable def specCompFiberIso :
    spec R ⋙ fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≅
      CommAlgCat.FiniteEtale.fiber R Ω :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl (specCompFiberCompInclIso R Ω)

/-- The algebra map that `specCompFiberIso` attaches to a point `y` of the geometric fibre of
`Spec A` has as spectrum the lift of the geometric point to `Spec A` given by `y`. -/
theorem algSpec_map_specCompFiberIso_hom_app (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj ((spec R).obj A)) :
    (algSpec R).map (CommAlgCat.ofHom ((specCompFiberIso R Ω).hom.app A y)).op =
      (fiberCompInclIso _).hom.app ((spec R).obj A) y ≫ eqToHom (spec_obj_obj R A) := by
  have h : (specCompFiberIso R Ω).hom.app A y = (specCompFiberCompInclIso R Ω).hom.app A y := by
    have := FintypeCat.incl.map_preimage ((specCompFiberCompInclIso R Ω).hom.app A)
    rw [ObjectProperty.ι_map] at this
    rw [specCompFiberIso, Functor.fullyFaithfulCancelRight_hom_app, ← FintypeCat.hom_apply, this]
  rw [h]
  -- Unfolding `specCompFiberCompInclIso`, the algebra map is `algSpecHomEquivAlgHom` of the lift.
  simp only [specCompFiberCompInclIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, eqToIso.hom, NatTrans.comp_app, Functor.comp_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, eqToHom_app, Category.id_comp, comp_apply]
  rw [algSpecCompCoyonedaIso_hom_app_apply]
  exact AlgebraicGeometry.algSpec_map_algSpecHomEquivAlgHom _

/-- The geometric fibre at `Spec Ω ⟶ Spec R` of the spectrum of a finite étale `R`-algebra `A` is
the set `A →ₐ[R] Ω`. This is the component of `specCompFiberIso` at `A`, as an equivalence of
types. -/
noncomputable def specFiberEquiv (A : CommAlgCat.FiniteEtale.{u} R) :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj ((spec R).obj (op A)) ≃
      (A.obj →ₐ[R] Ω) :=
  FintypeCat.equivEquivIso.symm ((specCompFiberIso R Ω).app (op A))

/-- `specFiberEquiv` is the component of `specCompFiberIso`. -/
theorem specFiberEquiv_apply (A : CommAlgCat.FiniteEtale.{u} R)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj ((spec R).obj (op A))) :
    specFiberEquiv R Ω A y = (specCompFiberIso R Ω).hom.app (op A) y :=
  (rfl)

/-- **Naturality of `specFiberEquiv`.** On geometric fibres, the spectrum of a map `f : A ⟶ B` of
finite étale `R`-algebras acts on `Ω`-points by precomposition with `f`. -/
@[simp]
theorem specFiberEquiv_map {A B : CommAlgCat.FiniteEtale.{u} R} (f : A ⟶ B)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj ((spec R).obj (op B))) :
    specFiberEquiv R Ω A ((fiber _).map ((spec R).map f.op) y) =
      (specFiberEquiv R Ω B y).comp f.hom.hom :=
  ConcreteCategory.congr_hom ((specCompFiberIso R Ω).hom.naturality f.op) y

end TauCeti.FiniteEtaleScheme
