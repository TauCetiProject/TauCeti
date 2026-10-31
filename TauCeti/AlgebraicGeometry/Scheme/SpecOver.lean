/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Morphisms of affine schemes over an affine base

For commutative `R`-algebras `A` and `B`, the scheme `Spec B` is a scheme over `Spec R` through
Mathlib's `AlgebraicGeometry.specOverSpec`. This file identifies the morphisms
`Spec B ⟶ Spec A` over `Spec R`, in the vocabulary `Scheme.Hom.IsOver` of schemes over a base,
with the `R`-algebra homomorphisms `A →ₐ[R] B`. It is the `OverClass` form of Mathlib's
`AlgebraicGeometry.Spec.homEquivAlgHom`, whose compatibility condition is the explicit equation
of structure morphisms.

In particular, for a field `K`, the `K`-points of an affine `K`-scheme `Spec A` in the
functor-of-points sense, the morphisms `Spec K ⟶ Spec A` over `Spec K`, are the
`K`-algebra homomorphisms `A →ₐ[K] K`. A bare scheme morphism `Spec K ⟶ Spec A` is a ring
homomorphism `A →+* K` and need not be `K`-linear.

A morphism `Spec B ⟶ X` over `Spec R` whose image lies in an affine open `Spec A ⟶ X` over
`Spec R` factors through it by an `R`-algebra homomorphism `A →ₐ[R] B`.

For an arbitrary scheme `q : T ⟶ Spec R`, a morphism `f : T ⟶ Spec A` lies over `Spec R`
exactly when the ring map `A ⟶ Γ(T, ⊤)` of `f` restricts along `R ⟶ A` to the ring map
`R ⟶ Γ(T, ⊤)` of `q` (`TauCeti.AlgebraicGeometry.comp_spec_map_eq_iff`). Hence for an
`R`-algebra `A`, such morphisms are the `R`-algebra homomorphisms `A →ₐ[R] Γ(T, ⊤)`, where `R` acts
on global functions through `q` (`TauCeti.AlgebraicGeometry.overHomSpecEquivAlgHom`).

## Main declarations

* `TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom`: morphisms `Spec B ⟶ Spec A` over `Spec R`
  are the `R`-algebra homomorphisms `A →ₐ[R] B`.
* `TauCeti.AlgebraicGeometry.exists_spec_map_comp_eq_of_range_subset`: a morphism over `Spec R`
  with image in an affine open over `Spec R` factors through it by an algebra homomorphism.
* `TauCeti.AlgebraicGeometry.comp_spec_map_eq_iff`: a morphism `T ⟶ Spec A` lies over `Spec R`
  if and only if its ring map `A ⟶ Γ(T, ⊤)` is compatible with `R`.
* `TauCeti.AlgebraicGeometry.overHomSpecEquivAlgHom`: for an `R`-algebra `A`, morphisms
  `T ⟶ Spec A` over `Spec R` are the `R`-algebra homomorphisms `A →ₐ[R] Γ(T, ⊤)`.
-/

public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Morphisms `Spec B ⟶ Spec A` over `Spec R` are the `R`-algebra homomorphisms `A →ₐ[R] B`.
This is Mathlib's `AlgebraicGeometry.Spec.homEquivAlgHom`, with the compatibility with the
structure morphisms expressed by `Scheme.Hom.IsOver`. -/
noncomputable def specOverHomEquivAlgHom :
    {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))} ≃ (A →ₐ[R] B) :=
  (Equiv.subtypeEquivRight fun f ↦ by
    rw [Scheme.Hom.isOver_iff, specOverSpec_over, specOverSpec_over]).trans
    Spec.homEquivAlgHom

/-- The inverse of `specOverHomEquivAlgHom` applies `Spec` to an algebra homomorphism. -/
@[simp]
theorem coe_specOverHomEquivAlgHom_symm_apply (φ : A →ₐ[R] B) :
    (specOverHomEquivAlgHom.symm φ).1 = Spec.map (CommRingCat.ofHom (φ : A →+* B)) :=
  (rfl)

/-- Applying `Spec` to the algebra homomorphism of a morphism over `Spec R` recovers the
morphism. -/
@[simp]
theorem spec_map_specOverHomEquivAlgHom
    (f : {f : Spec (.of B) ⟶ Spec (.of A) // f.IsOver (Spec (.of R))}) :
    Spec.map (CommRingCat.ofHom (specOverHomEquivAlgHom f : A →+* B)) = f.1 := by
  rw [← coe_specOverHomEquivAlgHom_symm_apply, Equiv.symm_apply_apply]

/-- A morphism `p : Spec B ⟶ X` over `Spec R` whose image lies in the image of an open immersion
`f : Spec A ⟶ X` over `Spec R` factors through `f` by an `R`-algebra homomorphism
`A →ₐ[R] B`. -/
theorem exists_spec_map_comp_eq_of_range_subset {X : Scheme.{u}} [X.Over (Spec (.of R))]
    (f : Spec (.of A) ⟶ X) [IsOpenImmersion f] [f.IsOver (Spec (.of R))]
    (p : Spec (.of B) ⟶ X) [p.IsOver (Spec (.of R))] (h : Set.range p ⊆ Set.range f) :
    ∃ φ : A →ₐ[R] B, Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = p := by
  have hlift : (IsOpenImmersion.lift f p h).IsOver (Spec (.of R)) := by
    rw [Scheme.Hom.isOver_iff, ← comp_over f, IsOpenImmersion.lift_fac_assoc, comp_over]
  refine ⟨specOverHomEquivAlgHom ⟨_, hlift⟩, ?_⟩
  rw [AlgHom.toRingHom_eq_coe, spec_map_specOverHomEquivAlgHom, IsOpenImmersion.lift_fac]

/-- A morphism `f : T ⟶ Spec A` lies over `Spec R`, for the structure map `Spec A ⟶ Spec R` of a
ring map `π : R ⟶ A` and a morphism `q : T ⟶ Spec R`, exactly when the ring map `A ⟶ Γ(T, ⊤)` of
`f` restricts along `π` to the ring map `R ⟶ Γ(T, ⊤)` of `q`. -/
theorem comp_spec_map_eq_iff {T : Scheme.{u}} {R A : CommRingCat.{u}} (π : R ⟶ A)
    (f : T ⟶ Spec A) (q : T ⟶ Spec R) :
    f ≫ Spec.map π = q ↔
      π ≫ (Scheme.ΓSpecIso A).inv ≫ f.appTop = (Scheme.ΓSpecIso R).inv ≫ q.appTop := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ ext_to_Spec h⟩

/-- **Points of `Spec A` over `Spec R`.** For an `R`-algebra `A` and a scheme `q : T ⟶ Spec R`,
morphisms `T ⟶ Spec A` over `Spec R` correspond to `R`-algebra homomorphisms `A →ₐ[R] Γ(T, ⊤)`,
where `R` acts on global functions through `q`. A morphism goes to its ring map
`A ⟶ Γ(T, ⊤)`; an algebra homomorphism goes to its adjoint under the Γ–Spec adjunction. -/
noncomputable def overHomSpecEquivAlgHom {R : CommRingCat.{u}} (A : Type u) [CommRing A]
    [Algebra R A] (T : Over (Spec R)) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    (T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ≃
      (A →ₐ[R] Γ(T.left, ⊤)) :=
  letI := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
  { toFun t :=
      { ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop).hom with
        commutes' := ConcreteCategory.congr_hom
          ((comp_spec_map_eq_iff (R := R) _ t.left T.hom).mp (Over.w t)) }
    invFun φ := Over.homMk (ΓSpec.adjunction.homEquiv T.left (Opposite.op (.of A))
        (CommRingCat.ofHom φ.toRingHom).op) <| by
      refine (comp_spec_map_eq_iff (R := R) _ _ T.hom).mpr ?_
      rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
      ext r
      exact φ.commutes r
    left_inv t := Over.OverMorphism.ext (ext_to_Spec (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _))
    right_inv φ := AlgHom.ext fun a ↦ ConcreteCategory.congr_hom
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := T.left) (CommRingCat.ofHom φ.toRingHom)) a }

/-- The `R`-algebra homomorphism of a point `t : T ⟶ Spec A` over `Spec R` is its ring map
`A ⟶ Γ(T, ⊤)`. -/
lemma overHomSpecEquivAlgHom_apply {R : CommRingCat.{u}} (A : Type u) [CommRing A]
    [Algebra R A] (T : Over (Spec R))
    (t : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (a : A) :
    overHomSpecEquivAlgHom A T t a = ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop) a :=
  (rfl)

/-- The point of `Spec A` over `Spec R` of an `R`-algebra homomorphism `φ : A →ₐ[R] Γ(T, ⊤)` has
ring map `φ`. -/
lemma overHomSpecEquivAlgHom_symm_appTop {R : CommRingCat.{u}} (A : Type u) [CommRing A]
    [Algebra R A] (T : Over (Spec R)) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    ∀ φ : A →ₐ[R] Γ(T.left, ⊤), (Scheme.ΓSpecIso _).inv ≫
      ((overHomSpecEquivAlgHom A T).symm φ).left.appTop = CommRingCat.ofHom φ.toRingHom :=
  fun _ ↦ ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The bijection `overHomSpecEquivAlgHom` is natural in the scheme over `Spec R`: composing a
point with `g : T' ⟶ T` composes its algebra homomorphism with pullback of functions along `g`. -/
lemma overHomSpecEquivAlgHom_comp {R : CommRingCat.{u}} (A : Type u) [CommRing A] [Algebra R A]
    {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (a : A) :
    overHomSpecEquivAlgHom A T' (g ≫ t) a = g.left.appTop (overHomSpecEquivAlgHom A T t a) := by
  rw [overHomSpecEquivAlgHom_apply, overHomSpecEquivAlgHom_apply, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.comp_apply]

end TauCeti.AlgebraicGeometry
