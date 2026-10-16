/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Assoc
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Comm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Unit
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange

/-!
# The projective Weierstrass model as a commutative monoid object

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model and let `S = Spec R`. Group schemes over `S` are group objects in the cartesian
monoidal category `Over S`, whose tensor product is the fibre product over `S`. This file makes
`E`, as the object `Over.mk W.projModelOver` of `Over S`, a commutative monoid object: the unit is
the zero section `[0 : 1 : 0]` and the multiplication is the Bosma–Lenstra addition morphism
`E ×_S E ⟶ E`. The monoid axioms are the unit laws, associativity and commutativity of the
addition morphism, read through the description of the cartesian monoidal structure of `Over S`
by fibre products (`CategoryTheory.Over.lift_left` and its companions).

The monoid object is compatible with base change. For a ring homomorphism `f : R →+* R'`, the
projective model of `W.map f` over `Spec R'` is isomorphic, as an object of `Over (Spec R')`, to the
image of `Over.mk W.projModelOver` under the pullback functor along `Spec f`
(`WeierstrassCurve.projModelOverBaseChangeIso`, from the base change square
`WeierstrassCurve.isPullback_projModelBaseChange`). The pullback functor carries the
monoid object of `W` to a monoid object over `Spec R'` (`CategoryTheory.Functor.monObjObj`), and
the isomorphism is a homomorphism of monoid objects.

## Main definitions

* `WeierstrassCurve.monObjProjModelOver`: the monoid object structure on `Over.mk W.projModelOver`,
  with unit the zero section and multiplication the addition morphism.

## Main results

* `WeierstrassCurve.isCommMonObj_projModelOver`: the monoid object is commutative.
* `WeierstrassCurve.one_projModelOver_left` and `WeierstrassCurve.mul_projModelOver_left`: the
  underlying morphisms of schemes of the unit and the multiplication are the zero section and the
  addition morphism.
* `WeierstrassCurve.isMonHom_projModelOverBaseChangeIso_hom`: the base change isomorphism is a
  homomorphism of monoid objects.

## References

* N. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

The monoid part of AINTLIB's `modelGrpObj` (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/ModelRecord.lean`) is the same structure, with
its axioms proved in `Over (Spec R)` directly. Here the axioms are deduced from the laws of the
addition morphism as morphisms of schemes. The compatibility with base change corresponds to
`isMonHom_modelBaseChangeIso` (file `AffineSectionSpecPoints.lean` in the same directory), which
compares the source's model with its base change of elliptic curves; here the comparison is with
the pullback functor `Over.pullback`, and the two axioms are checked on the two projections of the
fibre product, using `WeierstrassCurve.additionMorphism_projModelBaseChange`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section MonObj

variable [W.IsElliptic]

/-- The projective model of an elliptic Weierstrass curve `W` over `R`, as an object of
`Over (Spec R)`, is a monoid object of the cartesian monoidal category `Over (Spec R)`: its unit is
the zero section `projModelZero W` and its multiplication is the Bosma–Lenstra addition morphism
`additionMorphism W` (`one_projModelOver_left`, `mul_projModelOver_left`). -/
noncomputable instance monObjProjModelOver : MonObj (Over.mk W.projModelOver) where
  one := Over.homMk W.projModelZero (by simp)
  mul := Over.homMk W.additionMorphism (by simp [additionMorphism_projModelOver])
  one_mul := by
    -- precomposed with the inverse of the left unitor, the law is the left unit law of the
    -- addition morphism
    rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id]
    have h : (λ_ (Over.mk W.projModelOver)).inv ≫
        Over.homMk (V := Over.mk W.projModelOver) W.projModelZero (by simp) ▷ _ =
        lift (toUnit _ ≫ Over.homMk W.projModelZero (by simp)) (𝟙 _) := by
      ext <;> simp
    rw [reassoc_of% h]
    ext1
    simp
  mul_one := by
    -- precomposed with the inverse of the right unitor, the law is the right unit law of the
    -- addition morphism
    rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id]
    have h : (ρ_ (Over.mk W.projModelOver)).inv ≫
        _ ◁ Over.homMk (V := Over.mk W.projModelOver) W.projModelZero (by simp) =
        lift (𝟙 _) (toUnit _ ≫ Over.homMk W.projModelZero (by simp)) := by
      ext <;> simp
    rw [reassoc_of% h]
    ext1
    simp
  mul_assoc := by
    -- both sides are the pairs of morphisms out of the triple fibre product compared by the
    -- associativity of the addition morphism, followed by the multiplication
    have h₁ : Over.homMk (U := Over.mk W.projModelOver ⊗ Over.mk W.projModelOver)
        (V := Over.mk W.projModelOver) W.additionMorphism (by simp) ▷ Over.mk W.projModelOver =
        lift (fst _ _ ≫ Over.homMk W.additionMorphism (by simp)) (snd _ _) := by
      ext <;> simp
    have h₂ : (α_ (Over.mk W.projModelOver) _ _).hom ≫
        _ ◁ Over.homMk (U := Over.mk W.projModelOver ⊗ Over.mk W.projModelOver)
          (V := Over.mk W.projModelOver) W.additionMorphism (by simp) =
        lift (fst _ _ ≫ fst _ _)
          (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ Over.homMk W.additionMorphism (by simp)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ (by simp) ?_
      rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
      congr 1
      exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
    rw [h₁, reassoc_of% h₂]
    ext1
    simpa using W.additionMorphism_assoc

/-- The unit of the monoid object `Over.mk W.projModelOver` is the zero section. -/
@[simp]
theorem one_projModelOver_left : η[Over.mk W.projModelOver].left = W.projModelZero :=
  (rfl)

/-- The multiplication of the monoid object `Over.mk W.projModelOver` is the Bosma–Lenstra
addition morphism. -/
@[simp]
theorem mul_projModelOver_left : μ[Over.mk W.projModelOver].left = W.additionMorphism :=
  (rfl)

/-- The monoid object `Over.mk W.projModelOver` is commutative, because the addition morphism is
invariant under swapping its two factors (`additionMorphism_comm`). -/
instance isCommMonObj_projModelOver : IsCommMonObj (Over.mk W.projModelOver) where
  mul_comm := by
    ext1
    simp

end MonObj

section BaseChange

open scoped CategoryTheory.Obj

variable {R' : Type u} [CommRing R'] (f : R →+* R')

/-- **The monoid object commutes with base change.** The base change isomorphism
`projModelOverBaseChangeIso W f` is a homomorphism from the monoid object of `W.map f` to the
image of the monoid object of `W` under the pullback functor along `Spec f`, whose monoid
structure is `CategoryTheory.Functor.monObjObj` (a scoped instance, in `CategoryTheory.Obj`). -/
instance isMonHom_projModelOverBaseChangeIso_hom [W.IsElliptic] :
    IsMonHom (W.projModelOverBaseChangeIso f).hom where
  one_hom := by
    ext1
    apply pullback.hom_ext <;> simp
  mul_hom := by
    ext1
    apply pullback.hom_ext
    · -- on the first projection, this is the compatibility of the addition morphism with base
      -- change
      have h : ((W.projModelOverBaseChangeIso f).hom ⊗ₘ (W.projModelOverBaseChangeIso f).hom).left ≫
          (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom f)))
            (Over.mk W.projModelOver) (Over.mk W.projModelOver)).left ≫ pullback.fst _ _ =
          pullback.map _ _ _ _ (W.projModelBaseChange f) (W.projModelBaseChange f)
            (Spec.map (CommRingCat.ofHom f)) (W.projModelBaseChange_projModelOver f).symm
            (W.projModelBaseChange_projModelOver f).symm := by
        apply pullback.hom_ext <;> simp [Over.tensorHom_left]
      simp only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left,
        pullback.lift_fst]
      rw [reassoc_of% h]
      simp
    · -- on the second projection, both sides lie over `Spec R'`
      simp [Over.tensorHom_left, pullback.condition]

end BaseChange

end WeierstrassCurve
