/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# Ordered positive-root multiplication as a scheme morphism

Multiply the root morphisms in a prescribed order, with one additive-group factor for
each root in the list. For a list of distinct positive roots, this is a monomorphism
into the simply connected Chevalley scheme. The assertion is integral: it tests arbitrary
commutative rings, not just fields. It is the uniqueness part of the scheme-theoretic
positive-root factorization, and does not assert that its image is the unipotent radical
or that the multiplication is a closed immersion.

The point calculation uses `list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj` and
`ChevalleyDatum.schemePointsMulEquiv_rootSubgroup`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

/-- The parameter scheme for an ordered root product. Only roots occurring in the list
carry parameters. It is a finite product of copies of the additive group scheme. -/
abbrev rootProductParameters (t : DynkinType) (l : List (Fin t.numRoots)) :
    Over (Spec (CommRingCat.of ℤ)) :=
  ∏ᶜ fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X

namespace ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Ordered multiplication of the integral root morphisms. This is a morphism of schemes
over `ℤ`, not a homomorphism of group schemes. Repeated roots reuse the same coordinate. -/
def rootProduct (l : List (Fin t.numRoots)) : t.rootProductParameters l ⟶ D.groupScheme.X :=
  (l.attach.map fun γ =>
    Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
      (D.rootSubgroup γ.val).hom.hom).prod

/-- Precomposing ordered root multiplication evaluates each root factor at the corresponding
additive-group coordinate of the test point. -/
theorem comp_rootProduct (l : List (Fin t.numRoots))
    {S : Over (Spec (CommRingCat.of ℤ))} (p : S ⟶ t.rootProductParameters l) :
    p ≫ D.rootProduct l = (l.attach.map fun γ =>
      p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ ≫
        (D.rootSubgroup γ.val).hom.hom).prod := by
  unfold rootProduct
  generalize l.attach = L
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, MonObj.comp_one]
  | cons γ L ih =>
    simp only [List.map_cons, List.prod_cons, MonObj.comp_mul, ih]

/-- Ordered root multiplication on ring-valued points is the ordered product of the root
homomorphisms with the same additive coordinates. -/
@[simp]
theorem schemePointsMulEquiv_rootProduct (l : List (Fin t.numRoots))
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) :
    GeneralLinear.schemePointsMulEquiv D.dim A
        (p ≫ D.rootProduct l ≫ D.groupSchemeι.hom.hom) =
      (l.attach.map fun γ => (D.rootSubgroupPoints γ.val A
        (AdditiveGroup.schemePointsMulEquiv A
          (p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ)) :
            Matrix.GeneralLinearGroup (Fin D.dim) A)).prod := by
  rw [← Category.assoc, D.comp_rootProduct]
  let ev := (GeneralLinear.schemePointsMulEquiv D.dim A).toMonoidHom.comp
    (IsMonHom.monoidHom D.groupSchemeι.hom.hom
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))))
  refine (ev.map_list_prod _).trans (congrArg List.prod ((List.map_map ..).trans
    (List.map_congr_left fun γ _ => ?_)))
  simp only [Function.comp_def, ev, MonoidHom.comp_apply, IsMonHom.monoidHom_apply,
    MulEquiv.toMonoidHom_eq_coe, Category.assoc, AdditiveGroup.schemePointsMulEquiv_apply]
  exact D.schemePointsMulEquiv_rootSubgroup γ.val A
    (p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) γ)

private theorem rootProduct_spec_injective
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type) [CommRing A] :
    Function.Injective (fun p : (Spec (CommRingCat.of A)).asOver
      (Spec (CommRingCat.of ℤ)) ⟶ t.rootProductParameters l =>
        p ≫ (t.scChevalleyDatum ht).rootProduct l) := by
  classical
  let E := t.scChevalleyDatum ht
  -- Extend by zero only inside this proof to use the native all-root parameter API.
  let coord := fun (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) (γ : Fin t.numRoots) =>
    if hγ : γ ∈ l then toAdd (AdditiveGroup.schemePointsMulEquiv A
      (p ≫ Pi.π (fun _ : {γ // γ ∈ l} => (AdditiveGroup.groupScheme ℤ).X) ⟨γ, hγ⟩))
    else 0
  have eval (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      t.rootProductParameters l) :
      GeneralLinear.schemePointsMulEquiv E.dim A (p ≫ E.rootProduct l ≫ E.groupSchemeι.hom.hom) =
        ((l.map fun γ => E.rootSubgroupPoints γ A (ofAdd (coord p γ))).prod :
          Matrix.GeneralLinearGroup (Fin E.dim) A) := by
    rw [E.schemePointsMulEquiv_rootProduct]
    simp only [SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def]
    rw [← List.attach_map_val (l := l)]
    apply congrArg List.prod
    apply List.map_congr_left
    intro γ _
    simp only [coord, dite_eq_left γ.property, ofAdd_toAdd]
  intro p q hpq
  have hmat := congrArg (fun z => GeneralLinear.schemePointsMulEquiv E.dim A
    (z ≫ E.groupSchemeι.hom.hom)) hpq
  simp only [Category.assoc] at hmat
  rw [eval p, eval q] at hmat
  have hprod : (l.map fun γ => E.rootSubgroupPoints γ A (ofAdd (coord p γ))).prod =
      (l.map fun γ => E.rootSubgroupPoints γ A (ofAdd (coord q γ))).prod :=
    (E.points A).subtype_injective hmat
  have hcoord := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A hl hpos).mp hprod
  apply Pi.hom_ext
  intro γ
  apply (AdditiveGroup.schemePointsMulEquiv A).injective
  simpa only [coord, dite_eq_left γ.property, ofAdd_toAdd] using
    congrArg ofAdd (hcoord γ.val γ.property)

end ChevalleyDatum

open ChevalleyDatum

/-- Ordered multiplication of distinct positive root schemes is a monomorphism into the
simply connected Chevalley scheme. The test schemes need not be affine or reduced. -/
theorem mono_rootProduct_scChevalleyDatum (t : DynkinType) (ht : t.Valid)
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    Mono ((t.scChevalleyDatum ht).rootProduct l) := by
  constructor
  intro S p q hpq
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall_spec fun A a => ?_
  let u : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ S :=
    Over.homMk a (specZIsTerminal.hom_ext _ _)
  have h : u ≫ p = u ≫ q := rootProduct_spec_injective l hl hpos A
    (by simpa only [Category.assoc] using congrArg (u ≫ ·) hpq)
  exact congrArg (fun z => z.left) h

end

end TauCeti.DynkinType
