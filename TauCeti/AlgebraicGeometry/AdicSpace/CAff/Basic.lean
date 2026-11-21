/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Functor.Hom
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair

import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.RingOfDefinition
import TauCeti.RingTheory.Polynomial.IsIntegral

/-!
# The category of complete Hausdorff Huber pairs

This file bundles complete Hausdorff Huber pairs `(A, A⁺)` into a category `TauCeti.CAff.{u}` whose
morphisms `X ⟶ Y` are continuous ring homomorphisms `X.ring →+* Y.ring` carrying `X.pair.plus` into
`Y.pair.plus`. Its opposite category `CAff.{u}ᵒᵖ` is the category of affinoid adic spaces in the
wide sense — prior to imposing any sheafiness hypothesis on `(A, A⁺)` — on which the rational
covering site and Yoneda-adic spaces are built.

## Main definitions

* `TauCeti.CAff`: the category of complete Hausdorff Huber pairs `(A, A⁺)`.
* `TauCeti.CAff.of`: construct an object of `CAff` from a `Huber.Pair` on a complete `T0Space`
  Huber ring.
* `TauCeti.CAff.discrete`: any commutative ring `R` as an object `(R, R)` of `CAff` with the
  discrete uniformity.
* `TauCeti.CAff.pairOfDefinition`: a chosen pair of definition of `X.ring` whose ring of definition
  is contained in `X.pair.plus`.
* `TauCeti.CAff.spa`: the adic spectrum functor `CAff.{u}ᵒᵖ ⥤ TopCat.{u}` sending `op (A, A⁺)` to
  `Spa(A, A⁺)` and `op φ` to `φ.spaComap`.
* `TauCeti.CAff.globalSections` and `TauCeti.CAff.ringPresheaf`: the global-ring presheaf
  `op (A, A⁺) ↦ A` on `CAff.{u}ᵒᵖ`, valued respectively in `Type u` and `CommRingCat.{u}`.
* `TauCeti.CAff.affineLine`: the discrete Huber pair `(ℤ[T], ℤ)` in `CAff.{u}`, together with its
  coordinate `CAff.affineLineVar` and evaluation morphisms `CAff.eval X a : CAff.affineLine ⟶ X`.
* `TauCeti.CAff.globalSectionsRepresentableBy` and `TauCeti.CAff.globalSectionsIsoYoneda`:
  representability of `CAff.globalSections` by `op CAff.affineLine`.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §2–3.
* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Lectures 2–4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3–7.5.
-/

public section

open CategoryTheory Opposite Polynomial Topology TauCeti.Huber TauCeti.ValuationSpectrum

universe u

namespace TauCeti

/-- An object of `CAff.{u}` is a complete Hausdorff Huber pair `(A, A⁺)` in universe `u`. The
separation axiom is stored as `T0Space`, from which `T2Space` follows automatically via
`IsUniformAddGroup`. -/
structure CAff : Type (u + 1) where
  /-- The underlying commutative ring `A`. -/
  ring : Type u
  [commRing : CommRing ring]
  [uniformSpace : UniformSpace ring]
  [isUniformAddGroup : IsUniformAddGroup ring]
  [isTopologicalRing : IsTopologicalRing ring]
  [isHuberRing : IsHuberRing ring]
  [completeSpace : CompleteSpace ring]
  [t0Space : T0Space ring]
  /-- The Huber pair `(A, A⁺)` specifying the ring of integral elements `A⁺ ⊆ A`. -/
  pair : Pair ring

attribute [instance] CAff.commRing CAff.uniformSpace CAff.isUniformAddGroup CAff.isTopologicalRing
  CAff.isHuberRing CAff.completeSpace CAff.t0Space

namespace CAff

/-- Bundle a `Huber.Pair` on a complete separated Huber ring as an object of `CAff.{u}`. -/
abbrev of {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A] [CompleteSpace A] [T0Space A] (S : Pair A) : CAff.{u} :=
  { ring := A, pair := S }

/-- Equip an arbitrary commutative ring `R` with the discrete uniformity and `R⁺ = R` to obtain an
object `(R, R)` of `CAff.{u}`. -/
@[expose]
def discrete (R : Type u) [CommRing R] : CAff.{u} :=
  letI : UniformSpace R := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteTopology R := ⟨rfl⟩
  { ring := R
    pair := Pair.discrete R }

@[simp]
theorem discrete_ring (R : Type u) [CommRing R] : (discrete R).ring = R :=
  (rfl)

instance instDiscreteTopologyDiscreteRing (R : Type u) [CommRing R] :
    DiscreteTopology (discrete R).ring :=
  ⟨rfl⟩

@[simp]
theorem discrete_plus (R : Type u) [CommRing R] : (discrete R).pair.plus = ⊤ :=
  Pair.discrete_plus

/-- Every `X : CAff` admits a pair of definition whose ring of definition lies in `X.pair.plus`. -/
noncomputable def pairOfDefinition (X : CAff.{u}) : PairOfDefinition X.ring :=
  (exists_pairOfDefinition_ringOfDefinition_le X.pair.isRingOfIntegralElements.isOpen).choose

/-- The ring of definition of `X.pairOfDefinition` is contained in `X.pair.plus`. -/
theorem ringOfDefinition_le_plus (X : CAff.{u}) :
    X.pairOfDefinition.ringOfDefinition ≤ X.pair.plus :=
  (exists_pairOfDefinition_ringOfDefinition_le X.pair.isRingOfIntegralElements.isOpen).choose_spec

/-! ### Category structure on `CAff` -/

instance : Category.{u} CAff.{u} where
  Hom X Y := Pair.Hom X.pair Y.pair
  id X := Pair.Hom.id X.pair
  comp f g := g.comp f
  id_comp f := Pair.Hom.comp_id f
  comp_id f := Pair.Hom.id_comp f
  assoc f g h := (Pair.Hom.comp_assoc h g f).symm

/-- Morphisms in `CAff` are determined by their underlying ring homomorphisms. -/
@[ext]
theorem hom_ext {X Y : CAff.{u}} {f g : X ⟶ Y} (h : f.toRingHom = g.toRingHom) : f = g :=
  Pair.Hom.ext h

@[simp]
theorem id_toRingHom (X : CAff.{u}) : (𝟙 X : X ⟶ X).toRingHom = RingHom.id X.ring :=
  Pair.Hom.toRingHom_id X.pair

@[simp]
theorem comp_toRingHom {X Y Z : CAff.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRingHom = g.toRingHom.comp f.toRingHom :=
  Pair.Hom.toRingHom_comp g f

@[simp]
theorem id_spaComap (X : CAff.{u}) : (𝟙 X : X ⟶ X).spaComap = id :=
  Pair.Hom.spaComap_id X.pair

@[simp]
theorem comp_spaComap {X Y Z : CAff.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).spaComap = f.spaComap ∘ g.spaComap :=
  Pair.Hom.spaComap_comp g f

/-- Construct an isomorphism in `CAff` from a homeomorphic ring isomorphism carrying one plus ring
onto the other. -/
def isoMk {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e) (he' : Continuous e.symm)
    (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) : X ≅ Y where
  hom :=
    { toRingHom := e.toRingHom
      continuous_toRingHom := he
      map_mem_plus _ ha := (hplus _).mp ha }
  inv :=
    { toRingHom := e.symm.toRingHom
      continuous_toRingHom := he'
      map_mem_plus b hb := (hplus (e.symm b)).mpr (by simpa using hb) }
  hom_inv_id := by ext x; simp
  inv_hom_id := by ext y; simp

@[simp]
theorem isoMk_hom_toRingHom {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) :
    (isoMk e he he' hplus).hom.toRingHom = e.toRingHom :=
  (rfl)

@[simp]
theorem isoMk_inv_toRingHom {X Y : CAff.{u}} (e : X.ring ≃+* Y.ring) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : ∀ a, a ∈ X.pair.plus ↔ e a ∈ Y.pair.plus) :
    (isoMk e he he' hplus).inv.toRingHom = e.symm.toRingHom :=
  (rfl)

/-! ### The adic spectrum functor `CAffᵒᵖ ⥤ TopCat` -/

/-- The functor sending `op (A, A⁺)` to the topological space `Spa(A, A⁺)` and `op φ` to the
pullback map `φ.spaComap : Spa(B, B⁺) → Spa(A, A⁺)`. -/
@[expose]
def spa : CAff.{u}ᵒᵖ ⥤ TopCat.{u} where
  obj X := TopCat.of ↥(ValuationSpectrum.spa (unop X).pair.plus)
  map f := TopCat.ofHom ⟨f.unop.spaComap, f.unop.continuous_spaComap⟩
  map_id X := TopCat.ext fun v ↦ congrFun (Pair.Hom.spaComap_id (unop X).pair) v
  map_comp f g := TopCat.ext fun v ↦ congrFun (Pair.Hom.spaComap_comp f.unop g.unop) v

@[simp]
theorem spa_obj (X : CAff.{u}) :
    (spa.obj (op X) : Type u) = ↥(ValuationSpectrum.spa X.pair.plus) :=
  (rfl)

@[simp]
theorem coe_spa_map {X Y : CAff.{u}} (f : X ⟶ Y) :
    ⇑(spa.map f.op) = f.spaComap :=
  (rfl)

/-- **Wedhorn Proposition 7.52 in `CAff`**: the adic spectrum of a complete Hausdorff Huber pair
`X : CAff` is empty if and only if `X.ring` is trivial. -/
theorem isEmpty_spa_iff (X : CAff.{u}) :
    IsEmpty (spa.obj (op X)) ↔ Subsingleton X.ring := by
  rw [spa_obj, Set.isEmpty_coe_sort,
    spa_eq_empty_iff_subsingleton X.pair.plus X.pair.isRingOfIntegralElements]

/-! ### The global-ring presheaves on `CAffᵒᵖ` -/

/-- The presheaf of commutative rings on `CAff.{u}ᵒᵖ` sending `op (A, A⁺)` to `A` and `op φ`
(for `φ : X ⟶ Y`) to `φ.toRingHom : X.ring →+* Y.ring`. -/
-- exposed so that its objects are definitionally `CommRingCat.of X.ring`
@[expose]
def ringPresheaf : (CAff.{u}ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (unop (unop X)).ring
  map f := CommRingCat.ofHom f.unop.unop.toRingHom
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- The presheaf of sets on `CAff.{u}ᵒᵖ` sending `op (A, A⁺)` to the underlying ring `A` and a
morphism `op Y ⟶ op X` (given by `φ : X ⟶ Y`) to `φ.toRingHom : X.ring → Y.ring`. -/
-- exposed so that `globalSections.obj (op (op X))` is definitionally `X.ring`
@[expose]
def globalSections : (CAff.{u}ᵒᵖ)ᵒᵖ ⥤ Type u where
  obj X := (unop (unop X)).ring
  map f := TypeCat.ofHom f.unop.unop.toRingHom
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

@[simp]
theorem globalSections_obj (X : CAff.{u}) : globalSections.obj (op (op X)) = X.ring :=
  (rfl)

@[simp]
theorem globalSections_map_apply {X Y : CAff.{u}} (f : X ⟶ Y) (a : X.ring) :
    globalSections.map f.op.op a = f.toRingHom a :=
  (rfl)

@[simp]
theorem ringPresheaf_comp_forget :
    ringPresheaf.{u} ⋙ forget CommRingCat.{u} = globalSections.{u} :=
  (rfl)

/-! ### Representability of `CAff.globalSections` by the discrete affine line `(ℤ[T], ℤ)` -/

section AffineLine

/-- Underlying pair `(ℤ[T], ℤ)` in universe `u` with the discrete topology on `(ULift ℤ)[X]`. -/
private noncomputable def affineLinePair :
    letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
    haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
    Pair (ULift.{u} ℤ)[X] :=
  letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
  haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
  haveI : IsDomain (ULift.{u} ℤ) :=
    Function.Injective.isDomain ULift.ringEquiv.toRingHom ULift.ringEquiv.injective
  { plus := (Polynomial.C (R := ULift.{u} ℤ)).range
    isRingOfIntegralElements :=
      { isOpen := isOpen_discrete _
        isIntegrallyClosedIn := TauCeti.isIntegrallyClosedIn_range_C
        le_powerBoundedSubring := by simp } }

/-- The discrete polynomial ring `ℤ[T]` in universe `u` paired with the constant subring `ℤ` as its
ring of integral elements. Morphisms `(ℤ[T], ℤ) ⟶ (A, A⁺)` in `CAff` correspond bijectively to
elements of `A` (`CAff.evalEquiv`), since `ℤ[T]` is discrete and `ℤ` maps into every subring
`A⁺`. -/
noncomputable def affineLine : CAff.{u} :=
  letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
  haveI : DiscreteUniformity (ULift.{u} ℤ)[X] := ⟨rfl⟩
  haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
  { ring := (ULift.{u} ℤ)[X]
    pair := affineLinePair.{u} }

/-- Private ring isomorphism encapsulating the single definitional unfolding
`affineLine.{u}.ring = (ULift.{u} ℤ)[X]` inside this module. -/
private noncomputable def affineLineRingEquiv : (ULift.{u} ℤ)[X] ≃+* affineLine.{u}.ring :=
  RingEquiv.refl _

/-- The indeterminate `T` in `CAff.affineLine.ring`. -/
noncomputable def affineLineVar : affineLine.{u}.ring :=
  affineLineRingEquiv Polynomial.X

private theorem affineLineVar_eq :
    affineLineVar.{u} = affineLineRingEquiv Polynomial.X := rfl

private theorem mem_affineLine_plus_iff (p : (ULift.{u} ℤ)[X]) :
    affineLineRingEquiv p ∈ affineLine.{u}.pair.plus ↔
      p ∈ (Polynomial.C (R := ULift.{u} ℤ)).range :=
  Iff.rfl

/-- The indeterminate `T` does not lie in the plus ring `ℤ` of `CAff.affineLine = (ℤ[T], ℤ)`,
reflecting that morphisms `(ℤ[T], ℤ) ⟶ (A, A⁺)` may evaluate `T` at arbitrary (not necessarily
power-bounded) elements of `A`. -/
theorem affineLineVar_notMem_plus : affineLineVar.{u} ∉ affineLine.{u}.pair.plus := by
  rw [affineLineVar_eq, mem_affineLine_plus_iff]
  rintro ⟨c, hc⟩
  simpa using congrArg (fun p : (ULift.{u} ℤ)[X] ↦ p.coeff 1) hc

/-- Evaluate `(ℤ[T], ℤ)` at an arbitrary element `a : X.ring` to obtain a morphism
`CAff.affineLine ⟶ X` in `CAff`. Continuity is automatic because `ℤ[T]` carries the discrete
topology, and plus-ring compatibility holds because `ℤ` maps into every subring `X.pair.plus`. -/
noncomputable def eval (X : CAff.{u}) (a : X.ring) : affineLine.{u} ⟶ X :=
  letI : DiscreteTopology affineLine.{u}.ring := ⟨rfl⟩
  { toRingHom :=
      (Polynomial.eval₂RingHom ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a).comp
        affineLineRingEquiv.symm.toRingHom
    continuous_toRingHom := continuous_of_discreteTopology
    map_mem_plus := by
      intro p hp
      rw [← affineLineRingEquiv.apply_symm_apply p, mem_affineLine_plus_iff] at hp
      obtain ⟨c, hc⟩ := hp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, ← hc, coe_eval₂RingHom, eval₂_C, eq_intCast]
      exact intCast_mem X.pair.plus _ }

private theorem eval_toRingHom_apply_affineLineRingEquiv (X : CAff.{u}) (a : X.ring)
    (p : (ULift.{u} ℤ)[X]) :
    (eval X a).toRingHom (affineLineRingEquiv p) =
      eval₂ ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a p := by
  simp [eval]

private theorem eval_toRingHom_comp_affineLineRingEquiv (X : CAff.{u}) (a : X.ring) :
    (eval X a).toRingHom.comp affineLineRingEquiv.toRingHom =
      Polynomial.eval₂RingHom ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a :=
  RingHom.ext fun p ↦ eval_toRingHom_apply_affineLineRingEquiv X a p

@[simp]
theorem eval_affineLineVar (X : CAff.{u}) (a : X.ring) :
    (eval X a).toRingHom affineLineVar = a := by
  rw [affineLineVar_eq, eval_toRingHom_apply_affineLineRingEquiv]
  exact eval₂_X _ a

@[simp]
theorem eval_comp {X Y : CAff.{u}} (a : X.ring) (f : X ⟶ Y) :
    eval X a ≫ f = eval Y (f.toRingHom a) := by
  apply hom_ext
  refine (RingHom.cancel_right (f := affineLineRingEquiv.toRingHom)
    affineLineRingEquiv.surjective).mp ?_
  rw [comp_toRingHom, RingHom.comp_assoc, eval_toRingHom_comp_affineLineRingEquiv,
    eval_toRingHom_comp_affineLineRingEquiv]
  exact Polynomial.ringHom_ext' (by ext ⟨n⟩; simp) (by simp)

/-- Morphisms `CAff.affineLine ⟶ X` in `CAff` correspond bijectively to elements of `X.ring` via
evaluation at `CAff.affineLineVar`. -/
noncomputable def evalEquiv (X : CAff.{u}) : X.ring ≃ (affineLine.{u} ⟶ X) where
  toFun := eval X
  invFun f := f.toRingHom affineLineVar
  left_inv a := eval_affineLineVar X a
  right_inv f := by
    apply hom_ext
    refine (RingHom.cancel_right (f := affineLineRingEquiv.toRingHom)
      affineLineRingEquiv.surjective).mp ?_
    rw [eval_toRingHom_comp_affineLineRingEquiv]
    refine Polynomial.ringHom_ext' ?_ (by simp [affineLineVar_eq])
    ext ⟨n⟩
    have hn : Polynomial.C (⟨n⟩ : ULift.{u} ℤ) = (n : (ULift.{u} ℤ)[X]) := by
      rw [← Polynomial.C_eq_intCast]; rfl
    simp only [RingHom.comp_apply, hn, map_intCast]

@[simp]
theorem evalEquiv_apply (X : CAff.{u}) (a : X.ring) : evalEquiv X a = eval X a := (rfl)

@[simp]
theorem evalEquiv_symm_apply (X : CAff.{u}) (f : affineLine.{u} ⟶ X) :
    (evalEquiv X).symm f = f.toRingHom affineLineVar := (rfl)

/-- `CAff.eval X : X.ring → (CAff.affineLine ⟶ X)` is bijective. -/
theorem eval_bijective (X : CAff.{u}) : Function.Bijective (eval X) :=
  (evalEquiv X).bijective

/-- `op CAff.affineLine` represents the global-ring presheaf `CAff.globalSections` on `CAffᵒᵖ`. -/
noncomputable def globalSectionsRepresentableBy :
    globalSections.{u}.RepresentableBy (op affineLine.{u}) where
  homEquiv {Z} := Quiver.Hom.opEquiv.symm.trans (evalEquiv (unop Z)).symm
  homEquiv_comp g f :=
    -- `globalSections` is `@[expose]`, so both sides reduce definitionally via
    -- `evalEquiv_symm_apply` and `globalSections_map_apply` to `comp_toRingHom` at `affineLineVar`.
    RingHom.congr_fun (comp_toRingHom f.unop g.unop) affineLineVar

/-- **Representability of the global-ring presheaf on `CAffᵒᵖ`.** Sending `a ∈ A` to the opposite of
the evaluation morphism `CAff.eval (A, A⁺) a : (ℤ[T], ℤ) ⟶ (A, A⁺)` defines a natural isomorphism
`CAff.globalSections ≅ yoneda.obj (op CAff.affineLine)`. -/
noncomputable def globalSectionsIsoYoneda : globalSections.{u} ≅ yoneda.obj (op affineLine.{u}) :=
  globalSectionsRepresentableBy.toIso.symm

@[simp]
theorem globalSectionsIsoYoneda_hom_app (X : CAff.{u}) (a : X.ring) :
    globalSectionsIsoYoneda.hom.app (op (op X)) a = (eval X a).op := (rfl)

@[simp]
theorem globalSectionsIsoYoneda_inv_app (X : CAff.{u}) (f : op X ⟶ op affineLine.{u}) :
    globalSectionsIsoYoneda.inv.app (op (op X)) f = f.unop.toRingHom affineLineVar := (rfl)

end AffineLine

end CAff

end TauCeti

end
