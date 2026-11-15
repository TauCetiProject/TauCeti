/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.FiniteEtale.Conservative
public import TauCeti.AlgebraicGeometry.FiniteEtale.Quotient
public import TauCeti.CategoryTheory.Galois.FiberFunctorIso
public import TauCeti.CategoryTheory.Limits.Shapes.SingleObj

/-!
# The Galois category of finite étale covers of a connected scheme

Let `S` be a scheme and `x : Spec Ω ⟶ S` a geometric point, with `Ω` separably closed. The
geometric fibre functor `FiniteEtaleScheme.fiber x` preserves quotients by finite groups: if a
finite group `G` acts on a finite étale `S`-scheme `Y`, the geometric fibre of the quotient `Y / G`
is the set of `G`-orbits on the geometric fibre of `Y`. This is the quotient part of Lenstra's
axiom (G5) for a fibre functor.

Finite étale schemes over every scheme form a `CategoryTheory.PreGaloisCategory`
(`TauCeti.AlgebraicGeometry.FiniteEtale.Quotient`). Together with the axioms already established
for geometric fibre functors, it follows that every geometric fibre functor is a
`CategoryTheory.PreGaloisCategory.FiberFunctor` when `S` is connected, and hence that finite étale
schemes over a connected scheme form a `CategoryTheory.GaloisCategory`. Mathlib's theory of Galois
categories then applies to them: for instance,
`CategoryTheory.PreGaloisCategory.functorToContAction` is an equivalence from finite étale schemes
over `S` to finite continuous sets under the automorphism group of a geometric fibre functor.

The proof of preservation works with lifts of `x`, which are the points of the fibre
(`FiniteEtaleScheme.fiberCompInclIso`). Surjectivity on fibres holds because the quotient map is
an epimorphism and the fibre functor preserves epimorphisms. Injectivity modulo `G` holds because
two points of `Y` with values in a field and the same image in the quotient differ by an element of
`G` (`TauCeti.FiniteEtaleScheme.exists_comp_map_eq_of_comp_quotientπ_eq`).

## Main results

* `PreservesColimitsOfShape (SingleObj G) (FiniteEtaleScheme.fiber x)` for a finite group `G`:
  geometric fibre functors preserve quotients by finite groups.
* `PreGaloisCategory.FiberFunctor (FiniteEtaleScheme.fiber x)` when `S` is connected.
* `GaloisCategory (FiniteEtaleScheme S)` when `S` is connected.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_iso`: when `S` is connected, any two geometric fibre
  functors are isomorphic, so any two geometric points are joined by an étale path.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

universe u v

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {G : Type v} [Group G] [Finite G] (F : SingleObj G ⥤ FiniteEtaleScheme S)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre of the quotient of a finite étale `S`-scheme by a finite group, as a type,
is the quotient of the geometric fibre by the group. -/
private noncomputable def isColimitInclMapCoconeFiber (x : Spec (.of Ω) ⟶ S) :
    IsColimit (FintypeCat.incl.mapCocone ((fiber x).mapCocone (quotientCocone F))) := by
  -- The leg of a colimit over `SingleObj G` is an epimorphism.
  have : Epi (quotientπ F) :=
    ⟨fun _ _ h ↦ (isColimitQuotientCocone F).hom_ext fun ⟨⟩ ↦ h⟩
  refine SingleObj.Types.isColimitOf _
    (surjective_of_epi (FintypeCat.incl.map ((fiber x).map (quotientπ F)))) fun y₂ y₁ h ↦ ?_
  -- Pass to lifts of `x`, the points of the fibre.
  let e := (fiberCompInclIso x).hom
  have h₁ := NatTrans.naturality_apply e (quotientπ F) y₁
  have h₂ := NatTrans.naturality_apply e (quotientπ F) y₂
  have hu : e.app _ y₁ ≫ (quotientπ F).hom = e.app _ y₂ ≫ (quotientπ F).hom := by
    simpa using h₁.symm.trans ((congrArg (e.app (quotient F)) h.symm).trans h₂)
  obtain ⟨g, hg⟩ := exists_comp_map_eq_of_comp_quotientπ_eq F congr(($hu).left)
  have hg' : e.app _ y₁ ≫ (F.map g).hom = e.app _ y₂ := Over.OverMorphism.ext hg
  refine ⟨g, (mono_iff_injective (e.app _)).mp inferInstance ?_⟩
  have h₃ : e.app _ ((fiber x).map (F.map g) y₁) = e.app _ y₂ := by
    simpa [hg'] using
      NatTrans.naturality_apply e (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g) y₁
  -- The action of `g` on the fibre is, by definition, the fibre of `F.map g`.
  exact h₃

/-- **Geometric fibre functors preserve quotients by finite groups.** The geometric fibre of the
quotient of a finite étale `S`-scheme by a finite group is the set of orbits of the group on the
geometric fibre. -/
instance (x : Spec (.of Ω) ⟶ S) : PreservesColimitsOfShape (SingleObj G) (fiber x) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (isColimitQuotientCocone F)
    (isColimitOfReflects FintypeCat.incl (isColimitInclMapCoconeFiber F x))

end TauCeti.FiniteEtaleScheme

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **Over a connected scheme, every geometric fibre functor is a fibre functor** of the Galois
category of finite étale schemes. -/
instance [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) : FiberFunctor (fiber x) where
  preservesQuotientsByFiniteGroups _ := inferInstance

/-- **Finite étale schemes over a connected scheme form a Galois category.** A fibre functor is
the geometric fibre at an algebraic closure of a residue field. -/
instance [ConnectedSpace S] : GaloisCategory (FiniteEtaleScheme S) where
  hasFiberFunctor := by
    obtain ⟨p⟩ : Nonempty S := inferInstance
    let K := S.residueField p
    let x := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      S.fromSpecResidueField p
    exact ⟨fiber x, inferInstance⟩

/-- **Any two geometric points of a connected scheme are joined by an étale path**: their
geometric fibre functors on finite étale schemes are isomorphic. The geometric points may have
different separably closed fields. -/
theorem nonempty_fiber_iso [ConnectedSpace S] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (x : Spec (.of Ω) ⟶ S) (y : Spec (.of Ω') ⟶ S) : Nonempty (fiber x ≅ fiber y) :=
  FiberFunctor.nonempty_iso _ _

end TauCeti.FiniteEtaleScheme
