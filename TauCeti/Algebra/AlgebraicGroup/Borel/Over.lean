/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic

/-!
# Borel subgroups of affine group schemes over a ring

Let `H` be the coordinate Hopf algebra of a finite-type affine group `G` over a commutative ring
`R`, and let `I` be a Hopf ideal of `H`, cutting out a closed subgroup `B` of `G`. Then `B` is a
**Borel subgroup** of `G` when it is smooth over `R` and every geometric fiber of `B` is a Borel
subgroup of the corresponding geometric fiber of `G`: for every algebraically closed field `k`
with an `R`-algebra structure, the base-changed ideal `I_k` is minimal among the defining ideals of
smooth, connected, solvable closed subgroups of `G_k`.

This is the relative notion of Borel subgroup used for reductive group schemes, where a pinning
consists of a split maximal torus, a Borel subgroup containing it, and root vectors for the
simple roots. Smoothness over the base is imposed explicitly, as in the relative definition;
the fiberwise condition alone only controls the geometric fibers.

Over a field `k`, a Borel subgroup in this sense is in particular a Borel subgroup in the sense
of `TauCeti.HopfIdeal.IsBorel`, which only tests the base change to `AlgebraicClosure k`.

Borel subgroups over a ring are transported along isomorphisms of coordinate Hopf algebras and
are stable under arbitrary base change `R → S`, so a Borel subgroup chosen over `ℤ` specializes
to every commutative ring.

## Main declarations

* `TauCeti.HopfIdeal.IsBorelOver`: the Hopf ideal of a Borel subgroup of an affine group over a
  commutative ring.
* `TauCeti.HopfIdeal.IsBorelOver.isBorel`: over a field, a Borel subgroup over the base is a
  Borel subgroup.
* `TauCeti.HopfIdeal.IsBorelOver.comapOfIso` and `TauCeti.HopfIdeal.IsBorelOver.comapOfIso_iff`:
  invariance under isomorphisms of the ambient coordinate Hopf algebra.
* `TauCeti.HopfIdeal.IsBorelOver.baseChange`: stability under base change along `R → S`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.2.
* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v

/-- A Hopf ideal `I` of the coordinate Hopf algebra `H` of a finite-type affine group `G` over
`R` cuts out a **Borel subgroup** of `G` when the closed subgroup it defines is smooth over `R`
and, on every geometric fiber, is a Borel subgroup of the geometric fiber of `G`. -/
def IsBorelOver (R : Type u) [CommRing R] (H : _root_.CommHopfAlgCat.{v} R)
    [Algebra.FiniteType R H] (I : HopfIdeal R H) : Prop :=
  Algebra.Smooth R (CommHopfAlgCat.quotient H I) ∧
    ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
      IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) I)

/-- A Borel subgroup over a ring is a smooth closed subgroup whose geometric fibers are Borel
subgroups. -/
@[simp]
theorem isBorelOver_iff (R : Type u) [CommRing R] (H : _root_.CommHopfAlgCat.{v} R)
    [Algebra.FiniteType R H] (I : HopfIdeal R H) :
    IsBorelOver R H I ↔
      Algebra.Smooth R (CommHopfAlgCat.quotient H I) ∧
        ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
          IsBorelOverAlgClosed k
            (FiniteTypeCommHopfAlgCat.baseChange (K := k)
              ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩)
            (CommHopfAlgCat.baseChangeHopfIdeal (K := k) I) :=
  Iff.rfl

namespace IsBorelOver

section Basic

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R} [Algebra.FiniteType R H]
    {I : HopfIdeal R H}

/-- Construct a Borel subgroup over a ring from smoothness over the base and the Borel property
of every geometric fiber. -/
theorem mk (h_smooth : Algebra.Smooth R (CommHopfAlgCat.quotient H I))
    (h_fiber : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
      IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := k) I)) :
    IsBorelOver R H I :=
  ⟨h_smooth, h_fiber⟩

/-- A Borel subgroup over a ring is smooth over the base. -/
theorem smooth (hI : IsBorelOver R H I) : Algebra.Smooth R (CommHopfAlgCat.quotient H I) :=
  hI.1

/-- Every geometric fiber of a Borel subgroup over a ring is a Borel subgroup of the geometric
fiber of the ambient group. -/
theorem geometricFiber (hI : IsBorelOver R H I)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.baseChange (K := k)
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) I) :=
  hI.2 k

end Basic

/-- Over a field, a Borel subgroup over the base is a Borel subgroup: its base change to the
algebraic closure is a Borel subgroup there. -/
theorem isBorel {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H]
    {I : HopfIdeal k H} (hI : IsBorelOver k H I) : IsBorel k H I :=
  (isBorel_iff_isBorelOverAlgClosed_baseChange k H I).2 (hI.geometricFiber (AlgebraicClosure k))

section ComapOfIso

variable {R : Type u} [CommRing R] {H L : _root_.CommHopfAlgCat.{v} R} [Algebra.FiniteType R H]
    [Algebra.FiniteType R L] {J : HopfIdeal R L}

/-- Pulling a Borel subgroup back across an isomorphism `e : H ≅ L` of coordinate Hopf algebras
gives a Borel subgroup of the source. -/
theorem comapOfIso (hJ : IsBorelOver R L J) (e : H ≅ L) :
    IsBorelOver R H
      (J.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  refine ⟨?_, fun k _ _ _ ↦ ?_⟩
  · let _ := hJ.smooth
    exact (smoothCommHopfAlgProperty_iff _).mp
      ((smoothCommHopfAlgProperty R).prop_of_iso (CommHopfAlgCat.quotientIsoOfIso e J).symm
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
  · let ek : FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ ≅
        FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨L, (finiteTypeCommHopfAlgProperty_iff L).2 inferInstance⟩ :=
      ObjectProperty.isoMk _ ((CommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e)
    rw [CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso]
    exact (hJ.geometricFiber k).comapOfIso ek

variable (J) in
/-- Borel status over a ring is invariant under pulling the defining ideal back across an
isomorphism of coordinate Hopf algebras. -/
theorem comapOfIso_iff (e : H ≅ L) :
    IsBorelOver R H
        (J.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) ↔
      IsBorelOver R L J := by
  refine ⟨fun hJ ↦ ?_, fun hJ ↦ hJ.comapOfIso e⟩
  have hcomap : (J.comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2).comapOfSurjective e.inv.hom
        (ConcreteCategory.bijective_of_isIso e.inv).2 = J := by
    ext x
    simp
  simpa [hcomap] using hJ.comapOfIso e.symm

end ComapOfIso

section BaseChange

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{u} R} [Algebra.FiniteType R H]
    {I : HopfIdeal R H} (S : Type u) [CommRing S] [Algebra R S]

/-- **Base change of a Borel subgroup** along `R → S`: the base-changed ideal cuts out a Borel
subgroup of the base-changed affine group. Its geometric fibers are geometric fibers of the
original Borel subgroup. -/
theorem baseChange (hI : IsBorelOver R H I) :
    IsBorelOver S (CommHopfAlgCat.baseChange (K := S) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := S) I) := by
  refine ⟨?_, fun k _ _ _ ↦ ?_⟩
  · let _ := hI.smooth
    exact (smoothCommHopfAlgProperty_iff _).mp
      ((smoothCommHopfAlgProperty S).prop_of_iso
        (CommHopfAlgCat.quotientBaseChangeIso (K := S) I).symm
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
  · let _ : Algebra R k := ((algebraMap S k).comp (algebraMap R S)).toAlgebra
    let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let e : FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨CommHopfAlgCat.baseChange (K := S) H,
            (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ ≅
        FiniteTypeCommHopfAlgCat.baseChange (K := k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ :=
      ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso (E := S) R k H)
    rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal]
    exact (hI.geometricFiber k).comapOfIso e

end BaseChange

end IsBorelOver

end TauCeti.HopfIdeal
