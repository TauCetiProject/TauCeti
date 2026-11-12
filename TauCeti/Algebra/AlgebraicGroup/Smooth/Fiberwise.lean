/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product

/-!
# Smooth affine group schemes with prescribed geometric fibers

Given a property `P k` of finite-type affine groups over each field `k`, a finite-type affine
group scheme over `Spec R` is smooth with geometric fibers in `P` when it is smooth over `R` and
each scalar extension `k ⊗[R] H` to an algebraically closed field `k` satisfies `P k`. Reductive
and semisimple group schemes over a ring are the instances of this construction.

The construction inherits invariance under coordinate-Hopf-algebra isomorphism and stability under
arbitrary base change from the fieldwise property, and it is stable under direct products when
the fieldwise property is stable under products over algebraically closed fields.

## Main declarations

* `TauCeti.smoothFiberwiseCommHopfAlgPropertyOver`: smooth affine group schemes over a ring whose
  geometric fibers satisfy a given fieldwise property.
* `TauCeti.smoothFiberwiseCommHopfAlgPropertyOver.baseChange`: the condition is preserved by
  arbitrary base change.
* `TauCeti.smoothFiberwiseCommHopfAlgPropertyOver.tensorProduct`: the condition is preserved by
  direct products when the fieldwise property is.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A finite-type affine group scheme over a commutative ring is smooth with geometric fibers in
`P` when it is smooth and its scalar extension to every algebraically closed field `k` satisfies
`P k`. -/
def smoothFiberwiseCommHopfAlgPropertyOver
    (P : ∀ (k : Type u) [Field k], ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    (R : Type u) [CommRing R] : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} R) :=
  fun H ↦ Algebra.Smooth R H ∧
    ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
      P k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H)

/-- The geometric-fiber characterization of `smoothFiberwiseCommHopfAlgPropertyOver`. -/
@[simp]
theorem smoothFiberwiseCommHopfAlgPropertyOver_iff
    (P : ∀ (k : Type u) [Field k], ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    (R : Type u) [CommRing R] (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    smoothFiberwiseCommHopfAlgPropertyOver P R H ↔
      Algebra.Smooth R H ∧
        ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
          P k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  Iff.rfl

namespace smoothFiberwiseCommHopfAlgPropertyOver

variable {P : ∀ (k : Type u) [Field k], ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k)}
  {R : Type u} [CommRing R] {H : FiniteTypeCommHopfAlgCat.{u, u} R}

/-- Smoothness with geometric fibers in a property closed under isomorphisms is invariant under
coordinate-Hopf-algebra isomorphism. -/
instance [∀ (k : Type u) [Field k], (P k).IsClosedUnderIsomorphisms] :
    (smoothFiberwiseCommHopfAlgPropertyOver P R).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    refine ⟨?_, ?_⟩
    · apply (smoothCommHopfAlgProperty_iff _).mp
      exact (smoothCommHopfAlgProperty R).prop_of_iso
        ((finiteTypeCommHopfAlgProperty R).ι.mapIso e)
        ((smoothCommHopfAlgProperty_iff _).mpr hH.1)
    · intro k _ _ _
      exact (P k).prop_of_iso
        ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e) (hH.2 k)

/-- A group scheme with prescribed geometric fibers is smooth over its base. -/
theorem smooth (hH : smoothFiberwiseCommHopfAlgPropertyOver P R H) : Algebra.Smooth R H :=
  hH.1

/-- Every geometric fiber of a group scheme with geometric fibers in `P` satisfies `P`. -/
theorem geometricFiber (hH : smoothFiberwiseCommHopfAlgPropertyOver P R H)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    P k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  hH.2 k

/-- Smoothness with geometric fibers in a property closed under isomorphisms is preserved by
arbitrary base change. -/
theorem baseChange [∀ (k : Type u) [Field k], (P k).IsClosedUnderIsomorphisms]
    (hH : smoothFiberwiseCommHopfAlgPropertyOver P R H)
    (S : Type u) [CommRing S] [Algebra R S] :
    smoothFiberwiseCommHopfAlgPropertyOver P S
      (FiniteTypeCommHopfAlgCat.baseChange (K := S) H) := by
  let _ : Algebra.Smooth R H := hH.smooth
  refine ⟨inferInstance, ?_⟩
  intro k _ _ _
  let _ : Algebra R k := (algebraMap S k).comp (algebraMap R S) |>.toAlgebra
  let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact (P k).prop_of_iso (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := S) R k H).symm
    (hH.geometricFiber k)

/-- **Direct products preserve smoothness with prescribed geometric fibers** when the fieldwise
property is preserved by direct products over algebraically closed fields. The tensor product is
the coordinate Hopf algebra of the direct product of groups. -/
theorem tensorProduct [∀ (k : Type u) [Field k], (P k).IsClosedUnderIsomorphisms]
    (hP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (H K : FiniteTypeCommHopfAlgCat.{u, u} k),
      P k H → P k K → P k (FiniteTypeCommHopfAlgCat.tensorProduct H K))
    {K : FiniteTypeCommHopfAlgCat.{u, u} R}
    (hH : smoothFiberwiseCommHopfAlgPropertyOver P R H)
    (hK : smoothFiberwiseCommHopfAlgPropertyOver P R K) :
    smoothFiberwiseCommHopfAlgPropertyOver P R (FiniteTypeCommHopfAlgCat.tensorProduct H K) :=
  ⟨FiniteTypeCommHopfAlgCat.smooth_tensorProduct hH.smooth hK.smooth, fun k _ _ _ ↦
    (P k).prop_of_iso (FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso k H K).symm
      (hP k _ _ (hH.geometricFiber k) (hK.geometricFiber k))⟩

end smoothFiberwiseCommHopfAlgPropertyOver

end TauCeti
