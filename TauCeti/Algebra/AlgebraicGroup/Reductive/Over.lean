/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# Reductive affine group schemes over a ring

A reductive affine group scheme over `Spec R` is smooth over `R` and has connected reductive
geometric fibers. In Hopf coordinates, its geometric fibers are the scalar extensions
`k ⊗[R] H` for algebraically closed fields `k` equipped with an `R`-algebra structure.
The finite-type ambient category and smoothness give finite presentation; neither reducedness
of `R` nor a field hypothesis on `R` is required.

`reductiveCommHopfAlgPropertyOver` keeps this condition separate from the ambient category and
from the choice of a maximal torus. Its base-change theorem permits an integral group scheme
and its specializations to be recognized using the same condition.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A finite-type affine group scheme over a commutative ring is reductive when it is smooth
and all of its geometric fibers are connected reductive groups. -/
def reductiveCommHopfAlgPropertyOver (R : Type u) [CommRing R] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} R) :=
  fun H ↦ Algebra.Smooth R H ∧
    ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
      reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H)

/-- The geometric-fiber characterization of a reductive affine group scheme over a ring. -/
@[simp]
theorem reductiveCommHopfAlgPropertyOver_iff (R : Type u) [CommRing R]
    (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    reductiveCommHopfAlgPropertyOver R H ↔
      Algebra.Smooth R H ∧
        ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
          reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  Iff.rfl

/-- Reductivity over a ring is invariant under coordinate-Hopf-algebra isomorphism. -/
instance (R : Type u) [CommRing R] :
    (reductiveCommHopfAlgPropertyOver R).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    refine ⟨?_, ?_⟩
    · apply (smoothCommHopfAlgProperty_iff _).mp
      exact (smoothCommHopfAlgProperty R).prop_of_iso
        ((finiteTypeCommHopfAlgProperty R).ι.mapIso e)
        ((smoothCommHopfAlgProperty_iff _).mpr hH.1)
    · intro k _ _ _
      exact (reductiveCommHopfAlgProperty k).prop_of_iso
        ((FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := k)).mapIso e) (hH.2 k)

namespace reductiveCommHopfAlgPropertyOver

variable {R : Type u} [CommRing R] {H : FiniteTypeCommHopfAlgCat.{u, u} R}

/-- A reductive group scheme is smooth over its base. -/
theorem smooth (hH : reductiveCommHopfAlgPropertyOver R H) : Algebra.Smooth R H :=
  hH.1

/-- Every geometric fiber of a reductive group scheme is reductive. -/
theorem geometricFiber (hH : reductiveCommHopfAlgPropertyOver R H)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  hH.2 k

/-- Reductivity of affine group schemes is preserved by arbitrary base change. -/
theorem baseChange (hH : reductiveCommHopfAlgPropertyOver R H)
    (S : Type u) [CommRing S] [Algebra R S] :
    reductiveCommHopfAlgPropertyOver S (FiniteTypeCommHopfAlgCat.baseChange (K := S) H) := by
  let _ : Algebra.Smooth R H := hH.smooth
  refine ⟨inferInstance, ?_⟩
  intro k _ _ _
  let _ : Algebra R k := (algebraMap S k).comp (algebraMap R S) |>.toAlgebra
  let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : FiniteTypeCommHopfAlgCat.baseChange (K := k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := S) H) ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := k) H :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.baseChangeTowerIso R k H.obj)
  exact (reductiveCommHopfAlgProperty k).prop_of_iso e.symm (hH.geometricFiber k)

end reductiveCommHopfAlgPropertyOver

end TauCeti
