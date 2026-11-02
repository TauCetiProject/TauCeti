/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Fiberwise
import TauCeti.Algebra.AlgebraicGroup.Reductive.Product

/-!
# Reductive affine group schemes over a ring

A reductive affine group scheme over `Spec R` is smooth over `R` and has connected reductive
geometric fibers. In Hopf coordinates, its geometric fibers are the scalar extensions
`k ⊗[R] H` for algebraically closed fields `k` equipped with an `R`-algebra structure.
The finite-type ambient category and smoothness give finite presentation; neither reducedness
of `R` nor a field hypothesis on `R` is required.

`reductiveCommHopfAlgPropertyOver` is `smoothFiberwiseCommHopfAlgPropertyOver` for the
fieldwise reductive property. It keeps this condition separate from the ambient category and
from the choice of a maximal torus. Its base-change theorem permits an integral group scheme
and its specializations to be recognized using the same condition. Direct products of reductive
group schemes are reductive, because scalar extension commutes with tensor products of
coordinate Hopf algebras.

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
  smoothFiberwiseCommHopfAlgPropertyOver reductiveCommHopfAlgProperty R

/-- The geometric-fiber characterization of a reductive affine group scheme over a ring. -/
@[simp]
theorem reductiveCommHopfAlgPropertyOver_iff (R : Type u) [CommRing R]
    (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    reductiveCommHopfAlgPropertyOver R H ↔
      Algebra.Smooth R H ∧
        ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
          reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver_iff _ R H

/-- Reductivity over a ring is invariant under coordinate-Hopf-algebra isomorphism. -/
instance (R : Type u) [CommRing R] :
    (reductiveCommHopfAlgPropertyOver R).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| ObjectProperty.IsClosedUnderIsomorphisms <|
    smoothFiberwiseCommHopfAlgPropertyOver reductiveCommHopfAlgProperty R

namespace reductiveCommHopfAlgPropertyOver

variable {R : Type u} [CommRing R] {H : FiniteTypeCommHopfAlgCat.{u, u} R}

/-- A reductive group scheme is smooth over its base. -/
theorem smooth (hH : reductiveCommHopfAlgPropertyOver R H) : Algebra.Smooth R H :=
  smoothFiberwiseCommHopfAlgPropertyOver.smooth hH

/-- Every geometric fiber of a reductive group scheme is reductive. -/
theorem geometricFiber (hH : reductiveCommHopfAlgPropertyOver R H)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver.geometricFiber hH k

/-- Reductivity of affine group schemes is preserved by arbitrary base change. -/
theorem baseChange (hH : reductiveCommHopfAlgPropertyOver R H)
    (S : Type u) [CommRing S] [Algebra R S] :
    reductiveCommHopfAlgPropertyOver S (FiniteTypeCommHopfAlgCat.baseChange (K := S) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver.baseChange hH S

/-- **A direct product of reductive group schemes over a ring is reductive.** The tensor product
is the coordinate Hopf algebra of the direct product of groups. -/
theorem tensorProduct {K : FiniteTypeCommHopfAlgCat.{u, u} R}
    (hH : reductiveCommHopfAlgPropertyOver R H) (hK : reductiveCommHopfAlgPropertyOver R K) :
    reductiveCommHopfAlgPropertyOver R (FiniteTypeCommHopfAlgCat.tensorProduct H K) :=
  smoothFiberwiseCommHopfAlgPropertyOver.tensorProduct
    (fun _ _ _ ↦ reductiveCommHopfAlgProperty.tensorProduct) hH hK

end reductiveCommHopfAlgPropertyOver

end TauCeti
