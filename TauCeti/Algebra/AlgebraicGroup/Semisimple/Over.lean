/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Semisimple.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Semisimple.Product
import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive
import Mathlib.RingTheory.Etale.Descent

/-!
# Semisimple affine group schemes over a ring

A semisimple affine group scheme over `Spec R` is smooth over `R` and has connected semisimple
geometric fibers. In Hopf coordinates, its geometric fibers are the scalar extensions `k ⊗[R] H`
for algebraically closed fields `k` equipped with an `R`-algebra structure. This is the
semisimple counterpart of `TauCeti.reductiveCommHopfAlgPropertyOver`; both are instances of
`TauCeti.smoothFiberwiseCommHopfAlgPropertyOver`, and as there, neither reducedness of `R` nor a
field hypothesis on `R` is required.

Since semisimple groups over a field are reductive, every semisimple group scheme over `R` is
reductive over `R`. Both conditions are stable under arbitrary base change and under direct
products, the latter because scalar extension commutes with tensor products of coordinate
Hopf algebras. Over a `ℚ`-algebra, semisimplicity also descends along faithfully flat ring maps:
smoothness descends by `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`, and
semisimplicity of fibers descends along extensions of fields of characteristic zero.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgPropertyOver`: smooth affine group schemes over a ring whose
  geometric fibers are semisimple.
* `TauCeti.semisimpleCommHopfAlgPropertyOver.reductive`: a semisimple group scheme over a ring is
  reductive over that ring.
* `TauCeti.semisimpleCommHopfAlgPropertyOver.baseChange`: semisimplicity over a ring is preserved
  by arbitrary base change.
* `TauCeti.semisimpleCommHopfAlgPropertyOver.tensorProduct`: direct products of semisimple group
  schemes over a ring are semisimple.
* `TauCeti.semisimpleCommHopfAlgPropertyOver.of_baseChange_of_faithfullyFlat`: over a `ℚ`-algebra,
  semisimplicity descends along faithfully flat base change.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1.
* SGA 3, Exposé XIX, Définition 2.7.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

/-- A finite-type affine group scheme over a commutative ring is semisimple when it is smooth
and all of its geometric fibers are connected semisimple groups. -/
def semisimpleCommHopfAlgPropertyOver (R : Type u) [CommRing R] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} R) :=
  smoothFiberwiseCommHopfAlgPropertyOver semisimpleCommHopfAlgProperty R

/-- The geometric-fiber characterization of a semisimple affine group scheme over a ring. -/
@[simp]
theorem semisimpleCommHopfAlgPropertyOver_iff (R : Type u) [CommRing R]
    (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    semisimpleCommHopfAlgPropertyOver R H ↔
      Algebra.Smooth R H ∧
        ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
          semisimpleCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver_iff _ R H

/-- Semisimplicity over a ring is invariant under coordinate-Hopf-algebra isomorphism. -/
instance (R : Type u) [CommRing R] :
    (semisimpleCommHopfAlgPropertyOver R).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| ObjectProperty.IsClosedUnderIsomorphisms <|
    smoothFiberwiseCommHopfAlgPropertyOver semisimpleCommHopfAlgProperty R

namespace semisimpleCommHopfAlgPropertyOver

variable {R : Type u} [CommRing R] {H : FiniteTypeCommHopfAlgCat.{u, u} R}

/-- A semisimple group scheme is smooth over its base. -/
theorem smooth (hH : semisimpleCommHopfAlgPropertyOver R H) : Algebra.Smooth R H :=
  smoothFiberwiseCommHopfAlgPropertyOver.smooth hH

/-- Every geometric fiber of a semisimple group scheme is semisimple. -/
theorem geometricFiber (hH : semisimpleCommHopfAlgPropertyOver R H)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    semisimpleCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.baseChange (K := k) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver.geometricFiber hH k

/-- A semisimple group scheme over a ring is reductive over that ring. -/
theorem reductive (hH : semisimpleCommHopfAlgPropertyOver R H) :
    reductiveCommHopfAlgPropertyOver R H :=
  (reductiveCommHopfAlgPropertyOver_iff R H).mpr
    ⟨hH.smooth, fun k _ _ _ ↦ (hH.geometricFiber k).reductive⟩

/-- Semisimplicity of affine group schemes is preserved by arbitrary base change. -/
theorem baseChange (hH : semisimpleCommHopfAlgPropertyOver R H)
    (S : Type u) [CommRing S] [Algebra R S] :
    semisimpleCommHopfAlgPropertyOver S (FiniteTypeCommHopfAlgCat.baseChange (K := S) H) :=
  smoothFiberwiseCommHopfAlgPropertyOver.baseChange hH S

/-- **A direct product of semisimple group schemes over a ring is semisimple.** The tensor
product is the coordinate Hopf algebra of the direct product of groups. -/
theorem tensorProduct {K : FiniteTypeCommHopfAlgCat.{u, u} R}
    (hH : semisimpleCommHopfAlgPropertyOver R H) (hK : semisimpleCommHopfAlgPropertyOver R K) :
    semisimpleCommHopfAlgPropertyOver R (FiniteTypeCommHopfAlgCat.tensorProduct H K) :=
  smoothFiberwiseCommHopfAlgPropertyOver.tensorProduct
    (fun _ _ _ ↦ semisimpleCommHopfAlgProperty.tensorProduct) hH hK

/-- **Semisimplicity descends along faithfully flat base change in characteristic zero.** If
`R` is a `ℚ`-algebra, `R → S` is faithfully flat and `S ⊗[R] H` is semisimple over `S`, then `H`
is semisimple over `R`. The characteristic-zero hypothesis is used to descend semisimplicity of
geometric fibers along extensions of algebraically closed fields. -/
theorem of_baseChange_of_faithfullyFlat [Algebra ℚ R] (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (hH : semisimpleCommHopfAlgPropertyOver S (FiniteTypeCommHopfAlgCat.baseChange (K := S) H)) :
    semisimpleCommHopfAlgPropertyOver R H := by
  let _ : Algebra.Smooth S (S ⊗[R] H) := hH.smooth
  refine (semisimpleCommHopfAlgPropertyOver_iff R H).mpr
    ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat S, fun k _ _ _ ↦ ?_⟩
  have : CharZero k :=
    (RingHom.charZero_iff ((algebraMap R k).comp (algebraMap ℚ R)).injective).mp inferInstance
  -- The algebraic closure `K` of a residue field of the nonzero ring `k ⊗[R] S` is an
  -- algebraically closed extension of both `k` and `S` over `R`.
  let _ : Algebra S (k ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  let _ : Field (k ⊗[R] S ⧸ m) := Ideal.Quotient.field m
  let K := AlgebraicClosure (k ⊗[R] S ⧸ m)
  let eS := FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := S) R K H
  let ek := FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := k) R K H
  exact semisimpleCommHopfAlgProperty.of_baseChange (K := K) <|
    (semisimpleCommHopfAlgProperty K).prop_of_iso (eS ≪≫ ek.symm) (hH.geometricFiber K)

end semisimpleCommHopfAlgPropertyOver

/-- Semisimplicity over a ring is stronger than reductivity over that ring. -/
theorem semisimpleCommHopfAlgPropertyOver_le_reductiveCommHopfAlgPropertyOver
    (R : Type u) [CommRing R] :
    semisimpleCommHopfAlgPropertyOver R ≤ reductiveCommHopfAlgPropertyOver R :=
  fun _ hH ↦ hH.reductive

end TauCeti
