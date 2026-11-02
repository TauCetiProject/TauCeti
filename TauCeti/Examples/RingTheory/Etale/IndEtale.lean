/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Category.CommAlgCat.BaseChange
import TauCeti.RingTheory.Henselization.IndEtale

/-!
# Base-change checks for ind-étale algebras

These checks exercise arbitrary and successive base change, including reduction modulo five
and a zero base ring, on the henselization of a pair. They also check the computational API
of the scalar-extension adjunction from an importing module.
-/

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

namespace TauCeti.Examples

-- No flatness or finiteness of the new base is needed.
example (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.IndEtale R S] :
    Algebra.IndEtale T (T ⊗[R] S) := inferInstance

-- A successive scalar extension uses the result over the intermediate base.
example (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra T U] [Algebra.IndEtale R S] :
    Algebra.IndEtale U (U ⊗[T] (T ⊗[R] S)) := inferInstance

-- The henselization supplies a filtered presentation without assuming it is étale.
-- Select the module structure supplied by its algebra, rather than the competing integer action.
example :
    let H := Henselization.algebra (Ideal.span {(5 : ℤ)})
    letI : Module ℤ H := (inferInstance : _root_.Algebra ℤ H).toModule
    Algebra.IndEtale (ZMod 5) ((ZMod 5) ⊗[ℤ] H) := by
  dsimp
  infer_instance

-- The preceding change of base is not flat.
example : ¬ Module.Flat ℤ (ZMod 5) := by
  intro _
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ZMod 5)
    (mem_nonZeroDivisors_of_ne_zero (by decide : (5 : ℤ) ≠ 0))
  have hn : (1 : ZMod 5) ≠ 0 := by decide
  exact hn (h (show (5 : ℤ) • (1 : ZMod 5) = (5 : ℤ) • 0 by decide))

-- The zero ring is allowed as a new base, and as the original ring.
example (R : Type u) [CommRing R] (I : Ideal R) :
    Algebra.IndEtale (R ⧸ (⊤ : Ideal R))
      ((R ⧸ (⊤ : Ideal R)) ⊗[R] Henselization.algebra I) := inferInstance

example : Algebra.IndEtale (ZMod 1)
    ((ZMod 1) ⊗[ZMod 1] Henselization.algebra (⊤ : Ideal (ZMod 1))) := inferInstance

-- Left adjointness gives preservation for every diagram size, not only filtered ones.
example (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    PreservesColimitsOfSize.{u, u}
      (CommAlgCat.extendScalars.{u, v, max v w} R S) := inferInstance

-- The source algebras need not live in the scalar ring's universe.
example (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (A A' : CommAlgCat.{w} R) (f : A ⟶ A') :
    ((CommAlgCat.extendScalars R S).map f).hom =
      Algebra.TensorProduct.map (AlgHom.id S S) f.hom := by
  rw [CommAlgCat.extendScalars_map_hom]

-- Both directions of the adjunction can be computed without unfolding its construction.
example (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (A : CommAlgCat.{max v w} R) (B : CommAlgCat.{max v w} S)
    (f : (CommAlgCat.extendScalars R S).obj A ⟶ B) (a : A) :
    ((CommAlgCat.extendRestrictScalarsAdj R S).homEquiv A B f).hom a =
      f.hom (1 ⊗ₜ[R] a) := by
  rw [CommAlgCat.extendRestrictScalarsAdj_homEquiv]
  exact CommAlgCat.extendScalarsHomEquiv_apply R S A B f a

example (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (A : CommAlgCat.{max v w} R) (B : CommAlgCat.{max v w} S)
    (f : A ⟶ (CommAlgCat.restrictScalars (algebraMap R S)).obj B) (s : S) (a : A) :
    (((CommAlgCat.extendRestrictScalarsAdj R S).homEquiv A B).symm f).hom
      (s ⊗ₜ[R] a) = s • f.hom a := by
  rw [CommAlgCat.extendRestrictScalarsAdj_homEquiv]
  exact CommAlgCat.extendScalarsHomEquiv_symm_tmul R S A B f s a

end TauCeti.Examples
