/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.Cube.Basic

/-!
# The Euler characteristic of a cube of modules

Let `F : Finset ι ⥤ ModuleCat R` be a commutative cube of finite free modules. The term of its
signed totalization `F.cubeComplex` in degree `r` is the biproduct of the vertices `F(S)` of
height `#S = r`, so its rank is the sum of their ranks, and the Euler characteristic of the terms
of the totalization is the signed count `∑ₛ (-1) ^ #S rank F(S)` over all vertices. The edge maps
of the cube play no role.

For the cube of resolutions of a link diagram, this identifies the Euler characteristic of the
terms of the Khovanov complex with the enhanced state sum; Euler–Poincaré then transfers it to the
homology.

## Main results

* The terms of the totalization of a cube of finite, respectively free, modules are finite,
  respectively free.
* `CategoryTheory.Functor.finrank_cubeComplex_X`: the rank of the degree `r` term is the sum of
  the ranks of the vertices of height `r`.
* `CategoryTheory.Functor.eulerChar_cubeComplex`: the Euler characteristic of the terms of the
  totalization is `∑ₛ (-1) ^ #S rank F(S)`.

## References

* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.
-/

public section

open CategoryTheory Limits Finset

universe w v u

namespace CategoryTheory.Functor

variable {R : Type u} [Ring R] {ι : Type w} [Fintype ι] [LinearOrder ι]
  (F : Finset ι ⥤ ModuleCat.{v} R)

instance [∀ S, Module.Free R (F.obj S)] (r : ℤ) : Module.Free R (F.cubeComplex.X r) :=
  .of_equiv (F.cubeComplexXIso r).toLinearEquiv.symm

instance [∀ S, Module.Finite R (F.obj S)] (r : ℤ) : Module.Finite R (F.cubeComplex.X r) :=
  .equiv (F.cubeComplexXIso r).toLinearEquiv.symm

variable [StrongRankCondition R] [∀ S, Module.Free R (F.obj S)] [∀ S, Module.Finite R (F.obj S)]

/-- The rank of the degree `r` term of the totalization of a cube of finite free modules is the
sum of the ranks of its vertices of height `r`. -/
theorem finrank_cubeComplex_X (r : ℤ) :
    Module.finrank R (F.cubeComplex.X r) =
      ∑ S with (#S : ℤ) = r, Module.finrank R (F.obj S) := by
  rw [(F.cubeComplexXIso r).toLinearEquiv.finrank_eq, ModuleCat.finrank_biproduct]
  exact (Finset.sum_subtype (p := fun S : Finset ι ↦ (#S : ℤ) = r) _ mem_filter_univ
    fun S ↦ Module.finrank R (F.obj S)).symm

/-- **The Euler characteristic of a cube of finite free modules**: the alternating sum of the
ranks of the terms of its signed totalization is the signed count `∑ₛ (-1) ^ #S rank F(S)` of
the ranks of its vertices. -/
theorem eulerChar_cubeComplex :
    F.cubeComplex.eulerChar = ∑ S, (-1 : ℤ) ^ #S * Module.finrank R (F.obj S) := by
  -- Only the heights of actual vertices carry nonzero terms; group the vertices by height.
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _
    (univ.image fun S : Finset ι ↦ (#S : ℤ))]
  · rw [← sum_fiberwise_of_maps_to (g := fun S : Finset ι ↦ (#S : ℤ))
      fun S _ ↦ mem_image_of_mem (fun S : Finset ι ↦ (#S : ℤ)) (mem_univ S)]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [finrank_cubeComplex_X, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun S hS ↦ ?_
    rw [(mem_filter.mp hS).2.symm]
    simp only [ComplexShape.χ, ComplexShape.eulerCharSignsUpInt_χ, Int.coe_negOnePow_natCast]
  · intro r hr
    by_contra h
    apply hr
    dsimp only
    rw [finrank_cubeComplex_X]
    refine sum_eq_zero fun S hS ↦ absurd ?_ h
    rw [← (mem_filter.mp hS).2]
    exact mem_image_of_mem (fun S : Finset ι ↦ (#S : ℤ)) (mem_univ S)

end CategoryTheory.Functor
