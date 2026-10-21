/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Extension
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Extensions built from 2-cocycles

A 2-cocycle `c` of a Lie algebra `L` with values in an `L`-module `M` shears the bracket of `L × M`.
Mathlib's `LieAlgebra.ofTwoCocycle c` is this Lie algebra, and Mathlib packages it as an extension
(`LieAlgebra.Extension.ofTwoCocycle`) only when `M` is itself given the structure of an abelian Lie
algebra.

This file works with an arbitrary module `M` and supplies:

* `LieAlgebra.ofProdLinearEquiv`: the identification `LieAlgebra.ofProd` with `L × M` as a linear
  equivalence, so that finiteness transfers to `LieAlgebra.ofTwoCocycle c`;
* `LieAlgebra.ofTwoCocycle.proj`: the projection onto `L` as a surjective Lie algebra
  homomorphism, whose kernel `0 × M` is an abelian ideal.

These let structure theorems about abelian ideals, such as the existence of Levi complements, be
applied to the sheared Lie algebra, for instance to show that a 2-cocycle is a coboundary. The
degree-one counterpart, the module sheared by a Lie derivation, is
`LieDerivation.ShearedModule` in `TauCeti.Algebra.Lie.Derivation.Cocycle`.
-/

public section

open LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

variable (c : twoCocycle R L M)

/-- The identification `LieAlgebra.ofProd` of `L × M` with the Lie algebra sheared by a 2-cocycle,
as a linear equivalence. -/
def ofProdLinearEquiv : (L × M) ≃ₗ[R] ofTwoCocycle c where
  __ := ofProd c
  map_add' := of_add c
  map_smul' := of_smul c

@[simp]
lemma coe_ofProdLinearEquiv : ⇑(ofProdLinearEquiv c) = ofProd c := (rfl)

@[simp]
lemma coe_ofProdLinearEquiv_symm : ⇑(ofProdLinearEquiv c).symm = (ofProd c).symm := (rfl)

instance [Module.Finite R L] [Module.Finite R M] : Module.Finite R (ofTwoCocycle c) :=
  Module.Finite.equiv (ofProdLinearEquiv c)

namespace ofTwoCocycle

/-- The projection of the Lie algebra sheared by a 2-cocycle onto `L`, as a Lie algebra
homomorphism. -/
def proj : ofTwoCocycle c →ₗ⁅R⁆ L where
  toFun x := ((ofProd c).symm x).1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {_ _} := by simp [bracket_ofTwoCocycle]

@[simp]
lemma proj_apply (x : ofTwoCocycle c) : proj c x = ((ofProd c).symm x).1 := (rfl)

lemma proj_surjective : Function.Surjective (proj c) :=
  fun x ↦ ⟨ofProd c (x, 0), by simp⟩

lemma mem_ker_proj {x : ofTwoCocycle c} : x ∈ (proj c).ker ↔ ((ofProd c).symm x).1 = 0 :=
  LieHom.mem_ker

/-- The kernel `0 × M` of the projection is an abelian ideal. -/
instance : IsLieAbelian (proj c).ker where
  trivial a b := by
    have ha := (mem_ker_proj c).1 a.2
    have hb := (mem_ker_proj c).1 b.2
    refine Subtype.ext ((ofProd c).symm.injective ?_)
    simp [bracket_ofTwoCocycle, ha, hb]

end ofTwoCocycle

end LieAlgebra
