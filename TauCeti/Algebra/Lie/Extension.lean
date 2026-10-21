/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Extension
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Extensions built from low-degree cocycles

Lie algebra cocycles of degree one and two with values in an `L`-module `M` shear direct products:

* a 1-cocycle, that is a Lie derivation `D : L → M`, shears the action of `L` on `M × R` to
  `⁅x, (m, t)⁆ = (⁅x, m⁆ + t • D x, 0)`, an extension of the trivial module `R` by `M`;
* a 2-cocycle `c` shears the bracket of `L × M`. Mathlib's `LieAlgebra.ofTwoCocycle c` is this Lie
  algebra, and Mathlib packages it as an extension (`LieAlgebra.Extension.ofTwoCocycle`) only when
  `M` is itself given the structure of an abelian Lie algebra.

This file works with an arbitrary module `M` and supplies:

* `LieModule.Cohomology.range_d₁₂_le_twoCocycle`: every coboundary is a 2-cocycle;
* `LieDerivation.ofD₁₂EqZero`: a 1-cochain `f` with `d₁₂ f = 0` as a Lie derivation;
* `LieDerivation.ShearedModule D`: the module `M × R` sheared by a Lie derivation `D`, with its
  identification `LieDerivation.ShearedModule.ofProd` with `M × R`;
* `LieAlgebra.ofProdLinearEquiv`: the identification `LieAlgebra.ofProd` with `L × M` as a linear
  equivalence, so that finiteness transfers to `LieAlgebra.ofTwoCocycle c`;
* `LieAlgebra.ofTwoCocycle.proj`: the projection onto `L` as a surjective Lie algebra
  homomorphism, whose kernel `0 × M` is an abelian ideal.

These let structure theorems about Lie modules and abelian ideals, such as Weyl's theorem and Levi
complements, be applied to the sheared objects, for instance to show that a cocycle is a
coboundary.

## Implementation notes

`LieDerivation.ShearedModule D` is a type synonym for `M × R`, so that the action sheared by `D` is
a global instance on its own carrier rather than a local structure on `M × R`. As with Mathlib's
`LieAlgebra.ofProd`, all access goes through the linear equivalence
`LieDerivation.ShearedModule.ofProd`, which is the identity, and
`LieDerivation.ShearedModule.ofProd_symm_lie` restates the bracket field of the instance, so it is
proved by `rfl`.
-/

public section

open LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieModule.Cohomology

/-- Every coboundary is a 2-cocycle. -/
lemma range_d₁₂_le_twoCocycle : LinearMap.range (d₁₂ R L M) ≤ twoCocycle R L M := by
  rintro _ ⟨f, rfl⟩
  rw [mem_twoCocycle_iff, ← LinearMap.comp_apply, d₂₃_comp_d₁₂, LinearMap.zero_apply]

end LieModule.Cohomology

namespace LieDerivation

/-- A 1-cochain `f` with `d₁₂ f = 0` satisfies the Leibniz rule, so it is a Lie derivation. -/
def ofD₁₂EqZero (f : oneCochain R L M) (hf : d₁₂ R L M f = 0) : LieDerivation R L M where
  toLinearMap := f
  leibniz' x y := by
    have h : d₁₂ R L M f x y = 0 := by simp [hf, ← twoCochain_val_apply]
    rw [d₁₂_apply_apply, sub_eq_zero] at h
    exact h.symm

@[simp]
lemma coe_ofD₁₂EqZero (f : oneCochain R L M) (hf : d₁₂ R L M f = 0) :
    ⇑(ofD₁₂EqZero f hf) = f := (rfl)

/-- The module `M × R` with the action of `L` sheared by a Lie derivation `D`:
`⁅x, (m, t)⁆ = (⁅x, m⁆ + t • D x, 0)`. Use `LieDerivation.ShearedModule.ofProd` to pass between it
and `M × R`. -/
@[expose] def ShearedModule (_D : LieDerivation R L M) : Type _ := M × R

namespace ShearedModule

variable (D : LieDerivation R L M)

instance : AddCommGroup D.ShearedModule := inferInstanceAs (AddCommGroup (M × R))

instance : Module R D.ShearedModule := inferInstanceAs (Module R (M × R))

/-- The identification of `M × R` with the module sheared by `D`, as a linear equivalence. -/
def ofProd : (M × R) ≃ₗ[R] D.ShearedModule := LinearEquiv.refl R (M × R)

instance [Module.Finite R M] : Module.Finite R D.ShearedModule :=
  Module.Finite.equiv (ofProd D)

instance : LieRingModule L D.ShearedModule where
  bracket x v := ofProd D (⁅x, ((ofProd D).symm v).1⁆ + ((ofProd D).symm v).2 • D x, 0)
  add_lie x y v := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, add_lie, smul_add, Prod.mk_add_mk, add_zero]
    abel_nf
  lie_add x v w := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, Prod.fst_add, Prod.snd_add, lie_add,
      add_smul, Prod.mk_add_mk, add_zero]
    abel_nf
  leibniz_lie x y v := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, lie_add, lie_smul, D.apply_lie_eq_sub,
      zero_smul, add_zero, Prod.mk_add_mk, smul_sub, leibniz_lie x y ((ofProd D).symm v).1]
    abel_nf

@[simp]
lemma ofProd_symm_lie (x : L) (v : D.ShearedModule) :
    (ofProd D).symm ⁅x, v⁆ = (⁅x, ((ofProd D).symm v).1⁆ + ((ofProd D).symm v).2 • D x, 0) :=
  (rfl)

instance : LieModule R L D.ShearedModule where
  smul_lie t x v := (ofProd D).symm.injective <| by simp [smul_add, smul_comm t]
  lie_smul t x v := (ofProd D).symm.injective <| by simp [smul_add, smul_smul, mul_comm t]

end ShearedModule

end LieDerivation

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
