/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Commuting scalar actions on `Ext` groups of modules

Let `k` be a commutative ring, `S` a semiring, and `M` a `k`-module carrying a commuting `S`-module
structure (`[SMulCommClass k S M]`). Scalar multiplication by `s : S` on `M` is a `k`-linear
endomorphism of `M`, so covariant functoriality of `Ext` in its second argument via
`CategoryTheory.Abelian.Ext.postcompOfLinear` induces a ring homomorphism
`TauCeti.extScalarAction : S →+* Module.End k (Ext A (ModuleCat.of k M) n)` for any `k`-module `A`
and degree `n : ℕ`.
-/

public section

noncomputable section

open CategoryTheory Abelian

universe v u

namespace TauCeti

variable (k : Type u) [CommRing k] [Small.{v} k] (S : Type*) [Semiring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Scalar multiplication by `s : S` on `M` as a `k`-linear endomorphism of `ModuleCat.of k M`. -/
private def coeffScalarHom (s : S) : ModuleCat.of k M ⟶ ModuleCat.of k M :=
  have := SMulCommClass.symm k S M
  ModuleCat.ofHom (DistribSMul.toLinearMap k M s)

/-- **The `S`-action on `Extⁿ(A, M)`** induced by functoriality of `Ext` in the target module. -/
def extScalarAction (A : ModuleCat.{v} k) (n : ℕ) :
    S →+* Module.End k (Ext.{v} A (ModuleCat.of k M) n) where
  toFun s := Ext.postcompOfLinear (Ext.mk₀ (coeffScalarHom k S M s)) k A (add_zero n)
  map_one' := by
    have h1 : coeffScalarHom k S M 1 = 𝟙 _ := by ext m; exact one_smul S m
    ext e
    simp [h1]
  map_mul' r s := by
    have hmul : coeffScalarHom k S M (r * s) =
        coeffScalarHom k S M s ≫ coeffScalarHom k S M r := by
      ext m
      exact mul_smul r s m
    ext e
    simp only [mul_apply_eq_comp, LinearMap.flip_apply, Ext.bilinearCompOfLinear_apply_apply,
      hmul, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (add_zero n)]
  map_zero' := by
    have h0 : coeffScalarHom k S M 0 = 0 := by ext m; exact zero_smul S m
    ext e
    simp [h0]
  map_add' r s := by
    have hadd : coeffScalarHom k S M (r + s) =
        coeffScalarHom k S M r + coeffScalarHom k S M s := by
      ext m
      exact add_smul r s m
    ext e
    simp [hadd, Ext.mk₀_add]

@[simp]
lemma extScalarAction_apply (A : ModuleCat.{v} k) (n : ℕ) (s : S)
    (e : Ext.{v} A (ModuleCat.of k M) n) :
    have := SMulCommClass.symm k S M
    extScalarAction k S M A n s e =
      e.comp (Ext.mk₀ (ModuleCat.ofHom (DistribSMul.toLinearMap k M s))) (add_zero n) := by
  simp [extScalarAction, coeffScalarHom]

end TauCeti
