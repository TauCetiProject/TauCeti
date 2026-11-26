/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Module.LinearMap.End
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.CategoryTheory.Preadditive.Endomorphism

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

/-- **The `S`-action on `Extⁿ(A, M)`** induced by functoriality of `Ext` in the target module. -/
def extScalarAction (A : ModuleCat.{v} k) (n : ℕ) :
    S →+* Module.End k (Ext.{v} A (ModuleCat.of k M) n) :=
  have := SMulCommClass.symm k S M
  (ModuleCat.endRingEquiv _).toRingHom.comp
    (((linearExtFunctorObj.{v} k A n).mapEndRingHom (ModuleCat.of k M)).comp
      ((ModuleCat.endRingEquiv (ModuleCat.of k M)).symm.toRingHom.comp
        (Module.toModuleEnd k M)))

@[simp]
lemma extScalarAction_apply (A : ModuleCat.{v} k) (n : ℕ) (s : S)
    (e : Ext.{v} A (ModuleCat.of k M) n) :
    have := SMulCommClass.symm k S M
    extScalarAction k S M A n s e =
      e.comp (Ext.mk₀ (ModuleCat.ofHom (DistribSMul.toLinearMap k M s))) (add_zero n) := by
  simp only [extScalarAction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Module.toModuleEnd_apply, ModuleCat.endRingEquiv_apply,
    CategoryTheory.Functor.mapEndRingHom_apply_asHom]
  simp [linearExtFunctorObj, ModuleCat.endRingEquiv]

end TauCeti
