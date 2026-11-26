/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Ext.RegularTensor
public import TauCeti.RingTheory.MatlisDuality.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.StandardResolution
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The regular-dual Ext tensor formula for path algebras

For the path algebra `A = kQ` of a quiver with finitely many paths and `D = Hom_k(-, k)`,
`Ext¹_A(D A, A) ⊗_A M ≃ Ext¹_A(D A, M)` canonically for every left `A`-module `M`.
Here `D A` is the dual of the right regular module. The comparison is natural in `M` and
sends a pure tensor to the extension obtained by pushout along the map `a ↦ a • m`.
This describes the tensor functor used in the hereditary construction of preprojective algebras.

The formula uses the hereditary property of path algebras and `ModuleCat.extRegularTensorEquiv`.

## References

* J. Grant, *The Nakayama automorphism of a self-injective preprojective algebra*, Proposition 2.5.
-/

public section

open CategoryTheory CategoryTheory.Abelian ModuleCat
open scoped ModuleCat.Algebra ModuleCat

namespace TauCeti.PathAlgebra

universe u v w

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [Finite (Quiver.TotalPath Q)]

local notation "A" => pathAlgebra k Q
local notation "DA" => of A (MatlisDual k k A)

/-- Over a path algebra with finitely many paths, `Ext¹(D(kQ), -)` is computed by tensoring with
`Ext¹(D(kQ), kQ)`. The right action on the first tensor factor comes from right multiplication on
`kQ`. -/
noncomputable def extDualRegularTensorEquiv (M : ModuleCat.{max u v w} A) :
    BalancedTensorProduct k A (Ext DA (of A A) 1) M ≃ₗ[k] Ext DA M 1 := by
  have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have : Module.Finite k (MatlisDual k k A) :=
    Module.Finite.equiv (MatlisDual.equivLinearMap k k A).symm
  have : Module.Finite A (MatlisDual k k A) :=
    Module.Finite.of_restrictScalars_finite k A _
  exact extRegularTensorEquiv k DA M

/-- The path-algebra comparison takes a tensor with `m` to pushout along `a ↦ a • m`. -/
@[simp]
theorem extDualRegularTensorEquiv_tmul {M : ModuleCat.{max u v w} A}
    (x : Ext DA (of A A) 1) (m : M) :
    extDualRegularTensorEquiv k Q M (BalancedTensorProduct.tmul k A x m) =
      x.comp (Ext.mk₀ (ofHom (LinearMap.toSpanSingleton A M m))) (add_zero 1) := by
  simp [extDualRegularTensorEquiv]

/-- The path-algebra tensor formula commutes with pushforward along a module morphism. -/
theorem extDualRegularTensorEquiv_naturality {M N : ModuleCat.{max u v w} A} (g : M ⟶ N)
    (x : BalancedTensorProduct k A (Ext DA (of A A) 1) M) :
    extDualRegularTensorEquiv k Q N (BalancedTensorProduct.lTensor k _ g.hom x) =
      (extDualRegularTensorEquiv k Q M x).comp (Ext.mk₀ g) (add_zero 1) := by
  simpa only [extDualRegularTensorEquiv, extRegularTensorEquiv_apply] using
    extRegularTensor_naturality k g x

end TauCeti.PathAlgebra
