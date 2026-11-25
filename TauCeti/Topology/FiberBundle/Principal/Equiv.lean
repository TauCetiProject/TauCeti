/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Equivalences of principal bundles

An **equivalence** `TauCeti.PrincipalBundle.Equiv H Q Q'` of two bundles `Q` and `Q'` over the
same base, each with a right action of `H` on its fibres, is a family of bijections
`Q x ≃ Q' x` that is `H`-equivariant and induces continuous maps of total spaces in both
directions. For principal `H`-bundles these are the isomorphisms of principal bundles over the
identity of the base. Equivalences form a groupoid (`refl`, `symm`, `trans`, with the groupoid
laws `symm_symm`, `refl_trans`, `trans_refl`, `self_trans_symm`, `symm_trans_self` and
`symm_trans`).

## Main definitions

* `TauCeti.PrincipalBundle.Equiv`: an equivariant fibrewise bijection, continuous on total spaces
  in both directions.
* `TauCeti.PrincipalBundle.Equiv.refl`, `TauCeti.PrincipalBundle.Equiv.symm`,
  `TauCeti.PrincipalBundle.Equiv.trans`: the identity, inverse and composite equivalences.
-/

public section

open Bundle MulOpposite

namespace TauCeti.PrincipalBundle

variable {X : Type*} (H : Type*) [Group H] (Q Q' Q'' : X → Type*)
  [TopologicalSpace (TotalSpace H Q)] [TopologicalSpace (TotalSpace H Q')]
  [TopologicalSpace (TotalSpace H Q'')]
  [∀ x, MulAction Hᵐᵒᵖ (Q x)] [∀ x, MulAction Hᵐᵒᵖ (Q' x)] [∀ x, MulAction Hᵐᵒᵖ (Q'' x)]

/-- An **equivalence of principal `H`-bundles** `Q ≃ Q'` over the same base: a family of
bijections between the fibres, equivariant for the right action of `H`, inducing continuous maps
of total spaces in both directions. -/
structure Equiv where
  /-- The bijection between fibres. -/
  toEquiv : ∀ x, Q x ≃ Q' x
  /-- The induced map of total spaces is continuous. -/
  continuous_toFun : Continuous fun q : TotalSpace H Q ↦
    (⟨q.proj, toEquiv q.proj q.snd⟩ : TotalSpace H Q')
  /-- The inverse map of total spaces is continuous. -/
  continuous_invFun : Continuous fun q : TotalSpace H Q' ↦
    (⟨q.proj, (toEquiv q.proj).symm q.snd⟩ : TotalSpace H Q)
  /-- The bijection is equivariant. -/
  map_smul : ∀ (x : X) (q : Q x) (h : H), toEquiv x (op h • q) = op h • toEquiv x q

namespace Equiv

variable {H Q Q' Q''}

attribute [simp] map_smul

/-- The inverse of the bijection of an equivalence is equivariant. -/
@[simp]
theorem map_smul_symm (ψ : Equiv H Q Q') (x : X) (q : Q' x) (h : H) :
    (ψ.toEquiv x).symm (op h • q) = op h • (ψ.toEquiv x).symm q := by
  rw [_root_.Equiv.symm_apply_eq, ψ.map_smul, _root_.Equiv.apply_symm_apply]

/-- Two equivalences of principal bundles are equal when their bijections agree pointwise. -/
@[ext]
theorem ext {ψ ψ' : Equiv H Q Q'} (h : ∀ x q, ψ.toEquiv x q = ψ'.toEquiv x q) : ψ = ψ' := by
  obtain ⟨ψ, _⟩ := ψ
  obtain ⟨ψ', _⟩ := ψ'
  congr
  funext x
  exact _root_.Equiv.ext (h x)

variable (H Q) in
/-- The identity equivalence of a principal bundle. -/
@[expose, refl]
def refl : Equiv H Q Q where
  toEquiv _ := _root_.Equiv.refl _
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  map_smul _ _ _ := rfl

/-- The inverse of an equivalence of principal bundles. -/
@[expose, symm]
def symm (ψ : Equiv H Q Q') : Equiv H Q' Q where
  toEquiv x := (ψ.toEquiv x).symm
  continuous_toFun := ψ.continuous_invFun
  continuous_invFun := ψ.continuous_toFun
  map_smul := ψ.map_smul_symm

/-- The composite of two equivalences of principal bundles. -/
@[expose, trans]
def trans (ψ : Equiv H Q Q') (ψ' : Equiv H Q' Q'') : Equiv H Q Q'' where
  toEquiv x := (ψ.toEquiv x).trans (ψ'.toEquiv x)
  continuous_toFun := ψ'.continuous_toFun.comp ψ.continuous_toFun
  continuous_invFun := ψ.continuous_invFun.comp ψ'.continuous_invFun
  map_smul x q h := by simp only [_root_.Equiv.trans_apply, ψ.map_smul, ψ'.map_smul]

@[simp]
theorem refl_toEquiv (x : X) : (refl H Q).toEquiv x = _root_.Equiv.refl (Q x) :=
  (rfl)

@[simp]
theorem symm_toEquiv (ψ : Equiv H Q Q') (x : X) : ψ.symm.toEquiv x = (ψ.toEquiv x).symm :=
  (rfl)

@[simp]
theorem trans_toEquiv (ψ : Equiv H Q Q') (ψ' : Equiv H Q' Q'') (x : X) :
    (ψ.trans ψ').toEquiv x = (ψ.toEquiv x).trans (ψ'.toEquiv x) :=
  (rfl)

@[simp]
theorem symm_symm (ψ : Equiv H Q Q') : ψ.symm.symm = ψ :=
  (rfl)

@[simp]
theorem refl_symm : (refl H Q).symm = refl H Q :=
  (rfl)

@[simp]
theorem refl_trans (ψ : Equiv H Q Q') : (refl H Q).trans ψ = ψ :=
  (rfl)

@[simp]
theorem trans_refl (ψ : Equiv H Q Q') : ψ.trans (refl H Q') = ψ :=
  (rfl)

@[simp]
theorem self_trans_symm (ψ : Equiv H Q Q') : ψ.trans ψ.symm = refl H Q :=
  ext fun x q ↦ (ψ.toEquiv x).symm_apply_apply q

@[simp]
theorem symm_trans_self (ψ : Equiv H Q Q') : ψ.symm.trans ψ = refl H Q' :=
  ext fun x q ↦ (ψ.toEquiv x).apply_symm_apply q

@[simp]
theorem symm_trans (ψ : Equiv H Q Q') (ψ' : Equiv H Q' Q'') :
    (ψ.trans ψ').symm = ψ'.symm.trans ψ.symm :=
  (rfl)

end Equiv

end TauCeti.PrincipalBundle
