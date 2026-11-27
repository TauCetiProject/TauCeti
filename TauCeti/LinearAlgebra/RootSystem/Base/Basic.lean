/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Base
import TauCeti.GroupTheory.Perm.Basic

/-!
# Bases and simple-root support transport of a root pairing

This file records the action of automorphisms on bases (`RootPairing.Base.map_one`,
`RootPairing.Base.map_mul`, `RootPairing.Base.map_eq_of_forall_mem_support`,
`RootPairing.Base.mem_support_indexEquiv_iff`), and the bijection on simple-root supports induced
by a base-preserving equivalence of root pairings (`RootPairing.Equiv.supportEquiv`).
-/

public section

namespace RootPairing

namespace Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

section Map

/-- Transporting a base along the identity automorphism does nothing. -/
@[simp]
protected theorem map_one (b : P.Base) : b.map (1 : P.Aut) = b := by
  classical
  ext i
  simp

/-- Transporting a base along a product of automorphisms transports it along each factor in turn,
the right-hand factor first. -/
protected theorem map_mul (b : P.Base) (g h : P.Aut) : b.map (g * h) = (b.map h).map g := by
  classical
  ext i
  simp [Finset.image_image]

/-- An automorphism carrying every simple root of `b` to a simple root fixes `b`. -/
theorem map_eq_of_forall_mem_support {b : P.Base} {u : P.Aut}
    (hu : ∀ j ∈ b.support, u.indexEquiv j ∈ b.support) : b.map u = b := by
  classical
  exact ext <| Finset.eq_of_subset_of_card_le (by simpa [Finset.image_subset_iff] using hu)
    (by rw [support_map_eq, Finset.card_image_of_injective _ u.indexEquiv.injective])

/-- An automorphism carrying `b.support` into itself maps a root index into `b.support` if and only
if the index already lies in `b.support`, because `b.support` is finite. -/
theorem mem_support_indexEquiv_iff (b : P.Base) {u : P.Aut}
    (hu : ∀ j ∈ b.support, u.indexEquiv j ∈ b.support) (i : ι) :
    u.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  classical
  have hsupp : b.support.image u.indexEquiv = b.support := by
    rw [← support_map_eq, map_eq_of_forall_mem_support hu]
  refine ⟨fun hi ↦ ?_, hu i⟩
  rw [← hsupp, Finset.mem_image] at hi
  obtain ⟨j, hj, hij⟩ := hi
  exact u.indexEquiv.injective hij ▸ hj

end Map

end Base

section EquivBase

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  (e : P.Equiv Q) {b : P.Base} {b' : Q.Base}
  (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support)

/-- The bijection `b.support ≃ b'.support` induced by a base-preserving equivalence. -/
def Equiv.supportEquiv : b.support ≃ b'.support where
  toFun i := ⟨e.indexEquiv i, (hb i).mp i.property⟩
  invFun j := ⟨e.indexEquiv.symm j, (hb _).mpr (by simp [j.property])⟩
  left_inv i := Subtype.ext (e.indexEquiv.symm_apply_apply i)
  right_inv j := Subtype.ext (e.indexEquiv.apply_symm_apply j)

/-- `Equiv.supportEquiv` acts on root indices by `e.indexEquiv`. -/
@[simp] theorem Equiv.coe_supportEquiv_apply (i : b.support) :
    (e.supportEquiv hb i : ι₂) = e.indexEquiv i := (rfl)

/-- `(Equiv.supportEquiv hb).symm` acts on root indices by `e.indexEquiv.symm`. -/
@[simp] theorem Equiv.coe_supportEquiv_symm_apply (j : b'.support) :
    ((e.supportEquiv hb).symm j : ι) = e.indexEquiv.symm j := (rfl)

/-- A base-preserving automorphism's powers act on simple roots via `supportEquiv`. -/
theorem Equiv.coe_supportEquiv_pow {σ : P.Aut} {b : P.Base}
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) (n : ℕ) (j : b.support) :
    (((σ.supportEquiv hb ^ n) j : b.support) : ι) = (σ.indexEquiv ^ n) (j : ι) := by
  rw [_root_.Equiv.Perm.coe_pow, _root_.Equiv.Perm.coe_pow]
  exact Function.Semiconj.iterate_right (fun i ↦ σ.coe_supportEquiv_apply hb i) n j

/-- Two simple roots of `b` lie in the same cycle of `σ.supportEquiv hb` iff they lie in the
same cycle of `σ.indexEquiv`. -/
@[simp] theorem Equiv.sameCycle_supportEquiv_iff {σ : P.Aut} {b : P.Base}
    (hb : ∀ i, i ∈ b.support ↔ σ.indexEquiv i ∈ b.support) {i j : b.support} :
    _root_.Equiv.Perm.SameCycle (σ.supportEquiv hb) i j ↔
      _root_.Equiv.Perm.SameCycle σ.indexEquiv (i : ι) (j : ι) :=
  (Function.Semiconj.sameCycle_iff (σ := σ.supportEquiv hb) (g := fun x : b.support ↦ (x : ι))
    (fun x ↦ σ.coe_supportEquiv_apply hb x) Subtype.val_injective).symm

end EquivBase

section SupportPerm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The permutation of `b.support` induced by an automorphism stabilizing `b.support`. -/
noncomputable def Base.supportPerm (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) : _root_.Equiv.Perm b.support :=
  σ.supportEquiv fun i ↦ (b.mem_support_indexEquiv_iff hσ i).symm

@[simp] theorem Base.coe_supportPerm_apply (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : b.support) :
    (b.supportPerm hσ i : ι) = σ.indexEquiv i := (rfl)

@[simp] theorem Base.coe_supportPerm_symm_apply (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : b.support) :
    ((b.supportPerm hσ).symm i : ι) = σ.indexEquiv.symm i := (rfl)

@[simp] theorem Base.coe_supportPerm_pow (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (n : ℕ) (i : b.support) :
    (((b.supportPerm hσ ^ n) i : b.support) : ι) = (σ.indexEquiv ^ n) (i : ι) :=
  σ.coe_supportEquiv_pow _ n i

@[simp] theorem Base.sameCycle_supportPerm_iff (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i j : b.support} :
    _root_.Equiv.Perm.SameCycle (b.supportPerm hσ) i j ↔
      _root_.Equiv.Perm.SameCycle σ.indexEquiv (i : ι) (j : ι) :=
  σ.sameCycle_supportEquiv_iff _

end SupportPerm

end RootPairing
