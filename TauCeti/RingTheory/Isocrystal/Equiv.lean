/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Isocrystal

/-!
# Inverse and composition of Witt isocrystal isomorphisms

Inverting or composing the underlying linear equivalences preserves Frobenius equivariance.
-/

public section

open scoped Isocrystal

namespace WittVector.IsocrystalEquiv

variable {p : ℕ} [Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
variable {V V₂ V₃ : Type*} [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]
variable [source : Isocrystal p k V] [middle : Isocrystal p k V₂] [target : Isocrystal p k V₃]

/-- The inverse of an isocrystal isomorphism. The named instance arguments `source` and
`middle` specify the two isocrystals even when their underlying types coincide. -/
noncomputable def symm (f : V ≃ᶠⁱ[p, k] V₂) : V₂ ≃ᶠⁱ[p, k] V where
  toLinearEquiv := f.toLinearEquiv.symm
  frob_equivariant x := by
    apply f.toLinearEquiv.injective
    simp only [← f.frob_equivariant, LinearEquiv.apply_symm_apply]

@[simp]
theorem symm_toLinearEquiv (f : V ≃ᶠⁱ[p, k] V₂) :
    f.symm.toLinearEquiv = f.toLinearEquiv.symm := (rfl)

/-- The composition of isocrystal isomorphisms, applying `f` first. The named instance
arguments `source`, `middle`, and `target` distinguish isocrystals on the same underlying type. -/
noncomputable def trans (f : V ≃ᶠⁱ[p, k] V₂) (g : V₂ ≃ᶠⁱ[p, k] V₃) : V ≃ᶠⁱ[p, k] V₃ where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  frob_equivariant x := by
    simp only [LinearEquiv.trans_apply, f.frob_equivariant, g.frob_equivariant]

@[simp]
theorem trans_toLinearEquiv (f : V ≃ᶠⁱ[p, k] V₂) (g : V₂ ≃ᶠⁱ[p, k] V₃) :
    (f.trans g).toLinearEquiv = f.toLinearEquiv.trans g.toLinearEquiv := (rfl)

end WittVector.IsocrystalEquiv
