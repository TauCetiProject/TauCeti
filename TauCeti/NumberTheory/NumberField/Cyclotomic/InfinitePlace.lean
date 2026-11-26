/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Galois

/-!
# Cyclotomic labels for infinite places

Over a field with a unique infinite place, an irreducible cyclotomic polynomial labels
all the infinite places of the cyclotomic extension by units modulo its order. To fix
these labels, choose an embedding whose infinite place is unramified over the base.
The representative embedding at label `a` sends the chosen root of unity to the `a`th
power of its image under the basepoint embedding.

This is the labeling of infinite places used in lsernau/grh-lean,
`New/Reduction/Data/FieldsAndPlaces.lean` (`New.Parameters.placeMulEquiv`, revision `72fead1`).
-/

public section

namespace NumberField.InfinitePlace

open IsCyclotomicExtension Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Subsingleton (InfinitePlace K)] {n : ℕ} [IsCyclotomicExtension {n} K L]

/-- Label the infinite places of a cyclotomic extension by units modulo the order of the
roots of unity, relative to an unramified basepoint `w`. -/
noncomputable def equivUnitsZMod (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic n K)) : InfinitePlace L ≃ (ZMod n)ˣ := by
  letI : NeZero n := ⟨fun hn ↦ h.not_isUnit (hn ▸ cyclotomic_zero K ▸ isUnit_one)⟩
  letI := IsCyclotomicExtension.isGalois {n} K L
  exact (w.galEquivOfSubsingleton hw).symm.trans (autEquivPow L h).toEquiv

variable [NeZero n]

/-- An automorphism `σ` labels the place obtained by its inverse action on the basepoint
by the power to which it raises the primitive root. -/
@[simp]
theorem equivUnitsZMod_inv_smul (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (σ : Gal(L/K)) :
    w.equivUnitsZMod hw h (σ⁻¹ • w) = autEquivPow L h σ := by
  let := IsCyclotomicExtension.isGalois {n} K L
  rw [← galEquivOfSubsingleton_apply w hw, equivUnitsZMod, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rfl

/-- The place with label `a` is induced by precomposing the reference embedding with the
automorphism attached to `a` by `autEquivPow`. -/
@[simp]
theorem equivUnitsZMod_symm_apply_mk (φ : L →+* ℂ) (hφ : (mk φ).IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (a : (ZMod n)ˣ) :
    ((mk φ).equivUnitsZMod hφ h).symm a = mk (φ.comp ((autEquivPow L h).symm a)) := by
  let := IsCyclotomicExtension.isGalois {n} K L
  rw [equivUnitsZMod, Equiv.symm_trans_apply]
  exact galEquivOfSubsingleton_mk_apply φ hφ _

end NumberField.InfinitePlace
