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
power of its image under the basepoint embedding, by `autEquivPow_symm_apply_zeta` and `map_pow`.

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

/-- The basepoint has cyclotomic label `1`. -/
@[simp]
theorem equivUnitsZMod_self (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic n K)) : w.equivUnitsZMod hw h w = 1 := by
  simp only [equivUnitsZMod, Equiv.trans_apply, galEquivOfSubsingleton_symm_self,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_one]

variable [NeZero n]

/-- An automorphism `σ` labels the place obtained by its inverse action on the basepoint
by the power to which it raises the primitive root. -/
@[simp]
theorem equivUnitsZMod_inv_smul (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (σ : Gal(L/K)) :
    w.equivUnitsZMod hw h (σ⁻¹ • w) = autEquivPow L h σ := by
  let := IsCyclotomicExtension.isGalois {n} K L
  simp only [equivUnitsZMod, Equiv.trans_apply, galEquivOfSubsingleton_symm_inv_smul,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]

/-- The place of `φ ∘ σ` has the cyclotomic label of `σ`, relative to the place of `φ`. -/
@[simp]
theorem equivUnitsZMod_mk_comp (φ : L →+* ℂ) (hφ : (mk φ).IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (σ : Gal(L/K)) :
    (mk φ).equivUnitsZMod hφ h (mk (φ.comp σ)) = autEquivPow L h σ := by
  let := IsCyclotomicExtension.isGalois {n} K L
  rw [← galEquivOfSubsingleton_mk_apply φ hφ, galEquivOfSubsingleton_apply,
    equivUnitsZMod_inv_smul]

/-- The place with label `a` is obtained by the inverse action of the corresponding automorphism. -/
@[simp low]
theorem equivUnitsZMod_symm_apply (w : InfinitePlace L) (hw : w.IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (a : (ZMod n)ˣ) :
    (w.equivUnitsZMod hw h).symm a = ((autEquivPow L h).symm a)⁻¹ • w := by
  simp only [equivUnitsZMod, Equiv.symm_trans_apply, Equiv.symm_symm,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm, galEquivOfSubsingleton_apply]

/-- The place with label `a` is induced by precomposing the reference embedding with the
automorphism attached to `a` by `autEquivPow`. -/
@[simp]
theorem equivUnitsZMod_symm_apply_mk (φ : L →+* ℂ) (hφ : (mk φ).IsUnramified K)
    (h : Irreducible (cyclotomic n K)) (a : (ZMod n)ˣ) :
    ((mk φ).equivUnitsZMod hφ h).symm a = mk (φ.comp ((autEquivPow L h).symm a)) := by
  rw [equivUnitsZMod_symm_apply, smul_mk, AlgEquiv.aut_inv, AlgEquiv.symm_symm]

end NumberField.InfinitePlace
