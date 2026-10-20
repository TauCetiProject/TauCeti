/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# The cyclic representation of an automorphism of finite order

Let `T` be an additive commutative group, `m > 0`, and `A : T ≃+ T` an additive automorphism of
order dividing `m`, that is `A^[m] = id`. Then the cyclic group `C_m = Multiplicative (ZMod m)`
acts on `T` with its standard generator `ofAdd 1` acting by `A`; this is the integral
representation `AddEquiv.cyclicRep A hA : Rep ℤ C_m`. Its norm `N = ∑ g, ρ g` is the ordered sum
of powers `∑ j < m, A^j` (`AddEquiv.cyclicRepresentation_norm_apply`).

Its group cohomology is read off in
`TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicAutomorphism`.

## Main definitions

* `AddEquiv.cyclicRepresentation A hA`: the representation of `C_m` on `T` in which the
  generator acts by `A`.
* `AddEquiv.cyclicRep A hA`: the same representation, as an object of `Rep ℤ C_m`.

## Main results

* `AddEquiv.cyclicRepresentation_ofAdd_apply`: the element `a` of `C_m` acts by `A^[a.val]`.
* `AddEquiv.cyclicRepresentation_norm_apply`: the norm is the ordered sum of powers of `A`.
-/

public section

namespace AddEquiv

variable {T : Type*} [AddCommGroup T] {m : ℕ} [NeZero m] (A : T ≃+ T) (hA : (⇑A)^[m] = id)

/-- The integral representation of the cyclic group `C_m = Multiplicative (ZMod m)` on `T` in
which the generator `ofAdd 1` acts by an additive automorphism `A` of order dividing `m`. -/
noncomputable def cyclicRepresentation : Representation ℤ (Multiplicative (ZMod m)) T :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((TauCeti.zmodMonoidHomEquiv m (T ≃ₗ[ℤ] T)).symm ⟨A.toIntLinearEquiv, by
      ext x
      rw [LinearEquiv.coe_pow]
      simpa using congrFun hA x⟩)

/-- The element `a` of `C_m` acts on `T` by the `a.val`-th iterate of `A`. -/
theorem cyclicRepresentation_ofAdd_apply (a : ZMod m) (x : T) :
    A.cyclicRepresentation hA (.ofAdd a) x = (⇑A)^[a.val] x := by
  simp [cyclicRepresentation, LinearEquiv.coe_pow]

/-- The generator `ofAdd 1` of `C_m` acts on `T` by `A`. -/
@[simp]
theorem cyclicRepresentation_ofAdd_one_apply (x : T) :
    A.cyclicRepresentation hA (.ofAdd 1) x = A x := by
  rw [cyclicRepresentation, MonoidHom.comp_apply, ← TauCeti.coe_zmodMonoidHomEquiv_apply,
    Equiv.apply_symm_apply]
  simp

/-- The norm of the cyclic representation of `A` is the ordered sum of the powers
`A^0, …, A^(m-1)`. -/
theorem cyclicRepresentation_norm_apply (x : T) :
    (A.cyclicRepresentation hA).norm x = ∑ j ∈ Finset.range m, (⇑A)^[j] x := by
  rw [Representation.norm, LinearMap.sum_apply]
  -- Reindex `C_m` by the representatives `0, …, m - 1` of `ZMod m`.
  refine Finset.sum_nbij' (fun g : Multiplicative (ZMod m) ↦ g.toAdd.val)
    (fun j : ℕ ↦ Multiplicative.ofAdd (j : ZMod m)) ?_ ?_ ?_ ?_ ?_
  all_goals simp +contextual [ZMod.val_lt, Nat.mod_eq_of_lt, cyclicRepresentation_ofAdd_apply]

/-- The cyclic representation of `A` as an object of `Rep ℤ C_m`. -/
noncomputable abbrev cyclicRep : Rep ℤ (Multiplicative (ZMod m)) :=
  Rep.of (A.cyclicRepresentation hA)

end AddEquiv
