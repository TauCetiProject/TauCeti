/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.GroupExtension.Defs
public import TauCeti.Data.ZMod.MulCastHom

/-!
# The extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`

The cyclic group of order four is a non-split extension of `ℤ/2` by `ℤ/2`: the kernel is the
subgroup `2ℤ/4ℤ`, included by the doubling map `ZMod.mulCastHom 2`, and the projection is
reduction modulo two. Written multiplicatively, as the extension dictionary of
`TauCeti/GroupTheory/GroupExtension` requires, this is `TauCeti.zmodFourExtension`. It has no
homomorphic section (`TauCeti.isEmpty_splitting_zmodFourExtension`): a section would send the
generator of `ℤ/2` to an element of order dividing two with odd residue, and the elements of order
dividing two in `ℤ/4` are `0` and `2`.

This is the extension whose class in `H²(ℤ/2, 𝔽₂)` is the cup square of the generator of
`H¹(ℤ/2, 𝔽₂)`, the first nonzero cup square of the theory of Demushkin groups; the profinite
extension it defines and its class are the subject of
`TauCeti/Topology/Algebra/GroupExtension/ZModFour.lean`.

## Main declarations

* `TauCeti.zmodFourExtension`: the extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`, with its inclusion and
  projection `TauCeti.zmodFourExtension_inl` and `TauCeti.zmodFourExtension_rightHom`, and its
  canonical normalized section `TauCeti.zmodFourExtensionSection`.
* `TauCeti.isEmpty_splitting_zmodFourExtension`: **it has no homomorphic section.**

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open Multiplicative

/-- **The extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`**, written multiplicatively: the kernel `ℤ/2` is
included as `2ℤ/4ℤ` by the doubling map, and the projection is reduction modulo two. -/
def zmodFourExtension :
    GroupExtension (Multiplicative (ZMod 2)) (Multiplicative (ZMod 4))
      (Multiplicative (ZMod 2)) where
  inl := AddMonoidHom.toMultiplicative (ZMod.mulCastHom 2 rfl)
  rightHom :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom
  inl_injective := fun x y h =>
    toAdd.injective (ZMod.mulCastHom_injective 2 rfl two_ne_zero (ofAdd.injective h))
  range_inl_eq_ker_rightHom := by
    ext y
    -- Exactness of `ℤ/2 → ℤ/4 → ℤ/2`, transported along `ofAdd`.
    have h := (ZMod.exact_mulCastHom_castHom (m := 2) (n := 4) 2 rfl (toAdd y)).symm
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, AddMonoidHom.toMultiplicative_apply_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, ofAdd_eq_one]
    rw [← h, Set.mem_range]
    exact toAdd.exists_congr fun x => by rw [← toAdd.apply_eq_iff_eq, toAdd_ofAdd]
  rightHom_surjective :=
    ofAdd.surjective.comp
      ((ZMod.castHom_surjective (by decide : (2 : ℕ) ∣ 4)).comp toAdd.surjective)

/-- The kernel of `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` is included by the doubling map. -/
@[simp]
theorem zmodFourExtension_inl :
    zmodFourExtension.inl = AddMonoidHom.toMultiplicative (ZMod.mulCastHom 2 rfl) :=
  (rfl)

/-- The projection of `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` is reduction modulo two. -/
@[simp]
theorem zmodFourExtension_rightHom :
    zmodFourExtension.rightHom =
      AddMonoidHom.toMultiplicative
        (ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom :=
  (rfl)

/-- The inclusion of `TauCeti.zmodFourExtension` sends the generator `ofAdd 1` of `ℤ/2` to
`ofAdd 2` in `ℤ/4`. -/
theorem zmodFourExtension_inl_ofAdd_one :
    zmodFourExtension.inl (ofAdd 1) = ofAdd 2 := by
  rw [zmodFourExtension_inl, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    ZMod.mulCastHom_apply]
  decide

/-- The projection of `TauCeti.zmodFourExtension` sends `ofAdd 1` in `ℤ/4` to `ofAdd 1` in
`ℤ/2`. -/
theorem zmodFourExtension_rightHom_ofAdd_one :
    zmodFourExtension.rightHom (ofAdd 1) = ofAdd 1 := by
  rw [zmodFourExtension_rightHom]
  decide

/-- **The canonical normalized section `0 ↦ 0, 1 ↦ 1` of `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`**, lifting each
residue modulo two to its canonical representative `{0, 1}` modulo four. -/
def zmodFourExtensionSection : zmodFourExtension.Section where
  toFun y := ofAdd ((toAdd y).cast : ZMod 4)
  rightInverse_rightHom y :=
    toAdd.injective (by simp [zmodFourExtension_rightHom])

theorem zmodFourExtensionSection_apply (y : Multiplicative (ZMod 2)) :
    zmodFourExtensionSection y = ofAdd ((toAdd y).cast : ZMod 4) :=
  (rfl)

/-- The canonical section of `TauCeti.zmodFourExtension` is normalized at `1`. -/
@[simp]
theorem zmodFourExtensionSection_one : zmodFourExtensionSection 1 = 1 := by
  decide

/-- The canonical section of `TauCeti.zmodFourExtension` lifts the generator `ofAdd 1` of `ℤ/2` to
`ofAdd 1` in `ℤ/4`. -/
@[simp]
theorem zmodFourExtensionSection_ofAdd_one : zmodFourExtensionSection (ofAdd 1) = ofAdd 1 := by
  decide

/-- **The extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` has no homomorphic section**: a section would send
the generator of `ℤ/2` to an element of `ℤ/4` of order dividing two with odd residue, and the only
elements of `ℤ/4` of order dividing two are `0` and `2`. -/
theorem isEmpty_splitting_zmodFourExtension : IsEmpty zmodFourExtension.Splitting := ⟨fun s => by
  -- The generator of `ℤ/2` squares to `1`, so its image under the section does.
  have hgen : ofAdd (1 : ZMod 2) * ofAdd 1 = 1 := by decide
  have hsq : s (ofAdd 1) * s (ofAdd 1) = 1 := by
    rw [← map_mul, hgen, map_one]
  have hred := s.rightHom_splitting (ofAdd 1)
  rw [zmodFourExtension_rightHom, AddMonoidHom.toMultiplicative_apply_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at hred
  revert hsq hred
  generalize s (ofAdd 1) = x
  revert x
  decide⟩

end TauCeti
