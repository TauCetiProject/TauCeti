/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
import Mathlib.Algebra.Group.Equiv.TypeTags
import TauCeti.Algebra.Group.TypeTags.Hom
import TauCeti.LinearAlgebra.BilinearForm.Polarization

/-!
# The Heisenberg group of a bilinear form

The Heisenberg group of a symplectic space is the central extension of the additive group of that
space by its coefficient group, with factor set the half-form `ω / 2` when `2` is invertible. This
file builds the extension of an arbitrary bilinear map in the library's factor-set coordinates, and
computes the group law, the inverse, the commutator and the centre in those coordinates. The
development is deliberately coordinate-level: no alternating, nondegeneracy or invertibility
hypothesis is used unless a theorem states it, so one API serves both the integral bilinear
extensions and the half-alternating convention of the metaplectic cover. In general the copy of the
coefficient group supplied by `TauCeti.FactorSet.inl` is only a subgroup of the centre; it is the
whole centre exactly when the skew part `B - Bᵀ` has trivial left radical, i.e. is left-separating.
For the half-form extension `E_{ω/2}` of an alternating `ω` with `2` invertible, the skew part is
`ω` itself (`LinearMap.IsAlt.half_skew_eq_self`), so the centre is `inl.range` exactly when `ω` is
left-separating, and in particular when `ω` is nondegenerate.

The extension of `B : W × W → C` is the `TauCeti.FactorSet.Extension` of
`B.bilinearFactorSet`: its elements are pairs `(t, w)` with the coefficient written first, its
identity is `(0, 0)`, and its multiplication is

`(t, w) * (s, v) = (t + s + B w v, w + v)`.

Because the action of the space on the coefficients is trivial, the copy of the coefficient group
supplied by `TauCeti.FactorSet.inl` is central (`TauCeti.FactorSet.inl_range_le_center`), and the
commutator of two elements measures the failure of `B` to be symmetric
(`TauCeti.HeisenbergGroup.Bilinear.bilinearExtension_commutatorElement_eq_inl`). Halving an
alternating form is what makes the commutator recover the form itself
(`LinearMap.IsAlt.halfForm_commutatorElement_eq_inl`), and the centre of the extension of `ω / 2`
is the copy of the coefficient group exactly when `ω` is left-separating
(`LinearMap.IsAlt.halfForm_center_eq_range_iff`), in particular when `ω` is nondegenerate.

## Main definitions

* `LinearMap.BilinMap.bilinearFactorSet`: the factor set `(w, v) ↦ B w v` of a bilinear map, for
  the trivial action, written multiplicatively on the space and on the coefficients.

## Main results

* `LinearMap.BilinMap.bilinearFactorSet_apply`: the value of the factor set is `B`.
* `TauCeti.HeisenbergGroup.Bilinear.bilinearExtension_inv`: the inverse of `(t, w)` is
  `(B w w - t, -w)`.
* `TauCeti.HeisenbergGroup.Bilinear.bilinearExtension_commutatorElement_eq_inl`: the commutator of
  `(t, w)` and `(s, v)` is `inl (B w v - B v w)`.
* `TauCeti.HeisenbergGroup.Bilinear.bilinearExtension_mem_center_iff`: `(t, w)` is central exactly
  when `B w ·` and `B · w` agree.
* `TauCeti.HeisenbergGroup.Bilinear.bilinearExtension_center_eq_range_iff`: the coefficient
  subgroup is the whole centre exactly when `B - Bᵀ` is left-separating.
* `LinearMap.IsAlt.halfForm_commutatorElement_eq_inl` and
  `LinearMap.IsAlt.halfForm_center_eq_range_iff`: the commutator and centre formulas for the
  half-alternating convention.
* `LinearMap.BilinMap.polarization_cocycle` (in
  `TauCeti.LinearAlgebra.BilinearForm.Polarization`): the quadratic correction `q x = B x x / 2`
  converts the cocycle of `B` into the cocycle of `ω / 2` for `ω = B - Bᵀ`.

## References

* S. Kudla, Notes on local theta correspondence and local Langlands correspondence (1996), I.1.
* H. Weil, Sur certains groupes d'opérateurs unitaires, Acta Math. 111 (1964), I.§3.
-/

public section

open Multiplicative TauCeti
open scoped commutatorElement

attribute [local instance] trivialMulDistribMulAction

namespace LinearMap.BilinMap

variable {R : Type*} [CommSemiring R] {W C : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]

/-- **The factor set of a bilinear map**, specializing `TauCeti.FactorSet.ofBimultiplicative`: for
`B : W × W → C`, it is the normalized factor set `(w, v) ↦ ofAdd (B w.toAdd v.toAdd)` (additively
`(w, v) ↦ B w v`) on `Multiplicative W` with coefficients in `Multiplicative C` and the trivial
action of `Multiplicative W` on `Multiplicative C`. The associated extension
`TauCeti.FactorSet.Extension (B.bilinearFactorSet)` is the **Heisenberg group of `B`**; its law is
`(t, w) * (s, v) = (t + s + B w v, w + v)`. -/
def bilinearFactorSet (B : LinearMap.BilinMap R W C) :
    FactorSet (Multiplicative W) (Multiplicative C) :=
  FactorSet.ofBimultiplicative
    (AddMonoidHom.toMultiplicativeLeft
      ((AddMonoidHom.toMultiplicativeLeftAddEquiv (M := W)
          (N := Multiplicative C)).toAddMonoidHom.comp
        ((LinearMap.toAddMonoidHom'.comp B.toAddMonoidHom).compr₂
          (AddEquiv.additiveMultiplicative C).symm.toAddMonoidHom)))
    TauCeti.trivialMulDistribMulAction_smul

/-- The value of the factor set of `B` at two multiplicatively written space coordinates is the
image under `ofAdd` of the value of `B` at the corresponding additive coordinates: the additive
value of the factor set is `B` itself. -/
@[simp]
theorem bilinearFactorSet_apply (B : LinearMap.BilinMap R W C) (w v : Multiplicative W) :
    B.bilinearFactorSet (w, v) = ofAdd (B w.toAdd v.toAdd) := by
  rw [bilinearFactorSet, FactorSet.ofBimultiplicative_apply]
  simp only [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddMonoidHom.toMultiplicativeLeftAddEquiv_apply, toMul_ofMul,
    AddMonoidHom.compr₂_apply, LinearMap.toAddMonoidHom'_apply, LinearMap.toAddMonoidHom_coe,
    AddEquiv.additiveMultiplicative_symm_apply]

end LinearMap.BilinMap

namespace TauCeti.HeisenbergGroup.Bilinear

open LinearMap.BilinMap

variable {R : Type*} [CommSemiring R] {W C : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]

section

variable {B : LinearMap.BilinMap R W C} {p q : (bilinearFactorSet B).Extension}

/-- **The inverse in the Heisenberg group of `B`** is `(t, w)⁻¹ = (B w w - t, -w)`. In particular,
the inverse of `(0, w)` is `(0, -w)` exactly when `B w w = 0`; this holds for every `w` when `B` is
alternating. -/
theorem bilinearExtension_inv :
    p⁻¹ = ⟨ofAdd (-p.left.toAdd + B p.right.toAdd p.right.toAdd), ofAdd (-p.right.toAdd)⟩ := by
  refine FactorSet.Extension.ext (toAdd.injective ?_) (toAdd.injective ?_)
  · simp only [FactorSet.Extension.inv_left, TauCeti.trivialMulDistribMulAction_smul,
      bilinearFactorSet_apply, toAdd_inv, toAdd_mul, map_neg, toAdd_ofAdd]
    abel
  · simp only [FactorSet.Extension.inv_right, toAdd_inv, toAdd_ofAdd]

/-- **The commutator in the Heisenberg group of `B`**, with the convention
`⁅p, q⁆ = p * q * p⁻¹ * q⁻¹`, is a central element determined by the two space coordinates: it
records the failure of `B` to be symmetric. This is the additive form, for the factor set of a
bilinear map, of `TauCeti.FactorSet.commutatorElement_eq_inl`. -/
theorem bilinearExtension_commutatorElement_eq_inl :
    ⁅p, q⁆ = FactorSet.inl (bilinearFactorSet B)
      (ofAdd (B p.right.toAdd q.right.toAdd - B q.right.toAdd p.right.toAdd)) := by
  rw [FactorSet.commutatorElement_eq_inl (bilinearFactorSet B)
    TauCeti.trivialMulDistribMulAction_smul]
  simp only [bilinearFactorSet_apply, ← ofAdd_sub]

/-- **The centre criterion for the Heisenberg group of `B`**: `(t, w)` is central exactly when the
two maps `B w ·` and `B · w` agree. No nondegeneracy is assumed, so a degenerate `B` can have a
larger centre than the copy of the coefficient group. -/
theorem bilinearExtension_mem_center_iff :
    p ∈ Subgroup.center _ ↔ ∀ v : W, B p.right.toAdd v = B v p.right.toAdd := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hp v
    have hcomm := commutatorElement_eq_one_iff_mul_comm.mpr (hp ⟨1, ofAdd v⟩)
    rw [bilinearExtension_commutatorElement_eq_inl, map_eq_one_iff _ (FactorSet.inl_injective _),
      ofAdd_eq_one, sub_eq_zero] at hcomm
    exact hcomm.symm
  · intro hv q
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    rw [bilinearExtension_commutatorElement_eq_inl]
    have h0 : B q.right.toAdd p.right.toAdd - B p.right.toAdd q.right.toAdd = 0 := by
      rw [hv q.right.toAdd, sub_self]
    simp only [h0, ofAdd_zero, map_one]

end

/-- **When the coefficient subgroup is the whole centre.** For the Heisenberg group of `B`, the
range of `TauCeti.FactorSet.inl` is the whole centre exactly when the skew part `B - Bᵀ` is
left-separating. This specializes to the familiar nondegenerate alternating criterion for the
half-form extension. -/
theorem bilinearExtension_center_eq_range_iff {B : LinearMap.BilinMap R W C} :
    Subgroup.center ((bilinearFactorSet B).Extension) =
      (FactorSet.inl (bilinearFactorSet B)).range ↔
      (B - B.flip).SeparatingLeft := by
  have hmem_range (p : (bilinearFactorSet B).Extension) :
      p ∈ (FactorSet.inl (bilinearFactorSet B)).range ↔ p.right.toAdd = 0 := by
    rw [FactorSet.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, FactorSet.rightHom_apply,
      ← toAdd_eq_zero]
  have hmem_center (p : (bilinearFactorSet B).Extension) :
      p ∈ Subgroup.center ((bilinearFactorSet B).Extension) ↔
        ∀ v : W, (B - B.flip) p.right.toAdd v = 0 := by
    simp only [bilinearExtension_mem_center_iff, LinearMap.sub_apply, LinearMap.flip_apply,
      sub_eq_zero]
  constructor
  · intro h_eq w hw
    have hcentral : ⟨1, ofAdd w⟩ ∈ Subgroup.center ((bilinearFactorSet B).Extension) :=
      (hmem_center ⟨1, ofAdd w⟩).mpr (by simpa only [toAdd_ofAdd] using hw)
    have hin_range : ⟨1, ofAdd w⟩ ∈ (FactorSet.inl (bilinearFactorSet B)).range := by
      rw [← h_eq]
      exact hcentral
    simpa only [toAdd_ofAdd] using (hmem_range ⟨1, ofAdd w⟩).mp hin_range
  · intro h_sep
    refine le_antisymm ?_ (FactorSet.inl_range_le_center _ TauCeti.trivialMulDistribMulAction_smul)
    intro p hp
    exact (hmem_range p).mpr (h_sep p.right.toAdd ((hmem_center p).mp hp))

end TauCeti.HeisenbergGroup.Bilinear

namespace LinearMap.IsAlt

open LinearMap.BilinMap TauCeti

variable {R : Type*} [CommSemiring R] {W C : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C] [Invertible (2 : R)] {ω : LinearMap.BilinMap R W C}

/-- **The commutator in the half-alternating Heisenberg group**: for an alternating `ω` with `2`
invertible, the commutator of two elements of the extension of `ω / 2` is the central element
`inl (ω w v)`. The halving is what makes the commutator recover `ω` itself, rather than twice `ω`.
-/
theorem halfForm_commutatorElement_eq_inl (hω : ω.IsAlt)
    (p q : (bilinearFactorSet (⅟(2 : R) • ω)).Extension) :
    ⁅p, q⁆ = FactorSet.inl (bilinearFactorSet (⅟(2 : R) • ω))
      (ofAdd (ω p.right.toAdd q.right.toAdd)) := by
  rw [HeisenbergGroup.Bilinear.bilinearExtension_commutatorElement_eq_inl]
  have key := LinearMap.congr_fun (LinearMap.congr_fun hω.half_skew_eq_self p.right.toAdd)
    q.right.toAdd
  simp only [LinearMap.sub_apply, LinearMap.flip_apply] at key
  rw [key]

/-- **The centre of the half-alternating Heisenberg group**: for an alternating `ω` with `2`
invertible, the centre of the extension of `ω / 2` is the range of `TauCeti.FactorSet.inl`
exactly when `ω` is left-separating. In particular, for a nondegenerate alternating `ω`
(`hωn : ω.Nondegenerate`), the reverse implication applied to `hωn.1` gives the standard centre
equality. -/
theorem halfForm_center_eq_range_iff (hω : ω.IsAlt) :
    Subgroup.center ((bilinearFactorSet (⅟(2 : R) • ω)).Extension) =
      (FactorSet.inl (bilinearFactorSet (⅟(2 : R) • ω))).range ↔
      ω.SeparatingLeft := by
  rw [HeisenbergGroup.Bilinear.bilinearExtension_center_eq_range_iff, hω.half_skew_eq_self]

end LinearMap.IsAlt
