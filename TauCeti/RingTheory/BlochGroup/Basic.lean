/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.AntisymSquare
public import TauCeti.RingTheory.BlochGroup.PreBloch
import Mathlib.Data.ZMod.Defs

/-!
# The Bloch boundary and the Bloch group of a commutative ring

Let `A` be a commutative ring and write `U(A) = Additive Aˣ` for its group of units, written
additively. The *Bloch boundary* is the homomorphism
`∂ : P(A) → antisymSquare ℤ U(A)` from the pre-Bloch group to the antisymmetric tensor cokernel
of `U(A)`, sending the symbol `[x]` of an exceptional unit `x` to `x ∧ (1 - x)`. The *Bloch group*
`B(A)` is its kernel, a subgroup of `P(A)`. Over a field `F` these are Suslin's boundary
`[x] ↦ x ∧ (1 - x)` and Bloch group `B(F)`, the target of the map from indecomposable `K₃(F)`.

The boundary is well defined because the boundary of the five-term element of an admissible pair
`(x, y)` is `a ∧ c + c ∧ a = 0`, where `a = x` and `c = (1 - x)/(1 - y)`: every argument of the
five-term element, and one minus every argument, is a product of the units `x`, `y`, `1 - x`,
`1 - y`, `x - y` and their inverses, and expanding the five wedges bilinearly leaves exactly
`x ∧ (1 - x) + (1 - x) ∧ x - (x ∧ (1 - y) + (1 - y) ∧ x)`. Only these multiplicative relations
are used, so the argument works over every commutative ring.

The target is the antisymmetric tensor cokernel, in which `a ∧ a` need not vanish, and not the
exterior square. This matters: over `𝔽₅` the boundary of `[3]` is the diagonal class `3 ∧ 3`,
which is nonzero because `3` is not a square, so `[3] ∉ B(𝔽₅)`; the exterior square of the cyclic
group `𝔽₅ˣ` is zero, so the boundary into it vanishes on all of `P(𝔽₅)`.

## Main definitions

* `TauCeti.preBloch.boundary A`: the Bloch boundary `P(A) →+ antisymSquare ℤ (Additive Aˣ)`.
* `TauCeti.blochGroup A`: the Bloch group, the kernel of the boundary.
* `TauCeti.blochGroup.map`: the homomorphism of Bloch groups induced by a ring homomorphism.

## Main results

* `TauCeti.preBloch.boundary_preBlochSymbol`: `∂[x] = x ∧ (1 - x)` for an exceptional unit `x`.
* `TauCeti.preBloch.boundary_comp_map`: the boundary commutes with the maps induced by a ring
  homomorphism.
* `TauCeti.preBloch.boundary_preBlochSymbol_add_preBlochSymbol_inv`: over a field,
  `∂([u] + [u⁻¹]) = u ∧ (-u)` for every unit `u`.
* `TauCeti.preBlochSymbol_add_preBlochSymbol_one_sub_mem_blochGroup`: `[x] + [1 - x] ∈ B(A)`.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics **145**, AMS, 2013, Chapter VI, Definition 5.1.
* B. Mirzaii, F. Y. Mokari, *A Bloch-Wigner theorem over rings with many units II*,
  arXiv:1108.5452, §3.
-/

public section

open Additive
open scoped Ring

namespace TauCeti

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-! ### The boundary -/

namespace preBloch

/-- The value `x ∧ (1 - x)` of the boundary at an exceptional unit `x`, and zero elsewhere. -/
private noncomputable def boundaryAux (x : A) : antisymSquare ℤ (Additive Aˣ) := by
  classical
  exact if h : IsUnit x ∧ IsUnit (1 - x) then
    antisymSquare.mk ℤ _ (ofMul h.1.unit) (ofMul h.2.unit) else 0

private theorem boundaryAux_of_notMem {x : A} (hx : x ∉ exceptionalUnits A) :
    boundaryAux x = 0 := by
  rw [mem_exceptionalUnits] at hx
  simp [boundaryAux, hx]

/-- The value of `boundaryAux` at an element `z` that is a unit `u` with `1 - u` a unit `v`. -/
private theorem boundaryAux_eq {z : A} {u v : Aˣ} (hz : z = u) (huv : (u : A) + v = 1) :
    boundaryAux z = antisymSquare.mk ℤ _ (ofMul u) (ofMul v) := by
  subst hz
  have hv : (v : A) = 1 - u := eq_sub_of_add_eq' huv
  have hx : IsUnit (u : A) ∧ IsUnit (1 - (u : A)) := ⟨u.isUnit, hv ▸ v.isUnit⟩
  rw [boundaryAux, dite_eq_left_of_eq_true (eq_true hx)]
  congr 3
  · exact IsUnit.unit_of_val_units _
  · exact Units.ext (by rw [IsUnit.unit_spec, hv])

/-- The boundary of the five-term element of an admissible pair vanishes. -/
private theorem boundaryAux_fiveTerm {x y : A} (h : IsFiveTermAdmissible x y) :
    boundaryAux x - boundaryAux y + boundaryAux (y * x⁻¹ʳ) -
        boundaryAux ((1 - x⁻¹ʳ) * (1 - y⁻¹ʳ)⁻¹ʳ) + boundaryAux ((1 - x) * (1 - y)⁻¹ʳ) = 0 := by
  -- Name the five units `x = X`, `y = Y`, `1 - x = P`, `1 - y = Q` and `x - y = D`.
  obtain ⟨⟨X, rfl⟩, P, hP⟩ := mem_exceptionalUnits.1 h.left_mem
  obtain ⟨⟨Y, rfl⟩, Q, hQ⟩ := mem_exceptionalUnits.1 h.right_mem
  obtain ⟨D, hD⟩ := h.isUnit_sub
  have hX := X.mul_inv
  have hY := Y.mul_inv
  have hQ' := Q.mul_inv
  have hQinv : (1 - (Y : A)⁻¹ʳ)⁻¹ʳ = ((-(Y * Q⁻¹) : Aˣ) : A) := by
    have : 1 - (Y : A)⁻¹ʳ = ((-(Q * Y⁻¹) : Aˣ) : A) := by
      rw [Ring.inverse_unit, Units.val_neg, Units.val_mul]
      linear_combination ((Y⁻¹ : Aˣ) : A) * hQ - hY
    rw [this, Ring.inverse_unit, inv_neg, mul_inv_rev, inv_inv]
  -- Write each argument and its complement as a product of the five units.
  rw [boundaryAux_eq rfl (v := P) (by rw [hP]; ring),
    boundaryAux_eq rfl (v := Q) (by rw [hQ]; ring),
    boundaryAux_eq (u := Y * X⁻¹) (v := D * X⁻¹) (by rw [Ring.inverse_unit, Units.val_mul])
      (by simp only [Units.val_mul, hD]; linear_combination hX),
    boundaryAux_eq (u := P * Y * Q⁻¹ * X⁻¹) (v := D * Q⁻¹ * X⁻¹)
      (by
        rw [hQinv, Ring.inverse_unit]
        simp only [Units.val_mul, Units.val_neg, hP]
        linear_combination ((Q⁻¹ : Aˣ) : A) * Y * hX)
      (by
        simp only [Units.val_mul, hP, hD]
        linear_combination ((Q⁻¹ : Aˣ) : A) * (1 - (Y : A)) * hX - ((Q⁻¹ : Aˣ) : A) * hQ + hQ'),
    boundaryAux_eq (u := P * Q⁻¹) (v := D * Q⁻¹)
      (by rw [← hP, ← hQ, Ring.inverse_unit, Units.val_mul])
      (by simp only [Units.val_mul, hP, hD]; linear_combination -((Q⁻¹ : Aˣ) : A) * hQ + hQ')]
  -- Expanding bilinearly leaves `X ∧ P + P ∧ X - (X ∧ Q + Q ∧ X)`.
  refine Eq.trans ?_ (show antisymSquare.mk ℤ _ (ofMul X) (ofMul P) +
      antisymSquare.mk ℤ _ (ofMul P) (ofMul X) - (antisymSquare.mk ℤ _ (ofMul X) (ofMul Q) +
        antisymSquare.mk ℤ _ (ofMul Q) (ofMul X)) = 0 by simp)
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  abel

variable (A) in
/-- The *Bloch boundary* `∂ : P(A) → antisymSquare ℤ (Additive Aˣ)` of a commutative ring `A`,
sending the symbol `[x]` of an exceptional unit `x` to `x ∧ (1 - x)`
(`TauCeti.preBloch.boundary_preBlochSymbol`). Its kernel is the Bloch group
`TauCeti.blochGroup A`. Over a field it is Suslin's boundary `[x] ↦ x ∧ (1 - x)`, with
`∂[1] = 0`. -/
noncomputable def boundary : preBloch A →+ antisymSquare ℤ (Additive Aˣ) :=
  lift boundaryAux (fun _ => boundaryAux_of_notMem) fun _ _ => boundaryAux_fiveTerm

/-- The boundary of the symbol of a unit `u` whose complement `1 - u` is the unit `v` is
`u ∧ v`. -/
theorem boundary_preBlochSymbol_coe {u v : Aˣ} (huv : (u : A) + v = 1) :
    boundary A (preBlochSymbol (u : A)) = antisymSquare.mk ℤ _ (ofMul u) (ofMul v) := by
  rw [boundary, lift_preBlochSymbol, boundaryAux_eq rfl huv]

/-- The boundary of the symbol of an exceptional unit `x` is `x ∧ (1 - x)`. -/
theorem boundary_preBlochSymbol {x : A} (hx : IsUnit x) (hx1 : IsUnit (1 - x)) :
    boundary A (preBlochSymbol x) =
      antisymSquare.mk ℤ _ (ofMul hx.unit) (ofMul hx1.unit) := by
  rw [← boundary_preBlochSymbol_coe (by rw [IsUnit.unit_spec, IsUnit.unit_spec, add_sub_cancel]),
    IsUnit.unit_spec]

/-- Over a field, the boundary of the symbol of `x ∉ {0, 1}` is `x ∧ (1 - x)`. -/
theorem boundary_preBlochSymbol_mk0 {F : Type*} [Field F] {x : F} (hx : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    boundary F (preBlochSymbol x) =
      antisymSquare.mk ℤ _ (ofMul (Units.mk0 x hx)) (ofMul (Units.mk0 (1 - x) hx1)) :=
  boundary_preBlochSymbol_coe (u := Units.mk0 x hx) (by simp)

/-- The boundary commutes with the maps induced by a ring homomorphism `f : A →+* B`, on the
pre-Bloch groups and on the antisymmetric tensor cokernels of the unit groups. -/
theorem boundary_comp_map (f : A →+* B) :
    (boundary B).comp (map f) =
      (antisymSquare.map (Units.map (f : A →* B)).toAdditive.toIntLinearMap).toAddMonoidHom.comp
        (boundary A) := by
  refine hom_ext fun x hx => ?_
  obtain ⟨⟨X, rfl⟩, P, hP⟩ := mem_exceptionalUnits.1 hx
  have hXP : (X : A) + P = 1 := by rw [hP]; ring
  have hfX : f X = (Units.map (f : A →* B) X : B) := by simp
  rw [AddMonoidHom.comp_apply, map_preBlochSymbol _ hx, AddMonoidHom.comp_apply,
    boundary_preBlochSymbol_coe hXP, hfX,
    boundary_preBlochSymbol_coe (v := Units.map (f : A →* B) P) (by simp [← map_add, hXP])]
  simp

/-- The boundary commutes with the maps induced by a ring homomorphism, applied to an element:
see `TauCeti.preBloch.boundary_comp_map`. -/
theorem boundary_map (f : A →+* B) (z : preBloch A) :
    boundary B (map f z) =
      antisymSquare.map (Units.map (f : A →* B)).toAdditive.toIntLinearMap (boundary A z) :=
  congr($(boundary_comp_map f) z)

/-- The boundary of `[u] + [u⁻¹]` is `u ∧ (-u)`, for a unit `u` with `1 - u` a unit. -/
theorem boundary_preBlochSymbol_add_preBlochSymbol_inv_of_isUnit_one_sub {u : Aˣ}
    (hu : IsUnit (1 - (u : A))) :
    boundary A (preBlochSymbol (u : A) + preBlochSymbol ((u⁻¹ : Aˣ) : A)) =
      antisymSquare.mk ℤ _ (ofMul u) (ofMul (-u)) := by
  obtain ⟨P, hP⟩ := hu
  have hu := u.mul_inv
  rw [map_add, boundary_preBlochSymbol_coe (v := P) (by rw [hP]; ring),
    boundary_preBlochSymbol_coe (v := -1 * P * u⁻¹)
      (by simp only [Units.val_mul, Units.val_neg, Units.val_one, hP]; linear_combination hu),
    ← neg_one_mul u]
  -- The wedge `u ∧ (-1)` is `2`-torsion, since `(-1)²` is trivial.
  have h2 : antisymSquare.mk ℤ _ (ofMul u) (ofMul (-1 : Aˣ)) +
      antisymSquare.mk ℤ _ (ofMul u) (ofMul (-1 : Aˣ)) = 0 := by
    rw [← map_add, ← ofMul_mul, neg_one_mul, neg_neg, ofMul_one, map_zero]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h2]
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg, LinearMap.neg_apply]
  abel

/-- Over a field, the boundary of `[u] + [u⁻¹]` is `u ∧ (-u)` for every unit `u`. -/
theorem boundary_preBlochSymbol_add_preBlochSymbol_inv {F : Type*} [Field F] (u : Fˣ) :
    boundary F (preBlochSymbol (u : F) + preBlochSymbol ((u⁻¹ : Fˣ) : F)) =
      antisymSquare.mk ℤ _ (ofMul u) (ofMul (-u)) := by
  rcases eq_or_ne u 1 with rfl | hu
  · simp
  · exact boundary_preBlochSymbol_add_preBlochSymbol_inv_of_isUnit_one_sub
      (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (Ne.symm (Units.val_eq_one.not.2 hu))))

end preBloch

/-! ### The Bloch group -/

variable (A) in
/-- The *Bloch group* `B(A)` of a commutative ring `A`: the kernel of the Bloch boundary
`TauCeti.preBloch.boundary A`, a subgroup of the pre-Bloch group. Over a field `F` it is Suslin's
Bloch group `B(F)`. -/
noncomputable def blochGroup : AddSubgroup (preBloch A) :=
  (preBloch.boundary A).ker

@[simp]
theorem mem_blochGroup {z : preBloch A} : z ∈ blochGroup A ↔ preBloch.boundary A z = 0 :=
  Iff.rfl

/-- The class `[x] + [1 - x]` of an exceptional unit `x` lies in the Bloch group. -/
theorem preBlochSymbol_add_preBlochSymbol_one_sub_mem_blochGroup {x : A}
    (hx : x ∈ exceptionalUnits A) :
    preBlochSymbol x + preBlochSymbol (1 - x) ∈ blochGroup A := by
  obtain ⟨hx, hx1⟩ := mem_exceptionalUnits.1 hx
  have h := preBloch.boundary_preBlochSymbol_coe (u := hx1.unit) (v := hx.unit) (by simp)
  rw [IsUnit.unit_spec] at h
  rw [mem_blochGroup, map_add, preBloch.boundary_preBlochSymbol hx hx1, h,
    antisymSquare.mk_add_mk_swap]

/-- The homomorphism of pre-Bloch groups induced by a ring homomorphism maps the Bloch group into
the Bloch group. -/
theorem map_mem_blochGroup (f : A →+* B) {z : preBloch A} (hz : z ∈ blochGroup A) :
    preBloch.map f z ∈ blochGroup B := by
  rw [mem_blochGroup] at hz ⊢
  rw [preBloch.boundary_map, hz, map_zero]

namespace blochGroup

/-- The homomorphism of Bloch groups induced by a ring homomorphism `f : A →+* B`, the restriction
of `TauCeti.preBloch.map f`. -/
noncomputable def map (f : A →+* B) : blochGroup A →+ blochGroup B :=
  ((preBloch.map f).comp (blochGroup A).subtype).codRestrict _ fun z =>
    map_mem_blochGroup f z.property

@[simp]
theorem coe_map (f : A →+* B) (z : blochGroup A) : (map f z : preBloch B) = preBloch.map f z :=
  (rfl)

@[simp]
theorem map_id : map (RingHom.id A) = AddMonoidHom.id (blochGroup A) := by
  ext z
  simp

theorem map_comp (g : B →+* C) (f : A →+* B) : map (g.comp f) = (map g).comp (map f) := by
  ext z
  simp [preBloch.map_comp]

end blochGroup

/-! ### Examples -/

/-- Over `𝔽₅` the symbol `[2]` lies in the Bloch group: its boundary is `2 ∧ 4 = 2 • (2 ∧ 2)`,
since `1 - 2 = 4 = 2²`, and the diagonal class `2 ∧ 2` is `2`-torsion. -/
example : preBlochSymbol (2 : ZMod 5) ∈ blochGroup (ZMod 5) := by
  obtain ⟨u, hu⟩ : ∃ u : (ZMod 5)ˣ, (u : ZMod 5) = 2 := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩
  rw [mem_blochGroup, ← hu,
    preBloch.boundary_preBlochSymbol_coe (v := u ^ 2)
      (by rw [Units.val_pow_eq_pow_val, hu]; decide),
    ofMul_pow, map_nsmul, antisymSquare.two_nsmul_mk_self]

/-- Over `𝔽₅` the symbol `[3]` does not lie in the Bloch group: its boundary is the diagonal class
`3 ∧ 3`, since `1 - 3 = 3`, and this class is nonzero because `3` is not a square in `𝔽₅`. The
boundary into the exterior square, which kills `3 ∧ 3`, would not detect this. -/
example : preBlochSymbol (3 : ZMod 5) ∉ blochGroup (ZMod 5) := by
  obtain ⟨u, hu⟩ : ∃ u : (ZMod 5)ˣ, (u : ZMod 5) = 3 := ⟨⟨3, 2, by decide, by decide⟩, rfl⟩
  rw [mem_blochGroup, ← hu, preBloch.boundary_preBlochSymbol_coe (v := u) (by rw [hu]; decide),
    ← antisymSquare.diag_apply, antisymSquare.diag_eq_zero_iff]
  rintro ⟨c, hc⟩
  have h : (c.toMul : ZMod 5) ^ 2 = 3 := by
    rw [← Units.val_pow_eq_pow_val, ← toMul_nsmul, ← hc, toMul_ofMul, hu]
  have hsq : ∀ a : ZMod 5, a ^ 2 ≠ 3 := by decide
  exact hsq _ h

end TauCeti
