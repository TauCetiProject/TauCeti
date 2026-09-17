/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny

/-!
# The special isogeny of the rank-two type-`C` carrier

The rank-two member of the explicit full-weight type-`C` Chevalley carrier is the ambient group
of the two classification-list families on the `B₂` diagram, the untwisted `B₂(q)` and the Suzuki
family `²B₂(2^(2m+1))`. Over a field of characteristic two its points carry the special isogeny,
the endomorphism exchanging the two root lengths whose odd powers cut out the Suzuki groups. This
file transports that endomorphism from the symplectic group to the carrier.

The transport is possible because the two point groups coincide:
`TauCeti.SpStd.points_eq_GLSymplecticFin` identifies the carrier's points with the symplectic
matrices over any field, so the special isogeny of `Sp₄` restricts to an endomorphism of the
carrier rather than merely mapping it into a larger group. The four pinning equations and the
square relation below are the symplectic-group statements read through that identification.

## Main definitions

* `TauCeti.SpStd.pointsMulEquivGLSymplecticFin`: the all-rank identification of the carrier's
  points with the symplectic group, specialized here to rank two.
* `TauCeti.SpStd.specialIsogeny`: the special isogeny of the carrier in characteristic two.

## Main results

* `TauCeti.SpStd.specialIsogeny_rootSubgroupPoints_inl_zero` and its three siblings: the pinning
  equations on the four numbered simple root subgroups. The short root at the nonfinal node goes to
  the long root at the final one with the parameter squared, and the long root goes back to the
  short one with the parameter unchanged, which is the exponent convention `1` on a long simple
  root and the defining characteristic on a short one.
* `TauCeti.SpStd.specialIsogeny_specialIsogeny`: the square relation, that the isogeny composed
  with itself is the Frobenius `TauCeti.SpStd.frobenius 1 2 1`, transported from the symplectic
  group along the identification, with `TauCeti.SpStd.specialIsogeny_comp_specialIsogeny` stating
  it for the composite endomorphism itself.

## What is not here

No fixed-point subgroup is formed, no odd power `τ ^ (2m+1)` is taken, and nothing is claimed to be
finite or simple. The isogeny is built on the carrier alone, with no Lie-type index in sight.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (K : Type v) [Field K]

variable [CharP K 2]

/-- **The special isogeny of the rank-two type-`C` carrier in characteristic two.** -/
noncomputable def specialIsogeny : points 1 K →* points 1 K :=
  (pointsMulEquivGLSymplecticFin 1 K).symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := K)).comp (pointsMulEquivGLSymplecticFin 1 K).toMonoidHom)

/-- The matrix of the carrier's special isogeny is the matrix of `2 × 2` minors. -/
@[simp]
theorem coe_specialIsogeny (g : points 1 K) :
    ((specialIsogeny K g : GL (Fin (1 + 1 + (1 + 1))) K) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) K) =
      Matrix.symplecticSpecialIsogeny ((g : GL (Fin (1 + 1 + (1 + 1))) K) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) K) := by
  rw [specialIsogeny, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [coe_pointsMulEquivGLSymplecticFin_symm_apply, TauCeti.coe_specialIsogeny,
    coe_pointsMulEquivGLSymplecticFin_apply]

/-- The special isogeny of the carrier, read in the symplectic group. -/
theorem coe_specialIsogeny_gl (g : points 1 K) :
    ((specialIsogeny K g : points 1 K) : GL (Fin (1 + 1 + (1 + 1))) K) =
      ((TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFin 1 K g) :
        GLSymplecticFin 2 K) : GL (Fin (2 + 2)) K) := by
  rw [specialIsogeny, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [coe_pointsMulEquivGLSymplecticFin_symm_apply]

/-- The identification intertwines the two special isogenies. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_specialIsogeny (g : points 1 K) :
    pointsMulEquivGLSymplecticFin 1 K (specialIsogeny K g) =
      TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFin 1 K g) := by
  rw [specialIsogeny]
  simp

/-- **The square of the carrier's special isogeny is the Frobenius.** -/
@[simp]
theorem specialIsogeny_specialIsogeny (g : points 1 K) :
    specialIsogeny K (specialIsogeny K g) = frobenius 1 2 1 K g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny_gl, pointsMulEquivGLSymplecticFin_specialIsogeny,
    TauCeti.specialIsogeny_specialIsogeny, GLSymplecticFin.coe_map,
    coe_pointsMulEquivGLSymplecticFin_apply]
  ext i j
  rw [coe_frobenius_apply]
  simp [frobenius_def]

/-- **The square of the carrier's special isogeny is the Frobenius**, as an identity of monoid
homomorphisms, so a consumer taking odd powers can rewrite the composite itself. -/
@[simp]
theorem specialIsogeny_comp_specialIsogeny :
    (specialIsogeny K).comp (specialIsogeny K) = frobenius 1 2 1 K :=
  MonoidHom.ext fun g => specialIsogeny_specialIsogeny K g

private theorem zero_ne_last : (0 : Fin (1 + 1)) ≠ Fin.last 1 := by decide

private theorem next_zero : next 1 0 zero_ne_last = 1 := Fin.ext (by rw [val_next]; rfl)

private theorem last_one : Fin.last 1 = (1 : Fin (1 + 1)) := rfl

-- The two rank-two transports below name the successor node in one form and the numeral in the
-- other, so they need the index pair of a difference short-root element to be all that matters.
omit [CharP K 2] in
private theorem shortRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin 1 K
        (rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (0 : Fin (1 + 1)) ≠ 1 by decide) t := by
  rw [pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_of_ne_last 1 0 zero_ne_last,
    toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _ rfl next_zero]

omit [CharP K 2] in
private theorem longRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin 1 K
        (rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.positiveLongRootTransvectionUnit 1 t := by
  rw [pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_last, toAdd_ofAdd, last_one]

/-- The isogeny carries the short simple root subgroup to the long one, squaring the parameter. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inl_zero (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, shortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFin_apply] using
    congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
      (longRootUnit_eq K (t ^ 2)).symm

/-- The isogeny carries the long simple root subgroup to the short one, keeping the parameter. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inl_last (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, longRootUnit_eq,
    TauCeti.specialIsogeny_positiveLongRootTransvectionUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFin_apply] using
    congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
      (shortRootUnit_eq K t).symm

omit [CharP K 2] in
private theorem negShortRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin 1 K
        (rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (1 : Fin (1 + 1)) ≠ 0 by decide) t := by
  rw [pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inr_of_ne_last 1 0 zero_ne_last,
    toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _ next_zero rfl]

omit [CharP K 2] in
private theorem negLongRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin 1 K
        (rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.negativeLongRootTransvectionUnit 1 t := by
  rw [pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inr_last, toAdd_ofAdd, last_one]

/-- The isogeny on the negative short simple root subgroup. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inr_zero (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negShortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit_one_zero]
  simpa only [coe_pointsMulEquivGLSymplecticFin_apply] using
    congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
      (negLongRootUnit_eq K (t ^ 2)).symm

/-- The isogeny on the negative long simple root subgroup. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inr_last (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negLongRootUnit_eq,
    TauCeti.specialIsogeny_negativeLongRootTransvectionUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFin_apply] using
    congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
      (negShortRootUnit_eq K t).symm

end TauCeti.SpStd
