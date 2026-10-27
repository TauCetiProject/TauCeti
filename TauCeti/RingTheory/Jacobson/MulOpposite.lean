/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.RingTheory.Jacobson.Basic

/-!
# The Jacobson radical, and semiprimary rings, are left-right symmetric

`Ring.jacobson R` is the intersection of the maximal *left* ideals of `R`, so nothing about the
definition is symmetric in the two sides. Mathlib knows the resulting ideal is two-sided, but it
does not record the sharper statement that the *same* ideal is cut out by the maximal right
ideals, and consequently it leaves the transfer of `IsSemiprimaryRing` to the opposite ring as a
`proof_wanted` in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`, annotated "Need
left-right symmetry of Jacobson radical".

This file supplies that symmetry and the two consequences it was wanted for. The route is the
elementwise description of the radical proved in `TauCeti/RingTheory/Jacobson/Basic.lean`: `x`
lies in `Ring.jacobson R` exactly when `1 + y * x` is a unit for every `y`, and hence, by
`TauCeti.isUnit_one_add_mul_comm`, exactly when `1 + x * y` is a unit for every `y`. The second
description is the first one read in `Rᵐᵒᵖ`, so the radical of the opposite ring is the opposite
of the radical.

## Main results

* `TauCeti.Ring.op_mem_jacobson_mulOpposite_iff`: `MulOpposite.op x` lies in `Ring.jacobson Rᵐᵒᵖ`
  exactly when `x` lies in `Ring.jacobson R` -- the left-right symmetry, in membership form.
* `TauCeti.Ring.quotientJacobsonMulOppositeRingEquiv`: the resulting identification
  `Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ ≃+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ`.
* `TauCeti.isSemiprimaryRing_mulOpposite_iff` and `TauCeti.IsSemiprimaryRing.mulOpposite`:
  semiprimarity passes to the opposite ring.
* `TauCeti.IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite`: a left
  Artinian ring is right Noetherian exactly when it is right Artinian, the statement that
  `WedderburnArtin.lean` records as waiting on the same symmetry.
-/

public section

namespace TauCeti

open MulOpposite

variable (R : Type*) [Ring R]

namespace Ring

variable {R}

/-- **Left-right symmetry of the Jacobson radical**: the intersection of the maximal left ideals
of `Rᵐᵒᵖ` is the opposite of the intersection of the maximal left ideals of `R`, which is to say
that the Jacobson radical of `R` is also the intersection of its maximal right ideals. -/
theorem op_mem_jacobson_mulOpposite_iff {x : R} :
    op x ∈ Ring.jacobson Rᵐᵒᵖ ↔ x ∈ Ring.jacobson R := by
  rw [mem_jacobson_iff_isUnit_one_add_mul_left, mem_jacobson_iff_isUnit_one_add_mul_right,
    op_surjective.forall]
  exact forall_congr' fun y => by rw [← op_one, ← op_mul, ← op_add, isUnit_op]

/-- `TauCeti.Ring.op_mem_jacobson_mulOpposite_iff` phrased for an element of `Rᵐᵒᵖ`. -/
@[simp]
theorem mem_jacobson_mulOpposite_iff {X : Rᵐᵒᵖ} :
    X ∈ Ring.jacobson Rᵐᵒᵖ ↔ X.unop ∈ Ring.jacobson R := by
  conv_lhs => rw [← op_unop X]
  exact op_mem_jacobson_mulOpposite_iff

/-- The Jacobson radical of `Rᵐᵒᵖ` is, as a set, the `op`-image of the Jacobson radical of `R`. -/
theorem coe_jacobson_mulOpposite (R : Type*) [Ring R] :
    (Ring.jacobson Rᵐᵒᵖ : Set Rᵐᵒᵖ) = unop ⁻¹' (Ring.jacobson R) :=
  Set.ext fun _ => mem_jacobson_mulOpposite_iff

/-- The symmetry passes to the powers of the radical: `op` reverses products, so a product of `n`
elements of `Ring.jacobson R` is the opposite of a product of `n` elements of
`Ring.jacobson Rᵐᵒᵖ`, taken in the other order.

This is the forward half of `TauCeti.Ring.op_mem_jacobson_mulOpposite_pow_iff`, which is the form
to use. -/
private theorem op_mem_jacobson_pow (n : ℕ) (x : R) (hx : x ∈ Ring.jacobson R ^ n) :
    op x ∈ Ring.jacobson Rᵐᵒᵖ ^ n := by
  induction n generalizing x with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [op_mul, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (op_mem_jacobson_mulOpposite_iff.mpr hb) (ih a ha)
    · rw [op_add]
      exact Ideal.add_mem _ ha hb

/-- The reverse half of `TauCeti.Ring.op_mem_jacobson_mulOpposite_pow_iff`, the same induction run
in the opposite ring. -/
private theorem unop_mem_jacobson_pow (n : ℕ) (X : Rᵐᵒᵖ) (hX : X ∈ Ring.jacobson Rᵐᵒᵖ ^ n) :
    X.unop ∈ Ring.jacobson R ^ n := by
  induction n generalizing X with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hX
    refine Submodule.mul_induction_on hX (fun A hA B hB => ?_) (fun A B hA hB => ?_)
    · rw [unop_mul, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (mem_jacobson_mulOpposite_iff.mp hB) (ih A hA)
    · rw [unop_add]
      exact Ideal.add_mem _ hA hB

/-- The left-right symmetry of the Jacobson radical, at the level of powers: `op x` lies in the
`n`-th power of `Ring.jacobson Rᵐᵒᵖ` exactly when `x` lies in the `n`-th power of
`Ring.jacobson R`. -/
theorem op_mem_jacobson_mulOpposite_pow_iff {x : R} {n : ℕ} :
    op x ∈ Ring.jacobson Rᵐᵒᵖ ^ n ↔ x ∈ Ring.jacobson R ^ n := by
  refine ⟨fun h => ?_, op_mem_jacobson_pow n x⟩
  have h' := unop_mem_jacobson_pow n (op x) h
  rwa [unop_op] at h'

/-- `TauCeti.Ring.op_mem_jacobson_mulOpposite_pow_iff` phrased for an element of `Rᵐᵒᵖ`. -/
@[simp]
theorem mem_jacobson_mulOpposite_pow_iff {X : Rᵐᵒᵖ} {n : ℕ} :
    X ∈ Ring.jacobson Rᵐᵒᵖ ^ n ↔ X.unop ∈ Ring.jacobson R ^ n := by
  conv_lhs => rw [← op_unop X]
  exact op_mem_jacobson_mulOpposite_pow_iff

variable (R)

/-- Nilpotence of the Jacobson radical is left-right symmetric: the two radicals have the same
vanishing powers. -/
theorem isNilpotent_jacobson_mulOpposite_iff :
    IsNilpotent (Ring.jacobson Rᵐᵒᵖ) ↔ IsNilpotent (Ring.jacobson R) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, eq_bot_iff.mpr fun x hx => ?_⟩
    have hx' := op_mem_jacobson_mulOpposite_pow_iff.mpr hx
    rw [hn] at hx'
    simpa [Ideal.mem_bot] using hx'
  · rintro ⟨n, hn⟩
    refine ⟨n, eq_bot_iff.mpr fun X hX => ?_⟩
    have hX' := mem_jacobson_mulOpposite_pow_iff.mp hX
    rw [hn] at hX'
    simpa [Ideal.mem_bot] using hX'

/-- Reduction modulo the Jacobson radical, read in the opposite ring: this sends `op x` to
`op (Ideal.Quotient.mk (Ring.jacobson R) x)`. -/
private def opQuotientMk : Rᵐᵒᵖ →+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ :=
  RingHom.op (Ideal.Quotient.mk (Ring.jacobson R))

/-- `TauCeti.Ring.opQuotientMk` on `op`-generators. This is how `RingHom.op` is defined, so the
computation is definitional; every later use of `TauCeti.Ring.opQuotientMk` goes through this
lemma rather than through the definition. -/
private theorem opQuotientMk_op (x : R) :
    opQuotientMk R (op x) = op (Ideal.Quotient.mk (Ring.jacobson R) x) := rfl

/-- `TauCeti.Ring.opQuotientMk` is surjective, since `Ideal.Quotient.mk` is. -/
private theorem opQuotientMk_surjective : Function.Surjective (opQuotientMk R) := fun Y => by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective Y.unop
  exact ⟨op x, by rw [opQuotientMk_op, hx, op_unop]⟩

/-- The kernel of `TauCeti.Ring.opQuotientMk` is the Jacobson radical of `Rᵐᵒᵖ`: this is the
left-right symmetry again. -/
private theorem ker_opQuotientMk : RingHom.ker (opQuotientMk R) = Ring.jacobson Rᵐᵒᵖ := by
  ext X
  induction X using MulOpposite.rec' with
  | _ x =>
    rw [RingHom.mem_ker, opQuotientMk_op, op_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      op_mem_jacobson_mulOpposite_iff]

/-- Reduction modulo the Jacobson radical commutes with passing to the opposite ring. -/
noncomputable def quotientJacobsonMulOppositeRingEquiv :
    Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ ≃+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ :=
  (Ideal.quotEquivOfEq (ker_opQuotientMk R).symm).trans
    (RingHom.quotientKerEquivOfSurjective (opQuotientMk_surjective R))

/-- `TauCeti.Ring.quotientJacobsonMulOppositeRingEquiv` is reduction modulo the radical read in
`Rᵐᵒᵖ`: it sends the class of `op x` to the opposite of the class of `x`. -/
@[simp]
theorem quotientJacobsonMulOppositeRingEquiv_mk (x : R) :
    quotientJacobsonMulOppositeRingEquiv R (Ideal.Quotient.mk (Ring.jacobson Rᵐᵒᵖ) (op x)) =
      op (Ideal.Quotient.mk (Ring.jacobson R) x) := by
  rw [quotientJacobsonMulOppositeRingEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, opQuotientMk_op]

/-- The inverse of `TauCeti.Ring.quotientJacobsonMulOppositeRingEquiv`, on generators. -/
@[simp]
theorem quotientJacobsonMulOppositeRingEquiv_symm_op_mk (x : R) :
    (quotientJacobsonMulOppositeRingEquiv R).symm (op (Ideal.Quotient.mk (Ring.jacobson R) x)) =
      Ideal.Quotient.mk (Ring.jacobson Rᵐᵒᵖ) (op x) :=
  (RingEquiv.symm_apply_eq _).mpr (quotientJacobsonMulOppositeRingEquiv_mk R x).symm

/-- Semisimplicity of the quotient by the Jacobson radical is left-right symmetric. -/
theorem isSemisimpleRing_quotient_jacobson_mulOpposite_iff :
    IsSemisimpleRing (Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ) ↔ IsSemisimpleRing (R ⧸ Ring.jacobson R) :=
  (quotientJacobsonMulOppositeRingEquiv R).isSemisimpleRing_iff.trans
    isSemisimpleRing_mulOpposite_iff

end Ring

/-- **Semiprimarity is left-right symmetric**, discharging Mathlib's `proof_wanted`
`isSemiprimaryRing_mulOpposite_iff`. -/
theorem isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R := by
  rw [isSemiprimaryRing_iff, isSemiprimaryRing_iff,
    Ring.isSemisimpleRing_quotient_jacobson_mulOpposite_iff,
    Ring.isNilpotent_jacobson_mulOpposite_iff]

/-- The opposite of a semiprimary ring is semiprimary, discharging Mathlib's `proof_wanted`
`IsSemiprimaryRing.mulOpposite`. -/
instance IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ :=
  (isSemiprimaryRing_mulOpposite_iff R).mpr ‹_›

/-- For a left Artinian ring, being right Noetherian and being right Artinian coincide: the
opposite ring is semiprimary, so Hopkins-Levitzki applies to it. This is the `example` that
`Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean` leaves open. -/
theorem IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ :=
  IsSemiprimaryRing.isNoetherian_iff_isArtinian

end TauCeti
