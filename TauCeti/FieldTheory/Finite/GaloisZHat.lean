/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.FieldTheory.Finite.SepClosedSubfield
public import TauCeti.FieldTheory.IsSepClosed
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The absolute Galois group of a finite field is `ℤ̂`

Let `k` be a finite field with `q` elements and `L` an algebraic extension of `k` that is separably
closed, for instance an algebraic closure. The arithmetic Frobenius `x ↦ x ^ q` of `L` generates
`Gal(L/k)` topologically: its fixed field is `k`, so the closure of the subgroup it generates is
the fixing subgroup of `k`. On the fixed field `k_n` of its `n`-th power, of degree `n` over `k`,
it restricts to the Frobenius of `k_n / k`, of order `n`, which detects every finite quotient of
`ℤ`. So the continuous homomorphism `ℤ̂ → Gal(L/k)` sending the generator to Frobenius is
bijective, and `Gal(L/k) ≃ₜ* ℤ̂` with Frobenius going to `zHat.gen`
(`TauCeti.FiniteField.galoisGroupEquivZHat`). The extension is Galois by
`TauCeti.isGalois_of_isSepClosed`.

The proof follows `TauCeti.maximalUnramifiedGaloisGroupEquivZHat`
(`TauCeti/NumberTheory/LocalField/Unramified/ZHat.lean`), through the criteria
`TauCeti.zHat.lift_surjective` and `TauCeti.zHat.lift_injective_of_forall_orderOf` and the
equivalence `TauCeti.zHat.liftContinuousMulEquiv` that both identifications share.

## Main results

* `TauCeti.FiniteField.fixedField_zpowers_frobeniusAlgEquivOfAlgebraic`: the fixed field of
  Frobenius is `k`.
* `TauCeti.FiniteField.topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic`: Frobenius
  generates `Gal(L/k)` topologically.
* `TauCeti.FiniteField.galoisGroupEquivZHat`: `Gal(L/k) ≃ₜ* ℤ̂`, with
  `galoisGroupEquivZHat_apply_frobenius` and `galoisGroupEquivZHat_symm_apply_gen`.
-/

public section

noncomputable section

open IntermediateField

namespace TauCeti.FiniteField

universe u v

variable (k : Type u) (L : Type v) [Field k] [Fintype k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L]

/-- The fixed field of the arithmetic Frobenius of `L` is `k`. -/
theorem fixedField_zpowers_frobeniusAlgEquivOfAlgebraic :
    fixedField (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)) = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  rw [mem_fixedField_zpowers_iff, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic] at hx
  rw [IntermediateField.mem_bot]
  exact (pow_natCard_eq_self_iff_mem_range_algebraMap x).1 (by rwa [Nat.card_eq_fintype_card])

/-- **Frobenius generates the absolute Galois group of a finite field topologically.** -/
theorem topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic [IsGalois k L] :
    (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)).topologicalClosure =
      ⊤ := by
  rw [← fixingSubgroup_fixedField_eq_topologicalClosure,
    fixedField_zpowers_frobeniusAlgEquivOfAlgebraic, fixingSubgroup_bot]

variable [IsSepClosed L]

/-- The fixed field `k_n` of the `n`-th power of Frobenius, of degree `n` over `k`. -/
private abbrev frobeniusLevel (n : ℕ+) : IntermediateField k L :=
  fixedField (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ (n : ℕ)))

private instance (n : ℕ+) : FiniteDimensional k (frobeniusLevel k L n) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero]; exact n.pos)

private instance (n : ℕ+) : Finite (frobeniusLevel k L n) := Module.finite_of_finite k

/-- Restricted to `k_n`, Frobenius has order `n`. -/
private theorem orderOf_restrictNormalHom_frobeniusAlgEquivOfAlgebraic (n : ℕ+) :
    orderOf (AlgEquiv.restrictNormalHom (frobeniusLevel k L n)
      (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)) = n := by
  have : Fintype (frobeniusLevel k L n) := Fintype.ofFinite _
  have h : AlgEquiv.restrictNormalHom (frobeniusLevel k L n)
      (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) =
      _root_.FiniteField.frobeniusAlgEquivOfAlgebraic k (frobeniusLevel k L n) := by
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    simp
  rw [h, _root_.FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero]

/-- The lift to `ℤ̂` of the arithmetic Frobenius is bijective. -/
private theorem frobeniusAlgEquivOfAlgebraic_lift_bijective :
    Function.Bijective (zHat.lift (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) :
      zHat.{v} →ₜ* Gal(L/k)) :=
  ⟨zHat.lift_injective_of_forall_orderOf _ (fun n ↦ Gal(frobeniusLevel k L n/k))
    (fun n ↦ ⟨AlgEquiv.restrictNormalHom _, InfiniteGalois.restrictNormalHom_continuous _⟩)
    (fun n ↦ by
      rw [IsGalois.card_aut_eq_finrank]
      exact finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero)
    (orderOf_restrictNormalHom_frobeniusAlgEquivOfAlgebraic k L),
  zHat.lift_surjective _ (topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic k L)⟩

/-- **The absolute Galois group of a finite field is the profinite integers.** For a finite field
`k` and a separably closed algebraic extension `L`, the continuous multiplicative equivalence
`Gal(L/k) ≃ₜ* ℤ̂` sends the arithmetic Frobenius `x ↦ x ^ q` to `zHat.gen`. -/
def galoisGroupEquivZHat : Gal(L/k) ≃ₜ* zHat.{v} :=
  haveI : T2Space Gal(L/k) := krullTopology_t2
  zHat.liftContinuousMulEquiv _ (frobeniusAlgEquivOfAlgebraic_lift_bijective k L)

/-- The inverse equivalence sends the canonical generator of `ℤ̂` to the arithmetic Frobenius. -/
@[simp]
theorem galoisGroupEquivZHat_symm_apply_gen :
    (galoisGroupEquivZHat k L).symm zHat.gen =
      _root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  rw [galoisGroupEquivZHat, zHat.liftContinuousMulEquiv_symm_apply, zHat.lift_gen]

/-- The equivalence sends the arithmetic Frobenius to the canonical generator of `ℤ̂`. -/
@[simp]
theorem galoisGroupEquivZHat_apply_frobenius :
    galoisGroupEquivZHat k L (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) = zHat.gen := by
  rw [← ContinuousMulEquiv.eq_symm_apply, galoisGroupEquivZHat_symm_apply_gen]

end TauCeti.FiniteField
