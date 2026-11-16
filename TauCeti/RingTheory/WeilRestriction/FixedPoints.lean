/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Invariant.FixedPointIdeal
public import TauCeti.RingTheory.Invariant.Galois
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth
import TauCeti.RingTheory.Invariant.ModuleDescent

/-!
# Edixhoven's tame fixed-point theorem for Weil restrictions

Let `B` be a finite projective `A`-algebra, let `C` be a finitely presented `B`-algebra, and let a
monoid `Γ` act on `B` by `A`-algebra automorphisms (`ρB`) and semilinearly on `C` by ring
automorphisms (`ρC`). By `WeilRestriction.inducedAction` and
`WeilRestriction.inducedMulSemiringAction`, `Γ` acts on `WeilRestriction A B C` by `A`-algebra
automorphisms.

This file studies the closed subscheme `(Res_{B/A} Spec C)^Γ` cut out by the fixed-point ideal
`WeilRestriction.fixedPointIdeal ρB ρC h`:

* **Universal property on points.** For every `A`-algebra `T`, `A`-algebra homomorphisms out of
  `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` into `T` correspond bijectively via
  `WeilRestriction.homEquiv` to `Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`
  (`WeilRestriction.fixedPointsHomEquiv`).
* **Edixhoven's tame fixed-point smoothness theorem.** Because `WeilRestriction A B C` is smooth
  over `A` whenever `C` is smooth over `B` (`WeilRestriction.instSmooth`), applying
  `TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit` shows that when `Γ` is a
  finite group whose order `#Γ` is invertible in `A` and `C` is smooth over `B`, the fixed-point
  quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is smooth over `A`
  (`WeilRestriction.smooth_fixedPoints`, `WeilRestriction.instSmoothQuotientFixedPointIdeal`), with
  no henselian or discrete-valuation-ring hypothesis on the base.
* **Trivial action and tame affine line.** A trivial action fixes the entire Weil restriction
  (`WeilRestriction.fixedPointIdeal_eq_bot_of_eq_one`, `WeilRestriction.fixedPointIdeal_one`,
  `WeilRestriction.quotientFixedPointIdealAlgEquivOfEqOne`). For `C = B[X]` with `Γ` acting on
  coefficients, when `#Γ` is invertible in `A`, `algebraMap A B` is injective, and the
  `Γ`-invariants of `B` come from `A` (in particular, for a Galois extension of integrally closed
  domains of degree invertible in `A`, such as a totally tamely ramified Galois extension of
  discrete valuation rings), `(#Γ)⁻¹` has trace `1`, so
  `TauCeti.MulSemiringAction.invariantsBaseChangeEquiv` identifies `(B ⊗[A] T)^Γ` with `T` and
  yields the `A`-algebra isomorphism `(WeilRestriction A B B[X] ⧸ fixedPointIdeal ...) ≃ₐ[A] A[X]`
  (`WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv`,
  `WeilRestriction.quotientFixedPointIdealPolynomialAlgEquivOfIsGalois`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointIdeal`: the fixed-point ideal of the induced `Γ`-action
  on `WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.fixedPointsHomEquiv`: the universal bijection between points of
  the fixed-point quotient and `Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealAlgEquivOfEqOne`: the isomorphism with
  `WeilRestriction A B C` when `Γ` acts trivially on `B` and `C`.
* `TauCeti.Algebra.WeilRestriction.polynomialAction`: the semilinear coefficient action of `Γ` on
  `B[X]`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv` and
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquivOfIsGalois`: the
  isomorphism `(Res_{B/A} 𝔸¹_B)^Γ ≃ₐ[A] 𝔸¹_A` when `#Γ` is invertible in `A` and `B^Γ = A`.

## Main results

* `TauCeti.Algebra.WeilRestriction.finitePresentation_quotient_fixedPointIdeal`: finite presentation
  of the fixed-point quotient for finite `Γ`.
* `TauCeti.Algebra.WeilRestriction.smooth_fixedPoints` and
  `TauCeti.Algebra.WeilRestriction.instSmoothQuotientFixedPointIdeal`: Edixhoven's theorem that
  `(Res_{B/A} X)^Γ` is smooth over `A` when `X` is smooth affine over `B` and `#Γ` is invertible
  in `A`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.1
  (p. 293) and Proposition 3.4 (pp. 294–295).
-/

public noncomputable section

open Algebra TensorProduct
open scoped Polynomial

namespace TauCeti.Algebra.WeilRestriction

section InducedAction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The **fixed-point ideal** of the `Γ`-action on `WeilRestriction A B C` induced by `(ρB, ρC, h)`:
the ideal cutting out the closed subscheme `(Res_{B/A} Spec C)^Γ`. -/
def fixedPointIdeal : Ideal (WeilRestriction A B C) :=
  letI := inducedMulSemiringAction ρB ρC h
  TauCeti.MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)

/-- `WeilRestriction.fixedPointIdeal` coincides with `TauCeti.MulSemiringAction.fixedPointIdeal`
for `inducedMulSemiringAction`. -/
theorem fixedPointIdeal_eq_mulSemiringActionFixedPointIdeal :
    letI := inducedMulSemiringAction ρB ρC h
    fixedPointIdeal ρB ρC h =
      TauCeti.MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) :=
  (rfl)

/-- Explicit span description of `WeilRestriction.fixedPointIdeal`. -/
theorem fixedPointIdeal_def :
    fixedPointIdeal ρB ρC h =
      Ideal.span {x : WeilRestriction A B C | ∃ γ y, inducedAction ρB ρC h γ y - y = x} := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_def]
  simp only [MulAction.compHom_smul_def, AlgEquiv.smul_def]

/-- Every displacement `inducedAction ρB ρC h γ x - x` lies in `fixedPointIdeal ρB ρC h`. -/
theorem sub_mem_fixedPointIdeal (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x - x ∈ fixedPointIdeal ρB ρC h := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal]
  simpa only [MulAction.compHom_smul_def, AlgEquiv.smul_def] using
    TauCeti.MulSemiringAction.smul_sub_mem_fixedPointIdeal γ x

/-- `fixedPointIdeal ρB ρC h` is the smallest ideal containing every displacement
`inducedAction ρB ρC h γ x - x`. -/
theorem fixedPointIdeal_le_iff {I : Ideal (WeilRestriction A B C)} :
    fixedPointIdeal ρB ρC h ≤ I ↔ ∀ γ x, inducedAction ρB ρC h γ x - x ∈ I := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_le_iff]
  refine forall₂_congr fun γ x ↦ ?_
  rw [MulAction.compHom_smul_def, AlgEquiv.smul_def]

/-- In the quotient by `fixedPointIdeal ρB ρC h`, `inducedAction` acts trivially. -/
-- Not `@[simp]`: `inducedAction_apply` simplifies the inner argument to `semilinearMap`, handled by
-- `mk_fixedPointIdeal_semilinearMap`.
theorem mk_fixedPointIdeal_inducedAction (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) (inducedAction ρB ρC h γ x) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x :=
  Ideal.Quotient.eq.mpr (sub_mem_fixedPointIdeal ρB ρC h γ x)

/-- In the quotient by `fixedPointIdeal ρB ρC h`, the semilinear endomorphism attached to `γ` acts
trivially. -/
@[simp]
theorem mk_fixedPointIdeal_semilinearMap (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mk (fixedPointIdeal ρB ρC h)
        (semilinearMap (ρB γ) (ρC γ : C →+* C) (h γ) x) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x := by
  rw [← inducedAction_apply]
  exact mk_fixedPointIdeal_inducedAction ρB ρC h γ x

/-- `Ideal.Quotient.mkₐ` form of `mk_fixedPointIdeal_inducedAction`. -/
-- Not `@[simp]`: `inducedAction_apply` simplifies the inner argument to `semilinearMap`, handled by
-- `mkₐ_fixedPointIdeal_semilinearMap`.
theorem mkₐ_fixedPointIdeal_inducedAction (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h) (inducedAction ρB ρC h γ x) =
      Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h) x :=
  mk_fixedPointIdeal_inducedAction ρB ρC h γ x

/-- `Ideal.Quotient.mkₐ` form of `mk_fixedPointIdeal_semilinearMap`. -/
@[simp]
theorem mkₐ_fixedPointIdeal_semilinearMap (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h)
        (semilinearMap (ρB γ) (ρC γ : C →+* C) (h γ) x) =
      Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h) x :=
  mk_fixedPointIdeal_semilinearMap ρB ρC h γ x

/-- **Points of `(Res_{B/A} Spec C)^Γ`**: an `A`-algebra homomorphism `g` out of
`WeilRestriction A B C` kills `fixedPointIdeal ρB ρC h` if and only if the `B`-algebra homomorphism
`homEquiv A B C T g : C →ₐ[B] B ⊗[A] T` it classifies is `Γ`-equivariant. -/
theorem fixedPointIdeal_le_ker_iff {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    fixedPointIdeal ρB ρC h ≤ RingHom.ker g ↔
      ∀ γ c, homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_le_ker_iff_comp_toAlgHom_eq]
  refine forall_congr' fun γ ↦ ?_
  have hto : _root_.MulSemiringAction.toAlgHom A (WeilRestriction A B C) γ =
      (inducedAction ρB ρC h γ : WeilRestriction A B C →ₐ[A] WeilRestriction A B C) :=
    AlgHom.ext fun x ↦ by
      rw [_root_.MulSemiringAction.toAlgHom_apply, MulAction.compHom_smul_def, AlgEquiv.smul_def,
        AlgEquiv.coe_toAlgHom]
  rw [hto, comp_inducedAction_eq_iff]

/-- **Universal property of `(Res_{B/A} Spec C)^Γ`** (Edixhoven, Proposition 3.1): `A`-algebra
homomorphisms out of `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` into `T` correspond
bijectively to `Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointsHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T //
        ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  letI := inducedMulSemiringAction ρB ρC h
  (TauCeti.MulSemiringAction.quotientFixedPointIdealAlgHomEquiv A Γ (WeilRestriction A B C) T).trans
    ((homEquiv A B C T).subtypeEquiv fun g ↦
      (TauCeti.MulSemiringAction.fixedPointIdeal_le_ker_algHom_iff g).symm.trans
        (fixedPointIdeal_le_ker_iff ρB ρC h g))

/-- Forward direction of `fixedPointsHomEquiv`. -/
@[simp]
theorem fixedPointsHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h →ₐ[A] T) :
    (fixedPointsHomEquiv ρB ρC h T g).1 =
      homEquiv A B C T (g.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) := by
  unfold fixedPointsHomEquiv fixedPointIdeal at *
  simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    TauCeti.MulSemiringAction.quotientFixedPointIdealAlgHomEquiv_apply]

/-- Inverse direction of `fixedPointsHomEquiv` evaluated on a quotient class. -/
@[simp]
theorem fixedPointsHomEquiv_symm_apply_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T //
      ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)})
    (x : WeilRestriction A B C) :
    (fixedPointsHomEquiv ρB ρC h T).symm y (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) =
      (homEquiv A B C T).symm y.1 x := by
  unfold fixedPointsHomEquiv fixedPointIdeal at *
  simp only [Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    TauCeti.MulSemiringAction.quotientFixedPointIdealAlgHomEquiv_symm_apply_mk]

/-- Classifying the composite of `Ideal.Quotient.mkₐ` with `(fixedPointsHomEquiv ...).symm y`
recovers `y`. -/
theorem homEquiv_fixedPointsHomEquiv_symm_comp_mkₐ {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T //
      ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    homEquiv A B C T
        (((fixedPointsHomEquiv ρB ρC h T).symm y).comp
          (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) = y.1 := by
  have := (fixedPointsHomEquiv ρB ρC h T).apply_symm_apply y
  simpa only [fixedPointsHomEquiv_apply] using congrArg Subtype.val this

/-- **Trivial action fixes all of `Res_{B/A} Spec C`**: if `Γ` acts trivially on `B` and on `C`,
then `fixedPointIdeal ρB ρC h = ⊥`. -/
theorem fixedPointIdeal_eq_bot_of_eq_one (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdeal ρB ρC h = ⊥ := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_eq_bot_iff]
  intro γ x
  rw [MulAction.compHom_smul_def, inducedAction_eq_one ρB ρC h hB hC, MonoidHom.one_apply,
    one_smul]

/-- The fixed-point ideal of the trivial homomorphisms `1` on `B` and `C` is `⊥`. -/
@[simp]
theorem fixedPointIdeal_one
    (h : ∀ (γ : Γ) (b : B), (1 : Γ →* RingAut C) γ (algebraMap B C b) =
      algebraMap B C ((1 : Γ →* (B ≃ₐ[A] B)) γ b)) :
    fixedPointIdeal (1 : Γ →* (B ≃ₐ[A] B)) (1 : Γ →* RingAut C) h = ⊥ :=
  fixedPointIdeal_eq_bot_of_eq_one _ _ h rfl rfl

/-- For a trivial action on `B` and on `C`, the fixed-point quotient is canonically isomorphic to
`WeilRestriction A B C` itself. -/
def quotientFixedPointIdealAlgEquivOfEqOne (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointIdeal_eq_bot_of_eq_one ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- `quotientFixedPointIdealAlgEquivOfEqOne` sends the class of `x` to `x`. -/
@[simp]
theorem quotientFixedPointIdealAlgEquivOfEqOne_mk (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    quotientFixedPointIdealAlgEquivOfEqOne ρB ρC h hB hC
        (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) = x := by
  simp [quotientFixedPointIdealAlgEquivOfEqOne]

/-- `quotientFixedPointIdealAlgEquivOfEqOne` sends `Ideal.Quotient.mkₐ A ... x` to `x`. -/
-- Not `@[simp]`: `Ideal.Quotient.mkₐ_eq_mk` reduces the argument to `Ideal.Quotient.mk`.
theorem quotientFixedPointIdealAlgEquivOfEqOne_mkₐ (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    quotientFixedPointIdealAlgEquivOfEqOne ρB ρC h hB hC
        (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h) x) = x :=
  quotientFixedPointIdealAlgEquivOfEqOne_mk ρB ρC h hB hC x

/-- Inverse of `quotientFixedPointIdealAlgEquivOfEqOne`: the canonical quotient projection. -/
@[simp]
theorem quotientFixedPointIdealAlgEquivOfEqOne_symm_apply (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (quotientFixedPointIdealAlgEquivOfEqOne ρB ρC h hB hC).symm x =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x := by
  simp [quotientFixedPointIdealAlgEquivOfEqOne]

/-! ### Finite generation, finite presentation, and Edixhoven's smoothness theorem -/

/-- When `Γ` is finite, `WeilRestriction.fixedPointIdeal` is finitely generated. -/
theorem fixedPointIdeal_fg [Finite Γ] : (fixedPointIdeal ρB ρC h).FG := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact TauCeti.MulSemiringAction.fixedPointIdeal_fg (R := A)

/-- When `Γ` is finite, the fixed-point quotient of `WeilRestriction A B C` is finitely presented
over `A`. -/
instance finitePresentation_quotient_fixedPointIdeal [Finite Γ] :
    FinitePresentation A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) :=
  FinitePresentation.quotient (fixedPointIdeal_fg ρB ρC h)

/-- **Edixhoven's formal smoothness theorem for Weil restrictions**: if `C` is formally smooth
(and finitely presented) over a finite projective `A`-algebra `B` and `Γ` is a finite group of order
invertible in `A` acting semilinearly on `(B, C)`, then `(Res_{B/A} Spec C)^Γ` is formally smooth
over `A`. -/
theorem formallySmooth_quotient_fixedPointIdeal {Γ : Type*} [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
    (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
    [FormallySmooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact TauCeti.MulSemiringAction.formallySmooth_quotient_fixedPointIdeal_of_isUnit hΓ

/-- Typeclass form of `formallySmooth_quotient_fixedPointIdeal` when `Nat.card Γ` carries an
`Invertible` instance in `A`. -/
instance instFormallySmoothQuotientFixedPointIdeal {Γ : Type*} [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
    (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
    [FormallySmooth B C] [Invertible (Nat.card Γ : A)] :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) :=
  formallySmooth_quotient_fixedPointIdeal ρB ρC h (isUnit_of_invertible _)

/-- **Edixhoven's tame fixed-point smoothness theorem for Weil restrictions**
(Edixhoven, Propositions 3.1 and 3.4): if `C` is smooth over a finite projective `A`-algebra `B`
and `Γ` is a finite group of order invertible in `A` acting semilinearly on `(B, C)`, then the
fixed-point scheme `(Res_{B/A} Spec C)^Γ` is smooth over `A`. -/
theorem smooth_fixedPoints {Γ : Type*} [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
    (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
    [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit hΓ

/-- Typeclass form of `smooth_fixedPoints` when `Nat.card Γ` carries an `Invertible` instance in
`A`. -/
instance instSmoothQuotientFixedPointIdeal {Γ : Type*} [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
    (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
    [Smooth B C] [Invertible (Nat.card Γ : A)] :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) where

end InducedAction

section TypeclassFixedPointIdeal

variable {A B C Γ : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  [Group Γ] [_root_.MulSemiringAction Γ B] [SMulCommClass Γ A B]
  [_root_.MulSemiringAction Γ C] [SMulDistribClass Γ B C]

/-- For a semilinear typeclass action of a group `Γ` on `(B, C)`, `WeilRestriction.fixedPointIdeal`
coincides with `TauCeti.MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)`. -/
@[simp]
theorem fixedPointIdeal_toAlgAut_toRingAut
    (h : ∀ (γ : Γ) (b : B),
      _root_.MulSemiringAction.toRingAut Γ C γ (algebraMap B C b) =
        algebraMap B C (_root_.MulSemiringAction.toAlgAut Γ A B γ b)) :
    fixedPointIdeal (_root_.MulSemiringAction.toAlgAut Γ A B)
        (_root_.MulSemiringAction.toRingAut Γ C) h =
      TauCeti.MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) :=
  (rfl)

end TypeclassFixedPointIdeal

/-! ### Tame descent of the affine line -/

section TameLine

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The semilinear action of a monoid `Γ` on the polynomial ring `B[X]` through its action `ρB` on
the coefficients `B`, fixing the indeterminate `X`. -/
def polynomialAction {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) : Γ →* RingAut B[X] where
  toFun γ := Polynomial.mapEquiv (ρB γ : B ≃+* B)
  map_one' := RingEquiv.ext fun p ↦ by
    simp only [map_one, Polynomial.mapEquiv_apply, RingAut.one_apply]
    exact Polynomial.map_id
  map_mul' γ δ := RingEquiv.ext fun p ↦ by
    simp only [map_mul, Polynomial.mapEquiv_apply, RingAut.mul_apply]
    exact (Polynomial.map_map (ρB δ : B →+* B) (ρB γ : B →+* B) p).symm

/-- `polynomialAction ρB γ` acts on a polynomial by mapping its coefficients through `ρB γ`. -/
-- Not `@[simp]`: `polynomialAction_C` and `polynomialAction_X` simplify generators directly.
theorem polynomialAction_apply {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (γ : Γ) (p : B[X]) :
    polynomialAction ρB γ p = Polynomial.map (ρB γ : B →+* B) p := by
  simp [polynomialAction]

/-- `polynomialAction` transforms constant polynomials via `ρB`. -/
@[simp]
theorem polynomialAction_C {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialAction ρB γ (Polynomial.C b) = Polynomial.C (ρB γ b) := by
  simp [polynomialAction_apply]

/-- `polynomialAction` fixes the indeterminate `X`. -/
@[simp]
theorem polynomialAction_X {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) :
    polynomialAction ρB γ Polynomial.X = Polynomial.X := by
  simp [polynomialAction_apply]

/-- `polynomialAction` is `ρB`-semilinear with respect to `algebraMap B B[X]`. -/
theorem polynomialAction_algebraMap {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (γ : Γ) (b : B) :
    polynomialAction ρB γ (algebraMap B B[X] b) = algebraMap B B[X] (ρB γ b) :=
  polynomialAction_C ρB γ b

/-- Evaluation of `B[X]` at `1 ⊗ₜ X ∈ B ⊗[A] A[X]` is `Γ`-equivariant for `polynomialAction`. -/
private theorem aeval_one_tmul_X_polynomialAction {Γ : Type*} [Monoid Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (f : B[X]) :
    Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) (polynomialAction ρB γ f) =
      Algebra.TensorProduct.rTensor A[X] (ρB γ : B →ₐ[A] B)
        (Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) f) := by
  let φ₁ : B[X] →+* B ⊗[A] A[X] :=
    (Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X])).toRingHom.comp
      (polynomialAction ρB γ : B[X] →+* B[X])
  let φ₂ : B[X] →+* B ⊗[A] A[X] :=
    (Algebra.TensorProduct.rTensor A[X] (ρB γ : B →ₐ[A] B)).toRingHom.comp
      (Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X])).toRingHom
  suffices φ₁ = φ₂ from RingHom.congr_fun this f
  apply Polynomial.ringHom_ext'
  · ext b
    simp [φ₁, φ₂]
  · simp [φ₁, φ₂]

section Retraction

variable {Γ : Type*} [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B))

private def algAutActionToRingAut : Γ →* RingAut B where
  toFun γ := (ρB γ).toRingEquiv
  map_one' := by ext; simp
  map_mul' γ δ := by ext; simp

omit [Finite Γ] in
private theorem exists_trace_eq_one_of_isUnit_card [Fintype Γ] (hΓ : IsUnit (Nat.card Γ : A)) :
    letI : _root_.MulSemiringAction Γ B :=
      _root_.MulSemiringAction.compHom B (algAutActionToRingAut ρB)
    ∃ c : B, ∑ γ : Γ, γ • c = 1 := by
  let _ : Invertible (Nat.card Γ : A) := hΓ.nonempty_invertible.some
  let _ : _root_.MulSemiringAction Γ B :=
    _root_.MulSemiringAction.compHom B (algAutActionToRingAut ρB)
  refine ⟨algebraMap A B ⅟(Nat.card Γ : A), ?_⟩
  have hsmul (γ : Γ) :
      γ • algebraMap A B ⅟(Nat.card Γ : A) = algebraMap A B ⅟(Nat.card Γ : A) := by
    rw [MulAction.compHom_smul_def, algAutActionToRingAut, MonoidHom.coe_mk, OneHom.coe_mk,
      RingAut.smul_def, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
  simp only [hsmul, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul A, smul_eq_mul, mul_invOf_self, map_one]

omit [Finite Γ] in
private theorem compHom_smul_eq_rTensor (T : Type*) [CommRing T] [Algebra A T]
    (γ : Γ) (z : B ⊗[A] T) :
    letI : _root_.MulSemiringAction Γ B :=
      _root_.MulSemiringAction.compHom B (algAutActionToRingAut ρB)
    letI : SMulCommClass Γ A B := ⟨fun γ a b ↦ by
      rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
      exact map_smul (ρB γ) a b⟩
    letI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
    γ • z = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z := by
  let _ : _root_.MulSemiringAction Γ B :=
    _root_.MulSemiringAction.compHom B (algAutActionToRingAut ρB)
  let _ : SMulCommClass Γ A B := ⟨fun γ a b ↦ by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    exact map_smul (ρB γ) a b⟩
  let _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  induction z using TensorProduct.inductionOn with
  | tmul b t =>
    rw [TensorProduct.smul_tmul', MulAction.compHom_smul_def]
    simp [algAutActionToRingAut]
  | add x y hx hy => rw [smul_add, map_add, hx, hy]

/-- Tame base-change invariants equivalence `T ≃ (B ⊗[A] T)^Γ` sending `t ↦ 1 ⊗ₜ t`, obtained from
`TauCeti.MulSemiringAction.invariantsBaseChangeEquiv` applied to the trace-`1` element `(#Γ)⁻¹`. -/
private def tameInvariantsEquiv (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (T : Type*) [CommRing T] [Algebra A T] :
    T ≃ {z : B ⊗[A] T //
      ∀ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z = z} :=
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : _root_.MulSemiringAction Γ B :=
    _root_.MulSemiringAction.compHom B (algAutActionToRingAut ρB)
  letI : SMulCommClass Γ A B := ⟨fun γ a b ↦ by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    exact map_smul (ρB γ) a b⟩
  letI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  letI : _root_.Algebra.IsInvariant A B Γ := ⟨fun b hb ↦ hfix b fun γ ↦ by
    simpa [MulAction.compHom_smul_def, algAutActionToRingAut] using hb γ⟩
  (TauCeti.MulSemiringAction.invariantsBaseChangeEquiv A B Γ T
    (exists_trace_eq_one_of_isUnit_card ρB hΓ)).toEquiv.trans
    (Equiv.subtypeEquivRight fun z ↦ by
      rw [Representation.mem_invariants]
      refine forall_congr' fun γ ↦ ?_
      simp [compHom_smul_eq_rTensor ρB T γ z])

private theorem tameInvariantsEquiv_apply_val (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (T : Type*) [CommRing T] [Algebra A T] (t : T) :
    (tameInvariantsEquiv ρB hΓ hinj hfix T t).1 =
      Algebra.TensorProduct.includeRight (R := A) (A := B) t := by
  simp [tameInvariantsEquiv]

private theorem includeRight_tameInvariantsEquiv_symm (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (T : Type*) [CommRing T] [Algebra A T]
    (z : {z : B ⊗[A] T //
      ∀ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z = z}) :
    Algebra.TensorProduct.includeRight (R := A) (A := B)
      ((tameInvariantsEquiv ρB hΓ hinj hfix T).symm z) = z.1 := by
  rw [← tameInvariantsEquiv_apply_val ρB hΓ hinj hfix T, Equiv.apply_symm_apply]

section PolynomialEquiv

variable [Module.Finite A B] [Module.Projective A B]

private def polynomialForwardHom :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)) →ₐ[A] A[X] :=
  (fixedPointsHomEquiv ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB) A[X]).symm
    ⟨Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]),
      aeval_one_tmul_X_polynomialAction ρB⟩

omit [Finite Γ] in
private theorem homEquiv_polynomialForwardHom_comp_mkₐ :
    homEquiv A B B[X] A[X]
      ((polynomialForwardHom ρB).comp
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))) =
      Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) :=
  homEquiv_fixedPointsHomEquiv_symm_comp_mkₐ ρB (polynomialAction ρB)
    (polynomialAction_algebraMap ρB) ⟨_, aeval_one_tmul_X_polynomialAction ρB⟩

omit [Finite Γ] in
private theorem rTensor_homEquiv_mkₐ_X (γ : Γ) :
    Algebra.TensorProduct.rTensor _ (ρB γ : B →ₐ[A] B)
        (homEquiv A B B[X] _
          (Ideal.Quotient.mkₐ A
            (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))
          Polynomial.X) =
      homEquiv A B B[X] _
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))
        Polynomial.X := by
  have hq := (fixedPointIdeal_le_ker_iff ρB (polynomialAction ρB)
    (polynomialAction_algebraMap ρB)
    (Ideal.Quotient.mkₐ A
      (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))).mp
    (Ideal.Quotient.mkₐ_ker A _).ge γ Polynomial.X
  simpa only [polynomialAction_X] using hq.symm

private def polynomialGenerator (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    WeilRestriction A B B[X] ⧸
      fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB) :=
  (tameInvariantsEquiv ρB hΓ hinj hfix _).symm
    ⟨homEquiv A B B[X] _
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))
        Polynomial.X,
      rTensor_homEquiv_mkₐ_X ρB⟩

private theorem includeRight_polynomialGenerator (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    Algebra.TensorProduct.includeRight (R := A) (A := B)
        (polynomialGenerator ρB hΓ hinj hfix) =
      homEquiv A B B[X] _
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))
        Polynomial.X :=
  includeRight_tameInvariantsEquiv_symm ρB hΓ hinj hfix _ _

/-- **Tame fixed-point scheme of `Res_{B/A} 𝔸¹_B`**: when `#Γ` is invertible in `A`,
`algebraMap A B` is injective, and every `Γ`-invariant element of `B` lies in the image of `A`, the
fixed-point quotient of `WeilRestriction A B B[X]` under the coefficient action of `Γ` is
isomorphic as an `A`-algebra to `A[X]`. -/
def quotientFixedPointIdealPolynomialAlgEquiv (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)) ≃ₐ[A] A[X] :=
  AlgEquiv.ofAlgHom (polynomialForwardHom ρB)
    (Polynomial.aeval (polynomialGenerator ρB hΓ hinj hfix))
    (by
      refine Polynomial.algHom_ext ?_
      rw [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X]
      refine (tameInvariantsEquiv ρB hΓ hinj hfix A[X]).injective (Subtype.ext ?_)
      rw [tameInvariantsEquiv_apply_val, tameInvariantsEquiv_apply_val]
      calc
        Algebra.TensorProduct.includeRight (R := A) (A := B)
            (polynomialForwardHom ρB (polynomialGenerator ρB hΓ hinj hfix))
            = Algebra.TensorProduct.lTensor (S := B) B (polynomialForwardHom ρB)
                (Algebra.TensorProduct.includeRight (R := A) (A := B)
                  (polynomialGenerator ρB hΓ hinj hfix)) := by simp
        _ = Algebra.TensorProduct.lTensor (S := B) B (polynomialForwardHom ρB)
              (homEquiv A B B[X] _
                (Ideal.Quotient.mkₐ A
                  (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))
                Polynomial.X) := by rw [includeRight_polynomialGenerator]
        _ = homEquiv A B B[X] A[X]
              ((polynomialForwardHom ρB).comp
                (Ideal.Quotient.mkₐ A
                  (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB))))
              Polynomial.X := by rw [homEquiv_comp, AlgHom.comp_apply]
        _ = Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) Polynomial.X := by
              rw [homEquiv_polynomialForwardHom_comp_mkₐ]
        _ = Algebra.TensorProduct.includeRight (R := A) (A := B) Polynomial.X := by simp)
    (by
      refine Ideal.Quotient.algHom_ext A ?_
      apply (homEquiv A B B[X] _).injective
      refine Polynomial.algHom_ext' (by ext) ?_
      rw [AlgHom.comp_assoc, homEquiv_comp, AlgHom.comp_apply,
        homEquiv_polynomialForwardHom_comp_mkₐ]
      simp only [Polynomial.aeval_X, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.id_comp]
      exact includeRight_polynomialGenerator ρB hΓ hinj hfix)

/-- The forward direction of `quotientFixedPointIdealPolynomialAlgEquiv` classifies evaluation at
`1 ⊗ₜ X`. -/
theorem homEquiv_quotientFixedPointIdealPolynomialAlgEquiv_comp_mkₐ
    (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    homEquiv A B B[X] A[X]
        ((quotientFixedPointIdealPolynomialAlgEquiv ρB hΓ hinj hfix).toAlgHom.comp
          (Ideal.Quotient.mkₐ A
            (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))) =
      Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) :=
  homEquiv_polynomialForwardHom_comp_mkₐ ρB

end PolynomialEquiv

end Retraction

private theorem algebraMap_injective_of_isScalarTower
    {K L : Type*} [CommRing K] [CommRing L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [FaithfulSMul A K] [FaithfulSMul K L] :
    Function.Injective (algebraMap A B) := fun a₁ a₂ h ↦
  FaithfulSMul.algebraMap_injective A K <|
    FaithfulSMul.algebraMap_injective K L <| by
      rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L,
        IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L, h]

private theorem mem_range_algebraMap_of_fixed_of_isGalois [Module.Finite A B]
    {K L : Type*} [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosedIn A K] [IsGalois K L] [FaithfulSMul B L]
    (ρB : Gal(L/K) →* (B ≃ₐ[A] B))
    (hρB : ∀ (σ : Gal(L/K)) (b : B), algebraMap B L (ρB σ b) = σ (algebraMap B L b))
    (b : B) (hb : ∀ σ : Gal(L/K), ρB σ b = b) :
    b ∈ Set.range (algebraMap A B) := by
  have hint : IsIntegral A (algebraMap B L b) :=
    IsIntegral.map (IsScalarTower.toAlgHom A B L) (Algebra.IsIntegral.isIntegral b)
  have hfixL (σ : Gal(L/K)) : σ (algebraMap B L b) = algebraMap B L b := by
    rw [← hρB, hb]
  obtain ⟨a, ha⟩ := (TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed K
    (algebraMap B L b)).mpr ⟨hint, hfixL⟩
  refine ⟨a, FaithfulSMul.algebraMap_injective B L ?_⟩
  rwa [← IsScalarTower.algebraMap_apply A B L]

/-- **Tame fixed-point scheme of `Res_{B/A} 𝔸¹_B` for a Galois extension of integrally closed
domains** (such as a Galois extension of discrete valuation rings of degree invertible in `A`):
when `A` is integrally closed in `K`, `L / K` is Galois, `B` is an `A`-finite-projective
`A`-algebra inside `L` stabilized by `Gal(L/K)` via `ρB`, and `#Gal(L/K)` is invertible in `A`,
the fixed-point scheme `(Res_{B/A} 𝔸¹_B)^{Gal(L/K)}` is `𝔸¹_A`. -/
def quotientFixedPointIdealPolynomialAlgEquivOfIsGalois [Module.Finite A B] [Module.Projective A B]
    {K L : Type*} [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosedIn A K] [IsGalois K L] [Finite Gal(L/K)]
    [FaithfulSMul A K] [FaithfulSMul B L]
    (ρB : Gal(L/K) →* (B ≃ₐ[A] B))
    (hρB : ∀ (σ : Gal(L/K)) (b : B), algebraMap B L (ρB σ b) = σ (algebraMap B L b))
    (hΓ : IsUnit (Nat.card Gal(L/K) : A)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)) ≃ₐ[A] A[X] :=
  quotientFixedPointIdealPolynomialAlgEquiv ρB hΓ
    (algebraMap_injective_of_isScalarTower (K := K) (L := L))
    (mem_range_algebraMap_of_fixed_of_isGalois ρB hρB)

/-- `quotientFixedPointIdealPolynomialAlgEquivOfIsGalois` coincides with
`quotientFixedPointIdealPolynomialAlgEquiv`. -/
theorem quotientFixedPointIdealPolynomialAlgEquivOfIsGalois_def
    [Module.Finite A B] [Module.Projective A B]
    {K L : Type*} [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosedIn A K] [IsGalois K L] [Finite Gal(L/K)]
    [FaithfulSMul A K] [FaithfulSMul B L]
    (ρB : Gal(L/K) →* (B ≃ₐ[A] B))
    (hρB : ∀ (σ : Gal(L/K)) (b : B), algebraMap B L (ρB σ b) = σ (algebraMap B L b))
    (hΓ : IsUnit (Nat.card Gal(L/K) : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ σ : Gal(L/K), ρB σ b = b) → b ∈ Set.range (algebraMap A B)) :
    quotientFixedPointIdealPolynomialAlgEquivOfIsGalois ρB hρB hΓ =
      quotientFixedPointIdealPolynomialAlgEquiv ρB hΓ hinj hfix := by
  rw [quotientFixedPointIdealPolynomialAlgEquivOfIsGalois]

/-- The forward direction of `quotientFixedPointIdealPolynomialAlgEquivOfIsGalois` classifies
evaluation at `1 ⊗ₜ X`. -/
theorem homEquiv_quotientFixedPointIdealPolynomialAlgEquivOfIsGalois_comp_mkₐ
    [Module.Finite A B] [Module.Projective A B]
    {K L : Type*} [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosedIn A K] [IsGalois K L] [Finite Gal(L/K)]
    [FaithfulSMul A K] [FaithfulSMul B L]
    (ρB : Gal(L/K) →* (B ≃ₐ[A] B))
    (hρB : ∀ (σ : Gal(L/K)) (b : B), algebraMap B L (ρB σ b) = σ (algebraMap B L b))
    (hΓ : IsUnit (Nat.card Gal(L/K) : A)) :
    homEquiv A B B[X] A[X]
        ((quotientFixedPointIdealPolynomialAlgEquivOfIsGalois ρB hρB hΓ).toAlgHom.comp
          (Ideal.Quotient.mkₐ A
            (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))) =
      Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) :=
  homEquiv_quotientFixedPointIdealPolynomialAlgEquiv_comp_mkₐ ρB hΓ _ _

end TameLine

end TauCeti.Algebra.WeilRestriction
