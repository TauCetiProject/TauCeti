/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import TauCeti.RingTheory.Invariant.FixedPointIdeal
public import TauCeti.RingTheory.Invariant.Galois
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth
import TauCeti.RingTheory.Invariant.ModuleDescent

/-!
# Edixhoven's tame fixed-point theorem for Weil restrictions

Let `B` be a finite projective `A`-algebra, let `C` be a finitely presented `B`-algebra, and let a
monoid `Γ` act on `B` by `A`-algebra automorphisms (`ρB`) and semilinearly on `C` by ring
automorphisms (`ρC`). By `WeilRestriction.inducedAction`, `Γ` acts on `WeilRestriction A B C` by
`A`-algebra automorphisms.

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
  (`WeilRestriction.smooth_fixedPoints`), with no henselian or discrete-valuation-ring hypothesis on
  the base.
* **Trivial action and tame affine line.** A trivial action fixes the entire Weil restriction
  (`WeilRestriction.fixedPointIdeal_eq_bot_of_eq_one`,
  `WeilRestriction.quotientFixedPointIdealAlgEquivOfEqOne`). For `C = B[X]` with `Γ` acting on
  coefficients, when `#Γ` is invertible in `A`, `algebraMap A B` is injective, and the
  `Γ`-invariants of `B` come from `A` (in particular, for a tame Galois extension of integrally
  closed domains such as discrete valuation rings), `(#Γ)⁻¹` has trace `1`, so
  `TauCeti.MulSemiringAction.invariantsBaseChangeEquiv` identifies `(B ⊗[A] T)^Γ` with `T` and
  yields the `A`-algebra isomorphism `(WeilRestriction A B B[X] ⧸ fixedPointIdeal ...) ≃ₐ[A] A[X]`
  (`WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv`,
  `WeilRestriction.quotientFixedPointIdealPolynomialAlgEquivOfIsGalois`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.inducedMulSemiringAction`: the `MulSemiringAction` of `Γ` on
  `WeilRestriction A B C` attached to `(ρB, ρC, h)`.
* `TauCeti.Algebra.WeilRestriction.fixedPointIdeal`: the fixed-point ideal of the induced `Γ`-action
  on `WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.fixedPointsHomEquiv`: the universal bijection between points of
  the fixed-point quotient and `Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.polynomialAction`: the semilinear coefficient action of `Γ` on
  `B[X]`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv`: the isomorphism
  `(Res_{B/A} 𝔸¹_B)^Γ ≃ₐ[A] 𝔸¹_A` for a tame invariant extension `A → B`.

## Main results

* `TauCeti.Algebra.WeilRestriction.smooth_fixedPoints`: Edixhoven's theorem that `(Res_{B/A} X)^Γ`
  is smooth over `A` when `X` is smooth affine over `B` and `#Γ` is invertible in `A`.
* `TauCeti.Algebra.WeilRestriction.instMulSemiringAction` and
  `TauCeti.Algebra.WeilRestriction.instSMulCommClass`: typeclass instances equipping
  `WeilRestriction A B C` with the induced `Γ`-action for `[Group Γ]` and
  `[SMulDistribClass Γ B C]`.

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

/-- The `MulSemiringAction` of `Γ` on `WeilRestriction A B C` induced by an action `ρB` on `B` by
`A`-algebra automorphisms and a `ρB`-semilinear action `ρC` on `C` by ring automorphisms. -/
abbrev inducedMulSemiringAction : _root_.MulSemiringAction Γ (WeilRestriction A B C) :=
  _root_.MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)

/-- Scalar multiplication in `inducedMulSemiringAction` commutes with the `A`-algebra structure. -/
theorem inducedSMulCommClass :
    letI := inducedMulSemiringAction ρB ρC h
    SMulCommClass Γ A (WeilRestriction A B C) := by
  let _ := inducedMulSemiringAction ρB ρC h
  refine ⟨fun γ a x ↦ ?_⟩
  exact map_smul (inducedAction ρB ρC h γ) a x

/-- The **fixed-point ideal** of the `Γ`-action on `WeilRestriction A B C` induced by `(ρB, ρC, h)`:
the ideal cutting out the closed subscheme `(Res_{B/A} Spec C)^Γ`. -/
def fixedPointIdeal : Ideal (WeilRestriction A B C) :=
  letI := inducedMulSemiringAction ρB ρC h
  TauCeti.MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)

/-- Explicit span description of `WeilRestriction.fixedPointIdeal`. -/
theorem fixedPointIdeal_def :
    fixedPointIdeal ρB ρC h =
      Ideal.span {x : WeilRestriction A B C | ∃ γ y, inducedAction ρB ρC h γ y - y = x} := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_def]
  rfl

/-- Every displacement `inducedAction ρB ρC h γ x - x` lies in `fixedPointIdeal ρB ρC h`. -/
theorem sub_mem_fixedPointIdeal (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x - x ∈ fixedPointIdeal ρB ρC h := by
  let _ := inducedMulSemiringAction ρB ρC h
  exact TauCeti.MulSemiringAction.smul_sub_mem_fixedPointIdeal γ x

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
    AlgHom.ext fun _ ↦ rfl
  rw [hto, comp_inducedAction_eq_iff]

/-- **Universal property of `(Res_{B/A} Spec C)^Γ`** (Edixhoven, Proposition 3.1): `A`-algebra
homomorphisms out of `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` into `T` correspond
bijectively to `Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointsHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T //
        ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} where
  toFun g :=
    ⟨homEquiv A B C T (g.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))),
      (fixedPointIdeal_le_ker_iff ρB ρC h _).mp fun x hx ↦ by
        rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun y :=
    Ideal.Quotient.liftₐ (fixedPointIdeal ρB ρC h) ((homEquiv A B C T).symm y.1) fun x hx ↦
      RingHom.mem_ker.mp <|
        ((fixedPointIdeal_le_ker_iff ρB ρC h ((homEquiv A B C T).symm y.1)).mpr
          (by simpa only [Equiv.apply_symm_apply] using y.2)) hx
  left_inv g := Ideal.Quotient.algHom_ext A <| by
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_apply]
  right_inv y := Subtype.ext <| by
    dsimp only
    rw [Ideal.Quotient.liftₐ_comp, Equiv.apply_symm_apply]

/-- Forward direction of `fixedPointsHomEquiv`. -/
@[simp]
theorem fixedPointsHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h →ₐ[A] T) :
    (fixedPointsHomEquiv ρB ρC h T g).1 =
      homEquiv A B C T (g.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) :=
  (rfl)

/-- Inverse direction of `fixedPointsHomEquiv` evaluated on a quotient class. -/
@[simp]
theorem fixedPointsHomEquiv_symm_apply_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T //
      ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)})
    (x : WeilRestriction A B C) :
    (fixedPointsHomEquiv ρB ρC h T).symm y (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) =
      (homEquiv A B C T).symm y.1 x :=
  (rfl)

/-- Classifying the composite of `Ideal.Quotient.mkₐ` with `(fixedPointsHomEquiv ...).symm y`
recovers `y`. -/
theorem homEquiv_comp_fixedPointsHomEquiv_symm {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T //
      ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    homEquiv A B C T
        (((fixedPointsHomEquiv ρB ρC h T).symm y).comp
          (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) = y.1 := by
  have := (fixedPointsHomEquiv ρB ρC h T).apply_symm_apply y
  exact congrArg Subtype.val this

/-- **Trivial action fixes all of `Res_{B/A} Spec C`**: if `Γ` acts trivially on `B` and on `C`,
then `fixedPointIdeal ρB ρC h = ⊥`. -/
theorem fixedPointIdeal_eq_bot_of_eq_one (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdeal ρB ρC h = ⊥ := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_eq_bot_iff]
  intro γ x
  rw [MulAction.compHom_smul_def, inducedAction_eq_one ρB ρC h hB hC, MonoidHom.one_apply,
    one_smul]

/-- For a trivial action on `B` and on `C`, the fixed-point quotient is canonically isomorphic to
`WeilRestriction A B C` itself. -/
def quotientFixedPointIdealAlgEquivOfEqOne (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointIdeal_eq_bot_of_eq_one ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-! ### Finite generation, finite presentation, and Edixhoven's smoothness theorem -/

/-- When `Γ` is finite, `WeilRestriction.fixedPointIdeal` is finitely generated. -/
theorem fixedPointIdeal_fg [Finite Γ] : (fixedPointIdeal ρB ρC h).FG := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact TauCeti.MulSemiringAction.fixedPointIdeal_fg (R := A)

/-- When `Γ` is finite, the fixed-point quotient of `WeilRestriction A B C` is finitely presented
over `A`. -/
theorem finitePresentation_quotient_fixedPointIdeal [Finite Γ] :
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

end InducedAction

/-! ### Typeclass instances for semilinear group actions -/

section TypeclassAction

variable {A B C Γ : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  [Group Γ] [_root_.MulSemiringAction Γ B] [SMulCommClass Γ A B]
  [_root_.MulSemiringAction Γ C] [SMulDistribClass Γ B C]

/-- A group `Γ` acting on `B` by `A`-algebra automorphisms and semilinearly on `C`
(`[SMulDistribClass Γ B C]`) acts on `WeilRestriction A B C` by `A`-algebra automorphisms. -/
instance instMulSemiringAction : _root_.MulSemiringAction Γ (WeilRestriction A B C) :=
  inducedMulSemiringAction (_root_.MulSemiringAction.toAlgAut Γ A B)
    (_root_.MulSemiringAction.toRingAut Γ C) fun γ b ↦ (algebraMap.smul' γ b C).symm

/-- The induced `Γ`-action on `WeilRestriction A B C` commutes with the `A`-algebra structure. -/
instance instSMulCommClass : SMulCommClass Γ A (WeilRestriction A B C) :=
  inducedSMulCommClass (_root_.MulSemiringAction.toAlgAut Γ A B)
    (_root_.MulSemiringAction.toRingAut Γ C) fun γ b ↦ (algebraMap.smul' γ b C).symm

/-- Explicit formula for the `Γ`-action on `WeilRestriction A B C` via `semilinearMap`. -/
theorem smul_def (γ : Γ) (x : WeilRestriction A B C) :
    γ • x = semilinearMap (_root_.MulSemiringAction.toAlgAut Γ A B γ)
      (_root_.MulSemiringAction.toRingAut Γ C γ : C →+* C)
      (fun b ↦ (algebraMap.smul' γ b C).symm) x :=
  inducedAction_apply _ _ _ γ x

end TypeclassAction

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

/-- `polynomialAction` transforms constant polynomials via `ρB`. -/
@[simp]
theorem polynomialAction_C {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialAction ρB γ (Polynomial.C b) = Polynomial.C (ρB γ b) := by
  simp [polynomialAction]

/-- `polynomialAction` fixes the indeterminate `X`. -/
@[simp]
theorem polynomialAction_X {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) :
    polynomialAction ρB γ Polynomial.X = Polynomial.X := by
  simp [polynomialAction]

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
  induction f using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => rw [map_add, map_add, map_add, map_add, hp₁, hp₂]
  | monomial n b =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, polynomialAction_C,
      polynomialAction_X, map_mul, map_pow, map_mul, map_pow, map_mul, map_pow]
    simp only [Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, map_one]

section Retraction

variable {Γ : Type*} [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B))

/-- Tame base-change invariants equivalence `T ≃ (B ⊗[A] T)^Γ` sending `t ↦ 1 ⊗ₜ t`, obtained from
`TauCeti.MulSemiringAction.invariantsBaseChangeEquiv` applied to the trace-`1` element `(#Γ)⁻¹`. -/
private def tameInvariantsEquiv (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (T : Type*) [CommRing T] [Algebra A T] :
    T ≃ {z : B ⊗[A] T //
      ∀ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z = z} :=
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Invertible (Nat.card Γ : A) := hΓ.nonempty_invertible.some
  let ρBring : Γ →* RingAut B :=
    { toFun γ := (ρB γ).toRingEquiv
      map_one' := by ext; simp
      map_mul' γ δ := by ext; simp }
  letI : _root_.MulSemiringAction Γ B := _root_.MulSemiringAction.compHom B ρBring
  letI : SMulCommClass Γ A B := ⟨fun γ a b ↦ map_smul (ρB γ) a b⟩
  letI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  letI : _root_.Algebra.IsInvariant A B Γ := ⟨hfix⟩
  have hc : ∃ c : B, ∑ γ : Γ, γ • c = 1 :=
    ⟨algebraMap A B ⅟(Nat.card Γ : A), by
      have hsmul (γ : Γ) :
          γ • algebraMap A B ⅟(Nat.card Γ : A) = algebraMap A B ⅟(Nat.card Γ : A) :=
        AlgEquiv.commutes (ρB γ) _
      simp only [hsmul, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul A, smul_eq_mul, mul_invOf_self, map_one]⟩
  have hsmul_rTensor (γ : Γ) (z : B ⊗[A] T) :
      γ • z = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b t => rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  (TauCeti.MulSemiringAction.invariantsBaseChangeEquiv A B Γ T hc).toEquiv.trans
    (Equiv.subtypeEquivRight fun z ↦ by
      rw [Representation.mem_invariants]
      refine forall_congr' fun γ ↦ ?_
      simp [hsmul_rTensor])

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

/-- **Tame fixed-point scheme of `Res_{B/A} 𝔸¹_B`**: when `#Γ` is invertible in `A`,
`algebraMap A B` is injective, and every `Γ`-invariant element of `B` lies in the image of `A`, the
fixed-point quotient of `WeilRestriction A B B[X]` under the coefficient action of `Γ` is
isomorphic as an `A`-algebra to `A[X]`. -/
def quotientFixedPointIdealPolynomialAlgEquiv [Module.Finite A B] [Module.Projective A B]
    (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)) ≃ₐ[A] A[X] :=
  let I := fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)
  let q : WeilRestriction A B B[X] →ₐ[A] WeilRestriction A B B[X] ⧸ I := Ideal.Quotient.mkₐ A I
  let y₀ : B[X] →ₐ[B] B ⊗[A] A[X] := Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X])
  let ψ : (WeilRestriction A B B[X] ⧸ I) →ₐ[A] A[X] :=
    (fixedPointsHomEquiv ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB) A[X]).symm
      ⟨y₀, aeval_one_tmul_X_polynomialAction ρB⟩
  let u := homEquiv A B B[X] (WeilRestriction A B B[X] ⧸ I) q
  let hu : ∀ γ : Γ,
      Algebra.TensorProduct.rTensor _ (ρB γ : B →ₐ[A] B) (u Polynomial.X) = u Polynomial.X :=
    fun γ ↦ by
      have hq := (fixedPointIdeal_le_ker_iff ρB (polynomialAction ρB)
        (polynomialAction_algebraMap ρB) q).mp (Ideal.Quotient.mkₐ_ker A I).ge γ Polynomial.X
      simpa only [u, polynomialAction_X] using hq.symm
  let x₀ : WeilRestriction A B B[X] ⧸ I :=
    (tameInvariantsEquiv ρB hΓ hinj hfix (WeilRestriction A B B[X] ⧸ I)).symm ⟨u Polynomial.X, hu⟩
  AlgEquiv.ofAlgHom ψ (Polynomial.aeval x₀)
    (by
      have hx₀ : Algebra.TensorProduct.includeRight (R := A) (A := B) x₀ = u Polynomial.X :=
        includeRight_tameInvariantsEquiv_symm ρB hΓ hinj hfix _ ⟨u Polynomial.X, hu⟩
      have hψ_comp : homEquiv A B B[X] A[X] (ψ.comp q) = y₀ :=
        homEquiv_comp_fixedPointsHomEquiv_symm ρB (polynomialAction ρB)
          (polynomialAction_algebraMap ρB) ⟨y₀, aeval_one_tmul_X_polynomialAction ρB⟩
      refine Polynomial.algHom_ext ?_
      rw [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X]
      refine (tameInvariantsEquiv ρB hΓ hinj hfix A[X]).injective (Subtype.ext ?_)
      rw [tameInvariantsEquiv_apply_val, tameInvariantsEquiv_apply_val]
      calc
        Algebra.TensorProduct.includeRight (R := A) (A := B) (ψ x₀)
            = Algebra.TensorProduct.lTensor (S := B) B ψ
                (Algebra.TensorProduct.includeRight (R := A) (A := B) x₀) := by simp
        _ = Algebra.TensorProduct.lTensor (S := B) B ψ (u Polynomial.X) := by rw [hx₀]
        _ = homEquiv A B B[X] A[X] (ψ.comp q) Polynomial.X := by
              rw [homEquiv_comp, AlgHom.comp_apply]
        _ = y₀ Polynomial.X := by rw [hψ_comp]
        _ = Algebra.TensorProduct.includeRight (R := A) (A := B) Polynomial.X := by simp [y₀])
    (by
      have hx₀ : Algebra.TensorProduct.includeRight (R := A) (A := B) x₀ = u Polynomial.X :=
        includeRight_tameInvariantsEquiv_symm ρB hΓ hinj hfix _ ⟨u Polynomial.X, hu⟩
      have hψ_comp : homEquiv A B B[X] A[X] (ψ.comp q) = y₀ :=
        homEquiv_comp_fixedPointsHomEquiv_symm ρB (polynomialAction ρB)
          (polynomialAction_algebraMap ρB) ⟨y₀, aeval_one_tmul_X_polynomialAction ρB⟩
      refine Ideal.Quotient.algHom_ext A ?_
      apply (homEquiv A B B[X] (WeilRestriction A B B[X] ⧸ I)).injective
      refine Polynomial.algHom_ext' (by ext) ?_
      rw [AlgHom.comp_assoc, homEquiv_comp, AlgHom.comp_apply, hψ_comp]
      simp only [y₀, Polynomial.aeval_X, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Polynomial.aeval_X, AlgHom.id_comp]
      exact hx₀)

/-- The forward direction of `quotientFixedPointIdealPolynomialAlgEquiv` classifies evaluation at
`1 ⊗ₜ X`. -/
theorem homEquiv_quotientFixedPointIdealPolynomialAlgEquiv_comp_mkₐ
    [Module.Finite A B] [Module.Projective A B]
    (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    homEquiv A B B[X] A[X]
        ((quotientFixedPointIdealPolynomialAlgEquiv ρB hΓ hinj hfix).toAlgHom.comp
          (Ideal.Quotient.mkₐ A
            (fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)))) =
      Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X : B ⊗[A] A[X]) :=
  homEquiv_comp_fixedPointsHomEquiv_symm ρB (polynomialAction ρB)
    (polynomialAction_algebraMap ρB) ⟨_, aeval_one_tmul_X_polynomialAction ρB⟩

end Retraction

/-- **Tame fixed-point scheme of `Res_{B/A} 𝔸¹_B` for a Galois extension of integrally closed
domains** (such as a tamely ramified Galois extension of discrete valuation rings): when `A` is
integrally closed in `K`, `L / K` is Galois, `B` is an `A`-finite-projective integral `A`-algebra
inside `L` stabilized by `Gal(L/K)` via `ρB`, and `#Gal(L/K)` is invertible in `A`, the fixed-point
scheme `(Res_{B/A} 𝔸¹_B)^{Gal(L/K)}` is `𝔸¹_A`. -/
def quotientFixedPointIdealPolynomialAlgEquivOfIsGalois [Module.Finite A B] [Module.Projective A B]
    {K L : Type*} [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosedIn A K] [IsGalois K L] [Finite Gal(L/K)]
    [Algebra.IsIntegral A B] [FaithfulSMul A K] [FaithfulSMul B L]
    (ρB : Gal(L/K) →* (B ≃ₐ[A] B))
    (hρB : ∀ (σ : Gal(L/K)) (b : B), algebraMap B L (ρB σ b) = σ (algebraMap B L b))
    (hΓ : IsUnit (Nat.card Gal(L/K) : A)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdeal ρB (polynomialAction ρB) (polynomialAction_algebraMap ρB)) ≃ₐ[A] A[X] :=
  quotientFixedPointIdealPolynomialAlgEquiv ρB hΓ
    (fun a₁ a₂ h ↦ FaithfulSMul.algebraMap_injective A K <|
      FaithfulSMul.algebraMap_injective K L <| by
        rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L,
          IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L, h])
    (fun b hb ↦ by
      have hint : IsIntegral A (algebraMap B L b) :=
        IsIntegral.map (IsScalarTower.toAlgHom A B L) (Algebra.IsIntegral.isIntegral b)
      have hfixL (σ : Gal(L/K)) : σ (algebraMap B L b) = algebraMap B L b := by
        rw [← hρB, hb]
      obtain ⟨a, ha⟩ := (TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed K
        (algebraMap B L b)).mpr ⟨hint, hfixL⟩
      refine ⟨a, FaithfulSMul.algebraMap_injective B L ?_⟩
      rwa [← IsScalarTower.algebraMap_apply A B L])

end TameLine

end TauCeti.Algebra.WeilRestriction
