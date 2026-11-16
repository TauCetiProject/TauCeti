/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.RingTheory.WeilRestriction.Semilinear
import TauCeti.RingTheory.WeilRestriction.Smooth

/-!
# Tame fixed points of Weil restrictions

Let `B` be a finite projective `A`-algebra and `C` a commutative `B`-algebra. An action `ρB` of a
monoid `Γ` on `B` by `A`-algebra automorphisms together with a compatible semilinear action `ρC` on
`C` by ring automorphisms induces an action `WeilRestriction.inducedAction ρB ρC h` of `Γ` on
`WeilRestriction A B C` by `A`-algebra automorphisms.

This file studies the fixed-point quotient of `WeilRestriction A B C` under this induced action.
By the universal properties of the Weil restriction and of `TauCeti.fixedPointIdeal`, the
`T`-points of the fixed-point quotient are canonically the `Γ`-equivariant `B ⊗[A] T`-points of `C`
(`TauCeti.Algebra.WeilRestriction.fixedPointQuotientHomEquiv`). When `Γ` is finite, finite
presentation passes from `C` over `B` to the fixed-point quotient over `A`
(`TauCeti.Algebra.WeilRestriction.finitePresentation_quotient_fixedPointIdeal_inducedAction`). When
`Γ` is a finite group whose order is invertible in `A` and `C` is formally smooth (respectively,
smooth) over `B`, the Weil restriction is formally smooth (respectively, smooth) over `A`, so
Edixhoven's tame fixed-point theorem shows that the fixed-point quotient is formally smooth
(respectively, smooth) over `A`
(`TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdeal_inducedAction` and
`TauCeti.Algebra.WeilRestriction.smooth_quotient_fixedPointIdeal_inducedAction`), over any
commutative ring `A` without Noetherian or Henselian hypotheses.

As a concrete descent calculation, when `B` has `Γ`-invariants equal to `A` (with `A → B`
injective) and `|Γ|` is invertible in `A`, the fixed-point quotient of `WeilRestriction A B B[X]`
for the coefficient action on `B[X]` is canonically isomorphic to `A[X]`
(`TauCeti.Algebra.WeilRestriction.fixedPointQuotientPolynomialEquiv`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientHomEquiv`: `T`-points of the fixed-point
  quotient of `WeilRestriction A B C` are `Γ`-equivariant `B ⊗[A] T`-points of `C`.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientEquivOfTrivial`: for trivial actions on `B`
  and `C`, the fixed-point quotient is `WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.polynomialCoeffAction`: the semilinear action of `Γ` on `B[X]`
  induced by `ρB` on coefficients.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientPolynomialEquiv`: tame Galois descent of the
  affine line, identifying `(Res_{B/A} B[X])^Γ` with `A[X]` when `B^Γ = A`, `A → B` is injective,
  and `|Γ|` is a unit in `A`.

## Main results

* `TauCeti.Algebra.WeilRestriction.fixedPointIdeal_inducedAction_le_ker_iff`: a point of
  `WeilRestriction A B C` kills the fixed-point ideal iff the point of `C` it classifies is
  `Γ`-equivariant.
* `TauCeti.Algebra.WeilRestriction.finitePresentation_quotient_fixedPointIdeal_inducedAction`:
  finite presentation passes to fixed points of a finite monoid action on a Weil restriction.
* `TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdeal_inducedAction` and
  `TauCeti.Algebra.WeilRestriction.smooth_quotient_fixedPointIdeal_inducedAction`: Edixhoven's tame
  fixed-point theorem for Weil restrictions.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4 and
  Propositions 3.1 and 3.4, pp. 292–295.
-/

public noncomputable section

open Algebra Polynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

universe u v w z

section General

variable {A : Type u} {B : Type v} {C : Type w} {Γ : Type z}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
variable [Module.Finite A B] [Module.Projective A B]

section Monoid

variable [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
variable (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- A point `g` of `WeilRestriction A B C` kills the fixed-point ideal of `inducedAction` if and
only if the point of `C` it classifies is `Γ`-equivariant. -/
theorem fixedPointIdeal_inducedAction_le_ker_iff {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    TauCeti.fixedPointIdeal (inducedAction ρB ρC h) ≤ RingHom.ker g ↔
      ∀ (γ : Γ) (c : C), homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  rw [TauCeti.fixedPointIdeal_le_ker_iff]
  exact forall_congr' fun γ ↦ comp_inducedAction_eq_iff ρB ρC h γ g

/-- **Universal property of the fixed-point quotient of a Weil restriction**: `T`-points of
`(Res_{B/A} C)^Γ` are canonically in bijection with `Γ`-equivariant `B ⊗[A] T`-points of `C`. -/
def fixedPointQuotientHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
        y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  (TauCeti.fixedPointQuotientHomEquiv (inducedAction ρB ρC h) T).trans
    { toFun := fun g ↦ ⟨homEquiv A B C T g.1,
        (fixedPointIdeal_inducedAction_le_ker_iff ρB ρC h g.1).mp
          ((TauCeti.fixedPointIdeal_le_ker_iff g.1).mpr g.2)⟩
      invFun := fun y ↦ ⟨(homEquiv A B C T).symm y.1, fun γ ↦ by
        rw [comp_inducedAction_eq_iff, Equiv.apply_symm_apply]
        exact y.2 γ⟩
      left_inv := fun g ↦ Subtype.ext ((homEquiv A B C T).symm_apply_apply g.1)
      right_inv := fun y ↦ Subtype.ext ((homEquiv A B C T).apply_symm_apply y.1) }

/-- The forward direction of `fixedPointQuotientHomEquiv` applies `homEquiv` after precomposing
with the quotient map. -/
@[simp]
theorem fixedPointQuotientHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (q : WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h) →ₐ[A] T) :
    (fixedPointQuotientHomEquiv ρB ρC h T q : C →ₐ[B] B ⊗[A] T) =
      homEquiv A B C T (q.comp (Ideal.Quotient.mkₐ A _)) := by
  simp [fixedPointQuotientHomEquiv]

/-- The inverse of `fixedPointQuotientHomEquiv`, precomposed with the quotient map, is
`(homEquiv A B C T).symm`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_symm_comp_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
      y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    ((fixedPointQuotientHomEquiv ρB ρC h T).symm y).comp (Ideal.Quotient.mkₐ A _) =
      (homEquiv A B C T).symm y.1 := by
  simp [fixedPointQuotientHomEquiv]

/-- For trivial actions on `B` and `C`, the fixed-point ideal of the induced action vanishes. -/
theorem fixedPointIdeal_inducedAction_eq_bot_of_trivial (hB : ρB = 1) (hC : ρC = 1) :
    TauCeti.fixedPointIdeal (inducedAction ρB ρC h) = ⊥ := by
  rw [inducedAction_eq_one ρB ρC h hB hC, TauCeti.fixedPointIdeal_one]

/-- For trivial actions on `B` and `C`, the fixed-point quotient is canonically isomorphic to the
full Weil restriction `WeilRestriction A B C`. -/
def fixedPointQuotientEquivOfTrivial (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h)) ≃ₐ[A]
      WeilRestriction A B C :=
  TauCeti.fixedPointQuotientEquivOfEqOne (inducedAction_eq_one ρB ρC h hB hC)

/-- `fixedPointQuotientEquivOfTrivial` sends a quotient class to its representative. -/
@[simp]
theorem fixedPointQuotientEquivOfTrivial_mk (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    fixedPointQuotientEquivOfTrivial ρB ρC h hB hC (Ideal.Quotient.mk _ x) = x :=
  TauCeti.fixedPointQuotientEquivOfEqOne_mk (inducedAction_eq_one ρB ρC h hB hC) x

/-- The inverse of `fixedPointQuotientEquivOfTrivial` is the quotient map. -/
@[simp]
theorem fixedPointQuotientEquivOfTrivial_symm (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (fixedPointQuotientEquivOfTrivial ρB ρC h hB hC).symm x = Ideal.Quotient.mk _ x :=
  TauCeti.fixedPointQuotientEquivOfEqOne_symm (inducedAction_eq_one ρB ρC h hB hC) x

/-- If `C` is finitely presented over `B` and `Γ` is a finite monoid, then the fixed-point quotient
of `WeilRestriction A B C` is finitely presented over `A`. -/
theorem finitePresentation_quotient_fixedPointIdeal_inducedAction [Finite Γ]
    [FinitePresentation B C] :
    FinitePresentation A
      (WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h)) :=
  TauCeti.finitePresentation_quotient_fixedPointIdeal (inducedAction ρB ρC h)

end Monoid

section Smoothness

variable [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
variable (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions**: if `C` is formally smooth over
`B` and `Γ` is a finite group whose order is invertible in `A`, then the fixed-point quotient of
`WeilRestriction A B C` is formally smooth over `A`. -/
theorem formallySmooth_quotient_fixedPointIdeal_inducedAction [FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A
      (WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h)) :=
  TauCeti.formallySmooth_quotient_fixedPointIdeal (inducedAction ρB ρC h) hΓ

/-- **Edixhoven's tame fixed-point theorem for Weil restrictions** (Edixhoven, Props. 3.1 and 3.4):
if `C` is smooth over `B` and `Γ` is a finite group whose order is invertible in `A`, then the
fixed-point quotient of `WeilRestriction A B C` is smooth over `A`, over any base ring `A`. -/
theorem smooth_quotient_fixedPointIdeal_inducedAction [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A
      (WeilRestriction A B C ⧸ TauCeti.fixedPointIdeal (inducedAction ρB ρC h)) :=
  TauCeti.smooth_quotient_fixedPointIdeal (inducedAction ρB ρC h) hΓ

end Smoothness

end General

section PolynomialCoeffAction

variable {A : Type u} {B : Type v} {Γ : Type z}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- The semilinear coefficient action of a monoid `Γ` on `B[X]` induced by an action `ρB` on `B`.
-/
def polynomialCoeffAction [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) : Γ →* RingAut B[X] where
  toFun γ := Polynomial.mapEquiv (ρB γ).toRingEquiv
  map_one' := by
    ext p
    simp [Polynomial.mapEquiv_apply]
  map_mul' γ δ := by
    ext p
    simp [Polynomial.mapEquiv_apply, Polynomial.map_map]

/-- `polynomialCoeffAction ρB γ` acts on `B[X]` by mapping coefficients through `ρB γ`. -/
@[simp]
theorem polynomialCoeffAction_apply [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (p : B[X]) :
    polynomialCoeffAction ρB γ p = p.map (ρB γ : B →+* B) :=
  (rfl)

/-- The coefficient action on `B[X]` is semilinear over `ρB`. -/
theorem polynomialCoeffAction_algebraMap [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialCoeffAction ρB γ (algebraMap B B[X] b) = algebraMap B B[X] (ρB γ b) := by
  simp

end PolynomialCoeffAction

section AffineLine

variable {A : Type u} {B : Type v} {Γ : Type z}
variable [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B]

/-- **Tame Galois descent of the affine line.** Let `B` be a finite projective `A`-algebra with
an action `ρB` of a finite group `Γ` of order invertible in `A`. If `A → B` is injective and its
image is the fixed subalgebra of `B`, then the fixed-point quotient of `WeilRestriction A B B[X]`
under the coefficient action is canonically isomorphic to `A[X]`. -/
def fixedPointQuotientPolynomialEquiv [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (hΓ : IsUnit (Nat.card Γ : A))
    (hinv : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (hinj : Function.Injective (algebraMap A B)) :
    (WeilRestriction A B B[X] ⧸
      TauCeti.fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB)
        (polynomialCoeffAction_algebraMap ρB))) ≃ₐ[A] A[X] :=
  let Q := WeilRestriction A B B[X] ⧸
    TauCeti.fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB)
      (polynomialCoeffAction_algebraMap ρB))
  -- Forward map `Q →ₐ[A] A[X]` classifying `X ↦ 1 ⊗ X`.
  let toFun : Q →ₐ[A] A[X] :=
    (fixedPointQuotientHomEquiv ρB (polynomialCoeffAction ρB)
      (polynomialCoeffAction_algebraMap ρB) A[X]).symm
      ⟨Polynomial.aeval ((1 : B) ⊗ₜ[A] (Polynomial.X : A[X])), fun γ p ↦ by
        let lhs : B[X] →+* B ⊗[A] A[X] :=
          (Polynomial.aeval (R := B) ((1 : B) ⊗ₜ[A] (Polynomial.X : A[X]))).toRingHom.comp
            (polynomialCoeffAction ρB γ : B[X] →+* B[X])
        let rhs : B[X] →+* B ⊗[A] A[X] :=
          (Algebra.TensorProduct.rTensor A[X] (ρB γ : B →ₐ[A] B)).toRingHom.comp
            (Polynomial.aeval (R := B) ((1 : B) ⊗ₜ[A] (Polynomial.X : A[X]))).toRingHom
        have heq : lhs = rhs := by
          apply Polynomial.ringHom_ext'
          · ext b
            simp [lhs, rhs, Algebra.TensorProduct.algebraMap_apply]
          · simp [lhs, rhs]
        exact RingHom.congr_fun heq p⟩
  -- Backward map `A[X] →ₐ[A] Q` sending `X` to the descended universal coordinate.
  let uBar := fixedPointQuotientHomEquiv ρB (polynomialCoeffAction ρB)
    (polynomialCoeffAction_algebraMap ρB) Q (AlgHom.id A Q)
  let xBar : Q := TauCeti.reynoldsRetractionTensor ρB hΓ hinv hinj Q (uBar.1 Polynomial.X)
  have hxBar : (1 : B) ⊗ₜ[A] xBar = uBar.1 Polynomial.X := by
    refine TauCeti.one_tmul_reynoldsRetractionTensor_of_fixed ρB hΓ hinv hinj fun γ ↦ ?_
    have hrTensor : ∀ t : B ⊗[A] Q,
        LinearMap.rTensor Q (ρB γ).toLinearMap t =
          Algebra.TensorProduct.rTensor Q (ρB γ : B →ₐ[A] B) t := by
      intro t
      induction t with
      | tmul b q => simp
      | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]
    rw [hrTensor]
    have hX := uBar.2 γ Polynomial.X
    simpa only [polynomialCoeffAction_apply, Polynomial.map_X] using hX.symm
  let invFun : A[X] →ₐ[A] Q := Polynomial.aeval xBar
  AlgEquiv.ofAlgHom toFun invFun
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply, invFun, Polynomial.aeval_X]
      have hnat : Algebra.TensorProduct.lTensor (S := B) B toFun (uBar.1 Polynomial.X) =
          (1 : B) ⊗ₜ[A] (Polynomial.X : A[X]) := by
        have hu : uBar.1 = homEquiv A B B[X] Q (Ideal.Quotient.mkₐ A _) := by
          dsimp only [uBar]
          rw [fixedPointQuotientHomEquiv_apply, AlgHom.id_comp]
        rw [hu, ← AlgHom.comp_apply, ← homEquiv_comp]
        have hcomp : toFun.comp (Ideal.Quotient.mkₐ A _) =
            (homEquiv A B B[X] A[X]).symm
              (Polynomial.aeval ((1 : B) ⊗ₜ[A] (Polynomial.X : A[X]))) :=
          fixedPointQuotientHomEquiv_symm_comp_mk _ _ _ _
        rw [hcomp, Equiv.apply_symm_apply, Polynomial.aeval_X]
      have htmul : (1 : B) ⊗ₜ[A] (toFun xBar) = (1 : B) ⊗ₜ[A] (Polynomial.X : A[X]) := by
        simpa [← hxBar] using hnat
      simpa using congrArg (TauCeti.reynoldsRetractionTensor ρB hΓ hinv hinj A[X]) htmul)
    (by
      apply (fixedPointQuotientHomEquiv ρB (polynomialCoeffAction ρB)
        (polynomialCoeffAction_algebraMap ρB) Q).injective
      apply Subtype.ext
      apply Polynomial.algHom_ext
      simp only [fixedPointQuotientHomEquiv_apply, AlgHom.comp_assoc]
      rw [fixedPointQuotientHomEquiv_symm_comp_mk, homEquiv_comp, AlgHom.comp_apply,
        Equiv.apply_symm_apply, Polynomial.aeval_X, AlgHom.id_comp]
      have hu : homEquiv A B B[X] Q (Ideal.Quotient.mkₐ A _) = uBar.1 := by
        dsimp only [uBar]
        rw [fixedPointQuotientHomEquiv_apply, AlgHom.id_comp]
      rw [hu, ← hxBar]
      simp [invFun])

/-- The forward map of `fixedPointQuotientPolynomialEquiv`, precomposed with the quotient map,
classifies the `B ⊗[A] A[X]`-point `X ↦ 1 ⊗ X` of `B[X]`. -/
@[simp]
theorem fixedPointQuotientPolynomialEquiv_comp_mk [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinv : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (hinj : Function.Injective (algebraMap A B)) :
    (fixedPointQuotientPolynomialEquiv ρB hΓ hinv hinj).toAlgHom.comp
        (Ideal.Quotient.mkₐ A _) =
      (homEquiv A B B[X] A[X]).symm
        (Polynomial.aeval ((1 : B) ⊗ₜ[A] (Polynomial.X : A[X]))) := by
  refine AlgHom.ext fun x ↦ ?_
  simpa only [fixedPointQuotientPolynomialEquiv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.ofAlgHom_apply] using
    AlgHom.congr_fun (fixedPointQuotientHomEquiv_symm_comp_mk ρB (polynomialCoeffAction ρB)
      (polynomialCoeffAction_algebraMap ρB) _) x

/-- The inverse of `fixedPointQuotientPolynomialEquiv` maps `X : A[X]` to the element whose
tensor image `1 ⊗ x` is the universal coordinate of `WeilRestriction A B B[X] ⧸ I`. -/
theorem homEquiv_comp_fixedPointQuotientPolynomialEquiv_symm_X [Group Γ] [Finite Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinv : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (hinj : Function.Injective (algebraMap A B)) :
    (1 : B) ⊗ₜ[A]
        ((fixedPointQuotientPolynomialEquiv ρB hΓ hinv hinj).symm (Polynomial.X : A[X])) =
      homEquiv A B B[X] _ (Ideal.Quotient.mkₐ A _) Polynomial.X := by
  have hto := fixedPointQuotientPolynomialEquiv_comp_mk ρB hΓ hinv hinj
  have hback : homEquiv A B B[X] _
      ((fixedPointQuotientPolynomialEquiv ρB hΓ hinv hinj).symm.toAlgHom.comp
        ((fixedPointQuotientPolynomialEquiv ρB hΓ hinv hinj).toAlgHom.comp
          (Ideal.Quotient.mkₐ A _))) Polynomial.X =
      homEquiv A B B[X] _ (Ideal.Quotient.mkₐ A _) Polynomial.X := by
    rw [← AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.id_comp]
  rw [← hback, hto, homEquiv_comp, AlgHom.comp_apply, Equiv.apply_symm_apply,
    Polynomial.aeval_X]
  simp

end AffineLine

end TauCeti.Algebra.WeilRestriction
