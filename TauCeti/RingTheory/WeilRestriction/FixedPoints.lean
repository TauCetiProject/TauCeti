/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import TauCeti.RingTheory.Invariant.Coinvariant
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth
import TauCeti.RingTheory.Invariant.ModuleDescent

/-!
# Fixed-point subschemes of Weil restrictions and Edixhoven's smoothness theorem

Let `B` be a finite projective `A`-algebra and `C` a finitely presented `B`-algebra, with a monoid
`Γ` acting on `B` via `ρB : Γ →* (B ≃ₐ[A] B)` and on `C` via `ρC : Γ →* RingAut C` semilinearly
over `ρB`. Through `inducedAction ρB ρC h`, `Γ` acts on `WeilRestriction A B C` by `A`-algebra
automorphisms. This file constructs the coordinate algebra `fixedCoordinateRing ρB ρC h` of
`(Res_{B/A} Spec C)^Γ`, cut out by `fixedIdeal ρB ρC h`, and proves its universal property, finite
presentation for finite `Γ`, and Edixhoven's smoothness theorem when `|Γ|` is invertible in `A`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.fixedIdeal`, `fixedCoordinateRing`, `mkFixed`, `fixedHomEquiv`:
  displacement ideal, coordinate `A`-algebra, quotient map, and universal property classifying
  `T`-points of `(Res_{B/A} Spec C)^Γ` by `Γ`-equivariant `(B ⊗[A] T)`-points of `Spec C`.
* `TauCeti.Algebra.WeilRestriction.instFinitePresentationFixedCoordinateRing`,
  `formallySmooth_fixedPoints`, `smooth_fixedPoints`: finite presentation for finite `Γ` and
  Edixhoven's smoothness theorem when `|Γ| ∈ Aˣ`.
* `TauCeti.Algebra.WeilRestriction.fixedCoordinateRingEquivOfEqOne` and
  `fixedCoordinateRingPolynomialEquiv`: trivial-action isomorphism and `(Res_{B/A} 𝔸¹_B)^Γ ≃ 𝔸¹_A`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
-/

public noncomputable section

open Algebra TensorProduct Polynomial

namespace TauCeti.Algebra.WeilRestriction

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The **fixed-point ideal** of `inducedAction ρB ρC h` in `WeilRestriction A B C`, cutting out
`(Res_{B/A} Spec C)^Γ`. -/
def fixedIdeal : Ideal (WeilRestriction A B C) :=
  letI := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  TauCeti.coinvariantIdeal Γ (WeilRestriction A B C)

/-- Explicit supremum-of-spans presentation of `fixedIdeal ρB ρC h`. -/
theorem fixedIdeal_def :
    fixedIdeal ρB ρC h = ⨆ γ : Γ,
      Ideal.span (Set.range fun x : WeilRestriction A B C ↦ inducedAction ρB ρC h γ x - x) := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  exact TauCeti.coinvariantIdeal_eq_iSup Γ (WeilRestriction A B C)

/-- Every displacement `inducedAction ρB ρC h γ x - x` lies in `fixedIdeal ρB ρC h`. -/
@[grind ←]
theorem sub_mem_fixedIdeal (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x - x ∈ fixedIdeal ρB ρC h := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  exact TauCeti.sub_mem_coinvariantIdeal γ x

/-- `fixedIdeal ρB ρC h` is the smallest ideal containing every displacement of `inducedAction`. -/
@[simp]
theorem fixedIdeal_le_iff {J : Ideal (WeilRestriction A B C)} :
    fixedIdeal ρB ρC h ≤ J ↔
      ∀ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x ∈ J := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  exact TauCeti.coinvariantIdeal_le_iff

private theorem forall_inducedAction_eq_iff_equivariant {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    (∀ (γ : Γ) (x : WeilRestriction A B C), g (inducedAction ρB ρC h γ x) = g x) ↔
      ∀ (γ : Γ) (c : C), homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  let _ : SMulCommClass Γ A (WeilRestriction A B C) :=
    SMul.comp.smulCommClass (inducedAction ρB ρC h)
  exact g.forall_smul_eq_iff_comp_toAlgHom.trans <|
    forall_congr' fun γ ↦ comp_inducedAction_eq_iff ρB ρC h γ g

/-- An `A`-algebra map `g : WeilRestriction A B C →ₐ[A] T` kills `fixedIdeal ρB ρC h` iff
`homEquiv A B C T g` is `Γ`-equivariant. -/
theorem fixedIdeal_le_ker_iff {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    fixedIdeal ρB ρC h ≤ RingHom.ker g.toRingHom ↔
      ∀ (γ : Γ) (c : C), homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  exact (TauCeti.coinvariantIdeal_le_ker_iff g.toRingHom).trans
    (forall_inducedAction_eq_iff_equivariant ρB ρC h g)

/-- The **coordinate `A`-algebra of `(Res_{B/A} Spec C)^Γ`**. -/
abbrev fixedCoordinateRing : Type _ :=
  WeilRestriction A B C ⧸ fixedIdeal ρB ρC h

/-- The canonical surjective `A`-algebra quotient map onto `fixedCoordinateRing ρB ρC h`. -/
def mkFixed : WeilRestriction A B C →ₐ[A] fixedCoordinateRing ρB ρC h :=
  Ideal.Quotient.mkₐ A (fixedIdeal ρB ρC h)

/-- `mkFixed ρB ρC h` is `Ideal.Quotient.mkₐ A (fixedIdeal ρB ρC h)`. -/
theorem mkFixed_def : mkFixed ρB ρC h = Ideal.Quotient.mkₐ A (fixedIdeal ρB ρC h) := by rfl

/-- The kernel of `mkFixed ρB ρC h` is `fixedIdeal ρB ρC h`. -/
@[simp]
theorem ker_mkFixed : RingHom.ker (mkFixed ρB ρC h) = fixedIdeal ρB ρC h :=
  Ideal.mk_ker

/-- An element maps to `0` under `mkFixed ρB ρC h` iff it lies in `fixedIdeal ρB ρC h`. -/
@[simp]
theorem mkFixed_eq_zero_iff {x : WeilRestriction A B C} :
    mkFixed ρB ρC h x = 0 ↔ x ∈ fixedIdeal ρB ρC h :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The quotient map `mkFixed ρB ρC h` is surjective. -/
theorem mkFixed_surjective : Function.Surjective (mkFixed ρB ρC h) :=
  Ideal.Quotient.mkₐ_surjective A (fixedIdeal ρB ρC h)

/-- `mkFixed ρB ρC h` equalizes every `inducedAction ρB ρC h γ` with the identity. -/
theorem mkFixed_inducedAction_apply (γ : Γ) (x : WeilRestriction A B C) :
    mkFixed ρB ρC h (inducedAction ρB ρC h γ x) = mkFixed ρB ρC h x := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  let _ : SMulCommClass Γ A (WeilRestriction A B C) :=
    SMul.comp.smulCommClass (inducedAction ρB ρC h)
  exact TauCeti.mkₐ_smul_coinvariantIdeal A γ x

/-- Normal-form version of `mkFixed_inducedAction_apply` after `inducedAction_apply`. -/
@[simp]
theorem mkFixed_semilinearMap_apply (γ : Γ) (x : WeilRestriction A B C) :
    mkFixed ρB ρC h (semilinearMap (ρB γ) (ρC γ : C →+* C) (h γ) x) = mkFixed ρB ρC h x := by
  rw [← inducedAction_apply]; exact mkFixed_inducedAction_apply ρB ρC h γ x

/-- The universal `Γ`-equivariant point `C →ₐ[B] B ⊗[A] fixedCoordinateRing ρB ρC h`. -/
def fixedUniversalPoint : C →ₐ[B] B ⊗[A] fixedCoordinateRing ρB ρC h :=
  homEquiv A B C (fixedCoordinateRing ρB ρC h) (mkFixed ρB ρC h)

/-- Explicit `homEquiv` formula for `fixedUniversalPoint`. -/
theorem fixedUniversalPoint_def :
    fixedUniversalPoint ρB ρC h =
      homEquiv A B C (fixedCoordinateRing ρB ρC h) (mkFixed ρB ρC h) := by rfl

/-- The universal point of `fixedCoordinateRing ρB ρC h` is `Γ`-equivariant. -/
theorem fixedUniversalPoint_equivariant (γ : Γ) (c : C) :
    fixedUniversalPoint ρB ρC h (ρC γ c) =
      Algebra.TensorProduct.rTensor (fixedCoordinateRing ρB ρC h) (ρB γ : B →ₐ[A] B)
        (fixedUniversalPoint ρB ρC h c) := by
  refine (fixedIdeal_le_ker_iff ρB ρC h (mkFixed ρB ρC h)).mp ?_ γ c
  rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom, ker_mkFixed]

/-- **Universal property of `(Res_{B/A} Spec C)^Γ`** (Edixhoven, Proposition 3.1). -/
def fixedHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (fixedCoordinateRing ρB ρC h →ₐ[A] T) ≃
      { y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C), y (ρC γ c) =
          Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c) } :=
  letI := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  letI : SMulCommClass Γ A (WeilRestriction A B C) :=
    SMul.comp.smulCommClass (inducedAction ρB ρC h)
  (TauCeti.coinvariantAlgHomEquiv A Γ (WeilRestriction A B C) T).trans
    (Equiv.subtypeEquiv (homEquiv A B C T) (forall_inducedAction_eq_iff_equivariant ρB ρC h))

/-- `fixedHomEquiv` acts by precomposing with `mkFixed` and applying `homEquiv`. -/
@[simp]
theorem coe_fixedHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (g : fixedCoordinateRing ρB ρC h →ₐ[A] T) :
    (fixedHomEquiv ρB ρC h T g).1 = homEquiv A B C T (g.comp (mkFixed ρB ρC h)) := by
  revert g; unfold fixedCoordinateRing mkFixed fixedHomEquiv fixedIdeal; intro g; simp

/-- Base-change description of `fixedHomEquiv` in terms of `fixedUniversalPoint`. -/
theorem coe_fixedHomEquiv_eq_lTensor_comp_fixedUniversalPoint {T : Type*} [CommRing T] [Algebra A T]
    (g : fixedCoordinateRing ρB ρC h →ₐ[A] T) :
    (fixedHomEquiv ρB ρC h T g).1 =
      (Algebra.TensorProduct.lTensor (S := B) B g).comp (fixedUniversalPoint ρB ρC h) := by
  rw [coe_fixedHomEquiv_apply, homEquiv_comp, fixedUniversalPoint_def]

/-- Evaluating `(fixedHomEquiv ρB ρC h T).symm y` on `mkFixed ρB ρC h x`. -/
@[simp]
theorem fixedHomEquiv_symm_mkFixed {T : Type*} [CommRing T] [Algebra A T]
    (y : { y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C), y (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c) })
    (x : WeilRestriction A B C) :
    (fixedHomEquiv ρB ρC h T).symm y (mkFixed ρB ρC h x) = (homEquiv A B C T).symm y.1 x := by
  unfold fixedCoordinateRing mkFixed fixedHomEquiv fixedIdeal
  simp [TauCeti.coinvariantAlgHomEquiv_symm_mkₐ]

/-- Precomposing `(fixedHomEquiv ρB ρC h T).symm y` with `mkFixed` is `(homEquiv).symm y.1`. -/
@[simp]
theorem fixedHomEquiv_symm_comp_mkFixed {T : Type*} [CommRing T] [Algebra A T]
    (y : { y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C), y (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c) }) :
    ((fixedHomEquiv ρB ρC h T).symm y).comp (mkFixed ρB ρC h) = (homEquiv A B C T).symm y.1 :=
  AlgHom.ext (fixedHomEquiv_symm_mkFixed ρB ρC h y)

/-- If `Γ` acts trivially on `B` and `C`, then `fixedIdeal ρB ρC h` vanishes. -/
theorem fixedIdeal_eq_bot_of_eq_one (hB : ρB = 1) (hC : ρC = 1) : fixedIdeal ρB ρC h = ⊥ := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  exact TauCeti.coinvariantIdeal_eq_bot_iff.mpr fun γ x ↦ by
    rw [MulAction.compHom_smul_def, inducedAction_eq_one ρB ρC h hB hC, MonoidHom.one_apply,
      one_smul]

/-- A trivial semilinear action fixes the entire Weil restriction. -/
def fixedCoordinateRingEquivOfEqOne (hB : ρB = 1) (hC : ρC = 1) :
    fixedCoordinateRing ρB ρC h ≃ₐ[A] WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedIdeal_eq_bot_of_eq_one ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- `fixedCoordinateRingEquivOfEqOne` sends `mkFixed ρB ρC h x` to `x`. -/
@[simp]
theorem fixedCoordinateRingEquivOfEqOne_mkFixed (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    fixedCoordinateRingEquivOfEqOne ρB ρC h hB hC (mkFixed ρB ρC h x) = x := by
  simp [fixedCoordinateRingEquivOfEqOne, mkFixed_def]

/-- The inverse of `fixedCoordinateRingEquivOfEqOne` is `mkFixed ρB ρC h`. -/
@[simp]
theorem fixedCoordinateRingEquivOfEqOne_symm_apply (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (fixedCoordinateRingEquivOfEqOne ρB ρC h hB hC).symm x = mkFixed ρB ρC h x := by
  apply (fixedCoordinateRingEquivOfEqOne ρB ρC h hB hC).injective
  rw [AlgEquiv.apply_symm_apply, fixedCoordinateRingEquivOfEqOne_mkFixed]

/-- When `Γ` is finite, `fixedIdeal ρB ρC h` is finitely generated. -/
theorem fixedIdeal_fg [_root_.Finite Γ] : (fixedIdeal ρB ρC h).FG := by
  let _ := MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  let _ : SMulCommClass Γ A (WeilRestriction A B C) :=
    SMul.comp.smulCommClass (inducedAction ρB ρC h)
  exact TauCeti.coinvariantIdeal_fg (R := A)

/-- When `Γ` is finite, `fixedCoordinateRing ρB ρC h` is of finite presentation over `A`. -/
instance instFinitePresentationFixedCoordinateRing [_root_.Finite Γ] :
    FinitePresentation A (fixedCoordinateRing ρB ρC h) :=
  Algebra.FinitePresentation.quotient (fixedIdeal_fg ρB ρC h)

end General

section Smoothness

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]
  {Γ : Type*} [Group Γ] [_root_.Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions** (Edixhoven, Proposition 3.4). -/
theorem formallySmooth_fixedPoints [FormallySmooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (fixedCoordinateRing ρB ρC h) :=
  TauCeti.formallySmooth_quotient_of_eq_iSup_span_range_sub (inducedAction ρB ρC h)
    (fixedIdeal_def ρB ρC h) hΓ

/-- **Edixhoven's tame fixed-point theorem for Weil restrictions** (Edixhoven, Propositions 3.1
and 3.4). -/
theorem smooth_fixedPoints [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (fixedCoordinateRing ρB ρC h) :=
  TauCeti.smooth_quotient_of_eq_iSup_span_range_sub (inducedAction ρB ρC h)
    (fixedIdeal_def ρB ρC h) hΓ

end Smoothness

section TameAffineLine

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))

/-- The semilinear action of `Γ` on `B[X]` through its coefficients, fixing `X`. -/
def polynomialCoefficientAction : Γ →* RingAut B[X] where
  toFun γ := Polynomial.mapEquiv (ρB γ).toRingEquiv
  map_one' := by ext p n; simp [map_one ρB]
  map_mul' γ δ := by ext p n; simp [map_mul ρB]

/-- Pointwise evaluation of `polynomialCoefficientAction` maps coefficients along `ρB γ`. -/
@[simp]
theorem polynomialCoefficientAction_apply (γ : Γ) (p : B[X]) :
    polynomialCoefficientAction ρB γ p = p.map (ρB γ : B →+* B) := by rfl

/-- `polynomialCoefficientAction` acts on constant polynomials `C b` through `ρB`. -/
theorem polynomialCoefficientAction_C (γ : Γ) (b : B) :
    polynomialCoefficientAction ρB γ (Polynomial.C b) = Polynomial.C (ρB γ b) := by simp

/-- `polynomialCoefficientAction` fixes the indeterminate `X`. -/
theorem polynomialCoefficientAction_X (γ : Γ) :
    polynomialCoefficientAction ρB γ Polynomial.X = Polynomial.X := by simp

/-- Semilinearity of `polynomialCoefficientAction` over `ρB`. -/
theorem polynomialCoefficientAction_algebraMap (γ : Γ) (b : B) :
    polynomialCoefficientAction ρB γ (algebraMap B B[X] b) = algebraMap B B[X] (ρB γ b) := by simp

/-- `y : B[X] →ₐ[B] B ⊗[A] T` is `Γ`-equivariant iff `y X` is fixed by every `ρB γ ⊗ id_T`. -/
theorem polynomialCoefficientAction_equivariant_iff {T : Type*} [CommRing T] [Algebra A T]
    (y : B[X] →ₐ[B] B ⊗[A] T) :
    (∀ (γ : Γ) (p : B[X]), y (polynomialCoefficientAction ρB γ p) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y p)) ↔
      ∀ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y Polynomial.X) =
        y Polynomial.X := by
  refine ⟨fun hy γ ↦ by simpa using (hy γ Polynomial.X).symm, fun hX γ p ↦ ?_⟩
  have hHom : y.toRingHom.comp (polynomialCoefficientAction ρB γ : B[X] →+* B[X]) =
      (Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B)).toRingHom.comp y.toRingHom := by
    ext b
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, polynomialCoefficientAction_C]
      rw [← Polynomial.algebraMap_eq, y.commutes, y.commutes]; simp
    · simpa using (hX γ).symm
  exact DFunLike.congr_fun hHom p

private abbrev polyFixedRing [Module.Finite A B] [Module.Projective A B]
    {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) :=
  fixedCoordinateRing ρB (polynomialCoefficientAction ρB)
    (polynomialCoefficientAction_algebraMap ρB)

private def toPolynomialAlgHom [Module.Finite A B] [Module.Projective A B]
    {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) : polyFixedRing ρB →ₐ[A] A[X] :=
  (fixedHomEquiv ρB (polynomialCoefficientAction ρB)
    (polynomialCoefficientAction_algebraMap ρB) A[X]).symm
    ⟨Polynomial.aeval (Algebra.TensorProduct.includeRight Polynomial.X),
      (polynomialCoefficientAction_equivariant_iff ρB _).mpr fun _ ↦ by
        simp [Algebra.TensorProduct.includeRight_apply]⟩

section PolyEquiv

variable [Module.Finite A B] [Module.Projective A B]

private theorem lTensor_toPolynomialAlgHom_universalPoint_X
    {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) :
    (Algebra.TensorProduct.lTensor (S := B) B (toPolynomialAlgHom ρB))
        (fixedUniversalPoint ρB (polynomialCoefficientAction ρB)
          (polynomialCoefficientAction_algebraMap ρB) Polynomial.X) =
      Algebra.TensorProduct.includeRight Polynomial.X := by
  have hX := congrArg (fun f : B[X] →ₐ[B] B ⊗[A] A[X] ↦ f Polynomial.X)
    (coe_fixedHomEquiv_eq_lTensor_comp_fixedUniversalPoint ρB
      (polynomialCoefficientAction ρB) (polynomialCoefficientAction_algebraMap ρB)
      (toPolynomialAlgHom ρB))
  exact hX.symm.trans (by simp [toPolynomialAlgHom])

variable {Γ : Type*} [Group Γ] [_root_.Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B))
  (hΓ : IsUnit (Nat.card Γ : A)) (hinj : Function.Injective (algebraMap A B))
  (hinv : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))

private def fromPolynomialAlgHom : A[X] →ₐ[A] polyFixedRing ρB :=
  letI := MulSemiringAction.compHom B ρB
  letI : SMulCommClass Γ A B := SMul.comp.smulCommClass ρB
  letI := SMulCommClass.symm Γ A B
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  haveI : Algebra.IsInvariant A B Γ := ⟨hinv⟩
  Polynomial.aeval ((TauCeti.MulSemiringAction.invariantsBaseChangeEquivOfIsUnitCard A B Γ _
    hΓ).symm ⟨_, by
      rw [Representation.mem_invariants]; intro γ
      have hsmul (w : B ⊗[A] polyFixedRing ρB) :
          γ • w = Algebra.TensorProduct.rTensor _ (ρB γ : B →ₐ[A] B) w := by
        induction w using TensorProduct.inductionOn with
        | tmul b t => rfl
        | add x y hx hy => simp [smul_add, hx, hy]
      simpa only [Representation.ofDistribMulAction_apply_apply, hsmul] using
        (polynomialCoefficientAction_equivariant_iff ρB _).mp (fixedUniversalPoint_equivariant ρB
          (polynomialCoefficientAction ρB) (polynomialCoefficientAction_algebraMap ρB)) γ⟩)

private theorem includeRight_fromPolynomialAlgHom_X :
    Algebra.TensorProduct.includeRight (fromPolynomialAlgHom ρB hΓ hinj hinv Polynomial.X) =
      fixedUniversalPoint ρB (polynomialCoefficientAction ρB)
        (polynomialCoefficientAction_algebraMap ρB) Polynomial.X := by
  let _ := MulSemiringAction.compHom B ρB
  let _ : SMulCommClass Γ A B := SMul.comp.smulCommClass ρB
  let _ := SMulCommClass.symm Γ A B
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have _ : Algebra.IsInvariant A B Γ := ⟨hinv⟩
  simpa only [fromPolynomialAlgHom, Polynomial.aeval_X, Algebra.TensorProduct.includeRight_apply]
    using TauCeti.MulSemiringAction.one_tmul_invariantsBaseChangeEquivOfIsUnitCard_symm hΓ _

/-- **Tame fixed points of the restricted affine line**: when `B` is finite projective over `A`,
`|Γ| ∈ Aˣ`, `A → B` is injective, and `B^Γ = A`, `(Res_{B/A} 𝔸¹_B)^Γ` has coordinate ring `A[X]`. -/
def fixedCoordinateRingPolynomialEquiv :
    fixedCoordinateRing ρB (polynomialCoefficientAction ρB)
        (polynomialCoefficientAction_algebraMap ρB) ≃ₐ[A] A[X] :=
  AlgEquiv.ofAlgHom (toPolynomialAlgHom ρB) (fromPolynomialAlgHom ρB hΓ hinj hinv)
    (by
      let _ := MulSemiringAction.compHom B ρB
      let _ : SMulCommClass Γ A B := SMul.comp.smulCommClass ρB
      let _ := SMulCommClass.symm Γ A B
      have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
      have _ : Algebra.IsInvariant A B Γ := ⟨hinv⟩
      let e := TauCeti.MulSemiringAction.invariantsBaseChangeEquivOfIsUnitCard A B Γ A[X] hΓ
      apply Polynomial.algHom_ext; apply e.injective; apply Subtype.ext
      rw [TauCeti.MulSemiringAction.coe_invariantsBaseChangeEquivOfIsUnitCard_apply,
        TauCeti.MulSemiringAction.coe_invariantsBaseChangeEquivOfIsUnitCard_apply,
        ← Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.includeRight_apply,
        AlgHom.comp_apply, AlgHom.id_apply, ← lTensor_toPolynomialAlgHom_universalPoint_X ρB,
        ← includeRight_fromPolynomialAlgHom_X ρB hΓ hinj hinv]
      simp [Algebra.TensorProduct.includeRight_apply])
    (by
      apply (fixedHomEquiv ρB (polynomialCoefficientAction ρB)
        (polynomialCoefficientAction_algebraMap ρB) _).injective
      apply Subtype.ext; apply Polynomial.algHom_ext
      rw [coe_fixedHomEquiv_eq_lTensor_comp_fixedUniversalPoint,
        coe_fixedHomEquiv_eq_lTensor_comp_fixedUniversalPoint, AlgHom.comp_apply, AlgHom.comp_apply]
      refine (DFunLike.congr_fun (Algebra.TensorProduct.map_id_comp (S := B)
        (fromPolynomialAlgHom ρB hΓ hinj hinv) (toPolynomialAlgHom ρB)) _).trans ?_
      rw [AlgHom.comp_apply, lTensor_toPolynomialAlgHom_universalPoint_X]
      simpa [Algebra.TensorProduct.includeRight_apply] using
        includeRight_fromPolynomialAlgHom_X ρB hΓ hinj hinv)

/-- Under `fixedHomEquiv`, `fixedCoordinateRingPolynomialEquiv` classifies `X ↦ 1 ⊗ₜ X`. -/
theorem coe_fixedHomEquiv_fixedCoordinateRingPolynomialEquiv :
    (fixedHomEquiv ρB (polynomialCoefficientAction ρB)
        (polynomialCoefficientAction_algebraMap ρB) A[X]
        (fixedCoordinateRingPolynomialEquiv ρB hΓ hinj hinv).toAlgHom).1 =
      Polynomial.aeval (Algebra.TensorProduct.includeRight Polynomial.X) := by
  rw [fixedCoordinateRingPolynomialEquiv, AlgEquiv.toAlgHom_ofAlgHom, toPolynomialAlgHom]
  exact congrArg Subtype.val ((fixedHomEquiv ρB (polynomialCoefficientAction ρB)
    (polynomialCoefficientAction_algebraMap ρB) A[X]).apply_symm_apply _)

end PolyEquiv

end TameAffineLine

end TauCeti.Algebra.WeilRestriction
