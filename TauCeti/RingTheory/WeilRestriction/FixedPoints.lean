/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.Invariant.ModuleDescent
public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.RingTheory.WeilRestriction.Etale
public import TauCeti.RingTheory.WeilRestriction.Semilinear

/-!
# Fixed-point schemes of Weil restrictions and Edixhoven's tame descent theorem

Let `B` be a finite projective `A`-algebra, `C` a finitely presented `B`-algebra, and `Γ` a monoid
acting on `B` by `A`-algebra automorphisms `ρB : Γ →* (B ≃ₐ[A] B)` and on `C` by ring automorphisms
`ρC : Γ →* RingAut C` semilinear over `ρB`. By `WeilRestriction.inducedAction`, `Γ` acts on
`WeilRestriction A B C` by `A`-algebra automorphisms.

This file studies the **fixed-point ideal** `WeilRestriction.fixedPointIdeal ρB ρC h` and its
quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h`, which represents the closed subscheme
`(Res_{B/A} Spec C)^Γ`:
* For any `A`-algebra `T`, `A`-algebra homomorphisms out of the quotient correspond naturally and
  bijectively to `Γ`-equivariant `B`-algebra points `C →ₐ[B] B ⊗[A] T` (`fixedPointsHomEquiv`).
* When `Γ` is a finite group whose order `(Nat.card Γ : A)` is invertible in `A` and `C` is
  formally smooth (respectively smooth) over `B`, the fixed-point quotient
  `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally smooth (respectively smooth) over
  `A` (`formallySmooth_quotient_fixedPointIdeal`, `smooth_quotient_fixedPointIdeal`). This is
  Edixhoven's tame fixed-point smoothness theorem applied to Weil restrictions — the algebraic core
  of tame Galois descent of integral models, requiring neither Noetherian nor Henselian hypotheses
  on `A`.
* When `C` is formally étale (respectively étale, for finite `Γ`) over `B`, the fixed-point
  quotient is formally étale (respectively étale) over `A` with no invertibility assumption on
  `Nat.card Γ` (`formallyEtale_quotient_fixedPointIdeal`, `etale_quotient_fixedPointIdeal`).
* When a finite group `Γ` acts on `B` with invariant ring `A`
  (`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`) and `B` admits an element of trace `1` — in
  particular whenever `(Nat.card Γ : A)` is invertible (including ramified tame extensions) or
  whenever `Γ` acts freely (`TauCeti.MulSemiringAction.exists_sum_smul_eq_one`) — for every
  finitely presented `A`-algebra `D` the `Γ`-fixed quotient of `WeilRestriction A B (B ⊗[A] D)` is
  canonically isomorphic as an `A`-algebra to `D`
  (`quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne`,
  `quotientFixedPointIdealBaseChangeAlgEquiv`). Specializing to `D = A[X]` identifies the `Γ`-fixed
  quotient of `WeilRestriction A B B[X]` with `A[X]` (`quotientFixedPointIdealPolynomialAlgEquiv`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointIdeal`: the ideal of `WeilRestriction A B C` generated
  by all displacements `inducedAction ρB ρC h γ x - x`.
* `TauCeti.Algebra.WeilRestriction.fixedPointsHomEquiv`: functor of points of
  `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h`, classifying `Γ`-equivariant points
  `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealAlgEquivOfEquiv`: functoriality of the
  fixed-point quotient under `Γ`-equivariant `B`-algebra isomorphisms.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne`,
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealBaseChangeAlgEquiv`, and
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv`: descent of
  `(Res_{B/A}(B ⊗[A] D))^Γ ≃ₐ[A] D` and `(Res_{B/A} B[X])^Γ ≃ₐ[A] A[X]`.

## Main results

* `TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdeal` and
  `TauCeti.Algebra.WeilRestriction.smooth_quotient_fixedPointIdeal`: Edixhoven's tame fixed-point
  smoothness theorem for Weil restrictions.
* `TauCeti.Algebra.WeilRestriction.formallyEtale_quotient_fixedPointIdeal` and
  `TauCeti.Algebra.WeilRestriction.etale_quotient_fixedPointIdeal`: preservation of formal
  étaleness and étaleness on fixed points of Weil restrictions.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4 and
  Propositions 3.1, 3.4, pp. 292–295.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), Proposition 1.3.9, p. 143.
-/

public noncomputable section

open Algebra TensorProduct Polynomial

namespace TauCeti.Algebra.WeilRestriction

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The **fixed-point ideal** of `WeilRestriction.inducedAction ρB ρC h` inside
`WeilRestriction A B C`: the ideal generated by all displacements
`inducedAction ρB ρC h γ x - x`. Its quotient represents the closed subscheme of `Γ`-fixed points
of `Res_{B/A}(Spec C)`. -/
def fixedPointIdeal : Ideal (WeilRestriction A B C) :=
  Ideal.span {y : WeilRestriction A B C |
    ∃ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x = y}

theorem fixedPointIdeal_def :
    fixedPointIdeal ρB ρC h = Ideal.span {y : WeilRestriction A B C |
      ∃ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x = y} :=
  (rfl)

/-- Every displacement `inducedAction ρB ρC h γ x - x` belongs to `fixedPointIdeal ρB ρC h`. -/
theorem inducedAction_sub_mem_fixedPointIdeal (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x - x ∈ fixedPointIdeal ρB ρC h :=
  Ideal.subset_span ⟨γ, x, rfl⟩

/-- Universal property of `fixedPointIdeal ρB ρC h` among ideals of `WeilRestriction A B C`. -/
theorem fixedPointIdeal_le_iff {J : Ideal (WeilRestriction A B C)} :
    fixedPointIdeal ρB ρC h ≤ J ↔
      ∀ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x ∈ J := by
  rw [fixedPointIdeal_def, Ideal.span_le]
  exact ⟨fun hJ γ x ↦ hJ ⟨γ, x, rfl⟩, by rintro hJ _ ⟨γ, x, rfl⟩; exact hJ γ x⟩

/-- A ring homomorphism out of `WeilRestriction A B C` vanishes on `fixedPointIdeal ρB ρC h` if and
only if it is invariant under `inducedAction ρB ρC h`. -/
theorem fixedPointIdeal_le_ker_iff {F R' : Type*} [Ring R']
    [FunLike F (WeilRestriction A B C) R'] [RingHomClass F (WeilRestriction A B C) R'] (φ : F) :
    fixedPointIdeal ρB ρC h ≤ RingHom.ker φ ↔
      ∀ (γ : Γ) (x : WeilRestriction A B C), φ (inducedAction ρB ρC h γ x) = φ x := by
  rw [fixedPointIdeal_le_iff]
  simp only [RingHom.mem_ker, map_sub, sub_eq_zero]

/-- `fixedPointIdeal ρB ρC h` vanishes if and only if the induced action on `WeilRestriction A B C`
is trivial. -/
@[simp]
theorem fixedPointIdeal_eq_bot_iff :
    fixedPointIdeal ρB ρC h = ⊥ ↔ inducedAction ρB ρC h = 1 := by
  rw [eq_bot_iff, fixedPointIdeal_le_iff]
  constructor
  · intro htriv
    ext γ x
    exact sub_eq_zero.mp (htriv γ x)
  · intro hone γ x
    exact sub_eq_zero.mpr congr($hone γ x)

/-- Modulo `fixedPointIdeal ρB ρC h`, `inducedAction ρB ρC h γ x` equals `x`. -/
theorem mk_inducedAction_eq (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) (inducedAction ρB ρC h γ x) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x :=
  Ideal.Quotient.eq.mpr (inducedAction_sub_mem_fixedPointIdeal ρB ρC h γ x)

/-- **Functor of points of the fixed-point scheme of a Weil restriction.** For every commutative
`A`-algebra `T`, `A`-algebra homomorphisms
`(WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T` correspond bijectively to
`Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointsHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    ((WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
        y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} where
  toFun φ :=
    ⟨homEquiv A B C T (φ.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))), fun γ ↦
      (comp_inducedAction_eq_iff ρB ρC h γ _).mp
        (AlgHom.ext fun x ↦ by
          simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
            mk_inducedAction_eq])⟩
  invFun y := Ideal.Quotient.liftₐ (fixedPointIdeal ρB ρC h) ((homEquiv A B C T).symm y.1)
    fun z hz ↦ by
      rw [← RingHom.mem_ker]
      refine (fixedPointIdeal_le_ker_iff ρB ρC h ((homEquiv A B C T).symm y.1)).mpr ?_ hz
      intro γ x
      have hcomp : ((homEquiv A B C T).symm y.1).comp
          (inducedAction ρB ρC h γ : _ →ₐ[A] _) = (homEquiv A B C T).symm y.1 := by
        rw [comp_inducedAction_eq_iff, Equiv.apply_symm_apply]
        exact y.2 γ
      exact congr($hcomp x)
  left_inv φ := by
    apply AlgHom.ext
    rintro ⟨x⟩
    change ((homEquiv A B C T).symm (homEquiv A B C T _)) x = φ (Ideal.Quotient.mk _ x)
    rw [(homEquiv A B C T).symm_apply_apply]
    rfl
  right_inv y := Subtype.ext <| by
    dsimp only
    exact (congrArg (homEquiv A B C T) (AlgHom.ext fun _ ↦ rfl)).trans
      ((homEquiv A B C T).apply_symm_apply y.1)

@[simp]
theorem fixedPointsHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (φ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T) :
    (fixedPointsHomEquiv ρB ρC h T φ).1 =
      homEquiv A B C T (φ.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) :=
  (rfl)

/-- Naturality of `fixedPointsHomEquiv` in the target `A`-algebra `T`. -/
theorem fixedPointsHomEquiv_comp {T T' : Type*} [CommRing T] [Algebra A T] [CommRing T']
    [Algebra A T'] (φ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T)
    (k : T →ₐ[A] T') :
    (fixedPointsHomEquiv ρB ρC h T' (k.comp φ)).1 =
      (Algebra.TensorProduct.lTensor B k).comp (fixedPointsHomEquiv ρB ρC h T φ).1 := by
  rw [fixedPointsHomEquiv_apply, AlgHom.comp_assoc, homEquiv_comp, fixedPointsHomEquiv_apply]

/-- Two `A`-algebra homomorphisms out of `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` are
equal if they classify the same `B`-algebra point. -/
theorem fixedPoints_hom_ext {T : Type*} [CommRing T] [Algebra A T]
    {φ ψ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T}
    (heq : (fixedPointsHomEquiv ρB ρC h T φ).1 = (fixedPointsHomEquiv ρB ρC h T ψ).1) :
    φ = ψ :=
  (fixedPointsHomEquiv ρB ρC h T).injective (Subtype.ext heq)

/-- A `Γ`-equivariant `B`-algebra isomorphism `e : C ≃ₐ[B] D` induces an `A`-algebra isomorphism
between the fixed-point quotients of `WeilRestriction A B C` and `WeilRestriction A B D`. -/
def quotientFixedPointIdealAlgEquivOfEquiv {D : Type*} [CommRing D] [Algebra B D]
    [FinitePresentation B D] (ρD : Γ →* RingAut D)
    (hD : ∀ γ b, ρD γ (algebraMap B D b) = algebraMap B D (ρB γ b))
    (e : C ≃ₐ[B] D) (he : ∀ (γ : Γ) (c : C), ρD γ (e c) = e (ρC γ c)) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A]
      (WeilRestriction A B D ⧸ fixedPointIdeal ρB ρD hD) := by
  let Q₁ := WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h
  let Q₂ := WeilRestriction A B D ⧸ fixedPointIdeal ρB ρD hD
  let u₁ := fixedPointsHomEquiv ρB ρC h Q₁ (AlgHom.id A Q₁)
  let u₂ := fixedPointsHomEquiv ρB ρD hD Q₂ (AlgHom.id A Q₂)
  have he_symm (γ : Γ) (d : D) : ρC γ (e.symm d) = e.symm (ρD γ d) := by
    apply e.injective
    rw [e.apply_symm_apply, ← he, e.apply_symm_apply]
  let y₂ : {y : C →ₐ[B] B ⊗[A] Q₂ // ∀ (γ : Γ) (c : C),
      y (ρC γ c) = Algebra.TensorProduct.rTensor Q₂ (ρB γ : B →ₐ[A] B) (y c)} :=
    ⟨u₂.1.comp e.toAlgHom, fun γ c ↦ by
      change u₂.1 (e (ρC γ c)) =
        Algebra.TensorProduct.rTensor Q₂ (ρB γ : B →ₐ[A] B) (u₂.1 (e c))
      rw [← he, u₂.2]⟩
  let y₁ : {y : D →ₐ[B] B ⊗[A] Q₁ // ∀ (γ : Γ) (d : D),
      y (ρD γ d) = Algebra.TensorProduct.rTensor Q₁ (ρB γ : B →ₐ[A] B) (y d)} :=
    ⟨u₁.1.comp e.symm.toAlgHom, fun γ d ↦ by
      change u₁.1 (e.symm (ρD γ d)) =
        Algebra.TensorProduct.rTensor Q₁ (ρB γ : B →ₐ[A] B) (u₁.1 (e.symm d))
      rw [← he_symm, u₁.2]⟩
  let fwd : Q₁ →ₐ[A] Q₂ := (fixedPointsHomEquiv ρB ρC h Q₂).symm y₂
  let bwd : Q₂ →ₐ[A] Q₁ := (fixedPointsHomEquiv ρB ρD hD Q₁).symm y₁
  have hfwd_u₁ : (Algebra.TensorProduct.lTensor B fwd).comp u₁.1 = y₂.1 := by
    rw [← fixedPointsHomEquiv_comp, AlgHom.comp_id]
    exact congrArg Subtype.val ((fixedPointsHomEquiv ρB ρC h Q₂).apply_symm_apply y₂)
  have hbwd_u₂ : (Algebra.TensorProduct.lTensor B bwd).comp u₂.1 = y₁.1 := by
    rw [← fixedPointsHomEquiv_comp, AlgHom.comp_id]
    exact congrArg Subtype.val ((fixedPointsHomEquiv ρB ρD hD Q₁).apply_symm_apply y₁)
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · apply fixedPoints_hom_ext ρB ρD hD
    rw [fixedPointsHomEquiv_comp, (fixedPointsHomEquiv ρB ρD hD Q₁).apply_symm_apply]
    change (Algebra.TensorProduct.lTensor B fwd).comp (u₁.1.comp e.symm.toAlgHom) = u₂.1
    rw [← AlgHom.comp_assoc, hfwd_u₁]
    exact AlgHom.ext fun d ↦ by simp [y₂]
  · apply fixedPoints_hom_ext ρB ρC h
    rw [fixedPointsHomEquiv_comp, (fixedPointsHomEquiv ρB ρC h Q₂).apply_symm_apply]
    change (Algebra.TensorProduct.lTensor B bwd).comp (u₂.1.comp e.toAlgHom) = u₁.1
    rw [← AlgHom.comp_assoc, hbwd_u₂]
    exact AlgHom.ext fun c ↦ by simp [y₁]

/-- When `Γ` acts trivially on both `B` and `C`, `fixedPointIdeal ρB ρC h` vanishes. -/
theorem fixedPointIdeal_eq_bot_of_eq_one (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdeal ρB ρC h = ⊥ :=
  (fixedPointIdeal_eq_bot_iff ρB ρC h).mpr (inducedAction_eq_one ρB ρC h hB hC)

/-- When `Γ` acts trivially on `B` and `C`, the fixed-point quotient of `WeilRestriction A B C` is
isomorphic as an `A`-algebra to `WeilRestriction A B C`. -/
def quotientFixedPointIdealAlgEquivOfEqOne (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointIdeal_eq_bot_of_eq_one ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- When `Γ` is finite, `fixedPointIdeal ρB ρC h` is finitely generated. -/
theorem fg_fixedPointIdeal [Finite Γ] : (fixedPointIdeal ρB ρC h).FG := by
  let _ : MulSemiringAction Γ (WeilRestriction A B C) :=
    MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  have : SMulCommClass Γ A (WeilRestriction A B C) :=
    ⟨fun γ a x ↦ map_smul (inducedAction ρB ρC h γ) a x⟩
  have hI : fixedPointIdeal ρB ρC h =
      MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) := by
    rw [fixedPointIdeal_def, MulSemiringAction.fixedPointIdeal_def]
    rfl
  rw [hI]
  exact MulSemiringAction.fg_fixedPointIdeal (R := A)

/-- When `Γ` is finite, `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is finitely presented
over `A`. -/
theorem finitePresentation_quotient_fixedPointIdeal [Finite Γ] :
    FinitePresentation A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) :=
  FinitePresentation.quotient (fg_fixedPointIdeal ρB ρC h)

/-- **Formal étaleness of fixed points of a Weil restriction.** If `C` is formally étale over `B`,
then for any monoid `Γ` acting compatibly on `B` and `C`, the fixed-point quotient
`WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally étale over `A`. -/
theorem formallyEtale_quotient_fixedPointIdeal [FormallyEtale B C] :
    FormallyEtale A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ : MulSemiringAction Γ (WeilRestriction A B C) :=
    MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  have : SMulCommClass Γ A (WeilRestriction A B C) :=
    ⟨fun γ a x ↦ map_smul (inducedAction ρB ρC h γ) a x⟩
  have hI : fixedPointIdeal ρB ρC h =
      MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) := by
    rw [fixedPointIdeal_def, MulSemiringAction.fixedPointIdeal_def]
    rfl
  have := MulSemiringAction.formallyEtale_quotient_fixedPointIdeal
    (R := A) (M := Γ) (A := WeilRestriction A B C)
  exact .of_equiv (Ideal.quotientEquivAlgOfEq A hI.symm)

/-- **Étaleness of fixed points of a Weil restriction.** If `Γ` is finite and `C` is étale over
`B`, then `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is étale over `A`. -/
theorem etale_quotient_fixedPointIdeal [Finite Γ] [Etale B C] :
    Etale A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) where
  formallyEtale := formallyEtale_quotient_fixedPointIdeal ρB ρC h
  finitePresentation := finitePresentation_quotient_fixedPointIdeal ρB ρC h

end General

section TameSmooth

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions.** Let `B` be finite projective
over `A`, `C` finitely presented and formally smooth over `B`, and `Γ` a finite group with
`(Nat.card Γ : A)` invertible in `A` acting compatibly on `B` and `C`. Then the fixed-point
quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally smooth over `A`. -/
theorem formallySmooth_quotient_fixedPointIdeal [FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ : MulSemiringAction Γ (WeilRestriction A B C) :=
    MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)
  have : SMulCommClass Γ A (WeilRestriction A B C) :=
    ⟨fun γ a x ↦ map_smul (inducedAction ρB ρC h γ) a x⟩
  have hI : fixedPointIdeal ρB ρC h =
      MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) := by
    rw [fixedPointIdeal_def, MulSemiringAction.fixedPointIdeal_def]
    rfl
  have := MulSemiringAction.formallySmooth_quotient_fixedPointIdeal
    (R := A) (G := Γ) (A := WeilRestriction A B C) hΓ
  exact .of_equiv (Ideal.quotientEquivAlgOfEq A hI.symm)

/-- **Edixhoven's smoothness theorem for Weil restrictions.** Let `B` be finite projective over `A`,
`C` smooth over `B`, and `Γ` a finite group with `(Nat.card Γ : A)` invertible in `A` acting on `B`
by `A`-algebra automorphisms and on `C` by compatible semilinear ring automorphisms. Then the
fixed-point quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` — the coordinate ring of
`(Res_{B/A} Spec C)^Γ` — is smooth over `A`. -/
theorem smooth_quotient_fixedPointIdeal [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) where
  formallySmooth := formallySmooth_quotient_fixedPointIdeal ρB ρC h hΓ
  finitePresentation := finitePresentation_quotient_fixedPointIdeal ρB ρC h

end TameSmooth

section GaloisDescent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (Γ : Type*) [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

/-- The induced action `Γ →* RingAut (B ⊗[A] D)` acting on the left factor by `Γ` and trivially on
`D`. -/
def baseChangeRingAutHom (D : Type*) [CommRing D] [Algebra A D] :
    Γ →* RingAut (B ⊗[A] D) where
  toFun γ :=
    (Algebra.TensorProduct.congr (MulSemiringAction.toAlgEquiv A B γ)
      (AlgEquiv.refl : D ≃ₐ[A] D)).toRingEquiv
  map_one' := RingEquiv.ext fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul b d => simp
    | add x y hx hy => simp [map_add, hx, hy]
  map_mul' γ δ := RingEquiv.ext fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul b d => simp [mul_smul]
    | add x y hx hy => simp [map_add, hx, hy]

theorem baseChangeRingAutHom_algebraMap (D : Type*) [CommRing D] [Algebra A D] (γ : Γ) (b : B) :
    baseChangeRingAutHom A B Γ D γ (algebraMap B (B ⊗[A] D) b) =
      algebraMap B (B ⊗[A] D) (MulSemiringAction.toAlgAut Γ A B γ b) := by
  simp [baseChangeRingAutHom, Algebra.TensorProduct.algebraMap_apply]

private theorem includeRight_injective_of_exists_trace_one {T : Type*} [CommRing T] [Algebra A T]
    [Fintype Γ] [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    Function.Injective (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T) := by
  have : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  intro t₁ t₂ h
  have h' : ((MulSemiringAction.invariantsBaseChangeEquiv A B Γ T hc t₁ : _) : B ⊗[A] T) =
      MulSemiringAction.invariantsBaseChangeEquiv A B Γ T hc t₂ := by
    simpa [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply] using h
  exact (MulSemiringAction.invariantsBaseChangeEquiv A B Γ T hc).injective (Subtype.ext h')

private theorem mem_range_includeRight_of_forall_rTensor_eq {T : Type*} [CommRing T] [Algebra A T]
    [Fintype Γ] [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) {z : B ⊗[A] T}
    (hz : ∀ γ : Γ, Algebra.TensorProduct.rTensor T (MulSemiringAction.toAlgHom A B γ) z = z) :
    z ∈ (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).range := by
  have : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  have hrTensor (γ : Γ) (w : B ⊗[A] T) :
      γ • w = Algebra.TensorProduct.rTensor T (MulSemiringAction.toAlgHom A B γ) w := by
    induction w using TensorProduct.inductionOn with
    | tmul b t => simp [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  let z' : (Representation.ofDistribMulAction A Γ (B ⊗[A] T)).invariants :=
    ⟨z, (Representation.mem_invariants _ _).mpr fun γ ↦ (hrTensor γ z).trans (hz γ)⟩
  let e := MulSemiringAction.invariantsBaseChangeEquiv A B Γ T hc
  have he : (e (e.symm z') : B ⊗[A] T) = z := congrArg Subtype.val (e.apply_symm_apply z')
  rw [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply] at he
  exact ⟨e.symm z', he⟩

private def retractToBaseAlgHom {D T : Type*} [CommRing D] [Algebra A D] [CommRing T]
    [Algebra A T] [Fintype Γ] [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (u : D →ₐ[A] B ⊗[A] T)
    (hu : ∀ (γ : Γ) (d : D),
      Algebra.TensorProduct.rTensor T (MulSemiringAction.toAlgHom A B γ) (u d) = u d) :
    D →ₐ[A] T :=
  (AlgEquiv.ofInjective (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T)
    (includeRight_injective_of_exists_trace_one A B Γ hc)).symm.toAlgHom.comp
      (u.codRestrict _ fun d ↦
        mem_range_includeRight_of_forall_rTensor_eq A B Γ hc (hu · d))

private theorem includeRight_retractToBaseAlgHom_apply {D T : Type*} [CommRing D] [Algebra A D]
    [CommRing T] [Algebra A T] [Fintype Γ] [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (u : D →ₐ[A] B ⊗[A] T)
    (hu : ∀ (γ : Γ) (d : D),
      Algebra.TensorProduct.rTensor T (MulSemiringAction.toAlgHom A B γ) (u d) = u d) (d : D) :
    (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T)
      (retractToBaseAlgHom A B Γ hc u hu d) = u d := by
  let e := AlgEquiv.ofInjective (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T)
    (includeRight_injective_of_exists_trace_one A B Γ hc)
  exact congrArg Subtype.val
    (e.apply_symm_apply (u.codRestrict _
      (fun d ↦ mem_range_includeRight_of_forall_rTensor_eq A B Γ hc (hu · d)) d))

/-- **Galois descent for constant Weil restrictions.** Let `B` be finite projective over `A`, and
let a finite group `Γ` act on `B` with invariant ring `A`
(`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`) such that `B` admits an element of trace `1`
(`∃ c : B, ∑ γ : Γ, γ • c = 1`). For every finitely presented `A`-algebra `D`, the `Γ`-fixed
quotient of `WeilRestriction A B (B ⊗[A] D)` is canonically isomorphic as an `A`-algebra to `D`. -/
def quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B) (baseChangeRingAutHom A B Γ D)
        (baseChangeRingAutHom_algebraMap A B Γ D)) ≃ₐ[A] D := by
  let ρB : Γ →* (B ≃ₐ[A] B) := MulSemiringAction.toAlgAut Γ A B
  let ρBD := baseChangeRingAutHom A B Γ D
  let hBD := baseChangeRingAutHom_algebraMap A B Γ D
  let Q := WeilRestriction A B (B ⊗[A] D) ⧸ fixedPointIdeal ρB ρBD hBD
  have hid_eqv (γ : Γ) (x : B ⊗[A] D) :
      AlgHom.id B (B ⊗[A] D) (ρBD γ x) =
        Algebra.TensorProduct.rTensor D (ρB γ : B →ₐ[A] B) (AlgHom.id B (B ⊗[A] D) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul b d => rfl
    | add x y hx hy => simp [map_add, hx, hy]
  let fwd : Q →ₐ[A] D := (fixedPointsHomEquiv ρB ρBD hBD D).symm ⟨AlgHom.id B (B ⊗[A] D), hid_eqv⟩
  let uQ := fixedPointsHomEquiv ρB ρBD hBD Q (AlgHom.id A Q)
  let uD : D →ₐ[A] B ⊗[A] Q :=
    (uQ.1.restrictScalars A).comp (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D)
  have huD (γ : Γ) (d : D) :
      Algebra.TensorProduct.rTensor Q (MulSemiringAction.toAlgHom A B γ) (uD d) = uD d := by
    have h1 := uQ.2 γ ((1 : B) ⊗ₜ[A] d)
    have hfix1 : ρBD γ ((1 : B) ⊗ₜ[A] d) = (1 : B) ⊗ₜ[A] d := by simp [ρBD, baseChangeRingAutHom]
    rw [hfix1] at h1
    exact h1.symm
  let bwd : D →ₐ[A] Q := retractToBaseAlgHom A B Γ hc uD huD
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · ext d
    apply includeRight_injective_of_exists_trace_one A B Γ hc
    have hd := congr($(fixedPointsHomEquiv_comp ρB ρBD hBD (AlgHom.id A Q) fwd) ((1 : B) ⊗ₜ[A] d))
    rw [AlgHom.comp_id, (fixedPointsHomEquiv ρB ρBD hBD D).apply_symm_apply] at hd
    calc
      (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) (fwd (bwd d))
          = Algebra.TensorProduct.lTensor (S := B) B fwd
              ((Algebra.TensorProduct.includeRight : Q →ₐ[A] B ⊗[A] Q) (bwd d)) := by simp
      _ = Algebra.TensorProduct.lTensor (S := B) B fwd (uD d) := by
            rw [includeRight_retractToBaseAlgHom_apply]
      _ = (1 : B) ⊗ₜ[A] d := hd.symm
  · apply fixedPoints_hom_ext ρB ρBD hBD
    rw [fixedPointsHomEquiv_comp, (fixedPointsHomEquiv ρB ρBD hBD D).apply_symm_apply]
    apply Algebra.TensorProduct.ext
    · ext
    · ext d
      simpa [bwd, uD, uQ] using includeRight_retractToBaseAlgHom_apply A B Γ hc uD huD d

/-- **Tame Galois descent for constant Weil restrictions.** Let `B` be finite projective over `A`,
and let a finite group `Γ` with `(Nat.card Γ : A)` invertible act on `B` with invariant ring `A`
(`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`). For every finitely presented `A`-algebra `D`,
the `Γ`-fixed quotient of `WeilRestriction A B (B ⊗[A] D)` is canonically isomorphic as an
`A`-algebra to `D`. -/
def quotientFixedPointIdealBaseChangeAlgEquiv
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B) (baseChangeRingAutHom A B Γ D)
        (baseChangeRingAutHom_algebraMap A B Γ D)) ≃ₐ[A] D := by
  have := Fintype.ofFinite Γ
  refine quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ D
    ⟨algebraMap A B ↑hΓ.unit⁻¹, ?_⟩
  have hsmul (γ : Γ) (a : A) : γ • algebraMap A B a = algebraMap A B a := by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hmul : (Fintype.card Γ : A) * ↑hΓ.unit⁻¹ = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Units.mul_inv_eq_one.mpr rfl
  simp only [hsmul, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A,
    Algebra.smul_def, ← map_mul, hmul, map_one]

/-- Compatibility of the coefficientwise `Γ`-action on `B[X]` with `algebraMap B B[X]`. -/
theorem toRingAut_polynomial_algebraMap (γ : Γ) (b : B) :
    MulSemiringAction.toRingAut Γ B[X] γ (algebraMap B B[X] b) =
      algebraMap B B[X] (MulSemiringAction.toAlgAut Γ A B γ b) :=
  Polynomial.smul_C γ b

/-- **Tame Galois descent of the affine line.** Under the same hypotheses as
`quotientFixedPointIdealBaseChangeAlgEquiv`, the `Γ`-fixed quotient of `WeilRestriction A B B[X]`
for the coefficientwise `Γ`-action on `B[X]` is isomorphic as an `A`-algebra to `A[X]`. -/
def quotientFixedPointIdealPolynomialAlgEquiv
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B B[X] ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B) (MulSemiringAction.toRingAut Γ B[X])
        (toRingAut_polynomial_algebraMap A B Γ)) ≃ₐ[A] A[X] := by
  refine (quotientFixedPointIdealAlgEquivOfEquiv
    (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeRingAutHom A B Γ A[X]) (baseChangeRingAutHom_algebraMap A B Γ A[X])
    (MulSemiringAction.toRingAut Γ B[X]) (toRingAut_polynomial_algebraMap A B Γ)
    (polyEquivTensor' A B).symm ?_).symm.trans
      (quotientFixedPointIdealBaseChangeAlgEquiv A B Γ A[X] hΓ)
  intro γ z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b q =>
    have hsmul (a : A) : γ • algebraMap A B a = algebraMap A B a := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    ext k
    change (γ • (polyEquivTensor' A B).symm (b ⊗ₜ[A] q)).coeff k =
      ((polyEquivTensor' A B).symm (baseChangeRingAutHom A B Γ A[X] γ (b ⊗ₜ[A] q))).coeff k
    simp [baseChangeRingAutHom, smul_mul', hsmul]

end GaloisDescent

end TauCeti.Algebra.WeilRestriction
