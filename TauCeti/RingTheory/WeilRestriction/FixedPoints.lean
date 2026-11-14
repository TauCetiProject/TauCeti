/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.Invariant.ModuleDescent
public import TauCeti.RingTheory.Smooth.FixedPointIdeal
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Fixed-point subschemes of Weil restrictions and Edixhoven's tame descent

Let `B` be a finite projective `A`-algebra, `C` a finitely presented `B`-algebra, and `Γ` a monoid
acting on `B` (`ρB : Γ →* (B ≃ₐ[A] B)`) and `ρB`-semilinearly on `C` (`ρC : Γ →* RingAut C`). Via
`mulSemiringActionOfInduced`, `Γ` acts on `WeilRestriction A B C` by `A`-algebra automorphisms.
This file studies `(Res_{B/A} Spec C)^Γ` with coordinate ring
`WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h`:

1. **Functor of points (`fixedPointQuotientHomEquiv`)**: `A`-algebra maps into `T` correspond to
   `Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`.
2. **Trivial action (`fixedPointIdealOfInduced_eq_bot`, `fixedPointQuotientAlgEquivOfTrivial`)**:
   when `ρB = 1` and `ρC = 1`, the quotient is canonically `WeilRestriction A B C`.
3. **Edixhoven's smoothness theorem (`formallySmooth_quotient_fixedPointIdealOfInduced`,
   `smooth_quotient_fixedPointIdealOfInduced`)**: when `Γ` is a group with `(Nat.card Γ : A)`
   invertible in `A` and `C` is formally smooth (resp. smooth) over `B`, the fixed-point quotient is
   formally smooth (resp. smooth) over `A`. Since `B` need only be finite projective (not étale),
   this covers Galois extensions of DVRs whose Galois group has order invertible in `A` (e.g.
   totally tamely ramified Galois extensions).
4. **Tame Galois descent (`counitFixedPointQuotient`,
   `fixedPointQuotientBaseChangeAlgEquivOfTraceOne`, `fixedPointQuotientBaseChangeAlgEquiv`)**:
   when `A → B` is injective with `B^Γ = A` and `|Γ|` is invertible in `A` (or `B` has a trace-`1`
   element), `(Res_{B/A} (B ⊗[A] D))^Γ ≃ D` for every finitely presented `A`-algebra `D`. The
   affine-line specialization lives in `TauCeti.RingTheory.WeilRestriction.Polynomial`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.fixedPointIdealOfInduced`, `fixedPointQuotientHomEquiv`,
  `fixedPointQuotientAlgEquivOfTrivial`, `mapFixedPointQuotient`, and
  `mapFixedPointQuotientAlgEquiv`.
* `TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdealOfInduced` and
  `smooth_quotient_fixedPointIdealOfInduced`.
* `TauCeti.Algebra.WeilRestriction.counitFixedPointQuotient`,
  `fixedPointQuotientBaseChangeAlgEquivOfTraceOne`, and `fixedPointQuotientBaseChangeAlgEquiv`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4, p. 292 and
  Propositions 3.1 and 3.4, pp. 293–295.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), Proposition 1.3.3, pp. 142–143.
-/

public noncomputable section

open Algebra TensorProduct
open TauCeti.Algebra.TensorProduct

namespace TauCeti.Algebra.WeilRestriction

section InducedFixedPoints

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The **fixed-point ideal** of `WeilRestriction A B C` under the semilinearly induced `Γ`-action,
cutting out `(Res_{B/A} Spec C)^Γ`. -/
def fixedPointIdealOfInduced : Ideal (WeilRestriction A B C) :=
  letI := mulSemiringActionOfInduced ρB ρC h
  MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)

/-- Unfolding `fixedPointIdealOfInduced` as `MulSemiringAction.fixedPointIdeal`. -/
theorem fixedPointIdealOfInduced_def :
    fixedPointIdealOfInduced ρB ρC h =
      @MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) _ _
        (mulSemiringActionOfInduced ρB ρC h) := (rfl)

/-- **Universal property on points.** An `A`-algebra map `g : WeilRestriction A B C →ₐ[A] T` kills
`fixedPointIdealOfInduced ρB ρC h` iff `homEquiv A B C T g` is `Γ`-equivariant. -/
theorem fixedPointIdealOfInduced_le_ker_algHom_iff {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    fixedPointIdealOfInduced ρB ρC h ≤ RingHom.ker g ↔
      ∀ (γ : Γ) (c : C), homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  rw [fixedPointIdealOfInduced_def, MulSemiringAction.fixedPointIdeal_le_ker_algHom_iff]
  exact forall_congr' fun γ ↦ by rw [toAlgHom_mulSemiringActionOfInduced, comp_inducedAction_eq_iff]

/-- **Functor of points of `(Res_{B/A} Spec C)^Γ`.** `A`-algebra maps into `T` correspond to
`Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointQuotientHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    ((WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
        y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  letI := mulSemiringActionOfInduced ρB ρC h
  haveI := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  (MulSemiringAction.fixedPointQuotientAlgHomEquiv A Γ (WeilRestriction A B C) T).trans
    ((homEquiv A B C T).subtypeEquiv fun _ ↦ forall_congr' fun _ ↦ by
      rw [toAlgHom_mulSemiringActionOfInduced, comp_inducedAction_eq_iff])

/-- Evaluating `fixedPointQuotientHomEquiv` precomposes with `mkₐ` before applying `homEquiv`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (ψ : (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A] T) :
    (fixedPointQuotientHomEquiv ρB ρC h T ψ : C →ₐ[B] B ⊗[A] T) =
      homEquiv A B C T (ψ.comp (Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC h))) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  exact congrArg (homEquiv A B C T)
    (MulSemiringAction.fixedPointQuotientAlgHomEquiv_apply (R := A) (Γ := Γ) ψ)

/-- Precomposing `(fixedPointQuotientHomEquiv ...).symm y` with `mkₐ` recovers
`(homEquiv A B C T).symm y.1`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_symm_comp_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
      y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    ((fixedPointQuotientHomEquiv ρB ρC h T).symm y).comp
        (Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC h)) =
      (homEquiv A B C T).symm y.1 := by
  refine (homEquiv A B C T).injective ?_
  rw [← fixedPointQuotientHomEquiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Trivial action check.** When `ρB = 1` and `ρC = 1`, `fixedPointIdealOfInduced` vanishes. -/
theorem fixedPointIdealOfInduced_eq_bot (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdealOfInduced ρB ρC h = ⊥ := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  rw [fixedPointIdealOfInduced_def, MulSemiringAction.fixedPointIdeal_eq_bot_iff]
  intro γ x
  rw [smul_mulSemiringActionOfInduced, inducedAction_eq_one ρB ρC h hB hC,
    MonoidHom.one_apply, AlgEquiv.one_apply]

/-- **Trivial action equivalence.** When `ρB = 1` and `ρC = 1`, the fixed-point quotient is
canonically isomorphic to `WeilRestriction A B C`. -/
def fixedPointQuotientAlgEquivOfTrivial (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointIdealOfInduced_eq_bot ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- Under `fixedPointQuotientAlgEquivOfTrivial`, the coset of `x` maps to `x`. -/
@[simp]
theorem fixedPointQuotientAlgEquivOfTrivial_mk (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    fixedPointQuotientAlgEquivOfTrivial ρB ρC h hB hC
        (Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC h) x) = x := (rfl)

/-- The inverse of `fixedPointQuotientAlgEquivOfTrivial` is the quotient map. -/
@[simp]
theorem fixedPointQuotientAlgEquivOfTrivial_symm_apply (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (fixedPointQuotientAlgEquivOfTrivial ρB ρC h hB hC).symm x =
      Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC h) x :=
  (fixedPointQuotientAlgEquivOfTrivial ρB ρC h hB hC).symm_apply_eq.mpr
    (fixedPointQuotientAlgEquivOfTrivial_mk ρB ρC h hB hC x).symm

/-- For finite `Γ`, `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is finitely presented
over `A`. -/
instance finitePresentation_quotient_fixedPointIdealOfInduced [Finite Γ] :
    FinitePresentation A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  exact MulSemiringAction.finitePresentation_quotient_fixedPointIdeal

end InducedFixedPoints

section Smoothness

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions.** -/
theorem formallySmooth_quotient_fixedPointIdealOfInduced [FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  exact MulSemiringAction.formallySmooth_quotient_fixedPointIdeal hΓ

/-- **Edixhoven's smoothness theorem for Weil restrictions.** -/
theorem smooth_quotient_fixedPointIdealOfInduced [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClass_mulSemiringActionOfInduced ρB ρC h
  exact MulSemiringAction.smooth_quotient_fixedPointIdeal hΓ

end Smoothness

section Functoriality

variable {A B C C' C'' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing C'] [CommRing C'']
  [Algebra A B] [Algebra B C] [Algebra B C'] [Algebra B C'']
  [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C] [FinitePresentation B C'] [FinitePresentation B C'']
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
  (ρC : Γ →* RingAut C) (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
  (ρC' : Γ →* RingAut C') (h' : ∀ γ b, ρC' γ (algebraMap B C' b) = algebraMap B C' (ρB γ b))

/-- A `Γ`-equivariant `B`-algebra map `φ : C →ₐ[B] C'` induces an `A`-algebra map between
fixed-point quotients of Weil restrictions. -/
def mapFixedPointQuotient (φ : C →ₐ[B] C') (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c)) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A]
      (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h') :=
  Ideal.Quotient.liftₐ (fixedPointIdealOfInduced ρB ρC h)
    ((Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC' h')).comp (map A B φ))
    fun _ hx ↦ RingHom.mem_ker.mp <| (fixedPointIdealOfInduced_le_ker_algHom_iff ρB ρC h _).mpr
      (fun γ c ↦ by
        have hmk := (fixedPointQuotientHomEquiv ρB ρC' h' _
          (AlgHom.id A (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h'))).2 γ (φ c)
        simp only [fixedPointQuotientHomEquiv_apply, AlgHom.id_comp] at hmk
        rw [homEquiv_comp_map, AlgHom.comp_apply, AlgHom.comp_apply, hφ, hmk]) hx

/-- `mapFixedPointQuotient` acts on cosets through `WeilRestriction.map`. -/
@[simp]
theorem mapFixedPointQuotient_mk (φ : C →ₐ[B] C')
    (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c)) (x : WeilRestriction A B C) :
    mapFixedPointQuotient ρB ρC h ρC' h' φ hφ
        (Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC h) x) =
      Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC' h') (map A B φ x) := (rfl)

/-- `mapFixedPointQuotient` sends `AlgHom.id B C` to the identity `A`-algebra map. -/
@[simp]
theorem mapFixedPointQuotient_id
    (hid : ∀ (γ : Γ) (c : C), AlgHom.id B C (ρC γ c) = ρC γ (AlgHom.id B C c) := fun _ _ ↦ rfl) :
    mapFixedPointQuotient ρB ρC h ρC h (AlgHom.id B C) hid =
      AlgHom.id A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) :=
  Ideal.Quotient.algHom_ext A <| AlgHom.ext fun _ ↦ by
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
      mapFixedPointQuotient_mk, map_id]

/-- `mapFixedPointQuotient` respects composition of `Γ`-equivariant `B`-algebra maps. -/
theorem mapFixedPointQuotient_comp
    (ρC'' : Γ →* RingAut C'') (h'' : ∀ γ b, ρC'' γ (algebraMap B C'' b) = algebraMap B C'' (ρB γ b))
    (φ : C →ₐ[B] C') (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c))
    (ψ : C' →ₐ[B] C'') (hψ : ∀ (γ : Γ) (c' : C'), ψ (ρC' γ c') = ρC'' γ (ψ c')) :
    (mapFixedPointQuotient ρB ρC' h' ρC'' h'' ψ hψ).comp
        (mapFixedPointQuotient ρB ρC h ρC' h' φ hφ) =
      mapFixedPointQuotient ρB ρC h ρC'' h'' (ψ.comp φ)
        (fun γ c ↦ by rw [AlgHom.comp_apply, AlgHom.comp_apply, hφ, hψ]) :=
  Ideal.Quotient.algHom_ext A <| AlgHom.ext fun _ ↦ by
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapFixedPointQuotient_mk]
    rw [← AlgHom.comp_apply, ← map_comp]

private theorem mapFixedPointQuotient_congr {φ φ' : C →ₐ[B] C'} (heq : φ = φ')
    (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c)) :
    mapFixedPointQuotient ρB ρC h ρC' h' φ hφ =
      mapFixedPointQuotient ρB ρC h ρC' h' φ' (heq ▸ hφ) := by subst heq; rfl

/-- A `Γ`-equivariant `B`-algebra isomorphism `e : C ≃ₐ[B] C'` induces an `A`-algebra isomorphism
between the fixed-point quotients of `WeilRestriction A B C` and `WeilRestriction A B C'`. -/
def mapFixedPointQuotientAlgEquiv (e : C ≃ₐ[B] C')
    (he : ∀ (γ : Γ) (c : C), e (ρC γ c) = ρC' γ (e c)) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) ≃ₐ[A]
      (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h') :=
  have hφ (γ : Γ) (c : C) : e.toAlgHom (ρC γ c) = ρC' γ (e.toAlgHom c) := he γ c
  have hψ (γ : Γ) (c' : C') : e.symm.toAlgHom (ρC' γ c') = ρC γ (e.symm.toAlgHom c') :=
    e.injective (by rw [AlgEquiv.coe_toAlgHom, e.apply_symm_apply, he, e.apply_symm_apply])
  AlgEquiv.ofAlgHom
    (mapFixedPointQuotient ρB ρC h ρC' h' e.toAlgHom hφ)
    (mapFixedPointQuotient ρB ρC' h' ρC h e.symm.toAlgHom hψ)
    (by rw [mapFixedPointQuotient_comp, mapFixedPointQuotient_congr ρB ρC' h' ρC' h'
          (AlgHom.ext e.apply_symm_apply : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id B C'),
          mapFixedPointQuotient_id])
    (by rw [mapFixedPointQuotient_comp, mapFixedPointQuotient_congr ρB ρC h ρC h
          (AlgHom.ext e.symm_apply_apply : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id B C),
          mapFixedPointQuotient_id])

/-- The forward map of `mapFixedPointQuotientAlgEquiv` is `mapFixedPointQuotient`. -/
@[simp]
theorem mapFixedPointQuotientAlgEquiv_apply (e : C ≃ₐ[B] C')
    (he : ∀ (γ : Γ) (c : C), e (ρC γ c) = ρC' γ (e c))
    (q : WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) :
    mapFixedPointQuotientAlgEquiv ρB ρC h ρC' h' e he q =
      mapFixedPointQuotient ρB ρC h ρC' h' e.toAlgHom
        (fun γ c ↦ by rw [AlgEquiv.coe_toAlgHom]; exact he γ c) q := (rfl)

/-- On cosets, `mapFixedPointQuotientAlgEquiv` applies `WeilRestriction.map A B e.toAlgHom`.
Not `@[simp]` because `_apply` and `mapFixedPointQuotient_mk` already simplify the LHS. -/
theorem mapFixedPointQuotientAlgEquiv_mk (e : C ≃ₐ[B] C')
    (he : ∀ (γ : Γ) (c : C), e (ρC γ c) = ρC' γ (e c)) (x : WeilRestriction A B C) :
    mapFixedPointQuotientAlgEquiv ρB ρC h ρC' h' e he
        (Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC h) x) =
      Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC' h') (map A B e.toAlgHom x) := (rfl)

/-- The inverse of `mapFixedPointQuotientAlgEquiv` is `mapFixedPointQuotientAlgEquiv` of `e.symm`.
-/
@[simp]
theorem mapFixedPointQuotientAlgEquiv_symm (e : C ≃ₐ[B] C')
    (he : ∀ (γ : Γ) (c : C), e (ρC γ c) = ρC' γ (e c)) :
    (mapFixedPointQuotientAlgEquiv ρB ρC h ρC' h' e he).symm =
      mapFixedPointQuotientAlgEquiv ρB ρC' h' ρC h e.symm
        (fun γ c' ↦ e.injective (by rw [e.apply_symm_apply, he, e.apply_symm_apply])) :=
  AlgEquiv.ext fun _ ↦ rfl

end Functoriality

section BaseChangeDescent

section TraceOne

variable (A B D Γ : Type*) [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation A D]

private abbrev baseChangeFixedPointIdeal : Ideal (WeilRestriction A B (B ⊗[A] D)) :=
  fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)

private abbrev BaseChangeQuotient : Type _ :=
  WeilRestriction A B (B ⊗[A] D) ⧸ baseChangeFixedPointIdeal A B D Γ

/-- The canonical `A`-algebra map `(Res_{B/A} Spec (B ⊗[A] D))^Γ →ₐ[A] D` classified under
`fixedPointQuotientHomEquiv` by `AlgHom.id B (B ⊗[A] D)`. -/
def counitFixedPointQuotient :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) →ₐ[A] D :=
  (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ) D).symm
    ⟨AlgHom.id B (B ⊗[A] D), fun γ z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul b d => simp
      | add x y hx hy => simp only [AlgHom.id_apply, map_add] at hx hy ⊢; rw [hx, hy]⟩

/-- Under `fixedPointQuotientHomEquiv`, `counitFixedPointQuotient` classifies `AlgHom.id`.
Not `@[simp]` because `fixedPointQuotientHomEquiv_apply` and `counitFixedPointQuotient_comp_mk`
already simplify the LHS. -/
theorem fixedPointQuotientHomEquiv_counitFixedPointQuotient :
    (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
      (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ) D
      (counitFixedPointQuotient A B D Γ) : B ⊗[A] D →ₐ[B] B ⊗[A] D) =
      AlgHom.id B (B ⊗[A] D) := by
  rw [counitFixedPointQuotient, Equiv.apply_symm_apply]

/-- Precomposing `counitFixedPointQuotient` with `mkₐ` gives the adjunction counit. -/
@[simp]
theorem counitFixedPointQuotient_comp_mk :
    (counitFixedPointQuotient A B D Γ).comp
        (Ideal.Quotient.mkₐ A
          (fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
            (baseChangeSemilinearAction A B D Γ)
            (baseChangeSemilinearAction_algebraMap A B D Γ))) =
      (homEquiv A B (B ⊗[A] D) D).symm (AlgHom.id B (B ⊗[A] D)) := by
  rw [counitFixedPointQuotient, fixedPointQuotientHomEquiv_symm_comp_mk]

variable [Fintype Γ] [FaithfulSMul A B] [Algebra.IsInvariant A B Γ]

private def unitFixedPointQuotientLinearMap (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    D →ₗ[A] BaseChangeQuotient A B D Γ :=
  haveI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  let uQ := fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
    (BaseChangeQuotient A B D Γ) (AlgHom.id A _)
  (MulSemiringAction.invariantsBaseChangeEquiv A B Γ _ hc).symm.toLinearMap ∘ₗ
    (((uQ.1.restrictScalars A).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := D))).toLinearMap.codRestrict
      (Representation.ofDistribMulAction A Γ (B ⊗[A] BaseChangeQuotient A B D Γ)).invariants
      fun d ↦ (Representation.mem_invariants _ _).mpr fun γ ↦ by
        simp only [Representation.ofDistribMulAction_apply_apply, AlgHom.toLinearMap_apply,
          AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
        have hr (w : B ⊗[A] BaseChangeQuotient A B D Γ) :
            Algebra.TensorProduct.rTensor _ (MulSemiringAction.toAlgAut Γ A B γ : B →ₐ[A] B) w =
              γ • w := by
          induction w using TensorProduct.inductionOn with
          | tmul b q => simp [TensorProduct.smul_tmul']
          | add _ _ hx hy => rw [map_add, smul_add, hx, hy]
        rw [← hr, ← uQ.2 γ (1 ⊗ₜ[A] d), baseChangeSemilinearAction_tmul, smul_one])

private theorem one_tmul_unitFixedPointQuotientLinearMap (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (d : D) :
    (1 : B) ⊗ₜ[A] unitFixedPointQuotientLinearMap A B D Γ hc d =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
        _ (AlgHom.id A _)).1 (1 ⊗ₜ[A] d) := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  let eInv := MulSemiringAction.invariantsBaseChangeEquiv A B Γ (BaseChangeQuotient A B D Γ) hc
  dsimp only [unitFixedPointQuotientLinearMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  exact (MulSemiringAction.coe_invariantsBaseChangeEquiv_apply hc _).symm.trans
    (congrArg Subtype.val (eInv.apply_symm_apply _))

private theorem unitFixedPointQuotientLinearMap_map_mul (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (d₁ d₂ : D) :
    unitFixedPointQuotientLinearMap A B D Γ hc (d₁ * d₂) =
      unitFixedPointQuotientLinearMap A B D Γ hc d₁ *
        unitFixedPointQuotientLinearMap A B D Γ hc d₂ := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  refine (MulSemiringAction.invariantsBaseChangeEquiv A B Γ _ hc).injective <| Subtype.ext ?_
  simpa only [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply] using
    calc (1 : B) ⊗ₜ[A] unitFixedPointQuotientLinearMap A B D Γ hc (d₁ * d₂)
        = (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
            (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
            _ (AlgHom.id A _)).1 ((1 : B) ⊗ₜ[A] d₁ * (1 : B) ⊗ₜ[A] d₂) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            one_tmul_unitFixedPointQuotientLinearMap]
      _ = (1 : B) ⊗ₜ[A] (unitFixedPointQuotientLinearMap A B D Γ hc d₁ *
            unitFixedPointQuotientLinearMap A B D Γ hc d₂) := by
          rw [map_mul, ← one_tmul_unitFixedPointQuotientLinearMap,
            ← one_tmul_unitFixedPointQuotientLinearMap, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul]

private def unitFixedPointQuotient (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    D →ₐ[A] BaseChangeQuotient A B D Γ :=
  haveI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  AlgHom.ofLinearMap (unitFixedPointQuotientLinearMap A B D Γ hc)
    ((MulSemiringAction.invariantsBaseChangeEquiv A B Γ _ hc).injective <| Subtype.ext <| by
      simpa only [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply] using by
        rw [one_tmul_unitFixedPointQuotientLinearMap, ← Algebra.TensorProduct.one_def, map_one,
          Algebra.TensorProduct.one_def])
    (unitFixedPointQuotientLinearMap_map_mul A B D Γ hc)

private theorem counitFixedPointQuotient_comp_unitFixedPointQuotient
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (counitFixedPointQuotient A B D Γ).comp (unitFixedPointQuotient A B D Γ hc) =
      AlgHom.id A D := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  refine AlgHom.ext fun d ↦
    (MulSemiringAction.invariantsBaseChangeEquiv A B Γ D hc).injective <| Subtype.ext ?_
  simpa only [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply, AlgHom.comp_apply,
    AlgHom.id_apply] using
    calc (1 : B) ⊗ₜ[A] counitFixedPointQuotient A B D Γ (unitFixedPointQuotient A B D Γ hc d)
        = Algebra.TensorProduct.lTensor B (counitFixedPointQuotient A B D Γ)
            ((1 : B) ⊗ₜ[A] unitFixedPointQuotient A B D Γ hc d) :=
          (Algebra.TensorProduct.map_tmul (AlgHom.id B B) (counitFixedPointQuotient A B D Γ)
            1 _).symm
      _ = Algebra.TensorProduct.lTensor B (counitFixedPointQuotient A B D Γ)
            (homEquiv A B (B ⊗[A] D) _ (Ideal.Quotient.mkₐ A (baseChangeFixedPointIdeal A B D Γ))
              (1 ⊗ₜ[A] d)) := by
          rw [unitFixedPointQuotient, AlgHom.ofLinearMap_apply,
            one_tmul_unitFixedPointQuotientLinearMap, fixedPointQuotientHomEquiv_apply,
            AlgHom.id_comp]
      _ = (1 : B) ⊗ₜ[A] d := by
          rw [← AlgHom.comp_apply, ← homEquiv_comp, counitFixedPointQuotient_comp_mk,
            Equiv.apply_symm_apply, AlgHom.id_apply]

private theorem unitFixedPointQuotient_comp_counitFixedPointQuotient
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (unitFixedPointQuotient A B D Γ hc).comp (counitFixedPointQuotient A B D Γ) =
      AlgHom.id A (BaseChangeQuotient A B D Γ) := by
  refine Ideal.Quotient.algHom_ext A <|
    (homEquiv A B (B ⊗[A] D) _).injective <| AlgHom.ext fun z ↦ ?_
  rw [AlgHom.comp_assoc, AlgHom.id_comp]
  have h1 (d : D) :
      homEquiv A B (B ⊗[A] D) _
          ((unitFixedPointQuotient A B D Γ hc).comp ((counitFixedPointQuotient A B D Γ).comp
            (Ideal.Quotient.mkₐ A (baseChangeFixedPointIdeal A B D Γ)))) (1 ⊗ₜ[A] d) =
        homEquiv A B (B ⊗[A] D) _ (Ideal.Quotient.mkₐ A (baseChangeFixedPointIdeal A B D Γ))
          (1 ⊗ₜ[A] d) := by
    rw [homEquiv_comp, AlgHom.comp_apply, counitFixedPointQuotient_comp_mk, Equiv.apply_symm_apply,
      AlgHom.id_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, unitFixedPointQuotient,
      AlgHom.ofLinearMap_apply, one_tmul_unitFixedPointQuotientLinearMap,
      fixedPointQuotientHomEquiv_apply, AlgHom.id_comp]
  induction z using TensorProduct.inductionOn with
  | add _ _ hx hy => rw [map_add, map_add, hx, hy]
  | tmul b d =>
    have hbd : b ⊗ₜ[A] d = algebraMap B (B ⊗[A] D) b * (1 ⊗ₜ[A] d) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hbd, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, h1]

/-- **Galois descent of base-changed Weil restrictions (trace-`1` form).** -/
def fixedPointQuotientBaseChangeAlgEquivOfTraceOne (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) ≃ₐ[A] D :=
  AlgEquiv.ofAlgHom (counitFixedPointQuotient A B D Γ) (unitFixedPointQuotient A B D Γ hc)
    (counitFixedPointQuotient_comp_unitFixedPointQuotient A B D Γ hc)
    (unitFixedPointQuotient_comp_counitFixedPointQuotient A B D Γ hc)

/-- The forward map of `fixedPointQuotientBaseChangeAlgEquivOfTraceOne` is
`counitFixedPointQuotient`. -/
@[simp]
theorem fixedPointQuotientBaseChangeAlgEquivOfTraceOne_apply (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (q : WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ)
        (baseChangeSemilinearAction_algebraMap A B D Γ)) :
    fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc q =
      counitFixedPointQuotient A B D Γ q := (rfl)

/-- The underlying `AlgHom` of `fixedPointQuotientBaseChangeAlgEquivOfTraceOne` is
`counitFixedPointQuotient`. -/
@[simp]
theorem fixedPointQuotientBaseChangeAlgEquivOfTraceOne_toAlgHom
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc).toAlgHom =
      counitFixedPointQuotient A B D Γ := (rfl)

/-- Under `fixedPointQuotientHomEquiv`, `fixedPointQuotientBaseChangeAlgEquivOfTraceOne` classifies
`AlgHom.id B (B ⊗[A] D)`. Not `@[simp]` because `_toAlgHom` already reduces the LHS. -/
theorem fixedPointQuotientHomEquiv_fixedPointQuotientBaseChangeAlgEquivOfTraceOne
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
      (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ) D
      (fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc).toAlgHom :
        B ⊗[A] D →ₐ[B] B ⊗[A] D) = AlgHom.id B (B ⊗[A] D) := by simp

/-- Characterizes `(fixedPointQuotientBaseChangeAlgEquivOfTraceOne ...).symm` via `1 ⊗ₜ ·`. -/
@[simp]
theorem one_tmul_fixedPointQuotientBaseChangeAlgEquivOfTraceOne_symm
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (d : D) :
    (1 : B) ⊗ₜ[A] (fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc).symm d =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
        _ (AlgHom.id A _)).1 (1 ⊗ₜ[A] d) :=
  one_tmul_unitFixedPointQuotientLinearMap A B D Γ hc d

end TraceOne

section TameDescent

variable (A B D Γ : Type*) [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]
  [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation A D] [FaithfulSMul A B] [Algebra.IsInvariant A B Γ]

private theorem bijective_counitFixedPointQuotient (hΓ : IsUnit (Nat.card Γ : A)) :
    Function.Bijective (counitFixedPointQuotient A B D Γ) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton D := Module.subsingleton A D
    have : Subsingleton (BaseChangeQuotient A B D Γ) := Module.subsingleton A _
    exact Function.bijective_iff_has_inverse.mpr
      ⟨0, fun _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩
  · have : Finite Γ := finite_of_natCast_card_ne_zero hΓ.ne_zero
    cases nonempty_fintype Γ
    exact (fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ
      (MulSemiringAction.exists_sum_smul_eq_one_of_isUnit_card hΓ)).bijective

/-- **Tame Galois descent of base-changed Weil restrictions.** When `A → B` is injective with
`B^Γ = A` and `(Nat.card Γ : A)` is invertible in `A`, `(Res_{B/A} (B ⊗[A] D))^Γ ≃ D` for every
finitely presented `A`-algebra `D`. -/
def fixedPointQuotientBaseChangeAlgEquiv (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) ≃ₐ[A] D :=
  AlgEquiv.ofBijective (counitFixedPointQuotient A B D Γ)
    (bijective_counitFixedPointQuotient A B D Γ hΓ)

/-- The forward map of `fixedPointQuotientBaseChangeAlgEquiv` is `counitFixedPointQuotient`. -/
@[simp]
theorem fixedPointQuotientBaseChangeAlgEquiv_apply (hΓ : IsUnit (Nat.card Γ : A))
    (q : WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ)
        (baseChangeSemilinearAction_algebraMap A B D Γ)) :
    fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ q = counitFixedPointQuotient A B D Γ q := (rfl)

/-- The underlying `AlgHom` of `fixedPointQuotientBaseChangeAlgEquiv` is `counitFixedPointQuotient`.
-/
@[simp]
theorem fixedPointQuotientBaseChangeAlgEquiv_toAlgHom (hΓ : IsUnit (Nat.card Γ : A)) :
    (fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ).toAlgHom =
      counitFixedPointQuotient A B D Γ := AlgHom.ext fun _ ↦ rfl

/-- Under `fixedPointQuotientHomEquiv`, `fixedPointQuotientBaseChangeAlgEquiv` classifies
`AlgHom.id B (B ⊗[A] D)`. Not `@[simp]` because `_toAlgHom` already reduces the LHS. -/
theorem fixedPointQuotientHomEquiv_fixedPointQuotientBaseChangeAlgEquiv
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
      (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ) D
      (fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ).toAlgHom :
        B ⊗[A] D →ₐ[B] B ⊗[A] D) = AlgHom.id B (B ⊗[A] D) := by simp

/-- Characterizes `(fixedPointQuotientBaseChangeAlgEquiv ...).symm` via `1 ⊗ₜ ·`. -/
@[simp]
theorem one_tmul_fixedPointQuotientBaseChangeAlgEquiv_symm
    (hΓ : IsUnit (Nat.card Γ : A)) (d : D) :
    (1 : B) ⊗ₜ[A] (fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ).symm d =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
        _ (AlgHom.id A _)).1 (1 ⊗ₜ[A] d) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton (B ⊗[A] BaseChangeQuotient A B D Γ) := Module.subsingleton A _
    exact Subsingleton.elim _ _
  · have : Finite Γ := finite_of_natCast_card_ne_zero hΓ.ne_zero
    cases nonempty_fintype Γ
    let hc := MulSemiringAction.exists_sum_smul_eq_one_of_isUnit_card (B := B) hΓ
    have hEq : (fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ).symm d =
        (fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc).symm d :=
      (fixedPointQuotientBaseChangeAlgEquiv A B D Γ hΓ).injective <| by
        rw [AlgEquiv.apply_symm_apply, fixedPointQuotientBaseChangeAlgEquiv_apply,
          ← fixedPointQuotientBaseChangeAlgEquivOfTraceOne_apply A B D Γ hc,
          AlgEquiv.apply_symm_apply]
    rw [hEq, one_tmul_fixedPointQuotientBaseChangeAlgEquivOfTraceOne_symm]

end TameDescent

end BaseChangeDescent

end TauCeti.Algebra.WeilRestriction
