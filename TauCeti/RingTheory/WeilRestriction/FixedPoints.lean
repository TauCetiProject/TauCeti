/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.Invariant.ModuleDescent
public import TauCeti.RingTheory.Smooth.FixedPointIdeal
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth

/-!
# Fixed-point subschemes of Weil restrictions and Edixhoven's tame descent

Let `B` be a finite projective `A`-algebra, `C` a finitely presented `B`-algebra, and `Γ` a monoid
acting on `B` by `A`-algebra automorphisms (`ρB : Γ →* (B ≃ₐ[A] B)`) and on `C` by `ρB`-semilinear
ring automorphisms (`ρC : Γ →* RingAut C`). By `TauCeti.Algebra.WeilRestriction.inducedAction`, `Γ`
acts on `WeilRestriction A B C` by `A`-algebra automorphisms.

This file studies the **fixed-point closed subscheme** `(Res_{B/A} Spec C)^Γ`, whose coordinate
`A`-algebra is `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h`:

1. **Functor of points (`fixedPointQuotientHomEquiv`).** For any commutative `A`-algebra `T`,
   `A`-algebra homomorphisms `(WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A] T`
   are in natural bijection with `Γ`-equivariant `B`-algebra homomorphisms `y : C →ₐ[B] B ⊗[A] T`,
   i.e. those satisfying `y (ρC γ c) = (ρB γ ⊗ id_T) (y c)` for all `γ : Γ` and `c : C`.
2. **Trivial action (`fixedPointIdealOfInduced_eq_bot`, `fixedPointQuotientAlgEquivOfTrivial`).**
   When `ρB = 1` and `ρC = 1`, the fixed-point ideal vanishes and the fixed-point quotient is
   canonically isomorphic to `WeilRestriction A B C`.
3. **Edixhoven's tame smoothness theorem for Weil restrictions
   (`formallySmooth_quotient_fixedPointIdealOfInduced`,
   `smooth_quotient_fixedPointIdealOfInduced`).** When `Γ` is a group whose order `(Nat.card Γ : A)`
   is invertible in `A` and `C` is formally smooth (respectively smooth) over `B`, the fixed-point
   quotient `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is formally smooth
   (respectively smooth) over `A`. Notice that `B` need not be étale over `A` — only finite
   projective — so this applies directly to Weil restrictions of smooth models along tamely ramified
   extensions of discrete valuation rings.
4. **Tame Galois descent of base-changed Weil restrictions (`fixedPointQuotientBaseChangeAlgEquiv`,
   `fixedPointQuotientPolynomialAlgEquiv`).** When `A → B` is injective with `B^Γ = A` and `|Γ|` is
   invertible in `A` (or more generally `B` admits an element of trace `1`), taking `Γ`-fixed points
   of `WeilRestriction A B (B ⊗[A] D)` recovers `D` for any finitely presented `A`-algebra `D`; in
   particular, `(Res_{B/A} 𝔸¹_B)^Γ ≃ 𝔸¹_A` (`fixedPointQuotientPolynomialAlgEquiv`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointIdealOfInduced`: the fixed-point ideal of the induced
  `Γ`-action on `WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientHomEquiv`: the point-level universal property
  of `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h`.
* `TauCeti.Algebra.WeilRestriction.mapFixedPointQuotient` and
  `TauCeti.Algebra.WeilRestriction.equivFixedPointQuotientAlgEquiv`: functoriality of the
  fixed-point quotient in `Γ`-equivariant `B`-algebra morphisms and isomorphisms.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientBaseChangeAlgEquiv`: tame descent isomorphism
  `(WeilRestriction A B (B ⊗[A] D) ⧸ fixedPointIdealOfInduced ...) ≃ₐ[A] D`.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientPolynomialAlgEquiv`: tame descent of the affine
  line `(WeilRestriction A B B[X] ⧸ fixedPointIdealOfInduced ...) ≃ₐ[A] A[X]`.

## Main results

* `TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdealOfInduced` and
  `TauCeti.Algebra.WeilRestriction.smooth_quotient_fixedPointIdealOfInduced`: Edixhoven's smoothness
  theorem for `(Res_{B/A} Spec C)^Γ`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4, p. 292 and
  Propositions 3.1 and 3.4, pp. 293–295.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), Proposition 1.3.3, pp. 142–143.
-/

public noncomputable section

open Algebra TensorProduct Polynomial

namespace TauCeti.Algebra.WeilRestriction

section InducedFixedPoints

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- The left `MulSemiringAction` of `Γ` on `WeilRestriction A B C` attached to `inducedAction`. -/
@[instance_reducible]
def mulSemiringActionOfInduced : MulSemiringAction Γ (WeilRestriction A B C) :=
  MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)

/-- Scalar multiplication in `mulSemiringActionOfInduced` applies `inducedAction`. -/
@[simp]
theorem smul_mulSemiringActionOfInduced (γ : Γ) (x : WeilRestriction A B C) :
    letI := mulSemiringActionOfInduced ρB ρC h
    γ • x = inducedAction ρB ρC h γ x :=
  (rfl)

/-- The action `mulSemiringActionOfInduced` commutes with the `A`-module structure on
`WeilRestriction A B C`. -/
theorem smulCommClassOfInduced :
    letI := mulSemiringActionOfInduced ρB ρC h
    SMulCommClass Γ A (WeilRestriction A B C) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  exact ⟨fun γ a x ↦ map_smul (inducedAction ρB ρC h γ) a x⟩

/-- The **fixed-point ideal** of `WeilRestriction A B C` under the semilinearly induced action of
`Γ`. Its quotient `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is the coordinate
`A`-algebra of `(Res_{B/A} Spec C)^Γ`. -/
def fixedPointIdealOfInduced : Ideal (WeilRestriction A B C) :=
  letI := mulSemiringActionOfInduced ρB ρC h
  MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)

/-- Explicit unfolding of `fixedPointIdealOfInduced` as `MulSemiringAction.fixedPointIdeal` for
`mulSemiringActionOfInduced`. -/
theorem fixedPointIdealOfInduced_def :
    fixedPointIdealOfInduced ρB ρC h =
      @MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C) _ _
        (mulSemiringActionOfInduced ρB ρC h) :=
  (rfl)

/-- **Universal property on points.** An `A`-algebra map `g : WeilRestriction A B C →ₐ[A] T` kills
`fixedPointIdealOfInduced ρB ρC h` if and only if the `B`-algebra map `y : C →ₐ[B] B ⊗[A] T` it
classifies is `Γ`-equivariant (`y ∘ ρC γ = (ρB γ ⊗ id_T) ∘ y`). -/
theorem fixedPointIdealOfInduced_le_ker_algHom_iff {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C →ₐ[A] T) :
    fixedPointIdealOfInduced ρB ρC h ≤ RingHom.ker g ↔
      ∀ (γ : Γ) (c : C), homEquiv A B C T g (ρC γ c) =
        Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (homEquiv A B C T g c) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  have htoAlg (γ : Γ) :
      MulSemiringAction.toAlgHom A (WeilRestriction A B C) γ =
        (inducedAction ρB ρC h γ : WeilRestriction A B C →ₐ[A] WeilRestriction A B C) :=
    AlgHom.ext fun _ ↦ rfl
  rw [fixedPointIdealOfInduced_def, MulSemiringAction.fixedPointIdeal_le_ker_algHom_iff]
  exact forall_congr' fun γ ↦ by rw [htoAlg, comp_inducedAction_eq_iff]

/-- **Functor of points of `(Res_{B/A} Spec C)^Γ`.** `A`-algebra maps out of
`WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` into `T` correspond bijectively to
`Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointQuotientHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    ((WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
        y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  letI := mulSemiringActionOfInduced ρB ρC h
  haveI := smulCommClassOfInduced ρB ρC h
  (MulSemiringAction.fixedPointQuotientAlgHomEquiv A Γ (WeilRestriction A B C) T).trans
    ((homEquiv A B C T).subtypeEquiv fun g ↦
      forall_congr' fun γ ↦ by
        have htoAlg :
            MulSemiringAction.toAlgHom A (WeilRestriction A B C) γ =
              (inducedAction ρB ρC h γ : WeilRestriction A B C →ₐ[A] WeilRestriction A B C) :=
          AlgHom.ext fun _ ↦ rfl
        rw [htoAlg, comp_inducedAction_eq_iff])

/-- Evaluating `fixedPointQuotientHomEquiv` precomposes with the quotient map before applying
`homEquiv`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (ψ : (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A] T) :
    (fixedPointQuotientHomEquiv ρB ρC h T ψ : C →ₐ[B] B ⊗[A] T) =
      homEquiv A B C T (ψ.comp (Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC h))) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  exact congrArg (homEquiv A B C T)
    (MulSemiringAction.fixedPointQuotientAlgHomEquiv_apply
      (R := A) (Γ := Γ) (A := WeilRestriction A B C) ψ)

/-- Precomposing `(fixedPointQuotientHomEquiv ...).symm y` with the quotient map recovers
`(homEquiv A B C T).symm y.1`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_symm_comp_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
      y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    ((fixedPointQuotientHomEquiv ρB ρC h T).symm y).comp
        (Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC h)) =
      (homEquiv A B C T).symm y.1 := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  refine AlgHom.ext fun x ↦ ?_
  dsimp only [fixedPointQuotientHomEquiv, fixedPointIdealOfInduced]
  exact MulSemiringAction.fixedPointQuotientAlgHomEquiv_symm_apply_mk (R := A)
    (((homEquiv A B C T).subtypeEquiv _).symm y) x

/-- **Trivial action check.** When `Γ` acts trivially on `B` and `C`, the fixed-point ideal of the
induced action vanishes. -/
theorem fixedPointIdealOfInduced_eq_bot (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdealOfInduced ρB ρC h = ⊥ := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  rw [fixedPointIdealOfInduced_def, MulSemiringAction.fixedPointIdeal_eq_bot_iff]
  intro γ x
  rw [smul_mulSemiringActionOfInduced, inducedAction_eq_one ρB ρC h hB hC,
    MonoidHom.one_apply, AlgEquiv.one_apply]

/-- **Trivial action equivalence.** When `Γ` acts trivially on `B` and `C`, the fixed-point quotient
is canonically isomorphic as an `A`-algebra to `WeilRestriction A B C`. -/
def fixedPointQuotientAlgEquivOfTrivial (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ (fixedPointIdealOfInduced ρB ρC h) (AlgHom.id A (WeilRestriction A B C))
      fun x hx ↦ by
        rw [fixedPointIdealOfInduced_eq_bot ρB ρC h hB hC, Ideal.mem_bot] at hx
        simp [hx])
    (Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC h))
    (AlgHom.ext fun _ ↦ rfl)
    (Ideal.Quotient.algHom_ext A rfl)

/-- When `Γ` is finite, `WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is finitely
presented over `A`. -/
theorem finitePresentation_quotient_fixedPointIdealOfInduced [Finite Γ] :
    FinitePresentation A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  exact MulSemiringAction.finitePresentation_quotient_fixedPointIdeal

end InducedFixedPoints

section Smoothness

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions.** If `C` is formally smooth and
finitely presented over a finite projective `A`-algebra `B`, and a group `Γ` acts on `B` and
semilinearly on `C` with `(Nat.card Γ : A)` invertible in `A`, then the fixed-point quotient
`WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is formally smooth over `A`. -/
theorem formallySmooth_quotient_fixedPointIdealOfInduced [FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  exact MulSemiringAction.formallySmooth_quotient_fixedPointIdeal hΓ

/-- **Edixhoven's smoothness theorem for Weil restrictions.** If `C` is smooth over a finite
projective `A`-algebra `B`, and a group `Γ` acts on `B` and semilinearly on `C` with
`(Nat.card Γ : A)` invertible in `A`, then the fixed-point quotient
`WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h` is smooth over `A`. -/
theorem smooth_quotient_fixedPointIdealOfInduced [Smooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) := by
  let _ := mulSemiringActionOfInduced ρB ρC h
  have _ := smulCommClassOfInduced ρB ρC h
  exact MulSemiringAction.smooth_quotient_fixedPointIdeal hΓ

end Smoothness

section Functoriality

variable {A B C C' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing C']
  [Algebra A B] [Algebra B C] [Algebra B C']
  [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C] [FinitePresentation B C']
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
  (ρC : Γ →* RingAut C) (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))
  (ρC' : Γ →* RingAut C') (h' : ∀ γ b, ρC' γ (algebraMap B C' b) = algebraMap B C' (ρB γ b))

/-- A `Γ`-equivariant `B`-algebra homomorphism `φ : C →ₐ[B] C'` induces an `A`-algebra homomorphism
between the corresponding fixed-point quotients of Weil restrictions. -/
def mapFixedPointQuotient (φ : C →ₐ[B] C')
    (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c)) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) →ₐ[A]
      (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h') :=
  Ideal.Quotient.liftₐ (fixedPointIdealOfInduced ρB ρC h)
    ((Ideal.Quotient.mkₐ A (fixedPointIdealOfInduced ρB ρC' h')).comp (map A B φ))
    fun x hx ↦ RingHom.mem_ker.mp <|
      (fixedPointIdealOfInduced_le_ker_algHom_iff ρB ρC h _).mpr
        (fun γ c ↦ by
          have hmk := (fixedPointQuotientHomEquiv ρB ρC' h' _
            (AlgHom.id A (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h'))).2 γ (φ c)
          simp only [fixedPointQuotientHomEquiv_apply, AlgHom.id_comp] at hmk
          rw [homEquiv_comp_map, AlgHom.comp_apply, AlgHom.comp_apply, hφ, hmk])
        hx

/-- `mapFixedPointQuotient` acts on cosets through `WeilRestriction.map`. -/
@[simp]
theorem mapFixedPointQuotient_mk (φ : C →ₐ[B] C')
    (hφ : ∀ (γ : Γ) (c : C), φ (ρC γ c) = ρC' γ (φ c)) (x : WeilRestriction A B C) :
    mapFixedPointQuotient ρB ρC h ρC' h' φ hφ
        (Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC h) x) =
      Ideal.Quotient.mk (fixedPointIdealOfInduced ρB ρC' h') (map A B φ x) :=
  (rfl)

/-- A `Γ`-equivariant `B`-algebra isomorphism `e : C ≃ₐ[B] C'` induces an `A`-algebra isomorphism
between the fixed-point quotients of `WeilRestriction A B C` and `WeilRestriction A B C'`. -/
def equivFixedPointQuotientAlgEquiv (e : C ≃ₐ[B] C')
    (he : ∀ (γ : Γ) (c : C), e (ρC γ c) = ρC' γ (e c)) :
    (WeilRestriction A B C ⧸ fixedPointIdealOfInduced ρB ρC h) ≃ₐ[A]
      (WeilRestriction A B C' ⧸ fixedPointIdealOfInduced ρB ρC' h') :=
  have hφ (γ : Γ) (c : C) : e.toAlgHom (ρC γ c) = ρC' γ (e.toAlgHom c) := he γ c
  have hψ (γ : Γ) (c' : C') : e.symm.toAlgHom (ρC' γ c') = ρC γ (e.symm.toAlgHom c') :=
    e.injective (by rw [AlgEquiv.coe_toAlgHom, e.apply_symm_apply, he, e.apply_symm_apply])
  have he1 : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id B C' := AlgHom.ext e.apply_symm_apply
  have he2 : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id B C := AlgHom.ext e.symm_apply_apply
  AlgEquiv.ofAlgHom
    (mapFixedPointQuotient ρB ρC h ρC' h' e.toAlgHom hφ)
    (mapFixedPointQuotient ρB ρC' h' ρC h e.symm.toAlgHom hψ)
    (Ideal.Quotient.algHom_ext A <| AlgHom.ext fun x ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapFixedPointQuotient_mk,
        AlgHom.id_apply]
      rw [← AlgHom.comp_apply, ← map_comp, he1, map_id, AlgHom.id_apply])
    (Ideal.Quotient.algHom_ext A <| AlgHom.ext fun x ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapFixedPointQuotient_mk,
        AlgHom.id_apply]
      rw [← AlgHom.comp_apply, ← map_comp, he2, map_id, AlgHom.id_apply])

end Functoriality

section BaseChangeDescent

section SemilinearAction

variable (A B D Γ : Type*) [CommSemiring A] [CommSemiring B] [Semiring D]
  [Algebra A B] [Algebra A D]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

/-- The canonical semilinear action of `Γ` on `B ⊗[A] D` through the left tensor factor
(`γ • (b ⊗ₜ d) = (γ • b) ⊗ₜ d`). -/
def baseChangeSemilinearAction : Γ →* RingAut (B ⊗[A] D) :=
  (MulSemiringAction.toRingAut (B ≃ₐ[A] B) (B ⊗[A] D)).comp (MulSemiringAction.toAlgAut Γ A B)

/-- `baseChangeSemilinearAction` acts on pure tensors via the left tensor factor. -/
@[simp]
theorem baseChangeSemilinearAction_tmul (γ : Γ) (b : B) (d : D) :
    baseChangeSemilinearAction A B D Γ γ (b ⊗ₜ[A] d) = (γ • b) ⊗ₜ[A] d :=
  (rfl)

/-- `baseChangeSemilinearAction` is semilinear with respect to `MulSemiringAction.toAlgAut Γ A B`.
-/
theorem baseChangeSemilinearAction_algebraMap (γ : Γ) (b : B) :
    baseChangeSemilinearAction A B D Γ γ (algebraMap B (B ⊗[A] D) b) =
      algebraMap B (B ⊗[A] D) (MulSemiringAction.toAlgAut Γ A B γ b) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

end SemilinearAction

section TraceOne

variable (A B D Γ : Type*) [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation A D]

private def counitFixedPointQuotient :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) →ₐ[A] D :=
  (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ) D).symm
    ⟨AlgHom.id B (B ⊗[A] D), fun γ z ↦ by
      rw [AlgHom.id_apply, AlgHom.id_apply]
      induction z using TensorProduct.inductionOn with
      | tmul b d => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]⟩

variable [Fintype Γ] [FaithfulSMul A B] [Algebra.IsInvariant A B Γ]

private def unitFixedPointQuotientLinearMap (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    D →ₗ[A]
      (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) :=
  haveI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  let Q := WeilRestriction A B (B ⊗[A] D) ⧸
    fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
      (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
  let uQ := fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
    Q (AlgHom.id A Q)
  (MulSemiringAction.invariantsBaseChangeEquiv A B Γ Q hc).symm.toLinearMap ∘ₗ
    (((uQ.1.restrictScalars A).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := D))).toLinearMap.codRestrict
      (Representation.ofDistribMulAction A Γ (B ⊗[A] Q)).invariants fun d ↦
        (Representation.mem_invariants _ _).mpr fun γ ↦ by
          simp only [Representation.ofDistribMulAction_apply_apply, AlgHom.toLinearMap_apply,
            AlgHom.comp_apply, AlgHom.restrictScalars_apply,
            Algebra.TensorProduct.includeRight_apply]
          have hr (w : B ⊗[A] Q) :
              Algebra.TensorProduct.rTensor Q (MulSemiringAction.toAlgAut Γ A B γ : B →ₐ[A] B) w =
                γ • w := by
            induction w using TensorProduct.inductionOn with
            | tmul b q => simp [TensorProduct.smul_tmul']
            | add x y hx hy => rw [map_add, smul_add, hx, hy]
          rw [← hr, ← uQ.2 γ (1 ⊗ₜ[A] d), baseChangeSemilinearAction_tmul, smul_one])

private theorem one_tmul_unitFixedPointQuotientLinearMap (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (d : D) :
    (1 : B) ⊗ₜ[A] unitFixedPointQuotientLinearMap A B D Γ hc d =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
        _ (AlgHom.id A _)).1 (1 ⊗ₜ[A] d) := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  let Q := WeilRestriction A B (B ⊗[A] D) ⧸
    fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
      (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
  let eInv := MulSemiringAction.invariantsBaseChangeEquiv A B Γ Q hc
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
            (baseChangeSemilinearAction A B D Γ)
            (baseChangeSemilinearAction_algebraMap A B D Γ)
            _ (AlgHom.id A _)).1 ((1 : B) ⊗ₜ[A] d₁ * (1 : B) ⊗ₜ[A] d₂) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
              one_tmul_unitFixedPointQuotientLinearMap]
      _ = ((1 : B) ⊗ₜ[A] unitFixedPointQuotientLinearMap A B D Γ hc d₁) *
            ((1 : B) ⊗ₜ[A] unitFixedPointQuotientLinearMap A B D Γ hc d₂) := by
            rw [map_mul, one_tmul_unitFixedPointQuotientLinearMap,
              one_tmul_unitFixedPointQuotientLinearMap]
      _ = (1 : B) ⊗ₜ[A]
            (unitFixedPointQuotientLinearMap A B D Γ hc d₁ *
              unitFixedPointQuotientLinearMap A B D Γ hc d₂) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private def unitFixedPointQuotient (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    D →ₐ[A]
      (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) :=
  haveI : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  AlgHom.ofLinearMap (unitFixedPointQuotientLinearMap A B D Γ hc)
    ((MulSemiringAction.invariantsBaseChangeEquiv A B Γ _ hc).injective <| Subtype.ext <| by
      simpa only [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply] using by
        rw [one_tmul_unitFixedPointQuotientLinearMap, ← Algebra.TensorProduct.one_def, map_one,
          Algebra.TensorProduct.one_def])
    (unitFixedPointQuotientLinearMap_map_mul A B D Γ hc)

private theorem one_tmul_unitFixedPointQuotient (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (d : D) :
    (1 : B) ⊗ₜ[A] unitFixedPointQuotient A B D Γ hc d =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
        _ (AlgHom.id A _)).1 (1 ⊗ₜ[A] d) :=
  one_tmul_unitFixedPointQuotientLinearMap A B D Γ hc d

private theorem counitFixedPointQuotient_comp_unitFixedPointQuotient
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (counitFixedPointQuotient A B D Γ).comp (unitFixedPointQuotient A B D Γ hc) =
      AlgHom.id A D := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  refine AlgHom.ext fun d ↦
    (MulSemiringAction.invariantsBaseChangeEquiv A B Γ D hc).injective <| Subtype.ext ?_
  let I := fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
  simpa only [MulSemiringAction.coe_invariantsBaseChangeEquiv_apply, AlgHom.comp_apply,
    AlgHom.id_apply] using
    calc (1 : B) ⊗ₜ[A] counitFixedPointQuotient A B D Γ (unitFixedPointQuotient A B D Γ hc d)
        = Algebra.TensorProduct.lTensor B (counitFixedPointQuotient A B D Γ)
            ((1 : B) ⊗ₜ[A] unitFixedPointQuotient A B D Γ hc d) := rfl
      _ = Algebra.TensorProduct.lTensor B (counitFixedPointQuotient A B D Γ)
            (homEquiv A B (B ⊗[A] D) _ (Ideal.Quotient.mkₐ A I) (1 ⊗ₜ[A] d)) := by
            rw [one_tmul_unitFixedPointQuotient, fixedPointQuotientHomEquiv_apply, AlgHom.id_comp]
      _ = homEquiv A B (B ⊗[A] D) D
            ((counitFixedPointQuotient A B D Γ).comp (Ideal.Quotient.mkₐ A I)) (1 ⊗ₜ[A] d) := by
            rw [homEquiv_comp, AlgHom.comp_apply]
      _ = (1 : B) ⊗ₜ[A] d := by
            dsimp only [counitFixedPointQuotient, I]
            rw [fixedPointQuotientHomEquiv_symm_comp_mk, Equiv.apply_symm_apply, AlgHom.id_apply]

private theorem unitFixedPointQuotient_comp_counitFixedPointQuotient
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (unitFixedPointQuotient A B D Γ hc).comp (counitFixedPointQuotient A B D Γ) =
      AlgHom.id A _ := by
  refine Ideal.Quotient.algHom_ext A <|
    (homEquiv A B (B ⊗[A] D) _).injective <| AlgHom.ext fun z ↦ ?_
  let I := fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B D Γ) (baseChangeSemilinearAction_algebraMap A B D Γ)
  rw [AlgHom.comp_assoc, AlgHom.id_comp]
  have h1 (d : D) :
      homEquiv A B (B ⊗[A] D) _
          ((unitFixedPointQuotient A B D Γ hc).comp
            ((counitFixedPointQuotient A B D Γ).comp (Ideal.Quotient.mkₐ A I)))
          (1 ⊗ₜ[A] d) =
        homEquiv A B (B ⊗[A] D) _ (Ideal.Quotient.mkₐ A I) (1 ⊗ₜ[A] d) := by
    rw [homEquiv_comp, AlgHom.comp_apply]
    dsimp only [counitFixedPointQuotient, I]
    rw [fixedPointQuotientHomEquiv_symm_comp_mk, Equiv.apply_symm_apply, AlgHom.id_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, one_tmul_unitFixedPointQuotient,
      fixedPointQuotientHomEquiv_apply, AlgHom.id_comp]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b d =>
    have hbd : b ⊗ₜ[A] d = algebraMap B (B ⊗[A] D) b * (1 ⊗ₜ[A] d) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hbd, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, h1]

/-- **Galois descent of base-changed Weil restrictions (trace-`1` form).** Let a finite group `Γ`
act on a finite projective faithful `A`-algebra `B` with `B^Γ = A` and an element `c : B` of trace
`1`. For any finitely presented `A`-algebra `D`, the fixed-point quotient of
`WeilRestriction A B (B ⊗[A] D)` under the left-factor `Γ`-action is canonically isomorphic to `D`.
-/
def fixedPointQuotientBaseChangeAlgEquivOfTraceOne (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) ≃ₐ[A] D :=
  AlgEquiv.ofAlgHom
    (counitFixedPointQuotient A B D Γ)
    (unitFixedPointQuotient A B D Γ hc)
    (counitFixedPointQuotient_comp_unitFixedPointQuotient A B D Γ hc)
    (unitFixedPointQuotient_comp_counitFixedPointQuotient A B D Γ hc)

end TraceOne

/-- **Tame Galois descent of base-changed Weil restrictions.** Let a group `Γ` act on a finite
projective faithful `A`-algebra `B` with `B^Γ = A` and `(Nat.card Γ : A)` invertible in `A`. Then
for every finitely presented `A`-algebra `D`, the fixed-point quotient of
`WeilRestriction A B (B ⊗[A] D)` is canonically isomorphic to `D` — even when `B` is ramified over
`A`. -/
def fixedPointQuotientBaseChangeAlgEquiv (A B D Γ : Type*) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D]
    [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]
    [Module.Finite A B] [Module.Projective A B]
    [FinitePresentation A D] [FaithfulSMul A B] [Algebra.IsInvariant A B Γ]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (baseChangeSemilinearAction A B D Γ)
          (baseChangeSemilinearAction_algebraMap A B D Γ)) ≃ₐ[A] D := by
  have _ : SMulCommClass A Γ B := SMulCommClass.symm Γ A B
  by_cases hA : Subsingleton A
  · have _ : Subsingleton D := Module.subsingleton A D
    have _ : Subsingleton
        (WeilRestriction A B (B ⊗[A] D) ⧸
          fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
            (baseChangeSemilinearAction A B D Γ)
            (baseChangeSemilinearAction_algebraMap A B D Γ)) := Module.subsingleton A _
    exact default
  · have _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    have _ : Finite Γ := Nat.finite_of_card_ne_zero fun h0 ↦ hΓ.ne_zero (by simp [h0])
    let _ : Fintype Γ := Fintype.ofFinite Γ
    have hc : ∃ c : B, ∑ γ : Γ, γ • c = 1 := by
      refine ⟨((hΓ.unit⁻¹ : Aˣ) : A) • (1 : B), ?_⟩
      have hcard : ((hΓ.unit⁻¹ : Aˣ) : A) * (Fintype.card Γ : A) = 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact Units.inv_mul hΓ.unit
      have hsmul (γ : Γ) :
          γ • (((hΓ.unit⁻¹ : Aˣ) : A) • (1 : B)) = ((hΓ.unit⁻¹ : Aˣ) : A) • (1 : B) := by
        rw [smul_comm, smul_one]
      simp_rw [hsmul]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A, ← mul_smul,
        mul_comm, hcard, one_smul]
    exact fixedPointQuotientBaseChangeAlgEquivOfTraceOne A B D Γ hc

end BaseChangeDescent

section PolynomialDescent

variable (A B Γ : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

/-- **Tame descent of the affine line.** Under the hypotheses of
`fixedPointQuotientBaseChangeAlgEquiv`, the fixed-point quotient of `WeilRestriction A B B[X]`
under the coefficient-wise `Γ`-action is canonically isomorphic to `A[X]`. -/
def fixedPointQuotientPolynomialAlgEquiv
    [Module.Finite A B] [Module.Projective A B]
    [FaithfulSMul A B] [Algebra.IsInvariant A B Γ] (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (MulSemiringAction.toRingAut Γ B[X])
          (fun γ b ↦ by simp)) ≃ₐ[A] A[X] :=
  (equivFixedPointQuotientAlgEquiv (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)
    (baseChangeSemilinearAction A B A[X] Γ) (baseChangeSemilinearAction_algebraMap A B A[X] Γ)
    (polyEquivTensor' A B)
    (fun γ p ↦ by
      have hfg :
          (polyEquivTensor' A B).toAlgHom.toRingHom.comp
              (MulSemiringAction.toRingAut Γ B[X] γ).toRingHom =
            (baseChangeSemilinearAction A B A[X] Γ γ).toRingHom.comp
              (polyEquivTensor' A B).toAlgHom.toRingHom := by
        refine Polynomial.ringHom_ext' ?_ ?_
        · ext b
          simp
        · simp
      exact congr($hfg p))).trans
    (fixedPointQuotientBaseChangeAlgEquiv A B A[X] Γ hΓ)

end PolynomialDescent

end TauCeti.Algebra.WeilRestriction
