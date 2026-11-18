/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth

/-!
# Tame fixed points of Weil restrictions

Let `A → B` be a finite projective homomorphism of commutative rings, `C` a commutative
`B`-algebra, and `Γ` a monoid acting on `B` by `A`-algebra automorphisms `ρB` and semilinearly on
`C` by ring automorphisms `ρC`. The induced action `WeilRestriction.inducedAction ρB ρC h` acts on
`WeilRestriction A B C` by `A`-algebra automorphisms.

This file studies the fixed-point quotient
`WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))`:

1. **Functor of points** (`fixedPointsEquiv`): its `T`-points correspond naturally to
   `Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`.
2. **Smoothness** (`formallySmooth_fixedPoints`, `smooth_fixedPoints`): when `Γ` is a group whose
   order `Nat.card Γ` is a unit in `A` and `C` is formally smooth (resp. smooth) over `B`, the
   fixed-point quotient is formally smooth (resp. smooth) over `A`.
3. **Trivial actions and tame Galois descent of the affine line**: when `Γ` acts trivially, the
   fixed-point ideal vanishes and the quotient is canonically isomorphic to `WeilRestriction A B C`.
   When `algebraMap A B` is injective, `Nat.card Γ` is a unit in `A`, and `B^Γ = A`, the
   fixed-point quotient of `WeilRestriction A B (Polynomial B)` under the coefficient action is
   canonically isomorphic to `Polynomial A`.

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointsEquiv`: identification of `T`-points of the
  fixed-point quotient of a Weil restriction with `Γ`-equivariant `B`-algebra homomorphisms
  `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointsEquivOfTrivial`: identification of the
  fixed-point quotient with `WeilRestriction A B C` when the action is trivial.
* `TauCeti.Algebra.WeilRestriction.polynomialAction`: the coefficient action of `Γ` on
  `Polynomial B` induced by `ρB : Γ →* (B ≃ₐ[A] B)`.
* `TauCeti.Algebra.WeilRestriction.fixedPointsPolynomialEquiv`: tame Galois descent identifying
  the fixed-point quotient of `WeilRestriction A B (Polynomial B)` with `Polynomial A`.

## Main results

* `TauCeti.Algebra.WeilRestriction.formallySmooth_fixedPoints`: formal smoothness of the
  fixed-point quotient of a Weil restriction under a tame group action.
* `TauCeti.Algebra.WeilRestriction.smooth_fixedPoints`: smoothness of the fixed-point quotient of
  a Weil restriction under a tame group action.
* `TauCeti.Algebra.WeilRestriction.fixedPointsIdeal_inducedAction_eq_bot`: a trivial action
  induces the zero fixed-point ideal.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions
  3.1 and 3.4, pp. 293–295.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  §1.5.
-/

public section

open scoped TensorProduct Polynomial

namespace TauCeti.Algebra.WeilRestriction

section Points

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
variable {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Points of the fixed-point quotient of a Weil restriction.** For any commutative `A`-algebra
`T`, `A`-algebra homomorphisms out of the fixed-point quotient of `WeilRestriction A B C`
correspond bijectively to `Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
noncomputable def fixedPointsEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h)) →ₐ[A] T) ≃
      { f : C →ₐ[B] B ⊗[A] T //
        ∀ (γ : Γ) (c : C),
          f (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (f c) } :=
  (TauCeti.quotientFixedPointsAlgHomEquiv (⇑(inducedAction ρB ρC h))).trans <|
    Equiv.subtypeEquiv (homEquiv A B C T) fun g ↦ by
      refine forall_congr' fun γ ↦ ?_
      rw [← comp_inducedAction_eq_iff ρB ρC h γ g, AlgHom.ext_iff]
      rfl

/-- `fixedPointsEquiv` applies `homEquiv` after precomposing with the quotient map. -/
@[simp]
theorem fixedPointsEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (q : WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h)) →ₐ[A] T) :
    (fixedPointsEquiv ρB ρC h T q : C →ₐ[B] B ⊗[A] T) =
      homEquiv A B C T
        (q.comp (Ideal.Quotient.mkₐ A (TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))))) := by
  simp [fixedPointsEquiv, TauCeti.quotientFixedPointsAlgHomEquiv_apply]

/-- The inverse of `fixedPointsEquiv` evaluates on a coset via `(homEquiv A B C T).symm`. -/
@[simp]
theorem fixedPointsEquiv_symm_apply_mk {T : Type*} [CommRing T] [Algebra A T]
    (f : { f : C →ₐ[B] B ⊗[A] T //
      ∀ (γ : Γ) (c : C),
        f (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (f c) })
    (x : WeilRestriction A B C) :
    (fixedPointsEquiv ρB ρC h T).symm f
        (Ideal.Quotient.mk (TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) x) =
      (homEquiv A B C T).symm f.1 x := by
  simp [fixedPointsEquiv, TauCeti.quotientFixedPointsAlgHomEquiv_symm_apply_mk]

/-- `fixedPointsEquiv` is natural in the test `A`-algebra `T`. -/
theorem fixedPointsEquiv_naturality {T T' : Type*} [CommRing T] [Algebra A T]
    [CommRing T'] [Algebra A T'] (ψ : T →ₐ[A] T')
    (q : WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h)) →ₐ[A] T) :
    (fixedPointsEquiv ρB ρC h T' (ψ.comp q) : C →ₐ[B] B ⊗[A] T') =
      (Algebra.TensorProduct.lTensor (S := B) B ψ).comp (fixedPointsEquiv ρB ρC h T q).1 := by
  rw [fixedPointsEquiv_apply, fixedPointsEquiv_apply, AlgHom.comp_assoc, homEquiv_comp]

/-- A trivial semilinear action induces the zero fixed-point ideal on the Weil restriction. -/
theorem fixedPointsIdeal_inducedAction_eq_bot (hB : ρB = 1) (hC : ρC = 1) :
    TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h)) = ⊥ := by
  rw [TauCeti.fixedPointsIdeal_eq_bot_iff]
  intro γ x
  rw [inducedAction_eq_one ρB ρC h hB hC]
  rfl

/-- For a trivial semilinear action, the fixed-point quotient is canonically isomorphic to the
entire Weil restriction. -/
noncomputable def quotientFixedPointsEquivOfTrivial (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) ≃ₐ[A]
      WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointsIdeal_inducedAction_eq_bot ρB ρC h hB hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- On cosets, `quotientFixedPointsEquivOfTrivial` returns the representative. -/
@[simp]
theorem quotientFixedPointsEquivOfTrivial_mk (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    quotientFixedPointsEquivOfTrivial ρB ρC h hB hC
      (Ideal.Quotient.mk (TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) x) = x := by
  simp [quotientFixedPointsEquivOfTrivial]

/-- The inverse of `quotientFixedPointsEquivOfTrivial` is the quotient projection. -/
@[simp]
theorem quotientFixedPointsEquivOfTrivial_symm_apply (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (quotientFixedPointsEquivOfTrivial ρB ρC h hB hC).symm x =
      Ideal.Quotient.mk (TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) x := by
  simp [quotientFixedPointsEquivOfTrivial]

end Points

section Smoothness

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
variable {Γ : Type*} [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Formal smoothness of tame fixed points of a Weil restriction.** If `C` is formally smooth
over `B` and `Nat.card Γ` is a unit in `A`, then the fixed-point quotient of `WeilRestriction A B C`
is formally smooth over `A`. -/
theorem formallySmooth_fixedPoints [_root_.Algebra.FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    _root_.Algebra.FormallySmooth A
      (WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) :=
  _root_.Algebra.FormallySmooth.quotient_fixedPointsIdeal (⇑(inducedAction ρB ρC h))
    (fun γ τ x ↦ by simp [map_mul]) hΓ

/-- **Smoothness of tame fixed points of a Weil restriction.** If `C` is smooth over `B` and
`Nat.card Γ` is a unit in `A`, then the fixed-point quotient of `WeilRestriction A B C` is smooth
over `A`. -/
theorem smooth_fixedPoints [_root_.Algebra.Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    _root_.Algebra.Smooth A
      (WeilRestriction A B C ⧸ TauCeti.fixedPointsIdeal (⇑(inducedAction ρB ρC h))) :=
  _root_.Algebra.Smooth.quotient_fixedPointsIdeal (⇑(inducedAction ρB ρC h))
    (fun γ τ x ↦ by simp [map_mul]) hΓ

end Smoothness

section PolynomialAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {Γ : Type*} [Monoid Γ]

/-- The coefficient action of `Γ` on `Polynomial B` induced by an action `ρB : Γ →* (B ≃ₐ[A] B)`. -/
noncomputable def polynomialAction (ρB : Γ →* (B ≃ₐ[A] B)) : Γ →* RingAut (Polynomial B) where
  toFun γ := (Polynomial.mapAlgEquiv (ρB γ)).toRingEquiv
  map_one' := by
    ext p n
    simp [Polynomial.coe_mapAlgEquiv]
  map_mul' γ δ := by
    ext p n
    simp [Polynomial.coe_mapAlgEquiv]

/-- Evaluating `polynomialAction ρB γ` on a polynomial applies `ρB γ` to its coefficients. -/
@[simp]
theorem polynomialAction_apply (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (p : Polynomial B) :
    polynomialAction ρB γ p = Polynomial.map (ρB γ).toRingHom p :=
  congrFun (Polynomial.coe_mapAlgEquiv (ρB γ)) p

/-- The coefficient action on `Polynomial B` is semilinear over `ρB`. -/
theorem polynomialAction_semilinear (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialAction ρB γ (algebraMap B (Polynomial B) b) =
      algebraMap B (Polynomial B) (ρB γ b) := by
  simp [Polynomial.algebraMap_eq]

end PolynomialAction

section AffineLineDescent

private noncomputable def reynoldsAvg {A B Γ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Monoid Γ] [Fintype Γ] (u : Aˣ) (ρB : Γ →* (B ≃ₐ[A] B)) : B →ₗ[A] B where
  toFun b := (↑u⁻¹ : A) • ∑ γ : Γ, ρB γ b
  map_add' b₁ b₂ := by simp [Finset.sum_add_distrib, smul_add]
  map_smul' r b := by
    simp only [map_smul, ← Finset.smul_sum, RingHom.id_apply]
    rw [smul_comm]

private theorem reynoldsAvg_invariant {A B Γ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group Γ] [Fintype Γ] (u : Aˣ) (ρB : Γ →* (B ≃ₐ[A] B)) (b : B) (γ : Γ) :
    ρB γ (reynoldsAvg u ρB b) = reynoldsAvg u ρB b := by
  simp only [reynoldsAvg, LinearMap.coe_mk, AddHom.coe_mk, map_smul, map_sum]
  congr 1
  have hcomp : ∀ τ : Γ, ρB γ (ρB τ b) = ρB (γ * τ) b := fun τ ↦ by simp [map_mul]
  simp_rw [hcomp]
  exact Equiv.sum_comp (Equiv.mulLeft γ) (fun τ ↦ ρB τ b)

private noncomputable def reynoldsRetraction {A B Γ : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Group Γ] [Fintype Γ] (u : Aˣ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) : B →ₗ[A] A :=
  let hπ := fun b ↦ hfix (reynoldsAvg u ρB b) (reynoldsAvg_invariant u ρB b)
  { toFun := fun b ↦ Classical.choose (hπ b)
    map_add' := fun b₁ b₂ ↦ hinj <| by
      rw [map_add (algebraMap A B), Classical.choose_spec (hπ _), Classical.choose_spec (hπ _),
        Classical.choose_spec (hπ _), map_add]
    map_smul' := fun r b ↦ hinj <| by
      rw [RingHom.id_apply, smul_eq_mul, map_mul (algebraMap A B), Classical.choose_spec (hπ _),
        Classical.choose_spec (hπ _), map_smul, Algebra.smul_def] }

private theorem algebraMap_reynoldsRetraction {A B Γ : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Group Γ] [Fintype Γ] (u : Aˣ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) (b : B) :
    algebraMap A B (reynoldsRetraction u ρB hinj hfix b) = reynoldsAvg u ρB b :=
  Classical.choose_spec (hfix (reynoldsAvg u ρB b) (reynoldsAvg_invariant u ρB b))

private theorem reynoldsRetraction_one {A B Γ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group Γ] [Fintype Γ] (u : Aˣ) (hu : (u : A) = Fintype.card Γ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    reynoldsRetraction u ρB hinj hfix 1 = 1 := by
  apply hinj
  rw [algebraMap_reynoldsRetraction, map_one (algebraMap A B)]
  simp only [reynoldsAvg, LinearMap.coe_mk, AddHom.coe_mk, map_one, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul A, ← mul_smul, ← hu, Units.inv_mul, one_smul]

private theorem reynoldsRetraction_tensor_fixed {A B Γ : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Group Γ] [Fintype Γ] (u : Aˣ) (hu : (u : A) = Fintype.card Γ)
    (ρB : Γ →* (B ≃ₐ[A] B)) (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    {T : Type*} [CommRing T] [Algebra A T] (y : B ⊗[A] T)
    (hy : ∀ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) y = y) :
    Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T)
      (TensorProduct.lid A T (LinearMap.rTensor T (reynoldsRetraction u ρB hinj hfix) y)) = y := by
  have hinc : ∀ z : B ⊗[A] T,
      Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T)
        (TensorProduct.lid A T (LinearMap.rTensor T (reynoldsRetraction u ρB hinj hfix) z)) =
        LinearMap.rTensor T (reynoldsAvg u ρB) z := by
    intro z
    induction z with
    | tmul b t =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        Algebra.TensorProduct.includeRight_apply]
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, algebraMap_reynoldsRetraction]
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
  have hre : ∀ z : B ⊗[A] T,
      LinearMap.rTensor T (reynoldsAvg u ρB) z =
        (↑u⁻¹ : A) • ∑ γ : Γ, Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) z := by
    intro z
    induction z with
    | tmul b t =>
      simp only [LinearMap.rTensor_tmul, reynoldsAvg, LinearMap.coe_mk, AddHom.coe_mk,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
      rw [← TensorProduct.smul_tmul', TensorProduct.sum_tmul]
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂, Finset.sum_add_distrib, smul_add]
  rw [hinc y, hre y]
  simp_rw [hy]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A, ← mul_smul, ← hu,
    Units.inv_mul, one_smul]

private theorem aeval_includeRight_equivariant {A B Γ T : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [CommRing T] [Algebra A T] [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (t : T) (γ : Γ) (c : Polynomial B) :
    Polynomial.aeval (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T) t)
        (polynomialAction ρB γ c) =
      Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B)
        (Polynomial.aeval (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T) t) c) := by
  induction c using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simp only [map_add, hp₁, hp₂]
  | monomial n b =>
    simp only [polynomialAction_apply, Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul,
      map_pow, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, map_one,
      Algebra.algebraMap_self, RingHom.id_apply]
    rfl

private noncomputable def fixedPointsPolynomialPointsEquiv {A B Γ : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Group Γ] [Fintype Γ]
    (u : Aˣ) (hu : (u : A) = Fintype.card Γ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B (Polynomial B) ⧸
        TauCeti.fixedPointsIdeal
          (⇑(inducedAction ρB (polynomialAction ρB) (polynomialAction_semilinear ρB))) →ₐ[A] T) ≃
      (Polynomial A →ₐ[A] T) where
  toFun q :=
    Polynomial.aeval
      (TensorProduct.lid A T
        (LinearMap.rTensor T (reynoldsRetraction u ρB hinj hfix)
          ((fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) T q).1
            Polynomial.X)))
  invFun p :=
    (fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) T).symm
      ⟨Polynomial.aeval (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T)
          (p Polynomial.X)),
        aeval_includeRight_equivariant ρB (p Polynomial.X)⟩
  left_inv q := by
    apply (fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) T).injective
    apply Subtype.ext
    apply Polynomial.algHom_ext
    simp only [Equiv.apply_symm_apply, Polynomial.aeval_X]
    refine reynoldsRetraction_tensor_fixed u hu ρB hinj hfix _ fun γ ↦ ?_
    have hγ := (fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) T q).2
      γ Polynomial.X
    simpa [polynomialAction_apply] using hγ.symm
  right_inv p := by
    apply Polynomial.algHom_ext
    simp only [Polynomial.aeval_X, Equiv.apply_symm_apply,
      Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul,
      reynoldsRetraction_one u hu ρB hinj hfix, TensorProduct.lid_tmul, one_smul]

private theorem fixedPointsPolynomialPointsEquiv_naturality {A B Γ : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Group Γ] [Fintype Γ]
    (u : Aˣ) (hu : (u : A) = Fintype.card Γ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    {T T' : Type*} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (ψ : T →ₐ[A] T')
    (q : WeilRestriction A B (Polynomial B) ⧸
      TauCeti.fixedPointsIdeal
        (⇑(inducedAction ρB (polynomialAction ρB) (polynomialAction_semilinear ρB))) →ₐ[A] T) :
    fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix T' (ψ.comp q) =
      ψ.comp (fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix T q) := by
  apply Polynomial.algHom_ext
  simp only [fixedPointsPolynomialPointsEquiv, Equiv.coe_fn_mk, AlgHom.comp_apply,
    Polynomial.aeval_X, fixedPointsEquiv_naturality]
  generalize (fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) T q).1
      Polynomial.X = y
  induction y with
  | tmul b t => simp
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]

private noncomputable def fixedPointsPolynomialEquivOfFintype {A B Γ : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Group Γ] [Fintype Γ]
    (u : Aˣ) (hu : (u : A) = Fintype.card Γ) (ρB : Γ →* (B ≃ₐ[A] B))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (WeilRestriction A B (Polynomial B) ⧸
      TauCeti.fixedPointsIdeal
        (⇑(inducedAction ρB (polynomialAction ρB) (polynomialAction_semilinear ρB)))) ≃ₐ[A]
      Polynomial A :=
  let Q := WeilRestriction A B (Polynomial B) ⧸
    TauCeti.fixedPointsIdeal
      (⇑(inducedAction ρB (polynomialAction ρB) (polynomialAction_semilinear ρB)))
  let fwd : Q →ₐ[A] Polynomial A :=
    (fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A)).symm
      (AlgHom.id A (Polynomial A))
  let inv : Polynomial A →ₐ[A] Q :=
    fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix Q (AlgHom.id A Q)
  AlgEquiv.ofAlgHom fwd inv
    (by
      calc
        fwd.comp inv =
            fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A)
              (fwd.comp (AlgHom.id A Q)) :=
          (fixedPointsPolynomialPointsEquiv_naturality u hu ρB hinj hfix fwd (AlgHom.id A Q)).symm
        _ = fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A) fwd := by
          rw [AlgHom.comp_id]
        _ = AlgHom.id A (Polynomial A) :=
          (fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A)).apply_symm_apply _)
    (by
      apply (fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix Q).injective
      calc
        fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix Q (inv.comp fwd) =
            inv.comp (fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A) fwd) :=
          fixedPointsPolynomialPointsEquiv_naturality u hu ρB hinj hfix inv fwd
        _ = inv.comp (AlgHom.id A (Polynomial A)) := by
          rw [(fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix (Polynomial A)).apply_symm_apply]
        _ = fixedPointsPolynomialPointsEquiv u hu ρB hinj hfix Q (AlgHom.id A Q) :=
          AlgHom.comp_id inv)

/-- **Tame Galois descent of the affine line.** Let `A → B` be a finite projective injective
extension of commutative rings with an action `ρB : Γ →* (B ≃ₐ[A] B)` of a group `Γ` of invertible
order in `A` whose fixed subring is `A`. Then the fixed-point quotient of
`WeilRestriction A B (Polynomial B)` under the coefficient action is canonically isomorphic to
`Polynomial A`. -/
noncomputable def fixedPointsPolynomialEquiv {A B Γ : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Group Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (WeilRestriction A B (Polynomial B) ⧸
      TauCeti.fixedPointsIdeal
        (⇑(inducedAction ρB (polynomialAction ρB) (polynomialAction_semilinear ρB)))) ≃ₐ[A]
      Polynomial A := by
  classical
  exact if hnt : Nontrivial A then
    have hfin : Finite Γ := Nat.finite_of_card_ne_zero fun h0 ↦ by
      rw [h0, Nat.cast_zero] at hΓ
      exact not_isUnit_zero hΓ
    let _ : Fintype Γ := Fintype.ofFinite Γ
    fixedPointsPolynomialEquivOfFintype hΓ.unit
      (by rw [IsUnit.unit_spec, Nat.card_eq_fintype_card]) ρB hinj hfix
  else
    have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnt
    have : Subsingleton (WeilRestriction A B (Polynomial B)) := Module.subsingleton A _
    have : Subsingleton (Polynomial A) := Module.subsingleton A _
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _
      commutes' := fun _ ↦ Subsingleton.elim _ _ }

/-- Under `fixedPointsEquiv`, the canonical isomorphism `fixedPointsPolynomialEquiv` corresponds to
the `B`-algebra map `B[X] → B ⊗[A] A[X]` sending `X` to `1 ⊗ₜ X`. -/
theorem fixedPointsEquiv_fixedPointsPolynomialEquiv {A B Γ : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Group Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (fixedPointsEquiv ρB (polynomialAction ρB) (polynomialAction_semilinear ρB) (Polynomial A)
        (fixedPointsPolynomialEquiv ρB hΓ hinj hfix).toAlgHom).1 =
      Polynomial.aeval
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := Polynomial A)
          Polynomial.X) := by
  by_cases hnt : Nontrivial A
  · simp only [fixedPointsPolynomialEquiv, dite_eq_left hnt, fixedPointsPolynomialEquivOfFintype,
      AlgEquiv.toAlgHom_ofAlgHom, fixedPointsPolynomialPointsEquiv, Equiv.coe_fn_symm_mk,
      Equiv.apply_symm_apply, AlgHom.id_apply]
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnt
    have : Subsingleton (B ⊗[A] Polynomial A) := Module.subsingleton A _
    exact Subsingleton.elim _ _

end AffineLineDescent

end TauCeti.Algebra.WeilRestriction
