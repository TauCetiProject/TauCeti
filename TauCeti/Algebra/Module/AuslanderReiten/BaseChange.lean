/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Base change of the Auslander–Bridger transpose over commutative rings

Let `R` be a commutative ring, `A` a commutative `R`-algebra, and `f : P₁ →ₗ[R] P₀` a linear map
between finitely generated projective `R`-modules. For a finitely generated projective module `P`,
scalar extension commutes with linear duality:
`A ⊗[R] Hom_R(P, R) ≃ₗ[A] Hom_A(A ⊗[R] P, A)` (`TauCeti.Module.Dual.baseChangeEvaluationEquiv`).
Applying right exactness of the tensor product to the defining cokernel sequence
`Hom_R(P₀, R) → Hom_R(P₁, R) → Tr f → 0` therefore identifies the base change of the transpose
with the transpose of the base-changed map:

  `A ⊗[R] AuslanderReitenTranspose f ≃ₗ[A] AuslanderReitenTranspose (f.baseChange A)`.

This compatibility allows invariants of transposed presentations, such as Fitting ideals, to be
computed locally on `Spec R`, where finitely generated projective modules become free.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.mkLinear`: the quotient map `Module.Dual R P₁ →ₗ[R]
  AuslanderReitenTranspose f` over a commutative ring `R`.
* `TauCeti.AuslanderReitenTranspose.baseChangeHom`: the canonical `A`-linear comparison map
  `A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A)`, defined
  without finiteness or projectivity assumptions.
* `TauCeti.AuslanderReitenTranspose.baseChangeEquiv`: the `A`-linear isomorphism when `P₀` and `P₁`
  are finitely generated projective `R`-modules.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  Appendix B.2, proof of Lemma B.4.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AuslanderReitenTranspose

section ScalarTower

variable {k R B Q₀ Q₁ : Type*} [CommSemiring k] [CommSemiring R] [Ring B]
  [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
  [AddCommMonoid Q₀] [Module B Q₀] [AddCommMonoid Q₁] [Module B Q₁]

instance (p : Q₁ →ₗ[B] Q₀) : IsScalarTower k R (AuslanderReitenTranspose p) :=
  IsScalarTower.of_algebraMap_smul fun c x ↦ by
    rw [← op_algebraMap_smul (k := R), ← op_algebraMap_smul (k := k),
      IsScalarTower.algebraMap_apply k R B]

end ScalarTower

section CommRing

variable {R P₀ P₁ : Type*} [CommRing R] [AddCommMonoid P₀] [Module R P₀]
  [AddCommMonoid P₁] [Module R P₁]

private theorem op_smul_eq_smul {S : Type*} [CommRing S] {Q₀ Q₁ : Type*}
    [AddCommMonoid Q₀] [Module S Q₀] [AddCommMonoid Q₁] [Module S Q₁]
    (p : Q₁ →ₗ[S] Q₀) (s : S) (y : AuslanderReitenTranspose p) :
    MulOpposite.op s • y = s • y := by
  simpa only [Algebra.algebraMap_self_apply] using (op_algebraMap_smul (k := S) p s y)

/-- Over a commutative ring `R`, the quotient map from `Module.Dual R P₁` onto
`AuslanderReitenTranspose f` is `R`-linear. -/
def mkLinear (f : P₁ →ₗ[R] P₀) : Module.Dual R P₁ →ₗ[R] AuslanderReitenTranspose f where
  toFun := mk f
  map_add' := map_add (mk f)
  map_smul' r φ := by
    have hsmul : r • φ = MulOpposite.op r • φ := by
      ext x
      exact mul_comm r (φ x)
    rw [hsmul, map_smul, op_smul_eq_smul, RingHom.id_apply]

@[simp]
theorem mkLinear_apply (f : P₁ →ₗ[R] P₀) (φ : Module.Dual R P₁) :
    mkLinear f φ = mk f φ :=
  (rfl)

theorem mkLinear_surjective (f : P₁ →ₗ[R] P₀) : Function.Surjective (mkLinear f) :=
  mk_surjective f

variable (A : Type*) [CommRing A] [Algebra R A]

private def toBaseChangeAux (f : P₁ →ₗ[R] P₀) :
    AuslanderReitenTranspose f →ₗ[R] AuslanderReitenTranspose (f.baseChange A) := by
  let N := AuslanderReitenTranspose (f.baseChange A)
  letI : Module Rᵐᵒᵖ N :=
    Module.compHom N (RingEquiv.toOpposite R).symm.toRingHom
  let g : Module.Dual R P₁ →ₗ[Rᵐᵒᵖ] N :=
    { toFun φ := mk (f.baseChange A) (Module.Dual.baseChange A φ)
      map_add' φ ψ := by simp [map_add]
      map_smul' r φ := by
        have hφ : Module.Dual.baseChange A (r • φ) =
            algebraMap R A r.unop • Module.Dual.baseChange A φ :=
          LinearMap.restrictScalars_injective R <| TensorProduct.ext' fun a x ↦ by
            simp [MulOpposite.smul_eq_mul_unop, Algebra.smul_def, mul_left_comm, mul_comm]
        -- Unfold the pulled-back `Rᵐᵒᵖ`-action on `N` to the underlying `R`-action.
        change mk (f.baseChange A) (Module.Dual.baseChange A (r • φ)) =
          r.unop • mk (f.baseChange A) (Module.Dual.baseChange A φ)
        rw [hφ, ← mkLinear_apply, map_smul, algebraMap_smul, mkLinear_apply] }
  have hg (ψ : Module.Dual R P₀) : g (f.lcomp Rᵐᵒᵖ R ψ) = 0 := by
    have hcomp : Module.Dual.baseChange A (f.lcomp Rᵐᵒᵖ R ψ) =
        (f.baseChange A).lcomp Aᵐᵒᵖ A (Module.Dual.baseChange A ψ) :=
      LinearMap.restrictScalars_injective R <| TensorProduct.ext' fun a x ↦ by simp
    simp [g, hcomp]
  let L := lift f g hg
  exact
    { toFun := L
      map_add' := map_add L
      map_smul' r y := by
        rw [← op_smul_eq_smul f r y]
        exact L.map_smul (MulOpposite.op r) y }

/-- The canonical `A`-linear comparison map
`A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A)`, sending
`a ⊗ [φ]` to `a • [φ_A]`. No finiteness or projectivity is needed to form this map. -/
def baseChangeHom (f : P₁ →ₗ[R] P₀) :
    A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A) :=
  (toBaseChangeAux A f).liftBaseChange A

@[simp]
theorem baseChangeHom_tmul_mk (f : P₁ →ₗ[R] P₀) (a : A) (φ : Module.Dual R P₁) :
    baseChangeHom A f (a ⊗ₜ[R] mk f φ) =
      a • mk (f.baseChange A) (Module.Dual.baseChange A φ) := by
  simp only [baseChangeHom, LinearMap.liftBaseChange_tmul, toBaseChangeAux, LinearMap.coe_mk,
    AddHom.coe_mk, lift_mk]

section FiniteProjective

variable [Module.Finite R P₀] [Module.Projective R P₀]
  [Module.Finite R P₁] [Module.Projective R P₁]

private def ofBaseChangeHom (f : P₁ →ₗ[R] P₀) :
    AuslanderReitenTranspose (f.baseChange A) →ₗ[A] A ⊗[R] AuslanderReitenTranspose f := by
  letI : Module Aᵐᵒᵖ (A ⊗[R] AuslanderReitenTranspose f) :=
    Module.compHom (A ⊗[R] AuslanderReitenTranspose f) (RingEquiv.toOpposite A).symm.toRingHom
  let e₁ := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₁)
  let g : Module.Dual A (A ⊗[R] P₁) →ₗ[Aᵐᵒᵖ] A ⊗[R] AuslanderReitenTranspose f :=
    { toFun Φ := (mkLinear f).baseChange A (e₁.symm Φ)
      map_add' Φ Ψ := by simp
      map_smul' a Φ := by
        have ha : a • Φ = a.unop • Φ := LinearMap.ext fun z ↦ mul_comm (Φ z) a.unop
        -- Unfold the pulled-back `Aᵐᵒᵖ`-action on `A ⊗[R] AuslanderReitenTranspose f`.
        change (mkLinear f).baseChange A (e₁.symm (a • Φ)) =
          a.unop • (mkLinear f).baseChange A (e₁.symm Φ)
        rw [ha, map_smul, map_smul] }
  have hg (Ψ : Module.Dual A (A ⊗[R] P₀)) : g ((f.baseChange A).lcomp Aᵐᵒᵖ A Ψ) = 0 := by
    let e₀ := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₀)
    obtain ⟨w, rfl⟩ := e₀.surjective Ψ
    induction w using TensorProduct.inductionOn with
    | tmul a ψ =>
      have hcomp : (f.baseChange A).lcomp Aᵐᵒᵖ A (e₀ (a ⊗ₜ[R] ψ)) =
          e₁ (a ⊗ₜ[R] f.lcomp Rᵐᵒᵖ R ψ) :=
        LinearMap.restrictScalars_injective R <| TensorProduct.ext' fun b x ↦ by simp [e₀, e₁]
      simp [g, hcomp]
    | add u v hu hv =>
      rw [map_add, map_add, map_add, hu, hv, add_zero]
  let L := lift (f.baseChange A) g hg
  exact
    { toFun := L
      map_add' := map_add L
      map_smul' a y := by
        rw [← op_smul_eq_smul (f.baseChange A) a y]
        exact L.map_smul (MulOpposite.op a) y }

private theorem ofBaseChangeHom_mk_eval (f : P₁ →ₗ[R] P₀) (a : A) (φ : Module.Dual R P₁) :
    ofBaseChangeHom A f
      (mk (f.baseChange A)
        (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₁) (a ⊗ₜ[R] φ))) =
      a ⊗ₜ[R] mk f φ := by
  simp only [ofBaseChangeHom, LinearMap.coe_mk, AddHom.coe_mk, lift_mk,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, mkLinear_apply]

/-- **Base change commutes with the transpose of a finite projective presentation.** For a
commutative ring `R`, a commutative `R`-algebra `A`, and a linear map `f : P₁ →ₗ[R] P₀` between
finitely generated projective `R`-modules, `A ⊗[R] Tr f` is canonically `A`-linearly isomorphic
to `Tr (f.baseChange A)`. -/
def baseChangeEquiv (f : P₁ →ₗ[R] P₀) :
    A ⊗[R] AuslanderReitenTranspose f ≃ₗ[A] AuslanderReitenTranspose (f.baseChange A) :=
  LinearEquiv.ofLinearMap (baseChangeHom A f) (ofBaseChangeHom A f)
    (LinearMap.ext fun y ↦ by
      induction y using induction_on with | h Φ => ?_
      let e₁ := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₁)
      obtain ⟨z, rfl⟩ := e₁.surjective Φ
      induction z using TensorProduct.inductionOn with
      | tmul a φ =>
        have heval : e₁ (a ⊗ₜ[R] φ) = a • Module.Dual.baseChange A φ :=
          LinearMap.restrictScalars_injective R <| TensorProduct.ext' fun b x ↦ by
            simp [e₁, Algebra.smul_def, mul_comm, mul_assoc]
        rw [LinearMap.comp_apply, LinearMap.id_apply, ofBaseChangeHom_mk_eval,
          baseChangeHom_tmul_mk, ← mkLinear_apply, ← map_smul, mkLinear_apply, heval]
      | add u v hu hv =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hu hv ⊢
        rw [hu, hv])
    (LinearMap.ext fun z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul a t =>
        induction t using induction_on with | h φ => ?_
        let e₁ := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₁)
        have heval : a • Module.Dual.baseChange A φ = e₁ (a ⊗ₜ[R] φ) :=
          LinearMap.restrictScalars_injective R <| TensorProduct.ext' fun b x ↦ by
            simp [e₁, Algebra.smul_def, mul_comm, mul_assoc]
        rw [LinearMap.comp_apply, LinearMap.id_apply, baseChangeHom_tmul_mk,
          ← mkLinear_apply, ← map_smul, mkLinear_apply, heval, ofBaseChangeHom_mk_eval]
      | add u v hu hv =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hu hv ⊢
        rw [hu, hv])

@[simp]
theorem baseChangeEquiv_tmul_mk (f : P₁ →ₗ[R] P₀) (a : A) (φ : Module.Dual R P₁) :
    baseChangeEquiv A f (a ⊗ₜ[R] mk f φ) =
      a • mk (f.baseChange A) (Module.Dual.baseChange A φ) :=
  baseChangeHom_tmul_mk A f a φ

end FiniteProjective

end CommRing

end TauCeti.AuslanderReitenTranspose
