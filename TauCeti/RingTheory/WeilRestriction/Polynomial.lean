/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.WeilRestriction.FixedPoints

/-!
# Tame Galois descent of the affine line under Weil restriction

For a group `Γ` acting on a finite projective faithful `A`-algebra `B` with `B^Γ = A` and
`(Nat.card Γ : A)` invertible in `A`, specializing `fixedPointQuotientBaseChangeAlgEquiv` along
`polyEquivTensor' A B : B[X] ≃ₐ[B] B ⊗[A] A[X]` gives the canonical `A`-algebra isomorphism
`(WeilRestriction A B B[X] ⧸ fixedPointIdealOfInduced ...) ≃ₐ[A] A[X]`, descending
`(Res_{B/A} 𝔸¹_B)^Γ` to `𝔸¹_A`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientPolynomialAlgEquiv`:
  `(Res_{B/A} 𝔸¹_B)^Γ ≃ 𝔸¹_A`.
* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientHomEquiv_fixedPointQuotientPolynomialAlgEquiv`
  and `one_tmul_fixedPointQuotientPolynomialAlgEquiv_symm`: point and inverse characterizations.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4, p. 292 and
  Propositions 3.1 and 3.4, pp. 293–295.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), Proposition 1.3.3, pp. 142–143.
-/

public noncomputable section

open Algebra TensorProduct Polynomial
open TauCeti.Algebra.TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable (A B Γ : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

private theorem polyEquivTensor_smul (γ : Γ) (p : B[X]) :
    polyEquivTensor' A B (MulSemiringAction.toRingAut Γ B[X] γ p) =
      baseChangeSemilinearAction A B A[X] Γ γ (polyEquivTensor' A B p) := by
  have hfg : (polyEquivTensor' A B).toAlgHom.toRingHom.comp
        (MulSemiringAction.toRingAut Γ B[X] γ).toRingHom =
      (baseChangeSemilinearAction A B A[X] Γ γ).toRingHom.comp
        (polyEquivTensor' A B).toAlgHom.toRingHom :=
    Polynomial.ringHom_ext' (by ext; simp) (by simp)
  exact congr($hfg p)

variable [Module.Finite A B] [Module.Projective A B]
  [FaithfulSMul A B] [Algebra.IsInvariant A B Γ]

/-- **Tame descent of the affine line.** Under the hypotheses of
`fixedPointQuotientBaseChangeAlgEquiv`, `(Res_{B/A} 𝔸¹_B)^Γ` is canonically isomorphic to `A[X]`. -/
def fixedPointQuotientPolynomialAlgEquiv (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B B[X] ⧸
        fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
          (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)) ≃ₐ[A] A[X] :=
  (mapFixedPointQuotientAlgEquiv (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)
    (baseChangeSemilinearAction A B A[X] Γ) (baseChangeSemilinearAction_algebraMap A B A[X] Γ)
    (polyEquivTensor' A B) (polyEquivTensor_smul A B Γ)).trans
    (fixedPointQuotientBaseChangeAlgEquiv A B A[X] Γ hΓ)

/-- On cosets, `fixedPointQuotientPolynomialAlgEquiv` maps via `polyEquivTensor'` and
`counitFixedPointQuotient`. -/
@[simp]
theorem fixedPointQuotientPolynomialAlgEquiv_mk (hΓ : IsUnit (Nat.card Γ : A))
    (x : WeilRestriction A B B[X]) :
    fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ
        (Ideal.Quotient.mk
          (fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)) x) =
      counitFixedPointQuotient A B A[X] Γ
        (Ideal.Quotient.mk
          (fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
            (baseChangeSemilinearAction A B A[X] Γ)
            (baseChangeSemilinearAction_algebraMap A B A[X] Γ))
          (map A B (polyEquivTensor' A B).toAlgHom x)) := by
  rw [fixedPointQuotientPolynomialAlgEquiv, AlgEquiv.trans_apply,
    mapFixedPointQuotientAlgEquiv_mk, fixedPointQuotientBaseChangeAlgEquiv_apply]

/-- Under `fixedPointQuotientHomEquiv`, `fixedPointQuotientPolynomialAlgEquiv` classifies
`polyEquivTensor' A B`. Not `@[simp]` because `fixedPointQuotientHomEquiv_apply` simplifies. -/
theorem fixedPointQuotientHomEquiv_fixedPointQuotientPolynomialAlgEquiv
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
      (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp) A[X]
      (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).toAlgHom : B[X] →ₐ[B] B ⊗[A] A[X]) =
      (polyEquivTensor' A B).toAlgHom := by
  let I₁ := fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)
  have hcomp :
      (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).toAlgHom.comp (Ideal.Quotient.mkₐ A I₁) =
        ((homEquiv A B (B ⊗[A] A[X]) A[X]).symm (AlgHom.id B (B ⊗[A] A[X]))).comp
          (map A B (polyEquivTensor' A B).toAlgHom) :=
    AlgHom.ext fun _ ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
        fixedPointQuotientPolynomialAlgEquiv_mk, I₁]
      exact congr($(counitFixedPointQuotient_comp_mk A B A[X] Γ) _)
  rw [fixedPointQuotientHomEquiv_apply, hcomp, homEquiv_comp_map, Equiv.apply_symm_apply,
    AlgHom.id_comp]

/-- Characterizes `(fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm` via `1 ⊗ₜ ·`. -/
@[simp]
theorem one_tmul_fixedPointQuotientPolynomialAlgEquiv_symm
    (hΓ : IsUnit (Nat.card Γ : A)) (p : A[X]) :
    (1 : B) ⊗ₜ[A] (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm p =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp) _ (AlgHom.id A _)).1
        (Polynomial.map (algebraMap A B) p) := by
  let I₁ := fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)
  let I₂ := fixedPointIdealOfInduced (MulSemiringAction.toAlgAut Γ A B)
    (baseChangeSemilinearAction A B A[X] Γ) (baseChangeSemilinearAction_algebraMap A B A[X] Γ)
  let q₂ := (fixedPointQuotientBaseChangeAlgEquiv A B A[X] Γ hΓ).symm p
  let f := (mapFixedPointQuotientAlgEquiv (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp)
    (baseChangeSemilinearAction A B A[X] Γ) (baseChangeSemilinearAction_algebraMap A B A[X] Γ)
    (polyEquivTensor' A B) (polyEquivTensor_smul A B Γ)).symm.toAlgHom
  have hsymm : (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm p = f q₂ := by
    simp [fixedPointQuotientPolynomialAlgEquiv, q₂, f]
  have hfcomp : f.comp (Ideal.Quotient.mkₐ A I₂) =
      (Ideal.Quotient.mkₐ A I₁).comp (map A B (polyEquivTensor' A B).symm.toAlgHom) :=
    AlgHom.ext fun _ ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
        mapFixedPointQuotientAlgEquiv_symm, mapFixedPointQuotientAlgEquiv_mk, f, I₁, I₂]
  calc (1 : B) ⊗ₜ[A] (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm p
      = Algebra.TensorProduct.lTensor B f ((1 : B) ⊗ₜ[A] q₂) := by
          rw [hsymm]; exact (Algebra.TensorProduct.map_tmul (AlgHom.id B B) f 1 q₂).symm
    _ = homEquiv A B (B ⊗[A] A[X]) (WeilRestriction A B B[X] ⧸ I₁)
          (f.comp (Ideal.Quotient.mkₐ A I₂)) ((1 : B) ⊗ₜ[A] p) := by
          rw [one_tmul_fixedPointQuotientBaseChangeAlgEquiv_symm, fixedPointQuotientHomEquiv_apply,
            AlgHom.id_comp, ← AlgHom.comp_apply, ← homEquiv_comp]
    _ = _ := by
          rw [hfcomp, homEquiv_comp_map, AlgHom.comp_apply, fixedPointQuotientHomEquiv_apply,
            AlgHom.id_comp]
          exact congrArg _ (by simp)

/-- Specializes `one_tmul_fixedPointQuotientPolynomialAlgEquiv_symm` to `X : A[X]`.
Not `@[simp]` because `one_tmul_fixedPointQuotientPolynomialAlgEquiv_symm` already simplifies. -/
theorem one_tmul_fixedPointQuotientPolynomialAlgEquiv_symm_X (hΓ : IsUnit (Nat.card Γ : A)) :
    (1 : B) ⊗ₜ[A] (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm X =
      (fixedPointQuotientHomEquiv (MulSemiringAction.toAlgAut Γ A B)
        (MulSemiringAction.toRingAut Γ B[X]) (fun γ b ↦ by simp) _ (AlgHom.id A _)).1 X := by
  simp

/-- `(fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm` sends constants `C a` to scalars. -/
@[simp]
theorem fixedPointQuotientPolynomialAlgEquiv_symm_C (hΓ : IsUnit (Nat.card Γ : A)) (a : A) :
    (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm (C a) = algebraMap A _ a := by
  rw [← Polynomial.algebraMap_eq]
  exact (fixedPointQuotientPolynomialAlgEquiv A B Γ hΓ).symm.commutes a

end TauCeti.Algebra.WeilRestriction
