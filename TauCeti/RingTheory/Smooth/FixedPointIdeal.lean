/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.RingTheory.Ideal.FixedPoint
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import TauCeti.Algebra.BigOperators.Finset.Average
import TauCeti.RepresentationTheory.Invariants
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Edixhoven's tame fixed-point smoothness theorem

For a group `Γ` acting by `R`-algebra automorphisms on a commutative `R`-algebra `A`, the quotient
`A ⧸ fixedPointIdeal Γ A` cuts out `(Spec A)^Γ`. Unlike `TauCeti.Comodule.fixedPointIdeal` (for
diagonalizable coactions, formally smooth over any base), invertibility of `|Γ|` in `R` is essential
here: `T ↦ T⁻¹` on `𝔽₂[T; T⁻¹]` has non-smooth quotient `𝔽₂[ε] ⧸ (ε²)`.

We prove **Edixhoven's tame fixed-point smoothness theorem**
(`formallySmooth_quotient_fixedPointIdeal`, `smooth_quotient_fixedPointIdeal`): when `A` is formally
smooth (resp. smooth) over `R` and `(Nat.card Γ : R)` is a unit in `R`, `A ⧸ fixedPointIdeal Γ A` is
formally smooth (resp. smooth) over `R` (`[Finite Γ]` is deduced automatically over nontrivial `R`).
Given a square-zero extension `C ↠ C ⧸ J` (`J ^ 2 = ⊥`) and an unaveraged lift `φ : A →ₐ[R] C` with
displacements `δ γ a = φ (γ • a) - φ a ∈ J`, composing `φ` with `Representation.averageMap` makes
the lift multiplicative (as products of elements of `J` vanish) and `Γ`-invariant.

## Main results

* `TauCeti.MulSemiringAction.formallySmooth_quotient_fixedPointIdeal` and
  `TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal`: Edixhoven's smoothness theorem.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
-/

public section

namespace TauCeti.MulSemiringAction

section Lift

variable {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing C] [Algebra R C]
  [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
  [Invertible (Fintype.card Γ : R)] {J : Ideal C}

private theorem averagedLift_map_mul (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (a b : A) :
    φ ((Representation.ofDistribMulAction R Γ A).averageMap (a * b)) =
      φ ((Representation.ofDistribMulAction R Γ A).averageMap a) *
        φ ((Representation.ofDistribMulAction R Γ A).averageMap b) := by
  let D (x : A) : C := ⅟(Fintype.card Γ : R) • ∑ γ : Γ, (φ (γ • x) - φ x)
  have hDJ (x : A) : D x ∈ J := by
    dsimp only [D]; rw [Algebra.smul_def]; exact J.mul_mem_left _ (sum_mem fun γ _ ↦ hφ γ x)
  have havg (x : A) : φ ((Representation.ofDistribMulAction R Γ A).averageMap x) = φ x + D x := by
    rw [Representation.averageMap_apply, map_smul, map_sum]
    simp only [Representation.ofDistribMulAction_apply_apply]
    have hsum : (∑ γ : Γ, φ (γ • x)) = (∑ _γ : Γ, φ x) + ∑ γ : Γ, (φ (γ • x) - φ x) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ (add_sub_cancel _ _).symm
    rw [hsum, smul_add, Fintype.invOf_card_smul_sum_const]
  have hterm (γ : Γ) :
      φ (γ • (a * b)) = φ a * φ b + φ a * (φ (γ • b) - φ b) + (φ (γ • a) - φ a) * φ b := by
    have hzero : (φ (γ • a) - φ a) * (φ (γ • b) - φ b) = 0 :=
      Ideal.mem_bot.mp (hJ ▸ sq J ▸ Ideal.mul_mem_mul (hφ γ a) (hφ γ b))
    calc φ (γ • (a * b))
        = (φ a + (φ (γ • a) - φ a)) * (φ b + (φ (γ • b) - φ b)) := by
          rw [smul_mul', map_mul, add_sub_cancel, add_sub_cancel]
      _ = φ a * φ b + φ a * (φ (γ • b) - φ b) + (φ (γ • a) - φ a) * φ b +
            (φ (γ • a) - φ a) * (φ (γ • b) - φ b) := by ring
      _ = φ a * φ b + φ a * (φ (γ • b) - φ b) + (φ (γ • a) - φ a) * φ b := by rw [hzero, add_zero]
  have hsum : (∑ γ : Γ, φ (γ • (a * b))) =
      (∑ _γ : Γ, φ a * φ b) + φ a * (∑ γ : Γ, (φ (γ • b) - φ b)) +
        (∑ γ : Γ, (φ (γ • a) - φ a)) * φ b := by
    simp only [hterm, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have hDD : D a * D b = 0 := Ideal.mem_bot.mp (hJ ▸ sq J ▸ Ideal.mul_mem_mul (hDJ a) (hDJ b))
  rw [Representation.averageMap_apply, map_smul, map_sum]
  simp only [Representation.ofDistribMulAction_apply_apply]
  calc ⅟(Fintype.card Γ : R) • ∑ γ : Γ, φ (γ • (a * b))
      = ⅟(Fintype.card Γ : R) • (∑ _γ : Γ, φ a * φ b) +
          ⅟(Fintype.card Γ : R) • (φ a * ∑ γ : Γ, (φ (γ • b) - φ b)) +
          ⅟(Fintype.card Γ : R) • ((∑ γ : Γ, (φ (γ • a) - φ a)) * φ b) := by
        rw [hsum, smul_add, smul_add]
    _ = φ a * φ b + φ a * D b + D a * φ b := by
        rw [mul_smul_comm, smul_mul_assoc, Fintype.invOf_card_smul_sum_const]
    _ = (φ a + D a) * (φ b + D b) := by linear_combination -hDD
    _ = φ ((Representation.ofDistribMulAction R Γ A).averageMap a) *
          φ ((Representation.ofDistribMulAction R Γ A).averageMap b) := by rw [havg a, havg b]

/-- Square-zero Reynolds averaging via `Representation.averageMap`. -/
private noncomputable def averagedLift (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) : A →ₐ[R] C :=
  AlgHom.ofLinearMap (φ.toLinearMap ∘ₗ (Representation.ofDistribMulAction R Γ A).averageMap)
    (by rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Representation.averageMap_id _ 1 (by simp), map_one])
    (fun a b ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      exact averagedLift_map_mul hJ φ hφ a b)

private theorem mk_averagedLift (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (a : A) :
    Ideal.Quotient.mk J (averagedLift hJ φ hφ a) = Ideal.Quotient.mk J (φ a) := by
  have happly : averagedLift hJ φ hφ a =
      φ ((Representation.ofDistribMulAction R Γ A).averageMap a) := rfl
  rw [Ideal.Quotient.eq, happly, Representation.averageMap_apply, map_smul, map_sum]
  simp only [Representation.ofDistribMulAction_apply_apply]
  have hsub : ⅟(Fintype.card Γ : R) • (∑ γ : Γ, φ (γ • a)) - φ a =
      ⅟(Fintype.card Γ : R) • ∑ γ : Γ, (φ (γ • a) - φ a) := by
    conv_lhs => rw [← Fintype.invOf_card_smul_sum_const (ι := Γ) (R := R) (φ a)]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
  rw [hsub, Algebra.smul_def]
  exact J.mul_mem_left _ (sum_mem fun γ _ ↦ hφ γ a)

private theorem averagedLift_smul (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (θ : Γ) (a : A) :
    averagedLift hJ φ hφ (θ • a) = averagedLift hJ φ hφ a :=
  congrArg φ
    (LinearMap.congr_fun ((Representation.ofDistribMulAction R Γ A).averageMap_comp_ρ θ) a)

end Lift

section Smooth

variable {R Γ A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A]

/-- **Edixhoven's tame fixed-point formal smoothness theorem.** If a group `Γ` acts on a formally
smooth `R`-algebra `A` and `(Nat.card Γ : R)` is a unit in `R`, then `A ⧸ fixedPointIdeal Γ A` is
formally smooth over `R`. -/
theorem formallySmooth_quotient_fixedPointIdeal [Algebra.FormallySmooth R A]
    (hΓ : IsUnit (Nat.card Γ : R)) : Algebra.FormallySmooth R (A ⧸ fixedPointIdeal Γ A) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (A ⧸ fixedPointIdeal Γ A) := Module.subsingleton R _
    infer_instance
  have : Finite Γ := finite_of_natCast_card_ne_zero hΓ.ne_zero
  cases nonempty_fintype Γ
  let _ : Invertible (Fintype.card Γ : R) := (Nat.card_eq_fintype_card (α := Γ) ▸ hΓ).invertible
  refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun C _ _ J hJ f ↦ ?_
  obtain ⟨φ, hφ⟩ := Algebra.FormallySmooth.comp_surjective R A J hJ
    (f.comp (Ideal.Quotient.mkₐ R (fixedPointIdeal Γ A)))
  have hφJ (γ : Γ) (a : A) : φ (γ • a) - φ a ∈ J := by
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply,
      ← AlgHom.comp_apply, hφ, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      quotientMk_fixedPointIdeal_smul]
  refine ⟨(fixedPointQuotientAlgHomEquiv R Γ A C).symm
      ⟨averagedLift hJ φ hφJ, fun γ ↦ AlgHom.ext (averagedLift_smul hJ φ hφJ γ)⟩,
    Ideal.Quotient.algHom_ext R (AlgHom.ext fun a ↦ ?_)⟩
  have hφa := congr($hφ a)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    fixedPointQuotientAlgHomEquiv_symm_apply_mk] at hφa ⊢
  exact (mk_averagedLift hJ φ hφJ a).trans hφa

/-- **Edixhoven's tame fixed-point smoothness theorem.** If a group `Γ` acts on a smooth `R`-algebra
`A` and `(Nat.card Γ : R)` is a unit in `R`, then `A ⧸ fixedPointIdeal Γ A` is smooth over `R`. -/
theorem smooth_quotient_fixedPointIdeal [Algebra.Smooth R A] (hΓ : IsUnit (Nat.card Γ : R)) :
    Algebra.Smooth R (A ⧸ fixedPointIdeal Γ A) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (A ⧸ fixedPointIdeal Γ A) := Module.subsingleton R _
    infer_instance
  have : Finite Γ := finite_of_natCast_card_ne_zero hΓ.ne_zero
  have : Algebra.FormallySmooth R (A ⧸ fixedPointIdeal Γ A) :=
    formallySmooth_quotient_fixedPointIdeal hΓ
  exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

end Smooth

end TauCeti.MulSemiringAction
