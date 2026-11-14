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

Let a group `Γ` act by `R`-algebra automorphisms on a commutative `R`-algebra `A`. The
**fixed-point ideal** `TauCeti.MulSemiringAction.fixedPointIdeal Γ A` (defined in
`TauCeti.RingTheory.Ideal.FixedPoint`) cuts out the closed subscheme `(Spec A)^Γ` of fixed points.

This complements `TauCeti.Comodule.fixedPointIdeal` (for coactions of `MonoidAlgebra R M`, i.e.
actions of diagonalizable monoid schemes `D(M)`), where formal smoothness holds over any base ring.
For an abstract finite group `Γ`, invertibility of `|Γ|` in the base ring `R` is essential: the
involution `T ↦ T⁻¹` on `𝔽₂[T; T⁻¹]` has quotient `𝔽₂[T; T⁻¹] ⧸ ((T - 1)²) ≃ 𝔽₂[ε] ⧸ (ε²)`, which
is not formally smooth over `𝔽₂`.

The main result is **Edixhoven's tame fixed-point smoothness theorem**
(`formallySmooth_quotient_fixedPointIdeal`, `smooth_quotient_fixedPointIdeal`): if `Γ` is a group
acting on a formally smooth (respectively smooth) `R`-algebra `A` by `R`-algebra automorphisms and
`(Nat.card Γ : R)` is a unit in `R`, then `A ⧸ fixedPointIdeal Γ A` is formally smooth
(respectively smooth) over `R`. Note that `[Finite Γ]` is deduced automatically from
`IsUnit (Nat.card Γ : R)` when `R` is nontrivial, while over a subsingleton base ring every algebra
is smooth.

The proof uses the infinitesimal lifting criterion together with square-zero Reynolds averaging via
`Representation.averageMap`. An `R`-algebra map `f : A ⧸ fixedPointIdeal Γ A →ₐ[R] C ⧸ J` with
`J ^ 2 = ⊥` lifts by formal smoothness of `A` to an `R`-algebra map `φ : A →ₐ[R] C` whose
displacements `δ γ a = φ (γ • a) - φ a` lie in `J`. Composing `φ` with the averaging projection
`averageMap` sets `g a = ⅟|Γ| • ∑ γ : Γ, φ (γ • a) = φ a + D a` with
`D a = ⅟|Γ| • ∑ γ : Γ, δ γ a ∈ J`; both `δ γ a * δ γ b` and `D a * D b` vanish because `J ^ 2 = ⊥`,
so `g` is multiplicative, and right-invariance of `averageMap` makes `g` kill `fixedPointIdeal Γ A`,
giving an `R`-algebra lift of `f` to `C`.

## Main results

* `TauCeti.MulSemiringAction.formallySmooth_quotient_fixedPointIdeal` and
  `TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal`: **Edixhoven's theorem** that the
  fixed-point quotient of a formally smooth (or smooth) `R`-algebra under a group of invertible
  order is formally smooth (or smooth) over `R`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
-/

public section

namespace TauCeti.MulSemiringAction

section Lift

private theorem averagedLift_map_mul {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing C] [Algebra R C] [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
    [Invertible (Fintype.card Γ : R)] {J : Ideal C} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (a b : A) :
    φ ((Representation.ofDistribMulAction R Γ A).averageMap (a * b)) =
      φ ((Representation.ofDistribMulAction R Γ A).averageMap a) *
        φ ((Representation.ofDistribMulAction R Γ A).averageMap b) := by
  let w : R := ⅟(Fintype.card Γ : R)
  have hw : w = ⅟(Fintype.card Γ : R) := rfl
  let D : A → C := fun x ↦ w • ∑ γ : Γ, (φ (γ • x) - φ x)
  have hD (x : A) : D x = w • ∑ γ : Γ, (φ (γ • x) - φ x) := rfl
  have hDJ (x : A) : D x ∈ J := by
    rw [hD, Algebra.smul_def]
    exact J.mul_mem_left _ (sum_mem fun γ _ ↦ hφ γ x)
  have havg (x : A) : φ ((Representation.ofDistribMulAction R Γ A).averageMap x) = φ x + D x := by
    rw [hD, Representation.averageMap_apply, map_smul, map_sum, ← hw]
    simp only [Representation.ofDistribMulAction_apply_apply]
    have hsum : (∑ γ : Γ, φ (γ • x)) = (∑ _γ : Γ, φ x) + ∑ γ : Γ, (φ (γ • x) - φ x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ (add_sub_cancel _ _).symm
    rw [hsum, smul_add, hw, Fintype.invOf_card_smul_sum_const, ← hw]
  have hterm (γ : Γ) :
      φ (γ • (a * b)) =
        φ a * φ b + φ a * (φ (γ • b) - φ b) + (φ (γ • a) - φ a) * φ b := by
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
  rw [Representation.averageMap_apply, map_smul, map_sum, ← hw]
  simp only [Representation.ofDistribMulAction_apply_apply]
  calc w • ∑ γ : Γ, φ (γ • (a * b))
      = w • (∑ _γ : Γ, φ a * φ b) + w • (φ a * ∑ γ : Γ, (φ (γ • b) - φ b)) +
          w • ((∑ γ : Γ, (φ (γ • a) - φ a)) * φ b) := by rw [hsum, smul_add, smul_add]
    _ = φ a * φ b + φ a * D b + D a * φ b := by
        rw [hD a, hD b, mul_smul_comm, smul_mul_assoc, hw, Fintype.invOf_card_smul_sum_const]
    _ = φ a * φ b + φ a * D b + D a * φ b + D a * D b := by rw [hDD, add_zero]
    _ = (φ a + D a) * (φ b + D b) := by ring
    _ = φ ((Representation.ofDistribMulAction R Γ A).averageMap a) *
          φ ((Representation.ofDistribMulAction R Γ A).averageMap b) := by rw [havg a, havg b]

/-- Square-zero Reynolds averaging: given an `R`-algebra map `φ : A →ₐ[R] C` whose `Γ`-displacements
lie in a square-zero ideal `J`, composing `φ` with `Representation.averageMap` yields an `R`-algebra
map `A →ₐ[R] C`. -/
private noncomputable def averagedLift {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing C] [Algebra R C] [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
    [Invertible (Fintype.card Γ : R)] {J : Ideal C} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) : A →ₐ[R] C :=
  AlgHom.ofLinearMap
    (φ.toLinearMap ∘ₗ (Representation.ofDistribMulAction R Γ A).averageMap)
    (by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Representation.averageMap_id _ 1 (by simp), map_one])
    (averagedLift_map_mul hJ φ hφ)

private theorem averagedLift_apply {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing C] [Algebra R C] [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
    [Invertible (Fintype.card Γ : R)] {J : Ideal C} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (a : A) :
    averagedLift hJ φ hφ a = φ ((Representation.ofDistribMulAction R Γ A).averageMap a) :=
  rfl

/-- Modulo `J`, `averagedLift` agrees with the unaveraged lift `φ`. -/
private theorem mk_averagedLift {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing C] [Algebra R C] [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
    [Invertible (Fintype.card Γ : R)] {J : Ideal C} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (a : A) :
    Ideal.Quotient.mk J (averagedLift hJ φ hφ a) = Ideal.Quotient.mk J (φ a) := by
  rw [Ideal.Quotient.eq, averagedLift_apply, Representation.averageMap_apply, map_smul, map_sum]
  simp only [Representation.ofDistribMulAction_apply_apply]
  have hsub : ⅟(Fintype.card Γ : R) • (∑ γ : Γ, φ (γ • a)) - φ a =
      ⅟(Fintype.card Γ : R) • ∑ γ : Γ, (φ (γ • a) - φ a) := by
    conv_lhs => rw [← Fintype.invOf_card_smul_sum_const (ι := Γ) (R := R) (φ a)]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
  rw [hsub, Algebra.smul_def]
  exact J.mul_mem_left _ (sum_mem fun γ _ ↦ hφ γ a)

/-- Right-invariance of `Representation.averageMap` makes `averagedLift` invariant under `Γ`. -/
private theorem averagedLift_smul {R Γ A C : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing C] [Algebra R C] [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A] [Fintype Γ]
    [Invertible (Fintype.card Γ : R)] {J : Ideal C} (hJ : J ^ 2 = ⊥) (φ : A →ₐ[R] C)
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) - φ a ∈ J) (θ : Γ) (a : A) :
    averagedLift hJ φ hφ (θ • a) = averagedLift hJ φ hφ a := by
  rw [averagedLift_apply, averagedLift_apply]
  exact congrArg φ
    (LinearMap.congr_fun ((Representation.ofDistribMulAction R Γ A).averageMap_comp_ρ θ) a)

end Lift

section Smooth

variable {R Γ A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Group Γ] [MulSemiringAction Γ A] [SMulCommClass Γ R A]

/-- **Edixhoven's tame fixed-point formal smoothness theorem.** Let a group `Γ` act on a formally
smooth commutative `R`-algebra `A` by `R`-algebra automorphisms. If `(Nat.card Γ : R)` is a unit in
`R`, then the fixed-point quotient `A ⧸ fixedPointIdeal Γ A` is formally smooth over `R`. -/
theorem formallySmooth_quotient_fixedPointIdeal [Algebra.FormallySmooth R A]
    (hΓ : IsUnit (Nat.card Γ : R)) :
    Algebra.FormallySmooth R (A ⧸ fixedPointIdeal Γ A) := by
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
  let g := averagedLift hJ φ hφJ
  have hg : ∀ γ : Γ, g.comp (MulSemiringAction.toAlgHom R A γ) = g := fun γ ↦
    AlgHom.ext (averagedLift_smul hJ φ hφJ γ)
  refine ⟨(fixedPointQuotientAlgHomEquiv R Γ A C).symm ⟨g, hg⟩,
    Ideal.Quotient.algHom_ext R ?_⟩
  ext a
  have hφa := congr($hφ a)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    fixedPointQuotientAlgHomEquiv_symm_apply_mk] at hφa ⊢
  exact (mk_averagedLift hJ φ hφJ a).trans hφa

/-- **Edixhoven's tame fixed-point smoothness theorem.** Let a group `Γ` act on a smooth commutative
`R`-algebra `A` by `R`-algebra automorphisms. If `(Nat.card Γ : R)` is a unit in `R`, then the
fixed-point quotient `A ⧸ fixedPointIdeal Γ A` is smooth over `R`. -/
theorem smooth_quotient_fixedPointIdeal [Algebra.Smooth R A]
    (hΓ : IsUnit (Nat.card Γ : R)) :
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
