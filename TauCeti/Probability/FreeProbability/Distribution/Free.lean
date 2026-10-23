/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Basic
public import TauCeti.Probability.FreeProbability.Variables

/-!
# Joint distributions of free families

Free independence depends only on the joint algebraic distribution. For normalized
functionals, freely independent families in possibly different algebras have the same joint
distribution exactly when their one-variable moments agree. Consequently, polynomial
expressions in free families have distributions independent of the chosen realization.

The comparison pulls both functionals back to the same free algebra and uses
`IsFreelyIndependentElements.eq_of_adjoin_range_eq_top`. No isomorphism between the ambient
algebras, positivity, or traciality is required. Normalization is imposed separately, so the
empty family is covered as well.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 5.
-/

public section

namespace TauCeti

variable {R A B ι : Type*}

section Semiring

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- A family is free precisely when the formal generators are free for its joint
distribution. Evaluation need not be injective. -/
theorem isFreelyIndependentElements_jointDistribution_iff (φ : A →ₗ[R] R) (a : ι → A) :
    IsFreelyIndependentElements (jointDistribution φ a) (FreeAlgebra.ι R) ↔
      IsFreelyIndependentElements φ a := by
  simpa only [jointDistribution_def, FreeAlgebra.ι_comp_lift] using
    (isFreelyIndependentElements_map_iff φ (FreeAlgebra.lift R a) (FreeAlgebra.ι R)).symm

/-- Families with equal joint distributions are either both free or both nonfree,
even when their ambient algebras differ. -/
theorem isFreelyIndependentElements_iff_of_jointDistribution_eq
    {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    (h : jointDistribution φ a = jointDistribution ψ b) :
    IsFreelyIndependentElements φ a ↔ IsFreelyIndependentElements ψ b := by
  rw [← isFreelyIndependentElements_jointDistribution_iff φ a,
    ← isFreelyIndependentElements_jointDistribution_iff ψ b, h]

end Semiring

section Ring

variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

namespace IsFreelyIndependentElements

/-- Free families with the same one-variable polynomial moments have the same joint
distribution. The two families may live in different algebras. -/
theorem jointDistribution_eq_of_forall_aeval {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (ha : IsFreelyIndependentElements φ a)
    (hb : IsFreelyIndependentElements ψ b) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hmom : ∀ i (p : Polynomial R), φ (Polynomial.aeval (R := R) (a i) p) =
      ψ (Polynomial.aeval (R := R) (b i) p)) :
    jointDistribution φ a = jointDistribution ψ b := by
  refine eq_of_adjoin_range_eq_top (by simp [hφ]) (by simp [hψ])
    ((isFreelyIndependentElements_jointDistribution_iff φ a).2 ha)
    ((isFreelyIndependentElements_jointDistribution_iff ψ b).2 hb) ?_
    (FreeAlgebra.adjoin_range_ι R ι)
  intro i p
  simpa only [jointDistribution_apply, ← AlgHom.comp_apply,
    ← Polynomial.aeval_algHom, FreeAlgebra.lift_ι_apply] using hmom i p

/-- Free families with equal power moments have equal joint distributions. Normalization
also determines the empty word when the index type is empty. -/
theorem jointDistribution_eq_of_forall_pow {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (ha : IsFreelyIndependentElements φ a)
    (hb : IsFreelyIndependentElements ψ b) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hmom : ∀ i (n : ℕ), φ (a i ^ n) = ψ (b i ^ n)) :
    jointDistribution φ a = jointDistribution ψ b := by
  apply ha.jointDistribution_eq_of_forall_aeval hb hφ hψ
  intro i p
  have h : φ.comp (Polynomial.aeval (R := R) (a i)).toLinearMap =
      ψ.comp (Polynomial.aeval (R := R) (b i)).toLinearMap := by
    apply Polynomial.lhom_ext'
    intro n
    apply LinearMap.ext
    intro r
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Polynomial.aeval_monomial,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul] using
      congrArg (r • ·) (hmom i n)
  exact LinearMap.congr_fun h p

/-- For free families, equality of joint distributions is equivalent to equality of
the individual power moments. -/
theorem jointDistribution_eq_iff_forall_pow {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (ha : IsFreelyIndependentElements φ a)
    (hb : IsFreelyIndependentElements ψ b) (hφ : φ 1 = 1) (hψ : ψ 1 = 1) :
    jointDistribution φ a = jointDistribution ψ b ↔
      ∀ i (n : ℕ), φ (a i ^ n) = ψ (b i ^ n) := by
  refine ⟨fun h i n => ?_, ha.jointDistribution_eq_of_forall_pow hb hφ hψ⟩
  simpa using LinearMap.congr_fun h (FreeAlgebra.ι R i ^ n)

end IsFreelyIndependentElements

end Ring

end TauCeti
