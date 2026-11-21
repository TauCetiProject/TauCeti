/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.SkewPolynomial.Basic

/-!
# Skew polynomials acting on a semilinear operator

A semilinear endomorphism gives an action of the corresponding skew polynomial ring on the
underlying additive group: the coefficient action is scalar multiplication and the variable
acts by the endomorphism. We also record the monic product rule used to compose annihilators.
The construction uses `SkewMonoidAlgebra.liftNCRingHom`.
-/

public section

open Multiplicative

namespace RingHom

variable {R : Type*} [Semiring R]

/-- The action of additive natural numbers by iterating a ring endomorphism. -/
@[instance_reducible]
def iterateMulSemiringAction (σ : R →+* R) : MulSemiringAction (Multiplicative ℕ) R where
  smul n r := (powersHom (R →+* R) σ n) r
  one_smul r := congrArg (fun f : R →+* R ↦ f r) ((powersHom (R →+* R) σ).map_one)
  mul_smul n m r := congrArg (fun f : R →+* R ↦ f r) ((powersHom (R →+* R) σ).map_mul n m)
  smul_zero n := map_zero (powersHom (R →+* R) σ n)
  smul_add n := map_add (powersHom (R →+* R) σ n)
  smul_one n := map_one (powersHom (R →+* R) σ n)
  smul_mul n := map_mul (powersHom (R →+* R) σ n)

/-- The scalar indexed by `n` acts by the `n`-fold iterate. -/
@[simp]
theorem iterateMulSemiringAction_smul (σ : R →+* R) (n : ℕ) (r : R) :
    (σ.iterateMulSemiringAction).toSMul.smul (ofAdd n) r = σ^[n] r := by
  exact congrFun (RingHom.coe_pow σ n) r

end RingHom

namespace SkewPolynomial

variable {R : Type*} [Semiring R]

/-- The twist from the iteration action is the original ring endomorphism. -/
@[simp]
theorem φ_iterateMulSemiringAction (σ : R →+* R) :
    letI := σ.iterateMulSemiringAction
    (φ : R →+* R) = σ := by
  ext r
  exact (σ.iterateMulSemiringAction_smul 1 r).trans (by simp)

/-- A skew polynomial has leading coefficient `1` at degree `n` and no terms above it.
The specified degree convention also makes sense over the zero ring. -/
def IsMonicOfDegree (q : SkewPolynomial R) (n : ℕ) : Prop :=
  q.coeff n = 1 ∧ ∀ k ∈ q.support, k ≤ n

/-- The coefficient and support characterization of a monic skew polynomial. -/
theorem isMonicOfDegree_iff {q : SkewPolynomial R} {n : ℕ} :
    q.IsMonicOfDegree n ↔ q.coeff n = 1 ∧ ∀ k ∈ q.support, k ≤ n := Iff.rfl

/-- Products of monic skew polynomials are monic, with degrees adding. -/
theorem IsMonicOfDegree.mul [MulSemiringAction (Multiplicative ℕ) R]
    {q r : SkewPolynomial R} {m n : ℕ} (hq : q.IsMonicOfDegree m) (hr : r.IsMonicOfDegree n) :
    (q * r).IsMonicOfDegree (m + n) := by
  obtain ⟨hqm, hqb⟩ := isMonicOfDegree_iff.mp hq
  obtain ⟨hrn, hrb⟩ := isMonicOfDegree_iff.mp hr
  rw [isMonicOfDegree_iff, mul_def]
  have hc (k : ℕ) :
      (q.sum fun i a ↦ r.sum fun j b ↦ monomial (i + j) (a * φ^[i] b)).coeff k =
        ∑ i ∈ q.support, ∑ j ∈ r.support,
          if i + j = k then q.coeff i * φ^[i] (r.coeff j) else 0 := by
    simp only [sum_def, coeff, ← SkewMonoidAlgebra.coeffAddEquiv_apply, map_sum,
      Finsupp.finsetSum_apply]
    -- The remaining equality removes the multiplicative tags on the same indices.
    simp [monomial_def, Finsupp.single_apply, eq_comm]
    rfl
  refine ⟨?_, fun k hk ↦ not_lt.mp fun h ↦ ?_⟩
  · rw [hc]
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    have hm : m ∈ q.support := mem_support_iff.mpr (by simp [hqm])
    have hn : n ∈ r.support := mem_support_iff.mpr (by simp [hrn])
    rw [Finset.sum_eq_single_of_mem m hm]
    · rw [Finset.sum_eq_single_of_mem n hn]
      · simp [hqm, hrn, iterate_map_one]
      · intro j _ hjn
        simp [hjn]
    · intro i hi him
      exact Finset.sum_eq_zero fun j hj ↦
        ite_eq_right (by have := hqb i hi; have := hrb j hj; omega)
  · apply mem_support_iff.mp hk
    rw [hc]
    exact Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦
      ite_eq_right (by have := hqb i hi; have := hrb j hj; omega)

variable {M : Type*} [AddCommMonoid M] [Module R M]
variable [MulSemiringAction (Multiplicative ℕ) R]

/-- Evaluate a skew polynomial at a semilinear endomorphism, as an additive endomorphism. -/
noncomputable def evalSemilinear (F : M →ₛₗ[(φ : R →+* R)] M) :
    SkewPolynomial R →+* AddMonoid.End M :=
  SkewMonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd R M)
    (powersHom (AddMonoid.End M) F.toAddMonoidHom) (by
      intro a n
      induction n using Multiplicative.rec with
      | _ n =>
        ext x
        -- Composition of additive endomorphisms reduces to the iterated semilinear law.
        let T : AddMonoid.End M := F.toAddMonoidHom
        change (ofAdd n • a) • (T ^ n : AddMonoid.End M) x = (T ^ n : AddMonoid.End M) (a • x)
        rw [← φ_iterate_apply, AddMonoid.End.coe_pow]
        -- The coercions of the linear map and its additive endomorphism agree.
        change φ^[n] a • F^[n] x = F^[n] (a • x)
        induction n with
        | zero => rfl
        | succ n ih => simp only [Function.iterate_succ_apply', ← ih, LinearMap.map_smulₛₗ])

/-- Evaluation of a single skew monomial is a scalar times an iterate of the operator. -/
@[simp]
theorem evalSemilinear_monomial_apply (F : M →ₛₗ[(φ : R →+* R)] M)
    (n : ℕ) (a : R) (x : M) :
    evalSemilinear F (monomial n a) x = a • F^[n] x := by
  let T : AddMonoid.End M := F.toAddMonoidHom
  -- Expose the additive lift beneath the ring homomorphism to use its single-term rule.
  change (SkewMonoidAlgebra.liftNC (Module.toAddMonoidEnd R M).toAddMonoidHom
    (powersHom (AddMonoid.End M) T) (SkewMonoidAlgebra.single (ofAdd n) a)) x = _
  rw [SkewMonoidAlgebra.liftNC_single, powersHom_apply]
  change a • (T ^ n : AddMonoid.End M) x = a • F^[n] x
  rw [AddMonoid.End.coe_pow]
  rfl

/-- Evaluation intertwines every linear map commuting with the semilinear operators. -/
theorem evalSemilinear_apply_map {N : Type*} [AddCommMonoid N] [Module R N]
    {F : M →ₛₗ[(φ : R →+* R)] M} {G : N →ₛₗ[(φ : R →+* R)] N}
    {f : M →ₗ[R] N} (hf : Function.Semiconj f F G) (q : SkewPolynomial R) (x : M) :
    f (evalSemilinear F q x) = evalSemilinear G q (f x) := by
  induction q using SkewPolynomial.induction with
  | h0 => simp
  | ha n a q _ _ ih =>
    rw [map_add, map_add]
    -- Addition in the endomorphism semiring is pointwise addition of additive maps.
    change f (evalSemilinear F (monomial n a) x + evalSemilinear F q x) =
      evalSemilinear G (monomial n a) (f x) + evalSemilinear G q (f x)
    simp [ih, hf.iterate_right n x]

end SkewPolynomial

namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {σ : R →+* R}

/-- Regard a semilinear endomorphism as semilinear for the twist of the iteration action. -/
def withIterateTwist (F : M →ₛₗ[σ] M) :
    letI := σ.iterateMulSemiringAction
    M →ₛₗ[(SkewPolynomial.φ : R →+* R)] M where
  toAddHom := F.toAddHom
  map_smul' a x := by
    simpa only [SkewPolynomial.φ_iterateMulSemiringAction] using F.map_smul' a x

/-- Changing the presentation of the twist does not change the underlying operator. -/
@[simp]
theorem withIterateTwist_apply (F : M →ₛₗ[σ] M) (x : M) :
    F.withIterateTwist x = F x := (rfl)

end LinearMap
