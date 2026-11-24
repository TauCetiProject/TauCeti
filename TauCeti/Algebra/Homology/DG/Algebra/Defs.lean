/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.RingTheory.GradedAlgebra.SignedDerivation.Basic
public import TauCeti.RingTheory.GradedAlgebra.Trivial
import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.Data.List.ProdOfFn
import TauCeti.Algebra.GradedMonoid

/-!
# Nonunital and unital differential graded algebras

A nonunital differential graded algebra over a commutative ring `R` is an internally
`ℤ`-graded nonunital `R`-algebra `A` together with an `R`-linear differential `d` of degree
`+1` which squares to zero and satisfies the graded Leibniz rule

`d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.

This file fixes the nonunital structure as `TauCeti.IsNonUnitalDGAlgebra`.  Every unital
`TauCeti.IsDGAlgebra` has a canonical underlying nonunital DG algebra, while consequences that
genuinely use the unit remain in the unital namespace.  In particular, the differential of a
unital DG algebra annihilates the unit and hence the image of the ground ring.

The grading is stored *internally*, as a family `𝒜 : ℤ → Submodule R A` of submodules of a
single carrier.  In the nonunital case it consists of a direct-sum decomposition together with
degree-additive multiplication; the unital case uses Mathlib's `GradedAlgebra 𝒜`.  The product is
therefore the product of `A`, so no signed totalization is needed to state the Leibniz rule, and
`Int.negOnePow` carries the only sign.

Only a homogeneous *left* factor is constrained by the Leibniz axiom, because the sign depends on
its degree alone.

## Main definitions

* `TauCeti.IsNonUnitalDGAlgebra`: the nonunital differential graded algebra axioms.
* `TauCeti.IsDGAlgebra`: the differential graded algebra axioms on an internally `ℤ`-graded
  unital `R`-algebra and an `R`-linear endomorphism of its carrier.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.map_decompose` computes the differential on homogeneous
  components.
* `TauCeti.IsNonUnitalDGAlgebra.leibniz_of_map_eq_zero` and
  `TauCeti.IsNonUnitalDGAlgebra.map_mul_eq_zero_of_map_eq_zero` specialize the Leibniz rule
  when the right factor is a cycle.
* `TauCeti.IsNonUnitalDGAlgebra.leibniz_of_mem_zero` specializes the Leibniz rule when the left
  factor has degree zero.
* `TauCeti.IsDGAlgebra.map_one_eq_zero` and `TauCeti.IsDGAlgebra.map_algebraMap`: the differential
  annihilates the unit and, more generally, the image of the ground ring.
* `TauCeti.IsDGAlgebra.neg`: the negative of a differential is a differential.
* `TauCeti.IsDGAlgebra.map_list_prod_ofFn`: the differential of an ordered product of homogeneous
  elements is given by the graded Leibniz rule, one factor at a time.
* `TauCeti.isNonUnitalDGAlgebra_zero` and `TauCeti.isDGAlgebra_zero`: a graded algebra with zero
  differential is a differential graded algebra.
* `TauCeti.isDGAlgebra_trivialGrading`: in particular, the ground ring, trivially graded with zero
  differential, is a differential graded algebra.

For a unital DG algebra, the homogeneous consequences of the axioms are also available through
its regular differential graded left module.  Cycles, boundaries, and the cohomology algebra are
built from that module structure in `TauCeti.Algebra.Homology.DG.Algebra.Cohomology`.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

open DirectSum

namespace TauCeti

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A}

/-- A **nonunital differential graded algebra**: an internally `ℤ`-graded nonunital
`R`-algebra `𝒜` on a carrier `A`, together with an `R`-linear map `d` which raises degree by
one, squares to zero, and satisfies the graded Leibniz rule on a homogeneous left factor. -/
structure IsNonUnitalDGAlgebra (𝒜 : ℤ → Submodule R A) [IsScalarTower R A A]
    [SMulCommClass R A A] [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
    (d : A →ₗ[R] A) : Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (a : A) : d (d a) = 0
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

attribute [grind =>] IsNonUnitalDGAlgebra.map_mem

namespace IsNonUnitalDGAlgebra

/-- The differential commutes with homogeneous projections, up to the degree shift by one. -/
@[simp]
theorem map_decompose (h : IsNonUnitalDGAlgebra 𝒜 d) (p : ℤ) (a : A) :
    d (DirectSum.decompose 𝒜 a p : A) =
      (DirectSum.decompose 𝒜 (d a) (p + 1) : A) :=
  (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha).map_decompose p a

/-- The Leibniz rule against a cycle in the right factor.  The vanishing signed term permits an
arbitrary left factor, without a homogeneity hypothesis. -/
theorem leibniz_of_map_eq_zero (h : IsNonUnitalDGAlgebra 𝒜 d) (a : A) {b : A}
    (hb : d b = 0) : d (a * b) = d a * b :=
  map_mul_of_leibniz_of_map_eq_zero (𝒜 := 𝒜) h.leibniz a hb

/-- The Leibniz rule for a left factor of degree zero, where the sign is trivial. -/
theorem leibniz_of_mem_zero (h : IsNonUnitalDGAlgebra 𝒜 d) {a : A} (ha : a ∈ 𝒜 0) (b : A) :
    d (a * b) = d a * b + a * d b := by
  simpa using h.leibniz ha b

/-- The product of two cycles in a nonunital DG algebra is a cycle. -/
theorem map_mul_eq_zero_of_map_eq_zero (h : IsNonUnitalDGAlgebra 𝒜 d) {a b : A}
    (ha : d a = 0) (hb : d b = 0) : d (a * b) = 0 := by
  rw [h.leibniz_of_map_eq_zero a hb, ha, zero_mul]

end IsNonUnitalDGAlgebra

/-- An internally graded nonunital algebra with zero differential is a nonunital differential
graded algebra. -/
theorem isNonUnitalDGAlgebra_zero (𝒜 : ℤ → Submodule R A) [SetLike.GradedMul 𝒜]
    [DirectSum.Decomposition 𝒜] :
    IsNonUnitalDGAlgebra 𝒜 (0 : A →ₗ[R] A) where
  map_mem := fun _ ↦ zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ ↦ by simp

end NonUnital

section Unital

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- A **differential graded algebra**: an internally `ℤ`-graded `R`-algebra `𝒜` on a carrier `A`
together with an `R`-linear map `d` which raises degree by one, squares to zero, and satisfies the
graded Leibniz rule on a homogeneous left factor.  The sign `(-1) ^ p` is `Int.negOnePow p`, acting
through the units of `ℤ`. -/
structure IsDGAlgebra (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) : Prop where
  /-- The differential raises the degree by one. -/
  map_mem : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1)
  /-- The differential squares to zero. -/
  sq_zero (a : A) : d (d a) = 0
  /-- The graded Leibniz rule for a left factor of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

attribute [grind =>] IsDGAlgebra.map_mem

namespace IsDGAlgebra

/-- Forget the unit of a differential graded algebra. -/
theorem toIsNonUnitalDGAlgebra (h : IsDGAlgebra 𝒜 d) : IsNonUnitalDGAlgebra 𝒜 d where
  map_mem := h.map_mem
  sq_zero := h.sq_zero
  leibniz := h.leibniz

/-- The differential of a differential graded algebra annihilates the unit: the Leibniz rule for
`1 * 1` reads `d 1 = d 1 + d 1`. -/
theorem map_one_eq_zero (h : IsDGAlgebra 𝒜 d) : d 1 = 0 :=
  map_one_eq_zero_of_leibniz 𝒜 h.leibniz

/-- The differential of a differential graded algebra annihilates the image of the ground ring. -/
theorem map_algebraMap (h : IsDGAlgebra 𝒜 d) (r : R) : d (algebraMap R A r) = 0 :=
  map_algebraMap_of_leibniz 𝒜 h.leibniz r

/-- The negative of the differential of a differential graded algebra is again a differential. -/
theorem neg (h : IsDGAlgebra 𝒜 d) : IsDGAlgebra 𝒜 (-d) where
  map_mem ha := Submodule.neg_mem _ (h.map_mem ha)
  sq_zero a := by rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, h.sq_zero, neg_neg]
  leibniz ha b := by
    simp only [LinearMap.neg_apply, h.leibniz ha, neg_add, neg_mul, mul_neg, smul_neg]

/-- **The graded Leibniz rule for an ordered product** of homogeneous elements: the differential of
`b 0 ⋯ b (n - 1)` is the sum over `k` of the products with `b k` replaced by `d (b k)`, each with
the sign of the total degree of the factors before it. -/
theorem map_list_prod_ofFn (h : IsDGAlgebra 𝒜 d) {n : ℕ} (b : ℕ → A) (e : ℕ → ℤ)
    (hb : ∀ i < n, b i ∈ 𝒜 (e i)) :
    d (List.ofFn fun j : Fin n ↦ b j).prod =
      ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range k, e i).negOnePow •
        (List.ofFn fun j : Fin n ↦ Function.update b k (d (b k)) j).prod := by
  induction n with
  | zero => simp [h.map_one_eq_zero]
  | succ n ih =>
    rw [List.prod_ofFn_val_succ,
      h.leibniz (SetLike.list_prod_ofFn_val_mem_graded 𝒜 b e fun i hi ↦ hb i (by omega)),
      ih fun i hi ↦ hb i (by omega), Finset.sum_range_succ, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [smul_mul_assoc, List.prod_ofFn_val_succ (Function.update b k (d (b k))),
        Function.update_of_ne (by omega : n ≠ k)]
    · rw [List.prod_ofFn_val_succ (Function.update b n (d (b n))), Function.update_self,
        List.prod_ofFn_val_congr fun i hi ↦ Function.update_of_ne (by omega : i ≠ n) _ _]

end IsDGAlgebra

/-- A `ℤ`-graded algebra with zero differential is a differential graded algebra. -/
theorem isDGAlgebra_zero (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    IsDGAlgebra 𝒜 (0 : A →ₗ[R] A) where
  map_mem := fun _ ↦ zero_mem _
  sq_zero _ := rfl
  leibniz := fun _ _ ↦ by simp

/-- The ground ring with its trivial grading and zero differential is a differential graded
algebra. -/
theorem isDGAlgebra_trivialGrading (R : Type*) [CommRing R] :
    IsDGAlgebra (trivialGrading R R) (0 : R →ₗ[R] R) :=
  isDGAlgebra_zero _

end Unital

end TauCeti
