/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The cyclic quotient of an algebra

For a (not necessarily unital or associative) ring `A` which is a module over a ring `k`, the
**commutator submodule** of `A` is the `k`-span of the additive commutators `x * y - y * x`.  The
quotient by this submodule is the **cyclic quotient**

```text
A / [A, A].
```

Its elements are cyclic classes.  For a path algebra `kQ`, a potential for the three-dimensional
Ginzburg construction is naturally a cyclic class rather than a chosen representative in `kQ`.
This file provides the quotient and its elementary universal property; cyclic derivatives of a path
algebra are descended to it in `TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Derivative`.

## Main definitions

* `TauCeti.commutatorSubmodule`: the span of additive commutators in `A`.
* `TauCeti.cyclicQuotient`: the quotient `A / [A, A]`.

## Main results

* `TauCeti.neg_mem_commutatorSubmodule`, `TauCeti.zsmul_mem_commutatorSubmodule` and
  `TauCeti.neg_one_pow_mul_mem_commutatorSubmodule`: the commutator submodule is closed under
  negation, under integer multiples and under multiplication by signs, even over a semiring of
  scalars.
* `TauCeti.mul_mem_commutatorSubmodule_comm`: a product is a sum of commutators exactly when its
  rotation is.
* `TauCeti.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator submodule exactly
  when it takes equal values on `x * y` and `y * x`.
* `TauCeti.map_mem_commutatorSubmodule`: a multiplicative linear map, such as an algebra
  homomorphism, carries commutators to commutators.
* `TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule`: the trace of a matrix representation
  vanishes on the commutator submodule.  A representation in which an element has nonzero trace
  therefore shows that its cyclic class is nonzero.
* `TauCeti.cyclicQuotientRingHomMap`: functoriality of `cyclicQuotient ℤ` in ring homomorphisms.
* `TauCeti.cyclicQuotientEquivOfCommRing`: for a (possibly non-unital) commutative ring `B`,
  `B / [B, B] ≃ₗ[k] B`.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the identification
  `HH₀(A) = A / [A, A]`.
-/

public section

namespace TauCeti

section General

variable (k : Type*) (A : Type*) [NonUnitalNonAssocRing A]

section Semiring

variable [Semiring k] [Module k A]

/-- The `k`-submodule of `A` spanned by the additive commutators `x * y - y * x`. -/
def commutatorSubmodule : Submodule k A :=
  Submodule.span k (Set.range fun p : A × A => p.1 * p.2 - p.2 * p.1)

/-- Every additive commutator belongs to the commutator submodule. -/
theorem mul_sub_mul_mem_commutatorSubmodule (x y : A) :
    x * y - y * x ∈ commutatorSubmodule k A :=
  Submodule.subset_span ⟨(x, y), rfl⟩

variable {k A} in
/-- The commutator submodule is closed under negation even when `k` is only a semiring: the
negative of a commutator `x * y - y * x` is the commutator `y * x - x * y`. -/
theorem neg_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) :
    -x ∈ commutatorSubmodule k A := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hz
    simpa using mul_sub_mul_mem_commutatorSubmodule k A b a
  | zero => simp
  | add y z _ _ hy hz => rw [neg_add]; exact add_mem hy hz
  | smul r y _ hy => simpa [smul_neg] using Submodule.smul_mem _ r hy

variable {k A} in
/-- The commutator submodule is closed under integer multiples even when `k` is only a
semiring. -/
theorem zsmul_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) (n : ℤ) :
    n • x ∈ commutatorSubmodule k A := by
  cases n with
  | ofNat m => simpa using (commutatorSubmodule k A).toAddSubmonoid.nsmul_mem hx m
  | negSucc m =>
    rw [negSucc_zsmul]
    exact neg_mem_commutatorSubmodule
      ((commutatorSubmodule k A).toAddSubmonoid.nsmul_mem hx (m + 1))

variable {k} in
/-- The commutator submodule is closed under multiplication by a sign `(-1) ^ e`, even when `k` is
only a semiring. -/
theorem neg_one_pow_mul_mem_commutatorSubmodule {B : Type*} [Ring B] [Module k B] {x : B}
    (hx : x ∈ commutatorSubmodule k B) (e : ℕ) : (-1 : B) ^ e * x ∈ commutatorSubmodule k B := by
  rcases neg_one_pow_eq_or B e with h | h
  · simpa [h] using hx
  · simpa [h] using neg_mem_commutatorSubmodule hx

variable {k A} in
/-- **Rotation**: a product lies in the commutator submodule exactly when the product of its
factors in the other order does, since the two differ by the commutator `x * y - y * x`. -/
theorem mul_mem_commutatorSubmodule_comm {x y : A} :
    x * y ∈ commutatorSubmodule k A ↔ y * x ∈ commutatorSubmodule k A := by
  constructor <;> intro h
  · simpa using add_mem h (mul_sub_mul_mem_commutatorSubmodule k A y x)
  · simpa using add_mem h (mul_sub_mul_mem_commutatorSubmodule k A x y)

variable {k A} in
/-- A linear map kills the commutator submodule exactly when it is invariant under exchanging the
two factors of a product. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommGroup M] [Module k M]
    (f : A →ₗ[k] M) :
    commutatorSubmodule k A ≤ LinearMap.ker f ↔ ∀ x y : A, f (x * y) = f (y * x) := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
  constructor
  · intro h x y
    have hzero := LinearMap.mem_ker.1 (h (x, y))
    rwa [map_sub, sub_eq_zero] at hzero
  · intro h p
    apply LinearMap.mem_ker.2
    rw [map_sub, h, sub_self]

variable {k A} in
/-- A multiplicative linear map, such as an algebra homomorphism, carries the commutator submodule
into the commutator submodule. -/
theorem map_mem_commutatorSubmodule {B F : Type*} [NonUnitalNonAssocRing B] [Module k B]
    [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule k B := by
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k B).comap (f : A →ₗ[k] B) := by
    rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
    rintro ⟨x, y⟩
    simpa using mul_sub_mul_mem_commutatorSubmodule k B (f x) (f y)
  exact hle hx

end Semiring

section Matrix

variable {k A} [CommRing k] [Module k A]

/-- **The trace of a matrix representation kills commutators**: if `f` is a multiplicative linear
map to square matrices, then the trace of `f x` vanishes for every `x` in the commutator submodule.
-/
theorem trace_map_eq_zero_of_mem_commutatorSubmodule {n F : Type*} [Fintype n]
    [FunLike F A (Matrix n n k)] [MulHomClass F A (Matrix n n k)]
    [LinearMapClass F k A (Matrix n n k)] (f : F) {x : A} (hx : x ∈ commutatorSubmodule k A) :
    (f x).trace = 0 :=
  (commutatorSubmodule_le_ker_iff (Matrix.traceLinearMap n k k)).2
    (fun X Y => Matrix.trace_mul_comm X Y) (map_mem_commutatorSubmodule f hx)

end Matrix

/-- The **cyclic quotient** `A / [A, A]`.  Its elements are cyclic classes; for a path algebra,
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient [Ring k] [Module k A] := A ⧸ commutatorSubmodule k A

end General

section RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- Every ring homomorphism carries the integer commutator submodule into the integer commutator
submodule. -/
theorem ringHom_mem_commutatorSubmodule (φ : R →+* S) {x : R}
    (hx : x ∈ commutatorSubmodule ℤ R) : φ x ∈ commutatorSubmodule ℤ S := by
  have hle : commutatorSubmodule ℤ R ≤
      (commutatorSubmodule ℤ S).comap (φ : R →+ S).toIntLinearMap := by
    rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
    rintro ⟨a, b⟩
    simpa using mul_sub_mul_mem_commutatorSubmodule ℤ S (φ a) (φ b)
  exact hle hx

/-- The additive map `R / [R, R] → S / [S, S]` induced on integer cyclic quotients by a ring
homomorphism `φ : R →+* S`. -/
def cyclicQuotientRingHomMap (φ : R →+* S) : cyclicQuotient ℤ R →ₗ[ℤ] cyclicQuotient ℤ S :=
  Submodule.mapQ (commutatorSubmodule ℤ R) (commutatorSubmodule ℤ S) (φ : R →+ S).toIntLinearMap
    fun _ hx ↦ ringHom_mem_commutatorSubmodule φ hx

@[simp]
theorem cyclicQuotientRingHomMap_mk (φ : R →+* S) (x : R) :
    cyclicQuotientRingHomMap φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ x) :=
  (rfl)

theorem cyclicQuotientRingHomMap_mkQ (φ : R →+* S) (x : R) :
    cyclicQuotientRingHomMap φ ((commutatorSubmodule ℤ R).mkQ x) =
      (commutatorSubmodule ℤ S).mkQ (φ x) :=
  (rfl)

@[simp]
theorem cyclicQuotientRingHomMap_id :
    cyclicQuotientRingHomMap (RingHom.id R) = LinearMap.id := by
  ext x
  rfl

theorem cyclicQuotientRingHomMap_comp (ψ : S →+* T) (φ : R →+* S) :
    cyclicQuotientRingHomMap (ψ.comp φ) =
      (cyclicQuotientRingHomMap ψ).comp (cyclicQuotientRingHomMap φ) := by
  ext x
  rfl

end RingHom

section CommRing

/-- In a (possibly non-unital) commutative ring every additive commutator vanishes, so the
commutator submodule is trivial. -/
@[simp]
theorem commutatorSubmodule_eq_bot (k B : Type*) [Semiring k] [NonUnitalCommRing B] [Module k B] :
    commutatorSubmodule k B = ⊥ := by
  rw [commutatorSubmodule, Submodule.span_eq_bot]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact sub_eq_zero.2 (mul_comm x y)

/-- For a (possibly non-unital) commutative ring `B`, the cyclic quotient `B / [B, B]` is
canonically isomorphic to `B`. -/
def cyclicQuotientEquivOfCommRing (k B : Type*) [Ring k] [NonUnitalCommRing B] [Module k B] :
    cyclicQuotient k B ≃ₗ[k] B :=
  Submodule.quotEquivOfEqBot (commutatorSubmodule k B) (commutatorSubmodule_eq_bot k B)

@[simp]
theorem cyclicQuotientEquivOfCommRing_mk (k B : Type*) [Ring k] [NonUnitalCommRing B] [Module k B]
    (x : B) :
    cyclicQuotientEquivOfCommRing k B (Submodule.Quotient.mk x) = x :=
  (rfl)

theorem cyclicQuotientEquivOfCommRing_mkQ (k B : Type*) [Ring k] [NonUnitalCommRing B] [Module k B]
    (x : B) :
    cyclicQuotientEquivOfCommRing k B ((commutatorSubmodule k B).mkQ x) = x :=
  (rfl)

@[simp]
theorem cyclicQuotientEquivOfCommRing_symm_apply (k B : Type*) [Ring k] [NonUnitalCommRing B]
    [Module k B] (x : B) :
    (cyclicQuotientEquivOfCommRing k B).symm x = (commutatorSubmodule k B).mkQ x :=
  (rfl)

end CommRing

end TauCeti
