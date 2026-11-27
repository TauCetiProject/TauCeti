/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The cyclic quotient of an algebra

For a (not necessarily unital or associative) ring `A` which is a module over a semiring `k`, the
**commutator submodule** of `A` is the `k`-span of the additive commutators `x * y - y * x`.  When
`k` is a ring, the quotient by this submodule is the **cyclic quotient**

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
* `TauCeti.cyclicQuotientMap`: functoriality of `cyclicQuotient k` in multiplicative `k`-linear
  maps.
* `TauCeti.cyclicQuotientRingHomMap`: functoriality of `cyclicQuotient ℤ` in (possibly non-unital)
  ring homomorphisms.
* `TauCeti.cyclicQuotientEquivOfComm`: for a (possibly non-unital, non-associative) commutative
  ring `B`, `B / [B, B] ≃ₗ[k] B`.

## Main results

* `TauCeti.neg_mem_commutatorSubmodule`, `TauCeti.zsmul_mem_commutatorSubmodule` and
  `TauCeti.neg_one_pow_mul_mem_commutatorSubmodule`: the commutator submodule is closed under
  negation, under integer multiples and under multiplication by signs, even over a semiring of
  scalars.
* `TauCeti.mul_mem_commutatorSubmodule_comm`: a product is a sum of commutators exactly when its
  rotation is.
* `TauCeti.commutatorSubmodule_induction`: induction on membership in the commutator submodule,
  with cases for the additive commutators, sums and scalar multiples.
* `TauCeti.commutatorSubmodule_le_iff`: the commutator submodule lies in a submodule exactly
  when every additive commutator `x * y - y * x` does.
* `TauCeti.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator submodule exactly
  when it takes equal values on `x * y` and `y * x`.
* `TauCeti.map_mem_commutatorSubmodule`: a multiplicative `k`-linear map carries the commutator
  submodule over `k` into the commutator submodule over `k` of its target.
* `TauCeti.map_mem_commutatorSubmodule_of_ringHom`: when `k` acts on `A` associatively and
  centrally, a non-unital ring homomorphism carries the commutator submodule over `k` into the
  commutator submodule of its target over any semiring of scalars acting on the target.

The trace criterion for nonmembership in the commutator submodule (hence, over a ring of scalars,
for nonvanishing cyclic classes), which needs matrices, is
`TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule` in
`TauCeti.LinearAlgebra.Matrix.Trace.CyclicQuotient`.

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
@[simp]
theorem mul_sub_mul_mem_commutatorSubmodule (x y : A) :
    x * y - y * x ∈ commutatorSubmodule k A :=
  Submodule.subset_span ⟨(x, y), rfl⟩

variable {k A} in
/-- **Induction on the commutator submodule**: a property of elements of the commutator submodule
holds for all of them if it holds for every additive commutator `x * y - y * x` and is preserved
by sums and scalar multiples.  No case for `0` is needed, as `0 = 0 * 0 - 0 * 0`. -/
@[elab_as_elim]
theorem commutatorSubmodule_induction {p : (x : A) → x ∈ commutatorSubmodule k A → Prop}
    (mem : ∀ x y : A, p (x * y - y * x) (mul_sub_mul_mem_commutatorSubmodule k A x y))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (smul : ∀ (r : k) (x) (hx), p x hx → p (r • x) (Submodule.smul_mem _ r hx))
    {x : A} (hx : x ∈ commutatorSubmodule k A) : p x hx := by
  -- `commutatorSubmodule k A` is by definition the span of the additive commutators
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hz
    exact mem a b
  | zero => simpa using mem 0 0
  | add y z hy hz py pz => exact add y z hy hz py pz
  | smul r y hy py => exact smul r y hy py

variable {k A} in
/-- The commutator submodule lies in a submodule `S` exactly when every additive commutator
`x * y - y * x` lies in `S`. -/
theorem commutatorSubmodule_le_iff {S : Submodule k A} :
    commutatorSubmodule k A ≤ S ↔ ∀ x y : A, x * y - y * x ∈ S := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff, Prod.forall]
  simp only [SetLike.mem_coe]

variable {k A} in
/-- The commutator submodule is closed under negation even when `k` is only a semiring: the
negative of a commutator `x * y - y * x` is the commutator `y * x - x * y`. -/
theorem neg_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) :
    -x ∈ commutatorSubmodule k A := by
  -- negation, as a `k`-linear map, sends each spanning commutator to a commutator
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k A).comap (-LinearMap.id) :=
    commutatorSubmodule_le_iff.2 fun x y => by simp
  simpa only [LinearMap.neg_apply, LinearMap.id_apply] using Submodule.mem_comap.1 (hle hx)

variable {k A} in
/-- The commutator submodule is closed under integer multiples even when `k` is only a
semiring. -/
theorem zsmul_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) (n : ℤ) :
    n • x ∈ commutatorSubmodule k A := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using nsmul_mem hx m
  · simpa using neg_mem_commutatorSubmodule (nsmul_mem hx m)

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
two factors of a product.  The target may be any `k`-module whose additive structure is a
commutative monoid: additive inverses are not needed. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommMonoid M] [Module k M]
    (f : A →ₗ[k] M) :
    commutatorSubmodule k A ≤ LinearMap.ker f ↔ ∀ x y : A, f (x * y) = f (y * x) := by
  refine commutatorSubmodule_le_iff.trans (forall₂_congr fun x y => ?_)
  rw [LinearMap.mem_ker]
  constructor <;> intro h
  · -- add back `f (y * x)` to the vanishing value `f (x * y - y * x)`
    calc f (x * y) = f (x * y - y * x + y * x) := by rw [sub_add_cancel]
      _ = f (x * y - y * x) + f (y * x) := map_add f _ _
      _ = f (y * x) := by rw [h, zero_add]
  · -- replace `f (x * y)` by `f (y * x)`; the result is `f (y * x - y * x) = f 0`
    calc f (x * y - y * x) = f (x * y) + f (-(y * x)) := by rw [sub_eq_add_neg, map_add]
      _ = f (y * x) + f (-(y * x)) := by rw [h]
      _ = f (y * x - y * x) := by rw [← map_add, ← sub_eq_add_neg]
      _ = 0 := by simp

variable {k A} in
/-- A multiplicative linear map, such as an algebra homomorphism, carries the commutator submodule
into the commutator submodule. -/
theorem map_mem_commutatorSubmodule {B F : Type*} [NonUnitalNonAssocRing B] [Module k B]
    [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule k B := by
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k B).comap (f : A →ₗ[k] B) :=
    commutatorSubmodule_le_iff.2 fun x y => by simp
  simpa only [LinearMap.coe_ofClass] using Submodule.mem_comap.1 (hle hx)

variable {k A} in
/-- A non-unital ring homomorphism carries the commutator submodule over `k` into the commutator
submodule over any semiring `l`, whenever `k` acts associatively and centrally on `A`: each scalar
multiple `r • (a * b - b * a) = (r • a) * b - b * (r • a)` is itself a commutator. -/
theorem map_mem_commutatorSubmodule_of_ringHom {l B F : Type*} [Semiring l]
    [NonUnitalNonAssocRing B] [IsScalarTower k A A] [SMulCommClass k A A] [Module l B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule l B := by
  suffices ∀ r : k, f (r • x) ∈ commutatorSubmodule l B by simpa using this 1
  induction hx using commutatorSubmodule_induction with
  | mem a b =>
    intro r
    have hr : r • (a * b - b * a) = (r • a) * b - b * (r • a) := by
      rw [smul_sub, smul_mul_assoc, mul_smul_comm]
    rw [hr, map_sub, map_mul, map_mul]
    exact mul_sub_mul_mem_commutatorSubmodule l B (f (r • a)) (f b)
  | add y z _ _ hy hz => intro r; rw [smul_add, map_add]; exact add_mem (hy r) (hz r)
  | smul s y _ hy => intro r; rw [smul_smul]; exact hy (r * s)

end Semiring

/-- The **cyclic quotient** `A / [A, A]`.  Its elements are cyclic classes; for a path algebra,
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient [Ring k] [Module k A] := A ⧸ commutatorSubmodule k A

end General

section Map

variable (k : Type*) {A B F : Type*} [Ring k] [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B]
  [Module k A] [Module k B] [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B]

/-- The `k`-linear map `A / [A, A] →ₗ[k] B / [B, B]` induced on cyclic quotients by a
multiplicative `k`-linear map `f : A → B`. -/
def cyclicQuotientMap (f : F) : cyclicQuotient k A →ₗ[k] cyclicQuotient k B :=
  Submodule.mapQ (commutatorSubmodule k A) (commutatorSubmodule k B) (f : A →ₗ[k] B)
    fun _ hx ↦ map_mem_commutatorSubmodule f hx

@[simp]
theorem cyclicQuotientMap_mk (f : F) (x : A) :
    cyclicQuotientMap k f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := by rfl

end Map

@[simp]
theorem cyclicQuotientMap_id (k : Type*) {A : Type*} [Ring k] [NonUnitalNonAssocRing A]
    [Module k A] :
    cyclicQuotientMap k (NonUnitalAlgHom.id k A) = LinearMap.id := by ext x; rfl

@[simp]
theorem cyclicQuotientMap_algHom_id (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A] :
    cyclicQuotientMap k (AlgHom.id k A) = LinearMap.id := by ext x; rfl

theorem cyclicQuotientMap_comp (k : Type*) {A B C : Type*} [Ring k] [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C] [Module k A] [Module k B] [Module k C]
    (g : B →ₙₐ[k] C) (f : A →ₙₐ[k] B) :
    cyclicQuotientMap k (g.comp f) =
      (cyclicQuotientMap k g).comp (cyclicQuotientMap k f) := by ext x; rfl

theorem cyclicQuotientMap_algHom_comp (k : Type*) {A B C : Type*} [CommRing k] [Ring A] [Ring B]
    [Ring C] [Algebra k A] [Algebra k B] [Algebra k C] (g : B →ₐ[k] C) (f : A →ₐ[k] B) :
    cyclicQuotientMap k (g.comp f) =
      (cyclicQuotientMap k g).comp (cyclicQuotientMap k f) := by ext x; rfl

section RingHom

variable {R S F : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- The additive map `R / [R, R] →ₗ[ℤ] S / [S, S]` induced on integer cyclic quotients by a
(possibly non-unital) ring homomorphism `φ : R → S`. -/
def cyclicQuotientRingHomMap (φ : F) : cyclicQuotient ℤ R →ₗ[ℤ] cyclicQuotient ℤ S :=
  cyclicQuotientMap ℤ
    ({ (φ : R →+ S).toIntLinearMap with map_zero' := map_zero φ, map_mul' := map_mul φ } :
      R →ₙₐ[ℤ] S)

@[simp]
theorem cyclicQuotientRingHomMap_mk (φ : F) (x : R) :
    cyclicQuotientRingHomMap φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ x) := by rfl

@[simp]
theorem cyclicQuotientRingHomMap_id {R : Type*} [NonUnitalNonAssocRing R] :
    cyclicQuotientRingHomMap (NonUnitalRingHom.id R) = LinearMap.id := by ext x; rfl

@[simp]
theorem cyclicQuotientRingHomMap_ringHom_id {R : Type*} [NonAssocRing R] :
    cyclicQuotientRingHomMap (RingHom.id R) = LinearMap.id := by ext x; rfl

theorem cyclicQuotientRingHomMap_comp {R S T : Type*} [NonUnitalNonAssocRing R]
    [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T] (ψ : S →ₙ+* T) (φ : R →ₙ+* S) :
    cyclicQuotientRingHomMap (ψ.comp φ) =
      (cyclicQuotientRingHomMap ψ).comp (cyclicQuotientRingHomMap φ) := by ext x; rfl

theorem cyclicQuotientRingHomMap_ringHom_comp {R S T : Type*} [NonAssocRing R] [NonAssocRing S]
    [NonAssocRing T] (ψ : S →+* T) (φ : R →+* S) :
    cyclicQuotientRingHomMap (ψ.comp φ) =
      (cyclicQuotientRingHomMap ψ).comp (cyclicQuotientRingHomMap φ) := by ext x; rfl

end RingHom

section Comm

/-- In a (possibly non-unital, non-associative) commutative ring every additive commutator
vanishes, so the commutator submodule is trivial. -/
@[simp]
theorem commutatorSubmodule_eq_bot (k B : Type*) [Semiring k] [NonUnitalNonAssocCommRing B]
    [Module k B] : commutatorSubmodule k B = ⊥ := by
  rw [commutatorSubmodule, Submodule.span_eq_bot]
  rintro _ ⟨⟨x, y⟩, rfl⟩; exact sub_eq_zero.2 (mul_comm x y)

section Equiv

variable (k B : Type*) [Ring k] [NonUnitalNonAssocCommRing B] [Module k B]

/-- For a (possibly non-unital, non-associative) commutative ring `B`, the cyclic quotient
`B / [B, B]` is canonically isomorphic to `B`. -/
def cyclicQuotientEquivOfComm : cyclicQuotient k B ≃ₗ[k] B :=
  Submodule.quotEquivOfEqBot (commutatorSubmodule k B) (commutatorSubmodule_eq_bot k B)

@[simp]
theorem cyclicQuotientEquivOfComm_mk (x : B) :
    cyclicQuotientEquivOfComm k B (Submodule.Quotient.mk x) = x := by rfl

@[simp]
theorem cyclicQuotientEquivOfComm_symm_apply (x : B) :
    (cyclicQuotientEquivOfComm k B).symm x = Submodule.Quotient.mk x := by rfl

end Equiv

/-- Naturality of `cyclicQuotientEquivOfComm` with respect to multiplicative `k`-linear maps. -/
@[simp]
theorem cyclicQuotientEquivOfComm_cyclicQuotientMap (k : Type*) {A B F : Type*} [Ring k]
    [NonUnitalNonAssocCommRing A] [NonUnitalNonAssocCommRing B] [Module k A] [Module k B]
    [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B] (f : F)
    (c : cyclicQuotient k A) :
    cyclicQuotientEquivOfComm k B (cyclicQuotientMap k f c) =
      f (cyclicQuotientEquivOfComm k A c) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c; rfl

/-- Naturality of `cyclicQuotientEquivOfComm` with respect to (possibly non-unital) ring
homomorphisms. -/
@[simp]
theorem cyclicQuotientEquivOfComm_cyclicQuotientRingHomMap {A B F : Type*}
    [NonUnitalNonAssocCommRing A] [NonUnitalNonAssocCommRing B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (φ : F) (c : cyclicQuotient ℤ A) :
    cyclicQuotientEquivOfComm ℤ B (cyclicQuotientRingHomMap φ c) =
      φ (cyclicQuotientEquivOfComm ℤ A c) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c; rfl

end Comm

end TauCeti
