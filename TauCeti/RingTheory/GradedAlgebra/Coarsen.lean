/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Coarsen

/-!
# Coarsening the grading of a graded algebra

If `𝒜 : ι → Submodule R A` grades an `R`-algebra `A` and `f : ι →+ κ` is an additive
homomorphism of index monoids, the coarsened family `TauCeti.coarsenGrading 𝒜 f`, whose
degree-`k` piece is the sum of the pieces `𝒜 i` with `f i = k`, again grades `A`.  In particular
an integer-graded algebra is a `ZMod 2`-graded (super) algebra through its parity grading
`TauCeti.parityGrading 𝒜`.

Graded commutativity with Koszul signs `(-1) ^ (p * q)` and the graded Leibniz rule with signs
`(-1) ^ p` both pass to any coarsening along any function `f : ι → κ` that preserves `(-1) ^ ·`.
In particular, integer graded commutativity and signed derivations pass to the parity grading, with
the signs `(-1) ^ (i * j)` and `(-1) ^ i` for parities `i j : ZMod 2`, written with Mathlib's power
of a unit of `ℤ` by an element of `ZMod 2`.

## Main results

* `TauCeti.coarsenGrading_mul_le`: the product of coarsened pieces of degrees `k` and `l` lies in
  the coarsened piece of degree `k + l`.
* The instances `SetLike.GradedMul (coarsenGrading 𝒜 f)`, over a nonunital algebra,
  `SetLike.GradedMonoid (coarsenGrading 𝒜 f)` and `GradedAlgebra (coarsenGrading 𝒜 f)`, which
  apply in particular to `parityGrading 𝒜`.
* `TauCeti.uzpow_mul_eq_of_forall_uzpow_eq`,
  `TauCeti.mul_eq_uzpow_smul_mul_of_mem_coarsenGrading`, and
  `TauCeti.mul_eq_uzpow_smul_mul_of_mem_parityGrading`: Koszul graded commutativity passes to
  sign-preserving coarsenings, and in particular from integer degree to parity.
* `TauCeti.commute_of_mul_eq_uzpow_smul_mul`,
  `TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero`,
  `TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul`, and
  `TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one`: in any ring with Koszul graded
  commutativity over a Koszul-signed degree semiring `ι`, elements of degree `p` with
  `(-1 : ℤˣ) ^ p = 1` (in particular degree `0`) commute with every element, and elements of degree
  `p` with `(-1 : ℤˣ) ^ p = -1` (in particular degree `1`) square to their own negatives.
* `TauCeti.leibniz_coarsenGrading_of_leibniz`: the graded Leibniz rule passes to sign-preserving
  coarsenings.
-/

public section

open DirectSum

namespace TauCeti

universe uR uA uι uκ

section GradedMul

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Add ι] [Add κ]
  [FunLike F ι κ] [AddHomClass F ι κ] (𝒜 : ι → Submodule R A)

/-- Coarsening a graded multiplication along an additive homomorphism of index types gives a
graded multiplication. -/
instance [SetLike.GradedMul 𝒜] (f : F) : SetLike.GradedMul (coarsenGrading 𝒜 f) where
  mul_mem k l a b ha hb := by
    -- Both sides are additive in each factor, so it suffices to treat homogeneous elements.
    refine coarsenGrading_induction (motive := fun a ↦ a * b ∈ coarsenGrading 𝒜 f (k + l)) ha
      (fun i hi a ha ↦ ?_) (by simp) fun x y hx hy ↦ by rw [add_mul]; exact add_mem hx hy
    refine coarsenGrading_induction (motive := fun b ↦ a * b ∈ coarsenGrading 𝒜 f (k + l)) hb
      (fun j hj b hb ↦ ?_) (by simp) fun x y hx hy ↦ by rw [mul_add]; exact add_mem hx hy
    rw [← hi, ← hj, ← map_add]
    exact mem_coarsenGrading_of_mem f (SetLike.mul_mem_graded ha hb)

end GradedMul

/-- The product of the coarsened pieces of degrees `k` and `l` of a graded multiplication lies
in the coarsened piece of degree `k + l`. -/
theorem coarsenGrading_mul_le {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
    [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A] [Add ι] [Add κ]
    [FunLike F ι κ] [AddHomClass F ι κ] (𝒜 : ι → Submodule R A) [SetLike.GradedMul 𝒜] (f : F)
    (k l : κ) :
    coarsenGrading 𝒜 f k * coarsenGrading 𝒜 f l ≤ coarsenGrading 𝒜 f (k + l) :=
  Submodule.mul_le.2 fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb

section GradedMonoid

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [Semiring R] [Semiring A] [Module R A] [AddMonoid ι] [AddMonoid κ]
  [FunLike F ι κ] [AddMonoidHomClass F ι κ] (𝒜 : ι → Submodule R A)

/-- Coarsening a graded monoid structure along an additive homomorphism of index monoids gives a
graded monoid structure. -/
instance [SetLike.GradedMonoid 𝒜] (f : F) : SetLike.GradedMonoid (coarsenGrading 𝒜 f) :=
  { (inferInstance : SetLike.GradedMul (coarsenGrading 𝒜 f)) with
    one_mem := by simpa using mem_coarsenGrading_of_mem f (SetLike.one_mem_graded 𝒜) }

end GradedMonoid

section Coarsen

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ} {F : Type*}
  [CommSemiring R] [Semiring A] [Algebra R A] [AddMonoid ι] [AddMonoid κ]
  [FunLike F ι κ] [AddMonoidHomClass F ι κ] (𝒜 : ι → Submodule R A)

/-- Coarsening the grading of a graded algebra along an additive homomorphism of index monoids
gives a graded algebra. -/
noncomputable instance [DecidableEq ι] [DecidableEq κ] [GradedAlgebra 𝒜] (f : F) :
    GradedAlgebra (coarsenGrading 𝒜 f) :=
  { (inferInstance : SetLike.GradedMonoid (coarsenGrading 𝒜 f)),
    (inferInstance : Decomposition (coarsenGrading 𝒜 f)) with }

end Coarsen

section CoarsenComm

variable {R : Type uR} {A : Type uA} {ι : Type uι} {κ : Type uκ}
  [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  [CommSemiring ι] [Module ι (Additive ℤˣ)] [CommSemiring κ] [Module κ (Additive ℤˣ)]
  {𝒜 : ι → Submodule R A}

omit [Semiring R] [NonUnitalNonAssocRing A] [Module R A] in
/-- Any function between Koszul-signed degree semirings that preserves `u ^ ·` for a unit
`u : ℤˣ` automatically preserves pairwise powers `u ^ (p * q)`. -/
theorem uzpow_mul_eq_of_forall_uzpow_eq {u : ℤˣ} {f : ι → κ}
    (hf : ∀ p : ι, u ^ f p = u ^ p) (p q : ι) :
    u ^ (f p * f q) = u ^ (p * q) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [uzpow_mul, uzpow_mul, hf p]
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ p) with h | h
    · rw [h, one_uzpow, one_uzpow]
    · rw [h, hf q]

/-- **Koszul graded commutativity passes to any sign-preserving coarsening.** If homogeneous
elements of degrees `p` and `q` commute up to the Koszul sign `(-1) ^ (p * q)` and `f : ι → κ`
preserves `(-1) ^ ·`, then elements of coarsened degrees `i` and `j` commute up to
`(-1) ^ (i * j)`. -/
theorem mul_eq_uzpow_smul_mul_of_mem_coarsenGrading {f : ι → κ}
    (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (hcomm : ∀ {p q : ι} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q →
      a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {i j : κ} {a b : A} (ha : a ∈ coarsenGrading 𝒜 f i) (hb : b ∈ coarsenGrading 𝒜 f j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) := by
  -- Both sides are additive in each factor, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction (motive := fun a ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ by rw [add_mul, mul_add, hx, hy, smul_add]
  refine coarsenGrading_induction (motive := fun b ↦ a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)) hb
    (fun q hq b hb ↦ ?_) (by simp) fun x y hx hy ↦ by rw [mul_add, add_mul, hx, hy, smul_add]
  rw [hcomm ha hb, ← hp, ← hq, uzpow_mul_eq_of_forall_uzpow_eq hf]

/-- **The graded Leibniz rule passes to any sign-preserving coarsening.** If `d` satisfies the
graded Leibniz rule with the sign `(-1) ^ p` on a left factor of degree `p` and `f : ι → κ`
preserves `(-1) ^ ·`, then `d` satisfies the graded Leibniz rule with the sign `(-1) ^ i` on a
left factor in the coarsened piece of degree `i`. -/
theorem leibniz_coarsenGrading_of_leibniz {d : A →ₗ[R] A} {f : ι → κ}
    (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b))
    {i : κ} {a : A} (ha : a ∈ coarsenGrading 𝒜 f i) (b : A) :
    d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) := by
  -- Both sides are additive in `a`, so it suffices to treat homogeneous elements.
  refine coarsenGrading_induction
    (motive := fun a ↦ d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) ha
    (fun p hp a ha ↦ ?_) (by simp) fun x y hx hy ↦ ?_
  · rw [hl ha b, ← hp, hf]
  · rw [add_mul, map_add, hx, hy, map_add, add_mul, add_mul, smul_add]
    abel

end CoarsenComm

section SignedComm

variable {A : Type uA} {ι : Type uι} {σ : Type*}
  [NonUnitalNonAssocRing A] [CommSemiring ι] [Module ι (Additive ℤˣ)] [SetLike σ A]

/-- In an internally graded ring with Koszul signs, every homogeneous element whose degree `p`
satisfies `(-1 : ℤˣ) ^ p = 1` commutes with the entire ring. -/
theorem commute_of_mul_eq_uzpow_smul_mul [DecidableEq ι] [AddSubmonoidClass σ A] {ℬ : ι → σ}
    [Decomposition ℬ]
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {p : ι} {a : A} (ha : a ∈ ℬ p) (hp : (-1 : ℤˣ) ^ p = 1) (b : A) : Commute a b := by
  induction b using Decomposition.inductionOn ℬ with
  | zero => simp [Commute, SemiconjBy]
  | @homogeneous q b => simpa [Commute, SemiconjBy, uzpow_mul, hp] using hcomm ha b.2
  | add x y hx hy => simp only [Commute, SemiconjBy, mul_add, add_mul, hx.eq, hy.eq]

/-- In an internally graded ring with Koszul signs, every element of degree `0` commutes with the
entire ring. -/
theorem commute_of_mul_eq_uzpow_smul_mul_of_mem_zero [DecidableEq ι] [AddSubmonoidClass σ A]
    {ℬ : ι → σ} [Decomposition ℬ]
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {a : A} (ha : a ∈ ℬ 0) (b : A) : Commute a b :=
  commute_of_mul_eq_uzpow_smul_mul hcomm ha (uzpow_zero (-1)) b

/-- Under Koszul graded commutativity, every homogeneous element whose degree `p` satisfies
`(-1 : ℤˣ) ^ p = -1` squares to its own negative. -/
theorem mul_self_eq_neg_of_mul_eq_uzpow_smul_mul {ℬ : ι → σ}
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {p : ι} {a : A} (ha : a ∈ ℬ p) (hp : (-1 : ℤˣ) ^ p = -1) : a * a = -(a * a) := by
  simpa [uzpow_mul, hp] using hcomm ha ha

/-- Under Koszul graded commutativity, every element of degree `1` squares to its own negative. -/
theorem mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one {ℬ : ι → σ}
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {a : A} (ha : a ∈ ℬ 1) : a * a = -(a * a) :=
  mul_self_eq_neg_of_mul_eq_uzpow_smul_mul hcomm ha (uzpow_one (-1))

end SignedComm

section ParityComm

variable {R : Type uR} {A : Type uA} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  {𝒜 : ℤ → Submodule R A}

/-- **Integer graded commutativity implies parity graded commutativity.** If homogeneous
elements of degrees `p` and `q` commute up to the Koszul sign `(-1) ^ (p * q)`, then elements of
parities `i` and `j` commute up to the sign `(-1) ^ (i * j)`. -/
theorem mul_eq_uzpow_smul_mul_of_mem_parityGrading
    (hcomm : ∀ {p q : ℤ} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q → a * b = (p * q).negOnePow • (b * a))
    {i j : ZMod 2} {a b : A} (ha : a ∈ parityGrading 𝒜 i) (hb : b ∈ parityGrading 𝒜 j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) :=
  mul_eq_uzpow_smul_mul_of_mem_coarsenGrading (f := Int.castAddHom (ZMod 2))
    (fun p ↦ by rw [Int.coe_castAddHom]; exact uzpow_intCast (-1) p) hcomm ha hb

end ParityComm

end TauCeti
