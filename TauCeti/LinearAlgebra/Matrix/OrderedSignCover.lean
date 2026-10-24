/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet

/-!
# The ordered sign cover of an integral lattice

Let `B : Matrix I I ℤ` be the Gram matrix of the lattice `Q = I → ℤ` in the basis indexed by a
linearly ordered finite set `I`, for instance the Cartan matrix of a simply laced Dynkin diagram
with its vertices ordered. Keeping only the strictly lower triangular entries of `B` gives a
bilinear form

`β(a, b) = ∑_{j < i} a i * B i j * b j`

on `Q`, and its sign `ε(a, b) = (-1) ^ β(a, b)` is bimultiplicative, hence a factor set of `Q` with
values in `ℤˣ`. The central extension `1 → ℤˣ → Q̂ → Q → 1` it builds is the ordered sign cover of
`Q`: its elements are pairs of a lattice vector and a sign, multiplied by
`(a, s) * (b, t) = (a + b, s * t * ε(a, b))`.

For a simply laced diagram, `-B i j` is the number of bonds between distinct vertices `i` and `j`,
so `ε(a, b)` is the parity of the bonds pairing a later coordinate of `a` with an earlier one of
`b`. The point of the cover is its commutator formula: when `B` is symmetric with even diagonal,
the commutator of two elements of `Q̂` lying over `a` and `b` is `τ ^ (a ⬝ᵥ B *ᵥ b)`, a power of the
central sign `τ = (0, -1)` (`Matrix.commutatorElement_signCover`). This is the sign input of the
Frenkel--Kac construction of a simply laced Lie algebra over `ℤ`, whose root vectors are indexed by
lifts of roots to `Q̂`. The bracket `Matrix.ShellLieAlgebra`, in
`TauCeti.Algebra.Lie.NormTwoShell.Basic`, uses this cocycle on root vectors indexed by the section
`a ↦ (a, 1)` instead, so it is not the lifted-generator presentation. The section
`a ↦ (a, 1)` is a homomorphism exactly when every strictly lower entry of `B` is even
(`Matrix.forall_canonicalSection_signFactorSet_mul_iff`); for a simply laced diagram this means
exactly that the diagram has no bonds, which is proved in
`TauCeti.LinearAlgebra.Matrix.OrderedSignCover.SimplyLaced`.

The group structure, the inclusion of `ℤˣ`, the projection to `Multiplicative Q`, the exactness of
`1 → ℤˣ → Q̂ → Q → 1`, the section `a ↦ (a, 1)` and the centrality of `ℤˣ` all come from the general
factor-set construction `TauCeti.FactorSet.Extension` for the trivial action of `Q` on `ℤˣ`; this
file supplies the sign cocycle and the facts specific to it.

## Main definitions

* `Matrix.orderedSignForm B`: the bilinear form of the strictly lower triangular part of
  `B`.
* `Matrix.orderedSign B`: its sign `ε`, as a bimultiplicative map on `Multiplicative Q`.
* `Matrix.signFactorSet B`: `ε` as a factor set for the trivial action of `Q` on `ℤˣ`.
* `Matrix.SignCover B`: the central extension `Q̂` of `Q` by `ℤˣ` it builds.
* `Matrix.SignCover.tau B`: the central sign `τ`, the image of `-1 : ℤˣ` in `Q̂`.

## Main results

* `Matrix.orderedSignForm_add_orderedSignForm_swap`: for symmetric `B`, the symmetrization
  of the ordered form is the Gram pairing with its diagonal terms removed.
* `Matrix.even_orderedSignForm_add_orderedSignForm_swap_sub`: for symmetric `B` with even
  diagonal, `orderedSignForm B a b + orderedSignForm B b a` and `a ⬝ᵥ B *ᵥ b` have the same parity.
* `Matrix.orderedSign_div_orderedSign_swap`: for symmetric `B` with even diagonal,
  `ε(a, b) / ε(b, a) = (-1) ^ (a ⬝ᵥ B *ᵥ b)`.
* `Matrix.SignCover.inv_canonicalSection`: the inverse lift `⟨1, a⟩⁻¹ = ε(a, a) ⟨1, -a⟩`.
* `Matrix.commutatorElement_signCover`: the commutator formula in `Q̂`.
* `Matrix.forall_canonicalSection_signFactorSet_mul_iff`: the section `a ↦ (a, 1)` is a
  homomorphism exactly when all strictly lower entries of `B` are even.

## References

* I. B. Frenkel and V. G. Kac, *Basic representations of affine Lie algebras and dual resonance
  models*, Invent. Math. **62** (1980), 23--66.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix

open TauCeti

open scoped commutatorElement

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)

/-- **The ordered form of an integer matrix**: the bilinear form on `I → ℤ` of the strictly lower
triangular part of `B` for the order of `I`,
`orderedSignForm B a b = ∑_{j < i} a i * B i j * b j`. Its sign is the factor set
`Matrix.signFactorSet B`. -/
noncomputable def orderedSignForm : LinearMap.BilinForm ℤ (I → ℤ) :=
  toBilin' (of fun i j => if j < i then B i j else 0)

theorem orderedSignForm_apply (a b : I → ℤ) :
    orderedSignForm B a b = ∑ i, ∑ j, if j < i then a i * B i j * b j else 0 := by
  simp only [orderedSignForm, toBilin'_apply, of_apply, mul_ite, ite_mul, mul_zero, zero_mul]

/-- On basis vectors the ordered form reads off the strictly lower triangular entries of `B`. -/
@[simp]
theorem orderedSignForm_single_single (i j : I) :
    orderedSignForm B (Pi.single i 1) (Pi.single j 1) = if j < i then B i j else 0 :=
  toBilin'_single _ i j

/-- **Symmetrizing the ordered form.** For a symmetric matrix `B`, adding the ordered form to its
transpose recovers the Gram pairing `a ⬝ᵥ B *ᵥ b` with its diagonal terms removed: each
off-diagonal pair `i ≠ j` is counted once by whichever of the two forms sees `j < i`. -/
theorem orderedSignForm_add_orderedSignForm_swap (hB : B.IsSymm) (a b : I → ℤ) :
    orderedSignForm B a b + orderedSignForm B b a + ∑ i, a i * B i i * b i = a ⬝ᵥ B *ᵥ b := by
  have key : ∀ i j, ((if j < i then a i * B i j * b j else 0) +
      (if i < j then b j * B j i * a i else 0) + if i = j then a i * B i i * b i else 0) =
      a i * (B i j * b j) := fun i j => by
    rcases lt_trichotomy j i with h | rfl | h
    · simp [h, h.not_gt, h.ne', mul_assoc]
    · simp [mul_assoc]
    · simp [h, h.not_gt, h.ne, hB.apply i j]
      ring
  rw [orderedSignForm_apply B b a, Finset.sum_comm]
  simp only [orderedSignForm_apply, dotProduct, mulVec, Finset.mul_sum, ← key,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The ordered sign of an integer matrix**: `ε(a, b) = (-1) ^ orderedSignForm B a b`, written
`Int.negOnePow (orderedSignForm B a b)`, as a map
on `Multiplicative (I → ℤ)` that is multiplicative in each variable. This is the factor set of the
ordered sign cover `Matrix.SignCover B`. -/
noncomputable def orderedSign :
    Multiplicative (I → ℤ) →* Multiplicative (I → ℤ) →* ℤˣ where
  toFun a :=
    { toFun b := (orderedSignForm B a.toAdd b.toAdd).negOnePow
      map_one' := by simp
      map_mul' b c := by simp [Int.negOnePow_add] }
  map_one' := by ext; simp
  map_mul' a c := by ext; simp [Int.negOnePow_add]

@[simp]
theorem orderedSign_apply (a b : Multiplicative (I → ℤ)) :
    orderedSign B a b = (orderedSignForm B a.toAdd b.toAdd).negOnePow :=
  (rfl)

/-- **The commutator parity.** For a symmetric matrix `B` with even diagonal, the ordered form and
its transpose add up to the Gram pairing modulo `2`. -/
theorem even_orderedSignForm_add_orderedSignForm_swap_sub (hB : B.IsSymm)
    (hdiag : ∀ i, Even (B i i)) (a b : I → ℤ) :
    Even (orderedSignForm B a b + orderedSignForm B b a - a ⬝ᵥ B *ᵥ b) := by
  rw [← orderedSignForm_add_orderedSignForm_swap B hB, sub_add_cancel_left]
  -- The two sides differ by the diagonal sum `∑ i, a i * B i i * b i`, which is even.
  exact (Finset.even_sum _ fun i _ => ((hdiag i).mul_left _).mul_right _).neg

/-- **The commutator sign.** For a symmetric matrix `B` with even diagonal, the ratio of the two
ordered signs of `a` and `b` is the sign of their Gram pairing. -/
theorem orderedSign_div_orderedSign_swap (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (a b : Multiplicative (I → ℤ)) :
    orderedSign B a b / orderedSign B b a = (a.toAdd ⬝ᵥ B *ᵥ b.toAdd).negOnePow := by
  rw [div_eq_mul_inv, Int.units_inv_eq_self, orderedSign_apply, orderedSign_apply,
    ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact even_orderedSignForm_add_orderedSignForm_swap_sub B hB hdiag _ _

section Cover

attribute [local instance] trivialMulDistribMulAction

/-- **The ordered sign factor set** of an integer matrix: the bimultiplicative ordered sign
`Matrix.orderedSign B` as a factor set of `Multiplicative (I → ℤ)` with values in `ℤˣ`, for
the trivial action. -/
noncomputable def signFactorSet : FactorSet (Multiplicative (I → ℤ)) ℤˣ :=
  FactorSet.ofBimultiplicative (orderedSign B) trivialMulDistribMulAction_smul

@[simp]
theorem signFactorSet_apply (p : Multiplicative (I → ℤ) × Multiplicative (I → ℤ)) :
    signFactorSet B p = orderedSign B p.1 p.2 :=
  FactorSet.ofBimultiplicative_apply _ _ p

/-- **The ordered sign cover** `Q̂` of the lattice `Q = I → ℤ` with Gram matrix `B`: the central
extension `1 → ℤˣ → Q̂ → Q → 1` built from the ordered sign factor set. An element is a pair of a
sign `x.left` and a lattice vector `x.right`, and
`x * y = ⟨x.left * y.left * ε(x.right, y.right), x.right * y.right⟩`. The inclusion of `ℤˣ`, the
projection to `Multiplicative Q` and the section `a ↦ ⟨1, a⟩` are `TauCeti.FactorSet.inl`,
`TauCeti.FactorSet.rightHom` and `TauCeti.FactorSet.canonicalSection` of
`Matrix.signFactorSet B`, and `(Matrix.signFactorSet B).groupExtension` packages them as a
`GroupExtension`. The image of `ℤˣ` is central by `TauCeti.FactorSet.inl_range_le_center`, the
action being trivial. -/
abbrev SignCover : Type _ :=
  (signFactorSet B).Extension

/-- **The central sign** `τ = ⟨-1, 1⟩` of the ordered sign cover: the image of `-1 : ℤˣ`, an
element of order `2` in the center. -/
noncomputable def SignCover.tau : SignCover B :=
  FactorSet.inl (signFactorSet B) (-1)

@[simp]
theorem SignCover.tau_left : (SignCover.tau B).left = -1 :=
  FactorSet.inl_left _ _

@[simp]
theorem SignCover.tau_right : (SignCover.tau B).right = 1 :=
  FactorSet.inl_right _ _

@[simp]
theorem SignCover.tau_mul_self : SignCover.tau B * SignCover.tau B = 1 := by
  rw [SignCover.tau, ← map_mul, Int.units_mul_self, map_one]

theorem SignCover.tau_ne_one : SignCover.tau B ≠ 1 := by
  rw [SignCover.tau, ← map_one (FactorSet.inl (signFactorSet B)),
    (FactorSet.inl_injective _).ne_iff]
  decide

theorem SignCover.tau_mem_center : SignCover.tau B ∈ Subgroup.center (SignCover B) :=
  FactorSet.inl_range_le_center _ trivialMulDistribMulAction_smul ⟨-1, rfl⟩

/-- **The inverse lift** in the ordered sign cover: the inverse of the section value `⟨1, a⟩` lies
over `-a` with the sign `ε(a, a)`, that is, `⟨1, a⟩⁻¹ = ε(a, a) ⟨1, -a⟩`. -/
theorem SignCover.inv_canonicalSection (a : Multiplicative (I → ℤ)) :
    ((signFactorSet B).canonicalSection a)⁻¹ =
      FactorSet.inl (signFactorSet B) (orderedSign B a a) *
        (signFactorSet B).canonicalSection a⁻¹ := by
  rw [FactorSet.inv_canonicalSection, trivialMulDistribMulAction_smul, signFactorSet_apply,
    (orderedSign B a).map_inv, inv_inv]

/-- **The commutator formula of the ordered sign cover.** For a symmetric matrix `B` with even
diagonal, two elements of the cover lying over `a` and `b` commute up to the power
`τ ^ (a ⬝ᵥ B *ᵥ b)` of the central sign given by their Gram pairing, whatever signs they
carry. -/
theorem commutatorElement_signCover (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (x y : SignCover B) :
    ⁅x, y⁆ = SignCover.tau B ^ (x.right.toAdd ⬝ᵥ B *ᵥ y.right.toAdd) := by
  rw [FactorSet.commutatorElement_eq_inl _ trivialMulDistribMulAction_smul, signFactorSet_apply,
    signFactorSet_apply, orderedSign_div_orderedSign_swap B hB hdiag, Int.negOnePow_def, map_zpow,
    SignCover.tau]

/-- **The canonical section of the ordered sign cover is a homomorphism exactly when every strictly
lower triangular entry of `B` is even**, that is, exactly when the ordered sign is trivial. -/
theorem forall_canonicalSection_signFactorSet_mul_iff :
    (∀ a b : Multiplicative (I → ℤ), (signFactorSet B).canonicalSection (a * b) =
        (signFactorSet B).canonicalSection a * (signFactorSet B).canonicalSection b) ↔
      ∀ i j, j < i → Even (B i j) := by
  rw [FactorSet.forall_canonicalSection_mul_iff, FactorSet.ext_iff]
  simp only [signFactorSet_apply, orderedSign_apply, FactorSet.trivial_apply,
    Int.negOnePow_eq_one_iff, Prod.forall]
  refine ⟨fun h i j hji => ?_, fun h a b => ?_⟩
  · simpa [hji] using
      h (Multiplicative.ofAdd (Pi.single i 1)) (Multiplicative.ofAdd (Pi.single j 1))
  · rw [orderedSignForm_apply]
    refine Finset.even_sum _ fun i _ => Finset.even_sum _ fun j _ => ?_
    split_ifs with hji
    · exact ((h i j hji).mul_left _).mul_right _
    · exact Even.zero

end Cover

end Matrix
