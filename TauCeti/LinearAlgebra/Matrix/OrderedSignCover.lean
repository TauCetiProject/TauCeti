/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
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
the commutator of two elements of `Q̂` lying over `a` and `b` is the central sign
`(-1) ^ (a ⬝ᵥ B *ᵥ b)` (`Matrix.commutatorElement_signCover`). This is the sign input of the
Frenkel--Kac construction of a simply laced Lie algebra over `ℤ`, whose root vectors are indexed by
lifts of roots to `Q̂`; that bracket is not constructed here. The section
`a ↦ (a, 1)` is a homomorphism exactly when every strictly lower entry of `B` is even
(`Matrix.forall_canonicalSection_signFactorSet_mul_iff`), so for a simply laced diagram
exactly when the diagram has no bonds
(`Matrix.forall_canonicalSection_signFactorSet_mul_iff_of_simplyLaced`).

The group structure, the inclusion of `ℤˣ`, the projection to `Multiplicative Q`, the exactness of
`1 → ℤˣ → Q̂ → Q → 1`, the section `a ↦ (a, 1)` and the centrality of `ℤˣ` all come from the general
factor-set construction `TauCeti.FactorSet.Extension` for the trivial action of `Q` on `ℤˣ`; this
file supplies the sign cocycle and the two facts specific to it.

## Main definitions

* `Matrix.orderedSignForm B`: the bilinear form of the strictly lower triangular part of
  `B`.
* `Matrix.orderedSign B`: its sign `ε`, as a bimultiplicative map on `Multiplicative Q`.
* `Matrix.signFactorSet B`: `ε` as a factor set for the trivial action of `Q` on `ℤˣ`.
* `Matrix.SignCover B`: the central extension `Q̂` of `Q` by `ℤˣ` it builds.

## Main results

* `Matrix.orderedSignForm_add_orderedSignForm_swap`: for symmetric `B`, the symmetrization
  of the ordered form is the Gram pairing with its diagonal terms removed.
* `Matrix.orderedSign_div_orderedSign_swap`: for symmetric `B` with even diagonal,
  `ε(a, b) / ε(b, a) = (-1) ^ (a ⬝ᵥ B *ᵥ b)`.
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
  toLinearMap₂' ℤ (of fun i j => if j < i then B i j else 0)

theorem orderedSignForm_apply (a b : I → ℤ) :
    orderedSignForm B a b = ∑ i, ∑ j, if j < i then a i * B i j * b j else 0 := by
  simp only [orderedSignForm, toLinearMap₂'_apply, of_apply, smul_eq_mul, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- On basis vectors the ordered form reads off the strictly lower triangular entries of `B`. -/
@[simp]
theorem orderedSignForm_single_single (i j : I) :
    orderedSignForm B (Pi.single i 1) (Pi.single j 1) = if j < i then B i j else 0 := by
  simp only [orderedSignForm_apply, Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
    zero_mul]
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
    Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
  simp

/-- **Symmetrizing the ordered form.** For a symmetric matrix `B`, adding the ordered form to its
transpose recovers the Gram pairing `a ⬝ᵥ B *ᵥ b` with its diagonal terms removed: each
off-diagonal pair `i ≠ j` is counted once by whichever of the two forms sees `j < i`. -/
theorem orderedSignForm_add_orderedSignForm_swap (hB : B.IsSymm) (a b : I → ℤ) :
    orderedSignForm B a b + orderedSignForm B b a + ∑ i, a i * B i i * b i = a ⬝ᵥ B *ᵥ b := by
  rw [orderedSignForm_apply, orderedSignForm_apply, Finset.sum_comm (f := fun i j =>
      if j < i then b i * B i j * a j else 0), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [lt_irrefl, ite_false, zero_add]
  rw [add_comm]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · simp only [h, ↓reduceIte, not_lt_of_gt h, add_zero]
      ring
    · simp only [not_lt_of_gt h, ↓reduceIte, h, zero_add]
      rw [hB.apply]
      ring

/-- **The ordered sign of an integer matrix**: `ε(a, b) = (-1) ^ orderedSignForm B a b`, as a map
on `Multiplicative (I → ℤ)` that is multiplicative in each variable. This is the factor set of the
ordered sign cover `Matrix.SignCover B`. -/
noncomputable def orderedSign :
    Multiplicative (I → ℤ) →* Multiplicative (I → ℤ) →* ℤˣ where
  toFun a :=
    { toFun b := (-1) ^ orderedSignForm B a.toAdd b.toAdd
      map_one' := by simp
      map_mul' b c := by simp [zpow_add] }
  map_one' := by ext; simp
  map_mul' a c := by ext; simp [zpow_add]

@[simp]
theorem orderedSign_apply (a b : Multiplicative (I → ℤ)) :
    orderedSign B a b = (-1) ^ orderedSignForm B a.toAdd b.toAdd :=
  (rfl)

/-- **The commutator sign.** For a symmetric matrix `B` with even diagonal, the ratio of the two
ordered signs of `a` and `b` is the sign of their Gram pairing. -/
theorem orderedSign_div_orderedSign_swap (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (a b : Multiplicative (I → ℤ)) :
    orderedSign B a b / orderedSign B b a = (-1) ^ (a.toAdd ⬝ᵥ B *ᵥ b.toAdd) := by
  have hd : Even (2 * orderedSignForm B b.toAdd a.toAdd + ∑ i, a.toAdd i * B i i * b.toAdd i) :=
    (even_two_mul _).add (Finset.even_sum _ fun i _ => ((hdiag i).mul_left _).mul_right _)
  rw [orderedSign_apply, orderedSign_apply, div_eq_mul_inv, ← zpow_sub,
    ← orderedSignForm_add_orderedSignForm_swap B hB,
    show orderedSignForm B a.toAdd b.toAdd + orderedSignForm B b.toAdd a.toAdd +
        ∑ i, a.toAdd i * B i i * b.toAdd i =
      orderedSignForm B a.toAdd b.toAdd - orderedSignForm B b.toAdd a.toAdd +
        (2 * orderedSignForm B b.toAdd a.toAdd + ∑ i, a.toAdd i * B i i * b.toAdd i) by ring,
    zpow_add, hd.neg_one_zpow, mul_one]

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

/-- **The commutator formula of the ordered sign cover.** For a symmetric matrix `B` with even
diagonal, two elements of the cover lying over `a` and `b` commute up to the central sign
`(-1) ^ (a ⬝ᵥ B *ᵥ b)` of their Gram pairing, whatever signs they carry. -/
theorem commutatorElement_signCover (hB : B.IsSymm) (hdiag : ∀ i, Even (B i i))
    (x y : SignCover B) :
    ⁅x, y⁆ = FactorSet.inl (signFactorSet B) ((-1) ^ (x.right.toAdd ⬝ᵥ B *ᵥ y.right.toAdd)) := by
  rw [FactorSet.commutatorElement_eq_inl _ trivialMulDistribMulAction_smul, signFactorSet_apply,
    signFactorSet_apply, orderedSign_div_orderedSign_swap B hB hdiag]

/-- **The canonical section of the ordered sign cover is a homomorphism exactly when every strictly
lower triangular entry of `B` is even**, that is, exactly when the ordered sign is trivial. -/
theorem forall_canonicalSection_signFactorSet_mul_iff :
    (∀ a b : Multiplicative (I → ℤ), (signFactorSet B).canonicalSection (a * b) =
        (signFactorSet B).canonicalSection a * (signFactorSet B).canonicalSection b) ↔
      ∀ i j, j < i → Even (B i j) := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rw [FactorSet.forall_canonicalSection_mul_iff, FactorSet.ext_iff]
  simp only [signFactorSet_apply, orderedSign_apply, FactorSet.trivial_apply, neg_one_zpow_eq_ite,
    ite_eq_left_iff, hne, imp_false, not_not, Prod.forall]
  refine ⟨fun h i j hji => ?_, fun h a b => ?_⟩
  · simpa [hji] using
      h (Multiplicative.ofAdd (Pi.single i 1)) (Multiplicative.ofAdd (Pi.single j 1))
  · rw [orderedSignForm_apply]
    refine Finset.even_sum _ fun i _ => Finset.even_sum _ fun j _ => ?_
    split_ifs with hji
    · exact ((h i j hji).mul_left _).mul_right _
    · exact Even.zero

/-- **For a simply laced Gram matrix, the canonical section of the ordered sign cover is a
homomorphism exactly when the diagram has no bonds.** Here `B` is symmetric with off-diagonal
entries `0` or `-1`, the negative of the number of bonds, as for the Cartan matrix of a simply laced
Dynkin diagram. -/
theorem forall_canonicalSection_signFactorSet_mul_iff_of_simplyLaced (hB : B.IsSymm)
    (hoff : ∀ i j, i ≠ j → B i j = 0 ∨ B i j = -1) :
    (∀ a b : Multiplicative (I → ℤ), (signFactorSet B).canonicalSection (a * b) =
        (signFactorSet B).canonicalSection a * (signFactorSet B).canonicalSection b) ↔
      ∀ i j, i ≠ j → B i j = 0 := by
  rw [forall_canonicalSection_signFactorSet_mul_iff]
  refine ⟨fun h i j hij => ?_, fun h i j hji => by simp [h i j hji.ne']⟩
  have key : ∀ i j, j < i → B i j = 0 := fun i j hji =>
    (hoff i j hji.ne').resolve_right fun h' => by simpa [h'] using h i j hji
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [← hB.apply]
    exact key j i hlt
  · exact key i j hlt

end Cover

end Matrix
