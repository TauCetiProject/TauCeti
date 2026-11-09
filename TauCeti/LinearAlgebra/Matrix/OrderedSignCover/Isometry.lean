/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover
public import TauCeti.RingTheory.Binomial

/-!
# Lifting lattice isometries to the ordered sign cover

Let `B : Matrix I I ℤ` and `B' : Matrix J J ℤ` be symmetric Gram matrices with even diagonal on
linearly ordered finite sets, with ordered forms `β` and `β'` (`Matrix.orderedSignForm`) and
ordered signs `ε = (-1) ^ β` and `ε' = (-1) ^ β'`. Let `g : (I → ℤ) →ₗ[ℤ] (J → ℤ)` be an isometry,
`g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b`. This file lifts `g` to a homomorphism of ordered sign covers
`Matrix.SignCover B →* Matrix.SignCover B'` that fixes the central `ℤˣ` and lies over `g`.

The lift rescales the canonical section by a sign `σ`, so `σ` must satisfy the coboundary equation
`ε(a, b) σ(a + b) = ε'(g a, g b) σ(a) σ(b)`. The two sides are governed by the *isometry defect*
`δ(a, b) = β'(g a, g b) - β(a, b)` (`Matrix.isometryDefect`), a bilinear form on `I → ℤ`. Both
`β + βᵀ` and `β' + β'ᵀ` are congruent to the Gram pairings modulo `2`
(`Matrix.even_orderedSignForm_add_orderedSignForm_swap_sub`), and `g` preserves the Gram pairings,
so `δ` is symmetric modulo `2` (`Matrix.even_isometryDefect_add_swap`).

Every integer matrix `D` symmetric modulo `2` has an explicit quadratic refinement modulo `2`
(`Matrix.quadraticRefinement`),

`q(a) = ∑_{j < i} a i * D i j * a j + ∑ i, D i i * (a i).choose 2`,

whose polarization `q(a + b) - q(a) - q(b)` is congruent to `a ⬝ᵥ D *ᵥ b` modulo `2`
(`Matrix.even_quadraticRefinement_add_sub`). The binomial terms on the diagonal are needed: unlike
the matrix of the ordered form, the matrix of `δ` can have odd diagonal entries, for instance when
`g` sends a simple root of a simply laced diagram to a sum of two adjacent simple roots, and no
quadratic form `∑_{i ≤ j} c i j * a i * a j` polarizes to an odd diagonal term. The sign
`σ = (-1) ^ q`, for `D` the matrix of `δ`, is the isometry sign `Matrix.isometrySign`, and it solves
the coboundary equation (`Matrix.negOnePow_orderedSignForm_mul_isometrySign_add`).

The lift is `Matrix.SignCover.map`, `(s, a) ↦ (s σ(a), g a)`. It fixes the kernel `ℤˣ` and hence
the central sign `τ`, and it sends the lift `(1, αᵢ)` of each coordinate vector to the canonical
lift `(1, g αᵢ)`, since `σ` is `1` on coordinate vectors. For a linear equivalence `g` it is an
isomorphism `Matrix.SignCover.congr`. The identity isometry lifts to the identity.

## Main definitions

* `Matrix.quadraticRefinement D`: the quadratic refinement modulo `2` of an integer matrix `D`.
* `Matrix.isometryDefect B B' g`: the bilinear form `β'(g a, g b) - β(a, b)`.
* `Matrix.isometrySign B B' g`: the sign `σ = (-1) ^ q` for `q` the quadratic refinement of the
  matrix of the isometry defect.
* `Matrix.SignCover.map`: the lift `(s, a) ↦ (s σ(a), g a)` of an isometry to the sign covers.
* `Matrix.SignCover.congr`: the same lift of an isometric linear equivalence, as an isomorphism.

## Main results

* `Matrix.quadraticRefinement_add`: the exact polarization of the quadratic refinement.
* `Matrix.even_quadraticRefinement_add_sub`: for `D` symmetric modulo `2`, the polarization of `q`
  is congruent to `a ⬝ᵥ D *ᵥ b` modulo `2`.
* `Matrix.even_isometryDefect_add_swap`: the isometry defect is symmetric modulo `2`.
* `Matrix.negOnePow_orderedSignForm_mul_isometrySign_add`: the coboundary equation
  `ε(a, b) σ(a + b) = ε'(g a, g b) σ(a) σ(b)`.
* `Matrix.SignCover.map_inl`, `Matrix.SignCover.map_tau`, `Matrix.SignCover.map_canonicalSection`,
  `Matrix.SignCover.map_canonicalSection_single`: the lift fixes the kernel `ℤˣ` and acts on the
  section `a ↦ (1, a)` by `σ`.
* `Matrix.SignCover.map_id`: the identity isometry lifts to the identity.

## References

* I. B. Frenkel, J. Lepowsky and A. Meurman, *Vertex operator algebras and the Monster*, Pure and
  Applied Mathematics **134**, Academic Press (1988), Chapter 5.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix

open TauCeti

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [LinearOrder J]

section QuadraticRefinement

variable (D : Matrix I I ℤ)

/-- **The quadratic refinement** of an integer matrix `D`: the function on `I → ℤ`
`q(a) = ∑_{j < i} a i * D i j * a j + ∑ i, D i i * (a i).choose 2`.
When `D` is symmetric modulo `2`, its polarization `q(a + b) - q(a) - q(b)` is congruent to
`a ⬝ᵥ D *ᵥ b` modulo `2` (`Matrix.even_quadraticRefinement_add_sub`), so `(-1) ^ q` trivializes
the sign `(-1) ^ (a ⬝ᵥ D *ᵥ b)` as a coboundary. -/
noncomputable def quadraticRefinement (a : I → ℤ) : ℤ :=
  orderedSignForm D a a + ∑ i, D i i * Ring.choose (a i) 2

theorem quadraticRefinement_def (a : I → ℤ) :
    quadraticRefinement D a = orderedSignForm D a a + ∑ i, D i i * Ring.choose (a i) 2 :=
  (rfl)

@[simp]
theorem quadraticRefinement_zero : quadraticRefinement D 0 = 0 := by
  simp [quadraticRefinement]

/-- On a multiple of a coordinate vector only the diagonal binomial term of the quadratic
refinement survives. -/
@[simp]
theorem quadraticRefinement_single (i : I) (n : ℤ) :
    quadraticRefinement D (Pi.single i n) = D i i * Ring.choose n 2 := by
  have hform : orderedSignForm D (Pi.single i n) (Pi.single i n) = 0 := by
    rw [orderedSignForm_apply]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hk : k = i
    · by_cases hl : l = i
      · subst hk hl
        simp
      · simp [hl]
    · simp [hk]
  rw [quadraticRefinement, hform, zero_add, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- **The polarization of the quadratic refinement**: the defect of additivity of
`Matrix.quadraticRefinement D` is the symmetrized ordered form of `D` plus its diagonal part. -/
theorem quadraticRefinement_add (a b : I → ℤ) :
    quadraticRefinement D (a + b) = quadraticRefinement D a + quadraticRefinement D b +
      (orderedSignForm D a b + orderedSignForm D b a + ∑ i, a i * D i i * b i) := by
  have hchoose (x y : ℤ) := TauCeti.Ring.add_choose_two (Commute.all x y)
  simp only [quadraticRefinement, map_add, LinearMap.add_apply, Pi.add_apply, hchoose, mul_add,
    Finset.sum_add_distrib]
  have hdiag : ∑ i, D i i * (a i * b i) = ∑ i, a i * D i i * b i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hdiag]
  ring

/-- **The quadratic refinement polarizes to `D` modulo `2`.** If `D` is symmetric modulo `2`, then
`q(a + b) - q(a) - q(b)` and `a ⬝ᵥ D *ᵥ b` have the same parity, for `q` the quadratic refinement
`Matrix.quadraticRefinement D`. -/
theorem even_quadraticRefinement_add_sub (hD : ∀ i j, Even (D i j + D j i)) (a b : I → ℤ) :
    Even (quadraticRefinement D (a + b) - quadraticRefinement D a - quadraticRefinement D b -
      a ⬝ᵥ D *ᵥ b) := by
  -- Termwise, the pairs `j < i` and `i = j` cancel exactly, and a pair `i < j` leaves
  -- `a i * (D j i - D i j) * b j`, which is even.
  have key : ∀ i j, Even ((if j < i then a i * D i j * b j else 0) +
      (if i < j then b j * D j i * a i else 0) + (if i = j then a i * D i i * b i else 0) -
      a i * (D i j * b j)) := fun i j => by
    rcases lt_trichotomy j i with h | rfl | h
    · simp [h, h.not_gt, h.ne', mul_assoc]
    · simp [mul_assoc]
    · obtain ⟨k, hk⟩ := hD i j
      simp only [h.not_gt, h, h.ne, ite_false, ite_true, zero_add, add_zero]
      exact ⟨a i * b j * k - a i * D i j * b j, by linear_combination (a i * b j) * hk⟩
  have hsum : quadraticRefinement D (a + b) - quadraticRefinement D a -
      quadraticRefinement D b - a ⬝ᵥ D *ᵥ b =
      ∑ i, ∑ j, ((if j < i then a i * D i j * b j else 0) +
        (if i < j then b j * D j i * a i else 0) + (if i = j then a i * D i i * b i else 0) -
        a i * (D i j * b j)) := by
    rw [quadraticRefinement_add, orderedSignForm_apply D b a, Finset.sum_comm (f := fun i j =>
      if j < i then b i * D i j * a j else 0)]
    simp only [orderedSignForm_apply, dotProduct, mulVec, Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    ring
  rw [hsum]
  exact Finset.even_sum _ fun i _ => Finset.even_sum _ fun j _ => key i j

/-- **The sign of the quadratic refinement is a coboundary trivializing `(-1) ^ (a ⬝ᵥ D *ᵥ b)`**:
for `D` symmetric modulo `2`, `(-1) ^ q(a + b) = (-1) ^ q(a) (-1) ^ q(b) (-1) ^ (a ⬝ᵥ D *ᵥ b)`,
for `q` the quadratic refinement `Matrix.quadraticRefinement D`. -/
theorem negOnePow_quadraticRefinement_add (hD : ∀ i j, Even (D i j + D j i)) (a b : I → ℤ) :
    (quadraticRefinement D (a + b)).negOnePow =
      (quadraticRefinement D a).negOnePow * (quadraticRefinement D b).negOnePow *
        (a ⬝ᵥ D *ᵥ b).negOnePow := by
  simp only [← Int.negOnePow_add]
  rw [Int.negOnePow_eq_iff]
  convert even_quadraticRefinement_add_sub D hD a b using 1
  ring

end QuadraticRefinement

section Isometry

variable (B : Matrix I I ℤ) (B' : Matrix J J ℤ) (g : (I → ℤ) →ₗ[ℤ] (J → ℤ))

/-- **The isometry defect** of a linear map `g : (I → ℤ) →ₗ[ℤ] (J → ℤ)` between lattices with
Gram matrices `B` and `B'`: the bilinear form `δ(a, b) = β'(g a, g b) - β(a, b)` comparing the
ordered form `β'` of `B'` pulled back along `g` with the ordered form `β` of `B`. -/
noncomputable def isometryDefect : LinearMap.BilinForm ℤ (I → ℤ) :=
  (orderedSignForm B').compl₁₂ g g - orderedSignForm B

@[simp]
theorem isometryDefect_apply (a b : I → ℤ) :
    isometryDefect B B' g a b = orderedSignForm B' (g a) (g b) - orderedSignForm B a b :=
  (rfl)

/-- **The isometry defect is symmetric modulo `2`.** For symmetric Gram matrices `B` and `B'` with
even diagonal and an isometry `g`, the sum `δ(a, b) + δ(b, a)` is even: the symmetrized ordered
forms are congruent to the Gram pairings modulo `2`, and `g` preserves the Gram pairings. -/
theorem even_isometryDefect_add_swap (hB : B.IsSymm) (hBdiag : ∀ i, Even (B i i))
    (hB' : B'.IsSymm) (hB'diag : ∀ j, Even (B' j j))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (a b : I → ℤ) :
    Even (isometryDefect B B' g a b + isometryDefect B B' g b a) := by
  have h := (even_orderedSignForm_add_orderedSignForm_swap_sub B' hB' hB'diag (g a) (g b)).sub
    (even_orderedSignForm_add_orderedSignForm_swap_sub B hB hBdiag a b)
  rw [hg] at h
  convert h using 1
  simp only [isometryDefect_apply]
  ring

/-- **The isometry sign** `σ(a) = (-1) ^ q(a)` of a linear map `g` between lattices with Gram
matrices `B` and `B'`, where `q` is the quadratic refinement (`Matrix.quadraticRefinement`) of the
matrix of the isometry defect `Matrix.isometryDefect B B' g`. When `g` is an isometry it is the
sign by which the lift `Matrix.SignCover.map` of `g` rescales the canonical section. -/
noncomputable def isometrySign (a : I → ℤ) : ℤˣ :=
  (quadraticRefinement (LinearMap.BilinForm.toMatrix' (isometryDefect B B' g)) a).negOnePow

theorem isometrySign_def (a : I → ℤ) :
    isometrySign B B' g a =
      (quadraticRefinement (LinearMap.BilinForm.toMatrix' (isometryDefect B B' g)) a).negOnePow :=
  (rfl)

@[simp]
theorem isometrySign_zero : isometrySign B B' g 0 = 1 := by
  simp [isometrySign]

/-- **The isometry sign of a coordinate vector is `1`.** -/
@[simp]
theorem isometrySign_single (i : I) : isometrySign B B' g (Pi.single i 1) = 1 := by
  have h : Ring.choose (1 : ℤ) 2 = 0 := by simpa using Ring.choose_natCast (R := ℤ) 1 2
  simp [isometrySign, h]

/-- **The identity has isometry sign `1`**: its isometry defect vanishes. -/
@[simp]
theorem isometrySign_id (a : I → ℤ) : isometrySign B B LinearMap.id a = 1 := by
  have h : isometryDefect B B LinearMap.id = 0 := by
    ext a b
    simp
  rw [isometrySign, h, map_zero, Int.negOnePow_eq_one_iff, quadraticRefinement_def,
    orderedSignForm_apply]
  simp

/-- **The ordered signs differ by the coboundary of the isometry sign.** For symmetric Gram
matrices `B` and `B'` with even diagonal and an isometry `g`, with `ε` and `ε'` the ordered signs
of `B` and `B'` and `σ` the isometry sign of `g`,
`ε(a, b) σ(a + b) = ε'(g a, g b) σ(a) σ(b)`. -/
theorem negOnePow_orderedSignForm_mul_isometrySign_add (hB : B.IsSymm)
    (hBdiag : ∀ i, Even (B i i)) (hB' : B'.IsSymm) (hB'diag : ∀ j, Even (B' j j))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (a b : I → ℤ) :
    (orderedSignForm B a b).negOnePow * isometrySign B B' g (a + b) =
      (orderedSignForm B' (g a) (g b)).negOnePow *
        (isometrySign B B' g a * isometrySign B B' g b) := by
  set D := LinearMap.BilinForm.toMatrix' (isometryDefect B B' g)
  have hD : ∀ i j, Even (D i j + D j i) := fun i j => by
    simpa only [D, LinearMap.BilinForm.toMatrix'_apply] using
      even_isometryDefect_add_swap B B' g hB hBdiag hB' hB'diag hg (Pi.single i 1) (Pi.single j 1)
  have hδ : a ⬝ᵥ D *ᵥ b = orderedSignForm B' (g a) (g b) - orderedSignForm B a b := by
    rw [← toBilin'_apply', toBilin'_toMatrix', isometryDefect_apply]
  have h := even_quadraticRefinement_add_sub D hD a b
  rw [hδ] at h
  simp only [isometrySign_def, ← Int.negOnePow_add]
  rw [Int.negOnePow_eq_iff]
  convert h using 1
  ring

end Isometry

section Cover

attribute [local instance] trivialMulDistribMulAction

variable {B : Matrix I I ℤ} {B' : Matrix J J ℤ}

/-- **The lift of a lattice isometry to the ordered sign covers.** For symmetric Gram matrices `B`
and `B'` with even diagonal and an isometry `g`, the homomorphism `(s, a) ↦ (s σ(a), g a)` from the
ordered sign cover of `B` to that of `B'`, where `σ` is the isometry sign of `g`. It fixes the
kernel `ℤˣ` (`Matrix.SignCover.map_inl`) and lies over `g` (`Matrix.SignCover.map_right`); it is a
homomorphism by the coboundary equation `Matrix.negOnePow_orderedSignForm_mul_isometrySign_add`. -/
noncomputable def SignCover.map (hB : B.IsSymm) (hBdiag : ∀ i, Even (B i i)) (hB' : B'.IsSymm)
    (hB'diag : ∀ j, Even (B' j j)) (g : (I → ℤ) →ₗ[ℤ] (J → ℤ))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) : SignCover B →* SignCover B' where
  toFun x := ⟨x.left * isometrySign B B' g x.right.toAdd, .ofAdd (g x.right.toAdd)⟩
  map_one' := by
    ext <;> simp
  map_mul' x y := by
    ext
    · simp only [FactorSet.Extension.mul_left, trivialMulDistribMulAction_smul,
        signFactorSet_apply, orderedSign_apply, FactorSet.Extension.mul_right, toAdd_mul,
        toAdd_ofAdd, mul_assoc]
      rw [negOnePow_orderedSignForm_mul_isometrySign_add B B' g hB hBdiag hB' hB'diag hg]
      ac_rfl
    · simp

variable (hB : B.IsSymm) (hBdiag : ∀ i, Even (B i i)) (hB' : B'.IsSymm)
  (hB'diag : ∀ j, Even (B' j j))

section Map

variable (g : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b)

@[simp]
theorem SignCover.map_left (x : SignCover B) :
    (SignCover.map hB hBdiag hB' hB'diag g hg x).left =
      x.left * isometrySign B B' g x.right.toAdd :=
  (rfl)

@[simp]
theorem SignCover.map_right (x : SignCover B) :
    (SignCover.map hB hBdiag hB' hB'diag g hg x).right = .ofAdd (g x.right.toAdd) :=
  (rfl)

/-- The lift of an isometry to the ordered sign covers fixes the kernel `ℤˣ`. -/
@[simp]
theorem SignCover.map_inl (u : ℤˣ) :
    SignCover.map hB hBdiag hB' hB'diag g hg (FactorSet.inl (signFactorSet B) u) =
      FactorSet.inl (signFactorSet B') u := by
  ext <;> simp

/-- The lift of an isometry to the ordered sign covers fixes the central sign `τ`. -/
@[simp]
theorem SignCover.map_tau :
    SignCover.map hB hBdiag hB' hB'diag g hg (SignCover.tau B) = SignCover.tau B' := by
  ext <;> simp

/-- The lift of an isometry `g` to the ordered sign covers sends the lift `(1, a)` to
`σ(a) (1, g a)`, for `σ` the isometry sign of `g`. -/
theorem SignCover.map_canonicalSection (a : Multiplicative (I → ℤ)) :
    SignCover.map hB hBdiag hB' hB'diag g hg ((signFactorSet B).canonicalSection a) =
      FactorSet.inl (signFactorSet B') (isometrySign B B' g a.toAdd) *
        (signFactorSet B').canonicalSection (.ofAdd (g a.toAdd)) := by
  ext <;> simp

/-- **The lift of an isometry respects the simple lifts**: it sends the lift `(1, αᵢ)` of a
coordinate vector to the canonical lift `(1, g αᵢ)` of its image. -/
theorem SignCover.map_canonicalSection_single (i : I) :
    SignCover.map hB hBdiag hB' hB'diag g hg
        ((signFactorSet B).canonicalSection (.ofAdd (Pi.single i 1))) =
      (signFactorSet B').canonicalSection (.ofAdd (g (Pi.single i 1))) := by
  ext <;> simp

end Map

/-- **The identity isometry lifts to the identity** of the ordered sign cover. -/
@[simp]
theorem SignCover.map_id :
    SignCover.map hB hBdiag hB hBdiag LinearMap.id (fun _ _ => rfl) = MonoidHom.id _ := by
  ext x <;> simp

/-- **The lift of an isometric linear equivalence to the ordered sign covers**, as an isomorphism:
the homomorphism `Matrix.SignCover.map` of `g`, `(s, a) ↦ (s σ(a), g a)`, with inverse
`(s, b) ↦ (s σ(g⁻¹ b), g⁻¹ b)`, where `σ` is the isometry sign of `g`. -/
noncomputable def SignCover.congr (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) : SignCover B ≃* SignCover B' where
  __ := SignCover.map hB hBdiag hB' hB'diag g.toLinearMap hg
  invFun y := ⟨y.left * isometrySign B B' g.toLinearMap (g.symm y.right.toAdd),
    .ofAdd (g.symm y.right.toAdd)⟩
  left_inv x := by
    ext <;> simp [mul_assoc]
  right_inv y := by
    ext <;> simp [mul_assoc]

@[simp]
theorem SignCover.congr_apply (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (x : SignCover B) :
    SignCover.congr hB hBdiag hB' hB'diag g hg x =
      SignCover.map hB hBdiag hB' hB'diag g.toLinearMap hg x :=
  (rfl)

@[simp]
theorem SignCover.congr_symm_left (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (y : SignCover B') :
    ((SignCover.congr hB hBdiag hB' hB'diag g hg).symm y).left =
      y.left * isometrySign B B' g.toLinearMap (g.symm y.right.toAdd) :=
  (rfl)

@[simp]
theorem SignCover.congr_symm_right (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
    (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (y : SignCover B') :
    ((SignCover.congr hB hBdiag hB' hB'diag g hg).symm y).right = .ofAdd (g.symm y.right.toAdd) :=
  (rfl)

end Cover

end Matrix
