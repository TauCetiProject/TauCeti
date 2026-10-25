/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover

/-!
# Relabelling the vertices of the ordered sign cover

The ordered sign `ε(a, b) = (-1) ^ β(a, b)` of a Gram matrix `B : Matrix I I ℤ`
(`Matrix.orderedSignForm`) depends on the linear order of the vertex set `I`. This file compares
the signs, and the sign covers, of two vertex labellings. Let `e : I ≃ J` be a bijection onto a
second linearly ordered finite set, and let `B' = B.reindex e e` be the same Gram matrix on the
new labels, so that `a ↦ a ∘ e.symm` is an isometry `I → ℤ ≃ J → ℤ`. A change of the order of
`I` is the case where `e` is the identity map of `I` onto a copy of it carrying the new order,
and a diagram automorphism is the case `J = I` with `B.reindex e e = B`.

The pairs `j < i` of `I` with `e i < e j` are the *inversions* of `e`. Keeping only the entries
of `B` at the inversions gives the inversion form (`Matrix.inversionForm`)

`ρ(a, b) = ∑_{j < i, e i < e j} a i * B i j * b j`,

and the inversion sign is `σ(a) = (-1) ^ ρ(a, a)` (`Matrix.inversionSign`). For a symmetric
`B`, only the unordered bonds `{i, j}` whose relative order `e` reverses contribute to `σ`, and
the ordered forms of the two labellings differ by the antisymmetrization of `ρ`
(`Matrix.orderedSignForm_reindex`). Hence the two ordered signs differ by the coboundary of `σ`:

`ε(a, b) σ(a + b) = ε'(a ∘ e.symm, b ∘ e.symm) σ(a) σ(b)`

(`Matrix.negOnePow_orderedSignForm_mul_inversionSign_add`). Rescaling the canonical section by
`σ` therefore relabels the ordered sign cover: `(s, a) ↦ (s σ(a), a ∘ e.symm)` is an isomorphism
`Matrix.SignCover.reindex` from the cover of `B` to the cover of `B'`. It fixes the central
sign and sends the lift `(1, αᵢ)` of each simple root to the lift `(1, α_(e i))`, since a
coordinate vector has inversion sign `1`. The inversion signs compose along `e.trans f` up to an
even correction (`Matrix.inversionSign_trans`), so the relabellings compose
(`Matrix.SignCover.reindex_trans`), and the identity relabels by the identity.

## Main definitions

* `Matrix.inversionForm B e`: the bilinear form of the entries of `B` at the inversions of `e`.
* `Matrix.inversionSign B e`: the sign `σ(a) = (-1) ^ ρ(a, a)`.
* `Matrix.SignCover.reindex`: the isomorphism `(s, a) ↦ (s σ(a), a ∘ e.symm)` of sign covers.

## Main results

* `Matrix.orderedSignForm_reindex`: the ordered form of the relabelled matrix is
  `β(a, b) + ρ(b, a) - ρ(a, b)`, for symmetric `B`.
* `Matrix.negOnePow_orderedSignForm_mul_inversionSign_add`: the two ordered signs differ by the
  coboundary of `σ`.
* `Matrix.inversionSign_single`: the inversion sign of a coordinate vector is `1`.
* `Matrix.inversionSign_trans`: the inversion signs of a composite relabelling.
* `Matrix.SignCover.reindex_tau`, `Matrix.SignCover.reindex_inl`,
  `Matrix.SignCover.reindex_canonicalSection`, `Matrix.SignCover.reindex_canonicalSection_single`:
  the relabelling fixes the kernel `ℤˣ` and acts on the section `a ↦ (1, a)` by `σ`.
* `Matrix.SignCover.reindex_refl`, `Matrix.SignCover.reindex_trans`: the relabellings are
  functorial.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix

open TauCeti

variable {I J K : Type*} [Fintype I] [LinearOrder I] [LinearOrder J] [LinearOrder K]
  (B : Matrix I I ℤ) (e : I ≃ J)

/-- **The inversion form** of a relabelling `e : I ≃ J` of the vertices of an integer matrix `B`:
the bilinear form on `I → ℤ` of the entries of `B` at the inversions of `e`, the pairs `j < i`
with `e i < e j`,
`inversionForm B e a b = ∑_{j < i, e i < e j} a i * B i j * b j`. -/
noncomputable def inversionForm : LinearMap.BilinForm ℤ (I → ℤ) :=
  toBilin' (of fun i j => if j < i ∧ e i < e j then B i j else 0)

theorem inversionForm_apply (a b : I → ℤ) :
    inversionForm B e a b =
      ∑ i, ∑ j, if j < i ∧ e i < e j then a i * B i j * b j else 0 := by
  simp only [inversionForm, toBilin'_apply, of_apply, mul_ite, ite_mul, mul_zero, zero_mul]

/-- **The inversion sign** `σ(a) = (-1) ^ ρ(a, a)` of a relabelling `e` of the vertices of `B`,
where `ρ` is the inversion form `Matrix.inversionForm B e`. For a symmetric `B` it is the parity
of `∑ a i * B i j * a j` over the unordered pairs `{i, j}` whose relative order `e` reverses. -/
noncomputable def inversionSign (a : I → ℤ) : ℤˣ :=
  (inversionForm B e a a).negOnePow

theorem inversionSign_def (a : I → ℤ) : inversionSign B e a = (inversionForm B e a a).negOnePow :=
  (rfl)

@[simp]
theorem inversionSign_zero : inversionSign B e 0 = 1 := by
  simp [inversionSign]

@[simp]
theorem inversionSign_neg (a : I → ℤ) : inversionSign B e (-a) = inversionSign B e a := by
  simp [inversionSign]

/-- **A coordinate vector has inversion sign `1`**: the inversion form vanishes on the diagonal. -/
@[simp]
theorem inversionSign_single [DecidableEq I] (i : I) (n : ℤ) :
    inversionSign B e (Pi.single i n) = 1 := by
  rw [inversionSign, inversionForm_apply, Int.negOnePow_eq_one_iff]
  refine Finset.even_sum _ fun k _ => Finset.even_sum _ fun l _ => ?_
  by_cases hk : k = i
  · by_cases hl : l = i
    · subst hk hl
      simp
    · simp [hl]
  · simp [hk]

/-- **The inversion sign of the identity relabelling is `1`.** -/
@[simp]
theorem inversionSign_refl (a : I → ℤ) : inversionSign B (Equiv.refl I) a = 1 := by
  rw [inversionSign, inversionForm_apply, Int.negOnePow_eq_one_iff]
  refine Finset.even_sum _ fun i _ => Finset.even_sum _ fun j _ => ?_
  rw [ite_eq_right_iff.mpr fun h => absurd h.2 (lt_asymm h.1)]
  exact Even.zero

/-- The inversion sign of a sum differs from the product of the inversion signs by the symmetrized
inversion form. -/
theorem inversionSign_add (a b : I → ℤ) :
    inversionSign B e (a + b) =
      inversionSign B e a * inversionSign B e b *
        (inversionForm B e a b + inversionForm B e b a).negOnePow := by
  simp only [inversionSign, map_add, LinearMap.add_apply, ← Int.negOnePow_add]
  congr 1
  ring

omit [Fintype I] in
/-- The termwise form of `Matrix.orderedSignForm_reindex`: for `i ≠ j` exactly one of `j < i`
and `i < j` holds, and similarly for `e i` and `e j`. -/
private theorem ite_reindex_eq (i j : I) (x : ℤ) :
    (if e j < e i then x else 0) = (if j < i then x else 0) +
      (if i < j ∧ e j < e i then x else 0) - if j < i ∧ e i < e j then x else 0 := by
  rcases lt_trichotomy j i with h | rfl | h
  · rcases lt_trichotomy (e j) (e i) with h' | h' | h'
    · simp [h, h', h.not_gt, h'.not_gt]
    · exact absurd (e.injective h') h.ne
    · simp [h, h', h.not_gt, h'.not_gt]
  · simp
  · rcases lt_trichotomy (e j) (e i) with h' | h' | h'
    · simp [h, h', h.not_gt, h'.not_gt]
    · exact absurd (e.injective h') h.ne'
    · simp [h, h', h.not_gt, h'.not_gt]

variable [Fintype J]

/-- **The ordered form of a relabelled matrix.** For a symmetric `B` and a relabelling
`e : I ≃ J` of its vertices, the ordered form of `B.reindex e e` on the relabelled vectors is the
ordered form of `B` corrected by the antisymmetrization of the inversion form `ρ`:
`β'(a ∘ e.symm, b ∘ e.symm) = β(a, b) + ρ(b, a) - ρ(a, b)`. -/
theorem orderedSignForm_reindex (hB : B.IsSymm) (a b : I → ℤ) :
    orderedSignForm (B.reindex e e) (a ∘ e.symm) (b ∘ e.symm) =
      orderedSignForm B a b + inversionForm B e b a - inversionForm B e a b := by
  -- The middle sum runs over the pairs `j < i` with `e i < e j`; swapping the two summation
  -- variables, and using the symmetry of `B`, turns it into the pairs `i < j` with `e j < e i`.
  have hswap : inversionForm B e b a =
      ∑ i, ∑ j, if i < j ∧ e j < e i then a i * B i j * b j else 0 := by
    rw [inversionForm_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB.apply i j]
    split_ifs <;> ring
  rw [hswap, orderedSignForm_apply, orderedSignForm_apply, inversionForm_apply,
    ← e.sum_comp]
  simp only [← e.sum_comp, Function.comp_apply, Equiv.symm_apply_apply, reindex_apply,
    submatrix_apply]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    ite_reindex_eq e i j _

/-- **The ordered signs of two labellings differ by the coboundary of the inversion sign.** For a
symmetric `B` and a relabelling `e : I ≃ J` of its vertices, with `ε` and `ε'` the ordered signs
of `B` and `B.reindex e e` and `σ` the inversion sign of `e`,
`ε(a, b) σ(a + b) = ε'(a ∘ e.symm, b ∘ e.symm) σ(a) σ(b)`. -/
theorem negOnePow_orderedSignForm_mul_inversionSign_add (hB : B.IsSymm) (a b : I → ℤ) :
    (orderedSignForm B a b).negOnePow * inversionSign B e (a + b) =
      (orderedSignForm (B.reindex e e) (a ∘ e.symm) (b ∘ e.symm)).negOnePow *
        (inversionSign B e a * inversionSign B e b) := by
  rw [orderedSignForm_reindex B e hB, inversionSign_add, inversionSign, inversionSign]
  simp only [← Int.negOnePow_add]
  rw [Int.negOnePow_eq_iff]
  exact ⟨inversionForm B e a b, by ring⟩

omit [Fintype I] [Fintype J] in
/-- The termwise form of `Matrix.inversionSign_trans`, for a pair `j < i`. -/
private theorem ite_trans_add (f : J ≃ K) {i j : I} (hji : j < i) (x : ℤ) :
    (if e i < e j then x else 0) +
        ((if e j < e i ∧ f (e i) < f (e j) then x else 0) +
          if e i < e j ∧ f (e j) < f (e i) then x else 0) =
      (if f (e i) < f (e j) then x else 0) +
        2 * if e i < e j ∧ f (e j) < f (e i) then x else 0 := by
  have hne : e i ≠ e j := e.injective.ne hji.ne'
  have hne' : f (e i) ≠ f (e j) := f.injective.ne hne
  rcases hne.lt_or_gt with h | h <;> rcases hne'.lt_or_gt with h' | h' <;>
    simp [h, h', h.not_gt, h'.not_gt, two_mul]

/-- **The inversion signs of a composite relabelling.** For a symmetric `B` and relabellings
`e : I ≃ J` and `f : J ≃ K`, the inversion sign of `e.trans f` is the product of the inversion
sign of `e` and that of `f` on the relabelled matrix `B.reindex e e` and vector `a ∘ e.symm`: a
pair reversed by both `e` and `f` is not an inversion of the composite, and is counted twice by
the product. -/
theorem inversionSign_trans (hB : B.IsSymm) (f : J ≃ K) (a : I → ℤ) :
    inversionSign B (e.trans f) a =
      inversionSign B e a * inversionSign (B.reindex e e) f (a ∘ e.symm) := by
  -- Sum the inversions of `f` over the pairs `e j < e i`, and split them according to the order
  -- of `i` and `j`; the pairs with `i < j` become pairs with `j < i` after swapping the summation
  -- variables, by the symmetry of `B`.
  have hsplit : inversionForm (B.reindex e e) f (a ∘ e.symm) (a ∘ e.symm) =
      ∑ i, ∑ j, ((if j < i ∧ e j < e i ∧ f (e i) < f (e j) then a i * B i j * a j else 0) +
        if j < i ∧ e i < e j ∧ f (e j) < f (e i) then a i * B i j * a j else 0) := by
    rw [inversionForm_apply, ← e.sum_comp]
    simp only [← e.sum_comp, Function.comp_apply, Equiv.symm_apply_apply, reindex_apply,
      submatrix_apply]
    have hlow : (∑ i, ∑ j, if e j < e i ∧ f (e i) < f (e j) then a i * B i j * a j else 0) =
        ∑ i, ∑ j, ((if j < i ∧ e j < e i ∧ f (e i) < f (e j) then a i * B i j * a j else 0) +
          if i < j ∧ e j < e i ∧ f (e i) < f (e j) then a i * B i j * a j else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy j i with h | rfl | h
      · simp [h, h.not_gt]
      · simp
      · simp [h, h.not_gt]
    rw [hlow]
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB.apply i j]
    split_ifs <;> ring
  rw [inversionSign, inversionSign, inversionSign, hsplit, ← Int.negOnePow_add,
    Int.negOnePow_eq_iff]
  refine ⟨-∑ i, ∑ j, if j < i ∧ e i < e j ∧ f (e j) < f (e i) then a i * B i j * a j else 0,
    ?_⟩
  rw [inversionForm_apply, inversionForm_apply]
  simp only [Equiv.trans_apply, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases lt_or_ge j i with h | h
  · have key := ite_trans_add e f h (a i * B i j * a j)
    simp only [h, true_and] at key ⊢
    split_ifs at key ⊢ <;> linarith
  · simp [h.not_gt]

section Cover

attribute [local instance] trivialMulDistribMulAction

variable {B} {B' : Matrix J J ℤ}

/-- **Relabelling the ordered sign cover.** For a symmetric `B` and a relabelling `e : I ≃ J` of
its vertices with `B.reindex e e = B'`, the isomorphism `(s, a) ↦ (s σ(a), a ∘ e.symm)` from the
ordered sign cover of `B` to that of `B'`, where `σ` is the inversion sign of `e`. It rescales the
canonical section `a ↦ (1, a)` by `σ`, which turns the ordered sign of `B` into the pullback of
that of `B'` by `Matrix.negOnePow_orderedSignForm_mul_inversionSign_add`, and then relabels the
lattice. -/
noncomputable def SignCover.reindex (hB : B.IsSymm) (he : B.reindex e e = B') :
    SignCover B ≃* SignCover B' where
  toFun x := ⟨x.left * inversionSign B e x.right.toAdd, .ofAdd (x.right.toAdd ∘ e.symm)⟩
  invFun y := ⟨y.left * inversionSign B e (y.right.toAdd ∘ e), .ofAdd (y.right.toAdd ∘ e)⟩
  left_inv x := by
    ext <;> simp [Function.comp_assoc, mul_assoc]
  right_inv y := by
    ext <;> simp [Function.comp_assoc, mul_assoc]
  map_mul' x y := by
    subst he
    ext
    · simp only [FactorSet.Extension.mul_left, trivialMulDistribMulAction_smul,
        signFactorSet_apply, orderedSign_apply, FactorSet.Extension.mul_right, toAdd_mul,
        toAdd_ofAdd, mul_assoc]
      rw [negOnePow_orderedSignForm_mul_inversionSign_add B e hB]
      ac_rfl
    · rfl

@[simp]
theorem SignCover.reindex_left (hB : B.IsSymm) (he : B.reindex e e = B') (x : SignCover B) :
    (SignCover.reindex e hB he x).left = x.left * inversionSign B e x.right.toAdd :=
  (rfl)

@[simp]
theorem SignCover.reindex_right (hB : B.IsSymm) (he : B.reindex e e = B') (x : SignCover B) :
    (SignCover.reindex e hB he x).right = .ofAdd (x.right.toAdd ∘ e.symm) :=
  (rfl)

@[simp]
theorem SignCover.reindex_symm_left (hB : B.IsSymm) (he : B.reindex e e = B')
    (y : SignCover B') :
    ((SignCover.reindex e hB he).symm y).left = y.left * inversionSign B e (y.right.toAdd ∘ e) :=
  (rfl)

@[simp]
theorem SignCover.reindex_symm_right (hB : B.IsSymm) (he : B.reindex e e = B')
    (y : SignCover B') :
    ((SignCover.reindex e hB he).symm y).right = .ofAdd (y.right.toAdd ∘ e) :=
  (rfl)

/-- The relabelling of the ordered sign cover fixes the kernel `ℤˣ`. -/
@[simp]
theorem SignCover.reindex_inl (hB : B.IsSymm) (he : B.reindex e e = B') (u : ℤˣ) :
    SignCover.reindex e hB he (FactorSet.inl (signFactorSet B) u) =
      FactorSet.inl (signFactorSet B') u := by
  ext <;> simp [Pi.zero_comp]

/-- The relabelling of the ordered sign cover fixes the central sign `τ`. -/
@[simp]
theorem SignCover.reindex_tau (hB : B.IsSymm) (he : B.reindex e e = B') :
    SignCover.reindex e hB he (SignCover.tau B) = SignCover.tau B' := by
  ext <;> simp

/-- The relabelling of the ordered sign cover sends the lift `(1, a)` to `σ(a) (1, a ∘ e.symm)`. -/
theorem SignCover.reindex_canonicalSection (hB : B.IsSymm) (he : B.reindex e e = B')
    (a : Multiplicative (I → ℤ)) :
    SignCover.reindex e hB he ((signFactorSet B).canonicalSection a) =
      FactorSet.inl (signFactorSet B') (inversionSign B e a.toAdd) *
        (signFactorSet B').canonicalSection (.ofAdd (a.toAdd ∘ e.symm)) := by
  ext <;> simp

/-- **The relabelling of the ordered sign cover respects the simple lifts**: it sends the lift
`(1, αᵢ)` of the coordinate vector `αᵢ` to the lift `(1, α_(e i))`. -/
theorem SignCover.reindex_canonicalSection_single [DecidableEq I] [DecidableEq J] (hB : B.IsSymm)
    (he : B.reindex e e = B') (i : I) :
    SignCover.reindex e hB he ((signFactorSet B).canonicalSection (.ofAdd (Pi.single i 1))) =
      (signFactorSet B').canonicalSection (.ofAdd (Pi.single (e i) 1)) := by
  ext
  · simp
  · simp [Pi.single_comp_equiv]

/-- **The identity relabels the ordered sign cover by the identity.** -/
@[simp]
theorem SignCover.reindex_refl (hB : B.IsSymm) :
    SignCover.reindex (Equiv.refl I) hB (by simp) = MulEquiv.refl (SignCover B) := by
  ext x <;> simp

/-- **Relabellings of the ordered sign cover compose.** -/
theorem SignCover.reindex_trans [Fintype K] {B'' : Matrix K K ℤ} (f : J ≃ K) (hB : B.IsSymm)
    (he : B.reindex e e = B') (hB' : B'.IsSymm) (hf : B'.reindex f f = B'') :
    (SignCover.reindex e hB he).trans (SignCover.reindex f hB' hf) =
      SignCover.reindex (e.trans f) hB (by rw [← hf, ← he]; ext; simp) := by
  subst he hf
  refine MulEquiv.ext fun x => FactorSet.Extension.ext ?_ ?_
  · simp only [MulEquiv.trans_apply, reindex_left, reindex_right, toAdd_ofAdd,
      inversionSign_trans B e hB f, mul_assoc]
  · rfl

end Cover

end Matrix
