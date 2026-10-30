/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.Ring.Invertible

/-!
# Matrices equal to the negative of their transpose

A matrix satisfying `Mᵀ = -M` is determined by its entries above the diagonal, once its diagonal
is known to vanish: the entries below are the negatives of their mirror images. The diagonal does
vanish as soon as the value ring has no element that is its own negative apart from zero, which
covers every ring of odd characteristic.

## Main results

* `Matrix.transpose_single_sub_single`: transposing the difference of two opposite singleton
  matrices with the same coefficient negates it.
* `Matrix.transpose_map_of_transpose_eq_neg`: the condition passes to the image of the matrix
  under an additive morphism of the entry types.
* `Matrix.diag_eq_zero_of_transpose_eq_neg`: the diagonal vanishes when doubling is injective at
  zero, with `Matrix.diag_eq_zero_of_transpose_eq_neg_of_charP` reading that off an odd
  characteristic.
* `Matrix.trace_eq_zero_of_transpose_eq_neg`: the trace vanishes when `2` is invertible.
* `Matrix.ext_of_lt_of_transpose_eq_neg`: two such matrices with vanishing diagonals agree as soon
  as they agree above the diagonal.
* `Matrix.eta_fin_four_of_transpose_eq_neg`: a `4 × 4` such matrix written out in terms of its six
  entries above the diagonal.
* `Matrix.ofStrictUpper` and `Matrix.skewStrictUpperAddEquiv`: complete arbitrary strict-upper
  entries and give additive coordinates when doubling has trivial kernel.
* `Matrix.ofStrictUpper_apply`, `Matrix.ofStrictUpper_zero`, `Matrix.ofStrictUpper_neg`, and
  `Matrix.ofStrictUpper_add`: the entry formula and preservation of zero, negation, and addition.
* `Matrix.ofStrictUpper_apply_of_gt`: lower entries are the negatives of the supplied upper
  entries.
* `Matrix.natCard_transpose_eq_neg`: when doubling is injective at zero, the `Nat.card` of such
  matrices with entries in an additive subgroup `I` is `(Nat.card I) ^ (k.choose 2)`, for an
  index type of cardinality `k`; for finite `I` this is the number of such matrices.
-/

public section

namespace Matrix

variable {n : Type*} {S T : Type*}

/-- Transposing the difference of two opposite singleton matrices with the same coefficient
negates it. -/
theorem transpose_single_sub_single {K ι : Type*} [AddGroup K] [DecidableEq ι]
    (i j : ι) (a : K) :
    (single i j a - single j i a).transpose = -(single i j a - single j i a) := by
  simp only [transpose_sub, transpose_single, neg_sub]

/-- A strict-upper entry of the difference of opposite matrix units reads its coefficient. -/
theorem single_sub_single_apply_of_lt [LinearOrder n] [AddGroup S]
    (p q : {p : n × n // p.1 < p.2}) (x : S) :
    (single p.val.1 p.val.2 x - single p.val.2 p.val.1 x : Matrix n n S)
        q.val.1 q.val.2 = if p = q then x else 0 := by
  have hrev : ¬(p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) := by
    rintro ⟨h₁, h₂⟩
    have h := p.property
    rw [h₁, h₂] at h
    exact (not_lt_of_ge q.property.le) h
  have heq : (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) ↔ p = q :=
    ⟨fun h => Subtype.ext (Prod.ext h.1 h.2), fun h => by subst q; exact ⟨rfl, rfl⟩⟩
  simp [sub_apply, single_apply, hrev, heq]

/-- **The condition `Mᵀ = -M` passes to the image of the matrix** under an additive morphism of
the entry types. -/
theorem transpose_map_of_transpose_eq_neg [AddGroup S] [SubtractionMonoid T] {F : Type*}
    [FunLike F S T] [AddMonoidHomClass F S T] (f : F) {M : Matrix n n S} (hM : Mᵀ = -M) :
    (M.map f)ᵀ = -M.map f := by
  ext a b
  have h := congrFun (congrFun hM a) b
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, Matrix.map_apply, h, map_neg]

/-- **The diagonal of a matrix equal to the negative of its transpose vanishes**, as soon as zero
is the only entry that doubles to zero. -/
theorem diag_eq_zero_of_transpose_eq_neg [AddGroup S] {M : Matrix n n S} (hM : Mᵀ = -M)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a : n) : M a a = 0 := by
  refine h2 _ ?_
  have h := congrFun (congrFun hM a) a
  rw [Matrix.transpose_apply, Matrix.neg_apply] at h
  nth_rewrite 1 [h]
  rw [neg_add_cancel]

/-- A skew-symmetric matrix has trace zero when `2` is invertible. -/
theorem trace_eq_zero_of_transpose_eq_neg {R : Type*} [Fintype n] [Ring R]
    [Invertible (2 : R)] (X : Matrix n n R) (hX : Xᵀ = -X) : trace X = 0 := by
  exact Finset.sum_eq_zero fun a _ => diag_eq_zero_of_transpose_eq_neg hX
    (isUnit_of_invertible (2 : R)).eq_zero_of_add_self_eq_zero a

/-- **In a ring of odd characteristic the diagonal of a matrix equal to the negative of its
transpose vanishes**: odd characteristic implies that doubling is injective at zero, which
is what the diagonal entries need. -/
theorem diag_eq_zero_of_transpose_eq_neg_of_charP [Ring S] (p : ℕ) [CharP S p] (hp : Odd p)
    {M : Matrix n n S} (hM : Mᵀ = -M) (a : n) : M a a = 0 := by
  obtain ⟨k, hk⟩ := hp
  refine diag_eq_zero_of_transpose_eq_neg hM (fun x hx => ?_) a
  have hpz : ((2 * k + 1 : ℕ) : S) = 0 := by rw [← hk]; exact CharP.cast_eq_zero S p
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hpz
  have hx2 : (2 : S) * x = 0 := by rw [two_mul]; exact hx
  have key : ((2 : S) * (k : S) + 1) * x - (k : S) * ((2 : S) * x) = x := by
    rw [add_mul, one_mul, ← mul_assoc, (Nat.cast_commute k 2).eq, add_sub_cancel_left]
  rw [← key, hpz, hx2, zero_mul, mul_zero, sub_zero]

/-- **Two matrices equal to the negatives of their transposes agree as soon as they agree above
the diagonal**, provided both diagonals vanish: the entries below the diagonal are the negatives
of their mirror images. -/
theorem ext_of_lt_of_transpose_eq_neg [LinearOrder n] [Zero S] [Neg S] {M N : Matrix n n S}
    (hM : Mᵀ = -M) (hN : Nᵀ = -N) (hMd : ∀ a, M a a = 0) (hNd : ∀ a, N a a = 0)
    (h : ∀ a b : n, a < b → M a b = N a b) : M = N := by
  have hskew : ∀ K : Matrix n n S, Kᵀ = -K → ∀ a b, K b a = -K a b := by
    intro K hK a b
    have hab := congrFun (congrFun hK a) b
    rw [Matrix.transpose_apply, Matrix.neg_apply] at hab
    exact hab
  ext a b
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact h a b hab
  · rw [hMd a, hNd a]
  · rw [hskew M hM b a, hskew N hN b a, h b a hab]

/-- **A `4 × 4` matrix equal to the negative of its transpose, written out in terms of its six
entries above the diagonal**, as soon as zero is the only entry that doubles to zero. -/
theorem eta_fin_four_of_transpose_eq_neg [AddGroup S] {M : Matrix (Fin 4) (Fin 4) S}
    (hM : Mᵀ = -M) (h2 : ∀ x : S, x + x = 0 → x = 0) :
    M = !![0, M 0 1, M 0 2, M 0 3;
      -M 0 1, 0, M 1 2, M 1 3;
      -M 0 2, -M 1 2, 0, M 2 3;
      -M 0 3, -M 1 3, -M 2 3, 0] := by
  have h (i j : Fin 4) : M j i = -M i j := by simpa using congrFun (congrFun hM i) j
  have hd := diag_eq_zero_of_transpose_eq_neg hM h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hd, h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

/-- Complete strict-upper entries to a matrix with zero diagonal and opposite lower entries. -/
def ofStrictUpper [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) : Matrix n n S :=
  fun i j => if h : i < j then b ⟨(i, j), h⟩
    else if h : j < i then -b ⟨(j, i), h⟩ else 0

/-- The entries of a strict-upper completion. -/
theorem ofStrictUpper_apply [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) (i j : n) :
    ofStrictUpper b i j = if h : i < j then b ⟨(i, j), h⟩
      else if h : j < i then -b ⟨(j, i), h⟩ else 0 := by
  rfl

/-- Completing zero coefficients gives the zero matrix. -/
@[simp]
theorem ofStrictUpper_zero [LinearOrder n] [AddGroup S] :
    ofStrictUpper (0 : {p : n × n // p.1 < p.2} → S) = 0 := by
  ext i j
  simp [ofStrictUpper_apply]

/-- Strict-upper completion commutes with negation. -/
@[simp]
theorem ofStrictUpper_neg [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) : ofStrictUpper (-b) = -ofStrictUpper b := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [ofStrictUpper_apply, h]
  · simp [ofStrictUpper_apply]
  · simp [ofStrictUpper_apply, h, h.not_gt]

/-- Strict-upper completion is additive for commutative coefficients. -/
@[simp]
theorem ofStrictUpper_add [LinearOrder n] [AddCommGroup S]
    (b c : {p : n × n // p.1 < p.2} → S) :
    ofStrictUpper (b + c) = ofStrictUpper b + ofStrictUpper c := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [ofStrictUpper_apply, h]
  · simp [ofStrictUpper_apply]
  · simp [ofStrictUpper_apply, h, h.not_gt, add_comm]

/-- Strict-upper completion negates under transposition. -/
@[simp]
theorem transpose_ofStrictUpper [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) : (ofStrictUpper b).transpose = -ofStrictUpper b := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [ofStrictUpper, h, h.not_gt]
  · simp [ofStrictUpper]
  · simp [ofStrictUpper, h, h.not_gt]

/-- The diagonal of a strict-upper completion is zero. -/
@[simp]
theorem ofStrictUpper_apply_diag [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) (i : n) : ofStrictUpper b i i = 0 := by
  simp [ofStrictUpper]

/-- Completing a strict-upper coefficient function preserves its specified entries. -/
@[simp]
theorem ofStrictUpper_apply_of_lt [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) (p : {p : n × n // p.1 < p.2}) :
    ofStrictUpper b p.val.1 p.val.2 = b p := by
  simp [ofStrictUpper, p.property]

/-- Lower entries of a strict-upper completion negate their corresponding upper coefficients. -/
@[simp]
theorem ofStrictUpper_apply_of_gt [LinearOrder n] [AddGroup S]
    (b : {p : n × n // p.1 < p.2} → S) (p : {p : n × n // p.1 < p.2}) :
    ofStrictUpper b p.val.2 p.val.1 = -b p := by
  simpa only [transpose_apply, neg_apply, ofStrictUpper_apply_of_lt] using
    congrFun (congrFun (transpose_ofStrictUpper b) p.val.1) p.val.2

/-- A skew matrix is recovered from its strict-upper entries when doubling has trivial kernel. -/
theorem ofStrictUpper_eq_of_transpose_eq_neg [LinearOrder n] [AddGroup S]
    (h2 : ∀ x : S, x + x = 0 → x = 0) (M : Matrix n n S) (hM : M.transpose = -M) :
    ofStrictUpper (fun p => M p.val.1 p.val.2) = M := by
  apply ext_of_lt_of_transpose_eq_neg
    (transpose_ofStrictUpper _) hM (ofStrictUpper_apply_diag _)
    (diag_eq_zero_of_transpose_eq_neg hM h2)
  intro i j hij
  exact ofStrictUpper_apply_of_lt _ ⟨(i, j), hij⟩

/-- The additive subgroup of matrices equal to the negative of their transpose. -/
def skewAddSubgroup (n S : Type*) [AddCommGroup S] : AddSubgroup (Matrix n n S) :=
  AddMonoidHom.eqLocus (transposeAddEquiv n n S).toAddMonoidHom (-AddMonoidHom.id _)

@[simp]
theorem mem_skewAddSubgroup [AddCommGroup S] (M : Matrix n n S) :
    M ∈ skewAddSubgroup n S ↔ M.transpose = -M := Iff.rfl

/-- Strict-upper entries give additive coordinates on skew matrices with no nonzero
entries annihilated by doubling. No finiteness or scalar multiplication is required. -/
def skewStrictUpperAddEquiv [LinearOrder n] [AddCommGroup S]
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    skewAddSubgroup n S ≃+ ({p : n × n // p.1 < p.2} → S) where
  toFun M p := M.val p.val.1 p.val.2
  invFun b := ⟨ofStrictUpper b, transpose_ofStrictUpper b⟩
  left_inv M := Subtype.ext (ofStrictUpper_eq_of_transpose_eq_neg h2 M.val M.property)
  right_inv b := funext (ofStrictUpper_apply_of_lt b)
  map_add' _ _ := rfl

/-- The forward additive coordinates are the strict-upper matrix entries. -/
@[simp]
theorem skewStrictUpperAddEquiv_apply [LinearOrder n] [AddCommGroup S]
    (h2 : ∀ x : S, x + x = 0 → x = 0) (M : skewAddSubgroup n S)
    (p : {p : n × n // p.1 < p.2}) :
    skewStrictUpperAddEquiv h2 M p = M.val p.val.1 p.val.2 := by
  rfl

/-- The inverse additive coordinates are strict-upper completion. -/
@[simp]
theorem coe_skewStrictUpperAddEquiv_symm [LinearOrder n] [AddCommGroup S]
    (h2 : ∀ x : S, x + x = 0 → x = 0) (b : {p : n × n // p.1 < p.2} → S) :
    ((skewStrictUpperAddEquiv h2).symm b : Matrix n n S) = ofStrictUpper b := by
  rfl

/-- **Counting matrices equal to the negative of their transpose with entries in a subgroup.**
When zero is the only element that doubles to zero, such a matrix is determined by its entries
above the diagonal, and these are arbitrary elements of the subgroup; for an index type of
cardinality `k` there are `k.choose 2` of them. As an identity of `Nat.card`s this holds for
every subgroup; when the subgroup is finite it counts the matrices. -/
theorem natCard_transpose_eq_neg [Fintype n] [AddCommGroup S] (I : AddSubgroup S)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    Nat.card {M : Matrix n n S // (∀ i j, M i j ∈ I) ∧ Mᵀ = -M} =
      Nat.card I ^ (Fintype.card n).choose 2 := by
  classical
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have hpairs : Nat.card {q : n × n // q.1 < q.2} = (Fintype.card n).choose 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt]
  have h2I : ∀ x : I, x + x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext
    exact h2 x (congrArg Subtype.val hx)
  let e : {M : Matrix n n S // (∀ i j, M i j ∈ I) ∧ Mᵀ = -M} ≃
      skewAddSubgroup n I :=
    { toFun := fun M => ⟨fun i j => ⟨M.val i j, M.property.1 i j⟩, by
        ext i j
        exact congrFun (congrFun M.property.2 i) j⟩
      invFun := fun M => ⟨M.val.map I.subtype, fun i j => (M.val i j).property,
        transpose_map_of_transpose_eq_neg I.subtype M.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← hpairs, ← Nat.card_fun]
  exact Nat.card_congr (e.trans (skewStrictUpperAddEquiv h2I).toEquiv)

end Matrix
