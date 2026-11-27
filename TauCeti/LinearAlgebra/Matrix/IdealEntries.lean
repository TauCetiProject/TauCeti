/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Matrix entries lying in an ideal

A two-sided ideal containing every entry of a matrix contains every entry of any two-sided
product formed from it, and a submodule (in particular an ideal) contains every entry of any
linear combination of matrices whose entries it contains: each such entry is a combination of
entries of the original matrices.

Nothing here needs invertibility or a square shape outside the statements about powers and
about `I • M_n(R)` — only that the products are conformable — so the other statements are
rectangular. Everything except the quotient comparison `Matrix.map_mk_eq_map_mk_iff`, which needs
a `CommRing`, and the description of `I • M_n(R)`, which needs a `CommSemiring`, holds over any
`Semiring`; the two-sided product statement asks the ideal to be two-sided
(`Ideal.IsTwoSided`), which is automatic over a commutative semiring. These are the membership
computations a defining-ideal closure proof performs when it propagates a relation through a
matrix identity.

## Main results

* `Matrix.mul_mul_apply_mem`: every entry of `P * A * Q` lies in a two-sided ideal containing
  every entry of `A`.
* `Matrix.mul_apply_mem_left`, `Matrix.mul_apply_mem_right`: the same for one-sided products
  `P * A` (for a left ideal) and `A * Q`.
* `Matrix.mul_apply_mem_mul`: every entry of `A * B` lies in `I * J` when the entries of `A` lie
  in `I` and those of `B` lie in `J`.
* `Matrix.sum_smul_apply_mem`: every entry of `∑ a, c a • F a` lies in a submodule containing
  every entry of every `F a`.
* `Matrix.mul_eq_zero_of_mul_eq_bot`: the product of a matrix with entries in `I` and a matrix
  with entries in `J` vanishes when `I * J = ⊥`.
* `Matrix.forall_mem_ker_iff_map_eq_zero`: the entries of a matrix lie in the kernel of a ring
  homomorphism exactly when its image under that homomorphism is zero.
* `Matrix.mem_ideal_smul_top_iff`: a square matrix lies in `I • M_n(R)` exactly when its entries
  lie in the ideal `I`.
* `Matrix.exists_map_eq_and_apply_eq_zero`: along a surjection, a matrix lifts to one vanishing
  at the same prescribed entries.
* `RingHom.natCard_ker_mapMatrix`: so the kernel of `f` applied entrywise to `n × n` matrices
  has `|ker f| ^ (n * n)` elements.
* `Matrix.map_mk_eq_map_mk_iff`: two matrices agree modulo `r` exactly when they differ by `r`
  times a matrix.
* `Matrix.pow_apply_mem_pow`, `Matrix.isNilpotent_of_forall_apply_mem`: the `k`-th power of a
  square matrix with entries in `I` has entries in `I ^ k`, so a square matrix with entries in a
  nilpotent ideal is nilpotent.
-/

public section

namespace Matrix

variable {l m n o ι S : Type*}

/-- **A two-sided ideal containing the entries of a matrix contains the entries of any two-sided
product formed from it.** Each entry of `P * A * Q` is an `S`-combination of entries of `A`. -/
theorem mul_mul_apply_mem [Semiring S] [Fintype m] [Fintype n] {A : Matrix m n S} {I : Ideal S}
    [I.IsTwoSided] (hA : ∀ i j, A i j ∈ I) (P : Matrix l m S) (Q : Matrix n o S) (i : l) (j : o) :
    (P * A * Q) i j ∈ I := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun t _ =>
    I.mul_mem_right _ (I.mul_mem_left _ (hA t k))

/-- **A left ideal containing the entries of a matrix contains the entries of every left multiple
of it.** -/
theorem mul_apply_mem_left [Semiring S] [Fintype m] {A : Matrix m n S} {I : Ideal S}
    (hA : ∀ i j, A i j ∈ I) (P : Matrix l m S) (i : l) (j : n) : (P * A) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => I.mul_mem_left _ (hA k j)

/-- **A two-sided ideal containing the entries of a matrix contains the entries of every right
multiple of it.** -/
theorem mul_apply_mem_right [Semiring S] [Fintype n] {A : Matrix m n S} {I : Ideal S}
    [I.IsTwoSided] (hA : ∀ i j, A i j ∈ I) (Q : Matrix n o S) (i : m) (j : o) :
    (A * Q) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => I.mul_mem_right _ (hA i k)

/-- **The entries of a product of matrices with entries in two ideals lie in the product
ideal.** -/
theorem mul_apply_mem_mul [Semiring S] [Fintype m] {I J : Ideal S} {A : Matrix l m S}
    {B : Matrix m o S} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ J) (i : l) (j : o) :
    (A * B) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)

/-- **A submodule containing the entries of a family of matrices contains the entries of every
linear combination of them.** -/
theorem sum_smul_apply_mem {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι]
    {F : ι → Matrix m n M} {p : Submodule R M} (hF : ∀ a i j, F a i j ∈ p) (c : ι → R) (i : m)
    (j : n) : (∑ a, c a • F a) i j ∈ p := by
  rw [Matrix.sum_apply]
  exact p.sum_mem fun a _ => p.smul_mem (c a) (hF a i j)

/-- **The product of two matrices with entries in ideals whose product is zero vanishes**: each
entry of `A * B` is a sum of elements of `I * J`. -/
theorem mul_eq_zero_of_mul_eq_bot [Semiring S] [Fintype m] {I J : Ideal S} (hIJ : I * J = ⊥)
    {A : Matrix l m S} {B : Matrix m o S} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ J) :
    A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Ideal.mem_bot, ← hIJ]
  exact Ideal.mul_mem_mul (hA i k) (hB k j)

/-- The entries of a matrix lie in the kernel of `f` exactly when its image under `f` is zero. -/
theorem forall_mem_ker_iff_map_eq_zero {R : Type*} [Semiring R] [Semiring S] {F : Type*}
    [FunLike F R S] [RingHomClass F R S] {f : F} {D : Matrix m n R} :
    (∀ i j, D i j ∈ RingHom.ker f) ↔ D.map f = 0 := by
  simp only [RingHom.mem_ker, ← Matrix.ext_iff, map_apply, Matrix.zero_apply]

/-- A matrix lies in `I • M_n(R)` exactly when all its entries lie in the ideal `I`. -/
theorem mem_ideal_smul_top_iff {R : Type*} [CommSemiring R] [Finite n] (I : Ideal R)
    {x : Matrix n n R} :
    x ∈ I • (⊤ : Submodule R (Matrix n n R)) ↔ ∀ i j, x i j ∈ I := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun r hr m _ i j ↦ ?_) fun y z hy hz i j ↦ ?_
    · simpa using I.mul_mem_right (m i j) hr
    · simpa using I.add_mem (hy i j) (hz i j)
  -- Otherwise `x` is the sum of its entries, all in `I`, times the matrix units.
  have := Fintype.ofFinite n
  classical
  rw [matrix_eq_sum_single x]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ ?_
  rw [show single i j (x i j) = x i j • single i j 1 by simp [smul_single]]
  exact Submodule.smul_mem_smul (hx i j) Submodule.mem_top

/-- **Lifting a matrix along a surjection with prescribed zero entries.** If `f` is surjective,
a matrix over `S` whose entries vanish at the positions satisfying `p` is the image of a matrix
over `R` whose entries vanish at the same positions. -/
theorem exists_map_eq_and_apply_eq_zero {R : Type*} [Zero R] [Zero S] {F : Type*}
    [FunLike F R S] [ZeroHomClass F R S] {f : F} (hf : Function.Surjective f) (Y : Matrix m n S)
    (p : m → n → Prop) (hY : ∀ i j, p i j → Y i j = 0) :
    ∃ X : Matrix m n R, X.map f = Y ∧ ∀ i j, p i j → X i j = 0 := by
  classical
  choose x hx using fun i j ↦ hf (Y i j)
  refine ⟨of fun i j ↦ if p i j then 0 else x i j, ?_, fun i j h ↦ by simp [h]⟩
  ext i j
  simp only [map_apply, of_apply]
  split_ifs with h
  · rw [map_zero, hY i j h]
  · exact hx i j

/-- **The kernel of an entrywise ring homomorphism** consists of the matrices with entries in
`ker f`, so it has `|ker f| ^ (n * n)` elements. -/
theorem _root_.RingHom.natCard_ker_mapMatrix {R : Type*} [Semiring R] [Semiring S] [Fintype n]
    [DecidableEq n] (f : R →+* S) :
    Nat.card (RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S)) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n * Fintype.card n) := by
  let e : RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) ≃
      Matrix n n (RingHom.ker f) :=
    { toFun M := of fun i j ↦
        ⟨M.val i j, forall_mem_ker_iff_map_eq_zero.mpr (RingHom.mem_ker.mp M.property) i j⟩
      invFun M := ⟨of fun i j ↦ (M i j).val,
        RingHom.mem_ker.mpr (forall_mem_ker_iff_map_eq_zero.mp fun i j ↦ (M i j).property)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, card_matrix, Nat.card_eq_fintype_card (α := n)]

/-- Two matrices have the same image modulo `r` exactly when they differ by `r` times a
matrix. -/
theorem map_mk_eq_map_mk_iff [CommRing S] {r : S} {A A' : Matrix m n S} :
    A'.map (Ideal.Quotient.mk (Ideal.span {r})) = A.map (Ideal.Quotient.mk (Ideal.span {r})) ↔
      ∃ C : Matrix m n S, A' = A + r • C := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have (i : m) (j : n) : ∃ c, A' i j = A i j + r * c := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congr_fun₂ h i j))
      exact ⟨c, by rw [← hc, add_sub_cancel]⟩
    choose c hc using this
    exact ⟨of c, ext fun i j ↦ by simp [hc]⟩
  · rintro ⟨C, rfl⟩
    ext i j
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self r)]

/-- **The powers of a matrix with entries in an ideal.** If every entry of a square matrix `M`
lies in `I`, then every entry of `M ^ k` lies in `I ^ k`. -/
theorem pow_apply_mem_pow [Semiring S] [Fintype n] [DecidableEq n] {I : Ideal S}
    {M : Matrix n n S} (hM : ∀ i j, M i j ∈ I) (k : ℕ) (i j : n) : (M ^ k) i j ∈ I ^ k := by
  induction k generalizing j with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Submodule.pow_succ]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (ih l) (hM l j)

/-- **A matrix with entries in a nilpotent ideal is nilpotent.** -/
theorem isNilpotent_of_forall_apply_mem [Semiring S] [Fintype n] [DecidableEq n] {I : Ideal S}
    (hI : IsNilpotent I) {M : Matrix n n S} (hM : ∀ i j, M i j ∈ I) : IsNilpotent M := by
  obtain ⟨k, hk⟩ := hI
  exact ⟨k, ext fun i j => by simpa [hk] using pow_apply_mem_pow hM k i j⟩

end Matrix
