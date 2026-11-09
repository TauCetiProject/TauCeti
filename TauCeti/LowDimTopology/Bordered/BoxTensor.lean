/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import TauCeti.LowDimTopology.Bordered.TypeD
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Type `A` modules and their box tensor product with type `D` structures

In bordered Heegaard Floer homology a three-manifold with parametrized boundary has a type `A`
module `CFA`, an `A∞` right module over the algebra of the boundary, and a type `D` structure
`CFD` (`TauCeti.TypeDStructure`). The Floer complex of a closed manifold glued from two pieces is
the box tensor product `CFA ⊠ CFD`, with the differential
`∂ (y ⊗ x) = ∑_k (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`. This file constructs that differential over a ring of
characteristic two, for the ungraded type `D` structures of `TauCeti.LowDimTopology.Bordered.TypeD`,
and proves that it squares to zero when either factor is bounded.

* **Type `A` modules.** A type `A` module over the differential algebra `(A, d)`
  (`TauCeti.TypeAModule`) has operations `m_{n+1} : M ⊗ A^{⊗ n} → M`, stored as
  `op n : M →ₗ[R] MultilinearMap R (Fin n → A) M`, satisfying the `A∞` relations
  `TauCeti.TypeAModule.stasheffSum`. The operations read the first `n` entries of a sequence
  `a : ℕ → A`, so that splitting the inputs of the `A∞` relations needs no reindexing between
  propositionally equal arities. There is no grading: the bordered algebras carry gradings by
  noncommutative groups, not by `ℤ`, so the `ℤ`-graded `TauCeti.AInfinityRightModule` does not
  apply, and over a ring of characteristic two the relations need no signs. A differential right
  module is a type `A` module with `m₁ = dM`, `m₂` the action and no higher operations
  (`TauCeti.TypeAModule.ofDGRightModule`).
* **Iterates of `δ¹`.** The coefficient of `z` in `δᵏ x` is the sum over the paths
  `x = r 0, …, r k = z` of `coeff (r 0) (r 1) ⊗ ⋯ ⊗ coeff (r (k-1)) (r k)` in the `k`-th tensor
  power of `A` over `R` (`TauCeti.TypeDStructure.iteratedCoeff`). A type `D` structure is bounded
  when `δᵏ = 0` for large `k`, for instance when its coefficients strictly decrease a height
  function (`TauCeti.TypeDStructure.iteratedCoeff_eq_zero_of_lt`). The tensor power over the ring
  of idempotents is a quotient of the one over `R`, so this boundedness implies the vanishing of
  the iterates over the idempotents.
* **The box tensor product.** On row vectors `φ : X → M`, standing for `∑ x, φ x ⊗ x`, the
  differential with the first `K` iterates is `TauCeti.TypeAModule.boxDifferential`. Row vectors
  model the tensor product over `R`; the summand over the idempotents, which
  `TauCeti.TypeDStructure.boxTensor` cuts out for differential modules, needs an action of the
  idempotents on `M` and is not treated here. When the type
  `A` module is bounded (`m_{n+1} = 0` for `n ≥ K`) or the type `D` structure is bounded
  (`δⁿ = 0` for `n ≥ K`), every term with at least `K` algebra inputs vanishes, the differential
  does not depend on the truncation beyond `K`, and it squares to zero. Without boundedness the sum
  over `k` is infinite and is not a differential; boundedness is a hypothesis of the tensor
  product, not a consequence of the finiteness of `X`. For a differential right module the box
  tensor differential is `TauCeti.TypeDStructure.boxDifferential`.

The proof of `∂ ∘ ∂ = 0` concatenates paths: the terms of `∂ ∘ ∂` with `n` algebra inputs in
total are the first sum of the `A∞` relation of arity `n` along the paths of length `n`, so they
are the derivative and multiplication terms of that relation. Expanding `d` of a coefficient by
the structure equation `d δ = δ * δ` of the type `D` structure inserts an intermediate
generator, which turns the derivative terms along paths of length `n` into the multiplication
terms along paths of length `n + 1`. The sum over `n` telescopes, and the remaining terms vanish
by boundedness.

## Main definitions

* `TauCeti.TypeAModule`: a type `A` module, given by its operations and the `A∞` relations.
* `TauCeti.TypeDStructure.iteratedCoeff`: the iterates `δᵏ` of a type `D` structure.
* `TauCeti.TypeAModule.boxDifferential`: the box tensor differential, truncated to `K` iterates.
* `TauCeti.TypeAModule.ofDGRightModule`: the type `A` module of a differential right module.

## Main results

* `TauCeti.TypeAModule.boxDifferential_boxDifferential_of_op_eq_zero` and
  `TauCeti.TypeAModule.boxDifferential_boxDifferential_of_iteratedCoeff_eq_zero`: `∂ ∘ ∂ = 0` on
  `M ⊠ N` when the type `A` module or the type `D` structure is bounded.
* `TauCeti.TypeAModule.boxDifferential_eq_of_op_eq_zero` and
  `TauCeti.TypeAModule.boxDifferential_eq_of_iteratedCoeff_eq_zero`: under either boundedness the
  differential does not depend on the truncation.
* `TauCeti.TypeAModule.boxDifferential_ofDGRightModule`: for a differential right module this is
  the box tensor differential `∂ φ = dM φ + φ ⬝ δ`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2: `A∞` modules, type `D` structures and their iterates, boundedness, and the box
  tensor product (equation (2.29)).
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (d : A →ₗ[R] A)
  (M : Type*) [AddCommGroup M] [Module R M]

namespace TypeAModule

variable {M}

/-- Multiply the entries `l` and `l + 1` of a sequence, shifting the later entries down by one:
the inputs of the multiplication terms of the `A∞` relations. -/
def mulAt (l : ℕ) (a : ℕ → A) (t : ℕ) : A :=
  if t < l then a t else if t = l then a l * a (l + 1) else a (t + 1)

theorem mulAt_apply (l : ℕ) (a : ℕ → A) (t : ℕ) :
    mulAt l a t = if t < l then a t else if t = l then a l * a (l + 1) else a (t + 1) :=
  (rfl)

/-- The left side of the **`A∞` relation** of arity `n` for operations `op k`, where
`op k x a = m_{k+1}(x, a 0, …, a (k - 1))` reads the first `k` entries of a sequence `a : ℕ → A`:
```
∑_{j ≤ n} m(m(x, a₀, …, a_{j-1}), a_j, …, a_{n-1}) + ∑_{l < n} m(x, …, d a_l, …)
  + ∑_{l < n - 1} m(x, …, a_l a_{l+1}, …).
```
Over a ring of characteristic two these are all the terms of the `A∞` relation of a right module
over a differential algebra. -/
def stasheffSum (op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M) (n : ℕ)
    (x : M) (a : ℕ → A) : M :=
  (∑ j ∈ range (n + 1), op (n - j) (op j x fun t => a t) fun t => a (j + t)) +
    (∑ l ∈ range n, op n x fun t => Function.update a l (d (a l)) t) +
    ∑ l ∈ range (n - 1), op (n - 1) x fun t => mulAt l a t

theorem stasheffSum_def (op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M)
    (n : ℕ) (x : M) (a : ℕ → A) :
    stasheffSum d op n x a =
      (∑ j ∈ range (n + 1), op (n - j) (op j x fun t => a t) fun t => a (j + t)) +
        (∑ l ∈ range n, op n x fun t => Function.update a l (d (a l)) t) +
        ∑ l ∈ range (n - 1), op (n - 1) x fun t => mulAt l a t :=
  (rfl)

end TypeAModule

/-- A **type `A` module** over the differential algebra `(A, d)`: an ungraded right `A∞` module,
given by operations `op n x a = m_{n+1}(x, a 0, …, a (n - 1))`, linear in the module element and
multilinear in the `n` algebra elements, satisfying the `A∞` relations
`TauCeti.TypeAModule.stasheffSum`. -/
@[ext]
structure TypeAModule where
  /-- `op n x a = m_{n+1}(x, a 0, …, a (n - 1))`. -/
  op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M
  /-- The `A∞` relations. -/
  stasheffSum_eq_zero (n : ℕ) (x : M) (a : ℕ → A) : TypeAModule.stasheffSum d op n x a = 0

section Clamp

variable {X : Type*}

private theorem comp_clamp_apply {k t : ℕ} (r : Fin (k + 1) → X) (h : t ≤ k) :
    (r ∘ (Fin.clamp · k)) t = r ⟨t, by omega⟩ := by
  simp only [Function.comp_apply]
  congr 1
  ext
  simp [h]

private theorem comp_clamp_apply_of_le {k t : ℕ} (r : Fin (k + 1) → X) (h : k ≤ t) :
    (r ∘ (Fin.clamp · k)) t = r (Fin.last k) := by
  simp only [Function.comp_apply]
  congr 1
  ext
  simp [h]

end Clamp

namespace TypeDStructure

variable {d} {S : Type*} {ι : S → A} {X : Type*} [Fintype X]

/-- The coefficients of a type `D` structure along a sequence of generators `w`:
`pathCoeff w t = coeff (w t) (w (t + 1))`. -/
def pathCoeff (N : TypeDStructure d ι X) (w : ℕ → X) (t : ℕ) : A :=
  N.coeff (w t) (w (t + 1))

@[simp]
theorem pathCoeff_apply (N : TypeDStructure d ι X) (w : ℕ → X) (t : ℕ) :
    N.pathCoeff w t = N.coeff (w t) (w (t + 1)) :=
  (rfl)

/-- The **iterates** `δᵏ` of the structure map of a type `D` structure: the coefficient of the
generator `z` in `δᵏ x ∈ A^{⊗ k} ⊗ N`, the sum over the paths `x = r 0, r 1, …, r k = z` of
`coeff (r 0) (r 1) ⊗ ⋯ ⊗ coeff (r (k - 1)) (r k)`. -/
noncomputable def iteratedCoeff [DecidableEq X] (N : TypeDStructure d ι X) (k : ℕ) (x z : X) :
    PiTensorProduct R fun _ : Fin k => A :=
  ∑ r : Fin (k + 1) → X with r 0 = x ∧ r (Fin.last k) = z,
    PiTensorProduct.tprod R fun t : Fin k => N.pathCoeff (r ∘ (Fin.clamp · k)) t

theorem iteratedCoeff_def [DecidableEq X] (N : TypeDStructure d ι X) (k : ℕ) (x z : X) :
    N.iteratedCoeff k x z = ∑ r : Fin (k + 1) → X with r 0 = x ∧ r (Fin.last k) = z,
      PiTensorProduct.tprod R fun t : Fin k => N.pathCoeff (r ∘ (Fin.clamp · k)) t :=
  (rfl)

end TypeDStructure

namespace TypeAModule

variable {d M} (𝓜 : TypeAModule d M) {S : Type*} {ι : S → A} {X : Type*} [Fintype X]
  [DecidableEq X]

/-- The **box tensor differential** of a type `A` module `𝓜` with a type `D` structure `N`,
truncated to the first `K` iterates of the structure map. On row vectors `φ : X → M`, standing
for `∑ x, φ x ⊗ x`, it sums over the paths `r 0, …, r k = z` with `k < K`:
`∂ φ z = ∑ m_{k+1}(φ (r 0), coeff (r 0) (r 1), …, coeff (r (k-1)) (r k))`, that is
`∂ (y ⊗ x) = ∑_{k < K} (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`. When `𝓜` or `N` is bounded, it does not
depend on `K` once `K` is large (`boxDifferential_eq_of_op_eq_zero`,
`boxDifferential_eq_of_iteratedCoeff_eq_zero`). -/
noncomputable def boxDifferential (N : TypeDStructure d ι X) (K : ℕ) :
    (X → M) →ₗ[R] (X → M) where
  toFun φ z := ∑ k ∈ range K, ∑ r : Fin (k + 1) → X with r (Fin.last k) = z,
    𝓜.op k (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · k)) t
  map_add' φ ψ := by
    funext z
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    funext z
    simp [Finset.smul_sum]

theorem boxDifferential_apply (N : TypeDStructure d ι X) (K : ℕ) (φ : X → M) (z : X) :
    𝓜.boxDifferential N K φ z = ∑ k ∈ range K, ∑ r : Fin (k + 1) → X with r (Fin.last k) = z,
      𝓜.op k (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · k)) t :=
  (rfl)

/-! ### Paths of generators -/

section Paths

variable {N : TypeDStructure d ι X}

/-- The terms of the box tensor differential with `k` algebra inputs. -/
private noncomputable def boxTerm (N : TypeDStructure d ι X) (k : ℕ) (φ : X → M) (z : X) : M :=
  ∑ r : Fin (k + 1) → X with r (Fin.last k) = z,
    𝓜.op k (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · k)) t

private theorem boxDifferential_apply_eq_sum_boxTerm (K : ℕ) (φ : X → M) (z : X) :
    𝓜.boxDifferential N K φ z = ∑ k ∈ range K, 𝓜.boxTerm N k φ z :=
  (rfl)

/-- The concatenation of a path `p` of length `j` with a path `q` of length `i`. -/
private def concatPath {i j : ℕ} (q : Fin (i + 1) → X) (p : Fin (j + 1) → X) :
    Fin (j + i + 1) → X :=
  fun t => if h : (t : ℕ) ≤ j then p ⟨t, by omega⟩ else q ⟨t - j, by omega⟩

omit [Fintype X] [DecidableEq X] in
private theorem concatPath_comp_clamp_of_le {i j : ℕ} (q : Fin (i + 1) → X)
    (p : Fin (j + 1) → X) {t : ℕ} (ht : t ≤ j) :
    (concatPath q p ∘ (Fin.clamp · (j + i))) t = (p ∘ (Fin.clamp · j)) t := by
  rw [comp_clamp_apply (k := j + i) (t := t) _ (by omega), comp_clamp_apply _ ht]
  simp [concatPath, ht]

omit [Fintype X] [DecidableEq X] in
private theorem concatPath_comp_clamp_add {i j : ℕ} (q : Fin (i + 1) → X)
    (p : Fin (j + 1) → X) (hp : p (Fin.last j) = q 0) (s : ℕ) :
    (concatPath q p ∘ (Fin.clamp · (j + i))) (j + s) = (q ∘ (Fin.clamp · i)) s := by
  have key : ∀ s (hs : s ≤ i), concatPath q p ⟨j + s, by omega⟩ = q ⟨s, by omega⟩ := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp only [concatPath, add_zero, le_refl, dite_true]
      exact hp
    · simp only [concatPath, show ¬ j + s ≤ j by omega, dite_false]
      congr 1
      ext
      simp
  rcases le_or_gt s i with hs | hs
  · rw [comp_clamp_apply (k := j + i) (t := j + s) _ (by omega), comp_clamp_apply _ hs, key s hs]
  · rw [comp_clamp_apply_of_le (k := j + i) (t := j + s) _ (by omega),
      comp_clamp_apply_of_le (k := i) (t := s) _ hs.le]
    exact key i le_rfl

/-- Concatenating paths: the terms of `∂ ∘ ∂` with `j` and then `i` algebra inputs are a sum over
paths of length `j + i`. -/
private theorem boxTerm_boxTerm (φ : X → M) (i j : ℕ) (z : X) :
    𝓜.boxTerm N i (𝓜.boxTerm N j φ) z =
      ∑ r : Fin (j + i + 1) → X with r (Fin.last (j + i)) = z,
        𝓜.op i (𝓜.op j (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · (j + i))) t)
          fun s => N.pathCoeff (r ∘ (Fin.clamp · (j + i))) (j + s) := by
  simp only [boxTerm, map_sum, sum_apply]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun qp => concatPath qp.1 qp.2)
    (fun r => ⟨fun s : Fin (i + 1) => r ⟨j + s, by omega⟩, fun t : Fin (j + 1) => r ⟨t, by omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨hq, hp⟩ := h
    have h := concatPath_comp_clamp_add q p hp i
    rwa [comp_clamp_apply_of_le _ le_rfl, comp_clamp_apply_of_le _ le_rfl, hq] at h
  · intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_sigma] at hr ⊢
    exact ⟨hr, rfl⟩
  · rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h
    obtain ⟨-, hp⟩ := h
    refine Sigma.ext (funext fun s => ?_) (heq_of_eq (funext fun t => ?_))
    · have h := concatPath_comp_clamp_add q p hp s
      rwa [comp_clamp_apply (k := j + i) (t := j + s) _ (by omega),
        comp_clamp_apply (k := i) (t := s) _ (by omega)] at h
    · simp only [concatPath]
      rw [dite_eq_left (Nat.lt_succ_iff.mp t.isLt)]
  · intro r _
    funext t
    simp only [concatPath]
    split_ifs with ht
    · simp
    · congr 1
      ext
      simp only
      omega
  · rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h
    obtain ⟨-, hp⟩ := h
    have h0 : concatPath q p 0 = p 0 := by simp [concatPath]
    simp only [TypeDStructure.pathCoeff]
    rw [h0]
    refine congrArg₂ (fun u v => 𝓜.op i u v) (congrArg _ (funext fun t => ?_))
      (funext fun s => ?_)
    · rw [concatPath_comp_clamp_of_le q p (t := t) (by omega),
        concatPath_comp_clamp_of_le q p (t := t + 1) (by omega)]
    · rw [concatPath_comp_clamp_add q p hp, show j + (s : ℕ) + 1 = j + ((s : ℕ) + 1) by omega,
        concatPath_comp_clamp_add q p hp]

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_apply {n l : ℕ} (hl : l < n) (w : X) (r : Fin (n + 1) → X)
    (t : Fin (n + 2)) :
    Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r t =
      if h : (t : ℕ) < l + 1 then r ⟨t, by omega⟩
      else if (t : ℕ) = l + 1 then w else r ⟨t - 1, by omega⟩ := by
  rcases lt_trichotomy (t : ℕ) (l + 1) with ht | ht | ht
  · rw [Fin.insertNth_apply_below (Fin.lt_def.2 ht), dite_eq_left ht, eq_rec_constant]
    congr 1
  · rw [show t = ⟨l + 1, by omega⟩ from Fin.ext ht]
    simp
  · rw [Fin.insertNth_apply_above (Fin.lt_def.2 ht), dite_eq_right (by omega),
      ite_eq_right (by omega), eq_rec_constant]
    congr 1

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_of_le {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) {t : ℕ} (ht : t ≤ l) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) t =
      (r ∘ (Fin.clamp · n)) t := by
  rw [comp_clamp_apply (k := n + 1) (t := t) _ (by omega),
    comp_clamp_apply (k := n) (t := t) _ (by omega), insertNth_apply hl,
    dite_eq_left (by simp only; omega)]

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_self {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) (l + 1) =
      w := by
  rw [comp_clamp_apply (k := n + 1) (t := l + 1) _ (by omega), insertNth_apply hl]
  simp

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_last {n l : ℕ} (hl : l < n) (w : X) (r : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r (Fin.last (n + 1)) = r (Fin.last n) := by
  rw [insertNth_apply hl]
  simp only [Fin.val_last, show ¬ n + 1 < l + 1 by omega, show n + 1 ≠ l + 1 by omega, dite_false,
    ite_false]
  congr 1

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_zero {n l : ℕ} (hl : l < n) (w : X) (r : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r 0 = r 0 := by
  simp [insertNth_apply hl]

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_succ {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) {t : ℕ} (ht : l + 1 ≤ t) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) (t + 1) =
      (r ∘ (Fin.clamp · n)) t := by
  rcases le_or_gt t n with htn | htn
  · rw [comp_clamp_apply (k := n + 1) (t := t + 1) _ (by omega),
      comp_clamp_apply (k := n) (t := t) _ htn, insertNth_apply hl]
    simp only [show ¬ t + 1 < l + 1 by omega, show t + 1 ≠ l + 1 by omega, dite_false, ite_false,
      Nat.add_sub_cancel]
  · rw [comp_clamp_apply_of_le (k := n + 1) (t := t + 1) _ (by omega),
      comp_clamp_apply_of_le (k := n) (t := t) _ htn.le, insertNth_last hl]

/-- Expanding `d` of one coefficient along a path by the structure equation of `N` inserts an
intermediate generator: the derivative terms of the `A∞` relation along paths of length `n` are
the multiplication terms along paths of length `n + 1`. -/
private theorem sum_op_update_eq [CharP R 2] (φ : X → M) {n l : ℕ} (hl : l < n) (z : X) :
    ∑ r : Fin (n + 1) → X with r (Fin.last n) = z,
      𝓜.op n (φ (r 0)) (fun t => Function.update (N.pathCoeff (r ∘ (Fin.clamp · n))) l
        (d (N.pathCoeff (r ∘ (Fin.clamp · n)) l)) t) =
    ∑ r : Fin (n + 1 + 1) → X with r (Fin.last (n + 1)) = z,
      𝓜.op n (φ (r 0)) (fun t => mulAt l (N.pathCoeff (r ∘ (Fin.clamp · (n + 1)))) t) := by
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (n := n + 1) (fun _ => X) ⟨l + 1, by omega⟩),
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : d (N.pathCoeff (r ∘ (Fin.clamp · n)) l) = ∑ w, N.coeff ((r ∘ (Fin.clamp · n)) l) w *
      N.coeff w ((r ∘ (Fin.clamp · n)) (l + 1)) := by
    have h := congrFun (congrFun (N.map_coeff_eq_coeff_mul_coeff) ((r ∘ (Fin.clamp · n)) l))
      ((r ∘ (Fin.clamp · n)) (l + 1))
    simpa [TypeDStructure.pathCoeff, Matrix.mul_apply] using h
  have hupd (a : ℕ → A) (v : A) : (fun t : Fin n => Function.update a l v t) =
      Function.update (fun t : Fin n => a t) ⟨l, hl⟩ v :=
    Function.update_comp_eq_of_injective a Fin.val_injective (⟨l, hl⟩ : Fin n) v
  rw [hd, hupd, MultilinearMap.map_update_sum]
  simp only [Fin.insertNthEquiv_apply, insertNth_last hl, insertNth_zero hl]
  by_cases hz : r (Fin.last n) = z
  · simp only [hz, ite_true]
    refine Finset.sum_congr rfl fun w _ => congrArg _ (funext fun t => ?_)
    simp only [Function.update_apply, mulAt, TypeDStructure.pathCoeff, Fin.ext_iff]
    rcases lt_trichotomy (t : ℕ) l with ht | ht | ht
    · rw [ite_eq_right ht.ne, ite_eq_left ht, insertNth_comp_clamp_of_le hl w r ht.le,
        insertNth_comp_clamp_of_le hl w r (by omega : (t : ℕ) + 1 ≤ l)]
    · simp only [ht, ite_true, lt_irrefl, ite_false]
      rw [insertNth_comp_clamp_of_le hl w r le_rfl, insertNth_comp_clamp_self hl,
        insertNth_comp_clamp_succ hl w r le_rfl]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        insertNth_comp_clamp_succ hl w r (by omega : l + 1 ≤ (t : ℕ)),
        insertNth_comp_clamp_succ hl w r (by omega : l + 1 ≤ (t : ℕ) + 1)]
  · simp [hz]

/-- The derivative terms of the `A∞` relations along the paths of length `n` ending at `z`. -/
private noncomputable def derivSum (φ : X → M) (z : X) (n : ℕ) : M :=
  ∑ r : Fin (n + 1) → X with r (Fin.last n) = z, ∑ l ∈ range n,
    𝓜.op n (φ (r 0)) (fun t => Function.update (N.pathCoeff (r ∘ (Fin.clamp · n))) l
      (d (N.pathCoeff (r ∘ (Fin.clamp · n)) l)) t)

/-- The multiplication terms of the `A∞` relations along the paths of length `n` ending at `z`. -/
private noncomputable def mulSum (φ : X → M) (z : X) (n : ℕ) : M :=
  ∑ r : Fin (n + 1) → X with r (Fin.last n) = z, ∑ l ∈ range (n - 1),
    𝓜.op (n - 1) (φ (r 0)) (fun t => mulAt l (N.pathCoeff (r ∘ (Fin.clamp · n))) t)

private theorem derivSum_eq_mulSum_succ [CharP R 2] (φ : X → M) (z : X) (n : ℕ) :
    𝓜.derivSum (N := N) φ z n = 𝓜.mulSum (N := N) φ z (n + 1) := by
  rw [derivSum, mulSum, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l hl => 𝓜.sum_op_update_eq φ (mem_range.1 hl) z

omit [DecidableEq X] in
private theorem sum_fin_congr {a b : ℕ} (h : a = b) (F : ∀ a, (Fin (a + 1) → X) → M) :
    ∑ r, F a r = ∑ r, F b r := by
  subst h
  rfl

private theorem boxTerm_sum (i : ℕ) {ι' : Type*} (s : Finset ι') (f : ι' → X → M) (z : X) :
    𝓜.boxTerm N i (fun w => ∑ j ∈ s, f j w) z = ∑ j ∈ s, 𝓜.boxTerm N i (f j) z := by
  simp only [boxTerm, map_sum, sum_apply]
  exact Finset.sum_comm

/-- The terms of `∂ ∘ ∂` with `n` algebra inputs in total add up to the derivative and the
multiplication terms of the `A∞` relations along the paths of length `n`. -/
private theorem sum_boxTerm_boxTerm [CharP R 2] (φ : X → M) (z : X) (n : ℕ) :
    ∑ j ∈ range (n + 1), 𝓜.boxTerm N (n - j) (𝓜.boxTerm N j φ) z =
      𝓜.derivSum (N := N) φ z n + 𝓜.mulSum (N := N) φ z n := by
  have hconcat : ∀ j ∈ range (n + 1), 𝓜.boxTerm N (n - j) (𝓜.boxTerm N j φ) z =
      ∑ r : Fin (n + 1) → X with r (Fin.last n) = z,
        𝓜.op (n - j) (𝓜.op j (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · n)) t)
          fun s => N.pathCoeff (r ∘ (Fin.clamp · n)) (j + s) := by
    intro j hj
    rw [boxTerm_boxTerm]
    simp only [Finset.sum_filter]
    exact sum_fin_congr (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hj)))
      (fun a r => if r (Fin.last a) = z then
        𝓜.op (n - j) (𝓜.op j (φ (r 0)) fun t => N.pathCoeff (r ∘ (Fin.clamp · a)) t)
          fun s => N.pathCoeff (r ∘ (Fin.clamp · a)) (j + s) else 0)
  rw [Finset.sum_congr rfl hconcat, Finset.sum_comm, derivSum, mulSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h := 𝓜.stasheffSum_eq_zero n (φ (r 0)) (N.pathCoeff (r ∘ (Fin.clamp · n)))
  rw [stasheffSum, add_assoc, add_eq_zero_iff_eq_of_charTwo R] at h
  exact h

omit [Fintype X] [DecidableEq X] in
private theorem sum_range_add_succ [CharP R 2] (f : ℕ → M) (L : ℕ) :
    ∑ n ∈ range L, (f (n + 1) + f n) = f L + f 0 := by
  induction L with
  | zero => simp [add_self_eq_zero_of_charTwo R]
  | succ L ih =>
    rw [sum_range_succ, ih]
    calc f L + f 0 + (f (L + 1) + f L) = f (L + 1) + f 0 + (f L + f L) := by abel
      _ = f (L + 1) + f 0 := by rw [add_self_eq_zero_of_charTwo R, add_zero]

/-- The terms of the `A∞` relations with at least `K` algebra inputs, with any linear maps applied
to the coefficients, vanish along the paths of `N`. Both a bounded type `A` module and a bounded
type `D` structure satisfy this. -/
private def PathTermsVanish (𝓜 : TypeAModule d M) (N : TypeDStructure d ι X) (K : ℕ) : Prop :=
  ∀ n, K ≤ n → ∀ (L : Fin n → A →ₗ[R] A) (φ : X → M) (z : X),
    ∑ r : Fin (n + 1) → X with r (Fin.last n) = z,
      (𝓜.op n (φ (r 0))).compLinearMap L (fun t => N.pathCoeff (r ∘ (Fin.clamp · n)) t) = 0

private theorem boxTerm_eq_zero {K : ℕ} (hK : 𝓜.PathTermsVanish N K) {k : ℕ} (hk : K ≤ k)
    (φ : X → M) (z : X) : 𝓜.boxTerm N k φ z = 0 := by
  simpa [boxTerm, MultilinearMap.compLinearMap_id] using hK k hk (fun _ => LinearMap.id) φ z

private theorem boxTerm_boxTerm_eq_zero {K : ℕ} (hK : 𝓜.PathTermsVanish N K) (φ : X → M)
    (z : X) {i j : ℕ} (h : K ≤ i ∨ K ≤ j) : 𝓜.boxTerm N i (𝓜.boxTerm N j φ) z = 0 := by
  rcases h with hi | hj
  · exact 𝓜.boxTerm_eq_zero hK hi _ z
  · have h0 : 𝓜.boxTerm N j φ = 0 := funext fun w => 𝓜.boxTerm_eq_zero hK hj φ w
    rw [h0]
    simp only [boxTerm, Pi.zero_apply, map_zero, zero_apply, sum_const_zero]

/-- `∂ (∂ φ)`, as the sum of the terms with `j` and then `i` algebra inputs, grouped by the total
number `n = i + j < 2 K + 1` of algebra inputs. -/
private theorem boxDifferential_boxDifferential_apply {K : ℕ} (hK : 𝓜.PathTermsVanish N K)
    (φ : X → M) (z : X) :
    𝓜.boxDifferential N K (𝓜.boxDifferential N K φ) z =
      ∑ n ∈ range (2 * K + 1), ∑ j ∈ range (n + 1), 𝓜.boxTerm N (n - j) (𝓜.boxTerm N j φ) z := by
  have h : 𝓜.boxDifferential N K φ = fun w => ∑ j ∈ range K, 𝓜.boxTerm N j φ w :=
    funext fun w => 𝓜.boxDifferential_apply_eq_sum_boxTerm K φ w
  rw [boxDifferential_apply_eq_sum_boxTerm, h,
    Finset.sum_congr rfl fun i _ => 𝓜.boxTerm_sum i (range K) (fun j => 𝓜.boxTerm N j φ) z,
    Finset.sum_comm,
    Finset.sum_range_diag_flip (2 * K + 1) fun j i => 𝓜.boxTerm N i (𝓜.boxTerm N j φ) z]
  calc ∑ j ∈ range K, ∑ i ∈ range K, 𝓜.boxTerm N i (𝓜.boxTerm N j φ) z
      = ∑ j ∈ range K, ∑ i ∈ range (2 * K + 1 - j), 𝓜.boxTerm N i (𝓜.boxTerm N j φ) z :=
        Finset.sum_congr rfl fun j hj => Finset.sum_subset
          (range_subset_range.2 (by simp only [mem_range] at hj; omega))
          fun i _ hi => 𝓜.boxTerm_boxTerm_eq_zero hK φ z (Or.inl (by simpa using hi))
    _ = _ := Finset.sum_subset (range_subset_range.2 (by omega)) fun j _ hj =>
        Finset.sum_eq_zero fun i _ => 𝓜.boxTerm_boxTerm_eq_zero hK φ z (Or.inr (by simpa using hj))

private theorem derivSum_eq_zero {K : ℕ} (hK : 𝓜.PathTermsVanish N K) (φ : X → M) (z : X)
    {n : ℕ} (hn : K ≤ n) : 𝓜.derivSum (N := N) φ z n = 0 := by
  rw [derivSum, Finset.sum_comm]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [← hK n hn (Function.update (fun _ => LinearMap.id) ⟨l, mem_range.1 hl⟩ d) φ z]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.compLinearMap_apply]
  congr 1
  funext t
  by_cases ht : (t : ℕ) = l
  · obtain rfl : t = ⟨l, mem_range.1 hl⟩ := Fin.ext ht
    simp
  · rw [Function.update_of_ne ht, Function.update_of_ne (fun h => ht (by rw [h])),
      LinearMap.id_apply]

/-- **The box tensor differential squares to zero** as soon as the terms of the `A∞` relations
with at least `K` algebra inputs vanish along the paths of `N`. -/
private theorem boxDifferential_boxDifferential_of_pathTermsVanish [CharP R 2] {K : ℕ}
    (hK : 𝓜.PathTermsVanish N K) (φ : X → M) :
    𝓜.boxDifferential N K (𝓜.boxDifferential N K φ) = 0 := by
  funext z
  -- By the `A∞` relations, the terms of `∂ ∘ ∂` with `n` algebra inputs are the derivative and
  -- multiplication terms of length `n`. By the structure equation of `N`, the derivative terms of
  -- length `n` are the multiplication terms of length `n + 1`, so everything cancels except the
  -- multiplication terms of length `2 K + 1`, which are derivative terms of length `2 K ≥ K`.
  rw [𝓜.boxDifferential_boxDifferential_apply hK, Finset.sum_congr rfl fun n _ =>
    𝓜.sum_boxTerm_boxTerm φ z n, Finset.sum_congr rfl fun n _ => by rw [derivSum_eq_mulSum_succ],
    sum_range_add_succ (R := R), ← derivSum_eq_mulSum_succ, 𝓜.derivSum_eq_zero hK φ z (by omega),
    zero_add, mulSum]
  simp

end Paths

/-! ### Bounded type `A` modules -/

section BoundedModule

variable {N : TypeDStructure d ι X} {K : ℕ}

private theorem pathTermsVanish_of_op_eq_zero (hK : ∀ n, K ≤ n → 𝓜.op n = 0) :
    𝓜.PathTermsVanish N K :=
  fun n hn L φ z => Finset.sum_eq_zero fun r _ => by simp [hK n hn]

/-- **The box tensor differential squares to zero** for a bounded type `A` module: if the
operations `m_{n+1}` vanish for `n ≥ K`, then `∂ ∘ ∂ = 0` on `M ⊠ N`. -/
theorem boxDifferential_boxDifferential_of_op_eq_zero [CharP R 2]
    (hK : ∀ n, K ≤ n → 𝓜.op n = 0) (φ : X → M) :
    𝓜.boxDifferential N K (𝓜.boxDifferential N K φ) = 0 :=
  𝓜.boxDifferential_boxDifferential_of_pathTermsVanish
    (𝓜.pathTermsVanish_of_op_eq_zero hK) φ

/-- For a bounded type `A` module, with `m_{n+1} = 0` for `n ≥ K`, the box tensor differential
does not depend on the truncation `K' ≥ K`. -/
theorem boxDifferential_eq_of_op_eq_zero (hK : ∀ n, K ≤ n → 𝓜.op n = 0) {K' : ℕ}
    (hKK' : K ≤ K') : 𝓜.boxDifferential N K' = 𝓜.boxDifferential N K := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  simp only [boxDifferential_apply_eq_sum_boxTerm]
  exact (Finset.sum_subset (range_subset_range.2 hKK') fun k _ hk =>
    𝓜.boxTerm_eq_zero (𝓜.pathTermsVanish_of_op_eq_zero hK)
      (by simpa using hk) φ z).symm

end BoundedModule

end TypeAModule

namespace TypeDStructure

variable {d} {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]
  (N : TypeDStructure d ι X)

/-- Evaluating a multilinear map on the iterate `δᵏ` sums it over the paths. -/
@[simp]
theorem lift_iteratedCoeff {P : Type*} [AddCommGroup P] [Module R P] (k : ℕ)
    (f : MultilinearMap R (fun _ : Fin k => A) P) (x z : X) :
    PiTensorProduct.lift f (N.iteratedCoeff k x z) =
      ∑ r : Fin (k + 1) → X with r 0 = x ∧ r (Fin.last k) = z,
        f fun t => N.pathCoeff (r ∘ (Fin.clamp · k)) t := by
  simp [iteratedCoeff, map_sum]

/-- A type `D` structure whose coefficients strictly decrease a height function `h` is bounded:
`δᵏ x = 0` as soon as `k > h x`. -/
theorem iteratedCoeff_eq_zero_of_lt (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h y < h x)
    {k : ℕ} {x : X} (hk : h x < k) (z : X) : N.iteratedCoeff k x z = 0 := by
  refine Finset.sum_eq_zero fun r hr => ?_
  simp only [mem_filter, mem_univ, true_and] at hr
  by_contra hne
  have hnz : ∀ t < k, N.pathCoeff (r ∘ (Fin.clamp · k)) t ≠ 0 := fun t ht h0 =>
    hne (MultilinearMap.map_coord_zero _ (⟨t, ht⟩ : Fin k) h0)
  have key : ∀ t ≤ k, h ((r ∘ (Fin.clamp · k)) t) + t ≤ h x := by
    intro t ht
    induction t with
    | zero =>
      have : (r ∘ (Fin.clamp · k)) 0 = r 0 := by
        rw [comp_clamp_apply _ (Nat.zero_le k), Fin.zero_eta]
      rw [this, hr.1]
      simp
    | succ t ih =>
      have := hh _ _ (hnz t (by omega))
      have := ih (by omega)
      omega
  have := key k le_rfl
  omega

end TypeDStructure

namespace TypeAModule

variable {d M} (𝓜 : TypeAModule d M) {S : Type*} {ι : S → A} {X : Type*} [Fintype X]
  [DecidableEq X]

/-! ### Bounded type `D` structures -/

section BoundedStructure

variable {N : TypeDStructure d ι X} {K : ℕ}

private theorem pathTermsVanish_of_iteratedCoeff_eq_zero
    (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) : 𝓜.PathTermsVanish N K := by
  intro n hn L φ z
  rw [← Finset.sum_fiberwise _ (fun r : Fin (n + 1) → X => r 0)]
  refine Finset.sum_eq_zero fun x _ => ?_
  have h := N.lift_iteratedCoeff n ((𝓜.op n (φ x)).compLinearMap L) x z
  rw [hK n hn x z, map_zero, eq_comm] at h
  rw [Finset.filter_filter, ← h]
  refine Finset.sum_congr (Finset.filter_congr fun r _ => and_comm) fun r hr => ?_
  simp only [mem_filter, mem_univ, true_and] at hr
  rw [hr.1]

/-- **The box tensor differential squares to zero** for a bounded type `D` structure: if the
iterates `δⁿ` vanish for `n ≥ K`, then `∂ ∘ ∂ = 0` on `M ⊠ N`. -/
theorem boxDifferential_boxDifferential_of_iteratedCoeff_eq_zero [CharP R 2]
    (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) (φ : X → M) :
    𝓜.boxDifferential N K (𝓜.boxDifferential N K φ) = 0 :=
  𝓜.boxDifferential_boxDifferential_of_pathTermsVanish
    (𝓜.pathTermsVanish_of_iteratedCoeff_eq_zero hK) φ

/-- For a bounded type `D` structure, with `δⁿ = 0` for `n ≥ K`, the box tensor differential
does not depend on the truncation `K' ≥ K`. -/
theorem boxDifferential_eq_of_iteratedCoeff_eq_zero
    (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) {K' : ℕ} (hKK' : K ≤ K') :
    𝓜.boxDifferential N K' = 𝓜.boxDifferential N K := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  simp only [boxDifferential_apply_eq_sum_boxTerm]
  exact (Finset.sum_subset (range_subset_range.2 hKK') fun k _ hk =>
    𝓜.boxTerm_eq_zero (𝓜.pathTermsVanish_of_iteratedCoeff_eq_zero hK)
      (by simpa using hk) φ z).symm

end BoundedStructure

end TypeAModule

/-! ### Differential modules -/

namespace TypeAModule

section DG

variable {d M} [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The right action `a ↦ x * a` as an `R`-linear map. -/
private def rightMul (x : M) : A →ₗ[R] M where
  toFun a := MulOpposite.op a • x
  map_add' a b := by simp [add_smul]
  map_smul' c a := by simp [op_smul, smul_assoc]

/-- The operations of a differential right module: `m₁ = dM`, `m₂` the right action, and no
higher operations. -/
private noncomputable def dgOp (dM : M →ₗ[R] M) :
    (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M
  | 0 =>
    { toFun x := MultilinearMap.constOfIsEmpty R _ (dM x)
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
  | 1 =>
    { toFun x := MultilinearMap.ofSubsingleton R A M (0 : Fin 1) (rightMul x)
      map_add' x y := by ext; simp [rightMul]
      map_smul' c x := by
        ext a
        simp only [rightMul, MultilinearMap.ofSubsingleton_apply_apply,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, smul_apply]
        exact smul_comm _ _ _ }
  | _ + 2 => 0

private theorem dgOp_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) : dgOp (A := A) dM n = 0 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

private theorem stasheffSum_dgOp [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (n : ℕ) (x : M) (a : ℕ → A) :
    stasheffSum d (dgOp dM) n x a = 0 := by
  have h2 := add_self_eq_zero_of_charTwo R (M := M)
  match n with
  | 0 => simp [stasheffSum, dgOp, hM.map_map]
  | 1 =>
    simp only [stasheffSum, sum_range_succ, range_zero, sum_empty, zero_add, Nat.sub_self,
      add_zero]
    simp only [Nat.sub_zero, dgOp, Fin.isValue, rightMul, LinearMap.coe_mk, AddHom.coe_mk,
      MultilinearMap.constOfIsEmpty_apply, Function.const_apply, Fin.val_eq_zero,
      MultilinearMap.ofSubsingleton_apply_apply, Nat.add_one_sub_one, hM.map_smul,
      Function.update_self]
    rw [← add_assoc, h2, zero_add, h2]
  | 2 =>
    simp only [stasheffSum, sum_range_succ, range_zero, sum_empty, zero_add]
    simp [dgOp, rightMul, mulAt, mul_smul, h2]
  | n + 3 =>
    simp only [stasheffSum]
    rw [Finset.sum_eq_zero fun j hj => ?_, Finset.sum_eq_zero fun l _ => ?_,
      Finset.sum_eq_zero fun l _ => ?_]
    · simp
    · rw [dgOp_of_two_le dM (by omega)]
      simp
    · rw [dgOp_of_two_le dM (by omega)]
      simp
    · rcases le_or_gt 2 j with hj2 | hj2
      · rw [dgOp_of_two_le dM hj2]
        simp
      · rw [dgOp_of_two_le dM (by simp only [mem_range] at hj; omega)]
        simp

/-- The type `A` module of a differential right module `(M, dM)` over `(A, d)`: `m₁ = dM`,
`m₂(x, a) = x * a`, and no higher operations. -/
noncomputable def ofDGRightModule [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) : TypeAModule d M where
  op := dgOp dM
  stasheffSum_eq_zero := stasheffSum_dgOp hM

variable [CharP R 2] {dM : M →ₗ[R] M}
  (hM : IsUngradedDGRightModule d dM)

@[simp]
theorem ofDGRightModule_op_zero_apply (x : M) (a : Fin 0 → A) :
    (ofDGRightModule hM).op 0 x a = dM x :=
  (rfl)

@[simp]
theorem ofDGRightModule_op_one_apply (x : M) (a : Fin 1 → A) :
    (ofDGRightModule hM).op 1 x a = MulOpposite.op (a 0) • x :=
  (rfl)

theorem ofDGRightModule_op_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (ofDGRightModule hM).op n = 0 :=
  dgOp_of_two_le dM hn

variable {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

/-- For a differential right module, the box tensor differential with the type `A` module
`ofDGRightModule` is the box tensor differential `TauCeti.TypeDStructure.boxDifferential` of the
differential module, `∂ φ = dM φ + φ ⬝ δ`, for every truncation `K ≥ 2`. -/
theorem boxDifferential_ofDGRightModule (N : TypeDStructure d ι X) {K : ℕ} (hK : 2 ≤ K) :
    (ofDGRightModule hM).boxDifferential N K = N.boxDifferential dM := by
  rw [boxDifferential_eq_of_op_eq_zero _ (fun n hn => ofDGRightModule_op_of_two_le hM hn) hK]
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [boxDifferential_apply, TypeDStructure.boxDifferential_apply, Pi.add_apply,
    continuationMap_apply (R := R) (M := M) N.coeff]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, ofDGRightModule_op_zero_apply,
    ofDGRightModule_op_one_apply, Finset.sum_filter]
  congr 1
  · rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
    simp
  · rw [← (piFinTwoEquiv fun _ => X).symm.sum_comp, Fintype.sum_prod_type]
    simp [TypeDStructure.pathCoeff, Fin.clamp]

end DG

end TypeAModule

end TauCeti
