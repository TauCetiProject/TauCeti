/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA
public import TauCeti.LowDimTopology.Bordered.TypeD
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The box tensor product of type `A` modules with type `D` structures

In bordered Heegaard Floer homology the Floer complex of a closed manifold glued from two pieces
is the box tensor product `CFA ⊠ CFD` of a type `A` module (`TauCeti.TypeAModule`) with a type `D`
structure (`TauCeti.TypeDStructure`), with the differential
`∂ (y ⊗ x) = ∑_k (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`, where `δᵏ` are the iterates
`TauCeti.TypeDStructure.iteratedCoeff`. This file constructs that differential over a ring of
characteristic two and proves that it squares to zero when either factor is bounded.

On row vectors `φ : X → M`, standing for `∑ x, φ x ⊗ x`, the differential with the first `K`
iterates is `TauCeti.TypeAModule.boxDifferential`. Row vectors model the tensor product over `R`;
the summand over the idempotents, which `TauCeti.TypeDStructure.boxTensor` cuts out for
differential modules, needs an action of the idempotents on `M` and is not treated here. When the
type `A` module is bounded (`m_{n+1} = 0` for `n ≥ K`) or the type `D` structure is bounded
(`δⁿ = 0` for `n ≥ K`), every term with at least `K` algebra inputs vanishes, the differential
does not depend on the truncation beyond `K`, and it squares to zero. Without boundedness the sum
over `k` is infinite and is not a differential; boundedness is a hypothesis of the tensor product,
not a consequence of the finiteness of `X`. For a differential right module the box tensor
differential is `TauCeti.TypeDStructure.boxDifferential`.

The proof of `∂ ∘ ∂ = 0` concatenates paths: the terms of `∂ ∘ ∂` with `n` algebra inputs in
total are the first sum of the `A∞` relation of arity `n` along the paths of length `n`, so they
are the derivative and multiplication terms of that relation. Expanding `d` of a coefficient by
the structure equation `d δ = δ * δ` of the type `D` structure inserts an intermediate
generator, which turns the derivative terms along paths of length `n` into the multiplication
terms along paths of length `n + 1`. The sum over `n` telescopes, and the remaining terms vanish
by boundedness.

## Main definitions

* `TauCeti.TypeAModule.boxDifferential`: the box tensor differential, truncated to `K` iterates.

## Main results

* `TauCeti.TypeAModule.boxDifferential_apply_eq_sum_lift_iteratedCoeff`: the box tensor
  differential is `∂ (y ⊗ x) = ∑_{k < K} (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`.
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
  Chapter 2: boundedness and the box tensor product (equation (2.29)).
-/

public section

open Finset

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d : A →ₗ[R] A}
  {M : Type*} [AddCommGroup M] [Module R M]

namespace TypeAModule

variable (𝓜 : TypeAModule d M) {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

/-- The **box tensor differential** of a type `A` module `𝓜` with a type `D` structure `N`,
truncated to the first `K` iterates of the structure map. On row vectors `φ : X → M`, standing
for `∑ x, φ x ⊗ x`, it sums over the paths `r 0, …, r k = z` with `k < K`:
`∂ φ z = ∑ m_{k+1}(φ (r 0), coeff (r 0) (r 1), …, coeff (r (k-1)) (r k))`, that is
`∂ (y ⊗ x) = ∑_{k < K} (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`
(`boxDifferential_apply_eq_sum_lift_iteratedCoeff`). When `𝓜` or `N` is bounded, it does not
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

/-- The box tensor differential in terms of the iterates `δᵏ` of the structure map:
`∂ (y ⊗ x) = ∑_{k < K} (m_{k+1} ⊗ 1)(y ⊗ δᵏ x)`. -/
theorem boxDifferential_apply_eq_sum_lift_iteratedCoeff (N : TypeDStructure d ι X) (K : ℕ)
    (φ : X → M) (z : X) :
    𝓜.boxDifferential N K φ z =
      ∑ k ∈ range K, ∑ x, PiTensorProduct.lift (𝓜.op k (φ x)) (N.iteratedCoeff k x z) := by
  simp only [TypeDStructure.sum_lift_iteratedCoeff, boxDifferential_apply]

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
  simp [concatPath, ht, Fin.clamp_eq_mk ht, Fin.clamp_eq_mk (show t ≤ j + i by omega)]

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
  · simp only [Function.comp_apply, Fin.clamp_eq_mk (show j + s ≤ j + i by omega),
      Fin.clamp_eq_mk hs, key s hs]
  · simp only [Function.comp_apply, Fin.clamp_eq_last (j + s) (j + i) (by omega),
      Fin.clamp_eq_last s i hs.le]
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
  -- The pairs `(q, p)` of a path `p` of length `j` followed by a path `q` of length `i` starting
  -- where `p` ends correspond to the paths of length `j + i`: concatenate them, or split a path
  -- at `j`.
  refine Finset.sum_nbij' (fun qp => concatPath qp.1 qp.2)
    (fun r => ⟨fun s : Fin (i + 1) => r ⟨j + s, by omega⟩, fun t : Fin (j + 1) => r ⟨t, by omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- The concatenation ends where `q` ends.
    rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨hq, hp⟩ := h
    have h := concatPath_comp_clamp_add q p hp i
    simpa only [Function.comp_apply, Fin.clamp_eq_last (j + i) (j + i) le_rfl,
      Fin.clamp_eq_last i i le_rfl, hq] using h
  · -- The second half of a split path ends where the path ends and starts where the first half
    -- ends.
    intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_sigma] at hr ⊢
    exact ⟨hr, rfl⟩
  · -- Splitting a concatenation at `j` recovers both paths.
    rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h
    obtain ⟨-, hp⟩ := h
    refine Sigma.ext (funext fun s => ?_) (heq_of_eq (funext fun t => ?_))
    · have h := concatPath_comp_clamp_add q p hp s
      simpa only [Function.comp_apply, Fin.clamp_eq_mk (show j + (s : ℕ) ≤ j + i by omega),
        Fin.clamp_eq_mk (show (s : ℕ) ≤ i by omega)] using h
    · simp only [concatPath]
      rw [dite_eq_left (Nat.lt_succ_iff.mp t.isLt)]
  · -- Concatenating the two halves of a split path recovers the path.
    intro r _
    funext t
    simp only [concatPath]
    split_ifs with ht
    · simp
    · congr 1
      ext
      simp only
      omega
  · -- Along a concatenation, the first `j` coefficients are those of `p` and the next `i` are
    -- those of `q`.
    rintro ⟨q, p⟩ h
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h
    obtain ⟨-, hp⟩ := h
    have h0 : concatPath q p 0 = p 0 := by simp [concatPath]
    simp only [TypeDStructure.pathCoeff_apply]
    rw [h0]
    refine congrArg₂ (fun u v => 𝓜.op i u v) (congrArg _ (funext fun t => ?_))
      (funext fun s => ?_)
    · rw [concatPath_comp_clamp_of_le q p (t := t) (by omega),
        concatPath_comp_clamp_of_le q p (t := t + 1) (by omega)]
    · rw [concatPath_comp_clamp_add q p hp, show j + (s : ℕ) + 1 = j + ((s : ℕ) + 1) by omega,
        concatPath_comp_clamp_add q p hp]

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_of_le {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) {t : ℕ} (ht : t ≤ l) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) t =
      (r ∘ (Fin.clamp · n)) t := by
  simp only [Function.comp_apply, Fin.clamp_eq_mk (show t ≤ n + 1 by omega),
    Fin.clamp_eq_mk (show t ≤ n by omega)]
  rw [Fin.insertNth_apply_below (i := ⟨l + 1, by omega⟩) (j := ⟨t, by omega⟩)
    (Fin.mk_lt_mk.2 (by omega)), eq_rec_constant]
  rfl

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_self {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) (l + 1) =
      w := by
  simp only [Function.comp_apply, Fin.clamp_eq_mk (show l + 1 ≤ n + 1 by omega),
    Fin.insertNth_apply_same]

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_last {n l : ℕ} (hl : l < n) (w : X) (r : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r (Fin.last (n + 1)) = r (Fin.last n) := by
  rw [Fin.insertNth_apply_above (i := ⟨l + 1, by omega⟩) (j := Fin.last (n + 1))
    (Fin.lt_def.2 (by simp only [Fin.val_last]; omega)), eq_rec_constant]
  exact congrArg r (Fin.ext (by simp))

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_zero {n l : ℕ} (hl : l < n) (w : X) (r : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r 0 = r 0 := by
  simpa only [Function.comp_apply, Fin.clamp_eq_mk (Nat.zero_le _), Fin.zero_eta] using
    insertNth_comp_clamp_of_le hl w r (Nat.zero_le l)

omit [Fintype X] [DecidableEq X] in
private theorem insertNth_comp_clamp_succ {n l : ℕ} (hl : l < n) (w : X)
    (r : Fin (n + 1) → X) {t : ℕ} (ht : l + 1 ≤ t) :
    (Fin.insertNth (α := fun _ => X) ⟨l + 1, by omega⟩ w r ∘ (Fin.clamp · (n + 1))) (t + 1) =
      (r ∘ (Fin.clamp · n)) t := by
  rcases le_or_gt t n with htn | htn
  · simp only [Function.comp_apply, Fin.clamp_eq_mk (show t + 1 ≤ n + 1 by omega),
      Fin.clamp_eq_mk htn]
    rw [Fin.insertNth_apply_above (i := ⟨l + 1, by omega⟩) (j := ⟨t + 1, by omega⟩)
      (Fin.mk_lt_mk.2 (by omega)), eq_rec_constant]
    rfl
  · simp only [Function.comp_apply, Fin.clamp_eq_last (t + 1) (n + 1) (by omega),
      Fin.clamp_eq_last t n htn.le]
    exact insertNth_last hl w r

/-- Expanding `d` of one coefficient along a path by the structure equation of `N` inserts an
intermediate generator: the derivative terms of the `A∞` relation along paths of length `n` are
the multiplication terms along paths of length `n + 1`. -/
private theorem sum_op_update_eq [CharP R 2] (φ : X → M) {n l : ℕ} (hl : l < n) (z : X) :
    ∑ r : Fin (n + 1) → X with r (Fin.last n) = z,
      𝓜.op n (φ (r 0)) (fun t => Function.update (N.pathCoeff (r ∘ (Fin.clamp · n))) l
        (d (N.pathCoeff (r ∘ (Fin.clamp · n)) l)) t) =
    ∑ r : Fin (n + 1 + 1) → X with r (Fin.last (n + 1)) = z,
      𝓜.op n (φ (r 0)) (fun t => replaceBlock (N.pathCoeff (r ∘ (Fin.clamp · (n + 1)))) l 2
        (N.pathCoeff (r ∘ (Fin.clamp · (n + 1))) l *
          N.pathCoeff (r ∘ (Fin.clamp · (n + 1))) (l + 1)) t) := by
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (n := n + 1) (fun _ => X) ⟨l + 1, by omega⟩),
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : d (N.pathCoeff (r ∘ (Fin.clamp · n)) l) = ∑ w, N.coeff ((r ∘ (Fin.clamp · n)) l) w *
      N.coeff w ((r ∘ (Fin.clamp · n)) (l + 1)) := by
    have h := congrFun (congrFun (N.map_coeff_eq_coeff_mul_coeff) ((r ∘ (Fin.clamp · n)) l))
      ((r ∘ (Fin.clamp · n)) (l + 1))
    simpa [TypeDStructure.pathCoeff_apply, Matrix.mul_apply] using h
  have hupd (a : ℕ → A) (v : A) : (fun t : Fin n => Function.update a l v t) =
      Function.update (fun t : Fin n => a t) ⟨l, hl⟩ v :=
    Function.update_comp_eq_of_injective a Fin.val_injective (⟨l, hl⟩ : Fin n) v
  rw [hd, hupd, MultilinearMap.map_update_sum]
  simp only [Fin.insertNthEquiv_apply, insertNth_last hl, insertNth_zero hl]
  by_cases hz : r (Fin.last n) = z
  · simp only [hz, ite_true]
    refine Finset.sum_congr rfl fun w _ => congrArg _ (funext fun t => ?_)
    simp only [Function.update_apply, Fin.ext_iff]
    rcases lt_trichotomy (t : ℕ) l with ht | ht | ht
    · rw [ite_eq_right ht.ne, replaceBlock_of_lt _ _ _ _ ht, TypeDStructure.pathCoeff_apply,
        TypeDStructure.pathCoeff_apply, insertNth_comp_clamp_of_le hl w r ht.le,
        insertNth_comp_clamp_of_le hl w r (by omega : (t : ℕ) + 1 ≤ l)]
    · simp only [ht, ite_true, replaceBlock_self, TypeDStructure.pathCoeff_apply]
      rw [insertNth_comp_clamp_of_le hl w r le_rfl, insertNth_comp_clamp_self hl,
        insertNth_comp_clamp_succ hl w r le_rfl]
    · rw [ite_eq_right (by omega), replaceBlock_of_gt _ _ _ _ ht,
        show (t : ℕ) + 2 - 1 = t + 1 by omega, TypeDStructure.pathCoeff_apply,
        TypeDStructure.pathCoeff_apply,
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
    𝓜.op (n - 1) (φ (r 0)) (fun t => replaceBlock (N.pathCoeff (r ∘ (Fin.clamp · n))) l 2
      (N.pathCoeff (r ∘ (Fin.clamp · n)) l * N.pathCoeff (r ∘ (Fin.clamp · n)) (l + 1)) t)

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
  rw [stasheffSum_def, add_assoc, add_eq_zero_iff_eq_of_charTwo R] at h
  exact h

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
  -- In characteristic two, `∑ n < L, (f (n + 1) + f n) = f L + f 0` telescopes.
  have htel (f : ℕ → M) (L : ℕ) : ∑ n ∈ range L, (f (n + 1) + f n) = f L + f 0 := by
    have hneg (x : M) : -x = x := neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_charTwo R x)
    simpa only [sub_eq_add_neg, hneg] using Finset.sum_range_sub f L
  -- By the `A∞` relations, the terms of `∂ ∘ ∂` with `n` algebra inputs are the derivative and
  -- multiplication terms of length `n`. By the structure equation of `N`, the derivative terms of
  -- length `n` are the multiplication terms of length `n + 1`, so everything cancels except the
  -- multiplication terms of length `2 K + 1`, which are derivative terms of length `2 K ≥ K`.
  rw [𝓜.boxDifferential_boxDifferential_apply hK, Finset.sum_congr rfl fun n _ =>
    𝓜.sum_boxTerm_boxTerm φ z n, Finset.sum_congr rfl fun n _ => by rw [derivSum_eq_mulSum_succ],
    htel, ← derivSum_eq_mulSum_succ, 𝓜.derivSum_eq_zero hK φ z (by omega), zero_add, mulSum]
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

/-! ### Bounded type `D` structures -/

section BoundedStructure

variable {N : TypeDStructure d ι X} {K : ℕ}

private theorem pathTermsVanish_of_iteratedCoeff_eq_zero
    (hK : ∀ n, K ≤ n → ∀ x z, N.iteratedCoeff n x z = 0) : 𝓜.PathTermsVanish N K := by
  intro n hn L φ z
  have h := N.sum_lift_iteratedCoeff n (fun x => (𝓜.op n (φ x)).compLinearMap L) z
  simp only [hK n hn, map_zero, sum_const_zero] at h
  exact h.symm

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

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [CharP R 2] {dM : M →ₗ[R] M}
  (hM : IsUngradedDGRightModule d dM)
  {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]

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
    simp [Fin.clamp_eq_mk]

end TypeAModule

end TauCeti
