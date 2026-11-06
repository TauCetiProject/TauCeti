/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Ungraded
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Ungraded `A∞` right modules over a differential algebra

Let `(A, d)` be an algebra with a linear map `d`, thought of as an ungraded differential algebra
(`TauCeti.IsUngradedDGAlgebra`). An **ungraded `A∞` right module** over it is a module `M` with
operations `m_{n+1} : M ⊗ A^{⊗ n} → M` for every `n ≥ 0`, here
`act n : MultilinearMap R (Fin n → A) (M →ₗ[R] M)`, satisfying for every `m` and `a₁, …, aₙ` the
relation

`∑_{i + j = n} m_{j+1}(m_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
`  + ∑_l m_{n+1}(m, a₁, …, d aₗ, …, aₙ) + ∑_l m_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ) = 0`

(`TauCeti.UngradedAInfinityRightModule`). Over a ring of characteristic two these are the `A∞`
relations of a right module over the differential algebra `A`: every Koszul sign is `±1`, hence
`1`. They are the type `A` modules of bordered Heegaard Floer homology over `𝔽₂`, such as the
module `CFA` of a bordered three-manifold. Tau Ceti's `A∞` right modules
(`TauCeti.AInfinityRightModule`) are `ℤ`-graded with operations of degree `1 - n`, which an ungraded
differential cannot carry, for the reason recorded in `TauCeti.Algebra.Homology.DG.Ungraded`.

A differential right module (`TauCeti.IsUngradedDGRightModule`) is an `A∞` module whose
operations `m_{n+1}` vanish for `n ≥ 2`, over a ring of characteristic two
(`TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule`).

Two constructions are developed.

* **Twisting.** For a Maurer–Cartan element `β`, that is `d β + β * β = 0`, the
  **twisted differential** `∂^β = ∑ₙ m_{n+1}(·, β, …, β)`
  (`TauCeti.UngradedAInfinityRightModule.twistedDifferential`) squares to zero over a ring of
  characteristic two, provided the operations vanish from some arity on when fed elements of a set
  containing `β` and `β * β`
  (`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential`). Summing the
  relations over all lengths, the composite terms assemble into `∂^β ∘ ∂^β`, while the
  differential term `m_{n+1}(…, d β, …)` cancels the product term `m_{n+1}(…, β * β, …)` coming from
  length `n + 1`.
* **Matrices.** The row vectors `X → M`, for a finite type `X`, form an `A∞` module over the
  matrix algebra `Matrix X X A` with the entrywise differential
  (`TauCeti.UngradedAInfinityRightModule.matrix`): `m_{n+1}(φ, F₁, …, Fₙ)` has `z`-component the
  sum, over the paths `x₀ → x₁ → ⋯ → xₙ = z` in `X`, of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`
  (`TauCeti.UngradedAInfinityRightModule.matrixAct`). The composite terms concatenate paths and the
  product terms insert a vertex into a path.

Twisting the matrix module by the coefficient matrix of a type `D` structure gives the box tensor
product of bordered Heegaard Floer homology; see `TauCeti.LowDimTopology.Bordered.TypeA`.

## Main definitions

* `TauCeti.UngradedAInfinityRightModule`: an ungraded `A∞` right module.
* `TauCeti.UngradedAInfinityRightModule.twistedDifferential`: the differential twisted by an
  element of the algebra.
* `TauCeti.UngradedAInfinityRightModule.matrixAct` and
  `TauCeti.UngradedAInfinityRightModule.matrix`: the `A∞` module of row vectors over the matrix
  algebra.
* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule`: a differential right module as
  an `A∞` module.

## Main results

* `TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential`: the twisted
  differential squares to zero.
* `TauCeti.UngradedAInfinityRightModule.matrixAct_apply`: the components of the matrix operations
  are sums over paths.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (`A∞` modules over `𝔽₂` and the box tensor product).
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. **3**
  (2001), 1–35, Section 4 (`A∞` modules).
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-! ### The relations -/

section Stasheff

variable (act : (n : ℕ) → MultilinearMap R (fun _ : Fin n => A) (M →ₗ[R] M))

/-- The **composite terms** of the `A∞` relation of length `n`:
`∑_{i + j = n} m_{j+1}(m_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`, where `act i` is `m_{i+1}`. -/
noncomputable def ungradedStasheffComp (n : ℕ) (a : Fin n → A) (m : M) : M :=
  ∑ k : Fin (n + 1), act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
    (act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m)

/-- The **differential terms** of the `A∞` relation of length `n`:
`∑_l m_{n+1}(m, a₁, …, d aₗ, …, aₙ)`. -/
noncomputable def ungradedStasheffDiff (d : A →ₗ[R] A) (n : ℕ) (a : Fin n → A) (m : M) : M :=
  ∑ l : Fin n, act n (Function.update a l (d (a l))) m

/-- The **product terms** of the `A∞` relation of length `n`:
`∑_l m_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ)`, over the `n - 1` adjacent pairs. -/
noncomputable def ungradedStasheffMul : (n : ℕ) → (Fin n → A) → M → M
  | 0, _, _ => 0
  | n + 1, a, m => ∑ l : Fin n, act n (Fin.contractNth l.castSucc (· * ·) a) m

@[simp]
theorem ungradedStasheffMul_zero (a : Fin 0 → A) (m : M) : ungradedStasheffMul act 0 a m = 0 :=
  (rfl)

theorem ungradedStasheffMul_succ (n : ℕ) (a : Fin (n + 1) → A) (m : M) :
    ungradedStasheffMul act (n + 1) a m =
      ∑ l : Fin n, act n (Fin.contractNth l.castSucc (· * ·) a) m :=
  (rfl)

end Stasheff

/-- An **ungraded `A∞` right module** over the algebra `A` with differential `d`. The operation
`act n` is `m_{n+1} : M ⊗ A^{⊗ n} → M`, multilinear in the algebra inputs and linear in the module
input, and the operations satisfy the `A∞` relation of every length `n`: the composite terms
`TauCeti.ungradedStasheffComp`, the differential terms `TauCeti.ungradedStasheffDiff` and the
product terms `TauCeti.ungradedStasheffMul` sum to zero. No sign appears: over a ring of
characteristic two these are the `A∞` relations, and no characteristic is imposed by the
definition itself. The relation of length zero says that `m₁ = act 0` squares to zero. -/
@[ext]
structure UngradedAInfinityRightModule (d : A →ₗ[R] A) (M : Type*) [AddCommGroup M]
    [Module R M] where
  /-- The operation `m_{n+1}`, with `n` algebra inputs. -/
  act : (n : ℕ) → MultilinearMap R (fun _ : Fin n => A) (M →ₗ[R] M)
  /-- The `A∞` relation of length `n`. -/
  stasheff (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffComp act n a m + ungradedStasheffDiff act d n a m +
      ungradedStasheffMul act n a m = 0

namespace UngradedAInfinityRightModule

variable {d : A →ₗ[R] A} (Mm : UngradedAInfinityRightModule d M)

/-- The operation `m₁` squares to zero: the relation of length zero. -/
@[simp]
theorem act_zero_act_zero (a b : Fin 0 → A) (m : M) : Mm.act 0 a (Mm.act 0 b m) = 0 := by
  have h := Mm.stasheff 0 a m
  rw [ungradedStasheffComp, Fin.sum_univ_one] at h
  simp only [ungradedStasheffDiff, Fin.sum_univ_zero, ungradedStasheffMul_zero, add_zero] at h
  convert h using 2
  · exact congrArg (Mm.act 0) (Subsingleton.elim _ _)
  · exact congrArg (fun c => Mm.act 0 c m) (Subsingleton.elim _ _)

/-! ### Twisting by a Maurer–Cartan element -/

/-- The **twisted differential** `∂^β = ∑ₙ m_{n+1}(·, β, …, β)` of an element `β` of the algebra.
It is a finite sum when the operations `m_{n+1}(·, β, …, β)` vanish for large `n`
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential_eq_sum`); otherwise this `finsum` is
`0` by convention. -/
noncomputable def twistedDifferential (β : A) : M →ₗ[R] M :=
  ∑ᶠ n, Mm.act n fun _ => β

/-- When `m_{n+1}(·, β, …, β)` vanishes for `n ≥ K`, the twisted differential is the sum of the
first `K` operations. -/
theorem twistedDifferential_eq_sum {β : A} {K : ℕ}
    (h : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0) :
    Mm.twistedDifferential β = ∑ n ∈ range K, Mm.act n fun _ => β := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simpa using not_le.mp (mt (h n) hn)

/-- Contracting an adjacent pair in a constant tuple gives an update of the constant tuple. -/
private theorem contractNth_const {n : ℕ} (l : Fin n) (β : A) :
    Fin.contractNth l.castSucc (· * ·) (fun _ : Fin (n + 1) => β) =
      Function.update (fun _ => β) l (β * β) := by
  funext k
  rcases lt_trichotomy (k : ℕ) l with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Function.update_of_ne (Fin.ne_of_lt h)]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.ext h, Function.update_self]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Function.update_of_ne (Fin.ne_of_gt h)]

/-- The `A∞` relations of length at most `N` along a constant tuple `β` with `d β = β * β`, over a
ring of characteristic two, summed: the differential terms of length `n` cancel the product terms
of length `n + 1`, and the composite terms add up to the differential terms of length `N`. -/
private theorem sum_sum_act_act_const [CharP R 2] {β : A} (hβ : d β = β * β) (N : ℕ) (m : M) :
    ∑ n ∈ range (N + 1), ∑ k ∈ range (n + 1),
        Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m) =
      ∑ l : Fin N, Mm.act N (Function.update (fun _ => β) l (β * β)) m := by
  set T : ℕ → M := fun n =>
    ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (β * β)) m with hT
  have h := Finset.sum_eq_zero (s := range (N + 1)) fun n _ => Mm.stasheff n (fun _ => β) m
  rw [sum_add_distrib, sum_add_distrib, sum_range_succ' (fun n =>
    ungradedStasheffMul Mm.act n (fun _ => β) m), sum_range_succ (fun n =>
    ungradedStasheffDiff Mm.act d n (fun _ => β) m)] at h
  have hcomp (n : ℕ) : ungradedStasheffComp Mm.act n (fun _ => β) m =
      ∑ k ∈ range (n + 1), Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m) :=
    Fin.sum_univ_eq_sum_range (fun k => Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m))
      (n + 1)
  have hdiff (n : ℕ) : ungradedStasheffDiff Mm.act d n (fun _ => β) m = T n := by
    simp only [ungradedStasheffDiff, hβ, hT]
  have hmul (n : ℕ) : ungradedStasheffMul Mm.act (n + 1) (fun _ => β) m = T n := by
    simp only [ungradedStasheffMul_succ, contractNth_const, hT]
  simp only [hcomp, hdiff, hmul, ungradedStasheffMul_zero, add_zero] at h
  refine (add_eq_zero_iff_eq_of_charTwo R).mp ?_
  calc _ = ∑ n ∈ range (N + 1), ∑ k ∈ range (n + 1),
          Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m) + T N +
        (∑ n ∈ range N, T n + ∑ n ∈ range N, T n) := by
        rw [add_self_eq_zero_of_charTwo R, add_zero]
    _ = 0 := by rw [← h]; abel

/-- **The twisted differential squares to zero.** Let `β` be a Maurer–Cartan element,
`d β + β * β = 0`, over a ring of characteristic two, and suppose that `m_{n+1}` vanishes for
`n ≥ K` on every tuple of elements of a set `U` containing `β` and `β * β`. Then
`∂^β ∘ ∂^β = 0`. For `U` the whole algebra this is the case of a module whose operations vanish
from some arity on. -/
theorem twistedDifferential_twistedDifferential [CharP R 2] {β : A} (hβ : d β + β * β = 0)
    {U : Set A} (hβU : β ∈ U) (hββU : β * β ∈ U) {K : ℕ}
    (hU : ∀ n, K ≤ n → ∀ u : Fin n → A, (∀ l, u l ∈ U) → Mm.act n u = 0) (m : M) :
    Mm.twistedDifferential β (Mm.twistedDifferential β m) = 0 := by
  have hc : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0 := fun n hn => hU n hn _ fun _ => hβU
  set f : ℕ → ℕ → M := fun i j => Mm.act j (fun _ => β) (Mm.act i (fun _ => β) m) with hf
  -- The relations of length at most `2 K` leave only terms of length `2 K`, which vanish.
  have hrel : ∑ n ∈ range (2 * K + 1), ∑ k ∈ range (n + 1), f k (n - k) = 0 := by
    rw [Mm.sum_sum_act_act_const ((add_eq_zero_iff_eq_of_charTwo R).mp hβ)]
    refine sum_eq_zero fun l _ => ?_
    rw [hU _ (by omega) _ fun t => ?_, LinearMap.zero_apply]
    by_cases ht : t = l
    · subst ht; simpa using hββU
    · simpa [Function.update_of_ne ht] using hβU
  have hfi (i j : ℕ) (hi : K ≤ i) : f i j = 0 := by simp [hf, hc i hi]
  have hfj (i j : ℕ) (hj : K ≤ j) : f i j = 0 := by simp [hf, hc j hj]
  rw [Mm.twistedDifferential_eq_sum hc]
  simp only [LinearMap.sum_apply, map_sum]
  -- `∂^β ∘ ∂^β` is the sum of the composite terms of all lengths at most `2 K`.
  calc _ = ∑ i ∈ range K, ∑ j ∈ range K, f i j := rfl
    _ = ∑ i ∈ range (2 * K + 1), ∑ j ∈ range (2 * K + 1 - i), f i j := by
        rw [← sum_subset (range_subset_range.mpr (by omega : K ≤ 2 * K + 1)) fun i _ hi =>
          sum_eq_zero fun j _ => hfi i j (by simpa using hi)]
        refine sum_congr rfl fun i hi => ?_
        exact sum_subset (range_subset_range.mpr (by simp at hi; omega)) fun j _ hj =>
          hfj i j (by simpa using hj)
    _ = 0 := by rw [← sum_range_diag_flip, hrel]

/-! ### The module of row vectors over the matrix algebra -/

section Matrix

variable (X : Type*) [Fintype X] [DecidableEq X]

/-- The operations of the **matrix module**: `m_{n+1}(φ, F₁, …, Fₙ)` sends a row vector
`φ : X → M` to the row vector whose `z`-component is the sum, over the paths
`x₀ → x₁ → ⋯ → xₙ = z` in `X`, of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`
(`TauCeti.UngradedAInfinityRightModule.matrixAct_apply`). -/
noncomputable def matrixAct (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => Matrix X X A) ((X → M) →ₗ[R] X → M) :=
  ∑ x : Fin (n + 1) → X,
    (LinearMap.llcomp R (X → M) M (X → M) (LinearMap.single R (fun _ => M) (x (Fin.last n))) ∘ₗ
      LinearMap.lcomp R M (LinearMap.proj (x 0))).compMultilinearMap
      ((Mm.act n).compLinearMap fun l => Matrix.entryLinearMap R A (x l.castSucc) (x l.succ))

/-- The `z`-component of `m_{n+1}(φ, F₁, …, Fₙ)` in the matrix module is the sum over the paths
`x₀ → ⋯ → xₙ = z` of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`. -/
theorem matrixAct_apply (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    Mm.matrixAct X n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then Mm.act n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  simp only [matrixAct, _root_.sum_apply, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.lcomp_apply, LinearMap.llcomp_apply, LinearMap.coe_single,
    LinearMap.coe_proj, Function.eval, Matrix.entryLinearMap_apply, Pi.single_apply, eq_comm]

/-- Concatenating paths: pairs of paths of lengths `i` and `j` meeting at an endpoint are the
paths of length `i + j`. -/
private theorem sum_sum_ite_eq {N : Type*} [AddCommMonoid N] {i j n : ℕ} (h : i + j = n)
    (g : (Fin (i + 1) → X) → (Fin (j + 1) → X) → N) :
    ∑ x : Fin (i + 1) → X, ∑ y : Fin (j + 1) → X,
        (if x (Fin.last i) = y 0 then g x y else 0) =
      ∑ w : Fin (n + 1) → X,
        g (fun t => w ⟨t, by have := t.isLt; omega⟩)
          (fun t => w ⟨i + t, by have := t.isLt; omega⟩) := by
  rw [← sum_product', ← sum_filter]
  symm
  refine sum_nbij' (fun w => ((fun t => w ⟨t, by have := t.isLt; omega⟩),
      fun t => w ⟨i + t, by have := t.isLt; omega⟩))
    (fun p t => if ht : (t : ℕ) ≤ i then p.1 ⟨t, by omega⟩
      else p.2 ⟨t - i, by have := t.isLt; omega⟩)
    (fun w _ => by simp [Fin.last]) (fun _ _ => mem_univ _) (fun w _ => ?_) (fun p hp => ?_)
    (fun _ _ => rfl)
  · funext t
    split_ifs with ht
    · rfl
    · dsimp only
      exact congrArg w (Fin.ext (by simp only; omega))
  · simp only [mem_filter, mem_product, mem_univ, true_and] at hp
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
    · simp [show (t : ℕ) ≤ i by have := t.isLt; omega]
    · by_cases ht : (t : ℕ) = 0
      · have h0 : t = 0 := Fin.ext ht
        subst h0
        simpa [Fin.last] using hp
      · simp only [show ¬ (i + t ≤ i) by omega, dite_false]
        exact congrArg p.2 (Fin.ext (by simp))

/-- **Composing operations of the matrix module.** The `z`-component of
`m_{j+1}(m_{i+1}(φ, F₁, …, Fᵢ), G₁, …, Gⱼ)` is the sum over the paths `w₀ → ⋯ → wᵢ₊ⱼ = z` of
`m_{j+1}(m_{i+1}(φ w₀, F₁ w₀ w₁, …), G₁ wᵢ wᵢ₊₁, …)`. -/
theorem matrixAct_matrixAct_apply {i j n : ℕ} (h : i + j = n) (G : Fin j → Matrix X X A)
    (F : Fin i → Matrix X X A) (φ : X → M) (z : X) :
    Mm.matrixAct X j G (Mm.matrixAct X i F φ) z = ∑ w : Fin (n + 1) → X,
      if w (Fin.last n) = z then
        Mm.act j (fun l => G l (w ⟨i + l, by have := l.isLt; omega⟩)
          (w ⟨i + l + 1, by have := l.isLt; omega⟩))
          (Mm.act i (fun l => F l (w ⟨l, by have := l.isLt; omega⟩)
            (w ⟨l + 1, by have := l.isLt; omega⟩)) (φ (w 0)))
      else 0 := by
  have hy (y : Fin (j + 1) → X) :
      (if y (Fin.last j) = z then Mm.act j (fun l => G l (y l.castSucc) (y l.succ))
        (Mm.matrixAct X i F φ (y 0)) else 0) =
      ∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
        (if y (Fin.last j) = z then Mm.act j (fun l => G l (y l.castSucc) (y l.succ))
          (Mm.act i (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))) else 0) else 0 := by
    split_ifs with hyz
    · simp only [matrixAct_apply, map_sum]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    · simp
  rw [matrixAct_apply, sum_congr rfl fun y _ => hy y, sum_comm, sum_sum_ite_eq X h]
  refine sum_congr rfl fun w _ => ?_
  have hlast : w ⟨i + (Fin.last j : ℕ), by simp; omega⟩ = w (Fin.last n) :=
    congrArg w (Fin.ext (by simp [h]))
  have hzero : w ⟨((0 : Fin (i + 1)) : ℕ), by simp⟩ = w 0 := congrArg w (Fin.ext (by simp))
  dsimp only
  simp only [hlast, hzero]
  rfl

omit [Ring A] [Fintype X] [DecidableEq X] in
/-- Updating one matrix of a tuple updates one entry along every path. -/
private theorem update_apply_apply {n : ℕ} (F : Fin n → Matrix X X A) (x : Fin (n + 1) → X)
    (l : Fin n) (G : Matrix X X A) :
    (fun t => Function.update F l G t (x t.castSucc) (x t.succ)) =
      Function.update (fun t => F t (x t.castSucc) (x t.succ)) l (G (x l.castSucc) (x l.succ)) := by
  funext t
  by_cases ht : t = l
  · subst ht; simp
  · simp [Function.update_of_ne ht]

/-- The composite terms of the matrix module are sums over paths. -/
private theorem stasheffComp_matrixAct (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedStasheffComp (Mm.matrixAct X) n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then
        ungradedStasheffComp Mm.act n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  simp only [ungradedStasheffComp, Finset.sum_apply]
  rw [sum_congr rfl fun k _ => Mm.matrixAct_matrixAct_apply X
    (Nat.add_sub_of_le (Nat.lt_succ_iff.mp k.isLt)) _ _ φ z, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · rfl
  · simp

/-- The differential terms of the matrix module are sums over paths. -/
private theorem stasheffDiff_matrixAct (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedStasheffDiff (Mm.matrixAct X) (d.mapMatrix : Matrix X X A →ₗ[R] Matrix X X A) n F φ z =
      ∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
        ungradedStasheffDiff Mm.act d n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  simp only [ungradedStasheffDiff, Finset.sum_apply, matrixAct_apply, update_apply_apply,
    LinearMap.mapMatrix_apply, Matrix.map_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

omit [Fintype X] [DecidableEq X] in
/-- Inserting the vertex `v` after the `l`-th vertex of a path `x`. -/
private theorem insertNth_apply_eq_ite {n : ℕ} (l : Fin n) (v : X) (x : Fin (n + 1) → X)
    (t : Fin (n + 2)) :
    Fin.insertNth (α := fun _ => X) l.succ.castSucc v x t =
      if h : (t : ℕ) < l + 1 then x ⟨t, by omega⟩
      else if (t : ℕ) = l + 1 then v else x ⟨t - 1, by omega⟩ := by
  rcases lt_trichotomy t l.succ.castSucc with h | h | h
  · rw [Fin.insertNth_apply_below h]
    have h' : (t : ℕ) < l + 1 := by simpa [Fin.lt_def] using h
    simp [h']
    rfl
  · subst h
    simp
  · rw [Fin.insertNth_apply_above h]
    have h' : l + 1 < (t : ℕ) := by simpa [Fin.lt_def] using h
    simp [show ¬ (t : ℕ) < l + 1 by omega, show (t : ℕ) ≠ l + 1 by omega]
    rfl

omit [Fintype X] [DecidableEq X] in
/-- Inserting a vertex keeps the starting point of a path. -/
private theorem insertNth_apply_zero {n : ℕ} (l : Fin n) (v : X) (x : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) l.succ.castSucc v x 0 = x 0 := by
  rw [insertNth_apply_eq_ite]
  simp

omit [Fintype X] [DecidableEq X] in
/-- Inserting a vertex keeps the end point of a path. -/
private theorem insertNth_apply_last {n : ℕ} (l : Fin n) (v : X) (x : Fin (n + 1) → X) :
    Fin.insertNth (α := fun _ => X) l.succ.castSucc v x (Fin.last (n + 1)) = x (Fin.last n) := by
  rw [insertNth_apply_eq_ite]
  simp only [Fin.val_last, show ¬ n + 1 < (l : ℕ) + 1 by omega,
    show n + 1 ≠ (l : ℕ) + 1 by omega, dite_false, ite_false, Nat.add_sub_cancel]
  rfl

omit [DecidableEq X] in
/-- Along the path obtained by inserting `v` after `xₗ`, contracting the `l`-th pair of entries
gives the entries of the contracted tuple along `x`, with the entry `F_{l} xₗ v * F_{l+1} v xₗ₊₁`
in position `l`. -/
private theorem contractNth_insertNth {n : ℕ} (l : Fin n) (F : Fin (n + 1) → Matrix X X A)
    (x : Fin (n + 1) → X) (v : X) :
    Fin.contractNth l.castSucc (· * ·) (fun k => F k
        (Fin.insertNth (α := fun _ => X) l.succ.castSucc v x k.castSucc)
        (Fin.insertNth (α := fun _ => X) l.succ.castSucc v x k.succ)) =
      Function.update (fun k => Fin.contractNth l.castSucc (· * ·) F k (x k.castSucc) (x k.succ))
        l (F l.castSucc (x l.castSucc) v * F l.succ v (x l.succ)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) l with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Function.update_of_ne (Fin.ne_of_lt h),
      Fin.contractNth_apply_of_lt _ _ _ _ h]
    simp only [insertNth_apply_eq_ite, Fin.val_castSucc, Fin.val_succ,
      show (k : ℕ) < l + 1 by omega, show (k : ℕ) + 1 < l + 1 by omega, dite_true]
    rfl
  · have hk : k = l := Fin.ext h
    subst hk
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self]
    simp only [insertNth_apply_eq_ite, Fin.val_castSucc, Fin.val_succ, Nat.lt_irrefl, dite_false,
      ite_true, show (k : ℕ) < k + 1 by omega, show ¬ ((k : ℕ) + 1 + 1 < k + 1) by omega,
      show (k : ℕ) + 1 + 1 ≠ k + 1 by omega, dite_true]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Function.update_of_ne (Fin.ne_of_gt h),
      Fin.contractNth_apply_of_gt _ _ _ _ h]
    simp only [insertNth_apply_eq_ite, Fin.val_castSucc, Fin.val_succ,
      show ¬ ((k : ℕ) + 1 < l + 1) by omega, show ¬ ((k : ℕ) + 1 + 1 < l + 1) by omega,
      show (k : ℕ) + 1 ≠ l + 1 by omega, show (k : ℕ) + 1 + 1 ≠ l + 1 by omega, dite_false,
      ite_false]
    rfl

/-- The product terms of the matrix module are sums over paths. -/
private theorem stasheffMul_matrixAct (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedStasheffMul (Mm.matrixAct X) n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then
        ungradedStasheffMul Mm.act n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [ungradedStasheffMul_succ, Finset.sum_apply, matrixAct_apply]
    have hR (w : Fin (n + 2) → X) :
        (if w (Fin.last (n + 1)) = z then ∑ l : Fin n,
          Mm.act n (Fin.contractNth l.castSucc (· * ·) fun k => F k (w k.castSucc) (w k.succ))
            (φ (w 0)) else 0) =
        ∑ l : Fin n, if w (Fin.last (n + 1)) = z then
          Mm.act n (Fin.contractNth l.castSucc (· * ·) fun k => F k (w k.castSucc) (w k.succ))
            (φ (w 0)) else 0 := by
      split_ifs <;> simp
    rw [sum_congr rfl fun w _ => hR w]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    refine Eq.trans ?_ (Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => X) l.succ.castSucc) _ _
      fun _ => rfl)
    rw [Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    simp only [Fin.insertNthEquiv_apply, contractNth_insertNth, insertNth_apply_zero,
      insertNth_apply_last]
    split_ifs
    · have hx : (fun k => Fin.contractNth l.castSucc (· * ·) F k (x k.castSucc) (x k.succ)) =
          Function.update (fun k => Fin.contractNth l.castSucc (· * ·) F k (x k.castSucc)
            (x k.succ)) l (∑ v, F l.castSucc (x l.castSucc) v * F l.succ v (x l.succ)) := by
        rw [eq_comm, Function.update_eq_self_iff, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
          Matrix.mul_apply]
      conv_lhs => rw [hx]
      rw [MultilinearMap.map_update_sum, LinearMap.sum_apply]
    · simp

/-- The **matrix module**: the row vectors `X → M` form an ungraded `A∞` right module over the
matrix algebra `Matrix X X A`, with the entrywise differential and the operations
`TauCeti.UngradedAInfinityRightModule.matrixAct`. -/
noncomputable def matrix :
    UngradedAInfinityRightModule (d.mapMatrix : Matrix X X A →ₗ[R] Matrix X X A) (X → M) where
  act := Mm.matrixAct X
  stasheff n F φ := by
    funext z
    rw [Pi.add_apply, Pi.add_apply, Pi.zero_apply, stasheffComp_matrixAct, stasheffDiff_matrixAct,
      stasheffMul_matrixAct, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun x _ => ?_
    split_ifs
    · exact Mm.stasheff n _ _
    · simp

@[simp]
theorem matrix_act : (Mm.matrix X).act = Mm.matrixAct X :=
  (rfl)

end Matrix

end UngradedAInfinityRightModule

/-! ### Differential modules as `A∞` modules -/

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The right action of `A` on `M`, as an `R`-linear map to the `R`-linear endomorphisms. -/
private noncomputable def rightAct : A →ₗ[R] M →ₗ[R] M where
  toFun a :=
    { toFun := fun m => op a • m
      map_add' := smul_add _
      map_smul' := fun r m => (smul_comm r (op a) m).symm }
  map_add' a b := by ext m; simp [add_smul]
  map_smul' r a := by ext m; simp [op_smul, smul_assoc]

/-- The operations of a differential right module: `m₁ = dM`, `m₂` is the right action and
`m_{n+1} = 0` for `n ≥ 2`. -/
private noncomputable def dgAct (dM : M →ₗ[R] M) :
    (n : ℕ) → MultilinearMap R (fun _ : Fin n => A) (M →ₗ[R] M)
  | 0 => MultilinearMap.constOfIsEmpty R _ dM
  | 1 => MultilinearMap.ofSubsingleton R A (M →ₗ[R] M) 0 rightAct
  | _ + 2 => 0

private theorem dgAct_apply_of_eq_zero (dM : M →ₗ[R] M) {n : ℕ} (hn : n = 0) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = dM m := by
  subst hn
  rfl

private theorem dgAct_apply_of_eq_one (dM : M →ₗ[R] M) {n : ℕ} (hn : n = 1) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = op (a ⟨0, by omega⟩) • m := by
  subst hn
  rfl

private theorem dgAct_eq_zero_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) :
    dgAct (R := R) (A := A) dM n = 0 := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

private theorem dgAct_apply_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = 0 := by
  rw [dgAct_eq_zero_of_two_le dM hn]
  rfl

variable {d : A →ₗ[R] A} {dM : M →ₗ[R] M}

/-- **A differential right module is an `A∞` module**, over a ring of characteristic two: its
operations are `m₁ = dM`, the right action `m₂(m, a) = m * a` and `m_{n+1} = 0` for `n ≥ 2`.
The `A∞` relation of length one is the Leibniz rule, that of length two is associativity of the
action, and the others hold trivially. -/
noncomputable def toUngradedAInfinityRightModule [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) : UngradedAInfinityRightModule d M where
  act := dgAct dM
  stasheff n a m := by
    have h2 (x : M) : x + x = 0 := add_self_eq_zero_of_charTwo R x
    match n with
    | 0 =>
      simp [ungradedStasheffComp, ungradedStasheffDiff, dgAct_apply_of_eq_zero, hM.map_map]
    | 1 =>
      simp only [ungradedStasheffComp, ungradedStasheffDiff, Fin.sum_univ_succ,
        Fin.sum_univ_zero, ungradedStasheffMul_succ, dgAct_apply_of_eq_zero,
        dgAct_apply_of_eq_one, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.sub_self, add_zero,
        Fin.zero_eta, Function.update_self, hM.map_smul, Fin.isValue]
      calc _ = (op (a 0) • dM m + op (a 0) • dM m) + (op (d (a 0)) • m + op (d (a 0)) • m) := by
            abel
        _ = 0 := by rw [h2, h2, add_zero]
    | 2 =>
      simp only [ungradedStasheffComp, ungradedStasheffDiff, Fin.sum_univ_succ,
        Fin.sum_univ_zero, ungradedStasheffMul_succ, dgAct_apply_of_eq_zero,
        dgAct_apply_of_eq_one, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Fin.contractNth,
        Fin.isValue, dgAct_apply_of_two_le dM (le_refl 2), map_zero, add_zero, zero_add,
        Fin.castSucc_zero, lt_irrefl, ite_false, ite_true,
        Fin.zero_eta, Fin.mk_one]
      rw [Fin.succ_zero_eq_one, op_mul, mul_smul, h2]
    | n + 3 =>
      have hcomp : ungradedStasheffComp (dgAct dM) (n + 3) a m = 0 := sum_eq_zero fun k _ => by
        rcases le_or_gt 2 (k : ℕ) with hk | hk
        · rw [dgAct_apply_of_two_le dM hk, map_zero]
        · exact dgAct_apply_of_two_le dM (by omega) _ _
      have hdiff : ungradedStasheffDiff (dgAct dM) d (n + 3) a m = 0 :=
        sum_eq_zero fun l _ => dgAct_apply_of_two_le dM (by omega) _ _
      have hmul : ungradedStasheffMul (dgAct dM) (n + 3) a m = 0 := by
        rw [ungradedStasheffMul_succ]
        exact sum_eq_zero fun l _ => dgAct_apply_of_two_le dM (by omega) _ _
      rw [hcomp, hdiff, hmul, add_zero, add_zero]

/-- The operation `m₁` of a differential module viewed as an `A∞` module is its differential. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_zero [CharP R 2] (hM : IsUngradedDGRightModule d dM)
    (a : Fin 0 → A) (m : M) : hM.toUngradedAInfinityRightModule.act 0 a m = dM m :=
  (rfl)

/-- The operation `m₂` of a differential module viewed as an `A∞` module is its right action. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_one [CharP R 2] (hM : IsUngradedDGRightModule d dM)
    (a : Fin 1 → A) (m : M) : hM.toUngradedAInfinityRightModule.act 1 a m = op (a 0) • m :=
  (rfl)

/-- The operations `m_{n+1}`, `n ≥ 2`, of a differential module viewed as an `A∞` module vanish. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_add_two [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) (n : ℕ) :
    hM.toUngradedAInfinityRightModule.act (n + 2) = 0 :=
  (rfl)

end IsUngradedDGRightModule

end TauCeti
