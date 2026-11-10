/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Ungraded
import Mathlib.Algebra.BigOperators.Intervals
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Data.Fin.StrictMono
import TauCeti.Data.Fin.Tuple.Basic

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
  length `n + 1`. For an arbitrary `β` the two combine into the curvature `d β + β * β`, and
  `∂^β ∘ ∂^β` is the sum of the operations with the curvature inserted once
  (`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential_eq_sum`).
* **Matrices.** The row vectors `X → M`, for a finite type `X`, form an `A∞` module over the
  matrix algebra `Matrix X X A` with the entrywise differential
  (`TauCeti.UngradedAInfinityRightModule.matrix`): `m_{n+1}(φ, F₁, …, Fₙ)` has `z`-component the
  sum, over the paths `x₀ → x₁ → ⋯ → xₙ = z` in `X`, of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`
  (`TauCeti.UngradedAInfinityRightModule.matrixAct`). The composite terms concatenate paths and the
  product terms insert a vertex into a path. For block upper-triangular matrices on `X ⊕ Y`, paths
  never return from `Y` to `X`; this restricts the operations to `X` and to `Y`
  (`TauCeti.UngradedAInfinityRightModule.matrixAct_apply_inl`,
  `TauCeti.UngradedAInfinityRightModule.matrixAct_sumElim_zero_apply_inr`), and a path from `X` to
  `Y` crosses the off-diagonal block exactly once
  (`TauCeti.UngradedAInfinityRightModule.sum_matrixAct_update_fromBlocks_apply_inr`).

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

* `TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential_eq_sum`: the
  square of the twisted differential inserts the curvature once.
* `TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential`: the twisted
  differential of a Maurer–Cartan element squares to zero.
* `TauCeti.UngradedAInfinityRightModule.matrixAct_apply`: the components of the matrix operations
  are sums over paths.
* `TauCeti.UngradedAInfinityRightModule.matrixAct_eq_zero_of_act_eq_zero` and
  `TauCeti.UngradedAInfinityRightModule.matrixAct_eq_zero_of_lt`: the matrix operations vanish
  when those of `M` do, and along matrices whose nonzero entries strictly increase a bounded
  height.
* `TauCeti.UngradedAInfinityRightModule.sum_matrixAct_update_fromBlocks_apply_inr`: along block
  upper-triangular matrices, paths from `X` to `Y` see the off-diagonal block exactly once.

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

theorem ungradedStasheffComp_def (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffComp act n a m =
      ∑ k : Fin (n + 1), act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) :=
  (rfl)

/-- The **differential terms** of the `A∞` relation of length `n`:
`∑_l m_{n+1}(m, a₁, …, d aₗ, …, aₙ)`. -/
noncomputable def ungradedStasheffDiff (d : A →ₗ[R] A) (n : ℕ) (a : Fin n → A) (m : M) : M :=
  ∑ l : Fin n, act n (Function.update a l (d (a l))) m

theorem ungradedStasheffDiff_def (d : A →ₗ[R] A) (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffDiff act d n a m = ∑ l : Fin n, act n (Function.update a l (d (a l))) m :=
  (rfl)

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

theorem twistedDifferential_def (β : A) :
    Mm.twistedDifferential β = ∑ᶠ n, Mm.act n fun _ => β :=
  (rfl)

/-- When `m_{n+1}(·, β, …, β)` vanishes for `n ≥ K`, the twisted differential is the sum of the
first `K` operations. -/
theorem twistedDifferential_eq_sum {β : A} {K : ℕ}
    (h : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0) :
    Mm.twistedDifferential β = ∑ n ∈ range K, Mm.act n fun _ => β := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simpa using not_le.mp (mt (h n) hn)

/-- The `A∞` relations of length at most `N` along a constant tuple `β`, over a ring of
characteristic two, summed: the differential terms of length `n` and the product terms of length
`n + 1` combine into insertions of the curvature `d β + β * β`, and the composite terms add up to
these insertions together with the differential terms of length `N`. -/
private theorem sum_sum_act_act_const [CharP R 2] (β : A) (N : ℕ) (m : M) :
    ∑ n ∈ range (N + 1), ∑ k ∈ range (n + 1),
        Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m) =
      ∑ n ∈ range N, ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (d β + β * β)) m +
        ∑ l : Fin N, Mm.act N (Function.update (fun _ => β) l (d β)) m := by
  set D : ℕ → M := fun n => ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (d β)) m
    with hD
  set P : ℕ → M := fun n => ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (β * β)) m
    with hP
  have h := Finset.sum_eq_zero (s := range (N + 1)) fun n _ => Mm.stasheff n (fun _ => β) m
  rw [sum_add_distrib, sum_add_distrib, sum_range_succ' (fun n =>
    ungradedStasheffMul Mm.act n (fun _ => β) m), sum_range_succ (fun n =>
    ungradedStasheffDiff Mm.act d n (fun _ => β) m)] at h
  have hcomp (n : ℕ) : ungradedStasheffComp Mm.act n (fun _ => β) m =
      ∑ k ∈ range (n + 1), Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m) :=
    Fin.sum_univ_eq_sum_range (fun k => Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m))
      (n + 1)
  have hdiff (n : ℕ) : ungradedStasheffDiff Mm.act d n (fun _ => β) m = D n := by
    simp only [ungradedStasheffDiff, hD]
  have hmul (n : ℕ) : ungradedStasheffMul Mm.act (n + 1) (fun _ => β) m = P n := by
    simp only [ungradedStasheffMul_succ, Fin.contractNth_castSucc_const, hP]
  have hDP : ∑ n ∈ range N, ∑ l : Fin n,
      Mm.act n (Function.update (fun _ => β) l (d β + β * β)) m =
        ∑ n ∈ range N, D n + ∑ n ∈ range N, P n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [hD, hP, ← sum_add_distrib, MultilinearMap.map_update_add, LinearMap.add_apply]
  simp only [hcomp, hdiff, hmul, ungradedStasheffMul_zero, add_zero] at h
  rw [hDP]
  refine (add_eq_zero_iff_eq_of_charTwo R).mp ?_
  rw [← h]
  abel

/-- **The square of the twisted differential is the insertion of the curvature.** Over a ring of
characteristic two, suppose that `m_{n+1}` vanishes for `n ≥ K` on every tuple of elements of a set
`U` containing `β`, `d β` and the curvature `d β + β * β`. Then `∂^β ∘ ∂^β` is the sum, over
`n < K` and the `n` slots, of `m_{n+1}(·, β, …, β, d β + β * β, β, …, β)`, the curvature inserted
once. In particular `∂^β` squares to zero when `β` is a Maurer–Cartan element
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential_twistedDifferential`). -/
theorem twistedDifferential_twistedDifferential_eq_sum [CharP R 2] {β : A} {U : Set A}
    (hβU : β ∈ U) (hdβU : d β ∈ U) (hcU : d β + β * β ∈ U) {K : ℕ}
    (hU : ∀ n, K ≤ n → ∀ u : Fin n → A, (∀ l, u l ∈ U) → Mm.act n u = 0) (m : M) :
    Mm.twistedDifferential β (Mm.twistedDifferential β m) =
      ∑ n ∈ range K, ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (d β + β * β)) m := by
  have hupd {n : ℕ} (l : Fin n) {c : A} (hc : c ∈ U) (t : Fin n) :
      Function.update (fun _ => β) l c t ∈ U := by
    by_cases ht : t = l
    · subst ht; simpa using hc
    · simpa [Function.update_of_ne ht] using hβU
  have hc : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0 := fun n hn => hU n hn _ fun _ => hβU
  set f : ℕ → ℕ → M := fun i j => Mm.act j (fun _ => β) (Mm.act i (fun _ => β) m) with hf
  -- The relations of length at most `2 K` leave the curvature insertions of length less than
  -- `K`, and the differential terms of length `2 K`, which vanish.
  have hrel : ∑ n ∈ range (2 * K + 1), ∑ k ∈ range (n + 1), f k (n - k) =
      ∑ n ∈ range K, ∑ l : Fin n, Mm.act n (Function.update (fun _ => β) l (d β + β * β)) m := by
    have hlast : ∑ l : Fin (2 * K),
        Mm.act (2 * K) (Function.update (fun _ => β) l (d β)) m = 0 :=
      sum_eq_zero fun l _ => by rw [hU _ (by omega) _ (hupd l hdβU), LinearMap.zero_apply]
    rw [Mm.sum_sum_act_act_const, hlast, add_zero]
    refine (sum_subset (range_subset_range.mpr (by omega)) fun n _ hn => ?_).symm
    exact sum_eq_zero fun l _ => by
      rw [hU n (by simpa using hn) _ (hupd l hcU), LinearMap.zero_apply]
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
    _ = _ := by rw [← sum_range_diag_flip, hrel]

/-- **The twisted differential squares to zero.** Let `β` be a Maurer–Cartan element,
`d β + β * β = 0`, over a ring of characteristic two, and suppose that `m_{n+1}` vanishes for
`n ≥ K` on every tuple of elements of a set `U` containing `β` and `β * β`. Then
`∂^β ∘ ∂^β = 0`. For `U` the whole algebra this is the case of a module whose operations vanish
from some arity on. -/
theorem twistedDifferential_twistedDifferential [CharP R 2] {β : A} (hβ : d β + β * β = 0)
    {U : Set A} (hβU : β ∈ U) (hββU : β * β ∈ U) {K : ℕ}
    (hU : ∀ n, K ≤ n → ∀ u : Fin n → A, (∀ l, u l ∈ U) → Mm.act n u = 0) (m : M) :
    Mm.twistedDifferential β (Mm.twistedDifferential β m) = 0 := by
  -- A tuple with a zero entry is killed by multilinearity, so `0` may join `U`.
  have hU' : ∀ n, K ≤ n → ∀ u : Fin n → A, (∀ l, u l ∈ insert 0 U) → Mm.act n u = 0 := by
    intro n hn u hu
    by_cases h0 : ∃ l, u l = 0
    · obtain ⟨l, hl⟩ := h0
      exact (Mm.act n).map_coord_zero l hl
    · push Not at h0
      exact hU n hn u fun l => (hu l).resolve_left (h0 l)
  have hdβ : d β = β * β := (add_eq_zero_iff_eq_of_charTwo R).mp hβ
  rw [Mm.twistedDifferential_twistedDifferential_eq_sum (Set.mem_insert_of_mem _ hβU)
    (hdβ ▸ Set.mem_insert_of_mem _ hββU) (hβ ▸ Set.mem_insert _ _) hU' m, hβ]
  simp

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

/-- If the operation `m_{n+1}` of `M` vanishes, so does that of the matrix module. -/
theorem matrixAct_eq_zero_of_act_eq_zero {n : ℕ} (h : Mm.act n = 0) : Mm.matrixAct X n = 0 := by
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  simp [Mm.matrixAct_apply, h]

/-- **Operations of the matrix module along height-increasing matrices vanish.** If a height
`h` on `X` strictly increases along every nonzero entry of each of `F₁, …, Fₙ`, and `n` exceeds
every height, then `m_{n+1}(·, F₁, …, Fₙ) = 0`: every path `x₀ → ⋯ → xₙ` meets a zero entry. -/
theorem matrixAct_eq_zero_of_lt (h : X → ℕ) {n : ℕ} (hn : univ.sup h < n)
    {F : Fin n → Matrix X X A} (hF : ∀ l x y, F l x y ≠ 0 → h x < h y) :
    Mm.matrixAct X n F = 0 := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  simp only [Mm.matrixAct_apply, LinearMap.zero_apply, Pi.zero_apply]
  refine sum_eq_zero fun x _ => ?_
  -- Some entry along the path `x` vanishes, since the height cannot increase `n` times.
  obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
    by_contra hne
    push Not at hne
    have hx : StrictMono (h ∘ x) := Fin.strictMono_iff_lt_succ.mpr fun l => hF l _ _ (hne l)
    have := hx.add_sub_le_nat (Fin.zero_le (Fin.last n))
    simp only [Function.comp_apply, Fin.val_last, Fin.val_zero, Nat.sub_zero] at this
    have := le_sup (f := h) (mem_univ (x (Fin.last n)))
    omega
  rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply, ite_self]

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
  rw [matrixAct_apply, sum_congr rfl fun y _ => hy y, sum_comm,
    Fin.sum_sum_ite_apply_last_eq_apply_zero h]
  refine sum_congr rfl fun w _ => ?_
  have hlast : w ⟨i + (Fin.last j : ℕ), by simp; omega⟩ = w (Fin.last n) :=
    congrArg w (Fin.ext (by simp [h]))
  have hzero : w ⟨((0 : Fin (i + 1)) : ℕ), by simp⟩ = w 0 := congrArg w (Fin.ext (by simp))
  simp only [hlast, hzero, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]

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
  -- Updating one matrix of a tuple updates one entry along every path.
  have hupd (x : Fin (n + 1) → X) (l : Fin n) (G : Matrix X X A) :
      (fun t => Function.update F l G t (x t.castSucc) (x t.succ)) =
        Function.update (fun t => F t (x t.castSucc) (x t.succ)) l (G (x l.castSucc) (x l.succ)) :=
    funext (Function.apply_update (fun t (G : Matrix X X A) => G (x t.castSucc) (x t.succ)) F l G)
  simp only [ungradedStasheffDiff, Finset.sum_apply, matrixAct_apply, hupd,
    LinearMap.mapMatrix_apply, Matrix.map_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

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
    have hp₀ : l.succ.castSucc ≠ 0 := by simp [Fin.ext_iff]
    have hpl : l.succ.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last _).ne
    simp only [Fin.insertNthEquiv_apply, Fin.contractNth_castSucc_insertNth_succ_castSucc (f := F),
      Fin.insertNth_apply_zero_of_ne_zero hp₀, Fin.insertNth_apply_last_of_ne_last hpl]
    split_ifs
    · have hx : (fun k => Fin.contractNth l.castSucc (· * ·) F k (x k.castSucc) (x k.succ)) =
          Function.update (fun k => F (l.succ.succAbove k) (x k.castSucc) (x k.succ)) l
            (∑ v, F l.castSucc (x l.castSucc) v * F l.succ v (x l.succ)) := by
        funext k
        rcases eq_or_ne k l with rfl | hk
        · rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl, Matrix.mul_apply]
        · rw [Function.update_of_ne hk]
          rcases hk.lt_or_gt with h | h
          · rw [Fin.contractNth_apply_of_lt _ _ _ _ h,
              Fin.succAbove_of_castSucc_lt _ _ (by simpa using h.le)]
          · rw [Fin.contractNth_apply_of_gt _ _ _ _ h,
              Fin.succAbove_of_le_castSucc _ _ (by simpa using h)]
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

/-! ### Block upper-triangular matrices -/

section Block

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **Restricting the matrix module to the first summand.** If no matrix `Fᵢ` on `X ⊕ Y` has a
nonzero entry from `Y` to `X`, then no path ending in `X` passes through `Y`, so the
`X`-components of `m_{n+1}(φ, F₁, …, Fₙ)` are those of the operation of the matrix module of `X`
on the `X`-components of `φ` and the `X × X` blocks of the `Fᵢ`. -/
theorem matrixAct_apply_inl {n : ℕ} (F : Fin n → Matrix (X ⊕ Y) (X ⊕ Y) A)
    (hF : ∀ l a b, F l (Sum.inr a) (Sum.inl b) = 0) (φ : X ⊕ Y → M) (z : X) :
    Mm.matrixAct (X ⊕ Y) n F φ (Sum.inl z) =
      Mm.matrixAct X n (fun l => (F l).toBlocks₁₁) (φ ∘ Sum.inl) z := by
  rw [matrixAct_apply, matrixAct_apply]
  refine (Fintype.sum_of_injective (fun x => Sum.inl ∘ x)
    (fun x y h => funext fun k => Sum.inl_injective (congrFun h k)) _ _ (fun x hx => ?_)
    fun x => by simp [Matrix.toBlocks₁₁]).symm
  split_ifs with hz
  · -- A path ending in `X` and meeting `Y` steps from `Y` to `X` somewhere.
    obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
      by_contra! hne
      have hleft (k : Fin (n + 1)) : (x k).isLeft := by
        induction k using Fin.reverseInduction with
        | last => rw [hz]; rfl
        | cast k ih =>
          rcases hxk : x k.castSucc with a | b
          · rfl
          · rcases hxs : x k.succ with a' | b'
            · exact absurd (by rw [hxk, hxs]; exact hF k b a') (hne k)
            · rw [hxs] at ih; simp at ih
      exact hx ⟨fun k => (x k).getLeft (hleft k), funext fun k => by simp⟩
    rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply]
  · rfl

/-- **Restricting the matrix module to the second summand.** If no matrix `Fᵢ` on `X ⊕ Y` has a
nonzero entry from `Y` to `X`, then a path starting in `Y` stays in `Y`, so on row vectors
supported on `Y` the `Y`-components of `m_{n+1}(·, F₁, …, Fₙ)` are those of the operation of the
matrix module of `Y` along the `Y × Y` blocks of the `Fᵢ`. -/
theorem matrixAct_sumElim_zero_apply_inr {n : ℕ} (F : Fin n → Matrix (X ⊕ Y) (X ⊕ Y) A)
    (hF : ∀ l a b, F l (Sum.inr a) (Sum.inl b) = 0) (ψ : Y → M) (z : Y) :
    Mm.matrixAct (X ⊕ Y) n F (Sum.elim 0 ψ) (Sum.inr z) =
      Mm.matrixAct Y n (fun l => (F l).toBlocks₂₂) ψ z := by
  rw [matrixAct_apply, matrixAct_apply]
  refine (Fintype.sum_of_injective (fun x => Sum.inr ∘ x)
    (fun x y h => funext fun k => Sum.inr_injective (congrFun h k)) _ _ (fun x hx => ?_)
    fun x => by simp [Matrix.toBlocks₂₂]).symm
  split_ifs with hz
  · rcases hx0 : x 0 with a | b
    · simp
    -- A path starting in `Y` and meeting `X` steps from `Y` to `X` somewhere.
    obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
      by_contra! hne
      have hright (k : Fin (n + 1)) : (x k).isRight := by
        induction k using Fin.induction with
        | zero => rw [hx0]; rfl
        | succ k ih =>
          rcases hxs : x k.succ with a' | b'
          · rcases hxk : x k.castSucc with a | b''
            · rw [hxk] at ih; simp at ih
            · exact absurd (by rw [hxk, hxs]; exact hF k b'' a') (hne k)
          · rfl
      exact hx ⟨fun k => (x k).getRight (hright k), funext fun k => by simp⟩
    rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply]
  · rfl

/-- **Inserting an off-diagonal block.** Let `δ` and `δ'` be matrices on `X` and `Y`, and `F`
and `G` matrices from `X` to `Y`. On row vectors supported on `X`, the `Y`-components of
`m_{n+1}(·, C_G, …, C_G)` for the block upper-triangular matrix `C_G = fromBlocks δ G 0 δ'` are
the sum, over the slots `l`, of `m_{n+1}(·, C_F, …, C_F, fromBlocks 0 G 0 0, C_F, …, C_F)` with
`fromBlocks 0 G 0 0` in slot `l`: a path from `X` to `Y` steps from `X` to `Y` exactly once,
through an entry of `G`, while its other steps see only `δ` and `δ'`. -/
theorem sum_matrixAct_update_fromBlocks_apply_inr {n : ℕ} (δ : Matrix X X A) (δ' : Matrix Y Y A)
    (F G : Matrix X Y A) (φ : X → M) (z : Y) :
    ∑ l : Fin n, Mm.matrixAct (X ⊕ Y) n
        (Function.update (fun _ => Matrix.fromBlocks δ F 0 δ') l (Matrix.fromBlocks 0 G 0 0))
        (Sum.elim φ 0) (Sum.inr z) =
      Mm.matrixAct (X ⊕ Y) n (fun _ => Matrix.fromBlocks δ G 0 δ') (Sum.elim φ 0) (Sum.inr z) := by
  set C : Matrix (X ⊕ Y) (X ⊕ Y) A := Matrix.fromBlocks δ F 0 δ'
  set E : Matrix (X ⊕ Y) (X ⊕ Y) A := Matrix.fromBlocks 0 G 0 0
  -- Updating one matrix of a tuple updates one entry along every path.
  have hupd (x : Fin (n + 1) → X ⊕ Y) (l : Fin n) :
      (fun t => Function.update (fun _ => C) l E t (x t.castSucc) (x t.succ)) =
        Function.update (fun t => C (x t.castSucc) (x t.succ)) l (E (x l.castSucc) (x l.succ)) :=
    funext (Function.apply_update (fun t (P : Matrix (X ⊕ Y) (X ⊕ Y) A) =>
      P (x t.castSucc) (x t.succ)) (fun _ => C) l E)
  simp only [matrixAct_apply, hupd]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs with hz
  swap
  · simp
  rcases hx0 : x 0 with a | b
  swap
  · simp
  by_cases hback : ∃ l : Fin n, (x l.castSucc).isRight ∧ (x l.succ).isLeft
  · -- A step from `Y` back to `X` sees a zero entry of every matrix involved.
    obtain ⟨l, h₁, h₂⟩ := hback
    obtain ⟨b, hb⟩ := Sum.isRight_iff.mp h₁
    obtain ⟨a', ha'⟩ := Sum.isLeft_iff.mp h₂
    rw [(Mm.act n).map_coord_zero l (by simp [hb, ha']), LinearMap.zero_apply]
    refine sum_eq_zero fun l' _ => ?_
    rw [(Mm.act n).map_coord_zero l ?_, LinearMap.zero_apply]
    rcases eq_or_ne l l' with rfl | hne
    · simp [E, hb, ha']
    · simp [Function.update_of_ne hne, C, hb, ha']
  push Not at hback
  obtain ⟨l₀, ⟨h₁, h₂⟩, huniq⟩ := Fin.existsUnique_isLeft_castSucc_and_isRight_succ x
    (by simp [hx0]) (by simp [hz]) fun l h => by
      by_contra h'
      exact hback l h (by simpa using h')
  -- Away from the crossing `l₀` the entries of `C_F`, `C_G` and `E` are the diagonal blocks.
  have hoff (l : Fin n) (hl : l ≠ l₀) :
      E (x l.castSucc) (x l.succ) = 0 ∧
        C (x l.castSucc) (x l.succ) = Matrix.fromBlocks δ G 0 δ' (x l.castSucc) (x l.succ) := by
    rcases hxl : x l.castSucc with a | b <;> rcases hxs : x l.succ with a' | b'
    · simp [E, C]
    · exact absurd (huniq l ⟨by simp [hxl], by simp [hxs]⟩) hl
    · simp [E, C]
    · simp [E, C]
  rw [sum_eq_single l₀ (fun l _ hl => by
      rw [(Mm.act n).map_coord_zero l (by rw [Function.update_self]; exact (hoff l hl).1),
        LinearMap.zero_apply]) (by simp)]
  congr 2
  funext t
  rcases eq_or_ne t l₀ with rfl | ht
  · obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp h₁
    obtain ⟨b, hb⟩ := Sum.isRight_iff.mp h₂
    simp [E, ha, hb]
  · rw [Function.update_of_ne ht, (hoff t ht).2]

end Block

end UngradedAInfinityRightModule

/-! ### Differential modules as `A∞` modules -/

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The operations of a differential right module: `m₁ = dM`, `m₂` is the right action and
`m_{n+1} = 0` for `n ≥ 2`. -/
private noncomputable def dgAct (dM : M →ₗ[R] M) :
    (n : ℕ) → MultilinearMap R (fun _ : Fin n => A) (M →ₗ[R] M)
  | 0 => MultilinearMap.constOfIsEmpty R _ dM
  | 1 => MultilinearMap.ofSubsingleton R A (M →ₗ[R] M) 0
    ((Algebra.lsmul R R M).toLinearMap ∘ₗ (opLinearEquiv R).toLinearMap)
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
      have hmul : Fin.contractNth 0 (· * ·) a 0 = a 0 * a 1 := by
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero, Fin.succ_zero_eq_one]
      simp only [ungradedStasheffComp, ungradedStasheffDiff, Fin.sum_univ_succ,
        Fin.sum_univ_zero, ungradedStasheffMul_succ, dgAct_apply_of_eq_zero,
        dgAct_apply_of_eq_one, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Fin.isValue,
        dgAct_apply_of_two_le dM (le_refl 2), map_zero, add_zero, zero_add, Fin.zero_eta, hmul,
        Fin.castSucc_zero, Fin.mk_one]
      rw [op_mul, mul_smul, h2]
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
