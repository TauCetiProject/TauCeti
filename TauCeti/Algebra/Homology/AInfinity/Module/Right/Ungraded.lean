/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import TauCeti.LinearAlgebra.Multilinear.Split
public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Ungraded
import Mathlib.Algebra.BigOperators.Intervals
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Fin.StrictMono
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Ungraded `A∞` right modules over a differential algebra

Let `(A, d)` be an algebra with a linear map `d`, thought of as an ungraded differential algebra
(`TauCeti.IsUngradedDGAlgebra`). An **ungraded `A∞` right module** over it is a module `M` with
operations `m_{n+1} : M ⊗ A^{⊗ n} → M` for every `n ≥ 0`, here
`act n : MultilinearMap (RingHom.id R) (Fin n → A) (M →ₗ[R]
M)`, satisfying for every `m` and `a₁, …, aₙ` the
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
operations `m_{n+1}` vanish for `n ≥ 2`, over a ring of characteristic two; see
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded.DG`.

The constructions below apply to families of operations `f_{n+1} : M ⊗ A^{⊗ n} → M'`, here
`(n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')`, such as the
operations of a module or a morphism of modules. Two families compose
(`TauCeti.ungradedFamilyComp`) by
`(g ∘ f)_{n+1}(m, a₁, …, aₙ) = ∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`. This
composition is associative (`TauCeti.ungradedFamilyComp_assoc`), with the identity family
`TauCeti.ungradedFamilyId` as unit. It needs no multiplication on `A`, so the families are developed
over a commutative semiring and additive commutative monoids.

Two constructions are developed for modules, together with strict units.

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
  More generally, the twist `f^β = ∑ₙ f_{n+1}(·, β, …, β)` of a family
  (`TauCeti.ungradedTwistedMap`) takes composites to composites
  (`TauCeti.ungradedTwistedMap_ungradedFamilyComp`).
* **Matrices.** The row vectors `X → M`, for a finite type `X`, form an `A∞` module over the
  matrix algebra `Matrix X X A` with the entrywise differential
  (`TauCeti.UngradedAInfinityRightModule.matrix`): `m_{n+1}(φ, F₁, …, Fₙ)` has `z`-component the
  sum, over the paths `x₀ → x₁ → ⋯ → xₙ = z` in `X`, of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`
  (`TauCeti.UngradedAInfinityRightModule.matrixAct`). The composite terms concatenate paths and the
  product terms insert a vertex into a path. If no matrix has an entry into the range of an
  embedding `Y → X` from outside it, the components of the operations on that range are those of
  the matrix module of `Y` (`TauCeti.UngradedAInfinityRightModule.matrixAct_apply_of_injective`);
  if no matrix has an entry out of the range, the same holds on row vectors supported on the range
  (`TauCeti.UngradedAInfinityRightModule.matrixAct_apply_of_injective_of_forall_notMem_range`).
  For block upper-triangular matrices on `X ⊕ Y`, paths never return from `Y` to `X`; this
  restricts the operations to `X` and to `Y`
  (`TauCeti.UngradedAInfinityRightModule.matrixAct_apply_inl`,
  `TauCeti.UngradedAInfinityRightModule.matrixAct_sumElim_zero_apply_inr`), and a path from `X` to
  `Y` crosses the off-diagonal block exactly once
  (`TauCeti.UngradedAInfinityRightModule.sum_matrixAct_update_fromBlocks_apply_inr`). The same
  path sums turn any family into a family of maps of row vectors (`TauCeti.ungradedMatrixFamily`),
  compatibly with composition (`TauCeti.ungradedMatrixFamily_ungradedFamilyComp`).
* **Morphisms.** The differential of morphisms
  (`TauCeti.UngradedAInfinityRightModule.morphismDifferential`) sends a family `f` from `M` to `M'`
  to the sum of the composites `f ∘ m` and `m' ∘ f` with the operations of the two modules, of the
  terms `f_{n+1}(…, d aₗ, …)` and of the terms `f_n(…, aₗ aₗ₊₁, …)`. Over a ring of characteristic
  two the homomorphisms of `A∞` modules are the families with `∂f = 0`, and `∂h = f + g` is a
  homotopy between `f` and `g`; the identity is a homomorphism
  (`TauCeti.UngradedAInfinityRightModule.morphismDifferential_ungradedFamilyId`). The differential
  commutes with matrix families
  (`TauCeti.UngradedAInfinityRightModule.morphismDifferential_ungradedMatrixFamily`), and along a
  Maurer–Cartan element `β` the twists satisfy `∂'^β ∘ f^β + f^β ∘ ∂^β = (∂f)^β`
  (`TauCeti.UngradedAInfinityRightModule.twistedDifferential_ungradedTwistedMap`): the same
  telescoping of differential and product terms as for `∂^β ∘ ∂^β`, now with one operation of each
  module composed with `f`.

* **Strict units.** A module is strictly unital for a family `ι` of elements of the algebra
  (`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital`) when its operations `m_{n+1}`,
  `n ≥ 2`, vanish on every tuple containing some `ι s`. If moreover `d (ι s) = 0`, the relation
  with last input `ι s` reduces to
  `m₂(m_{n+1}(m, a₁, …, aₙ), ι s) = m_{n+1}(m, a₁, …, aₙ ι s)`
  (`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_act`), and that of length one to
  `m₂(m₁ m, ι s) = m₁ (m₂(m, ι s))`. So `m₂(·, ι s)` is a projection when `ι s` is idempotent, and
  twisting by `β` with `β * ι s = β` preserves its fixed points. The matrix module of a strictly
  unital module is strictly unital for the diagonal matrices of units
  (`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.matrix`).

Twisting the matrix module by the coefficient matrix of a type `D` structure gives the box tensor
product of bordered Heegaard Floer homology (`TauCeti.LowDimTopology.Bordered.TypeA`), and twisting
the matrix family of a morphism gives the induced map of box tensor products
(`TauCeti.LowDimTopology.Bordered.TypeA.ModuleMap`).

## Main definitions

* `TauCeti.UngradedAInfinityRightModule`: an ungraded `A∞` right module.
* `TauCeti.ungradedFamilyComp` and `TauCeti.ungradedFamilyId`: composition of families of
  operations, and its unit.
* `TauCeti.ungradedTwistedMap` and `TauCeti.UngradedAInfinityRightModule.twistedDifferential`: the
  twist of a family, and of the operations of a module, by an element of the algebra.
* `TauCeti.ungradedMatrixFamily`: a family of operations on row vectors, along matrices.
* `TauCeti.UngradedAInfinityRightModule.morphismDifferential`: the differential of morphisms.
* `TauCeti.UngradedAInfinityRightModule.matrixAct` and
  `TauCeti.UngradedAInfinityRightModule.matrix`: the `A∞` module of row vectors over the matrix
  algebra.
* `TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital`: strict unitality for a family of
  elements of the algebra.

## Main results

* `TauCeti.ungradedFamilyComp_assoc`: composition of families is associative.
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
* `TauCeti.UngradedAInfinityRightModule.matrixAct_apply_of_injective` and
  `TauCeti.UngradedAInfinityRightModule.matrixAct_apply_of_injective_of_forall_notMem_range`: the
  matrix operations restrict along an embedding whose range no path enters, respectively leaves.
* `TauCeti.UngradedAInfinityRightModule.sum_matrixAct_update_fromBlocks_apply_inr`: along block
  upper-triangular matrices, paths from `X` to `Y` see the off-diagonal block exactly once.
* `TauCeti.ungradedTwistedMap_ungradedFamilyComp` and
  `TauCeti.ungradedMatrixFamily_ungradedFamilyComp`: twisting and matrix families respect
  composition.
* `TauCeti.UngradedAInfinityRightModule.morphismDifferential_ungradedMatrixFamily`: the
  differential of morphisms commutes with matrix families.
* `TauCeti.UngradedAInfinityRightModule.twistedDifferential_ungradedTwistedMap`: twisting a
  family along a Maurer–Cartan element intertwines the differentials up to the twist of `∂f`.
* `TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_act`: a unit acting on the output
  of an operation multiplies its last input.
* `TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_twistedDifferential` and
  `TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_matrix_twistedDifferential_apply`:
  twisting preserves the summands of the units.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (`A∞` modules over `𝔽₂`, their morphisms, homotopies and strict unitality, and the box
  tensor product).
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. **3**
  (2001), 1–35, Section 4 (`A∞` modules).
-/

public section

open Finset MulOpposite

namespace TauCeti

/-! ### Composing families of operations -/

section Family

variable {R A M M' M'' M''' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] [AddCommMonoid M'']
  [Module R M''] [AddCommMonoid M'''] [Module R M''']

/-- The **composite** of two families of operations: for `f_{i+1} : M ⊗ A^{⊗ i} → M'` and
`g_{j+1} : M' ⊗ A^{⊗ j} → M''`, the family whose operation with `n` algebra inputs is
`∑_{i + j = n} g_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`. This is the composition of morphisms
of `A∞` modules, and with `f = g` the operations of an `A∞` module it gives the composite terms
`TauCeti.ungradedStasheffComp` of the `A∞` relations. -/
noncomputable def ungradedFamilyComp
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M''))
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'') :=
  ∑ k : Fin (n + 1),
    MultilinearMap.compSplit (Nat.add_sub_of_le (Nat.lt_succ_iff.mp k.isLt)) (g (n - k)) (f k)

theorem ungradedFamilyComp_apply
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M''))
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ)
    (a : Fin n → A) (m : M) :
    ungradedFamilyComp g f n a m =
      ∑ k : Fin (n + 1), g (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (f k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) := by
  simp [ungradedFamilyComp]

/-- **Composition of families is associative.** -/
theorem ungradedFamilyComp_assoc
    (h : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M'' →ₗ[R] M'''))
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M''))
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ungradedFamilyComp (ungradedFamilyComp h g) f =
      ungradedFamilyComp h (ungradedFamilyComp g f) := by
  funext n
  refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
  -- Read the blocks of `a` off its extension by zero, to sum over natural numbers.
  set b : ℕ → A := fun p => if hp : p < n then a ⟨p, hp⟩ else 0 with hb
  set T : ℕ → ℕ → M''' := fun i k => h (n - k) (fun l => b (k + l))
    (g (k - i) (fun l => b (i + l)) (f i (fun l => b l) m)) with hT
  have hb' (p : ℕ) (hp : p < n) : a ⟨p, hp⟩ = b p := by simp [hb, hp]
  simp only [ungradedFamilyComp_apply, map_sum]
  calc _ = ∑ i : Fin (n + 1), ∑ j : Fin (n - i + 1), T i (i + j) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [hT]
        dsimp only
        rw [Nat.add_sub_cancel_left, ← Nat.sub_sub]
        congr! with l l l <;> rw [hb' _ (by omega)]
        rw [Nat.add_assoc]
    _ = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i), T i (i + j) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range (n + 1 - i), T i (i + j))]
        refine sum_congr rfl fun i _ => ?_
        rw [← Fin.sum_univ_eq_sum_range (fun j => T i (i + j)), show n + 1 - i = n - i + 1 by omega]
    _ = ∑ k ∈ range (n + 1), ∑ i ∈ range (k + 1), T i k := by
        rw [← sum_range_diag_flip]
        refine sum_congr rfl fun k _ => sum_congr rfl fun i hi => ?_
        rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]
    _ = ∑ k : Fin (n + 1), ∑ i : Fin (k + 1), T i k := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ i ∈ range (k + 1), T i k)]
        exact sum_congr rfl fun k _ => (Fin.sum_univ_eq_sum_range (fun i => T i k) _).symm
    _ = _ := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
        rw [hT]
        dsimp only
        congr! with l l l <;> rw [hb' _ (by omega)]

/-! ### Twisting a family by an element of the algebra -/

section Twist

/-- The **twist** `∑ₙ f_{n+1}(·, β, …, β)` of a family of operations `f_{n+1}` by an element `β` of
the algebra. For the operations of a module this is its twisted differential
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential`); for a morphism of modules it is the
induced map of the twisted modules. It is a finite sum when the operations `f_{n+1}(·, β, …, β)`
vanish for large `n` (`TauCeti.ungradedTwistedMap_eq_sum`); otherwise this `finsum` is `0` by
convention. -/
noncomputable def ungradedTwistedMap
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (β : A) :
    M →ₗ[R] M' :=
  ∑ᶠ n, f n fun _ => β

theorem ungradedTwistedMap_def
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (β : A) :
    ungradedTwistedMap f β = ∑ᶠ n, f n fun _ => β :=
  (rfl)

/-- When `f_{n+1}(·, β, …, β)` vanishes for `n ≥ K`, the twist is the sum of the first `K`
operations. -/
theorem ungradedTwistedMap_eq_sum
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {β : A} {K : ℕ}
    (h : ∀ n, K ≤ n → (f n fun _ => β) = 0) :
    ungradedTwistedMap f β = ∑ n ∈ range K, f n fun _ => β := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simpa using not_le.mp (mt (h n) hn)

@[simp]
theorem ungradedTwistedMap_zero (β : A) :
    ungradedTwistedMap
      (0 : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) β = 0 := by
  simp [ungradedTwistedMap_def]

/-- **Twisting is additive** on families whose operations along `β` vanish from arity `K` on. -/
theorem ungradedTwistedMap_add
    {f g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {β : A}
    {K : ℕ} (hf : ∀ n, K ≤ n → (f n fun _ => β) = 0) (hg : ∀ n, K ≤ n → (g n fun _ => β) = 0) :
    ungradedTwistedMap (f + g) β = ungradedTwistedMap f β + ungradedTwistedMap g β := by
  rw [ungradedTwistedMap_eq_sum hf, ungradedTwistedMap_eq_sum hg,
    ungradedTwistedMap_eq_sum (K := K) fun n hn => by simp [hf n hn, hg n hn], ← sum_add_distrib]
  simp

/-- The composite family along a constant tuple `β`, summed over the arities `n ≤ 2 K`, is the
composite of the twists, when both families vanish along `β` from arity `K` on. -/
private theorem sum_ungradedFamilyComp_const
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M'')}
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {β : A} {K : ℕ}
    (hg : ∀ n, K ≤ n → (g n fun _ => β) = 0) (hf : ∀ n, K ≤ n → (f n fun _ => β) = 0) (m : M) :
    ∑ n ∈ range (2 * K + 1), ungradedFamilyComp g f n (fun _ => β) m =
      ungradedTwistedMap g β (ungradedTwistedMap f β m) := by
  rw [ungradedTwistedMap_eq_sum (K := 2 * K + 1) fun n hn => hg n (by omega),
    ungradedTwistedMap_eq_sum (K := 2 * K + 1) fun n hn => hf n (by omega)]
  simp only [LinearMap.sum_apply, map_sum, ungradedFamilyComp_apply]
  set F : ℕ → ℕ → M'' := fun i j => g j (fun _ => β) (f i (fun _ => β) m) with hF
  calc _ = ∑ n ∈ range (2 * K + 1), ∑ k ∈ range (n + 1), F k (n - k) :=
        sum_congr rfl fun n _ => Fin.sum_univ_eq_sum_range (fun k => F k (n - k)) (n + 1)
    _ = _ := sum_range_triangle _ F fun i j hij => by
          rcases le_or_gt K i with hi | hi
          · simp [hF, hf i hi]
          · simp [hF, hg j (by omega)]

/-- The composite family vanishes along `β` from arity `2 K - 1` on, when both families vanish
along `β` from arity `K` on. -/
private theorem ungradedFamilyComp_const_eq_zero
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M'')}
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {β : A} {K : ℕ}
    (hg : ∀ n, K ≤ n → (g n fun _ => β) = 0) (hf : ∀ n, K ≤ n → (f n fun _ => β) = 0) {n : ℕ}
    (hn : 2 * K ≤ n + 1) : (ungradedFamilyComp g f n fun _ => β) = 0 := by
  refine LinearMap.ext fun m => ?_
  rw [ungradedFamilyComp_apply, LinearMap.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  rcases le_or_gt K k with hk | hk
  · simp [hf k hk]
  · simp [hg (n - k) (by omega)]

/-- **Twisting is functorial.** When `f` and `g` vanish along `β` from arity `K` on, the twist of
their composite is the composite of their twists. -/
theorem ungradedTwistedMap_ungradedFamilyComp
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M'')}
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {β : A} {K : ℕ}
    (hg : ∀ n, K ≤ n → (g n fun _ => β) = 0) (hf : ∀ n, K ≤ n → (f n fun _ => β) = 0) :
    ungradedTwistedMap (ungradedFamilyComp g f) β =
      ungradedTwistedMap g β ∘ₗ ungradedTwistedMap f β :=
  LinearMap.ext fun m => by
    rw [ungradedTwistedMap_eq_sum (K := 2 * K + 1) fun n hn =>
      ungradedFamilyComp_const_eq_zero hg hf (by omega), LinearMap.sum_apply,
      sum_ungradedFamilyComp_const hg hf, LinearMap.comp_apply]

/-- The **identity family**: the identity of `M` with no algebra input, and zero operations with
algebra inputs. It is the identity morphism of an `A∞` module. -/
noncomputable def ungradedFamilyId :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _ LinearMap.id
  | _ + 1 => 0

@[simp]
theorem ungradedFamilyId_zero_apply (a : Fin 0 → A) :
    ungradedFamilyId (R := R) (M := M) 0 a = LinearMap.id :=
  (rfl)

@[simp]
theorem ungradedFamilyId_succ (n : ℕ) : ungradedFamilyId (R := R) (A := A) (M := M) (n + 1) = 0 :=
  (rfl)

/-- The identity family is the identity with no algebra input and zero otherwise. -/
theorem ungradedFamilyId_apply {n : ℕ} (a : Fin n → A) :
    ungradedFamilyId (R := R) (M := M) n a = if n = 0 then LinearMap.id else 0 := by
  cases n <;> rfl

/-- The identity family is a right unit for composition. -/
@[simp]
theorem ungradedFamilyComp_ungradedFamilyId
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ungradedFamilyComp g ungradedFamilyId = g := by
  funext n
  refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [ungradedFamilyComp_apply, Fintype.sum_eq_single 0 fun k hk => by
    simp [ungradedFamilyId_apply, hk], ungradedFamilyId_apply, ite_eq_left (by simp),
    LinearMap.id_apply]
  exact LinearMap.congr_fun (congrArg (g n) (funext fun l => congrArg a (Fin.ext (by simp)))) m

/-- The identity family is a left unit for composition. -/
@[simp]
theorem ungradedFamilyId_ungradedFamilyComp
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ungradedFamilyComp ungradedFamilyId f = f := by
  funext n
  refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [ungradedFamilyComp_apply, Fintype.sum_eq_single (Fin.last n) fun k hk => by
    have hn : n - (k : ℕ) ≠ 0 := by
      have : (k : ℕ) < n := Fin.val_lt_last hk
      omega
    simp [ungradedFamilyId_apply, hn], ungradedFamilyId_apply, ite_eq_left (by simp),
    LinearMap.id_apply]
  rfl

/-- The twist of the identity family is the identity. -/
@[simp]
theorem ungradedTwistedMap_ungradedFamilyId (β : A) :
    ungradedTwistedMap (ungradedFamilyId (R := R) (M := M)) β = LinearMap.id := by
  rw [ungradedTwistedMap_eq_sum (K := 1) fun n hn => ?_, sum_range_one,
    ungradedFamilyId_zero_apply]
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp

end Twist

/-! ### Families of operations on row vectors -/

section MatrixFamily

variable (X : Type*) [Fintype X] [DecidableEq X]

/-- The **matrix family** of a family of operations `f_{n+1} : M ⊗ A^{⊗ n} → M'`: the operation
`f_{n+1}(φ, F₁, …, Fₙ)` with matrices `Fᵢ` over `A` sends a row vector `φ : X → M` to the row
vector whose `z`-component is the sum, over the paths `x₀ → x₁ → ⋯ → xₙ = z` in `X`, of
`f_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)` (`TauCeti.ungradedMatrixFamily_apply`). For the operations
of a module these are the operations of its matrix module
(`TauCeti.UngradedAInfinityRightModule.matrix`). -/
noncomputable def ungradedMatrixFamily
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => Matrix X X A) ((X → M) →ₗ[R] X → M') :=
  ∑ x : Fin (n + 1) → X,
    (LinearMap.llcomp R (X → M) M' (X → M') (LinearMap.single R (fun _ => M') (x (Fin.last n))) ∘ₗ
      LinearMap.lcomp R M' (LinearMap.proj (x 0))).compMultilinearMap
      ((f n).compLinearMap fun l => Matrix.entryLinearMap R A (x l.castSucc) (x l.succ))

variable {X}

/-- The `z`-component of `f_{n+1}(φ, F₁, …, Fₙ)` in the matrix family is the sum over the paths
`x₀ → ⋯ → xₙ = z` of `f_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`. -/
theorem ungradedMatrixFamily_apply
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ)
    (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedMatrixFamily X f n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then f n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  simp only [ungradedMatrixFamily, _root_.sum_apply, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.lcomp_apply, LinearMap.llcomp_apply, LinearMap.coe_single,
    LinearMap.coe_proj, Function.eval, Matrix.entryLinearMap_apply, Pi.single_apply, eq_comm]

@[simp]
theorem ungradedMatrixFamily_zero :
    ungradedMatrixFamily X
      (0 : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) = 0 := by
  funext n
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  simp [ungradedMatrixFamily_apply]

theorem ungradedMatrixFamily_add
    (f g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ungradedMatrixFamily X (f + g) = ungradedMatrixFamily X f + ungradedMatrixFamily X g := by
  funext n
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  simp only [ungradedMatrixFamily_apply, Pi.add_apply, add_apply,
    LinearMap.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

/-- If the operation `f_{n+1}` vanishes, so does that of the matrix family. -/
theorem ungradedMatrixFamily_eq_zero_of_eq_zero
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')} {n : ℕ}
    (h : f n = 0) :
    ungradedMatrixFamily X f n = 0 := by
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  simp [ungradedMatrixFamily_apply, h]

/-- **Operations of a matrix family along height-increasing matrices vanish.** If a height `h` on
`X` strictly increases along every nonzero entry of each of `F₁, …, Fₙ`, and `n` exceeds every
height, then `f_{n+1}(·, F₁, …, Fₙ) = 0`: every path `x₀ → ⋯ → xₙ` meets a zero entry. -/
theorem ungradedMatrixFamily_eq_zero_of_lt
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (h : X → ℕ)
    {n : ℕ} (hn : univ.sup h < n) {F : Fin n → Matrix X X A}
    (hF : ∀ l x y, F l x y ≠ 0 → h x < h y) :
    ungradedMatrixFamily X f n F = 0 := by
  refine LinearMap.ext fun φ => funext fun z => ?_
  simp only [ungradedMatrixFamily_apply, LinearMap.zero_apply, Pi.zero_apply]
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
  rw [(f n).map_coord_zero l hl, LinearMap.zero_apply, ite_self]

/-- **Composing operations of matrix families.** The `z`-component of
`g_{j+1}(f_{i+1}(φ, F₁, …, Fᵢ), G₁, …, Gⱼ)` is the sum over the paths `w₀ → ⋯ → wᵢ₊ⱼ = z` of
`g_{j+1}(f_{i+1}(φ w₀, F₁ w₀ w₁, …), G₁ wᵢ wᵢ₊₁, …)`. -/
theorem ungradedMatrixFamily_apply_ungradedMatrixFamily_apply {i j n : ℕ} (h : i + j = n)
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M''))
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'))
    (G : Fin j → Matrix X X A) (F : Fin i → Matrix X X A) (φ : X → M) (z : X) :
    ungradedMatrixFamily X g j G (ungradedMatrixFamily X f i F φ) z = ∑ w : Fin (n + 1) → X,
      if w (Fin.last n) = z then
        g j (fun l => G l (w ⟨i + l, by have := l.isLt; omega⟩)
          (w ⟨i + l + 1, by have := l.isLt; omega⟩))
          (f i (fun l => F l (w ⟨l, by have := l.isLt; omega⟩)
            (w ⟨l + 1, by have := l.isLt; omega⟩)) (φ (w 0)))
      else 0 := by
  have hy (y : Fin (j + 1) → X) :
      (if y (Fin.last j) = z then g j (fun l => G l (y l.castSucc) (y l.succ))
        (ungradedMatrixFamily X f i F φ (y 0)) else 0) =
      ∑ x : Fin (i + 1) → X, if x (Fin.last i) = y 0 then
        (if y (Fin.last j) = z then g j (fun l => G l (y l.castSucc) (y l.succ))
          (f i (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))) else 0) else 0 := by
    split_ifs with hyz
    · simp only [ungradedMatrixFamily_apply, map_sum]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    · simp
  rw [ungradedMatrixFamily_apply, sum_congr rfl fun y _ => hy y, sum_comm,
    Fin.sum_sum_ite_apply_last_eq_apply_zero h]
  refine sum_congr rfl fun w _ => ?_
  have hlast : w ⟨i + (Fin.last j : ℕ), by simp; omega⟩ = w (Fin.last n) :=
    congrArg w (Fin.ext (by simp [h]))
  have hzero : w ⟨((0 : Fin (i + 1)) : ℕ), by simp⟩ = w 0 := congrArg w (Fin.ext (by simp))
  simp only [hlast, hzero, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]

/-- **The matrix family of a composite** is the composite of the matrix families. -/
theorem ungradedMatrixFamily_ungradedFamilyComp
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M''))
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ungradedMatrixFamily X (ungradedFamilyComp g f) =
      ungradedFamilyComp (ungradedMatrixFamily X g) (ungradedMatrixFamily X f) := by
  funext n
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  rw [ungradedFamilyComp_apply, Finset.sum_apply]
  rw [sum_congr rfl fun k _ => ungradedMatrixFamily_apply_ungradedMatrixFamily_apply
    (Nat.add_sub_of_le (Nat.lt_succ_iff.mp k.isLt)) _ _ _ _ φ z, sum_comm,
    ungradedMatrixFamily_apply]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [ungradedFamilyComp_apply]
    rfl
  · simp

/-- The matrix family of the identity family is the identity family of the row vectors. -/
@[simp]
theorem ungradedMatrixFamily_ungradedFamilyId :
    ungradedMatrixFamily X (ungradedFamilyId (R := R) (A := A) (M := M)) = ungradedFamilyId := by
  funext n
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  cases n with
  | zero =>
    rw [ungradedMatrixFamily_apply, ← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
    simp
  | succ n => simp [ungradedMatrixFamily_apply]

end MatrixFamily

end Family

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-! ### The relations -/

section Stasheff

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable (act : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M))

/-- The **composite terms** of the `A∞` relation of length `n`:
`∑_{i + j = n} m_{j+1}(m_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`, where `act i` is `m_{i+1}`. -/
noncomputable def ungradedStasheffComp (n : ℕ) (a : Fin n → A) (m : M) : M :=
  ungradedFamilyComp act act n a m

theorem ungradedStasheffComp_def (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffComp act n a m =
      ∑ k : Fin (n + 1), act (n - k) (fun l => a ⟨k + l, by have := l.isLt; omega⟩)
        (act k (fun l => a ⟨l, by have := l.isLt; have := k.isLt; omega⟩) m) :=
  ungradedFamilyComp_apply act act n a m

variable (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'))

/-- The **differential terms** of the `A∞` relation of length `n` for a family of operations
`f_{n+1}`, such as the operations `m_{n+1}` of a module: `∑_l f_{n+1}(m, a₁, …, d aₗ, …, aₙ)`. -/
noncomputable def ungradedStasheffDiff (d : A →ₗ[R] A) (n : ℕ) (a : Fin n → A) (m : M) : M' :=
  ∑ l : Fin n, f n (Function.update a l (d (a l))) m

theorem ungradedStasheffDiff_def (d : A →ₗ[R] A) (n : ℕ) (a : Fin n → A) (m : M) :
    ungradedStasheffDiff f d n a m = ∑ l : Fin n, f n (Function.update a l (d (a l))) m :=
  (rfl)

/-- The **product terms** of the `A∞` relation of length `n` for a family of operations
`f_{n+1}`, such as the operations `m_{n+1}` of a module: `∑_l f_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ)`, over
the `n - 1` adjacent pairs. -/
noncomputable def ungradedStasheffMul : (n : ℕ) → (Fin n → A) → M → M'
  | 0, _, _ => 0
  | n + 1, a, m => ∑ l : Fin n, f n (Fin.contractNth l.castSucc (· * ·) a) m

@[simp]
theorem ungradedStasheffMul_zero (a : Fin 0 → A) (m : M) : ungradedStasheffMul f 0 a m = 0 :=
  (rfl)

theorem ungradedStasheffMul_succ (n : ℕ) (a : Fin (n + 1) → A) (m : M) :
    ungradedStasheffMul f (n + 1) a m =
      ∑ l : Fin n, f n (Fin.contractNth l.castSucc (· * ·) a) m :=
  (rfl)

end Stasheff

section MatrixFamily

variable {M' : Type*} [AddCommGroup M'] [Module R M'] {X : Type*} [Fintype X] [DecidableEq X]

/-- The differential terms of a matrix family are sums over paths. -/
private theorem stasheffDiff_ungradedMatrixFamily
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (d : A →ₗ[R] A)
    (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedStasheffDiff (ungradedMatrixFamily X f)
        (d.mapMatrix : Matrix X X A →ₗ[R] Matrix X X A) n F φ z =
      ∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
        ungradedStasheffDiff f d n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  -- Updating one matrix of a tuple updates one entry along every path.
  have hupd (x : Fin (n + 1) → X) (l : Fin n) (G : Matrix X X A) :
      (fun t => Function.update F l G t (x t.castSucc) (x t.succ)) =
        Function.update (fun t => F t (x t.castSucc) (x t.succ)) l (G (x l.castSucc) (x l.succ)) :=
    funext (Function.apply_update (fun t (G : Matrix X X A) => G (x t.castSucc) (x t.succ)) F l G)
  simp only [ungradedStasheffDiff, Finset.sum_apply, ungradedMatrixFamily_apply, hupd,
    LinearMap.mapMatrix_apply, Matrix.map_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- The product terms of a matrix family are sums over paths. -/
private theorem stasheffMul_ungradedMatrixFamily
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ)
    (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    ungradedStasheffMul (ungradedMatrixFamily X f) n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then
        ungradedStasheffMul f n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [ungradedStasheffMul_succ, Finset.sum_apply, ungradedMatrixFamily_apply]
    have hR (w : Fin (n + 2) → X) :
        (if w (Fin.last (n + 1)) = z then ∑ l : Fin n,
          f n (Fin.contractNth l.castSucc (· * ·) fun k => F k (w k.castSucc) (w k.succ))
            (φ (w 0)) else 0) =
        ∑ l : Fin n, if w (Fin.last (n + 1)) = z then
          f n (Fin.contractNth l.castSucc (· * ·) fun k => F k (w k.castSucc) (w k.succ))
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

end MatrixFamily

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
  act : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)
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
  rw [ungradedStasheffComp_def, Fin.sum_univ_one] at h
  simp only [ungradedStasheffDiff, Fin.sum_univ_zero, ungradedStasheffMul_zero, add_zero] at h
  convert h using 2
  · exact congrArg (Mm.act 0) (Subsingleton.elim _ _)
  · exact congrArg (fun c => Mm.act 0 c m) (Subsingleton.elim _ _)

/-! ### Twisting by a Maurer–Cartan element -/

/-- The **twisted differential** `∂^β = ∑ₙ m_{n+1}(·, β, …, β)` of an element `β` of the algebra,
the twist `TauCeti.ungradedTwistedMap` of the operations. It is a finite sum when the operations
`m_{n+1}(·, β, …, β)` vanish for large `n`
(`TauCeti.UngradedAInfinityRightModule.twistedDifferential_eq_sum`); otherwise this `finsum` is
`0` by convention. -/
noncomputable def twistedDifferential (β : A) : M →ₗ[R] M :=
  ungradedTwistedMap Mm.act β

theorem twistedDifferential_def (β : A) :
    Mm.twistedDifferential β = ∑ᶠ n, Mm.act n fun _ => β :=
  (rfl)

theorem twistedDifferential_eq_ungradedTwistedMap (β : A) :
    Mm.twistedDifferential β = ungradedTwistedMap Mm.act β :=
  (rfl)

/-- When `m_{n+1}(·, β, …, β)` vanishes for `n ≥ K`, the twisted differential is the sum of the
first `K` operations. -/
theorem twistedDifferential_eq_sum {β : A} {K : ℕ}
    (h : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0) :
    Mm.twistedDifferential β = ∑ n ∈ range K, Mm.act n fun _ => β :=
  ungradedTwistedMap_eq_sum h

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
    (ungradedStasheffComp_def _ _ _ _).trans <| Fin.sum_univ_eq_sum_range
      (fun k => Mm.act (n - k) (fun _ => β) (Mm.act k (fun _ => β) m)) (n + 1)
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
  set f : ℕ → ℕ → M := fun i j => Mm.act j (fun _ => β) (Mm.act i (fun _ => β) m)
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
  -- `∂^β ∘ ∂^β` is the sum of the composite terms of all lengths at most `2 K`.
  rw [twistedDifferential_eq_ungradedTwistedMap, ← sum_ungradedFamilyComp_const hc hc m, ← hrel]
  exact sum_congr rfl fun n _ => (ungradedFamilyComp_apply _ _ _ _ _).trans <|
    Fin.sum_univ_eq_sum_range (fun k => f k (n - k)) (n + 1)

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

/-! ### Strict units -/

section StrictUnit

variable {S : Type*} {ι : S → A}

/-- An ungraded `A∞` right module is **strictly unital** for a family `ι` of elements of the
algebra, typically its idempotents, when every operation `m_{n+1}`, `n ≥ 2`, vanishes as soon as
one of its algebra inputs is some `ι s`. The binary operation `m₂(·, ι s)` is not prescribed: over
a ring of idempotents it is the action of `ι s`, a projection onto a summand of `M`
(`TauCeti.UngradedAInfinityRightModule.IsStrictlyUnital.act_one_act_one`). -/
def IsStrictlyUnital (ι : S → A) : Prop :=
  ∀ n, 2 ≤ n → ∀ (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → Mm.act n a = 0

/-- The defining property of a strictly unital module, for proving strict unitality without
unfolding the definition. -/
theorem isStrictlyUnital_iff : Mm.IsStrictlyUnital ι ↔
    ∀ n, 2 ≤ n → ∀ (a : Fin n → A) (i : Fin n) (s : S), a i = ι s → Mm.act n a = 0 :=
  Iff.rfl

variable {Mm}

/-- A strictly unital module's operations of arity at least three vanish on a unit input. -/
theorem IsStrictlyUnital.act_eq_zero (hMm : Mm.IsStrictlyUnital ι) {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → A} {i : Fin n} {s : S} (hi : a i = ι s) : Mm.act n a = 0 :=
  hMm n hn a i s hi

variable (Mm) in
/-- **`m₁` commutes with the action of a cycle.** Over a ring of characteristic two, if `d e = 0`
then `m₂(m₁ m, e) = m₁ (m₂(m, e))`: this is the relation of length one. -/
theorem act_one_act_zero [CharP R 2] {e : A} (he : d e = 0) (a : Fin 0 → A) (m : M) :
    Mm.act 1 (fun _ => e) (Mm.act 0 a m) = Mm.act 0 a (Mm.act 1 (fun _ => e) m) := by
  have h := Mm.stasheff 1 (fun _ => e) m
  rw [ungradedStasheffComp_def, ungradedStasheffDiff, ungradedStasheffMul_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_zero, add_zero] at h
  rw [(Mm.act 1).map_coord_zero 0 (by simp [he]), LinearMap.zero_apply, add_zero] at h
  obtain rfl : a = fun _ => e := Subsingleton.elim _ _
  exact (add_eq_zero_iff_eq_of_charTwo R).mp h

/-- Operations of equal arity agree on tuples that agree after the cast of indices. -/
private theorem act_congr {j k : ℕ} (h : j = k) {u : Fin j → A} {v : Fin k → A}
    (huv : ∀ l, u l = v (Fin.cast h l)) (m : M) : Mm.act j u m = Mm.act k v m := by
  subst h
  rw [show u = v from funext huv]

/-- **The action of a unit on the output of an operation.** For a strictly unital module over a
ring of characteristic two, with `d (ι s) = 0`,
`m₂(m_{n+2}(m, a₁, …, aₙ₊₁), ι s) = m_{n+2}(m, a₁, …, aₙ₊₁ ι s)`. This is the relation of length
`n + 2` with inputs `a₁, …, aₙ₊₁, ι s`: every other term has `ι s` among the inputs of an operation
of arity at least three. -/
theorem IsStrictlyUnital.act_one_act [CharP R 2] (hMm : Mm.IsStrictlyUnital ι) {s : S}
    (hs : d (ι s) = 0) {n : ℕ} (a : Fin (n + 1) → A) (m : M) :
    Mm.act 1 (fun _ => ι s) (Mm.act (n + 1) a m) =
      Mm.act (n + 1) (Function.update a (Fin.last n) (a (Fin.last n) * ι s)) m := by
  set b : Fin (n + 2) → A := Fin.snoc a (ι s) with hb
  have hbl : b (Fin.last (n + 1)) = ι s := by simp [hb]
  have hbc (l : Fin (n + 1)) : b l.castSucc = a l := by simp [hb]
  have h := Mm.stasheff (n + 2) b m
  -- Among the composite terms only `m₂(m_{n+2}(m, a), ι s)` survives.
  have hcomp : ungradedStasheffComp Mm.act (n + 2) b m =
      Mm.act 1 (fun _ => ι s) (Mm.act (n + 1) a m) := by
    rw [ungradedStasheffComp_def, Finset.sum_eq_single (⟨n + 1, by omega⟩ : Fin (n + 3))]
    · rw [act_congr (h := (by simp : n + 2 - ((⟨n + 1, by omega⟩ : Fin (n + 3)) : ℕ) = 1))
          (v := fun _ => ι s) (fun l => by
            have hl := l.isLt
            simp only [Fin.val_mk] at hl
            rw [← hbl]; congr 1; ext; simp; omega),
        act_congr (h := (rfl : ((⟨n + 1, by omega⟩ : Fin (n + 3)) : ℕ) = n + 1)) (v := a)
          (fun l => by rw [← hbc]; rfl)]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ n + 1 := fun h => hk (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hk' with hlt | hgt
      · rw [hMm.act_eq_zero (i := ⟨n + 1 - k, by omega⟩) (s := s) (by omega)
          (by rw [← hbl]; congr 1; ext; simp; omega), LinearMap.zero_apply]
      · rw [hMm.act_eq_zero (n := k) (i := ⟨n + 1, by omega⟩) (s := s) (by omega)
          (by rw [← hbl]; congr 1), LinearMap.zero_apply, map_zero]
    · simp
  -- The differential terms vanish: `d (ι s) = 0`, and the unit remains in the other terms.
  have hdiff : ungradedStasheffDiff Mm.act d (n + 2) b m = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = Fin.last (n + 1)
    · subst hl
      rw [(Mm.act (n + 2)).map_coord_zero (Fin.last (n + 1)) (by simp [hbl, hs]),
        LinearMap.zero_apply]
    · rw [hMm.act_eq_zero (i := Fin.last (n + 1)) (s := s) (by omega)
        (by rw [Function.update_of_ne (Ne.symm hl), hbl]), LinearMap.zero_apply]
  -- Among the product terms only the product `aₙ₊₁ * ι s` of the last two inputs survives.
  have hmul : ungradedStasheffMul Mm.act (n + 2) b m =
      Mm.act (n + 1) (Function.update a (Fin.last n) (a (Fin.last n) * ι s)) m := by
    rw [ungradedStasheffMul_succ, Finset.sum_eq_single (Fin.last n)]
    · congr 2
      funext k
      by_cases hk : k = Fin.last n
      · subst hk
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self, hbc, Fin.succ_last,
          hbl]
      · have hk' : (k : ℕ) < n := Fin.val_lt_last hk
        rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using hk'), hbc,
          Function.update_of_ne hk]
    · intro l _ hl
      have hl' : (l : ℕ) < n := Fin.val_lt_last hl
      rw [hMm.act_eq_zero (i := Fin.last n) (s := s) (by omega)
        (by rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using hl'), Fin.succ_last, hbl]),
        LinearMap.zero_apply]
    · simp
  rw [hcomp, hdiff, hmul, add_zero] at h
  exact (add_eq_zero_iff_eq_of_charTwo R).mp h

/-- For a strictly unital module over a ring of characteristic two, the action
`m₂(·, ι s)` of an idempotent cycle `ι s` is a projection. -/
theorem IsStrictlyUnital.act_one_act_one [CharP R 2] (hMm : Mm.IsStrictlyUnital ι) {s : S}
    (hs : d (ι s) = 0) (hss : IsIdempotentElem (ι s)) (m : M) :
    Mm.act 1 (fun _ => ι s) (Mm.act 1 (fun _ => ι s) m) = Mm.act 1 (fun _ => ι s) m := by
  rw [hMm.act_one_act hs (n := 0), hss.eq]
  congr 2
  funext l
  rw [Fin.fin_one_eq_zero l]
  simp

/-- **Twisting preserves the summand of a unit.** For a strictly unital module over a ring of
characteristic two, with `d (ι s) = 0`, if `β * ι s = β` and `m₂(m, ι s) = m`, then also
`m₂(∂^β m, ι s) = ∂^β m`. -/
theorem IsStrictlyUnital.act_one_twistedDifferential [CharP R 2] (hMm : Mm.IsStrictlyUnital ι)
    {s : S} (hs : d (ι s) = 0) {β : A} (hβ : β * ι s = β) {m : M}
    (hm : Mm.act 1 (fun _ => ι s) m = m) :
    Mm.act 1 (fun _ => ι s) (Mm.twistedDifferential β m) = Mm.twistedDifferential β m := by
  rw [twistedDifferential_def]
  by_cases hfin : (Function.support fun n => Mm.act n fun _ => β).Finite
  · rw [finsum_eq_sum _ hfin, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    cases n with
    | zero => rw [Mm.act_one_act_zero hs, hm]
    | succ n => rw [hMm.act_one_act hs, hβ, Function.update_eq_self]
  · rw [finsum_of_infinite_support hfin, LinearMap.zero_apply, map_zero]

end StrictUnit

/-! ### The module of row vectors over the matrix algebra -/

section Matrix

variable (X : Type*) [Fintype X] [DecidableEq X]

/-- The operations of the **matrix module**, the matrix family
`TauCeti.ungradedMatrixFamily` of the operations of `M`: `m_{n+1}(φ, F₁, …, Fₙ)` sends a row
vector `φ : X → M` to the row vector whose `z`-component is the sum, over the paths
`x₀ → x₁ → ⋯ → xₙ = z` in `X`, of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`
(`TauCeti.UngradedAInfinityRightModule.matrixAct_apply`). -/
noncomputable def matrixAct (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => Matrix X X A) ((X → M) →ₗ[R] X → M) :=
  ungradedMatrixFamily X Mm.act n

theorem matrixAct_eq_ungradedMatrixFamily : Mm.matrixAct X = ungradedMatrixFamily X Mm.act :=
  (rfl)

/-- The `z`-component of `m_{n+1}(φ, F₁, …, Fₙ)` in the matrix module is the sum over the paths
`x₀ → ⋯ → xₙ = z` of `m_{n+1}(φ x₀, F₁ x₀ x₁, …, Fₙ xₙ₋₁ xₙ)`. -/
theorem matrixAct_apply (n : ℕ) (F : Fin n → Matrix X X A) (φ : X → M) (z : X) :
    Mm.matrixAct X n F φ z = ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then Mm.act n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 :=
  ungradedMatrixFamily_apply Mm.act n F φ z

/-- If the operation `m_{n+1}` of `M` vanishes, so does that of the matrix module. -/
theorem matrixAct_eq_zero_of_act_eq_zero {n : ℕ} (h : Mm.act n = 0) : Mm.matrixAct X n = 0 :=
  ungradedMatrixFamily_eq_zero_of_eq_zero h

/-- **Operations of the matrix module along height-increasing matrices vanish.** If a height
`h` on `X` strictly increases along every nonzero entry of each of `F₁, …, Fₙ`, and `n` exceeds
every height, then `m_{n+1}(·, F₁, …, Fₙ) = 0`: every path `x₀ → ⋯ → xₙ` meets a zero entry. -/
theorem matrixAct_eq_zero_of_lt (h : X → ℕ) {n : ℕ} (hn : univ.sup h < n)
    {F : Fin n → Matrix X X A} (hF : ∀ l x y, F l x y ≠ 0 → h x < h y) :
    Mm.matrixAct X n F = 0 :=
  ungradedMatrixFamily_eq_zero_of_lt Mm.act h hn hF

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
      else 0 :=
  ungradedMatrixFamily_apply_ungradedMatrixFamily_apply h Mm.act Mm.act G F φ z

/-- The **matrix module**: the row vectors `X → M` form an ungraded `A∞` right module over the
matrix algebra `Matrix X X A`, with the entrywise differential and the operations
`TauCeti.UngradedAInfinityRightModule.matrixAct`. -/
noncomputable def matrix :
    UngradedAInfinityRightModule (d.mapMatrix : Matrix X X A →ₗ[R] Matrix X X A) (X → M) where
  act := Mm.matrixAct X
  stasheff n F φ := by
    funext z
    have hcomp : ungradedStasheffComp (Mm.matrixAct X) n F φ z = ∑ x : Fin (n + 1) → X,
        if x (Fin.last n) = z then
          ungradedStasheffComp Mm.act n (fun l => F l (x l.castSucc) (x l.succ)) (φ (x 0))
        else 0 := by
      rw [ungradedStasheffComp, matrixAct_eq_ungradedMatrixFamily,
        ← ungradedMatrixFamily_ungradedFamilyComp, ungradedMatrixFamily_apply]
      rfl
    rw [Pi.add_apply, Pi.add_apply, Pi.zero_apply, hcomp, matrixAct_eq_ungradedMatrixFamily,
      stasheffDiff_ungradedMatrixFamily, stasheffMul_ungradedMatrixFamily, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_eq_zero fun x _ => ?_
    split_ifs
    · exact Mm.stasheff n _ _
    · simp

@[simp]
theorem matrix_act : (Mm.matrix X).act = Mm.matrixAct X :=
  (rfl)

/-- The operation `m₂` of the matrix module along a diagonal matrix acts componentwise. -/
theorem matrixAct_one_diagonal_apply (v : X → A) (φ : X → M) (z : X) :
    Mm.matrixAct X 1 (fun _ => Matrix.diagonal v) φ z = Mm.act 1 (fun _ => v z) (φ z) := by
  rw [matrixAct_apply, ← (piFinTwoEquiv fun _ => X).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single z]
  · rw [Finset.sum_eq_single z]
    · split_ifs with h
      · congr 2
        funext l
        rw [Fin.fin_one_eq_zero l]
        simp
      · simp at h
    · intro y _ hy
      simp [hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun y' _ => ?_
    split_ifs with h
    · have h' : y' = z := by simpa using h
      subst h'
      rw [(Mm.act 1).map_coord_zero 0 (by simp [Matrix.diagonal_apply_ne _ hy]),
        LinearMap.zero_apply]
    · rfl
  · simp

variable {S : Type*} {ι : S → A} {Mm}

/-- **The matrix module of a strictly unital module is strictly unital** for the diagonal
matrices of units. -/
theorem IsStrictlyUnital.matrix (hMm : Mm.IsStrictlyUnital ι) :
    (Mm.matrix X).IsStrictlyUnital fun e : X → S => Matrix.diagonal fun x => ι (e x) := by
  refine (isStrictlyUnital_iff _).2 fun n hn F i e hFi => ?_
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [matrix_act, matrixAct_apply, LinearMap.zero_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs
  · by_cases hx : x i.castSucc = x i.succ
    · rw [hMm.act_eq_zero hn (i := i) (s := e (x i.castSucc)) (by simp [hFi, ← hx]),
        LinearMap.zero_apply]
    · rw [(Mm.act n).map_coord_zero i (by simp [hFi, Matrix.diagonal_apply_ne _ hx]),
        LinearMap.zero_apply]
  · rfl

/-- **Twisting the matrix module preserves the summands of the units.** For a strictly unital
module over a ring of characteristic two whose units are cycles, let `e` assign a unit `ι (e x)`
to each `x`, and let the columns of `β` satisfy `β x y * ι (e y) = β x y`. If each component of a
row vector `φ` satisfies `m₂(φ x, ι (e x)) = φ x`, so does each component of `∂^β φ`. -/
theorem IsStrictlyUnital.act_one_matrix_twistedDifferential_apply [CharP R 2]
    (hMm : Mm.IsStrictlyUnital ι) (hι : ∀ s, d (ι s) = 0) {e : X → S} {β : Matrix X X A}
    (hβ : ∀ x y, β x y * ι (e y) = β x y) {φ : X → M}
    (hφ : ∀ x, Mm.act 1 (fun _ => ι (e x)) (φ x) = φ x) (z : X) :
    Mm.act 1 (fun _ => ι (e z)) ((Mm.matrix X).twistedDifferential β φ z) =
      (Mm.matrix X).twistedDifferential β φ z := by
  have hP (ψ : X → M) (y : X) :
      (Mm.matrix X).act 1 (fun _ => Matrix.diagonal fun x => ι (e x)) ψ y =
        Mm.act 1 (fun _ => ι (e y)) (ψ y) :=
    Mm.matrixAct_one_diagonal_apply X _ ψ y
  rw [← hP]
  refine congrFun ((hMm.matrix X).act_one_twistedDifferential (s := e) ?_ ?_ ?_) z
  · rw [LinearMap.mapMatrix_apply, Matrix.diagonal_map (map_zero d)]
    simp [hι]
  · ext x y
    rw [Matrix.mul_diagonal]
    exact hβ x y
  · exact funext fun x => (hP φ x).trans (hφ x)

end Matrix

/-! ### Block upper-triangular matrices -/

section Block

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **Restricting the matrix module along an embedding.** Let `e : Y → X` be injective, and
suppose that no matrix `Fᵢ` on `X` has a nonzero entry into the range of `e` from outside it. Then
no path ending in the range of `e` leaves it, so the components of `m_{n+1}(φ, F₁, …, Fₙ)` at the
points `e z` are those of the operation of the matrix module of `Y` on `φ ∘ e`, along the matrices
`Pᵢ` that the `Fᵢ` restrict to. -/
theorem matrixAct_apply_of_injective {n : ℕ} {e : Y → X} (he : Function.Injective e)
    (F : Fin n → Matrix X X A) (P : Fin n → Matrix Y Y A)
    (hP : ∀ l a b, F l (e a) (e b) = P l a b)
    (hF : ∀ l a b, a ∉ Set.range e → F l a (e b) = 0) (φ : X → M) (z : Y) :
    Mm.matrixAct X n F φ (e z) = Mm.matrixAct Y n P (φ ∘ e) z := by
  rw [matrixAct_apply, matrixAct_apply]
  refine (Fintype.sum_of_injective (fun y => e ∘ y)
    (fun y y' h => funext fun k => he (congrFun h k)) _ _ (fun x hx => ?_)
    fun y => by simp [he.eq_iff, hP]).symm
  split_ifs with hz
  · -- A path ending in the range of `e` and leaving it steps into the range from outside.
    obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
      by_contra! hne
      have hmem (k : Fin (n + 1)) : x k ∈ Set.range e := by
        induction k using Fin.reverseInduction with
        | last => exact ⟨z, hz.symm⟩
        | cast k ih =>
          by_contra hk
          obtain ⟨b, hb⟩ := ih
          exact hne k (by rw [← hb]; exact hF k _ b hk)
      exact hx ⟨fun k => (hmem k).choose, funext fun k => (hmem k).choose_spec⟩
    rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply]
  · rfl

/-- **Restricting the matrix module along an embedding, on supported row vectors.** Let
`e : Y → X` be injective, and suppose that no matrix `Fᵢ` on `X` has a nonzero entry from the range
of `e` to outside it. Then a path starting in the range of `e` stays there, so on a row vector `φ`
vanishing outside the range of `e`, the components of `m_{n+1}(φ, F₁, …, Fₙ)` at the points `e z`
are those of the operation of the matrix module of `Y` on `φ ∘ e`, along the matrices `Pᵢ` that
the `Fᵢ` restrict to. -/
theorem matrixAct_apply_of_injective_of_forall_notMem_range {n : ℕ} {e : Y → X}
    (he : Function.Injective e) (F : Fin n → Matrix X X A) (P : Fin n → Matrix Y Y A)
    (hP : ∀ l a b, F l (e a) (e b) = P l a b)
    (hF : ∀ l a b, b ∉ Set.range e → F l (e a) b = 0) {φ : X → M}
    (hφ : ∀ a, a ∉ Set.range e → φ a = 0) (z : Y) :
    Mm.matrixAct X n F φ (e z) = Mm.matrixAct Y n P (φ ∘ e) z := by
  rw [matrixAct_apply, matrixAct_apply]
  refine (Fintype.sum_of_injective (fun y => e ∘ y)
    (fun y y' h => funext fun k => he (congrFun h k)) _ _ (fun x hx => ?_)
    fun y => by simp [he.eq_iff, hP]).symm
  split_ifs with hz
  · by_cases hx0 : x 0 ∈ Set.range e
    swap
    · rw [hφ _ hx0, map_zero]
    -- A path starting in the range of `e` and leaving it steps out of the range.
    obtain ⟨l, hl⟩ : ∃ l : Fin n, F l (x l.castSucc) (x l.succ) = 0 := by
      by_contra! hne
      have hmem (k : Fin (n + 1)) : x k ∈ Set.range e := by
        induction k using Fin.induction with
        | zero => exact hx0
        | succ k ih =>
          by_contra hk
          obtain ⟨a, ha⟩ := ih
          exact hne k (by rw [← ha]; exact hF k a _ hk)
      exact hx ⟨fun k => (hmem k).choose, funext fun k => (hmem k).choose_spec⟩
    rw [(Mm.act n).map_coord_zero l hl, LinearMap.zero_apply]
  · rfl

/-- **Restricting the matrix module to the first summand.** If no matrix `Fᵢ` on `X ⊕ Y` has a
nonzero entry from `Y` to `X`, then no path ending in `X` passes through `Y`, so the
`X`-components of `m_{n+1}(φ, F₁, …, Fₙ)` are those of the operation of the matrix module of `X`
on the `X`-components of `φ` and the `X × X` blocks of the `Fᵢ`. -/
theorem matrixAct_apply_inl {n : ℕ} (F : Fin n → Matrix (X ⊕ Y) (X ⊕ Y) A)
    (hF : ∀ l a b, F l (Sum.inr a) (Sum.inl b) = 0) (φ : X ⊕ Y → M) (z : X) :
    Mm.matrixAct (X ⊕ Y) n F φ (Sum.inl z) =
      Mm.matrixAct X n (fun l => (F l).toBlocks₁₁) (φ ∘ Sum.inl) z :=
  Mm.matrixAct_apply_of_injective Sum.inl_injective F _ (fun _ _ _ => rfl)
    (fun l a b ha => by
      rcases a with a | a
      · exact absurd ⟨a, rfl⟩ ha
      · exact hF l a b) φ z

/-- **Restricting the matrix module to the second summand.** If no matrix `Fᵢ` on `X ⊕ Y` has a
nonzero entry from `Y` to `X`, then a path starting in `Y` stays in `Y`, so on row vectors
supported on `Y` the `Y`-components of `m_{n+1}(·, F₁, …, Fₙ)` are those of the operation of the
matrix module of `Y` along the `Y × Y` blocks of the `Fᵢ`. -/
theorem matrixAct_sumElim_zero_apply_inr {n : ℕ} (F : Fin n → Matrix (X ⊕ Y) (X ⊕ Y) A)
    (hF : ∀ l a b, F l (Sum.inr a) (Sum.inl b) = 0) (ψ : Y → M) (z : Y) :
    Mm.matrixAct (X ⊕ Y) n F (Sum.elim 0 ψ) (Sum.inr z) =
      Mm.matrixAct Y n (fun l => (F l).toBlocks₂₂) ψ z :=
  Mm.matrixAct_apply_of_injective_of_forall_notMem_range Sum.inr_injective F _
    (fun _ _ _ => rfl)
    (fun l a b hb => by
      rcases b with b | b
      · exact hF l a b
      · exact absurd ⟨b, rfl⟩ hb)
    (fun a ha => by
      rcases a with a | a
      · rfl
      · exact absurd ⟨a, rfl⟩ ha) z

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

/-! ### Morphisms -/

section Morphism

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (Mm' : UngradedAInfinityRightModule d M')

/-- The **differential of morphisms** from `M` to `M'`: for a family of maps
`f_{n+1} : M ⊗ A^{⊗ n} → M'`, the family `∂f` with

`(∂f)_{n+1}(m, a₁, …, aₙ) = ∑_{i + j = n} f_{j+1}(m_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
`  + ∑_{i + j = n} m'_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)`
`  + ∑_l f_{n+1}(m, a₁, …, d aₗ, …, aₙ) + ∑_l f_n(m, a₁, …, aₗ aₗ₊₁, …, aₙ)`

(`TauCeti.UngradedAInfinityRightModule.morphismDifferential_apply`). Over a ring of characteristic
two, a **homomorphism** (`A∞` morphism) of ungraded `A∞` modules is a family with `∂f = 0`, and
`∂h = f + g` exhibits `h` as a **homotopy** between `f` and `g`. -/
noncomputable def morphismDifferential
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M') :=
  ungradedFamilyComp f Mm.act n + ungradedFamilyComp Mm'.act f n +
    ∑ l : Fin n, (f n).compLinearMap (Function.update (fun _ => LinearMap.id) l d) +
    match n with
    | 0 => 0
    | n + 1 => ∑ l : Fin n, (f n).compContractNthMul l

/-- The differential of morphisms is the sum of the composite terms with the operations of `M` and
of `M'`, the differential terms and the product terms. -/
theorem morphismDifferential_apply
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (n : ℕ)
    (a : Fin n → A) (m : M) :
    Mm.morphismDifferential Mm' f n a m =
      ungradedFamilyComp f Mm.act n a m + ungradedFamilyComp Mm'.act f n a m +
        ungradedStasheffDiff f d n a m + ungradedStasheffMul f n a m := by
  have hupd (l : Fin n) : (fun t => Function.update (fun _ => (LinearMap.id : A →ₗ[R] A)) l d t
      (a t)) = Function.update a l (d (a l)) := by
    funext t
    by_cases ht : t = l
    · subst ht; simp
    · simp [Function.update_of_ne ht]
  cases n <;>
    simp [morphismDifferential, ungradedStasheffDiff, ungradedStasheffMul_succ, hupd]

/-- **The identity is a homomorphism**, over a ring of characteristic two. -/
@[simp]
theorem morphismDifferential_ungradedFamilyId [CharP R 2] :
    Mm.morphismDifferential Mm ungradedFamilyId = 0 := by
  funext n
  refine MultilinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [morphismDifferential_apply, ungradedFamilyId_ungradedFamilyComp,
    ungradedFamilyComp_ungradedFamilyId, add_self_eq_zero_of_charTwo R, zero_add]
  rcases n with _ | _ | n
  · simp [ungradedStasheffDiff]
  · simp [ungradedStasheffDiff, ungradedStasheffMul_succ]
  · simp [ungradedStasheffDiff, ungradedStasheffMul_succ]

/-- **The differential of morphisms commutes with matrix families**: the differential of the matrix
family of `f`, a family of maps between the matrix modules, is the matrix family of `∂f`. -/
theorem morphismDifferential_ungradedMatrixFamily (X : Type*) [Fintype X] [DecidableEq X]
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    (Mm.matrix X).morphismDifferential (Mm'.matrix X) (ungradedMatrixFamily X f) =
      ungradedMatrixFamily X (Mm.morphismDifferential Mm' f) := by
  funext n
  refine MultilinearMap.ext fun F => LinearMap.ext fun φ => funext fun z => ?_
  rw [morphismDifferential_apply, matrix_act, matrix_act, matrixAct_eq_ungradedMatrixFamily,
    matrixAct_eq_ungradedMatrixFamily, ← ungradedMatrixFamily_ungradedFamilyComp,
    ← ungradedMatrixFamily_ungradedFamilyComp]
  simp only [Pi.add_apply]
  rw [ungradedMatrixFamily_apply, ungradedMatrixFamily_apply, stasheffDiff_ungradedMatrixFamily,
    stasheffMul_ungradedMatrixFamily, ungradedMatrixFamily_apply, ← sum_add_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [morphismDifferential_apply]

/-- Over a ring of characteristic two, along an element `β` with `d β = β * β`, the differential
and product terms of the morphism relations of length at most `N` telescope to the differential
terms of length `N`: the product terms of length `n + 1` insert `β * β` where those of length `n`
insert `d β`. -/
private theorem sum_stasheffDiff_add_stasheffMul_const [CharP R 2]
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) {β : A}
    (hβ : d β = β * β) (m : M) (N : ℕ) :
    ∑ n ∈ range (N + 1),
        (ungradedStasheffDiff f d n (fun _ => β) m + ungradedStasheffMul f n (fun _ => β) m) =
      ungradedStasheffDiff f d N (fun _ => β) m := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hmul : ungradedStasheffMul f (N + 1) (fun _ => β) m =
        ungradedStasheffDiff f d N (fun _ => β) m := by
      simp [ungradedStasheffMul_succ, ungradedStasheffDiff, Fin.contractNth_castSucc_const, hβ]
    rw [sum_range_succ, ih, hmul, add_comm (ungradedStasheffDiff f d (N + 1) _ m), ← add_assoc,
      add_self_eq_zero_of_charTwo R, zero_add]

/-- **The maps induced on twisted modules.** Let `β` be a Maurer–Cartan element,
`d β + β * β = 0`, over a ring of characteristic two. Suppose that the operations
`m_{n+1}(·, β, …, β)` of `M` and `M'` vanish for `n ≥ K`, and that `f_{n+1}` vanishes for `n ≥ K`
on every tuple of elements of a set `U` containing `β` and `β * β`. Then the twists
`f^β = ∑ₙ f_{n+1}(·, β, …, β)` (`TauCeti.ungradedTwistedMap`) satisfy
`∂'^β ∘ f^β + f^β ∘ ∂^β = (∂f)^β`, where `∂^β` and `∂'^β` are the twisted differentials. In
particular a homomorphism induces a chain map, and homotopic homomorphisms induce homotopic chain
maps. -/
theorem twistedDifferential_ungradedTwistedMap [CharP R 2]
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) {β : A}
    (hβ : d β + β * β = 0) {U : Set A} (hβU : β ∈ U) (hββU : β * β ∈ U) {K : ℕ}
    (hK : ∀ n, K ≤ n → (Mm.act n fun _ => β) = 0) (hK' : ∀ n, K ≤ n → (Mm'.act n fun _ => β) = 0)
    (hf : ∀ n, K ≤ n → ∀ u : Fin n → A, (∀ l, u l ∈ U) → f n u = 0) (m : M) :
    Mm'.twistedDifferential β (ungradedTwistedMap f β m) +
        ungradedTwistedMap f β (Mm.twistedDifferential β m) =
      ungradedTwistedMap (Mm.morphismDifferential Mm' f) β m := by
  have hdβ : d β = β * β := (add_eq_zero_iff_eq_of_charTwo R).mp hβ
  have hfβ : ∀ n, K ≤ n → (f n fun _ => β) = 0 := fun n hn => hf n hn _ fun _ => hβU
  -- Inserting `d β = β * β` once keeps a tuple in `U`, so these insertions vanish from arity `K`.
  have hins {n : ℕ} (hn : K ≤ n) (l : Fin n) : f n (Function.update (fun _ => β) l (β * β)) = 0 :=
    hf n hn _ fun t => by
      by_cases ht : t = l
      · subst ht; simpa using hββU
      · simpa [Function.update_of_ne ht] using hβU
  have hdiff {n : ℕ} (hn : K ≤ n) (m : M) : ungradedStasheffDiff f d n (fun _ => β) m = 0 :=
    sum_eq_zero fun l _ => by simp [hdβ, hins hn l]
  -- `(∂f)_{n+1}(·, β, …, β)` vanishes for `n > 2 K`.
  have hD : ∀ n, 2 * K + 1 ≤ n → (Mm.morphismDifferential Mm' f n fun _ => β) = 0 := by
    intro n hn
    refine LinearMap.ext fun m => ?_
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hmul : ungradedStasheffMul f (n + 1) (fun _ => β) m = 0 :=
      sum_eq_zero fun l _ => by simp [Fin.contractNth_castSucc_const, hins (by omega : K ≤ n) l]
    rw [morphismDifferential_apply, ungradedFamilyComp_const_eq_zero hfβ hK (by omega),
      ungradedFamilyComp_const_eq_zero hK' hfβ (by omega), hdiff (by omega), hmul]
    simp
  have hsplit (n : ℕ) : Mm.morphismDifferential Mm' f n (fun _ => β) m =
      ungradedFamilyComp Mm'.act f n (fun _ => β) m + ungradedFamilyComp f Mm.act n (fun _ => β) m +
        (ungradedStasheffDiff f d n (fun _ => β) m + ungradedStasheffMul f n (fun _ => β) m) := by
    rw [morphismDifferential_apply]
    abel
  rw [ungradedTwistedMap_eq_sum hD, LinearMap.sum_apply]
  simp only [hsplit, sum_add_distrib, sum_stasheffDiff_add_stasheffMul_const f hdβ,
    hdiff (by omega : K ≤ 2 * K), add_zero, sum_ungradedFamilyComp_const hK' hfβ,
    sum_ungradedFamilyComp_const hfβ hK, twistedDifferential_eq_ungradedTwistedMap]

end Morphism

end UngradedAInfinityRightModule

end TauCeti
