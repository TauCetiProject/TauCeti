/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA.Basic
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Type `DA` bimodules and associativity of the box tensor product

Bordered Heegaard Floer homology attaches to a three-manifold with two parametrized boundary
components a type `DA` bimodule, and gluing along one boundary component is a box tensor product.
This file sets up type `DA` bimodules over ungraded differential algebras
(`TauCeti.IsUngradedDGAlgebra`) over a ring of characteristic two, their box tensor products with
differential modules on one side and with type `D` structures on the other, the latter also over
the idempotents, and the associativity `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)` relating the two.

A type `DA` bimodule `P = ^B P_A`, of type `D` over `(B, dB)` on the left and of type `A` over
`(A, dA)` on the right, has operations `δ¹_{n+1} : P ⊗ A^{⊗ n} → B ⊗ P` for every `n ≥ 0`. As for
type `D` structures (`TauCeti.TypeDStructure`), we describe it in a basis of generators `y : Y`,
each lying in the summand of an idempotent `ιB (idem y)` of `B`:
`δ¹_{n+1}(y, a₁, …, aₙ) = ∑ y', δₙ(a) y y' ⊗ y'`, with coefficient matrices `δₙ(a₁, …, aₙ)`
multilinear in the inputs (`TauCeti.TypeDAStructure`). The structure relation of length `n` is

`∑_{i + j = n} δᵢ(a₁, …, aᵢ) * δⱼ(aᵢ₊₁, …, aₙ) + dB δₙ(a)`
`  + ∑_l δₙ(a₁, …, dA aₗ, …, aₙ) + ∑_l δₙ₋₁(a₁, …, aₗ aₗ₊₁, …, aₙ) = 0`,

the matrix form of `(μ₂ ⊗ 1) ∘ (1 ⊗ δ¹) ∘ δ¹ + (μ₁ ⊗ 1) ∘ δ¹ + δ¹ ∘ (1 ⊗ d) + δ¹ ∘ (1 ⊗ μ₂) = 0`,
with no signs over a ring of characteristic two. Only the idempotents of `B` are recorded in the
structure. The idempotents of `A` at the generators enter through the predicate
`TauCeti.TypeDAStructure.IsRightIdemCompatible`, for the box tensor product over the idempotents
below; strict unitality is not needed.

* **The type `A` module `M ⊠ P`.** For a differential right `B`-module `(M, dM)`, the row vectors
  `Y → M`, standing for `∑ y, ψ y ⊗ y`, form an `A∞` right module over `A`
  (`TauCeti.TypeDAStructure.boxModule`) with `m₁ ψ = dM ψ + ψ ⬝ δ₀` and
  `m_{n+1}(ψ, a) = ψ ⬝ δₙ(a)` for `n ≥ 1`, where `ψ ⬝ F = TauCeti.continuationMap R M F ψ`. Its
  `A∞` relations are the structure relations of `P`.
* **The type `D` structure `P ⊠ N`.** For a type `D` structure `N` over `A` with generators `X`,
  `P ⊠ N` is the type `D` structure over `B` on the generators `y ⊗ x`, written `(y, x)`, with
  `δ¹ (y ⊗ x) = ∑_k (δ¹_{k+1} ⊗ 1) (y ⊗ δᵏ x)` (`TauCeti.TypeDAStructure.boxTypeD`), where
  `δᵏ` is the iterate `TauCeti.TypeDStructure.iteratedCoeff`. The sum is finite when `N` is
  bounded or the operations of `P` vanish from some arity on.
* **Boundedness of `P ⊠ N`.** A finite set of generators does not make `P ⊠ N` bounded, so its
  boundedness is a separate statement. If the coefficients of `N` strictly increase a height `h`
  and those of `δ¹₁` of `P` strictly increase a height `g`, then the coefficients of `P ⊠ N`
  strictly increase the height `(c + 1) h(x) + g(y)` on its generators `(y, x)`, with `c` the
  largest value of `g` (`TauCeti.TypeDAStructure.lt_of_boxCoeff_ne_zero`), and `P ⊠ N` is bounded
  (`TauCeti.TypeDAStructure.isBounded_boxTypeD_of_lt`). It can then be paired in turn with type `A`
  modules and type `DA` bimodules whose operations do not vanish from any arity on.
* **Associativity.** The box tensor differential of the type `A` module `M ⊠ P` with `N`
  (`TauCeti.TypeDStructure.typeABoxDifferential`) is the box tensor differential
  `∂ φ = dM φ + φ ⬝ δ` of `M` with `P ⊠ N` (`TauCeti.TypeDStructure.boxDifferential`)
  (`TauCeti.TypeDAStructure.typeABoxDifferential_boxModule_apply`, and
  `TauCeti.TypeDAStructure.typeABoxDifferential_boxModule` when `dB` is a differential, so that
  `P ⊠ N` is a type `D` structure). This is also how the structure
  equation of `P ⊠ N` is proved: for `M = B`, the row of `dB δ + δ * δ` at a generator `p` is the
  square of the box tensor differential at `1 ⊗ p`, which vanishes because the box tensor
  differential of the type `A` module `B ⊠ P` with `N` squares to zero.
* **The box tensor product over the idempotents.** If each generator `y` of `P` carries a right
  idempotent `ιA (idemA y)` of `A` for which the operations are right linear
  (`TauCeti.TypeDAStructure.IsRightIdemCompatible`), and the idempotents of `A` are orthogonal,
  then `δ¹` of `P ⊠ N` never leads from a generator `(y, x)` with `idemA y = idem x` to one with
  `idemA y' ≠ idem x'` (`TauCeti.TypeDAStructure.boxCoeff_eq_zero_of_isRightIdemCompatible`). The
  elementary tensors of the second kind vanish over the idempotents, so restricting `P ⊠ N` to the
  matching generators gives the box tensor product `P ⊠_I N` over the idempotents, a type `D`
  structure over `B` (`TauCeti.TypeDAStructure.boxTensorTypeD`).
* **The identity bimodule.** When the idempotents `ι s` of `A` are cycles summing to `1`, the
  identity bimodule `[I]` (`TauCeti.TypeDAStructure.identity`) has one generator at each
  idempotent and the single operation `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t`. If the idempotents are
  moreover orthogonal, the coefficients of `[I] ⊠ N` restricted to the generators `(idem x, x)` are
  those of `N`, and the other generators carry zero coefficients
  (`TauCeti.TypeDAStructure.boxCoeff_identity`). The identity bimodule is compatible with the
  right idempotents `s ↦ s` (`TauCeti.TypeDAStructure.isRightIdemCompatible_identity`), and
  `[I] ⊠_I N` is `N`: its generators are the pairs `(idem x, x)`, with the idempotents and the
  coefficients of `N` (`TauCeti.TypeDAStructure.boxTensorTypeD_identity_idem`,
  `TauCeti.TypeDAStructure.boxTensorTypeD_identity_coeff`).

The tensor products in `M ⊠ P` and `P ⊠ N` are taken over `R` on the generators, as for the box
tensor differential of `TauCeti.LowDimTopology.Bordered.TypeA`; the elementary tensors `y ⊗ x` whose
idempotents do not match are among the generators of `P ⊠ N`, and they vanish in the tensor product
over the idempotents, which `P ⊠_I N` discards. The type `A` module `M ⊠ P` is built here from a
differential module `M`; for a general `A∞` module `M` whose operations vanish from some arity on it
is `TauCeti.TypeDAStructure.typeABoxModule`, in `TauCeti.LowDimTopology.Bordered.TypeA.BoxTypeDA`.
The associativity `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)` for such a module is not treated.

## Main definitions

* `TauCeti.TypeDAStructure`: a type `DA` bimodule, given by its generators, their idempotents and
  its coefficient matrices.
* `TauCeti.TypeDAStructure.boxModule`: the type `A` module `M ⊠ P`.
* `TauCeti.TypeDAStructure.boxCoeff` and `TauCeti.TypeDAStructure.boxTypeD`: the coefficient
  matrix of `P ⊠ N`, and `P ⊠ N` as a type `D` structure.
* `TauCeti.TypeDAStructure.IsRightIdemCompatible`: the operations of `P` are right linear over
  idempotents of `A` attached to its generators.
* `TauCeti.TypeDAStructure.boxTensorTypeD`: the box tensor product `P ⊠_I N` over the idempotents.
* `TauCeti.TypeDAStructure.identity`: the identity bimodule `[I]`.

## Main results

* `TauCeti.TypeDAStructure.map_boxCoeff_add_boxCoeff_mul_boxCoeff`: the structure equation of
  `P ⊠ N`.
* `TauCeti.TypeDAStructure.lt_of_boxCoeff_ne_zero`,
  `TauCeti.TypeDAStructure.isBounded_boxTypeD_of_lt` and
  `TauCeti.TypeDAStructure.isBounded_boxTensorTypeD_of_lt`: `P ⊠ N` and `P ⊠_I N` are bounded when
  `N` and `δ¹₁` of `P` increase heights.
* `TauCeti.TypeDAStructure.typeABoxDifferential_boxModule_apply` and
  `TauCeti.TypeDAStructure.typeABoxDifferential_boxModule`: associativity,
  `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)`, on row vectors and through the type `D` structure `P ⊠ N`.
* `TauCeti.TypeDAStructure.boxCoeff_eq_zero_of_isRightIdemCompatible`: `δ¹` of `P ⊠ N` does not
  lead from a generator with matching idempotents to one without.
* `TauCeti.TypeDAStructure.boxCoeff_identity`: the coefficients of `[I] ⊠ N` are those of `N` on
  the generators `(idem x, x)` and zero on the others.
* `TauCeti.TypeDAStructure.boxTensorTypeD_identity_coeff` and
  `TauCeti.TypeDAStructure.boxTensorTypeD_identity_idem`: `[I] ⊠_I N` is `N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (type `DA` bimodules over `𝔽₂`, the identity bimodule, and box tensor products of
  bimodules with modules and type `D` structures).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), Section 2
  (type `DA` bimodules and the associativity of box tensor products).
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-! ### The structure relations -/

section Relations

variable {Y : Type*}
  (coeff : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (Matrix Y Y B))

/-- The **composite terms** of the type `DA` structure relation of length `n`:
`∑_{i + j = n} δ_i(a₁, …, aᵢ) * δ_j(aᵢ₊₁, …, aₙ)`, the product of coefficient matrices. -/
noncomputable def typeDAComp [Fintype Y] (n : ℕ) (a : Fin n → A) : Matrix Y Y B :=
  ∑ k : Fin (n + 1), coeff k (fun l => a ⟨l, l.isLt.trans_le k.is_le⟩) *
    coeff (n - k) (fun l => a ⟨k + l, lt_tsub_iff_left.mp l.isLt⟩)

theorem typeDAComp_def [Fintype Y] (n : ℕ) (a : Fin n → A) :
    typeDAComp coeff n a =
      ∑ k : Fin (n + 1), coeff k (fun l => a ⟨l, l.isLt.trans_le k.is_le⟩) *
        coeff (n - k) (fun l => a ⟨k + l, lt_tsub_iff_left.mp l.isLt⟩) :=
  (rfl)

end Relations

variable (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) {S : Type*} (ιB : S → B) (Y : Type*) [Fintype Y]

/-- A **type `DA` bimodule** `^B P_A`, of type `D` over the differential algebra `(B, dB)` with
idempotents `ιB` and of type `A` over the differential algebra `(A, dA)`, in a basis of generators
`Y`. Each generator `y` lies in the summand of the idempotent `ιB (idem y)`, and the operation
`δ¹_{n+1}(y, a₁, …, aₙ) = ∑ y', coeff n a y y' ⊗ y'` has coefficient matrix `coeff n a`,
multilinear in `a`. The structure relations say that the composite terms `TauCeti.typeDAComp`,
the entrywise differential `dB` of `coeff n a`, the differential terms
`TauCeti.ungradedStasheffDiff` and the product terms `TauCeti.ungradedStasheffMul` sum to zero;
over a ring of characteristic two they need no signs. -/
@[ext]
structure TypeDAStructure where
  /-- The idempotent of `B` of each generator. -/
  idem : Y → S
  /-- The coefficient matrices: `δ¹_{n+1}(y, a₁, …, aₙ) = ∑ y', coeff n a y y' ⊗ y'`. -/
  coeff : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (Matrix Y Y B)
  /-- The coefficients from `y` lie in the summand of the idempotent of `y` on the left. -/
  idem_mul_coeff (n : ℕ) (a : Fin n → A) (y y' : Y) : ιB (idem y) * coeff n a y y' = coeff n a y y'
  /-- The coefficients to `y'` lie in the summand of the idempotent of `y'` on the right. -/
  coeff_mul_idem (n : ℕ) (a : Fin n → A) (y y' : Y) :
    coeff n a y y' * ιB (idem y') = coeff n a y y'
  /-- The type `DA` structure relation of length `n`. -/
  stasheff (n : ℕ) (a : Fin n → A) :
    typeDAComp coeff n a + (coeff n a).map dB + ungradedStasheffDiff coeff dA n a +
      ungradedStasheffMul coeff n a = 0

namespace TypeDAStructure

variable {dA dB ιB Y}

/-! ### The type `A` module `M ⊠ P` -/

section BoxModule

variable {M : Type*} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [SMulCommClass R Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M]

/-- The differential part of the operations of `M ⊠ P`: `m₁` contributes `dM` on each entry. -/
private noncomputable def diffAct (dM : M →ₗ[R] M) :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) ((Y → M) →ₗ[R] Y → M)
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _ (dM.compLeft Y)
  | _ + 1 => 0

omit [Fintype Y] in
private theorem diffAct_apply (dM : M →ₗ[R] M) (n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    diffAct (Y := Y) dM n a ψ = if n = 0 then fun y => dM (ψ y) else 0 := by
  cases n <;> rfl

omit [Fintype Y] in
private theorem diffAct_succ (dM : M →ₗ[R] M) (n : ℕ) : diffAct (A := A) (Y := Y) dM (n + 1) = 0 :=
  MultilinearMap.ext fun a => LinearMap.ext fun ψ => by
    rw [diffAct_apply, ite_eq_right n.succ_ne_zero, zero_apply, LinearMap.zero_apply]

variable (P : TypeDAStructure dA dB ιB Y)

/-- The operations of `M ⊠ P`. -/
private noncomputable def boxAct (dM : M →ₗ[R] M) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) ((Y → M) →ₗ[R] Y → M) :=
  diffAct dM n + (continuationMapₗ R M Y Y).compMultilinearMap (P.coeff n)

private theorem boxAct_apply (dM : M →ₗ[R] M) (n : ℕ) (a : Fin n → A) (ψ : Y → M) :
    P.boxAct dM n a ψ =
      (if n = 0 then fun y => dM (ψ y) else 0) + continuationMap R M (P.coeff n a) ψ := by
  rw [boxAct, add_apply, LinearMap.add_apply, diffAct_apply, LinearMap.compMultilinearMap_apply,
    continuationMapₗ_apply]

/-- The operation `m_{n+1}` of `M ⊠ P`, `n ≥ 1`, is right multiplication by `δₙ`. -/
private theorem boxAct_apply_of_ne_zero (dM : M →ₗ[R] M) {n : ℕ} (hn : n ≠ 0) (a : Fin n → A)
    (ψ : Y → M) : P.boxAct dM n a ψ = continuationMap R M (P.coeff n a) ψ := by
  rw [boxAct_apply, ite_eq_right hn, zero_add]

/-- A coefficient matrix only depends on the length and the entries of its tuple of inputs. -/
theorem coeff_congr {m n : ℕ} (h : m = n) {b : Fin m → A} {a : Fin n → A}
    (hab : ∀ l, b l = a (Fin.cast h l)) : P.coeff m b = P.coeff n a := by
  subst h
  congr 1
  exact funext hab

/-- The composite terms of the `A∞` relations of `M ⊠ P`: the composites of the products with
`δᵢ` and `δⱼ` give the composite terms of the type `DA` relation, the differential of `M` after
`m_{n+1}` gives `dM ψ ⬝ δₙ + ψ ⬝ dB δₙ` by the Leibniz rule, and the differential before `m_{n+1}`
gives `dM ψ ⬝ δₙ` once more. -/
private theorem ungradedStasheffComp_boxAct {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule dB dM)
    (n : ℕ) (a : Fin n → A) (φ : Y → M) :
    ungradedStasheffComp (P.boxAct dM) n a φ =
      continuationMap R M (typeDAComp P.coeff n a) φ +
        continuationMap R M ((P.coeff n a).map dB) φ +
        (continuationMap R M (P.coeff n a) (fun y => dM (φ y)) +
          continuationMap R M (P.coeff n a) (fun y => dM (φ y))) := by
  -- The composite of `m_{k+1}` followed by `m_{n-k+1}`, split into its three parts.
  have hterm (k : ℕ) (b : Fin k → A) (c : Fin (n - k) → A) :
      P.boxAct dM (n - k) c (P.boxAct dM k b φ) =
        (if n - k = 0 then fun y => dM (P.boxAct dM k b φ y) else 0) +
        (continuationMap R M (P.coeff (n - k) c) (if k = 0 then fun y => dM (φ y) else 0) +
          continuationMap R M (P.coeff k b * P.coeff (n - k) c) φ) := by
    rw [boxAct_apply P dM (n - k)]
    congr 1
    rw [boxAct_apply P dM k, map_add, continuationMap_matMul, LinearMap.comp_apply]
  -- Only the last composite has `m₁` outside.
  have hlast : ∑ k : Fin (n + 1), (if n - (k : ℕ) = 0 then
        fun y => dM (P.boxAct dM k (fun l => a ⟨l, l.isLt.trans_le k.is_le⟩) φ y) else 0) =
      fun y => dM (P.boxAct dM n a φ y) := by
    rw [Finset.sum_eq_single (Fin.last n) (fun k _ hk => ite_eq_right (by
      have := Fin.val_lt_last hk; omega)) (by simp),
      ite_eq_left (by simp), boxAct_apply, boxAct_apply, P.coeff_congr (Fin.val_last n),
      Fin.val_last]
    exact fun l => congrArg a (Fin.ext (by simp))
  -- Only the first composite has `m₁` inside.
  have hfirst : ∑ k : Fin (n + 1),
      continuationMap R M (P.coeff (n - k) fun l => a ⟨k + l, lt_tsub_iff_left.mp l.isLt⟩)
        (if (k : ℕ) = 0 then fun y => dM (φ y) else 0) =
      continuationMap R M (P.coeff n a) (fun y => dM (φ y)) := by
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      rw [ite_eq_right (Fin.val_ne_zero_iff.mpr hk), map_zero]) (by simp),
      ite_eq_left (Fin.val_zero _), P.coeff_congr (n := n) (by simp)]
    exact fun l => congrArg a (Fin.ext (by rw [Fin.val_cast]; simp))
  -- The Leibniz rule for `dM (ψ ⬝ δₙ)`.
  have hdM : (fun y => dM (P.boxAct dM n a φ y)) =
      continuationMap R M (P.coeff n a) (fun y => dM (φ y)) +
        continuationMap R M ((P.coeff n a).map dB) φ := by
    funext y
    rw [boxAct_apply, Pi.add_apply, map_add, hM.map_continuationMap, Pi.add_apply]
    split_ifs
    · rw [hM.map_map, zero_add]
    · rw [Pi.zero_apply, map_zero, zero_add]
  rw [ungradedStasheffComp_def, Finset.sum_congr rfl fun (k : Fin (n + 1)) _ => hterm k _ _,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hlast, hfirst, hdM, typeDAComp_def,
    continuationMap_sum, LinearMap.sum_apply]
  abel

variable [CharP R 2]

/-- **The box tensor product `M ⊠ P` of a differential module with a type `DA` bimodule.** For a
differential right `B`-module `(M, dM)` and a type `DA` bimodule `P = ^B P_A`, the row
vectors `Y → M`, standing for `∑ y, ψ y ⊗ y`, form an `A∞` right module over `A` with operations
`m₁ ψ = dM ψ + ψ ⬝ δ₀` and `m_{n+1}(ψ, a₁, …, aₙ) = ψ ⬝ δₙ(a₁, …, aₙ)` for `n ≥ 1`, over a ring
of characteristic two. -/
noncomputable def boxModule {dM : M →ₗ[R] M} (hM : IsUngradedDGRightModule dB dM) :
    UngradedAInfinityRightModule dA (Y → M) where
  act := P.boxAct dM
  stasheff n a φ := by
    -- The `A∞` relations are the type `DA` structure relations, multiplied on the left by `φ`:
    -- the two terms `dM φ ⬝ δₙ` from `m₁` acting before and after `m_{n+1}` cancel, and the
    -- Leibniz rule turns `dM (φ ⬝ δₙ)` into the differential term `φ ⬝ dB δₙ`.
    have hcomp := P.ungradedStasheffComp_boxAct hM n a φ
    have hdiff : ungradedStasheffDiff (P.boxAct dM) dA n a φ =
        continuationMap R M (ungradedStasheffDiff P.coeff dA n a : Matrix Y Y B) φ := by
      rw [ungradedStasheffDiff_apply, ungradedStasheffDiff_def, continuationMap_sum,
        LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun l _ => P.boxAct_apply_of_ne_zero dM l.pos.ne' _ _
    have hmul : ungradedStasheffMul (P.boxAct dM) n a φ =
        continuationMap R M (ungradedStasheffMul P.coeff n a : Matrix Y Y B) φ := by
      cases n with
      | zero => simp
      | succ n =>
        rw [ungradedStasheffMul_succ_apply, ungradedStasheffMul_succ, continuationMap_sum,
          LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun l _ => P.boxAct_apply_of_ne_zero dM l.pos.ne' _ _
    rw [hcomp, hdiff, hmul, add_self_eq_zero_of_charTwo R, add_zero]
    calc _ = continuationMap R M (typeDAComp P.coeff n a + (P.coeff n a).map dB +
          ungradedStasheffDiff P.coeff dA n a + ungradedStasheffMul P.coeff n a) φ := by
          simp only [continuationMap_add, LinearMap.add_apply]
      _ = 0 := by rw [P.stasheff, continuationMap_zero, LinearMap.zero_apply]

end BoxModule

/-! ### The type `D` structure `P ⊠ N` -/

section BoxTypeD

variable {T : Type*} {ιA : T → A} {X : Type*} [Fintype X] [DecidableEq X]
  (P : TypeDAStructure dA dB ιB Y) (N : TypeDStructure dA ιA X)

/-- The **coefficient matrix of the box tensor product** `P ⊠ N` of a type `DA` bimodule with a
type `D` structure, on the generators `y ⊗ x` written `(y, x)`:
`δ¹ (y ⊗ x) = ∑_k (δ¹_{k+1} ⊗ 1) (y ⊗ δᵏ x)`, so the coefficient from `(y, x)` to `(y', x')` is the
sum over `k` of the coefficient `y → y'` of `δ¹_{k+1}` evaluated on the iterate `δᵏ` from `x` to
`x'`. The sum is finite when `N` is bounded or the operations of `P` vanish from some arity on;
otherwise this `finsum` is `0` by convention. -/
noncomputable def boxCoeff : Matrix (Y × X) (Y × X) B :=
  fun p q => ∑ᶠ k, PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k p.2 q.2) p.1 q.1

theorem boxCoeff_apply (p q : Y × X) :
    P.boxCoeff N p q = ∑ᶠ k, PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k p.2 q.2) p.1 q.1 :=
  (rfl)

/-- When the terms of length at least `K` vanish, the coefficients of `P ⊠ N` are the sums over the
lengths `k < K`. -/
theorem boxCoeff_eq_sum {K : ℕ}
    (hK : ∀ k, K ≤ k → ∀ x x', PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k x x') = 0)
    (p q : Y × X) :
    P.boxCoeff N p q =
      ∑ k ∈ range K, PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k p.2 q.2) p.1 q.1 := by
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  rw [Function.mem_support] at hk
  simp only [coe_range, Set.mem_Iio]
  by_contra hlt
  exact hk (by simp only [hK k (not_lt.mp hlt), Matrix.zero_apply])

/-- A coefficient of `δ¹_{k+1}` evaluated on a tensor lies in the summand of the idempotent of its
source on the left and of its target on the right. -/
private theorem idem_mul_lift_coeff_mul_idem (k : ℕ) (t : PiTensorProduct R fun _ : Fin k => A)
    (y y' : Y) :
    ιB (P.idem y) * PiTensorProduct.lift (P.coeff k) t y y' =
        PiTensorProduct.lift (P.coeff k) t y y' ∧
      PiTensorProduct.lift (P.coeff k) t y y' * ιB (P.idem y') =
        PiTensorProduct.lift (P.coeff k) t y y' := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Matrix.smul_apply, mul_smul_comm,
      smul_mul_assoc, P.idem_mul_coeff, P.coeff_mul_idem, and_self]
  | add t t' ht ht' =>
    simp only [map_add, Matrix.add_apply, mul_add, add_mul, ht.1, ht.2, ht'.1, ht'.2, and_self]

theorem idem_mul_boxCoeff (p q : Y × X) : ιB (P.idem p.1) * P.boxCoeff N p q = P.boxCoeff N p q :=
  mul_finsum_of_forall fun k => (P.idem_mul_lift_coeff_mul_idem k _ p.1 q.1).1

theorem boxCoeff_mul_idem (p q : Y × X) : P.boxCoeff N p q * ιB (P.idem q.1) = P.boxCoeff N p q :=
  finsum_mul_of_forall fun k => (P.idem_mul_lift_coeff_mul_idem k _ p.1 q.1).2

/-- **The coefficients of `P ⊠ N` increase a height.** Suppose that the coefficients of `N`
strictly increase a height `h` on its generators and that those of `δ¹₁` of `P` strictly increase
a height `g` on its generators. Then a nonzero coefficient of `P ⊠ N` from `(y, x)` to `(y', x')`
strictly increases the height `(c + 1) h(x) + g(y)`, where `c` is the largest value of `g`: such a
coefficient comes either from `δ¹₁` of `P` with `x' = x`, raising `g`, or from a nonzero iterate
`δᵏ` of `N` with `k ≥ 1`, raising `h`. -/
theorem lt_of_boxCoeff_ne_zero (g : Y → ℕ) (hg : ∀ a y y', P.coeff 0 a y y' ≠ 0 → g y < g y')
    (h : X → ℕ) (hh : ∀ x x', N.coeff x x' ≠ 0 → h x < h x') {p q : Y × X}
    (hpq : P.boxCoeff N p q ≠ 0) :
    (univ.sup g + 1) * h p.2 + g p.1 < (univ.sup g + 1) * h q.2 + g q.1 := by
  obtain ⟨k, hk⟩ : ∃ k, PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k p.2 q.2) p.1 q.1 ≠ 0 :=
    not_forall.mp fun h0 => hpq (finsum_eq_zero_of_forall_eq_zero h0)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- `δ⁰` is the identity, so `x` stays put while `δ¹₁` of `P` raises `g`.
    rw [N.iteratedCoeff_zero] at hk
    split_ifs at hk with hx
    · rw [PiTensorProduct.lift.tprod] at hk
      rw [hx]
      have := hg _ _ _ hk
      omega
    · rw [map_zero, Matrix.zero_apply] at hk
      exact absurd rfl hk
  · -- A nonzero iterate `δᵏ` with `k ≥ 1` raises `h`, which outweighs any change of `g`.
    have hN : N.iteratedCoeff k p.2 q.2 ≠ 0 := fun h0 => hk (by
      rw [h0, map_zero, Matrix.zero_apply])
    have h₁ : (univ.sup g + 1) * (h p.2 + 1) ≤ (univ.sup g + 1) * h q.2 :=
      Nat.mul_le_mul_left _ (by have := N.add_le_of_iteratedCoeff_ne_zero h hh hN; omega)
    have h₂ := Finset.le_sup (f := g) (Finset.mem_univ p.1)
    rw [mul_add, mul_one] at h₁
    omega

end BoxTypeD

/-! ### Associativity -/

section Associativity

variable {T : Type*} {ιA : T → A} {X : Type*} [Fintype X] [DecidableEq X]
  {M : Type*} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [SMulCommClass R Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M] [CharP R 2] {dM : M →ₗ[R] M}
  (P : TypeDAStructure dA dB ιB Y) (N : TypeDStructure dA ιA X)

private theorem boxModule_act (hM : IsUngradedDGRightModule dB dM) (n : ℕ) :
    (P.boxModule hM).act n = P.boxAct dM n :=
  (rfl)

/-- The operations of `M ⊠ P`: `m₁ ψ = dM ψ + ψ ⬝ δ₀` and `m_{n+1}(ψ, a) = ψ ⬝ δₙ(a)`, `n ≥ 1`. -/
@[simp]
theorem boxModule_act_apply (hM : IsUngradedDGRightModule dB dM) (n : ℕ) (a : Fin n → A)
    (ψ : Y → M) :
    (P.boxModule hM).act n a ψ =
      (if n = 0 then fun y => dM (ψ y) else 0) + continuationMap R M (P.coeff n a) ψ :=
  P.boxAct_apply dM n a ψ

/-- The operation `m_{n+1}` of `M ⊠ P`, `n ≥ 1`, vanishes when `δ¹_{n+1}` does. -/
theorem boxModule_act_eq_zero (hM : IsUngradedDGRightModule dB dM) {n : ℕ} (hn : n ≠ 0)
    (hP : P.coeff n = 0) : (P.boxModule hM).act n = 0 :=
  MultilinearMap.ext fun a => LinearMap.ext fun ψ => by
    simp only [boxModule_act, P.boxAct_apply_of_ne_zero dM hn, hP, zero_apply,
      continuationMap_zero, LinearMap.zero_apply]

/-- Evaluating the operations of `M ⊠ P` on a tensor: the differential of `M` on the empty tensor,
and the action of `δ¹_{n+1}` evaluated on the tensor. -/
private theorem lift_boxModule_act (hM : IsUngradedDGRightModule dB dM) (n : ℕ) (x z : X)
    (ψ : Y → M) :
    PiTensorProduct.lift ((P.boxModule hM).act n) (N.iteratedCoeff n x z) ψ =
      (if n = 0 ∧ x = z then fun y => dM (ψ y) else 0) +
        continuationMap R M (PiTensorProduct.lift (P.coeff n) (N.iteratedCoeff n x z)) ψ := by
  have hL : PiTensorProduct.lift ((continuationMapₗ R M Y Y).compMultilinearMap (P.coeff n)) =
      continuationMapₗ R M Y Y ∘ₗ PiTensorProduct.lift (P.coeff n) :=
    PiTensorProduct.ext (MultilinearMap.ext fun a => by simp)
  rw [boxModule_act, boxAct, map_add, hL, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.comp_apply, continuationMapₗ_apply]
  congr 1
  cases n with
  | zero =>
    rw [N.iteratedCoeff_zero]
    by_cases hxz : x = z
    · rw [ite_eq_left hxz, PiTensorProduct.lift.tprod, ite_eq_left ⟨rfl, hxz⟩, diffAct_apply,
        ite_eq_left rfl]
    · rw [ite_eq_right hxz, map_zero, ite_eq_right fun h => hxz h.2, LinearMap.zero_apply]
  | succ n =>
    rw [ite_eq_right fun h => Nat.succ_ne_zero n h.1, diffAct_succ, map_zero,
      LinearMap.zero_apply, LinearMap.zero_apply]

/-- Under either boundedness hypothesis, a single length `K ≥ 1` bounds both the nonzero operations
of the matrix module of `M ⊠ P` along the coefficients of `N` and the nonzero terms of the
coefficients of `P ⊠ N`. -/
private theorem exists_bound (hM : IsUngradedDGRightModule dB dM)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    ∃ K, 1 ≤ K ∧
      (∀ n, K ≤ n → ((P.boxModule hM).matrixAct X n fun _ => N.coeff) = 0) ∧
      ∀ k, K ≤ k → ∀ x x', PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k x x') = 0 := by
  rcases h with hN | ⟨K, hK⟩
  · obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
    refine ⟨K + 1, by omega, fun n hn => ?_, fun k hk x x' => by rw [hK k (by omega), map_zero]⟩
    exact N.matrixAct_eq_zero_of_iteratedCoeff_eq_zero _ (hK n (by omega)) fun _ => Or.inl rfl
  · refine ⟨K + 1, by omega, fun n hn => ?_, fun k hk x x' => by
      rw [hK k (by omega), map_zero, LinearMap.zero_apply]⟩
    rw [(P.boxModule hM).matrixAct_eq_zero_of_act_eq_zero X
      (P.boxModule_act_eq_zero hM (by omega) (hK n (by omega))), zero_apply]

/-- **Associativity of the box tensor product, on row vectors.** For a differential right
`B`-module `(M, dM)`, a type `DA` bimodule `P = ^B P_A` and a type `D` structure `N` over
`A`, one of `N` and `P` bounded, the box tensor differential of the type `A` module `M ⊠ P` with
`N` is the box tensor differential `∂ = dM + · ⬝ δ` of `M` with `P ⊠ N`: on a row vector `φ`,
standing for `∑ m ⊗ y ⊗ x` with coefficients `φ x y`,
`∂ φ = dM φ + φ ⬝ (P ⊠ N)` at the generator `y' ⊗ z`. -/
theorem typeABoxDifferential_boxModule_apply (hM : IsUngradedDGRightModule dB dM)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (φ : X → Y → M) (z : X) (y' : Y) :
    N.typeABoxDifferential (P.boxModule hM) φ z y' =
      dM (φ z y') + continuationMap R M (P.boxCoeff N) (fun p => φ p.2 p.1) (y', z) := by
  obtain ⟨K, hK1, hKm, hKl⟩ := P.exists_bound N hM h
  rw [N.typeABoxDifferential_apply_eq_sum_lift_iteratedCoeff _ hKm, Finset.sum_apply]
  simp only [Finset.sum_apply, P.lift_boxModule_act N hM, Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  · -- Only the empty path from `z` to itself contributes the differential of `M`.
    rw [Finset.sum_eq_single 0 (fun n _ hn => Finset.sum_eq_zero fun x _ => by
      rw [ite_eq_right fun h => hn h.1, Pi.zero_apply])
        (fun h => (h (Finset.mem_range.mpr hK1)).elim),
      Finset.sum_eq_single z (fun x _ hx => by
        rw [ite_eq_right fun h => hx h.2, Pi.zero_apply])
        (by simp), ite_eq_left ⟨rfl, rfl⟩]
  · rw [continuationMap_apply (R := R) (M := M) (P.boxCoeff N), Fintype.sum_prod_type]
    have hL (k : ℕ) (x : X) :
        continuationMap R M (PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k x z)) (φ x) y' =
          ∑ y, op (PiTensorProduct.lift (P.coeff k) (N.iteratedCoeff k x z) y y') • φ x y :=
      continuationMap_apply (R := R) (M := M) _ _ _
    simp only [P.boxCoeff_eq_sum N hKl, Finset.op_sum, Finset.sum_smul, hL]
    -- Reorder the sum `∑ k, ∑ x, ∑ y` over lengths `k`, sources `x` and generators `y` of `P` into
    -- `∑ y, ∑ x, ∑ k`: swap the outer `k` and `x`, then `k` and `y` under `x`, then the outer
    -- `x` and `y`.
    exact (Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm)).trans
      Finset.sum_comm

/-- **The structure equation of `P ⊠ N`.** If `dB` is a differential, over a ring of characteristic
two, and `N` is bounded or the operations of `P` vanish from some arity on, the coefficient matrix
`δ` of `P ⊠ N` satisfies `dB δ + δ * δ = 0`. -/
theorem map_boxCoeff_add_boxCoeff_mul_boxCoeff (hdB : IsUngradedDGAlgebra dB)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    (P.boxCoeff N).map dB + P.boxCoeff N * P.boxCoeff N = 0 := by
  classical
  -- The row of `δ` at `p` is the box tensor differential of the generator `1 ⊗ p` of
  -- `B ⊠ (P ⊠ N)`, which by associativity is the box tensor differential of the type `A` module
  -- `B ⊠ P` with `N`. That differential squares to zero, and its square at `1 ⊗ p` is the row at
  -- `p` of `dB δ + δ * δ`.
  have hB := hdB.isUngradedDGRightModule
  have hsq (φ : X → Y → B) : N.typeABoxDifferential (P.boxModule hB)
      (N.typeABoxDifferential (P.boxModule hB) φ) = 0 := by
    rcases h with hN | ⟨K, hK⟩
    · exact N.typeABoxDifferential_typeABoxDifferential_of_isBounded _ hN φ
    · exact N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero _ (K := K + 1)
        (fun n hn => P.boxModule_act_eq_zero hB (by omega) (hK n (by omega))) φ
  ext p₀ q₀
  -- The box tensor differential of the generator `1 ⊗ p₀` is the row of `δ` at `p₀`.
  set e : X → Y → B := fun x y => Pi.single (M := fun _ : Y × X => B) p₀ 1 (y, x) with he
  have hrow : N.typeABoxDifferential (P.boxModule hB) e =
      fun x y => P.boxCoeff N p₀ (y, x) := by
    funext x y
    rw [P.typeABoxDifferential_boxModule_apply N hB h]
    simp only [he, Prod.mk.eta]
    rw [continuationMap_single_apply (R := R) (M := B) (P.boxCoeff N), op_smul_eq_mul, one_mul]
    rcases eq_or_ne (y, x) p₀ with hp | hp
    · rw [hp, Pi.single_eq_same, hdB.map_one, zero_add]
    · rw [Pi.single_eq_of_ne hp, map_zero, zero_add]
  have h₀ := congrFun (congrFun (hsq e) q₀.2) q₀.1
  rw [hrow, P.typeABoxDifferential_boxModule_apply N hB h,
    continuationMap_apply (R := R) (M := B) (P.boxCoeff N)] at h₀
  -- Its square at `1 ⊗ p₀` is the entry of `dB δ + δ * δ`.
  have hentry : ((P.boxCoeff N).map dB + P.boxCoeff N * P.boxCoeff N) p₀ q₀ =
      dB (P.boxCoeff N p₀ (q₀.1, q₀.2)) +
        ∑ p, op (P.boxCoeff N p (q₀.1, q₀.2)) • P.boxCoeff N p₀ (p.1, p.2) := by
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, op_smul_eq_mul, Prod.mk.eta]
  rw [hentry, Matrix.zero_apply]
  exact h₀

/-- **The box tensor product `P ⊠ N`** of a type `DA` bimodule `^B P_A` with a type `D`
structure over `A`, a type `D` structure over `B` on the generators `y ⊗ x`, written `(y, x)`, with
the idempotent of `y` and the coefficients `TauCeti.TypeDAStructure.boxCoeff`. It is defined when
`N` is bounded or the operations of `P` vanish from some arity on, over a ring of characteristic
two. -/
noncomputable def boxTypeD (hdB : IsUngradedDGAlgebra dB)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) : TypeDStructure dB ιB (Y × X) where
  idem p := P.idem p.1
  coeff := P.boxCoeff N
  idem_mul_coeff := P.idem_mul_boxCoeff N
  coeff_mul_idem := P.boxCoeff_mul_idem N
  map_coeff_add_coeff_mul_coeff := P.map_boxCoeff_add_boxCoeff_mul_boxCoeff N hdB h

@[simp]
theorem boxTypeD_idem (hdB : IsUngradedDGAlgebra dB)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (p : Y × X) :
    (P.boxTypeD N hdB h).idem p = P.idem p.1 :=
  (rfl)

@[simp]
theorem boxTypeD_coeff (hdB : IsUngradedDGAlgebra dB)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    (P.boxTypeD N hdB h).coeff = P.boxCoeff N :=
  (rfl)

/-- **Boundedness of `P ⊠ N`.** If the coefficients of `N` strictly increase a height on its
generators and those of `δ¹₁` of `P` strictly increase a height on its generators, then the type
`D` structure `P ⊠ N` is bounded, so that it can itself be paired with type `A` modules and type
`DA` bimodules whose operations do not vanish from any arity on. -/
theorem isBounded_boxTypeD_of_lt [DecidableEq Y] (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (g : Y → ℕ)
    (hg : ∀ a y y', P.coeff 0 a y y' ≠ 0 → g y < g y') (h : X → ℕ)
    (hh : ∀ x x', N.coeff x x' ≠ 0 → h x < h x') : (P.boxTypeD N hdB hN).IsBounded :=
  TypeDStructure.isBounded_of_lt _ (fun p => (univ.sup g + 1) * h p.2 + g p.1)
    fun _ _ hpq => P.lt_of_boxCoeff_ne_zero N g hg h hh hpq

/-- **Associativity of the box tensor product**, `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)`: the box tensor
differential of the type `A` module `M ⊠ P` with `N` is the box tensor differential of the
differential module `M` with the type `D` structure `P ⊠ N`, under the identification of the row
vectors `X → Y → M` with the row vectors `Y × X → M`. -/
theorem typeABoxDifferential_boxModule (hM : IsUngradedDGRightModule dB dM)
    (hdB : IsUngradedDGAlgebra dB) (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (φ : X → Y → M) (z : X) (y' : Y) :
    N.typeABoxDifferential (P.boxModule hM) φ z y' =
      (P.boxTypeD N hdB h).boxDifferential dM (fun p => φ p.2 p.1) (y', z) := by
  rw [P.typeABoxDifferential_boxModule_apply N hM h, TypeDStructure.boxDifferential_apply,
    Pi.add_apply, boxTypeD_coeff]

end Associativity

/-! ### The box tensor product over the idempotents -/

section BoxTensor

variable {T : Type*} (P : TypeDAStructure dA dB ιB Y) (ιA : T → A)

/-- A type `DA` bimodule `^B P_A` is **compatible with right idempotents** `idemA` when each
generator `y` lies, on the right, in the summand of the idempotent `ιA (idemA y)` of `A`, and the
operations are right linear over the idempotents:
`δ¹_{k+1}(y, a₁, …, aₖ ι) = δ¹_{k+1}(y, a₁, …, aₖ) ι` for an idempotent `ι` of `A`, and
`δ¹₁(y ι) = δ¹₁(y) ι`. In terms of the coefficient matrices, for orthogonal idempotents: the
coefficient of `δ¹₁` from `y` to `y'` vanishes unless `y` and `y'` have the same idempotent, and
the coefficient of `δ¹_{k+1}` to `y'` only sees the last input through its summand
`aₖ * ιA (idemA y')`. -/
structure IsRightIdemCompatible (idemA : Y → T) : Prop where
  /-- `δ¹₁` preserves the right idempotents of the generators. -/
  coeff_zero_eq_zero (a : Fin 0 → A) {y y' : Y} (h : idemA y ≠ idemA y') : P.coeff 0 a y y' = 0
  /-- The coefficient to `y'` of `δ¹_{k+1}` only sees the summand `aₖ * ιA (idemA y')` of its
  last input. -/
  coeff_update_last_mul (n : ℕ) (a : Fin (n + 1) → A) (y y' : Y) :
    P.coeff (n + 1) (Function.update a (Fin.last n) (a (Fin.last n) * ιA (idemA y'))) y y' =
      P.coeff (n + 1) a y y'

variable {ιA} {X : Type*} [Fintype X] [DecidableEq X] (N : TypeDStructure dA ιA X) {idemA : Y → T}

/-- **The generators of `P ⊠ N` over the idempotents are closed under `δ¹`.** If `P` is compatible
with right idempotents `idemA` and the idempotents of `A` are orthogonal, the coefficient of
`P ⊠ N` from a generator `(y, x)` with `idemA y = idem x` to a generator `(y', x')` with
`idemA y' ≠ idem x'` vanishes: these elementary tensors `y' ⊗ x'` are zero over the idempotents,
and `δ¹` of `y ⊗ x` does not reach them. -/
theorem boxCoeff_eq_zero_of_isRightIdemCompatible (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) {p q : Y × X} (hp : idemA p.1 = N.idem p.2)
    (hq : idemA q.1 ≠ N.idem q.2) : P.boxCoeff N p q = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  cases k with
  | zero =>
    -- `δ⁰` is the identity, and `δ¹₁` preserves right idempotents.
    rw [N.iteratedCoeff_zero]
    split_ifs with hx
    · rw [PiTensorProduct.lift.tprod]
      exact hP.coeff_zero_eq_zero _ fun h' => hq (h'.symm.trans (hp.trans (congrArg N.idem hx)))
    · rw [map_zero, Matrix.zero_apply]
  | succ n =>
    -- The last coefficient of each path ends at `x'`, so it lies in `A * ιA (idem x')`, which
    -- `ιA (idemA y')` annihilates on the right.
    rw [N.lift_iteratedCoeff, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_filter] at hr
    rw [← hP.coeff_update_last_mul, MultilinearMap.map_coord_zero _ (Fin.last n),
      Matrix.zero_apply]
    simp only [Function.update_self, Fin.succ_last, hr.2.2]
    rw [← N.coeff_mul_idem, mul_assoc, hιA _ _ (Ne.symm hq), mul_zero]

variable [DecidableEq T] [CharP R 2]

/-- **The box tensor product over the idempotents** `P ⊠_I N` of a type `DA` bimodule compatible
with right idempotents `idemA` and a type `D` structure `N` over `A` with orthogonal idempotents:
the type `D` structure over `B` on the generators `y ⊗ x` with matching idempotents
`idemA y = idem x`, with the coefficients of `P ⊠ N`
(`TauCeti.TypeDAStructure.boxTypeD`). The other elementary tensors vanish in the tensor product
over the idempotents, and `δ¹` of `P ⊠ N` does not reach them from the matching ones
(`TauCeti.TypeDAStructure.boxCoeff_eq_zero_of_isRightIdemCompatible`). It is defined when `N` is
bounded or the operations of `P` vanish from some arity on, over a ring of characteristic two. -/
noncomputable def boxTensorTypeD (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    TypeDStructure dB ιB {p : Y × X // idemA p.1 = N.idem p.2} :=
  (P.boxTypeD N hdB h).restrict (fun p => idemA p.1 = N.idem p.2)
    fun _ _ hp hq => by
      rw [boxTypeD_coeff]
      exact P.boxCoeff_eq_zero_of_isRightIdemCompatible N hP hιA hp hq

variable {hP : P.IsRightIdemCompatible ιA idemA} {hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0}
  {hdB : IsUngradedDGAlgebra dB} {h : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0}

@[simp]
theorem boxTensorTypeD_idem (p : {p : Y × X // idemA p.1 = N.idem p.2}) :
    (P.boxTensorTypeD N hP hιA hdB h).idem p = P.idem p.val.1 := by
  rw [boxTensorTypeD, TypeDStructure.restrict_idem, boxTypeD_idem]

@[simp]
theorem boxTensorTypeD_coeff (p q : {p : Y × X // idemA p.1 = N.idem p.2}) :
    (P.boxTensorTypeD N hP hιA hdB h).coeff p q = P.boxCoeff N p q := by
  rw [boxTensorTypeD, TypeDStructure.restrict_coeff, boxTypeD_coeff]

/-- **Boundedness of `P ⊠_I N`.** If the coefficients of `N` strictly increase a height on its
generators and those of `δ¹₁` of `P` strictly increase a height on its generators, then the box
tensor product over the idempotents is bounded, as `P ⊠ N` is
(`TauCeti.TypeDAStructure.isBounded_boxTypeD_of_lt`). -/
theorem isBounded_boxTensorTypeD_of_lt [DecidableEq Y]
    (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (g : Y → ℕ)
    (hg : ∀ a y y', P.coeff 0 a y y' ≠ 0 → g y < g y') (h : X → ℕ)
    (hh : ∀ x x', N.coeff x x' ≠ 0 → h x < h x') :
    (P.boxTensorTypeD N hP hιA hdB hN).IsBounded :=
  TypeDStructure.isBounded_of_lt _ (fun p => (univ.sup g + 1) * h p.val.2 + g p.val.1)
    fun p q hpq => by
      rw [boxTensorTypeD_coeff] at hpq
      exact P.lt_of_boxCoeff_ne_zero N g hg h hh hpq

end BoxTensor

/-! ### The identity bimodule -/

section Identity

variable {d : A →ₗ[R] A} {ι : S → A}

variable (ι) in
/-- The map `a ↦ (ι s * a * ι t)_{s, t}` cutting an element of `A` into its idempotent blocks. -/
private noncomputable def blockLinear : A →ₗ[R] Matrix S S A where
  toFun a := Matrix.of fun s t => ι s * a * ι t
  map_add' a b := by ext; simp [mul_add, add_mul]
  map_smul' r a := by ext; simp

variable (ι) in
/-- The operations of the identity bimodule: `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t`, all others
zero. -/
private noncomputable def identityCoeff :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (Matrix S S A)
  | 0 => 0
  | 1 => MultilinearMap.ofSubsingleton (RingHom.id R) A (Matrix S S A) 0 (blockLinear ι)
  | _ + 2 => 0

private theorem identityCoeff_one_apply (a : Fin 1 → A) (s t : S) :
    identityCoeff (R := R) ι 1 a s t = ι s * a 0 * ι t :=
  (rfl)

private theorem identityCoeff_apply_of_eq_one {n : ℕ} (hn : n = 1) (a : Fin n → A) (s t : S) :
    identityCoeff (R := R) ι n a s t = ι s * a ⟨0, by omega⟩ * ι t := by
  subst hn
  rfl

private theorem identityCoeff_eq_zero {n : ℕ} (hn : n ≠ 1) :
    identityCoeff (R := R) ι n = 0 := by
  match n, hn with
  | 0, _ => rfl
  | _ + 2, _ => rfl

private theorem identityCoeff_apply_eq_zero {n : ℕ} (hn : n ≠ 1) (a : Fin n → A) :
    identityCoeff (R := R) ι n a = 0 := by
  rw [identityCoeff_eq_zero hn, zero_apply]

/-- The relation of length two of the identity bimodule:
`∑ u, ι s * a₀ * ι u * ι u * a₁ * ι t = ι s * a₀ * a₁ * ι t` cancels the product term. -/
private theorem identityCoeff_stasheff_two [Fintype S] [CharP R 2] (hιι : ∀ s, ι s * ι s = ι s)
    (hsum : ∑ s, ι s = 1) (a : Fin 2 → A) :
    typeDAComp (identityCoeff (R := R) ι) 2 a + (identityCoeff (R := R) ι 2 a).map d +
      ungradedStasheffDiff (identityCoeff (R := R) ι) d 2 a +
        ungradedStasheffMul (identityCoeff (R := R) ι) 2 a = 0 := by
  -- `∑ u, ι s * a₀ * ι u * ι u * a₁ * ι t = ι s * a₀ * a₁ * ι t`, the product term.
  have hmid : (identityCoeff (R := R) ι ((1 : Fin 3) : ℕ) fun l => a ⟨l, by omega⟩) *
      (identityCoeff (R := R) ι (2 - ((1 : Fin 3) : ℕ)) fun l =>
        a ⟨((1 : Fin 3) : ℕ) + l, by omega⟩) =
      identityCoeff (R := R) ι 1 fun _ => a 0 * a 1 := by
    ext s t
    simp only [Matrix.mul_apply, identityCoeff_apply_of_eq_one rfl]
    calc ∑ u, ι s * a 0 * ι u * (ι u * a 1 * ι t)
        = ι s * a 0 * (∑ u, ι u * ι u) * a 1 * ι t := by
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = ι s * (a 0 * a 1) * ι t := by
          simp only [hιι, hsum, mul_one, mul_assoc]
  have hmul : Fin.contractNth (0 : Fin 1).castSucc (· * ·) a = fun _ => a 0 * a 1 :=
    funext fun l => by
      rw [Fin.fin_one_eq_zero l, Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero,
        Fin.succ_zero_eq_one]
  -- Only the composite `δ₁ * δ₁` and the product term survive, and they cancel.
  rw [typeDAComp_def, Fin.sum_univ_three, hmid, ungradedStasheffDiff_def,
    ungradedStasheffMul_succ, Fin.sum_univ_one, hmul]
  simp only [ne_eq, identityCoeff_apply_eq_zero, Fin.val_zero, Fin.val_two, Nat.sub_zero,
    Nat.sub_self, zero_ne_one, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.mul_zero,
    Matrix.map_zero _ (map_zero d), Finset.sum_const_zero, zero_add, add_zero]
  exact add_self_eq_zero_of_charTwo R _

variable [Fintype S] [CharP R 2]

variable (ι) in
/-- **The identity type `DA` bimodule** `[I]` of a differential algebra `(A, d)` whose idempotents
`ι s` are cycles and sum to `1`, over a ring of characteristic two: one generator `s` at each
idempotent, with `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t` and all other operations zero. -/
noncomputable def identity (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) : TypeDAStructure d d ι S where
  idem s := s
  coeff := identityCoeff ι
  idem_mul_coeff n a s t := by
    rcases eq_or_ne n 1 with rfl | hn
    · rw [identityCoeff_one_apply, ← mul_assoc, ← mul_assoc, hιι]
    · rw [identityCoeff_apply_eq_zero hn, Matrix.zero_apply, mul_zero]
  coeff_mul_idem n a s t := by
    rcases eq_or_ne n 1 with rfl | hn
    · rw [identityCoeff_one_apply, mul_assoc, hιι]
    · rw [identityCoeff_apply_eq_zero hn, Matrix.zero_apply, zero_mul]
  stasheff n a := by
    -- The relation of length one is the Leibniz rule for `ι s * a * ι t`, and that of length two
    -- is `∑ u, ι s * a * ι u * ι u * b * ι t = ι s * a * b * ι t`.
    -- The only nonzero operation has one algebra input, so composites vanish except in length two.
    have hcomp (n : ℕ) (hn : n ≠ 2) (a : Fin n → A) :
        typeDAComp (identityCoeff (R := R) ι) n a = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rcases eq_or_ne (k : ℕ) 1 with hk | hk
        · rw [identityCoeff_apply_eq_zero (n := n - k) (by omega), Matrix.mul_zero]
        · rw [identityCoeff_apply_eq_zero hk, Matrix.zero_mul]
    match n with
    | 0 =>
      simp [hcomp 0 (by decide), ungradedStasheffDiff_def,
        identityCoeff_apply_eq_zero (n := 0) (by decide)]
    | 1 =>
      have hmap : (identityCoeff (R := R) ι 1 a).map d =
          identityCoeff (R := R) ι 1 fun _ => d (a 0) := by
        ext s t
        simp only [Matrix.map_apply, identityCoeff_one_apply, hd.map_mul, hι, mul_zero, zero_mul,
          add_zero, zero_add]
      have hupd : Function.update a 0 (d (a 0)) = fun _ => d (a 0) :=
        funext fun l => by rw [Fin.fin_one_eq_zero l, Function.update_self]
      simp only [hcomp 1 (by decide), hmap, ungradedStasheffDiff_def, Fin.sum_univ_one, hupd,
        ungradedStasheffMul_succ, identityCoeff_apply_eq_zero (n := 0) (by decide),
        Finset.sum_const_zero, zero_add, add_zero]
      exact add_self_eq_zero_of_charTwo R _
    | 2 => exact identityCoeff_stasheff_two hιι hsum a
    | n + 3 =>
      simp [hcomp (n + 3) (by omega), ungradedStasheffDiff_def, ungradedStasheffMul_succ,
        identityCoeff_apply_eq_zero]

@[simp]
theorem identity_idem (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) (s : S) :
    (identity ι hd hι hιι hsum).idem s = s :=
  (rfl)

/-- The operation `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t` of the identity bimodule. -/
@[simp]
theorem identity_coeff_one_apply (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) (a : Fin 1 → A) (s t : S) :
    (identity ι hd hι hιι hsum).coeff 1 a s t = ι s * a 0 * ι t :=
  (rfl)

/-- The operations of the identity bimodule other than `δ¹₂` vanish. -/
theorem identity_coeff_eq_zero (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) {n : ℕ} (hn : n ≠ 1) :
    (identity ι hd hι hιι hsum).coeff n = 0 :=
  identityCoeff_eq_zero hn

/-- The operations of the identity bimodule vanish from arity two on, so it can be boxed with any
type `D` structure (`TauCeti.TypeDAStructure.boxTypeD`). -/
theorem exists_forall_ge_identity_coeff_eq_zero (hd : IsUngradedDGAlgebra d)
    (hι : ∀ s, d (ι s) = 0) (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) :
    ∃ K, ∀ k, K ≤ k → (identity ι hd hι hιι hsum).coeff k = 0 :=
  ⟨2, fun _ hk => identity_coeff_eq_zero hd hι hιι hsum (by omega)⟩

/-- **The coefficients of `[I] ⊠ N`.** If moreover the idempotents are orthogonal, the coefficient
of `[I] ⊠ N` from `(s, x)` to `(t, x')` is the coefficient of `N` from `x` to `x'` when `s` and `t`
are the idempotents of `x` and `x'`, and zero otherwise. So the coefficients restricted to the
generators `(idem x, x)` are those of `N`, and the other generators, the elementary tensors
`s ⊗ x` with `ι s * ι (idem x) = 0` that vanish over the idempotents, carry zero coefficients. -/
theorem boxCoeff_identity (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) (hιo : ∀ s t, s ≠ t → ι s * ι t = 0)
    [DecidableEq S] {X : Type*} [Fintype X] [DecidableEq X] (N : TypeDStructure d ι X)
    (p q : S × X) :
    (identity ι hd hι hιι hsum).boxCoeff N p q =
      if p.1 = N.idem p.2 ∧ q.1 = N.idem q.2 then N.coeff p.2 q.2 else 0 := by
  have hzero {k : ℕ} (hk : k ≠ 1) (t : PiTensorProduct R fun _ : Fin k => A) :
      PiTensorProduct.lift ((identity ι hd hι hιι hsum).coeff k) t = 0 := by
    rw [identity_coeff_eq_zero hd hι hιι hsum hk, map_zero, LinearMap.zero_apply]
  simp only [boxCoeff_eq_sum _ N (K := 2) fun k hk x x' => hzero (by omega) _,
    Finset.sum_range_succ, Finset.sum_range_zero, hzero zero_ne_one, Matrix.zero_apply, zero_add,
    N.iteratedCoeff_one, PiTensorProduct.lift.tprod, identity_coeff_one_apply]
  -- `ι s * δ * ι t` with `δ = ι (idem x) * δ * ι (idem x')`.
  by_cases h₁ : p.1 = N.idem p.2
  · by_cases h₂ : q.1 = N.idem q.2
    · rw [ite_eq_left ⟨h₁, h₂⟩, h₁, h₂, N.idem_mul_coeff, N.coeff_mul_idem]
    · -- `δ = δ * ι (idem x')` and `ι (idem x') * ι t = 0`.
      rw [ite_eq_right fun h => h₂ h.2, ← N.coeff_mul_idem]
      simp only [mul_assoc, hιo _ _ (Ne.symm h₂), mul_zero]
  · -- `δ = ι (idem x) * δ` and `ι s * ι (idem x) = 0`.
    rw [ite_eq_right fun h => h₁ h.1, ← N.idem_mul_coeff]
    simp only [← mul_assoc, hιo _ _ h₁, zero_mul]

/-- The identity bimodule is compatible with right idempotents, the generator `s` lying on the
right in the summand of `ι s`: its only operation `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t` sees `a`
through `a * ι t` in its coefficient to `t`. -/
theorem isRightIdemCompatible_identity (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) :
    (identity ι hd hι hιι hsum).IsRightIdemCompatible ι id where
  coeff_zero_eq_zero a s t _ := by
    rw [identity_coeff_eq_zero hd hι hιι hsum zero_ne_one, zero_apply, Matrix.zero_apply]
  coeff_update_last_mul n a s t := by
    match n with
    | 0 => simp [identity_coeff_one_apply, mul_assoc, hιι]
    | n + 1 =>
      simp [identity_coeff_eq_zero hd hι hιι hsum (show n + 1 + 1 ≠ 1 by omega)]

variable [DecidableEq S] {X : Type*} [Fintype X] [DecidableEq X]

/-- **`[I] ⊠ N` is `N` over the idempotents.** If the idempotents are moreover orthogonal, the
generators of the box tensor product over the idempotents of the identity bimodule with `N` are
the pairs `(idem x, x)`, identified with the generators `x` of `N` by `p ↦ p.1.2`, and this
identification carries the coefficients of `[I] ⊠_I N` to those of `N`. It also carries the
idempotents (`TauCeti.TypeDAStructure.boxTensorTypeD_identity_idem`), so it is an isomorphism of
type `D` structures. -/
theorem boxTensorTypeD_identity_coeff (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) (hιo : ∀ s t, s ≠ t → ι s * ι t = 0)
    (N : TypeDStructure d ι X) (p q : {p : S × X // p.1 = N.idem p.2}) :
    ((identity ι hd hι hιι hsum).boxTensorTypeD N (isRightIdemCompatible_identity hd hι hιι hsum)
        hιo hd (Or.inr (exists_forall_ge_identity_coeff_eq_zero hd hι hιι hsum))).coeff
        p q =
      N.coeff p.val.2 q.val.2 := by
  rw [boxTensorTypeD_coeff, boxCoeff_identity hd hι hιι hsum hιo,
    ite_eq_left ⟨p.property, q.property⟩]

/-- The idempotent of a generator `(idem x, x)` of `[I] ⊠_I N` is the idempotent of `x`. -/
theorem boxTensorTypeD_identity_idem (hd : IsUngradedDGAlgebra d) (hι : ∀ s, d (ι s) = 0)
    (hιι : ∀ s, ι s * ι s = ι s) (hsum : ∑ s, ι s = 1) (hιo : ∀ s t, s ≠ t → ι s * ι t = 0)
    (N : TypeDStructure d ι X) (p : {p : S × X // p.1 = N.idem p.2}) :
    ((identity ι hd hι hιι hsum).boxTensorTypeD N (isRightIdemCompatible_identity hd hι hιι hsum)
        hιo hd (Or.inr (exists_forall_ge_identity_coeff_eq_zero hd hι hιι hsum))).idem
        p =
      N.idem p.val.2 := by
  rw [boxTensorTypeD_idem, identity_idem, p.property]

end Identity

end TypeDAStructure

end TauCeti
