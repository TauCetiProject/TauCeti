/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.TypeA

/-!
# Type `DA` bimodules and their box tensor product with type `D` structures

Bordered Heegaard Floer homology attaches to a three-manifold with two parametrized boundary
components a type `DA` bimodule `^A P_B`: type `D` over the algebra `A` of one boundary and type `A`
over the algebra `B` of the other. Gluing a manifold with a type `D` structure `N` over `B` along
the second boundary gives the type `D` structure `P ⊠ N` over `A`. This file sets up type `DA`
bimodules over ungraded differential algebras (`TauCeti.IsUngradedDGAlgebra`), over a ring of
characteristic two, and their box tensor product with type `D` structures
(`TauCeti.TypeDStructure`).

A type `DA` bimodule has maps `δ¹_{1+n} : P ⊗ B^{⊗ n} → A ⊗ P`. As for type `D` structures, we
describe it in a basis of generators `x : X`, each with an idempotent `ι (idemLeft x)` of `A` on the
left and an idempotent `κ (idemRight x)` of `B` on the right:
`δ¹_{1+n}(x, b₁, …, bₙ) = ∑ y, coeff n b x y ⊗ y`, with `coeff n` an `n`-multilinear map with
values in matrices over `A` (`TauCeti.TypeDAStructure`). The structure relation of length `n` is

`∑_{i + j = n} coeff i (b₁, …, bᵢ) * coeff j (bᵢ₊₁, …, bₙ) + d (coeff n b)`
`  + ∑_l coeff n (b₁, …, d bₗ, …, bₙ) + ∑_l coeff (n - 1) (b₁, …, bₗ bₗ₊₁, …, bₙ) = 0`,

with the composite terms `TauCeti.typeDAComp`, the differential terms `TauCeti.typeDADiff` and the
product terms `TauCeti.typeDAMul`. In length zero it says that `coeff 0` is a type `D` structure
over `A`, and in length one that `coeff 1` is compatible with the differentials up to the
homotopy given by `coeff 0`.

* **The induced module.** The row vectors `X → A`, which model `A ⊗ P`, form an `A∞` right module
  over `B` (`TauCeti.TypeDAStructure.toUngradedAInfinityRightModule`), with
  `m₁(φ) = d φ + φ * coeff 0` and `m_{1+n}(φ, b) = φ * coeff n b` for `n ≥ 1`. Its `A∞` relations
  are the structure relations of `P` multiplied on the left by `φ`.
* **The box tensor product.** For a type `D` structure `N` over `B` with generators `Y`, the
  coefficients of `P ⊠ N` on the generators `x ⊗ y` are
  `δ¹(x ⊗ y) = ∑_n (δ¹_{1+n} ⊗ 1)(x ⊗ δⁿ(y))`, where `δⁿ` is the `n`-th iterate of the structure
  map of `N` (`TauCeti.TypeDStructure.iteratedCoeff`): the coefficient of `x' ⊗ y'` is
  `∑_n coeff n (δ(y₀, y₁), …, δ(yₙ₋₁, yₙ)) x x'` over the paths `y = y₀ → ⋯ → yₙ = y'` in `Y`
  (`TauCeti.TypeDAStructure.boxCoeff`). The sum is finite when the operations of `P` vanish from
  some arity on, or when `N` is bounded, and in either case the coefficients satisfy the structure
  equation of a type `D` structure
  (`TauCeti.TypeDAStructure.map_boxCoeff_add_boxCoeff_mul_boxCoeff`). The proof identifies the box
  tensor product `(A ⊠ P) ⊠ N` of the induced module with `N`
  (`TauCeti.TypeDStructure.typeABoxDifferential`) with the differential induced by these
  coefficients, `∂ φ = d φ + φ * boxCoeff`
  (`TauCeti.TypeDAStructure.typeABoxDifferential_toUngradedAInfinityRightModule_apply`), and reads
  the structure equation off `∂ ∘ ∂ = 0`.
* **Idempotents.** The tensor product `P ⊗ N` is taken over the idempotents of `B`: its generators
  are the pairs `x ⊗ y` with `idemRight x = idem y`. When the idempotents of `B` are orthogonal,
  no coefficient leads from such a pair to another pair, so the coefficients restrict to these
  generators, which gives the type `D` structure `P ⊠ N` over `A`
  (`TauCeti.TypeDAStructure.boxTensor`).
* **The identity bimodule.** For a complete family of orthogonal idempotents `ι` of `A` killed by
  the differential, the identity bimodule `^A 𝕀_A` has a generator for each idempotent and
  `δ¹₂(s, a) = ι s * a * ι t ⊗ t` (`TauCeti.TypeDAStructure.identity`), and `𝕀 ⊠ N` is `N`
  (`TauCeti.TypeDAStructure.boxTensor_identity_coeff`).

Over a ring of characteristic two no signs appear. The coefficients are multilinear over `R`;
the conditions `TauCeti.TypeDAStructure.coeff_zero_eq_zero_of_ne`,
`TauCeti.TypeDAStructure.coeff_succ_update_zero` and
`TauCeti.TypeDAStructure.coeff_succ_update_last` record that they are compatible with the
idempotents of `B` at the two ends of `P ⊗ B^{⊗ n}`.

## Main definitions

* `TauCeti.TypeDAStructure`: a type `DA` bimodule, given by its generators, their idempotents and
  its coefficient matrices.
* `TauCeti.TypeDAStructure.toUngradedAInfinityRightModule`: the induced `A∞` right module `A ⊠ P`
  over `B`.
* `TauCeti.TypeDAStructure.boxCoeff`: the coefficients of the box tensor product `P ⊠ N`.
* `TauCeti.TypeDAStructure.boxTensor`: the box tensor product `P ⊠ N`, a type `D` structure over
  `A`.
* `TauCeti.TypeDAStructure.identity`: the identity type `DA` bimodule.

## Main results

* `TauCeti.TypeDAStructure.typeABoxDifferential_toUngradedAInfinityRightModule_apply`: the box
  tensor differential of the induced module with `N` is `∂ φ = d φ + φ * boxCoeff`.
* `TauCeti.TypeDAStructure.map_boxCoeff_add_boxCoeff_mul_boxCoeff`: the coefficients of `P ⊠ N`
  satisfy the structure equation of a type `D` structure.
* `TauCeti.TypeDAStructure.boxTensor_identity_coeff`: the box tensor product with the identity
  bimodule has the coefficients of `N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598),
  Section 2.2 (type `DA` bimodules, their structure relations, the box tensor product
  `P ⊠ N`, equation (2.2.48), and the identity bimodule).
-/

public section

open Finset

namespace TauCeti

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-! ### The structure relations -/

section Relations

variable {X : Type*} [Fintype X]
  (c : (n : ℕ) → MultilinearMap R (fun _ : Fin n => B) (Matrix X X A))

/-- The **composite terms** of the type `DA` structure relation of length `n`:
`∑_{i + j = n} coeff i (b₁, …, bᵢ) * coeff j (bᵢ₊₁, …, bₙ)`, which compose `δ¹` with itself. -/
noncomputable def typeDAComp (n : ℕ) (b : Fin n → B) : Matrix X X A :=
  ∑ k : Fin (n + 1), c k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) *
    c (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩)

theorem typeDAComp_def (n : ℕ) (b : Fin n → B) :
    typeDAComp c n b = ∑ k : Fin (n + 1),
      c k (fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩) *
        c (n - k) (fun l => b ⟨k + l, by have := l.isLt; omega⟩) :=
  (rfl)

/-- The **differential terms** of the type `DA` structure relation of length `n`:
`∑_l coeff n (b₁, …, d bₗ, …, bₙ)`. -/
noncomputable def typeDADiff (dB : B →ₗ[R] B) (n : ℕ) (b : Fin n → B) : Matrix X X A :=
  ∑ l : Fin n, c n (Function.update b l (dB (b l)))

omit [Fintype X] in
theorem typeDADiff_def (dB : B →ₗ[R] B) (n : ℕ) (b : Fin n → B) :
    typeDADiff c dB n b = ∑ l : Fin n, c n (Function.update b l (dB (b l))) :=
  (rfl)

/-- The **product terms** of the type `DA` structure relation of length `n`:
`∑_l coeff (n - 1) (b₁, …, bₗ bₗ₊₁, …, bₙ)`, over the `n - 1` adjacent pairs. -/
noncomputable def typeDAMul : (n : ℕ) → (Fin n → B) → Matrix X X A
  | 0, _ => 0
  | n + 1, b => ∑ l : Fin n, c n (Fin.contractNth l.castSucc (· * ·) b)

omit [Fintype X] in
@[simp]
theorem typeDAMul_zero (b : Fin 0 → B) : typeDAMul c 0 b = 0 :=
  (rfl)

omit [Fintype X] in
theorem typeDAMul_succ (n : ℕ) (b : Fin (n + 1) → B) :
    typeDAMul c (n + 1) b = ∑ l : Fin n, c n (Fin.contractNth l.castSucc (· * ·) b) :=
  (rfl)

end Relations

variable (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) {S T : Type*} (ι : S → A) (κ : T → B)
  (X : Type*) [Fintype X]

/-- A **type `DA` bimodule** `^A P_B` over the differential algebras `(A, dA)` and `(B, dB)`, with
idempotents `ι` of `A` and `κ` of `B`, in a basis of generators `X`. Each generator `x` lies in the
summand of `ι (idemLeft x)` on the left and of `κ (idemRight x)` on the right, and
`δ¹_{1+n}(x, b₁, …, bₙ) = ∑ y, coeff n b x y ⊗ y`. The coefficients lie in
`ι (idemLeft x) * A * ι (idemLeft y)`; the operation `δ¹₁` preserves the idempotent of `B`, and
the operations `δ¹_{1+n}`, `n ≥ 1`, absorb the idempotent of `B` of the source into their first
input and that of the target into their last input. The structure relation of every length `n`
says that the composite terms `TauCeti.typeDAComp`, the differential of the coefficients, the
differential terms `TauCeti.typeDADiff` and the product terms `TauCeti.typeDAMul` sum to zero. -/
@[ext]
structure TypeDAStructure where
  /-- The idempotent of `A` of each generator. -/
  idemLeft : X → S
  /-- The idempotent of `B` of each generator. -/
  idemRight : X → T
  /-- The coefficients: `δ¹_{1+n}(x, b₁, …, bₙ) = ∑ y, coeff n b x y ⊗ y`. -/
  coeff : (n : ℕ) → MultilinearMap R (fun _ : Fin n => B) (Matrix X X A)
  /-- The coefficients from `x` lie in the summand of the idempotent of `x` on the left. -/
  idem_mul_coeff (n : ℕ) (b : Fin n → B) (x y : X) :
    ι (idemLeft x) * coeff n b x y = coeff n b x y
  /-- The coefficients to `y` lie in the summand of the idempotent of `y` on the right. -/
  coeff_mul_idem (n : ℕ) (b : Fin n → B) (x y : X) :
    coeff n b x y * ι (idemLeft y) = coeff n b x y
  /-- The operation `δ¹₁` preserves the idempotent of `B`. -/
  coeff_zero_eq_zero_of_ne (b : Fin 0 → B) {x y : X} (h : idemRight x ≠ idemRight y) :
    coeff 0 b x y = 0
  /-- The first input of `δ¹_{1+n}`, `n ≥ 1`, absorbs the idempotent of `B` of the source. -/
  coeff_succ_update_zero (n : ℕ) (b : Fin (n + 1) → B) (x y : X) :
    coeff (n + 1) (Function.update b 0 (κ (idemRight x) * b 0)) x y = coeff (n + 1) b x y
  /-- The last input of `δ¹_{1+n}`, `n ≥ 1`, absorbs the idempotent of `B` of the target. -/
  coeff_succ_update_last (n : ℕ) (b : Fin (n + 1) → B) (x y : X) :
    coeff (n + 1) (Function.update b (Fin.last n) (b (Fin.last n) * κ (idemRight y))) x y =
      coeff (n + 1) b x y
  /-- The structure relation of length `n`. -/
  structure_eq (n : ℕ) (b : Fin n → B) :
    typeDAComp coeff n b + (coeff n b).map dA + typeDADiff coeff dB n b +
      typeDAMul coeff n b = 0

namespace TypeDAStructure

variable {dA dB ι κ X}

/-- Coefficients of equal arities on tuples with equal entries are equal; this transports a
coefficient along an equality of arities. -/
theorem coeff_congr (P : TypeDAStructure dA dB ι κ X) {m n : ℕ} (h : m = n) (b : Fin m → B)
    (b' : Fin n → B) (hb : ∀ l, b l = b' (Fin.cast h l)) : P.coeff m b = P.coeff n b' := by
  subst h
  exact congrArg (P.coeff m) (funext fun l => hb l)

/-! ### The induced module `A ⊠ P` -/

section Induced

/-- The arity-zero part `m₁(φ) ∋ d φ` of the operations of the induced module. -/
private noncomputable def diffAct (dA : A →ₗ[R] A) :
    (n : ℕ) → MultilinearMap R (fun _ : Fin n => B) ((X → A) →ₗ[R] X → A)
  | 0 => MultilinearMap.constOfIsEmpty R _ (dA.compLeft X)
  | _ + 1 => 0

/-- The operations of the induced module: `m₁(φ) = d φ + φ * coeff 0` and
`m_{1+n}(φ, b) = φ * coeff n b` for `n ≥ 1`. -/
private noncomputable def inducedAct (P : TypeDAStructure dA dB ι κ X) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => B) ((X → A) →ₗ[R] X → A) :=
  diffAct dA n + (LinearMap.mk₂' R R (fun (F : Matrix X X A) (φ : X → A) => Matrix.vecMul φ F)
    (fun F G φ => Matrix.vecMul_add F G φ)
    (fun r F φ => by
      funext y
      simp [Matrix.vecMul, dotProduct, Finset.smul_sum])
    (fun F φ ψ => Matrix.add_vecMul F φ ψ)
    (fun r F φ => by
      funext y
      simp [Matrix.vecMul, dotProduct, Finset.smul_sum])).compMultilinearMap (P.coeff n)

private theorem inducedAct_apply (P : TypeDAStructure dA dB ι κ X) (n : ℕ) (b : Fin n → B)
    (φ : X → A) :
    P.inducedAct n b φ =
      (if n = 0 then dA.compLeft X φ else 0) + Matrix.vecMul φ (P.coeff n b) := by
  cases n <;> rfl

private theorem compLeft_vecMul (hA : IsUngradedDGAlgebra dA) (φ : X → A) (F : Matrix X X A) :
    dA.compLeft X (Matrix.vecMul φ F) =
      Matrix.vecMul (dA.compLeft X φ) F + Matrix.vecMul φ (F.map dA) := by
  funext y
  simp [Matrix.vecMul, dotProduct, map_sum, hA.map_mul, Finset.sum_add_distrib]

/-- The composite terms of the `A∞` relation of the induced module: the two terms carrying the
differential of a row vector cancel in characteristic two, leaving the composite terms of `P` and
the differential of `coeff n`. -/
private theorem ungradedStasheffComp_inducedAct [CharP R 2] (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) (n : ℕ) (b : Fin n → B) (φ : X → A) :
    ungradedStasheffComp P.inducedAct n b φ =
      Matrix.vecMul φ (typeDAComp P.coeff n b + (P.coeff n b).map dA) := by
  rw [ungradedStasheffComp_def, typeDAComp_def, Matrix.vecMul_add, Matrix.vecMul_sum]
  simp only [inducedAct_apply, Matrix.add_vecMul, ← Matrix.vecMul_vecMul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- The differential of `m_{1+n}(φ)` occurs only for `k = n`, after `n` inputs.
  have hlast : ∑ k : Fin (n + 1), (if n - (k : ℕ) = 0 then
      dA.compLeft X ((if (k : ℕ) = 0 then dA.compLeft X φ else 0) +
        Matrix.vecMul φ (P.coeff k fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩))
      else 0) =
        Matrix.vecMul (dA.compLeft X φ) (P.coeff n b) + Matrix.vecMul φ ((P.coeff n b).map dA) := by
    rw [Fintype.sum_eq_single (Fin.last n) fun k hk => ite_eq_right fun h => hk (Fin.ext (by
      have := k.isLt; simp; omega))]
    simp only [Fin.val_last, Nat.sub_self, ite_true, Fin.eta]
    rw [map_add, compLeft_vecMul hA]
    split_ifs
    · have hdd : dA.compLeft X (dA.compLeft X φ) = 0 := funext fun x => hA.map_map (φ x)
      rw [hdd, zero_add]
    · rw [map_zero, zero_add]
  -- The differential of `φ` is fed to `m_{1+n}` only for `k = 0`.
  have hfirst : ∑ k : Fin (n + 1), Matrix.vecMul (if (k : ℕ) = 0 then dA.compLeft X φ else 0)
      (P.coeff (n - k) fun l => b ⟨k + l, by have := l.isLt; omega⟩) =
        Matrix.vecMul (dA.compLeft X φ) (P.coeff n b) := by
    rw [Fintype.sum_eq_single 0 fun k hk => by
      rw [ite_eq_right (show (k : ℕ) ≠ 0 from fun h => hk (Fin.ext h)), Matrix.zero_vecMul]]
    have hc : (P.coeff (n - ((0 : Fin (n + 1)) : ℕ)) fun l =>
        b ⟨((0 : Fin (n + 1)) : ℕ) + l, by have := l.isLt; simp at this ⊢; omega⟩) =
          P.coeff n b :=
      P.coeff_congr (by simp) _ _ fun l => congrArg b (Fin.ext (by simp; rfl))
    rw [hc, Fin.val_zero, ite_eq_left rfl]
  rw [hlast, hfirst]
  have h2 := add_self_eq_zero_of_charTwo R (Matrix.vecMul (dA.compLeft X φ) (P.coeff n b))
  calc _ = (∑ k : Fin (n + 1), Matrix.vecMul (Matrix.vecMul φ
          (P.coeff k fun l => b ⟨l, by have := l.isLt; have := k.isLt; omega⟩))
          (P.coeff (n - k) fun l => b ⟨k + l, by have := l.isLt; omega⟩)) +
        Matrix.vecMul φ ((P.coeff n b).map dA) +
        (Matrix.vecMul (dA.compLeft X φ) (P.coeff n b) +
          Matrix.vecMul (dA.compLeft X φ) (P.coeff n b)) := by abel
    _ = _ := by rw [h2, add_zero]

/-- **The induced module `A ⊠ P`.** Over a ring of characteristic two, the row vectors `X → A`,
which model `A ⊗ P`, form an ungraded `A∞` right module over `(B, dB)` with operations
`m₁(φ) = dA φ + φ * coeff 0` and `m_{1+n}(φ, b) = φ * coeff n b` for `n ≥ 1`
(`TauCeti.TypeDAStructure.toUngradedAInfinityRightModule_act_apply`). Its `A∞` relation of
length `n` is the structure relation of length `n` multiplied on the left by `φ`. -/
noncomputable def toUngradedAInfinityRightModule [CharP R 2] (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) : UngradedAInfinityRightModule dB (X → A) where
  act := P.inducedAct
  stasheff n b φ := by
    have hdiff : ungradedStasheffDiff P.inducedAct dB n b φ =
        Matrix.vecMul φ (typeDADiff P.coeff dB n b) := by
      rw [ungradedStasheffDiff_def, typeDADiff_def, Matrix.vecMul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [inducedAct_apply, ite_eq_right (by have := l.isLt; omega), zero_add]
    have hmul : ungradedStasheffMul P.inducedAct n b φ =
        Matrix.vecMul φ (typeDAMul P.coeff n b) := by
      cases n with
      | zero => simp
      | succ n =>
        rw [ungradedStasheffMul_succ, typeDAMul_succ, Matrix.vecMul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [inducedAct_apply, ite_eq_right (by have := l.isLt; omega), zero_add]
    rw [ungradedStasheffComp_inducedAct hA, hdiff, hmul, ← Matrix.vecMul_add, ← Matrix.vecMul_add,
      P.structure_eq, Matrix.vecMul_zero]

/-- The operations of the induced module: `m_{1+n}(φ, b) = d φ + φ * coeff 0 b` for `n = 0`, and
`φ * coeff n b` otherwise. -/
theorem toUngradedAInfinityRightModule_act_apply [CharP R 2] (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) (n : ℕ) (b : Fin n → B) (φ : X → A) (y : X) :
    (P.toUngradedAInfinityRightModule hA).act n b φ y =
      (if n = 0 then dA (φ y) else 0) + ∑ x, φ x * P.coeff n b x y := by
  exact (congrFun (P.inducedAct_apply n b φ) y).trans (by split_ifs <;> rfl)

end Induced

/-! ### The box tensor product with a type `D` structure -/

section BoxTensor

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The coefficients of length `n` of the box tensor product `P ⊠ N`: the coefficient of
`x' ⊗ y'` in `(δ¹_{1+n} ⊗ 1)(x ⊗ δⁿ(y))`, where `δⁿ` is the `n`-th iterate of the structure map
of `N`. -/
noncomputable def boxCoeffOfLength (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y)
    (n : ℕ) : Matrix (X × Y) (X × Y) A :=
  fun p q => PiTensorProduct.lift ((Matrix.entryLinearMap R A p.1 q.1).compMultilinearMap
    (P.coeff n)) (N.iteratedCoeff n p.2 q.2)

/-- The coefficients of length `n` of `P ⊠ N` as a sum over the paths `y = y₀ → ⋯ → yₙ = y'` in
`Y` of `coeff n (δ(y₀, y₁), …, δ(yₙ₋₁, yₙ)) x x'`. -/
theorem boxCoeffOfLength_apply (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y)
    (n : ℕ) (p q : X × Y) :
    P.boxCoeffOfLength N n p q = ∑ v : Fin (n + 1) → Y with v 0 = p.2 ∧ v (Fin.last n) = q.2,
      P.coeff n (fun l => N.coeff (v l.castSucc) (v l.succ)) p.1 q.1 := by
  simp [boxCoeffOfLength]

/-- The coefficients of length `n` of `P ⊠ N` vanish when the iterate `δⁿ` of `N` does. -/
theorem boxCoeffOfLength_eq_zero_of_iteratedCoeff_eq_zero (P : TypeDAStructure dA dB ι κ X)
    (N : TypeDStructure dB κ Y) {n : ℕ} (hn : ∀ y z, N.iteratedCoeff n y z = 0) :
    P.boxCoeffOfLength N n = 0 := by
  ext p q
  simp [boxCoeffOfLength, hn]

/-- The coefficients of length `n` of `P ⊠ N` vanish when the operation `δ¹_{1+n}` of `P` does. -/
theorem boxCoeffOfLength_eq_zero_of_coeff_eq_zero (P : TypeDAStructure dA dB ι κ X)
    (N : TypeDStructure dB κ Y) {n : ℕ} (hn : P.coeff n = 0) : P.boxCoeffOfLength N n = 0 := by
  ext p q
  simp [boxCoeffOfLength, hn]

/-- The **coefficients of the box tensor product** `P ⊠ N` on the generators `x ⊗ y`, for all
pairs `(x, y)`: `δ¹(x ⊗ y) = ∑_n (δ¹_{1+n} ⊗ 1)(x ⊗ δⁿ(y))`. The sum over `n` is finite when the
operations of `P` vanish from some arity on, or when `N` is bounded
(`TauCeti.TypeDAStructure.boxCoeff_eq_sum`); otherwise this `finsum` is `0` by convention. -/
noncomputable def boxCoeff (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) :
    Matrix (X × Y) (X × Y) A :=
  ∑ᶠ n, P.boxCoeffOfLength N n

/-- When the coefficients of length `n ≥ K` vanish, the coefficients of `P ⊠ N` are the sum of
those of length less than `K`. -/
theorem boxCoeff_eq_sum (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) {K : ℕ}
    (hK : ∀ n, K ≤ n → P.boxCoeffOfLength N n = 0) :
    P.boxCoeff N = ∑ n ∈ range K, P.boxCoeffOfLength N n := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simpa using not_le.mp (mt (hK n) hn)

/-- The boundedness hypotheses under which the box tensor product `P ⊠ N` is defined: the
operations `δ¹_{1+n}` of `P` vanish for all large `n`, or `N` is bounded. -/
def BoxBounded (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) : Prop :=
  (∃ K, ∀ n, K ≤ n → P.coeff n = 0) ∨ N.IsBounded

/-- The box tensor product with a bounded type `D` structure is defined. -/
theorem BoxBounded.of_isBounded (P : TypeDAStructure dA dB ι κ X) {N : TypeDStructure dB κ Y}
    (hN : N.IsBounded) : P.BoxBounded N :=
  Or.inr hN

/-- The box tensor product with a type `DA` bimodule whose operations vanish from some arity on is
defined. -/
theorem BoxBounded.of_coeff_eq_zero {P : TypeDAStructure dA dB ι κ X} (N : TypeDStructure dB κ Y)
    {K : ℕ} (hK : ∀ n, K ≤ n → P.coeff n = 0) : P.BoxBounded N :=
  Or.inl ⟨K, hK⟩

/-- Under either boundedness hypothesis, the coefficients of length `n` of `P ⊠ N` vanish for all
large `n`. -/
theorem BoxBounded.exists_boxCoeffOfLength_eq_zero {P : TypeDAStructure dA dB ι κ X}
    {N : TypeDStructure dB κ Y} (hb : P.BoxBounded N) :
    ∃ K, ∀ n, K ≤ n → P.boxCoeffOfLength N n = 0 := by
  rcases hb with ⟨K, hK⟩ | hN
  · exact ⟨K, fun n hn => P.boxCoeffOfLength_eq_zero_of_coeff_eq_zero N (hK n hn)⟩
  · obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
    exact ⟨K, fun n hn => P.boxCoeffOfLength_eq_zero_of_iteratedCoeff_eq_zero N (hK n hn)⟩

variable [CharP R 2]

/-- The operation `m_{1+n}` of the matrix module of the induced module along the coefficient
matrix of `N`: the differential when `n = 0`, plus the action of the coefficients of length `n`
of `P ⊠ N` on row vectors. -/
theorem matrixAct_toUngradedAInfinityRightModule_apply (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) (n : ℕ) (φ : Y → X → A)
    (z : Y) (x' : X) :
    (P.toUngradedAInfinityRightModule hA).matrixAct Y n (fun _ => N.coeff) φ z x' =
      (if n = 0 then dA (φ z x') else 0) +
        ∑ p : X × Y, φ p.2 p.1 * P.boxCoeffOfLength N n p (x', z) := by
  rw [UngradedAInfinityRightModule.matrixAct_apply, Finset.sum_apply]
  have hterm (c : Fin (n + 1) → Y) :
      (if c (Fin.last n) = z then (P.toUngradedAInfinityRightModule hA).act n
          (fun l => N.coeff (c l.castSucc) (c l.succ)) (φ (c 0)) else (0 : X → A)) x' =
        (if c (Fin.last n) = z then (if n = 0 then dA (φ (c 0) x') else 0) else 0) +
          if c (Fin.last n) = z then
            ∑ x, φ (c 0) x * P.coeff n (fun l => N.coeff (c l.castSucc) (c l.succ)) x x'
          else 0 := by
    split_ifs <;> simp_all [toUngradedAInfinityRightModule_act_apply]
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib]
  congr 1
  · -- The paths of length zero end where they start.
    cases n with
    | zero =>
      rw [← (Equiv.funUnique (Fin 1) Y).symm.sum_comp,
        Fintype.sum_eq_single z fun y hy => by simp [hy]]
      simp
    | succ n => simp
  · -- The other terms are the coefficients of length `n`, summed over the starting points.
    simp_rw [Fintype.sum_prod_type, boxCoeffOfLength_apply, Finset.mul_sum, Finset.sum_filter]
    trans ∑ x, ∑ v : Fin (n + 1) → Y, if v (Fin.last n) = z then
      φ (v 0) x * P.coeff n (fun l => N.coeff (v l.castSucc) (v l.succ)) x x' else 0
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Fintype.sum_eq_single (v 0) fun y hy => by simp [Ne.symm hy]]
      simp

/-- **The box tensor differential of the induced module.** If the coefficients of length `n ≥ K`
of `P ⊠ N` vanish, the box tensor differential of the induced module `A ⊠ P` with `N` is the
differential `∂ φ = d φ + φ * boxCoeff` induced by the coefficients of `P ⊠ N`, on row vectors
indexed by the pairs `(x, y)`. -/
theorem typeABoxDifferential_toUngradedAInfinityRightModule_apply (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) {K : ℕ}
    (hK : ∀ n, K ≤ n → P.boxCoeffOfLength N n = 0) (φ : Y → X → A) (z : Y) (x' : X) :
    N.typeABoxDifferential (P.toUngradedAInfinityRightModule hA) φ z x' =
      dA (φ z x') + ∑ p : X × Y, φ p.2 p.1 * P.boxCoeff N p (x', z) := by
  -- Beyond length `K + 1` the operations along `δ` vanish.
  have hK' : ∀ n, K + 1 ≤ n →
      ((P.toUngradedAInfinityRightModule hA).matrixAct Y n fun _ => N.coeff) = 0 := fun n hn =>
    LinearMap.ext fun ψ => funext fun z => funext fun x' => by
      rw [matrixAct_toUngradedAInfinityRightModule_apply, ite_eq_right (by omega), hK n (by omega)]
      simp
  rw [TypeDStructure.typeABoxDifferential_def,
    UngradedAInfinityRightModule.twistedDifferential_eq_sum _
      (by simpa only [UngradedAInfinityRightModule.matrix_act] using hK'),
    LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply,
    P.boxCoeff_eq_sum N (K := K + 1) fun n hn => hK n (by omega),
    UngradedAInfinityRightModule.matrix_act]
  rw [Finset.sum_congr rfl fun n _ =>
      matrixAct_toUngradedAInfinityRightModule_apply hA P N n φ z x', Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range (K + 1)) 0, ite_eq_left (by simp)]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.sum_apply, Finset.mul_sum]

/-- **The structure equation of the box tensor product.** If the operations of `P` vanish from
some arity on, or `N` is bounded, the coefficients of `P ⊠ N` on all pairs `(x, y)` satisfy
`d boxCoeff + boxCoeff * boxCoeff = 0`, over a ring of characteristic two. -/
theorem map_boxCoeff_add_boxCoeff_mul_boxCoeff (hA : IsUngradedDGAlgebra dA)
    (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) (hb : P.BoxBounded N) :
    (P.boxCoeff N).map dA + P.boxCoeff N * P.boxCoeff N = 0 := by
  classical
  obtain ⟨K, hK⟩ := hb.exists_boxCoeffOfLength_eq_zero
  set Mm := P.toUngradedAInfinityRightModule hA
  -- The box tensor differential of `A ⊠ P` with `N` squares to zero.
  have hsq : ∀ φ, N.typeABoxDifferential Mm (N.typeABoxDifferential Mm φ) = 0 := by
    rcases hb with ⟨L, hL⟩ | hN
    · refine N.typeABoxDifferential_typeABoxDifferential_of_act_eq_zero Mm (K := L + 1)
        fun n hn => ?_
      refine MultilinearMap.ext fun b => LinearMap.ext fun φ => funext fun y => ?_
      rw [toUngradedAInfinityRightModule_act_apply, ite_eq_right (by omega), hL n (by omega)]
      simp
    · exact N.typeABoxDifferential_typeABoxDifferential_of_isBounded Mm hN
  ext ⟨x₀, y₀⟩ ⟨x'', z''⟩
  -- Apply `∂ ∘ ∂` to the generator `x₀ ⊗ y₀`.
  set φ : Y → X → A := fun y x => if (x, y) = (x₀, y₀) then 1 else 0 with hφ
  have hφ' : ∀ z x', N.typeABoxDifferential Mm φ z x' = P.boxCoeff N (x₀, y₀) (x', z) := by
    intro z x'
    rw [typeABoxDifferential_toUngradedAInfinityRightModule_apply hA P N hK,
      Fintype.sum_eq_single (x₀, y₀) fun p hp => by simp only [hφ, ite_eq_right hp, zero_mul]]
    simp only [hφ, ite_true, one_mul]
    split_ifs <;> simp [hA.map_one]
  have h := congrFun (congrFun (hsq φ) z'') x''
  rw [typeABoxDifferential_toUngradedAInfinityRightModule_apply hA P N hK] at h
  simp only [hφ', Pi.zero_apply] at h
  simpa [Matrix.mul_apply] using h

omit [CharP R 2] in
/-- **No coefficient leaves the generators of `P ⊗ N`.** When the idempotents of `B` are
orthogonal, the coefficient of `P ⊠ N` from a pair `(x, y)` with `idemRight x = idem y` to a pair
`(x', y')` with `idemRight x' ≠ idem y'` vanishes. -/
theorem boxCoeff_eq_zero_of_ne (hκ : Pairwise (κ · * κ · = 0))
    (P : TypeDAStructure dA dB ι κ X) (N : TypeDStructure dB κ Y) (hb : P.BoxBounded N)
    {p q : X × Y}
    (hp : P.idemRight p.1 = N.idem p.2) (hq : P.idemRight q.1 ≠ N.idem q.2) :
    P.boxCoeff N p q = 0 := by
  have hn : ∀ n, P.boxCoeffOfLength N n p q = 0 := by
    intro n
    rw [boxCoeffOfLength_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    cases n with
    | zero =>
      -- A path of length zero is constant, and `δ¹₁` preserves the idempotent of `B`.
      refine P.coeff_zero_eq_zero_of_ne _ fun h => hq ?_
      rw [← h, hp, ← hv.1, ← hv.2]
      rfl
    | succ n =>
      -- The last input is killed by the idempotent of `B` of the target.
      rw [← P.coeff_succ_update_last, MultilinearMap.map_coord_zero _ (Fin.last n),
        Matrix.zero_apply]
      rw [Function.update_self, Fin.succ_last, hv.2, ← N.coeff_mul_idem, mul_assoc,
        hκ (Ne.symm hq), mul_zero]
  obtain ⟨K, hK⟩ := hb.exists_boxCoeffOfLength_eq_zero
  rw [P.boxCoeff_eq_sum N hK, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun n _ => hn n

/-- **The box tensor product** `P ⊠ N` of a type `DA` bimodule `^A P_B` with a type `D` structure
`N` over `B`, a type `D` structure over `A`, over a ring of characteristic two. Its generators are
the pairs `x ⊗ y` with `idemRight x = idem y`, the generators of the tensor product over the
idempotents of `B`, the idempotent of `x ⊗ y` is `idemLeft x`, and its coefficients are those of
`TauCeti.TypeDAStructure.boxCoeff`. It is defined when the operations of `P` vanish from some
arity on or `N` is bounded, and the idempotents of `B` are orthogonal. -/
noncomputable def boxTensor [DecidableEq T] (hA : IsUngradedDGAlgebra dA)
    (hκ : Pairwise (κ · * κ · = 0)) (P : TypeDAStructure dA dB ι κ X)
    (N : TypeDStructure dB κ Y) (hb : P.BoxBounded N) :
    TypeDStructure dA ι {p : X × Y // P.idemRight p.1 = N.idem p.2} where
  idem p := P.idemLeft p.1.1
  coeff := (P.boxCoeff N).submatrix (↑) (↑)
  idem_mul_coeff p q := by
    obtain ⟨K, hK⟩ := hb.exists_boxCoeffOfLength_eq_zero
    rw [Matrix.submatrix_apply, P.boxCoeff_eq_sum N hK, Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [boxCoeffOfLength_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => P.idem_mul_coeff _ _ _ _
  coeff_mul_idem p q := by
    obtain ⟨K, hK⟩ := hb.exists_boxCoeffOfLength_eq_zero
    rw [Matrix.submatrix_apply, P.boxCoeff_eq_sum N hK, Matrix.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [boxCoeffOfLength_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => P.coeff_mul_idem _ _ _ _
  map_coeff_add_coeff_mul_coeff := by
    ext p q
    have h := congrFun (congrFun (P.map_boxCoeff_add_boxCoeff_mul_boxCoeff hA N hb) p.1) q.1
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, ← h]
    simp_rw [Matrix.submatrix_apply]
    congr 1
    -- The pairs outside `P ⊗ N` contribute nothing to the product.
    rw [← Fintype.sum_subtype_add_sum_subtype (fun r : X × Y => P.idemRight r.1 = N.idem r.2)
      (fun r => P.boxCoeff N p r * P.boxCoeff N r q), left_eq_add]
    exact Fintype.sum_eq_zero _ fun r => by rw [P.boxCoeff_eq_zero_of_ne hκ N hb p.2 r.2, zero_mul]

@[simp]
theorem boxTensor_idem [DecidableEq T] (hA : IsUngradedDGAlgebra dA)
    (hκ : Pairwise (κ · * κ · = 0)) (P : TypeDAStructure dA dB ι κ X)
    (N : TypeDStructure dB κ Y) (hb : P.BoxBounded N)
    (p : {p : X × Y // P.idemRight p.1 = N.idem p.2}) :
    (P.boxTensor hA hκ N hb).idem p = P.idemLeft p.1.1 :=
  (rfl)

@[simp]
theorem boxTensor_coeff [DecidableEq T] (hA : IsUngradedDGAlgebra dA)
    (hκ : Pairwise (κ · * κ · = 0)) (P : TypeDAStructure dA dB ι κ X)
    (N : TypeDStructure dB κ Y) (hb : P.BoxBounded N)
    (p q : {p : X × Y // P.idemRight p.1 = N.idem p.2}) :
    (P.boxTensor hA hκ N hb).coeff p q = P.boxCoeff N p q :=
  Matrix.submatrix_apply _ _ _ _ _

end BoxTensor

/-! ### The identity bimodule -/

section Identity

/-- The coefficient `a ↦ (ι s * a * ι t)_{s, t}` of the identity bimodule. -/
private noncomputable def identityCoeffOne (ι : S → A) : A →ₗ[R] Matrix S S A where
  toFun a := Matrix.of fun s t => ι s * a * ι t
  map_add' a b := by
    ext s t
    simp [mul_add, add_mul]
  map_smul' r a := by
    ext s t
    simp

/-- The coefficients of the identity bimodule: only `δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t` is
nonzero. -/
private noncomputable def identityCoeff (ι : S → A) :
    (n : ℕ) → MultilinearMap R (fun _ : Fin n => A) (Matrix S S A)
  | 0 => 0
  | 1 => MultilinearMap.ofSubsingleton R A (Matrix S S A) 0 (identityCoeffOne ι)
  | _ + 2 => 0

private theorem identityCoeff_one_apply (b : Fin 1 → A) (s t : S) :
    identityCoeff (R := R) ι 1 b s t = ι s * b 0 * ι t :=
  (rfl)

private theorem identityCoeff_apply_of_eq_one {n : ℕ} (hn : n = 1) (b : Fin n → A) (s t : S) :
    identityCoeff (R := R) ι n b s t = ι s * b ⟨0, by omega⟩ * ι t := by
  subst hn
  rfl

private theorem identityCoeff_eq_zero {n : ℕ} (hn : n ≠ 1) :
    identityCoeff (R := R) ι n = 0 := by
  match n, hn with
  | 0, _ => rfl
  | _ + 2, _ => rfl

private theorem identityCoeff_apply_eq_zero {n : ℕ} (hn : n ≠ 1) (b : Fin n → A) :
    identityCoeff (R := R) ι n b = 0 := by
  rw [identityCoeff_eq_zero hn, zero_apply]

variable [Fintype S]

/-- Except in length two, the composite terms of the identity bimodule vanish: no composite term
has its single nonzero operation `δ¹₂` in both places. -/
private theorem typeDAComp_identityCoeff_eq_zero {n : ℕ} (hn : n ≠ 2) (b : Fin n → A) :
    typeDAComp (identityCoeff (R := R) ι) n b = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne (k : ℕ) 1 with hk | hk
  · rw [identityCoeff_apply_eq_zero (n := n - k) (by omega), mul_zero]
  · rw [identityCoeff_apply_eq_zero hk, zero_mul]

/-- In length two, the composite term `δ¹₂ ∘ δ¹₂` of the identity bimodule is its product term:
`(ι s * b₀ * ι u) * (ι u * b₁ * ι t)` summed over `u` is `ι s * b₀ b₁ * ι t`. -/
private theorem typeDAComp_identityCoeff_two (hι : CompleteOrthogonalIdempotents ι)
    (b : Fin 2 → A) :
    typeDAComp (identityCoeff (R := R) ι) 2 b =
      identityCoeff (R := R) ι 1 (Fin.contractNth 0 (· * ·) b) := by
  ext s t
  rw [typeDAComp, Fin.sum_univ_three, Matrix.add_apply, Matrix.add_apply,
    identityCoeff_apply_eq_zero (show ((0 : Fin 3) : ℕ) ≠ 1 by decide),
    identityCoeff_apply_eq_zero (show ((2 : Fin 3) : ℕ) ≠ 1 by decide), Matrix.zero_mul,
    Matrix.zero_mul, Matrix.zero_apply, zero_add, add_zero, Matrix.mul_apply,
    identityCoeff_apply_of_eq_one rfl, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
  simp only [identityCoeff_apply_of_eq_one (show 2 - ((1 : Fin 3) : ℕ) = 1 by decide),
    identityCoeff_apply_of_eq_one (show ((1 : Fin 3) : ℕ) = 1 by decide)]
  calc _ = ι s * b 0 * (∑ u, ι u * ι u) * b 1 * ι t := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rfl
    _ = _ := by
        simp only [fun u => (hι.idem u).eq, hι.complete, mul_one, mul_assoc, Fin.zero_eta,
          Fin.castSucc_zero, Fin.succ_zero_eq_one]

omit [Fintype S] in
/-- The differential of `δ¹₂(s, a)` is `δ¹₂(s, d a)`, since the differential kills the
idempotents. -/
private theorem map_identityCoeff_one (hA : IsUngradedDGAlgebra dA) (hdι : ∀ s, dA (ι s) = 0)
    (b : Fin 1 → A) :
    (identityCoeff (R := R) ι 1 b).map dA =
      identityCoeff (R := R) ι 1 (Function.update b 0 (dA (b 0))) := by
  ext s t
  simp [identityCoeff_one_apply, hA.map_mul, hdι]

/-- **The identity bimodule** `^A 𝕀_A` of a complete family of orthogonal idempotents `ι` of `A`
killed by the differential, over a ring of characteristic two. It has a generator for each
idempotent, with that idempotent on both sides, and its only nonzero operation is
`δ¹₂(s, a) = ∑ t, ι s * a * ι t ⊗ t` (`TauCeti.TypeDAStructure.identity_coeff_one_apply`). Its
box tensor product with a type `D` structure `N` is `N`
(`TauCeti.TypeDAStructure.boxTensor_identity_coeff`). -/
noncomputable def identity [CharP R 2] (hA : IsUngradedDGAlgebra dA)
    (hι : CompleteOrthogonalIdempotents ι) (hdι : ∀ s, dA (ι s) = 0) :
    TypeDAStructure dA dA ι ι S where
  idemLeft := id
  idemRight := id
  coeff := identityCoeff ι
  idem_mul_coeff n b s t := by
    rcases eq_or_ne n 1 with rfl | hn
    · rw [identityCoeff_one_apply, id_eq, ← mul_assoc, ← mul_assoc, (hι.idem s).eq]
    · rw [identityCoeff_apply_eq_zero hn, Matrix.zero_apply, mul_zero]
  coeff_mul_idem n b s t := by
    rcases eq_or_ne n 1 with rfl | hn
    · rw [identityCoeff_one_apply, id_eq, mul_assoc, (hι.idem t).eq]
    · rw [identityCoeff_apply_eq_zero hn, Matrix.zero_apply, zero_mul]
  coeff_zero_eq_zero_of_ne b s t _ := by
    rw [identityCoeff_apply_eq_zero zero_ne_one, Matrix.zero_apply]
  coeff_succ_update_zero n b s t := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [identityCoeff_apply_of_eq_one rfl, identityCoeff_apply_of_eq_one rfl]
      simp only [Fin.zero_eta, Function.update_self, id_eq, ← mul_assoc, (hι.idem s).eq]
    · rw [identityCoeff_apply_eq_zero (by omega), identityCoeff_apply_eq_zero (by omega)]
  coeff_succ_update_last n b s t := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [identityCoeff_apply_of_eq_one rfl, identityCoeff_apply_of_eq_one rfl]
      simp only [Fin.zero_eta, Fin.last_zero, Function.update_self, id_eq, mul_assoc,
        (hι.idem t).eq]
    · rw [identityCoeff_apply_eq_zero (by omega), identityCoeff_apply_eq_zero (by omega)]
  structure_eq n b := by
    have h2 (a : Matrix S S A) : a + a = 0 := add_self_eq_zero_of_charTwo R a
    match n with
    | 0 =>
      simp [typeDAComp_identityCoeff_eq_zero (by decide : 0 ≠ 2), typeDADiff,
        identityCoeff_apply_eq_zero zero_ne_one]
    | 1 =>
      simp only [typeDAComp_identityCoeff_eq_zero (by decide : 1 ≠ 2),
        map_identityCoeff_one hA hdι, typeDADiff, Fin.sum_univ_one, typeDAMul_succ,
        Finset.univ_eq_empty, Finset.sum_empty, zero_add, h2]
    | 2 =>
      simp only [typeDAComp_identityCoeff_two hι, typeDADiff, typeDAMul_succ, Fin.sum_univ_one,
        Fin.castSucc_zero, identityCoeff_apply_eq_zero (by decide : (2 : ℕ) ≠ 1),
        Matrix.map_zero, map_zero, Finset.sum_const_zero, add_zero, h2]
    | m + 3 =>
      simp [typeDAComp_identityCoeff_eq_zero (by omega : m + 3 ≠ 2), typeDADiff, typeDAMul_succ,
        identityCoeff_apply_eq_zero (by omega : m + 3 ≠ 1),
        identityCoeff_apply_eq_zero (by omega : m + 2 ≠ 1)]

variable [CharP R 2] (hA : IsUngradedDGAlgebra dA) (hι : CompleteOrthogonalIdempotents ι)
  (hdι : ∀ s, dA (ι s) = 0)

/-- The operation `δ¹₂` of the identity bimodule: `δ¹₂(s, a)` has coefficient `ι s * a * ι t` on
`t`. -/
@[simp]
theorem identity_coeff_one_apply (b : Fin 1 → A) (s t : S) :
    (identity hA hι hdι).coeff 1 b s t = ι s * b 0 * ι t :=
  (rfl)

/-- The operations `δ¹_{1+n}`, `n ≠ 1`, of the identity bimodule vanish. -/
theorem identity_coeff_eq_zero {n : ℕ} (hn : n ≠ 1) : (identity hA hι hdι).coeff n = 0 :=
  identityCoeff_eq_zero hn

@[simp]
theorem identity_idemLeft : (identity hA hι hdι).idemLeft = id :=
  (rfl)

@[simp]
theorem identity_idemRight : (identity hA hι hdι).idemRight = id :=
  (rfl)

variable {Y : Type*} [Fintype Y] [DecidableEq Y] (N : TypeDStructure dA ι Y)

/-- The box tensor product with the identity bimodule is defined for every type `D` structure,
since the operations of the identity bimodule vanish beyond `δ¹₂`. -/
theorem boxBounded_identity : (identity hA hι hdι).BoxBounded N :=
  .of_coeff_eq_zero N (K := 2) fun _ hn => identity_coeff_eq_zero hA hι hdι (by omega)

/-- **The box tensor product with the identity bimodule.** On the generators `s ⊗ y` of `𝕀 ⊗ N`,
those with `s = idem y`, the coefficients of `𝕀 ⊠ N` are those of `N`. -/
theorem boxCoeff_identity {p q : S × Y} (hp : p.1 = N.idem p.2) (hq : q.1 = N.idem q.2) :
    (identity hA hι hdι).boxCoeff N p q = N.coeff p.2 q.2 := by
  rw [boxCoeff_eq_sum _ N (K := 2) fun n hn => boxCoeffOfLength_eq_zero_of_coeff_eq_zero _ N
    (identity_coeff_eq_zero hA hι hdι (by omega)), Finset.sum_range_succ, Finset.sum_range_one,
    boxCoeffOfLength_eq_zero_of_coeff_eq_zero _ N (identity_coeff_eq_zero hA hι hdι zero_ne_one),
    zero_add, boxCoeffOfLength, N.iteratedCoeff_one, PiTensorProduct.lift.tprod,
    LinearMap.compMultilinearMap_apply, Matrix.entryLinearMap_apply, identity_coeff_one_apply, hp,
    hq, N.idem_mul_coeff, N.coeff_mul_idem]

variable [DecidableEq S]

/-- **The box tensor product with the identity bimodule is `N`.** The generators `s ⊗ y` of
`𝕀 ⊠ N` are in bijection with those of `N` by `s ⊗ y ↦ y`, and under this bijection the
idempotents and the coefficients of `𝕀 ⊠ N` are those of `N`. -/
theorem boxTensor_identity_coeff
    (p q : {p : S × Y // (identity hA hι hdι).idemRight p.1 = N.idem p.2}) :
    ((identity hA hι hdι).boxTensor hA hι.ortho N (boxBounded_identity hA hι hdι N)).coeff p q =
      N.coeff p.1.2 q.1.2 :=
  boxCoeff_identity hA hι hdι N p.2 q.2

theorem boxTensor_identity_idem
    (p : {p : S × Y // (identity hA hι hdι).idemRight p.1 = N.idem p.2}) :
    ((identity hA hι hdι).boxTensor hA hι.ortho N (boxBounded_identity hA hι hdι N)).idem p =
      N.idem p.1.2 :=
  p.2

end Identity

end TypeDAStructure

end TauCeti
