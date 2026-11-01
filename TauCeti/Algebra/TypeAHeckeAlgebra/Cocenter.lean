/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.Algebra.TypeAHeckeAlgebra.CycleWord

/-!
# Cycle-block words span the cocenter of a Hecke stage

Let `Hₙ` be the stage of the first `n` strands of the infinite type-A Hecke algebra
(`TauCeti.InfiniteTypeAHeckeAlgebra.stage`), which is the Hecke algebra on `n` strands
(`TauCeti.TypeAHeckeAlgebra.stageEquiv`). Its *cocenter* is the cyclic quotient
`TauCeti.cyclicQuotient R Hₙ = Hₙ / [Hₙ, Hₙ]` of `Hₙ` by the `R`-linear span
`TauCeti.commutatorSubmodule R Hₙ` of the commutators `x * y - y * x`; this span is not an ideal.
Its image in the infinite algebra is `TauCeti.InfiniteTypeAHeckeAlgebra.stageCommutatorSpan`,
which is where the arguments of this file take place. A linear
map on `Hₙ` is a trace exactly when it kills this span, so trace functionals on `Hₙ` are the
linear functionals on the cocenter.

Write `gᵢ = q • T i` and let `ζₘ = g_(m-2) * ⋯ * g_0` be the cycle word on `m` strands
(`TauCeti.InfiniteTypeAHeckeAlgebra.cycleWord`). For a list `[m₁, …, mₖ]` of block sizes, the
cycle-block word (`TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord`) places `ζ_(m₁), …, ζ_(mₖ)`
on consecutive disjoint blocks of strands:
`ζ_(m₁) * shift m₁ ζ_(m₂) * shift (m₁ + m₂) ζ_(m₃) * ⋯`. For a partition `λ` of `n`, the element
`ζ_λ` (`TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlock`) is the cycle-block word of the parts
`λ₁ ≥ λ₂ ≥ ⋯` of `λ`. It is the element `q ^ (n - k) • T_w` attached to the permutation `w` with
these consecutive cycles, where `k` is the number of parts, although that identification is not
needed here.

The main result, `TauCeti.InfiniteTypeAHeckeAlgebra.span_cycleBlock_sup_stageCommutatorSpan`,
says that the classes of the elements `ζ_λ`, for `λ` a partition of `n`, span the cocenter of
`Hₙ`, over every commutative ring and for every unit `q`. Consequently two trace functionals on
`Hₙ` agree as soon as they agree on every `ζ_λ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.trace_eq_of_cycleBlock_values`). This is the spanning half of
the theorem that these classes form a basis of the cocenter; their linear independence is not
proved here.

The proof has two steps. First, along the decomposition `Hₙ₊₁ = Hₙ + Hₙ Tₙ₋₁ Hₙ`, every element of
`Hₙ` is congruent modulo commutators to a combination of cycle-block words of compositions of `n`,
with blocks in arbitrary order. Second, reordering the blocks does not change the class of a
cycle-block word: for `x ∈ Hₐ` and `y ∈ H_b`, the element `x * shift a y` is conjugate in
`Hₐ₊_b` to `y * shift b x`
(`TauCeti.InfiniteTypeAHeckeAlgebra.mul_shift_sub_mul_shift_mem_stageCommutatorSpan`).
The conjugating element is the positive lift of the permutation exchanging the two blocks, the
product of the descending words `T (b + k - 1) * ⋯ * T k` for `k < a`, which moves the first `a`
strands past the next `b` strands.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.stageCommutatorSpan`: the span of the commutators of `Hₙ`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord`: the cycle-block word of a list of block
  sizes.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlock`: the element `ζ_λ` of a partition `λ`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.mul_shift_sub_mul_shift_mem_stageCommutatorSpan`: elements
  on two consecutive blocks of strands may be exchanged modulo commutators.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockWord_sub_mem_stageCommutatorSpan`: permuting the
  blocks of a cycle-block word does not change its class in the cocenter.
* `TauCeti.InfiniteTypeAHeckeAlgebra.span_cycleBlock_sup_stageCommutatorSpan` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.span_cycleBlock_sup_commutatorSubmodule`: the elements `ζ_λ`
  span the cocenter of `Hₙ`, in the infinite algebra and in the stage itself.
* `TauCeti.InfiniteTypeAHeckeAlgebra.trace_eq_of_cycleBlock_values`: trace functionals on `Hₙ`
  agreeing on every `ζ_λ` agree on `Hₙ`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cycleBlock`: a Markov trace with
  parameter `z` takes the value `∏ᵢ (q * z) ^ (λᵢ - 1)` on `ζ_λ`.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Sections 8.2 and 8.4, where the classes of the elements `T_w` of minimal length in
  the conjugacy classes of `W` are shown to span (and to form a basis of) the cocenter.
* A. Ram, *A Frobenius formula for the characters of the Hecke algebras*, Invent. Math. 106
  (1991), 461–488, for the cycle-block words `ζ_λ`.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

section Commutators

variable (R q) in
/-- The `R`-linear span of the commutators `x * y - y * x` of elements `x`, `y` of the stage of
the first `n` strands, as a submodule of the infinite algebra: the image of the commutator
submodule of the stage. The quotient of the stage by it is the cocenter of the stage. -/
def stageCommutatorSpan (n : ℕ) : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
  (commutatorSubmodule R (stage R q n)).map (stage R q n).val.toLinearMap

/-- A commutator of two elements of the stage `n` lies in the commutator span of that stage. -/
theorem mul_sub_mul_mem_stageCommutatorSpan {n : ℕ} {x y : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q n) (hy : y ∈ stage R q n) :
    x * y - y * x ∈ stageCommutatorSpan R q n :=
  ⟨_, mul_sub_mul_mem_commutatorSubmodule R _ ⟨x, hx⟩ ⟨y, hy⟩, rfl⟩

/-- The commutator span of the stage `n` is contained in a submodule exactly when every
commutator of two elements of the stage is. -/
theorem stageCommutatorSpan_le_iff {n : ℕ} {p : Submodule R (InfiniteTypeAHeckeAlgebra R q)} :
    stageCommutatorSpan R q n ≤ p ↔ ∀ x ∈ stage R q n, ∀ y ∈ stage R q n, x * y - y * x ∈ p := by
  rw [stageCommutatorSpan, Submodule.map_le_iff_le_comap, ← Submodule.ker_mkQ p,
    ← LinearMap.ker_comp, commutatorSubmodule_le_ker_iff]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val, Subtype.forall, Submodule.ker_mkQ,
    MulMemClass.coe_mul]

/-- The commutator span of a stage is contained in the stage. -/
theorem stageCommutatorSpan_le_toSubmodule_stage (n : ℕ) :
    stageCommutatorSpan R q n ≤ Subalgebra.toSubmodule (stage R q n) :=
  stageCommutatorSpan_le_iff.2 fun _ hx _ hy ↦ by
    rw [Subalgebra.mem_toSubmodule]
    exact sub_mem (mul_mem hx hy) (mul_mem hy hx)

/-- The commutator spans increase with the number of strands. -/
theorem stageCommutatorSpan_mono : Monotone (stageCommutatorSpan R q) :=
  fun _ _ hmn ↦ stageCommutatorSpan_le_iff.2 fun _ hx _ hy ↦
    mul_sub_mul_mem_stageCommutatorSpan (stage_mono hmn hx) (stage_mono hmn hy)

/-- A linear map kills the commutator span of the stage `n` exactly when it is a trace on that
stage. -/
theorem stageCommutatorSpan_le_ker_iff {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] M} :
    stageCommutatorSpan R q n ≤ LinearMap.ker τ ↔
      ∀ x ∈ stage R q n, ∀ y ∈ stage R q n, τ (x * y) = τ (y * x) := by
  simp only [stageCommutatorSpan_le_iff, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Multiplying the shift by `a` of a commutator of the stage `k` on the left by an element of the
stage `a` gives a commutator of the stage `a + k`. -/
theorem mul_shift_mem_stageCommutatorSpan_left {a k : ℕ} {x c : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q a) (hc : c ∈ stageCommutatorSpan R q k) :
    x * shift R q a c ∈ stageCommutatorSpan R q (a + k) := by
  have h : stageCommutatorSpan R q k ≤ (stageCommutatorSpan R q (a + k)).comap
      (LinearMap.mulLeft R x ∘ₗ (shift R q a).toLinearMap) :=
    stageCommutatorSpan_le_iff.2 fun u hu v hv ↦ by
      have hU : shift R q a u ∈ stage R q (a + k) := by
        rw [Nat.add_comm]
        exact shift_mem_stage a hu
      have hV : shift R q a v ∈ stage R q (a + k) := by
        rw [Nat.add_comm]
        exact shift_mem_stage a hv
      -- `x * [U, V] = [U, x * V]`, since `x` commutes with `U`.
      have hxU := (commute_shift_of_mem_stage hx u).eq
      have key : x * shift R q a (u * v - v * u) =
          shift R q a u * (x * shift R q a v) - x * shift R q a v * shift R q a u := by
        rw [map_sub, map_mul, map_mul, mul_sub, ← mul_assoc, hxU, mul_assoc, mul_assoc]
      rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, key]
      exact mul_sub_mul_mem_stageCommutatorSpan hU
        (mul_mem (stage_mono (Nat.le_add_right a k) hx) hV)
  exact h hc

/-- Multiplying a commutator of the stage `k` on the right by the shift by `k` of an element of
the stage `m` gives a commutator of the stage `k + m`. -/
theorem mul_shift_mem_stageCommutatorSpan_right {k m : ℕ} {c y : InfiniteTypeAHeckeAlgebra R q}
    (hc : c ∈ stageCommutatorSpan R q k) (hy : y ∈ stage R q m) :
    c * shift R q k y ∈ stageCommutatorSpan R q (k + m) := by
  have hY : shift R q k y ∈ stage R q (k + m) := by
    rw [Nat.add_comm]
    exact shift_mem_stage k hy
  have h : stageCommutatorSpan R q k ≤ (stageCommutatorSpan R q (k + m)).comap
      (LinearMap.mulRight R (shift R q k y)) := stageCommutatorSpan_le_iff.2 fun u hu v hv ↦ by
    -- `[u, v] * Y = [u, v * Y]`, since `Y` commutes with `u`.
    have huY := (commute_shift_of_mem_stage hu y).eq
    rw [Submodule.mem_comap, LinearMap.mulRight_apply, sub_mul, mul_assoc u,
      mul_assoc v, huY, ← mul_assoc v]
    exact mul_sub_mul_mem_stageCommutatorSpan (stage_mono (Nat.le_add_right k m) hu)
      (mul_mem (stage_mono (Nat.le_add_right k m) hv) hY)
  exact h hc

end Commutators

section BlockSwap

/-- The positive lift of the permutation moving the first `a` strands past the next `b` strands:
`blockSwap q 0 b = 1` and
`blockSwap q (a + 1) b = (T (b - 1) * ⋯ * T 0) * shift 1 (blockSwap q a b)`. -/
private def blockSwap (q : Rˣ) : ℕ → ℕ → InfiniteTypeAHeckeAlgebra R q
  | 0, _ => 1
  | a + 1, b => cosetRep q b 0 * shift R q 1 (blockSwap q a b)

private theorem blockSwap_zero (b : ℕ) : blockSwap q 0 b = 1 := by
  rw [blockSwap]

private theorem blockSwap_succ (a b : ℕ) :
    blockSwap q (a + 1) b = cosetRep q b 0 * shift R q 1 (blockSwap q a b) := by
  rw [blockSwap]

private theorem blockSwap_mem_stage (a b : ℕ) : blockSwap q a b ∈ stage R q (a + b) := by
  induction a with
  | zero => simpa only [blockSwap_zero] using one_mem _
  | succ a ih =>
    rw [blockSwap_succ]
    refine mul_mem (stage_mono (by omega) (cosetRep_mem_stage b 0)) ?_
    simpa only [Nat.add_right_comm a 1 b] using shift_mem_stage 1 ih

/-- The generator `T i` is a unit of every stage containing it: its inverse
`T i - (q - q⁻¹)` lies in the same stage. -/
private theorem isUnit_mk_T {i n : ℕ} (h : i + 1 < n) :
    IsUnit (⟨T q i, T_mem_stage h⟩ : stage R q n) := by
  have hinv : (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) ∈ stage R q n := by
    rw [val_inv_unitT]
    exact sub_mem (T_mem_stage h) (algebraMap_mem _ _)
  refine isUnit_iff_exists.2 ⟨⟨_, hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa only [MulMemClass.mk_mul_mk, OneMemClass.coe_one, val_unitT] using (unitT q i).mul_inv
  · simpa only [MulMemClass.mk_mul_mk, OneMemClass.coe_one, val_unitT] using (unitT q i).inv_mul

/-- A unit of a stage stays a unit of every later stage. -/
private theorem isUnit_mk_of_le {m n : ℕ} (hmn : m ≤ n) {x : InfiniteTypeAHeckeAlgebra R q}
    {hx : x ∈ stage R q m} (h : IsUnit (⟨x, hx⟩ : stage R q m)) :
    IsUnit (⟨x, stage_mono hmn hx⟩ : stage R q n) :=
  h.map (Subalgebra.inclusion (stage_mono hmn))

/-- The strand shift by `k` carries units of the stage `n` to units of the stage `n + k`. -/
private theorem isUnit_mk_shift {n : ℕ} (k : ℕ) {x : InfiniteTypeAHeckeAlgebra R q}
    {hx : x ∈ stage R q n} (h : IsUnit (⟨x, hx⟩ : stage R q n)) :
    IsUnit (⟨shift R q k x, shift_mem_stage k hx⟩ : stage R q (n + k)) :=
  h.map (((shift R q k).comp (stage R q n).val).codRestrict (stage R q (n + k))
    fun y ↦ shift_mem_stage k y.2)

/-- Units of a stage are closed under multiplication. -/
private theorem isUnit_mk_mul {n : ℕ} {x y : InfiniteTypeAHeckeAlgebra R q} {hx : x ∈ stage R q n}
    {hy : y ∈ stage R q n} (h : IsUnit (⟨x, hx⟩ : stage R q n))
    (h' : IsUnit (⟨y, hy⟩ : stage R q n)) : IsUnit (⟨x * y, mul_mem hx hy⟩ : stage R q n) :=
  h.mul h'

/-- Being a unit of a stage only depends on the element. -/
private theorem isUnit_mk_of_eq {n : ℕ} {x y : InfiniteTypeAHeckeAlgebra R q} (hxy : x = y)
    {hx : x ∈ stage R q n} (h : IsUnit (⟨x, hx⟩ : stage R q n)) :
    IsUnit (⟨y, hxy ▸ hx⟩ : stage R q n) := by
  subst hxy
  exact h

private theorem isUnit_cosetRep (n m : ℕ) :
    IsUnit (⟨cosetRep q n m, cosetRep_mem_stage n m⟩ : stage R q (n + 1)) := by
  induction n with
  | zero =>
    simp only [cosetRep_of_le (Nat.zero_le m)]
    exact isUnit_one
  | succ n ih =>
    rcases le_or_gt m n with h | h
    · exact isUnit_mk_of_eq (cosetRep_succ h).symm
        (isUnit_mk_mul (isUnit_mk_T (i := n) (by omega)) (isUnit_mk_of_le (by omega) ih))
    · simp only [cosetRep_of_le h]
      exact isUnit_one

private theorem isUnit_blockSwap (a b : ℕ) :
    IsUnit (⟨blockSwap q a b, blockSwap_mem_stage a b⟩ : stage R q (a + b)) := by
  induction a with
  | zero =>
    simp only [blockSwap_zero]
    exact isUnit_one
  | succ a ih =>
    exact isUnit_mk_of_eq (blockSwap_succ a b).symm
      (isUnit_mk_mul (isUnit_mk_of_le (by omega) (isUnit_cosetRep (q := q) b 0))
        (isUnit_mk_of_le (by omega) (isUnit_mk_shift 1 ih)))

/-- The two-block identity: moving two strands past `b` strands carries the crossing `T 0` of the
two strands to the crossing `T b`. -/
private theorem cosetRep_mul_cosetRep_mul_T_zero (b : ℕ) :
    cosetRep q b 0 * cosetRep q (b + 1) 1 * T q 0 =
      T q b * (cosetRep q b 0 * cosetRep q (b + 1) 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hc : cosetRep q b 0 * T q (b + 1) = T q (b + 1) * cosetRep q b 0 :=
      (commute_T_of_mem_stage le_rfl (cosetRep_mem_stage b 0)).eq.symm
    have hD : cosetRep q (b + 1) 0 * cosetRep q (b + 1 + 1) 1 =
        T q b * T q (b + 1) * (cosetRep q b 0 * cosetRep q (b + 1) 1) := by
      rw [cosetRep_succ (Nat.zero_le b), cosetRep_succ (by omega : 1 ≤ b + 1), mul_assoc,
        ← mul_assoc (cosetRep q b 0), hc]
      simp only [mul_assoc]
    rw [hD, mul_assoc, ih, ← mul_assoc, ← mul_assoc, T_braid]
    simp only [mul_assoc]

/-- The block swap carries a generator crossing two of the last `b` strands to the corresponding
generator crossing two of the first `b` strands. -/
private theorem blockSwap_mul_T_add {a b j : ℕ} (hj : j + 1 < b) :
    blockSwap q a b * T q (a + j) = T q j * blockSwap q a b := by
  induction a generalizing j with
  | zero => rw [blockSwap_zero, Nat.zero_add, one_mul, mul_one]
  | succ a ih =>
    have hs : shift R q 1 (blockSwap q a b) * T q (a + 1 + j) =
        T q (j + 1) * shift R q 1 (blockSwap q a b) := by
      rw [show a + 1 + j = a + j + 1 by omega, ← shift_T 1 (a + j), ← map_mul, ih hj, map_mul,
        shift_T]
    rw [blockSwap_succ, mul_assoc, hs, ← mul_assoc, cosetRep_mul_T_succ (Nat.zero_le j)
      (by omega), mul_assoc]

/-- The block swap carries a generator crossing two of the first `a` strands to the corresponding
generator crossing two of the strands `b, …, a + b - 1`. -/
private theorem blockSwap_mul_T {a b i : ℕ} (hi : i + 1 < a) :
    blockSwap q a b * T q i = T q (i + b) * blockSwap q a b := by
  induction a generalizing i with
  | zero => omega
  | succ a ih =>
    rcases i with _ | i
    · -- The crossing `T 0` of the first two strands, which needs the two-block identity.
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hT : Commute (T q 0) (shift R q 2 (blockSwap q a b)) :=
        commute_shift_of_mem_stage (T_mem_stage (by omega)) _
      rw [blockSwap_succ, blockSwap_succ, map_mul, shift_shift, shift_cosetRep, Nat.zero_add,
        ← mul_assoc, mul_assoc _ _ (T q 0), ← hT.eq, ← mul_assoc,
        cosetRep_mul_cosetRep_mul_T_zero, Nat.zero_add]
      simp only [mul_assoc]
    · -- A crossing inside the shifted block, which commutes past `cosetRep q b 0`.
      have hs : shift R q 1 (blockSwap q a b) * T q (i + 1) =
          T q (i + 1 + b) * shift R q 1 (blockSwap q a b) := by
        rw [← shift_T 1 i, ← map_mul, ih (by omega), map_mul, shift_T,
          show i + b + 1 = i + 1 + b by omega]
      have hc : cosetRep q b 0 * T q (i + 1 + b) = T q (i + 1 + b) * cosetRep q b 0 :=
        (commute_T_of_mem_stage (by omega) (cosetRep_mem_stage b 0)).eq.symm
      rw [blockSwap_succ, mul_assoc, hs, ← mul_assoc, hc, mul_assoc]

/-- The subalgebra of elements `x` with `P * g x = f x * P`, for algebra endomorphisms `f`, `g`. -/
private def intertwiners (P : InfiniteTypeAHeckeAlgebra R q)
    (f g : InfiniteTypeAHeckeAlgebra R q →ₐ[R] InfiniteTypeAHeckeAlgebra R q) :
    Subalgebra R (InfiniteTypeAHeckeAlgebra R q) where
  carrier := {x | P * g x = f x * P}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    rw [mul_add, add_mul, hx, hy]
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, AlgHom.commutes]
    exact (Algebra.commutes r P).symm

private theorem mem_intertwiners {P x : InfiniteTypeAHeckeAlgebra R q}
    {f g : InfiniteTypeAHeckeAlgebra R q →ₐ[R] InfiniteTypeAHeckeAlgebra R q} :
    x ∈ intertwiners P f g ↔ P * g x = f x * P :=
  Iff.rfl

/-- **Exchanging two blocks of strands.** For `x` in the stage `a` and `y` in the stage `b`, the
block swap conjugates `x * shift a y` to `y * shift b x`. -/
private theorem blockSwap_mul_mul_shift {a b : ℕ} {x y : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q a) (hy : y ∈ stage R q b) :
    blockSwap q a b * (x * shift R q a y) = y * shift R q b x * blockSwap q a b := by
  have hX : stage R q a ≤ intertwiners (blockSwap q a b) (shift R q b) (AlgHom.id R _) :=
    stage_le_iff.2 fun i hi ↦ mem_intertwiners.2 <| by
      rw [AlgHom.id_apply, shift_T, blockSwap_mul_T hi]
  have hY : stage R q b ≤ intertwiners (blockSwap q a b) (AlgHom.id R _) (shift R q a) :=
    stage_le_iff.2 fun j hj ↦ mem_intertwiners.2 <| by
      rw [AlgHom.id_apply, shift_T, Nat.add_comm j a, blockSwap_mul_T_add hj]
  have hx' : blockSwap q a b * x = shift R q b x * blockSwap q a b := by
    simpa only [AlgHom.id_apply] using mem_intertwiners.1 (hX hx)
  have hy' : blockSwap q a b * shift R q a y = y * blockSwap q a b := by
    simpa only [AlgHom.id_apply] using mem_intertwiners.1 (hY hy)
  rw [← mul_assoc, hx', mul_assoc, hy', ← mul_assoc, (commute_shift_of_mem_stage hy x).eq]

end BlockSwap

section Exchange

/-- **Exchanging two blocks modulo commutators.** For `x` in the stage `a` and `y` in the stage
`b`, the element `x * shift a y`, with `x` on the first `a` strands and `y` on the next `b`, is
congruent modulo the commutators of the stage `a + b` to `y * shift b x`, with the two blocks
exchanged. -/
theorem mul_shift_sub_mul_shift_mem_stageCommutatorSpan {a b : ℕ}
    {x y : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q a) (hy : y ∈ stage R q b) :
    x * shift R q a y - y * shift R q b x ∈ stageCommutatorSpan R q (a + b) := by
  obtain ⟨u, hu⟩ := isUnit_blockSwap (q := q) a b
  set P := blockSwap q a b
  set P' : InfiniteTypeAHeckeAlgebra R q :=
    (((u⁻¹ : (stage R q (a + b))ˣ) : stage R q (a + b)) : InfiniteTypeAHeckeAlgebra R q)
  have hP' : P' ∈ stage R q (a + b) := SetLike.coe_mem _
  have hP'P : P' * P = 1 := by
    simpa only [hu, MulMemClass.coe_mul, OneMemClass.coe_one] using congrArg Subtype.val u.inv_mul
  have hPP' : P * P' = 1 := by
    simpa only [hu, MulMemClass.coe_mul, OneMemClass.coe_one] using congrArg Subtype.val u.mul_inv
  set Z := y * shift R q b x
  have hZ : Z ∈ stage R q (a + b) :=
    mul_mem (stage_mono (Nat.le_add_left b a) hy) (shift_mem_stage b hx)
  -- `x * shift a y = P' * (Z * P)` and `Z = (Z * P) * P'`.
  have hX : x * shift R q a y = P' * (Z * P) := by
    rw [← blockSwap_mul_mul_shift hx hy, ← mul_assoc, hP'P, one_mul]
  have hZ' : P' * (Z * P) - Z = P' * (Z * P) - Z * P * P' := by rw [mul_assoc Z, hPP', mul_one]
  rw [hX, hZ']
  exact mul_sub_mul_mem_stageCommutatorSpan hP' (mul_mem hZ (blockSwap_mem_stage a b))

/-- A trace on the stage `a + b` takes the same value on `x * shift a y` and on `y * shift b x`,
for `x` in the stage `a` and `y` in the stage `b`. -/
theorem map_mul_shift_comm {M : Type*} [AddCommGroup M] [Module R M]
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] M} {a b : ℕ}
    (hτ : ∀ x ∈ stage R q (a + b), ∀ y ∈ stage R q (a + b), τ (x * y) = τ (y * x))
    {x y : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q a) (hy : y ∈ stage R q b) :
    τ (x * shift R q a y) = τ (y * shift R q b x) := by
  rw [← sub_eq_zero, ← map_sub]
  exact stageCommutatorSpan_le_ker_iff.2 hτ (mul_shift_sub_mul_shift_mem_stageCommutatorSpan hx hy)

end Exchange

section CycleBlockWord

variable (q) in
/-- The cycle-block word of a list `[m₁, …, mₖ]` of block sizes: the cycle words `ζ_(m₁), …,
ζ_(mₖ)` placed on consecutive disjoint blocks of strands,
`ζ_(m₁) * shift m₁ ζ_(m₂) * shift (m₁ + m₂) ζ_(m₃) * ⋯`. -/
def cycleBlockWord : List ℕ → InfiniteTypeAHeckeAlgebra R q
  | [] => 1
  | m :: l => cycleWord q m * shift R q m (cycleBlockWord l)

/-- The cycle-block word of the empty list is `1`. -/
@[simp]
theorem cycleBlockWord_nil : cycleBlockWord q [] = 1 := by
  rw [cycleBlockWord]

/-- The cycle-block word of `m :: l` is `ζₘ` followed by the shift by `m` of the cycle-block word
of `l`. -/
theorem cycleBlockWord_cons (m : ℕ) (l : List ℕ) :
    cycleBlockWord q (m :: l) = cycleWord q m * shift R q m (cycleBlockWord q l) := by
  rw [cycleBlockWord]

/-- The cycle-block word of a single block is the cycle word. -/
@[simp]
theorem cycleBlockWord_singleton (m : ℕ) : cycleBlockWord q [m] = cycleWord q m := by
  rw [cycleBlockWord_cons, cycleBlockWord_nil, map_one, mul_one]

/-- The cycle-block word of a concatenation is the cycle-block word of the first list followed by
the shifted cycle-block word of the second. -/
theorem cycleBlockWord_append (l l' : List ℕ) :
    cycleBlockWord q (l ++ l') = cycleBlockWord q l * shift R q l.sum (cycleBlockWord q l') := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.cons_append, cycleBlockWord_cons, cycleBlockWord_cons, ih, map_mul, shift_shift,
      List.sum_cons, mul_assoc]

/-- The cycle-block word of a list of block sizes lies in the stage of its total number of
strands. -/
theorem cycleBlockWord_mem_stage (l : List ℕ) : cycleBlockWord q l ∈ stage R q l.sum := by
  induction l with
  | nil => simpa only [cycleBlockWord_nil] using one_mem _
  | cons m l ih =>
    rw [cycleBlockWord_cons, List.sum_cons]
    refine mul_mem (stage_mono (Nat.le_add_right m l.sum) (cycleWord_mem_stage m)) ?_
    rw [Nat.add_comm]
    exact shift_mem_stage m ih

/-- **Reordering blocks.** Permuting the block sizes does not change the class of a cycle-block
word modulo the commutators of its stage. -/
theorem cycleBlockWord_sub_mem_stageCommutatorSpan {l l' : List ℕ} (h : l.Perm l') :
    cycleBlockWord q l - cycleBlockWord q l' ∈ stageCommutatorSpan R q l.sum := by
  induction h with
  | nil => simp
  | cons m _ ih =>
    rw [cycleBlockWord_cons, cycleBlockWord_cons, ← mul_sub, ← map_sub, List.sum_cons]
    exact mul_shift_mem_stageCommutatorSpan_left (cycleWord_mem_stage m) ih
  | swap m m' l =>
    rw [cycleBlockWord_cons, cycleBlockWord_cons, cycleBlockWord_cons, cycleBlockWord_cons,
      map_mul, map_mul, shift_shift, shift_shift, ← mul_assoc, ← mul_assoc, Nat.add_comm m m',
      ← sub_mul, List.sum_cons, List.sum_cons, ← Nat.add_assoc]
    exact mul_shift_mem_stageCommutatorSpan_right
      (mul_shift_sub_mul_shift_mem_stageCommutatorSpan (cycleWord_mem_stage m')
        (cycleWord_mem_stage m))
      (cycleBlockWord_mem_stage l)
  | trans h₁ _ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel _ (cycleBlockWord q _)]
    exact add_mem ih₁ (h₁.sum_eq ▸ ih₂)

end CycleBlockWord

section CycleBlock

variable (q) in
/-- The element `ζ_λ` of a partition `λ` of `n`: the cycle-block word of the parts
`λ₁ ≥ λ₂ ≥ ⋯` of `λ`, placing the cycle word `ζ_(λᵢ)` on the `i`-th of consecutive disjoint
blocks of strands. -/
def cycleBlock {n : ℕ} (μ : n.Partition) : InfiniteTypeAHeckeAlgebra R q :=
  cycleBlockWord q (μ.parts.sort (· ≥ ·))

/-- The element `ζ_λ` is the cycle-block word of the parts of `λ` in nonincreasing order. -/
theorem cycleBlock_def {n : ℕ} (μ : n.Partition) :
    cycleBlock q μ = cycleBlockWord q (μ.parts.sort (· ≥ ·)) := (rfl)

/-- The sum of the parts of a partition, listed in nonincreasing order, is the partitioned
number. -/
private theorem sum_sort_parts {n : ℕ} (μ : n.Partition) : (μ.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- The element `ζ_λ` of a partition of `n` lies in the stage of the first `n` strands. -/
theorem cycleBlock_mem_stage {n : ℕ} (μ : n.Partition) : cycleBlock q μ ∈ stage R q n := by
  have h := cycleBlockWord_mem_stage (q := q) (μ.parts.sort (· ≥ ·))
  rwa [sum_sort_parts] at h

/-- The cycle-block word of a list of positive block sizes with sum `n` is congruent modulo the
commutators of the stage `n` to the element `ζ_λ` of the partition `λ` with these parts. -/
theorem cycleBlockWord_sub_cycleBlock_mem_stageCommutatorSpan {n : ℕ} {l : List ℕ}
    (hpos : ∀ m ∈ l, 0 < m) (hsum : l.sum = n) :
    cycleBlockWord q l -
        cycleBlock (n := n) q ⟨↑l, fun hm ↦ hpos _ hm, by rw [Multiset.sum_coe, hsum]⟩ ∈
      stageCommutatorSpan R q n := by
  have h := cycleBlockWord_sub_mem_stageCommutatorSpan (q := q)
    (Multiset.coe_eq_coe.1 (Multiset.sort_eq (↑l : Multiset ℕ) (· ≥ ·))).symm
  rw [hsum] at h
  rwa [cycleBlock_def]

/-- The submodule of the stage `n + 1` spanned modulo commutators by the products of an element of
the stage `j ≤ n` with the cycle word on the remaining `n + 1 - j` strands. -/
private def lastCycleSpan (n : ℕ) : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
  Submodule.span R {z | ∃ j ≤ n, ∃ x ∈ stage R q j, z = x * shift R q j (cycleWord q (n + 1 - j))}
    ⊔ stageCommutatorSpan R q (n + 1)

/-- The descending product `T (n - 1) * ⋯ * T a` is a rescaled shifted cycle word. -/
private theorem cosetRep_eq_smul_shift_cycleWord {a n : ℕ} (han : a ≤ n) :
    cosetRep q n a = (↑q⁻¹ : R) ^ (n - a) • shift R q a (cycleWord q (n + 1 - a)) := by
  rw [cycleWord_def, show n + 1 - a - 1 = n - a by omega, map_smul, shift_cosetRep,
    Nat.zero_add, Nat.sub_add_cancel han, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]

/-- The rotation step of the reduction: for `b` and `e` in the stage `a + 1` and `a < n`, the
element `b * T a * e * cosetRep q n (a + 1)` is congruent modulo the commutators of the stage
`n + 1` to `e * b * cosetRep q n a`. -/
private theorem mul_T_mul_mul_cosetRep_sub_mem {a n : ℕ} (han : a < n)
    {b e : InfiniteTypeAHeckeAlgebra R q} (hb : b ∈ stage R q (a + 1))
    (he : e ∈ stage R q (a + 1)) :
    b * T q a * e * cosetRep q n (a + 1) - e * b * cosetRep q n a ∈
      stageCommutatorSpan R q (n + 1) := by
  have hbc : b * cosetRep q n (a + 1) = cosetRep q n (a + 1) * b := by
    rw [cosetRep_eq_smul_shift_cycleWord han, mul_smul_comm, smul_mul_assoc,
      (commute_shift_of_mem_stage hb _).eq]
  have hle : a + 1 ≤ n + 1 := by omega
  have hbTe : b * T q a * e ∈ stage R q (n + 1) :=
    mul_mem (mul_mem (stage_mono hle hb) (T_mem_stage (by omega))) (stage_mono hle he)
  have hC : cosetRep q n (a + 1) ∈ stage R q (n + 1) := cosetRep_mem_stage n (a + 1)
  -- Rotate `cosetRep q n (a + 1)` to the front, then `e` to the front.
  have h₁ := mul_sub_mul_mem_stageCommutatorSpan hbTe hC
  have h₂ := mul_sub_mul_mem_stageCommutatorSpan
    (mul_mem (mul_mem (stage_mono hle hb) hC) (T_mem_stage (i := a) (by omega)))
    (stage_mono hle he)
  have e₁ : cosetRep q n (a + 1) * (b * T q a * e) = b * cosetRep q n (a + 1) * T q a * e := by
    rw [hbc]
    simp only [mul_assoc]
  have e₂ : e * (b * cosetRep q n (a + 1) * T q a) = e * b * cosetRep q n a := by
    rw [mul_assoc b, cosetRep_succ_mul_T han, mul_assoc]
  have key : b * T q a * e * cosetRep q n (a + 1) - e * b * cosetRep q n a =
      (b * T q a * e * cosetRep q n (a + 1) - cosetRep q n (a + 1) * (b * T q a * e)) +
        (b * cosetRep q n (a + 1) * T q a * e - e * (b * cosetRep q n (a + 1) * T q a)) := by
    rw [e₁, e₂]
    abel
  rw [key]
  exact add_mem h₁ h₂

/-- The reduction along `Hₙ₊₁ = Hₙ + Hₙ Tₙ₋₁ Hₙ`: for `y` in the stage `a + 1` and `a ≤ n`, the
element `y * cosetRep q n a` lies in `lastCycleSpan n`. -/
private theorem mul_cosetRep_mem_lastCycleSpan {a n : ℕ} (han : a ≤ n)
    {y : InfiniteTypeAHeckeAlgebra R q} (hy : y ∈ stage R q (a + 1)) :
    y * cosetRep q n a ∈ lastCycleSpan (q := q) n := by
  have hgen : ∀ {j}, j ≤ n → ∀ {x}, x ∈ stage R q j → x * cosetRep q n j ∈ lastCycleSpan n :=
    fun hj x hx ↦ by
      rw [cosetRep_eq_smul_shift_cycleWord hj, mul_smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span ⟨_, hj, x, hx,
        rfl⟩))
  induction a generalizing y with
  | zero =>
    have h0 : stage R q (0 + 1) = stage R q 0 := by
      rw [stage_eq_bot_of_le_one le_rfl, stage_eq_bot_of_le_one (Nat.zero_le 1)]
    exact hgen han (h0 ▸ hy)
  | succ a ih =>
    let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
      (lastCycleSpan n).comap (LinearMap.mulRight R (cosetRep q n (a + 1)))
    refine (toSubmodule_stage_add_two_le_iff (P := P)).2 ⟨fun b hb ↦ hgen han hb,
      fun b hb e he ↦ ?_⟩ hy
    -- `b * T a * e * cosetRep q n (a + 1) ≡ e * b * cosetRep q n a`, which is in the span by the
    -- inductive hypothesis.
    have h := mul_T_mul_mul_cosetRep_sub_mem (by omega : a < n) hb he
    have hm := ih (by omega) (mul_mem he hb)
    rw [Submodule.mem_comap, LinearMap.mulRight_apply,
      ← sub_add_cancel (b * T q a * e * cosetRep q n (a + 1)) (e * b * cosetRep q n a)]
    exact add_mem (Submodule.mem_sup_right h) hm

/-- The span of the cycle-block words of compositions of `n`, that is of lists of positive block
sizes with sum `n`. -/
private def compositionSpan (n : ℕ) : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
  Submodule.span R {z | ∃ l : List ℕ, (∀ m ∈ l, 0 < m) ∧ l.sum = n ∧ z = cycleBlockWord q l}

/-- Every element of the stage `n` is congruent modulo commutators to a combination of
cycle-block words of compositions of `n`. -/
private theorem toSubmodule_stage_le_compositionSpan_sup (n : ℕ) :
    Subalgebra.toSubmodule (stage R q n) ≤
      compositionSpan (q := q) n ⊔ stageCommutatorSpan R q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · -- On no strands the stage consists of the scalars, multiples of the empty word.
      intro x hx
      rw [Subalgebra.mem_toSubmodule, stage_eq_bot_of_le_one (Nat.zero_le 1), Algebra.mem_bot] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨[], by simp, rfl, by rw [cycleBlockWord_nil]⟩))
    · intro y hy
      have hy' := mul_cosetRep_mem_lastCycleSpan (q := q) le_rfl hy
      rw [cosetRep_self, mul_one] at hy'
      refine (sup_le (Submodule.span_le.2 ?_) le_sup_right :
        lastCycleSpan n ≤ compositionSpan (n + 1) ⊔ stageCommutatorSpan R q (n + 1)) hy'
      rintro _ ⟨j, hj, x, hx, rfl⟩
      -- Append the last block to each composition of `j` expressing `x`.
      have hle : compositionSpan j ⊔ stageCommutatorSpan R q j ≤
          (compositionSpan (n + 1) ⊔ stageCommutatorSpan R q (n + 1)).comap
            (LinearMap.mulRight R (shift R q j (cycleWord q (n + 1 - j)))) := by
        refine sup_le (Submodule.span_le.2 ?_) fun c hc ↦ ?_
        · rintro _ ⟨l, hpos, hsum, rfl⟩
          refine Submodule.mem_sup_left (Submodule.subset_span ⟨l ++ [n + 1 - j], ?_, ?_, ?_⟩)
          · simp only [List.mem_append, List.mem_singleton]
            rintro m (hm | rfl)
            exacts [hpos m hm, by omega]
          · rw [List.sum_append, hsum, List.sum_singleton]
            omega
          · rw [LinearMap.mulRight_apply, cycleBlockWord_append, hsum, cycleBlockWord_singleton]
        · have := mul_shift_mem_stageCommutatorSpan_right hc
            (cycleWord_mem_stage (q := q) (n + 1 - j))
          rw [show j + (n + 1 - j) = n + 1 by omega] at this
          exact Submodule.mem_sup_right this
      exact hle (ih j (by omega) hx)

/-- **The elements `ζ_λ` span the cocenter.** The stage of the first `n` strands is spanned by the
elements `ζ_λ`, for `λ` a partition of `n`, together with its commutators. -/
theorem span_cycleBlock_sup_stageCommutatorSpan (n : ℕ) :
    Submodule.span R (Set.range (cycleBlock (R := R) q (n := n))) ⊔ stageCommutatorSpan R q n =
      Subalgebra.toSubmodule (stage R q n) := by
  refine le_antisymm (sup_le (Submodule.span_le.2 ?_) (stageCommutatorSpan_le_toSubmodule_stage n))
    ((toSubmodule_stage_le_compositionSpan_sup n).trans
      (sup_le (Submodule.span_le.2 ?_) le_sup_right))
  · rintro _ ⟨μ, rfl⟩
    exact cycleBlock_mem_stage μ
  · rintro _ ⟨l, hpos, hsum, rfl⟩
    rw [← sub_add_cancel (cycleBlockWord q l) (cycleBlock (n := n) q ⟨↑l, fun hm ↦ hpos _ hm,
      by rw [Multiset.sum_coe, hsum]⟩)]
    exact add_mem (Submodule.mem_sup_right
      (cycleBlockWord_sub_cycleBlock_mem_stageCommutatorSpan hpos hsum))
      (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩))

/-- **The classes of the elements `ζ_λ` span the cocenter.** Inside the stage of the first `n`
strands, the elements `ζ_λ`, for `λ` a partition of `n`, together with the commutator submodule
span everything: their classes span the cyclic quotient `Hₙ / [Hₙ, Hₙ]`. -/
theorem span_cycleBlock_sup_commutatorSubmodule (n : ℕ) :
    Submodule.span R (Set.range fun μ : n.Partition ↦
        (⟨cycleBlock q μ, cycleBlock_mem_stage μ⟩ : stage R q n)) ⊔
      commutatorSubmodule R (stage R q n) = ⊤ := by
  have h : (Submodule.span R (Set.range fun μ : n.Partition ↦
        (⟨cycleBlock q μ, cycleBlock_mem_stage μ⟩ : stage R q n)) ⊔
      commutatorSubmodule R (stage R q n)).map (stage R q n).val.toLinearMap =
        Subalgebra.toSubmodule (stage R q n) := by
    rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp]
    exact span_cycleBlock_sup_stageCommutatorSpan n
  refine eq_top_iff.2 fun z _ ↦ ?_
  have hz : (z : InfiniteTypeAHeckeAlgebra R q) ∈ Subalgebra.toSubmodule (stage R q n) := z.2
  rw [← h] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rwa [← Subtype.val_injective hwz]

/-- **Traces are determined by their values on the elements `ζ_λ`.** Two linear maps which are
traces on the stage of the first `n` strands agree on that stage as soon as they agree on the
element `ζ_λ` of every partition `λ` of `n`. -/
theorem trace_eq_of_cycleBlock_values {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    {τ τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] M}
    (hτ : ∀ x ∈ stage R q n, ∀ y ∈ stage R q n, τ (x * y) = τ (y * x))
    (hτ' : ∀ x ∈ stage R q n, ∀ y ∈ stage R q n, τ' (x * y) = τ' (y * x))
    (h : ∀ μ : n.Partition, τ (cycleBlock q μ) = τ' (cycleBlock q μ))
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q n) : τ x = τ' x := by
  have hle : Submodule.span R (Set.range (cycleBlock (R := R) q (n := n))) ⊔
      stageCommutatorSpan R q n ≤ LinearMap.ker (τ - τ') := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨μ, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, h μ, sub_self]
    · exact stageCommutatorSpan_le_ker_iff.2 fun x hx y hy ↦ by
        rw [LinearMap.sub_apply, LinearMap.sub_apply, hτ x hx y hy, hτ' x hx y hy]
  rw [span_cycleBlock_sup_stageCommutatorSpan] at hle
  rw [← sub_eq_zero, ← LinearMap.sub_apply]
  exact hle hx

end CycleBlock

namespace IsMarkovTrace

variable {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- A Markov trace with parameter `z` takes the value `∏ᵢ (q * z) ^ (mᵢ - 1)` on the cycle-block
word of `[m₁, …, mₖ]`. -/
theorem map_cycleBlockWord (hτ : IsMarkovTrace z τ) (l : List ℕ) :
    τ (cycleBlockWord q l) = (l.map fun m ↦ ((q : R) * z) ^ (m - 1)).prod := by
  induction l with
  | nil => rw [cycleBlockWord_nil, hτ.map_one, List.map_nil, List.prod_nil]
  | cons m l ih =>
    rw [cycleBlockWord_cons, hτ.map_mul_shift (cycleWord_mem_stage m), hτ.map_cycleWord, ih,
      List.map_cons, List.prod_cons]

/-- A Markov trace with parameter `z` takes the value `∏ᵢ (q * z) ^ (λᵢ - 1)` on the element
`ζ_λ` of a partition `λ`. -/
theorem map_cycleBlock (hτ : IsMarkovTrace z τ) {n : ℕ} (μ : n.Partition) :
    τ (cycleBlock q μ) = (μ.parts.map fun m ↦ ((q : R) * z) ^ (m - 1)).prod := by
  rw [cycleBlock_def, hτ.map_cycleBlockWord, ← Multiset.prod_coe, ← Multiset.map_coe,
    Multiset.sort_eq]

end IsMarkovTrace

end InfiniteTypeAHeckeAlgebra

end TauCeti
