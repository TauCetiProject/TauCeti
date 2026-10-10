/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.DG.Algebra.Opposite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Nat.Choose.Basic

/-!
# The opposite of an `A∞` algebra

The opposite of an `A∞` algebra on a graded module `A` is the `A∞` algebra on the same graded
module whose operations read their inputs in the reverse order.  On homogeneous inputs

`mₙᵒᵖ(x₀, …, xₙ₋₁) = (-1) ^ (∑_{i < j} |xᵢ| |xⱼ| + (n - 1).choose 2) • mₙ(xₙ₋₁, …, x₀)`.

The first part of the exponent is the Koszul sign of reversing the order of homogeneous inputs.
The second depends only on the arity: it vanishes in arities one and two, so `m₁ᵒᵖ = m₁` and
`m₂ᵒᵖ(x, y) = (-1) ^ (|x| |y|) • m₂(y, x)` is the Koszul-signed opposite product, and it is what
makes the Stasheff identities hold in higher arity.  Indeed the `(p, s, t)` term of the opposite
identity of arity `n` is the `(t, s, p)` term of the original identity on the reversed inputs, up
to the opposite sign of the whole word (`AInfinity.opExp_replaceDeg`).

Opposites let left modules be treated as right modules over the opposite algebra, as
`TauCeti.IsDGLeftModule.gradedOppositeRight` does for DG modules.  The construction extends the
Koszul-signed graded opposite `TauCeti.GradedOpposite` of a DG algebra: the opposite of the `A∞`
algebra of a DG algebra is the `A∞` algebra of its graded opposite, through a bijective strict
morphism.

## Main definitions

* `TauCeti.AInfinity.opExp`: the exponent of the sign of the opposite operations.
* `TauCeti.AInfinityAlgebra.op`: the opposite of an `A∞` algebra.
* `TauCeti.IsDGAlgebra.gradedOppositeStrictHom`: the strict morphism from the opposite of the `A∞`
  algebra of a DG algebra to the `A∞` algebra of its graded opposite.

## Main results

* `TauCeti.AInfinity.opExp_replaceDeg`: the sign identity turning the original Stasheff identities
  into the opposite ones.
* `TauCeti.AInfinityAlgebra.op_m_apply`: the opposite operations on homogeneous inputs.
* `TauCeti.AInfinityAlgebra.op_op`: passing to the opposite is an involution.
* `TauCeti.AInfinityAlgebra.op_m_one` and `TauCeti.AInfinityAlgebra.op_m_two_apply`: the unary
  operation is unchanged and the binary operation is the Koszul-signed reversed product.
* `TauCeti.AInfinityAlgebra.StrictUnit.op`: a strict unit is a strict unit of the opposite.
* `TauCeti.AInfinityAlgebra.op_m_eq_zero_iff`: an opposite operation vanishes exactly when the
  original one does, so opposites of DG-type `A∞` algebras are again of DG type.
* `TauCeti.IsDGAlgebra.gradedOppositeStrictHom_bijective`: the comparison with the graded opposite
  of a DG algebra is bijective.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for the Koszul sign convention.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the operations of
  degree `2 - n` and the Stasheff identities.
-/

public section

open scoped BigOperators
open _root_.MultilinearMap

universe uR uA

namespace TauCeti

namespace AInfinity

/-- The exponent of the sign of the opposite operation of arity `k` on inputs of degrees `d`:
the Koszul exponent `∑_{i < j < k} d i * d j` of reversing the order of the inputs, plus the
arity correction `(k - 1).choose 2`. -/
def opExp (k : ℕ) (d : ℕ → ℤ) : ℤ :=
  (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, d i * d j) + ((k - 1).choose 2 : ℕ)

/-- The defining expression for the exponent of the opposite sign. -/
theorem opExp_def (k : ℕ) (d : ℕ → ℤ) :
    opExp k d =
      (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, d i * d j) + ((k - 1).choose 2 : ℕ) := (rfl)

/-- The exponent of the opposite sign through the sum and the sum of squares of the degrees. -/
theorem two_mul_opExp (k : ℕ) (d : ℕ → ℤ) :
    2 * opExp k d =
      (∑ i ∈ Finset.range k, d i) ^ 2 - ∑ i ∈ Finset.range k, d i ^ 2 +
        2 * ((k - 1).choose 2 : ℕ) := by
  rw [opExp_def, mul_add, TauCeti.two_mul_sum_range_pair]

/-- In arity zero the opposite sign is trivial. -/
@[simp]
theorem opExp_zero (d : ℕ → ℤ) : opExp 0 d = 0 := by
  simp [opExp_def]

/-- In arity one the opposite sign is trivial. -/
@[simp]
theorem opExp_one (d : ℕ → ℤ) : opExp 1 d = 0 := by
  simp [opExp_def]

/-- In arity two the opposite sign is the Koszul sign `(-1) ^ (d 0 * d 1)` of the transposition. -/
@[simp]
theorem opExp_two (d : ℕ → ℤ) : opExp 2 d = d 0 * d 1 := by
  simp [opExp_def, Finset.sum_range_succ]

/-- The opposite sign only reads the first `k` degrees. -/
theorem opExp_congr {k : ℕ} {d e : ℕ → ℤ} (h : ∀ i < k, d i = e i) :
    opExp k d = opExp k e := by
  rw [opExp_def, opExp_def]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi hj
  rw [h i (by omega), h j hj]

/-- Reversing the degrees does not change the opposite sign. -/
@[simp]
theorem opExp_reverse (k : ℕ) (d : ℕ → ℤ) : opExp k (fun i ↦ d (k - 1 - i)) = opExp k d := by
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  rw [two_mul_opExp, two_mul_opExp, Finset.sum_range_reflect d k,
    Finset.sum_range_reflect (fun i ↦ d i ^ 2) k]

/-- **The sign identity behind the opposite Stasheff identities.**  Collapsing the block of
length `s` at position `p` of an arity `p + s + t` word and passing to the opposite operations
reverses the decomposition to `t + s + p`.  The two exponents collected on the two sides of
this comparison -- the Stasheff coefficients `p + s * t` and `t + s * p`, the Koszul
coefficients of the inner operation crossing the prefix of length `p`, respectively of the
reversed prefix of length `t`, and the two opposite signs of the outer and inner operations --
differ by the opposite sign of the whole word, up to an explicit even number. -/
theorem opExp_replaceDeg (d : ℕ → ℤ) (p s t : ℕ) (hs : 1 ≤ s) :
    opExp (p + 1 + t) (replaceDeg d p s) + opExp s (fun j ↦ d (p + j)) +
        ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i) =
      opExp (p + s + t) d +
        ((t : ℤ) + s * p + (2 - s) * ∑ i ∈ Finset.range t, d (p + s + t - 1 - i)) +
        2 * ((2 - s) * ∑ i ∈ Finset.range p, d i - p * (s - 1)) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  -- Sums of a function of the degrees after the block has been collapsed.
  have hD (f : ℤ → ℤ) : ∑ i ∈ Finset.range (p + 1 + t), f (replaceDeg d p (s + 1) i) =
      ∑ i ∈ Finset.range p, f (d i) + f (blockDeg d p (s + 1)) +
        ∑ j ∈ Finset.range t, f (d (p + (s + 1) + j)) := by
    rw [Finset.sum_range_add, Finset.sum_range_succ]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ (by rw [replaceDeg_self]))
      (Finset.sum_congr rfl fun j _ ↦ ?_)
    · exact Finset.sum_congr rfl fun i hi ↦ by
        rw [replaceDeg_of_lt _ _ _ (Finset.mem_range.1 hi)]
    · rw [replaceDeg_of_gt _ _ _ (by omega)]
      congr 2
      omega
  -- Sums of a function of the original degrees, split into prefix, block, and suffix.
  have hd (f : ℤ → ℤ) : ∑ i ∈ Finset.range (p + (s + 1) + t), f (d i) =
      ∑ i ∈ Finset.range p, f (d i) + ∑ j ∈ Finset.range (s + 1), f (d (p + j)) +
        ∑ j ∈ Finset.range t, f (d (p + (s + 1) + j)) := by
    rw [Finset.sum_range_add, Finset.sum_range_add]
  have hrev : ∑ i ∈ Finset.range t, d (p + (s + 1) + t - 1 - i) =
      ∑ j ∈ Finset.range t, d (p + (s + 1) + j) := by
    rw [← Finset.sum_range_reflect (fun j ↦ d (p + (s + 1) + j)) t]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := Finset.mem_range.1 hi
    congr 1
    omega
  have h₁ := two_mul_opExp (p + 1 + t) (replaceDeg d p (s + 1))
  have h₂ := two_mul_opExp (s + 1) (fun j ↦ d (p + j))
  have h₃ := two_mul_opExp (p + (s + 1) + t) d
  have hDS := hD id
  have hDQ := hD (· ^ 2)
  have hdS := hd id
  have hdQ := hd (· ^ 2)
  simp only [id] at hDS hdS
  beta_reduce at hDQ hdQ
  rw [hDS, hDQ] at h₁
  rw [hdS, hdQ] at h₃
  have hc₁ : p + 1 + t - 1 = p + t := by omega
  have hc₃ : p + (s + 1) + t - 1 = p + t + s := by omega
  rw [hc₁] at h₁
  rw [hc₃, Nat.add_choose_two] at h₃
  rw [Nat.add_sub_cancel] at h₂
  rw [hrev]
  rw [blockDeg_def] at h₁
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  push_cast at h₁ h₂ h₃ ⊢
  linear_combination h₁ + h₂ - h₃

end AInfinity

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The operations of the opposite, assembled from their values on homogeneous pieces: on inputs
of degrees `d` the arity-`n` operation is `(-1) ^ opExp n d` times `m n` on the reversed inputs. -/
private noncomputable def opOperation (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ A) A :=
  InternalGrading.multilinearFromPieces (fun _ : Fin n ↦ 𝒜.grading) fun d ↦
    negOnePowCast R (AInfinity.opExp n fun i ↦ if h : i < n then d ⟨i, h⟩ else 0) •
      ((𝒜.m n).domDomCongr Fin.revPerm).compLinearMap
        fun i ↦ (𝒜.grading.piece (d i)).subtype

/-- The opposite operations on homogeneous inputs. -/
private theorem opOperation_apply (𝒜 : AInfinityAlgebra R A) {n : ℕ} (d : ℕ → ℤ)
    (x : Fin n → A) (hx : ∀ i : Fin n, x i ∈ 𝒜.grading.piece (d i)) :
    opOperation 𝒜 n x = negOnePowCast R (AInfinity.opExp n d) • 𝒜.m n (fun i ↦ x i.rev) := by
  have h := InternalGrading.multilinearFromPieces_apply (fun _ : Fin n ↦ 𝒜.grading)
    (fun e : Fin n → ℤ ↦
      negOnePowCast R (AInfinity.opExp n fun i ↦ if h : i < n then e ⟨i, h⟩ else 0) •
        ((𝒜.m n).domDomCongr Fin.revPerm).compLinearMap
          fun i ↦ (𝒜.grading.piece (e i)).subtype)
    (fun i ↦ d i) (fun i ↦ ⟨x i, hx i⟩)
  rw [opOperation, h, smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.domDomCongr_apply]
  congr 2
  exact AInfinity.opExp_congr fun i hi ↦ by simp [hi]

/-- The opposite operations on homogeneous inputs indexed by the naturals. -/
private theorem evalNat_opOperation (𝒜 : AInfinityAlgebra R A) (n : ℕ) (d : ℕ → ℤ)
    (x : ℕ → A) (hx : ∀ i < n, x i ∈ 𝒜.grading.piece (d i)) :
    evalNat (opOperation 𝒜 n) x =
      negOnePowCast R (AInfinity.opExp n d) • evalNat (𝒜.m n) (fun i ↦ x (n - 1 - i)) := by
  rw [evalNat_def, opOperation_apply 𝒜 d _ fun i ↦ hx i i.isLt, evalNat_def]
  congr 2
  funext i
  rw [Fin.val_rev]
  congr 1
  omega

/-- The opposite operation of arity zero vanishes, since the original one does. -/
private theorem opOperation_zero (𝒜 : AInfinityAlgebra R A) : opOperation 𝒜 0 = 0 := by
  apply InternalGrading.multilinearMap_ext (fun _ : Fin 0 ↦ 𝒜.grading)
  intro d x _
  rw [opOperation_apply 𝒜 (fun _ ↦ 0) x fun i ↦ i.elim0, m_zero]
  simp

/-- The opposite operation of arity `n` has degree `2 - n`, like the original one. -/
private theorem isHomogeneous_opOperation (𝒜 : AInfinityAlgebra R A) (n : ℕ) (hn : 0 < n) :
    MultilinearMap.IsHomogeneous (opOperation 𝒜 n) (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
      (2 - n) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  rw [opOperation_apply 𝒜 (fun i ↦ if h : i < n then d ⟨i, h⟩ else 0) x fun i ↦ by simpa using hx i]
  refine Submodule.smul_mem _ _ ?_
  have h := (𝒜.m_degree n hn).map_mem (fun i ↦ d i.rev) (fun i ↦ x i.rev) fun i ↦ hx i.rev
  have hrev := Equiv.sum_comp Fin.revPerm d
  simp only [Fin.revPerm_apply] at hrev
  rwa [hrev] at h

/-- A Stasheff term of the opposite operations is, up to the opposite sign of the whole word, the
Stasheff term of the original operations on the reversed word, with the reversed decomposition. -/
private theorem stasheffTerm_opOperation (𝒜 : AInfinityAlgebra R A) (d : ℕ → ℤ) (x : ℕ → A)
    {p s t : ℕ} (hs : 1 ≤ s) (hx : ∀ i < p + s + t, x i ∈ 𝒜.grading.piece (d i)) :
    AInfinity.stasheffTerm (opOperation 𝒜) d x p s t =
      negOnePowCast R (AInfinity.opExp (p + s + t) d) •
        AInfinity.stasheffTerm 𝒜.m (fun i ↦ d (p + s + t - 1 - i))
          (fun i ↦ x (p + s + t - 1 - i)) t s p := by
  -- The inner opposite operation, and the degree of the reversed inner value.
  have hin := evalNat_opOperation 𝒜 s (fun j ↦ d (p + j)) (fun j ↦ x (p + j))
    fun j hj ↦ hx _ (by omega)
  have hv : evalNat (𝒜.m s) (fun j ↦ x (p + (s - 1 - j))) ∈
      𝒜.grading.piece (AInfinity.blockDeg d p s) := by
    have h := (𝒜.m_degree s (by omega)).map_mem (fun j : Fin s ↦ d (p + (s - 1 - j)))
      (fun j ↦ x (p + (s - 1 - j))) fun j ↦ hx _ (by omega)
    rw [evalNat_def, AInfinity.blockDeg_def, add_sub_assoc,
      ← Finset.sum_range_reflect (fun j ↦ d (p + j)) s,
      ← Fin.sum_univ_eq_sum_range (fun j ↦ d (p + (s - 1 - j))) s]
    exact h
  rw [AInfinity.stasheffTerm_def, AInfinity.stasheffTerm_def, hin,
    evalNat_replaceBlock_smul _ _ _ (by omega : p < p + 1 + t),
    evalNat_opOperation 𝒜 (p + 1 + t) (AInfinity.replaceDeg d p s) _ fun i hi ↦
      AInfinity.replaceBlock_mem_replaceDeg_of_mem_blockDeg 𝒜.grading.piece
        (n := p + s + t) hx hv (by omega) (by omega)]
  have hu : t + 1 + p = p + 1 + t := by omega
  have hinner : evalNat (𝒜.m s) (fun j ↦ x (p + s + t - 1 - (t + j))) =
      evalNat (𝒜.m s) (fun j ↦ x (p + (s - 1 - j))) :=
    evalNat_congr _ fun j hj ↦ by congr 1; omega
  rw [hu, hinner]
  simp only [smul_smul, ← negOnePowCast_add]
  congr 1
  · -- The signs agree by the sign identity `AInfinity.opExp_replaceDeg`.
    have key := AInfinity.opExp_replaceDeg d p s t hs
    rw [negOnePowCast_eq_intCast, negOnePowCast_eq_intCast, (Int.negOnePow_eq_iff _ _).2]
    exact ⟨(2 - s) * ∑ i ∈ Finset.range p, d i - p * (s - 1), by linear_combination key⟩
  · apply evalNat_congr
    intro i hi
    rcases lt_trichotomy i t with h | rfl | h
    · rw [replaceBlock_of_gt _ _ _ _ (by omega : p < p + 1 + t - 1 - i),
        replaceBlock_of_lt _ _ _ _ h]
      congr 1
      omega
    · have hp : p + 1 + i - 1 - i = p := by omega
      rw [hp, replaceBlock_self, replaceBlock_self]
    · rw [replaceBlock_of_lt _ _ _ _ (by omega : p + 1 + t - 1 - i < p),
        replaceBlock_of_gt _ _ _ _ h]
      congr 1
      omega

/-- The opposite operations satisfy every Stasheff identity on homogeneous inputs: the arity-`n`
Stasheff sum of the opposite is the opposite sign of the word times the Stasheff sum of the
original operations on the reversed word. -/
private theorem stasheffSum_opOperation (𝒜 : AInfinityAlgebra R A) (n : ℕ) (hn : 0 < n)
    (d : ℕ → ℤ) (x : ℕ → A) (hx : ∀ i < n, x i ∈ 𝒜.grading.piece (d i)) :
    AInfinity.stasheffSum (opOperation 𝒜) d x n = 0 := by
  have hrefl := AInfinity.sum_stasheff_reflect n fun a b c ↦
    AInfinity.stasheffTerm 𝒜.m (fun i ↦ d (n - 1 - i)) (fun i ↦ x (n - 1 - i)) a b c
  beta_reduce at hrefl
  have h : AInfinity.stasheffSum (opOperation 𝒜) d x n =
      negOnePowCast R (AInfinity.opExp n d) •
        AInfinity.stasheffSum 𝒜.m (fun i ↦ d (n - 1 - i)) (fun i ↦ x (n - 1 - i)) n := by
    rw [AInfinity.stasheffSum_def, AInfinity.stasheffSum_def, hrefl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc] at hs
    have harity : p + s + (n - p - s) = n := by omega
    rw [stasheffTerm_opOperation 𝒜 d x hs.1 (by rwa [harity]), harity]
  rw [h, 𝒜.stasheff n hn _ _ fun i hi ↦ hx _ (by omega), smul_zero]

/-- The **opposite** of an `A∞` algebra: the same graded module, with the operations

`m n (x₀, …, xₙ₋₁) = (-1) ^ opExp n d • m n (xₙ₋₁, …, x₀)`

on homogeneous inputs of degrees `d`, where `AInfinity.opExp n d` is the Koszul exponent
`∑_{i < j} d i * d j` of reversing the inputs plus `(n - 1).choose 2`. -/
noncomputable def op (𝒜 : AInfinityAlgebra R A) : AInfinityAlgebra R A :=
  ofStasheff 𝒜.grading (opOperation 𝒜) (opOperation_zero 𝒜) (isHomogeneous_opOperation 𝒜)
    (AInfinity.suspensionTaylor 𝒜.grading (opOperation 𝒜))
    (AInfinity.isSuspension_suspensionTaylor _ _) (stasheffSum_opOperation 𝒜)

/-- The opposite has the same grading. -/
@[simp]
theorem op_grading (𝒜 : AInfinityAlgebra R A) : 𝒜.op.grading = 𝒜.grading := by
  rw [op, ofStasheff_grading]

/-- **The opposite operations** on homogeneous inputs: the original operation on the reversed
inputs, with the sign `(-1) ^ opExp n d`. -/
theorem op_m_apply (𝒜 : AInfinityAlgebra R A) {n : ℕ} (d : ℕ → ℤ) (x : Fin n → A)
    (hx : ∀ i : Fin n, x i ∈ 𝒜.grading.piece (d i)) :
    𝒜.op.m n x = negOnePowCast R (AInfinity.opExp n d) • 𝒜.m n (fun i ↦ x i.rev) := by
  rw [op, ofStasheff_m]
  exact opOperation_apply 𝒜 d x hx

/-- **The opposite is an involution.** -/
@[simp]
theorem op_op (𝒜 : AInfinityAlgebra R A) : 𝒜.op.op = 𝒜 := by
  refine ext (by rw [op_grading, op_grading]) (funext fun n ↦
    InternalGrading.multilinearMap_ext_nat 𝒜.grading fun d x hx ↦ ?_)
  have hrev : ∀ i : Fin n, x i.rev ∈ 𝒜.grading.piece (d (n - 1 - i)) := fun i ↦ by
    have hi : n - (i + 1) = n - 1 - i := by omega
    simpa [Fin.val_rev, hi] using hx i.rev
  rw [op_m_apply 𝒜.op d x (by simpa using hx), op_m_apply 𝒜 (fun i ↦ d (n - 1 - i)) _ hrev,
    AInfinity.opExp_reverse, smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul,
    one_smul]
  simp

/-- Passing to the opposite is an involution. -/
theorem op_involutive : Function.Involutive (op (R := R) (A := A)) :=
  op_op

/-- An `A∞` algebra is determined by its opposite. -/
theorem op_injective : Function.Injective (op (R := R) (A := A)) :=
  op_involutive.injective

/-- Two `A∞` algebras have the same opposite exactly when they are equal. -/
@[simp]
theorem op_inj {𝒜 𝒜' : AInfinityAlgebra R A} : 𝒜.op = 𝒜'.op ↔ 𝒜 = 𝒜' :=
  op_injective.eq_iff

/-- An operation of the opposite vanishes exactly when the corresponding original operation does.
In particular the opposite of an `A∞` algebra with vanishing higher operations again has vanishing
higher operations. -/
@[simp]
theorem op_m_eq_zero_iff (𝒜 : AInfinityAlgebra R A) (n : ℕ) : 𝒜.op.m n = 0 ↔ 𝒜.m n = 0 := by
  have key (ℬ : AInfinityAlgebra R A) (h : ℬ.m n = 0) : ℬ.op.m n = 0 :=
    InternalGrading.multilinearMap_ext_nat ℬ.grading fun d x hx ↦ by simp [op_m_apply ℬ d x hx, h]
  refine ⟨fun h ↦ ?_, key 𝒜⟩
  simpa using key 𝒜.op h

/-- The unary operation of the opposite is the original unary operation. -/
@[simp]
theorem op_m_one (𝒜 : AInfinityAlgebra R A) : 𝒜.op.m 1 = 𝒜.m 1 := by
  refine InternalGrading.multilinearMap_ext_nat 𝒜.grading fun d x hx ↦ ?_
  rw [op_m_apply 𝒜 d x hx, AInfinity.opExp_one, negOnePowCast_zero, one_smul]
  congr 1
  funext i
  rw [Subsingleton.elim i.rev i]

/-- The opposite has the same differential. -/
@[simp]
theorem differential_op (𝒜 : AInfinityAlgebra R A) : 𝒜.op.differential = 𝒜.differential := by
  ext x
  simp

/-- **The binary operation of the opposite** is the Koszul-signed reversed product
`m₂ᵒᵖ(x, y) = (-1) ^ (p * q) • m₂(y, x)` for `x` of degree `p` and `y` of degree `q`. -/
theorem op_m_two_apply (𝒜 : AInfinityAlgebra R A) {p q : ℤ} {x y : A}
    (hx : x ∈ 𝒜.grading.piece p) (hy : y ∈ 𝒜.grading.piece q) :
    𝒜.op.m 2 ![x, y] = negOnePowCast R (p * q) • 𝒜.m 2 ![y, x] := by
  rw [op_m_apply 𝒜 (fun i ↦ if i = 0 then p else q) ![x, y]
    (fun i ↦ by fin_cases i <;> simpa), AInfinity.opExp_two]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The binary product of the opposite, as a bilinear map. -/
theorem op_mul_apply (𝒜 : AInfinityAlgebra R A) {p q : ℤ} {x y : A}
    (hx : x ∈ 𝒜.grading.piece p) (hy : y ∈ 𝒜.grading.piece q) :
    𝒜.op.mul x y = negOnePowCast R (p * q) • 𝒜.mul y x := by
  rw [mul_apply, mul_apply, op_m_two_apply 𝒜 hx hy]

/-- A strict unit of an `A∞` algebra is a strict unit of its opposite. -/
theorem StrictUnit.op {𝒜 : AInfinityAlgebra R A} {e : A} (h : 𝒜.StrictUnit e) :
    𝒜.op.StrictUnit e where
  degree_zero := by simpa using h.degree_zero
  binary_left x := by
    have hL : 𝒜.op.mul e = LinearMap.id :=
      𝒜.grading.linearMap_ext fun q y hy ↦ by
        simp [op_mul_apply 𝒜 h.degree_zero hy, h.binary_right]
    simpa using LinearMap.congr_fun hL x
  binary_right x := by
    have hL : 𝒜.op.mul.flip e = LinearMap.id :=
      𝒜.grading.linearMap_ext fun q y hy ↦ by
        simp [op_mul_apply 𝒜 hy h.degree_zero, h.binary_left]
    simpa using LinearMap.congr_fun hL x
  higher n hn x := by
    rintro ⟨i, hi⟩
    -- Freeze the slot `i` at the unit; the remaining slots may be taken homogeneous.
    have hf : (𝒜.op.m n).domDomRestrict (fun j ↦ j ≠ i) (fun _ ↦ e) = 0 := by
      refine InternalGrading.multilinearMap_ext (fun _ ↦ 𝒜.grading) fun d y hy ↦ ?_
      rw [MultilinearMap.domDomRestrict_apply, zero_apply]
      let deg : ℕ → ℤ := fun k ↦
        if hk : k < n then (if hki : (⟨k, hk⟩ : Fin n) ≠ i then d ⟨⟨k, hk⟩, hki⟩ else 0) else 0
      rw [op_m_apply 𝒜 deg _ fun j ↦ ?_, h.higher n hn _ ⟨i.rev, by simp⟩, smul_zero]
      by_cases hj : j = i
      · subst hj
        simpa [deg] using h.degree_zero
      · simpa [deg, hj] using hy ⟨j, hj⟩
    have hx : x = fun j ↦ if _ : j ≠ i then x j else e := by
      funext j
      by_cases hj : j = i
      · simp [hj, hi]
      · simp [hj]
    have := congrArg (fun f ↦ f fun j : {j // j ≠ i} ↦ x j) hf
    simp only [MultilinearMap.domDomRestrict_apply, zero_apply] at this
    rwa [← hx] at this

end AInfinityAlgebra

namespace IsDGAlgebra

-- The decomposition of a graded algebra on `G.piece` is the one of its `GradedAlgebra` structure,
-- under which `IsDGAlgebra.toIsNonUnitalDGAlgebra` is stated; disable the competing instance
-- attached to the internal grading `G`.
attribute [-instance] InternalGrading.instDecompositionIntSubmodulePiece

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A}

/-- **The opposite of the `A∞` algebra of a DG algebra is the `A∞` algebra of its graded
opposite.**  The passage `GradedOpposite.op` to the Koszul-signed graded opposite is a strict
morphism from the opposite of the `A∞` algebra of `h` to the `A∞` algebra of
`h.gradedOpposite`; its underlying map is the linear equivalence `GradedOpposite.opLinearEquiv`. -/
noncomputable def gradedOppositeStrictHom (h : IsDGAlgebra G.piece d) :
    AInfinityStrictHom h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.op
      h.gradedOpposite.toIsNonUnitalDGAlgebra.toAInfinityAlgebra where
  toLinearMap := (GradedOpposite.opLinearEquiv G).toLinearMap
  map_mem' {p a} ha := by
    rw [AInfinityAlgebra.op_grading, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
      InternalGrading.ofDecomposition_piece] at ha
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading, InternalGrading.ofDecomposition_piece,
      LinearEquiv.coe_coe, GradedOpposite.opLinearEquiv_apply]
    exact (GradedOpposite.op_mem_piece_iff G p a).2 ha
  map_m' n := by
    refine InternalGrading.multilinearMap_ext (fun _ : Fin n ↦ G) fun e x hx ↦ ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
    simp only [LinearEquiv.coe_coe, GradedOpposite.opLinearEquiv_apply]
    rcases n with _ | _ | _ | n
    · simp
    · rw [AInfinityAlgebra.op_m_one, IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply,
        IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, GradedOpposite.differential_op]
    · have hx₀ : x 0 ∈ h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.piece (e 0) := by
        simpa using hx 0
      have hx₁ : x 1 ∈ h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.piece (e 1) := by
        simpa using hx 1
      have hx' : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx', AInfinityAlgebra.op_m_two_apply _ hx₀ hx₁,
        IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply,
        IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [GradedOpposite.op_mul G (hx 0) (hx 1), GradedOpposite.op_smul G,
        negOnePow_smul_eq_negOnePowCast_smul (R := R)]
    · rw [(AInfinityAlgebra.op_m_eq_zero_iff _ _).2
        (IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_add_three _ n)]
      simp

/-- The strict morphism `gradedOppositeStrictHom` is passage to the graded opposite. -/
@[simp]
theorem gradedOppositeStrictHom_apply (h : IsDGAlgebra G.piece d) (a : A) :
    h.gradedOppositeStrictHom a = GradedOpposite.op G a := by
  rw [gradedOppositeStrictHom, AInfinityStrictHom.coe_mk, LinearEquiv.coe_coe,
    GradedOpposite.opLinearEquiv_apply]

/-- The strict morphism `gradedOppositeStrictHom` is bijective, so it is an isomorphism of `A∞`
algebras. -/
theorem gradedOppositeStrictHom_bijective (h : IsDGAlgebra G.piece d) :
    Function.Bijective h.gradedOppositeStrictHom :=
  (GradedOpposite.opLinearEquiv G).bijective

end IsDGAlgebra

end TauCeti
