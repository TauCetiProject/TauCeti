/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Basic

/-!
# Suspension signs for right A-infinity module operations

This file collects the two sign calculations shared by right `A∞` module identities and
module-morphism identities.  The first compares a composite of two suspended Taylor maps with
the corresponding composite of their unsuspended components.  The second compares a term in
which the algebra bar differential collapses a block with the corresponding unsuspended term.
Both rest on the expansions of a cofree lift and of the algebra bar differential over a pure word.

The component index is the number of algebra inputs; the distinguished module input comes first.
If the inner family in a composite has degree `q - n` on `n` algebra inputs, moving from the
suspended composite to the unsuspended one contributes `(-1) ^ ((k + q) * (n - k))` at a cut
after `k` algebra inputs.  The formulas are stated for arbitrary source, intermediate, and target
modules so that the same calculations apply both to module operations (`q = 1`) and to module
morphisms (`q = 0`).

## Main definitions

* `TauCeti.AInfinityRightModule.unsuspend`: the module-first unsuspension of a map on a fixed
  tensor length.

## Main results

* `TauCeti.AInfinityRightModule.apply_tmul_tprod_of_mem` and
  `TauCeti.AInfinityRightModule.unsuspend_mem_piece`: its suspension sign and degree.
* `TauCeti.AInfinityRightModule.apply_comp_subword_of_mem`: the suspension sign for a composite
  of module-first Taylor maps.
* `TauCeti.AInfinityRightModule.cofreeLift_tmul_of_tprod`: the cofree lift of a map, expanded
  over the cuts of a pure word.
* `TauCeti.AInfinityRightModule.apply_coaugmentedBarDifferential_of_tprod`: the algebra bar
  differential expanded after an arbitrary linear map on a module tensor factor.
* `TauCeti.AInfinityRightModule.apply_algebra_splice_of_mem`: the suspension sign when an algebra
  operation is inserted into the algebra inputs.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators TensorProduct
open _root_.MultilinearMap (evalNat evalNat_def suspExp suspExp_def suspExp_add)

namespace TauCeti
namespace AInfinityRightModule

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

open TensorWords

attribute [local instance] Comodule.cofree

/-! ### Module-first unsuspension -/

/-- The module-first unsuspension of a map `F : M ⊗ A^⊗n → N` between suspended inputs: it
evaluates `F` after twisting the input in position `j` (the module input being in position `0`)
by the Koszul twist of parameter `n - j`. -/
noncomputable def unsuspend (G : InternalGrading R M) (GA : InternalGrading R A) (n : ℕ)
    (F : M ⊗[R] TensorPower R n A →ₗ[R] N) : M →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) N :=
  { toFun x :=
      ((F ∘ₗ TensorProduct.mk R M (TensorPower R n A) (G.koszulTwist n x)
        ).compMultilinearMap (PiTensorProduct.tprod R)).compLinearMap
          fun i ↦ GA.koszulTwist ((n : ℤ) - 1 - i)
    map_add' x y := by
      ext a
      simp
    map_smul' r x := by
      ext a
      simp }

/-- The unsuspension evaluates the map on Koszul-twisted inputs. -/
theorem unsuspend_apply (G : InternalGrading R M) (GA : InternalGrading R A) (n : ℕ)
    (F : M ⊗[R] TensorPower R n A →ₗ[R] N) (x : M) (a : Fin n → A) :
    unsuspend G GA n F x a =
      F (G.koszulTwist n x ⊗ₜ[R]
        PiTensorProduct.tprod R fun i ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i)) :=
  (rfl)

/-- A map evaluates its unsuspension on Koszul-twisted inputs: the twists are involutions. -/
theorem apply_tmul_tprod_eq_unsuspend (G : InternalGrading R M) (GA : InternalGrading R A)
    (n : ℕ) (F : M ⊗[R] TensorPower R n A →ₗ[R] N) (x : M) (a : Fin n → A) :
    F (x ⊗ₜ[R] PiTensorProduct.tprod R a) =
      unsuspend G GA n F (G.koszulTwist n x)
        fun i : Fin n ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i) := by
  simp only [unsuspend_apply, InternalGrading.koszulTwist_koszulTwist]

/-- On homogeneous inputs, the Koszul twists of the module-first unsuspension multiply to the
Koszul sign of suspending the module input and all algebra inputs. -/
theorem apply_koszulTwist_of_mem (G : InternalGrading R M) (GA : InternalGrading R A) {n : ℕ}
    (φ : M →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) N) {x : M} {e : ℤ} (hx : x ∈ G.piece e)
    (d : ℕ → ℤ) (a : ℕ → A) (ha : ∀ i < n, a i ∈ GA.piece (d i)) :
    φ (G.koszulTwist n x) (fun i : Fin n ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i)) =
      negOnePowCast R (n * e + suspExp n d) • evalNat (φ x) a := by
  have htwist : (fun i : Fin n ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i)) =
      fun i : Fin n ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i) • a i := by
    funext i
    rw [GA.koszulTwist_apply_of_mem (ha i i.isLt), negOnePowCast_eq_intCast]
  rw [htwist, G.koszulTwist_apply_of_mem hx, ← negOnePowCast_eq_intCast, map_smul, smul_apply,
    MultilinearMap.map_smul_univ, smul_smul, evalNat_def, suspExp_def, negOnePowCast_add,
    negOnePowCast_sum,
    ← Fin.prod_univ_eq_prod_range (fun i ↦ negOnePowCast R (((n : ℤ) - 1 - i) * d i)) n]

/-- On homogeneous inputs, a map is its module-first unsuspension multiplied by the suspension
Koszul sign. -/
theorem apply_tmul_tprod_of_mem (G : InternalGrading R M) (GA : InternalGrading R A) (n : ℕ)
    (F : M ⊗[R] TensorPower R n A →ₗ[R] N) {x : M} {e : ℤ} (hx : x ∈ G.piece e)
    (d : ℕ → ℤ) (a : ℕ → A) (ha : ∀ i < n, a i ∈ GA.piece (d i)) :
    F (x ⊗ₜ[R] PiTensorProduct.tprod R fun i : Fin n ↦ a i) =
      negOnePowCast R (n * e + suspExp n d) • evalNat (unsuspend G GA n F x) a := by
  rw [apply_tmul_tprod_eq_unsuspend G GA, apply_koszulTwist_of_mem G GA _ hx d a ha]

/-- If a map of suspended inputs raises total suspended degree by `k`, its module-first
unsuspension has degree `k - 1 - n` on `n` algebra inputs. -/
theorem unsuspend_mem_piece (G : InternalGrading R M) (GA : InternalGrading R A)
    {GN : InternalGrading R N} (n : ℕ) {F : M ⊗[R] TensorPower R n A →ₗ[R] N} (k : ℤ)
    (hF : ∀ {x : M} {p : ℤ}, x ∈ (G.shift 1).piece p → ∀ (a : Fin n → A) (d : Fin n → ℤ),
      (∀ i, a i ∈ (GA.shift 1).piece (d i)) →
        F (x ⊗ₜ[R] PiTensorProduct.tprod R a) ∈ GN.piece (p + ∑ i, d i + k))
    {x : M} {e : ℤ} (hx : x ∈ G.piece e) (a : Fin n → A) (d : Fin n → ℤ)
    (ha : ∀ i, a i ∈ GA.piece (d i)) :
    unsuspend G GA n F x a ∈ GN.piece (e + ∑ i, d i - n + (k - 1)) := by
  have hx' : G.koszulTwist n x ∈ (G.shift 1).piece (e - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact G.koszulTwist_mem_piece hx _
  have ha' : ∀ i, GA.koszulTwist ((n : ℤ) - 1 - i) (a i) ∈ (GA.shift 1).piece (d i - 1) :=
    fun i ↦ by
      rw [InternalGrading.shift_piece, sub_add_cancel]
      exact GA.koszulTwist_mem_piece (ha i) _
  have h := hF hx' _ _ ha'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  -- The suspended inputs have total degree `(e - 1) + (∑ i, d i - n)`, which `F` raises by `k`.
  have hdeg : e + ∑ i, d i - n + (k - 1) = e - 1 + (∑ i, d i - n) + k := by ring
  rw [unsuspend_apply, hdeg]
  exact h

/-! ### Bar-word expansions, composites, and algebra insertions -/

/-- A composite of suspended module-first Taylor maps on homogeneous inputs, expressed through
their unsuspended components.  The inner components have degree `q - k` on `k` algebra inputs;
the outer degree is irrelevant to the suspension sign. -/
theorem apply_comp_subword_of_mem
    {GA : InternalGrading R A} {GM : InternalGrading R M} {GN : InternalGrading R N}
    {F : (M ⊗[R] TensorWords R A) →ₗ[R] N}
    {H : (N ⊗[R] TensorWords R A) →ₗ[R] P}
    {f : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) N}
    {h : (n : ℕ) → N →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) P}
    {q : ℤ}
    (hFf : ∀ (n : ℕ) (x : M) (a : Fin n → A),
      F (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
        f n (GM.koszulTwist n x)
          fun i : Fin n ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i))
    (hf : ∀ (n : ℕ) {x : M} {p : ℤ}, x ∈ GM.piece p → ∀ (a : Fin n → A) (d : Fin n → ℤ),
      (∀ i, a i ∈ GA.piece (d i)) → f n x a ∈ GN.piece (p + ∑ i, d i + (q - n)))
    (hHh : ∀ (n : ℕ) (x : N) (a : Fin n → A),
      H (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
        h n (GN.koszulTwist n x)
          fun i : Fin n ↦ GA.koszulTwist ((n : ℤ) - 1 - i) (a i))
    {n k : ℕ} (hk : k ≤ n) {x : M} {e : ℤ} (hx : x ∈ GM.piece e)
    (d : ℕ → ℤ) (a : ℕ → A) (ha : ∀ i < n, a i ∈ GA.piece (d i)) :
    H (F (x ⊗ₜ[R] subword R (fun i : Fin n ↦ a i) 0 k) ⊗ₜ[R]
        subword R (fun i : Fin n ↦ a i) k (n - k)) =
      negOnePowCast R (n * e + suspExp n d) •
        negOnePowCast R (((k : ℤ) + q) * ((n : ℤ) - k)) •
          evalNat (h (n - k) (evalNat (f k x) a)) fun j ↦ a (k + j) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, subword_eq_of_tprod R _ (by omega),
    subword_eq_of_tprod R _ le_rfl]
  simp only [Nat.zero_add]
  rw [hFf]
  rw [apply_koszulTwist_of_mem GM GA (f k) hx d a fun i hi ↦ ha i (by omega)]
  have hy : evalNat (f k x) a ∈
      GN.piece (e + ∑ i ∈ Finset.range k, d i + (q - k)) := by
    rw [evalNat_def, ← Fin.sum_univ_eq_sum_range]
    exact hf k hx _ (fun i : Fin k ↦ d i) fun i ↦ ha i (by omega)
  rw [← TensorProduct.smul_tmul', map_smul, hHh,
    apply_koszulTwist_of_mem GN GA (h t) hy (fun j ↦ d (k + j))
      (fun j ↦ a (k + j)) fun j hj ↦ ha _ (by omega)]
  -- The two collected suspension signs differ from the target sign by an even exponent.  Writing
  -- `n = k + t`, `suspExp_add` splits `suspExp n d` into the prefix and suffix exponents plus
  -- `t * ∑ i < k, d i`; the latter is the degree of the intermediate output that the outer twist
  -- collects, leaving `t * (q - k)` against the target `(k + q) * t`, a difference of `2 * k * t`.
  simp only [smul_smul, ← negOnePowCast_add]
  congr 1
  have hsum : ∑ i ∈ Finset.range k, ((k : ℤ) + t - 1 - i) * d i =
      suspExp k d + t * ∑ i ∈ Finset.range k, d i := by
    rw [suspExp_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [negOnePowCast_eq_intCast, negOnePowCast_eq_intCast,
    (Int.negOnePow_eq_iff _ _).2 ⟨-((k : ℤ) * t), ?_⟩]
  rw [suspExp_add, hsum, suspExp_def t]
  push_cast
  ring

/-- On a pure word, the cofree lift of `F` applies `F` to every prefix and retains the
corresponding suffix. -/
theorem cofreeLift_tmul_of_tprod (F : (M ⊗[R] TensorWords R A) →ₗ[R] N) (n : ℕ) (x : M)
    (a : Fin n → A) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap
        (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
      ∑ k ∈ Finset.range (n + 1), F (x ⊗ₜ[R] subword R a 0 k) ⊗ₜ[R] subword R a k (n - k) := by
  rw [Comodule.Hom.cofreeLift_toLinearMap, LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    comul_eq_deconcatenation, of_tprod_eq_subword, deconcatenation_subword]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, Nat.zero_add]

/-- Applying a linear map after tensoring a module element with the algebra bar differential
expands as the sum over all nonempty blocks collapsed by the algebra Taylor map. -/
theorem apply_coaugmentedBarDifferential_of_tprod
    (F : (M ⊗[R] TensorWords R A) →ₗ[R] N) (n : ℕ) (x : M) (a : Fin n → A) :
    F (x ⊗ₜ[R]
        AA.coaugmentedBarDifferential (TensorWords.of R A n (PiTensorProduct.tprod R a))) =
      ∑ p ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 (n - p),
        F (x ⊗ₜ[R] reducedInclusion R A (ReducedTensorWords.splice R
          (InternalGrading.twistedTuple (AA.grading.shift 1) 1 a 0 p) 0 n p s
            (AA.taylor (ReducedTensorWords.subword R a p s)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hone : TensorWords.of R A 0 (PiTensorProduct.tprod R a) = 1 := by
      rw [one_eq_of_zero]
      exact of_tprod_congr R A fun j ↦ j.elim0
    rw [hone, AA.coaugmentedBarDifferential_one, TensorProduct.tmul_zero, map_zero,
      Finset.sum_range_zero]
  · rw [← reducedInclusion_of (R := R) (M := A) ⟨n, hn⟩, ← LinearMap.comp_apply,
      AInfinityAlgebra.coaugmentedBarDifferential_comp_reducedInclusion,
      LinearMap.comp_apply, AInfinityAlgebra.barDifferential_def,
      ReducedTensorWords.gradedCoderiv_of_tprod]
    simp only [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ (Finset.sum_subset (fun s hs ↦ ?_) ?_).symm
    · rw [Finset.mem_Icc] at hs
      rw [Finset.mem_range]
      omega
    · intro s _ hs
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · rw [Nat.lt_one_iff.1 hs, ReducedTensorWords.splice_zero_length, map_zero,
          TensorProduct.tmul_zero, map_zero]
      · rw [ReducedTensorWords.splice_eq_zero_of_block_lt_add R _ _ (by omega), map_zero,
          TensorProduct.tmul_zero, map_zero]

/-- A suspended term in which the algebra bar differential collapses a block of homogeneous
algebra inputs, expressed through the unsuspended module-first component and algebra operation. -/
theorem apply_algebra_splice_of_mem
    {G : InternalGrading R M}
    {F : (M ⊗[R] TensorWords R A) →ₗ[R] N}
    {f : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n ↦ A) N}
    (hFf : ∀ (n : ℕ) (x : M) (a : Fin n → A),
      F (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
        f n (G.koszulTwist n x)
          fun i : Fin n ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (a i))
    {n p s : ℕ} (hs : 0 < s) (hps : p + s ≤ n) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (d : ℕ → ℤ) (a : ℕ → A)
    (ha : ∀ i < n, a i ∈ AA.grading.piece (d i)) :
    F ((G.shift 1).koszulTwist 1 x ⊗ₜ[R]
        reducedInclusion R A (ReducedTensorWords.splice R
          (InternalGrading.twistedTuple (AA.grading.shift 1) 1 (fun i : Fin n ↦ a i) 0 p)
            0 n p s (AA.taylor (ReducedTensorWords.subword R (fun i : Fin n ↦ a i) p s)))) =
      negOnePowCast R (n * e + suspExp n d) •
        negOnePowCast R ((p : ℤ) + 1 + s * ((n : ℤ) - p - s) +
            (2 - s) * (e + ∑ i ∈ Finset.range p, d i)) •
          evalNat (f (p + 1 + (n - p - s)) x)
            (replaceBlock a p s (evalNat (AA.m s) fun j ↦ a (p + j))) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = p + s + t := ⟨n - p - s, by omega⟩
  have ht : p + s + t - p - s = t := by omega
  -- Pull the Koszul twists of the `p` letters before the block out of the splice as one sign.
  rw [ht, ReducedTensorWords.splice_twistedTuple_smul (AA.grading.shift 1) 1 _
    (fun i ↦ d i - 1) fun i ↦ by
      rw [InternalGrading.shift_piece, sub_add_cancel]
      exact ha i i.isLt]
  have hinner : AA.taylor (ReducedTensorWords.subword R (fun i : Fin (p + s + t) ↦ a i) p s) =
      negOnePowCast R (suspExp s fun j ↦ d (p + j)) •
        evalNat (AA.m s) fun j ↦ a (p + j) := by
    rw [ReducedTensorWords.subword_eq_of_tprod R _ hs (by omega), ← AInfinity.evalNat_suspend]
    exact (AInfinity.isSuspension_def _ _ _).1 AA.taylor_isSuspension s hs _ _
      fun i hi ↦ ha (p + i) (by omega)
  -- The suspended algebra operation on the block is its unsuspended operation up to a sign.
  rw [hinner]
  set v := evalNat (AA.m s) fun j ↦ a (p + j)
  set c := negOnePowCast R (suspExp s fun j ↦ d (p + j))
  -- The spliced word is the pure word in which the block is replaced by its collapse.
  have hsplice : ReducedTensorWords.splice R (fun i : Fin (p + s + t) ↦ a i) 0
      (p + s + t) p s (c • v) = ReducedTensorWords.of R A ⟨p + 1 + t, by omega⟩
        (PiTensorProduct.tprod R
          fun i : Fin (p + 1 + t) ↦ replaceBlock a p s (c • v) i) := by
    rw [ReducedTensorWords.splice_eq_of_tprod R _ _ hs (by omega) (by omega)]
    apply ReducedTensorWords.of_tprod_congr R A (by omega) (by omega)
    intro i
    simp only [Fin.val_cast, Nat.zero_add]
    split_ifs with hip hi
    · exact (replaceBlock_of_lt a p s _ hip).symm
    · rw [hi, replaceBlock_self]
    · exact (replaceBlock_of_gt a p s _ (by omega)).symm
  have hcv : c • v ∈ AA.grading.piece (AInfinity.blockDeg d p s) :=
    Submodule.smul_mem _ _ (AInfinity.evalNat_mem_blockDeg AA.grading.piece (AA.m s)
      (AA.m_degree s hs) p fun j hj ↦ ha _ (by omega))
  have hx' : x ∈ (G.shift 1).piece (e - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact hx
  -- Unsuspend the module-first component on the spliced word, whose block has degree
  -- `blockDeg d p s`, and collect the scalar of the collapsed block.
  rw [hsplice, map_smul, reducedInclusion_of, TensorProduct.tmul_smul, map_smul,
    InternalGrading.koszulTwist_apply_of_mem _ hx', ← TensorProduct.smul_tmul', map_smul,
    hFf, apply_koszulTwist_of_mem G AA.grading (f (p + 1 + t)) hx
      (AInfinity.replaceDeg d p s) _
      fun i hi ↦ AInfinity.replaceBlock_mem_replaceDeg_of_mem_blockDeg AA.grading.piece ha hcv
        (by omega) (by omega), evalNat_replaceBlock_smul _ _ _ (by omega)]
  have hpre : (1 : ℤ) * ∑ j ∈ Finset.range p,
      (if h : j < p + s + t then (fun i : Fin (p + s + t) ↦ d i - 1) ⟨j, h⟩ else 0) =
        ∑ i ∈ Finset.range p, (d i - 1) := by
    rw [one_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjn : j < p + s + t := by
      have := Finset.mem_range.mp hj
      omega
    simp only [hjn, dite_true]
  rw [hpre, ← negOnePowCast_eq_intCast, ← negOnePowCast_eq_intCast]
  -- The collected signs differ from the target sign by an even exponent, by the suspension sign
  -- identity `AInfinity.suspExp_replaceDeg` for the algebra inputs.
  simp only [c, smul_smul, ← negOnePowCast_add]
  congr 1
  rw [negOnePowCast_eq_intCast, negOnePowCast_eq_intCast,
    (Int.negOnePow_eq_iff _ _).2 ⟨(t : ℤ) - p - s * t - 1, ?_⟩]
  rw [AInfinity.suspExp_replaceDeg]
  push_cast
  ring

end AInfinityRightModule
end TauCeti
