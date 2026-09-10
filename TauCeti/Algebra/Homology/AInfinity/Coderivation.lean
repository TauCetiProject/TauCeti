/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import TauCeti.Algebra.Homology.AInfinity.Stasheff
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.LinearAlgebra.TensorCoalgebra.OddSquare
public import TauCeti.LinearAlgebra.TensorCoalgebra.TaylorComponent

/-!
# Stasheff identities from a bar coderivation

This file identifies the Stasheff identities with the Taylor components of the square of the
corresponding degree-one coderivation of the reduced tensor coalgebra.  The predicate
`TauCeti.AInfinity.IsSuspension` records the commuting suspension square on homogeneous pure
tensors.  If `F` is the resulting Taylor map and
`b = ReducedTensorWords.gradedCoderiv (G.shift 1) F 1`, then the arity-`n` Taylor component of
`b ∘ b` is exactly the suspended Stasheff sum.  Consequently `b ∘ b = 0` is equivalent to
all unsuspended Stasheff identities.

The arities one through four are also stated explicitly.  Together they pin the cohomological
Getzler--Jones/Keller convention: the Leibniz sign in arity two is `(-1)^|a|`, arity three has
ordinary associativity when the higher operations vanish, and arity four is then zero.

## Main results

* `TauCeti.AInfinity.IsSuspension`: compatibility between a Taylor map and unsuspended operations
  on homogeneous tensors.
* `TauCeti.AInfinity.IsSuspension.taylorComponent_comp_self_apply`: the arity component of the
  coderivation square is the suspended Stasheff sum.
* `TauCeti.AInfinity.IsSuspension.comp_self_eq_zero_iff_stasheff`: a degree-one bar coderivation
  squares to zero exactly when all Stasheff identities hold on homogeneous inputs.
* `TauCeti.AInfinity.IsSuspension.taylorComponent_comp_self_one` through
  `taylorComponent_comp_self_four`: the first four component formulas verbatim.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct
open _root_.MultilinearMap

universe uR uA

namespace TauCeti

namespace AInfinity

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A Taylor map `F : Tᶜ(A) ⟶ A` is the suspension of operations `mₙ` when, on every
homogeneous pure tensor, it is obtained from `mₙ` by the Koszul sign of the tensor power of the
degree-`-1` suspension.  The grading is the unsuspended grading; the associated coderivation is
built using `G.shift 1`.

The relation is required only on homogeneous inputs.  Requiring it on arbitrary inputs with an
arbitrarily supplied degree family would be inconsistent, since the suspension sign depends on
those degrees. -/
def IsSuspension (G : InternalGrading R A) (F : ReducedTensorWords R A →ₗ[R] A)
    (m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A),
    (∀ i < n, x i ∈ G.piece (d i)) →
      F (ReducedTensorWords.of R A ⟨n, hn⟩
          (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
        evalNat (MultilinearMap.suspend d (m n)) x

/-- The defining condition for a Taylor map to be the suspension of a family of operations. -/
theorem isSuspension_def (G : InternalGrading R A) (F : ReducedTensorWords R A →ₗ[R] A)
    (m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A) :
    IsSuspension G F m ↔
      ∀ (n : ℕ) (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A),
        (∀ i < n, x i ∈ G.piece (d i)) →
          F (ReducedTensorWords.of R A ⟨n, hn⟩
              (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
            evalNat (MultilinearMap.suspend d (m n)) x :=
  Iff.rfl

/-- Evaluate a suspended Taylor map on a homogeneous pure tensor. -/
theorem IsSuspension.apply {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m) (n : ℕ) (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    F (ReducedTensorWords.of R A ⟨n, hn⟩
        (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
      evalNat (MultilinearMap.suspend d (m n)) x :=
  (isSuspension_def G F m).1 hFm n hn d x hx

/-- A Taylor map related by suspension to operations of degree `2 - n` has degree one from tensor
words in the suspended grading to suspended letters.  This is the homogeneity input that makes the
square of its bar coderivation an ordinary coderivation. -/
theorem IsSuspension.isHomogeneous {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n)) :
    LinearMap.IsHomogeneous F (ReducedTensorWords.gradedPiece (G.shift 1))
      (G.shift 1).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine ReducedTensorWords.gradedPiece_induction
    (motive := fun w ↦ F w ∈ (G.shift 1).piece (D + 1)) hz ?_ ?_ ?_ ?_
  · intro n hn e x hx hD
    let d : ℕ → ℤ := fun i ↦ if h : i < n then e ⟨i, h⟩ + 1 else 0
    let y : ℕ → A := fun i ↦ if h : i < n then x ⟨i, h⟩ else 0
    have hy : ∀ i < n, y i ∈ G.piece (d i) := by
      intro i hi
      simp only [y, d, hi, dite_true]
      simpa only [InternalGrading.shift_piece] using hx ⟨i, hi⟩
    have hyx : (fun i : Fin n ↦ y i) = x := by
      funext i
      simp only [y, i.isLt, dite_true]
    rw [← hyx]
    rw [hFm.apply n hn d y hy, evalNat_suspend]
    apply Submodule.smul_mem
    have hop := (hm n hn).map_mem (fun i : Fin n ↦ d i) (fun i : Fin n ↦ y i)
      (fun i ↦ hy i i.isLt)
    have hsum : (∑ i : Fin n, d i) = D + n := by
      simp only [d, Fin.isLt, dite_true, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hD, mul_one]
    rw [hsum] at hop
    rw [InternalGrading.shift_piece]
    have hdeg : D + 1 + 1 = (D + (n : ℤ)) + (2 - (n : ℤ)) := by ring
    rw [hdeg]
    simpa only [evalNat_def] using hop
  · rw [_root_.map_zero]
    exact Submodule.zero_mem _
  · intro u v _hu _hv ihu ihv
    rw [map_add]
    exact Submodule.add_mem _ ihu ihv
  · intro a u _hu ihu
    rw [map_smul]
    exact Submodule.smul_mem _ _ ihu

/-- The arity-`n` Taylor component of the square of the suspended bar coderivation is the
suspended Stasheff sum.  The input elements are recorded with their unsuspended degrees `d`; they
therefore have degrees `d i - 1` for the shifted grading used by the coderivation. -/
theorem IsSuspension.taylorComponent_comp_self_apply {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨n, hn⟩
        (PiTensorProduct.tprod R fun i : Fin n ↦ x i) =
      suspendedStasheffSum m d x n := by
  rw [ReducedTensorWords.taylorComponent_comp_gradedCoderiv_of_tprod_of_homogeneous
    (G.shift 1) (ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) F 1 hn
    (fun i : Fin n ↦ x i) (fun i : Fin n ↦ d i - 1)]
  · rw [suspendedStasheffSum_def, Finset.sum_range_succ]
    have hnot : ¬1 ≤ 0 := by omega
    simp only [Nat.sub_self, Finset.Icc_eq_empty hnot, Finset.sum_empty,
      add_zero]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc] at hs
    have hps : p + s ≤ n := by omega
    have hspos : 0 < s := hs.1
    -- The inner Taylor component is the suspended operation on the collapsed block.
    have hinner : F (ReducedTensorWords.subword R (fun i : Fin n ↦ x i) p s) =
        evalNat (MultilinearMap.suspend (fun j ↦ d (p + j)) (m s))
          (fun j ↦ x (p + j)) := by
      rw [ReducedTensorWords.subword_eq_of_tprod R _ hspos hps]
      exact hFm.apply s hspos (fun j ↦ d (p + j)) (fun j ↦ x (p + j))
        (fun i hi ↦ hx (p + i) (by omega))
    let e := evalNat (MultilinearMap.suspend (fun j ↦ d (p + j)) (m s))
      (fun j ↦ x (p + j))
    have he : e ∈ G.piece (blockDeg d p s) := by
      simp only [e, evalNat_suspend]
      exact Submodule.smul_mem _ _
        (evalNat_mem_blockDeg G.piece (m s) (hm s hspos) p (fun j hj ↦ hx (p + j) (by omega)))
    have hreplace : ∀ i < p + 1 + (n - p - s),
        replaceBlock x p s e i ∈ G.piece (replaceDeg d p s i) := by
      intro i hi
      rcases lt_trichotomy i p with hip | rfl | hip
      · rw [replaceBlock_of_lt _ _ _ _ hip, replaceDeg_of_lt _ _ _ hip]
        exact hx i (by omega)
      · rw [replaceBlock_self, replaceDeg_self]
        exact he
      · rw [replaceBlock_of_gt _ _ _ _ hip, replaceDeg_of_gt _ _ _ hip]
        exact hx _ (by omega)
    -- Present the spliced word as the pure tensor to which the outer suspension relation applies.
    have hsplice : ReducedTensorWords.splice R (fun i : Fin n ↦ x i) 0 n p s e =
        ReducedTensorWords.of R A ⟨p + 1 + (n - p - s), by omega⟩
          (PiTensorProduct.tprod R fun i : Fin (p + 1 + (n - p - s)) ↦
            replaceBlock x p s e i) := by
      rw [ReducedTensorWords.splice_eq_of_tprod R _ e hspos hps (by omega)]
      apply ReducedTensorWords.of_tprod_congr R A (by omega) (by omega)
      intro i
      simp only [Fin.val_cast, Nat.zero_add]
      split_ifs with hip hi
      · exact (replaceBlock_of_lt x p s e hip).symm
      · rw [hi, replaceBlock_self]
      · exact (replaceBlock_of_gt x p s e (by omega)).symm
    rw [ReducedTensorWords.letter_comp_gradedCoderiv, hinner]
    -- `e` names the suspended inner operation so the splice lemma can be reused without
    -- exposing the implementation of tensor words.
    change _ • F (ReducedTensorWords.splice R (fun i : Fin n ↦ x i) 0 n p s e) = _
    rw [suspendedStasheffTerm_def, hsplice]
    rw [hFm.apply (p + 1 + (n - p - s)) (by omega) (replaceDeg d p s)
      (replaceBlock x p s e) hreplace]
    simp only [e]
    congr 1
    rw [negOnePowCast_eq_intCast]
    congr 2
    simp only [one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := (Finset.mem_range.mp hj).trans hp
    simp only [hjn, dite_true]
  · intro i
    have hi := hx i i.isLt
    rw [InternalGrading.shift_piece]
    simpa only [sub_add_cancel] using hi

/-- The arity component of the bar-coderivation square is the unsuspended Stasheff sum multiplied
by the single suspension sign of the whole input tuple. -/
theorem IsSuspension.taylorComponent_comp_self_eq_smul_stasheff {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨n, hn⟩
        (PiTensorProduct.tprod R fun i : Fin n ↦ x i) =
      negOnePowCast R (suspExp n d) • stasheffSum m d x n := by
  rw [hFm.taylorComponent_comp_self_apply hm hn d x hx,
    suspendedStasheffSum_eq_smul]

/-- On homogeneous inputs, an arity component of the bar-coderivation square vanishes exactly
when the corresponding unsuspended Stasheff sum vanishes. -/
theorem IsSuspension.taylorComponent_comp_self_eq_zero_iff {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨n, hn⟩
        (PiTensorProduct.tprod R fun i : Fin n ↦ x i) = 0 ↔
      stasheffSum m d x n = 0 := by
  rw [hFm.taylorComponent_comp_self_apply hm hn d x hx,
    suspendedStasheffSum_eq_zero_iff]

/-! ### The first four components -/

/-- The arity-one component of `b ∘ b` vanishes exactly when `m₁ m₁ = 0`. -/
theorem IsSuspension.taylorComponent_comp_self_one {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    (d : ℕ → ℤ) (x : ℕ → A) (hx : x 0 ∈ G.piece (d 0)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨1, by omega⟩
        (PiTensorProduct.tprod R fun i : Fin 1 ↦ x i) = 0 ↔
      m 1 ![m 1 ![x 0]] = 0 := by
  rw [hFm.taylorComponent_comp_self_eq_zero_iff hm (by omega) d x
    (fun i hi ↦ by
      have hi0 : i = 0 := by omega
      subst i
      exact hx),
    stasheffSum_one]

/-- The arity-two component of `b ∘ b` is zero exactly when `m₁` obeys the graded Leibniz
rule for `m₂`, with sign `(-1)^(d 0)` on the second differentiated input. -/
theorem IsSuspension.taylorComponent_comp_self_two {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    (d : ℕ → ℤ) (x : ℕ → A) (hx : ∀ i < 2, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨2, by omega⟩
        (PiTensorProduct.tprod R fun i : Fin 2 ↦ x i) = 0 ↔
      m 1 ![m 2 ![x 0, x 1]] =
        m 2 ![m 1 ![x 0], x 1] + negOnePowCast R (d 0) • m 2 ![x 0, m 1 ![x 1]] := by
  rw [hFm.taylorComponent_comp_self_eq_zero_iff hm (by omega) d x hx,
    stasheffSum_two_eq_zero_iff]

/-- The arity-three component of `b ∘ b` is zero exactly when the displayed arity-three
Stasheff expression vanishes, including the two degree-dependent Koszul factors. -/
theorem IsSuspension.taylorComponent_comp_self_three {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    (d : ℕ → ℤ) (x : ℕ → A) (hx : ∀ i < 3, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨3, by omega⟩
        (PiTensorProduct.tprod R fun i : Fin 3 ↦ x i) = 0 ↔
      m 1 ![m 3 ![x 0, x 1, x 2]]
        + m 2 ![m 2 ![x 0, x 1], x 2] - m 2 ![x 0, m 2 ![x 1, x 2]]
        + m 3 ![m 1 ![x 0], x 1, x 2]
        + negOnePowCast R (d 0) • m 3 ![x 0, m 1 ![x 1], x 2]
        + negOnePowCast R (d 0 + d 1) • m 3 ![x 0, x 1, m 1 ![x 2]] = 0 := by
  rw [hFm.taylorComponent_comp_self_eq_zero_iff hm (by omega) d x hx,
    stasheffSum_three]

/-- The arity-four component of `b ∘ b` is zero exactly when the displayed arity-four
Stasheff expression vanishes, with all four unary-insertion signs explicit. -/
theorem IsSuspension.taylorComponent_comp_self_four {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n))
    (d : ℕ → ℤ) (x : ℕ → A) (hx : ∀ i < 4, x i ∈ G.piece (d i)) :
    ((ReducedTensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1).taylorComponent ⟨4, by omega⟩
        (PiTensorProduct.tprod R fun i : Fin 4 ↦ x i) = 0 ↔
      m 1 ![m 4 ![x 0, x 1, x 2, x 3]]
        - m 2 ![m 3 ![x 0, x 1, x 2], x 3]
        - negOnePowCast R (d 0) • m 2 ![x 0, m 3 ![x 1, x 2, x 3]]
        + m 3 ![m 2 ![x 0, x 1], x 2, x 3] - m 3 ![x 0, m 2 ![x 1, x 2], x 3]
        + m 3 ![x 0, x 1, m 2 ![x 2, x 3]]
        - m 4 ![m 1 ![x 0], x 1, x 2, x 3]
        - negOnePowCast R (d 0) • m 4 ![x 0, m 1 ![x 1], x 2, x 3]
        - negOnePowCast R (d 0 + d 1) • m 4 ![x 0, x 1, m 1 ![x 2], x 3]
        - negOnePowCast R (d 0 + d 1 + d 2) • m 4 ![x 0, x 1, x 2, m 1 ![x 3]] = 0 := by
  rw [hFm.taylorComponent_comp_self_eq_zero_iff hm (by omega) d x hx,
    stasheffSum_four]

/-- The suspended bar coderivation squares to zero exactly when the unsuspended operations obey
every Stasheff identity on homogeneous inputs.  Since an internal grading decomposes every
element into a finite sum of homogeneous elements, testing those inputs detects the whole linear
map `b ∘ b`, not merely its restriction to homogeneous words. -/
theorem IsSuspension.comp_self_eq_zero_iff_stasheff {G : InternalGrading R A}
    {F : ReducedTensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A}
    (hFm : IsSuspension G F m)
    (hm : ∀ n, 0 < n → MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n)) :
    ReducedTensorWords.gradedCoderiv (G.shift 1) F 1 ∘ₗ
        ReducedTensorWords.gradedCoderiv (G.shift 1) F 1 = 0 ↔
      ∀ (n : ℕ) (_hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A),
        (∀ i < n, x i ∈ G.piece (d i)) → stasheffSum m d x n = 0 := by
  let b := ReducedTensorWords.gradedCoderiv (G.shift 1) F 1
  have hb : ReducedTensorWords.IsGradedCoderivation (G.shift 1) 1 b :=
    ReducedTensorWords.isGradedCoderivation_gradedCoderiv (G.shift 1) F 1
  have hbHom : LinearMap.IsHomogeneous b (ReducedTensorWords.gradedPiece (G.shift 1))
      (ReducedTensorWords.gradedPiece (G.shift 1)) 1 :=
    ReducedTensorWords.isHomogeneous_gradedCoderiv (G.shift 1) F 1 1
      (hFm.isHomogeneous hm)
  have hbSquare : ReducedTensorWords.IsCoderivation R (b ∘ₗ b) :=
    hb.isCoderivation_comp_self_of_isHomogeneous_one hbHom
  constructor
  · intro hzero n hn d x hx
    have hcomponent := hFm.taylorComponent_comp_self_apply hm hn d x hx
    -- Unfold only the local abbreviation, leaving the coderivation implementation opaque.
    change b ∘ₗ b = 0 at hzero
    rw [hzero] at hcomponent
    simp only [LinearMap.taylorComponent_zero, LinearMap.zero_apply] at hcomponent
    exact (suspendedStasheffSum_eq_zero_iff m d x n).1 hcomponent.symm
  · intro hstasheff
    -- Unfold only the local abbreviation before applying the coderivation Taylor criterion.
    change b ∘ₗ b = 0
    rw [hbSquare.eq_zero_iff_taylorComponent_eq_zero]
    intro n
    apply PiTensorProduct.ext_of_span_eq_top
      (g := fun _ (q : Σ d : ℤ, G.piece d) ↦ (q.2 : A))
    · intro i
      apply top_unique
      rw [← G.isInternal.submodule_iSup_eq_top]
      refine iSup_le fun d ↦ ?_
      intro a ha
      exact Submodule.subset_span ⟨⟨d, ⟨a, ha⟩⟩, rfl⟩
    · intro q
      let d : ℕ → ℤ := fun i ↦ if h : i < n.1 then (q ⟨i, h⟩).1 else 0
      let x : ℕ → A := fun i ↦ if h : i < n.1 then (q ⟨i, h⟩).2 else 0
      have hx : ∀ i < n.1, x i ∈ G.piece (d i) := by
        intro i hi
        simp only [x, d, hi, dite_true]
        exact (q ⟨i, hi⟩).2.property
      have hcomponent := hFm.taylorComponent_comp_self_apply hm n.2 d x hx
      have hsuspended : suspendedStasheffSum m d x n.1 = 0 :=
        (suspendedStasheffSum_eq_zero_iff m d x n.1).2
          (hstasheff n.1 n.2 d x hx)
      rw [hsuspended] at hcomponent
      simpa only [b, LinearMap.zero_apply, x, Fin.isLt, dite_true] using hcomponent

end AInfinity

end TauCeti
