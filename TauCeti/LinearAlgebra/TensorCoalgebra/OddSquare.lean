/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Odd squares of homogeneous tensor-coalgebra coderivations

A degree-one coderivation of the reduced tensor coalgebra is odd: it anticommutes with the
letterwise Koszul involution. Consequently its square is an ordinary coderivation, whose
vanishing can then be checked with the existing Taylor-component criterion.

The total-degree pieces `TauCeti.ReducedTensorWords.gradedPiece` were originally introduced only
to state homogeneity of a graded Taylor expansion. This file proves that they span all reduced
tensor words and that the letterwise Koszul twist acts on the degree-`D` piece by
`(-1)^(q * D)`. These two facts turn the usual calculation on a homogeneous word into an equality
of endomorphisms, with no extra oddness assumption.

## Main results

* `TauCeti.ReducedTensorWords.iSup_gradedPiece_eq_top`: the total-degree pieces span the reduced
  tensor coalgebra.
* `TauCeti.ReducedTensorWords.map_koszulTwist_apply_of_mem`: the letterwise twist has the expected
  scalar action on each total-degree piece.
* `TauCeti.LinearMap.IsHomogeneous.anticommute_map_koszulTwist_one`: a degree-one endomorphism of
  reduced tensor words anticommutes with the letterwise Koszul involution.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.isCoderivation_comp_self_of_isHomogeneous`:
  the square of a homogeneous degree-one graded coderivation is an ordinary coderivation.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

private theorem negOnePow_sum_range (q : ℤ) (degree : ℕ → ℤ) (n : ℕ) :
    (((q * ∑ i ∈ Finset.range n, degree i).negOnePow : ℤ) : R) =
      ∏ i ∈ Finset.range n, (((q * degree i).negOnePow : ℤ) : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, mul_add, Int.negOnePow_add,
        Units.val_mul, Int.cast_mul, ih]

/-- The total-degree pieces span the reduced tensor coalgebra. In particular, an equality of
linear maps out of reduced tensor words may be checked separately on these pieces. -/
theorem iSup_gradedPiece_eq_top (G : InternalGrading R M) :
    ⨆ D : ℤ, gradedPiece G D = ⊤ := by
  classical
  apply le_antisymm le_top
  rw [← iSup_range_of R M]
  refine iSup_le fun n ↦ ?_
  rintro z ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul]
      apply Submodule.smul_mem
      let support : Fin n.1 → Finset ℤ := fun i ↦ (DirectSum.decompose G.piece (x i)).support
      let component : (i : Fin n.1) → ℤ → M :=
        fun i p ↦ DirectSum.decompose G.piece (x i) p
      have hx (i : Fin n.1) : ∑ p ∈ support i, component i p = x i := by
        exact DirectSum.sum_support_decompose G.piece (x i)
      have htuple :
          PiTensorProduct.tprod R x =
            ∑ degree ∈ Fintype.piFinset support,
              PiTensorProduct.tprod R (fun i ↦ component i (degree i)) := by
        rw [← (PiTensorProduct.tprod R).map_sum_finset]
        congr 1
        funext i
        exact (hx i).symm
      rw [htuple, map_sum]
      refine Submodule.sum_mem _ fun degree _hdegree ↦ ?_
      refine Submodule.mem_iSup_of_mem (∑ i, degree i) ?_
      apply mem_gradedPiece_of_tprod G n.2
      intro i
      exact (DirectSum.decompose G.piece (x i) (degree i)).property
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- On the total-degree-`D` piece of reduced tensor words, applying the Koszul twist to every
letter is scalar multiplication by `(-1)^(q * D)`. -/
theorem map_koszulTwist_apply_of_mem (G : InternalGrading R M) {D : ℤ}
    {z : ReducedTensorWords R M} (hz : z ∈ gradedPiece G D) (q : ℤ) :
    ReducedTensorWords.map (R := R) (G.koszulTwist q) z =
      (((q * D).negOnePow : ℤ) : R) • z := by
  refine gradedPiece_induction
    (motive := fun z ↦ ReducedTensorWords.map (R := R) (G.koszulTwist q) z =
      (((q * D).negOnePow : ℤ) : R) • z) hz ?_ (by simp) ?_ ?_
  · intro n hn degree x hx hD
    rw [map_of_tprod]
    have htuple : (fun i ↦ G.koszulTwist q (x i)) =
        fun i ↦ ((((q * degree i).negOnePow : ℤ) : R) • x i) := by
      funext i
      exact G.koszulTwist_apply_of_mem (hx i) q
    have hsign :
        (((q * ∑ i, degree i).negOnePow : ℤ) : R) =
          ∏ i, (((q * degree i).negOnePow : ℤ) : R) := by
      rw [Finset.sum_fin_eq_sum_range, Finset.prod_fin_eq_prod_range]
      calc
        (((q * ∑ i ∈ Finset.range n,
            if h : i < n then degree ⟨i, h⟩ else 0).negOnePow : ℤ) : R) =
            ∏ i ∈ Finset.range n,
              (((q * (if h : i < n then degree ⟨i, h⟩ else 0)).negOnePow : ℤ) : R) :=
          negOnePow_sum_range q (fun i ↦ if h : i < n then degree ⟨i, h⟩ else 0) n
        _ = ∏ i ∈ Finset.range n,
            if h : i < n then (((q * degree ⟨i, h⟩).negOnePow : ℤ) : R) else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.mem_range.mp hi]
    rw [htuple, (PiTensorProduct.tprod R).map_smul_univ, map_smul, ← hD, ← hsign]
  · intro u v _ _ hu hv
    simp only [map_add, hu, hv, smul_add]
  · intro a u _ hu
    rw [map_smul, hu, smul_smul, smul_smul, mul_comm a]

end ReducedTensorWords

namespace LinearMap.IsHomogeneous

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A homogeneous endomorphism of reduced tensor words commutes with the letterwise Koszul twist
up to the sign contributed by its degree. -/
theorem map_koszulTwist_comp {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} {r : ℤ}
    (hb : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r) (q : ℤ) :
    ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ b =
      ((((q * r).negOnePow : ℤ) : R) •
        (b ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))) := by
  apply LinearMap.ext
  intro z
  have hz : z ∈ (⊤ : Submodule R (ReducedTensorWords R M)) := Submodule.mem_top
  rw [← ReducedTensorWords.iSup_gradedPiece_eq_top G] at hz
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  refine Submodule.iSup_induction (fun D : ℤ ↦ gradedPiece G D)
    (motive := fun z ↦
      ReducedTensorWords.map (R := R) (G.koszulTwist q) (b z) =
        (((q * r).negOnePow : ℤ) : R) •
          b (ReducedTensorWords.map (R := R) (G.koszulTwist q) z)) hz ?_ (by simp) ?_
  · intro D x hx
    rw [ReducedTensorWords.map_koszulTwist_apply_of_mem G (hb.map_mem hx) q,
      ReducedTensorWords.map_koszulTwist_apply_of_mem G hx q, map_smul, smul_smul]
    congr 1
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    ring_nf
  · intro x y hx hy
    simp only [map_add, hx, hy, smul_add]

/-- A homogeneous endomorphism of degree one anticommutes with the letterwise Koszul twist of
parameter one. -/
theorem anticommute_map_koszulTwist_one {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) 1) :
    b ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1) +
        ReducedTensorWords.map (R := R) (G.koszulTwist 1) ∘ₗ b = 0 := by
  have h := hb.map_koszulTwist_comp 1
  have hsign : ((((1 : ℤ) * 1).negOnePow : ℤ) : R) = -1 := by norm_num
  rw [hsign] at h
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hz
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hz]
  let x := b (ReducedTensorWords.map (R := R) (G.koszulTwist 1) z)
  change x + (-1 : R) • x = 0
  calc
    x + (-1 : R) • x = (1 : R) • x + (-1 : R) • x := by rw [one_smul]
    _ = ((1 : R) + (-1 : R)) • x := (add_smul _ _ _).symm
    _ = 0 := by simp

end LinearMap.IsHomogeneous

namespace ReducedTensorWords.IsGradedCoderivation

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The square of a homogeneous degree-one graded coderivation is an ordinary coderivation. The
degree hypothesis supplies the anticommutation with the Koszul twist required for the two mixed
terms in the co-Leibniz expansion to cancel. -/
theorem isCoderivation_comp_self_of_isHomogeneous {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G 1 b)
    (hhom : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) 1) :
    IsCoderivation R (b ∘ₗ b) :=
  hb.isCoderivation_comp_self hhom.anticommute_map_koszulTwist_one

end ReducedTensorWords.IsGradedCoderivation

end TauCeti
