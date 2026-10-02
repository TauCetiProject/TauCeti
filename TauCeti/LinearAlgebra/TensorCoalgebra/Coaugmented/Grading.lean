/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Multilinear
public import TauCeti.Algebra.Module.GradedModule.TensorProduct
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation

/-!
# The internal total-degree grading of tensor words

The total-letter-degree pieces of the coaugmented tensor coalgebra form an internal direct
sum. Thus every tensor word has a unique finite decomposition by cohomological degree,
independently of its decomposition by tensor length. The empty word has degree zero.

`TensorWords.grading` uses the existing `TensorWords.gradedPiece` submodules. Its Koszul
twist is the letterwise extension of the twist of the generating module. This identifies
the sign in the coalgebra coderivation equation with the sign of the total grading, and
allows the cofree bar comodule to use the tensor-product grading.

The independence proof uses degree projections obtained by extending multilinear maps on
homogeneous pieces. No freeness or flatness assumption on the generating module is needed.

## References

* E. Getzler and J. D. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1–2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

namespace TauCeti.TensorWords

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

private noncomputable def degreeProjection (G : InternalGrading R M) (p : ℤ) :
    TensorWords R M →ₗ[R] TensorWords R M :=
  DirectSum.toModule R ℕ _ fun n ↦ PiTensorProduct.lift
    (InternalGrading.multilinearFromPieces (fun _ : Fin n ↦ G) fun d ↦
      if ∑ i, d i = p then
        (of R M n).compMultilinearMap
          ((PiTensorProduct.tprod R).compLinearMap fun i ↦ (G.piece (d i)).subtype)
      else 0)

private theorem degreeProjection_of_tprod (G : InternalGrading R M) (p : ℤ) {n : ℕ}
    (d : Fin n → ℤ) (x : Fin n → M) (hx : ∀ i, x i ∈ G.piece (d i)) :
    degreeProjection G p (of R M n (PiTensorProduct.tprod R x)) =
      if ∑ i, d i = p then of R M n (PiTensorProduct.tprod R x) else 0 := by
  rw [degreeProjection, of_def, DirectSum.toModule_lof, PiTensorProduct.lift.tprod]
  have h := InternalGrading.multilinearFromPieces_apply (fun _ : Fin n ↦ G)
    (fun d ↦ if ∑ i, d i = p then
      (of R M n).compMultilinearMap
        ((PiTensorProduct.tprod R).compLinearMap fun i ↦ (G.piece (d i)).subtype)
      else 0) d (fun i ↦ ⟨x i, hx i⟩)
  rw [h]
  split <;> simp only [LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, Submodule.subtype_apply, of_def,
    zero_apply]

private theorem degreeProjection_apply_of_mem (G : InternalGrading R M) {d : ℤ}
    {x : TensorWords R M} (hx : x ∈ gradedPiece G d) (p : ℤ) :
    degreeProjection G p x = if d = p then x else 0 := by
  refine gradedPiece_induction
    (motive := fun x ↦ degreeProjection G p x = if d = p then x else 0)
    hx ?_ (by simp) ?_ ?_
  · intro n degree x hx hdegree
    rw [degreeProjection_of_tprod G p degree x hx, hdegree]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, ite_add_zero]
  · intro r x _ hx
    simp only [map_smul, hx, smul_ite, smul_zero]

/-- Distinct total-letter-degree pieces are independent, including in characteristic two. -/
theorem iSupIndep_gradedPiece (G : InternalGrading R M) : iSupIndep (gradedPiece G) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s x hx hsum p hp
  have h := congrArg (degreeProjection G p) hsum
  simp only [map_sum, map_zero] at h
  have hproj : ∑ q ∈ s, degreeProjection G p (x q) = x p := by
    rw [Finset.sum_eq_single p]
    · rw [degreeProjection_apply_of_mem G (hx p hp), ite_eq_left rfl]
    · intro q hq hqp
      rw [degreeProjection_apply_of_mem G (hx q hq), ite_eq_right hqp]
    · exact fun hnot ↦ (hnot hp).elim
  rwa [hproj] at h

/-- The total-degree pieces of the coaugmented tensor coalgebra form an internal direct sum. -/
theorem isInternal_gradedPiece (G : InternalGrading R M) :
    DirectSum.IsInternal (gradedPiece G) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_gradedPiece G) (iSup_gradedPiece_eq_top G)

/-- Tensor words graded by the sum of the cohomological degrees of their letters. -/
noncomputable def grading (G : InternalGrading R M) : InternalGrading R (TensorWords R M) where
  piece := gradedPiece G
  isInternal := isInternal_gradedPiece G

/-- The internal grading uses the total-letter-degree pieces. -/
@[simp]
theorem grading_piece (G : InternalGrading R M) : (grading G).piece = gradedPiece G := (rfl)

/-- Total-degree decomposition is available on the existing degree pieces. -/
noncomputable instance (G : InternalGrading R M) : DirectSum.Decomposition (gradedPiece G) :=
  (isInternal_gradedPiece G).chooseDecomposition

/-- The degree-`p` component of a homogeneous pure word is that word when its total degree is
`p`, and zero otherwise. -/
theorem coe_decompose_of_tprod (G : InternalGrading R M) {n : ℕ}
    (d : Fin n → ℤ) (x : Fin n → M) (hx : ∀ i, x i ∈ G.piece (d i)) (p : ℤ) :
    (DirectSum.decompose (gradedPiece G) (of R M n (PiTensorProduct.tprod R x)) p :
      TensorWords R M) =
        if ∑ i, d i = p then of R M n (PiTensorProduct.tprod R x) else 0 := by
  split_ifs with hp
  · subst p
    exact DirectSum.decompose_of_mem_same _ (mem_gradedPiece_of_tprod G x d hx)
  · exact DirectSum.decompose_of_mem_ne _ (mem_gradedPiece_of_tprod G x d hx) hp

/-- The empty word belongs to degree zero. -/
theorem one_mem_gradedPiece (G : InternalGrading R M) :
    (1 : TensorWords R M) ∈ gradedPiece G 0 := by
  rw [one_eq_of_zero]
  simpa using mem_gradedPiece_of_tprod G (fun i : Fin 0 ↦ i.elim0)
    (fun i : Fin 0 ↦ i.elim0) (fun i ↦ i.elim0)

/-- The counit is supported in total cohomological degree zero. -/
theorem counit_eq_zero_of_mem_gradedPiece (G : InternalGrading R M) {p : ℤ}
    {w : TensorWords R M} (hw : w ∈ gradedPiece G p) (hp : p ≠ 0) :
    counit R M w = 0 := by
  refine gradedPiece_induction
    (motive := fun w ↦ counit R M w = 0) hw ?_ (map_zero _) ?_ ?_
  · intro n d x _ hd
    have hn : n ≠ 0 := by
      intro hn
      subst n
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hd
      exact hp hd.symm
    exact counit_of_of_ne_zero R M hn _
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, add_zero]
  · intro r x _ hx
    simp only [map_smul, hx, smul_zero]

/-- The total-degree Koszul twist is exactly the letterwise Koszul twist. -/
@[simp]
theorem koszulTwist_grading (G : InternalGrading R M) (q : ℤ) :
    (grading G).koszulTwist q = map (G.koszulTwist q) := by
  apply InternalGrading.linearMap_ext (grading G)
  intro p x hx
  rw [InternalGrading.koszulTwist_apply_of_mem _ hx]
  exact (map_koszulTwist_apply_of_mem G (by simpa only [grading_piece] using hx) q).symm

/-- Deconcatenation preserves total cohomological degree: the degrees of the two cut halves
add to the degree of the original word. -/
theorem isHomogeneous_deconcatenation (G : InternalGrading R M) :
    LinearMap.IsHomogeneous (deconcatenation R M) (grading G).piece
      ((grading G).tensorProduct (grading G)).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p w hw
  simp only [grading_piece, add_zero] at hw ⊢
  refine gradedPiece_induction
    (motive := fun w ↦ deconcatenation R M w ∈
      ((grading G).tensorProduct (grading G)).piece p) hw ?_ ?_ ?_ ?_
  · intro n d x hx hd
    rw [deconcatenation_of, deconcatenationComponent_tprod]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    let dl : Fin i.1 → ℤ := fun j ↦ d (Fin.castLE (by have := i.isLt; omega) j)
    let dr : Fin (n - i.1) → ℤ := fun j ↦ d ⟨i.1 + j.1, by have := j.isLt; omega⟩
    have hsum : (∑ j, dl j) + (∑ j, dr j) = p := by
      rw [← hd]
      have hi : i.1 + (n - i.1) = n := by have := i.isLt; omega
      calc
        _ = ∑ j : Fin (i.1 + (n - i.1)), d (Fin.cast hi j) := by
          simpa only [dl, dr, Fin.castLE, Fin.cast, Fin.castAdd, Fin.natAdd] using
            (Fin.sum_univ_add (fun j : Fin (i.1 + (n - i.1)) ↦ d (Fin.cast hi j))).symm
        _ = ∑ j, d j := Equiv.sum_comp (finCongr hi) d
    rw [← hsum]
    apply InternalGrading.tmul_mem_tensorProduct
    · exact mem_gradedPiece_of_tprod G _ dl (fun j ↦ hx _)
    · exact mem_gradedPiece_of_tprod G _ dr (fun j ↦ hx _)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro r x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

end TauCeti.TensorWords
