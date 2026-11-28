/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Content
public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.JucysMurphy
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# One-box content selection on the regular Hecke carrier

For a preceding Young diagram, `CoxeterSystem.additiveContentSelectorMatrix` evaluates
`Lagrange.basis` for its addable-box contents on the fixed-carrier additive Jucys–Murphy matrix.
On a vector with one of these eigenvalues it acts as the identity for the chosen box and as
zero for the other boxes (`CoxeterSystem.additiveContentSelectorMatrix_mulVec`). The selectors
are symmetric and continuous for `Q > 0`, including at `Q = 1`. They are the factors used to
refine a preceding path projection; on the full carrier their eigenvalues need not be just
zero and one.

The construction uses `CoxeterSystem.additiveJucysMurphyMatrix` and the separation of additive
contents in `YoungDiagram.injOn_additiveContent_cellContent`.

## References

* H. Wenzl, *Hecke algebras of type Aₙ and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Matrix Polynomial TauCeti.TypeAHeckeAlgebra

namespace CoxeterSystem

variable {W : Type*} [Group W] [Fintype W] [DecidableEq W] {n : ℕ}
variable (cs : CoxeterSystem (CoxeterMatrix.A n) W)

/-- The Lagrange selector at an addable box `c` of `μ`, evaluated on the additive
Jucys–Murphy matrix of strand `i` at the positive-real Hecke parameter `√Q`. -/
noncomputable def additiveContentSelectorMatrix (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) (Q : ℝ) : Matrix W W ℝ :=
  aeval (cs.additiveJucysMurphyMatrix (Real.sqrt Q) i)
    (Lagrange.basis μ.addables (fun d => additiveContent Q (YoungDiagram.cellContent d)) c.val)

/-- The one-box selector is the evaluation of the Lagrange basis polynomial on the
additive Jucys–Murphy matrix. -/
theorem additiveContentSelectorMatrix_def (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) (Q : ℝ) :
    cs.additiveContentSelectorMatrix i c Q =
      aeval (cs.additiveJucysMurphyMatrix (Real.sqrt Q) i)
        (Lagrange.basis μ.addables (fun d => additiveContent Q (YoungDiagram.cellContent d))
          c.val) :=
  (rfl)

/-- For a positive parameter, the selector fixes vectors of the chosen addable content
and kills vectors of every other addable content of the same diagram. -/
theorem additiveContentSelectorMatrix_mulVec (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) {d : ℕ × ℕ} (hd : μ.IsAddable d) {Q : ℝ} (hQ : 0 < Q)
    {v : W → ℝ}
    (hv : cs.additiveJucysMurphyMatrix (Real.sqrt Q) i *ᵥ v =
      additiveContent Q (YoungDiagram.cellContent d) • v) :
    cs.additiveContentSelectorMatrix i c Q *ᵥ v = if c.val = d then v else 0 := by
  let f := fun e => additiveContent Q (YoungDiagram.cellContent e)
  have hsep : Set.InjOn f (↑μ.addables : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact μ.injOn_additiveContent_cellContent hQ
      (YoungDiagram.mem_addables.mp ha) (YoungDiagram.mem_addables.mp hb) hab
  have hvec : Matrix.toLinAlgEquiv' (cs.additiveJucysMurphyMatrix (Real.sqrt Q) i) v =
      f d • v := by
    rw [Matrix.toLinAlgEquiv'_apply]
    exact hv
  rw [additiveContentSelectorMatrix_def, ← Matrix.toLinAlgEquiv'_apply,
    ← aeval_algHom_apply Matrix.toLinAlgEquiv', Module.End.aeval_apply_of_mem_apply_eq_smul hvec]
  by_cases h : c.val = d
  · subst d
    rw [ite_eq_left rfl,
      Lagrange.eval_basis_self hsep (YoungDiagram.mem_addables.mpr c.property), one_smul]
  · rw [ite_eq_right h, Lagrange.eval_basis_of_ne h (YoungDiagram.mem_addables.mpr hd), zero_smul]

/-- The selector fixes a vector of its own additive content. -/
@[simp]
theorem additiveContentSelectorMatrix_mulVec_self (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) {Q : ℝ} (hQ : 0 < Q) {v : W → ℝ}
    (hv : cs.additiveJucysMurphyMatrix (Real.sqrt Q) i *ᵥ v =
      additiveContent Q (YoungDiagram.cellContent c.val) • v) :
    cs.additiveContentSelectorMatrix i c Q *ᵥ v = v := by
  rw [additiveContentSelectorMatrix_mulVec cs i c c.property hQ hv, ite_eq_left rfl]

/-- For a positive unit parameter, the selector is left multiplication by the corresponding
polynomial in the additive Jucys–Murphy element, written in the `basisTw` coordinates. -/
theorem additiveContentSelectorMatrix_eq_leftMulMatrix (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) {q : ℝˣ} (hq : 0 ≤ (q : ℝ)) :
    cs.additiveContentSelectorMatrix i c ((q : ℝ) ^ 2) =
      Algebra.leftMulMatrix (basisTw (n := n + 1) q cs) (aeval (additiveJucysMurphy q i)
        (Lagrange.basis μ.addables
          (fun d => additiveContent ((q : ℝ) ^ 2) (YoungDiagram.cellContent d)) c.val)) := by
  rw [additiveContentSelectorMatrix_def, Real.sqrt_sq hq,
    cs.additiveJucysMurphyMatrix_eq_leftMulMatrix, aeval_algHom_apply]

/-- The one-box selector is symmetric on the permutation-indexed regular carrier. -/
@[simp]
theorem transpose_additiveContentSelectorMatrix (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) (Q : ℝ) :
    (cs.additiveContentSelectorMatrix i c Q)ᵀ = cs.additiveContentSelectorMatrix i c Q := by
  rw [additiveContentSelectorMatrix_def]
  apply MulOpposite.op_injective
  rw [← Matrix.transposeAlgEquiv_apply (R := ℝ),
    ← aeval_algHom_apply (Matrix.transposeAlgEquiv W ℝ ℝ), Matrix.transposeAlgEquiv_apply,
    transpose_additiveJucysMurphyMatrix, aeval_op_apply]

/-- For an addable box, the Lagrange selector is continuous over the whole positive-real
parameter family. The formula uses no division by `Q - 1`. -/
@[fun_prop]
theorem continuousOn_additiveContentSelectorMatrix (i : Fin (n + 1)) {μ : YoungDiagram}
    (c : {c // μ.IsAddable c}) :
    ContinuousOn (cs.additiveContentSelectorMatrix i c) (Set.Ioi 0) := by
  let f := fun (Q : ℝ) e => additiveContent Q (YoungDiagram.cellContent e)
  let A : ℝ → Matrix W W ℝ := fun Q => cs.additiveJucysMurphyMatrix (Real.sqrt Q) i
  have hA : ContinuousOn A (Set.Ioi 0) := cs.continuousOn_additiveJucysMurphyMatrix_sqrt i
  have hprod (t : Finset (ℕ × ℕ)) (ht : t ⊆ μ.addables.erase c.val) :
      ContinuousOn (fun Q => aeval (A Q)
        (∏ d ∈ t, Lagrange.basisDivisor (f Q c.val) (f Q d))) (Set.Ioi 0) := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, map_one] using continuousOn_const
    | @insert d t hdt ih =>
      simp only [Finset.insert_subset_iff] at ht
      obtain ⟨hne, hd⟩ := Finset.mem_erase.mp ht.1
      have hfactor : ContinuousOn (fun Q => aeval (A Q)
            (Lagrange.basisDivisor (f Q c.val) (f Q d))) (Set.Ioi 0) := by
        simp only [Lagrange.basisDivisor, map_mul, map_sub, aeval_X, aeval_C,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul]
        exact (YoungDiagram.continuousOn_inv_sub_additiveContent_cellContent c.property
          (YoungDiagram.mem_addables.mp hd) hne.symm).smul
            (hA.sub ((continuousOn_additiveContent_pos _).smul continuousOn_const))
      simp only [Finset.prod_insert hdt, map_mul]
      exact hfactor.mul (ih ht.2)
  refine (hprod (μ.addables.erase c.val) (Finset.Subset.refl _)).congr fun Q _ => ?_
  rw [additiveContentSelectorMatrix_def, Lagrange.basis]

end CoxeterSystem
