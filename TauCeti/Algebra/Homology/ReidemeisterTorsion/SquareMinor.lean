/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The square-minor formula for Reidemeister torsion

Let `C` be a `ℤ`-graded chain complex of vector spaces over a field `F`, with ordered bases
`c i` of each `C.X i`. Split each basis into a first block `Eᵢ` of `q i` vectors followed by a
second block `Dᵢ` of `p i` vectors, so that `n i = q i + p i`, and assume `p (j + 1) = q j`: the
block `Dⱼ₊₁` of `Cⱼ₊₁` has as many vectors as the block `Eⱼ` of `Cⱼ`. The *square minor*
`HomologicalComplex.torsionMinor c hn hpq j` is the square matrix of the differential
`d : Cⱼ₊₁ → Cⱼ` restricted to the span of `Dⱼ₊₁` and followed by the coordinate projection onto
the span of `Eⱼ`; its rows are indexed by `Eⱼ` and its columns by `Dⱼ₊₁`. The differential itself
need not map `Dⱼ₊₁` into the span of `Eⱼ`.

If every square minor is invertible, then `C` is acyclic
(`HomologicalComplex.acyclic_of_det_torsionMinor_ne_zero`): in each degree `j` the boundaries
`d (Dⱼ₊₁)` and the vectors `Dⱼ` form a basis of `Cⱼ`, whose matrix with respect to `c j` is
block triangular with diagonal blocks the square minor and the identity. Applied to these boundary
bases and to the lifts `Dⱼ₊₁`, the defining alternating product of the torsion becomes a product of
minors. For a bounded complex this gives the *square-minor formula*
(`HomologicalComplex.reidemeisterTorsion_eq_finprod_det_torsionMinor`)

`τ(C) = ∏ⱼ det (Aⱼ) ^ ((-1) ^ (j + 1))`,

where `Aⱼ = torsionMinor c hn hpq j` is the square minor of `d : Cⱼ₊₁ → Cⱼ`. There is no
additional sign when each `Eᵢ` precedes `Dᵢ` in the basis `c i`. Coordinate blocks in any other
position are obtained by reordering the bases, which multiplies the torsion by the product of the
signs of the reorderings (`HomologicalComplex.reidemeisterTorsion_reindex`). For a complex
concentrated in degrees `1` and `0`, the only nontrivial minor is the matrix of the differential
itself, recovering the normalization `τ = det (d)⁻¹`.

## Main definitions

* `HomologicalComplex.torsionMinor`: the square minor of the differential `Cⱼ₊₁ → Cⱼ`, with
  columns the last `p (j + 1)` basis vectors of `Cⱼ₊₁` and rows the first `q j` coordinates
  of `Cⱼ`.

## Main results

* `HomologicalComplex.acyclic_of_det_torsionMinor_ne_zero`: a complex whose square minors are all
  invertible is acyclic.
* `HomologicalComplex.reidemeisterTorsion_eq_finprod_det_torsionMinor`: the square-minor formula.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I, Section 2
  (matrices and τ-chains).
* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), 358–426.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] {C : ChainComplex (ModuleCat F) ℤ} {n q p : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : ∀ i, n i = q i + p i)
  (hpq : ∀ j, p (j + 1) = q j)

/-- The square minor of the differential `d : Cⱼ₊₁ → Cⱼ` in the bases `c (j + 1)` and `c j`, each
split by `hn` into a first block `E` of `q` vectors followed by a second block `D` of `p` vectors:
its entry at `(r, k)` is the coordinate along the `r`-th vector of `Eⱼ` of the image under `d` of
the `k`-th vector of `Dⱼ₊₁`. It is square because `p (j + 1) = q j`. -/
def torsionMinor (j : ℤ) : Matrix (Fin (q j)) (Fin (q j)) F :=
  (LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom).submatrix
    (fun r ↦ Fin.cast (hn j).symm (Fin.castAdd (p j) r))
    (fun k ↦ Fin.cast (hn (j + 1)).symm (Fin.natAdd (q (j + 1)) (Fin.cast (hpq j).symm k)))

/-- The entries of the square minor `torsionMinor c hn hpq j`. -/
@[simp]
theorem torsionMinor_apply (j : ℤ) (r k : Fin (q j)) :
    torsionMinor c hn hpq j r k = (c j).repr ((C.d (j + 1) j).hom (c (j + 1)
      (Fin.cast (hn (j + 1)).symm (Fin.natAdd (q (j + 1)) (Fin.cast (hpq j).symm k)))))
      (Fin.cast (hn j).symm (Fin.castAdd (p j) r)) :=
  LinearMap.toMatrix_apply ..

/-- The splitting of the basis indices of `C.X i` into the first `q i` and the last `p i`. -/
private def splitEquiv (i : ℤ) : Fin (q i) ⊕ Fin (p i) ≃ Fin (n i) :=
  finSumFinEquiv.trans (finCongr (hn i).symm)

private theorem splitEquiv_inl (i : ℤ) (r : Fin (q i)) :
    splitEquiv hn i (.inl r) = Fin.cast (hn i).symm (Fin.castAdd (p i) r) :=
  rfl

private theorem splitEquiv_inr (i : ℤ) (k : Fin (p i)) :
    splitEquiv hn i (.inr k) = Fin.cast (hn i).symm (Fin.natAdd (q i) k) :=
  rfl

/-- The vectors of the block `Dⱼ₊₁` of the basis `c (j + 1)`, indexed by `Fin (q j)`: these are
the lifts of the boundary basis of `Bⱼ`. -/
private def minorLift (j : ℤ) (k : Fin (q j)) : C.X (j + 1) :=
  c (j + 1) (splitEquiv hn (j + 1) (.inr (Fin.cast (hpq j).symm k)))

/-- The family of `Cⱼ` made of the boundaries `d (Dⱼ₊₁)` followed by the block `Dⱼ` of `c j`. -/
private def minorFamily (j : ℤ) : Fin (q j) ⊕ Fin (p j) → C.X j :=
  Sum.elim (fun r ↦ (C.d (j + 1) j).hom (minorLift c hn hpq j r))
    fun k ↦ c j (splitEquiv hn j (.inr k))

/-- The determinant of `minorFamily` with respect to `c j`, with its indices split, is that of the
square minor: the matrix is block lower triangular with diagonal blocks the minor and the
identity. -/
private theorem det_minorFamily (j : ℤ) :
    ((c j).reindex (splitEquiv hn j).symm).det (minorFamily c hn hpq j) =
      (torsionMinor c hn hpq j).det := by
  classical
  rw [Basis.det_apply]
  have : ((c j).reindex (splitEquiv hn j).symm).toMatrix (minorFamily c hn hpq j) =
      Matrix.fromBlocks (torsionMinor c hn hpq j) 0
        ((LinearMap.toMatrix (c (j + 1)) (c j) (C.d (j + 1) j).hom).submatrix
          (fun k ↦ splitEquiv hn j (.inr k))
          (fun r ↦ splitEquiv hn (j + 1) (.inr (Fin.cast (hpq j).symm r)))) 1 := by
    ext (r | k) (r' | k')
    · simp [Basis.toMatrix_apply, minorFamily, minorLift, torsionMinor_apply, splitEquiv_inl,
        splitEquiv_inr]
    · simp [Basis.toMatrix_apply, minorFamily]
    · simp [Basis.toMatrix_apply, minorFamily, minorLift, LinearMap.toMatrix_apply]
    · simp [Basis.toMatrix_apply, minorFamily, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

variable {c hn hpq}

variable (hA : ∀ j, (torsionMinor c hn hpq j).det ≠ 0)
include hA

private theorem basis_minorFamily (j : ℤ) :
    LinearIndependent F (minorFamily c hn hpq j) ∧
      Submodule.span F (Set.range (minorFamily c hn hpq j)) = ⊤ :=
  (Basis.is_basis_iff_det _).2 (by rw [det_minorFamily]; exact (hA j).isUnit)

/-- When the square minor in degree `j` is invertible, `minorFamily` is a basis of `Cⱼ`. -/
private def minorBasis (j : ℤ) : Basis (Fin (q j) ⊕ Fin (p j)) F (C.X j) :=
  .mk (basis_minorFamily hA j).1 (basis_minorFamily hA j).2.ge

private theorem coe_minorBasis (j : ℤ) : ⇑(minorBasis hA j) = minorFamily c hn hpq j :=
  Basis.coe_mk _ _

/-- The differential of `x ∈ Cⱼ₊₁` only sees the coordinates of `x` along `Dⱼ₊₁` in
`minorBasis`, which become coordinates along the boundaries `d (Dⱼ₊₁) ⊆ Cⱼ`. -/
private theorem d_eq_sum (j : ℤ) (x : C.X (j + 1)) :
    (C.d (j + 1) j).hom x = ∑ k : Fin (p (j + 1)), (minorBasis hA (j + 1)).repr x (.inr k) •
      minorFamily c hn hpq j (.inl (Fin.cast (hpq j) k)) := by
  conv_lhs => rw [← (minorBasis hA (j + 1)).sum_repr x]
  simp [Fintype.sum_sum_type, coe_minorBasis, minorFamily, minorLift, d_comp_d_apply]

/-- The boundaries `d (Dⱼ₊₁) ⊆ Cⱼ` are linearly independent. -/
private theorem linearIndependent_minorFamily_inl (j : ℤ) :
    LinearIndependent F fun r ↦ minorFamily c hn hpq j (.inl r) := by
  simpa [Function.comp_def, coe_minorBasis] using
    (minorBasis hA j).linearIndependent.comp _ Sum.inl_injective

/-- A cycle `x ∈ Cⱼ₊₁` has no coordinates along `Dⱼ₊₁` in `minorBasis`, so it is the boundary of
the corresponding combination of the block `Dⱼ₊₂`. -/
private theorem exactAt_succ (j : ℤ) : C.ExactAt (j + 1) := by
  rw [C.exactAt_iff' (j + 1 + 1) (j + 1) j (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h0 : ∀ k, (minorBasis hA (j + 1)).repr x (.inr k) = 0 := by
    have := (linearIndependent_minorFamily_inl hA j).comp _ (Fin.cast_injective (hpq j))
    exact Fintype.linearIndependent_iff.1 this _ ((d_eq_sum hA j x).symm.trans hx)
  refine ⟨∑ r, (minorBasis hA (j + 1)).repr x (.inl r) • minorLift c hn hpq (j + 1) r, ?_⟩
  conv_rhs => rw [← (minorBasis hA (j + 1)).sum_repr x]
  simp [Fintype.sum_sum_type, h0, coe_minorBasis, minorFamily]

/-- A complex whose square minors `torsionMinor c hn hpq j` are all invertible is acyclic. -/
theorem acyclic_of_det_torsionMinor_ne_zero : C.Acyclic := fun i ↦ by
  simpa using exactAt_succ hA (i - 1)

/-- The boundaries `d (Dⱼ₊₁)` form a basis of the boundaries `Bⱼ`. -/
private def minorBoundaryBasis (j : ℤ) :
    Basis (Fin (q j)) F (LinearMap.range (C.d (j + 1) j).hom) :=
  .mk (v := fun r ↦ ⟨_, LinearMap.mem_range_self _ (minorLift c hn hpq j r)⟩)
    (.of_comp (Submodule.subtype _) (linearIndependent_minorFamily_inl hA j)) <| by
      rintro ⟨_, x, rfl⟩ -
      have : (⟨_, LinearMap.mem_range_self _ x⟩ : LinearMap.range (C.d (j + 1) j).hom) =
          ∑ k : Fin (p (j + 1)), (minorBasis hA (j + 1)).repr x (.inr k) •
            ⟨_, LinearMap.mem_range_self _ (minorLift c hn hpq j (Fin.cast (hpq j) k))⟩ :=
        Subtype.ext (by simp [d_eq_sum hA j x, minorFamily])
      rw [this]
      exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

private theorem coe_minorBoundaryBasis (j : ℤ) (r : Fin (q j)) :
    (minorBoundaryBasis hA j r : C.X j) = (C.d (j + 1) j).hom (minorLift c hn hpq j r) := by
  simp [minorBoundaryBasis]

/-- **The square-minor formula.** Let `C` be a bounded complex with bases `c i`, each split by
`hn` into a first block `Eᵢ` of `q i` vectors followed by a second block `Dᵢ` of `p i` vectors,
with `p (j + 1) = q j`. If every square minor `Aⱼ = torsionMinor c hn hpq j` of the differential
`Cⱼ₊₁ → Cⱼ` is invertible, then the torsion of `C` is `∏ⱼ det (Aⱼ) ^ ((-1) ^ (j + 1))`; the
complex is then acyclic by `acyclic_of_det_torsionMinor_ne_zero`, so this product is nonzero. -/
theorem reidemeisterTorsion_eq_finprod_det_torsionMinor (hfin : {i | n i ≠ 0}.Finite) :
    C.reidemeisterTorsion c =
      ∏ᶠ j : ℤ, (torsionMinor c hn hpq j).det ^ ((j + 1).negOnePow : ℤ) := by
  have hshift : ∏ᶠ j : ℤ, (torsionMinor c hn hpq j).det ^ ((j + 1).negOnePow : ℤ) =
      ∏ᶠ j : ℤ, (torsionMinor c hn hpq (j + 1)).det ^ ((j + 1 + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight 1)).symm
  rw [reidemeisterTorsion_eq_finprod (c := c) hfin (acyclic_of_det_torsionMinor_ne_zero hA)
      (minorBoundaryBasis hA) (minorLift c hn hpq)
      (fun j r ↦ (coe_minorBoundaryBasis hA j r).symm),
    hshift]
  refine finprod_congr fun j ↦ ?_
  have hn' : n (j + 1) = q (j + 1) + q j := by rw [hn, hpq]
  have hfam : Fin.append (fun k ↦ (minorBoundaryBasis hA (j + 1) k : C.X (j + 1)))
      (minorLift c hn hpq j) ∘ Fin.cast hn' =
        minorFamily c hn hpq (j + 1) ∘ (splitEquiv hn (j + 1)).symm := by
    ext k
    obtain ⟨m | m, rfl⟩ := (splitEquiv hn (j + 1)).surjective k
    · have : Fin.cast hn' (splitEquiv hn (j + 1) (.inl m)) = Fin.castAdd (q j) m :=
        Fin.ext (by simp [splitEquiv_inl])
      simp [this, coe_minorBoundaryBasis, minorFamily]
    · have : Fin.cast hn' (splitEquiv hn (j + 1) (.inr m)) =
          Fin.natAdd (q (j + 1)) (Fin.cast (hpq j) m) := Fin.ext (by simp [splitEquiv_inr])
      simp [this, minorFamily, minorLift]
  rw [torsionBracket_eq_det_append c _ _ _ _ _ hn', hfam, ← Basis.det_reindex, det_minorFamily]
  simp only [Int.negOnePow_succ, neg_neg]

end HomologicalComplex
