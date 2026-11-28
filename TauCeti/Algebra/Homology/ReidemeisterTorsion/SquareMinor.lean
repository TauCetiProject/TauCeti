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

The arguments only involve one differential `Cⱼ → Cᵢ` at a time, so they are first carried out
for a complex of any shape and two arbitrary degrees, with the condition `p j = q i` as a
hypothesis. The two-periodic square-minor formula in
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.SquareMinor` uses the same API.

## Main definitions

* `HomologicalComplex.squareMinor`: for a complex of any shape, the square minor of the
  differential `Cⱼ → Cᵢ`, with columns the last `p j` basis vectors of `Cⱼ` and rows the first
  `q i` coordinates of `Cᵢ`.
* `HomologicalComplex.squareMinorLift`, `HomologicalComplex.squareMinorBoundaryBasis`: the columns
  of the square minor, and their images under the differential, which form a basis of the
  boundaries when the square minors are invertible.
* `HomologicalComplex.torsionMinor`: the square minor of the differential `Cⱼ₊₁ → Cⱼ` of a
  `ℤ`-graded chain complex.

## Main results

* `HomologicalComplex.exactAt_of_det_squareMinor_ne_zero`: a complex is exact in a degree where
  the square minors of the incoming and outgoing differentials are invertible.
* `HomologicalComplex.torsionBracket_eq_det_squareMinor`: the bracket of the boundary bases
  `squareMinorBoundaryBasis` and the lifts `squareMinorLift` is the determinant of a square minor.
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

variable {F : Type*} [Field F]

section General

/-! ### The square minor of a differential between two degrees

For a complex of any shape, the arguments only involve a single differential `d : Cⱼ → Cᵢ`
between two based spaces, so they are stated for two arbitrary degrees `i` and `j` with the
condition `p j = q i` as a hypothesis. This avoids rewriting degrees such as `i + 1 + 1` inside
dependent types and serves both `ℤ`-graded and two-periodic complexes. -/

variable {ι : Type*} {cs : ComplexShape ι} {C : HomologicalComplex (ModuleCat F) cs}
  {n q p : ι → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : ∀ i, n i = q i + p i)

/-- The square minor of the differential `d : Cⱼ → Cᵢ` in the bases `c j` and `c i`, each split
by `hn` into a first block `E` of `q` vectors followed by a second block `D` of `p` vectors: its
entry at `(r, k)` is the coordinate along the `r`-th vector of `Eᵢ` of the image under `d` of the
`k`-th vector of `Dⱼ`. It is square because `p j = q i`. -/
def squareMinor (i j : ι) (h : p j = q i) : Matrix (Fin (q i)) (Fin (q i)) F :=
  (LinearMap.toMatrix (c j) (c i) (C.d j i).hom).submatrix
    (fun r ↦ Fin.cast (hn i).symm (Fin.castAdd (p i) r))
    (fun k ↦ Fin.cast (hn j).symm (Fin.natAdd (q j) (Fin.cast h.symm k)))

/-- The entries of the square minor `squareMinor c hn i j h`. -/
@[simp]
theorem squareMinor_apply (i j : ι) (h : p j = q i) (r k : Fin (q i)) :
    squareMinor c hn i j h r k = (c i).repr ((C.d j i).hom (c j
      (Fin.cast (hn j).symm (Fin.natAdd (q j) (Fin.cast h.symm k)))))
      (Fin.cast (hn i).symm (Fin.castAdd (p i) r)) :=
  LinearMap.toMatrix_apply ..

/-- The vectors of the block `Dⱼ` of the basis `c j`, indexed by `Fin (q i)`: the columns of the
square minor `squareMinor c hn i j h`, whose images under `d : Cⱼ → Cᵢ` are the boundary basis
`squareMinorBoundaryBasis` of `Bᵢ`. -/
def squareMinorLift (i j : ι) (h : p j = q i) (r : Fin (q i)) : C.X j :=
  c j (Fin.cast (hn j).symm (Fin.natAdd (q j) (Fin.cast h.symm r)))

/-- The lift `squareMinorLift c hn i j h r` is the vector of `c j` indexing the `r`-th column of
the square minor `squareMinor c hn i j h`. -/
@[simp]
theorem squareMinorLift_apply (i j : ι) (h : p j = q i) (r : Fin (q i)) :
    squareMinorLift c hn i j h r =
      c j (Fin.cast (hn j).symm (Fin.natAdd (q j) (Fin.cast h.symm r))) :=
  (rfl)

/-- The splitting of the basis indices of `C.X i` into the first `q i` and the last `p i`. -/
private def splitEquiv (i : ι) : Fin (q i) ⊕ Fin (p i) ≃ Fin (n i) :=
  finSumFinEquiv.trans (finCongr (hn i).symm)

private theorem splitEquiv_inl (i : ι) (r : Fin (q i)) :
    splitEquiv hn i (.inl r) = Fin.cast (hn i).symm (Fin.castAdd (p i) r) :=
  rfl

private theorem splitEquiv_inr (i : ι) (k : Fin (p i)) :
    splitEquiv hn i (.inr k) = Fin.cast (hn i).symm (Fin.natAdd (q i) k) :=
  rfl

/-- The family of `Cᵢ` made of the boundaries `d (Dⱼ)` followed by the block `Dᵢ` of `c i`. -/
private def minorFamily (i j : ι) (h : p j = q i) : Fin (q i) ⊕ Fin (p i) → C.X i :=
  Sum.elim (fun r ↦ (C.d j i).hom (squareMinorLift c hn i j h r))
    fun k ↦ c i (splitEquiv hn i (.inr k))

/-- The determinant of `minorFamily` with respect to `c i`, with its indices split, is that of the
square minor: the matrix is block lower triangular with diagonal blocks the minor and the
identity. -/
private theorem det_minorFamily (i j : ι) (h : p j = q i) :
    ((c i).reindex (splitEquiv hn i).symm).det (minorFamily c hn i j h) =
      (squareMinor c hn i j h).det := by
  classical
  rw [Basis.det_apply]
  have : ((c i).reindex (splitEquiv hn i).symm).toMatrix (minorFamily c hn i j h) =
      Matrix.fromBlocks (squareMinor c hn i j h) 0
        ((LinearMap.toMatrix (c j) (c i) (C.d j i).hom).submatrix
          (fun k ↦ splitEquiv hn i (.inr k))
          (fun r ↦ splitEquiv hn j (.inr (Fin.cast h.symm r)))) 1 := by
    ext (r | k) (r' | k')
    · simp [Basis.toMatrix_apply, minorFamily, splitEquiv_inl, splitEquiv_inr]
    · simp [Basis.toMatrix_apply, minorFamily]
    · simp [Basis.toMatrix_apply, minorFamily, LinearMap.toMatrix_apply,
        splitEquiv_inr]
    · simp [Basis.toMatrix_apply, minorFamily, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

/-- The bracket in degree `j` of a boundary basis `b₁` of `Bⱼ = d (Cᵢ)` made of the images of the
lifts `squareMinorLift c hn j i h₁`, followed by the lifts `squareMinorLift c hn k j h₂` of a basis
`b₀` of `d (Cⱼ)`, is the determinant of the square minor of `d : Cᵢ → Cⱼ`. -/
theorem torsionBracket_eq_det_squareMinor {i j k : ι} (hi : cs.prev j = i) (hk : cs.next j = k)
    (hex : C.ExactAt j) {h₁ : p i = q j} {h₂ : p j = q k}
    (b₁ : Basis (Fin (q j)) F (LinearMap.range (C.d i j).hom))
    (b₀ : Basis (Fin (q k)) F (LinearMap.range (C.d j k).hom))
    (hb₁ : ∀ r, (b₁ r : C.X j) = (C.d i j).hom (squareMinorLift c hn j i h₁ r))
    (hs : ∀ l, (C.d j k).hom (squareMinorLift c hn k j h₂ l) = b₀ l) :
    torsionBracket c hi hk hex b₁ b₀ (squareMinorLift c hn k j h₂) hs =
      (squareMinor c hn j i h₁).det := by
  have hn' : n j = q j + q k := by rw [hn, h₂]
  have hfam : Fin.append (fun r ↦ (b₁ r : C.X j)) (squareMinorLift c hn k j h₂) ∘ Fin.cast hn' =
      minorFamily c hn j i h₁ ∘ (splitEquiv hn j).symm := by
    ext l
    obtain ⟨m | m, rfl⟩ := (splitEquiv hn j).surjective l
    · have : Fin.cast hn' (splitEquiv hn j (.inl m)) = Fin.castAdd (q k) m :=
        Fin.ext (by simp [splitEquiv_inl])
      simp [this, hb₁, minorFamily]
    · have : Fin.cast hn' (splitEquiv hn j (.inr m)) = Fin.natAdd (q j) (Fin.cast h₂ m) :=
        Fin.ext (by simp [splitEquiv_inr])
      rw [Function.comp_apply, Function.comp_apply, this, Fin.append_right,
        Equiv.symm_apply_apply]
      simp [minorFamily, splitEquiv_inr]
  rw [torsionBracket_eq_det_append c _ _ _ _ _ _ _ hn', hfam, ← Basis.det_reindex,
    det_minorFamily]

variable {c hn}

private theorem basis_minorFamily {i j : ι} {h : p j = q i}
    (hA : (squareMinor c hn i j h).det ≠ 0) :
    LinearIndependent F (minorFamily c hn i j h) ∧
      Submodule.span F (Set.range (minorFamily c hn i j h)) = ⊤ :=
  (Basis.is_basis_iff_det _).2 (by rw [det_minorFamily]; exact hA.isUnit)

/-- When the square minor of `Cⱼ → Cᵢ` is invertible, `minorFamily` is a basis of `Cᵢ`. -/
private def minorBasis {i j : ι} {h : p j = q i} (hA : (squareMinor c hn i j h).det ≠ 0) :
    Basis (Fin (q i) ⊕ Fin (p i)) F (C.X i) :=
  .mk (basis_minorFamily hA).1 (basis_minorFamily hA).2.ge

private theorem coe_minorBasis {i j : ι} {h : p j = q i} (hA : (squareMinor c hn i j h).det ≠ 0) :
    ⇑(minorBasis hA) = minorFamily c hn i j h :=
  Basis.coe_mk _ _

/-- The boundaries `d (Dⱼ) ⊆ Cᵢ` are linearly independent. -/
private theorem linearIndependent_minorFamily_inl {i j : ι} {h : p j = q i}
    (hA : (squareMinor c hn i j h).det ≠ 0) :
    LinearIndependent F fun r ↦ minorFamily c hn i j h (.inl r) := by
  simpa [Function.comp_def, coe_minorBasis] using
    (minorBasis hA).linearIndependent.comp _ Sum.inl_injective

/-- The differential `Cⱼ → Cₖ` of `x` only sees the coordinates of `x` along `Dⱼ` in the basis
`minorBasis` of `Cⱼ`, which become coordinates along the boundaries `d (Dⱼ) ⊆ Cₖ`. -/
private theorem d_eq_sum {i j k : ι} {h₁ : p i = q j} (h₂ : p j = q k)
    (hA : (squareMinor c hn j i h₁).det ≠ 0) (x : C.X j) :
    (C.d j k).hom x = ∑ m : Fin (p j), (minorBasis hA).repr x (.inr m) •
      minorFamily c hn k j h₂ (.inl (Fin.cast h₂ m)) := by
  conv_lhs => rw [← (minorBasis hA).sum_repr x]
  simp [Fintype.sum_sum_type, coe_minorBasis, minorFamily, splitEquiv_inr,
    d_comp_d_apply]

/-- If the square minors of the differentials `Cᵢ → Cⱼ` into and `Cⱼ → Cₖ` out of degree `j` are
invertible, then `C` is exact at `j`: a cycle has no coordinates along `Dⱼ` in `minorBasis`, so it
is the boundary of the corresponding combination of the block `Dᵢ`. -/
theorem exactAt_of_det_squareMinor_ne_zero {i j k : ι} (hi : cs.prev j = i) (hk : cs.next j = k)
    {h₁ : p i = q j} {h₂ : p j = q k} (hA₁ : (squareMinor c hn j i h₁).det ≠ 0)
    (hA₂ : (squareMinor c hn k j h₂).det ≠ 0) : C.ExactAt j := by
  rw [C.exactAt_iff' i j k hi hk, ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h0 : ∀ m, (minorBasis hA₁).repr x (.inr m) = 0 := by
    have := (linearIndependent_minorFamily_inl hA₂).comp _ (Fin.cast_injective h₂)
    exact Fintype.linearIndependent_iff.1 this _ ((d_eq_sum h₂ hA₁ x).symm.trans hx)
  refine ⟨∑ r, (minorBasis hA₁).repr x (.inl r) • squareMinorLift c hn j i h₁ r, ?_⟩
  conv_rhs => rw [← (minorBasis hA₁).sum_repr x]
  simp [Fintype.sum_sum_type, h0, coe_minorBasis, minorFamily]

/-- When the square minors of `d : Cⱼ → Cₖ` and of `d : Cᵢ → Cⱼ` are invertible, the images
`d (Dⱼ)` of the lifts `squareMinorLift c hn k j h₁` form a basis of the boundaries
`Bₖ = d (Cⱼ)`. -/
def squareMinorBoundaryBasis {i j k : ι} {h₁ : p j = q k} {h₀ : p i = q j}
    (hA₁ : (squareMinor c hn k j h₁).det ≠ 0) (hA₀ : (squareMinor c hn j i h₀).det ≠ 0) :
    Basis (Fin (q k)) F (LinearMap.range (C.d j k).hom) :=
  .mk (v := fun r ↦ ⟨_, LinearMap.mem_range_self _ (squareMinorLift c hn k j h₁ r)⟩)
    (.of_comp (Submodule.subtype _) (linearIndependent_minorFamily_inl hA₁)) <| by
      rintro ⟨_, x, rfl⟩ -
      have : (⟨_, LinearMap.mem_range_self _ x⟩ : LinearMap.range (C.d j k).hom) =
          ∑ m : Fin (p j), (minorBasis hA₀).repr x (.inr m) •
            ⟨_, LinearMap.mem_range_self _ (squareMinorLift c hn k j h₁ (Fin.cast h₁ m))⟩ :=
        Subtype.ext (by simp [d_eq_sum h₁ hA₀ x, minorFamily])
      rw [this]
      exact Submodule.sum_mem _ fun m _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The vectors of `squareMinorBoundaryBasis` are the images under the differential of the
lifts `squareMinorLift`. -/
@[simp]
theorem coe_squareMinorBoundaryBasis {i j k : ι} {h₁ : p j = q k} {h₀ : p i = q j}
    (hA₁ : (squareMinor c hn k j h₁).det ≠ 0) (hA₀ : (squareMinor c hn j i h₀).det ≠ 0)
    (r : Fin (q k)) :
    (squareMinorBoundaryBasis hA₁ hA₀ r : C.X k) =
      (C.d j k).hom (squareMinorLift c hn k j h₁ r) := by
  simp [squareMinorBoundaryBasis]

end General

/-! ### Chain complexes graded by `ℤ` -/

variable {C : ChainComplex (ModuleCat F) ℤ} {n q p : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : ∀ i, n i = q i + p i)
  (hpq : ∀ j, p (j + 1) = q j)

/-- The square minor of the differential `d : Cⱼ₊₁ → Cⱼ` in the bases `c (j + 1)` and `c j`, each
split by `hn` into a first block `E` of `q` vectors followed by a second block `D` of `p` vectors:
its entry at `(r, k)` is the coordinate along the `r`-th vector of `Eⱼ` of the image under `d` of
the `k`-th vector of `Dⱼ₊₁`. It is square because `p (j + 1) = q j`. -/
def torsionMinor (j : ℤ) : Matrix (Fin (q j)) (Fin (q j)) F :=
  squareMinor c hn j (j + 1) (hpq j)

/-- The entries of the square minor `torsionMinor c hn hpq j`. -/
@[simp]
theorem torsionMinor_apply (j : ℤ) (r k : Fin (q j)) :
    torsionMinor c hn hpq j r k = (c j).repr ((C.d (j + 1) j).hom (c (j + 1)
      (Fin.cast (hn (j + 1)).symm (Fin.natAdd (q (j + 1)) (Fin.cast (hpq j).symm k)))))
      (Fin.cast (hn j).symm (Fin.castAdd (p j) r)) :=
  squareMinor_apply ..

/-- The square minor `torsionMinor c hn hpq j` is the square minor `squareMinor` of the
differential `Cⱼ₊₁ → Cⱼ`. -/
theorem torsionMinor_eq_squareMinor (j : ℤ) :
    torsionMinor c hn hpq j = squareMinor c hn j (j + 1) (hpq j) := by
  rw [torsionMinor]

variable {c hn hpq}

variable (hA : ∀ j, (torsionMinor c hn hpq j).det ≠ 0)
include hA

/-- A complex whose square minors `torsionMinor c hn hpq j` are all invertible is acyclic. -/
theorem acyclic_of_det_torsionMinor_ne_zero : C.Acyclic := fun i ↦ by
  simp only [torsionMinor_eq_squareMinor] at hA
  simpa using exactAt_of_det_squareMinor_ne_zero (c := c) (hn := hn) (j := i - 1 + 1)
    (by simp) (by simp) (hA (i - 1 + 1)) (hA (i - 1))

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
  have hA' (j : ℤ) : (squareMinor c hn j (j + 1) (hpq j)).det ≠ 0 := by
    simpa only [torsionMinor_eq_squareMinor] using hA j
  rw [reidemeisterTorsion_eq_finprod (c := c) hfin (acyclic_of_det_torsionMinor_ne_zero hA)
      (fun j ↦ squareMinorBoundaryBasis (hA' j) (hA' (j + 1)))
      (fun j ↦ squareMinorLift c hn j (j + 1) (hpq j))
      (fun j r ↦ (coe_squareMinorBoundaryBasis (hA' j) (hA' (j + 1)) r).symm),
    hshift]
  refine finprod_congr fun j ↦ ?_
  rw [torsionBracket_eq_det_squareMinor c hn _ _ _ _ _
    (coe_squareMinorBoundaryBasis (hA' (j + 1)) (hA' (j + 1 + 1)))]
  simp only [Int.negOnePow_succ, neg_neg, torsionMinor_eq_squareMinor]

end HomologicalComplex
