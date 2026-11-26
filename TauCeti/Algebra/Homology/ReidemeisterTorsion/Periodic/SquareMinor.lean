/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The square-minor formula for the torsion of a two-periodic complex

Let `C` be a two-periodic complex of vector spaces over a field `F`, a complex for the shape
`ComplexShape.up (ZMod 2)`, with ordered bases `c i` of its even and odd spaces `C₀` and `C₁`.
Split each basis into a first block `Eᵢ` of `q i` vectors followed by a second block `Dᵢ` of `p i`
vectors, so that `n i = q i + p i`, and assume `p (i + 1) = q i`: the block `D₁` of `C₁` has as
many vectors as the block `E₀` of `C₀`, and the block `D₀` as many as `E₁`. The *square minor*
`HomologicalComplex.parityTorsionMinor c hn hpq i` is the square matrix of the differential
`d : Cᵢ₊₁ → Cᵢ` restricted to the span of `Dᵢ₊₁` and followed by the coordinate projection onto
the span of `Eᵢ`; its rows are indexed by `Eᵢ` and its columns by `Dᵢ₊₁`. The differential itself
need not map `Dᵢ₊₁` into the span of `Eᵢ`.

If both square minors are invertible, then `C` is acyclic
(`HomologicalComplex.acyclic_of_det_parityTorsionMinor_ne_zero`): in each degree `i` the
boundaries `d (Dᵢ₊₁)` and the vectors `Dᵢ` form a basis of `Cᵢ`, whose matrix with respect to `c i`
is block triangular with diagonal blocks the square minor and the identity. Applied to these
boundary bases and to the lifts `Dᵢ₊₁`, the two brackets defining the torsion
`HomologicalComplex.parityTorsion` become the determinants of the minors, which gives the
*square-minor formula* (`HomologicalComplex.parityTorsion_eq_det_parityTorsionMinor_mul_inv`)

`τ(C) = det (A₁) · det (A₀)⁻¹`,

where `Aᵢ = parityTorsionMinor c hn hpq i` is the square minor of `d : Cᵢ₊₁ → Cᵢ`. There is no
additional sign when each `Eᵢ` precedes `Dᵢ` in the basis `c i`; coordinate blocks in any other
position are obtained by reordering the bases, which multiplies the torsion by a sign
(`HomologicalComplex.parityTorsion_reindex`). This is the two-periodic counterpart of the formula
`HomologicalComplex.reidemeisterTorsion_eq_finprod_det_torsionMinor` for bounded `ℤ`-graded
complexes. No boundedness enters: there are only two minors. For the complex `F → F` given by
multiplication by `a` from the odd to the even degree, with `E₀` and `D₁` the two basis vectors, the
only nontrivial minor is `A₀ = (a)`, recovering the normalization `τ = a⁻¹` of
`HomologicalComplex.parityTorsion_of_d_zero_one`.

Expressing the torsion through minors makes it a rational function of the matrix coefficients of
the differentials near any complex whose minors are invertible; this is how its continuity is
proved in `TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Topology`.

## Main definitions

* `HomologicalComplex.parityTorsionMinor`: the square minor of the differential `Cᵢ₊₁ → Cᵢ`, with
  columns the last `p (i + 1)` basis vectors of `Cᵢ₊₁` and rows the first `q i` coordinates
  of `Cᵢ`.

## Main results

* `HomologicalComplex.acyclic_of_det_parityTorsionMinor_ne_zero`: a two-periodic complex whose two
  square minors are invertible is acyclic.
* `HomologicalComplex.parityTorsion_eq_det_parityTorsionMinor_mul_inv`: the square-minor formula.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002), §2
  (torsion through nonvanishing minors).
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I, Section 2
  (matrices and τ-chains).
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2 (the torsion of a two-periodic complex).
-/

public section

noncomputable section

open CategoryTheory Module
open CochainComplex (prev_zmod_two_zero next_zmod_two_zero prev_zmod_two_one next_zmod_two_one)

namespace HomologicalComplex

variable {F : Type*} [Field F] {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))}
  {n q p : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : ∀ i, n i = q i + p i)
  (hpq : ∀ i, p (i + 1) = q i)

/-- The square minor of the differential `d : Cᵢ₊₁ → Cᵢ` of a two-periodic complex in the bases
`c (i + 1)` and `c i`, each split by `hn` into a first block `E` of `q` vectors followed by a second
block `D` of `p` vectors: its entry at `(r, k)` is the coordinate along the `r`-th vector of `Eᵢ` of
the image under `d` of the `k`-th vector of `Dᵢ₊₁`. It is square because `p (i + 1) = q i`. -/
def parityTorsionMinor (i : ZMod 2) : Matrix (Fin (q i)) (Fin (q i)) F :=
  (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).submatrix
    (fun r ↦ Fin.cast (hn i).symm (Fin.castAdd (p i) r))
    (fun k ↦ Fin.cast (hn (i + 1)).symm (Fin.natAdd (q (i + 1)) (Fin.cast (hpq i).symm k)))

/-- The entries of the square minor `parityTorsionMinor c hn hpq i`. -/
@[simp]
theorem parityTorsionMinor_apply (i : ZMod 2) (r k : Fin (q i)) :
    parityTorsionMinor c hn hpq i r k = (c i).repr ((C.d (i + 1) i).hom (c (i + 1)
      (Fin.cast (hn (i + 1)).symm (Fin.natAdd (q (i + 1)) (Fin.cast (hpq i).symm k)))))
      (Fin.cast (hn i).symm (Fin.castAdd (p i) r)) :=
  LinearMap.toMatrix_apply ..

/-! ### The minor of the differential `Cⱼ → Cᵢ`

The two degrees of a two-periodic complex are each other's successor, so the arguments below are
stated for a differential `Cⱼ → Cᵢ` between two arbitrary degrees, with the condition `p j = q i`
as a hypothesis; this avoids identifying `i + 1 + 1` with `i` inside dependent types. -/

/-- The square minor of the differential `d : Cⱼ → Cᵢ`, for `p j = q i`. -/
private def minorAt (i j : ZMod 2) (h : p j = q i) : Matrix (Fin (q i)) (Fin (q i)) F :=
  (LinearMap.toMatrix (c j) (c i) (C.d j i).hom).submatrix
    (fun r ↦ Fin.cast (hn i).symm (Fin.castAdd (p i) r))
    (fun k ↦ Fin.cast (hn j).symm (Fin.natAdd (q j) (Fin.cast h.symm k)))

private theorem parityTorsionMinor_eq_minorAt {i j : ZMod 2} (hj : i + 1 = j) (h : p j = q i) :
    parityTorsionMinor c hn hpq i = minorAt c hn i j h := by
  subst hj
  rfl

/-- The splitting of the basis indices of `C.X i` into the first `q i` and the last `p i`. -/
private def splitEquiv (i : ZMod 2) : Fin (q i) ⊕ Fin (p i) ≃ Fin (n i) :=
  finSumFinEquiv.trans (finCongr (hn i).symm)

private theorem splitEquiv_inl (i : ZMod 2) (r : Fin (q i)) :
    splitEquiv hn i (.inl r) = Fin.cast (hn i).symm (Fin.castAdd (p i) r) :=
  rfl

private theorem splitEquiv_inr (i : ZMod 2) (k : Fin (p i)) :
    splitEquiv hn i (.inr k) = Fin.cast (hn i).symm (Fin.natAdd (q i) k) :=
  rfl

/-- The vectors of the block `Dⱼ` of the basis `c j`, indexed by `Fin (q i)`: these are the lifts
of the boundary basis of `Bᵢ = d (Cⱼ)`. -/
private def minorLift (i j : ZMod 2) (h : p j = q i) (r : Fin (q i)) : C.X j :=
  c j (splitEquiv hn j (.inr (Fin.cast h.symm r)))

/-- The family of `Cᵢ` made of the boundaries `d (Dⱼ)` followed by the block `Dᵢ` of `c i`. -/
private def minorFamily (i j : ZMod 2) (h : p j = q i) : Fin (q i) ⊕ Fin (p i) → C.X i :=
  Sum.elim (fun r ↦ (C.d j i).hom (minorLift c hn i j h r)) fun k ↦ c i (splitEquiv hn i (.inr k))

/-- The determinant of `minorFamily` with respect to `c i`, with its indices split, is that of the
square minor: the matrix is block lower triangular with diagonal blocks the minor and the
identity. -/
private theorem det_minorFamily (i j : ZMod 2) (h : p j = q i) :
    ((c i).reindex (splitEquiv hn i).symm).det (minorFamily c hn i j h) =
      (minorAt c hn i j h).det := by
  classical
  rw [Basis.det_apply]
  have : ((c i).reindex (splitEquiv hn i).symm).toMatrix (minorFamily c hn i j h) =
      Matrix.fromBlocks (minorAt c hn i j h) 0
        ((LinearMap.toMatrix (c j) (c i) (C.d j i).hom).submatrix
          (fun k ↦ splitEquiv hn i (.inr k))
          (fun r ↦ splitEquiv hn j (.inr (Fin.cast h.symm r)))) 1 := by
    ext (r | k) (r' | k')
    · simp [Basis.toMatrix_apply, minorFamily, minorLift, minorAt, LinearMap.toMatrix_apply,
        splitEquiv_inl, splitEquiv_inr]
    · simp [Basis.toMatrix_apply, minorFamily]
    · simp [Basis.toMatrix_apply, minorFamily, minorLift, LinearMap.toMatrix_apply]
    · simp [Basis.toMatrix_apply, minorFamily, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

variable {c hn}

private theorem basis_minorFamily {i j : ZMod 2} {h : p j = q i}
    (hA : (minorAt c hn i j h).det ≠ 0) :
    LinearIndependent F (minorFamily c hn i j h) ∧
      Submodule.span F (Set.range (minorFamily c hn i j h)) = ⊤ :=
  (Basis.is_basis_iff_det _).2 (by rw [det_minorFamily]; exact hA.isUnit)

/-- When the square minor of `Cⱼ → Cᵢ` is invertible, `minorFamily` is a basis of `Cᵢ`. -/
private def minorBasis {i j : ZMod 2} {h : p j = q i} (hA : (minorAt c hn i j h).det ≠ 0) :
    Basis (Fin (q i) ⊕ Fin (p i)) F (C.X i) :=
  .mk (basis_minorFamily hA).1 (basis_minorFamily hA).2.ge

private theorem coe_minorBasis {i j : ZMod 2} {h : p j = q i}
    (hA : (minorAt c hn i j h).det ≠ 0) : ⇑(minorBasis hA) = minorFamily c hn i j h :=
  Basis.coe_mk _ _

/-- The boundaries `d (Dⱼ) ⊆ Cᵢ` are linearly independent. -/
private theorem linearIndependent_minorFamily_inl {i j : ZMod 2} {h : p j = q i}
    (hA : (minorAt c hn i j h).det ≠ 0) :
    LinearIndependent F fun r ↦ minorFamily c hn i j h (.inl r) := by
  simpa [Function.comp_def, coe_minorBasis] using
    (minorBasis hA).linearIndependent.comp _ Sum.inl_injective

/-- The differential `Cᵢ → Cⱼ` of `x` only sees the coordinates of `x` along `Dᵢ` in
`minorBasis`, which become coordinates along the boundaries `d (Dᵢ) ⊆ Cⱼ`. -/
private theorem d_eq_sum {i j : ZMod 2} {h₁ : p j = q i} (h₂ : p i = q j)
    (hA : (minorAt c hn i j h₁).det ≠ 0) (x : C.X i) :
    (C.d i j).hom x = ∑ k : Fin (p i), (minorBasis hA).repr x (.inr k) •
      minorFamily c hn j i h₂ (.inl (Fin.cast h₂ k)) := by
  conv_lhs => rw [← (minorBasis hA).sum_repr x]
  simp [Fintype.sum_sum_type, coe_minorBasis, minorFamily, minorLift, d_comp_d_apply]

/-- If the square minors of `Cⱼ → Cᵢ` and of `Cᵢ → Cⱼ` are invertible, then `C` is exact at `i`:
a cycle has no coordinates along `Dᵢ` in `minorBasis`, so it is the boundary of the corresponding
combination of the block `Dⱼ`. -/
private theorem exactAt_of_det_minorAt_ne_zero {i j : ZMod 2} (hij : i + 1 = j)
    {h₁ : p j = q i} {h₂ : p i = q j} (hA₁ : (minorAt c hn i j h₁).det ≠ 0)
    (hA₂ : (minorAt c hn j i h₂).det ≠ 0) : C.ExactAt i := by
  rw [C.exactAt_iff' j i j ((ComplexShape.up _).prev_eq' (hij ▸ CharTwo.add_cancel_right i 1))
      ((ComplexShape.up _).next_eq' hij), ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h0 : ∀ k, (minorBasis hA₁).repr x (.inr k) = 0 := by
    have := (linearIndependent_minorFamily_inl hA₂).comp _ (Fin.cast_injective h₂)
    exact Fintype.linearIndependent_iff.1 this _ ((d_eq_sum h₂ hA₁ x).symm.trans hx)
  refine ⟨∑ r, (minorBasis hA₁).repr x (.inl r) • minorLift c hn i j h₁ r, ?_⟩
  conv_rhs => rw [← (minorBasis hA₁).sum_repr x]
  simp [Fintype.sum_sum_type, h0, coe_minorBasis, minorFamily]

/-- The boundaries `d (Dⱼ)` form a basis of the boundaries `Bᵢ = d (Cⱼ)`. -/
private def minorBoundaryBasis {i j : ZMod 2} {h₁ : p j = q i} {h₂ : p i = q j}
    (hA₁ : (minorAt c hn i j h₁).det ≠ 0) (hA₂ : (minorAt c hn j i h₂).det ≠ 0) :
    Basis (Fin (q i)) F (LinearMap.range (C.d j i).hom) :=
  .mk (v := fun r ↦ ⟨_, LinearMap.mem_range_self _ (minorLift c hn i j h₁ r)⟩)
    (.of_comp (Submodule.subtype _) (linearIndependent_minorFamily_inl hA₁)) <| by
      rintro ⟨_, x, rfl⟩ -
      have : (⟨_, LinearMap.mem_range_self _ x⟩ : LinearMap.range (C.d j i).hom) =
          ∑ k : Fin (p j), (minorBasis hA₂).repr x (.inr k) •
            ⟨_, LinearMap.mem_range_self _ (minorLift c hn i j h₁ (Fin.cast h₁ k))⟩ :=
        Subtype.ext (by simp [d_eq_sum h₁ hA₂ x, minorFamily])
      rw [this]
      exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

private theorem coe_minorBoundaryBasis {i j : ZMod 2} {h₁ : p j = q i} {h₂ : p i = q j}
    (hA₁ : (minorAt c hn i j h₁).det ≠ 0) (hA₂ : (minorAt c hn j i h₂).det ≠ 0) (r : Fin (q i)) :
    (minorBoundaryBasis hA₁ hA₂ r : C.X i) = (C.d j i).hom (minorLift c hn i j h₁ r) := by
  simp [minorBoundaryBasis]

/-- The bracket in degree `i` of the boundary bases `d (Dⱼ)` of `Bᵢ` and `d (Dᵢ)` of `Bⱼ`, with
the lifts `Dᵢ`, is the determinant of the square minor of `Cⱼ → Cᵢ`. -/
private theorem torsionBracket_minorBoundaryBasis {i j : ZMod 2}
    (hi : (ComplexShape.up (ZMod 2)).prev i = j) (hk : (ComplexShape.up (ZMod 2)).next i = j)
    (hex : C.ExactAt i) {h₁ : p j = q i} {h₂ : p i = q j} (hA₁ : (minorAt c hn i j h₁).det ≠ 0)
    (hA₂ : (minorAt c hn j i h₂).det ≠ 0)
    (hs : ∀ l, (C.d i j).hom (minorLift c hn j i h₂ l) = minorBoundaryBasis hA₂ hA₁ l) :
    torsionBracket c hi hk hex (minorBoundaryBasis hA₁ hA₂) (minorBoundaryBasis hA₂ hA₁)
        (minorLift c hn j i h₂) hs = (minorAt c hn i j h₁).det := by
  have hn' : n i = q i + q j := by rw [hn, h₂]
  have hfam : Fin.append (fun k ↦ (minorBoundaryBasis hA₁ hA₂ k : C.X i))
      (minorLift c hn j i h₂) ∘ Fin.cast hn' =
        minorFamily c hn i j h₁ ∘ (splitEquiv hn i).symm := by
    ext k
    obtain ⟨m | m, rfl⟩ := (splitEquiv hn i).surjective k
    · have : Fin.cast hn' (splitEquiv hn i (.inl m)) = Fin.castAdd (q j) m :=
        Fin.ext (by simp [splitEquiv_inl])
      simp [this, coe_minorBoundaryBasis, minorFamily]
    · have : Fin.cast hn' (splitEquiv hn i (.inr m)) = Fin.natAdd (q i) (Fin.cast h₂ m) :=
        Fin.ext (by simp [splitEquiv_inr])
      simp [this, minorFamily, minorLift]
  rw [torsionBracket_eq_det_append c _ _ _ _ _ _ _ hn', hfam, ← Basis.det_reindex,
    det_minorFamily]

/-! ### The square-minor formula -/

variable {hpq}

/-- A two-periodic complex whose two square minors `parityTorsionMinor c hn hpq i` are invertible
is acyclic. -/
theorem acyclic_of_det_parityTorsionMinor_ne_zero
    (hA : ∀ i, (parityTorsionMinor c hn hpq i).det ≠ 0) : C.Acyclic := fun i ↦ by
  have h₂ : p i = q (i + 1) := by simpa [CharTwo.add_cancel_right] using hpq (i + 1)
  refine exactAt_of_det_minorAt_ne_zero (c := c) (hn := hn) rfl (h₁ := hpq i) (h₂ := h₂) ?_ ?_
  · rw [← parityTorsionMinor_eq_minorAt c hn hpq rfl]
    exact hA i
  · rw [← parityTorsionMinor_eq_minorAt c hn hpq (CharTwo.add_cancel_right i 1)]
    exact hA (i + 1)

/-- **The square-minor formula.** Let `C` be a two-periodic complex with bases `c i`, each split by
`hn` into a first block `Eᵢ` of `q i` vectors followed by a second block `Dᵢ` of `p i` vectors,
with `p (i + 1) = q i`. If both square minors `Aᵢ = parityTorsionMinor c hn hpq i` of the
differentials `Cᵢ₊₁ → Cᵢ` are invertible, then the torsion of `C` is `det (A₁) · det (A₀)⁻¹`; the
complex is then acyclic by `acyclic_of_det_parityTorsionMinor_ne_zero`, so this is nonzero. -/
theorem parityTorsion_eq_det_parityTorsionMinor_mul_inv
    (hA : ∀ i, (parityTorsionMinor c hn hpq i).det ≠ 0) :
    C.parityTorsion c =
      (parityTorsionMinor c hn hpq 1).det * ((parityTorsionMinor c hn hpq 0).det)⁻¹ := by
  have h01 : (0 : ZMod 2) + 1 = 1 := zero_add 1
  have h10 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hp₁ : p 1 = q 0 := by simpa [h01] using hpq 0
  have hp₀ : p 0 = q 1 := by simpa [h10] using hpq 1
  have hA₀ : (minorAt c hn 0 1 hp₁).det ≠ 0 := by
    rw [← parityTorsionMinor_eq_minorAt c hn hpq h01]
    exact hA 0
  have hA₁ : (minorAt c hn 1 0 hp₀).det ≠ 0 := by
    rw [← parityTorsionMinor_eq_minorAt c hn hpq h10]
    exact hA 1
  have hs₀ (l : Fin (q 1)) : (C.d 0 1).hom (minorLift c hn 1 0 hp₀ l) =
      minorBoundaryBasis hA₁ hA₀ l := (coe_minorBoundaryBasis hA₁ hA₀ l).symm
  have hs₁ (l : Fin (q 0)) : (C.d 1 0).hom (minorLift c hn 0 1 hp₁ l) =
      minorBoundaryBasis hA₀ hA₁ l := (coe_minorBoundaryBasis hA₀ hA₁ l).symm
  have h := acyclic_of_det_parityTorsionMinor_ne_zero hA
  rw [parityTorsion_eq h (minorBoundaryBasis hA₀ hA₁) (minorBoundaryBasis hA₁ hA₀) _ hs₀ _ hs₁,
    torsionBracket_minorBoundaryBasis, torsionBracket_minorBoundaryBasis,
    parityTorsionMinor_eq_minorAt c hn hpq h01, parityTorsionMinor_eq_minorAt c hn hpq h10]

end HomologicalComplex
