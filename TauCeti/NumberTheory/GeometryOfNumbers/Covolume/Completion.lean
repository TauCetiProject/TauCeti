/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Archimedean bounds for completed Gram determinants and basis completion

A covolume bound for a family in rational coordinates, together with squared-length bounds
for the additional vectors in those coordinates, controls every field conjugate of the
ordinary Gram determinant of the enlarged family. This lets a product-formula argument use
that determinant as a single complex number, without requiring field automorphisms to
commute with complex conjugation.

The completion estimate is the archimedean step of `New.TwistedLattice.covolume_add_index_nonneg`
in `New/Reduction/Lattices/TwistedLattice.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).

An independent family can be completed to a basis using short vectors from a set
that spans modulo that family. The added vectors cost at most their number times the common
logarithmic bound on their squared lengths, uniformly under complex field automorphisms applied
to the rational metric's coordinates. The added vectors stay in the prescribed set, which can
also impose arithmetic conditions on them. This is the archimedean basis-completion step of
`New.Data.integral_forms_long` in `grh/src/New/Determinant/Twist/LongForms.lean` of
lsernau/grh-lean (`72fead1`).
-/

public section

open scoped ComplexOrder InnerProductSpace

namespace Matrix

/-- Complete a family `y` by adjoining `z`. If the coordinates represent the inner product
by a rational positive semidefinite matrix, every field conjugate of the completed Gram
determinant is bounded by `exp (c + ∑ j, b j)`. Here `c` bounds the logarithmic squared covolume
of the first family, and `exp (b j)` bounds the squared length of each additional coordinate
vector after every field automorphism. No independence or spanning assumption is required. -/
theorem norm_map_det_gram_sumElim_le {E m n p : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Fintype m] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) (coord : E → m → ℂ)
    (hcoord : ∀ x y, ⟪x, y⟫_ℂ = star (coord x) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ coord y))
    {y : n → E} {z : p → E} {c : ℝ} {b : p → ℝ}
    (hy : (Matrix.of fun i j ↦ coord (y j) i).CovolumeLE G c)
    (hz : ∀ (τ : ℂ ≃+* ℂ) j, let v := τ ∘ coord (z j)
      (star v ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ v)).re ≤ Real.exp (b j)) (σ : ℂ ≃+* ℂ) :
    ‖σ (Matrix.gram ℂ (Sum.elim y z)).det‖ ≤ Real.exp (c + ∑ j, b j) := by
  let A : Matrix m n ℂ := Matrix.of fun i j ↦ coord (y j) i
  let B : Matrix m p ℂ := Matrix.of fun i j ↦ coord (z j) i
  let H := G.map (algebraMap ℚ ℂ)
  have hB : B.CovolumeLE G (∑ j, b j) := by
    apply covolumeLE_sum_of_forall_norm_diag_le hG
    intro τ j
    let v := τ ∘ coord (z j)
    have hv : (B.map τ).col j = v := (rfl)
    have hn : ‖star v ⬝ᵥ (H *ᵥ v)‖ = (star v ⬝ᵥ (H *ᵥ v)).re := by
      simpa only [Complex.ofReal_re] using
        congrArg Complex.re (Complex.norm_of_nonneg' (hG.dotProduct_mulVec_nonneg v))
    rw [conjTranspose_mul_mul_apply (B.map τ) _ (B.map τ) j j, hv, hn]
    exact hz τ j
  have hAB (j : n ⊕ p) : (fromCols A B).col j = coord (Sum.elim y z j) := by
    cases j <;> rfl
  have hgram : Matrix.gram ℂ (Sum.elim y z) = (fromCols A B)ᴴ * H * fromCols A B := by
    ext i j
    rw [Matrix.gram_apply, hcoord, conjTranspose_mul_mul_apply, hAB, hAB]
  rw [hgram]
  exact (hy.fromCols hB hG).norm_map_det_conjTranspose_mul_mul_le hG σ

end Matrix

namespace LinearIndependent

open Matrix Set Submodule

/-- An independent family with logarithmic squared covolume at most `c` can be kept as the
first block of a basis. If the auxiliary set spans modulo this family and its vectors have
conjugated squared lengths at most `exp h`, one can choose the remaining basis vectors from
that set and pay at most `h` per added vector in the covolume bound. -/
theorem exists_basis_completion_of_covolumeLE {V m ι : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Fintype m] [Fintype ι] [DecidableEq ι]
    {y : ι → V} (hy : LinearIndependent ℂ y) {S : Set V} (hS : span ℂ (range y ∪ S) = ⊤)
    (coord : V → m → ℂ) {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) {c h : ℝ}
    (hc : (of fun a i ↦ coord (y i) a).CovolumeLE G c)
    (hshort : ∀ v ∈ S, ∀ σ : ℂ ≃+* ℂ,
      ‖dotProduct (star (σ ∘ coord v)) ((G.map (algebraMap ℚ ℂ)) *ᵥ (σ ∘ coord v))‖ ≤
        Real.exp h) :
    let k := Module.finrank ℂ V - Fintype.card ι
    ∃ b : Module.Basis (ι ⊕ Fin k) ℂ V,
      (∀ i, b (.inl i) = y i) ∧ (∀ j, b (.inr j) ∈ S) ∧
      (of fun a i ↦ coord (b i) a).CovolumeLE G (c + k * h) := by
  classical
  intro k
  -- Extend in the union, then identify the difference with the new block of indices.
  let hs : range y ⊆ range y ∪ S := subset_union_left
  let B := Module.Basis.extendLe hy.linearIndepOn_id hs hS.ge
  let U := hy.linearIndepOn_id.extend hs
  let T := U \ range y
  let e : ι ⊕ T ≃ U :=
    (Equiv.sumCongr (Equiv.ofInjective y hy.injective) (Equiv.refl T)).trans
      (Equiv.Set.sumDiffSubset (hy.linearIndepOn_id.subset_extend hs))
  let : Finite U := Module.Finite.finite_basis B
  let : Fintype T := Fintype.ofFinite _
  let b₀ := B.reindex e.symm
  have hcard := Module.finrank_eq_card_basis b₀
  rw [Fintype.card_sum] at hcard
  have hk : Fintype.card T = k := by dsimp only [k]; omega
  let b := b₀.reindex (Equiv.sumCongr (Equiv.refl ι) (Fintype.equivFinOfCardEq hk))
  have hinl (i : ι) : b (.inl i) = y i := by
    simp [b, b₀, B, e, Equiv.Set.sumDiffSubset]
  have hinr (j : Fin k) : b (.inr j) ∈ S := by
    let t : T := (Fintype.equivFinOfCardEq hk).symm j
    have heq : b (.inr j) = (t : V) := by
      simp [b, b₀, B, e, t, Equiv.Set.sumDiffSubset]
    rw [heq]
    exact ((hy.linearIndepOn_id.extend_subset hs) t.property.1).resolve_left t.property.2
  refine ⟨b, hinl, hinr, ?_⟩
  let A : Matrix m ι ℂ := of fun a i ↦ coord (y i) a
  let C : Matrix m (Fin k) ℂ := of fun a j ↦ coord (b (.inr j)) a
  have hC : C.CovolumeLE G (k * h) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (covolumeLE_sum_of_forall_norm_diag_le (A := C) (b := fun _ ↦ h) hG fun σ j ↦ by
        rw [Matrix.mul_assoc, Matrix.mul_apply]
        simpa only [C, Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, map_apply,
          of_apply, Pi.star_apply, Function.comp_apply] using hshort _ (hinr j) σ)
  have hb : (of fun a i ↦ coord (b i) a) = fromCols A C := by
    ext a (i | j)
    · simp [A, hinl]
    · simp [C]
  rw [hb]
  exact hc.fromCols hC hG

end LinearIndependent
