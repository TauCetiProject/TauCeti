/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basis completion with a covolume budget

Complete an independent family to a basis using short vectors from a set that spans modulo
that family. The added vectors cost at most their number times the common logarithmic bound
on their squared lengths. The estimate is uniform under complex field automorphisms applied
to the rational metric's coordinates. The added vectors stay in the prescribed set, which
can also impose arithmetic conditions on them.

This is the archimedean basis-completion step of `New.Data.integral_forms_long` in
`grh/src/New/Determinant/Twist/LongForms.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Matrix Set Submodule
open scoped ComplexOrder

namespace LinearIndependent

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
