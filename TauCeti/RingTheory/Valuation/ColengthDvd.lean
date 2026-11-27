/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.ColengthDvd
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Colength bounds over a valuation ring

Over a commutative ring `O` in which divisibility is total (`PreValuationRing`), for instance a
valuation domain, a submodule of `O ^ ι` that contains the image of a square matrix `A`
has colength dividing `det A`, in the sense of `Submodule.ColengthDvd` (`M ⊸_z N`: every finite
family in `M` is carried into `N` by a square matrix whose determinant divides `z`). The ring need
not be noetherian: an example is the valuation ring `{z : |ι z| ≤ 1}` of `ℂ` for a field
isomorphism `ι : ℂ ≃ PadicAlgCl ℓ`, with the absolute value of `PadicAlgCl ℓ` pulled back.

## Main results

* `Submodule.ColengthDvd.of_det_dvd`: if `det A ∣ z` and `L` contains the image of `A`, then
  `O ^ ι ⊸_z L`. This rests on the Smith normal form over such a ring,
  `Matrix.exists_mul_mul_eq_diagonal_of_preValuationRing`.
* `Submodule.colengthDvd_inf_comap_span`: for a linear form `f`, `M ⊸_a {v ∈ M : a ∣ f v}`.
* `Submodule.colengthDvd_top_smul_top`: `O ^ ι ⊸_{a ^ #ι} a • O ^ ι`.
* `Submodule.colengthDvd_sup_span`: `(N + span S) ⊸_{z ^ #S} (N + z • V)` for a finite set `S`.

## References

Adapted from the formal proof of the Riemann hypothesis for Dirichlet L-functions in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at commit
72fead102f663d5c7a407964a13dc0cf9d977207, file `grh/src/New/Reduction/Lattices/Colength.lean`
(`New.ColengthDvd.of_det_dvd`, `New.colengthDvd_inf_comap_span`, `New.colengthDvd_top_smul_top`,
`New.colengthDvd_sup_span`).
-/

public section

open Matrix Finset Pointwise

namespace Submodule

variable {O V ι : Type*} [CommRing O] [PreValuationRing O] [AddCommGroup V] [Module O V] {z : O}

/-- Over a commutative ring with total divisibility, the vectors of `M` on which a linear form `f`
is divisible by `a` have colength dividing `a` in `M`. -/
theorem colengthDvd_inf_comap_span (M : Submodule O V) (f : V →ₗ[O] O) (a : O) :
    ColengthDvd M (M ⊓ Submodule.comap f (Ideal.span {a})) a := by
  refine colengthDvd_iff.2 fun n Φ hΦ ↦ ?_
  obtain rfl | hn := n.eq_zero_or_pos
  · exact ⟨1, by simp, finZeroElim⟩
  -- take a member `Φ p` whose value divides the others, subtract multiples of it from them to
  -- clear their values, and multiply it by `a`
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨p, hp⟩ := TauCeti.PreValuationRing.exists_forall_dvd fun k ↦ f (Φ k)
  choose c hc using hp
  let m : Matrix (Fin n) (Fin n) O := updateCol 1 p fun i ↦ if i = p then a else -c i
  have h_det : m.det = a := by simp [m, ← cramer_apply, cramer_one]
  have h_comb (i : Fin n) : ∑ k, m i k • Φ k = if i = p then a • Φ p else Φ i - c i • Φ p := by
    obtain rfl | hip := eq_or_ne i p
    · rw [Fintype.sum_eq_single i] <;> simp +contextual [m, eq_comm]
    · rw [Fintype.sum_eq_add i p hip] <;>
        simp +contextual [m, hip, Ne.symm hip, sub_eq_add_neg, eq_comm]
  refine ⟨m, h_det.dvd, fun i ↦ ⟨sum_smul_mem M _ fun k _ ↦ hΦ k, ?_⟩⟩
  rw [SetLike.mem_coe, mem_comap, h_comb]
  split_ifs <;> simp [Ideal.mem_span_singleton, hc i, mul_comm]

/-- **The image of a square matrix.** Over a commutative ring with total divisibility, if a square
matrix `A` has `det A ∣ z` and the submodule `L` of `ι → O` contains its image, then
`O ^ ι ⊸_z L`.

The proof writes `A` in diagonal form `L₀ * A * Q₀ = diagonal d` and imposes the conditions
`d j ∣ (L₀ x) j` one coordinate at a time, each of colength dividing `d j`. -/
theorem ColengthDvd.of_det_dvd [Fintype ι] [DecidableEq ι] {A : Matrix ι ι O}
    {L : Submodule O (ι → O)} (h_dvd : A.det ∣ z) (h_le : LinearMap.range A.mulVecLin ≤ L) :
    ColengthDvd ⊤ L z := by
  obtain ⟨L₀, Q₀, d, hL₀, hQ₀, h⟩ := exists_mul_mul_eq_diagonal_of_preValuationRing A
  let f (j : ι) : (ι → O) →ₗ[O] O := .proj j ∘ₗ L₀.mulVecLin
  let S (s : Finset ι) : Submodule O (ι → O) := ⨅ j ∈ s, Submodule.comap (f j) (Ideal.span {d j})
  -- each further coordinate condition costs `d j`
  have h_chain (s : Finset ι) : ColengthDvd ⊤ (S s) (∏ j ∈ s, d j) := by
    induction s using Finset.induction with
    | empty => simp [S]
    | insert j s hj ih =>
      simpa only [S, Finset.iInf_insert, inf_comm, prod_insert hj, mul_comm] using
        ih.trans (colengthDvd_inf_comap_span _ (f j) (d j))
  -- the last submodule lies in the image of `A = L₀⁻¹ * diagonal d * Q₀⁻¹`
  have h_image : S univ ≤ LinearMap.range A.mulVecLin := by
    intro x hx
    simp only [S, mem_iInf, mem_univ, forall_const] at hx
    choose w hw using fun j ↦ Ideal.mem_span_singleton.1 (hx j)
    have hA : A = L₀⁻¹ * diagonal d * Q₀⁻¹ := by
      rw [← h]
      simp [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hL₀, mul_nonsing_inv _ hQ₀]
    have h_diag : diagonal d *ᵥ w = L₀ *ᵥ x :=
      funext fun j ↦ by simpa [f, mulVec_diagonal] using (hw j).symm
    refine ⟨Q₀ *ᵥ w, ?_⟩
    calc A *ᵥ (Q₀ *ᵥ w) = L₀⁻¹ *ᵥ (diagonal d *ᵥ w) := by
          simp only [hA, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hQ₀, Matrix.mul_one]
      _ = x := by
          rw [h_diag]
          simp [mulVec_mulVec, nonsing_inv_mul _ hL₀]
  have h_assoc : Associated A.det (∏ j, d j) := by
    rw [← det_diagonal, ← h, det_mul, det_mul, mul_comm L₀.det, mul_assoc]
    exact associated_mul_unit_right _ _ (hL₀.mul hQ₀)
  have h_prod : ∏ j, d j ∣ z := h_assoc.symm.dvd.trans h_dvd
  simpa using ((h_chain univ).trans_dvd h_prod).trans (.of_le (h_image.trans h_le))

/-- Over a commutative ring with total divisibility, `a • O ^ ι` has colength dividing `a ^ #ι` in
`O ^ ι`. -/
theorem colengthDvd_top_smul_top [Fintype ι] (a : O) :
    ColengthDvd (⊤ : Submodule O (ι → O)) (a • ⊤) (a ^ Fintype.card ι) := by
  classical
  refine .of_det_dvd (A := a • (1 : Matrix ι ι O)) (by simp) ?_
  rintro _ ⟨v, rfl⟩
  simpa [smul_mulVec] using smul_mem_pointwise_smul v a ⊤ mem_top

/-- Over a commutative ring with total divisibility, for a submodule `N` and a finite set `s` of
vectors, the colength of `N + z • V` in `N + span s` divides `z ^ #s`. -/
theorem colengthDvd_sup_span (N : Submodule O V) (s : Finset V) (z : O) :
    ColengthDvd (N ⊔ span O (s : Set V)) (N ⊔ z • ⊤) (z ^ #s) := by
  -- push the bound for `z • O ^ s` in `O ^ s` forward along the map to linear combinations
  classical
  let comb : (s → O) →ₗ[O] V := Fintype.linearCombination O fun v : s ↦ (v : V)
  have h_range : (⊤ : Submodule O (s → O)).map comb = span O s := by
    simp [comb, Fintype.range_linearCombination]
  have h_free : ColengthDvd (⊤ : Submodule O (s → O)) (z • ⊤) (z ^ #s) := by
    simpa using colengthDvd_top_smul_top (ι := s) z
  refine h_free.map comb (by rw [h_range, sup_comm]; exact sup_le_sup_left le_sup_left _) ?_
  rw [map_pointwise_smul]
  exact le_sup_of_le_right (smul_mono_right z le_top)

end Submodule
