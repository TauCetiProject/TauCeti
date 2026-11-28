/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Module.FunctionModule
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.MatlisDuality.PrincipalIdealRing

/-!
# Fitting-ideal determinant decompositions and coordinate elimination

This file supplies three linear-algebraic bridges used in constructing tied character rows for
Ribet's method:
1. Every element of the top `minorsIdeal` of an image submodule `N.map f ≤ (ι → R)` is an
   `R`-linear combination of determinants of square matrices whose rows are images of elements of
   `N`.
2. Over a principal ideal domain `O`, if the function module of `N` on the `S₀`-coordinates is
   detected by a finite set `s`, then `N` contains rows mapping under a character `η` to the
   standard unit vectors on `S₀`.
3. Given unit rows on `S₀` under `η`, subtracting multiples of them eliminates the `S₀`-coordinates
   of any row of `N` and expresses the resulting `S`-coordinates via a block elimination matrix.

## Main results

* `TauCeti.exists_sum_mul_det_of_mem_minorsIdeal_map`: linear combination of determinants of
  `N`-row images for elements of `(N.map f).minorsIdeal (Fintype.card ι)`.
* `TauCeti.exists_unit_row_of_isDetectedBy`: unit rows on `S₀` from `Submodule.IsDetectedBy`.
* `TauCeti.exists_row_apply_eq_zero`: Gaussian elimination of `S₀`-coordinates in `N`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/FittingBlock.lean`
(`New.Selmer.exists_sum_mul_det_of_mem_fittingIdeal_map`, `New.Selmer.exists_unit_row`,
`New.Selmer.exists_row_apply_eq_zero`) in <https://github.com/lsernau/grh-lean> at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Matrix Submodule Sum

/-- An element of `(N.map f).minorsIdeal (Fintype.card ι)` is a finite linear combination of
determinants of `ι × ι` matrices whose rows are images under `f` of elements of `N`. -/
theorem exists_sum_mul_det_of_mem_minorsIdeal_map {R ι M : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] [AddCommGroup M] [Module R M] {N : Submodule R M} {f : M →ₗ[R] ι → R} {d : R}
    (hd : d ∈ (N.map f).minorsIdeal (Fintype.card ι)) :
    ∃ (l : ℕ) (w : Fin l → R) (B : Fin l → Matrix ι ι R) (B' : Fin l → ι → M),
      (∀ (i : Fin l) (j : ι), B' i j ∈ N) ∧
      (∀ (i : Fin l) (j : ι), f (B' i j) = B i j) ∧
      ∑ i : Fin l, w i * (B i).det = d := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let I : Ideal R := Ideal.span (Matrix.det '' {B : Matrix ι ι R | ∀ j : ι, B j ∈ N.map f})
  have hle : (N.map f).minorsIdeal (Fintype.card ι) ≤ I := by
    refine Submodule.minorsIdeal_le_iff.mpr fun φ v hv ↦ ?_
    let B : Matrix ι ι R := Matrix.of fun a j ↦ v (e a) j
    let Φ : Matrix ι ι R := Matrix.of fun a j ↦ φ (e j) (Pi.single a 1)
    have hmul : (Matrix.of fun i j ↦ φ j (v i)).submatrix e e = B * Φ := by
      ext a j
      simp only [submatrix_apply, of_apply, Matrix.mul_apply, B, Φ]
      conv_lhs => rw [pi_eq_sum_univ' (v (e a)), map_sum]
      simp [map_smul, smul_eq_mul]
    rw [← Matrix.det_submatrix_equiv_self e, hmul, Matrix.det_mul, mul_comm]
    exact I.mul_mem_left Φ.det (Ideal.subset_span ⟨B, fun a ↦ hv (e a), rfl⟩)
  obtain ⟨l, w, D, hw⟩ := Submodule.mem_span_set'.mp (hle hd)
  choose B hB hB_det using fun k : Fin l ↦ (D k).property
  choose B' hB' hB'_eq using fun k j ↦ Submodule.mem_map.mp (hB k j)
  exact ⟨l, w, B, B', hB', hB'_eq, by simp [hB_det, ← hw]⟩

/-- Let `η : A →ₐ[Λ] Λ` be a character and `p ≠ 0` in a principal ideal domain `O`. If `N` holds
`p` times every row and `v (z (gen i)) - Pi.single i 1` for each `i`, with `gen` the identity on
`s`, and if the function module of `(N.restrictScalars Λ).map E` on `S₀`-coordinates is detected by
`s`, then for each `i : S₀` some row `w ∈ N` maps under `η` to the unit vector `i` on `S₀`. -/
theorem exists_unit_row_of_isDetectedBy {O G Λ A W S₀ : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing Λ] [Algebra O Λ] [Ring A] [Algebra Λ A] [Algebra O A]
    [IsScalarTower O Λ A] [Finite W] [Finite S₀] [DecidableEq W] [DecidableEq S₀] [DecidableEq G]
    {s : Finset G} (η : A →ₐ[Λ] Λ) (N : Submodule A (W ⊕ S₀ ⊕ s → A))
    (v : (W ⊕ S₀ ⊕ s → O) →ₗ[O] W ⊕ S₀ ⊕ s → A) (gen : W ⊕ S₀ ⊕ s → G) (z : G → W ⊕ S₀ ⊕ s → O)
    {p : O} (hp : p ≠ 0) (h_p : ∀ w : W ⊕ S₀ ⊕ s → A, p • w ∈ N)
    (h_gen : ∀ i : W ⊕ S₀ ⊕ s, v (z (gen i)) - Pi.single i 1 ∈ N)
    (h_gen_s : ∀ j : s, gen (inr (inr j)) = j) (E : (W ⊕ S₀ ⊕ s → A) →ₗ[Λ] S₀ → Λ)
    (hE : ∀ (w : W ⊕ S₀ ⊕ s → A) (j : S₀), E w j = η (w (inr (inl j))))
    (h_detect :
      (((N.restrictScalars Λ).map E).functionModule (E.restrictScalars O ∘ₗ v) z p).IsDetectedBy
        (s : Set G))
    (i : S₀) :
    ∃ w ∈ N, ∀ j : S₀, η (w (inr (inl j))) = if j = i then 1 else 0 := by
  let K : Submodule Λ (S₀ → Λ) := (N.restrictScalars Λ).map E
  have hK {w : W ⊕ S₀ ⊕ s → A} (hw : w ∈ N) : E w ∈ K := Submodule.mem_map_of_mem hw
  have hK_p (m : W ⊕ S₀ ⊕ s → O) : E (v (p • m)) ∈ K := hK (by simpa using h_p (v m))
  have hK_s (g : s) : E (v (z g)) ∈ K := by
    have h_unit : E (Pi.single (inr (inr g)) 1) = 0 := funext fun j ↦ by simp [hE]
    simpa [h_gen_s, h_unit] using hK (h_gen (inr (inr g)))
  have hK_i : E (v (z (gen (inr (inl i))))) ∈ K := by
    by_contra hnot
    let C : Submodule O (W ⊕ S₀ ⊕ s → O) := (K.restrictScalars O).comap (E.restrictScalars O ∘ₗ v)
    obtain ⟨Ψ, hΨ⟩ := TauCeti.exists_linearMap_quotient_span_singleton_apply_ne_zero hp
      (smul_quotient_comap_eq_zero hK_p) (x := C.mkQ (z (gen (inr (inl i)))))
      (by simpa [C, Submodule.Quotient.mk_eq_zero] using hnot)
    have hmem : (fun g ↦ Ψ (C.mkQ (z g))) ∈ K.functionModule (E.restrictScalars O ∘ₗ v) z p :=
      K.apply_mkQ_mem_functionModule Ψ
    have hzero : (fun g ↦ Ψ (C.mkQ (z g))) = 0 :=
      Submodule.isDetectedBy_iff.mp h_detect _ hmem fun g hg ↦ by
      have hzg : z g ∈ C := hK_s ⟨g, hg⟩
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hzg]
    exact hΨ (congrFun hzero (gen (inr (inl i))))
  have hK_unit : E (Pi.single (inr (inl i)) 1) ∈ K := by
    simpa using K.sub_mem hK_i (hK (h_gen (inr (inl i))))
  obtain ⟨w, hw, hw_eq⟩ := Submodule.mem_map.mp hK_unit
  exact ⟨w, hw, fun j ↦ by simpa [hE, Pi.single_apply] using congrFun hw_eq j⟩

/-- Clearing the `S₀`-coordinates in `N`: given rows `ν i ∈ N` mapping under `η` to the unit
vectors on `S₀`, subtracting `∑ i, w (inr (inl i)) • ν i` from `w ∈ N` yields a row `w' ∈ N`
vanishing under `η` on `S₀` whose `S`-coordinates are given by the elimination matrix. -/
theorem exists_row_apply_eq_zero {Λ A W S₀ S : Type*} [CommRing Λ] [Ring A] [Algebra Λ A]
    [Fintype S₀] [DecidableEq S₀] [Fintype S] [DecidableEq S] (η : A →ₐ[Λ] Λ)
    {N : Submodule A (W ⊕ S₀ ⊕ S → A)} {ν : S₀ → W ⊕ S₀ ⊕ S → A} (hν : ∀ i : S₀, ν i ∈ N)
    (hν_eq : ∀ i j : S₀, η (ν i (inr (inl j))) = if j = i then 1 else 0)
    {w : W ⊕ S₀ ⊕ S → A} (hw : w ∈ N) :
    ∃ w' ∈ N,
      (∀ i : S₀, η (w' (inr (inl i))) = 0) ∧
      (fun j : S ↦ η (w' (inr (inr j)))) =
        Matrix.vecMulLinear
          (fromRows (-Matrix.of fun (i : S₀) (j : S) ↦ η (ν i (inr (inr j)))) (1 : Matrix S S Λ))
          fun l : S₀ ⊕ S ↦ η (w (inr l)) := by
  refine ⟨w - ∑ i : S₀, w (inr (inl i)) • ν i,
    sub_mem hw (sum_mem fun i _ ↦ N.smul_mem _ (hν i)), fun i ↦ ?_, funext fun j ↦ ?_⟩
  · simp [hν_eq]
  · simp [vecMul_eq_sum, Matrix.one_apply, sub_eq_neg_add]

end TauCeti
