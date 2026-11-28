/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Character separation and simultaneous unit rows over an algebra

For finitely many `Λ`-algebra characters `χ : E → A →ₐ[Λ] Λ` of a `Λ`-algebra `A`, this file
glues character-wise unit rows and block-triangular determinant matrices in a relation submodule
`N ≤ (ι → A)` across all characters simultaneously, and constructs Lagrange separating elements
from products of character value differences.

## Main results

* `TauCeti.exists_common_unit_row`: glues character-wise unit rows in `N` into a single row that
  acts as the unit vector on all characters simultaneously.
* `TauCeti.exists_rows_det_eq_pow_mul_det`: assembles a square matrix with rows in `N` whose
  determinant under each `χ e` is `μ e ^ Fintype.card ι * (B e).det`.
* `TauCeti.exists_forall_eq_one_and_forall_eq_zero`: multiplies elements that are `1` on all
  characters `η e` and `0` on individual homomorphisms `ψ x` into one common element.
* `TauCeti.exists_apply_eq_ite_of_prod_dvd`: Lagrange separation for finitely many characters from
  `∏ k ∈ {e}ᶜ, (η e a - η k a) ∣ c`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/FittingBlock.lean`
(`New.Selmer.exists_common_unit_row`, `New.Selmer.exists_rows_det_eq_pow_mul_det`,
`New.Selmer.exists_forall_eq_one_and_forall_eq_zero`,
`New.Selmer.exists_apply_eq_ite_of_prod_dvd`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Matrix Polynomial

/-- Let `N` be a submodule of `ι → A`, `η e` finitely many `Λ`-algebra characters of `A`, and
`c : κ → ι` finitely many coordinates. If for each `e` and each `i` some `w ∈ N` has coordinates
`w (c j)` sent by `η e` to the unit vector `i`, then one `w ∈ N` does so for all `e` at once. -/
theorem exists_common_unit_row {Λ A E ι κ : Type*} [CommRing Λ] [Ring A] [Algebra Λ A]
    [Finite E] [Finite κ] [DecidableEq κ] (η : E → A →ₐ[Λ] Λ) (N : Submodule A (ι → A))
    (c : κ → ι)
    (h_unit : ∀ (e : E) (i : κ), ∃ w ∈ N, ∀ j : κ, η e (w (c j)) = if j = i then 1 else 0)
    (i : κ) :
    ∃ w ∈ N, ∀ (e : E) (j : κ), η e (w (c j)) = if j = i then 1 else 0 := by
  classical
  cases nonempty_fintype E
  cases nonempty_fintype κ
  choose m hm hm_eq using h_unit
  suffices ∃ w ∈ N, ∀ e ∈ (univ : Finset E), ∀ j : κ, η e (w (c j)) = if j = i then 1 else 0 by
    simpa
  induction (univ : Finset E) using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert e s _ ih =>
    obtain ⟨w, hw, hw_eq⟩ := ih
    let w' : ι → A := w + ∑ j : κ, ((if j = i then 1 else 0) - w (c j)) • m e j
    have hw' : w' ∈ N := add_mem hw (sum_mem fun j _ ↦ N.smul_mem _ (hm e j))
    have h_new (j : κ) : η e (w' (c j)) = if j = i then 1 else 0 := by simp [w', hm_eq]
    have h_old (e' : E) (he' : e' ∈ s) (j : κ) : η e' (w' (c j)) = if j = i then 1 else 0 := by
      simp [w', hw_eq e' he']
    exact ⟨w', hw', (forall_mem_insert ..).mpr ⟨h_new, h_old⟩⟩

/-- Given characters `χ : E → R →ₐ[Λ] Λ` with separating elements `π e` (`χ e' (π e) = μ e` if
`e' = e`, else `0`), a submodule `N ≤ (ι₀ ⊕ ι → R)` having unit rows on `ι₀` under each `χ e`,
and matrices `B e` realized on `ι` by rows of `N` vanishing on `ι₀` under `χ e`, there is a square
matrix `M` with rows in `N` such that `(M.map (χ e)).det = μ e ^ Fintype.card ι * (B e).det`. -/
theorem exists_rows_det_eq_pow_mul_det {Λ R E ι₀ ι : Type*} [CommRing Λ] [Ring R] [Algebra Λ R]
    [Finite E] [DecidableEq E] [Fintype ι₀] [DecidableEq ι₀] [Fintype ι] [DecidableEq ι]
    (χ : E → R →ₐ[Λ] Λ) {π : E → R} {μ : E → Λ}
    (hπ : ∀ e e' : E, χ e' (π e) = if e' = e then μ e else 0) (N : Submodule R (ι₀ ⊕ ι → R))
    (h_gen : ∀ (e : E) (i : ι₀), ∃ w ∈ N, ∀ j : ι₀, χ e (w (.inl j)) = if j = i then 1 else 0)
    (B : E → Matrix ι ι Λ)
    (hB : ∀ (e : E) (l : ι), ∃ w ∈ N,
      (∀ j : ι₀, χ e (w (.inl j)) = 0) ∧ ∀ i : ι, χ e (w (.inr i)) = B e l i) :
    ∃ M : Matrix (ι₀ ⊕ ι) (ι₀ ⊕ ι) R,
      (∀ k : ι₀ ⊕ ι, M k ∈ N) ∧
      ∀ e : E, (M.map (χ e)).det = μ e ^ Fintype.card ι * (B e).det := by
  classical
  cases nonempty_fintype E
  choose w hw hw_zero hw_eq using hB
  choose v hv hv_eq using fun i : ι₀ ↦ exists_common_unit_row χ N Sum.inl h_gen i
  let M : Matrix (ι₀ ⊕ ι) (ι₀ ⊕ ι) R := Sum.elim v fun l ↦ ∑ e', π e' • w e' l
  have h_first (e : E) (i j : ι₀) : χ e (M (.inl i) (.inl j)) = if j = i then 1 else 0 :=
    hv_eq i e j
  have h_last (e : E) (l : ι) (k : ι₀ ⊕ ι) : χ e (M (.inr l) k) = μ e * χ e (w e l k) := by
    simp [M, Finset.sum_apply, hπ]
  refine ⟨M, fun k ↦ ?_, fun e ↦ ?_⟩
  · rcases k with i | l
    · exact hv i
    · exact sum_mem fun e' _ ↦ N.smul_mem _ (hw e' l)
  · have h_blocks : M.map (χ e) = fromBlocks 1 ((M.map (χ e)).toBlocks₁₂) 0 (μ e • B e) := by
      ext (i | l) (j | j)
      · simp [h_first, Matrix.one_apply, eq_comm (a := i)]
      · rfl
      · simp [h_last, hw_zero]
      · simp [h_last, hw_eq]
    rw [h_blocks, det_fromBlocks_zero₂₁, det_one, one_mul, det_smul]

/-- If each of finitely many algebra homomorphisms `ψ x` kills an element on which all characters
`η e` take the value `1`, then a single element is `1` under all `η e` and `0` under all `ψ x`. -/
theorem exists_forall_eq_one_and_forall_eq_zero {Λ A B E I : Type*} [CommSemiring Λ] [Semiring A]
    [Semiring B] [Algebra Λ A] [Algebra Λ B] [Finite I] (η : E → A →ₐ[Λ] Λ) (ψ : I → A →ₐ[Λ] B)
    (h_each : ∀ x : I, ∃ k : A, (∀ e : E, η e k = 1) ∧ ψ x k = 0) :
    ∃ k : A, (∀ e : E, η e k = 1) ∧ ∀ x : I, ψ x k = 0 := by
  classical
  cases nonempty_fintype I
  suffices ∃ k : A, (∀ e : E, η e k = 1) ∧ ∀ x ∈ (univ : Finset I), ψ x k = 0 by simpa
  induction (univ : Finset I) using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert x s _ ih =>
    obtain ⟨k, hkη, hkψ⟩ := ih
    obtain ⟨k', hk'η, hk'ψ⟩ := h_each x
    exact ⟨k * k', by simp [hkη, hk'η], by simp +contextual [hkψ, hk'ψ]⟩

/-- For finitely many characters `η : E → A →ₐ[Λ] Λ` and `a : A`, if `c` is a multiple of
`∏ k ∈ {e}ᶜ, (η e a - η k a)`, then some `q : A` satisfies `η e' q = if e' = e then c else 0`. -/
theorem exists_apply_eq_ite_of_prod_dvd {Λ A E : Type*} [CommRing Λ] [Ring A] [Algebra Λ A]
    [Fintype E] [DecidableEq E] (η : E → A →ₐ[Λ] Λ) (a : A) {e : E} {c : Λ}
    (hc : ∏ k ∈ ({e}ᶜ : Finset E), (η e a - η k a) ∣ c) :
    ∃ q : A, ∀ e' : E, η e' q = if e' = e then c else 0 := by
  obtain ⟨w, rfl⟩ := hc
  let P : Λ[X] := ∏ k ∈ ({e}ᶜ : Finset E), (X - Polynomial.C (η k a))
  refine ⟨w • aeval a P, fun e' ↦ ?_⟩
  have h_value : η e' (w • aeval a P) = w * ∏ k ∈ ({e}ᶜ : Finset E), (η e' a - η k a) := by
    rw [map_smul, ← aeval_algHom_apply]
    simp [P]
  rw [h_value]
  split_ifs with he
  · rw [he, mul_comm]
  · rw [prod_eq_zero (i := e') (by simpa using he) (sub_self _), mul_zero]

end TauCeti
