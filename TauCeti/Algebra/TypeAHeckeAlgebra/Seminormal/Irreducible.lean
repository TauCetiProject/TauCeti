/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Combinatorics.Young.StandardTableau.Swap

/-!
# Absolute irreducibility of the seminormal representations

Let `K` be a field, `q : Kˣ` and `Q = q ^ 2`, and let `μ` be a Young diagram with `n` cells. Under
the split-semisimplicity criterion that the `Q`-integers `[d]_Q`, `0 < d ≤ n`, are nonzero, the
seminormal representation `TauCeti.TypeAHeckeAlgebra.seminormalRep` of `H_n(q)` on the functions
on the standard tableaux of shape `μ` is onto the whole endomorphism algebra
(`TauCeti.TypeAHeckeAlgebra.seminormalRep_surjective`). This is the strong, absolute form of
irreducibility; in particular the only invariant subspaces are `⊥` and `⊤`
(`TauCeti.TypeAHeckeAlgebra.eq_bot_or_eq_top_of_seminormalRep_mem`).

The image contains every matrix unit of the tableau basis:

* the vectors `v_U` of the standard tableaux `U` are eigenvectors of the additive Jucys–Murphy
  elements `L_i`, with eigenvalues the additive contents `[content i]_Q`. A standard tableau is
  determined by the contents of its labels (`TauCeti.StandardYoungTableau.labelContent_injective`),
  and contents of two cells of `μ` differ by less than `n`, so the eigenvalues separate the
  tableaux; Lagrange interpolation in the `L_i` then gives the projection onto each line `K v_U`;
* when the labels `k` and `k + 1` of `U` lie neither next to each other in a row nor in a column,
  the generator `T_k` has a nonzero coefficient from `v_U` to the vector of the exchanged tableau,
  so compressing `T_k` between the two projections gives the corresponding matrix unit;
* these exchanges connect all the standard tableaux of shape `μ`
  (`TauCeti.StandardYoungTableau.reflTransGen_swap_rowSuperstandard`), and products of matrix
  units give the others.

The criterion cannot be weakened to the hypothesis `[d]_Q ≠ 0`, `0 < d < n`, under which the
representation is defined. For `μ = (2, 1)` and `Q` a primitive cube root of unity, the vector of
the tableau with first row `0, 1` spans an invariant line, since the off-diagonal coefficient
`Q [3]_Q [1]_Q / [2]_Q ^ 2` of `g_1` on it vanishes.

## Main results

* `TauCeti.TypeAHeckeAlgebra.seminormalRep_surjective`: the seminormal representation is onto
  the endomorphism algebra.
* `TauCeti.TypeAHeckeAlgebra.eq_bot_or_eq_top_of_seminormalRep_mem`: the seminormal
  representation is irreducible.

## References

* P. N. Hoefsmit, *Representations of Hecke algebras of finite groups with BN-pairs of classical
  type*, PhD thesis, University of British Columbia (1974).
* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133.
* A. Okounkov and A. Vershik, *A new approach to representation theory of symmetric groups*,
  Selecta Math. (N.S.) 2 (1996), 581–605, for the argument through Jucys–Murphy eigenvalues and
  admissible transpositions at `Q = 1`.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open YoungTableau Matrix

variable {K : Type*} [Field K] {q : Kˣ} {μ : YoungDiagram}
  {hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent ((q : K) ^ 2) d ≠ 0}

/-- The coefficient of `T_k` from the vector of `U` to that of the tableau with `k` and `k + 1`
exchanged is nonzero, under the split-semisimplicity criterion. -/
private theorem seminormalOffDiag_neg_axialDistance_ne_zero
    (hn : ∀ d : ℕ, 0 < d → d ≤ μ.card → additiveContent ((q : K) ^ 2) d ≠ 0)
    (U : StandardYoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card)
    (h : |axialDistance U.toTableau k hk| ≠ 1) :
    seminormalOffDiag ((q : K) ^ 2) (-axialDistance U.toTableau k hk) ≠ 0 := by
  have hQ : (q : K) ^ 2 ≠ 0 := pow_ne_zero 2 q.ne_zero
  have hd0 := U.axialDistance_ne_zero k hk
  have hlt := abs_axialDistance_lt_card U.toTableau k hk
  set d := axialDistance U.toTableau k hk
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · -- `-d > 1`: the coefficient is `Q [-d + 1]_Q [-d - 1]_Q / [-d]_Q ^ 2`
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hneg.le)
    have he1 : 1 < e := by rw [abs_of_neg hneg] at h; omega
    have hen : e < μ.card := by rw [abs_of_neg hneg] at hlt; omega
    have hce : additiveContent ((q : K) ^ 2) e ≠ 0 := hn e (by omega) hen.le
    rw [he, seminormalOffDiag_of_one_lt (by omega), add_seminormalDiag_mul_seminormalDiag_neg hce]
    have h₁ := hn (e + 1) (by omega) (by omega)
    have h₂ := hn (e - 1) (by omega) (by omega)
    push_cast at h₁
    rw [Nat.cast_sub (by omega), Nat.cast_one] at h₂
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hQ h₁) h₂) (pow_ne_zero 2 hce)
  · rw [seminormalOffDiag_of_lt_neg_one (by rw [abs_of_pos hpos] at h; omega)]
    exact one_ne_zero

/-- The matrices, in the basis of the standard tableaux, of the image of the seminormal
representation. -/
private noncomputable def seminormalMatrices (q : Kˣ) (μ : YoungDiagram)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent ((q : K) ^ 2) d ≠ 0) :
    Subalgebra K (Matrix (StandardYoungTableau μ) (StandardYoungTableau μ) K) :=
  (seminormalRep q μ hμ).range.comap (toLinAlgEquiv' : Matrix _ _ K ≃ₐ[K] _).toAlgHom

private theorem mem_seminormalMatrices {M : Matrix (StandardYoungTableau μ)
    (StandardYoungTableau μ) K} :
    M ∈ seminormalMatrices q μ hμ ↔ ∃ x, seminormalRep q μ hμ x = toLinAlgEquiv' M := by
  rw [seminormalMatrices, Subalgebra.mem_comap, AlgHom.mem_range,
    AlgEquiv.toAlgHom_apply]

/-- The projection onto the line of a standard tableau is in the image: the additive
Jucys–Murphy elements act diagonally, and their eigenvalues separate the tableaux. -/
private theorem single_self_mem_seminormalMatrices (U : StandardYoungTableau μ) :
    single U U (1 : K) ∈ seminormalMatrices q μ hμ := by
  have hQ : (q : K) ^ 2 ≠ 0 := pow_ne_zero 2 q.ne_zero
  -- the eigenvalues `U ↦ [content i]_Q` of the additive Jucys–Murphy elements
  set φ : Fin μ.card → StandardYoungTableau μ → K :=
    fun i U => additiveContent ((q : K) ^ 2) (labelContent U.toTableau i)
  set S := (seminormalMatrices q μ hμ).comap (diagonalAlgHom K) with hS
  have hφ : ∀ i, φ i ∈ S := fun i => by
    rw [hS, Subalgebra.mem_comap, mem_seminormalMatrices]
    refine ⟨additiveJucysMurphy q i, LinearMap.ext fun ψ => funext fun V => ?_⟩
    rw [seminormalRep_additiveJucysMurphy_apply, toLinAlgEquiv'_apply, diagonalAlgHom_apply,
      mulVec_diagonal]
  have hsep : ∀ V, U ≠ V → ∃ i, φ i U ≠ φ i V := by
    intro V hUV
    by_contra! h
    refine hUV (StandardYoungTableau.labelContent_injective μ (funext fun i => ?_))
    dsimp only
    refine (additiveContent_inj hQ hμ ?_).mp (h i)
    rw [labelContent_def, labelContent_def]
    exact YoungDiagram.abs_cellContent_sub_lt_card
      ((YoungDiagram.mem_cells _).mp (U.toTableau.symm i).property)
      ((YoungDiagram.mem_cells _).mp (V.toTableau.symm i).property)
  -- for each `V ≠ U`, a function in `S` that is `1` at `U` and `0` at `V`
  have hfactor : ∀ V, ∃ g ∈ S, g U = 1 ∧ (U ≠ V → g V = 0) := by
    intro V
    by_cases hUV : U = V
    · exact ⟨1, Subalgebra.one_mem _, rfl, fun h => absurd hUV h⟩
    obtain ⟨i, hi⟩ := hsep V hUV
    refine ⟨(φ i U - φ i V)⁻¹ • (φ i - algebraMap K _ (φ i V)),
      Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hφ i) (Subalgebra.algebraMap_mem _ _)) _,
      ?_, fun _ => ?_⟩ <;>
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul, sub_self, mul_zero, inv_mul_cancel₀ (sub_ne_zero.mpr hi)]
  choose g hgS hgU hgV using hfactor
  -- Lagrange interpolation: the indicator of `U` is the product of these functions
  have hprod : Pi.single U 1 = ∏ V, g V := by
    funext W
    rw [Finset.prod_apply]
    by_cases hW : W = U
    · subst hW
      rw [Pi.single_eq_same, eq_comm]
      exact Finset.prod_eq_one fun V _ => hgU V
    · rw [Pi.single_eq_of_ne hW, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ W) (hgV W (Ne.symm hW))
  have hmem : Pi.single U 1 ∈ S := hprod ▸ Subalgebra.prod_mem _ fun V _ => hgS V
  rw [hS, Subalgebra.mem_comap, diagonalAlgHom_apply, diagonal_single] at hmem
  exact hmem

/-- The matrix unit from a standard tableau to the tableau with two consecutive labels exchanged
is in the image. -/
private theorem single_swap_mem_seminormalMatrices
    (hn : ∀ d : ℕ, 0 < d → d ≤ μ.card → additiveContent ((q : K) ^ 2) d ≠ 0)
    (U : StandardYoungTableau μ) (k : ℕ) (hk : k + 1 < μ.card)
    (h : |axialDistance U.toTableau k hk| ≠ 1) :
    single (U.swap k hk h) U (1 : K) ∈ seminormalMatrices q μ hμ := by
  have hM : LinearMap.toMatrixAlgEquiv' (seminormalRep q μ hμ (T q ⟨k, by omega⟩)) ∈
      seminormalMatrices q μ hμ :=
    mem_seminormalMatrices.mpr ⟨_, (toLinAlgEquiv'_toMatrixAlgEquiv' _).symm⟩
  have hentry : LinearMap.toMatrixAlgEquiv' (seminormalRep q μ hμ (T q ⟨k, by omega⟩))
      (U.swap k hk h) U =
        (↑q⁻¹ : K) * seminormalOffDiag ((q : K) ^ 2) (-axialDistance U.toTableau k hk) := by
    simp [LinearMap.toMatrixAlgEquiv'_apply,
      seminormalRep_T_single_of_abs_ne_one (⟨k, by omega⟩ : Fin (μ.card - 1)) U h,
      Pi.single_eq_of_ne (U.swap_ne_self k hk h)]
  have hne : LinearMap.toMatrixAlgEquiv' (seminormalRep q μ hμ (T q ⟨k, by omega⟩))
      (U.swap k hk h) U ≠ 0 := by
    rw [hentry]
    exact mul_ne_zero (by simp) (seminormalOffDiag_neg_axialDistance_ne_zero hn U k hk h)
  generalize LinearMap.toMatrixAlgEquiv' (seminormalRep q μ hμ (T q ⟨k, by omega⟩)) = M at hM hne
  have hunit : single (U.swap k hk h) U (1 : K) = (M (U.swap k hk h) U)⁻¹ •
      (single (U.swap k hk h) (U.swap k hk h) 1 * M * single U U 1) := by
    rw [single_mul_mul_single, one_mul, mul_one, smul_single, smul_eq_mul, inv_mul_cancel₀ hne]
  rw [hunit]
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (single_self_mem_seminormalMatrices _) hM) (single_self_mem_seminormalMatrices U)) _

/-- Every matrix unit of the tableau basis is in the image. -/
private theorem single_mem_seminormalMatrices
    (hn : ∀ d : ℕ, 0 < d → d ≤ μ.card → additiveContent ((q : K) ^ 2) d ≠ 0)
    (U W : StandardYoungTableau μ) : single U W (1 : K) ∈ seminormalMatrices q μ hμ := by
  set R := StandardYoungTableau.rowSuperstandard μ
  -- the matrix units between any tableau and the row-superstandard tableau are in the image
  have key : ∀ U, single R U (1 : K) ∈ seminormalMatrices q μ hμ ∧
      single U R (1 : K) ∈ seminormalMatrices q μ hμ := by
    intro U
    induction U.reflTransGen_swap_rowSuperstandard using Relation.ReflTransGen.head_induction_on
      with
    | refl => exact ⟨single_self_mem_seminormalMatrices R, single_self_mem_seminormalMatrices R⟩
    | head hUV _ ih =>
      obtain ⟨k, hk, h, rfl⟩ := hUV
      rename_i U _
      have h' : |axialDistance (U.swap k hk h).toTableau k hk| ≠ 1 := by
        rwa [StandardYoungTableau.toTableau_swap, axialDistance_relabel_swap, abs_neg]
      have hfwd := single_swap_mem_seminormalMatrices (hμ := hμ) hn U k hk h
      have hbwd := single_swap_mem_seminormalMatrices (hμ := hμ) hn _ k hk h'
      rw [StandardYoungTableau.swap_swap] at hbwd
      refine ⟨?_, ?_⟩
      · simpa using Subalgebra.mul_mem _ ih.1 hfwd
      · simpa using Subalgebra.mul_mem _ hbwd ih.2
  simpa using Subalgebra.mul_mem _ (key U).2 (key W).1

/-- **The seminormal representation is absolutely irreducible.** Under the split-semisimplicity
criterion `[d]_Q ≠ 0` for `0 < d ≤ n`, with `Q = q ^ 2` and `n` the number of cells of `μ`, every
linear endomorphism of the functions on the standard tableaux of shape `μ` is the action of an
element of the Hecke algebra `H_n(q)`. -/
theorem seminormalRep_surjective
    (hn : ∀ d : ℕ, 0 < d → d ≤ μ.card → additiveContent ((q : K) ^ 2) d ≠ 0) :
    Function.Surjective (seminormalRep q μ fun d hd hdn => hn d hd hdn.le) := by
  intro f
  have hM : LinearMap.toMatrixAlgEquiv' f ∈
      seminormalMatrices q μ fun d hd hdn => hn d hd hdn.le := by
    rw [matrix_eq_sum_single (LinearMap.toMatrixAlgEquiv' f)]
    refine Subalgebra.sum_mem _ fun U _ => Subalgebra.sum_mem _ fun W _ => ?_
    rw [← mul_one (LinearMap.toMatrixAlgEquiv' f U W), ← smul_eq_mul, ← smul_single]
    exact Subalgebra.smul_mem _ (single_mem_seminormalMatrices hn U W) _
  obtain ⟨x, hx⟩ := mem_seminormalMatrices.mp hM
  exact ⟨x, hx.trans (toLinAlgEquiv'_toMatrixAlgEquiv' f)⟩

/-- **The seminormal representation is irreducible.** Under the split-semisimplicity criterion
`[d]_Q ≠ 0` for `0 < d ≤ n`, a subspace of the functions on the standard tableaux of shape `μ`
that is invariant under the Hecke algebra `H_n(q)` is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_seminormalRep_mem
    (hn : ∀ d : ℕ, 0 < d → d ≤ μ.card → additiveContent ((q : K) ^ 2) d ≠ 0)
    (W : Submodule K (StandardYoungTableau μ → K))
    (hW : ∀ x, ∀ w ∈ W, seminormalRep q μ (fun d hd hdn => hn d hd hdn.le) x w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hne => eq_top_iff.mpr fun v _ => ?_
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨U, hU⟩ : ∃ U, w U ≠ 0 := by
    by_contra! h
    exact hw0 (funext h)
  -- the endomorphism `ψ ↦ (ψ U / w U) • v` sends `w` to `v`
  obtain ⟨x, hx⟩ := seminormalRep_surjective hn
    ((w U)⁻¹ • (LinearMap.proj U).smulRight v)
  have hxw := hW x w hw
  simpa [hx, smul_smul, inv_mul_cancel₀ hU] using hxw

end TauCeti.TypeAHeckeAlgebra
