/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Decomposition
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Fin.Tuple
import Mathlib.RingTheory.Int.Basic
import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Unique
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Existence of the Hermite normal form

Every integer matrix `A` with `m` rows and `n` columns has a Hermite decomposition: there are
`k ≤ n`, an `m × k` matrix `H` in (column-style, upper) Hermite normal form and `U ∈ GL_n(ℤ)` with
`A * U = [H | 0]`. By the uniqueness of the Hermite normal form the pair `(k, H)` depends only on
the column lattice of `A`, and `k` is the rank of `A`; we call `H` the *Hermite basis* of `A`. It
is the canonical basis of the column lattice of `A`, with which sublattices of `ℤ^m`, such as
ideals of a number field in a fixed integral basis, are recorded and compared.

## Main definitions

* `Matrix.hermiteBasis A`: the unique matrix in Hermite normal form whose column lattice is that
  of `A`; it has `A.rank` columns.

## Main results

* `Matrix.exists_isHermiteNormalForm_range_mulVecLin_eq`: every sublattice of `ℤ^m` is the column
  lattice of a matrix in Hermite normal form.
* `Matrix.IsHermiteNormalForm.exists_isHermiteDecomposition`: if `H` is in Hermite normal form and
  has the column lattice of `A`, then `A * U = [H | 0]` for some `U ∈ GL_n(ℤ)`.
* `Matrix.exists_isHermiteDecomposition`: every integer matrix has a Hermite decomposition.
* `Matrix.isHermiteNormalForm_hermiteBasis`, `Matrix.range_mulVecLin_hermiteBasis`,
  `Matrix.exists_isHermiteDecomposition_hermiteBasis`: the Hermite basis of `A` is in Hermite
  normal form, has the column lattice of `A`, and is the Hermite matrix of a decomposition of `A`.
* `Matrix.mem_range_iff_hermite`: a vector lies in the column lattice of `A` if and only if it has
  unique coordinates in the Hermite basis of `A`.
* `Matrix.IsHermiteNormalForm.sigma_mk_hermiteBasis_eq`: every matrix in Hermite normal form with
  the column lattice of `A` is the Hermite basis of `A`;
  `Matrix.IsHermiteNormalForm.hermiteBasis_eq` is the version for matrices with `A.rank` columns.
* `Matrix.hermiteBasis_eq_of_range_eq`: matrices with the same column lattice have the same
  Hermite basis.

## Implementation notes

We first show that every sublattice `L` of `ℤ^m` is the column lattice of a matrix in
Hermite normal form, by induction on `m`. Deleting the top coordinate maps `L` onto a sublattice of
`ℤ^(m-1)`, which has a Hermite basis `H'` by induction; lift the columns of `H'` to `L`. The
vectors of `L` supported on the top coordinate are the multiples of `d • e₀` for some `d ≥ 0`. If
`d = 0`, the lifts are a Hermite basis of `L`. Otherwise `d • e₀` is a new first column, with pivot
in the top row, and the top entries of the lifts are reduced modulo `d`. The transformation `U`
is then assembled from a basis of `ℤ^n` consisting of lifts of the columns of `H` along `A`
followed by a basis of the kernel of `A`, which is free since `ℤ` is a principal ideal domain.

## References

* Daniele Micciancio, *CSE 206A: Lattice Algorithms and Applications*, lecture 1, Theorem 8, and
  lecture 4 (Basic algorithms), Definition 1: every lattice has a basis in Hermite normal form.
-/

public section

namespace Matrix

variable {m n k : ℕ}

/-! ### Adding a top row -/

/-- If deleting the top row of `H` leaves a matrix `H'` in Hermite normal form with pivot rows
`p`, then `H` is in Hermite normal form with pivot rows `Fin.succ ∘ p`, whatever its top row. -/
private theorem isHermitePivotedBy_of_succ {H' : Matrix (Fin m) (Fin k) ℤ} {p : Fin k → Fin m}
    (h : H'.IsHermitePivotedBy p) {H : Matrix (Fin (m + 1)) (Fin k) ℤ}
    (hH : ∀ (i : Fin m) (j : Fin k), H i.succ j = H' i j) :
    H.IsHermitePivotedBy (Fin.succ ∘ p) where
  strictMono := Fin.strictMono_succ.comp h.strictMono
  pivot_pos j := by simpa [hH] using h.pivot_pos j
  eq_zero_of_lt j {i} hi := by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.not_lt_zero _)
    | succ i => rw [hH]; exact h.eq_zero_of_lt j (Fin.succ_lt_succ_iff.mp hi)
  nonneg_of_lt hjj' := by simpa [hH] using h.nonneg_of_lt hjj'
  lt_pivot_of_lt hjj' := by simpa [hH] using h.lt_pivot_of_lt hjj'

/-- Let `H` have a positive top left entry `H 0 0`, zeros below it, top row entries reduced modulo
`H 0 0`, and, after deleting the top row and the first column, a matrix `H'` in Hermite normal
form with pivot rows `p`. Then `H` is in Hermite normal form, with pivot rows `0` followed by
`Fin.succ ∘ p`. -/
private theorem isHermitePivotedBy_cons {H' : Matrix (Fin m) (Fin k) ℤ} {p : Fin k → Fin m}
    (h : H'.IsHermitePivotedBy p) {H : Matrix (Fin (m + 1)) (Fin (k + 1)) ℤ}
    (h₀ : 0 < H 0 0) (hcol : ∀ i : Fin m, H i.succ 0 = 0)
    (hH : ∀ (i : Fin m) (j : Fin k), H i.succ j.succ = H' i j)
    (hrow : ∀ j : Fin k, 0 ≤ H 0 j.succ ∧ H 0 j.succ < H 0 0) :
    H.IsHermitePivotedBy (Fin.cons 0 (Fin.succ ∘ p)) where
  strictMono := Fin.strictMono_cons.mpr
    ⟨fun _ ↦ Fin.succ_pos _, Fin.strictMono_succ.comp h.strictMono⟩
  pivot_pos j := by
    cases j using Fin.cases with
    | zero => exact h₀
    | succ j => simpa [hH] using h.pivot_pos j
  eq_zero_of_lt j {i} hi := by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.not_lt_zero _)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact hcol i
      | succ j => rw [hH]; exact h.eq_zero_of_lt j (by simpa using hi)
  nonneg_of_lt {j j'} hjj' := by
    cases j' using Fin.cases with
    | zero => exact absurd hjj' (Fin.not_lt_zero _)
    | succ j' =>
      cases j using Fin.cases with
      | zero => exact (hrow j').1
      | succ j => simpa [hH] using h.nonneg_of_lt (Fin.succ_lt_succ_iff.mp hjj')
  lt_pivot_of_lt {j j'} hjj' := by
    cases j' using Fin.cases with
    | zero => exact absurd hjj' (Fin.not_lt_zero _)
    | succ j' =>
      cases j using Fin.cases with
      | zero => exact (hrow j').2
      | succ j => simpa [hH] using h.lt_pivot_of_lt (Fin.succ_lt_succ_iff.mp hjj')

/-- A matrix `H` with columns in `L` has column lattice `L` if every vector of `L` agrees with a
vector of the column lattice below the top row, and every vector of `L` supported on the top row
lies in the column lattice. -/
private theorem range_mulVecLin_eq_of_succ {L : Submodule ℤ (Fin (m + 1) → ℤ)}
    {H : Matrix (Fin (m + 1)) (Fin k) ℤ} (hcol : ∀ j, H.col j ∈ L)
    (htail : ∀ x ∈ L, ∃ c, ∀ i : Fin m, (H *ᵥ c) i.succ = x i.succ)
    (hsingle : ∀ a, Pi.single 0 a ∈ L → Pi.single 0 a ∈ LinearMap.range H.mulVecLin) :
    LinearMap.range H.mulVecLin = L := by
  have hle : LinearMap.range H.mulVecLin ≤ L := by
    rw [range_mulVecLin, Submodule.span_le, Set.range_subset_iff]
    exact hcol
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := htail x hx
  -- The difference of `x` and `H *ᵥ c` is supported on the top row.
  have hy : x - H *ᵥ c = Pi.single 0 ((x - H *ᵥ c) 0) := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [hc i]
  have hmem := hsingle _ (hy ▸ sub_mem hx (hle ⟨c, rfl⟩))
  rw [← hy] at hmem
  simpa using add_mem hmem (LinearMap.mem_range_self H.mulVecLin c)

/-- The vectors of a sublattice `L` of `ℤ^(m+1)` supported on the top coordinate are the multiples
of `d • e₀` for some `d : ℕ`. -/
private theorem exists_single_zero_mem_iff_dvd (L : Submodule ℤ (Fin (m + 1) → ℤ)) :
    ∃ d : ℕ, ∀ a : ℤ, Pi.single 0 a ∈ L ↔ (d : ℤ) ∣ a := by
  let I : Ideal ℤ := L.comap (LinearMap.single ℤ (fun _ ↦ ℤ) 0)
  refine ⟨(Submodule.IsPrincipal.generator I).natAbs, fun a ↦ ?_⟩
  rw [Int.natAbs_dvd, ← Submodule.IsPrincipal.mem_iff_generator_dvd]
  simp [I]

/-- Let `L` be a sublattice of `ℤ^(m+1)` whose vectors agree below the top row with vectors of the
column lattice of `H'`, a matrix in Hermite normal form with pivot rows `p`, and let `v j ∈ L` lift
the columns of `H'`. If the vectors of `L` supported on the top row are the multiples of `d • e₀`
with `d > 0`, then `d • e₀` followed by the lifts, with top entries reduced modulo `d`, is a
Hermite basis of `L`. -/
private theorem exists_isHermiteNormalForm_of_pos {L : Submodule ℤ (Fin (m + 1) → ℤ)}
    {H' : Matrix (Fin m) (Fin k) ℤ} {p : Fin k → Fin m} (hp : H'.IsHermitePivotedBy p)
    (htail : ∀ x ∈ L, ∃ c, ∀ i, (H' *ᵥ c) i = x i.succ)
    {v : Fin k → Fin (m + 1) → ℤ} (hvL : ∀ j, v j ∈ L) (hv : ∀ j i, v j i.succ = H' i j)
    {d : ℕ} (hd₀ : 0 < d) (hd : ∀ a : ℤ, Pi.single 0 a ∈ L ↔ (d : ℤ) ∣ a) :
    ∃ H : Matrix (Fin (m + 1)) (Fin (k + 1)) ℤ,
      H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = L := by
  let w : Fin k → Fin (m + 1) → ℤ := fun j ↦ v j - (v j 0 / d) • Pi.single 0 (d : ℤ)
  let C : Fin (k + 1) → Fin (m + 1) → ℤ := Fin.cons (Pi.single 0 (d : ℤ)) w
  have hd₀' : (0 : ℤ) < d := by exact_mod_cast hd₀
  have hw₀ (j : Fin k) : w j 0 = v j 0 % d := by
    simp [w, Int.emod_def, mul_comm]
  have hwsucc (j : Fin k) (i : Fin m) : w j i.succ = H' i j := by
    simp [w, hv]
  refine ⟨(of C)ᵀ, (isHermitePivotedBy_cons hp ?_ ?_ ?_ ?_).isHermiteNormalForm,
    range_mulVecLin_eq_of_succ (fun j ↦ ?_) (fun x hx ↦ ?_) fun a ha ↦ ?_⟩
  · simpa [C] using hd₀'
  · simp [C]
  · simp [C, hwsucc]
  · intro j
    simp only [transpose_apply, of_apply, C, Fin.cons_succ, hw₀]
    exact ⟨Int.emod_nonneg _ hd₀'.ne', Int.emod_lt_of_pos _ hd₀'⟩
  · rw [of_col]
    exact Fin.cases ((hd d).mpr dvd_rfl)
      (fun j ↦ sub_mem (hvL j) (Submodule.smul_mem _ _ ((hd d).mpr dvd_rfl))) j
  · obtain ⟨c, hc⟩ := htail x hx
    refine ⟨Fin.cons 0 c, fun i ↦ ?_⟩
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, C, hwsucc] using hc i
  · obtain ⟨t, rfl⟩ := (hd a).mp ha
    refine ⟨Pi.single 0 t, ?_⟩
    ext i
    cases i using Fin.cases with
    | zero => simp [C, mul_comm]
    | succ i => simp [C]

/-- **Existence of Hermite bases.** Every sublattice `L` of `ℤ^m` is the column lattice of a
matrix in Hermite normal form. -/
theorem exists_isHermiteNormalForm_range_mulVecLin_eq :
    ∀ {m : ℕ} (L : Submodule ℤ (Fin m → ℤ)), ∃ k, ∃ H : Matrix (Fin m) (Fin k) ℤ,
      H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = L
  | 0, L => ⟨0, 0, isHermiteNormalForm_of_fin_zero _, by
      ext x
      rw [Subsingleton.elim x 0]
      exact iff_of_true (Submodule.zero_mem _) L.zero_mem⟩
  | m + 1, L => by
    obtain ⟨k, H', hH'nf, hH'⟩ :=
      exists_isHermiteNormalForm_range_mulVecLin_eq (L.map (LinearMap.funLeft ℤ ℤ Fin.succ))
    obtain ⟨p, hp⟩ := isHermiteNormalForm_iff.mp hH'nf
    -- Every vector of `L` agrees below the top row with a vector of the column lattice of `H'`.
    have htail (x : Fin (m + 1) → ℤ) (hx : x ∈ L) : ∃ c, ∀ i, (H' *ᵥ c) i = x i.succ := by
      obtain ⟨c, hc⟩ : LinearMap.funLeft ℤ ℤ Fin.succ x ∈ LinearMap.range H'.mulVecLin :=
        hH' ▸ Submodule.mem_map_of_mem hx
      exact ⟨c, fun i ↦ by simpa using congrFun hc i⟩
    -- Lift the columns of `H'` to vectors of `L`.
    have hlift (j : Fin k) : ∃ v ∈ L, ∀ i, v i.succ = H' i j := by
      obtain ⟨v, hv, hvj⟩ := hH' ▸ H'.col_mem_range_mulVecLin j
      exact ⟨v, hv, fun i ↦ by simpa using congrFun hvj i⟩
    choose v hvL hv using hlift
    obtain ⟨d, hd⟩ := exists_single_zero_mem_iff_dvd L
    rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · -- If `d = 0`, the lifts of the columns of `H'` form a Hermite basis of `L`.
      refine ⟨k, (of v)ᵀ, (isHermitePivotedBy_of_succ hp fun i j ↦ hv j i).isHermiteNormalForm,
        range_mulVecLin_eq_of_succ (fun j ↦ by rw [of_col]; exact hvL j) (fun x hx ↦ ?_)
          fun a ha ↦ ?_⟩
      · obtain ⟨c, hc⟩ := htail x hx
        exact ⟨c, fun i ↦ by simpa [mulVec, dotProduct, hv] using hc i⟩
      · obtain rfl : a = 0 := by simpa using (hd a).mp ha
        simp
    · exact ⟨k + 1, exists_isHermiteNormalForm_of_pos hp htail hvL hv hd₀ hd⟩

/-! ### Hermite decompositions -/

/-- If the column lattice of `A` is that of a matrix `H` in Hermite normal form, then `A` has a
Hermite decomposition `A * U = [H | 0]` with Hermite matrix `H` and `U ∈ GL_n(ℤ)`. -/
theorem IsHermiteNormalForm.exists_isHermiteDecomposition {A : Matrix (Fin m) (Fin n) ℤ}
    {H : Matrix (Fin m) (Fin k) ℤ} (hH : H.IsHermiteNormalForm)
    (hAH : LinearMap.range A.mulVecLin = LinearMap.range H.mulVecLin) :
    ∃ U : GL (Fin n) ℤ, IsHermiteDecomposition A H U ↑U⁻¹ := by
  -- Lift the columns of `H` along `A`.
  have hlift (j : Fin k) : ∃ s, A *ᵥ s = H.col j :=
    (hAH ▸ H.col_mem_range_mulVecLin j : H.col j ∈ LinearMap.range A.mulVecLin)
  choose s hs using hlift
  have hAs (c : Fin k → ℤ) : A *ᵥ ∑ j, c j • s j = H *ᵥ c := by
    rw [mulVec_sum]
    simp_rw [mulVec_smul, hs]
    ext i
    simp [mulVec, dotProduct, mul_comm]
  have hinj : Function.Injective H.mulVec := mulVec_injective_iff.mpr hH.linearIndependent_cols
  have hli : LinearIndependent ℤ s :=
    LinearIndependent.of_comp A.mulVecLin <| by
      rw [show ⇑A.mulVecLin ∘ s = H.col from funext hs]
      exact hH.linearIndependent_cols
  -- The span of the lifts is a complement of the kernel of `A`.
  have hcompl : IsCompl (Submodule.span ℤ (Set.range s)) (LinearMap.ker A.mulVecLin) := by
    refine ⟨Submodule.disjoint_def.mpr fun x hx hker ↦ ?_,
      Submodule.codisjoint_iff_exists_add_eq.mpr fun x ↦ ?_⟩
    · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      obtain rfl : c = 0 := hinj <| by
        rw [← hAs, mulVec_zero]
        exact hker
      simp
    · obtain ⟨c, hc⟩ : A *ᵥ x ∈ LinearMap.range H.mulVecLin := hAH ▸ ⟨x, rfl⟩
      refine ⟨∑ j, c j • s j, x - ∑ j, c j • s j,
        Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩),
        ?_, add_sub_cancel _ _⟩
      rw [mulVecLin_apply] at hc
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, hAs, hc, sub_self]
  -- A basis of `ℤ^n`: the lifts, followed by a basis of the kernel of `A`.
  obtain ⟨r, b⟩ := (LinearMap.ker A.mulVecLin).basisOfPid (Pi.basisFun ℤ (Fin n))
  let b₀ := ((Module.Basis.span hli).prod b).map (Submodule.prodEquivOfIsCompl _ _ hcompl)
  have hkr : k + r = n := by
    simpa using (Module.finrank_eq_card_basis b₀).symm
  let e : Fin k ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr hkr)
  let b' := b₀.reindex e
  let U : GL (Fin n) ℤ := ⟨(Pi.basisFun ℤ (Fin n)).toMatrix b', b'.toMatrix (Pi.basisFun ℤ (Fin n)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨U, hkr ▸ Nat.le_add_right k r, hH, U.mul_inv, U.inv_mul, ?_⟩
  ext i j
  have hAU : (A * (U : Matrix (Fin n) (Fin n) ℤ)) i j = (A *ᵥ b' j) i := by
    simp [U, mul_apply, mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hAU]
  obtain ⟨a | a, rfl⟩ := e.surjective j
  · simp [b', b₀, e, hs, hermitePad_apply]
  · have hker : A *ᵥ (b a : Fin n → ℤ) = 0 := LinearMap.mem_ker.mp (b a).2
    simp [b', b₀, e, hker, hermitePad_apply]

/-- **Existence of the Hermite normal form.** Every integer matrix `A` has a Hermite
decomposition: `A * U = [H | 0]` for some matrix `H` in Hermite normal form and `U ∈ GL_n(ℤ)`. -/
theorem exists_isHermiteDecomposition (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ k, ∃ (H : Matrix (Fin m) (Fin k) ℤ) (U : GL (Fin n) ℤ), IsHermiteDecomposition A H U ↑U⁻¹ :=
  let ⟨k, H, hH, hHA⟩ := exists_isHermiteNormalForm_range_mulVecLin_eq (LinearMap.range A.mulVecLin)
  ⟨k, H, hH.exists_isHermiteDecomposition hHA.symm⟩

/-! ### The Hermite basis of an integer matrix -/

/-- Some matrix in Hermite normal form with `A.rank` columns has the column lattice of `A`. -/
private theorem exists_isHermiteNormalForm_rank (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ H : Matrix (Fin m) (Fin A.rank) ℤ,
      H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = LinearMap.range A.mulVecLin := by
  obtain ⟨k, H, U, h⟩ := A.exists_isHermiteDecomposition
  obtain rfl := h.rank_eq
  exact ⟨H, h.isHermiteNormalForm, h.range_mulVecLin_eq.symm⟩

/-- The *Hermite basis* of an integer matrix `A`: the unique matrix in Hermite normal form whose
column lattice is that of `A`, see `Matrix.IsHermiteNormalForm.sigma_mk_hermiteBasis_eq`. It has
`A.rank` columns. -/
noncomputable def hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin A.rank) ℤ :=
  (exists_isHermiteNormalForm_rank A).choose

variable {A : Matrix (Fin m) (Fin n) ℤ}

/-- The Hermite basis of `A` is in Hermite normal form. -/
theorem isHermiteNormalForm_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    A.hermiteBasis.IsHermiteNormalForm :=
  (exists_isHermiteNormalForm_rank A).choose_spec.1

/-- The column lattice of the Hermite basis of `A` is that of `A`. -/
@[simp]
theorem range_mulVecLin_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    LinearMap.range A.hermiteBasis.mulVecLin = LinearMap.range A.mulVecLin :=
  (exists_isHermiteNormalForm_rank A).choose_spec.2

/-- The Hermite basis of `A` is the Hermite matrix of a Hermite decomposition of `A`. -/
theorem exists_isHermiteDecomposition_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ U : GL (Fin n) ℤ, IsHermiteDecomposition A A.hermiteBasis U ↑U⁻¹ :=
  (isHermiteNormalForm_hermiteBasis A).exists_isHermiteDecomposition
    (range_mulVecLin_hermiteBasis A).symm

/-- A vector lies in the column lattice of `A` if and only if it is an integer combination of the
columns of the Hermite basis of `A`, with unique coefficients. -/
theorem mem_range_iff_hermite {x : Fin m → ℤ} :
    x ∈ LinearMap.range A.mulVecLin ↔ ∃! c, A.hermiteBasis *ᵥ c = x := by
  rw [← range_mulVecLin_hermiteBasis]
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨c, hc, fun c' hc' ↦ ?_⟩, fun ⟨c, hc, _⟩ ↦ ⟨c, hc⟩⟩
  exact mulVec_injective_iff.mpr (isHermiteNormalForm_hermiteBasis A).linearIndependent_cols
    (hc'.trans hc.symm)

/-- **Uniqueness of the Hermite basis.** Every matrix in Hermite normal form with the column
lattice of `A` is the Hermite basis of `A`, with the same number of columns. -/
theorem IsHermiteNormalForm.sigma_mk_hermiteBasis_eq {H : Matrix (Fin m) (Fin k) ℤ}
    (hH : H.IsHermiteNormalForm)
    (hAH : LinearMap.range A.mulVecLin = LinearMap.range H.mulVecLin) :
    (⟨A.rank, A.hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨k, H⟩ :=
  (isHermiteNormalForm_hermiteBasis A).sigma_mk_eq_of_range_mulVecLin_eq hH
    ((range_mulVecLin_hermiteBasis A).trans hAH)

/-- **Uniqueness of the Hermite basis.** A matrix with `A.rank` columns in Hermite normal form with
the column lattice of `A` is the Hermite basis of `A`. -/
theorem IsHermiteNormalForm.hermiteBasis_eq {H : Matrix (Fin m) (Fin A.rank) ℤ}
    (hH : H.IsHermiteNormalForm)
    (hAH : LinearMap.range A.mulVecLin = LinearMap.range H.mulVecLin) :
    A.hermiteBasis = H :=
  (isHermiteNormalForm_hermiteBasis A).eq_of_range_mulVecLin_eq hH
    ((range_mulVecLin_hermiteBasis A).trans hAH)

/-- Integer matrices with the same column lattice have the same Hermite basis, with the same
number of columns. -/
theorem hermiteBasis_eq_of_range_eq {n' : ℕ} {B : Matrix (Fin m) (Fin n') ℤ}
    (hAB : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    (⟨A.rank, A.hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨B.rank, B.hermiteBasis⟩ :=
  (isHermiteNormalForm_hermiteBasis B).sigma_mk_hermiteBasis_eq
    (hAB.trans (range_mulVecLin_hermiteBasis B).symm)

/-! ### Examples -/

/-- An invertible integer matrix has the identity as its Hermite basis. -/
example (U : GL (Fin n) ℤ) :
    (⟨_, (U : Matrix (Fin n) (Fin n) ℤ).hermiteBasis⟩ : Σ k, Matrix (Fin n) (Fin k) ℤ) =
      ⟨n, 1⟩ := by
  refine IsHermiteNormalForm.one.sigma_mk_hermiteBasis_eq ?_
  rw [mulVecLin_one, LinearMap.range_id, LinearMap.range_eq_top]
  exact fun x ↦ ⟨(U⁻¹ : GL (Fin n) ℤ) *ᵥ x, by simp [mulVec_mulVec]⟩

/-- The `1 × 2` matrix `(6, 10)` has the Hermite basis `(2)`. -/
example : (⟨_, (!![6, 10] : Matrix (Fin 1) (Fin 2) ℤ).hermiteBasis⟩ :
    Σ k, Matrix (Fin 1) (Fin k) ℤ) = ⟨1, !![2]⟩ := by
  refine (IsHermitePivotedBy.isHermiteNormalForm (p := id)
    ⟨strictMono_id, by decide, by decide, by decide, by decide⟩).sigma_mk_hermiteBasis_eq
    (le_antisymm ?_ ?_)
  · rintro _ ⟨c, rfl⟩
    exact ⟨![3 * c 0 + 5 * c 1], by ext i; fin_cases i; simp [vecHead, vecTail]; ring⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨![-3 * c 0, 2 * c 0], by ext i; fin_cases i; simp [vecHead, vecTail]; ring⟩

/-- The matrix with columns `(1, 2, 3)`, `(4, 5, 6)` and `(7, 8, 9)` has the Hermite basis with
the two columns `(2, 1, 0)` and `(-3, 0, 3)`. -/
example : (⟨_, (!![1, 4, 7; 2, 5, 8; 3, 6, 9] : Matrix (Fin 3) (Fin 3) ℤ).hermiteBasis⟩ :
    Σ k, Matrix (Fin 3) (Fin k) ℤ) = ⟨2, !![2, -3; 1, 0; 0, 3]⟩ := by
  refine (IsHermitePivotedBy.isHermiteNormalForm (p := ![1, 2])
    ⟨by decide, by decide, by decide, by decide, by decide⟩).sigma_mk_hermiteBasis_eq
    (le_antisymm ?_ ?_)
  · rintro _ ⟨c, rfl⟩
    exact ⟨![2 * c 0 + 5 * c 1 + 8 * c 2, c 0 + 2 * c 1 + 3 * c 2],
      by ext i; fin_cases i <;> simp [vecHead, vecTail] <;> ring⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨![-2 * c 0 + 5 * c 1, c 0 - 2 * c 1, 0],
      by ext i; fin_cases i <;> simp [vecHead, vecTail] <;> ring⟩

end Matrix
