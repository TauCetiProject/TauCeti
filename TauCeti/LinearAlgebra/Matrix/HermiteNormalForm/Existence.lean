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
import TauCeti.Algebra.Module.Submodule.Int
import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Unique
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Existence of the Hermite normal form

Every sublattice `L` of `ℤ^m` is the column lattice of exactly one matrix in (column-style, upper)
Hermite normal form, the *Hermite basis* of `L`; it has `finrank ℤ L` columns. It is the canonical
basis with which sublattices of `ℤ^m`, such as ideals of a number field in a fixed integral basis,
are recorded and compared.

Every integer matrix `A` with `m` rows and `n` columns has a Hermite decomposition: there are
`k ≤ n`, an `m × k` matrix `H` in Hermite normal form and `U ∈ GL_n(ℤ)` with `A * U = [H | 0]`.
Here `H` is the Hermite basis of the column lattice of `A`, which we also call the Hermite basis of
`A`, and `k` is the rank of `A`.

## Main definitions

* `Submodule.hermiteBasis L`: the unique matrix in Hermite normal form whose column lattice is the
  sublattice `L` of `ℤ^m`; it has `finrank ℤ L` columns.
* `Matrix.hermiteBasis A`: the Hermite basis of the column lattice of `A`; it has `A.rank`
  columns.

## Main results

* `Matrix.exists_isHermiteNormalForm_range_mulVecLin_eq`: every sublattice of `ℤ^m` is the column
  lattice of a matrix in Hermite normal form.
* `Matrix.existsUnique_isHermiteNormalForm_range_mulVecLin_eq`: every sublattice of `ℤ^m` is the
  column lattice of exactly one matrix in Hermite normal form, with a uniquely determined number of
  columns.
* `Submodule.hermiteBasis_eq_iff`, `Submodule.sigma_mk_hermiteBasis_eq_iff`: a matrix is the
  Hermite basis of `L` if and only if it is in Hermite normal form with column lattice `L`.
* `Submodule.mem_iff_hermite`: a vector lies in `L` if and only if it has unique coordinates in the
  Hermite basis of `L`.
* `Submodule.sigma_mk_hermiteBasis_inj`: sublattices are determined by their Hermite bases.
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
* `Matrix.hermiteBasis_eq_of_range_eq`, `Matrix.sigma_mk_hermiteBasis_eq_iff`: matrices have the
  same Hermite basis if and only if they have the same column lattice.

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
* Karim Belabas, *Topics in computational algebraic number theory*, J. Théor. Nombres Bordeaux 16
  (2004), Section 5.3.1: every sublattice of `ℤ^m` has a unique basis in Hermite normal form, the
  canonical representation of ideals in a fixed integral basis.
-/

public section

namespace Matrix

variable {m n k : ℕ}

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
    -- The vectors of `L` supported on the top row are the multiples of `d • e₀`.
    obtain ⟨d, hd⟩ := L.exists_smul_mem_iff_dvd (Pi.single 0 1)
    simp only [← Pi.single_smul', smul_eq_mul, mul_one] at hd
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

/-- **Every sublattice of `ℤ^m` has a unique Hermite basis.** For every sublattice `L` of `ℤ^m`
there is exactly one pair `⟨k, H⟩` of a number `k` and a matrix `H` with `m` rows and `k` columns
in Hermite normal form whose column lattice is `L`. -/
theorem existsUnique_isHermiteNormalForm_range_mulVecLin_eq (L : Submodule ℤ (Fin m → ℤ)) :
    ∃! H : Σ k, Matrix (Fin m) (Fin k) ℤ,
      H.2.IsHermiteNormalForm ∧ LinearMap.range H.2.mulVecLin = L := by
  obtain ⟨k, H, hH, hHL⟩ := exists_isHermiteNormalForm_range_mulVecLin_eq L
  exact ⟨⟨k, H⟩, ⟨hH, hHL⟩, fun H' hH' ↦
    hH'.1.sigma_mk_eq_of_range_mulVecLin_eq hH (hH'.2.trans hHL.symm)⟩

/-- Some matrix in Hermite normal form with `finrank ℤ L` columns has column lattice `L`. -/
private theorem exists_isHermiteNormalForm_finrank (L : Submodule ℤ (Fin m → ℤ)) :
    ∃ H : Matrix (Fin m) (Fin (Module.finrank ℤ L)) ℤ,
      H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = L := by
  obtain ⟨k, H, hH, rfl⟩ := exists_isHermiteNormalForm_range_mulVecLin_eq L
  have hk : Module.finrank ℤ (LinearMap.range H.mulVecLin) = k := by
    rw [← rank]
    exact hH.rank_eq
  generalize Module.finrank ℤ (LinearMap.range H.mulVecLin) = k' at hk ⊢
  subst hk
  exact ⟨H, hH, rfl⟩

end Matrix

/-! ### The Hermite basis of a sublattice -/

namespace Submodule

open Matrix

variable {m k : ℕ} (L : Submodule ℤ (Fin m → ℤ)) {L' : Submodule ℤ (Fin m → ℤ)}

/-- The *Hermite basis* of a sublattice `L` of `ℤ^m`: the unique matrix in Hermite normal form
whose column lattice is `L`, see `Submodule.hermiteBasis_eq_iff`. It has `finrank ℤ L` columns,
which form a basis of `L`. -/
noncomputable def hermiteBasis : Matrix (Fin m) (Fin (Module.finrank ℤ L)) ℤ :=
  (exists_isHermiteNormalForm_finrank L).choose

/-- The Hermite basis of `L` is in Hermite normal form. -/
@[simp]
theorem isHermiteNormalForm_hermiteBasis : L.hermiteBasis.IsHermiteNormalForm :=
  (exists_isHermiteNormalForm_finrank L).choose_spec.1

/-- The column lattice of the Hermite basis of `L` is `L`. -/
@[simp]
theorem range_mulVecLin_hermiteBasis : LinearMap.range L.hermiteBasis.mulVecLin = L :=
  (exists_isHermiteNormalForm_finrank L).choose_spec.2

variable {L}

/-- A vector lies in `L` if and only if it is an integer combination of the columns of the Hermite
basis of `L`, with unique coefficients. -/
theorem mem_iff_hermite {x : Fin m → ℤ} : x ∈ L ↔ ∃! c, L.hermiteBasis *ᵥ c = x := by
  conv_lhs => rw [← L.range_mulVecLin_hermiteBasis]
  exact (mulVec_injective_iff.mpr
    L.isHermiteNormalForm_hermiteBasis.linearIndependent_cols).mem_range_iff_existsUnique

/-- **Characterisation of the Hermite basis.** A matrix `H` with `k` columns is, together with
`k`, the Hermite basis of `L` if and only if it is in Hermite normal form with column lattice
`L`. -/
theorem sigma_mk_hermiteBasis_eq_iff {H : Matrix (Fin m) (Fin k) ℤ} :
    (⟨_, L.hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨k, H⟩ ↔
      H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = L := by
  refine ⟨fun h ↦ ?_, fun ⟨hH, hHL⟩ ↦
    L.isHermiteNormalForm_hermiteBasis.sigma_mk_eq_of_range_mulVecLin_eq hH
      (L.range_mulVecLin_hermiteBasis.trans hHL.symm)⟩
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨L.isHermiteNormalForm_hermiteBasis, L.range_mulVecLin_hermiteBasis⟩

/-- **Characterisation of the Hermite basis.** A matrix with `finrank ℤ L` columns is the Hermite
basis of `L` if and only if it is in Hermite normal form with column lattice `L`. -/
theorem hermiteBasis_eq_iff {H : Matrix (Fin m) (Fin (Module.finrank ℤ L)) ℤ} :
    L.hermiteBasis = H ↔ H.IsHermiteNormalForm ∧ LinearMap.range H.mulVecLin = L := by
  rw [← sigma_mk_hermiteBasis_eq_iff, Sigma.mk.inj_iff]
  simp

/-- Sublattices of `ℤ^m` are determined by their Hermite bases. -/
theorem sigma_mk_hermiteBasis_inj :
    (⟨_, L.hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨_, L'.hermiteBasis⟩ ↔ L = L' := by
  rw [sigma_mk_hermiteBasis_eq_iff]
  simp [eq_comm]

/-- The zero sublattice has the empty Hermite basis. -/
@[simp]
theorem sigma_mk_hermiteBasis_bot :
    (⟨_, (⊥ : Submodule ℤ (Fin m → ℤ)).hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨0, 0⟩ :=
  sigma_mk_hermiteBasis_eq_iff.mpr ⟨isHermiteNormalForm_of_fin_zero _, by
    ext x
    simp⟩

/-- The full lattice `ℤ^m` has the identity matrix as its Hermite basis. -/
@[simp]
theorem sigma_mk_hermiteBasis_top :
    (⟨_, (⊤ : Submodule ℤ (Fin m → ℤ)).hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨m, 1⟩ :=
  sigma_mk_hermiteBasis_eq_iff.mpr ⟨IsHermiteNormalForm.one, by simp⟩

end Submodule

namespace Matrix

variable {m n k : ℕ}

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
      have hAs' : ⇑A.mulVecLin ∘ s = H.col := funext fun j ↦ by
        rw [Function.comp_apply, mulVecLin_apply, hs]
      rw [hAs']
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
    simp [U, Matrix.mul_apply, mulVec, dotProduct, Module.Basis.toMatrix_apply]
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

/-- The *Hermite basis* of an integer matrix `A`: the unique matrix in Hermite normal form whose
column lattice is that of `A`, see `Matrix.IsHermiteNormalForm.sigma_mk_hermiteBasis_eq`. It is the
Hermite basis `Submodule.hermiteBasis` of the column lattice of `A`, and has `A.rank` columns,
which is by definition the rank of that lattice. -/
noncomputable def hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin A.rank) ℤ :=
  (LinearMap.range A.mulVecLin).hermiteBasis

variable {A : Matrix (Fin m) (Fin n) ℤ}

/-- The Hermite basis of `A` is in Hermite normal form. -/
@[simp]
theorem isHermiteNormalForm_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    A.hermiteBasis.IsHermiteNormalForm :=
  (LinearMap.range A.mulVecLin).isHermiteNormalForm_hermiteBasis

/-- The column lattice of the Hermite basis of `A` is that of `A`. -/
@[simp]
theorem range_mulVecLin_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    LinearMap.range A.hermiteBasis.mulVecLin = LinearMap.range A.mulVecLin :=
  (LinearMap.range A.mulVecLin).range_mulVecLin_hermiteBasis

/-- The Hermite basis of `A` is the Hermite matrix of a Hermite decomposition of `A`. -/
theorem exists_isHermiteDecomposition_hermiteBasis (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ U : GL (Fin n) ℤ, IsHermiteDecomposition A A.hermiteBasis U ↑U⁻¹ :=
  (isHermiteNormalForm_hermiteBasis A).exists_isHermiteDecomposition
    (range_mulVecLin_hermiteBasis A).symm

/-- A vector lies in the column lattice of `A` if and only if it is an integer combination of the
columns of the Hermite basis of `A`, with unique coefficients. -/
theorem mem_range_iff_hermite {x : Fin m → ℤ} :
    x ∈ LinearMap.range A.mulVecLin ↔ ∃! c, A.hermiteBasis *ᵥ c = x :=
  Submodule.mem_iff_hermite

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

/-- Two integer matrices have the same Hermite basis, with the same number of columns, if and only
if they have the same column lattice. -/
theorem sigma_mk_hermiteBasis_eq_iff {n' : ℕ} {B : Matrix (Fin m) (Fin n') ℤ} :
    (⟨A.rank, A.hermiteBasis⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨B.rank, B.hermiteBasis⟩ ↔
      LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  refine ⟨fun h ↦ ?_, hermiteBasis_eq_of_range_eq⟩
  simpa using congrArg (fun H : Σ k, Matrix (Fin m) (Fin k) ℤ ↦ LinearMap.range H.2.mulVecLin) h

/-! ### Examples -/

/-- The sublattice `2ℤ` of `ℤ` has the Hermite basis `(2)`. -/
example : (⟨_, (Submodule.span ℤ {![2]} : Submodule ℤ (Fin 1 → ℤ)).hermiteBasis⟩ :
    Σ k, Matrix (Fin 1) (Fin k) ℤ) = ⟨1, !![2]⟩ := by
  refine Submodule.sigma_mk_hermiteBasis_eq_iff.mpr ⟨IsHermitePivotedBy.isHermiteNormalForm
    (p := id) ⟨strictMono_id, by decide, by decide, by decide, by decide⟩, ?_⟩
  rw [range_mulVecLin, Set.range_unique]
  congr
  ext i
  simp [Fin.fin_one_eq_zero i]

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
