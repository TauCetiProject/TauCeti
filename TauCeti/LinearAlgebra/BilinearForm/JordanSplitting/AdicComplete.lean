/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.AdicComplete
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import Mathlib.Data.Matrix.Block
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.Submodule.Compl
import TauCeti.Order.SupIndep

/-!
# Jordan splittings over an adically complete local domain

Let `R` be a local domain, `π`-adically complete for a nonzero `π` with `2 ∣ π`; for instance
`R = ℤ_[2]` and `π = 2`, or `R = ℤ_[p]` and `π = p` with `p` odd, where `2` is a unit. Let `B` be a
symmetric form on a finite free module with a Jordan splitting `N` with respect to `π` whose
constituents have index at most `j`, the constituent of index `j` being even at its own scale:
`2 π ^ j` divides `B w w` for `w ∈ N j`. A linear map carrying `B` to a symmetric form `C` modulo
`π ^ (j + 1)`, and the self-pairings modulo `2 π ^ (j + 1)`, is congruent modulo `π` to one
carrying `B` exactly to `C` (`LinearMap.BilinForm.IsJordanSplitting.exists_isometry_of_dvd_sub`),
and two such forms related by approximate isometries in both directions are isometric
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_of_dvd_sub`).

The main application is to two constituents `N j` and `N (j + 1)` that are both even at their own
scales. Projecting along the constituents of index above `j` then carries `B` to the sum of the
constituents of index at most `j` to exactly this precision, so this sum is an isometry invariant
of `B`, although the individual constituents need not be
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent`). At `π = 2`
the parity condition is type II, and a pair of consecutive constituents of type II, possibly zero,
is where a Conway–Sloane 2-adic symbol breaks into trains: the constituents in the trains below
such a break form an isometry invariant of a dyadic lattice.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_isometry_of_dvd_sub`: an approximate isometry out
  of such a form is congruent modulo `π` to an exact one.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_of_dvd_sub`: two such forms related by
  approximate isometries in both directions are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent`: below two
  consecutive constituents that are even at their own scales, the sum of the constituents of a
  Jordan splitting is an isometry invariant.

## Implementation notes

In a basis adapted to the splitting, the Gram matrix of `B` is the block diagonal matrix of the
rescaled constituents `π ^ i • Uᵢ`, with `Uᵢ` unimodular. The block diagonal matrix of the
`π ^ (j - i) • Uᵢ⁻¹` is then a symmetric matrix with even diagonal whose product with it is
`π ^ j • 1`, which is the hypothesis of `LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {B : BilinForm R M} {N : ℕ → Submodule R M} {π : R}

section Domain

variable [IsDomain R] [IsLocalRing R]

/-- A form on a finite free module which is the orthogonal internal direct sum of finitely many
submodules `P i`, each `π ^ e i`-modular with `e i ≤ j`, those with `e i = j` being even at their
own scale, has a Gram matrix `G` and a symmetric matrix `H` with even diagonal such that
`G * H = π ^ j • 1`. -/
private theorem exists_basis_toMatrix_mul_eq_of_isInternal [Module.Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (hπ : π ≠ 0) (h2 : 2 ∣ π) {o : Type} [Finite o] [DecidableEq o]
    {P : o → Submodule R M}
    (hP : DirectSum.IsInternal P) (horth : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', B x y = 0)
    {e : o → ℕ} (hmod : ∀ i, (B.restrict (P i)).IsModular (π ^ e i)) {j : ℕ} (hle : ∀ i, e i ≤ j)
    (heven : ∀ i, e i = j → ∀ w ∈ P i, 2 * π ^ j ∣ B w w) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι R M) (H : Matrix ι ι R),
      B.toMatrix b * H = π ^ j • 1 ∧ H.IsSymm ∧ ∀ i, 2 ∣ H i i := by
  classical
  have : Fintype o := Fintype.ofFinite o
  have hπ' : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ
  have hfree (i : o) : Module.Finite R (P i) ∧ Module.Free R (P i) :=
    (P i).finite_free_of_isCompl
      (hP.submodule_iSupIndep.isCompl_biSup_ne hP.submodule_iSup_eq_top i)
  have (i : o) := (hfree i).1
  have (i : o) := (hfree i).2
  -- The unimodular rescalings `C i` of the summands and their Gram matrices `U i`.
  choose C hC hCp using fun i ↦ isModular_def.mp (hmod i)
  let d (i : o) := Module.finBasis R (P i)
  let U (i : o) := (C i).toMatrix (d i)
  have hCapp (i : o) (x y : P i) : π ^ e i * C i x y = B x y := by
    simpa using LinearMap.congr_fun₂ (hC i) x y
  have hUdet (i : o) : IsUnit (U i).det := (d i).isUnit_det_of_isPerfPair (C i) (hCp i)
  have hUs (i : o) : (U i).IsSymm := by
    ext a a'
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ' (e i))).mp ?_
    simp only [U, Matrix.transpose_apply, toMatrix_apply, hCapp, hB.eq (d i a : M)]
  let b := hP.collectedBasis d
  refine ⟨_, inferInstance, inferInstance, b,
    Matrix.blockDiagonal' fun i : o ↦ π ^ (j - e i) • (U i)⁻¹, ?_, ?_, ?_⟩
  · -- The Gram matrix is block diagonal, with blocks `π ^ e i • U i`.
    have hG : B.toMatrix b = Matrix.blockDiagonal' fun i : o ↦ π ^ e i • U i := by
      ext ⟨i, a⟩ ⟨i', a'⟩
      rw [toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
      by_cases hii : i = i'
      · subst hii
        simp [Matrix.blockDiagonal'_apply_eq, U, toMatrix_apply, ← hCapp]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hii]
        exact horth _ _ hii _ (d i a).2 _ (d i' a').2
    rw [hG, ← Matrix.blockDiagonal'_mul]
    have (i : o) : π ^ e i • U i * π ^ (j - e i) • (U i)⁻¹ = π ^ j • (1 : Matrix _ _ R) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, Nat.add_sub_cancel' (hle i),
        Matrix.mul_nonsing_inv _ (hUdet i)]
    simp only [this]
    have := Matrix.blockDiagonal'_smul (π ^ j)
      (1 : ∀ i : o, Matrix (Fin (finrank R (P i))) (Fin (finrank R (P i))) R)
    rwa [Matrix.blockDiagonal'_one] at this
  · rw [Matrix.IsSymm, Matrix.blockDiagonal'_transpose]
    simp only [Matrix.transpose_smul, Matrix.transpose_nonsing_inv, (hUs _).eq]
  · rintro ⟨i, a⟩
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul]
    rcases (hle i).lt_or_eq with hij | hij
    · exact ((h2.trans (dvd_pow_self π (by omega)))).mul_right _
    · -- A summand of scale `π ^ j` is even, and so is the inverse of its rescaled Gram matrix.
      refine dvd_mul_of_dvd_right ((hUs i).two_dvd_inv_apply_self (hUdet i) (fun a ↦ ?_) a) _
      obtain ⟨c, hc⟩ := heven i hij (d i a) (d i a).2
      refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ' (e i))).mp ?_⟩
      simp only [U, toMatrix_apply]
      rw [hCapp, hc, ← hij]
      ring

/-- The case of `exists_basis_toMatrix_mul_eq_of_isInternal` for a Jordan splitting, indexed by its
nonzero constituents. -/
private theorem IsJordanSplitting.exists_basis_toMatrix_mul_eq [Module.Free R M]
    [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ≠ 0) (h2 : 2 ∣ π)
    {j : ℕ} (htop : ∀ i, j < i → N i = ⊥) (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι R M) (H : Matrix ι ι R),
      B.toMatrix b * H = π ^ j • 1 ∧ H.IsSymm ∧ ∀ i, 2 ∣ H i i := by
  have : Finite {i // N i ≠ ⊥} := h.hasFiniteSupport.to_subtype
  exact exists_basis_toMatrix_mul_eq_of_isInternal hB hπ h2
    (DirectSum.isInternal_ne_bot_iff.mpr h.isInternal)
    (fun i i' hii ↦ h.apply_eq_zero i i' fun h ↦ hii (Subtype.ext h)) (e := fun i ↦ i)
    (fun i ↦ h.isModular i) (fun i ↦ not_lt.mp fun hj ↦ i.2 (htop i hj)) fun i hi ↦ hi ▸ heven

/-- **Approximate isometries out of a Jordan splitting.** Let `R` be a local domain, `π`-adically
complete for a nonzero `π` with `2 ∣ π`, for instance `ℤ_[2]` with `π = 2`. Let `B` be a symmetric
form on a finite free module with a Jordan splitting `N` with respect to `π` whose constituents
have index at most `j`, the one of index `j` being even at its own scale. If a linear map `φ`
carries `B` to a symmetric form `C` modulo `π ^ (j + 1)`, and the self-pairings modulo
`2 * π ^ (j + 1)`, then a linear map `ψ ≡ φ` modulo `π` carries `B` exactly to `C`. -/
theorem IsJordanSplitting.exists_isometry_of_dvd_sub [IsAdicComplete (Ideal.span {π}) R]
    [Module.Free R M] [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm)
    (hπ : π ≠ 0) (h2 : 2 ∣ π) {j : ℕ} (htop : ∀ i, j < i → N i = ⊥)
    (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) {C : BilinForm R M'} (hC : C.IsSymm) (φ : M →ₗ[R] M')
    (h₁ : ∀ x y, π ^ (j + 1) ∣ B x y - C (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ B x x - C (φ x) (φ x)) :
    ∃ τ : M →ₗ[R] M, ∀ x y, C (φ (x + π • τ x)) (φ (y + π • τ y)) = B x y := by
  obtain ⟨ι, _, _, b, H, hH, hHs, hHd⟩ := h.exists_basis_toMatrix_mul_eq hB hπ h2 htop heven
  exact hC.exists_isometry_of_dvd_sub π hB b hH hHs hHd φ h₁ h₂

/-- **Forms with Jordan splittings related by approximate isometries are isometric.** Let `R` be a
local domain, `π`-adically complete for a nonzero `π` with `2 ∣ π`, for instance `ℤ_[2]` with
`π = 2`. Let `B` and `B'` be symmetric forms on finite free modules with Jordan splittings `N` and
`N'` with respect to `π` whose constituents have index at most `j`, those of index `j` being even
at their own scale. If linear maps in both directions carry each form to the other modulo
`π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)`, then `B` and `B'` are isometric. -/
theorem IsJordanSplitting.equivalent_of_dvd_sub [IsAdicComplete (Ideal.span {π}) R]
    [Module.Free R M] [Module.Finite R M] [Module.Free R M'] [Module.Finite R M']
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm) (hB' : B'.IsSymm) (hπ : π ≠ 0) (h2 : 2 ∣ π)
    {j : ℕ} (htop : ∀ i, j < i → N i = ⊥) (htop' : ∀ i, j < i → N' i = ⊥)
    (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) (heven' : ∀ w ∈ N' j, 2 * π ^ j ∣ B' w w)
    (φ : M →ₗ[R] M') (h₁ : ∀ x y, π ^ (j + 1) ∣ B x y - B' (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ B x x - B' (φ x) (φ x))
    (φ' : M' →ₗ[R] M) (h₁' : ∀ x y, π ^ (j + 1) ∣ B' x y - B (φ' x) (φ' y))
    (h₂' : ∀ x, 2 * π ^ (j + 1) ∣ B' x x - B (φ' x) (φ' x)) :
    B.Equivalent B' := by
  obtain ⟨ι, _, _, b, H, hH, hHs, hHd⟩ := h.exists_basis_toMatrix_mul_eq hB hπ h2 htop heven
  obtain ⟨ι', _, _, b', H', hH', hH's, hH'd⟩ :=
    h'.exists_basis_toMatrix_mul_eq hB' hπ h2 htop' heven'
  exact hB.equivalent_of_dvd_sub π hπ hB' b b' hH hHs hHd hH' hH's hH'd φ' h₁' h₂' φ h₁ h₂

end Domain

/-- The sums of the constituents of a Jordan splitting of index at most `j` and at least `j + 1`
are complementary. -/
private theorem IsJordanSplitting.isCompl_biSup_Iic_biSup_Ici (h : B.IsJordanSplitting π N)
    (j : ℕ) : IsCompl (⨆ i ∈ Set.Iic j, N i) (⨆ i ∈ Set.Ici (j + 1), N i) := by
  refine ⟨h.isInternal.submodule_iSupIndep.disjoint_biSup_biSup
    (Set.disjoint_left.mpr fun i hi hi' ↦ by simp_all; omega), codisjoint_iff.mpr ?_⟩
  rw [← iSup_union, show Set.Iic j ∪ Set.Ici (j + 1) = Set.univ by ext; simp; omega]
  simpa using h.isInternal.submodule_iSup_eq_top

/-- Projecting to the sum of the constituents of index at most `j`, along those of index above `j`,
preserves the form modulo `π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)` when the
constituent of index `j + 1` is even at its own scale and `2 ∣ π`. -/
private theorem IsJordanSplitting.dvd_sub_apply_projectionOnto (h : B.IsJordanSplitting π N)
    (h2 : 2 ∣ π) {j : ℕ} (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w) (x y : M) :
    π ^ (j + 1) ∣ B x y - B ((⨆ i ∈ Set.Iic j, N i).projectionOnto _
      (h.isCompl_biSup_Iic_biSup_Ici j) x) ((⨆ i ∈ Set.Iic j, N i).projectionOnto _
      (h.isCompl_biSup_Iic_biSup_Ici j) y) ∧
    2 * π ^ (j + 1) ∣ B x x - B ((⨆ i ∈ Set.Iic j, N i).projectionOnto _
      (h.isCompl_biSup_Iic_biSup_Ici j) x) ((⨆ i ∈ Set.Iic j, N i).projectionOnto _
      (h.isCompl_biSup_Iic_biSup_Ici j) x) := by
  set hc := h.isCompl_biSup_Iic_biSup_Ici j
  have hdisj : Disjoint (Set.Iic j) (Set.Ici (j + 1)) :=
    Set.disjoint_left.mpr fun i hi hi' ↦ by simp_all; omega
  -- Write `x = p x + q x` with `q x` in the constituents of index above `j`.
  set p := (⨆ i ∈ Set.Iic j, N i).projectionOnto _ hc
  have hq (x : M) : x - p x ∈ ⨆ i ∈ Set.Ici (j + 1), N i := by
    simpa [p, Submodule.coe_projectionOnto_apply] using Submodule.sub_projection_mem hc x
  have hsub (x y : M) : B x y - B (p x) (p y) = B (x - p x) (y - p y) := by
    have h₁ := B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj (p x).2 (hq y)
    have h₂ := B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj.symm (hq x) (p y).2
    simp only [map_sub, LinearMap.sub_apply] at h₁ h₂ ⊢
    linear_combination h₁ + h₂
  refine ⟨hsub x y ▸ h.pow_dvd_apply_of_mem_biSup (hq x) _, hsub x x ▸ ?_⟩
  -- The constituent of index `j + 1` is even, and the others above it have scale `π ^ (j + 2)`.
  have hset : Set.Ici (j + 1) = insert (j + 1) (Set.Ici (j + 2)) := by
    ext i
    simp only [Set.mem_Ici, Set.mem_insert_iff]
    omega
  have hx := hq x
  rw [hset, iSup_insert] at hx
  obtain ⟨a, ha, d, hd, had⟩ := Submodule.mem_sup.mp hx
  have hdisj' : Disjoint ({j + 1} : Set ℕ) (Set.Ici (j + 2)) := by simp
  rw [← had]
  simp only [map_add, LinearMap.add_apply,
    B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj' (by simpa using ha) hd,
    B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj'.symm hd (by simpa using ha),
    add_zero, zero_add]
  refine dvd_add (hnext a ha) ((mul_dvd_mul_right h2 _).trans ?_)
  rw [← pow_succ']
  exact h.pow_dvd_apply_of_mem_biSup hd d

/-- For a Jordan splitting with `2 ∣ π`, the constituent of index `j` is even at its own scale
exactly when every vector pairing into `π ^ j R` has self-pairing divisible by `2 * π ^ j`. -/
private theorem IsJordanSplitting.forall_two_mul_pow_dvd_iff (h : B.IsJordanSplitting π N)
    (hπ : π ∈ nonZeroDivisors R) (h2 : 2 ∣ π) {j : ℕ} :
    (∀ w ∈ N j, 2 * π ^ j ∣ B w w) ↔ ∀ x : M, (∀ y, π ^ j ∣ B x y) → 2 * π ^ j ∣ B x x := by
  refine ⟨fun heven x hx ↦ ?_, fun H w hw ↦ H w (h.pow_dvd_apply hw)⟩
  obtain ⟨f, -, hf, -⟩ := h.exists_pow_succ_dvd_sub hπ j
  have := ((mul_dvd_mul_right h2 _).trans (by rw [← pow_succ'])).trans (hf x x hx hx)
  simpa using dvd_add this (heven _ (f x).2)

/-- Parity of the constituent of index `j` at its own scale, in the sense of `2 * π ^ j`
dividing the self-pairings, is an isometry invariant when `2 ∣ π`. -/
private theorem IsJordanSplitting.forall_two_mul_pow_dvd_of_equivalent
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hBB' : B.Equivalent B') (hπ : π ∈ nonZeroDivisors R)
    (h2 : 2 ∣ π) {j : ℕ} (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) :
    ∀ w ∈ N' j, 2 * π ^ j ∣ B' w w := by
  obtain ⟨ε⟩ := hBB'
  refine (h'.forall_two_mul_pow_dvd_iff hπ h2).mpr fun x hx ↦ ?_
  obtain ⟨x, rfl⟩ := ε.surjective x
  simp only [IsometryEquiv.coe_toLinearEquiv, ε.map_app] at hx ⊢
  exact (h.forall_two_mul_pow_dvd_iff hπ h2).mp heven x fun y ↦ by simpa using hx (ε y)

/-- The sum of the constituents of index at most `j` of a Jordan splitting, the one of index `j`
being even at its own scale, satisfies the hypothesis of
`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`. -/
private theorem IsJordanSplitting.exists_basis_restrict_biSup_Iic [IsDomain R] [IsLocalRing R]
    [Module.Free R M] [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm)
    (hπ : π ≠ 0) (h2 : 2 ∣ π) {j : ℕ} (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι R ↥(⨆ i ∈ Set.Iic j, N i))
      (H : Matrix ι ι R), (B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b * H = π ^ j • 1 ∧
      H.IsSymm ∧ ∀ i, 2 ∣ H i i := by
  classical
  set A := ⨆ i ∈ Set.Iic j, N i
  obtain ⟨_, _⟩ := A.finite_free_of_isCompl (h.isCompl_biSup_Iic_biSup_Ici j)
  have : Finite (Set.Iic j) := (Set.finite_Iic j).to_subtype
  -- `A` is the orthogonal internal sum of the constituents of index at most `j`.
  have hmap (i : Set.Iic j) : ((N i).comap A.subtype).map A.subtype = N i := by
    rw [Submodule.map_comap_subtype, inf_of_le_right (le_biSup N i.2)]
  refine exists_basis_toMatrix_mul_eq_of_isInternal (hB.restrict A) hπ h2
    (DirectSum.isInternal_biSup_submodule_of_iSupIndep (Set.Iic j)
      (h.isInternal.submodule_iSupIndep.comp Subtype.val_injective))
    (fun i i' hii x hx y hy ↦ h.apply_eq_zero i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy)
    (e := fun i ↦ i) (fun i ↦ ?_) (fun i ↦ i.2) fun i hi w hw ↦ heven _ (hi ▸ hw)
  exact isModular_restrict_map_subtype_iff.mp ((hmap i).symm ▸ h.isModular i)

/-- **The constituents below two consecutive constituents of type II.** Let `R` be a local domain,
`π`-adically complete for a nonzero `π` with `2 ∣ π`, for instance `ℤ_[2]` with `π = 2`. Let `B` be
a symmetric form on a finite free module, isometric to a form `B'`, and let `N` and `N'` be Jordan
splittings of `B` and `B'` with respect to `π`. Suppose that the constituents `N j` and `N (j + 1)`
are even at their own scales (of type II, possibly zero). Then the sums of the constituents of index
at most `j` of the two splittings are isometric. The parity hypotheses are isometry invariants, so
they are only assumed for `N`.

At `π = 2`, such a pair of constituents is where a Conway–Sloane 2-adic symbol breaks into trains,
so the part of a dyadic lattice in the trains below the break is an isometry invariant. Neither
hypothesis can be dropped. Over `ℤ_[2]`, `!![0, 1; 1, 0] ⊥ ⟨2⟩ ≅ !![2, 1; 1, 2] ⊥ ⟨-6⟩`, while
the constituents of index `0`, of type II, are not isometric. Also
`⟨1⟩ ⊥ !![0, 2; 2, 0] ≅ ⟨5⟩ ⊥ !![4, 2; 2, 4]`, while the constituents `⟨1⟩` and `⟨5⟩` of index
`0`, of type I, are not isometric. -/
theorem IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent [IsDomain R]
    [IsLocalRing R] [IsAdicComplete (Ideal.span {π}) R] [Module.Free R M] [Module.Finite R M]
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm) (hBB' : B.Equivalent B') (hπ : π ≠ 0)
    (h2 : 2 ∣ π) {j : ℕ} (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w)
    (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w) :
    (B.restrict (⨆ i ∈ Set.Iic j, N i)).Equivalent (B'.restrict (⨆ i ∈ Set.Iic j, N' i)) := by
  have hπ' : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ
  obtain ⟨ε⟩ := _root_.id hBB'
  have : Module.Free R M' := .of_equiv ε.toLinearEquiv
  have : Module.Finite R M' := .equiv ε.toLinearEquiv
  have hB' : B'.IsSymm := ⟨fun x y ↦ by
    rw [← ε.symm.map_app, ← ε.symm.map_app, hB.eq]⟩
  have heven' := h.forall_two_mul_pow_dvd_of_equivalent h' hBB' hπ' h2 heven
  have hnext' := h.forall_two_mul_pow_dvd_of_equivalent h' hBB' hπ' h2 hnext
  obtain ⟨ι, _, _, b, H, hH, hHs, hHd⟩ := h.exists_basis_restrict_biSup_Iic hB hπ h2 heven
  obtain ⟨ι', _, _, b', H', hH', hH's, hH'd⟩ := h'.exists_basis_restrict_biSup_Iic hB' hπ h2 heven'
  -- Projecting along the constituents of index above `j` gives approximate isometries.
  have hproj := h.dvd_sub_apply_projectionOnto h2 hnext
  have hproj' := h'.dvd_sub_apply_projectionOnto h2 hnext'
  set p := (⨆ i ∈ Set.Iic j, N i).projectionOnto _ (h.isCompl_biSup_Iic_biSup_Ici j)
  set p' := (⨆ i ∈ Set.Iic j, N' i).projectionOnto _ (h'.isCompl_biSup_Iic_biSup_Ici j)
  refine (hB.restrict _).equivalent_of_dvd_sub π hπ (hB'.restrict _) b b' hH hHs hHd hH' hH's
    hH'd (p ∘ₗ ε.symm.toLinearMap ∘ₗ Submodule.subtype _) (fun x y ↦ ?_) (fun x ↦ ?_)
    (p' ∘ₗ ε.toLinearMap ∘ₗ Submodule.subtype _) (fun x y ↦ ?_) (fun x ↦ ?_)
  · simpa [ε.symm.map_app] using (hproj (ε.symm x) (ε.symm y)).1
  · simpa [ε.symm.map_app] using (hproj (ε.symm x) (ε.symm x)).2
  · simpa [ε.map_app] using (hproj' (ε x) (ε y)).1
  · simpa [ε.map_app] using (hproj' (ε x) (ε x)).2

end LinearMap.BilinForm
