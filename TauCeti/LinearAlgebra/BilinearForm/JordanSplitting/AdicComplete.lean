/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.AdicComplete
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.Order.CompleteLattice.Basic

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

The constituents above the break are an isometry invariant as well
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Ici_of_equivalent`). This is
the same theorem applied to the dual lattices scaled by `π ^ m`, with `m` bounding the indices of
the nonzero constituents: the scaled dual has the constituents `π ^ (m - i) • Uᵢ⁻¹` in reverse
order and of the same parities, and isometric forms have isometric scaled duals
(`LinearMap.BilinForm.equivalent_iff_equivalent_of_toMatrix_mul_eq_smul`). So two forms are
isometric exactly when their two sides of a break are
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_equivalent_restrict_biSup_Iic_and_Ici`):
at `π = 2`, the classification of dyadic lattices reduces to lattices whose 2-adic symbol has a
single train.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_isometry_of_dvd_sub`: an approximate isometry out
  of such a form is congruent modulo `π` to an exact one.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_of_dvd_sub`: two such forms related by
  approximate isometries in both directions are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent`: below two
  consecutive constituents that are even at their own scales, the sum of the constituents of a
  Jordan splitting is an isometry invariant.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Ici_of_equivalent`: so is the
  sum of the constituents above them.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_equivalent_restrict_biSup_Iic_and_Ici`:
  across such a break, two forms are isometric exactly when the sums on either side are.

## Implementation notes

In a basis adapted to the splitting, the Gram matrix of `B` is the block diagonal matrix of the
rescaled constituents `π ^ i • Uᵢ`, with `Uᵢ` unimodular. The block diagonal matrix of the
`π ^ (j - i) • Uᵢ⁻¹` is then a symmetric matrix with even diagonal whose product with it is
`π ^ j • 1` (`LinearMap.BilinForm.exists_basis_toMatrix_mul_eq_of_isInternal`), which is the
hypothesis of `LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`. With `j = m` the block
diagonal matrix of the `π ^ (m - i) • Uᵢ⁻¹` is the Gram matrix of the scaled dual form, built
constituent by constituent as an orthogonal sum.

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

/-- The case of `exists_basis_toMatrix_mul_eq_of_isInternal` for a Jordan splitting, indexed by its
nonzero constituents. -/
private theorem IsJordanSplitting.exists_basis_toMatrix_mul_eq [Module.Free R M]
    [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ≠ 0) (h2 : 2 ∣ π)
    {j : ℕ} (htop : ∀ i, j < i → N i = ⊥) (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι R M) (H : Matrix ι ι R),
      B.toMatrix b * H = π ^ j • 1 ∧ H.IsSymm ∧ ∀ i, 2 ∣ H i i := by
  have : Finite {i // N i ≠ ⊥} := h.hasFiniteSupport.to_subtype
  obtain ⟨ι, _, _, b, H, hH, hHs, hHd⟩ := exists_basis_toMatrix_mul_eq_of_isInternal hB hπ
    (DirectSum.isInternal_ne_bot_iff.mpr h.isInternal)
    (fun i i' hii ↦ h.apply_eq_zero i i' fun h ↦ hii (Subtype.ext h)) (e := fun i ↦ i)
    (fun i ↦ h.isModular i) (fun i ↦ not_lt.mp fun hj ↦ i.2 (htop i hj))
  exact ⟨ι, _, _, b, H, hH, hHs, hHd h2 fun i hi ↦ hi ▸ heven⟩

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

section Dual

/-! ### The scaled dual of a Jordan splitting -/

variable [IsLocalRing R]

/-- **The scaled dual of a Jordan splitting.** Let `B` be a symmetric form on a finite free module
over a local ring with a Jordan splitting `N` with respect to a non-zero-divisor `π` whose
constituents have index at most `m`. Write the constituent `N i` as `π ^ i • Uᵢ` in a basis, with
`Uᵢ` unimodular. The form `D` which is `π ^ (m - i) • Uᵢ⁻¹` on `N i`, in the same basis, and for
which the `N i` are orthogonal is a symmetric form with the Jordan splitting `k ↦ N (m - k)`: it is
`B` read on its dual lattice and scaled by `π ^ m`. On each constituent the Gram matrices of `B`
and `D` multiply to `π ^ m • 1`, and a constituent even at its own scale for `B` is even at its own
scale for `D`, by `Matrix.IsSymm.two_dvd_inv_apply_self`. -/
private theorem IsJordanSplitting.exists_dual [Module.Free R M] [Module.Finite R M]
    (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ∈ nonZeroDivisors R) {m : ℕ}
    (htop : ∀ i, m < i → N i = ⊥) :
    ∃ D : BilinForm R M, D.IsSymm ∧
      D.IsJordanSplitting π (fun k ↦ if k ≤ m then N (m - k) else ⊥) ∧
      (∀ i k, i ≠ k → ∀ x ∈ N i, ∀ y ∈ N k, D x y = 0) ∧
      (∀ i ≤ m, ∃ d : Basis (Fin (finrank R (N i))) R (N i),
        (B.restrict (N i)).toMatrix d * (D.restrict (N i)).toMatrix d = π ^ m • 1) ∧
      ∀ i ≤ m, (∀ w ∈ N i, 2 * π ^ i ∣ B w w) → ∀ w ∈ N i, 2 * π ^ (m - i) ∣ D w w := by
  have (i : ℕ) := h.finite i
  have (i : ℕ) := h.free i
  -- The unimodular rescalings `C i` of the constituents and their Gram matrices `U i`.
  choose C hC hCp using fun i ↦ isModular_def.mp (h.isModular i)
  let d (i : ℕ) := Module.finBasis R (N i)
  let U (i : ℕ) := (C i).toMatrix (d i)
  have hCapp (i : ℕ) (x y : N i) : π ^ i * C i x y = B x y := by
    simpa using LinearMap.congr_fun₂ (hC i) x y
  have hUdet (i : ℕ) : IsUnit (U i).det := (d i).isUnit_det_of_isPerfPair (C i) (hCp i)
  have hUs (i : ℕ) : (U i).IsSymm := by
    ext a a'
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ i)).mp ?_
    simp only [U, Matrix.transpose_apply, toMatrix_apply, hCapp, hB.eq (d i a : M)]
  -- The form `E i` on `N i` with Gram matrix `π ^ (m - i) • (U i)⁻¹`, and `D` their orthogonal sum.
  let E (i : ℕ) : BilinForm R (N i) := Matrix.toBilin (d i) (π ^ (m - i) • (U i)⁻¹)
  have hEapp (i : ℕ) (a a' : Fin (finrank R (N i))) :
      E i (d i a) (d i a') = π ^ (m - i) * (U i)⁻¹ a a' := by
    rw [← toMatrix_apply, toMatrix_toBilin, Matrix.smul_apply, smul_eq_mul]
  have hEs (i : ℕ) : (E i).IsSymm := (Matrix.isSymm_toBilin_iff_isSymm (d i)).mpr <| by
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_nonsing_inv, (hUs i).eq]
  obtain ⟨D, hres, horth, hDs⟩ := exists_forall_restrict_eq_of_isInternal h.isInternal E
  have hmod : ∀ k ≤ m, (D.restrict (N (m - k))).IsModular (π ^ k) := fun k hk ↦ by
    -- The constituent of index `k ≤ m` is `N (m - k)`, with the form `π ^ k • (U (m - k))⁻¹`.
    rw [hres]
    refine (d (m - k)).isModular_of_isUnit_det (fun a a' ↦ ?_)
      (Matrix.isUnit_nonsing_inv_det _ (hUdet (m - k)))
    rw [hEapp, Nat.sub_sub_self hk]
  refine ⟨D, hDs hEs, isJordanSplitting_reverse h.isInternal htop horth hmod, horth,
    fun i hi ↦ ⟨d i, ?_⟩, fun i hi heven w hw ↦ ?_⟩
  · have hBU : (B.restrict (N i)).toMatrix (d i) = π ^ i • U i := by
      ext a a'
      simp [U, toMatrix_apply, ← hCapp]
    rw [hres i, toMatrix_toBilin, hBU, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add,
      Nat.add_sub_cancel' hi, Matrix.mul_nonsing_inv _ (hUdet i)]
  · -- `U i` has even diagonal, hence so does its inverse, and the norm ideal of `E i` lies in
    -- `2 π ^ (m - i) R`.
    have hUd (a : Fin (finrank R (N i))) : 2 ∣ U i a a := by
      obtain ⟨c, hc⟩ := heven _ (d i a).2
      refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ i)).mp ?_⟩
      simp only [U, toMatrix_apply]
      rw [hCapp, hc]
      ring
    have hDw : D w w = E i ⟨w, hw⟩ ⟨w, hw⟩ := by
      rw [← hres i, restrict_apply, LinearMap.domRestrict_apply]
    rw [hDw]
    refine (hEs i).two_mul_dvd_apply_self_of_forall_dvd_basis (d i) (fun a a' ↦ ?_) (fun a ↦ ?_) _
    · exact hEapp i a a' ▸ dvd_mul_right _ _
    · rw [hEapp, mul_comm 2]
      exact mul_dvd_mul_left _ (Matrix.IsSymm.two_dvd_inv_apply_self (hUs i) (hUdet i) hUd a)

end Dual

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
  obtain ⟨ι, _, _, b, H, hH, hHs, hHd⟩ := h.exists_basis_restrict_biSup_Iic hB hπ j
  obtain ⟨ι', _, _, b', H', hH', hH's, hH'd⟩ := h'.exists_basis_restrict_biSup_Iic hB' hπ j
  -- Projecting along the constituents of index above `j` gives approximate isometries.
  have hproj (x y : M) := h.pow_succ_dvd_sub_apply_projectionOnto j x y
  have hproj₂ := h.two_mul_pow_succ_dvd_sub_apply_projectionOnto h2 hnext
  have hproj' (x y : M') := h'.pow_succ_dvd_sub_apply_projectionOnto j x y
  have hproj'₂ := h'.two_mul_pow_succ_dvd_sub_apply_projectionOnto h2 hnext'
  set p := (⨆ i ∈ Set.Iic j, N i).projectionOnto _ (h.isCompl_biSup_Iic_biSup_Ici j)
  set p' := (⨆ i ∈ Set.Iic j, N' i).projectionOnto _ (h'.isCompl_biSup_Iic_biSup_Ici j)
  refine (hB.restrict _).equivalent_of_dvd_sub π hπ (hB'.restrict _) b b' hH hHs (hHd h2 heven)
    hH' hH's (hH'd h2 heven') (p ∘ₗ ε.symm.toLinearMap ∘ₗ Submodule.subtype _) (fun x y ↦ ?_)
    (fun x ↦ ?_) (p' ∘ₗ ε.toLinearMap ∘ₗ Submodule.subtype _) (fun x y ↦ ?_) (fun x ↦ ?_)
  · simpa [ε.symm.map_app] using hproj (ε.symm x) (ε.symm y)
  · simpa [ε.symm.map_app] using hproj₂ (ε.symm x)
  · simpa [ε.map_app] using hproj' (ε x) (ε y)
  · simpa [ε.map_app] using hproj'₂ (ε x)

/-- **The constituents above two consecutive constituents of type II.** Let `R` be a local domain,
`π`-adically complete for a nonzero `π` with `2 ∣ π`, for instance `ℤ_[2]` with `π = 2`. Let `B` be
a symmetric form on a finite free module, isometric to a form `B'`, and let `N` and `N'` be Jordan
splittings of `B` and `B'` with respect to `π`. Suppose that the constituents `N j` and `N (j + 1)`
are even at their own scales (of type II, possibly zero). Then the sums of the constituents of index
at least `j + 1` of the two splittings are isometric.

This is the counterpart of `IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent` on the
other side of the break: at `π = 2`, the part of a dyadic lattice in the trains above a break is an
isometry invariant as well. -/
theorem IsJordanSplitting.equivalent_restrict_biSup_Ici_of_equivalent [IsDomain R]
    [IsLocalRing R] [IsAdicComplete (Ideal.span {π}) R] [Module.Free R M] [Module.Finite R M]
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm) (hBB' : B.Equivalent B') (hπ : π ≠ 0)
    (h2 : 2 ∣ π) {j : ℕ} (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w)
    (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w) :
    (B.restrict (⨆ i ∈ Set.Ici (j + 1), N i)).Equivalent
      (B'.restrict (⨆ i ∈ Set.Ici (j + 1), N' i)) := by
  have hπ' : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ
  obtain ⟨ε⟩ := _root_.id hBB'
  have : Module.Free R M' := .of_equiv ε.toLinearEquiv
  have : Module.Finite R M' := .equiv ε.toLinearEquiv
  have hB' : B'.IsSymm := ⟨fun x y ↦ by
    rw [← ε.symm.map_app, ← ε.symm.map_app, hB.eq]⟩
  -- A common bound `m ≥ j + 1` for the indices of the nonzero constituents of both splittings.
  obtain ⟨m, hjm, htop, htop'⟩ : ∃ m, j + 1 ≤ m ∧ (∀ i, m < i → N i = ⊥) ∧
      ∀ i, m < i → N' i = ⊥ := by
    obtain ⟨a, ha⟩ := h.hasFiniteSupport.bddAbove
    obtain ⟨a', ha'⟩ := h'.hasFiniteSupport.bddAbove
    refine ⟨j + 1 + a + a', by omega, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · by_contra hne
      have := ha hne
      omega
    · by_contra hne
      have := ha' hne
      omega
  -- The scaled duals `D` and `D'` are isometric, since `B` and `B'` are.
  obtain ⟨D, hDs, hD, hDo, hBD, hDeven⟩ := h.exists_dual hB hπ' htop
  obtain ⟨D', -, hD', hD'o, hBD', -⟩ := h'.exists_dual hB' hπ' htop'
  obtain ⟨_, _, _, b, hb⟩ := exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal h.isInternal
    h.hasFiniteSupport h.apply_eq_zero hDo fun i hi ↦
      (hBD i (not_lt.mp fun hlt ↦ hi (htop i hlt))).elim fun d hd ↦ ⟨_, _, _, d, hd⟩
  obtain ⟨_, _, _, b', hb'⟩ := exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal
    h'.isInternal h'.hasFiniteSupport h'.apply_eq_zero hD'o fun i hi ↦
      (hBD' i (not_lt.mp fun hlt ↦ hi (htop' i hlt))).elim fun d hd ↦ ⟨_, _, _, d, hd⟩
  have hDD' : D.Equivalent D' :=
    (equivalent_iff_equivalent_of_toMatrix_mul_eq_smul b b' (pow_mem hπ' m) hb hb').mp hBB'
  -- In `D`, the constituents `N (j + 1)` and `N j` have indices `m - (j + 1)` and `m - j`, and
  -- they are still even at their own scales.
  have hevenD : ∀ w ∈ (fun k ↦ if k ≤ m then N (m - k) else ⊥) (m - (j + 1)),
      2 * π ^ (m - (j + 1)) ∣ D w w := by
    intro w hw
    simp only [show m - (j + 1) ≤ m by omega, ↓reduceIte, Nat.sub_sub_self hjm] at hw
    exact hDeven (j + 1) hjm hnext w hw
  have hnextD : ∀ w ∈ (fun k ↦ if k ≤ m then N (m - k) else ⊥) (m - (j + 1) + 1),
      2 * π ^ (m - (j + 1) + 1) ∣ D w w := by
    intro w hw
    have e₁ : m - (j + 1) + 1 = m - j := by omega
    have e₂ : m - (m - j) = j := by omega
    simp only [e₁, e₂, show m - j ≤ m by omega, ↓reduceIte] at hw ⊢
    exact hDeven j (by omega) heven w hw
  have hlow := hD.equivalent_restrict_biSup_Iic_of_equivalent hD' hDs hDD' hπ h2 hevenD hnextD
  rw [TauCeti.biSup_Iic_ite_tsub_eq_biSup_Icc N hjm,
    TauCeti.biSup_Iic_ite_tsub_eq_biSup_Icc N' hjm] at hlow
  -- Back from the duals to `B` and `B'`, on the constituents of index in `[j + 1, m]`.
  obtain ⟨_, _, _, c, hc⟩ := exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul
    h.isInternal.submodule_iSupIndep h.apply_eq_zero hDo (Set.finite_Icc (j + 1) m) fun i hi ↦
      (hBD i hi.2).elim fun d hd ↦ ⟨_, _, _, d, hd⟩
  obtain ⟨_, _, _, c', hc'⟩ := exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul
    h'.isInternal.submodule_iSupIndep h'.apply_eq_zero hD'o (Set.finite_Icc (j + 1) m) fun i hi ↦
      (hBD' i hi.2).elim fun d hd ↦ ⟨_, _, _, d, hd⟩
  rw [TauCeti.biSup_Ici_eq_biSup_Icc N htop, TauCeti.biSup_Ici_eq_biSup_Icc N' htop']
  exact (equivalent_iff_equivalent_of_toMatrix_mul_eq_smul c c' (pow_mem hπ' m) hc hc').mpr hlow

/-- Across a break between two consecutive constituents that are even at their own scales, the
isometry class of a form is that of its two sides: the constituents of index at most `j` and those
of index at least `j + 1`. At `π = 2` this reduces the classification of dyadic lattices to that
of the lattices whose Conway–Sloane 2-adic symbol has a single train. -/
theorem IsJordanSplitting.equivalent_iff_equivalent_restrict_biSup_Iic_and_Ici [IsDomain R]
    [IsLocalRing R] [IsAdicComplete (Ideal.span {π}) R] [Module.Free R M] [Module.Finite R M]
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm) (hπ : π ≠ 0) (h2 : 2 ∣ π) {j : ℕ}
    (heven : ∀ w ∈ N j, 2 * π ^ j ∣ B w w) (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w) :
    B.Equivalent B' ↔
      (B.restrict (⨆ i ∈ Set.Iic j, N i)).Equivalent (B'.restrict (⨆ i ∈ Set.Iic j, N' i)) ∧
      (B.restrict (⨆ i ∈ Set.Ici (j + 1), N i)).Equivalent
        (B'.restrict (⨆ i ∈ Set.Ici (j + 1), N' i)) := by
  refine ⟨fun hBB' ↦ ⟨h.equivalent_restrict_biSup_Iic_of_equivalent h' hB hBB' hπ h2 heven hnext,
    h.equivalent_restrict_biSup_Ici_of_equivalent h' hB hBB' hπ h2 heven hnext⟩, ?_⟩
  -- Conversely, the two sides are orthogonal summands, so isometries of them add up.
  rintro ⟨hlow, hup⟩
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  have hdisj : Disjoint (Set.Iic j) (Set.Ici (j + 1)) :=
    Set.disjoint_left.mpr fun i hi hi' ↦ by simp_all; omega
  let P : Fin 2 → Submodule R M := ![⨆ i ∈ Set.Iic j, N i, ⨆ i ∈ Set.Ici (j + 1), N i]
  let P' : Fin 2 → Submodule R M' := ![⨆ i ∈ Set.Iic j, N' i, ⨆ i ∈ Set.Ici (j + 1), N' i]
  refine equivalent_of_isInternal (N := P) (N' := P')
    ((DirectSum.isInternal_submodule_iff_isCompl P zero_ne_one huniv).mpr
      (h.isCompl_biSup_Iic_biSup_Ici j))
    ((DirectSum.isInternal_submodule_iff_isCompl P' zero_ne_one huniv).mpr
      (h'.isCompl_biSup_Iic_biSup_Ici j)) ?_ ?_ fun i ↦ ?_
  · intro i k hik x hx y hy
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact apply_eq_zero_of_mem_biSup B h.apply_eq_zero hdisj hx hy
    · exact apply_eq_zero_of_mem_biSup B h.apply_eq_zero hdisj.symm hx hy
    · exact absurd rfl hik
  · intro i k hik x hx y hy
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact apply_eq_zero_of_mem_biSup B' h'.apply_eq_zero hdisj hx hy
    · exact apply_eq_zero_of_mem_biSup B' h'.apply_eq_zero hdisj.symm hx hy
    · exact absurd rfl hik
  · fin_cases i
    exacts [hlow, hup]

end LinearMap.BilinForm
