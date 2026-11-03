/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The determinant of the lower constituents of a Jordan splitting

Let `B` be a symmetric form on a finite free module over a local domain, with a Jordan splitting
`N` with respect to `π`, where `2 ∣ π`. The sum `L₍ⱼ₎` of the constituents of index at most `j` is
not an isometry invariant of `B` when `π = 2`, and neither is its Gram determinant up to squares.
Over `ℤ_[2]`, `⟨1⟩ ⊥ ⟨2⟩ ≅ ⟨3⟩ ⊥ ⟨6⟩`, as the vectors `(1, 1)` and `(-2, 1)` show, while
`3` is not a square. But if one of the constituents `N j` and `N (j + 1)` is even at its own scale
(of type II, possibly zero), then the Gram determinant of `L₍ⱼ₎` is an isometry invariant up to
squares and a factor in `1 + 2πR`
(`LinearMap.BilinForm.IsJordanSplitting.exists_sq_mul_det_toMatrix_eq_of_equivalent`). Over
`ℤ_[2]` the unit part of the determinant of `L₍ⱼ₎` is then an invariant modulo `4`. Conditions on
the determinants of the partial sums `L₍ⱼ₎` of this kind enter O'Meara's classification of
lattices over dyadic local fields (93:28). In the Conway–Sloane calculus of 2-adic symbols, sign
walking across such a `j` multiplies the determinant of `L₍ⱼ₎` by `5`, which is `1` modulo `4`.

The factor `1 + 2πR` cannot be dropped, even though the sum of the constituents of index at most
`j` is an isometry invariant when both `N j` and `N (j + 1)` are of type II
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_biSup_Iic_of_equivalent`). Over
`ℤ_[2]`, `⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`) has its constituent of index `1` of type II,
and `!![0, 1; 1, 0] ⊥ ⟨2⟩ ≅ !![2, 1; 1, 2] ⊥ ⟨-6⟩` has its constituent of index `0` of type II;
in both, the determinants `1, 5` and `-1, 3` of the constituents of index `0` differ by the
nonsquare `5` modulo squares.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_sq_mul_det_toMatrix_eq_of_equivalent`: if `N j`
  or `N (j + 1)` is even at its own scale, then the Gram determinants of the sums of the
  constituents of index at most `j` of Jordan splittings of isometric forms agree up to a square
  and a factor in `1 + 2πR`.

## Implementation notes

Let `ε : B ≅ B'`, let `L₍ⱼ₎` and `K₍ⱼ₎` be the sums of the constituents of index at most `j` of the
two splittings, and let `p` be the projection to `L₍ⱼ₎` along the constituents of index above `j`.
Then `φ = p ∘ ε⁻¹` carries `B'` on `K₍ⱼ₎` to `B` on `L₍ⱼ₎` modulo `π ^ (j + 1)`, and the
self-pairings modulo `2 π ^ (j + 1)` when `N (j + 1)` is of type II
(`LinearMap.BilinForm.IsJordanSplitting.pow_succ_dvd_sub_apply_projectionOnto` and
`LinearMap.BilinForm.IsJordanSplitting.two_mul_pow_succ_dvd_sub_apply_projectionOnto`). So
`Pᵀ G P = G' - π ^ (j + 1) • E` for the Gram matrices `G` and `G'`, the matrix `P` of `φ`, and a
symmetric `E`, with even diagonal when `N (j + 1)` is of type II. The Gram matrix `G'` has a
symmetric partner `H` with `G' * H = π ^ j • 1`, with even diagonal when `N j` is of type II
(`LinearMap.BilinForm.IsJordanSplitting.exists_basis_restrict_biSup_Iic`), and
`Matrix.IsSymm.exists_det_sub_smul_eq_mul_det` compares the determinants.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93, in particular 93:28.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

section Approximate

variable {R A A' : Type*} [CommRing R] [Nontrivial R] [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A'] {C : BilinForm R A} {C' : BilinForm R A'}

/-- **Gram determinants under approximate isometries.** Let `C` and `C'` be symmetric, and let `b₀`
be a finite basis of the domain of `C'` whose Gram matrix times a symmetric matrix `H` is
`π ^ j • 1`, where `π` is a non-zero-divisor with `2 ∣ π`. Let `φ` carry `C'` to `C` modulo
`π ^ (j + 1)`, and suppose that `H` has even diagonal or that `φ` also carries the self-pairings
modulo `2 * π ^ (j + 1)`. Then in any bases of the same size, the Gram determinants `d` of `C` and
`d'` of `C'` satisfy `c ^ 2 * d = (1 + 2 π t) * d'` for some `c` and `t`. -/
theorem IsSymm.exists_sq_mul_det_toMatrix_eq_of_dvd_sub (hC : C.IsSymm) (hC' : C'.IsSymm)
    {π : R} (hπ : π ∈ nonZeroDivisors R) (h2 : 2 ∣ π) {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    (b₀ : Basis ι₀ R A') {j : ℕ} {H : Matrix ι₀ ι₀ R} (hH : C'.toMatrix b₀ * H = π ^ j • 1)
    (hHs : H.IsSymm) (φ : A' →ₗ[R] A) (h₁ : ∀ x y, π ^ (j + 1) ∣ C' x y - C (φ x) (φ y))
    (hd : (∀ k, 2 ∣ H k k) ∨ ∀ x, 2 * π ^ (j + 1) ∣ C' x x - C (φ x) (φ x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R A) (b' : Basis ι R A') :
    ∃ c t : R, c ^ 2 * (C.toMatrix b).det = (1 + 2 * π * t) * (C'.toMatrix b').det := by
  have hπj : π ^ (j + 1) ∈ nonZeroDivisors R := pow_mem hπ (j + 1)
  -- The pullback of `C` along `φ` is `G' - π ^ (j + 1) • E` for a symmetric matrix `E`.
  choose E hE using fun k l ↦ h₁ (b₀ k) (b₀ l)
  have hEs : (Matrix.of E).IsSymm := Matrix.IsSymm.ext fun k l ↦
    (mul_cancel_left_mem_nonZeroDivisors hπj).mp <| by
      rw [Matrix.of_apply, Matrix.of_apply, ← hE, ← hE, hC.eq (φ (b₀ k)), hC'.eq (b₀ k)]
  have hcomp : (C.comp φ φ).toMatrix b₀ = C'.toMatrix b₀ - (π ^ j * π) • Matrix.of E := by
    ext k l
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← pow_succ, ← hE,
      toMatrix_apply, toMatrix_apply, comp_apply, sub_sub_cancel]
  -- `H` or `E` has even diagonal.
  have hd' : (∀ k, 2 ∣ H k k) ∨ ∀ k, 2 ∣ Matrix.of E k k := by
    refine hd.imp_right fun h₂ k ↦ ?_
    obtain ⟨m, hm⟩ := hE k k ▸ h₂ (b₀ k)
    exact ⟨m, (mul_cancel_left_mem_nonZeroDivisors hπj).mp <| by
      rw [Matrix.of_apply, hm]
      ring⟩
  obtain ⟨t, ht⟩ := hHs.exists_det_sub_smul_eq_mul_det hEs hH (pow_mem hπ j) hd' h2
  -- Compare with the given bases, reindexed along `ι ≃ ι₀`.
  let e : ι ≃ ι₀ := b'.indexEquiv b₀
  have hre : (C.toMatrix (b.reindex e)).det = (C.toMatrix b).det := by
    rw [show C.toMatrix (b.reindex e) = Matrix.reindex e e (C.toMatrix b) by
      ext; simp [toMatrix_apply], Matrix.det_reindex_self]
  have hre' : (C'.toMatrix (b'.reindex e)).det = (C'.toMatrix b').det := by
    rw [show C'.toMatrix (b'.reindex e) = Matrix.reindex e e (C'.toMatrix b') by
      ext; simp [toMatrix_apply], Matrix.det_reindex_self]
  rw [← hcomp, det_toMatrix_comp b₀ (b.reindex e), hre] at ht
  refine ⟨(LinearMap.toMatrix b₀ (b.reindex e) φ).det * (b₀.toMatrix (b'.reindex e)).det, t, ?_⟩
  rw [← hre', det_toMatrix_eq_det_sq_mul_det b₀ (b'.reindex e)]
  linear_combination (b₀.toMatrix (b'.reindex e)).det ^ 2 * ht

end Approximate

variable {R M M' : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R M'] {B : BilinForm R M} {N : ℕ → Submodule R M}
  {π : R}

/-- **The determinant of the lower constituents of a Jordan splitting.** Let `R` be a local
domain, `π ≠ 0` with `2 ∣ π`, for instance `ℤ_[2]` with `π = 2`. Let `B` be a symmetric form on a
finite free module, isometric to a form `B'`, and let `N` and `N'` be Jordan splittings of `B` and
`B'` with respect to `π`. Suppose that `N j` or `N (j + 1)` is even at its own scale (of type II,
possibly zero). Then in any bases of the sums of the constituents of index at most `j` of the two
splittings, the Gram determinant `d` of the first and `d'` of the second satisfy
`c ^ 2 * d = (1 + 2 π t) * d'` for some `c` and `t`. Over `ℤ_[2]` the two sums have constituents
of the same ranks, so `d = 2 ^ e u` and `d' = 2 ^ e u'` with units `u` and `u'`, and this says
`u ≡ u'` modulo `4`, since unit squares are `1` modulo `8`.

Neither the hypothesis nor the factor `1 + 2 π t` can be dropped: over `ℤ_[2]`,
`⟨1⟩ ⊥ ⟨2⟩ ≅ ⟨3⟩ ⊥ ⟨6⟩`, both constituents of index `0` and `1` being of type I, and
`⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`, while `3` and `5` are not squares. -/
theorem IsJordanSplitting.exists_sq_mul_det_toMatrix_eq_of_equivalent [Module.Free R M]
    [Module.Finite R M] {B' : BilinForm R M'} {N' : ℕ → Submodule R M'}
    (h : B.IsJordanSplitting π N) (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm)
    (hBB' : B.Equivalent B') (hπ : π ≠ 0) (h2 : 2 ∣ π) {j : ℕ}
    (htype : (∀ w ∈ N j, 2 * π ^ j ∣ B w w) ∨ ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R ↥(⨆ i ∈ Set.Iic j, N i))
    (b' : Basis ι R ↥(⨆ i ∈ Set.Iic j, N' i)) :
    ∃ c t : R, c ^ 2 * ((B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b).det =
      (1 + 2 * π * t) * ((B'.restrict (⨆ i ∈ Set.Iic j, N' i)).toMatrix b').det := by
  have hπ' : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ
  obtain ⟨ε⟩ := _root_.id hBB'
  have : Module.Free R M' := .of_equiv ε.toLinearEquiv
  have : Module.Finite R M' := .equiv ε.toLinearEquiv
  have hB' : B'.IsSymm := ⟨fun x y ↦ by rw [← ε.symm.map_app, ← ε.symm.map_app, hB.eq]⟩
  obtain ⟨ι₀, _, _, b₀, H, hGH, hHs, hHd⟩ := h'.exists_basis_restrict_biSup_Iic hB' hπ j
  -- Project along the constituents of index above `j`, after pulling back by the isometry.
  refine (hB.restrict _).exists_sq_mul_det_toMatrix_eq_of_dvd_sub (hB'.restrict _) hπ' h2 b₀ hGH
    hHs ((⨆ i ∈ Set.Iic j, N i).projectionOnto _ (h.isCompl_biSup_Iic_biSup_Ici j) ∘ₗ
      ε.symm.toLinearMap ∘ₗ Submodule.subtype _) (fun x y ↦ ?_) ?_ b b'
  · simpa [ε.symm.map_app] using h.pow_succ_dvd_sub_apply_projectionOnto j (ε.symm x) (ε.symm y)
  · rcases htype with heven | hnext
    · exact .inl (hHd h2 (h.forall_two_mul_pow_dvd_of_equivalent h' hBB' hπ' h2 heven))
    · refine .inr fun x ↦ ?_
      simpa [ε.symm.map_app] using
        h.two_mul_pow_succ_dvd_sub_apply_projectionOnto h2 hnext (ε.symm x)

end LinearMap.BilinForm
