/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SubspaceLattice

import Mathlib.RingTheory.Complex
import TauCeti.Analysis.ExteriorPower.Nonarchimedean
import TauCeti.InformationTheory.Coding.GeneratorParityCheck
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.LinearAlgebra.Pi
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.FinitePlace.Ideal

/-!
# The covolume of the lattice of integral points of a number-field subspace

Let `K` be a number field of degree `D = [K : ℚ]` with `r₂` complex places, let `ι` be a finite
linearly ordered coordinate type, and let `W` be a `K`-subspace of `ι → K` of dimension `m`. Inside
the Euclidean Minkowski span `W.euclideanSpan` of `W`, the saturated integral lattice
`W.integerLattice` (`W ∩ 𝓞_K^ι`) is a discrete full `ℤ`-lattice of rank `D * m`. Schmidt's
covolume identity computes its Euclidean covolume in terms of the discriminant of `K` and the
Arakelov height of `W`:

```text
covolume W.integerLattice = ((2⁻¹) ^ r₂ * √|discr K|) ^ m * W.subspaceHeight ^ D
                          = covolume (mixedEmbedding.integerLattice K) ^ m *
                              W.relativeSubspaceArakelovHeight.
```

Over `ℚ` (`D = 1`, `r₂ = 0`, `discr ℚ = 1`), this recovers `Submodule.covolume_intLattice`:
`covolume V.intLattice = V.subspaceHeight`. Over a
general number field, no freeness of `W ∩ 𝓞_K^ι` over `𝓞 K` is assumed: choosing a Steinitz
pseudo-basis `W ∩ 𝓞_K^ι = ⊕ k, J k • b k` (`Submodule.exists_pseudoBasis_integerPoints`), the
norms `N(J k)` appear both in the archimedean change-of-basis determinant from the ideal lattices
`J k` and in the nonarchimedean Plücker product of `b`, cancelling in the product formula for
`W.relativeSubspaceArakelovHeight`.

For the kernel of a `K`-matrix `A`, combining Schmidt's identity with Hodge duality of heights
(`Submodule.subspaceHeight_euclideanDual`) expresses the covolume of the lattice of integral
solutions of `A x = 0` directly through the height of the row space of `A`, without any rank
assumption on `A`. This is the arithmetic input to Siegel's lemma and its basis forms over number
fields.

## Main results

* `Submodule.covolume_integerLattice`: Schmidt's formula
  `ZLattice.covolume W.integerLattice = ((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ finrank K W *
    W.subspaceHeight ^ finrank ℚ K`.
* `Submodule.covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight`: the same
  identity written in terms of `ZLattice.covolume (mixedEmbedding.integerLattice K)` and
  `W.relativeSubspaceArakelovHeight`.
* `Submodule.covolume_integerLattice_bot`, `Submodule.covolume_integerLattice_top`: the boundary
  cases `W = ⊥` (covolume `1`) and `W = ⊤` (`#ι`-th power of the ring-of-integers covolume).
* `Submodule.covolume_intLattice_eq_covolume_integerLattice`, `Submodule.covolume_intLattice`: over
  `ℚ`, the covolume of `V.intLattice` in `V.realSpan` agrees with that of `V.integerLattice` in
  `V.euclideanSpan` and equals `V.subspaceHeight`.
* `Matrix.covolume_integerLattice_ker_mulVecLin`: the covolume of the lattice of integral solutions
  of `A x = 0` in terms of the absolute height of the row space of `A`.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3, Theorem 1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* L. Fukshansky, *Siegel's lemma with additional conditions*, J. Number Theory **120** (2006),
  13–25, §3, (17).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §2.8 and Appendix C.2.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §6.1 and §13.

The rational specialization `Submodule.covolume_intLattice` is adapted from Ralf Stephan's
`ArithmeticHeights/RationalLattice.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0).
-/

public section

noncomputable section

open Complex IsDedekindDomain MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace nonZeroDivisors

namespace Submodule

section FinitePlaces

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

omit [LinearOrder ι] in
/-- Denominator-clearing bound for the inverse of a `v`-adic maximal-minor pivot submatrix of a
scaled Steinitz pseudo-basis. -/
private theorem apply_nonsing_inv_pivot_le_one {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hW : W.IsIntegerPseudoBasis b J)
    (v : FinitePlace K) {a : Fin p → 𝓞 K}
    (ha_eq : ∀ k,
      v (a k : K) * (v.maximalIdeal.asIdeal.absNorm : ℝ) ^
        multiplicity v.maximalIdeal.asIdeal (J k) = 1)
    {e : Fin p → ι}
    (hPx : ∀ i j,
      v ((((Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j).submatrix id e)⁻¹ *
          Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j) i j) ≤ 1)
    (i k : Fin p) :
    v (((Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j).submatrix id e)⁻¹ i k) ≤ 1 := by
  set x : Matrix (Fin p) ι K := Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j
  set P := x.submatrix id e
  obtain ⟨d, hd_val, hd_int⟩ := v.exists_apply_eq_one_forall_mul_mem_range (hPx i)
  let w : W := ∑ l : Fin p, ((d : K) * (P⁻¹ i l * (a l : K))) • b l
  have hw_int (j : ι) : (w : ι → K) j ∈ range (algebraMap (𝓞 K) K) := by
    have hwj : (w : ι → K) j = (d : K) * (P⁻¹ * x) i j := by
      have hi : (w : ι → K) j =
          ∑ l : Fin p, ((d : K) * (P⁻¹ i l * (a l : K))) * (b l : ι → K) j := by
        rw [← W.coe_subtype, map_sum, Finset.sum_apply]
        simp only [Submodule.coe_subtype, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      rw [hi, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by simp [x]; ring
    rw [hwj]
    exact hd_int j
  have hrepr : b.repr w k = (d : K) * (P⁻¹ i k * (a k : K)) := by
    simp [w, Finsupp.single_apply]
  obtain ⟨c, hcJ, hc⟩ := (hW.mem_coeSubmodule_iff w).1 hw_int k
  have hc_le := v.apply_mul_absNorm_pow_le_one hcJ
  have hvc : v (c : K) = v (P⁻¹ i k) * v (a k : K) := by
    have h1 : (c : K) = (d : K) * (P⁻¹ i k * (a k : K)) := hc.trans hrepr
    rw [h1, map_mul, map_mul, hd_val, one_mul]
  calc v (P⁻¹ i k)
      = v (P⁻¹ i k) * (v (a k : K) *
          (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k)) := by
        rw [ha_eq k, mul_one]
    _ = v (c : K) *
          (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k) := by
        rw [hvc, mul_assoc]
    _ ≤ 1 := hc_le

/-- Scaling each vector `b k` of a pseudo-basis `(b, J)` by an element `a k ∈ J k` attaining the
largest value of `v` on `J k` normalizes the local maximum Plücker norm at `v` to `1`. -/
private theorem iSup_apply_plucker_scaled_eq_one {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hW : W.IsIntegerPseudoBasis b J)
    (v : FinitePlace K) {a : Fin p → 𝓞 K} (haJ : ∀ k, a k ∈ J k)
    (ha_eq : ∀ k,
      v (a k : K) * (v.maximalIdeal.asIdeal.absNorm : ℝ) ^
        multiplicity v.maximalIdeal.asIdeal (J k) = 1) :
    (⨆ s, v (plucker (fun k j ↦ (a k : K) * (b k : ι → K) j) s)) = 1 := by
  cases nonempty_fintype ι
  set x : Matrix (Fin p) ι K := Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j
  have ha0 (k : Fin p) : (a k : K) ≠ 0 := fun h0 ↦ by simpa [h0] using ha_eq k
  have hx_li : LinearIndependent K x.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hsum : ∑ l : Fin p, (c l * (a l : K)) • (b l : ι → K) = 0 := by
      ext j
      simpa [x, Matrix.row_apply, Finset.sum_apply, mul_assoc] using congrFun hc j
    have hca := Fintype.linearIndependent_iff.mp
      (b.linearIndependent.map' W.subtype W.ker_subtype) _ hsum k
    exact (mul_eq_zero.mp hca).resolve_right (ha0 k)
  -- Every row of `x` is `(a k : K) • b k ∈ W ∩ (𝓞 K)^ι`, so its entries have `v ≤ 1`.
  have hx_le (k : Fin p) (j : ι) : v (x k j) ≤ 1 := by
    obtain ⟨z, hz⟩ := hW.coe_smul_basis_mem_range ⟨a k, haJ k, rfl⟩ j
    have hzx : x k j = (z : K) := by simpa [x] using hz.symm
    exact hzx ▸ v.apply_le_one z
  obtain ⟨e, hP0, hP_sup, hPx⟩ := v.val.exists_pivot_inv_mul_le_one hx_li
  set P := x.submatrix id e
  have hP_one : v P.det = 1 :=
    P.abv_det_eq_one_of_mul_eq_one v.add_le (Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP0))
      (fun i j ↦ hx_le i (e j)) (apply_nonsing_inv_pivot_le_one b hW v ha_eq hPx)
  simpa [x, Matrix.row_apply, FinitePlace.coe_apply] using hP_sup.symm.trans hP_one

/-- At each finite place `v`, the maximum `v`-adic Plücker coordinate of the `K`-basis `b` from a
pseudo-basis `(b, J)` of `W.integerPoints` equals `∏ k, N(𝔭_v) ^ multiplicity 𝔭_v (J k)`. -/
private theorem iSup_apply_plucker_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : W.IsIntegerPseudoBasis b J) (v : FinitePlace K) :
    (⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) =
      ∏ k : Fin p,
        (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k) := by
  choose a haJ ha_eq using fun k ↦ v.exists_mem_apply_mul_absNorm_pow_eq_one (hJ k)
  have hscale (s : powersetCard ι p) :
      plucker (fun k j ↦ (a k : K) * (b k : ι → K) j) s =
        (∏ k : Fin p, (a k : K)) * plucker (fun k ↦ (b k : ι → K)) s := by
    have hdiag :
        (fun k j ↦ (a k : K) * (b k : ι → K) j) =
          fun k ↦ ∑ l : Fin p, Matrix.diagonal (fun m ↦ (a m : K)) k l • (b l : ι → K) := by
      ext k j
      rw [Finset.sum_apply, Fintype.sum_eq_single k fun l hlk ↦ by simp [Matrix.diagonal, hlk.symm]]
      simp
    rw [hdiag, plucker_sum_smul, Matrix.det_diagonal]
  have hsup := iSup_apply_plucker_scaled_eq_one b hW v haJ ha_eq
  simp_rw [hscale, map_mul, map_prod] at hsup
  rw [← Real.mul_iSup_of_nonneg (Finset.prod_nonneg fun k _ ↦ apply_nonneg v _)] at hsup
  have hprod_eq :
      (∏ k : Fin p, v (a k : K)) *
        (∏ k : Fin p,
          (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k)) =
        1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ ↦ ha_eq k
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hprod_eq) (hsup.trans hprod_eq.symm)

/-- Across all finite places, the product of the maximum local Plücker norms of `b` from a
pseudo-basis `(b, J)` of `W.integerPoints` is the product `∏ k, N(J k)` of the norms of the
coefficient ideals. -/
private theorem finprod_iSup_plucker_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : W.IsIntegerPseudoBasis b J) :
    (∏ᶠ v : FinitePlace K, ⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) =
      ∏ k : Fin p, (Ideal.absNorm (J k) : ℝ) := by
  have hsupp (k : Fin p) : Function.HasFiniteMulSupport fun v : FinitePlace K ↦
      (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k) :=
    FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity (hJ k) fun I ↦ (Ideal.absNorm I : ℝ)
  simp_rw [iSup_apply_plucker_of_pseudoBasis b hJ hW]
  rw [finprod_prod_comm _ _ fun k _ ↦ hsupp k]
  exact Finset.prod_congr rfl fun k _ ↦ FinitePlace.finprod_absNorm_pow_multiplicity (R := ℝ) (hJ k)

end FinitePlaces

section Archimedean

variable {K : Type*} [Field K] [NumberField K]

/-- Placewise rearrangement between real/complex place factors and `Fin p → mixedSpace K`. -/
private def equivMixedPi (p : ℕ) :
    (({w : InfinitePlace K // w.IsReal} → Fin p → ℝ) ×
      ({w : InfinitePlace K // w.IsComplex} → Fin p → ℂ)) ≃ₗ[ℝ]
      (Fin p → mixedSpace K) where
  toFun g k := (fun w ↦ g.1 w k, fun w ↦ g.2 w k)
  invFun f := (fun w k ↦ (f k).1 w, fun w k ↦ (f k).2 w)
  left_inv g := by ext w k <;> rfl
  right_inv f := by ext k w <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The real Gram matrix of `b` at a real place `w`. -/
private def realPlaceGramMatrix {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W)
    (w : {w : InfinitePlace K // w.IsReal}) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun k₂ k₁ ↦
    ∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
      (mixedEmbedding K ((b k₁ : ι → K) i)).1 w

/-- The transpose of the Hermitian Gram matrix of `b` at a complex place `w`. -/
private def complexPlaceGramMatrix {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W)
    (w : {w : InfinitePlace K // w.IsComplex}) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun k₂ k₁ ↦
    ∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
      conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)

open scoped Classical in
/-- The real-linear endomorphism of `Fin p → mixedSpace K` acting at each real place by
`realPlaceGramMatrix b w` and at each complex place by `complexPlaceGramMatrix b w`. -/
private def archimedeanGramEndo {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W) :
    Module.End ℝ (Fin p → mixedSpace K) :=
  (equivMixedPi (K := K) p).toLinearMap ∘ₗ
    LinearMap.prodMap
      (LinearMap.pi fun w ↦ (Matrix.toLin' (realPlaceGramMatrix b w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w ↦
        ((Matrix.toLin' (complexPlaceGramMatrix b w)).restrictScalars ℝ).comp (LinearMap.proj w)) ∘ₗ
    (equivMixedPi (K := K) p).symm.toLinearMap

open scoped Classical in
omit [NumberField K] [LinearOrder ι] in
private theorem archimedeanGramEndo_apply_fst {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (f : Fin p → mixedSpace K) (k₂ : Fin p)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ((archimedeanGramEndo b f) k₂).1 w =
      ∑ k₁ : Fin p,
        (∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
          (mixedEmbedding K ((b k₁ : ι → K) i)).1 w) * (f k₁).1 w := by
  simp [archimedeanGramEndo, equivMixedPi, realPlaceGramMatrix, Matrix.mulVec, dotProduct]

open scoped Classical in
omit [NumberField K] [LinearOrder ι] in
private theorem archimedeanGramEndo_apply_snd {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (f : Fin p → mixedSpace K) (k₂ : Fin p)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ((archimedeanGramEndo b f) k₂).2 w =
      ∑ k₁ : Fin p,
        (∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
          conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)) * (f k₁).2 w := by
  simp [archimedeanGramEndo, equivMixedPi, complexPlaceGramMatrix, Matrix.mulVec, dotProduct]

open scoped Classical in
omit [NumberField K] [LinearOrder ι] in
@[simp]
private theorem archimedeanGramEndo_apply_pi_single_fst {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (k₁ k₂ : Fin p) (z : mixedSpace K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ((archimedeanGramEndo b (Pi.single k₁ z)) k₂).1 w =
      (∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
        (mixedEmbedding K ((b k₁ : ι → K) i)).1 w) * z.1 w := by
  rw [archimedeanGramEndo_apply_fst, Fintype.sum_eq_single k₁ fun k hk ↦ by simp [hk]]
  simp

open Classical in
omit [NumberField K] [LinearOrder ι] in
@[simp]
private theorem archimedeanGramEndo_apply_pi_single_snd {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (k₁ k₂ : Fin p) (z : mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ((archimedeanGramEndo b (Pi.single k₁ z)) k₂).2 w =
      (∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
        conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)) * z.2 w := by
  rw [archimedeanGramEndo_apply_snd, Fintype.sum_eq_single k₁ fun k hk ↦ by simp [hk]]
  simp

omit [NumberField K] in
/-- Cauchy–Binet evaluation of the real-place Gram determinant of `b`. -/
private theorem det_realPlaceGramMatrix {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    LinearMap.det (Matrix.toLin' (realPlaceGramMatrix b w)) =
      (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult := by
  let xr : Fin p → ι → ℝ := fun k i ↦ embedding_of_isReal w.2 ((b k : ι → K) i)
  have hmat : realPlaceGramMatrix b w = Matrix.of xr * (Matrix.of xr).transpose := by
    ext k₂ k₁
    simp [realPlaceGramMatrix, xr, Matrix.mul_apply]
  rw [LinearMap.det_toLin', hmat, det_mul_transpose_eq_sum_plucker_mul, mult_isReal, pow_one]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hp : plucker xr s = embedding_of_isReal w.2 (plucker (fun k ↦ (b k : ι → K)) s) :=
    plucker_map (embedding_of_isReal w.2) _ s
  have hnorm :
      ‖embedding_of_isReal w.2 (plucker (fun k ↦ (b k : ι → K)) s)‖ =
        ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ := by
    rw [norm_embedding_of_isReal, norm_embedding_eq]
  rw [hp, ← hnorm, Real.norm_eq_abs, sq_abs, sq]

omit [NumberField K] in
/-- Hermitian Cauchy–Binet evaluation of the real-restricted complex-place Gram determinant of
`b`. -/
private theorem det_restrictScalars_complexPlaceGramMatrix {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (w : {w : InfinitePlace K // w.IsComplex}) :
    LinearMap.det ((Matrix.toLin' (complexPlaceGramMatrix b w)).restrictScalars ℝ) =
      (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult := by
  let xc : Fin p → ι → ℂ := fun k i ↦ w.1.embedding ((b k : ι → K) i)
  have hmat :
      complexPlaceGramMatrix b w = (Matrix.of xc * (Matrix.of xc).conjTranspose).transpose := by
    ext k₂ k₁
    simp [complexPlaceGramMatrix, xc, Matrix.mul_apply]
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hmat, Matrix.det_transpose,
    det_mul_conjTranspose_eq_sum_plucker_mul_star, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq, mult_isComplex]
  have hsum :
      (∑ s, plucker xc s * star (plucker xc s)) =
        ((∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hp : plucker xc s = w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s) :=
      plucker_map w.1.embedding _ s
    rw [hp, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hsum, Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

open scoped Classical in
/-- The determinant of `archimedeanGramEndo b` is the product over all infinite places `w` of the
`w.mult`-th power of the squared Euclidean Plücker norm of `b` at `w`. -/
private theorem det_archimedeanGramEndo {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W) :
    LinearMap.det (archimedeanGramEndo b) =
      ∏ w : InfinitePlace K,
        (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
  rw [archimedeanGramEndo, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_pi,
    LinearMap.det_pi]
  simp_rw [det_realPlaceGramMatrix, det_restrictScalars_complexPlaceGramMatrix]
  have hcomp :
      (∏ w : {w : InfinitePlace K // ¬w.IsReal},
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult) =
      ∏ w : {w : InfinitePlace K // w.IsComplex},
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex) _ _ fun _ ↦ rfl
  rw [← hcomp]
  exact Fintype.prod_subtype_mul_prod_subtype IsReal fun w : InfinitePlace K ↦
    (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult

open scoped Classical in
omit [LinearOrder ι] in
/-- In the `ℤ`-basis `integerLatticeBasisOfPseudoBasis b hJ hW`, the Euclidean Gram matrix on
`Fin p × index K` factors through `archimedeanGramEndo b` and the change-of-basis matrix from
`stdBasis K` to `(J k).mixedLatticeBasis (hJ k)`. -/
private theorem gram_integerLatticeBasisOfPseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : W.IsIntegerPseudoBasis b J) :
    let e := Equiv.sigmaEquivProd (Fin p) (index K)
    let Bstd := (Pi.basis fun _ : Fin p ↦ stdBasis K).reindex e
    let Bideal := (Pi.basis fun k : Fin p ↦ (J k).mixedLatticeBasis (hJ k)).reindex e
    Matrix.gram ℝ (fun q : Fin p × index K ↦
        (integerLatticeBasisOfPseudoBasis b hJ hW q : W.euclideanSpan)) =
      (Bstd.toMatrix Bideal)ᵀ *
        (LinearMap.toMatrix Bstd Bstd (archimedeanGramEndo b))ᵀ *
        Bstd.toMatrix Bideal := by
  intro e Bstd Bideal
  let β := integerLatticeBasisOfPseudoBasis b hJ hW
  let T := archimedeanGramEndo b
  have hBideal (q : Fin p × index K) :
      Bideal q = Pi.single q.1 (mixedEmbedding K ((J q.1).mixedBasisElem (hJ q.1) q.2)) := by
    simp [Bideal, e]
  ext q₁ q₂
  -- Express the Euclidean inner product of `β q₁` and `β q₂` via `mixedInner` and `T (Bideal q₁)`.
  have hinner :
      Matrix.gram ℝ (fun q : Fin p × index K ↦ (β q : W.euclideanSpan)) q₁ q₂ =
        ∑ k : Fin p, mixedInner K ((T (Bideal q₁)) k) (Bideal q₂ k) := by
    have hrhs :
        (∑ k : Fin p, mixedInner K ((T (Bideal q₁)) k) (Bideal q₂ k)) =
          mixedInner K ((T (Bideal q₁)) q₂.1)
            (mixedEmbedding K ((J q₂.1).mixedBasisElem (hJ q₂.1) q₂.2)) := by
      rw [hBideal q₂, Fintype.sum_eq_single q₂.1 fun k hk ↦ by simp [hk, mixedInner_def]]
      simp
    rw [hrhs, Matrix.gram_apply, Submodule.coe_inner, PiLp.inner_apply]
    dsimp only [β]
    simp_rw [coe_integerLatticeBasisOfPseudoBasis_apply, ← mixedInner_toMixed,
      ContinuousLinearEquiv.apply_symm_apply, map_mul, mixedInner_def]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [T, hBideal q₁, archimedeanGramEndo_apply_pi_single_fst, Finset.sum_mul,
        Prod.fst_mul, Pi.mul_apply]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [T, hBideal q₁, archimedeanGramEndo_apply_pi_single_snd, Finset.sum_mul,
        ← Complex.re_sum, Prod.snd_mul, Pi.mul_apply, map_mul]
      congr 1
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
  -- Expand `∑ k, mixedInner K ...` in `Bstd`-coordinates to obtain `(Cᵀ * Mᵀ * C) q₁ q₂`.
  rw [hinner]
  simp_rw [mixedInner_eq_sum_stdBasis_repr K]
  have hdot (f g : Fin p → mixedSpace K) :
      (∑ k : Fin p, ∑ c : index K, (stdBasis K).repr (f k) c * (stdBasis K).repr (g k) c) =
        ∑ r : Fin p × index K, Bstd.repr f r * Bstd.repr g r := by
    conv_rhs => rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun c _ ↦ by simp [Bstd, e]
  rw [hdot]
  have hTB (r : Fin p × index K) :
      Bstd.repr (T (Bideal q₁)) r =
        ∑ s, LinearMap.toMatrix Bstd Bstd T r s * Bstd.toMatrix Bideal s q₁ := by
    have hm := congrFun (LinearMap.toMatrix_mulVec_repr Bstd Bstd T (Bideal q₁)) r
    rw [← hm, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [Basis.toMatrix_apply]
  simp_rw [hTB, ← Basis.toMatrix_apply Bstd Bideal _ q₂, Finset.sum_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

open scoped Classical in
/-- For a pseudo-basis `(b, J)` of `W.integerPoints`, the squared covolume of `W.integerLattice`
factors into the ideal-lattice covolume squares `∏ k, (N(J k) * covolume 𝓞_K) ^ 2` times the
product of archimedean Euclidean Plücker factors. -/
private theorem covolume_integerLattice_sq_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : W.IsIntegerPseudoBasis b J) :
    ZLattice.covolume W.integerLattice ^ 2 =
      (∏ k : Fin p,
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ 2 *
        ∏ w : InfinitePlace K,
          (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
  let e := Equiv.sigmaEquivProd (Fin p) (index K)
  let Bstd := (Pi.basis fun _ : Fin p ↦ stdBasis K).reindex e
  let Bideal_k (k : Fin p) := (J k).mixedLatticeBasis (hJ k)
  let Bideal := (Pi.basis Bideal_k).reindex e
  have hC_det : (Bstd.toMatrix Bideal).det = ∏ k : Fin p, (stdBasis K).det (Bideal_k k) := by
    have hcomp : ⇑Bideal ∘ e = ⇑(Pi.basis Bideal_k) :=
      funext fun x ↦ by rw [Function.comp_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
    have hid : (LinearMap.id : (Fin p → mixedSpace K) →ₗ[ℝ] Fin p → mixedSpace K) =
        LinearMap.piMap fun _ : Fin p ↦ LinearMap.id :=
      LinearMap.ext fun f ↦ funext fun k ↦ by simp
    rw [Basis.toMatrix_reindex', Matrix.det_reindexAlgEquiv, hcomp,
      ← LinearMap.toMatrix_id_eq_basis_toMatrix, hid, LinearMap.toMatrix_piMap,
      Matrix.det_blockDiagonal']
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [LinearMap.toMatrix_id_eq_basis_toMatrix, Basis.det_apply]
  have hC_det_sq :
      (Bstd.toMatrix Bideal).det ^ 2 =
        (∏ k : Fin p,
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ 2 := by
    rw [← sq_abs, hC_det, Finset.abs_prod]
    congr 1
    exact Finset.prod_congr rfl fun k _ ↦ (J k).abs_det_stdBasis_mixedLatticeBasis (hJ k)
  rw [ZLattice.covolume_sq_eq_det_gram W.integerLattice (integerLatticeBasisOfPseudoBasis b hJ hW),
    gram_integerLatticeBasisOfPseudoBasis b hJ hW, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_transpose, mul_right_comm, ← sq, hC_det_sq,
    LinearMap.det_toMatrix Bstd (archimedeanGramEndo b), det_archimedeanGramEndo]

end Archimedean

section MainTheorems

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open Classical in
/-- **Schmidt's covolume identity (relative form).** For any `K`-subspace `W` of `ι → K`, the
covolume of `W.integerLattice` in `W.euclideanSpan` equals the `(finrank K W)`-th power of the
ring-of-integers covolume times the relative Arakelov height of `W`. -/
theorem covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight
    (W : Submodule K (ι → K)) :
    ZLattice.covolume W.integerLattice =
      ZLattice.covolume (mixedEmbedding.integerLattice K) ^ finrank K W *
        W.relativeSubspaceArakelovHeight := by
  obtain ⟨b, J, hJ, hW⟩ := W.exists_pseudoBasis_integerPoints
  set y : powersetCard ι (finrank K W) → K := plucker fun k ↦ (b k : ι → K)
  have hy : y ≠ 0 := (plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis
  have hfin := finprod_iSup_plucker_of_pseudoBasis b hJ hW
  have harch := covolume_integerLattice_sq_of_pseudoBasis b hJ hW
  -- Square the RHS and match `harch` via the local product formula for `arakelovMulHeight y`.
  have hrhs_nonneg :
      0 ≤ ZLattice.covolume (mixedEmbedding.integerLattice K) ^ finrank K W *
        W.relativeSubspaceArakelovHeight :=
    mul_nonneg (pow_nonneg (ZLattice.covolume_pos _ volume).le _)
      (relativeSubspaceArakelovHeight_pos W).le
  have hsq :
      ZLattice.covolume W.integerLattice ^ 2 =
        (ZLattice.covolume (mixedEmbedding.integerLattice K) ^ finrank K W *
          W.relativeSubspaceArakelovHeight) ^ 2 := by
    rw [harch, relativeSubspaceArakelovHeight_eq_arakelovMulHeight_plucker b]
    dsimp only [y] at hfin hy ⊢
    have harak : arakelovMulHeight y =
        (∏ w : InfinitePlace K, (∑ s, ‖w.embedding (y s)‖ ^ 2) ^ ((w.mult : ℝ) / 2)) *
        ∏ᶠ v : FinitePlace K, ⨆ s, v (y s) := by
      rw [arakelovMulHeight_eq hy]; congr!
    -- Rewrite the `((w.mult : ℝ) / 2)`-rpow square at each infinite place as `^ w.mult`.
    have hinf_sq :
        (∏ w : InfinitePlace K,
          (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ ((w.mult : ℝ) / 2)) ^ 2 =
          ∏ w : InfinitePlace K,
            (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
        Nat.cast_ofNat, div_mul_cancel₀ _ two_ne_zero, Real.rpow_natCast]
    have hprod_split :
        (∏ k : Fin (finrank K W),
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) =
          (∏ k : Fin (finrank K W), (Ideal.absNorm (J k) : ℝ)) *
            ZLattice.covolume (mixedEmbedding.integerLattice K) ^ finrank K W := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [harak, mul_pow, mul_pow, hinf_sq, hfin, hprod_split]
    ring
  exact (pow_left_inj₀ (ZLattice.covolume_pos _ volume).le hrhs_nonneg two_ne_zero).mp hsq

open Classical in
/-- **Schmidt's covolume identity.** For a `K`-subspace `W` of `ι → K`, the covolume of the
saturated lattice `W.integerLattice` (`W ∩ 𝓞_K^ι`) in the Euclidean Minkowski span `W.euclideanSpan`
is `((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ finrank K W * W.subspaceHeight ^ finrank ℚ K`. -/
theorem covolume_integerLattice (W : Submodule K (ι → K)) :
    ZLattice.covolume W.integerLattice =
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|discr K|) ^ finrank K W *
        W.subspaceHeight ^ finrank ℚ K := by
  rw [covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
    mixedEmbedding.covolume_integerLattice, subspaceHeight_pow_finrank]

open Classical in
/-- The zero subspace has integral lattice of covolume `1` in its `0`-dimensional real span. -/
@[simp]
theorem covolume_integerLattice_bot :
    ZLattice.covolume (⊥ : Submodule K (ι → K)).integerLattice = 1 := by
  simp [covolume_integerLattice]

open Classical in
/-- The whole space `ι → K` has integral lattice covolume equal to the `#ι`-th power of the
ring-of-integers covolume. -/
theorem covolume_integerLattice_top_eq_covolume_pow :
    ZLattice.covolume (⊤ : Submodule K (ι → K)).integerLattice =
      ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  simp [covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
    Module.finrank_fintype_fun_eq_card]

open Classical in
/-- The whole space `ι → K` has integral lattice covolume
`((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ #ι`. -/
@[simp]
theorem covolume_integerLattice_top :
    ZLattice.covolume (⊤ : Submodule K (ι → K)).integerLattice =
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|discr K|) ^ Fintype.card ι := by
  rw [covolume_integerLattice_top_eq_covolume_pow, mixedEmbedding.covolume_integerLattice]

omit [LinearOrder ι] in
open Classical in
/-- Over `ℚ`, the covolume of `V.intLattice` in `V.realSpan` equals the covolume of
`V.integerLattice` in `V.euclideanSpan`. -/
theorem covolume_intLattice_eq_covolume_integerLattice (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.covolume V.intLattice = ZLattice.covolume V.integerLattice := by
  have he := LinearIsometryEquiv.measurePreserving
    (E := V.euclideanSpan) (F := V.realSpan) V.euclideanSpanEquivRealSpan
  rw [← V.comap_intLattice_euclideanSpanEquivRealSpan]
  exact (ZLattice.covolume_comap V.intLattice volume volume
    (e := V.euclideanSpanEquivRealSpan.toContinuousLinearEquiv) he).symm

end MainTheorems

/-- **The covolume of the lattice of integral points of a rational subspace is its absolute
Euclidean height.** For a subspace `V` of `ℚ^ι`, the lattice `V ∩ ℤ^ι` in the real span of `V`
has covolume `V.subspaceHeight`. -/
theorem covolume_intLattice {ι : Type*} [Fintype ι] [LinearOrder ι] (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.covolume V.intLattice = V.subspaceHeight := by
  classical
  rw [V.covolume_intLattice_eq_covolume_integerLattice, V.covolume_integerLattice,
    IsTotallyReal.nrComplexPlaces_eq_zero, discr_rat, finrank_self]
  norm_num

end Submodule

namespace Matrix

open Set Submodule NumberField

variable {K : Type*} [Field K] [NumberField K] {m ι : Type*} [Finite m] [Fintype ι]
  [LinearOrder ι]

open scoped Classical in
/-- **The covolume of the lattice of integral solutions of `A x = 0` over a number field.**
For any `m × ι` matrix `A` over `K` (without any row-independence assumption), the lattice of
integral solutions `(LinearMap.ker A.mulVecLin).integerLattice` in the real span of `ker A` has
covolume `((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ finrank K (ker A)` times the `[K : ℚ]`-th
power of the absolute Euclidean height of the row space of `A`. -/
theorem covolume_integerLattice_ker_mulVecLin (A : Matrix m ι K) :
    ZLattice.covolume (LinearMap.ker A.mulVecLin).integerLattice =
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|discr K|) ^ finrank K (LinearMap.ker A.mulVecLin) *
        (span K (range A.row)).subspaceHeight ^ finrank ℚ K := by
  cases nonempty_fintype m
  rw [Submodule.covolume_integerLattice, ← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy,
    subspaceHeight_euclideanDual, generatedBy_eq_span_rows]

end Matrix

end
