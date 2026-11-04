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
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.FinitePlace.Ideal
-- Proof-only: lattice scaling and invariants of `ℚ(i)` for the worked sanity checks.
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants

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

Over `ℚ` (`D = 1`, `r₂ = 0`, `discr ℚ = 1`), this recovers `Submodule.covolume_intLattice`. Over a
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
-/

public section

noncomputable section

open Complex IsDedekindDomain MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Set TauCeti TauCeti.NumberField.mixedEmbedding
open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace nonZeroDivisors

namespace Submodule

section FinitePlaces

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- At a finite place `v`, any square matrix with entries in the unit ball of `v` has determinant
of absolute value at most `1`. -/
private theorem apply_det_le_one {p : ℕ} (v : FinitePlace K) (M : Matrix (Fin p) (Fin p) K)
    (hM : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  have hsub : (M.submatrix id id).det = M.det := by simp
  rw [← hsub]
  refine (v.val.det_submatrix_le_iSup_plucker M id).trans ?_
  refine Real.iSup_le (fun s ↦ ?_) zero_le_one
  refine (v.val.plucker_le_prod_iSup (fun x y ↦ FinitePlace.add_le v x y) M.row s).trans ?_
  exact (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
    fun i _ ↦ Real.iSup_le (fun j ↦ hM i j) zero_le_one).trans_eq Finset.prod_const_one

/-- Scaling each vector `b k` of a pseudo-basis `(b, J)` by an element `a k ∈ J k` attaining the
largest value of `v` on `J k` normalizes the local maximum Plücker norm at `v` to `1`. -/
private theorem iSup_apply_plucker_scaled_eq_one {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)}
    (hW : ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k))
    (v : FinitePlace K) {a : Fin p → 𝓞 K} (haJ : ∀ k, a k ∈ J k)
    (ha_eq : ∀ k,
      v (a k : K) * (v.maximalIdeal.asIdeal.absNorm : ℝ) ^
        multiplicity v.maximalIdeal.asIdeal (J k) = 1) :
    (⨆ s, v (plucker (fun k j ↦ (a k : K) * (b k : ι → K) j) s)) = 1 := by
  cases nonempty_fintype ι
  set x : Matrix (Fin p) ι K := Matrix.of fun k j ↦ (a k : K) * (b k : ι → K) j
  have ha0 (k : Fin p) : (a k : K) ≠ 0 := by
    intro h0
    have := ha_eq k
    simp [h0] at this
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
    have hrepr : ∀ k', b.repr ((a k : K) • b k) k' ∈ IsLocalization.coeSubmodule K (J k') := by
      intro k'
      rw [map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with hk'
      · subst hk'
        exact ⟨a k, haJ k, rfl⟩
      · exact zero_mem _
    obtain ⟨z, hz⟩ := (hW ((a k : K) • b k)).2 hrepr j
    have hvz : v (z : K) ≤ 1 := by
      rw [← v.norm_embedding_eq]
      exact FinitePlace.norm_le_one K v.maximalIdeal z
    have hzx : (z : K) = x k j := by simpa [x, Algebra.smul_def] using hz
    rwa [← hzx]
  obtain ⟨e, hP0, hP_sup, hPx⟩ := v.val.exists_pivot_inv_mul_le_one hx_li
  set P := x.submatrix id e
  -- Upper bound: `P` is a submatrix of `x`, so `v P.det ≤ 1`.
  have hP_le : v P.det ≤ 1 := apply_det_le_one v P fun i j ↦ hx_le i (e j)
  -- Lower bound: clear denominators away from `v.maximalIdeal` in each row of `P⁻¹ * x`.
  have hPinv_le (i k : Fin p) : v (P⁻¹ i k) ≤ 1 := by
    set 𝔭 := v.maximalIdeal
    have hval (j : ι) : 𝔭.valuation K ((P⁻¹ * x) i j) ≤ 1 := by
      rw [← FinitePlace.mk_apply_le_one_iff, FinitePlace.mk_maximalIdeal]
      exact hPx i j
    choose n d hnd using fun j ↦ 𝔭.exists_primeCompl_mul_eq_of_integer ((P⁻¹ * x) i j) (hval j)
    let D : 𝔭.asIdeal.primeCompl := ∏ j : ι, d j
    have hD_val : v ((D : 𝓞 K) : K) = 1 := by
      rw [← v.norm_embedding_eq, FinitePlace.norm_eq_one_iff_notMem]
      exact D.2
    let w : W := ∑ l : Fin p, (((D : 𝓞 K) : K) * (P⁻¹ i l * (a l : K))) • b l
    have hw_int (j : ι) : (w : ι → K) j ∈ range (algebraMap (𝓞 K) K) := by
      have hwj : (w : ι → K) j = ((D : 𝓞 K) : K) * (P⁻¹ * x) i j := by
        have hi : (w : ι → K) j =
            ∑ l : Fin p, (((D : 𝓞 K) : K) * (P⁻¹ i l * (a l : K))) * (b l : ι → K) j := by
          rw [← W.coe_subtype, map_sum, Finset.sum_apply]
          rfl
        rw [hi, Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ ↦ by simp [x]; ring
      rw [hwj]
      let q : 𝓞 K := ∏ j' ∈ Finset.univ.erase j, (d j' : 𝓞 K)
      have hD_split : ((D : 𝓞 K) : K) = (q : K) * ((d j : 𝓞 K) : K) := by
        have hD_coe : (D : 𝓞 K) = ∏ j' : ι, (d j' : 𝓞 K) :=
          map_prod (Submonoid.subtype _) d Finset.univ
        rw [hD_coe, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        dsimp only [q]
        push_cast
        ring
      refine ⟨q * n j, ?_⟩
      calc algebraMap (𝓞 K) K (q * n j)
          = (q : K) * ((P⁻¹ * x) i j * ((d j : 𝓞 K) : K)) := by rw [map_mul, ← hnd j]
        _ = ((D : 𝓞 K) : K) * (P⁻¹ * x) i j := by rw [hD_split]; ring
    have hrepr : b.repr w k = ((D : 𝓞 K) : K) * (P⁻¹ i k * (a k : K)) := by
      simp [w, Finsupp.single_apply]
    obtain ⟨c, hcJ, hc⟩ := (hW w).1 hw_int k
    have hc_le := v.apply_mul_absNorm_pow_le_one hcJ
    have hvc : v (c : K) = v (P⁻¹ i k) * v (a k : K) := by
      have h1 : (c : K) = ((D : 𝓞 K) : K) * (P⁻¹ i k * (a k : K)) := hc.trans hrepr
      rw [h1, map_mul, map_mul, hD_val, one_mul]
    calc v (P⁻¹ i k)
        = v (P⁻¹ i k) * (v (a k : K) *
            (𝔭.asIdeal.absNorm : ℝ) ^ multiplicity 𝔭.asIdeal (J k)) := by rw [ha_eq k, mul_one]
      _ = v (c : K) * (𝔭.asIdeal.absNorm : ℝ) ^ multiplicity 𝔭.asIdeal (J k) := by
          rw [hvc, mul_assoc]
      _ ≤ 1 := hc_le
  have hPinv_det_le : v P⁻¹.det ≤ 1 := apply_det_le_one v P⁻¹ hPinv_le
  have hmul_one : v P.det * v P⁻¹.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP0),
      Matrix.det_one, map_one]
  have hP_ge : 1 ≤ v P.det := by
    calc (1 : ℝ) = v P.det * v P⁻¹.det := hmul_one.symm
      _ ≤ v P.det * 1 := mul_le_mul_of_nonneg_left hPinv_det_le (apply_nonneg v _)
      _ = v P.det := mul_one _
  have hP_one : v P.det = 1 := le_antisymm hP_le hP_ge
  simpa [x, Matrix.row_apply, FinitePlace.coe_apply] using hP_sup.symm.trans hP_one

/-- At each finite place `v`, the maximum `v`-adic Plücker coordinate of the `K`-basis `b` from a
pseudo-basis `(b, J)` of `W.integerPoints` equals `∏ k, N(𝔭_v) ^ multiplicity 𝔭_v (J k)`. -/
private theorem iSup_apply_plucker_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k))
    (v : FinitePlace K) :
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
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro l _ hlk
        simp [hlk.symm]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
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
  calc (⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s))
      = 1 * (⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) := (one_mul _).symm
    _ = ((∏ k : Fin p, v (a k : K)) *
          ∏ k : Fin p,
            (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k)) *
          (⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) := by rw [hprod_eq]
    _ = (∏ k : Fin p,
          (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k)) *
          ((∏ k : Fin p, v (a k : K)) * ⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) := by ring
    _ = ∏ k : Fin p,
          (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k) := by
          rw [hsup, mul_one]

/-- Across all finite places, the product of the maximum local Plücker norms of `b` from a
pseudo-basis `(b, J)` of `W.integerPoints` is the product `∏ k, N(J k)` of the norms of the
coefficient ideals. -/
private theorem finprod_iSup_plucker_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k)) :
    (∏ᶠ v : FinitePlace K, ⨆ s, v (plucker (fun k ↦ (b k : ι → K)) s)) =
      ∏ k : Fin p, (Ideal.absNorm (J k) : ℝ) := by
  have hsupp (k : Fin p) : Function.HasFiniteMulSupport fun v : FinitePlace K ↦
      (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k) :=
    FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity (hJ k) fun I ↦ (Ideal.absNorm I : ℝ)
  have hnorm (k : Fin p) :
      (∏ᶠ v : FinitePlace K,
        (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J k)) =
        Ideal.absNorm (J k) := by
    conv_rhs => rw [← FinitePlace.finprod_finitePlace_pow_multiplicity (hJ k)]
    rw [map_finprod _ (FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity (hJ k) (·)),
      Nat.cast_finprod']
    simp
  simp_rw [iSup_apply_plucker_of_pseudoBasis b hJ hW]
  rw [finprod_prod_comm _ _ fun k _ ↦ hsupp k]
  exact Finset.prod_congr rfl fun k _ ↦ hnorm k

end FinitePlaces

section Archimedean

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- `mixedInner` is the standard dot product in the coordinates of `mixedEmbedding.stdBasis K`. -/
private theorem mixedInner_eq_sum_stdBasis_repr (x y : mixedSpace K) :
    mixedInner K x y = ∑ c : index K, (stdBasis K).repr x c * (stdBasis K).repr y c := by
  rw [mixedInner_def, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Fin.sum_univ_two, stdBasis_apply_isComplex_fst, stdBasis_apply_isComplex_fst,
    stdBasis_apply_isComplex_snd, stdBasis_apply_isComplex_snd, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

open scoped Classical in
/-- The change-of-basis determinant from `stdBasis K` to `I.mixedLatticeBasis hI` has absolute
value `N(I) * covolume (mixedEmbedding.integerLattice K)`. -/
private theorem abs_det_stdBasis_mixedLatticeBasis {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    |(stdBasis K).det (I.mixedLatticeBasis hI)| =
      (I.absNorm : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K) := by
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have hvol :
      volume (ZSpan.fundamentalDomain (I.mixedLatticeBasis hI)) =
        ENNReal.ofReal |(stdBasis K).det (I.mixedLatticeBasis hI)| := by
    rw [ZSpan.measure_fundamentalDomain (I.mixedLatticeBasis hI) volume (stdBasis K),
      volume_fundamentalDomain_stdBasis, mul_one]
  have hcov :
      ZLattice.covolume (idealLattice K U) = |(stdBasis K).det (I.mixedLatticeBasis hI)| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
        (I.isAddFundamentalDomain_mixedLatticeBasis hI),
      measureReal_def, hvol, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [← hcov, covolume_idealLattice, covolume_integerLattice]
  simp only [U, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, mul_assoc]

/-- Placewise rearrangement of `Fin p → mixedSpace K` into real and complex place factors. -/
private def equivMixedPi (p : ℕ) :
    (Fin p → mixedSpace K) ≃ₗ[ℝ]
      ({w : InfinitePlace K // w.IsReal} → Fin p → ℝ) ×
        ({w : InfinitePlace K // w.IsComplex} → Fin p → ℂ) where
  toFun f := (fun w k ↦ (f k).1 w, fun w k ↦ (f k).2 w)
  invFun g k := (fun w ↦ g.1 w k, fun w ↦ g.2 w k)
  left_inv f := by ext k w <;> rfl
  right_inv g := by ext w k <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- The real-linear endomorphism of `Fin p → mixedSpace K` acting at each real place by the real
Gram matrix of `b` and at each complex place by the transpose of the Hermitian Gram matrix of
`b`. -/
private def archimedeanGramEndo {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W) :
    Module.End ℝ (Fin p → mixedSpace K) :=
  let Gr (w : {w : InfinitePlace K // w.IsReal}) : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun k₂ k₁ ↦
      ∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
        (mixedEmbedding K ((b k₁ : ι → K) i)).1 w
  let Gc (w : {w : InfinitePlace K // w.IsComplex}) : Matrix (Fin p) (Fin p) ℂ :=
    Matrix.of fun k₂ k₁ ↦
      ∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
        conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)
  (equivMixedPi (K := K) p).symm.toLinearMap ∘ₗ
    LinearMap.prodMap
      (LinearMap.pi fun w ↦ (Matrix.toLin' (Gr w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w ↦ ((Matrix.toLin' (Gc w)).restrictScalars ℝ).comp (LinearMap.proj w)) ∘ₗ
    (equivMixedPi (K := K) p).toLinearMap

open scoped Classical in
omit [NumberField K] [LinearOrder ι] in
private theorem archimedeanGramEndo_apply_fst {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (f : Fin p → mixedSpace K) (k₂ : Fin p)
    (w : {w : InfinitePlace K // w.IsReal}) :
    ((archimedeanGramEndo b f) k₂).1 w =
      ∑ k₁ : Fin p,
        (∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
          (mixedEmbedding K ((b k₁ : ι → K) i)).1 w) * (f k₁).1 w :=
  rfl

open scoped Classical in
omit [NumberField K] [LinearOrder ι] in
private theorem archimedeanGramEndo_apply_snd {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) (f : Fin p → mixedSpace K) (k₂ : Fin p)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    ((archimedeanGramEndo b f) k₂).2 w =
      ∑ k₁ : Fin p,
        (∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
          conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)) * (f k₁).2 w :=
  rfl

open scoped Classical in
/-- The determinant of `archimedeanGramEndo b` is the product over all infinite places `w` of the
`w.mult`-th power of the squared Euclidean Plücker norm of `b` at `w`. -/
private theorem det_archimedeanGramEndo {W : Submodule K (ι → K)} {p : ℕ} (b : Basis (Fin p) K W) :
    LinearMap.det (archimedeanGramEndo b) =
      ∏ w : InfinitePlace K,
        (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
  have hconj := LinearMap.det_conj
    (LinearMap.prodMap
      (LinearMap.pi fun w : {w : InfinitePlace K // w.IsReal} ↦
        (Matrix.toLin' (Matrix.of fun k₂ k₁ : Fin p ↦
          ∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
            (mixedEmbedding K ((b k₁ : ι → K) i)).1 w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w : {w : InfinitePlace K // w.IsComplex} ↦
        ((Matrix.toLin' (Matrix.of fun k₂ k₁ : Fin p ↦
          ∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
            conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w))).restrictScalars ℝ).comp
          (LinearMap.proj w)))
    (equivMixedPi (K := K) p).symm
  have heq : (equivMixedPi (K := K) p).toLinearMap =
      ((equivMixedPi (K := K) p).symm.symm : _ →ₗ[ℝ] _) := rfl
  rw [archimedeanGramEndo]
  dsimp only
  rw [heq, hconj, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  -- Evaluate each real-place factor by Cauchy–Binet.
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      LinearMap.det (Matrix.toLin' (Matrix.of fun k₂ k₁ : Fin p ↦
        ∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
          (mixedEmbedding K ((b k₁ : ι → K) i)).1 w)) =
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult := by
    let xr : Fin p → ι → ℝ := fun k i ↦ embedding_of_isReal w.2 ((b k : ι → K) i)
    have hmat :
        (Matrix.of fun k₂ k₁ : Fin p ↦
          ∑ i : ι, (mixedEmbedding K ((b k₂ : ι → K) i)).1 w *
            (mixedEmbedding K ((b k₁ : ι → K) i)).1 w) =
          Matrix.of xr * (Matrix.of xr).transpose := by
      ext k₂ k₁
      simp [xr, Matrix.mul_apply]
    rw [LinearMap.det_toLin', hmat, det_mul_transpose_eq_sum_plucker_mul, mult_isReal, pow_one]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hp : plucker xr s = embedding_of_isReal w.2 (plucker (fun k ↦ (b k : ι → K)) s) :=
      plucker_map (embedding_of_isReal w.2) _ s
    have hnorm :
        ‖embedding_of_isReal w.2 (plucker (fun k ↦ (b k : ι → K)) s)‖ =
          ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ := by
      rw [norm_embedding_of_isReal, norm_embedding_eq]
    rw [hp, ← hnorm, Real.norm_eq_abs, sq_abs, sq]
  -- Evaluate each complex-place factor by `det_restrictScalars` and Hermitian Cauchy–Binet.
  have hcomplex (w : {w : InfinitePlace K // w.IsComplex}) :
      LinearMap.det ((Matrix.toLin' (Matrix.of fun k₂ k₁ : Fin p ↦
        ∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
          conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w))).restrictScalars ℝ) =
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult := by
    let xc : Fin p → ι → ℂ := fun k i ↦ w.1.embedding ((b k : ι → K) i)
    have hmat :
        (Matrix.of fun k₂ k₁ : Fin p ↦
          ∑ i : ι, (mixedEmbedding K ((b k₁ : ι → K) i)).2 w *
            conj ((mixedEmbedding K ((b k₂ : ι → K) i)).2 w)) =
          (Matrix.of xc * (Matrix.of xc).conjTranspose).transpose := by
      ext k₂ k₁
      simp [xc, Matrix.mul_apply]
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
  simp_rw [hreal, hcomplex]
  have hcomp :
      (∏ w : {w : InfinitePlace K // ¬w.IsReal},
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult) =
      ∏ w : {w : InfinitePlace K // w.IsComplex},
        (∑ s, ‖w.1.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.1.mult :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex) _ _ fun _ ↦ rfl
  rw [← hcomp]
  exact Fintype.prod_subtype_mul_prod_subtype IsReal fun w : InfinitePlace K ↦
    (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult

/-- For a base basis `e` of `M` and a family of bases `v k` of `M`, the change-of-basis matrix on
`Fin p → M` between the product bases reindexed by `Fin p × κ` has determinant
`∏ k, e.det (v k)`. -/
private theorem det_toMatrix_pi_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Type*} [AddCommGroup M] [Module ℝ M] {p : ℕ}
    (e : Basis κ ℝ M) (v : Fin p → Basis κ ℝ M) :
    (((Pi.basis fun _ : Fin p ↦ e).reindex (Equiv.sigmaEquivProd (Fin p) κ)).toMatrix
      ((Pi.basis v).reindex (Equiv.sigmaEquivProd (Fin p) κ))).det =
      ∏ k : Fin p, e.det (v k) := by
  have : Module.Free ℝ M := Module.Free.of_basis e
  have : Module.Finite ℝ M := Module.Finite.of_basis e
  let Bstd := (Pi.basis fun _ : Fin p ↦ e).reindex (Equiv.sigmaEquivProd (Fin p) κ)
  let Bv := (Pi.basis v).reindex (Equiv.sigmaEquivProd (Fin p) κ)
  let Sk (k : Fin p) : M →ₗ[ℝ] M := e.constr ℝ (v k)
  let S : (Fin p → M) →ₗ[ℝ] (Fin p → M) := LinearMap.pi fun k ↦ (Sk k).comp (LinearMap.proj k)
  have hmat : Bstd.toMatrix Bv = LinearMap.toMatrix Bstd Bstd S := by
    ext r q
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    refine DFunLike.congr_fun (congrArg Bstd.repr ?_) r
    ext k
    simp only [Bstd, Bv, S, Sk, Basis.coe_reindex, Function.comp_apply,
      Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with hkq
    · subst hkq
      exact (e.constr_basis ℝ (v q.1) q.2).symm
    · exact (map_zero _).symm
  rw [hmat, LinearMap.det_toMatrix, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← LinearMap.det_toMatrix e (Sk k), Basis.det_apply]
  congr 1
  ext c₁ c₂
  rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply, e.constr_basis]

open scoped Classical in
/-- For a pseudo-basis `(b, J)` of `W.integerPoints`, the squared covolume of `W.integerLattice`
factors into the ideal-lattice covolume squares `∏ k, (N(J k) * covolume 𝓞_K) ^ 2` times the
product of archimedean Euclidean Plücker factors. -/
private theorem covolume_integerLattice_sq_of_pseudoBasis {W : Submodule K (ι → K)} {p : ℕ}
    (b : Basis (Fin p) K W) {J : Fin p → Ideal (𝓞 K)} (hJ : ∀ k, J k ≠ ⊥)
    (hW : ∀ w : W, (∀ i, (w : ι → K) i ∈ range (algebraMap (𝓞 K) K)) ↔
      ∀ k, b.repr w k ∈ IsLocalization.coeSubmodule K (J k)) :
    ZLattice.covolume W.integerLattice ^ 2 =
      (∏ k : Fin p,
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ 2 *
        ∏ w : InfinitePlace K,
          (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
  let β := integerLatticeBasisOfPseudoBasis b hJ hW
  rw [ZLattice.covolume_sq_eq_det_gram W.integerLattice β]
  -- Compare the Gram matrix on `Fin p × index K` with `archimedeanGramEndo b` in `stdBasis K`.
  let Bstd : Basis (Fin p × index K) ℝ (Fin p → mixedSpace K) :=
    (Pi.basis fun _ : Fin p ↦ stdBasis K).reindex (Equiv.sigmaEquivProd (Fin p) (index K))
  let Bideal_k (k : Fin p) : Basis (index K) ℝ (mixedSpace K) := (J k).mixedLatticeBasis (hJ k)
  let Bideal : Basis (Fin p × index K) ℝ (Fin p → mixedSpace K) :=
    (Pi.basis Bideal_k).reindex (Equiv.sigmaEquivProd (Fin p) (index K))
  let T := archimedeanGramEndo b
  have hBideal_apply (q : Fin p × index K) (k : Fin p) :
      Bideal q k =
        if k = q.1 then mixedEmbedding K ((J q.1).mixedBasisElem (hJ q.1) q.2) else 0 := by
    simp only [Bideal, Bideal_k, Basis.coe_reindex, Function.comp_apply,
      Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Pi.single_apply]
    split_ifs with hkq
    · subst hkq
      exact (J q.1).mixedLatticeBasis_apply (hJ q.1) q.2
    · rfl
  have hgram_eq :
      Matrix.gram ℝ (fun q : Fin p × index K ↦ (β q : W.euclideanSpan)) =
        (Bstd.toMatrix Bideal)ᵀ * (LinearMap.toMatrix Bstd Bstd T)ᵀ * Bstd.toMatrix Bideal := by
    ext q₁ q₂
    -- First rewrite the inner product via `mixedInner` and `T (Bideal q₁)`.
    have hinner :
        Matrix.gram ℝ (fun q : Fin p × index K ↦ (β q : W.euclideanSpan)) q₁ q₂ =
          ∑ k : Fin p, mixedInner K ((T (Bideal q₁)) k) (Bideal q₂ k) := by
      -- On the RHS only `k = q₂.1` contributes since `Bideal q₂ k = 0` for `k ≠ q₂.1`.
      have hrhs :
          (∑ k : Fin p, mixedInner K ((T (Bideal q₁)) k) (Bideal q₂ k)) =
            mixedInner K ((T (Bideal q₁)) q₂.1)
              (mixedEmbedding K ((J q₂.1).mixedBasisElem (hJ q₂.1) q₂.2)) := by
        rw [Finset.sum_eq_single q₂.1]
        · simp [hBideal_apply]
        · intro k _ hk
          simp [hBideal_apply, hk, mixedInner_def]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      rw [hrhs, Matrix.gram_apply, Submodule.coe_inner, PiLp.inner_apply]
      dsimp only [β]
      simp_rw [coe_integerLatticeBasisOfPseudoBasis_apply]
      have hterm (i : ι) :
          ⟪(euclidean.toMixed K).symm
              (mixedEmbedding K ((J q₁.1).mixedBasisElem (hJ q₁.1) q₁.2 * (b q₁.1 : ι → K) i)),
            (euclidean.toMixed K).symm
              (mixedEmbedding K ((J q₂.1).mixedBasisElem (hJ q₂.1) q₂.2 * (b q₂.1 : ι → K) i))⟫ =
            mixedInner K
              (mixedEmbedding K ((J q₁.1).mixedBasisElem (hJ q₁.1) q₁.2) *
                mixedEmbedding K ((b q₁.1 : ι → K) i))
              (mixedEmbedding K ((J q₂.1).mixedBasisElem (hJ q₂.1) q₂.2) *
                mixedEmbedding K ((b q₂.1 : ι → K) i)) := by
        rw [← mixedInner_toMixed, ContinuousLinearEquiv.apply_symm_apply,
          ContinuousLinearEquiv.apply_symm_apply, map_mul, map_mul]
      simp_rw [hterm, mixedInner_def]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        have hTw :
            ((T (Bideal q₁)) q₂.1).1 w =
              (∑ i : ι, (mixedEmbedding K ((b q₂.1 : ι → K) i)).1 w *
                (mixedEmbedding K ((b q₁.1 : ι → K) i)).1 w) *
                (mixedEmbedding K ((J q₁.1).mixedBasisElem (hJ q₁.1) q₁.2)).1 w := by
          dsimp only [T]
          rw [archimedeanGramEndo_apply_fst, Finset.sum_eq_single q₁.1]
          · simp [hBideal_apply]
          · intro k _ hk
            simp [hBideal_apply, hk]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        rw [hTw, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [Prod.fst_mul, Pi.mul_apply]
        ring
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        have hTw :
            ((T (Bideal q₁)) q₂.1).2 w =
              (∑ i : ι, (mixedEmbedding K ((b q₁.1 : ι → K) i)).2 w *
                conj ((mixedEmbedding K ((b q₂.1 : ι → K) i)).2 w)) *
                (mixedEmbedding K ((J q₁.1).mixedBasisElem (hJ q₁.1) q₁.2)).2 w := by
          dsimp only [T]
          rw [archimedeanGramEndo_apply_snd, Finset.sum_eq_single q₁.1]
          · simp [hBideal_apply]
          · intro k _ hk
            simp [hBideal_apply, hk]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        rw [hTw, Finset.sum_mul, Finset.sum_mul, ← Complex.re_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [Prod.snd_mul, Pi.mul_apply, map_mul]
        ring
    -- Next express `∑ k, mixedInner K ...` as `(Cᵀ * Mᵀ * C) q₁ q₂` via `Bstd`-coordinates.
    rw [hinner]
    have hdot (f g : Fin p → mixedSpace K) :
        (∑ k : Fin p, mixedInner K (f k) (g k)) =
          ∑ r : Fin p × index K, Bstd.repr f r * Bstd.repr g r := by
      simp_rw [mixedInner_eq_sum_stdBasis_repr]
      conv_rhs => rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
      simp [Bstd]
    rw [hdot]
    have hTB (r : Fin p × index K) :
        Bstd.repr (T (Bideal q₁)) r =
          ∑ s, LinearMap.toMatrix Bstd Bstd T r s * Bstd.toMatrix Bideal s q₁ := by
      have hm := congrFun (LinearMap.toMatrix_mulVec_repr Bstd Bstd T (Bideal q₁)) r
      rw [← hm, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun s _ ↦ by rw [Basis.toMatrix_apply]
    simp_rw [hTB, ← Basis.toMatrix_apply Bstd Bideal _ q₂, Finset.sum_mul]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring
  -- Evaluate `det (Bstd.toMatrix Bideal)` via `det_toMatrix_pi_reindex`.
  have hC_det_sq :
      (Bstd.toMatrix Bideal).det ^ 2 =
        (∏ k : Fin p,
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ 2 := by
    have hC_abs :
        |(Bstd.toMatrix Bideal).det| =
          ∏ k : Fin p,
            (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K) := by
      rw [det_toMatrix_pi_reindex (stdBasis K) Bideal_k, Finset.abs_prod]
      exact Finset.prod_congr rfl fun k _ ↦ abs_det_stdBasis_mixedLatticeBasis (hJ k)
    rw [← sq_abs, hC_abs]
  rw [hgram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    mul_right_comm, ← sq, hC_det_sq, LinearMap.det_toMatrix Bstd T, det_archimedeanGramEndo]

end Archimedean

section MainTheorems

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
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
    rw [arakelovMulHeight_eq hy,
      Subsingleton.elim (Fintype.ofFinite (powersetCard ι (finrank K W))) inferInstance]
    -- Rewrite the `((w.mult : ℝ) / 2)`-rpow square at each infinite place as `^ w.mult`.
    have hinf_sq :
        (∏ w : InfinitePlace K,
          (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^
            ((w.mult : ℝ) / 2)) ^ 2 =
          ∏ w : InfinitePlace K,
            (∑ s, ‖w.embedding (plucker (fun k ↦ (b k : ι → K)) s)‖ ^ 2) ^ w.mult := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
        Nat.cast_ofNat, div_mul_cancel₀ _ two_ne_zero, Real.rpow_natCast]
    have hprod_split :
        (∏ k : Fin (finrank K W),
          (Ideal.absNorm (J k) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K)) =
          (∏ k : Fin (finrank K W), (Ideal.absNorm (J k) : ℝ)) *
            ZLattice.covolume (mixedEmbedding.integerLattice K) ^ finrank K W := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow, mul_pow, hinf_sq, hfin, hprod_split]
    ring
  exact (pow_left_inj₀ (ZLattice.covolume_pos _ volume).le hrhs_nonneg two_ne_zero).mp hsq

open scoped Classical in
/-- **Schmidt's covolume identity.** For a `K`-subspace `W` of `ι → K`, the covolume of the
saturated lattice `W.integerLattice` (`W ∩ 𝓞_K^ι`) in the Euclidean Minkowski span `W.euclideanSpan`
is `((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ finrank K W * W.subspaceHeight ^ finrank ℚ K`. -/
theorem covolume_integerLattice (W : Submodule K (ι → K)) :
    ZLattice.covolume W.integerLattice =
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|discr K|) ^ finrank K W *
        W.subspaceHeight ^ finrank ℚ K := by
  rw [covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
    mixedEmbedding.covolume_integerLattice, subspaceHeight_pow_finrank]

open scoped Classical in
/-- The zero subspace has integral lattice of covolume `1` in its `0`-dimensional real span. -/
@[simp]
theorem covolume_integerLattice_bot :
    ZLattice.covolume (⊥ : Submodule K (ι → K)).integerLattice = 1 := by
  simp [covolume_integerLattice]

open scoped Classical in
/-- The whole space `ι → K` has integral lattice covolume equal to the `#ι`-th power of the
ring-of-integers covolume. -/
theorem covolume_integerLattice_top_eq_covolume_pow :
    ZLattice.covolume (⊤ : Submodule K (ι → K)).integerLattice =
      ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  simp [covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
    Module.finrank_fintype_fun_eq_card]

open scoped Classical in
/-- The whole space `ι → K` has integral lattice covolume
`((2⁻¹) ^ nrComplexPlaces K * √|discr K|) ^ #ι`. -/
@[simp]
theorem covolume_integerLattice_top :
    ZLattice.covolume (⊤ : Submodule K (ι → K)).integerLattice =
      ((2⁻¹ : ℝ) ^ nrComplexPlaces K * √|discr K|) ^ Fintype.card ι := by
  rw [covolume_integerLattice_top_eq_covolume_pow, mixedEmbedding.covolume_integerLattice]

end MainTheorems

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

/-! ### Worked sanity checks -/

section Examples

open Module NumberField NumberField.mixedEmbedding Set Submodule TauCeti

/-! Over `ℚ`, the line `W = ℚ ∙ ![1, 2]` has absolute height and integral-lattice covolume `√5`,
whereas the index-`2` sublattice `(2 : ℝ) • W.integerLattice` generated by `2 • (1, 2)` has
covolume `2 * √5`. -/

open scoped Classical Pointwise in
example :
    (ℚ ∙ ![(1 : ℚ), 2]).subspaceHeight = √5 ∧
      ZLattice.covolume (ℚ ∙ ![(1 : ℚ), 2]).integerLattice = √5 ∧
      ZLattice.covolume ((2 : ℝ) • (ℚ ∙ ![(1 : ℚ), 2]).integerLattice) = 2 * √5 := by
  set W : Submodule ℚ (Fin 2 → ℚ) := ℚ ∙ ![(1 : ℚ), 2]
  have hv : ![(1 : ℚ), 2] ≠ 0 := by simp
  have hcast : ![(1 : ℚ), 2] = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
    ext i
    fin_cases i <;> simp
  have hH : W.subspaceHeight = √5 := by
    rw [subspaceHeight_span_singleton hv, hcast,
      TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  have hr₂ : nrComplexPlaces ℚ = 0 := by
    have hcard := card_add_two_mul_card_eq_rank ℚ
    rw [finrank_self] at hcard
    omega
  have hcov : ZLattice.covolume W.integerLattice = √5 := by
    rw [W.covolume_integerLattice, hr₂, discr_rat, finrank_self, hH]
    norm_num
  have hdim : finrank ℝ W.euclideanSpan = 1 := by
    rw [W.finrank_euclideanSpan, finrank_self, one_mul, finrank_span_singleton hv]
  refine ⟨hH, hcov, ?_⟩
  rw [ZLattice.covolume_smul W.integerLattice (by norm_num : (2 : ℝ) ≠ 0) volume, hdim, pow_one,
    hcov]
  norm_num

/-! Over `K = ℚ(i)` (with `minpoly ℤ θ = X² + 1`), the line `W = K ∙ ![1, θ]` has absolute height
`√2`, relative Arakelov height `2`, and integral-lattice covolume `2`: both the complex-place factor
`2⁻¹ ^ r₂ = 1 / 2` (cancelling `√|discr K| = √4 = 2`) and the degree exponent `[K : ℚ] = 2` on
`subspaceHeight` are necessary. -/

open scoped Classical in
example (K : Type*) [Field K] [NumberField K] {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = Polynomial.X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (K ∙ ![(1 : K), (θ : K)]).subspaceHeight = √2 ∧
      (K ∙ ![(1 : K), (θ : K)]).relativeSubspaceArakelovHeight = 2 ∧
      ZLattice.covolume (K ∙ ![(1 : K), (θ : K)]).integerLattice = 2 := by
  set W : Submodule K (Fin 2 → K) := K ∙ ![(1 : K), (θ : K)]
  let y : Fin 2 → 𝓞 K := ![1, θ]
  have hy0 : y ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hv0 : ![(1 : K), (θ : K)] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hy_cast : (fun i ↦ (y i : K)) = ![(1 : K), (θ : K)] := by
    ext i
    fin_cases i <;> simp [y]
  have hspan_top : Ideal.span (range y) = ⊤ :=
    top_unique fun x _ ↦ by
      simpa [y] using Ideal.mul_mem_left _ x (Ideal.subset_span (s := range y) ⟨0, rfl⟩)
  have hr₁ : nrRealPlaces K = 0 := GaussianRationals.nrRealPlaces_eq_zero hmin
  have hr₂ : nrComplexPlaces K = 1 := GaussianRationals.nrComplexPlaces_eq_one hmin hgen
  have hdeg : finrank ℚ K = 2 := GaussianRationals.finrank_eq_two hmin hgen
  have hdiscr : discr K = -4 := GaussianRationals.discr_eq_neg_four hmin hgen
  have hθ_sq : (θ : K) ^ 2 = -1 := by
    have h0 := GaussianRationals.sq_eq_neg_one hmin
    exact_mod_cast h0
  -- Every infinite place `w` of `ℚ(i)` is complex and unique, with `‖w θ‖² = 1`.
  have hw_complex (w : InfinitePlace K) : w.IsComplex := by
    rcases w.isReal_or_isComplex with h | h
    · exfalso
      have hpos : 0 < Fintype.card {v : InfinitePlace K // v.IsReal} :=
        Fintype.card_pos_iff.mpr ⟨⟨w, h⟩⟩
      have hreal : Fintype.card {v : InfinitePlace K // v.IsReal} = nrRealPlaces K := rfl
      omega
    · exact h
  have hcard_inf : Fintype.card (InfinitePlace K) = 1 := by
    have := Fintype.card_subtype_compl (IsReal (K := K))
    have hcomp :
        Fintype.card {w : InfinitePlace K // ¬w.IsReal} = nrComplexPlaces K :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex)
    have hreal : Fintype.card {w : InfinitePlace K // w.IsReal} = nrRealPlaces K := rfl
    omega
  have hrel : W.relativeSubspaceArakelovHeight = 2 := by
    rw [relativeSubspaceArakelovHeight_span_singleton hv0, ← hy_cast]
    have hprod := arakelovMulHeight_mul_absNorm_span_range hy0
    rw [hspan_top, Ideal.absNorm_top, Nat.cast_one, mul_one] at hprod
    rw [hprod, Subsingleton.elim (Fintype.ofFinite (Fin 2)) inferInstance]
    have hfac (w : InfinitePlace K) :
        (∑ i : Fin 2, ‖w.embedding (y i : K)‖ ^ 2) ^ ((w.mult : ℝ) / 2) = 2 := by
      have hm : w.mult = 2 := (hw_complex w).mult_eq_two
      have hθ_norm : ‖w.embedding (θ : K)‖ ^ 2 = 1 := by
        rw [← norm_pow, ← map_pow, hθ_sq, map_neg, map_one, norm_neg, norm_one]
      rw [Fin.sum_univ_two, hm]
      simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, norm_one, one_pow, hθ_norm]
      norm_num
    simp_rw [hfac]
    rw [Finset.prod_const, Finset.card_univ, hcard_inf, pow_one]
  have habs : W.subspaceHeight = √2 := by
    have hp := W.subspaceHeight_pow_finrank
    rw [hdeg, hrel] at hp
    have hsq : W.subspaceHeight ^ 2 = √2 ^ 2 := by rw [hp, Real.sq_sqrt zero_le_two]
    exact (pow_left_inj₀ (subspaceHeight_pos W).le (Real.sqrt_nonneg _) two_ne_zero).mp hsq
  have hcov : ZLattice.covolume W.integerLattice = 2 := by
    rw [W.covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
      mixedEmbedding.covolume_integerLattice, finrank_span_singleton hv0, pow_one, hr₂, hdiscr,
      hrel]
    have h4 : √(|(-4 : ℤ)| : ℝ) = 2 := by
      have h4' : (|(-4 : ℤ)| : ℝ) = 2 ^ 2 := by norm_num
      rw [h4', Real.sqrt_sq zero_le_two]
    rw [h4]
    norm_num
  exact ⟨habs, hrel, hcov⟩

end Examples

end
