/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MixedImage
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
import TauCeti.NumberTheory.NumberField.FinitePlace.Ideal
import TauCeti.RingTheory.DedekindDomain.PseudoBasis

/-!
# The covolume of an `𝓞 K`-module, read at the finite places

Let `K` be a number field and `Λ` a finitely generated `𝓞 K`-submodule of `ι → K` spanning it
over `K`, so that its mixed image `Λ.mixedImage` is a full lattice in `ι → mixedSpace K`. For a
finite place `v` let `B v` be the largest value of `v` on the determinants of `card ι` vectors of
`Λ`. Then

```text
covol Λ.mixedImage  =  (∏ᶠ v, B v)⁻¹ · covol (𝓞 K) ^ card ι.
```

The factor `(∏ᶠ v, B v)⁻¹` is the generalized index of `Λ` in `(𝓞 K) ^ ι` (generalized because
`Λ` need not lie in `(𝓞 K) ^ ι`), computed one place at a time: a caller who knows `Λ` only
through local conditions, such as the approximation modules of the geometry of numbers over `K`,
reads off its covolume from the local largest determinants without forming a quotient, a
localization or a basis.

## Main results

* `Submodule.covolume_mixedImage_of_pseudoBasis`: if `Λ = ⊕ i, J i • b i` for a `K`-basis `b` and
  nonzero ideals `J i`, its covolume is `|N (det b)| · ∏ i, N (J i)` times `covol (𝓞 K) ^ card ι`.
* `Submodule.isGreatest_apply_det_of_pseudoBasis`: for `Λ = ⊕ i, J i • b i`, the largest value
  of a finite place `v` on the determinants of `card ι` vectors of `Λ` is
  `v (det b) · ∏ i, N 𝔭 ^ (-mᵢ)`, `mᵢ` the multiplicity of the prime `𝔭` of `v` in `J i`.
* `Submodule.exists_isGreatest_apply_det`: the values of a finite place on the determinants of
  `card ι` vectors of `Λ` have a largest element.
* `Submodule.covolume_mixedImage`: the display above.
* `NumberField.mixedEmbedding.instIsAddHaarMeasureVolumePi`,
  `NumberField.mixedEmbedding.instBorelSpacePi`: the volume of `ι → mixedSpace K` is an additive
  Haar measure for its Borel structure, which instance search does not find on its own.

## Implementation notes

The proof goes through a pseudo-basis `Λ = ⊕ i, J i • b i` (`Submodule.exists_pseudoBasis`), which
appears in the intermediate results but not in the main statement. The coefficient lattices `J i`
have the `ℤ`-bases of Mathlib's `fractionalIdealLatticeBasis`, of covolume `N (J i) · covol (𝓞 K)`,
and the change of variables `z ↦ ∑ i, z i • b i` is `mixedSpace K`-linear, so its real determinant
is one algebra norm, `Algebra.norm ℝ (det b)`, by `LinearMap.det_restrictScalars`; no place is
looked at separately.
At a finite place `v` with prime `𝔭`, the largest value on the determinants is
`v (det b) · ∏ i, N 𝔭 ^ (-mᵢ)`, `mᵢ` the multiplicity of `𝔭` in `J i`: an upper bound by the
ultrametric inequality on the Leibniz expansion, attained by the vectors `aᵢ • b i` with `aᵢ ∈ J i`
of largest value. The product formula and the factorization of `J i` into the primes of the finite
places (`NumberField.FinitePlace.finprod_finitePlace_pow_multiplicity`) then turn the two norms into
`(∏ᶠ v, B v)⁻¹`.

The statements use `open scoped Classical` for the `Fintype` instances of the real and complex
places that the metric and the measure of `mixedSpace K` need, as Mathlib does.

## References

* E. Steinitz, *Rechteckige Systeme und Moduln in algebraischen Zahlkörpern*, Math. Ann. **71**
  (1911), 328–354 (the pseudo-basis).
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Appendix C.2 and Lemma 7.5.7 (the lattice of an `𝓞 K`-module and its covolume).

The shape of the main statement and of its proof follow Ralf Stephan's
`DiophantineApproximation/ModuleCovolume.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

open Module NumberField NumberField.mixedEmbedding MeasureTheory Ideal Matrix
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

namespace NumberField.mixedEmbedding

open scoped Classical in
/-- The volume of `ι → mixedSpace K`, the product of the volumes of the factors, is an additive
Haar measure. Instance search does not find this through `Measure.pi.isAddHaarMeasure`, whose
hypothesis on the factors it fails to resolve for `mixedSpace K`. -/
instance instIsAddHaarMeasureVolumePi : (volume : Measure (ι → mixedSpace K)).IsAddHaarMeasure :=
  @Measure.pi.isAddHaarMeasure ι _ _ _ _ _ _ _ _ fun _ ↦ inferInstance

open scoped Classical in
/-- The Borel structure of `ι → mixedSpace K` for the topology of its sup norm. Instance search
does not identify that topology with the product topology on its own. -/
instance instBorelSpacePi :
    @BorelSpace (ι → mixedSpace K) PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
  @Pi.borelSpace ι _ _ _ _ _ fun _ ↦ inferInstance

end NumberField.mixedEmbedding

namespace Submodule

open scoped Classical in
/-- **The covolume of an `𝓞 K`-module with a given pseudo-basis.** If `Λ = ⊕ i, J i • b i`, that
is, `x ∈ Λ` exactly when the `i`-th coordinate of `x` in the `K`-basis `b` lies in the nonzero
ideal `J i` for every `i`, then the covolume of `Λ.mixedImage` is
`|N (det b)| · ∏ i, N (J i)` times the covolume of `(𝓞 K) ^ ι`. -/
theorem covolume_mixedImage_of_pseudoBasis [DecidableEq ι] {Λ : Submodule (𝓞 K) (ι → K)}
    (b : Basis ι K (ι → K)) {J : ι → Ideal (𝓞 K)} (hJ : ∀ i, J i ≠ ⊥)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i)) :
    ZLattice.covolume Λ.mixedImage =
      |(Algebra.norm ℚ (Matrix.of ⇑b).det : ℝ)| * (∏ i, (absNorm (J i) : ℝ)) *
        ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  -- The coefficient ideals as invertible fractional ideals, with their lattice bases.
  let U (i : ι) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (J i : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr (hJ i))
  let P := Pi.basis fun i ↦ fractionalIdealLatticeBasis K (U i)
  -- The change of variables `z ↦ ∑ i, z i • b i`, linear over `mixedSpace K`.
  let A : Matrix ι ι (mixedSpace K) := Matrix.of fun j i ↦ mixedEmbedding K (b i j)
  let φ : (ι → mixedSpace K) →ₗ[ℝ] ι → mixedSpace K := (Matrix.toLin' A).restrictScalars ℝ
  have hdetb : (Matrix.of ⇑b).det ≠ 0 := by
    rw [← Pi.basisFun_det_apply]
    exact ((Pi.basisFun K ι).isUnit_det b).ne_zero
  have hdet : |LinearMap.det φ| = |(Algebra.norm ℚ (Matrix.of ⇑b).det : ℝ)| :=
    mixedEmbedding.abs_det_changeOfVariables b
  have hdet0 : IsUnit (LinearMap.det φ) := by
    rw [isUnit_iff_ne_zero, ← abs_ne_zero, hdet, abs_ne_zero, Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hdetb
  have he : ⇑(LinearMap.equivOfIsUnitDet hdet0) = φ := funext (φ.equivOfIsUnitDet_apply hdet0)
  have hφ (c : ι → K) :
      φ (fun i ↦ mixedEmbedding K (c i)) = fun j ↦ mixedEmbedding K (b.equivFun.symm c j) := by
    ext1 j
    simp [φ, A, Matrix.mulVec, dotProduct, b.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  -- The `ℤ`-span of the product basis is the product of the coefficient lattices.
  have hP (z : ι → mixedSpace K) : z ∈ span ℤ (Set.range P) ↔
      ∃ c : ι → K, (∀ i, c i ∈ IsLocalization.coeSubmodule K (J i)) ∧
        (fun i ↦ mixedEmbedding K (c i)) = z :=
    mem_span_pi_fractionalIdealLatticeBasis (J := U) z
  -- The mixed image is the image of that product under the change of variables.
  have hL : Λ.mixedImage = span ℤ (Set.range (P.map (LinearMap.equivOfIsUnitDet hdet0))) := by
    have hrange : Set.range (P.map (LinearMap.equivOfIsUnitDet hdet0)) =
        φ.restrictScalars ℤ '' Set.range P := by
      rw [← Set.range_comp, Basis.coe_map, he, LinearMap.coe_restrictScalars ℤ φ]
    rw [hrange, ← Submodule.map_span]
    ext y
    simp only [mem_mixedImage, mem_map, hP, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨_, ⟨b.repr x, (hΛ x).1 hx, rfl⟩, ?_⟩
      rw [hφ, ← b.equivFun_apply, LinearEquiv.symm_apply_apply]
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨b.equivFun.symm c, (hΛ _).2 fun i ↦ ?_, (hφ c).symm⟩
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      exact hc i
  rw [hL, ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain _ volume), measureReal_def, ← ZSpan.map_fundamentalDomain,
    he, Measure.addHaar_image_linearMap, ZSpan.fundamentalDomain_pi_basis,
    volume_pi_pi]
  -- The fundamental domain of `(𝓞 K) ^ ι` has volume the covolume of `𝓞 K`.
  have hO : volume (ZSpan.fundamentalDomain (latticeBasis K)) =
      ENNReal.ofReal (ZLattice.covolume (mixedEmbedding.integerLattice K)) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (fundamentalDomain_integerLattice K), measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
  simp_rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, hO]
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal (abs_nonneg _), hdet]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ZLattice.covolume_pos _ volume).le]
  simp [U, FractionalIdeal.coeIdeal_absNorm, Finset.prod_mul_distrib, mul_assoc]

/-- **The largest local determinant of a pseudo-basis module.** At a finite place `v` with prime
`𝔭`, the values of `v` on the determinants of `card ι` vectors of `Λ = ⊕ i, J i • b i` have the
largest element `v (det b) · ∏ i, N 𝔭 ^ (-mᵢ)`, where `mᵢ` is the multiplicity of `𝔭` in
`J i`. -/
theorem isGreatest_apply_det_of_pseudoBasis [DecidableEq ι]
    {Λ : Submodule (𝓞 K) (ι → K)} (b : Basis ι K (ι → K)) {J : ι → Ideal (𝓞 K)}
    (hJ : ∀ i, J i ≠ ⊥)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, b.repr x i ∈ IsLocalization.coeSubmodule K (J i))
    (v : FinitePlace K) :
    IsGreatest
      ((fun x : ι → ι → K ↦ v (Matrix.of x).det) '' Set.univ.pi fun _ ↦ (Λ : Set (ι → K)))
      (v (Matrix.of ⇑b).det * ∏ i,
        ((v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i))⁻¹) := by
  have hN (i : ι) :
      0 < (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i) :=
    pow_pos (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _
  refine ⟨?_, ?_⟩
  · -- The bound is attained by the vectors `aᵢ • b i`, with `aᵢ ∈ J i` of largest value.
    choose a ha hav using fun i ↦ v.exists_mem_apply_mul_absNorm_pow_eq_one (hJ i)
    refine ⟨fun k ↦ (a k : K) • b k, fun k _ ↦ (hΛ _).2 fun i ↦ ?_, ?_⟩
    · rw [map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with h
      · exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨a k, h ▸ ha k, rfl⟩
      · exact zero_mem _
    · have hmat :
          Matrix.of (fun k ↦ (a k : K) • b k) = Matrix.of fun k j ↦ (a k : K) * b k j := by
        ext
        simp [Algebra.smul_def]
      dsimp only
      have hcol := Matrix.det_mul_column (fun k ↦ (a k : K)) (Matrix.of ⇑b)
      simp only [Matrix.of_apply] at hcol
      rw [hmat, hcol, map_mul, map_prod, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ eq_inv_of_mul_eq_one_left (hav i)
  · -- The upper bound: the coordinate matrix has its `i`-th column in `J i`.
    rintro _ ⟨x, hx, rfl⟩
    have hle (i : ι) {c : K} (hc : c ∈ IsLocalization.coeSubmodule K (J i)) :
        v c ≤
          ((v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i))⁻¹ := by
      obtain ⟨c, hcJ, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hc
      rw [← one_div, le_div_iff₀ (hN i)]
      exact v.apply_mul_absNorm_pow_le_one hcJ
    have hmat : Matrix.of x = Matrix.of (fun k i ↦ b.repr (x k) i) * Matrix.of ⇑b := by
      ext k j
      conv_lhs => rw [Matrix.of_apply, ← b.sum_repr (x k)]
      simp [Matrix.mul_apply, Finset.sum_apply]
    dsimp only
    rw [hmat, Matrix.det_mul, map_mul, mul_comm]
    gcongr
    exact Matrix.abv_det_le_prod_of_le' _ v.add_le fun k i ↦
      hle i ((hΛ _).1 (hx k (Set.mem_univ _)) i)

/-- **The largest local determinant of an `𝓞 K`-module.** For a finitely generated `𝓞 K`-module
`Λ` and a finite place `v`, the values of `v` on the determinants of `card ι` vectors of `Λ` have a
largest element. If `Λ` does not span `ι → K`, all these determinants vanish. -/
theorem exists_isGreatest_apply_det [DecidableEq ι] {Λ : Submodule (𝓞 K) (ι → K)} (hΛ : Λ.FG)
    (v : FinitePlace K) :
    ∃ B, IsGreatest
      ((fun x : ι → ι → K ↦ v (Matrix.of x).det) '' Set.univ.pi fun _ ↦ (Λ : Set (ι → K))) B := by
  by_cases hspan : span K (Λ : Set (ι → K)) = ⊤
  · obtain ⟨b, J, hJ, hmem⟩ := exists_pseudoBasis (K := K) (ι := ι) Λ hΛ hspan (by simp)
    exact ⟨_, isGreatest_apply_det_of_pseudoBasis b hJ hmem v⟩
  · have : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hspan (Subsingleton.elim _ _)
    refine ⟨0, ⟨0, fun _ _ ↦ Λ.zero_mem, by simp⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hdet : (Matrix.of x).det = 0 := by
      by_contra hne
      refine hspan (eq_top_iff.2 ?_)
      have hli := (Matrix.linearIndependent_row_iff_isUnit (A := Matrix.of x)).2
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
      rw [← hli.span_eq_top_of_card_eq_finrank' (by simp)]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hx i (Set.mem_univ _))
    simp [hdet]

open scoped Classical in
/-- **The covolume of an `𝓞 K`-module, read at the finite places.** Let `Λ` be a finitely
generated `𝓞 K`-module spanning `ι → K`, and let `B v` be the largest value of the finite place `v`
on the determinants of `card ι` vectors of `Λ` (it exists by
`Submodule.exists_isGreatest_apply_det`). Then the covolume of the mixed image of `Λ` is
`(∏ᶠ v, B v)⁻¹` times the covolume of `(𝓞 K) ^ ι`. -/
theorem covolume_mixedImage [DecidableEq ι] {Λ : Submodule (𝓞 K) (ι → K)} (hΛ : Λ.FG)
    (hspan : span K (Λ : Set (ι → K)) = ⊤) {B : FinitePlace K → ℝ}
    (hB : ∀ v, IsGreatest
      ((fun x : ι → ι → K ↦ v (Matrix.of x).det) '' Set.univ.pi fun _ ↦ (Λ : Set (ι → K))) (B v)) :
    ZLattice.covolume Λ.mixedImage =
      (∏ᶠ v, B v)⁻¹ * ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  obtain ⟨b, J, hJ, hmem⟩ := exists_pseudoBasis (K := K) (ι := ι) Λ hΛ hspan (by simp)
  have hdetb : (Matrix.of ⇑b).det ≠ 0 := by
    rw [← Pi.basisFun_det_apply]
    exact ((Pi.basisFun K ι).isUnit_det b).ne_zero
  have hBv (v : FinitePlace K) := (hB v).unique (isGreatest_apply_det_of_pseudoBasis b hJ hmem v)
  -- The local factors of the norms of the coefficient ideals.
  have hsupp (i : ι) : Function.HasFiniteMulSupport fun v : FinitePlace K ↦
      (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i) :=
    FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity (hJ i) fun I ↦ (absNorm I : ℝ)
  have hsupp' (i : ι) : Function.HasFiniteMulSupport fun v : FinitePlace K ↦
      ((v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i))⁻¹ :=
    (hsupp i).inv
  have hnorm (i : ι) : ∏ᶠ v : FinitePlace K,
      (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ multiplicity v.maximalIdeal.asIdeal (J i) =
        absNorm (J i) := by
    conv_rhs => rw [← FinitePlace.finprod_finitePlace_pow_multiplicity (hJ i)]
    rw [map_finprod _ (FinitePlace.hasFiniteMulSupport_fun_pow_multiplicity (hJ i) (·)),
      Nat.cast_finprod']
    simp
  rw [covolume_mixedImage_of_pseudoBasis b hJ hmem, finprod_congr hBv,
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hdetb)
      (Function.HasFiniteMulSupport.prod hsupp' _),
    FinitePlace.prod_eq_inv_abs_norm hdetb, finprod_prod_comm _ _ fun i _ ↦ hsupp' i]
  simp_rw [finprod_inv_distrib, hnorm]
  push_cast
  rw [Finset.prod_inv_distrib, ← mul_inv, inv_inv]

end Submodule
