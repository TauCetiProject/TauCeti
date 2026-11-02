/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Mult
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Euclidean heights in extensions of number fields

The Euclidean height `TauCeti.height2` of a tuple is independent of the number field in
which it is computed. Its relative version `TauCeti.arakelovMulHeight` instead raises to
the extension degree. These comparisons allow Euclidean heights of coefficient and Plücker
vectors to be computed in a common number field.

The statements include zero and empty tuples: their Euclidean height is zero and their
relative projective height is one. Ring isomorphisms preserve both heights. Appending a
coordinate one gives the corresponding extension and isomorphism laws for affine heights.

The argument follows the integral-tuple reduction of `NumberField.mulHeight_algebraMap`:
the finite-place product is the inverse norm of the coordinate ideal, and the archimedean
Euclidean factors group by restriction of infinite places, retaining complex multiplicity.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1 and §6.3.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
-/

public noncomputable section

open Function Ideal Module NumberField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {ι : Type*} [Finite ι]

private theorem arakelovMulHeight_algebraMap_coe (y : ι → 𝓞 K) :
    arakelovMulHeight (fun i ↦ algebraMap K L (y i)) =
      arakelovMulHeight (fun i ↦ (y i : K)) ^ finrank K L := by
  classical
  let _ := Fintype.ofFinite ι
  rcases eq_or_ne y 0 with rfl | hy
  · simp [← Pi.zero_def]
  let z : ι → 𝓞 L := fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)
  have hz : z ≠ 0 := by
    contrapose hy
    funext i
    exact (map_eq_zero_iff _ (RingOfIntegers.algebraMap.injective K L)).mp (congrFun hy i)
  have hrange : Set.range z = algebraMap (𝓞 K) (𝓞 L) '' Set.range y := Set.range_comp ..
  have hN : (span (Set.range z)).absNorm = (span (Set.range y)).absNorm ^ finrank K L := by
    rw [hrange, ← Ideal.map_span, Ideal.absNorm_algebraMap,
      ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  have hN₀ : ((span (Set.range z)).absNorm : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, absNorm_eq_zero_iff, span_eq_bot]
    simpa [funext_iff] using hz
  have hyz (i : ι) : (z i : L) = algebraMap K L (y i) := by
    simp [z, ← IsScalarTower.algebraMap_apply]
  refine mul_right_cancel₀ hN₀ ?_
  rw [← funext hyz, arakelovMulHeight_mul_absNorm_span_range hz, hN, Nat.cast_pow,
    ← mul_pow, arakelovMulHeight_mul_absNorm_span_range hy]
  simp_rw [hyz, InfinitePlace.norm_embedding_eq, ← InfinitePlace.comap_apply,
    Real.rpow_div_two_eq_sqrt _ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Real.rpow_natCast,
    InfinitePlace.prod_comap_pow_mult (fun v : InfinitePlace K ↦ √(∑ i, v (y i) ^ 2)),
    pow_mul, Finset.prod_pow]

/-- Relative Euclidean projective height raises to the extension degree under an extension
of number fields, including at the zero tuple. -/
@[simp]
theorem arakelovMulHeight_algebraMap (x : ι → K) :
    arakelovMulHeight (algebraMap K L ∘ x) = arakelovMulHeight x ^ finrank K L := by
  obtain ⟨⟨b, hb⟩, hbx⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose y hy using hbx
  have hb₀ : (b : K) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have hxy : (b : K) • x = fun i ↦ (y i : K) := by
    ext i
    simpa [Algebra.smul_def] using (hy i).symm
  rw [← arakelovMulHeight_smul x hb₀, ← arakelovMulHeight_smul _
    ((map_ne_zero (algebraMap K L)).mpr hb₀), hxy, ← arakelovMulHeight_algebraMap_coe]
  congr 1
  ext i
  simp [← congrFun hxy i]

/-- Relative logarithmic Euclidean height multiplies by the extension degree. -/
@[simp]
theorem arakelovLogHeight_algebraMap (x : ι → K) :
    arakelovLogHeight (algebraMap K L ∘ x) = finrank K L * arakelovLogHeight x := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_algebraMap,
    Real.log_pow, arakelovLogHeight_eq_log_arakelovMulHeight]

/-- The degree-normalized Euclidean height is unchanged by an extension of number fields,
including at zero. -/
@[simp]
theorem height2_algebraMap (x : ι → K) : height2 (algebraMap K L ∘ x) = height2 x := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : algebraMap K L ∘ x ≠ 0 := by
    intro h
    apply hx
    ext i
    exact (map_eq_zero_iff _ (algebraMap K L).injective).mp (congrFun h i)
  apply (pow_left_inj₀ (height2_nonneg _) (height2_nonneg _) (finrank_pos.ne' :
    finrank ℚ L ≠ 0)).mp
  rw [← arakelovMulHeight_of_ne_zero hx', arakelovMulHeight_algebraMap,
    arakelovMulHeight_of_ne_zero hx, ← pow_mul, finrank_mul_finrank ℚ K L]

/-- Relative affine Euclidean height raises to the extension degree. -/
@[simp]
theorem arakelovMulHeightAff_algebraMap (x : ι → K) :
    arakelovMulHeightAff (algebraMap K L ∘ x) =
      arakelovMulHeightAff x ^ finrank K L := by
  simp only [arakelovMulHeightAff_def]
  rw [← arakelovMulHeight_algebraMap]
  congr 1
  ext i
  cases i <;> simp

/-- Relative logarithmic affine Euclidean height multiplies by the extension degree. -/
@[simp]
theorem arakelovLogHeightAff_algebraMap (x : ι → K) :
    arakelovLogHeightAff (algebraMap K L ∘ x) = finrank K L * arakelovLogHeightAff x := by
  rw [arakelovLogHeightAff_eq_log_arakelovMulHeightAff, arakelovMulHeightAff_algebraMap,
    Real.log_pow, arakelovLogHeightAff_eq_log_arakelovMulHeightAff]

end TauCeti

namespace RingEquiv

open TauCeti

variable {K K' ι : Type*} [Field K] [Field K'] [NumberField K] [NumberField K'] [Finite ι]

/-- A ring isomorphism of number fields preserves relative Euclidean projective height. -/
@[simp]
theorem arakelovMulHeight_comp (e : K ≃+* K') (x : ι → K) :
    arakelovMulHeight (e ∘ x) = arakelovMulHeight x := by
  let _ : Algebra K K' := e.toRingHom.toAlgebra
  have h := arakelovMulHeight_algebraMap (L := K') x
  -- Transport the algebra structure along `e`; the extension has degree one.
  rwa [← (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl).toLinearEquiv.finrank_eq,
    finrank_self, pow_one] at h

/-- A ring isomorphism of number fields preserves relative logarithmic Euclidean height. -/
@[simp]
theorem arakelovLogHeight_comp (e : K ≃+* K') (x : ι → K) :
    arakelovLogHeight (e ∘ x) = arakelovLogHeight x := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, e.arakelovMulHeight_comp,
    arakelovLogHeight_eq_log_arakelovMulHeight]

/-- A ring isomorphism of number fields preserves degree-normalized Euclidean height. -/
@[simp]
theorem height2_comp (e : K ≃+* K') (x : ι → K) : height2 (e ∘ x) = height2 x := by
  let _ : Algebra K K' := e.toRingHom.toAlgebra
  simpa only [RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using
    height2_algebraMap (L := K') x

/-- A ring isomorphism of number fields preserves relative affine Euclidean height. -/
@[simp]
theorem arakelovMulHeightAff_comp (e : K ≃+* K') (x : ι → K) :
    arakelovMulHeightAff (e ∘ x) = arakelovMulHeightAff x := by
  simp only [arakelovMulHeightAff_def]
  rw [← e.arakelovMulHeight_comp]
  congr 1
  ext i
  cases i <;> simp

/-- A ring isomorphism of number fields preserves relative logarithmic affine Euclidean height. -/
@[simp]
theorem arakelovLogHeightAff_comp (e : K ≃+* K') (x : ι → K) :
    arakelovLogHeightAff (e ∘ x) = arakelovLogHeightAff x := by
  rw [arakelovLogHeightAff_eq_log_arakelovMulHeightAff, e.arakelovMulHeightAff_comp,
    arakelovLogHeightAff_eq_log_arakelovMulHeightAff]

end RingEquiv
