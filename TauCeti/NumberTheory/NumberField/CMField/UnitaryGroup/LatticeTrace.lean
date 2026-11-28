/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.WeilData
import TauCeti.RingTheory.Trace.RingHom

/-!
# Relative trace pairing of a Weil lattice

If the imaginary scalar of the Weil datum generates the inverse different of the base field,
then the product of the Weil lattice with its conjugate is the relative inverse different.
Consequently the relative trace of the Hermitian pairing is integral over the base. This lets
one read the pairings in complex coordinates as base integers, for instance when computing
periods of products of theta functions along a frame.

The integral pairing is the one in `New.Parameters.sum_mul_conj_mem_quadInt` in
`grh/src/New/Derivatives/Vacuum/TightFrames.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open scoped NumberField nonZeroDivisors

namespace TauCeti.WeilData

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [IsCMField E] {Φ : CMType E}

/-- When the imaginary scalar is the image of a generator of the base field's inverse
absolute different, the product of the Weil lattice with its conjugate is the relative inverse
different. -/
theorem toFractionalIdeal_mul_star_eq_dual (W : WeilData Φ) {j : K}
    (hj : algebraMap K E j = W.j)
    (hbase : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ j) :
    (toFractionalIdeal (W.α * star W.α) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.dual (𝓞 K) K 1 := by
  have hmap : (IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 E)) : K →+* E) =
      algebraMap K E := by
    unfold IsFractionRing.map
    exact IsLocalization.map_unique _ _ fun a ↦ by
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K E]
  have h := W.spanSingleton_mul_toFractionalIdeal
  rw [FractionalIdeal.dual_eq_dual_mul_dual ℤ ℚ K (𝓞 K) (𝓞 E) E, hbase,
    FractionalIdeal.extendedHom_spanSingleton, hmap, hj,
    mul_comm (FractionalIdeal.dual (𝓞 K) K _)] at h
  exact mul_left_cancel₀ (by simpa using W.j_ne_zero) h

/-- The relative trace of `x * star y`, for `x` and `y` in the Weil lattice `E ∩ α Ô`,
is a base integer when the imaginary scalar comes from a generator of the inverse different
of the base. -/
theorem isIntegral_trace_mul_star_of_mem_weil_lattice (W : WeilData Φ) {j : K}
    (hj : algebraMap K E j = W.j)
    (hbase : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ j)
    {x y : E} (hx : x ∈ (toFractionalIdeal W.α : FractionalIdeal (𝓞 E)⁰ E))
    (hy : y ∈ (toFractionalIdeal W.α : FractionalIdeal (𝓞 E)⁰ E)) :
    IsIntegral ℤ (Algebra.trace K E (x * star y)) := by
  let : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hy' : star y ∈ (toFractionalIdeal (star W.α) : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← algebraMap_mem_finiteAdelicIdeal_iff, mem_finiteAdelicIdeal_iff _ rfl] at hy ⊢
    rw [← star_mem_integralAdeles_iff] at hy
    simpa only [star_mul, ← algebraMap_star_comm, ← Units.coe_star, star_inv, mul_comm] using hy
  have hxy := FractionalIdeal.mul_mem_mul hx hy'
  rw [← Units.val_mul, ← map_mul, W.toFractionalIdeal_mul_star_eq_dual hj hbase] at hxy
  have ht := (FractionalIdeal.mem_dual one_ne_zero).1 hxy 1 (FractionalIdeal.one_mem_one _)
  simp only [Algebra.traceForm_apply, mul_one] at ht
  obtain ⟨a, ha⟩ := ht
  exact ha ▸ a.isIntegral_coe

/-- For a CM type consisting of the extensions of a fixed embedding of the base field, the
complex Hermitian pairing in the CM coordinates of the Weil lattice is the image of an
integer of the base field. -/
theorem exists_integer_eq_sum_embedding_mul_conj (W : WeilData Φ) {j : K}
    (hj : algebraMap K E j = W.j)
    (hbase : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ j)
    (ι : K →+* ℂ) (hΦ : (Φ : Set (E →+* ℂ)) = {φ | φ.comp (algebraMap K E) = ι})
    {x y : E} (hx : x ∈ (toFractionalIdeal W.α : FractionalIdeal (𝓞 E)⁰ E))
    (hy : y ∈ (toFractionalIdeal W.α : FractionalIdeal (𝓞 E)⁰ E)) :
    ∃ a : 𝓞 K, ι (a : K) = ∑ᶠ φ ∈ (Φ : Set (E →+* ℂ)), φ x * star (φ y) := by
  let : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hint := W.isIntegral_trace_mul_star_of_mem_weil_lattice hj hbase hx hy
  refine ⟨⟨Algebra.trace K E (x * star y), hint⟩, ?_⟩
  rw [hΦ]
  calc
    ι (↑(⟨Algebra.trace K E (x * star y), hint⟩ : 𝓞 K)) =
        ι (Algebra.trace K E (x * star y)) := congrArg ι (RingOfIntegers.coe_mk hint)
    _ = _ := by
      simpa only [map_mul, star_eq_complexConj, complexEmbedding_complexConj, Complex.star_def]
        using ι.apply_trace_eq_finsum (x * star y)

end TauCeti.WeilData
