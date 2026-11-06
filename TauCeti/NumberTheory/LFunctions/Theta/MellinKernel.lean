/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Theta.Inversion
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Invariance
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.TraceDual

/-!
# The Mellin kernel of a lattice of the mixed space

Hecke's proof of the functional equation of a partial zeta function (Neukirch VII (5.5)) takes the
Mellin transform of the theta series of a lattice `L` of the mixed space, averaged over a
fundamental domain `D` for the unit action on the norm-one hypersurface `S`. In the normalization
of `archHaar` and `surfaceHaar` this average is

`f_D(L, u) = (2^r₂ / w) ∫_D θ_L(x (u / V_L²)^(1/n)) d*x`,

where `V_L` is the covolume of `L`, `n = [K : ℚ]`, `w` is the number of roots of unity and `r₂` is
the number of complex places (`mellinKernel`). The factor `2^r₂` compensates the product-over-places
normalization of `d*x`, and `1/w` counts the torsion, which acts trivially on the parameters.

This file proves the analytic properties of the kernel that do not depend on the volume of `D`
(Neukirch VII (5.8)):

* `continuousOn_mellinKernel`: for a bounded `D` and a full lattice `L`, the kernel is continuous
  on `(0, ∞)`. On a bounded subset of `S` the parameters are bounded below, so the theta series is
  dominated by the theta series at a constant parameter.
* `mellinKernel_inv`: the transformation law `f_D(L, 1/u) = √u f_{D⁻¹}(L^∨, u)` against the
  Euclidean dual `L^∨ = mixedDual K L`. It is `latticeTheta_inv` integrated over `D`, followed by
  the substitution `x ↦ x⁻¹` of `S`, which preserves `d*x` (`measurePreserving_surfaceInv`); the
  covolumes `V_L V_{L^∨} = 1` make the two rescalings `u / V²` match.
* `mellinKernel_mixedDual_idealLattice`: for the lattice `σ(I)` of a fractional ideal, the dual
  side is again the kernel of an ideal lattice, that of the trace dual `J = I^∨`, over the
  translate of `D` by the point `traceShift K` of `S`. The Euclidean dual of `σ(I)` is
  `traceToEuclidean K` applied to `σ(J)` (`mixedDual_idealLattice`); this map multiplies the
  absolute value at `w` by `mult w`, which on the Gaussian multiplies the parameter by `mult w ^ 2`,
  and the radial part `16 ^ r₂` of that multiplication is absorbed by the covolumes
  `V_J = 4^(-r₂) V_I⁻¹` (`covolume_idealLattice_dual`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5) and (5.8).
-/

public section

noncomputable section

open Bornology Filter MeasureTheory Set NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units TauCeti.NumberField.mixedEmbedding
open scoped Topology nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Neukirch VII (5.5), the Mellin kernel** of a lattice `L` of the mixed space over a set `D` of
parameters: `f_D(L, u) = (2^r₂ / w) ∫_D θ_L(x (u / V_L²)^(1/n)) d*x`, the theta series averaged
over the points of `D` on the norm-one hypersurface, at norm `u / V_L²`, with `V_L` the covolume of
`L`. The kernel is meant for a unit fundamental domain `D` (`IsUnitFundamentalDomain`): then `1/w`
counts the torsion, which fixes the parameters, and `2^r₂` compensates the product-over-places
normalization of `surfaceHaar`. -/
def mellinKernel (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K)) (u : ℝ) : ℂ :=
  ((2 : ℂ) ^ nrComplexPlaces K / torsionOrder K) *
    ∫ x in (Subtype.val ⁻¹' D : Set (normOneSurface K)),
      latticeTheta L (surfaceScale (x : realSpace K) (u / ZLattice.covolume L ^ 2))
        ∂surfaceHaar K

open scoped Classical in
theorem mellinKernel_def (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K)) (u : ℝ) :
    mellinKernel D L u = ((2 : ℂ) ^ nrComplexPlaces K / torsionOrder K) *
      ∫ x in (Subtype.val ⁻¹' D : Set (normOneSurface K)),
        latticeTheta L (surfaceScale (x : realSpace K) (u / ZLattice.covolume L ^ 2))
          ∂surfaceHaar K := (rfl)

/-! ### Continuity -/

open scoped Classical in
/-- **The kernel is continuous on `(0, ∞)`**, Neukirch's continuity hypothesis in (1.4). For `u`
near `u₀ > 0` and `x` in a bounded subset of `S`, the parameters `x (u / V_L²)^(1/n)` are bounded
below by a positive constant, at which the theta series dominates the integrand. -/
theorem continuousOn_mellinKernel {D : Set (realSpace K)} (hD : IsBounded D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ContinuousOn (mellinKernel D L) (Ioi 0) := by
  intro u₀ hu₀
  have hu₀ : 0 < u₀ := hu₀
  set V := ZLattice.covolume L
  have hV : 0 < V := ZLattice.covolume_pos L volume
  set n := (Module.finrank ℚ K : ℝ)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hD
  -- The points of `S` of norm at most `C`: a measurable set containing `D`.
  set T : Set (normOneSurface K) := {x | ‖(x : realSpace K)‖ ≤ C}
  have hT : MeasurableSet T :=
    measurableSet_le (measurable_norm.comp measurable_subtype_coe) measurable_const
  have hDT : Subtype.val ⁻¹' D ⊆ T := fun x hx ↦ hC _ hx
  have hfin : surfaceHaar K (Subtype.val ⁻¹' D) ≠ ⊤ :=
    (surfaceHaar_lt_top_of_isBounded (hD.subset (image_preimage_subset _ _))).ne
  -- A positive lower bound for the parameters, uniform for `x ∈ T` and `u ≥ u₀ / 2`.
  set z : realSpace K := fun _ ↦
    (max C 1 ^ Module.finrank ℚ K)⁻¹ * (u₀ / 2 / V ^ 2) ^ (1 / n)
  have hz (w : InfinitePlace K) : 0 < z w := by positivity
  have hlow : ∀ x ∈ T, ∀ u, u₀ / 2 ≤ u → ∀ w,
      z w ≤ surfaceScale (x : realSpace K) (u / V ^ 2) w := by
    intro x hx u hu w
    rw [surfaceScale_apply]
    exact mul_le_mul (mem_Icc_of_mem_normOneSurface_of_norm_le x.2 hx w).1
      (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hu (sq_nonneg V))
        (by positivity)) (by positivity) ((mem_normOneSurface.mp x.2).1 w).le
  -- For fixed `u > 0` the integrand is continuous on `S`; for fixed `x` it is continuous in `u`.
  have hcontx {u : ℝ} (hu : 0 < u) :
      Continuous fun x : normOneSurface K ↦
        latticeTheta L (surfaceScale (x : realSpace K) (u / V ^ 2)) :=
    (continuousOn_latticeTheta L).comp_continuous
      (continuous_surfaceScale.comp (continuous_subtype_val.prodMk continuous_const))
      fun x ↦ surfaceScale_pos (mem_normOneSurface.mp x.2).1 (by positivity)
  have hcontu (x : normOneSurface K) :
      ContinuousAt (fun u ↦ latticeTheta L (surfaceScale (x : realSpace K) (u / V ^ 2))) u₀ :=
    ContinuousAt.comp (g := latticeTheta L)
      (f := fun u ↦ surfaceScale (x : realSpace K) (u / V ^ 2))
      ((continuousOn_latticeTheta L).continuousAt ((isOpen_setOf_forall_lt 0).mem_nhds
        (surfaceScale_pos (mem_normOneSurface.mp x.2).1 (by positivity))))
      (continuous_surfaceScale.comp
        (continuous_const.prodMk (continuous_id.div_const _))).continuousAt
  have hnhds : ∀ᶠ u in 𝓝 u₀, u₀ / 2 < u := Ioi_mem_nhds (half_lt_self hu₀)
  have : IsFiniteMeasure ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) :=
    isFiniteMeasure_restrict.mpr hfin
  have hint : ContinuousAt (fun u ↦ ∫ x in (Subtype.val ⁻¹' D : Set (normOneSurface K)),
      latticeTheta L (surfaceScale (x : realSpace K) (u / V ^ 2)) ∂surfaceHaar K) u₀ := by
    refine continuousAt_of_dominated (bound := fun _ ↦ ∑' ξ : L, ‖archGaussian z ξ‖) ?_ ?_
      (integrable_const _) (Eventually.of_forall hcontu)
    · filter_upwards [hnhds] with u hu
      exact (hcontx ((half_pos hu₀).trans hu)).aestronglyMeasurable
    · filter_upwards [hnhds] with u hu
      refine ae_restrict_of_ae_restrict_of_subset hDT ((ae_restrict_iff' hT).mpr ?_)
      exact Eventually.of_forall fun x hx ↦ norm_latticeTheta_le L hz (hlow x hx u hu.le)
  exact (continuousAt_const.mul hint).continuousWithinAt

/-! ### The transformation law -/

open scoped Classical in
/-- **Neukirch VII (5.8), the transformation law of the kernel**:
`f_D(L, 1/u) = √u f_{D⁻¹}(L^∨, u)` for every full lattice `L` and its Euclidean dual
`L^∨ = mixedDual K L`. It is `latticeTheta_inv` at the parameters over `D`, followed by the
substitution `x ↦ x⁻¹` of the norm-one hypersurface, which preserves `d*x`. The covolumes
`V_L V_{L^∨} = 1` make the two rescalings `u / V²` agree. -/
theorem mellinKernel_inv (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L] {u : ℝ} (hu : 0 < u) :
    mellinKernel D L u⁻¹ = (√u : ℂ) * mellinKernel D⁻¹ (mixedDual K L) u := by
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hpt (x : normOneSurface K) :
      latticeTheta L (surfaceScale (x : realSpace K) (u⁻¹ / ZLattice.covolume L ^ 2)) =
        (√u : ℂ) * latticeTheta (mixedDual K L) (surfaceScale (surfaceInv K x : realSpace K)
          (u / ZLattice.covolume (mixedDual K L) ^ 2)) := by
    have ht : 0 < u⁻¹ / ZLattice.covolume L ^ 2 := by positivity
    have hsqrt : (ZLattice.covolume L : ℂ)⁻¹ *
        (((√(u⁻¹ / ZLattice.covolume L ^ 2))⁻¹ : ℝ) : ℂ) = (√u : ℂ) := by
      rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hV.le, Real.sqrt_inv, inv_div,
        div_inv_eq_mul]
      have hV' : (ZLattice.covolume L : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
      push_cast
      field_simp
    rw [latticeTheta_inv L _ (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht),
      archNorm_surfaceScale_of_mem_normOneSurface x.2 ht.le, inv_surfaceScale _ ht.le,
      surfaceInv_apply, covolume_mixedDual, hsqrt]
    congr 2
    field_simp
  have hpre : surfaceInv K ⁻¹' (Subtype.val ⁻¹' D⁻¹) = Subtype.val ⁻¹' D := by
    ext x
    simp only [mem_preimage, surfaceInv_apply, Set.mem_inv, inv_inv]
  simp_rw [mellinKernel_def, hpt, integral_const_mul]
  rw [← hpre, measurePreserving_surfaceInv.setIntegral_preimage_emb
    (surfaceInv K).measurableEmbedding fun y : normOneSurface K ↦ latticeTheta (mixedDual K L)
      (surfaceScale (y : realSpace K) (u / ZLattice.covolume (mixedDual K L) volume ^ 2))]
  ring

/-! ### The dual of an ideal lattice -/

variable (K) in
/-- The point of the norm-one hypersurface by which the parameters are translated when the
Euclidean dual of an ideal lattice is read as the lattice of its trace dual: the surface part of
`(mult w ^ 2)_w`, that is `mult w ^ 2 / (16 ^ r₂) ^ (1 / n)`. `traceToEuclidean K` doubles the
complex coordinates, and `|2 z|² = 4 |z|²`. -/
def traceShift : realSpace K :=
  surfacePart fun w ↦ (mult w : ℝ) ^ 2

variable (K) in
theorem traceShift_def : traceShift K = surfacePart fun w ↦ (mult w : ℝ) ^ 2 := (rfl)

theorem traceShift_mem_normOneSurface : traceShift K ∈ normOneSurface K :=
  surfacePart_mem_normOneSurface fun _ ↦ pow_pos (zero_lt_one.trans_le one_le_mult) 2

/-- The norm of `(mult w ^ 2)_w` is `16 ^ r₂`: a complex place contributes `(2 ^ 2) ^ 2`. -/
private theorem archNorm_mult_sq :
    archNorm (fun w : InfinitePlace K ↦ (mult w : ℝ) ^ 2) = 16 ^ nrComplexPlaces K := by
  classical
  rw [archNorm_apply, prod_eq_prod_mul_prod]
  simp only [mult_isReal, mult_isComplex, Nat.cast_one, one_pow, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.card_univ, nrComplexPlaces]
  norm_num

/-- `traceToEuclidean K` on the lattice variable multiplies the parameter of the archimedean
Gaussian by `(mult w ^ 2)_w`. -/
private theorem latticeTheta_map_traceToEuclidean (L : Submodule ℤ (mixedSpace K))
    (y : realSpace K) :
    latticeTheta (L.map ((traceToEuclidean K).toLinearMap.restrictScalars ℤ)) y =
      latticeTheta L ((fun w ↦ (mult w : ℝ) ^ 2) * y) := by
  let e := Submodule.equivMapOfInjective ((traceToEuclidean K).toLinearMap.restrictScalars ℤ)
    (traceToEuclidean K).injective L
  rw [latticeTheta_def, latticeTheta_def, ← e.toEquiv.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  have he : (e x : mixedSpace K) = traceToEuclidean K x :=
    Submodule.coe_equivMapOfInjective_apply _ _ _ x
  rw [LinearEquiv.coe_toEquiv, he]
  simp only [archGaussian_apply, normAtPlace_traceToEuclidean, Pi.mul_apply]
  congr 4 with w
  ring

open scoped Classical in
/-- **The dual side of the transformation law is an ideal kernel.** For the lattice `σ(I)` of a
fractional ideal `I` and its trace dual `J = I^∨`, the kernel of the Euclidean dual of `σ(I)` over
`D` is the kernel of `σ(J)` over the translate of `D` by `traceShift K`. The Euclidean dual is
`traceToEuclidean K` applied to `σ(J)`, which multiplies the parameter by `(mult w ^ 2)_w`; its
surface part is the translation by `traceShift K`, and its norm `16 ^ r₂` is absorbed by the
covolume `V_J = 4^(-r₂) V_I⁻¹`. -/
theorem mellinKernel_mixedDual_idealLattice {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (D : Set (realSpace K)) (u : ℝ) :
    mellinKernel D (mixedDual K (idealLattice K I)) u =
      mellinKernel ((traceShift K * ·) '' D) (idealLattice K J) u := by
  classical
  set c : normOneSurface K := ⟨traceShift K, traceShift_mem_normOneSurface⟩ with hc
  have hV : 0 < ZLattice.covolume (idealLattice K I) := ZLattice.covolume_pos _ volume
  have hm (w : InfinitePlace K) : (0 : ℝ) < (mult w : ℝ) ^ 2 :=
    pow_pos (zero_lt_one.trans_le one_le_mult) 2
  have hN : 0 < archNorm (fun w : InfinitePlace K ↦ (mult w : ℝ) ^ 2) := archNorm_pos hm
  have hpt (x : normOneSurface K) :
      latticeTheta (mixedDual K (idealLattice K I))
          (surfaceScale (x : realSpace K)
            (u / ZLattice.covolume (mixedDual K (idealLattice K I)) ^ 2)) =
        latticeTheta (idealLattice K J) (surfaceScale (surfaceMul c x : realSpace K)
          (u / ZLattice.covolume (idealLattice K J) ^ 2)) := by
    have h16 : (16 : ℝ) ^ nrComplexPlaces K = ((4 : ℝ) ^ nrComplexPlaces K) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hrad : u / (((4 : ℝ) ^ nrComplexPlaces K)⁻¹ *
        (ZLattice.covolume (idealLattice K I))⁻¹) ^ 2 =
        archNorm (fun w : InfinitePlace K ↦ (mult w : ℝ) ^ 2) *
          (u / (ZLattice.covolume (idealLattice K I))⁻¹ ^ 2) := by
      rw [archNorm_mult_sq, h16]
      field_simp
    have hN' : (0 : ℝ) < archNorm (fun w : InfinitePlace K ↦ (mult w : ℝ) ^ 2) ^
        (1 / (Module.finrank ℚ K : ℝ)) := Real.rpow_pos_of_pos hN _
    rw [covolume_mixedDual, covolume_idealLattice_dual hJ, mixedDual_idealLattice hJ,
      latticeTheta_map_traceToEuclidean, surfaceMul_apply, hrad]
    congr 1
    ext w
    simp only [Pi.mul_apply, surfaceScale_apply, hc, traceShift_def, surfacePart_apply _ hN.le,
      Real.mul_rpow_of_pos_left hN]
    field_simp
  have hpre : surfaceMul c ⁻¹' (Subtype.val ⁻¹' ((traceShift K * ·) '' D)) =
      Subtype.val ⁻¹' D := by
    ext x
    simp only [mem_preimage, surfaceMul_apply]
    refine (Function.Injective.mem_set_image fun a b hab ↦ funext fun w ↦ ?_)
    exact mul_left_cancel₀ ((mem_normOneSurface.mp c.2).1 w).ne' (congrFun hab w)
  simp_rw [mellinKernel_def, hpt]
  rw [← hpre, (measurePreserving_surfaceMul c).setIntegral_preimage_emb
    (surfaceMul c).measurableEmbedding fun y : normOneSurface K ↦ latticeTheta (idealLattice K J)
      (surfaceScale (y : realSpace K) (u / ZLattice.covolume (idealLattice K J) volume ^ 2))]

end TauCeti.LFunctions
