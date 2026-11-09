/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Inversion
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Invariance

/-!
# The Mellin kernel of a lattice

Hecke's integral representation of a partial zeta function averages the theta series `θ_L(y)` of
a lattice `L` of the mixed space over a set `D` of the norm-one hypersurface `S`, normally a unit
fundamental domain, and keeps only the norm of the parameter as a radial variable. This file
defines that average, Neukirch's kernel of VII (5.5),

`f_D(L, u) = (2^r₂ / w) ∫_D θ_L(x (u / V_L²)^(1/n)) d*x`,

where `V_L` is the covolume of `L`, `n = [K : ℚ]`, `r₂` is the number of complex places, `w` is
the number of roots of unity and `d*x` is `surfaceHaar K`. The factor `2^r₂` compensates the
product-over-places normalization of `d*x`, which is `2^(-r₂)` times Neukirch's canonical measure,
and `1/w` accounts for the roots of unity, which act trivially on the parameters.

* `mellinKernel_inv`: the transformation law `f_D(L, 1/u) = u^(1/2) f_{D⁻¹}(L^∨, u)` for every
  full lattice `L` and every `D`, the first half of Neukirch (5.8). It follows from the theta
  transformation `latticeTheta_inv` and the invariance of `d*x` under inversion; the covolumes
  `V_L V_{L^∨} = 1` make the two rescalings match.
* `continuousOn_mellinKernel`: for a bounded measurable `D` the kernel is continuous on `(0, ∞)`.
  A bounded subset of `S` lies in a box `[C⁻¹, C]` of the open orthant, so near a positive `u` the
  theta series is dominated by a constant, which is integrable because `D` has finite `d*x`-mass.

These are the transformation law and the local integrability that Mathlib's Mellin principle
`WeakFEPair` asks of a pair of kernels.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5) and (5.8).
-/

public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Pointwise

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The Mellin kernel** of a lattice `L` over a set `D` of parameters, Neukirch VII (5.5):
`f_D(L, u) = (2^r₂ / w) ∫_D θ_L(x (u / V_L²)^(1/n)) d*x`, the theta series of `L` averaged over
the points `x` of `D` on the norm-one hypersurface at the norm `u / V_L²`, with `V_L` the covolume
of `L` and `d*x = surfaceHaar K`. -/
def mellinKernel (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K)) (u : ℝ) : ℂ :=
  (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
    ∫ x in Subtype.val ⁻¹' D,
      latticeTheta L (surfaceScale (x : realSpace K) (u / ZLattice.covolume L ^ 2)) ∂surfaceHaar K

open scoped Classical in
theorem mellinKernel_def (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K)) (u : ℝ) :
    mellinKernel D L u = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
      ∫ x in Subtype.val ⁻¹' D,
        latticeTheta L (surfaceScale (x : realSpace K) (u / ZLattice.covolume L ^ 2))
          ∂surfaceHaar K := (rfl)

open scoped Classical in
/-- The theta transformation `latticeTheta_inv` in norm-one and radial coordinates: at a point
`x` of `S` and the norm `u⁻¹ / V_L²`, the theta series of `L` is `√u` times that of the dual
lattice at `x⁻¹` and the norm `u / V_{L^∨}²`. -/
theorem latticeTheta_surfaceScale_inv (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {x : realSpace K} (hx : x ∈ normOneSurface K) {u : ℝ} (hu : 0 < u) :
    latticeTheta L (surfaceScale x (u⁻¹ / ZLattice.covolume L ^ 2)) =
      (√u : ℂ) * latticeTheta (mixedDual K L)
        (surfaceScale x⁻¹ (u / ZLattice.covolume (mixedDual K L) ^ 2)) := by
  set V := ZLattice.covolume L
  have hV : 0 < V := ZLattice.covolume_pos L
  have ht : 0 < u⁻¹ / V ^ 2 := by positivity
  have hc : (V : ℂ)⁻¹ * ((√(u⁻¹ / V ^ 2))⁻¹ : ℝ) = √u := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hV.le, Real.sqrt_inv]
    congr 1
    field_simp
  have ht' : (u⁻¹ / V ^ 2)⁻¹ = u / V⁻¹ ^ 2 := by
    field_simp
  rw [latticeTheta_inv L _ (surfaceScale_pos (mem_normOneSurface.mp hx).1 ht),
    archNorm_surfaceScale_of_mem_normOneSurface hx ht.le, surfaceScale_inv _ ht.le,
    covolume_mixedDual, hc, ht']

open scoped Classical in
/-- **The transformation law of the Mellin kernel**, the first half of Neukirch VII (5.8):
`f_D(L, 1/u) = u^(1/2) f_{D⁻¹}(L^∨, u)` for every full lattice `L`, with the Euclidean dual
`L^∨ = mixedDual K L`, and every set `D` of parameters. -/
theorem mellinKernel_inv (D : Set (realSpace K)) (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L] {u : ℝ} (hu : 0 < u) :
    mellinKernel D L u⁻¹ = (√u : ℂ) * mellinKernel D⁻¹ (mixedDual K L) u := by
  set g : normOneSurface K → ℂ := fun z ↦
    latticeTheta (mixedDual K L) (surfaceScale (z : realSpace K)
      (u / ZLattice.covolume (mixedDual K L) ^ 2))
  have hpre : surfaceInv K ⁻¹' (Subtype.val ⁻¹' D⁻¹) = Subtype.val ⁻¹' D := by
    ext x
    simp
  have h (x : normOneSurface K) :
      latticeTheta L (surfaceScale (x : realSpace K) (u⁻¹ / ZLattice.covolume L ^ 2)) =
        (√u : ℂ) * g (surfaceInv K x) := by
    rw [latticeTheta_surfaceScale_inv L x.property hu]
    simp only [g, surfaceInv_apply]
  rw [mellinKernel_def, mellinKernel_def, integral_congr_ae (Filter.Eventually.of_forall h),
    integral_const_mul, ← hpre, measurePreserving_surfaceInv.setIntegral_preimage_emb
      (surfaceInv K).measurableEmbedding]
  ring

open scoped Classical in
/-- **The Mellin kernel is continuous on `(0, ∞)`** for a bounded measurable set `D` of
parameters, such as a unit fundamental domain. -/
theorem continuousOn_mellinKernel {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ContinuousOn (mellinKernel D L) (Set.Ioi 0) := by
  intro u₀ hu₀
  replace hu₀ : 0 < u₀ := hu₀
  refine ContinuousAt.continuousWithinAt ?_
  set V := ZLattice.covolume L
  have hV : 0 < V := ZLattice.covolume_pos L
  set F : ℝ → normOneSurface K → ℂ := fun u x ↦
    latticeTheta L (surfaceScale (x : realSpace K) (u / V ^ 2))
  have hscale (u : ℝ) : Continuous fun x : normOneSurface K ↦
      surfaceScale (x : realSpace K) (u / V ^ 2) :=
    continuous_surfaceScale.comp (continuous_subtype_val.prodMk continuous_const)
  -- on `S ∩ D` the coordinates are bounded below by `C⁻¹ > 0`
  obtain ⟨C, hC1, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  set δ := C⁻¹ * (u₀ / 2 / V ^ 2) ^ (1 / (Module.finrank ℚ K : ℝ))
  have hδ : 0 < δ := by positivity
  have hmeas : ∀ᶠ u in nhds u₀, AEStronglyMeasurable (F u)
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    filter_upwards [Ioi_mem_nhds hu₀] with u (hu : 0 < u)
    refine (continuous_iff_continuousAt.mpr fun x : normOneSurface K ↦ ?_).aestronglyMeasurable
    exact ContinuousAt.comp (g := latticeTheta L) (continuousAt_latticeTheta L
      (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity)))
        (hscale u).continuousAt
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ x ∂(surfaceHaar K).restrict (Subtype.val ⁻¹' D),
      ‖F u x‖ ≤ ‖latticeTheta L fun _ ↦ δ‖ := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hu₀)] with u (hu : u₀ / 2 < u)
    filter_upwards [ae_restrict_mem (measurable_subtype_coe hDm)] with x hx
    refine norm_latticeTheta_le L (fun _ ↦ hδ) fun w ↦ ?_
    rw [surfaceScale_apply]
    exact mul_le_mul (hC x hx x.property w).1 (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right hu.le (sq_nonneg V)) (by positivity))
      (by positivity) ((mem_normOneSurface.mp x.property).1 w).le
  have hint : Integrable (fun _ ↦ ‖latticeTheta L fun _ ↦ δ‖)
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
    exact integrable_const _
  have hcont : ∀ᵐ x ∂(surfaceHaar K).restrict (Subtype.val ⁻¹' D),
      ContinuousAt (fun u ↦ F u x) u₀ := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hu : Continuous fun u : ℝ ↦ surfaceScale (x : realSpace K) (u / V ^ 2) :=
      continuous_surfaceScale.comp (continuous_const.prodMk (continuous_id.div_const _))
    exact ContinuousAt.comp (g := latticeTheta L) (continuousAt_latticeTheta L
      (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (by positivity))) hu.continuousAt
  exact continuousAt_const.mul (continuousAt_of_dominated hmeas hbound hint hcont)

end TauCeti.LFunctions
