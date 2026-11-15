/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Theta.Decay
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
* `exists_norm_mellinKernel_sub_le`: for a bounded measurable `D` the kernel tends to
  `(2^r₂ / w) vol(D)` with error `O(exp(-c u^(1/n)))`, uniformly from the decay of the theta
  series on bounded subsets of `S`, the second half of Neukirch (5.8);
  `isBigO_mellinKernel_sub_rpow` is the resulting decay faster than every power.
* `mellinKernel_mixedDual_idealLattice`: for the lattice `σ(I)` of a fractional ideal, the dual
  side is again the kernel of an ideal lattice, that of the trace dual `J = I^∨`, over the
  translate of `D` by the point `traceShift K` of `S`. The Euclidean dual of `σ(I)` is
  `traceToEuclidean K` applied to `σ(J)` (`mixedDual_idealLattice`); this map multiplies the
  absolute value at `w` by `mult w`, which on the Gaussian multiplies the parameter by `mult w ^ 2`,
  and the radial part `16 ^ r₂` of that multiplication is absorbed by the covolumes
  `V_J = 4^(-r₂) V_I⁻¹` (`covolume_idealLattice_dual`).

The transformation law, the local integrability and the decay at `∞` are what Mathlib's
Mellin principle `WeakFEPair` asks of a pair of kernels.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5) and (5.8).
-/

public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Pointwise nonZeroDivisors

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
/-- On a bounded surface set, the theta series is uniformly bounded for radial parameters
above any fixed positive lower radius. -/
theorem exists_norm_latticeTheta_surfaceScale_le {D : Set (realSpace K)}
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ t ≥ t₀, ∀ x : normOneSurface K, (x : realSpace K) ∈ D →
      ‖latticeTheta L (surfaceScale (x : realSpace K) t)‖ ≤ B := by
  obtain ⟨C, hC1, hC⟩ := exists_forall_mem_Icc_of_isBounded hD
  let δ := C⁻¹ * t₀ ^ (1 / (Module.finrank ℚ K : ℝ))
  have hδ : 0 < δ := by positivity
  refine ⟨‖latticeTheta L fun _ ↦ δ‖, fun t ht x hx ↦ ?_⟩
  refine norm_latticeTheta_le L (fun _ ↦ hδ) fun w ↦ ?_
  rw [surfaceScale_apply]
  exact mul_le_mul (hC x hx x.property w).1
    (Real.rpow_le_rpow ht₀.le ht (by positivity)) (by positivity)
    ((mem_normOneSurface.mp x.property).1 w).le

open scoped Classical in
/-- For a bounded measurable surface set, the theta series at a positive radial parameter is
integrable over that set. Boundedness on the norm-one surface bounds every coordinate away from
zero, so a single Gaussian theta value dominates it. -/
theorem integrableOn_latticeTheta_surfaceScale {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K))
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦ latticeTheta L (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) := by
  obtain ⟨B, hB⟩ := exists_norm_latticeTheta_surfaceScale_le hD L ht
  have hmeas : AEStronglyMeasurable
      (fun x : normOneSurface K ↦ latticeTheta L (surfaceScale (x : realSpace K) t))
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousAt]
    intro x
    exact ContinuousAt.comp (g := latticeTheta L) (continuousAt_latticeTheta L
      (surfaceScale_pos (mem_normOneSurface.mp x.2).1 ht))
        (continuous_surfaceScale.comp
          (continuous_subtype_val.prodMk continuous_const)).continuousAt
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  refine (integrable_const B).mono' hmeas ?_
  filter_upwards [ae_restrict_mem (measurable_subtype_coe hDm)] with x hx
  exact hB t le_rfl x hx

open scoped Classical in
/-- Subtracting the constant term of the kernel subtracts `1` from the theta series before
averaging. The constant is the surface mass times `2^r₂ / w`. -/
theorem mellinKernel_sub_eq_integral_sub_one {D : Set (realSpace K)}
    (hDm : MeasurableSet D) (hD : Bornology.IsBounded D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    {u : ℝ} (hu : 0 < u) :
    mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (surfaceHaar K).real (Subtype.val ⁻¹' D) =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ∫ x in Subtype.val ⁻¹' D,
          (latticeTheta L (surfaceScale (x : realSpace K)
            (u / ZLattice.covolume L ^ 2)) - 1) ∂surfaceHaar K := by
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have := isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  rw [integral_sub (integrableOn_latticeTheta_surfaceScale hDm hD L (by positivity))
    (integrable_const _), integral_const, measureReal_restrict_apply_univ, ← Complex.coe_smul,
    smul_eq_mul, mul_one, mellinKernel_def]
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
  have ht₀ : 0 < u₀ / 2 / V ^ 2 := by positivity
  obtain ⟨B, hB⟩ := exists_norm_latticeTheta_surfaceScale_le hD L ht₀
  have hmeas : ∀ᶠ u in nhds u₀, AEStronglyMeasurable (F u)
      ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) := by
    filter_upwards [Ioi_mem_nhds hu₀] with u (hu : 0 < u)
    exact (integrableOn_latticeTheta_surfaceScale hDm hD L (by positivity)).aestronglyMeasurable
  have hbound : ∀ᶠ u in nhds u₀, ∀ᵐ x ∂(surfaceHaar K).restrict (Subtype.val ⁻¹' D),
      ‖F u x‖ ≤ B := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hu₀)] with u (hu : u₀ / 2 < u)
    filter_upwards [ae_restrict_mem (measurable_subtype_coe hDm)] with x hx
    exact hB (u / V ^ 2) (div_le_div_of_nonneg_right hu.le (sq_nonneg V)) x hx
  have hint : Integrable (fun _ ↦ B)
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

/-! ### The kernel at `∞` -/

section

open Filter Set

/-- At a positive norm `t`, the theta series of a lattice is continuous along the norm-one
surface. -/
theorem continuous_latticeTheta_surfaceScale (L : Submodule ℤ (mixedSpace K))
    {t : ℝ} (ht : 0 < t) :
    Continuous fun x : normOneSurface K ↦ latticeTheta L (surfaceScale (x : realSpace K) t) :=
  continuous_iff_continuousAt.mpr fun x ↦ ContinuousAt.comp (g := latticeTheta L)
    (continuousAt_latticeTheta L (surfaceScale_pos (mem_normOneSurface.mp x.property).1 ht))
    (continuous_surfaceScale.comp (continuous_subtype_val.prodMk continuous_const)).continuousAt

open scoped Classical in
/-- **The Mellin kernel at `∞`**: over a bounded measurable set `D` of parameters the kernel of a
full lattice tends to `(2^r₂ / w) vol(D)`, `vol = surfaceHaar K`, with an error
`O(exp(-c u^(1/n)))`, `n = [K : ℚ]`. -/
theorem exists_norm_mellinKernel_sub_le {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop,
      ‖mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  set V := ZLattice.covolume L
  have hV : 0 < V := ZLattice.covolume_pos L
  set n : ℝ := (Module.finrank ℚ K : ℝ)⁻¹
  set A : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ)
  set S : Set (normOneSurface K) := Subtype.val ⁻¹' D
  have hS : MeasurableSet S := measurable_subtype_coe hDm
  have hfin : surfaceHaar K S < ⊤ := surfaceHaar_preimage_lt_top hD
  have : IsFiniteMeasure ((surfaceHaar K).restrict S) := isFiniteMeasure_restrict.mpr hfin.ne
  -- the decay of the theta series on the bounded subset `D ∩ S` of the norm-one surface
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_latticeTheta_surfaceScale_sub_one_le L
    (hD.subset inter_subset_left) inter_subset_right
  refine ⟨c / (V ^ 2) ^ n, by positivity, ‖A‖ * (C * (surfaceHaar K).real S), by positivity, ?_⟩
  have hu : Tendsto (fun u : ℝ ↦ u / V ^ 2) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [hu.eventually h, eventually_gt_atTop 0] with u hu hu0
  set e := Real.exp (-c * (u / V ^ 2) ^ n)
  set θ : normOneSurface K → ℂ := fun x ↦ latticeTheta L (surfaceScale (x : realSpace K)
    (u / V ^ 2))
  have hθ (x : normOneSurface K) (hx : x ∈ S) : ‖θ x - 1‖ ≤ C * e := hu x ⟨hx, x.property⟩
  have hint : IntegrableOn θ S (surfaceHaar K) := by
    refine Integrable.mono' (integrable_const (1 + C * e))
      (continuous_latticeTheta_surfaceScale L (by positivity)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with x hx
    calc ‖θ x‖ ≤ ‖(1 : ℂ)‖ + ‖θ x - 1‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ 1 + C * e := by rw [norm_one]; linarith [hθ x hx]
  have hsub : mellinKernel D L u - A * ((surfaceHaar K).real S : ℂ) =
      A * ∫ x in S, (θ x - 1) ∂surfaceHaar K := by
    rw [mellinKernel_def, integral_sub hint (integrableOn_const hfin.ne), setIntegral_const,
      Complex.real_smul, mul_one, mul_sub]
  have he : e = Real.exp (-(c / (V ^ 2) ^ n) * u ^ n) := by
    simp only [e]
    rw [Real.div_rpow hu0.le (sq_nonneg V)]
    ring_nf
  rw [hsub, norm_mul, ← he]
  calc ‖A‖ * ‖∫ x in S, (θ x - 1) ∂surfaceHaar K‖
      ≤ ‖A‖ * (C * e * (surfaceHaar K).real S) :=
        mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin hθ) (norm_nonneg _)
    _ = ‖A‖ * (C * (surfaceHaar K).real S) * e := by ring

open scoped Classical in
/-- Over a bounded measurable set `D` of parameters the kernel of a full lattice minus
`(2^r₂ / w) vol(D)` decays faster than every power, as the Mellin principle requires. -/
theorem isBigO_mellinKernel_sub_rpow {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (r : ℝ) :
    (fun u ↦ mellinKernel D L u - (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ)) =O[atTop] (· ^ r) := by
  obtain ⟨c, hc, C, -, h⟩ := exists_norm_mellinKernel_sub_le hDm hD L
  refine isBigO_rpow_of_isBigO_exp_neg hc
    (inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))))
    (Asymptotics.IsBigO.of_bound C ?_) r
  filter_upwards [h] with u hu
  rwa [Real.norm_of_nonneg (Real.exp_pos _).le]

end

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

/-- The coordinates of `traceShift K`: `mult w ^ 2 / (16 ^ r₂) ^ (1 / n)`. -/
@[simp]
theorem traceShift_apply (w : InfinitePlace K) :
    traceShift K w =
      (mult w : ℝ) ^ 2 / ((16 : ℝ) ^ nrComplexPlaces K) ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [traceShift_def, surfacePart_apply _ (archNorm_mult_sq K ▸ by positivity),
    archNorm_mult_sq]

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
    rw [covolume_mixedDual, covolume_idealLattice_dual hJ, mixedDual_idealLattice hJ,
      latticeTheta_map_traceToEuclidean, surfaceMul_apply, hrad]
    congr 1
    ext w
    simp only [Pi.mul_apply, surfaceScale_apply, hc, traceShift_def, surfacePart_apply _ hN.le,
      Real.mul_rpow_of_nonneg_left hN.le]
    field_simp
  have hpre : surfaceMul c ⁻¹' (Subtype.val ⁻¹' ((traceShift K * ·) '' D)) =
      Subtype.val ⁻¹' D := by
    ext x
    simp only [Set.mem_preimage, surfaceMul_apply]
    refine (Function.Injective.mem_set_image fun a b hab ↦ funext fun w ↦ ?_)
    exact mul_left_cancel₀ ((mem_normOneSurface.mp c.2).1 w).ne' (congrFun hab w)
  simp_rw [mellinKernel_def, hpt]
  rw [← hpre, (measurePreserving_surfaceMul c).setIntegral_preimage_emb
    (surfaceMul c).measurableEmbedding fun y : normOneSurface K ↦ latticeTheta (idealLattice K J)
      (surfaceScale (y : realSpace K) (u / ZLattice.covolume (idealLattice K J) volume ^ 2))]

end TauCeti.LFunctions
