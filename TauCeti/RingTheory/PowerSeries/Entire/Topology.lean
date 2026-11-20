/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.GaussFamily
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# The Gauss topology on entire series

For an ultrametric normed ring `R`, the algebra of entire power series carries the topology of
the Gauss norms at all positive radii. Convergence is convergence in each of these norms, rather
than convergence of individual coefficients. The resulting uniform ring is Hausdorff and is
complete when `R` is complete.

Restriction embeds the algebra into the product of the closed-disc algebras of all positive
radii. Its image consists of the families with the same formal coefficients at every radius.
This description proves completeness without choosing a sequence of radii or a single norm.
Convergence may also be tested along any family of radii that is unbounded above, for instance
along a sequence of radii tending to infinity, so such a sequence yields the same topology.
Polynomial truncations converge in this topology, and each coefficient is a uniformly continuous
function of the series. These are specializations of the Gauss topology of a family of radii in
`TauCeti.RingTheory.PowerSeries.GaussFamily`, which also covers the series on an open disc.

Evaluation of entire series at a point `b` of a complete normed algebra, which needs no
ultrametric hypothesis on the algebra, is continuous for this topology: its value is bounded by a
constant multiple of the Gauss norm at the radius `2 ‖b‖ + 1`
(`PowerSeries.norm_evalAt_le_mul_gaussNorm`).

Because `PowerSeries.IsEntire.subring R` is a complete nonarchimedean ring whose restrictions to
each closed disc are ultrametric normed rings, convergent infinite products are preserved by
restriction, evaluation, constant coefficients, and strict Gauss-norm perturbation bounds near `1`,
and any family tending to `1` along the cofinite filter is unconditionally multipliable in
`PowerSeries.IsEntire.subring R` even when its factors are not units.

## Main results

* `TauCeti.PowerSeries.IsEntire.tendsto_iff`: convergence of entire series is convergence in every
  positive-radius Gauss norm; `TauCeti.PowerSeries.IsEntire.tendsto_iff_of_tendsto_atTop` tests it
  along radii tending to infinity.
* `TauCeti.PowerSeries.IsEntire.denseRange_polynomialHom`: polynomials are dense.
* `TauCeti.PowerSeries.IsEntire.range_restrictFamily`: the image of the restriction embedding.
* `TauCeti.PowerSeries.IsEntire.continuous_evalAtHom`: evaluation is continuous.
* `TauCeti.PowerSeries.IsEntire.hasProd_iff`,
  `TauCeti.PowerSeries.IsEntire.multipliable_iff`,
  `TauCeti.PowerSeries.IsEntire.restrict_tprod` and
  `TauCeti.PowerSeries.IsEntire.constantCoeff_tprod`: unconditional infinite products of entire
  series.
* `TauCeti.PowerSeries.IsEntire.evalAt_hasProd` and
  `TauCeti.PowerSeries.IsEntire.gaussNorm_sub_one_lt_of_hasProd`: preservation of convergent
  infinite products of entire series under evaluation and strict Gauss-norm bounds near `1`.
* `TauCeti.PowerSeries.IsEntire.summable_prod_of_tendsto_cofinite_zero`,
  `TauCeti.PowerSeries.IsEntire.multipliable_one_add_of_tendsto_cofinite_zero` and
  `TauCeti.PowerSeries.IsEntire.multipliable_of_tendsto_cofinite_one`: unconditional convergence
  of infinite products in `PowerSeries.IsEntire.subring R` over complete coefficients.
* Instances: `IsUniformAddGroup`, `IsTopologicalRing`, `NonarchimedeanRing`, `T2Space` and, over
  complete coefficients, `CompleteSpace` on `PowerSeries.IsEntire.subring R`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.IsEntire

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
local instance radius_pos (r : Set.Ioi (0 : ℝ)) : Fact (0 < (r : ℝ)) := ⟨r.property⟩

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

omit [IsUltrametricDist R] in
/-- A series is entire exactly when it is restricted at every positive radius. -/
theorem mem_subring_iff_forall_isRestricted {f : R⟦X⟧} :
    f ∈ IsEntire.subring R ↔ ∀ r : Set.Ioi (0 : ℝ), f.IsRestricted r :=
  IsEntire.mem_subring.trans <| isEntire_iff_forall_pos.trans
    ⟨fun h r ↦ h r r.property, fun h r hr ↦ h ⟨r, hr⟩⟩

/-- Restriction of an entire series to the closed disc of a positive radius. -/
noncomputable def restrict (r : Set.Ioi (0 : ℝ)) :
    IsEntire.subring R →+* IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrict (fun _ ↦ mem_subring_iff_forall_isRestricted) r

/-- Restriction leaves the underlying formal series unchanged. -/
@[simp]
theorem coe_restrict (r : Set.Ioi (0 : ℝ)) (f : IsEntire.subring R) :
    (restrict r f : R⟦X⟧) = f :=
  GaussFamily.coe_restrict _ r f

/-- Restriction of an entire series to the closed discs of all positive radii at once. -/
noncomputable def restrictFamily :
    IsEntire.subring R →+* ∀ r : Set.Ioi (0 : ℝ), IsRestricted.subring (R := R) (r : ℝ) :=
  GaussFamily.restrictFamily fun _ ↦ mem_subring_iff_forall_isRestricted

/-- Each component of the family of restrictions is the restriction to that radius. -/
@[simp]
theorem restrictFamily_apply (f : IsEntire.subring R) (r : Set.Ioi (0 : ℝ)) :
    restrictFamily f r = restrict r f :=
  GaussFamily.restrictFamily_apply _ f r

/-- The uniformity generated by the Gauss norms at all positive radii. -/
noncomputable instance uniformSpace : UniformSpace (IsEntire.subring R) :=
  GaussFamily.uniformSpace fun _ ↦ mem_subring_iff_forall_isRestricted

/-- The Gauss uniformity is induced by the family of closed-disc restrictions. -/
theorem isUniformInducing_restrictFamily :
    IsUniformInducing (restrictFamily (R := R)) :=
  GaussFamily.isUniformInducing_restrictFamily_uniformSpace _

/-- Restriction to any closed disc is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_restrict (r : Set.Ioi (0 : ℝ)) :
    UniformContinuous (restrict (R := R) r) :=
  GaussFamily.uniformContinuous_restrict isUniformInducing_restrictFamily r

/-- Convergence of entire series is convergence in the Gauss norm at every positive radius. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι}
    {f : ι → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f l (𝓝 g) ↔ ∀ r : Set.Ioi (0 : ℝ),
      Tendsto (fun i ↦ restrict r (f i)) l (𝓝 (restrict r g)) :=
  GaussFamily.tendsto_iff isUniformInducing_restrictFamily

/-- Convergence can be tested at any family of positive radii that is unbounded above. -/
theorem tendsto_iff_of_cofinal_radius {ι κ : Type*}
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : ∀ r : Set.Ioi (0 : ℝ), ∃ i, (r : ℝ) ≤ ρ i)
    {F : Filter κ} {f : κ → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  GaussFamily.tendsto_iff_of_cofinal_radius isUniformInducing_restrictFamily hρ

/-- Convergence can be tested along positive radii tending to infinity, for instance along a
sequence of radii tending to infinity. -/
theorem tendsto_iff_of_tendsto_atTop {ι κ : Type*} {l : Filter ι} [l.NeBot]
    {ρ : ι → Set.Ioi (0 : ℝ)} (hρ : Tendsto (fun i ↦ (ρ i : ℝ)) l atTop)
    {F : Filter κ} {f : κ → IsEntire.subring R} {g : IsEntire.subring R} :
    Tendsto f F (𝓝 g) ↔ ∀ i, Tendsto (fun j ↦ restrict (ρ i) (f j)) F (𝓝 (restrict (ρ i) g)) :=
  tendsto_iff_of_cofinal_radius fun r ↦ (hρ.eventually_ge_atTop (r : ℝ)).exists

/-- A map into the entire series is continuous exactly when each restriction is continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → IsEntire.subring R} :
    Continuous f ↔ ∀ r : Set.Ioi (0 : ℝ), Continuous fun x ↦ restrict r (f x) :=
  GaussFamily.continuous_iff isUniformInducing_restrictFamily

/-- A map into the entire series is uniformly continuous exactly when each restriction is. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X] {f : X → IsEntire.subring R} :
    UniformContinuous f ↔ ∀ r : Set.Ioi (0 : ℝ), UniformContinuous fun x ↦ restrict r (f x) :=
  GaussFamily.uniformContinuous_iff isUniformInducing_restrictFamily

instance : IsUniformAddGroup (IsEntire.subring R) :=
  GaussFamily.isUniformAddGroup isUniformInducing_restrictFamily

instance : IsTopologicalRing (IsEntire.subring R) :=
  GaussFamily.isTopologicalRing isUniformInducing_restrictFamily

instance : NonarchimedeanRing (IsEntire.subring R) :=
  GaussFamily.nonarchimedeanRing isUniformInducing_restrictFamily

/-- Polynomial truncations converge in the Gauss norms at all positive radii simultaneously. -/
theorem tendsto_polynomialHom_trunc (f : IsEntire.subring R) :
    Tendsto (fun n ↦ IsEntire.polynomialHom ((f : R⟦X⟧).trunc n)) atTop (𝓝 f) :=
  GaussFamily.tendsto_polynomialHom_trunc isUniformInducing_restrictFamily _
    IsEntire.coe_polynomialHom f

/-- Polynomials are dense for the topology of the Gauss norms at all positive radii. -/
theorem denseRange_polynomialHom : DenseRange (IsEntire.polynomialHom (R := R)) :=
  GaussFamily.denseRange_polynomialHom isUniformInducing_restrictFamily _
    IsEntire.coe_polynomialHom

instance : T2Space (IsEntire.subring R) :=
  GaussFamily.t2Space isUniformInducing_restrictFamily

/-- Each coefficient is uniformly continuous for the Gauss uniformity on entire series. -/
theorem uniformContinuous_coeff (n : ℕ) :
    UniformContinuous fun f : IsEntire.subring R ↦ coeff n (f : R⟦X⟧) :=
  GaussFamily.uniformContinuous_coeff isUniformInducing_restrictFamily n

/-- The restriction image consists exactly of families with radius-independent coefficients. -/
theorem range_restrictFamily :
    Set.range (restrictFamily (R := R)) =
      {g | ∀ r s : Set.Ioi (0 : ℝ), ∀ n : ℕ, coeff n (g r : R⟦X⟧) = coeff n (g s : R⟦X⟧)} :=
  GaussFamily.range_restrictFamily _

/-- The entire series with the Gauss norms at all positive radii form a complete ring over
complete coefficients. -/
instance [CompleteSpace R] : CompleteSpace (IsEntire.subring R) :=
  GaussFamily.completeSpace isUniformInducing_restrictFamily

end NormedRing

section Eval

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A]

/-- The radius `2 ‖b‖ + 1`, at least twice the norm of `b`, whose Gauss norm controls
evaluation at `b`. -/
private noncomputable def evalRadius (b : A) : Set.Ioi (0 : ℝ) :=
  ⟨2 * ‖b‖ + 1, Set.mem_Ioi.mpr (by positivity)⟩

variable [CompleteSpace A]

/-- Evaluation of entire series at a point of a complete normed algebra is continuous for the
topology of the Gauss norms at all positive radii. -/
theorem continuous_evalAtHom (b : A) : Continuous (IsEntire.evalAtHom R b) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  have h : Tendsto (restrict (R := R) (evalRadius b)) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using
      (uniformContinuous_restrict (R := R) (evalRadius b)).continuous.tendsto 0
  have hb : ‖b‖ ≤ 2⁻¹ * (evalRadius b : ℝ) := by
    simp only [evalRadius]
    linarith
  refine squeeze_zero_norm
    (a := fun f ↦ (‖(1 : A)‖ + 1) * ‖restrict (evalRadius b) f‖ * (1 - 2⁻¹)⁻¹) (fun f ↦ ?_) ?_
  · have hf := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (restrict (evalRadius b) f).property
    rw [coe_restrict] at hf
    rw [IsEntire.evalAtHom_apply, TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict]
    exact norm_evalAt_le_mul_gaussNorm hf (by norm_num) (by norm_num) hb
  · simpa using (h.norm.const_mul (‖(1 : A)‖ + 1)).mul_const (1 - 2⁻¹ : ℝ)⁻¹

end Eval

section InfiniteProd

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- An unconditional product of entire series converges in the Gauss topology exactly when its
restriction to every positive-radius closed disc converges. -/
theorem hasProd_iff {ι : Type*} {f : ι → IsEntire.subring R} {g : IsEntire.subring R} :
    HasProd f g ↔
      ∀ r : Set.Ioi (0 : ℝ), HasProd (fun i ↦ restrict r (f i)) (restrict r g) :=
  GaussFamily.hasProd_iff isUniformInducing_restrictFamily

/-- A family of entire series is unconditionally multipliable in the Gauss topology exactly when
its restriction to every positive-radius closed disc is multipliable. -/
theorem multipliable_iff {ι : Type*} {f : ι → IsEntire.subring R} :
    Multipliable f ↔ ∀ r : Set.Ioi (0 : ℝ), Multipliable fun i ↦ restrict r (f i) :=
  GaussFamily.multipliable_iff isUniformInducing_restrictFamily

/-- Restriction to a positive-radius closed disc commutes with convergent infinite products of
entire series. -/
theorem restrict_tprod {ι : Type*} {f : ι → IsEntire.subring R} (hf : Multipliable f)
    (r : Set.Ioi (0 : ℝ)) :
    restrict r (∏' i, f i) = ∏' i, restrict r (f i) :=
  GaussFamily.restrict_tprod isUniformInducing_restrictFamily hf r

/-- The constant coefficient of a convergent infinite product of entire series is the infinite
product of the constant coefficients. -/
theorem constantCoeff_tprod {ι : Type*} {f : ι → IsEntire.subring R} (hf : Multipliable f) :
    constantCoeff ((∏' i, f i : IsEntire.subring R) : R⟦X⟧) =
      ∏' i, constantCoeff (f i : R⟦X⟧) :=
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, one_pos⟩⟩
  GaussFamily.constantCoeff_tprod isUniformInducing_restrictFamily hf

/-- Evaluation at a point of a complete normed commutative algebra preserves convergent infinite
products of entire series. -/
theorem evalAt_hasProd {ι A : Type*} [NormedCommRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] {f : ι → IsEntire.subring R} {g : IsEntire.subring R}
    (hf : HasProd f g) (b : A) :
    HasProd (fun i ↦ (f i : R⟦X⟧).evalAt b) ((g : R⟦X⟧).evalAt b) := by
  simpa only [Function.comp_def, IsEntire.evalAtHom_apply] using
    hf.map (IsEntire.evalAtHom R b) (continuous_evalAtHom b)

/-- If every factor of a convergent infinite product of entire series lies strictly within `ε ≤ 1`
of `1` in the Gauss norm at `r > 0`, then so does the infinite product. -/
theorem gaussNorm_sub_one_lt_of_hasProd {ι : Type*} {f : ι → IsEntire.subring R}
    {g : IsEntire.subring R} (hf : HasProd f g) {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (h : ∀ i, ((f i : R⟦X⟧) - 1).gaussNorm norm r < ε) :
    ((g : R⟦X⟧) - 1).gaussNorm norm r < ε := by
  have : Fact (0 < r) := ⟨hr⟩
  have hlt := (hasProd_iff.mp hf ⟨r, hr⟩).norm_sub_one_lt hε0 hε fun i ↦ by
    rw [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
      OneMemClass.coe_one]
    exact h i
  rwa [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
    OneMemClass.coe_one] at hlt

variable [CompleteSpace R]

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then the family of finite products `s ↦ ∏ i ∈ s, f i` is
unconditionally summable. -/
theorem summable_prod_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_iff.mpr fun r ↦ ?_)
  have hr : Tendsto (fun i ↦ restrict r (f i)) cofinite (𝓝 0) := by
    simpa only [map_zero] using tendsto_iff.mp hf r
  simpa only [map_zero, map_prod] using TauCeti.tendsto_finsetProd_cofinite_zero hr

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then `i ↦ 1 + f i` is unconditionally multipliable. -/
theorem multipliable_one_add_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Multipliable fun i ↦ 1 + f i :=
  multipliable_one_add_of_summable_prod (summable_prod_of_tendsto_cofinite_zero hf)

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, any
family tending to `1` along the cofinite filter is unconditionally multipliable, even when its
factors are not units of `PowerSeries.IsEntire.subring R`. -/
theorem multipliable_of_tendsto_cofinite_one {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 1)) :
    Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using multipliable_one_add_of_tendsto_cofinite_zero h0

end InfiniteProd

end TauCeti.PowerSeries.IsEntire
