/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev topology on the framed gauge group of plane vortices

For a real order `s > 1`, the Sobolev framed gauge group `G_s = {1 + h : h ∈ H^s, |1 + h| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`) is a subgroup of `ℂ → Circle`, and as such it carries the
topology of pointwise convergence. The gauge group of the vortex field space `A_m^k` is instead
modelled on the Hilbert space `H^s(ℂ)`: two gauges are close when `u - v` is small in `H^s`. This
file constructs that topology and shows that `G_s` is a Hausdorff topological group for it.

Since `G_s` already has the pointwise topology, the Sobolev topology lives on a type synonym,
`TauCeti.Vortex.SobolevTopologicalGaugeGroup hs`, identified with the subgroup by
`TauCeti.Vortex.SobolevTopologicalGaugeGroup.toSubgroup`. An element `u` determines the element
`subOne u` of `H^s(ℂ)` whose `L²` function is `u - 1`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne`), and `u` is
determined by it (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_injective`), since `u` is
continuous.

The group laws in these coordinates are

`(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)`,    `u⁻¹ - 1 = conj (u - 1)`.

The first is polynomial, and continuous for the `H^s` norm because pointwise multiplication is a
continuous bilinear map on `H^s(ℂ)`, `s > 1` (`BesselPotentialSpace.mulCLM`). To make inversion
continuous without discussing complex conjugation on `H^s`, the topology is induced by the pair
`u ↦ (u - 1, u⁻¹ - 1) ∈ H^s(ℂ) × H^s(ℂ)`: inversion exchanges the two coordinates, and
multiplication acts on each by the polynomial above, using `(u v)⁻¹ = v⁻¹ u⁻¹`. Thus a net
converges exactly when both `u - 1` and `conj (u - 1)` converge in `H^s`.

## Main definitions

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup hs`: the group `G_s`, `s > 1`, with its Sobolev
  topology.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne`: the element `u - 1` of `H^s(ℂ)`.

## Main results

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.subOne_mul`: the product law
  `(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)` in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne_inv`: the `L²`
  function of `u⁻¹ - 1` is `conj u - 1`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isEmbedding_subOne_prod`: the topology of `G_s` is
  induced by the injective map `u ↦ (u - 1, u⁻¹ - 1)` into `H^s(ℂ) × H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.continuous_iff`: a map into `G_s` is continuous
  exactly when `u - 1` and `u⁻¹ - 1` depend continuously on the parameter in `H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instIsTopologicalGroup`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instT2Space`: `G_s` is a Hausdorff topological group.

The Banach charts of `G_s`, its completeness and the continuity of its action on the field space
`A_m^k` are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, §3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace

variable {s : ℝ}

/-- **The Sobolev framed gauge group `G_s` with its Sobolev topology**, `s > 1`. As a group it is
the subgroup `sobolevGaugeGroup hs` of `ℂ → Circle` (`SobolevTopologicalGaugeGroup.toSubgroup`);
its topology is that of `u - 1` and `u⁻¹ - 1` in `H^s(ℂ)`
(`SobolevTopologicalGaugeGroup.continuous_iff`), rather than the pointwise topology of the
subgroup. -/
def SobolevTopologicalGaugeGroup (hs : 1 < s) : Type := sobolevGaugeGroup hs

namespace SobolevTopologicalGaugeGroup

variable {hs : 1 < s}

private theorem nonneg (hs : 1 < s) : 0 ≤ s := zero_le_one.trans hs.le

instance : Group (SobolevTopologicalGaugeGroup hs) := inferInstanceAs (Group (sobolevGaugeGroup hs))

variable (hs) in
/-- The identification of `SobolevTopologicalGaugeGroup hs` with the subgroup
`sobolevGaugeGroup hs` of `ℂ → Circle`. -/
def toSubgroup : SobolevTopologicalGaugeGroup hs ≃* sobolevGaugeGroup hs := MulEquiv.refl _

/-- **The element `u - 1` of `H^s(ℂ)`** of a Sobolev gauge `u ∈ G_s`: its `L²` function is `u - 1`
(`SobolevTopologicalGaugeGroup.coeFn_toLp_inclusion_subOne`). -/
def subOne (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) :=
  (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup
    (toSubgroup hs u).2).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `subOne u` is `u - 1`. -/
theorem coeFn_toLp_inclusion_subOne (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u)).toLp =ᵐ[volume]
      fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1 := by
  obtain ⟨hae, -⟩ :=
    (exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup (toSubgroup hs u).2).choose_spec
  rw [subOne, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact hae

/-- The `L²` function of `subOne u⁻¹` is `conj u - 1`. -/
theorem coeFn_toLp_inclusion_subOne_inv (h : 0 ≤ s) (u : SobolevTopologicalGaugeGroup hs) :
    ⇑(inclusion h (subOne u⁻¹)).toLp =ᵐ[volume]
      fun z ↦ (starRingEnd ℂ) ((toSubgroup hs u : ℂ → Circle) z) - 1 := by
  filter_upwards [coeFn_toLp_inclusion_subOne h u⁻¹] with z hz
  rw [hz, map_inv]
  simp only [InvMemClass.coe_inv, Pi.inv_apply, Circle.coe_inv_eq_conj]

/-- A Sobolev gauge is determined by its element `u - 1` of `H^s(ℂ)`. -/
theorem subOne_injective :
    Function.Injective (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  intro u v huv
  have h := nonneg hs
  have hae := (coeFn_toLp_inclusion_subOne h u).symm.trans
    ((congrArg (fun a ↦ ⇑(inclusion h a).toLp) huv).eventuallyEq.trans
      (coeFn_toLp_inclusion_subOne h v))
  -- Both gauges are continuous, so almost everywhere equality is equality.
  have hcont (w : SobolevTopologicalGaugeGroup hs) :
      Continuous fun z ↦ ((toSubgroup hs w : ℂ → Circle) z : ℂ) - 1 :=
    (continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs w).2).1).sub
      continuous_const
  have heq := (hcont u).ae_eq_iff_eq volume (hcont v) |>.1 hae
  apply (toSubgroup hs).injective
  refine Subtype.ext (funext fun z ↦ Subtype.ext ?_)
  simpa using congrFun heq z

/-- The identity gauge has `u - 1 = 0`. -/
@[simp]
theorem subOne_one : subOne (1 : SobolevTopologicalGaugeGroup hs) = 0 := by
  have h := nonneg hs
  refine toLp_inclusion_injective h (Lp.ext ?_)
  filter_upwards [coeFn_toLp_inclusion_subOne h (1 : SobolevTopologicalGaugeGroup hs),
    Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z h₁ h₂
  rw [h₁, map_zero, toLp_zero, h₂, map_one]
  simp

/-- **The product law in `H^s(ℂ)`:** `(u v) - 1 = (u - 1) + (v - 1) + (u - 1) (v - 1)`. -/
theorem subOne_mul (u v : SobolevTopologicalGaugeGroup hs) :
    subOne (u * v) = subOne u + subOne v +
      mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u) (subOne v) := by
  have h := nonneg hs
  refine toLp_inclusion_injective h (Lp.ext ?_)
  have hs' := finrank_real_complex_lt_two_mul hs
  filter_upwards [coeFn_toLp_inclusion_subOne h (u * v),
    coeFn_toLp_inclusion_add h (subOne u + subOne v) (mulCLM hs' (subOne u) (subOne v)),
    coeFn_toLp_inclusion_add h (subOne u) (subOne v),
    coeFn_toLp_inclusion_mulCLM hs' h (subOne u) (subOne v),
    coeFn_toLp_inclusion_subOne h u, coeFn_toLp_inclusion_subOne h v]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, Pi.add_apply, h₃, Pi.add_apply, h₄, h₅, h₆, map_mul]
  simp only [Subgroup.coe_mul, Pi.mul_apply, Circle.coe_mul]
  ring

/-- **The Sobolev topology of `G_s`**, induced by `u ↦ (u - 1, u⁻¹ - 1) ∈ H^s(ℂ) × H^s(ℂ)`. -/
instance : TopologicalSpace (SobolevTopologicalGaugeGroup hs) :=
  .induced (fun u ↦ (subOne u, subOne u⁻¹)) inferInstance

/-- **The defining embedding of `G_s`**: its Sobolev topology is that of
`u ↦ (u - 1, u⁻¹ - 1) ∈ H^s(ℂ) × H^s(ℂ)`, which is injective since `u ↦ u - 1` is. -/
theorem isEmbedding_subOne_prod :
    IsEmbedding fun u : SobolevTopologicalGaugeGroup hs ↦ (subOne u, subOne u⁻¹) :=
  ⟨⟨rfl⟩, fun _ _ h ↦ subOne_injective (congrArg Prod.fst h)⟩

/-- **Continuity into `G_s`.** A map into `G_s` is continuous exactly when `u - 1` and `u⁻¹ - 1`
depend continuously on the parameter in `H^s(ℂ)`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → SobolevTopologicalGaugeGroup hs} :
    Continuous f ↔
      Continuous (fun x ↦ subOne (f x)) ∧ Continuous (fun x ↦ subOne (f x)⁻¹) :=
  isEmbedding_subOne_prod.continuous_iff.trans continuous_prodMk

/-- `u ↦ u - 1` is continuous from `G_s` to `H^s(ℂ)`. -/
@[fun_prop, continuity]
theorem continuous_subOne : Continuous (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  ((continuous_iff (f := (id : SobolevTopologicalGaugeGroup hs → _))).1 continuous_id).1

/-- `u ↦ u⁻¹ - 1` is continuous from `G_s` to `H^s(ℂ)`. -/
@[fun_prop, continuity]
theorem continuous_subOne_inv :
    Continuous (fun u : SobolevTopologicalGaugeGroup hs ↦ subOne u⁻¹) :=
  ((continuous_iff (f := (id : SobolevTopologicalGaugeGroup hs → _))).1 continuous_id).2

/-- **`G_s` is a topological group** for its Sobolev topology: by `subOne_mul`, multiplication
acts on `u - 1` and, through `(u v)⁻¹ = v⁻¹ u⁻¹`, on `u⁻¹ - 1` by continuous polynomial maps of
`H^s(ℂ)`, while inversion exchanges `u - 1` and `u⁻¹ - 1`. -/
instance instIsTopologicalGroup : IsTopologicalGroup (SobolevTopologicalGaugeGroup hs) where
  continuous_mul := by
    have hu : Continuous fun p : SobolevTopologicalGaugeGroup hs ×
        SobolevTopologicalGaugeGroup hs ↦ subOne p.1⁻¹ :=
      continuous_subOne_inv.comp continuous_fst
    have hv : Continuous fun p : SobolevTopologicalGaugeGroup hs ×
        SobolevTopologicalGaugeGroup hs ↦ subOne p.2⁻¹ :=
      continuous_subOne_inv.comp continuous_snd
    exact continuous_iff.2 ⟨by simp only [subOne_mul]; fun_prop,
      by simp only [mul_inv_rev, subOne_mul]; fun_prop⟩
  continuous_inv := continuous_iff.2 ⟨continuous_subOne_inv, by
    simpa only [inv_inv] using continuous_subOne⟩

/-- `G_s` is Hausdorff for its Sobolev topology, since `u ↦ u - 1` is injective. -/
instance instT2Space : T2Space (SobolevTopologicalGaugeGroup hs) :=
  isEmbedding_subOne_prod.t2Space

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
