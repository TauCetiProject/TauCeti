/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The topology of the Sobolev framed gauge group

For a real order `s > 1` the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `Re u - 1` and `Im u` in `H^s`. This file
makes `G_s` a complete metric topological group, with the topology of `H^s`.

A gauge `u ∈ G_s` has the **coordinates** `(Re u - 1, Im u)`, two real `H^s` functions, which we
view as elements of Mathlib's complex Bessel-potential space `H^s(ℂ)` through their
complexifications (`TemperedDistribution.realSobolevToBesselPotential`). The coordinate map
`SobolevGauge.coords : G_s → H^s(ℂ) × H^s(ℂ)` is injective, since a continuous function is
determined by its values almost everywhere, and `G_s` carries the metric pulled back along it.
Writing `u = (1 + a) + i b` and `v = (1 + c) + i d`, the group law in coordinates is

`u v = (1 + (a + c + a c - b d)) + i (b + d + a d + b c)`,  `u⁻¹ = (1 + a) - i b`

(`SobolevGauge.coords_mul`, `SobolevGauge.coords_inv`). The products are the bounded bilinear
product of the algebra `H^s(ℂ)`, `s > 1` (`BesselPotentialSpace.mulCLM`), so multiplication and
inversion are continuous, and `G_s` is a topological group.

Since the subgroup `sobolevGaugeGroup hs` of `ℂ → Circle` already carries the topology of
pointwise convergence, the group with its `H^s` topology is the type synonym
`SobolevGauge hs`, identified with the subgroup by `SobolevGauge.toSubgroup`.

The image of the coordinate map is closed (`SobolevGauge.isClosed_range_coords`): a limit in `H^s`
of coordinates of gauges is the limit almost everywhere, by the Sobolev embedding, so it is real,
it satisfies `|1 + a + i b| = 1` almost everywhere, and its continuous representative, given by
the Sobolev embedding again, is a gauge. Hence `G_s` is complete. The complex function `u - 1`
is `a + i b`, so it depends continuously on `u` in `H^s(ℂ; ℂ)`; together with
`TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp` this shows that the
exponentials `exp (i f)` of continuous real `H^s` phases form a neighbourhood of the identity
(`SobolevGauge.setOf_exists_eq_exp_mem_nhds_one`).

## Main definitions

* `TauCeti.Vortex.SobolevGauge hs`: the group `G_s`, `s > 1`, with its `H^s` metric.
* `TauCeti.Vortex.SobolevGauge.coords`: the coordinates `(Re u - 1, Im u) ∈ H^s(ℂ) × H^s(ℂ)`.

## Main results

* `TauCeti.Vortex.SobolevGauge.coords_injective`, `TauCeti.Vortex.SobolevGauge.isometry_coords`:
  the coordinates are an isometric embedding.
* `TauCeti.Vortex.SobolevGauge.coords_mul`, `TauCeti.Vortex.SobolevGauge.coords_inv`: the group
  law in coordinates.
* The `IsTopologicalGroup` and `CompleteSpace` instances on `SobolevGauge hs`.
* `TauCeti.Vortex.SobolevGauge.isClosed_range_coords`: the image of the coordinates is closed.
* `TauCeti.Vortex.SobolevGauge.setOf_exists_eq_exp_mem_nhds_one`: the exponentials of continuous
  real `H^s` phases form a neighbourhood of the identity.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Module MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped Topology BesselPotentialSpace SchwartzMap

/-- **The Sobolev framed gauge group `G_s` with its `H^s` topology**, `s > 1`. This is a type
synonym of the subgroup `sobolevGaugeGroup hs` of `ℂ → Circle`, whose own topology is that of
pointwise convergence. It carries the metric of the coordinates `SobolevGauge.coords`. -/
def SobolevGauge {s : ℝ} (hs : 1 < s) : Type := sobolevGaugeGroup hs

namespace SobolevGauge

variable {s : ℝ} {hs : 1 < s}

instance : CommGroup (SobolevGauge hs) := inferInstanceAs (CommGroup (sobolevGaugeGroup hs))

variable (hs) in
/-- The identification of `SobolevGauge hs` with the subgroup `sobolevGaugeGroup hs`. -/
def toSubgroup : SobolevGauge hs ≃* sobolevGaugeGroup hs := MulEquiv.refl _

instance : FunLike (SobolevGauge hs) ℂ Circle where
  coe u := (toSubgroup hs u : ℂ → Circle)
  coe_injective _ _ h := (toSubgroup hs).injective (Subtype.ext h)

@[simp]
theorem coe_toSubgroup (u : SobolevGauge hs) : ((toSubgroup hs u : sobolevGaugeGroup hs) :
    ℂ → Circle) = u :=
  rfl

@[simp]
theorem coe_toSubgroup_symm (u : sobolevGaugeGroup hs) : ⇑((toSubgroup hs).symm u) = u := by
  rw [← coe_toSubgroup, MulEquiv.apply_symm_apply]

@[ext]
theorem ext {u v : SobolevGauge hs} (h : ∀ z, u z = v z) : u = v :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_one : ⇑(1 : SobolevGauge hs) = 1 := by
  rw [← coe_toSubgroup, map_one, OneMemClass.coe_one]

@[simp]
theorem coe_mul (u v : SobolevGauge hs) : ⇑(u * v) = u * v := by
  rw [← coe_toSubgroup, map_mul, Subgroup.coe_mul, coe_toSubgroup, coe_toSubgroup]

@[simp]
theorem coe_inv (u : SobolevGauge hs) : ⇑u⁻¹ = (⇑u)⁻¹ := by
  rw [← coe_toSubgroup, map_inv, Subgroup.coe_inv, coe_toSubgroup]

/-- The underlying map of an element of `SobolevGauge hs` lies in `sobolevGaugeGroup hs`. -/
theorem coe_mem (u : SobolevGauge hs) : ⇑u ∈ sobolevGaugeGroup hs :=
  (toSubgroup hs u).2

/-- Elements of `G_s` are continuous. -/
protected theorem continuous (u : SobolevGauge hs) : Continuous u :=
  ((mem_sobolevGaugeGroup hs _).1 u.coe_mem).1

/-- `Re u - 1` is a real `H^s` function. -/
theorem re_sub_one_mem_realSobolevFunctions (u : SobolevGauge hs) :
    (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 :=
  ((mem_sobolevGaugeGroup hs _).1 u.coe_mem).2.1

/-- `Im u` is a real `H^s` function. -/
theorem im_mem_realSobolevFunctions (u : SobolevGauge hs) :
    (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2 :=
  ((mem_sobolevGaugeGroup hs _).1 u.coe_mem).2.2

/-! ### Coordinates -/

private theorem memLp_ofReal_re_sub_one (u : SobolevGauge hs) :
    MemLp (fun z ↦ (((u z : ℂ).re - 1 : ℝ) : ℂ)) 2 volume :=
  Complex.ofRealCLM.comp_memLp'
    (memLp_of_mem_realSobolevFunctions u.re_sub_one_mem_realSobolevFunctions)

private theorem memLp_ofReal_im (u : SobolevGauge hs) :
    MemLp (fun z ↦ (((u z : ℂ).im : ℝ) : ℂ)) 2 volume :=
  Complex.ofRealCLM.comp_memLp' (memLp_of_mem_realSobolevFunctions u.im_mem_realSobolevFunctions)

/-- The real `H^s` function `Re u - 1`. -/
private def reCoord (u : SobolevGauge hs) : realSobolevFunctions ℂ s 2 :=
  ⟨fun z ↦ (u z : ℂ).re - 1, u.re_sub_one_mem_realSobolevFunctions⟩

/-- The real `H^s` function `Im u`. -/
private def imCoord (u : SobolevGauge hs) : realSobolevFunctions ℂ s 2 :=
  ⟨fun z ↦ (u z : ℂ).im, u.im_mem_realSobolevFunctions⟩

/-- **The `H^s` coordinates of a gauge** `u ∈ G_s`: the complexifications of the real `H^s`
functions `Re u - 1` and `Im u`, in `H^s(ℂ) × H^s(ℂ)`. They are characterized by
`SobolevGauge.toDistr_coords_fst` and `SobolevGauge.toDistr_coords_snd`. -/
def coords (u : SobolevGauge hs) : H^{s}(ℂ) × H^{s}(ℂ) :=
  (realSobolevToBesselPotential ℂ s 2 (reCoord u), realSobolevToBesselPotential ℂ s 2 (imCoord u))

/-- The first coordinate of `u` is the tempered distribution of `Re u - 1`. -/
theorem toDistr_coords_fst (u : SobolevGauge hs) {w : Lp ℂ 2 (volume : Measure ℂ)}
    (hw : w =ᵐ[volume] fun z ↦ (((u z : ℂ).re - 1 : ℝ) : ℂ)) : (coords u).1.toDistr = w :=
  toDistr_realSobolevToBesselPotential _ hw

/-- The second coordinate of `u` is the tempered distribution of `Im u`. -/
theorem toDistr_coords_snd (u : SobolevGauge hs) {w : Lp ℂ 2 (volume : Measure ℂ)}
    (hw : w =ᵐ[volume] fun z ↦ (((u z : ℂ).im : ℝ) : ℂ)) : (coords u).2.toDistr = w :=
  toDistr_realSobolevToBesselPotential _ hw

/-- A gauge is determined by its coordinates. -/
theorem coords_injective : Function.Injective (coords (hs := hs)) := by
  intro u v h
  have hre := realSobolevToBesselPotential_eq_iff.1 (congrArg Prod.fst h)
  have him := realSobolevToBesselPotential_eq_iff.1 (congrArg Prod.snd h)
  have hu : Continuous fun z ↦ (u z : ℂ) := continuous_subtype_val.comp u.continuous
  have hv : Continuous fun z ↦ (v z : ℂ) := continuous_subtype_val.comp v.continuous
  have hre' := Continuous.ae_eq_iff_eq volume (f := fun z ↦ (u z : ℂ).re - 1)
    (g := fun z ↦ (v z : ℂ).re - 1) (by fun_prop) (by fun_prop)
  have him' := Continuous.ae_eq_iff_eq volume (f := fun z ↦ (u z : ℂ).im)
    (g := fun z ↦ (v z : ℂ).im) (by fun_prop) (by fun_prop)
  refine ext fun z ↦ Circle.ext (Complex.ext ?_ (congrFun (him'.1 him) z))
  simpa using congrFun (hre'.1 hre) z

@[simp]
theorem coords_one : coords (1 : SobolevGauge hs) = 0 := by
  have h₁ : reCoord (1 : SobolevGauge hs) = 0 := Subtype.ext (funext fun z ↦ by simp [reCoord])
  have h₂ : imCoord (1 : SobolevGauge hs) = 0 := Subtype.ext (funext fun z ↦ by simp [imCoord])
  simp [coords, h₁, h₂]

/-- **The group law in coordinates.** If `u = (1 + a) + i b` and `v = (1 + c) + i d`, then
`u v = (1 + (a + c + a c - b d)) + i (b + d + a d + b c)`, the products being taken in the algebra
`H^s(ℂ)`. -/
theorem coords_mul (u v : SobolevGauge hs) :
    coords (u * v) =
      ((coords u).1 + (coords v).1 +
          mulCLM (finrank_real_complex_lt_two_mul hs) (coords u).1 (coords v).1 -
          mulCLM (finrank_real_complex_lt_two_mul hs) (coords u).2 (coords v).2,
        (coords u).2 + (coords v).2 +
          mulCLM (finrank_real_complex_lt_two_mul hs) (coords u).1 (coords v).2 +
          mulCLM (finrank_real_complex_lt_two_mul hs) (coords u).2 (coords v).1) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have hre : reCoord (u * v) = reCoord u + reCoord v +
      ⟨_, mul_mem_realSobolevFunctions hs' (reCoord u).2 (reCoord v).2⟩ -
      ⟨_, mul_mem_realSobolevFunctions hs' (imCoord u).2 (imCoord v).2⟩ :=
    Subtype.ext <| funext fun z ↦ by
      simp only [reCoord, imCoord, coe_mul, Pi.mul_apply, Circle.coe_mul, mul_re,
        Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply]
      ring
  have him : imCoord (u * v) = imCoord u + imCoord v +
      ⟨_, mul_mem_realSobolevFunctions hs' (reCoord u).2 (imCoord v).2⟩ +
      ⟨_, mul_mem_realSobolevFunctions hs' (imCoord u).2 (reCoord v).2⟩ :=
    Subtype.ext <| funext fun z ↦ by
      simp only [reCoord, imCoord, coe_mul, Pi.mul_apply, Circle.coe_mul, mul_im,
        Submodule.coe_add, Pi.add_apply]
      ring
  simp only [coords, hre, him, map_add, map_sub, realSobolevToBesselPotential_mul hs']

/-- **Inversion in coordinates.** If `u = (1 + a) + i b`, then `u⁻¹ = (1 + a) - i b`. -/
theorem coords_inv (u : SobolevGauge hs) : coords u⁻¹ = ((coords u).1, -(coords u).2) := by
  have hre : reCoord u⁻¹ = reCoord u :=
    Subtype.ext <| funext fun z ↦ by simp [reCoord]
  have him : imCoord u⁻¹ = -imCoord u :=
    Subtype.ext <| funext fun z ↦ by simp [imCoord]
  simp only [coords, hre, him, map_neg]

/-! ### The metric and the topological group structure -/

/-- The metric of `G_s` is that of its coordinates in `H^s(ℂ) × H^s(ℂ)`. -/
instance : MetricSpace (SobolevGauge hs) :=
  MetricSpace.induced coords coords_injective inferInstance

/-- The distance of two gauges is the distance of their coordinates. -/
theorem dist_eq (u v : SobolevGauge hs) : dist u v = dist (coords u) (coords v) :=
  rfl

/-- The coordinates are an isometric embedding of `G_s` into `H^s(ℂ) × H^s(ℂ)`. -/
theorem isometry_coords : Isometry (coords (hs := hs)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

theorem continuous_coords : Continuous (coords (hs := hs)) :=
  isometry_coords.continuous

/-- **`G_s` is a topological group**: in coordinates its multiplication and inversion are
polynomial maps for the continuous product of `H^s(ℂ)`. -/
instance : IsTopologicalGroup (SobolevGauge hs) where
  continuous_mul := by
    have hM := (mulCLM (finrank_real_complex_lt_two_mul hs)).continuous₂
    have hc₁ := continuous_coords.comp (continuous_fst (X := SobolevGauge hs)
      (Y := SobolevGauge hs))
    have hc₂ := continuous_coords.comp (continuous_snd (X := SobolevGauge hs)
      (Y := SobolevGauge hs))
    refine isometry_coords.isEmbedding.isInducing.continuous_iff.2 ?_
    simp only [Function.comp_def, coords_mul]
    refine Continuous.prodMk ?_ ?_
    · exact (((continuous_fst.comp hc₁).add (continuous_fst.comp hc₂)).add
        (hM.comp ((continuous_fst.comp hc₁).prodMk (continuous_fst.comp hc₂)))).sub
        (hM.comp ((continuous_snd.comp hc₁).prodMk (continuous_snd.comp hc₂)))
    · exact (((continuous_snd.comp hc₁).add (continuous_snd.comp hc₂)).add
        (hM.comp ((continuous_fst.comp hc₁).prodMk (continuous_snd.comp hc₂)))).add
        (hM.comp ((continuous_snd.comp hc₁).prodMk (continuous_fst.comp hc₂)))
  continuous_inv := by
    refine isometry_coords.isEmbedding.isInducing.continuous_iff.2 ?_
    simp only [Function.comp_def, coords_inv]
    exact (continuous_fst.comp continuous_coords).prodMk
      (continuous_snd.comp continuous_coords).neg

/-! ### Completeness -/

/-- In the limit of a sequence of gauges, the `H^s` limit of a coordinate is its limit almost
everywhere. -/
private theorem ae_tendsto_of_tendsto (hs' : (finrank ℝ ℂ : ℝ) < 2 * s) (hs0 : 0 ≤ s)
    (u : ℕ → SobolevGauge hs) (f : SobolevGauge hs → ℂ → ℂ) (c : SobolevGauge hs → H^{s}(ℂ))
    (hmem : ∀ v, MemLp (f v) 2 volume)
    (hc : ∀ v, (c v).toDistr = ((hmem v).toLp _ : Lp ℂ 2 (volume : Measure ℂ)))
    {a : H^{s}(ℂ)} (ha : Tendsto (fun n ↦ c (u n)) atTop (𝓝 a)) :
    ∀ᵐ z ∂volume, Tendsto (fun n ↦ f (u n) z) atTop (𝓝 ((inclusion hs0 a).toLp z)) := by
  have hR (n : ℕ) : MemSobolev s 2 (((hmem (u n)).toLp _ : Lp ℂ 2 (volume : Measure ℂ)) :
      𝓢'(ℂ, ℂ)) := hc (u n) ▸ (c (u n)).memSobolev_toDistr
  have hA : MemSobolev s 2 ((inclusion hs0 a).toLp : 𝓢'(ℂ, ℂ)) :=
    toDistr_eq_toLp_inclusion hs0 a ▸ a.memSobolev_toDistr
  have hconv : Tendsto (fun n ↦ (hR n).toBesselPotentialSpace) atTop
      (𝓝 hA.toBesselPotentialSpace) := by
    have e₁ (n : ℕ) : (hR n).toBesselPotentialSpace = c (u n) :=
      BesselPotentialSpace.ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, hc])
    have e₂ : hA.toBesselPotentialSpace = a :=
      BesselPotentialSpace.ext
        (by rw [MemSobolev.toBesselPotentialSpace_toDistr, ← toDistr_eq_toLp_inclusion])
    simpa only [e₁, e₂] using ha
  filter_upwards [ae_tendsto_of_tendsto_toBesselPotentialSpace hs' hR hA hconv,
    ae_all_iff.2 fun n ↦ (hmem (u n)).coeFn_toLp] with z hz hz'
  exact hz.congr fun n ↦ hz' n

/-- A pair `(a, b) ∈ H^s(ℂ) × H^s(ℂ)` whose `L²` functions `A`, `B` are real almost everywhere,
with `|1 + A + i B| = 1` almost everywhere, is the pair of coordinates of a gauge: by the Sobolev
embedding `A` and `B` have continuous representatives, and `1 + A + i B` is then a gauge. -/
private theorem mem_range_coords_of_ae (hs0 : 0 ≤ s) {a b : H^{s}(ℂ)}
    (h : ∀ᵐ z ∂volume, ((inclusion hs0 a).toLp z).im = 0 ∧ ((inclusion hs0 b).toLp z).im = 0 ∧
      ‖1 + (inclusion hs0 a).toLp z + I * (inclusion hs0 b).toLp z‖ = 1) :
    (a, b) ∈ Set.range (coords (hs := hs)) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  set A := (inclusion hs0 a).toLp
  set B := (inclusion hs0 b).toLp
  have hAs : MemSobolev s 2 (A : 𝓢'(ℂ, ℂ)) :=
    toDistr_eq_toLp_inclusion hs0 a ▸ a.memSobolev_toDistr
  have hBs : MemSobolev s 2 (B : 𝓢'(ℂ, ℂ)) :=
    toDistr_eq_toLp_inclusion hs0 b ▸ b.memSobolev_toDistr
  obtain ⟨gA, hgA⟩ := hAs.exists_zeroAtInftyContinuousMap_ae_eq hs'
  obtain ⟨gB, hgB⟩ := hBs.exists_zeroAtInftyContinuousMap_ae_eq hs'
  have hgAc : Continuous fun z ↦ gA z := gA.continuous
  have hgBc : Continuous fun z ↦ gB z := gB.continuous
  -- The almost everywhere identities hold everywhere for the continuous representatives.
  have key : ∀ᵐ z ∂volume, (gA z).im = 0 ∧ (gB z).im = 0 ∧ ‖1 + gA z + I * gB z‖ = 1 := by
    filter_upwards [h, hgA, hgB] with z hz hzA hzB
    rwa [← hzA, ← hzB]
  have himA : ∀ z, (gA z).im = 0 := congrFun (((continuous_im.comp hgAc).ae_eq_iff_eq volume
    continuous_const).1 (key.mono fun z h ↦ h.1))
  have himB : ∀ z, (gB z).im = 0 := congrFun (((continuous_im.comp hgBc).ae_eq_iff_eq volume
    continuous_const).1 (key.mono fun z h ↦ h.2.1))
  have hnorm : ∀ z, ‖1 + gA z + I * gB z‖ = 1 := congrFun (((continuous_norm.comp
    ((continuous_const.add hgAc).add (continuous_const.mul hgBc))).ae_eq_iff_eq volume
      continuous_const).1 (key.mono fun z h ↦ h.2.2))
  -- The gauge `w = 1 + gA + i gB`.
  set w : ℂ → Circle := fun z ↦ ⟨1 + gA z + I * gB z, mem_sphere_zero_iff_norm.2 (hnorm z)⟩
  have hwre (z : ℂ) : (w z : ℂ).re - 1 = (gA z).re := by simp [w, himB z]
  have hwim (z : ℂ) : (w z : ℂ).im = (gB z).re := by simp [w, himA z]
  have hAre : A =ᵐ[volume] fun z ↦ (((gA z).re : ℝ) : ℂ) := hgA.mono fun z hz ↦ by
    rw [hz]
    exact Complex.ext (by simp) (by simp [himA z])
  have hBre : B =ᵐ[volume] fun z ↦ (((gB z).re : ℝ) : ℂ) := hgB.mono fun z hz ↦ by
    rw [hz]
    exact Complex.ext (by simp) (by simp [himB z])
  have hwmem : w ∈ sobolevGaugeGroup hs := by
    refine (mem_sobolevGaugeGroup hs w).2 ⟨continuous_induced_rng.2
      ((continuous_const.add hgAc).add (continuous_const.mul hgBc)), ?_, ?_⟩
    · simp only [hwre]
      exact mem_realSobolevFunctions_of_ae_eq_ofReal hAs hAre
    · simp only [hwim]
      exact mem_realSobolevFunctions_of_ae_eq_ofReal hBs hBre
  refine ⟨(toSubgroup hs).symm ⟨w, hwmem⟩,
    Prod.ext (BesselPotentialSpace.ext ?_) (BesselPotentialSpace.ext ?_)⟩
  · rw [toDistr_coords_fst _ (w := A) (hAre.trans (.of_forall fun z ↦ by simp [hwre]))]
    exact (toDistr_eq_toLp_inclusion hs0 a).symm
  · rw [toDistr_coords_snd _ (w := B) (hBre.trans (.of_forall fun z ↦ by simp [hwim]))]
    exact (toDistr_eq_toLp_inclusion hs0 b).symm

/-- **The image of the coordinates is closed.** A limit in `H^s(ℂ) × H^s(ℂ)` of coordinates of
gauges is the pair of coordinates of a gauge. -/
theorem isClosed_range_coords : IsClosed (Set.range (coords (hs := hs))) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have hs0 : (0 : ℝ) ≤ s := by linarith [(finrank ℝ ℂ).cast_nonneg (α := ℝ)]
  refine IsSeqClosed.isClosed fun {x} {p} hx hlim ↦ ?_
  choose u hu using hx
  obtain ⟨a, b⟩ := p
  have hlim' : Tendsto (fun n ↦ coords (u n)) atTop (𝓝 (a, b)) := by simpa only [hu] using hlim
  -- Convergence in `H^s` gives convergence almost everywhere of the complexified coordinates.
  have hmre := memLp_ofReal_re_sub_one (hs := hs)
  have hmim := memLp_ofReal_im (hs := hs)
  have hA := ae_tendsto_of_tendsto hs' hs0 u _ (fun v ↦ (coords v).1) hmre
    (fun v ↦ toDistr_coords_fst v (hmre v).coeFn_toLp) ((continuous_fst.tendsto _).comp hlim')
  have hB := ae_tendsto_of_tendsto hs' hs0 u _ (fun v ↦ (coords v).2) hmim
    (fun v ↦ toDistr_coords_snd v (hmim v).coeFn_toLp) ((continuous_snd.tendsto _).comp hlim')
  refine mem_range_coords_of_ae hs0 ?_
  filter_upwards [hA, hB] with z hz₁ hz₂
  refine ⟨tendsto_nhds_unique ((continuous_im.tendsto _).comp hz₁) ?_,
    tendsto_nhds_unique ((continuous_im.tendsto _).comp hz₂) ?_,
    tendsto_nhds_unique ((continuous_norm.tendsto _).comp
      ((tendsto_const_nhds.add hz₁).add (tendsto_const_nhds.mul hz₂))) ?_⟩
  · simp [Function.comp_def]
  · simp [Function.comp_def]
  · refine tendsto_const_nhds.congr fun n ↦ ?_
    have h : (1 : ℂ) + (((u n z : ℂ).re - 1 : ℝ) : ℂ) + I * (((u n z : ℂ).im : ℝ) : ℂ) =
        u n z := by
      apply Complex.ext <;> simp
    simp only [Function.comp_apply, h, Circle.norm_coe]

/-- **`G_s` is complete** in its `H^s` metric. -/
instance : CompleteSpace (SobolevGauge hs) :=
  (completeSpace_iff_isComplete_range isometry_coords.isUniformInducing).2
    isClosed_range_coords.isComplete

/-! ### Neighbourhoods of the identity -/

/-- The complex function `u - 1` of a gauge, represented in `H^s(ℂ; ℂ)`, is `a + i b` for the
coordinates `(a, b)` of `u`. -/
theorem toBesselPotentialSpace_eq_coords (u : SobolevGauge hs)
    {h : Lp ℂ 2 (volume : Measure ℂ)} (hhu : h =ᵐ[volume] fun z ↦ (u z : ℂ) - 1)
    (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) :
    hh.toBesselPotentialSpace = (coords u).1 + I • (coords u).2 := by
  have hmre := memLp_ofReal_re_sub_one u
  have hmim := memLp_ofReal_im u
  refine BesselPotentialSpace.ext ?_
  rw [MemSobolev.toBesselPotentialSpace_toDistr, toDistr_add, toDistr_smul,
    toDistr_coords_fst u hmre.coeFn_toLp, toDistr_coords_snd u hmim.coeFn_toLp,
    ← Lp.toTemperedDistribution_smul, ← Lp.toTemperedDistribution_add]
  congr 1
  refine Lp.ext ?_
  filter_upwards [hhu, Lp.coeFn_add (hmre.toLp _) (I • hmim.toLp _),
    Lp.coeFn_smul I (hmim.toLp _), hmre.coeFn_toLp, hmim.coeFn_toLp] with z h₀ h₁ h₂ h₃ h₄
  rw [h₀, h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, h₄, smul_eq_mul]
  apply Complex.ext <;> simp

/-- **Exponentials form a neighbourhood of the identity.** The gauges `exp (i f)`, for continuous
real phases `f ∈ H^s(ℂ)`, form a neighbourhood of `1` in `G_s`. -/
theorem setOf_exists_eq_exp_mem_nhds_one :
    {u : SobolevGauge hs | ∃ f : ℂ → ℝ, Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2 ∧
      ⇑u = fun z ↦ Circle.exp (f z)} ∈ 𝓝 1 := by
  obtain ⟨δ, hδ, hexp⟩ := exists_continuous_mem_realSobolevFunctions_eq_exp hs
  refine Metric.mem_nhds_iff.2 ⟨δ / 2, by positivity, fun u hu ↦ ?_⟩
  rw [Metric.mem_ball, dist_eq, coords_one, dist_zero_right] at hu
  obtain ⟨h, hhu, hh⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup u.coe_mem
  refine hexp u u.coe_mem hhu hh ?_
  rw [toBesselPotentialSpace_eq_coords u hhu hh]
  calc ‖(coords u).1 + I • (coords u).2‖ ≤ ‖(coords u).1‖ + ‖(coords u).2‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 2 * ‖coords u‖ := by
        linarith [norm_fst_le (coords u), norm_snd_le (coords u)]
    _ < δ := by linarith

end SobolevGauge

end TauCeti.Vortex
