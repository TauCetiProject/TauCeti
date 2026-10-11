/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic

/-!
# The action functional of two exact graphs and the energy of holomorphic strips

In the linear cotangent space `V × V'` (with `V'` the continuous dual), the graph of the
differential of a function `h : V → ℝ` is an exact Lagrangian: the Liouville form
`λ_(q,p)(δq, δp) = p(δq)` restricts on it to `d(h ∘ π)`. For two such graphs
`L₀ = graph dh₀` and `L₁ = graph dh₁`, the **action** of a path `γ : [0, 1] → V × V'` from `L₀`
to `L₁` is

`A(γ) = ∫₀¹ γ^*λ + h₀(π γ(0)) - h₁(π γ(1))`

(`TauCeti.cotangentAction`). A point `x ∈ L₀ ∩ L₁` lies over a critical point of `h₁ - h₀`,
and the constant path at `x` has action `h₀(π x) - h₁(π x)` (`TauCeti.cotangentAction_const`).
The paths `t ↦ u(s, t)` of a strip `u : ℝ × [0, 1] → V × V'` with `u(s, 0) ∈ L₀` and
`u(s, 1) ∈ L₁` are paths from `L₀` to `L₁`.

The main result is that the symplectic area of such a strip over `[a, b] × [0, 1]` is the drop of
the action between the two ends
(`TauCeti.integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub`), with the
convention `ω = -dλ` of `TauCeti.strongDualCotangentSymplecticForm`. This is Green's formula
(`ContinuousLinearMap.integral_bilinear_fderiv_sub_prod_Icc`) for `u^*λ`: the boundary integrals
along the two vertical sides are the action integrals, and those along the horizontal sides
integrate the exact restrictions of `λ` to `L₀` and `L₁`
(`TauCeti.integral_cotangentLiouvilleForm_differential_graph`).

For a strip that is holomorphic for an almost complex structure `J` tamed by `ω`, the normalized
energy density is the area density, so the energy of the strip over `[a, b] × [0, 1]` equals the
action drop (`TauCeti.stdComplexLineEnergy_eq_cotangentAction_sub`), the action decreases along
the strip (`TauCeti.cotangentAction_le_cotangentAction`), and a strip whose actions converge at
both ends has energy equal to the difference of the limits
(`TauCeti.stdComplexLineEnergy_eq_of_tendsto_cotangentAction`). The theorem is stated for the
limits of the actions. When the paths `t ↦ u(s, t)` converge uniformly to constant paths at
intersection points `x₋` and `x₊`, the base components of their `t`-derivatives converge
uniformly to zero, and `h₀`, `h₁` are continuous at `π x₋` and `π x₊`,
`TauCeti.tendsto_cotangentAction_of_tendstoUniformlyOn` computes those limits as the critical
values `A(x₋)` and `A(x₊)`. Thus `TauCeti.stdComplexLineEnergy_eq_of_tendstoUniformlyOn` gives the
energy identity of Lagrangian Floer theory for exact Lagrangians,
`E(u) = A(x₋) - A(x₊)`, which bounds the energy of every such strip connecting two given
intersection points.

## Main declarations

* `TauCeti.cotangentAction`: the action of a path from `graph dh₀` to `graph dh₁`.
* `TauCeti.integral_cotangentLiouvilleForm_differential_graph`: along a path in `graph dh`, the
  Liouville form integrates to the change of `h`.
* `TauCeti.integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub`: the symplectic
  area of a strip with boundary on the two graphs is the drop of its action.
* `TauCeti.stdComplexLineEnergy_eq_cotangentAction_sub`: the energy identity for holomorphic
  strips over a rectangle.
* `TauCeti.stdComplexLineEnergy_eq_of_tendsto_cotangentAction`: the energy identity for a whole
  holomorphic strip.
* `TauCeti.tendsto_cotangentAction_of_tendstoUniformlyOn`: uniform convergence to a constant
  path, with the base components of the derivatives tending uniformly to zero, gives convergence
  of the action to the value at that point.
* `TauCeti.stdComplexLineEnergy_eq_of_tendstoUniformlyOn`: the whole-strip energy identity with
  the asymptotic action values computed from the limiting points.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  §2 (the action functional of a pair of exact Lagrangians and the energy of connecting strips).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.2 (the energy identity `E(u) = ∫ u^*ω` for
  holomorphic curves).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Filter Topology
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The **action** of a path `γ` in the linear cotangent space `V × V'` from the graph of `dh₀`
to the graph of `dh₁`: the integral over `[0, 1]` of the pullback of the Liouville form, plus
`h₀` at the projection of the starting point, minus `h₁` at the projection of the endpoint. -/
def cotangentAction (h₀ h₁ : V → ℝ) (γ : ℝ → V × StrongDual ℝ V) : ℝ :=
  (∫ t in (0 : ℝ)..1, cotangentLiouvilleForm (γ t) (fun _ ↦ deriv γ t)) + h₀ (γ 0).1 - h₁ (γ 1).1

/-- The action written out: the Liouville integrand pairs the covector of the path with the
derivative of its base point. -/
lemma cotangentAction_def (h₀ h₁ : V → ℝ) (γ : ℝ → V × StrongDual ℝ V) :
    cotangentAction h₀ h₁ γ =
      (∫ t in (0 : ℝ)..1, (γ t).2 (deriv γ t).1) + h₀ (γ 0).1 - h₁ (γ 1).1 := by
  simp [cotangentAction]

/-- The action of a constant path is `h₀ - h₁` at its base point. For a point of the intersection
of the two graphs, this is the action of the corresponding generator of the Floer complex. -/
@[simp]
lemma cotangentAction_const (h₀ h₁ : V → ℝ) (x : V × StrongDual ℝ V) :
    cotangentAction h₀ h₁ (fun _ ↦ x) = h₀ x.1 - h₁ x.1 := by
  simp [cotangentAction_def]

/-- **The action converges to its value on a limiting constant path.** Suppose paths in the
linear cotangent space converge uniformly on `[0, 1]` to the constant path at `x`, and the base
components of their derivatives converge uniformly to zero on `(0, 1]`. If the endpoint
potentials are continuous at the base point of `x`, then their actions converge to
`h₀ x.1 - h₁ x.1`. -/
theorem tendsto_cotangentAction_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {γ : ι → ℝ → V × StrongDual ℝ V} {x : V × StrongDual ℝ V} {h₀ h₁ : V → ℝ}
    (hγ : TendstoUniformlyOn γ (fun _ ↦ x) l (uIcc 0 1))
    (hγ' : TendstoUniformlyOn (fun i t ↦ (deriv (γ i) t).1) 0 l (uIoc 0 1))
    (hh₀ : ContinuousAt h₀ x.1) (hh₁ : ContinuousAt h₁ x.1) :
    Tendsto (fun i ↦ cotangentAction h₀ h₁ (γ i)) l (𝓝 (h₀ x.1 - h₁ x.1)) := by
  have hbound : ∀ᶠ i in l, ∀ t ∈ uIcc (0 : ℝ) 1, ‖(γ i t).2‖ < ‖x.2‖ + 1 := by
    have hnear :=
      (Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity.mp hγ) 1 zero_lt_one
    filter_upwards [hnear] with i hi
    intro t ht
    have hsnd : dist x.2 (γ i t).2 < 1 := by
      exact lt_of_le_of_lt (le_max_right _ _) (by simpa only [Prod.dist_eq] using hi t ht)
    calc
      ‖(γ i t).2‖ ≤ ‖x.2‖ + ‖(γ i t).2 - x.2‖ := norm_le_norm_add_norm_sub' _ _
      _ < ‖x.2‖ + 1 := by
        simpa only [dist_eq_norm, norm_sub_rev, add_comm] using add_lt_add_left hsnd ‖x.2‖
  have hint : Tendsto
      (fun i ↦ ∫ t in (0 : ℝ)..1, (γ i t).2 (deriv (γ i) t).1) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hderiv := (SeminormedAddGroup.tendstoUniformlyOn_zero.mp hγ')
      (ε / (2 * (‖x.2‖ + 1))) (by positivity)
    filter_upwards [hbound, hderiv] with i hi hi'
    have hpoint : ∀ t ∈ uIoc (0 : ℝ) 1,
        ‖(γ i t).2 (deriv (γ i) t).1‖ ≤ ε / 2 := by
      intro t ht
      have ht' : t ∈ uIcc (0 : ℝ) 1 := uIoc_subset_uIcc ht
      calc
        ‖(γ i t).2 (deriv (γ i) t).1‖ ≤ ‖(γ i t).2‖ * ‖(deriv (γ i) t).1‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖x.2‖ + 1) * (ε / (2 * (‖x.2‖ + 1))) := by
          gcongr
          · exact (hi t ht').le
          · exact (hi' t ht).le
        _ = ε / 2 := by field_simp
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 0), sub_zero, mul_one] at hnorm
    simpa only [dist_zero_right] using hnorm.trans_lt (half_lt_self hε)
  have hzero : (0 : ℝ) ∈ uIcc 0 1 := by simp
  have hone : (1 : ℝ) ∈ uIcc 0 1 := by simp
  have hstart : Tendsto (fun i ↦ h₀ (γ i 0).1) l (𝓝 (h₀ x.1)) :=
    hh₀.tendsto.comp (continuousAt_fst.tendsto.comp (hγ.tendsto_at hzero))
  have hend : Tendsto (fun i ↦ h₁ (γ i 1).1) l (𝓝 (h₁ x.1)) :=
    hh₁.tendsto.comp (continuousAt_fst.tendsto.comp (hγ.tendsto_at hone))
  simpa only [cotangentAction_def, zero_add] using hint.add hstart |>.sub hend

/-- **The Liouville form is exact on the graph of a differential.** Along a `C¹` path `σ` lying
over `[a, b]` in the graph of `dh`, the integral of the Liouville form is the change of `h` between
the projections of the endpoints. -/
theorem integral_cotangentLiouvilleForm_differential_graph {σ σ' : ℝ → V × StrongDual ℝ V}
    {h : V → ℝ} {a b : ℝ} (hσ : ∀ s ∈ [[a, b]], HasDerivAt σ (σ' s) s)
    (hσ' : ContinuousOn σ' [[a, b]]) (hh : ∀ s ∈ [[a, b]], DifferentiableAt ℝ h (σ s).1)
    (hgraph : ∀ s ∈ [[a, b]], (σ s).2 = fderiv ℝ h (σ s).1) :
    ∫ s in a..b, cotangentLiouvilleForm (σ s) (fun _ ↦ σ' s) = h (σ b).1 - h (σ a).1 := by
  simp only [cotangentLiouvilleForm_apply]
  have hσc : ContinuousOn σ [[a, b]] := fun s hs ↦ (hσ s hs).continuousAt.continuousWithinAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s ↦ h (σ s).1) (fun s hs ↦ ?_)
    ((hσc.snd.clm_apply hσ'.fst).intervalIntegrable)
  rw [hgraph s hs]
  have hfst : HasDerivAt (fun s ↦ (σ s).1) (σ' s).1 s :=
    (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)).hasFDerivAt.comp_hasDerivAt s (hσ s hs)
  exact (hh s hs).hasFDerivAt.comp_hasDerivAt s hfst

variable {u : ℝ × ℝ → V × StrongDual ℝ V} {h₀ h₁ : V → ℝ} {a b : ℝ}

/-- **The symplectic area of a strip is the drop of its action.** Let `u` be `C²` near the
rectangle `[a, b] × [0, 1]`, with its bottom side `t = 0` in the graph of `dh₀` and its top side
`t = 1` in the graph of `dh₁`. Then the integral of `ω(∂s u, ∂t u)` over the rectangle is the
action of the path `t ↦ u(a, t)` minus that of `t ↦ u(b, t)`. -/
theorem integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub (hab : a ≤ b)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) :
    ∫ z in Icc a b ×ˢ Icc 0 1, strongDualCotangentSymplecticForm
        (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      cotangentAction h₀ h₁ (fun t ↦ u (a, t)) - cotangentAction h₀ h₁ (fun t ↦ u (b, t)) := by
  -- the Liouville form as a continuous bilinear map, `B x v = λ_x(v)`
  let B : (V × StrongDual ℝ V) →L[ℝ] (V × StrongDual ℝ V) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ (V × StrongDual ℝ V) V ℝ).flip
      (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))).comp
      (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))
  have hB : ∀ x v, B x v = cotangentLiouvilleForm x (fun _ ↦ v) := fun x v ↦ by simp [B]
  have hdiff : ∀ z ∈ Icc a b ×ˢ Icc 0 1, DifferentiableAt ℝ u z := fun z hz ↦
    (hu z hz).differentiableAt (by norm_num)
  -- `stdComplexLineReal` and `stdComplexLineImag` are by definition `(1, 0)` and `(0, 1)`
  have hre : ((1, 0) : ℝ × ℝ) = stdComplexLineReal := rfl
  have him : ((0, 1) : ℝ × ℝ) = stdComplexLineImag := rfl
  have hab' : [[a, b]] = Icc a b := uIcc_of_le hab
  have h01 : [[(0 : ℝ), 1]] = Icc 0 1 := uIcc_of_le zero_le_one
  -- the two vertical sides carry the action integrals
  have hvert : ∀ s ∈ Icc a b,
      ∫ t in (0 : ℝ)..1, B (u (s, t)) (fderiv ℝ u (s, t) stdComplexLineImag) =
        ∫ t in (0 : ℝ)..1,
          cotangentLiouvilleForm (u (s, t)) (fun _ ↦ deriv (fun t ↦ u (s, t)) t) :=
    fun s hs ↦ intervalIntegral.integral_congr fun t ht ↦ by
      have hv : HasDerivAt (fun t ↦ ((s, t) : ℝ × ℝ)) stdComplexLineImag t := by
        rw [← him]
        exact (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      have hd : HasDerivAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, t) stdComplexLineImag) t :=
        (hdiff (s, t) ⟨hs, h01 ▸ ht⟩).hasFDerivAt.comp_hasDerivAt t hv
      rw [hB, hd.deriv]
  -- the two horizontal sides lie in the graphs, where the Liouville form is exact
  have hhor : ∀ {h : V → ℝ} {c : ℝ}, c ∈ Icc (0 : ℝ) 1 →
      (∀ s ∈ Icc a b, DifferentiableAt ℝ h (u (s, c)).1) →
      (∀ s ∈ Icc a b, (u (s, c)).2 = fderiv ℝ h (u (s, c)).1) →
      ∫ s in a..b, B (u (s, c)) (fderiv ℝ u (s, c) stdComplexLineReal) =
        h (u (b, c)).1 - h (u (a, c)).1 := by
    intro h c hc hh hgraph
    simp only [hB]
    refine integral_cotangentLiouvilleForm_differential_graph
      (σ := fun s ↦ u (s, c)) (σ' := fun s ↦ fderiv ℝ u (s, c) stdComplexLineReal)
      (fun s hs ↦ ?_) (fun s hs ↦ ?_) (fun s hs ↦ hh s (hab' ▸ hs))
      (fun s hs ↦ hgraph s (hab' ▸ hs))
    · have hv : HasDerivAt (fun s ↦ ((s, c) : ℝ × ℝ)) stdComplexLineReal s := by
        rw [← hre]
        exact (hasDerivAt_id s).prodMk (hasDerivAt_const s c)
      exact (hdiff _ ⟨hab' ▸ hs, hc⟩).hasFDerivAt.comp_hasDerivAt s hv
    · exact ((((hu _ ⟨hab' ▸ hs, hc⟩).continuousAt_fderiv (by norm_num)).comp
        (continuous_id.prodMk continuous_const).continuousAt).clm_apply
          continuousAt_const).continuousWithinAt
  have hgreen := B.integral_bilinear_fderiv_sub_prod_Icc (a := (a, 0)) (b := (b, 1))
    ⟨hab, zero_le_one⟩ (by rw [← Icc_prod_Icc]; exact hu)
  rw [← Icc_prod_Icc, hre, him] at hgreen
  have hω : ∀ z, strongDualCotangentSymplecticForm (fderiv ℝ u z stdComplexLineReal)
      (fderiv ℝ u z stdComplexLineImag) =
        -(B (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) -
          B (fderiv ℝ u z stdComplexLineImag) (fderiv ℝ u z stdComplexLineReal)) := fun z ↦ by
    simp [B]
  simp only [hω, integral_neg, hgreen, hvert a ⟨le_rfl, hab⟩, hvert b ⟨hab, le_rfl⟩,
    hhor ⟨zero_le_one, le_rfl⟩ hh₁ hu₁, hhor ⟨le_rfl, zero_le_one⟩ hh₀ hu₀, cotangentAction]
  ring

variable {J : AlmostComplexStructure (V × StrongDual ℝ V)}

/-- **The energy identity for a holomorphic strip over a rectangle.** Let `u` be `C²` near
`[a, b] × [0, 1]` and holomorphic there for an almost complex structure `J` tamed by `ω`, with its
bottom side in the graph of `dh₀` and its top side in the graph of `dh₁`. Then the energy of `u`
over the rectangle is the action of `t ↦ u(a, t)` minus that of `t ↦ u(b, t)`. -/
theorem stdComplexLineEnergy_eq_cotangentAction_sub
    (hω : strongDualCotangentSymplecticForm.Tames J) (hab : a ≤ b)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J u z)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) :
    strongDualCotangentSymplecticForm.stdComplexLineEnergy J
        (fun z ↦ (fderiv ℝ u z).toLinearMap) (volume.restrict (Icc a b ×ˢ Icc 0 1)) =
      ENNReal.ofReal
        (cotangentAction h₀ h₁ (fun t ↦ u (a, t)) - cotangentAction h₀ h₁ (fun t ↦ u (b, t))) := by
  have hR : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hnn : ∀ z ∈ Icc a b ×ˢ Icc 0 1, 0 ≤ strongDualCotangentSymplecticForm
      (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := fun z hz ↦ by
    simpa using IsComplexLinearMap.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg
      (hJ z hz).fderiv_isComplexLinear hω
  have hcont : ContinuousOn (fun z ↦ strongDualCotangentSymplecticForm
      (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      (Icc a b ×ˢ Icc 0 1) := fun z hz ↦ by
    have hdu := (hu z hz).continuousAt_fderiv (by norm_num)
    simp only [strongDualCotangentSymplecticForm_apply]
    exact ((((hdu.clm_apply continuousAt_const).snd).clm_apply
      (hdu.clm_apply continuousAt_const).fst).sub
      (((hdu.clm_apply continuousAt_const).snd).clm_apply
        (hdu.clm_apply continuousAt_const).fst)).continuousWithinAt
  rw [SymplecticForm.fderiv_stdComplexLineEnergy_eq_lintegral_symplecticForm
      (ae_restrict_of_forall_mem hR hJ),
    ← integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub hab hu hh₀ hh₁ hu₀ hu₁,
    ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      (ae_restrict_of_forall_mem hR hnn)]

/-- **The action decreases along a holomorphic strip.** Under the hypotheses of
`TauCeti.stdComplexLineEnergy_eq_cotangentAction_sub`, the action of `t ↦ u(b, t)` is at most
that of `t ↦ u(a, t)`. -/
theorem cotangentAction_le_cotangentAction
    (hω : strongDualCotangentSymplecticForm.Tames J) (hab : a ≤ b)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J u z)
    (hh₀ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s ∈ Icc a b, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s ∈ Icc a b, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s ∈ Icc a b, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) :
    cotangentAction h₀ h₁ (fun t ↦ u (b, t)) ≤ cotangentAction h₀ h₁ (fun t ↦ u (a, t)) := by
  have h := integral_strongDualCotangentSymplecticForm_eq_cotangentAction_sub hab hu hh₀ hh₁ hu₀ hu₁
  have hnn : ∀ z ∈ Icc a b ×ˢ Icc 0 1, 0 ≤ strongDualCotangentSymplecticForm
      (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := fun z hz ↦ by
    simpa using IsComplexLinearMap.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg
      (hJ z hz).fderiv_isComplexLinear hω
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc) hnn
  linarith

/-- **The energy identity for a holomorphic strip.** Let `u` be `C²` near the closed strip
`ℝ × [0, 1]` and holomorphic there for an almost complex structure `J` tamed by `ω`, with
`u(s, 0)` in the graph of `dh₀` and `u(s, 1)` in the graph of `dh₁`. If the actions of the paths
`t ↦ u(s, t)` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`, then the energy of `u` is
`A₁ - A₂`. If the paths `t ↦ u(s, t)` converge as `s → ∓∞` to the constant paths at
intersection points `x₋` and `x₊`, uniformly together with their `t`-derivatives, and `h₀` and
`h₁` are continuous at `π x₋` and `π x₊`, then `A₁` and `A₂` are the critical values
`h₀(π x₋) - h₁(π x₋)` and `h₀(π x₊) - h₁(π x₊)` of the action; this theorem assumes only the
convergence of the actions. -/
theorem stdComplexLineEnergy_eq_of_tendsto_cotangentAction
    (hω : strongDualCotangentSymplecticForm.Tames J)
    (hu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J u z)
    (hh₀ : ∀ s, DifferentiableAt ℝ h₀ (u (s, 0)).1) (hh₁ : ∀ s, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1) {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ cotangentAction h₀ h₁ (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ cotangentAction h₀ h₁ (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    strongDualCotangentSymplecticForm.stdComplexLineEnergy J
        (fun z ↦ (fderiv ℝ u z).toLinearMap) (volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)) =
      ENNReal.ofReal (A₁ - A₂) := by
  -- exhaust the strip by the rectangles `[-n, n] × [0, 1]`
  set R : ℕ → Set (ℝ × ℝ) := fun n ↦ Icc (-(n : ℝ)) n ×ˢ Icc 0 1
  have hRsub : ∀ n, R n ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 := fun n ↦ prod_mono (subset_univ _) le_rfl
  have hmono : Monotone R := fun m n hmn ↦ prod_mono
    (Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)) le_rfl
  have hunion : ⋃ n, R n = (univ : Set ℝ) ×ˢ Icc 0 1 := by
    refine (iUnion_subset hRsub).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |z.1|
    exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hn, hz.2⟩⟩
  have hE : ∀ n, strongDualCotangentSymplecticForm.stdComplexLineEnergy J
      (fun z ↦ (fderiv ℝ u z).toLinearMap) (volume.restrict (R n)) =
      ENNReal.ofReal (cotangentAction h₀ h₁ (fun t ↦ u (-(n : ℝ), t)) -
        cotangentAction h₀ h₁ (fun t ↦ u (n, t))) := fun n ↦
    stdComplexLineEnergy_eq_cotangentAction_sub hω (neg_le_self n.cast_nonneg)
      (fun z hz ↦ hu z (hRsub n hz)) (fun z hz ↦ hJ z (hRsub n hz)) (fun s _ ↦ hh₀ s)
      (fun s _ ↦ hh₁ s) (fun s _ ↦ hu₀ s) (fun s _ ↦ hu₁ s)
  -- the energies of the rectangles increase to the energy of the strip
  have hlim : Tendsto (fun n ↦ strongDualCotangentSymplecticForm.stdComplexLineEnergy J
      (fun z ↦ (fderiv ℝ u z).toLinearMap) (volume.restrict (R n))) atTop
      (𝓝 (strongDualCotangentSymplecticForm.stdComplexLineEnergy J
        (fun z ↦ (fderiv ℝ u z).toLinearMap) (volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)))) := by
    simp only [SymplecticForm.stdComplexLineEnergy_def, ← hunion]
    rw [setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono' (Measure.restrict_mono (hmono hmn)
      le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)).sub
      (htop.comp tendsto_natCast_atTop_atTop))

/-- **The energy of a holomorphic strip is the difference of its endpoint action values.**
Suppose a holomorphic strip with boundary on the exact graphs of `dh₀` and `dh₁` converges in the
path direction, uniformly to constant paths at `x₀` and `x₁` as the strip coordinate tends to
`-∞` and `+∞`, with the base components of its path derivatives tending uniformly to zero on
`(0, 1]`. Then its energy is the difference between `h₀ - h₁` at the base points of `x₀` and
`x₁`.

In Floer applications the boundary conditions and asymptotic convergence make `x₀` and `x₁`
intersection points of the two exact graphs. The statement needs only continuity of the two
potentials at their base points to identify the limiting actions. -/
theorem stdComplexLineEnergy_eq_of_tendstoUniformlyOn
    (hω : strongDualCotangentSymplecticForm.Tames J)
    (hu : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J u z)
    (hh₀ : ∀ s, DifferentiableAt ℝ h₀ (u (s, 0)).1)
    (hh₁ : ∀ s, DifferentiableAt ℝ h₁ (u (s, 1)).1)
    (hu₀ : ∀ s, (u (s, 0)).2 = fderiv ℝ h₀ (u (s, 0)).1)
    (hu₁ : ∀ s, (u (s, 1)).2 = fderiv ℝ h₁ (u (s, 1)).1)
    {x₀ x₁ : V × StrongDual ℝ V}
    (hbot : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ x₀) atBot (uIcc 0 1))
    (hbot' : TendstoUniformlyOn
      (fun s t ↦ (deriv (fun t ↦ u (s, t)) t).1) 0 atBot (uIoc 0 1))
    (htop : TendstoUniformlyOn (fun s t ↦ u (s, t)) (fun _ ↦ x₁) atTop (uIcc 0 1))
    (htop' : TendstoUniformlyOn
      (fun s t ↦ (deriv (fun t ↦ u (s, t)) t).1) 0 atTop (uIoc 0 1))
    (hh₀neg : ContinuousAt h₀ x₀.1) (hh₁neg : ContinuousAt h₁ x₀.1)
    (hh₀pos : ContinuousAt h₀ x₁.1) (hh₁pos : ContinuousAt h₁ x₁.1) :
    strongDualCotangentSymplecticForm.stdComplexLineEnergy J
        (fun z ↦ (fderiv ℝ u z).toLinearMap)
        (volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)) =
      ENNReal.ofReal ((h₀ x₀.1 - h₁ x₀.1) - (h₀ x₁.1 - h₁ x₁.1)) := by
  apply stdComplexLineEnergy_eq_of_tendsto_cotangentAction hω hu hJ hh₀ hh₁ hu₀ hu₁
  · exact tendsto_cotangentAction_of_tendstoUniformlyOn hbot hbot' hh₀neg hh₁neg
  · exact tendsto_cotangentAction_of_tendstoUniformlyOn htop htop' hh₀pos hh₁pos

end TauCeti
