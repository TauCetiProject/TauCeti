/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Divisor
public import TauCeti.Analysis.Complex.RiemannSurface.Ramification

/-!
# Pullback of meromorphic differentials

Pullback of a complex covector field is composition with the manifold derivative. In local
coordinates it sends `a(w) dw` to `a(f(z)) f'(z) dz`. Consequently, for a holomorphic map of
local multiplicity `e > 0`,

`ord_x(f*ω) = e * ord_(f x)(ω) + e - 1`.

On compact surfaces this gives the divisor identity
`div(f*ω) = f*(div ω) + R_f`, the canonical-divisor input to analytic Riemann–Hurwitz.
The local statements require neither compactness nor connectedness; the divisor identity
requires finite order of the target differential, since the divisor of the zero differential
does not obey that identity.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§9, 17: pullback of differentials
  and the ramification contribution to the canonical divisor.
* R. Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter IV §2: the local order
  formula for pullback of a meromorphic differential.
-/

public noncomputable section

open Filter Function IsManifold Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- Pullback of a complex covector field by a map, using its manifold derivative. -/
def pullback (ω : OneForm Y) (f : X → Y) : OneForm X :=
  fun x ↦ (ω (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x)

@[simp]
theorem pullback_apply (ω : OneForm Y) (f : X → Y) (x : X)
    (v : TangentSpace 𝓘(ℂ) x) :
    ω.pullback f x v = ω (f x) (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x v) := (rfl)

@[simp]
theorem pullback_id (ω : OneForm X) : ω.pullback id = ω := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [pullback_apply, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]

@[simp]
theorem pullback_zero (f : X → Y) : (0 : OneForm Y).pullback f = 0 := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp]
theorem pullback_add (ω η : OneForm Y) (f : X → Y) :
    (ω + η).pullback f = ω.pullback f + η.pullback f := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp]
theorem pullback_smul (a : Y → ℂ) (ω : OneForm Y) (f : X → Y) :
    (a • ω).pullback f = (a ∘ f) • ω.pullback f := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp]
theorem pullback_const_smul (c : ℂ) (ω : OneForm Y) (f : X → Y) :
    (c • ω).pullback f = c • ω.pullback f := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- Pullback reverses composition of differentiable maps. -/
theorem pullback_comp (ω : OneForm Z) {f : X → Y} {g : Y → Z}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    ω.pullback (g ∘ f) = (ω.pullback g).pullback f := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [pullback_apply, mfderiv_comp x (hg (f x)) (hf x),
    ContinuousLinearMap.comp_apply, comp_apply]

/-- Pullback of the differential of a function is the differential of its composite. -/
theorem pullback_mvfderiv {a : Y → ℂ} {f : X → Y}
    (ha : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    pullback (mvfderiv 𝓘(ℂ) a) f = mvfderiv 𝓘(ℂ) (a ∘ f) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [pullback_apply, mvfderiv_comp_apply x (ha (f x)) (hf x)]

/-- In source and target coordinates, pullback multiplies the pulled-back coefficient by the
complex derivative of the coordinate representative of the map. -/
theorem coeff_pullback (ω : OneForm Y) {f : X → Y} {x : X}
    {e : OpenPartialHomeomorph X ℂ} {d : OpenPartialHomeomorph Y ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hd : d ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ d.source)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    (ω.pullback f).coeff e (e x) =
      ω.coeff d (d (f x)) * deriv ((d ∘ f) ∘ e.symm) (e x) := by
  have hω := ω.coeff_smul_mvfderiv hd (d.map_source hfx)
  rw [d.left_inv hfx] at hω
  have hdf := mdifferentiableAt_of_mem_maximalAtlas hd hfx
  have hcoeff := coeff_mvfderiv he (e.map_source hx)
    (by simpa only [e.left_inv hx] using hdf.comp x hf)
  have hdc := (coeff_eq_iff (mvfderiv 𝓘(ℂ) (d ∘ f)) he hx).mp hcoeff
  rw [coeff_eq_iff _ he hx, mul_smul, hdc]
  apply ContinuousLinearMap.ext
  intro v
  rw [pullback_apply, ← hω]
  simp only [smul_apply, mvfderiv_comp_apply x hdf hf]

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- The local coefficient formula for pullback, as equality of germs in the preferred charts. -/
theorem coeff_pullback_eventuallyEq (ω : OneForm Y) {f : X → Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    (ω.pullback f).coeff (chartAt ℂ x) =ᶠ[𝓝 (chartAt ℂ x x)]
      (ω.coeff (chartAt ℂ (f x)) ∘
        ((chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm)) *
      deriv ((chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm) := by
  let e := chartAt ℂ x
  let d := chartAt ℂ (f x)
  have hfx : ∀ᶠ y in 𝓝 x, f y ∈ d.source :=
    hf.self_of_nhds.continuousAt.eventually (d.open_source.mem_nhds (mem_chart_source ℂ (f x)))
  have he := e.continuousAt_symm (e.map_source (mem_chart_source ℂ x))
  filter_upwards [e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x)),
    he.eventually (by simpa only [e.left_inv (mem_chart_source ℂ x)] using hf.and hfx)]
    with z hz hzf
  have h := coeff_pullback ω (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas (f x))
    (e.map_target hz) hzf.2 hzf.1
  simpa only [e, d, (chartAt ℂ x).right_inv hz, Pi.mul_apply, comp_apply] using h

/-- Pullback by a holomorphic map preserves meromorphy of a differential. -/
theorem MeromorphicAt.pullback {ω : OneForm Y} {f : X → Y} {x : X}
    (hω : ω.MeromorphicAt (f x))
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    (ω.pullback f).MeromorphicAt x := by
  have hg := analyticAt_chartAt_comp_comp_chartAt_symm hf
  have hω' : _root_.MeromorphicAt (ω.coeff (chartAt ℂ (f x)))
      (((chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    simpa only [comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using
      (meromorphicAt_def ω (f x)).mp hω
  apply (meromorphicAt_def _ x).mpr
  exact ((hω'.comp_analyticAt hg).mul hg.deriv.meromorphicAt).congr
    ((coeff_pullback_eventuallyEq ω hf).symm.filter_mono nhdsWithin_le_nhds)

/-- Pullback by a holomorphic map preserves holomorphy of a differential. -/
theorem HolomorphicAt.pullback {ω : OneForm Y} {f : X → Y} {x : X}
    (hω : ω.HolomorphicAt (f x))
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    (ω.pullback f).HolomorphicAt x := by
  have hg := analyticAt_chartAt_comp_comp_chartAt_symm hf
  have hω' : AnalyticAt ℂ (ω.coeff (chartAt ℂ (f x)))
      (((chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    simpa only [comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using
      (holomorphicAt_def ω (f x)).mp hω
  apply (holomorphicAt_def _ x).mpr
  exact ((hω'.comp hg).mul hg.deriv).congr (coeff_pullback_eventuallyEq ω hf).symm

/-- **The ramification formula for differentials.** If `f` is holomorphic and nonconstant near
`x`, pullback multiplies the order by its local multiplicity `e` and adds `e - 1`. -/
theorem order_pullback {ω : OneForm Y} {f : X → Y} {x : X}
    (hω : ω.MeromorphicAt (f x))
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hnc : ¬ EventuallyConst f (𝓝 x)) :
    (ω.pullback f).order x = ω.order (f x) * localMultiplicity f x +
      (((localMultiplicity f x : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  let g := ((chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm)
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) :=
    analyticAt_chartAt_comp_comp_chartAt_symm hf
  have hmult := natCast_localMultiplicity hf hnc
  have hpos : (localMultiplicity f x : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.1 ((localMultiplicity_pos_iff hf).2 hnc))
  have hgorder : _root_.meromorphicOrderAt (fun z ↦ g z - g (chartAt ℂ x x))
      (chartAt ℂ x x) = (localMultiplicity f x : ℤ) := by
    have hg₀ : AnalyticAt ℂ (fun z ↦ g z - g (chartAt ℂ x x)) (chartAt ℂ x x) :=
      hg.sub analyticAt_const
    rw [hg₀.meromorphicOrderAt_eq]
    simp only [g, comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), ← hmult]
    rfl
  have hgnc : ¬ EventuallyConst g (𝓝 (chartAt ℂ x x)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    simp only [g, comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), ← hmult]
    simp
  have hω' : _root_.MeromorphicAt (ω.coeff (chartAt ℂ (f x))) (g (chartAt ℂ x x)) := by
    simpa only [g, comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using
      (meromorphicAt_def ω (f x)).mp hω
  have hderiv : _root_.meromorphicOrderAt (deriv g) (chartAt ℂ x x) =
      (((localMultiplicity f x : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    have hd : deriv (fun z ↦ g z - g (chartAt ℂ x x)) = deriv g :=
      funext fun _ ↦ deriv_sub_const _
    rw [← hd]
    exact _root_.meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hpos) hgorder
  rw [order_def, _root_.meromorphicOrderAt_congr
    ((coeff_pullback_eventuallyEq ω hf).filter_mono nhdsWithin_le_nhds),
    _root_.meromorphicOrderAt_mul (hω'.comp_analyticAt hg) hg.deriv.meromorphicAt,
    hω'.meromorphicOrderAt_comp hg hgnc, hderiv]
  simp [g, comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), ← hmult, order_def]

section Compact

variable [CompactSpace X] [CompactSpace Y]

/-- **The divisor formula for pullback of a meromorphic differential.** The correction to
pullback of its divisor is exactly the ramification divisor of the map. -/
theorem divisor_pullback (ω : OneForm Y) (f : FiniteHolomorphicMap X Y)
    (hω : ∀ y, ω.MeromorphicAt y) (hω₀ : ∀ y, ω.order y ≠ ⊤) :
    (ω.pullback f).divisor = divisorPullback f ω.divisor + ramificationDivisor f := by
  have hpb (x : X) : (ω.pullback f).MeromorphicAt x :=
    (hω (f x)).pullback (Eventually.of_forall fun y ↦ f.holomorphic y)
  refine AlgebraicGeometry.WeilDivisor.ext fun x ↦ ?_
  rw [AlgebraicGeometry.WeilDivisor.coeff_add, coeff_divisor hpb,
    coeff_divisorPullback, coeff_divisor hω, coeff_ramificationDivisor,
    order_pullback (hω (f x)) (Eventually.of_forall fun y ↦ f.holomorphic y)
      (f.not_eventuallyConst x)]
  lift ω.order (f x) to ℤ using hω₀ (f x) with k hk
  simp only [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add,
    WithTop.untop₀_coe]
  ring

end Compact

end TauCeti.RiemannSurface.OneForm
