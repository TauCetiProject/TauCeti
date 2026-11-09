/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Meromorphic functions on a Riemann surface and their orders

Let `X` be a Riemann surface, that is, a complex manifold modelled on `ℂ`, and let `f : X → E` be
a function valued in a complex normed space. Reading `f` in the chart `chartAt ℂ x` at `x` gives
the function `f ∘ (chartAt ℂ x).symm` of one complex variable. This file defines `f` to be
*meromorphic at `x`* (`TauCeti.RiemannSurface.MeromorphicAt`) when that representative is
meromorphic at `chartAt ℂ x x` in the sense of Mathlib's `MeromorphicAt`, and defines the
*order of `f` at `x`* (`TauCeti.RiemannSurface.meromorphicOrderAt`) as the meromorphic order of
the representative there, in `WithTop ℤ`: positive at a zero, negative at a pole, and `⊤` when
`f` vanishes on a punctured neighbourhood of `x`.

Since the transition maps between charts of the maximal atlas are holomorphic with nowhere
vanishing derivative, both notions may be computed in any chart of the maximal atlas at `x`
(`TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas` and
`TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`); they are invariants of the
function, not of the coordinate used to read it.

Pulling a meromorphic function back along a holomorphic map `φ : X → Y` gives a meromorphic
function (`TauCeti.RiemannSurface.MeromorphicAt.comp`), and when `φ` is nonconstant near `x` the
order is multiplied by the local multiplicity of `φ`:
`ord_x (F ∘ φ) = ord_{φ x} F * localMultiplicity φ x`
(`TauCeti.RiemannSurface.meromorphicOrderAt_comp`). This is the formula relating orders of a
function upstairs and downstairs along a branched covering.

Orders also obey the local arithmetic used to bound poles: products add their orders, while the
order of a sum is at least the minimum of the two orders. Thus sums preserve a fixed divisor bound,
and products add the two divisor bounds.

## Main declarations

* `TauCeti.RiemannSurface.MeromorphicAt`: a function on a Riemann surface is meromorphic at `x`.
* `TauCeti.RiemannSurface.meromorphicOrderAt`: its order at `x`.
* `TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas` and
  `TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`: chart independence.
* `TauCeti.RiemannSurface.tendsto_zero_iff_meromorphicOrderAt_pos`: the order is positive exactly
  where the function tends to zero.
* `TauCeti.RiemannSurface.MeromorphicAt.eventually_contMDiffAt`: a meromorphic function is
  holomorphic on a punctured neighbourhood of its centre.
* `TauCeti.RiemannSurface.meromorphicAt_of_eventually_mdifferentiableAt` and
  `TauCeti.RiemannSurface.meromorphicOrderAt_nonneg_of_eventually_mdifferentiableAt`: a holomorphic
  function is meromorphic, of nonnegative order.
* `TauCeti.RiemannSurface.MeromorphicAt.comp` and `TauCeti.RiemannSurface.meromorphicOrderAt_comp`:
  pullback along a holomorphic map, with the order formula.
* `TauCeti.RiemannSurface.meromorphicAt_const`, `TauCeti.RiemannSurface.MeromorphicAt.add`,
  `.neg`, `.sub`, `.smul`, `.const_smul`, `.mul`, `.inv`, and `.pow`: arithmetic of local
  meromorphic sections.
* `TauCeti.RiemannSurface.meromorphicOrderAt_const`, `_add`, `_neg`, `_smul`, `_const_smul`, and
  `_mul`:
  arithmetic of their orders.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1 (meromorphic functions) and §16 (divisors).
* Mathlib's `meromorphicOrderAt_add`, `meromorphicOrderAt_neg`, and
  `meromorphicOrderAt_smul` in
  `Mathlib/Analysis/Meromorphic/Order.lean`, transferred through the Riemann-surface charts.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §§1 and 4.
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

variable {X E : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : X → E} {x : X}

/-! ### Definitions -/

/-- A function `f : X → E` on a Riemann surface is **meromorphic at `x`** if its representative
`f ∘ (chartAt ℂ x).symm` in the preferred chart at `x` is meromorphic at `chartAt ℂ x x`. Any
chart of the maximal atlas at `x` gives the same notion
(`TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas`). -/
def MeromorphicAt (f : X → E) (x : X) : Prop :=
  _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

theorem meromorphicAt_def (f : X → E) (x : X) :
    MeromorphicAt f x ↔ _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  Iff.rfl

/-- The **order** of a function `f : X → E` on a Riemann surface at `x`: the meromorphic order of
its representative in the preferred chart at `x`. It is positive at a zero, negative at a pole,
and `⊤` when `f` vanishes on a punctured neighbourhood of `x`. Any chart of the maximal atlas at
`x` gives the same value (`TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`).
If `f` is not meromorphic at `x` the value is the junk value `0`, as for `meromorphicOrderAt`. -/
def meromorphicOrderAt (f : X → E) (x : X) : WithTop ℤ :=
  _root_.meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

theorem meromorphicOrderAt_def (f : X → E) (x : X) :
    meromorphicOrderAt f x = _root_.meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  (rfl)

/-- The order of a function that is not meromorphic at `x` is the junk value `0`. -/
theorem meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 :=
  _root_.meromorphicOrderAt_of_not_meromorphicAt hf

/-! ### Values on a punctured neighbourhood -/

/-- Being meromorphic at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem MeromorphicAt.congr (hf : MeromorphicAt f x) (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x :=
  _root_.MeromorphicAt.congr hf (h.comp_tendsto (tendsto_chartAt_symm_nhdsNE x))

/-- Functions agreeing on a punctured neighbourhood of `x` are meromorphic at `x` together. -/
theorem meromorphicAt_congr (h : f =ᶠ[𝓝[≠] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/-- The order at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem meromorphicOrderAt_congr (h : f =ᶠ[𝓝[≠] x] g) :
    meromorphicOrderAt f x = meromorphicOrderAt g x :=
  _root_.meromorphicOrderAt_congr (h.comp_tendsto (tendsto_chartAt_symm_nhdsNE x))

/-! ### Limits and the sign of the order -/

/-- A function meromorphic at `x` tends to zero along the punctured neighbourhoods of `x` exactly
when its order at `x` is positive. -/
theorem tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) :
    Tendsto f (𝓝[≠] x) (𝓝 0) ↔ 0 < meromorphicOrderAt f x := by
  rw [← tendsto_comp_chartAt_symm_nhdsNE_iff (H := ℂ)]
  exact _root_.tendsto_zero_iff_meromorphicOrderAt_pos hf

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-! ### Chart independence -/

/-- **Chart independence of meromorphy.** A function is meromorphic at `x` exactly when its
representative in some (equivalently, any) chart of the maximal atlas at `x` is meromorphic at the
coordinate of `x`. -/
theorem meromorphicAt_iff_of_mem_maximalAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) :
    MeromorphicAt f x ↔ _root_.MeromorphicAt (f ∘ e.symm) (e x) := by
  have hcx := mem_chart_source ℂ x
  rw [_root_.MeromorphicAt.meromorphicAt_congr
      ((comp_symm_eventuallyEq_comp_chartAt_symm_comp f hx).filter_mono nhdsWithin_le_nhds),
    meromorphicAt_comp_iff_of_deriv_ne_zero
      (analyticAt_symm_trans he (chart_mem_maximalAtlas x) hx hcx)
      (deriv_symm_trans_ne_zero he (chart_mem_maximalAtlas x) hx hcx)]
  simp [MeromorphicAt, e.left_inv hx]

/-- **Chart independence of the order.** The order of a function at `x` is the meromorphic order
of its representative in any chart of the maximal atlas at `x`. -/
theorem meromorphicOrderAt_eq_of_mem_maximalAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) :
    meromorphicOrderAt f x = _root_.meromorphicOrderAt (f ∘ e.symm) (e x) := by
  have hcx := mem_chart_source ℂ x
  rw [_root_.meromorphicOrderAt_congr
      ((comp_symm_eventuallyEq_comp_chartAt_symm_comp f hx).filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_comp_of_deriv_ne_zero
      (analyticAt_symm_trans he (chart_mem_maximalAtlas x) hx hcx)
      (deriv_symm_trans_ne_zero he (chart_mem_maximalAtlas x) hx hcx)]
  simp [meromorphicOrderAt, e.left_inv hx]

/-- A meromorphic function is holomorphic on a punctured neighbourhood of its centre. -/
theorem MeromorphicAt.eventually_contMDiffAt [CompleteSpace E] (hf : MeromorphicAt f x) :
    ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, E) ω f y := by
  have : IsManifold 𝓘(ℂ) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  have hm := ((meromorphicAt_def _ _).1 hf).eventually_analyticAt
  filter_upwards [(tendsto_chartAt_nhdsNE x).eventually hm,
    nhdsWithin_le_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))]
    with y hy hys
  exact (contMDiffAt_omega_iff_analyticAt_of_mem_maximalAtlas
    (chart_mem_maximalAtlas x) hys).2 (by simpa using hy)

/-- A function holomorphic near `x` is meromorphic at `x`. -/
theorem meromorphicAt_of_eventually_mdifferentiableAt [CompleteSpace E]
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, E) f y) : MeromorphicAt f x :=
  (analyticAt_comp_chartAt_symm hf).meromorphicAt

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A function holomorphic near `x` has nonnegative order at `x`. -/
theorem meromorphicOrderAt_nonneg_of_eventually_mdifferentiableAt
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, E) f y) : 0 ≤ meromorphicOrderAt f x := by
  by_cases hm : MeromorphicAt f x
  · refine (_root_.tendsto_nhds_iff_meromorphicOrderAt_nonneg hm).1 ⟨f x, ?_⟩
    exact (hf.self_of_nhds.continuousAt.tendsto.comp
      ((chartAt ℂ x).tendsto_symm (mem_chart_source ℂ x))).mono_left nhdsWithin_le_nhds
  · rw [meromorphicOrderAt_of_not_meromorphicAt hm]

/-! ### Pullback along a holomorphic map -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  {F : Y → E} {φ : X → Y}

/-- **Pullback of a meromorphic function.** A function meromorphic at `φ x`, pulled back along a
map `φ` holomorphic near `x`, is meromorphic at `x`. -/
theorem MeromorphicAt.comp (hF : MeromorphicAt F (φ x))
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) : MeromorphicAt (F ∘ φ) x := by
  have hF' : _root_.MeromorphicAt (F ∘ (chartAt ℂ (φ x)).symm)
      (chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm (chartAt ℂ x x)))) := by
    rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  exact (hF'.comp_analyticAt (g := fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)))
    (analyticAt_chartAt_comp_comp_chartAt_symm hφ)).congr
    ((comp_comp_chartAt_symm_eventuallyEq F hφ.self_of_nhds.continuousAt).symm.filter_mono
      nhdsWithin_le_nhds)

/-- **The order formula for pullbacks.** Pulling a function meromorphic at `φ x` back along a map
`φ` holomorphic and nonconstant near `x` multiplies its order by the local multiplicity of `φ`
at `x`. -/
theorem meromorphicOrderAt_comp (hF : MeromorphicAt F (φ x))
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) (hnc : ¬ EventuallyConst φ (𝓝 x)) :
    meromorphicOrderAt (F ∘ φ) x = meromorphicOrderAt F (φ x) * localMultiplicity φ x := by
  have hcx := mem_chart_source ℂ x
  have hF' : _root_.MeromorphicAt (F ∘ (chartAt ℂ (φ x)).symm)
      (chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm (chartAt ℂ x x)))) := by
    rwa [(chartAt ℂ x).left_inv hcx]
  have hnc' := not_eventuallyConst_chartAt_comp_comp_chartAt_symm hφ hnc
  rw [meromorphicOrderAt, _root_.meromorphicOrderAt_congr
      ((comp_comp_chartAt_symm_eventuallyEq (H := ℂ) (H' := ℂ) F
        hφ.self_of_nhds.continuousAt).filter_mono nhdsWithin_le_nhds),
    hF'.meromorphicOrderAt_comp (g := fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)))
      (analyticAt_chartAt_comp_comp_chartAt_symm hφ) hnc']
  simp only [(chartAt ℂ x).left_inv hcx,
    ← natCast_localMultiplicity hφ.self_of_nhds.continuousAt hnc,
    ENat.map_natCast, WithTop.coe_natCast]
  simp only [meromorphicOrderAt]

end IsManifold

/-- A meromorphic function of finite order is nonzero on a punctured neighbourhood. -/
theorem MeromorphicAt.eventually_ne_zero (hf : MeromorphicAt f x)
    (ho : meromorphicOrderAt f x ≠ ⊤) : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  have hz : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), f ((chartAt ℂ x).symm z) ≠ 0 :=
    (_root_.meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp ho
  filter_upwards [(tendsto_chartAt_nhdsNE (H := ℂ) x).eventually hz,
    nhdsWithin_le_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))]
    with y hy hs
  simpa only [Function.comp_apply, (chartAt ℂ x).left_inv hs] using hy

/-! ### Arithmetic of meromorphic orders -/

/-- A constant function is meromorphic at every point of a Riemann surface. -/
@[simp]
theorem meromorphicAt_const (c : E) (x : X) : MeromorphicAt (fun _ ↦ c) x :=
  _root_.MeromorphicAt.const c _

/-- The order of a constant function is `⊤` if the constant is zero and `0` otherwise. -/
theorem meromorphicOrderAt_const (c : E) (x : X) [Decidable (c = 0)] :
    meromorphicOrderAt (fun _ ↦ c) x = if c = 0 then ⊤ else 0 :=
  _root_.meromorphicOrderAt_const _ c

/-- The sum of functions meromorphic at a point of a Riemann surface is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.add (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x := by
  rw [meromorphicAt_def] at hf hg ⊢
  rw [Pi.add_comp]
  exact hf.add hg

/-- Negation preserves meromorphy at a point of a Riemann surface. -/
@[to_fun]
theorem MeromorphicAt.neg (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  rw [meromorphicAt_def] at hf ⊢
  rw [Pi.neg_comp]
  exact hf.neg

/-- The difference of functions meromorphic at a point is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.sub (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  rw [meromorphicAt_def] at hf hg ⊢
  rw [Pi.sub_comp]
  exact hf.sub hg

/-- The order of a sum on a Riemann surface is at least the minimum of the orders of the summands,
when the second summand is meromorphic. If `f` is not meromorphic then neither is `f + g`, and both
`meromorphicOrderAt f x` and `meromorphicOrderAt (f + g) x` are the junk value `0`. -/
theorem meromorphicOrderAt_add (hg : MeromorphicAt g x) :
    min (meromorphicOrderAt f x) (meromorphicOrderAt g x) ≤
      meromorphicOrderAt (f + g) x := by
  by_cases hf : MeromorphicAt f x
  · rw [meromorphicAt_def] at hf hg
    simp only [meromorphicOrderAt_def, Pi.add_comp]
    exact _root_.meromorphicOrderAt_add hf hg
  · have hfg : ¬ MeromorphicAt (f + g) x := fun h ↦ hf (by simpa using h.sub hg)
    rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt hfg]
    exact min_le_left _ _

/-- Negation preserves the meromorphic order at a point of a Riemann surface. -/
theorem meromorphicOrderAt_neg : meromorphicOrderAt f x = meromorphicOrderAt (-f) x := by
  simp only [meromorphicOrderAt_def, Pi.neg_comp]
  exact _root_.meromorphicOrderAt_neg

section Scalar

variable {f : X → ℂ} {g : X → E}

/-- A scalar meromorphic function times a vector-valued meromorphic function is meromorphic. -/
@[to_fun]
theorem MeromorphicAt.smul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rw [meromorphicAt_def] at hf hg ⊢
  exact hf.smul hg

/-- A constant multiple of a function meromorphic at a point is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.const_smul (hg : MeromorphicAt g x) (c : ℂ) : MeromorphicAt (c • g) x := by
  rw [meromorphicAt_def] at hg ⊢
  rw [Pi.smul_comp]
  exact hg.const_smul c

/-- The order of a scalar times a vector-valued meromorphic function is the sum of their
orders. -/
@[to_fun]
theorem meromorphicOrderAt_smul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f • g) x =
      meromorphicOrderAt f x + meromorphicOrderAt g x := by
  rw [meromorphicAt_def] at hf hg
  simp only [meromorphicOrderAt_def]
  exact _root_.meromorphicOrderAt_smul hf hg

/-- Multiplying by a nonzero constant does not change the order at a point of a Riemann
surface. -/
theorem meromorphicOrderAt_const_smul {c : ℂ} (hc : c ≠ 0) :
    meromorphicOrderAt (c • g) x = meromorphicOrderAt g x := by
  simp only [meromorphicOrderAt_def, Pi.smul_comp]
  exact _root_.meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc

end Scalar

section Multiplicative

variable {f g : X → ℂ}

/-- The product of functions meromorphic at a point of a Riemann surface is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.mul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x := by
  simpa only [smul_eq_mul] using hf.smul hg

/-- The inverse of a function meromorphic at a point of a Riemann surface is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.inv (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
  rw [meromorphicAt_def] at hf ⊢
  rw [Pi.inv_comp]
  exact hf.inv

/-- The order of the inverse of a function on a Riemann surface is the negative of its order. -/
@[to_fun]
theorem meromorphicOrderAt_inv : meromorphicOrderAt f⁻¹ x = -meromorphicOrderAt f x := by
  simp only [meromorphicOrderAt_def, Pi.inv_comp, _root_.meromorphicOrderAt_inv]

/-- A power of a function meromorphic at a point of a Riemann surface is meromorphic there. -/
@[to_fun]
theorem MeromorphicAt.pow (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
  rw [meromorphicAt_def] at hf ⊢
  rw [Pi.pow_comp]
  exact hf.pow n

/-- The order of a product of meromorphic functions on a Riemann surface is the sum of their
orders. -/
@[to_fun]
theorem meromorphicOrderAt_mul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x =
      meromorphicOrderAt f x + meromorphicOrderAt g x := by
  simpa only [smul_eq_mul] using meromorphicOrderAt_smul hf hg

end Multiplicative

end TauCeti.RiemannSurface

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

/-- Every integer power of a centered holomorphic coordinate is meromorphic on its chart. -/
theorem meromorphicAt_coordinate_zpow (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (a : ℂ) (n : ℤ) {x : X} (hx : x ∈ e.source) :
    TauCeti.RiemannSurface.MeromorphicAt (fun y ↦ (e y - a) ^ n) x := by
  rw [TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas he hx]
  apply (_root_.MeromorphicAt.zpow (f := fun z : ℂ ↦ z - a) (by fun_prop) n).congr
  filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds (e.map_source hx))] with z hz
  simp only [Function.comp_apply, e.right_inv hz]
  rfl

/-- A power of a centered coordinate has its prescribed order at the centre, and order zero
at the other points of the chart. -/
theorem meromorphicOrderAt_coordinate_zpow (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (a : ℂ) (n : ℤ) {x : X} (hx : x ∈ e.source) :
    TauCeti.RiemannSurface.meromorphicOrderAt (fun y ↦ (e y - a) ^ n) x =
      if e x = a then (n : WithTop ℤ) else 0 := by
  rw [TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas he hx]
  have heq : (fun y ↦ (e y - a) ^ n) ∘ e.symm =ᶠ[𝓝[≠] (e x)] fun z ↦ (z - a) ^ n := by
    filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds (e.map_source hx))] with z hz
    simp only [Function.comp_apply, e.right_inv hz]
  rw [_root_.meromorphicOrderAt_congr heq]
  split_ifs with h
  · subst a
    exact _root_.meromorphicOrderAt_zpow_id_sub_const
  · have ha : AnalyticAt ℂ (fun z : ℂ ↦ (z - a) ^ n) (e x) := by
      apply AnalyticAt.zpow (by fun_prop)
      exact sub_ne_zero.mpr h
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr
      (zpow_ne_zero n (sub_ne_zero.mpr h))]
    rfl

end OpenPartialHomeomorph
