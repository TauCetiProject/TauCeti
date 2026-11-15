/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.MetricSpace.Cauchy
import TauCeti.Algebra.Order.Field.Basic

/-!
# The space `L⁰(μ; E)` of measurable functions with the convergence-in-measure metric

For a measure `μ` on `α` and a topological target `E`, `TauCeti.L0 E μ` is the space of
almost-everywhere equivalence classes of strongly measurable functions `α → E`. It wraps
`α →ₘ[μ] E` (`MeasureTheory.AEEqFun`) as a distinct type so that `AEEqFun` itself stays free of a
canonical topology (for instance, interpolation couples equip `AEEqFun` with the indiscrete
topology, whereas the convergence-in-measure metric requires a finite measure), while inheriting
the almost-everywhere pointwise order and topological lattice operations from `AEEqFun`.

When `E` is a (pseudo)metric space and `μ` is a finite measure, `L0 E μ` carries the bounded
metric
$$d(f, g) = \int \frac{\operatorname{dist}(f(x), g(x))}{1 + \operatorname{dist}(f(x), g(x))}
  \, d\mu(x).$$
Two-sided quantitative estimates link this integral to tail measures:
* Markov's inequality (`TauCeti.L0.measureReal_ge_le_mul_dist`): for $\varepsilon > 0$,
  $\mu(\{\operatorname{dist}(f, g) \ge \varepsilon\}) \le
    \frac{1 + \varepsilon}{\varepsilon} d(f, g)$.
* Reverse finite-mass bound (`TauCeti.L0.dist_le_mul_measureReal_univ_add_measureReal_gt`):
  $d(f, g) \le \varepsilon\,\mu(\mathrm{univ}) + \mu(\{\operatorname{dist}(f, g) > \varepsilon\})$
  for $\varepsilon \ge 0$.

Together these show that convergence in `L0 E μ` along an arbitrary filter is equivalent to
`MeasureTheory.TendstoInMeasure` (`TauCeti.L0.tendsto_iff_tendstoInMeasure`). When `E` is complete,
`L0 E μ` is complete (`TauCeti.L0.instCompleteSpace`): along any sequence controlled at dyadic
scales $B_k = 2^{-2k} / (1 + 2^{-k})$, Markov's inequality makes the tail events
$\{\operatorname{dist}(u_k, u_{k+1}) \ge 2^{-k}\}$ summable, so the first Borel–Cantelli lemma
produces an almost-everywhere limit in `E`, which is also the limit in measure.

## Main declarations

* `TauCeti.L0 E μ`: almost-everywhere equivalence classes of strongly measurable functions `α → E`,
  equipped with the almost-everywhere pointwise order/lattice structure and, on finite measure
  spaces, the convergence-in-measure metric.
* `TauCeti.L0.mk`, `TauCeti.L0.const`, `TauCeti.L0.equivAEEqFun`: quotient constructor, constant
  classes, and equivalence with `α →ₘ[μ] E`.
* `TauCeti.L0.instPseudoMetricSpace`, `TauCeti.L0.instMetricSpace`, `TauCeti.L0.dist_const_const`:
  (pseudo)metric space structure on `L0 E μ` when `[IsFiniteMeasure μ]` and closed-form distance
  between constant classes.
* `TauCeti.L0.measureReal_ge_le_mul_dist`,
  `TauCeti.L0.dist_le_mul_measureReal_univ_add_measureReal_gt`: quantitative two-sided tail bounds.
* `TauCeti.L0.tendsto_iff_tendstoInMeasure`: metric convergence in `L0 E μ` is equivalent to
  `MeasureTheory.TendstoInMeasure` along any filter.
* `TauCeti.L0.instCompleteSpace`: completeness of `L0 E μ` for complete `E` and finite `μ`.
-/

public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

/-- The space `L⁰(μ; E)` of almost-everywhere equivalence classes of strongly measurable functions
`α → E`, equipped on finite measure spaces with the convergence-in-measure metric. -/
structure L0 {α : Type*} (E : Type*) {mα : MeasurableSpace α} [TopologicalSpace E]
    (μ : Measure α := by volume_tac) where
  /-- Construct an element of `L0 E μ` from its underlying `AEEqFun` class. -/
  ofAEEqFun ::
  /-- The underlying `AEEqFun` equivalence class of an element of `L0 E μ`. -/
  toAEEqFun : α →ₘ[μ] E

namespace L0

section Basic

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E]

/-- `L0.toAEEqFun` is injective. -/
theorem toAEEqFun_injective : Function.Injective (toAEEqFun : L0 E μ → α →ₘ[μ] E) := by
  rintro ⟨f⟩ ⟨g⟩ rfl
  rfl

@[simp]
theorem ofAEEqFun_toAEEqFun (f : L0 E μ) : ofAEEqFun f.toAEEqFun = f := by
  cases f; rfl

@[simp]
theorem toAEEqFun_ofAEEqFun (f : α →ₘ[μ] E) : (ofAEEqFun f).toAEEqFun = f := by
  rfl

/-- Canonical equivalence between `L0 E μ` and `α →ₘ[μ] E`. -/
def equivAEEqFun : L0 E μ ≃ (α →ₘ[μ] E) where
  toFun := toAEEqFun
  invFun := ofAEEqFun
  left_inv := ofAEEqFun_toAEEqFun
  right_inv := toAEEqFun_ofAEEqFun

@[simp]
theorem equivAEEqFun_apply (f : L0 E μ) : equivAEEqFun f = f.toAEEqFun := by
  rfl

@[simp]
theorem equivAEEqFun_symm_apply (f : α →ₘ[μ] E) : equivAEEqFun.symm f = ofAEEqFun f := by
  rfl

/-- Canonical measurable representative of an element of `L0 E μ`. -/
@[coe]
def coeFn (f : L0 E μ) : α → E :=
  ⇑f.toAEEqFun

instance instCoeFun : CoeFun (L0 E μ) (fun _ ↦ α → E) :=
  ⟨coeFn⟩

@[simp]
theorem coeFn_toAEEqFun (f : L0 E μ) : ⇑f.toAEEqFun = ⇑f :=
  (rfl)

@[simp]
theorem coeFn_ofAEEqFun (f : α →ₘ[μ] E) : ⇑(ofAEEqFun f : L0 E μ) = ⇑f := by
  rfl

/-- The canonical representative of an element of `L0 E μ` is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable (f : L0 E μ) : StronglyMeasurable f :=
  f.toAEEqFun.stronglyMeasurable

/-- The canonical representative of an element of `L0 E μ` is almost-everywhere strongly
measurable. -/
@[fun_prop]
theorem aestronglyMeasurable (f : L0 E μ) : AEStronglyMeasurable f μ :=
  f.toAEEqFun.aestronglyMeasurable

/-- The canonical representative of an element of `L0 E μ` is measurable when `E` has a
pseudo-metrizable Borel structure. -/
@[fun_prop]
theorem measurable [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : L0 E μ) : Measurable f :=
  f.toAEEqFun.measurable

/-- Two elements of `L0 E μ` are equal when their representatives agree almost everywhere. -/
@[ext]
theorem ext {f g : L0 E μ} (h : f =ᵐ[μ] g) : f = g :=
  toAEEqFun_injective (AEEqFun.ext h)

instance instInhabited [Inhabited E] : Inhabited (L0 E μ) :=
  ⟨ofAEEqFun default⟩

instance instSubsingleton [IsEmpty α] : Subsingleton (L0 E μ) :=
  ⟨fun _ _ ↦ ext (ae_of_all _ isEmptyElim)⟩

/-- When `μ = 0`, `L0 E μ` is a subsingleton. -/
theorem subsingleton_of_measure_zero (hμ : μ = 0) : Subsingleton (L0 E μ) :=
  ⟨fun f g ↦ ext (by simp [EventuallyEq, hμ])⟩

/-- Quotient class in `L0 E μ` of an almost-everywhere strongly measurable function `f : α → E`. -/
def mk (f : α → E) (hf : AEStronglyMeasurable f μ) : L0 E μ :=
  ofAEEqFun (AEEqFun.mk f hf)

@[simp]
theorem toAEEqFun_mk (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (mk (μ := μ) f hf).toAEEqFun = AEEqFun.mk f hf := by
  rfl

@[simp]
theorem ofAEEqFun_mk (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (ofAEEqFun (AEEqFun.mk f hf) : L0 E μ) = mk f hf := by
  rfl

/-- The representative of `L0.mk f hf` agrees with `f` almost everywhere. -/
theorem coeFn_mk (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (mk (μ := μ) f hf : α → E) =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f hf

@[simp]
theorem mk_coeFn (f : L0 E μ) : mk (μ := μ) f f.aestronglyMeasurable = f :=
  toAEEqFun_injective (AEEqFun.mk_coeFn f.toAEEqFun)

/-- Two classes `L0.mk f hf` and `L0.mk g hg` are equal iff `f =ᵐ[μ] g`. -/
@[simp]
theorem mk_eq_mk {f g : α → E} {hf : AEStronglyMeasurable f μ} {hg : AEStronglyMeasurable g μ} :
    mk (μ := μ) f hf = mk (μ := μ) g hg ↔ f =ᵐ[μ] g := by
  rw [← toAEEqFun_injective.eq_iff, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.mk_eq_mk]

/-- The class in `L0 E μ` of the constant function with value `c : E`. -/
def const (α : Type*) {_ : MeasurableSpace α} {μ : Measure α} (c : E) : L0 E μ :=
  ofAEEqFun (AEEqFun.const α c)

@[simp]
theorem toAEEqFun_const (c : E) : (const (μ := μ) α c).toAEEqFun = AEEqFun.const α c := by
  rfl

@[simp]
theorem ofAEEqFun_const (c : E) : (ofAEEqFun (AEEqFun.const α c) : L0 E μ) = const α c := by
  rfl

/-- The representative of `L0.const α c` agrees with `Function.const α c` almost everywhere. -/
theorem coeFn_const (α : Type*) {_ : MeasurableSpace α} {μ : Measure α} (c : E) :
    (const (μ := μ) α c : α → E) =ᵐ[μ] Function.const α c :=
  coeFn_mk _ _

@[simp]
theorem coeFn_const_eq [NeZero μ] (c : E) (x : α) : const (μ := μ) α c x = c :=
  AEEqFun.coeFn_const_eq α c x

@[simp]
theorem mk_const (c : E) (hf : AEStronglyMeasurable (fun _ ↦ c) μ := aestronglyMeasurable_const) :
    mk (μ := μ) (fun _ ↦ c) hf = const α c :=
  mk_eq_mk.mpr Filter.EventuallyEq.rfl

end Basic

section Order

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E]

instance instPreorder [Preorder E] : Preorder (L0 E μ) :=
  Preorder.lift toAEEqFun

/-- Order on `L0 E μ` is the almost-everywhere pointwise order inherited from `α →ₘ[μ] E`. -/
theorem le_def [Preorder E] {f g : L0 E μ} : f ≤ g ↔ f.toAEEqFun ≤ g.toAEEqFun :=
  (Iff.rfl)

@[simp]
theorem ofAEEqFun_le [Preorder E] {f g : α →ₘ[μ] E} :
    (ofAEEqFun f : L0 E μ) ≤ ofAEEqFun g ↔ f ≤ g :=
  (Iff.rfl)

@[simp]
theorem mk_le_mk [Preorder E] {f g : α → E} {hf : AEStronglyMeasurable f μ}
    {hg : AEStronglyMeasurable g μ} :
    mk (μ := μ) f hf ≤ mk (μ := μ) g hg ↔ f ≤ᵐ[μ] g :=
  AEEqFun.mk_le_mk hf hg

@[simp]
theorem coeFn_le [Preorder E] {f g : L0 E μ} : (f : α → E) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← coeFn_toAEEqFun, ← coeFn_toAEEqFun, AEEqFun.coeFn_le, le_def]

instance instPartialOrder [PartialOrder E] : PartialOrder (L0 E μ) :=
  PartialOrder.lift toAEEqFun toAEEqFun_injective

instance instSup [SemilatticeSup E] [ContinuousSup E] : Max (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun ⊔ g.toAEEqFun)⟩

@[simp]
theorem toAEEqFun_sup [SemilatticeSup E] [ContinuousSup E] (f g : L0 E μ) :
    (f ⊔ g).toAEEqFun = f.toAEEqFun ⊔ g.toAEEqFun := by
  rfl

@[simp]
theorem ofAEEqFun_sup [SemilatticeSup E] [ContinuousSup E] (f g : α →ₘ[μ] E) :
    (ofAEEqFun (f ⊔ g) : L0 E μ) = ofAEEqFun f ⊔ ofAEEqFun g := by
  rfl

/-- Representative of `f ⊔ g` in `L0 E μ` agrees with `fun x ↦ f x ⊔ g x` almost everywhere. -/
theorem coeFn_sup [SemilatticeSup E] [ContinuousSup E] (f g : L0 E μ) :
    ⇑(f ⊔ g) =ᵐ[μ] fun x ↦ f x ⊔ g x := by
  simp_rw [← coeFn_toAEEqFun]
  exact AEEqFun.coeFn_sup f.toAEEqFun g.toAEEqFun

@[simp]
theorem mk_sup_mk [SemilatticeSup E] [ContinuousSup E] (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (μ := μ) f hf ⊔ mk (μ := μ) g hg = mk (f ⊔ g) (hf.sup hg) := by
  refine ext ((coeFn_sup _ _).trans ?_)
  filter_upwards [coeFn_mk f hf, coeFn_mk g hg, coeFn_mk (f ⊔ g) (hf.sup hg)] with x hfx hgx hfgx
  rw [hfx, hgx, hfgx, Pi.sup_apply]

instance instInf [SemilatticeInf E] [ContinuousInf E] : Min (L0 E μ) :=
  ⟨fun f g ↦ ofAEEqFun (f.toAEEqFun ⊓ g.toAEEqFun)⟩

@[simp]
theorem toAEEqFun_inf [SemilatticeInf E] [ContinuousInf E] (f g : L0 E μ) :
    (f ⊓ g).toAEEqFun = f.toAEEqFun ⊓ g.toAEEqFun := by
  rfl

@[simp]
theorem ofAEEqFun_inf [SemilatticeInf E] [ContinuousInf E] (f g : α →ₘ[μ] E) :
    (ofAEEqFun (f ⊓ g) : L0 E μ) = ofAEEqFun f ⊓ ofAEEqFun g := by
  rfl

/-- Representative of `f ⊓ g` in `L0 E μ` agrees with `fun x ↦ f x ⊓ g x` almost everywhere. -/
theorem coeFn_inf [SemilatticeInf E] [ContinuousInf E] (f g : L0 E μ) :
    ⇑(f ⊓ g) =ᵐ[μ] fun x ↦ f x ⊓ g x := by
  simp_rw [← coeFn_toAEEqFun]
  exact AEEqFun.coeFn_inf f.toAEEqFun g.toAEEqFun

@[simp]
theorem mk_inf_mk [SemilatticeInf E] [ContinuousInf E] (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (μ := μ) f hf ⊓ mk (μ := μ) g hg = mk (f ⊓ g) (hf.inf hg) := by
  refine ext ((coeFn_inf _ _).trans ?_)
  filter_upwards [coeFn_mk f hf, coeFn_mk g hg, coeFn_mk (f ⊓ g) (hf.inf hg)] with x hfx hgx hfgx
  rw [hfx, hgx, hfgx, Pi.inf_apply]

instance instLattice [Lattice E] [TopologicalLattice E] : Lattice (L0 E μ) where
  __ := instPartialOrder
  sup := max
  le_sup_left f g := AEEqFun.le_sup_left f.toAEEqFun g.toAEEqFun
  le_sup_right f g := AEEqFun.le_sup_right f.toAEEqFun g.toAEEqFun
  sup_le f g h := AEEqFun.sup_le f.toAEEqFun g.toAEEqFun h.toAEEqFun
  inf := min
  inf_le_left f g := AEEqFun.inf_le_left f.toAEEqFun g.toAEEqFun
  inf_le_right f g := AEEqFun.inf_le_right f.toAEEqFun g.toAEEqFun
  le_inf f g h := AEEqFun.le_inf f.toAEEqFun g.toAEEqFun h.toAEEqFun

end Order

end L0

/-- On a finite measure space, the bounded distance integrand `dist (f x) (g x) / (1 + dist ...)`
is integrable for any two almost-everywhere strongly measurable functions `f` and `g`. -/
theorem integrable_dist_div_one_add_of_aestronglyMeasurable {α E : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [PseudoMetricSpace E] [IsFiniteMeasure μ] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    Integrable (fun x ↦ dist (f x) (g x) / (1 + dist (f x) (g x))) μ := by
  have hcont : Continuous fun t : ℝ ↦ t / (1 + |t|) :=
    continuous_id.div (continuous_const.add continuous_abs) fun t ↦ by positivity
  have hmeas : AEStronglyMeasurable (fun x ↦ dist (f x) (g x) / (1 + dist (f x) (g x))) μ := by
    refine (hcont.comp_aestronglyMeasurable (hf.dist hg)).congr (ae_of_all _ fun x ↦ ?_)
    simp [abs_of_nonneg dist_nonneg]
  refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (div_one_add_nonneg dist_nonneg)]
  exact div_one_add_le_one dist_nonneg

namespace L0

section Metric

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- On a finite measure space, the integrand defining `dist f g` on `L0 E μ` is integrable. -/
theorem integrable_dist_div_one_add [PseudoMetricSpace E] [IsFiniteMeasure μ] (f g : L0 E μ) :
    Integrable (fun x ↦ dist (f x) (g x) / (1 + dist (f x) (g x))) μ :=
  integrable_dist_div_one_add_of_aestronglyMeasurable f.aestronglyMeasurable g.aestronglyMeasurable

instance instPseudoMetricSpace [PseudoMetricSpace E] [IsFiniteMeasure μ] :
    PseudoMetricSpace (L0 E μ) where
  dist f g := ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ
  dist_self f := by simp
  dist_comm f g := by simp_rw [dist_comm]
  dist_triangle f g h := by
    rw [← integral_add (integrable_dist_div_one_add f g) (integrable_dist_div_one_add g h)]
    refine integral_mono_ae (integrable_dist_div_one_add f h)
      ((integrable_dist_div_one_add f g).add (integrable_dist_div_one_add g h))
      (ae_of_all _ fun x ↦ ?_)
    exact (div_one_add_mono dist_nonneg (dist_triangle (f x) (g x) (h x))).trans
      (div_one_add_add_le dist_nonneg dist_nonneg)

/-- Explicit integral formula for the convergence-in-measure distance on `L0 E μ`. -/
theorem dist_def [PseudoMetricSpace E] [IsFiniteMeasure μ] (f g : L0 E μ) :
    dist f g = ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ :=
  (rfl)

/-- Norm form of the distance on `L0 E μ` when `E` is a seminormed additive group. -/
theorem dist_eq_integral_norm [SeminormedAddCommGroup E] [IsFiniteMeasure μ] (f g : L0 E μ) :
    dist f g = ∫ x, ‖f x - g x‖ / (1 + ‖f x - g x‖) ∂μ := by
  simp_rw [dist_def, dist_eq_norm]

/-- Absolute-value form of the distance on `L0 ℝ μ`. -/
theorem dist_eq_integral_abs [IsFiniteMeasure μ] (f g : L0 ℝ μ) :
    dist f g = ∫ x, |f x - g x| / (1 + |f x - g x|) ∂μ := by
  simp_rw [dist_def, Real.dist_eq]

/-- The distance between `L0.mk f hf` and `L0.mk g hg` is computed directly from the
representatives `f` and `g`, independent of the choice of representatives. -/
theorem dist_mk_mk [PseudoMetricSpace E] [IsFiniteMeasure μ] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    dist (mk (μ := μ) f hf) (mk (μ := μ) g hg) =
      ∫ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ∂μ := by
  rw [dist_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mk (μ := μ) f hf, coeFn_mk (μ := μ) g hg] with x hfx hgx
  rw [hfx, hgx]

/-- On the zero measure, every `L⁰` distance is `0`. -/
theorem dist_eq_zero_of_measure_zero [PseudoMetricSpace E] [IsFiniteMeasure μ] (hμ : μ = 0)
    (f g : L0 E μ) : dist f g = 0 := by
  have := subsingleton_of_measure_zero (E := E) hμ
  rw [Subsingleton.elim f g, dist_self]

/-- Closed-form `L⁰` distance between two constant classes on a finite measure space:
`dist (const α a) (const α b) = μ.real Set.univ * (dist a b / (1 + dist a b))`. -/
theorem dist_const_const [PseudoMetricSpace E] [IsFiniteMeasure μ] (a b : E) :
    dist (const (μ := μ) α a) (const (μ := μ) α b) =
      μ.real Set.univ * (dist a b / (1 + dist a b)) := by
  rw [dist_def]
  have hcongr : (fun x ↦ dist (const (μ := μ) α a x) (const (μ := μ) α b x) /
      (1 + dist (const (μ := μ) α a x) (const (μ := μ) α b x))) =ᵐ[μ]
      fun _ : α ↦ dist a b / (1 + dist a b) := by
    filter_upwards [coeFn_const (μ := μ) α a, coeFn_const (μ := μ) α b] with x ha hb
    rw [ha, hb]
    rfl
  rw [integral_congr_ae hcongr, integral_const, smul_eq_mul]

/-- Embedding a constant value into `L0 E μ` is continuous on a finite measure space. -/
@[fun_prop]
theorem continuous_const [PseudoMetricSpace E] [IsFiniteMeasure μ] :
    Continuous (const (μ := μ) α : E → L0 E μ) := by
  refine (LipschitzWith.of_dist_le' (K := μ.real Set.univ) fun a b ↦ ?_).continuous
  rw [dist_const_const]
  exact mul_le_mul_of_nonneg_left
    (div_le_self dist_nonneg (le_add_of_nonneg_right dist_nonneg)) measureReal_nonneg

instance instMetricSpace [MetricSpace E] [IsFiniteMeasure μ] : MetricSpace (L0 E μ) where
  eq_of_dist_eq_zero {f g} h := by
    rw [dist_def, integral_eq_zero_iff_of_nonneg (fun _ ↦ div_one_add_nonneg dist_nonneg)
      (integrable_dist_div_one_add f g)] at h
    refine ext (h.mono fun x hx ↦ ?_)
    exact dist_eq_zero.mp ((div_one_add_eq_zero_iff dist_nonneg).mp hx)

/-- The convergence-in-measure distance on `L0 E μ` is bounded above by the total mass
`μ.real Set.univ`. -/
theorem dist_le_measureReal_univ [PseudoMetricSpace E] [IsFiniteMeasure μ] (f g : L0 E μ) :
    dist f g ≤ μ.real Set.univ := by
  calc dist f g
      ≤ ∫ _ : α, (1 : ℝ) ∂μ := integral_mono (integrable_dist_div_one_add f g)
          (integrable_const 1) fun _ ↦ div_one_add_le_one dist_nonneg
    _ = μ.real Set.univ := by simp

/-- On a nonzero finite measure space, the distance between any two elements of `L0 E μ` is
strictly smaller than the total mass `μ.real Set.univ`. -/
theorem dist_lt_measureReal_univ [PseudoMetricSpace E] [IsFiniteMeasure μ] [NeZero μ]
    (f g : L0 E μ) : dist f g < μ.real Set.univ := by
  refine lt_of_le_of_ne (dist_le_measureReal_univ f g) fun heq ↦ ?_
  have hone : ∫ _ : α, (1 : ℝ) ∂μ = μ.real Set.univ := by simp
  rw [dist_def, ← hone, integral_eq_iff_of_ae_le (integrable_dist_div_one_add f g)
    (integrable_const 1) (ae_of_all _ fun _ ↦ div_one_add_le_one dist_nonneg)] at heq
  have hbot : ∀ᵐ _ ∂μ, False :=
    heq.mono fun _ hx ↦ (div_one_add_lt_one dist_nonneg).ne hx
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hbot))

/-- On a probability space, the convergence-in-measure distance is strictly bounded by `1`. -/
theorem dist_lt_one [PseudoMetricSpace E] [IsProbabilityMeasure μ] (f g : L0 E μ) :
    dist f g < 1 := by
  simpa using dist_lt_measureReal_univ f g

/-- **Markov's inequality for the `L⁰` metric.** For every `ε > 0`, the real measure of the set
where `dist (f x) (g x) ≥ ε` is bounded by `((1 + ε) / ε) * dist f g`. -/
theorem measureReal_ge_le_mul_dist [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε ≤ dist (f x) (g x)} ≤ (1 + ε) / ε * dist f g := by
  have h1ε : 0 < 1 + ε := by linarith
  have hstep : ε / (1 + ε) * μ.real {x | ε ≤ dist (f x) (g x)} ≤ dist f g :=
    (mul_le_mul_of_nonneg_left
      (measureReal_mono (fun _ hx ↦ div_one_add_mono hε.le hx) (measure_ne_top μ _))
      (div_one_add_nonneg hε.le)).trans
      (mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ fun _ ↦ div_one_add_nonneg dist_nonneg)
        (integrable_dist_div_one_add f g) (ε / (1 + ε)))
  calc μ.real {x | ε ≤ dist (f x) (g x)}
      = (1 + ε) / ε * (ε / (1 + ε) * μ.real {x | ε ≤ dist (f x) (g x)}) := by
          field_simp [hε.ne', h1ε.ne']
    _ ≤ (1 + ε) / ε * dist f g :=
        mul_le_mul_of_nonneg_left hstep (div_nonneg h1ε.le hε.le)

/-- Strict-tail variant of `measureReal_ge_le_mul_dist`. -/
theorem measureReal_gt_le_mul_dist [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε < dist (f x) (g x)} ≤ (1 + ε) / ε * dist f g :=
  (measureReal_mono (μ := μ) (fun _ hx ↦ by rw [Set.mem_ofPred_eq] at hx ⊢; exact hx.le)
    (measure_ne_top μ _)).trans (measureReal_ge_le_mul_dist hε)

/-- `ℝ≥0∞`-valued form of Markov's inequality for the `L⁰` metric. -/
theorem measure_ge_le_ofReal_mul_dist [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε ≤ dist (f x) (g x)} ≤ ENNReal.ofReal ((1 + ε) / ε * dist f g) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← measureReal_def]
  exact ENNReal.ofReal_le_ofReal (measureReal_ge_le_mul_dist hε)

/-- **Reverse tail bound for the `L⁰` metric.** On a finite measure space, for every `ε ≥ 0`,
`dist f g ≤ ε * μ.real Set.univ + μ.real {x | ε < dist (f x) (g x)}`. The total-mass factor
`μ.real Set.univ` is sharp on general finite measure spaces when `μ Set.univ ≠ 1`. -/
theorem dist_le_mul_measureReal_univ_add_measureReal_gt [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 ≤ ε) :
    dist f g ≤ ε * μ.real Set.univ + μ.real {x | ε < dist (f x) (g x)} := by
  let s : Set α := {x | ε < dist (f x) (g x)}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (f.stronglyMeasurable.dist g.stronglyMeasurable).measurable
  have hpt : ∀ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ≤
      ε + s.indicator (fun _ : α ↦ (1 : ℝ)) x := fun x ↦ by
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact (div_one_add_le_one dist_nonneg).trans (by linarith)
    · rw [Set.indicator_of_notMem hx, add_zero]
      rw [Set.mem_ofPred_eq, not_lt] at hx
      exact (div_le_self dist_nonneg (by linarith [dist_nonneg (x := f x) (y := g x)])).trans hx
  calc dist f g
      ≤ ∫ x, (ε + s.indicator (fun _ : α ↦ (1 : ℝ)) x) ∂μ :=
        integral_mono (integrable_dist_div_one_add f g)
          ((integrable_const ε).add ((integrable_const (1 : ℝ)).indicator hs)) hpt
    _ = (∫ _ : α, ε ∂μ) + ∫ x, s.indicator (fun _ : α ↦ (1 : ℝ)) x ∂μ :=
        integral_add (integrable_const ε) ((integrable_const (1 : ℝ)).indicator hs)
    _ = ε * μ.real Set.univ + μ.real s := by
        rw [integral_const, smul_eq_mul, mul_comm, integral_indicator hs]
        simp

/-- Non-strict tail variant of `dist_le_mul_measureReal_univ_add_measureReal_gt`. -/
theorem dist_le_mul_measureReal_univ_add_measureReal_ge [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 ≤ ε) :
    dist f g ≤ ε * μ.real Set.univ + μ.real {x | ε ≤ dist (f x) (g x)} := by
  have hsub : μ.real {x | ε < dist (f x) (g x)} ≤ μ.real {x | ε ≤ dist (f x) (g x)} :=
    measureReal_mono (fun _ hx ↦ by rw [Set.mem_ofPred_eq] at hx ⊢; exact hx.le)
      (measure_ne_top μ _)
  linarith [dist_le_mul_measureReal_univ_add_measureReal_gt (f := f) (g := g) hε]

/-- On a probability space, `dist f g ≤ ε + μ.real {x | ε < dist (f x) (g x)}` for `ε ≥ 0`. -/
theorem dist_le_add_measureReal_gt [PseudoMetricSpace E] [IsProbabilityMeasure μ]
    {f g : L0 E μ} {ε : ℝ} (hε : 0 ≤ ε) :
    dist f g ≤ ε + μ.real {x | ε < dist (f x) (g x)} := by
  simpa using dist_le_mul_measureReal_univ_add_measureReal_gt (f := f) (g := g) hε

/-- **Equivalence of `L⁰` convergence and convergence in measure.** On a finite measure space, a
family `u : ι → L0 E μ` converges to `f : L0 E μ` along a filter `l` if and only if its
representatives satisfy `MeasureTheory.TendstoInMeasure μ (fun i ↦ u i) l f`. -/
theorem tendsto_iff_tendstoInMeasure [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {l : Filter ι} {u : ι → L0 E μ} {f : L0 E μ} :
    Tendsto u l (𝓝 f) ↔ TendstoInMeasure μ (fun i ↦ (u i : α → E)) l f := by
  rw [tendsto_iff_dist_tendsto_zero, tendstoInMeasure_iff_measureReal_dist]
  constructor
  · intro hu ε hε
    have hlim : Tendsto (fun i ↦ (1 + ε) / ε * dist (u i) f) l (𝓝 0) := by
      simpa only [mul_zero] using hu.const_mul ((1 + ε) / ε)
    exact squeeze_zero (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_ge_le_mul_dist hε) hlim
  · intro hu
    rw [Metric.tendsto_nhds]
    intro η hη
    let ε : ℝ := η / (2 * (μ.real Set.univ + 1))
    have hden : 0 < μ.real Set.univ + 1 := by positivity
    have hε : 0 < ε := div_pos hη (by positivity)
    have hε_mass : ε * μ.real Set.univ < η / 2 := by
      calc ε * μ.real Set.univ
          < ε * (μ.real Set.univ + 1) := by gcongr; linarith
        _ = η / 2 := by
            dsimp [ε]
            field_simp [hden.ne']
    filter_upwards [(Metric.tendsto_nhds.mp (hu ε hε)) (η / 2) (half_pos hη)] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    linarith [dist_le_mul_measureReal_univ_add_measureReal_ge (f := u i) (g := f) hε.le]

/-- Quotient-constructor phrasing of `tendsto_iff_tendstoInMeasure`: `L0.mk (f i) _` converges to
`L0.mk g _` in `L0 E μ` along `l` if and only if `TendstoInMeasure μ f l g`. -/
theorem tendsto_mk_iff_tendstoInMeasure [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι → α → E} {g : α → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hg : AEStronglyMeasurable g μ) :
    Tendsto (fun i ↦ mk (μ := μ) (f i) (hf i)) l (𝓝 (mk (μ := μ) g hg)) ↔
      TendstoInMeasure μ f l g := by
  rw [tendsto_iff_tendstoInMeasure]
  exact ⟨fun h ↦ h.congr (fun i ↦ coeFn_mk (f i) (hf i)) (coeFn_mk g hg),
    fun h ↦ h.congr (fun i ↦ (coeFn_mk (f i) (hf i)).symm) (coeFn_mk g hg).symm⟩

/-- Almost-everywhere sequential convergence on a finite measure space implies convergence in
`L0 E μ`. -/
theorem tendsto_of_tendsto_ae [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {u : ℕ → L0 E μ} {f : L0 E μ}
    (h : ∀ᵐ x ∂μ, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) :
    Tendsto u atTop (𝓝 f) :=
  tendsto_iff_tendstoInMeasure.mpr
    (tendstoInMeasure_of_tendsto_ae (fun n ↦ (u n).aestronglyMeasurable) h)

/-- Every sequence converging in `L0 E μ` admits a subsequence whose representatives converge
almost everywhere. -/
theorem exists_seq_tendsto_ae_of_tendsto [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {u : ℕ → L0 E μ} {f : L0 E μ} (hu : Tendsto u atTop (𝓝 f)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun k ↦ u (ns k) x) atTop (𝓝 (f x)) :=
  (tendsto_iff_tendstoInMeasure.mp hu).exists_seq_tendsto_ae

private theorem exists_tendsto_of_controlled_dist [PseudoMetricSpace E] [CompleteSpace E]
    [IsFiniteMeasure μ] [Nonempty α] {u : ℕ → L0 E μ}
    (hu : ∀ k : ℕ, dist (u k) (u (k + 1)) < ((1 / 2 : ℝ) ^ k) ^ 2 / (1 + (1 / 2 : ℝ) ^ k)) :
    ∃ f : L0 E μ, Tendsto u atTop (𝓝 f) := by
  have : Nonempty E := ⟨u 0 (Classical.arbitrary α)⟩
  let S : ℕ → Set α := fun k ↦ {x | (1 / 2 : ℝ) ^ k ≤ dist (u k x) (u (k + 1) x)}
  have hμS : ∀ k : ℕ, μ (S k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k ↦ by
    have hε : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
    have hmul : (1 + (1 / 2 : ℝ) ^ k) / (1 / 2 : ℝ) ^ k * dist (u k) (u (k + 1)) ≤
        (1 / 2 : ℝ) ^ k := by
      have h1 : 0 < 1 + (1 / 2 : ℝ) ^ k := by positivity
      calc (1 + (1 / 2 : ℝ) ^ k) / (1 / 2 : ℝ) ^ k * dist (u k) (u (k + 1))
          ≤ (1 + (1 / 2 : ℝ) ^ k) / (1 / 2 : ℝ) ^ k *
              (((1 / 2 : ℝ) ^ k) ^ 2 / (1 + (1 / 2 : ℝ) ^ k)) :=
            mul_le_mul_of_nonneg_left (hu k).le (div_nonneg h1.le hε.le)
        _ = (1 / 2 : ℝ) ^ k := by field_simp [hε.ne', h1.ne']
    calc μ (S k)
        ≤ ENNReal.ofReal ((1 + (1 / 2 : ℝ) ^ k) / (1 / 2 : ℝ) ^ k * dist (u k) (u (k + 1))) :=
          measure_ge_le_ofReal_mul_dist hε
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.ofReal_le_ofReal hmul
      _ = (2⁻¹ : ℝ≥0∞) ^ k := by
          rw [ENNReal.ofReal_pow (by positivity), one_div,
            ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  have hμ_limsup : μ (atTop.limsup S) = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (tsum_le_tsum hμS))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  let g : α → E := fun x ↦ limUnder atTop fun k ↦ u k x
  have h_ae : ∀ᵐ x ∂μ, Tendsto (fun k ↦ u k x) atTop (𝓝 (g x)) := by
    refine measure_mono_null (fun x hx ↦ ?_) hμ_limsup
    rw [Set.mem_ofPred_eq] at hx
    by_contra hx_not
    rw [limsup_eq_iInf_iSup_of_nat] at hx_not
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_ofPred_eq, not_forall, not_exists, not_le] at hx_not
    obtain ⟨K, hK⟩ := hx_not
    have hcau : CauchySeq fun j ↦ u (j + K) x :=
      cauchySeq_of_le_geometric (1 / 2) ((1 / 2 : ℝ) ^ K) (by norm_num) fun j ↦ by
        rw [← pow_add, add_comm K j, add_right_comm]
        exact (hK (j + K) (Nat.le_add_left K j)).le
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
    exact hx (tendsto_nhds_limUnder ⟨y, (tendsto_add_atTop_iff_nat K).mp hy⟩)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k ↦ (u k).aestronglyMeasurable) h_ae
  refine ⟨mk (μ := μ) g hg, tendsto_iff_tendstoInMeasure.mpr ?_⟩
  exact (tendstoInMeasure_of_tendsto_ae (fun k ↦ (u k).aestronglyMeasurable) h_ae).congr_right
    (coeFn_mk (μ := μ) g hg).symm

/-- **Completeness of `L⁰(μ; E)`.** On a finite measure space, `L0 E μ` is complete whenever `E`
is a complete pseudometric space. -/
instance instCompleteSpace [PseudoMetricSpace E] [CompleteSpace E] [IsFiniteMeasure μ] :
    CompleteSpace (L0 E μ) := by
  refine Metric.complete_of_convergent_controlled_sequences
    (fun k ↦ ((1 / 2 : ℝ) ^ k) ^ 2 / (1 + (1 / 2 : ℝ) ^ k)) (fun k ↦ by positivity) fun u hu ↦ ?_
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨u 0, tendsto_const_nhds.congr fun n ↦ Subsingleton.elim _ _⟩
  · exact exists_tendsto_of_controlled_dist fun k ↦ hu k k (k + 1) le_rfl (Nat.le_succ k)

end Metric

end L0

end TauCeti
