/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# Bounded Borel symbols

Bounded measurable complex functions form a commutative C⋆-algebra under pointwise operations
and the supremum norm. They are realised as the star subalgebra of `ℓ^∞(X, ℂ)`, Mathlib's
`lp (fun _ : X ↦ ℂ) ∞`, cut out by measurability, so the supremum norm, the normed star algebra
structure and the C⋆-identity are those of `ℓ^∞`. Uniform limits of measurable functions are
measurable, so this subalgebra is closed and the symbols form a complete space.

Equality is pointwise; no measure or almost-everywhere quotient is involved. On a topological
space equipped with its Borel measurable space these are bounded Borel functions. The domain may
be empty, in which case every norm vanishes; on a nonempty domain the unit has norm one.

These symbols form the source algebra for bounded Borel functional calculus: constants,
measurable simple functions and restrictions to measurable sets are bounded symbols, pullback
along a measurable map is a star algebra homomorphism (hence norm-nonincreasing, as is every star
homomorphism between C⋆-algebras), and convergence in norm is uniform convergence.

Simple functions embed as a star subalgebra of symbols, and this subalgebra is dense: every symbol
is the uniform limit of simple symbols bounded by its norm (`exists_seq_tendsto_ofSimpleFunc`).
Since a simple symbol is a finite combination of indicators of disjoint measurable sets, this is
the approximation through which a functional calculus defined on indicators extends by
continuity to all bounded Borel symbols.

On a compact space whose open sets are measurable, continuous complex functions are bounded Borel
symbols (`ofContinuousMap`). This embedding of `C(X, ℂ)` is a unital star algebra homomorphism, is
isometric for the two supremum norms, and is compatible with pullback along continuous measurable
maps. It is how a Borel functional calculus is compared with a continuous one, for instance with
a star representation of `C(X, ℂ)` or with Mathlib's continuous functional calculus `cfcHom`.

Pointwise evaluation at `x : X` is a continuous unital star algebra homomorphism
`evalStarAlgHom x : BoundedBorelFunction X →⋆ₐ[ℂ] ℂ`. Self-adjointness is pointwise
(`isSelfAdjoint_iff`), and every bounded measurable real-valued function bundles as a self-adjoint
symbol `ofRealFunction`, which factors as `star s * s` whenever it is nonnegative
(`exists_star_mul_self_ofRealFunction`).

An arbitrary measurable complex function `f : X → ℂ` restricts on each norm sublevel
`{x | ‖f x‖ ≤ M}` to a bounded Borel symbol (`BoundedBorelFunction.truncate`). As `M` increases,
these level-set truncations have monotone extended norms and converge pointwise to `f`, providing
the bounded approximations through which an unbounded Borel functional calculus is constructed from
a bounded one.

For nonreal `z`, the resolvent function `s ↦ (z - s)⁻¹` on `ℝ` is a bounded Borel symbol
(`resolventSymbol`), bounded by `|Im z|⁻¹`.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal

namespace TauCeti

variable (X : Type*) [MeasurableSpace X]

/-- The star subalgebra of `ℓ^∞(X, ℂ)` consisting of the measurable bounded functions. -/
def boundedBorelSubalgebra : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞) where
  carrier := {f | Measurable (f : X → ℂ)}
  zero_mem' := measurable_const
  one_mem' := measurable_const
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  algebraMap_mem' _ := measurable_const
  star_mem' hf := Complex.continuous_conj.measurable.comp hf

/-- An element of `ℓ^∞(X, ℂ)` is a bounded Borel symbol exactly when it is measurable. -/
@[simp] theorem mem_boundedBorelSubalgebra (f : lp (fun _ : X ↦ ℂ) ∞) :
    f ∈ boundedBorelSubalgebra X ↔ Measurable (f : X → ℂ) := (Iff.rfl)

/-- Uniform limits of measurable functions are measurable, so the bounded Borel symbols form a
closed subalgebra of `ℓ^∞(X, ℂ)`. -/
theorem isClosed_boundedBorelSubalgebra :
    IsClosed (boundedBorelSubalgebra X : Set (lp (fun _ : X ↦ ℂ) ∞)) :=
  IsSeqClosed.isClosed fun _ _ hF hFf ↦
    measurable_of_tendsto_metrizable hF ((lp.uniformContinuous_coe.continuous.tendsto _).comp hFf)

/-- Bounded Borel symbols, with the pointwise algebra and the supremum norm of `ℓ^∞`. -/
abbrev BoundedBorelFunction : Type _ := ↥(boundedBorelSubalgebra X)

namespace BoundedBorelFunction

/-- Bounded Borel symbols form a Banach space, since they form a closed subspace of `ℓ^∞`. -/
instance : CompleteSpace (BoundedBorelFunction X) :=
  (isClosed_boundedBorelSubalgebra X).completeSpace_coe

/-- Bounded Borel symbols form a commutative unital C⋆-algebra, as a closed star subalgebra of
`ℓ^∞(X, ℂ)`. -/
instance : CommCStarAlgebra (BoundedBorelFunction X) :=
  StarSubalgebra.commCStarAlgebra _ (h_closed := isClosed_boundedBorelSubalgebra X)

variable {X}

instance : FunLike (BoundedBorelFunction X) X ℂ where
  coe f := (f : lp (fun _ : X ↦ ℂ) ∞)
  coe_injective _ _ h := Subtype.ext (lp.ext h)

/-- Evaluating the underlying element of `ℓ^∞` is evaluating the symbol. -/
@[simp] theorem coe_val (f : BoundedBorelFunction X) :
    ⇑(f : lp (fun _ : X ↦ ℂ) ∞) = ⇑f := (rfl)

/-- Function coercion determines a bounded Borel symbol. -/
theorem coe_injective : Function.Injective
    (DFunLike.coe : BoundedBorelFunction X → X → ℂ) := DFunLike.coe_injective

/-! Evaluation is pointwise for the algebraic operations, so Mathlib's generic `FunLike`
lemmas (`FunLike.coe_add`, `add_apply`, `FunLike.coe_sum`, `sum_apply`, ...) apply. -/

/-- Evaluating the zero symbol gives zero. -/
instance : IsZeroApply (BoundedBorelFunction X) where

/-- Evaluating the unit symbol gives one. -/
instance : IsOneApply (BoundedBorelFunction X) where

/-- Evaluation is additive. -/
instance : IsAddApply (BoundedBorelFunction X) where

/-- Evaluation commutes with negation. -/
instance : IsNegApply (BoundedBorelFunction X) where

/-- Evaluation commutes with subtraction. -/
instance : IsSubApply (BoundedBorelFunction X) where

/-- Evaluation is multiplicative. -/
instance : IsMulApply (BoundedBorelFunction X) where

/-- Evaluation commutes with complex scalar multiplication. -/
instance : IsSMulApply ℂ (BoundedBorelFunction X) where

/-- Evaluation commutes with natural powers. -/
instance : IsPowApply ℕ (BoundedBorelFunction X) where

/-- Function coercion preserves the star operation. -/
@[simp] theorem coe_star (f : BoundedBorelFunction X) : ⇑(star f) = star ⇑f := (rfl)

/-- Algebra scalars coerce to constant functions. -/
@[simp] theorem coe_algebraMap (c : ℂ) :
    ⇑(algebraMap ℂ (BoundedBorelFunction X) c) = fun _ => c := (rfl)

/-- Two symbols are equal when they agree at every point. -/
@[ext] theorem ext {f g : BoundedBorelFunction X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Evaluation of a bounded Borel symbol is measurable. -/
@[fun_prop] theorem measurable (f : BoundedBorelFunction X) : Measurable f := f.property

/-- The norm of a symbol is the supremum of the norms of its values. -/
theorem norm_eq_iSup_norm (f : BoundedBorelFunction X) : ‖f‖ = ⨆ x, ‖f x‖ :=
  lp.norm_eq_ciSup (f : lp (fun _ : X ↦ ℂ) ∞)

/-- Each value of a symbol is bounded in norm by the supremum norm. -/
theorem norm_coe_le_norm (f : BoundedBorelFunction X) (x : X) : ‖f x‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero (f : lp (fun _ : X ↦ ℂ) ∞) x

/-- A nonnegative constant bounds the supremum norm exactly when it bounds every value. -/
theorem norm_le {f : BoundedBorelFunction X} {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  ⟨fun h x ↦ (norm_coe_le_norm f x).trans h, lp.norm_le_of_forall_le hC⟩

/-- On an empty domain every symbol has norm zero. -/
theorem norm_eq_zero_of_empty [IsEmpty X] (f : BoundedBorelFunction X) : ‖f‖ = 0 := by
  simp [Subsingleton.elim f 0]

/-- Convergence in the supremum norm is uniform convergence of the values. -/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → BoundedBorelFunction X}
    {f : BoundedBorelFunction X} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i ↦ ⇑(F i)) f l := by
  refine ⟨fun h ↦ Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_,
    fun h ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  · filter_upwards [Metric.tendsto_nhds.1 h ε hε] with i hi x
    rw [dist_comm, dist_eq_norm] at hi
    simpa [dist_eq_norm] using (norm_coe_le_norm (f - F i) x).trans_lt hi
  · filter_upwards [Metric.tendstoUniformly_iff.1 h (ε / 2) (half_pos hε)] with i hi
    rw [dist_comm, dist_eq_norm]
    refine ((norm_le (half_pos hε).le).2 fun x ↦ ?_).trans_lt (half_lt_self hε)
    simpa [dist_eq_norm] using (hi x).le

/-- Every symbol has a nonnegative bound valid at every point, including on an empty domain. -/
theorem exists_bound (f : BoundedBorelFunction X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M :=
  ⟨‖f‖, norm_nonneg f, norm_coe_le_norm f⟩

/-- A symbol is integrable against every finite measure. -/
theorem integrable (f : BoundedBorelFunction X) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] : MeasureTheory.Integrable f μ :=
  .of_bound f.measurable.aestronglyMeasurable ‖f‖ (.of_forall (norm_coe_le_norm f))

/-- Any natural power of the norm of a symbol is integrable against every finite measure. -/
theorem integrable_norm_pow (f : BoundedBorelFunction X) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ) :
    MeasureTheory.Integrable (fun x => ‖f x‖ ^ k) μ := by
  simpa only [FunLike.coe_pow, Pi.pow_apply, norm_pow] using ((f ^ k).integrable μ).norm

/-- Bundle a measurable function with its everywhere bound. -/
def ofFunction (f : X → ℂ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) : BoundedBorelFunction X :=
  ⟨⟨f, memℓp_infty <| hbound.elim fun M hM ↦ ⟨M, Set.forall_mem_range.2 hM.2⟩⟩, hf⟩

/-- Bundling preserves evaluation. -/
@[simp] theorem ofFunction_apply (f : X → ℂ) (hf : Measurable f) (hbound) (x : X) :
    ofFunction f hf hbound x = f x := (rfl)

/-- Evaluation of an algebra scalar is the constant scalar. -/
@[simp] theorem algebraMap_apply (c : ℂ) (x : X) :
    algebraMap ℂ (BoundedBorelFunction X) c x = c := (rfl)

/-- Evaluation of the star operation is complex conjugation. -/
@[simp] theorem star_apply (f : BoundedBorelFunction X) (x : X) :
    (star f) x = star (f x) := (rfl)

/-- Pointwise evaluation at `x : X`, as a unital star algebra homomorphism on bounded Borel
symbols. -/
def evalStarAlgHom (x : X) : BoundedBorelFunction X →⋆ₐ[ℂ] ℂ where
  toFun f := f x
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

/-- Evaluating `evalStarAlgHom x` on a symbol evaluates the symbol at `x`. -/
@[simp]
theorem evalStarAlgHom_apply (x : X) (f : BoundedBorelFunction X) :
    evalStarAlgHom x f = f x :=
  (rfl)

/-- Pointwise evaluation at `x` is continuous for the supremum norm. -/
@[fun_prop]
theorem continuous_eval (x : X) : Continuous fun f : BoundedBorelFunction X ↦ f x :=
  (continuous_apply x).comp (lp.uniformContinuous_coe.continuous.comp continuous_subtypeVal)

/-- A bounded Borel symbol is self-adjoint iff each of its values is fixed by complex conjugation.
-/
theorem isSelfAdjoint_iff {f : BoundedBorelFunction X} :
    IsSelfAdjoint f ↔ ∀ x, star (f x) = f x := by
  simp [IsSelfAdjoint, BoundedBorelFunction.ext_iff]

/-- Bundle a bounded measurable real-valued function as a bounded Borel symbol. -/
def ofRealFunction (g : X → ℝ) (hg : Measurable g)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |g x| ≤ M) : BoundedBorelFunction X :=
  ofFunction (fun x ↦ (g x : ℂ)) (Complex.measurable_ofReal.comp hg) <|
    let ⟨M, hM, hgM⟩ := hbound
    ⟨M, hM, fun x ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using hgM x⟩

/-- Evaluating `ofRealFunction` at `x` gives `(g x : ℂ)`. -/
@[simp]
theorem ofRealFunction_apply (g : X → ℝ) (hg : Measurable g) (hbound) (x : X) :
    ofRealFunction g hg hbound x = g x := by
  simp [ofRealFunction]

/-- Coercing `ofRealFunction` gives the real-to-complex cast of the underlying function. -/
theorem coe_ofRealFunction (g : X → ℝ) (hg : Measurable g) (hbound) :
    ⇑(ofRealFunction g hg hbound) = fun x ↦ (g x : ℂ) :=
  funext (ofRealFunction_apply g hg hbound)

/-- Every real-valued bounded Borel symbol is self-adjoint. -/
theorem isSelfAdjoint_ofRealFunction (g : X → ℝ) (hg : Measurable g) (hbound) :
    IsSelfAdjoint (ofRealFunction g hg hbound) :=
  isSelfAdjoint_iff.2 fun x ↦ by simp

/-- A nonnegative constant bounds the norm of `ofRealFunction g` iff it bounds `|g x|` everywhere.
-/
theorem norm_ofRealFunction_le {g : X → ℝ} {hg : Measurable g} {hbound} {C : ℝ} (hC : 0 ≤ C) :
    ‖ofRealFunction g hg hbound‖ ≤ C ↔ ∀ x, |g x| ≤ C := by
  rw [norm_le hC]
  simp

/-- A nonnegative real-valued bounded Borel symbol is a square `star s * s` of a real-valued
bounded Borel symbol, namely its pointwise square root. -/
theorem exists_star_mul_self_ofRealFunction {g : X → ℝ} (hg : Measurable g) (hbound)
    (h0 : ∀ x, 0 ≤ g x) :
    ∃ s : BoundedBorelFunction X, ofRealFunction g hg hbound = star s * s := by
  obtain ⟨M, _, hgM⟩ := id hbound
  refine ⟨ofRealFunction (fun x ↦ √(g x)) hg.sqrt
    ⟨√M, Real.sqrt_nonneg M, fun x ↦ ?_⟩, ?_⟩
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hgM x))
  · ext x
    simp [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 x)]

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- Pullback of symbols along a measurable map, as a star algebra homomorphism. -/
def compStarAlgHom' (g : X → Y) (hg : Measurable g) :
    BoundedBorelFunction Y →⋆ₐ[ℂ] BoundedBorelFunction X where
  toFun f := ofFunction (f ∘ g) (f.measurable.comp hg) <| by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    exact ⟨M, hM, fun x => hfM (g x)⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

/-- Pullback evaluates by composition. -/
@[simp] theorem compStarAlgHom'_apply (g : X → Y) (hg : Measurable g)
    (f : BoundedBorelFunction Y) (x : X) : compStarAlgHom' g hg f x = f (g x) := (rfl)

/-- Pullback by the identity is the identity star algebra homomorphism. -/
@[simp] theorem compStarAlgHom'_id :
    compStarAlgHom' (X := X) id measurable_id = StarAlgHom.id ℂ (BoundedBorelFunction X) :=
  (rfl)

/-- Pullback along a composite is composition of the star algebra homomorphisms. -/
theorem compStarAlgHom'_comp (g : X → Y) (hg : Measurable g) (h : Y → Z) (hh : Measurable h) :
    compStarAlgHom' (h ∘ g) (hh.comp hg) = (compStarAlgHom' g hg).comp (compStarAlgHom' h hh) :=
  (rfl)

/-- Restriction to a measurable set and extension by zero, as a non-unital star algebra
homomorphism. It need not preserve the unit because the unit restricts to the set indicator. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) :
    BoundedBorelFunction X →⋆ₙₐ[ℂ] BoundedBorelFunction X where
  toFun f := ofFunction (s.indicator f) (f.measurable.indicator hs) <| by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    exact ⟨M, hM, fun x ↦ (norm_indicator_le_norm_self f x).trans (hfM x)⟩
  map_zero' := by ext x; exact congrFun (Set.indicator_zero ℂ s) x
  map_add' f g := by ext x; exact congrFun (Set.indicator_add s f g) x
  map_mul' f g := by ext x; exact congrFun (Set.indicator_mul s f g) x
  map_smul' c f := by ext x; exact Set.indicator_const_smul_apply s c f x
  map_star' f := by
    ext x
    exact (map_indicator (starAddEquiv : ℂ ≃+ ℂ) s f x).symm

/-- Restriction coerces to the usual set indicator function. -/
@[simp] theorem coe_indicator (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) : ⇑(indicator s hs f) = s.indicator f := (rfl)

/-- Indicator evaluation is the usual set indicator. -/
@[simp] theorem indicator_apply (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) (x : X) : indicator s hs f x = s.indicator f x := (rfl)

/-- The indicator of the empty set vanishes. -/
@[simp] theorem indicator_empty (f : BoundedBorelFunction X) :
    indicator ∅ MeasurableSet.empty f = 0 := by ext; simp

/-- The indicator of the whole domain is the original symbol. -/
@[simp] theorem indicator_univ (f : BoundedBorelFunction X) :
    indicator Set.univ MeasurableSet.univ f = f := by ext; simp

/-- Products of indicator symbols correspond to intersections. -/
theorem indicator_mul_indicator (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f g : BoundedBorelFunction X) :
    indicator s hs f * indicator t ht g = indicator (s ∩ t) (hs.inter ht) (f * g) := by
  ext x
  simp only [_root_.mul_apply, indicator_apply]
  exact (Set.inter_indicator_mul _ _ x).symm

/-- Multiplying a symbol on the left by `indicator s hs 1` restricts it to `s`. -/
@[simp] theorem indicator_one_mul (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) : indicator s hs 1 * f = indicator s hs f := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- Multiplying a symbol on the right by `indicator s hs 1` restricts it to `s`. -/
@[simp] theorem mul_indicator_one (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) : f * indicator s hs 1 = indicator s hs f := by
  rw [mul_comm, indicator_one_mul]

/-- Pullback commutes with restriction and extension by zero. -/
theorem compStarAlgHom'_indicator (g : X → Y) (hg : Measurable g) (s : Set Y)
    (hs : MeasurableSet s) (f : BoundedBorelFunction Y) :
    compStarAlgHom' g hg (indicator s hs f) =
      indicator (g ⁻¹' s) (hs.preimage hg) (compStarAlgHom' g hg f) := by
  ext x
  simp only [compStarAlgHom'_apply, indicator_apply]
  exact (Set.indicator_comp_right g (g := (f : Y → ℂ)) (s := s) (x := x)).symm

/-- The level-set truncation `{x | ‖f x‖ ≤ M}.indicator f` of a measurable function `f : X → ℂ`
at threshold `M : ℝ`, bundled as a bounded Borel symbol. -/
noncomputable def truncate (f : X → ℂ) (hf : Measurable f) (M : ℝ) : BoundedBorelFunction X :=
  ofFunction ({x | ‖f x‖ ≤ M}.indicator f)
    (hf.indicator (measurableSet_le hf.norm measurable_const))
    ⟨max M 0, le_max_right _ _, fun x => by
      by_cases hx : x ∈ {y | ‖f y‖ ≤ M}
      · rw [Set.indicator_of_mem hx]
        exact (Set.mem_ofPred.1 hx).trans (le_max_left _ _)
      · simp [Set.indicator_of_notMem hx]⟩

/-- Level-set truncation coerces to the indicator of `{x | ‖f x‖ ≤ M}`. -/
@[simp] theorem coe_truncate (f : X → ℂ) (hf : Measurable f) (M : ℝ) :
    ⇑(truncate f hf M) = {x | ‖f x‖ ≤ M}.indicator f := (rfl)

/-- Evaluating a level-set truncation evaluates `{y | ‖f y‖ ≤ M}.indicator f`. -/
@[simp] theorem truncate_apply (f : X → ℂ) (hf : Measurable f) (M : ℝ) (x : X) :
    truncate f hf M x = {y | ‖f y‖ ≤ M}.indicator f x := (rfl)

/-- At a negative threshold `M < 0`, the level-set truncation vanishes identically. -/
theorem truncate_of_neg {f : X → ℂ} (hf : Measurable f) {M : ℝ} (hM : M < 0) :
    truncate f hf M = 0 := by
  ext x
  have hx : ¬ ‖f x‖ ≤ M := not_le.2 (hM.trans_le (norm_nonneg _))
  simp [hx]

/-- Level-set truncation does not increase the pointwise norm. -/
theorem norm_truncate_apply_le (f : X → ℂ) (hf : Measurable f) (M : ℝ) (x : X) :
    ‖truncate f hf M x‖ ≤ ‖f x‖ :=
  norm_indicator_le_norm_self f x

/-- For `0 ≤ M`, the supremum norm of `truncate f hf M` is at most `M`. -/
theorem norm_truncate_le {f : X → ℂ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M) :
    ‖truncate f hf M‖ ≤ M :=
  (norm_le hM).2 fun x => by
    by_cases hx : ‖f x‖ ≤ M <;> simp [hx, hM]

/-- The pointwise extended norm of `truncate f hf M` is monotone in the threshold `M`. -/
theorem enorm_truncate_apply_mono {f : X → ℂ} (hf : Measurable f) :
    Monotone fun (M : ℝ) (x : X) => ‖truncate f hf M x‖ₑ := by
  intro M₁ M₂ hM x
  by_cases h₁ : ‖f x‖ ≤ M₁
  · simp [h₁, h₁.trans hM]
  · simp [h₁]

/-- The supremum over natural thresholds of any natural power of the extended norm of
`truncate f hf n x` is `‖f x‖ₑ ^ k`. -/
theorem iSup_enorm_pow_truncate_apply {f : X → ℂ} (hf : Measurable f) (k : ℕ) (x : X) :
    (⨆ n : ℕ, ‖truncate f hf n x‖ₑ ^ k) = ‖f x‖ₑ ^ k := by
  refine le_antisymm (iSup_le fun n =>
    pow_le_pow_left' (eNorm_le_iff_norm_le.2 (norm_truncate_apply_le f hf n x)) k) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖f x‖
  exact le_iSup_of_le N (by simp [hN])

/-- The supremum over natural thresholds of `‖truncate f hf n x‖ₑ` is `‖f x‖ₑ`. -/
theorem iSup_enorm_truncate_apply {f : X → ℂ} (hf : Measurable f) (x : X) :
    (⨆ n : ℕ, ‖truncate f hf n x‖ₑ) = ‖f x‖ₑ := by
  simpa using iSup_enorm_pow_truncate_apply hf 1 x

/-- By monotone convergence, the supremum over natural thresholds of
`∫⁻ x, ‖truncate f hf n x‖ₑ ^ k` equals `∫⁻ x, ‖f x‖ₑ ^ k`. -/
theorem iSup_lintegral_enorm_pow_truncate {f : X → ℂ} (hf : Measurable f) (k : ℕ)
    (μ : MeasureTheory.Measure X) :
    (⨆ n : ℕ, ∫⁻ x, ‖truncate f hf n x‖ₑ ^ k ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ k ∂μ := by
  rw [← MeasureTheory.lintegral_iSup
    (fun n => (truncate f hf n).measurable.eNorm.pow_const k)
    (fun _ _ hmn x => pow_le_pow_left'
      (enorm_truncate_apply_mono hf (Nat.cast_le.2 hmn) x) k)]
  exact MeasureTheory.lintegral_congr fun x => iSup_enorm_pow_truncate_apply hf k x

/-- As `M → ∞`, `truncate f hf M x` is eventually constant and converges to `f x`. -/
theorem tendsto_truncate_apply {f : X → ℂ} (hf : Measurable f) (x : X) :
    Tendsto (fun M : ℝ => truncate f hf M x) atTop (𝓝 (f x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ‖f x‖] with M hM
  simp [hM]

/-- Complex conjugation commutes with level-set truncation. -/
@[simp] theorem star_truncate (f : X → ℂ) (hf : Measurable f) (M : ℝ) :
    star (truncate f hf M) =
      truncate (star f) (continuous_star.measurable.comp hf) M := by
  ext x
  simp only [star_apply, truncate_apply, Pi.star_apply, norm_star]
  exact map_indicator (starAddEquiv : ℂ ≃+ ℂ) {y | ‖f y‖ ≤ M} f x

/-- Restricting `truncate f hf M` to `{x | ‖f x‖ ≤ M}` leaves it unchanged. -/
@[simp] theorem indicator_norm_le_truncate (f : X → ℂ) (hf : Measurable f) (M : ℝ)
    {hs : MeasurableSet {x | ‖f x‖ ≤ M}} :
    indicator {x | ‖f x‖ ≤ M} hs (truncate f hf M) = truncate f hf M := by
  ext x
  by_cases hx : ‖f x‖ ≤ M <;> simp [hx]

/-- Pullback along a measurable map commutes with level-set truncation. -/
@[simp] theorem compStarAlgHom'_truncate (g : X → Y) (hg : Measurable g) {f : Y → ℂ}
    (hf : Measurable f) (M : ℝ) :
    compStarAlgHom' g hg (truncate f hf M) = truncate (f ∘ g) (hf.comp hg) M := by
  ext x
  simp [Set.indicator_apply, Function.comp_apply]

/-- Every measurable complex simple function is an everywhere bounded symbol. This embedding is a
star algebra homomorphism for the pointwise operations on simple functions. -/
noncomputable def ofSimpleFunc : MeasureTheory.SimpleFunc X ℂ →⋆ₐ[ℂ] BoundedBorelFunction X where
  toFun f := ofFunction f f.measurable <| by
    obtain ⟨M, hM⟩ := (f.map norm).exists_forall_le
    exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

/-- A bundled simple function coerces to the simple function itself. -/
@[simp] theorem coe_ofSimpleFunc (f : MeasureTheory.SimpleFunc X ℂ) : ⇑(ofSimpleFunc f) = ⇑f :=
  (rfl)

/-- Bundling a simple function preserves its values. -/
@[simp] theorem ofSimpleFunc_apply (f : MeasureTheory.SimpleFunc X ℂ) (x : X) :
    ofSimpleFunc f x = f x := (rfl)

/-- The simple function equal to `c` on a measurable set `s` and to zero off `s` is the symbol
`c • indicator s hs 1`. -/
theorem ofSimpleFunc_piecewise_const_zero (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    ofSimpleFunc (MeasureTheory.SimpleFunc.piecewise s hs (MeasureTheory.SimpleFunc.const X c) 0) =
      c • indicator s hs 1 := by
  ext x
  by_cases hx : x ∈ s <;> simp [MeasureTheory.SimpleFunc.piecewise_apply, hx]

/-- **Uniform approximation by simple symbols.** Every bounded Borel symbol is the limit, in the
supremum norm, of simple symbols whose values are bounded by its norm. -/
theorem exists_seq_tendsto_ofSimpleFunc (f : BoundedBorelFunction X) :
    ∃ g : ℕ → MeasureTheory.SimpleFunc X ℂ, (∀ n x, ‖g n x‖ ≤ ‖f‖) ∧
      Tendsto (fun n ↦ ofSimpleFunc (g n)) atTop (𝓝 f) := by
  have h₀ : (0 : ℂ) ∈ Metric.closedBall 0 ‖f‖ := Metric.mem_closedBall_self (norm_nonneg f)
  refine ⟨MeasureTheory.SimpleFunc.approxOn f f.measurable _ 0 h₀, fun n x ↦ ?_, ?_⟩
  · simpa using MeasureTheory.SimpleFunc.approxOn_mem f.measurable h₀ n x
  · simpa only [tendsto_iff_tendstoUniformly, coe_ofSimpleFunc] using
      MeasureTheory.SimpleFunc.tendstoUniformly_approxOn f.measurable h₀
        (isCompact_closedBall 0 ‖f‖).totallyBounded
        fun x ↦ subset_closure (by simpa using norm_coe_le_norm f x)

/-- Simple symbols are dense among bounded Borel symbols. -/
theorem denseRange_ofSimpleFunc : DenseRange (ofSimpleFunc (X := X)) := fun f ↦ by
  obtain ⟨g, -, hg⟩ := exists_seq_tendsto_ofSimpleFunc f
  exact mem_closure_of_tendsto hg (Eventually.of_forall fun n ↦ Set.mem_range_self _)

section ContinuousMap

variable [TopologicalSpace X] [OpensMeasurableSpace X] [CompactSpace X]

/-- On a compact space whose open sets are measurable, every continuous complex function is a
bounded Borel symbol. This embedding is a unital star algebra homomorphism for the pointwise
operations on `C(X, ℂ)`, and it is isometric for the supremum norms (`norm_ofContinuousMap`). -/
noncomputable def ofContinuousMap : C(X, ℂ) →⋆ₐ[ℂ] BoundedBorelFunction X where
  toFun f := ofFunction f f.measurable ⟨‖f‖, norm_nonneg f, f.norm_coe_le_norm⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

/-- A continuous function regarded as a symbol coerces to the function itself. -/
@[simp] theorem coe_ofContinuousMap (f : C(X, ℂ)) : ⇑(ofContinuousMap f) = ⇑f := (rfl)

/-- Regarding a continuous function as a symbol preserves its values. -/
@[simp] theorem ofContinuousMap_apply (f : C(X, ℂ)) (x : X) : ofContinuousMap f x = f x := (rfl)

/-- The supremum norm of a continuous function regarded as a symbol is its supremum norm as a
continuous function. -/
theorem norm_ofContinuousMap (f : C(X, ℂ)) : ‖ofContinuousMap f‖ = ‖f‖ := by
  rw [norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm, coe_ofContinuousMap]

/-- Regarding continuous functions as symbols is an isometry. -/
theorem isometry_ofContinuousMap : Isometry (ofContinuousMap (X := X)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_ofContinuousMap

/-- Pulling back a continuous function along a continuous measurable map between compact spaces
gives the symbol of the composite continuous function. -/
@[simp] theorem compStarAlgHom'_ofContinuousMap [TopologicalSpace Y] [OpensMeasurableSpace Y]
    [CompactSpace Y] (φ : C(X, Y)) (hφ : Measurable φ) (g : C(Y, ℂ)) :
    compStarAlgHom' φ hφ (ofContinuousMap g) = ofContinuousMap (g.comp φ) := (rfl)

end ContinuousMap

/-- For nonreal `z`, the resolvent function `s ↦ (z - s)⁻¹` on `ℝ` as a bounded Borel symbol: it
is bounded by `|Im z|⁻¹`. Its spectral integral against a self-adjoint operator is the
resolvent of that operator. -/
def resolventSymbol (z : ℂ) (hz : z.im ≠ 0) : BoundedBorelFunction ℝ :=
  ofFunction (fun s : ℝ ↦ (z - s)⁻¹) (by fun_prop) <| by
    refine ⟨|z.im|⁻¹, by positivity, fun s ↦ ?_⟩
    rw [norm_inv]
    refine inv_anti₀ (abs_pos.2 hz) ?_
    simpa using Complex.abs_im_le_norm (z - s)

/-- The resolvent symbol takes the value `(z - s)⁻¹` at `s`. -/
@[simp] theorem resolventSymbol_apply (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    resolventSymbol z hz s = (z - s)⁻¹ := (rfl)

end BoundedBorelFunction
end TauCeti
