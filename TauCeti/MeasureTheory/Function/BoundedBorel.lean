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

/-- The zero symbol coerces to the zero function. -/
@[simp] theorem coe_zero : ⇑(0 : BoundedBorelFunction X) = 0 := (rfl)

/-- The unit symbol coerces to the constant unit function. -/
@[simp] theorem coe_one : ⇑(1 : BoundedBorelFunction X) = 1 := (rfl)

/-- Function coercion preserves addition. -/
@[simp] theorem coe_add (f g : BoundedBorelFunction X) : ⇑(f + g) = ⇑f + ⇑g := (rfl)

/-- Function coercion preserves negation. -/
@[simp] theorem coe_neg (f : BoundedBorelFunction X) : ⇑(-f) = -⇑f := (rfl)

/-- Function coercion preserves subtraction. -/
@[simp] theorem coe_sub (f g : BoundedBorelFunction X) : ⇑(f - g) = ⇑f - ⇑g := (rfl)

/-- Function coercion preserves multiplication. -/
@[simp] theorem coe_mul (f g : BoundedBorelFunction X) : ⇑(f * g) = ⇑f * ⇑g := (rfl)

/-- Function coercion preserves scalar multiplication. -/
@[simp] theorem coe_smul (c : ℂ) (f : BoundedBorelFunction X) : ⇑(c • f) = c • ⇑f := (rfl)

/-- Function coercion preserves the star operation. -/
@[simp] theorem coe_star (f : BoundedBorelFunction X) : ⇑(star f) = star ⇑f := (rfl)

/-- Function coercion preserves natural powers. -/
@[simp] theorem coe_pow (f : BoundedBorelFunction X) (n : ℕ) : ⇑(f ^ n) = ⇑f ^ n := (rfl)

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

/-- Evaluation of zero. -/
@[simp] theorem zero_apply (x : X) : (0 : BoundedBorelFunction X) x = 0 := (rfl)

/-- Evaluation of one. -/
@[simp] theorem one_apply (x : X) : (1 : BoundedBorelFunction X) x = 1 := (rfl)

/-- Evaluation of addition. -/
@[simp] theorem add_apply (f g : BoundedBorelFunction X) (x : X) :
    (f + g) x = f x + g x := (rfl)

/-- Evaluation of negation. -/
@[simp] theorem neg_apply (f : BoundedBorelFunction X) (x : X) : (-f) x = -f x := (rfl)

/-- Evaluation of subtraction. -/
@[simp] theorem sub_apply (f g : BoundedBorelFunction X) (x : X) :
    (f - g) x = f x - g x := (rfl)

/-- Evaluation of multiplication. -/
@[simp] theorem mul_apply (f g : BoundedBorelFunction X) (x : X) :
    (f * g) x = f x * g x := (rfl)

/-- Evaluation of scalar multiplication. -/
@[simp] theorem smul_apply (c : ℂ) (f : BoundedBorelFunction X) (x : X) :
    (c • f) x = c * f x := (rfl)

/-- Evaluation of the star operation is complex conjugation. -/
@[simp] theorem star_apply (f : BoundedBorelFunction X) (x : X) :
    (star f) x = star (f x) := (rfl)

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
  simp only [mul_apply, indicator_apply]
  exact (Set.inter_indicator_mul _ _ x).symm

/-- Pullback commutes with restriction and extension by zero. -/
theorem compStarAlgHom'_indicator (g : X → Y) (hg : Measurable g) (s : Set Y)
    (hs : MeasurableSet s) (f : BoundedBorelFunction Y) :
    compStarAlgHom' g hg (indicator s hs f) =
      indicator (g ⁻¹' s) (hs.preimage hg) (compStarAlgHom' g hg f) := by
  ext x
  simp only [compStarAlgHom'_apply, indicator_apply]
  exact (Set.indicator_comp_right g (g := (f : Y → ℂ)) (s := s) (x := x)).symm

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

end BoundedBorelFunction
end TauCeti
