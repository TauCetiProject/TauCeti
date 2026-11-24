/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.RingTheory.Valuation.Spectral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Newton polygons, spectral norms, and roots in field extensions

Let `K` be a complete normed field whose norm is recovered from a real additive valuation `v` at
base `b > 1` by `‖x‖ = b ^ (-v x)` for `x ≠ 0`. Every algebraic extension `L` of `K` carries the
spectral norm `spectralNorm K L` and its canonical base-`b` additive valuation
`TauCeti.spectralAddValuation K L b hb`, which restricts on `K` to `v`.

Consequently:
* Mapping a power series or polynomial from `K` to an algebraic extension `L` preserves its Newton
  polygon and finite slope multiset with respect to `TauCeti.spectralAddValuation K L b hb`.
* Without assuming that `L` is algebraic over `K` or that `f` splits in `L`, every nonzero root `α`
  of a nonzero polynomial `f : K[X]` in any field extension `L` of `K` satisfies
  `Real.logb b (spectralNorm K L α) ∈ f.newtonSlopes v`, and when `f` is pure of slope `m` every
  root satisfies `spectralNorm K L α ≤ b ^ m` (with equality for `α ≠ 0`).
* In any field extension `L` of `K` in which `f` splits — and unconditionally in any algebraically
  closed extension `L` of `K` such as `AlgebraicClosure K`, `PadicAlgCl p`, or `ℂ_[p]` —
  `f.newtonSlopes v` equals the multiset of `Real.logb b (spectralNorm K L α)` over nonzero roots
  `α` in `L` (and `-(TauCeti.spectralAddValuation K L b hb α).untop₀` when `L` is algebraic over
  `K`), and the endpoints and width of the finite face of slope `σ` count the roots of `f` in `L` in
  the open ball `spectralNorm K L α < b ^ σ`, closed ball `spectralNorm K L α ≤ b ^ σ`, and sphere
  `spectralNorm K L α = b ^ σ`.

## Main results

* `PowerSeries.newtonPolygon_map_spectralAddValuation`,
  `Polynomial.newtonPolygon_map_spectralAddValuation`, and
  `Polynomial.newtonSlopes_map_spectralAddValuation`: invariance of Newton polygons and finite
  slopes under scalar extension to an algebraic extension equipped with
  `TauCeti.spectralAddValuation`.
* `Polynomial.logb_spectralNorm_mem_newtonSlopes_of_aeval_eq_zero`,
  `Polynomial.spectralNorm_le_rpow_of_forall_mem_newtonSlopes_eq`, and
  `Polynomial.spectralNorm_eq_rpow_of_forall_mem_newtonSlopes_eq`: single-root spectral-norm
  membership and pure-slope root norm theorems in arbitrary field extensions of `K`.
* `Polynomial.newtonSlopes_eq_map_roots_map_spectralNorm`,
  `Polynomial.card_filter_roots_map_spectralNorm_lt`,
  `Polynomial.card_filter_roots_map_spectralNorm_le`, and
  `Polynomial.card_filter_roots_map_spectralNorm_eq`: root spectral-norm dictionary and ball counts
  when `f` splits in any field extension `L` of `K`.
* `Polynomial.newtonSlopes_eq_map_roots_map_spectralNorm_of_isAlgClosed`,
  `Polynomial.newtonSlopes_eq_map_roots_map_spectralAddValuation_of_isAlgClosed`,
  `Polynomial.forall_mem_newtonSlopes_eq_iff_spectralNorm_eq_of_isAlgClosed`,
  `Polynomial.card_filter_roots_map_spectralNorm_lt_of_isAlgClosed`,
  `Polynomial.card_filter_roots_map_spectralNorm_le_of_isAlgClosed`, and
  `Polynomial.card_filter_roots_map_spectralNorm_eq_of_isAlgClosed`: unconditional slope-root and
  ball-count dictionary in any algebraically closed extension `L` of `K` (such as
  `AlgebraicClosure K`, `PadicAlgCl p`, or `ℂ_[p]`; with `[Algebra.IsAlgebraic K L]` for
  `spectralAddValuation`), with no splitting assumption on `f`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 2 §4 and Chapter 6 §1.
-/

public section

open scoped IntermediateField PowerSeries
open TauCeti

namespace PowerSeries

/-- Mapping a power series from a complete ultrametric field `K` to an algebraic extension `L`
equipped with `TauCeti.spectralAddValuation K L b hb` preserves its Newton polygon. -/
theorem newtonPolygon_map_spectralAddValuation {K L : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (f : K⟦X⟧)
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) :
    (map (algebraMap K L) f).newtonPolygon (spectralAddValuation K L b hb) =
      f.newtonPolygon v :=
  f.newtonPolygon_map v (algebraMap K L) (v.spectralAddValuation_algebraMap_eq hb hv)

end PowerSeries

namespace Polynomial

section SpectralAddValuation

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Mapping a polynomial from `K` to an algebraic extension `L` equipped with
`TauCeti.spectralAddValuation K L b hb` preserves its Newton polygon. -/
theorem newtonPolygon_map_spectralAddValuation (f : K[X])
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) :
    (f.map (algebraMap K L)).newtonPolygon (spectralAddValuation K L b hb) =
      f.newtonPolygon v :=
  f.newtonPolygon_map v (algebraMap K L) (v.spectralAddValuation_algebraMap_eq hb hv)

/-- Mapping a polynomial from `K` to an algebraic extension `L` equipped with
`TauCeti.spectralAddValuation K L b hb` preserves its finite slope multiset. -/
theorem newtonSlopes_map_spectralAddValuation (f : K[X])
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) :
    (f.map (algebraMap K L)).newtonSlopes (spectralAddValuation K L b hb) =
      f.newtonSlopes v :=
  f.newtonSlopes_map v (algebraMap K L) (v.spectralAddValuation_algebraMap_eq hb hv)

/-- If `f : K[X]` splits in an algebraic extension `L` of `K`, its finite slope multiset equals the
multiset of negated `TauCeti.spectralAddValuation` values of its nonzero roots in `L`. -/
theorem newtonSlopes_eq_map_roots_map_spectralAddValuation [DecidableEq L]
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      -(spectralAddValuation K L b hb α).untop₀ :=
  newtonSlopes_eq_map_roots_map (fun _ ↦ (spectralAddValuation K L b hb).top_iff.mp)
    (algebraMap K L) (v.spectralAddValuation_algebraMap_eq hb hv) hf

end SpectralAddValuation

section SingleRoot

universe u

variable {K : Type*} {L : Type u} [NormedField K] [CompleteSpace K] [Field L] [Algebra K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- Transfer a predicate on the norm of a root of nonzero `f : K[X]` in a normed `K`-algebra field
extension to `spectralNorm K L x` for a root `x` in an arbitrary field extension `L`, by descending
to the finite extension `K⟮x⟯` equipped with `TauCeti.spectralNormedField`. -/
private theorem spectralNorm_prop_of_aeval_eq_zero {P : ℝ → Prop} {f : K[X]} (hf : f ≠ 0) {x : L}
    (hx : aeval x f = 0)
    (h : ∀ (E : Type u) [NormedField E] [NormedAlgebra K E] (y : E),
      (x ≠ 0 → y ≠ 0) → aeval y f = 0 → P ‖y‖) :
    P (spectralNorm K L x) := by
  have hgen : aeval (IntermediateField.AdjoinSimple.gen K x) f = 0 :=
    ZeroMemClass.coe_eq_zero.mp (by rwa [IntermediateField.AdjoinSimple.coe_aeval_gen_apply])
  have hgen0 : x ≠ 0 → IntermediateField.AdjoinSimple.gen K x ≠ 0 := fun hx0 h0 ↦
    hx0 (by simpa using congrArg (algebraMap K⟮x⟯ L) h0)
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hx_int : IsIntegral K x := isAlgebraic_iff_isIntegral.mp ⟨f, hf, hx⟩
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx_int
  let := spectralNormedField K K⟮x⟯
  let := spectralNormedAlgebra K K⟮x⟯
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x, ← spectralNorm.eq_of_tower,
    ← norm_spectralNormedField]
  exact h K⟮x⟯ (IntermediateField.AdjoinSimple.gen K x) hgen0 hgen

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, every root `x` of a nonzero polynomial
`f : K[X]` pure of slope `m` in any field extension `L` of `K` satisfies
`spectralNorm K L x ≤ b ^ m`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is needed. -/
theorem spectralNorm_le_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx : aeval x f = 0) :
    spectralNorm K L x ≤ b ^ m :=
  spectralNorm_prop_of_aeval_eq_zero (P := (· ≤ b ^ m)) v hb hv hf hx fun _ _ _ _ _ hy ↦
    norm_le_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf hm hy

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, every nonzero root `x` of a nonzero
polynomial `f : K[X]` pure of slope `m` in any field extension `L` of `K` has
`spectralNorm K L x = b ^ m`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is needed. -/
theorem spectralNorm_eq_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx0 : x ≠ 0) (hx : aeval x f = 0) :
    spectralNorm K L x = b ^ m :=
  spectralNorm_prop_of_aeval_eq_zero (P := (· = b ^ m)) v hb hv hf hx fun _ _ _ _ hy0 hy ↦
    norm_eq_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf hm (hy0 hx0) hy

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, for any nonzero root `α` of a nonzero
polynomial `f : K[X]` in any field extension `L` of `K`, `Real.logb b (spectralNorm K L α)` is one
of the finite slopes `f.newtonSlopes v`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is
needed. -/
theorem logb_spectralNorm_mem_newtonSlopes_of_aeval_eq_zero {f : K[X]} (hf : f ≠ 0) {α : L}
    (hα : α ≠ 0) (hx : aeval α f = 0) :
    Real.logb b (spectralNorm K L α) ∈ f.newtonSlopes v :=
  spectralNorm_prop_of_aeval_eq_zero (P := (Real.logb b · ∈ f.newtonSlopes v)) v hb hv hf hx
    fun _ _ _ _ hy0 hy ↦ logb_norm_mem_newtonSlopes_of_aeval_eq_zero v hb hv hf (hy0 hα) hy

end SingleRoot

section Splits

universe u

variable {K : Type*} {L : Type u} [NormedField K] [CompleteSpace K]
  [Field L] [Algebra K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- Descend a polynomial `f : K[X]` splitting in an arbitrary field extension `L` to its
finite-dimensional splitting intermediate field `E = K(rootSet f L)` equipped with
`TauCeti.spectralNormedField` and `TauCeti.spectralNormedAlgebra`. -/
private theorem of_splits_adjoin_rootSet {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {P : Prop}
    (h : ∀ (E : Type u) [NormedField E] [NormedAlgebra K E] (ι : E →+* L),
      (f.map (algebraMap K E)).Splits →
      (f.map (algebraMap K L)).roots = (f.map (algebraMap K E)).roots.map ι →
      (∀ α : E, spectralNorm K L (ι α) = ‖α‖) → P) : P := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  set E := IntermediateField.adjoin K (f.rootSet L)
  have : f.IsSplittingField K E := IntermediateField.adjoin_rootSet_isSplittingField hf
  have : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
  have hfE : (f.map (algebraMap K E)).Splits := IsSplittingField.splits E f
  let := spectralNormedField K E
  let := spectralNormedAlgebra K E
  refine h E (algebraMap E L) hfE ?_ fun α ↦ ?_
  · rw [IsScalarTower.algebraMap_eq K E L, ← Polynomial.map_map, hfE.roots_map]
  · rw [← spectralNorm.eq_of_tower (K := K) (E := E) (L := L) α, norm_spectralNormedField]

/-- Transfer a spectral-norm root count for a polynomial `f : K[X]` splitting in `L` from its
finite splitting field `E` equipped with the spectral norm. -/
private theorem card_filter_roots_map_spectralNorm_of_norm {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) (P : ℝ → Prop) [DecidablePred P] {n : ℕ}
    (h : ∀ (E : Type u) [NormedField E] [NormedAlgebra K E],
      (f.map (algebraMap K E)).Splits →
      ((f.map (algebraMap K E)).roots.filter fun α ↦ P ‖α‖).card = n) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ P (spectralNorm K L α)).card = n :=
  of_splits_adjoin_rootSet v hb hv hf fun E _ _ ι hfE hroots hnorm ↦ by
    rw [hroots, Multiset.filter_map, Multiset.card_map]
    simpa only [Function.comp_def, hnorm] using h E hfE

/-- If `f : K[X]` splits in a field extension `L` of complete `K`, its finite slope multiset
`f.newtonSlopes v` equals the multiset of `Real.logb b (spectralNorm K L α)` over its nonzero roots
`α` in `L`, counted with multiplicity. -/
theorem newtonSlopes_eq_map_roots_map_spectralNorm [DecidableEq L] {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      Real.logb b (spectralNorm K L α) := by
  refine of_splits_adjoin_rootSet v hb hv hf fun E _ _ ι hfE hroots hnorm ↦ ?_
  classical
  rw [newtonSlopes_eq_map_roots_map_norm (L := E) v hb hv hfE, hroots, Multiset.filter_map,
    Multiset.map_map]
  refine Multiset.map_congr ?_ fun α _ ↦ by simp only [Function.comp_def, hnorm]
  exact Multiset.filter_congr fun α _ ↦ by
    simp only [Function.comp_def, map_ne_zero_iff ι ι.injective]

/-- If `f : K[X]` splits in a field extension `L` of complete `K` and every nonzero root of `f`
in `L` has spectral norm `b ^ m`, then every finite slope of `f` equals `m`. -/
theorem newtonSlopes_eq_replicate_of_spectralNorm_eq {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) {m : ℝ}
    (hm : ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m) :
    f.newtonSlopes v = Multiset.replicate (f.natDegree - f.natTrailingDegree) m :=
  of_splits_adjoin_rootSet v hb hv hf fun E _ _ ι hfE hroots hnorm ↦
    newtonSlopes_eq_replicate_of_norm_eq (L := E) v hb hv hfE fun α hα hα0 ↦ by
      rw [← hnorm α]
      exact hm (ι α) (hroots ▸ Multiset.mem_map_of_mem ι hα)
        ((map_ne_zero_iff ι ι.injective).2 hα0)

/-- When `f : K[X]` splits in a field extension `L` of complete `K`, every finite slope of `f`
equals `m` if and only if every nonzero root of `f` in `L` has spectral norm `b ^ m`. -/
theorem forall_mem_newtonSlopes_eq_iff_spectralNorm_eq {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m := by
  refine of_splits_adjoin_rootSet v hb hv hf fun E _ _ ι hfE hroots hnorm ↦ ?_
  rw [forall_mem_newtonSlopes_eq_iff_norm_eq (L := E) v hb hv hfE, hroots]
  constructor
  · intro h _ hα hα0
    obtain ⟨α, hα', rfl⟩ := Multiset.mem_map.1 hα
    rw [hnorm α]
    exact h α hα' ((map_ne_zero_iff ι ι.injective).1 hα0)
  · intro h α hα hα0
    rw [← hnorm α]
    exact h (ι α) (Multiset.mem_map_of_mem ι hα) ((map_ne_zero_iff ι ι.injective).2 hα0)

/-- If `f : K[X]` splits in a field extension `L` of complete `K`, the left endpoint `l` of
the finite face of slope `σ` counts the roots `α` of `f` in `L` in the open spectral ball
`spectralNorm K L α < b ^ σ`, counted with multiplicity and including the root zero. -/
theorem card_filter_roots_map_spectralNorm_lt {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α < b ^ σ).card = l :=
  card_filter_roots_map_spectralNorm_of_norm v hb hv hf (· < b ^ σ) fun E _ _ hfE ↦
    card_filter_roots_map_norm_lt (L := E) v hb hv hfE hface

/-- If `f : K[X]` splits in a field extension `L` of complete `K`, the right endpoint `u` of
the finite face of slope `σ` counts the roots `α` of `f` in `L` in the closed spectral ball
`spectralNorm K L α ≤ b ^ σ`, counted with multiplicity and including the root zero. -/
theorem card_filter_roots_map_spectralNorm_le {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α ≤ b ^ σ).card = u :=
  card_filter_roots_map_spectralNorm_of_norm v hb hv hf (· ≤ b ^ σ) fun E _ _ hfE ↦
    card_filter_roots_map_norm_le (L := E) v hb hv hfE hface

/-- If `f : K[X]` splits in a field extension `L` of complete `K`, the horizontal width
`u - l` of the finite face of slope `σ` counts the roots `α` of `f` in `L` on the spectral sphere
`spectralNorm K L α = b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_map_spectralNorm_eq {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α = b ^ σ).card = u - l :=
  card_filter_roots_map_spectralNorm_of_norm v hb hv hf (· = b ^ σ) fun E _ _ hfE ↦
    card_filter_roots_map_norm_eq (L := E) v hb hv hfE hface

end Splits

section IsAlgClosed

variable {K : Type*} [NormedField K] [CompleteSpace K]
  (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Slope-root dictionary in an algebraically closed extension**: in any algebraically closed
extension `L` of complete `K` (such as `AlgebraicClosure K`, `PadicAlgCl p`, or `ℂ_[p]`), the
finite slope multiset `f.newtonSlopes v` of any polynomial `f : K[X]` is the multiset of
`Real.logb b (spectralNorm K L α)` over its nonzero roots `α` in `L`, with no splitting assumption
on `f`. -/
theorem newtonSlopes_eq_map_roots_map_spectralNorm_of_isAlgClosed [DecidableEq L] (f : K[X]) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      Real.logb b (spectralNorm K L α) :=
  newtonSlopes_eq_map_roots_map_spectralNorm v hb hv (IsAlgClosed.splits (f.map (algebraMap K L)))

/-- In any algebraically closed algebraic extension `L` of `K` (for example `AlgebraicClosure K`),
the finite slope multiset of any polynomial `f : K[X]` equals the multiset of negated
`TauCeti.spectralAddValuation` values of its nonzero roots in `L`, with no splitting hypothesis. -/
theorem newtonSlopes_eq_map_roots_map_spectralAddValuation_of_isAlgClosed [IsUltrametricDist K]
    [Algebra.IsAlgebraic K L] [DecidableEq L] (f : K[X]) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      -(spectralAddValuation K L b hb α).untop₀ :=
  newtonSlopes_eq_map_roots_map_spectralAddValuation v hb hv
    (IsAlgClosed.splits (f.map (algebraMap K L)))

/-- In any algebraically closed extension `L` of complete `K`, every finite slope of
`f : K[X]` equals `m` if and only if every nonzero root of `f` in `L` has spectral norm `b ^ m`. -/
theorem forall_mem_newtonSlopes_eq_iff_spectralNorm_eq_of_isAlgClosed (f : K[X]) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m :=
  forall_mem_newtonSlopes_eq_iff_spectralNorm_eq v hb hv
    (IsAlgClosed.splits (f.map (algebraMap K L)))

/-- In any algebraically closed extension `L` of complete `K`, the left endpoint `l` of
the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f` in `L`
with `spectralNorm K L α < b ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_map_spectralNorm_lt_of_isAlgClosed {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α < b ^ σ).card = l :=
  card_filter_roots_map_spectralNorm_lt v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

/-- In any algebraically closed extension `L` of complete `K`, the right endpoint `u` of
the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f` in `L`
with `spectralNorm K L α ≤ b ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_map_spectralNorm_le_of_isAlgClosed {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α ≤ b ^ σ).card = u :=
  card_filter_roots_map_spectralNorm_le v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

/-- In any algebraically closed extension `L` of complete `K`, the horizontal width
`u - l` of the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f`
in `L` with `spectralNorm K L α = b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_map_spectralNorm_eq_of_isAlgClosed {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α = b ^ σ).card = u - l :=
  card_filter_roots_map_spectralNorm_eq v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

end IsAlgClosed

end Polynomial
