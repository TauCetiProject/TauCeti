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

/-!
# Newton polygons, spectral norms, and roots in algebraic extensions

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
* In any algebraic extension `L` in which `f` splits — and unconditionally in any algebraically
  closed algebraic extension `L` of `K` such as `AlgebraicClosure K` — `f.newtonSlopes v` equals
  the multiset of `Real.logb b (spectralNorm K L α)` (equivalently
  `-(TauCeti.spectralAddValuation K L b hb α).untop₀`) over nonzero roots `α` in `L`, and the
  endpoints and width of the finite face of slope `σ` count the roots of `f` in `L` in the open
  ball `spectralNorm K L α < b ^ σ`, closed ball `spectralNorm K L α ≤ b ^ σ`, and sphere
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
  when `f` splits in an algebraic extension `L`.
* `Polynomial.newtonSlopes_eq_map_roots_spectralNorm`,
  `Polynomial.newtonSlopes_eq_map_roots_spectralAddValuation`,
  `Polynomial.card_filter_roots_spectralNorm_lt`,
  `Polynomial.card_filter_roots_spectralNorm_le`, and
  `Polynomial.card_filter_roots_spectralNorm_eq`: unconditional slope-root and ball-count
  dictionary in any algebraically closed algebraic extension `L` of `K` (such as
  `AlgebraicClosure K` or `PadicAlgCl p`), with no splitting assumption on `f`.

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
  f.newtonPolygon_map v (algebraMap K L) (spectralAddValuation_algebraMap_eq v hb hv)

end PowerSeries

namespace Polynomial

section SpectralAddValuation

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hv

/-- Mapping a polynomial from `K` to an algebraic extension `L` equipped with
`TauCeti.spectralAddValuation K L b hb` preserves its Newton polygon. -/
theorem newtonPolygon_map_spectralAddValuation (f : K[X]) :
    (f.map (algebraMap K L)).newtonPolygon (spectralAddValuation K L b hb) =
      f.newtonPolygon v :=
  f.newtonPolygon_map v (algebraMap K L) (spectralAddValuation_algebraMap_eq v hb hv)

/-- Mapping a polynomial from `K` to an algebraic extension `L` equipped with
`TauCeti.spectralAddValuation K L b hb` preserves its finite slope multiset. -/
theorem newtonSlopes_map_spectralAddValuation (f : K[X]) :
    (f.map (algebraMap K L)).newtonSlopes (spectralAddValuation K L b hb) =
      f.newtonSlopes v :=
  f.newtonSlopes_map v (algebraMap K L) (spectralAddValuation_algebraMap_eq v hb hv)

/-- If `f : K[X]` splits in an algebraic extension `L` of `K`, its finite slope multiset equals the
multiset of negated `TauCeti.spectralAddValuation` values of its nonzero roots in `L`. -/
theorem newtonSlopes_eq_map_roots_map_spectralAddValuation [DecidableEq L] {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      -(spectralAddValuation K L b hb α).untop₀ :=
  newtonSlopes_eq_map_roots_map (fun _ ↦ (spectralAddValuation K L b hb).top_iff.mp)
    (algebraMap K L) (spectralAddValuation_algebraMap_eq v hb hv) hf

/-- In any algebraically closed algebraic extension `L` of `K` (for example `AlgebraicClosure K`),
the finite slope multiset of any polynomial `f : K[X]` equals the multiset of negated
`TauCeti.spectralAddValuation` values of its nonzero roots in `L`, with no splitting hypothesis. -/
theorem newtonSlopes_eq_map_roots_spectralAddValuation (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsAlgClosed L] [DecidableEq L] (f : K[X]) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      -(spectralAddValuation K L b hb α).untop₀ :=
  newtonSlopes_eq_map_roots_map_spectralAddValuation v hb hv
    (IsAlgClosed.splits (f.map (algebraMap K L)))

end SpectralAddValuation

section SingleRoot

variable {K L : Type*} [NormedField K] [CompleteSpace K] [Field L] [Algebra K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, every root `x` of a nonzero polynomial
`f : K[X]` pure of slope `m` in any field extension `L` of `K` satisfies
`spectralNorm K L x ≤ b ^ m`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is needed. -/
theorem spectralNorm_le_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx : aeval x f = 0) :
    spectralNorm K L x ≤ b ^ m := by
  have hgen : aeval (IntermediateField.AdjoinSimple.gen K x) f = 0 :=
    ZeroMemClass.coe_eq_zero.mp (by rwa [IntermediateField.AdjoinSimple.coe_aeval_gen_apply])
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hx_int : IsIntegral K x := isAlgebraic_iff_isIntegral.mp ⟨f, hf, hx⟩
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx_int
  let := spectralNormedField K K⟮x⟯
  let := spectralNormedAlgebra K K⟮x⟯
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x, ← spectralNorm.eq_of_tower]
  exact norm_le_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf hm hgen

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, every nonzero root `x` of a nonzero
polynomial `f : K[X]` pure of slope `m` in any field extension `L` of `K` has
`spectralNorm K L x = b ^ m`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is needed. -/
theorem spectralNorm_eq_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx0 : x ≠ 0) (hx : aeval x f = 0) :
    spectralNorm K L x = b ^ m := by
  have hgen : aeval (IntermediateField.AdjoinSimple.gen K x) f = 0 :=
    ZeroMemClass.coe_eq_zero.mp (by rwa [IntermediateField.AdjoinSimple.coe_aeval_gen_apply])
  have hgen0 : IntermediateField.AdjoinSimple.gen K x ≠ 0 := fun h ↦
    hx0 (by simpa using congrArg (algebraMap K⟮x⟯ L) h)
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hx_int : IsIntegral K x := isAlgebraic_iff_isIntegral.mp ⟨f, hf, hx⟩
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx_int
  let := spectralNormedField K K⟮x⟯
  let := spectralNormedAlgebra K K⟮x⟯
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x, ← spectralNorm.eq_of_tower]
  exact norm_eq_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf hm hgen0 hgen

/-- Over a complete field `K` with `‖x‖ = b ^ (-v x)`, for any nonzero root `α` of a nonzero
polynomial `f : K[X]` in any field extension `L` of `K`, `Real.logb b (spectralNorm K L α)` is one
of the finite slopes `f.newtonSlopes v`. Neither `[Algebra.IsAlgebraic K L]` nor splitting is
needed. -/
theorem logb_spectralNorm_mem_newtonSlopes_of_aeval_eq_zero {f : K[X]} (hf : f ≠ 0) {α : L}
    (hα : α ≠ 0) (hx : aeval α f = 0) :
    Real.logb b (spectralNorm K L α) ∈ f.newtonSlopes v := by
  have hgen : aeval (IntermediateField.AdjoinSimple.gen K α) f = 0 :=
    ZeroMemClass.coe_eq_zero.mp (by rwa [IntermediateField.AdjoinSimple.coe_aeval_gen_apply])
  have hgen0 : IntermediateField.AdjoinSimple.gen K α ≠ 0 := fun h ↦
    hα (by simpa using congrArg (algebraMap K⟮α⟯ L) h)
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hα_int : IsIntegral K α := isAlgebraic_iff_isIntegral.mp ⟨f, hf, hx⟩
  have : FiniteDimensional K K⟮α⟯ := IntermediateField.adjoin.finiteDimensional hα_int
  let := spectralNormedField K K⟮α⟯
  let := spectralNormedAlgebra K K⟮α⟯
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen K α, ← spectralNorm.eq_of_tower]
  exact logb_norm_mem_newtonSlopes_of_aeval_eq_zero v hb hv hf hgen0 hgen

end SingleRoot

section AlgebraicExtension

variable {K L : Type*} [NormedField K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- If `f : K[X]` splits in an algebraic extension `L` of complete `K`, its finite slope multiset
`f.newtonSlopes v` equals the multiset of `Real.logb b (spectralNorm K L α)` over its nonzero roots
`α` in `L`, counted with multiplicity. -/
theorem newtonSlopes_eq_map_roots_map_spectralNorm [DecidableEq L] {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      Real.logb b (spectralNorm K L α) := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  rw [newtonSlopes_eq_map_roots_map_spectralAddValuation v hb hv hf]
  exact Multiset.map_congr rfl fun α _ ↦ by rw [untop₀_spectralAddValuation, neg_neg]

/-- If `f : K[X]` splits in an algebraic extension `L` of complete `K` and every nonzero root of `f`
in `L` has spectral norm `b ^ m`, then every finite slope of `f` equals `m`. -/
theorem newtonSlopes_eq_replicate_of_spectralNorm_eq {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) {m : ℝ}
    (hm : ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m) :
    f.newtonSlopes v = Multiset.replicate (f.natDegree - f.natTrailingDegree) m := by
  classical
  rw [← card_newtonSlopes f v (fun _ ↦ v.top_iff.mp), Multiset.eq_replicate_card,
    newtonSlopes_eq_map_roots_map_spectralNorm v hb hv hf]
  intro s hs
  obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hs
  rw [Multiset.mem_filter] at hα
  rw [hm α hα.1 hα.2, Real.logb_rpow (zero_lt_one.trans hb) hb.ne']

/-- When `f : K[X]` splits in an algebraic extension `L` of complete `K`, every finite slope of `f`
equals `m` if and only if every nonzero root of `f` in `L` has spectral norm `b ^ m`. -/
theorem forall_mem_newtonSlopes_eq_iff_spectralNorm_eq {f : K[X]}
    (hf : (f.map (algebraMap K L)).Splits) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  refine ⟨fun hm α hα hα0 ↦ ?_, fun hm s hs ↦ ?_⟩
  · refine spectralNorm_eq_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf0 hm hα0 ?_
    rw [← eval_map_algebraMap]
    exact isRoot_of_mem_roots hα
  · rw [newtonSlopes_eq_replicate_of_spectralNorm_eq v hb hv hf hm] at hs
    exact Multiset.eq_of_mem_replicate hs

/-- If `f : K[X]` splits in an algebraic extension `L` of complete `K`, the left endpoint `l` of
the finite face of slope `σ` counts the roots `α` of `f` in `L` in the open spectral ball
`spectralNorm K L α < b ^ σ`, counted with multiplicity and including the root zero. -/
theorem card_filter_roots_map_spectralNorm_lt {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α < b ^ σ).card = l := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hfaceL : IsFiniteFace
      ((f.map (algebraMap K L)).newtonPolygon (spectralAddValuation K L b hb)) σ l u := by
    rwa [newtonPolygon_map_spectralAddValuation v hb hv]
  rw [← card_filter_roots_lt_addValuation
    (fun _ ↦ (spectralAddValuation K L b hb).top_iff.mp) hf hfaceL]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [coe_lt_spectralAddValuation_iff hb, neg_neg]

/-- If `f : K[X]` splits in an algebraic extension `L` of complete `K`, the right endpoint `u` of
the finite face of slope `σ` counts the roots `α` of `f` in `L` in the closed spectral ball
`spectralNorm K L α ≤ b ^ σ`, counted with multiplicity and including the root zero. -/
theorem card_filter_roots_map_spectralNorm_le {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α ≤ b ^ σ).card = u := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hfaceL : IsFiniteFace
      ((f.map (algebraMap K L)).newtonPolygon (spectralAddValuation K L b hb)) σ l u := by
    rwa [newtonPolygon_map_spectralAddValuation v hb hv]
  rw [← card_filter_roots_le_addValuation
    (fun _ ↦ (spectralAddValuation K L b hb).top_iff.mp) hf hfaceL]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [coe_le_spectralAddValuation_iff hb, neg_neg]

/-- If `f : K[X]` splits in an algebraic extension `L` of complete `K`, the horizontal width
`u - l` of the finite face of slope `σ` counts the roots `α` of `f` in `L` on the spectral sphere
`spectralNorm K L α = b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_map_spectralNorm_eq {f : K[X]} (hf : (f.map (algebraMap K L)).Splits)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α = b ^ σ).card = u - l := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  have hfaceL : IsFiniteFace
      ((f.map (algebraMap K L)).newtonPolygon (spectralAddValuation K L b hb)) σ l u := by
    rwa [newtonPolygon_map_spectralAddValuation v hb hv]
  rw [← card_filter_roots_addValuation_eq
    (fun _ ↦ (spectralAddValuation K L b hb).top_iff.mp) hf hfaceL]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [spectralAddValuation_eq_coe_iff hb, neg_neg]

end AlgebraicExtension

section IsAlgClosed

variable {K : Type*} [NormedField K] [CompleteSpace K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Slope-root dictionary in an algebraic closure**: in any algebraically closed algebraic
extension `L` of complete `K` (such as `AlgebraicClosure K` or `PadicAlgCl p`), the finite slope
multiset `f.newtonSlopes v` of any polynomial `f : K[X]` is the multiset of
`Real.logb b (spectralNorm K L α)` over its nonzero roots `α` in `L`, with no splitting assumption
on `f`. -/
theorem newtonSlopes_eq_map_roots_spectralNorm [DecidableEq L] (f : K[X]) :
    f.newtonSlopes v = ((f.map (algebraMap K L)).roots.filter (· ≠ 0)).map fun α ↦
      Real.logb b (spectralNorm K L α) :=
  newtonSlopes_eq_map_roots_map_spectralNorm v hb hv (IsAlgClosed.splits (f.map (algebraMap K L)))

/-- In any algebraically closed algebraic extension `L` of complete `K`, every finite slope of
`f : K[X]` equals `m` if and only if every nonzero root of `f` in `L` has spectral norm `b ^ m`. -/
theorem forall_mem_newtonSlopes_eq_iff_isAlgClosed_spectralNorm_eq (f : K[X]) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ∀ α ∈ (f.map (algebraMap K L)).roots, α ≠ 0 → spectralNorm K L α = b ^ m :=
  forall_mem_newtonSlopes_eq_iff_spectralNorm_eq v hb hv
    (IsAlgClosed.splits (f.map (algebraMap K L)))

/-- In any algebraically closed algebraic extension `L` of complete `K`, the left endpoint `l` of
the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f` in `L`
with `spectralNorm K L α < b ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_spectralNorm_lt {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α < b ^ σ).card = l :=
  card_filter_roots_map_spectralNorm_lt v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

/-- In any algebraically closed algebraic extension `L` of complete `K`, the right endpoint `u` of
the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f` in `L`
with `spectralNorm K L α ≤ b ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_spectralNorm_le {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α ≤ b ^ σ).card = u :=
  card_filter_roots_map_spectralNorm_le v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

/-- In any algebraically closed algebraic extension `L` of complete `K`, the horizontal width
`u - l` of the finite face of slope `σ` of `f.newtonPolygon v` equals the number of roots `α` of `f`
in `L` with `spectralNorm K L α = b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_spectralNorm_eq {f : K[X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.map (algebraMap K L)).roots.filter fun α ↦ spectralNorm K L α = b ^ σ).card = u - l :=
  card_filter_roots_map_spectralNorm_eq v hb hv (IsAlgClosed.splits (f.map (algebraMap K L))) hface

end IsAlgClosed

end Polynomial
