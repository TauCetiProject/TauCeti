/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens

/-!
# Local vector-valued Sobolev classes

`TauCeti.MemWkpLoc p U k f μ` requires iterated weak derivatives through order `k` on
`interior U` relative to `μ`, with `Lᵖ(μ)` bounds on every compact subset of `U` itself, in the
sense of `TauCeti.MemLpLoc`, on an arbitrary real normed space `E` and for any real normed codomain
`F`. The measure `μ` defaults to `volume` when a `MeasureSpace` instance is available.

For non-open domains such as half-discs reaching a boundary hyperplane, the `Lᵖ` bounds hold on
compact subsets touching the boundary, while weak-derivative test functions stay inside
`interior U`. On open subsets of a finite-dimensional real normed space equipped with an additive
Haar measure, this is the usual local Sobolev class `W^{k,p}_loc(Ω; F)`. Derivatives
take values in iterated continuous linear maps rather than scalar jets, and no basis or separability
of the codomain `F` is assumed. The predicates concern actual functions, are invariant under
almost-everywhere modifications on `U`, and impose no global integrability condition on possibly
unbounded domains.

This file supplies:
* restriction to smaller sets (`MemWkpLoc.mono`) and almost-everywhere invariance
  (`MemWkpLoc.congr_ae`, `MemWkpLoc.congr_mono`, `MemWkpLoc.congr`);
* linearity, scalar multiplication, multiplication of a fixed vector by a scalar map
  (`MemWkpLoc.smul_const`), continuous-linear postcomposition, pairing of maps and operator fields,
  and continuous-linear change of codomain;
* decreasing the integrability exponent (`MemWkpLoc.mono_exponent`) and decreasing the derivative
  order (`MemWkpLoc.of_succ`, `MemWkpLoc.of_le`);
* uniqueness-of-weak-derivative consequences (`MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn`,
  `MemWkpLoc.memLpLoc_of_hasWeakFDerivOn`), first-order characterization for continuous functions
  (`ContinuousOn.memWkpLoc_one_iff`), classical differentiability criterion
  (`memWkpLoc_one_of_differentiableOn`), `Cᵏ` membership (`ContDiffOn.memWkpLoc`,
  `ContDiff.memWkpLoc`, `ContinuousLinearMap.memWkpLoc_affine`), and identification of derivatives
  of `Cᵏ` representatives on sets agreeing almost everywhere with their interior
  (`MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, `MemWkpLoc.iteratedFDeriv_of_contDiffOn`);
* `TauCeti.WeakDerivChainLe`, comparing the `Lᵖ` norms of two maps and recursively every pair of
  their weak derivatives through a given order.

In positive order, completeness of the codomain is inherited from `TauCeti.HasWeakFDerivOn`; the
definitions admit every real normed codomain without an additional typeclass assumption.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3 (first-order Bochner Sobolev spaces).
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Local Sobolev classes `MemWkpLoc` -/

section MemWkpLoc

universe u v w

/-- Auxiliary recursion for `TauCeti.MemWkpLoc` whose codomain lies in `Type max u v`, so iterated
operator spaces `E →L[ℝ] F` stay in the same universe. -/
private def memWkpLocAux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f μ
  | k + 1, F, _, _, f => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ memWkpLocAux μ p U k D

private theorem memWkpLocAux_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ}
    {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} :
    memWkpLocAux.{u, v} μ p U k f ↔ memWkpLocAux.{u, max u v} μ p U k f := by
  induction k generalizing F with
  | zero => exact Iff.rfl
  | succ k ih =>
    exact and_congr_right fun _ => exists_congr fun D =>
      and_congr_right fun _ => ih (F := E →L[ℝ] F) (f := D)

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E} {p q : ℝ≥0∞} {U V : Set E} {Ω : Opens E} {k l : ℕ} {f g : E → F}

/-- The iterated weak derivatives through order `k` exist on `interior U` relative to `μ` and are
`Lᵖ(μ)` on every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `E →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ℝ≥0∞) (U : Set E) (k : ℕ) (f : E → F)
    (μ : Measure E := by volume_tac) : Prop :=
  match k with
  | 0 => MemLpLoc p U f μ
  | k + 1 => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
        memWkpLocAux.{u, v} μ p U k D

private theorem memWkpLoc_iff_aux {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} :
    MemWkpLoc.{u, max u v} p U k f μ ↔ memWkpLocAux.{u, v} μ p U k f := by
  cases k with
  | zero => exact Iff.rfl
  | succ k =>
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
      (memWkpLocAux_univ.{u, v}).symm

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f μ ↔ MemLpLoc p U f μ := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f μ ↔ MemLpLoc p U f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ :=
  and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (memWkpLoc_iff_aux.{u, v}).symm

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f μ ↔ MemLpLoc p Ω f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- For a continuous function, the `MemLpLoc` condition on the function itself is automatic, so
membership in `W^{1,p}_loc(U; F)` is equivalent to having a weak derivative on `interior U` in
`MemLpLoc p U`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) :
    MemWkpLoc p U 1 f μ ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemLpLoc p U D μ := by
  simp only [memWkpLoc_succ_iff, memWkpLoc_zero_iff, hf.memLpLoc, true_and]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f μ) : MemLpLoc p U f μ := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ := (memWkpLoc_succ_iff.1 hf).2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f μ) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

private theorem memWkpLoc_mono_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U k f μ) (hVU : V ⊆ U) : MemWkpLoc p V k f μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_set hVU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f μ) (hVU : V ⊆ U) :
    MemWkpLoc p V k f μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_set hVU
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2
      ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), memWkpLoc_mono_max hk hVU⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemWkpLoc p U k g μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set μ interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) : MemWkpLoc p V k g μ := by
  cases k with
  | zero => exact MemLpLoc.congr_mono (memWkpLoc_zero_iff.1 hf) hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := memWkpLoc_succ_iff.1 (hf.mono hVU)
    exact memWkpLoc_succ_iff.2 ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f U) : MemWkpLoc p U k g μ :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω (k + 1) f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemWkpLoc p Ω k D μ := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω 1 f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemLpLoc p Ω D μ :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

private theorem memWkpLoc_mono_exponent_max [IsFiniteMeasureOnCompacts μ] {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ)
    (hqp : q ≤ p) : MemWkpLoc q U k f μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_exponent hqp
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemWkpLoc p U k f μ)
    (hqp : q ≤ p) : MemWkpLoc q U k f μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_exponent hqp
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, memWkpLoc_mono_exponent_max hk hqp⟩

private theorem memWkpLoc_of_succ_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U (k + 1) f μ) : MemWkpLoc p U k f μ := by
  induction k generalizing F with
  | zero => exact hf.memLpLoc
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f μ) : MemWkpLoc p U k f μ := by
  cases k with
  | zero => exact hf.memLpLoc
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, memWkpLoc_of_succ_max hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f μ) (hlk : l ≤ k) : MemWkpLoc p U l f μ := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

private theorem memWkpLoc_zero_fun_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) μ := by
  induction k generalizing F with
  | zero => exact memLpLoc_zero
  | succ k ih => exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) μ := by
  cases k with
  | zero => exact memLpLoc_zero
  | succ k =>
    exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, memWkpLoc_zero_fun_max⟩

private theorem memWkpLoc_add_max [OpensMeasurableSpace E] {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f + g) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).add (memWkpLoc_zero_iff.1 hg)
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f + g) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).add (memWkpLoc_zero_iff.1 hg)
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', memWkpLoc_add_max hk hk'⟩

private theorem memWkpLoc_neg_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k (-f) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).neg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k (-f) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).neg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, memWkpLoc_neg_max hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f - g) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem memWkpLoc_const_smul_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ) (c : ℝ) :
    MemWkpLoc p U k (c • f) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).const_smul c
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f μ) (c : ℝ) :
    MemWkpLoc p U k (c • f) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).const_smul c
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c,
      memWkpLoc_const_smul_max hk c⟩

private theorem memWkpLoc_clm_comp_max [OpensMeasurableSpace E] {F : Type max u v}
    {G : Type max u w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {f : E → F} (hf : MemWkpLoc p U k f μ) (A : F →L[ℝ] G) :
    MemWkpLoc p U k (fun z => A (f z)) μ := by
  induction k generalizing F G with
  | zero => exact (memWkpLoc_zero_iff.1 hf).clm_comp A
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      ih hk ((ContinuousLinearMap.compL ℝ E F G) A)⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hf : MemWkpLoc p U k f μ)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).clm_comp A
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      memWkpLoc_clm_comp_max hk ((ContinuousLinearMap.compL ℝ E F G) A)⟩

/-- Multiplying a fixed vector in a Banach space by a scalar local Sobolev function preserves
every local Sobolev class, with no basis of the codomain required. -/
theorem MemWkpLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemWkpLoc p U k a μ) (v : F) :
    MemWkpLoc p U k (fun z => a z • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G] {g : E → G}
    (hf : MemWkpLoc p U k f μ) (hg : MemWkpLoc p U k g μ) :
    MemWkpLoc p U k (fun z => (f z, g z)) μ := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap [OpensMeasurableSpace E] {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    [CompleteSpace E₄] {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A μ)
    (hB : MemWkpLoc p U k B μ) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) μ := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff [OpensMeasurableSpace E] (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) μ ↔ MemWkpLoc p U k f μ := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f) (μ := μ))
  | succ k =>
    constructor
    · intro h
      have : CompleteSpace G := h.completeSpace
      have : CompleteSpace F :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
        h.clm_comp e.symm.toContinuousLinearMap
    · intro h
      have : CompleteSpace F := h.completeSpace
      have : CompleteSpace G :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance
      exact h.clm_comp e.toContinuousLinearMap

/-- Constant functions belong to every local Sobolev class, for any additive Haar measure on a
finite-dimensional domain. -/
@[simp]
theorem memWkpLoc_const [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (c : F) : MemWkpLoc p U k (fun _ => c) μ := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine memWkpLoc_succ_iff.2 ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := μ) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum [OpensMeasurableSpace E] {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i) μ) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F) (μ := μ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A function differentiable at every point of an open set `Ω` with locally `Lᵖ` Fréchet
derivative lies in `W^{1,p}_loc(Ω; F)` whenever `1 ≤ p`. -/
theorem memWkpLoc_one_of_differentiableOn [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (hp : 1 ≤ p)
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ f x)
    (hD : MemLpLoc p Ω (fderiv ℝ f) μ) : MemWkpLoc p Ω 1 f μ := by
  have hc : ContinuousOn f Ω := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  exact memWkpLoc_succ_iff_of_isOpen.2 ⟨hc.memLpLoc, fderiv ℝ f,
    hasWeakFDerivOn_of_differentiableOn (hD.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) hdiff,
    hD⟩

private theorem contDiffOn_memWkpLoc_max [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E → F} (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) :
    MemWkpLoc p U k f μ := by
  induction k generalizing F with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k ih =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) :
    MemWkpLoc p U k f μ := by
  cases k with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2
      ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, contDiffOn_memWkpLoc_max hD hU⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A `Cᵏ` map on the whole space is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (hf : ContDiff ℝ k f) : MemWkpLoc p U k f μ :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-- Every continuous affine map `x ↦ L x + c` into a Banach space lies in `MemWkpLoc p U k` for
every exponent `p`, order `k`, and additive Haar measure `μ`. -/
theorem _root_.ContinuousLinearMap.memWkpLoc_affine [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (L : E →L[ℝ] F) (c : F) :
    MemWkpLoc p U k (fun x : E => L x + c) μ :=
  (L.contDiff.add contDiff_const).memWkpLoc

end MemWkpLoc

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

universe u v

/-- Auxiliary recursion for `TauCeti.WeakDerivChainLe` whose codomain lies in `Type max u v`, so
iterated operator spaces `E →L[ℝ] F` stay in the same universe. -/
private def weakDerivChainLeAux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (p : ℝ≥0∞) (S T : Set E) (C : ℝ≥0∞) :
    (m : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg →
            weakDerivChainLeAux μ p S T C m Df Dg

private theorem weakDerivChainLeAux_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p C : ℝ≥0∞} {S T : Set E} {m : ℕ}
    {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} :
    weakDerivChainLeAux.{u, v} μ p S T C m f g ↔
      weakDerivChainLeAux.{u, max u v} μ p S T C m f g := by
  induction m generalizing F with
  | zero => exact Iff.rfl
  | succ m ih =>
    exact and_congr_right fun _ => forall_congr' fun Df => forall_congr' fun Dg =>
      imp_congr_right fun _ => imp_congr_right fun _ => ih (F := E →L[ℝ] F) (f := Df) (g := Dg)

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {p C : ℝ≥0∞} {S T : Set E} {m : ℕ} {f g : E → F}

/-- `WeakDerivChainLe p S T C m f g μ` bounds the iterated weak derivatives of `f` through order
`m` by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ℝ≥0∞) (S T : Set E) (C : ℝ≥0∞) (m : ℕ) (f g : E → F)
    (μ : Measure E := by volume_tac) : Prop :=
  match m with
  | 0 => eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T)
  | m + 1 =>
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg →
            weakDerivChainLeAux.{u, v} μ p S T C m Df Dg

private theorem weakDerivChainLe_iff_aux {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLe.{u, max u v} p S T C m f g μ ↔
      weakDerivChainLeAux.{u, v} μ p S T C m f g := by
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        (weakDerivChainLeAux_univ.{u, v}).symm

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g μ ↔
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g μ ↔
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg μ :=
  and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ =>
      (weakDerivChainLe_iff_aux.{u, v}).symm

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g μ) :
    eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g μ)
    {Df Dg : E → E →L[ℝ] F} (hf : HasWeakFDerivOn μ (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn μ (Opens.interior T) g Dg) :
    WeakDerivChainLe p S T C m Df Dg μ :=
  (weakDerivChainLe_succ_iff.1 h).2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

section ClassicalRepresentatives

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {U : Set E} {k m : ℕ} {u g : E → F}

/-- **The derivative of a `C¹` representative is a weak derivative.** Let `U` agree almost
everywhere with its interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `C¹` on the interior of `U` and
agrees almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on the interior of `U` and lies in `MemWkpLoc p U k`. By uniqueness of weak
derivatives (`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on the interior of `U`
agrees with `fderiv ℝ g` almost everywhere on `U`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn (hu : MemWkpLoc p U (k + 1) u μ)
    (hU : U =ᵐ[μ] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ 1 g (Opens.interior U))
    (hug : u =ᵐ[μ.restrict U] g) :
    HasWeakFDerivOn μ (Opens.interior U) u (fderiv ℝ g) ∧ MemWkpLoc p U k (fderiv ℝ g) μ := by
  have := hu.completeSpace
  rw [Measure.restrict_congr_set hU] at hug
  have hg' : HasWeakFDerivOn μ (Opens.interior U) g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  refine ⟨hg'.congr_ae hug.symm, hDk.congr_ae ?_⟩
  rw [Measure.restrict_congr_set hU]
  exact (hD.congr_ae hug).ae_eq hg'

private theorem iteratedFDeriv_of_contDiffOn_max {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u g : E → F}
    (hu : MemWkpLoc p U (k + m) u μ) (hU : U =ᵐ[μ] (Opens.interior U : Set E))
    (hg : ContDiffOn ℝ k g (Opens.interior U)) (hug : u =ᵐ[μ.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) μ := by
  induction k generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff
      (E := E) (μ := μ)).2 ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k ih =>
    rw [Nat.add_right_comm] at hu
    have : CompleteSpace F := hu.completeSpace
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
    let L :=
      (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toLinearIsometry.toContinuousLinearMap
    have heq : iteratedFDeriv ℝ (k + 1) g = fun z => L (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact h.clm_comp L

/-- **Iterated derivatives of a `Cᵏ` representative.** Let `U` agree almost everywhere with its
interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `Cᵏ` on the interior of `U` and agrees
almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p U m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p U (k + m) u μ)
    (hU : U =ᵐ[μ] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ k g (Opens.interior U))
    (hug : u =ᵐ[μ.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) μ := by
  cases k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff
      (E := E) (μ := μ)).2 ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k =>
    rw [Nat.add_right_comm] at hu
    have : CompleteSpace F := hu.completeSpace
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := iteratedFDeriv_of_contDiffOn_max hDk hU hgk (Filter.EventuallyEq.refl _ _)
    let L :=
      (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toLinearIsometry.toContinuousLinearMap
    have heq : iteratedFDeriv ℝ (k + 1) g = fun z => L (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact h.clm_comp L

end ClassicalRepresentatives

end TauCeti
