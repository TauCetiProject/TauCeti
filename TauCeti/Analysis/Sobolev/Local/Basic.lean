/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc.PreciseRepresentative
public import TauCeti.Topology.Sets.Opens

/-!
# Local vector-valued Sobolev classes

`TauCeti.MemWkpLoc p U k f` requires iterated weak derivatives through order `k` on
`interior U`, with `Lᵖ` bounds on every compact subset of `U` itself, for a real normed measure
space `E` and function `f : E → F`, building on the local `Lᵖ` predicate `TauCeti.MemLpLoc` from
`TauCeti.MeasureTheory.Function.MemLpLoc.Basic`. On subsets reaching a boundary (such as
half-discs in `ℂ`), the `Lᵖ` bounds reach the boundary while test functions stay in the interior.
On open sets this is the usual local Sobolev class `W^{k,p}_loc(Ω; F)`. Derivatives take values in
iterated continuous linear maps rather than scalar jets.

These predicates concern actual functions; almost-everywhere changes do not affect membership.
They impose no global integrability condition on the possibly unbounded domain. Global `Lᵖ`
membership on a set implies local membership there (`MeasureTheory.MemLp.memLpLoc`).

This file supplies restriction to arbitrary subsets (also combined with a change of the function
off the subset), linearity, continuous-linear composition, pairing, pointwise product maps of
operator fields, decreasing the integrability exponent, and decreasing the derivative order.
Differentiability on an open set with a locally `Lᵖ` (in particular continuous) derivative gives
first-order local Sobolev membership (`DifferentiableOn.memWkpLoc_one`), smoothness on an open
neighbourhood gives membership at every order, and smooth or continuous linear maps (including the
identity map `TauCeti.memWkpLoc_id`) on the whole space are in every class on every set.
Conversely, let `U` agree almost everywhere with its interior, as open sets and half-discs do.
If `g` is `Cᵏ` on the interior of `U` and agrees almost everywhere on `U` with
`u ∈ MemWkpLoc p U (k + m)`, then `fderiv ℝ g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, for `k ≥ 1`) and
`iteratedFDeriv ℝ k g ∈ MemWkpLoc p U m` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
In finite dimension with a Borel measure, every weak derivative of a member of
`MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`; at order one, it is locally `Lᵖ`.
`TauCeti.WeakDerivChainLe` compares the `Lᵖ` norms of two maps and, recursively, of every pair of
their weak derivatives through a given order.
In positive order, completeness is inherited from the native weak-derivative predicate; the
definitions admit every real normed codomain without an additional typeclass assumption.
The continuous-linear composition result requires a complete target, as does the native
weak-derivative result it uses.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2 (Bochner-valued first-order Sobolev spaces).
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

section MemWkpLoc

universe u v w v' w'

variable {E : Type u} {F : Type v} {G : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p q : ENNReal} {U V : Set E} {Ω : Opens E} {k l m : ℕ} {f g u : E → F}

private def MemWkpLocAux (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type (max u v)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLocAux p U k D

/-- The iterated weak derivatives through order `k` exist on `interior U` and are `Lᵖ` on
every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `E →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLocAux.{u, v} p U k D

private theorem memWkpLocAux_max {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} : MemWkpLocAux.{u, v} p U k f ↔ MemWkpLocAux.{u, max u v} p U k f := by
  induction k generalizing F with
  | zero => exact Iff.rfl
  | succ k ih =>
    unfold MemWkpLocAux
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => ih

private theorem memWkpLocAux_iff_memWkpLoc {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} :
    MemWkpLocAux.{u, v} p U k f ↔ MemWkpLoc.{u, max u v} p U k f := by
  cases k with
  | zero => exact Iff.rfl
  | succ k =>
    unfold MemWkpLocAux MemWkpLoc
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => memWkpLocAux_max

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f ↔ MemLpLoc p U f := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f ↔ MemLpLoc p U f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D :=
  and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
    memWkpLocAux_iff_memWkpLoc

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f ↔ MemLpLoc p Ω f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f) : MemLpLoc p U f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D :=
  (memWkpLoc_succ_iff.mp hf).2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- For a continuous function on `U`, local `Lᵖ` membership is automatic, so successor-order
local Sobolev membership is equivalent to having a weak derivative of the preceding order. -/
theorem _root_.ContinuousOn.memWkpLoc_succ_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : ContinuousOn f U) :
    MemWkpLoc p U (k + 1) f ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLoc p U k D :=
  TauCeti.memWkpLoc_succ_iff.trans (and_iff_right hf.memLpLoc)

/-- For a continuous function on an open set `Ω`, order-one local Sobolev membership is equivalent
to having a locally `Lᵖ` weak derivative on `Ω`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : ContinuousOn f Ω) :
    MemWkpLoc p Ω 1 f ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemLpLoc p Ω D := by
  simpa only [Opens.interior_coe, memWkpLoc_zero_iff] using hf.memWkpLoc_succ_iff (p := p) (k := 0)

private theorem memWkpLoc_mono_succ {F' : Type v'} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {k : ℕ} {f : E → F'} (hVU : V ⊆ U)
    (ih : ∀ {D : E → E →L[ℝ] F'}, MemWkpLoc p U k D → MemWkpLoc p V k D)
    (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p V (k + 1) f := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f) (hVU : V ⊆ U) :
    MemWkpLoc p V k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p V k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact hf.mono_set hVU
    | succ k ih => intro _ _ _ _ hf; exact memWkpLoc_mono_succ hVU ih hf
  cases k with
  | zero => exact hf.mono_set hVU
  | succ k => exact memWkpLoc_mono_succ hVU (aux k) hf

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemWkpLoc p U k g := by
  cases k with
  | zero => exact MemLpLoc.congr_ae hf hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set volume interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemWkpLoc p V k g := by
  cases k with
  | zero => exact MemLpLoc.congr_mono hf hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := memWkpLoc_succ_iff.1 (hf.mono hVU)
    exact memWkpLoc_succ_iff.2 ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f)
    (hgf : Set.EqOn g f U) : MemWkpLoc p U k g :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω (k + 1) f) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    MemWkpLoc p Ω k D := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω 1 f) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    MemLpLoc p Ω D :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

private theorem memWkpLoc_mono_exponent_succ [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {F' : Type v'} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {k : ℕ} {f : E → F'} (hqp : q ≤ p)
    (ih : ∀ {D : E → E →L[ℝ] F'}, MemWkpLoc p U k D → MemWkpLoc q U k D)
    (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc q U (k + 1) f := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hf : MemWkpLoc p U k f) (hqp : q ≤ p) :
    MemWkpLoc q U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc q U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.mono_exponent hf hqp
    | succ k ih => intro _ _ _ _ hf; exact memWkpLoc_mono_exponent_succ hqp ih hf
  cases k with
  | zero => exact MemLpLoc.mono_exponent hf hqp
  | succ k => exact memWkpLoc_mono_exponent_succ hqp (aux k) hf

private theorem memWkpLoc_of_succ_succ {F' : Type v'} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {k : ℕ} {f : E → F'}
    (ih : ∀ {D : E → E →L[ℝ] F'}, MemWkpLoc p U (k + 1) D → MemWkpLoc p U k D)
    (hf : MemWkpLoc p U (k + 2) f) : MemWkpLoc p U (k + 1) f := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U (k + 1) f → MemWkpLoc p U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact hf.1
    | succ k ih => intro _ _ _ _ hf; exact memWkpLoc_of_succ_succ ih hf
  cases k with
  | zero => exact hf.1
  | succ k => exact memWkpLoc_of_succ_succ (aux k) hf

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f) (hlk : l ≤ k) : MemWkpLoc p U l f := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

private theorem memWkpLoc_zero_fun_succ {F' : Type v'} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] {k : ℕ} (ih : MemWkpLoc p U k (0 : E → E →L[ℝ] F')) :
    MemWkpLoc p U (k + 1) (0 : E → F') :=
  memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F], MemWkpLoc p U k (0 : E → F) := by
    intro k
    induction k with
    | zero => intro _ _ _ _; exact memLpLoc_zero
    | succ k ih => intro _ _ _ _; exact memWkpLoc_zero_fun_succ ih
  cases k with
  | zero => exact memLpLoc_zero
  | succ k => exact memWkpLoc_zero_fun_succ (aux k)

private theorem memWkpLoc_add_succ [OpensMeasurableSpace E] {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {k : ℕ} {f g : E → F'}
    (ih : ∀ {D₁ D₂ : E → E →L[ℝ] F'},
      MemWkpLoc p U k D₁ → MemWkpLoc p U k D₂ → MemWkpLoc p U k (D₁ + D₂))
    (hf : MemWkpLoc p U (k + 1) f) (hg : MemWkpLoc p U (k + 1) g) :
    MemWkpLoc p U (k + 1) (f + g) := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
  exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f + g) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f g : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k g → MemWkpLoc p U k (f + g) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ hf hg; exact MemLpLoc.add hf hg
    | succ k ih => intro _ _ _ _ _ hf hg; exact memWkpLoc_add_succ ih hf hg
  cases k with
  | zero => exact MemLpLoc.add hf hg
  | succ k => exact memWkpLoc_add_succ (aux k) hf hg

private theorem memWkpLoc_neg_succ {F' : Type v'} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {k : ℕ} {f : E → F'} (ih : ∀ {D : E → E →L[ℝ] F'}, MemWkpLoc p U k D → MemWkpLoc p U k (-D))
    (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U (k + 1) (-f) := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f) : MemWkpLoc p U k (-f) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k (-f) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.neg hf
    | succ k ih => intro _ _ _ _ hf; exact memWkpLoc_neg_succ ih hf
  cases k with
  | zero => exact MemLpLoc.neg hf
  | succ k => exact memWkpLoc_neg_succ (aux k) hf

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem memWkpLoc_const_smul_succ {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {k : ℕ} {f : E → F'} (c : ℝ)
    (ih : ∀ {D : E → E →L[ℝ] F'}, MemWkpLoc p U k D → MemWkpLoc p U k (c • D))
    (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U (k + 1) (c • f) := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f) (c : ℝ) :
    MemWkpLoc p U k (c • f) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k (c • f) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.const_smul hf c
    | succ k ih => intro _ _ _ _ hf; exact memWkpLoc_const_smul_succ c ih hf
  cases k with
  | zero => exact MemLpLoc.const_smul hf c
  | succ k => exact memWkpLoc_const_smul_succ c (aux k) hf

private theorem memWkpLoc_clm_comp_succ [OpensMeasurableSpace E] {F' : Type v'} {G' : Type w'}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    [CompleteSpace G'] {k : ℕ} {f : E → F'} (A : F' →L[ℝ] G')
    (ih : ∀ {D : E → E →L[ℝ] F'} (B : (E →L[ℝ] F') →L[ℝ] (E →L[ℝ] G')),
      MemWkpLoc p U k D → MemWkpLoc p U k (fun z => B (D z)))
    (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U (k + 1) (fun z => A (f z)) := by
  obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
  exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
    ih ((ContinuousLinearMap.compL ℝ E F' G') A) hk⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hf : MemWkpLoc p U k f)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} {G : Type (max u w)}
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] {f : E → F},
      MemWkpLoc p U k f → (A : F →L[ℝ] G) → MemWkpLoc p U k (fun z => A (f z)) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ _ _ _ hf A; exact MemLpLoc.clm_comp hf A
    | succ k ih =>
      intro _ _ _ _ _ _ _ _ hf A
      exact memWkpLoc_clm_comp_succ A (fun B hD => ih hD B) hf
  cases k with
  | zero => exact MemLpLoc.clm_comp hf A
  | succ k => exact memWkpLoc_clm_comp_succ A (fun B hD => aux k hD B) hf

/-- Multiplying a scalar local Sobolev function by a fixed vector in a complete real normed space
preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemWkpLoc p U k a) (v : F) : MemWkpLoc p U k (fun x => a x • v) := by
  simpa using ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G] {g : E → G}
    (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (fun z => (f z, g z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap [OpensMeasurableSpace E] {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A)
    (hB : MemWkpLoc p U k B) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff [OpensMeasurableSpace E]
    (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) ↔ MemWkpLoc p U k f := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f))
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

/-- Constant functions belong to every local Sobolev class. -/
@[simp]
theorem memWkpLoc_const [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (c : F) :
    MemWkpLoc p U k (fun _ => c) := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine memWkpLoc_succ_iff.2 ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := volume) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum [OpensMeasurableSpace E] {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i)) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A map differentiable on an open set `Ω` whose derivative is locally `Lᵖ` on `Ω` (with
`1 ≤ p`) belongs to `W^{1,p}_loc(Ω; F)`, with weak derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one_of_memLpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : DifferentiableOn ℝ f Ω)
    (hp : 1 ≤ p) (hD : MemLpLoc p Ω (fderiv ℝ f)) : MemWkpLoc p Ω 1 f :=
  hf.continuousOn.memWkpLoc_one_iff.2 ⟨fderiv ℝ f,
    hasWeakFDerivOn_of_differentiableOn
      (hD.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)
      (fun _ hx => hf.differentiableAt (Ω.isOpen.mem_nhds hx)),
    hD⟩

/-- A map differentiable on an open set `Ω` with continuous derivative belongs to
`W^{1,p}_loc(Ω; F)` for every exponent `p`, with weak derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : DifferentiableOn ℝ f Ω)
    (hD : ContinuousOn (fderiv ℝ f) Ω) : MemWkpLoc p Ω 1 f :=
  hf.continuousOn.memWkpLoc_one_iff.2 ⟨fderiv ℝ f,
    hasWeakFDerivOn_of_differentiableOn
      (hD.locallyIntegrableOn Ω.isOpen.measurableSet)
      (fun _ hx => hf.differentiableAt (Ω.isOpen.mem_nhds hx)),
    hD.memLpLoc⟩

private theorem contDiffOn_memWkpLoc_zero [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {f : E → F'} (hf : ContDiffOn ℝ 0 f (Ω : Set E)) (hU : U ⊆ Ω) :
    MemWkpLoc p U 0 f :=
  (hf.continuousOn.mono hU).memLpLoc

private theorem contDiffOn_memWkpLoc_succ [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [CompleteSpace F'] {k : ℕ} {f : E → F'}
    (hf : ContDiffOn ℝ (k + 1) f (Ω : Set E)) (hU : U ⊆ Ω)
    (ih : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) → MemWkpLoc p U k (fderiv ℝ f)) :
    MemWkpLoc p U (k + 1) f := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) := hf.fderiv_of_isOpen Ω.isOpen (by simp)
  refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
  exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F]
    (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) : MemWkpLoc p U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] {f : E → F}, ContDiffOn ℝ k f (Ω : Set E) → MemWkpLoc p U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ hf; exact contDiffOn_memWkpLoc_zero hf hU
    | succ k ih => intro _ _ _ _ f hf; exact contDiffOn_memWkpLoc_succ hf hU ih
  cases k with
  | zero => exact contDiffOn_memWkpLoc_zero hf hU
  | succ k => exact contDiffOn_memWkpLoc_succ hf hU (aux k)

/-- A `Cᵏ` map on the whole space is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : ContDiff ℝ k f) :
    MemWkpLoc p U k f :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-- Every continuous linear map belongs to every local Sobolev class on every set. -/
theorem _root_.ContinuousLinearMap.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (A : E →L[ℝ] F) :
    MemWkpLoc p U k A :=
  A.contDiff.memWkpLoc

/-- The identity map belongs to every local Sobolev class on every set of a finite-dimensional
real normed space with an additive Haar measure. -/
theorem memWkpLoc_id [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] : MemWkpLoc p U k (fun x : E => x) :=
  (ContinuousLinearMap.id ℝ E).memWkpLoc

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

private def WeakDerivChainLeAux (p : ENNReal) (S T : Set E) (C : ENNReal) :
    (m : ℕ) → {F : Type (max u v)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLeAux p S T C m Df Dg

/-- `WeakDerivChainLe p S T C m f g` bounds the iterated weak derivatives of `f` through order `m`
by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ENNReal) (S T : Set E) (C : ENNReal) :
    (m : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg →
            WeakDerivChainLeAux.{u, v} p S T C m Df Dg

variable {C : ENNReal} {S T : Set E}

private theorem weakDerivChainLeAux_max {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLeAux.{u, v} p S T C m f g ↔
      WeakDerivChainLeAux.{u, max u v} p S T C m f g := by
  induction m generalizing F with
  | zero => exact Iff.rfl
  | succ m ih =>
    unfold WeakDerivChainLeAux
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => forall_congr' fun _ => ih

private theorem weakDerivChainLeAux_iff {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLeAux.{u, v} p S T C m f g ↔
      WeakDerivChainLe.{u, max u v} p S T C m f g := by
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    unfold WeakDerivChainLeAux WeakDerivChainLe
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => forall_congr' fun _ => weakDerivChainLeAux_max

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg :=
  and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => weakDerivChainLeAux_iff

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g) :
    eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g)
    {Df Dg : E → E →L[ℝ] F} (hf : HasWeakFDerivOn volume (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior T) g Dg) : WeakDerivChainLe p S T C m Df Dg :=
  (weakDerivChainLe_succ_iff.1 h).2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

section ContDiffRepresentatives

variable [BorelSpace E]

/-- **The derivative of a `C¹` representative is a weak derivative.** Let `U` agree almost
everywhere with its interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `C¹` on the interior of `U` and
agrees almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on the interior of `U` and lies in `MemWkpLoc p U k`. By uniqueness of weak
derivatives (`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on the interior of `U`
agrees with `fderiv ℝ g` almost everywhere on `U`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (hu : MemWkpLoc p U (k + 1) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ 1 g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    HasWeakFDerivOn volume (Opens.interior U) u (fderiv ℝ g) ∧ MemWkpLoc p U k (fderiv ℝ g) := by
  have := hu.completeSpace
  rw [Measure.restrict_congr_set hU] at hug
  have hg' : HasWeakFDerivOn volume (Opens.interior U) g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  refine ⟨hg'.congr_ae hug.symm, hDk.congr_ae ?_⟩
  rw [Measure.restrict_congr_set hU]
  exact (hD.congr_ae hug).ae_eq hg'

private theorem iteratedFDeriv_of_contDiffOn_zero {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {u g : E → F'} (hu : MemWkpLoc p U (0 + m) u)
    (hug : u =ᵐ[volume.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ 0 g) := by
  rw [iteratedFDeriv_zero_eq_comp]
  exact (continuousMultilinearCurryFin0 ℝ E F').symm.toContinuousLinearEquiv
    |>.comp_memWkpLoc_iff.2 ((Nat.zero_add m ▸ hu).congr_ae hug)

variable [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]

private theorem iteratedFDeriv_of_contDiffOn_succ {F' : Type v'} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {k : ℕ} {u g : E → F'}
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hu : MemWkpLoc p U (k + 1 + m) u)
    (hg : ContDiffOn ℝ (k + 1) g (Opens.interior U)) (hug : u =ᵐ[volume.restrict U] g)
    (ih : MemWkpLoc p U (k + m) (fderiv ℝ g) → ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) →
      (fderiv ℝ g) =ᵐ[volume.restrict U] (fderiv ℝ g) →
      MemWkpLoc p U m (iteratedFDeriv ℝ k (fderiv ℝ g))) :
    MemWkpLoc p U m (iteratedFDeriv ℝ (k + 1) g) := by
  rw [Nat.add_right_comm] at hu
  obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
    (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
  have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
    hg.fderiv_of_isOpen isOpen_interior (by rfl)
  have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
  have heq : iteratedFDeriv ℝ (k + 1) g =
      fun z => (continuousMultilinearCurryRightEquiv' ℝ k E F').symm
        (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
    ext1 z
    exact iteratedFDeriv_succ_eq_comp_right
  rw [heq]
  exact (continuousMultilinearCurryRightEquiv' ℝ k E F').symm.toContinuousLinearEquiv
    |>.comp_memWkpLoc_iff.2 h

/-- **Iterated derivatives of a `Cᵏ` representative.** Let `U` agree almost everywhere with its
interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `Cᵏ` on the interior of `U` and agrees
almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p U m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p U (k + m) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ k g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u g : E → F}, MemWkpLoc p U (k + m) u → ContDiffOn ℝ k g (Opens.interior U) →
      u =ᵐ[volume.restrict U] g → MemWkpLoc p U m (iteratedFDeriv ℝ k g) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ hu _ hug; exact iteratedFDeriv_of_contDiffOn_zero hu hug
    | succ k ih =>
      intro _ _ _ _ _ hu hg hug
      exact iteratedFDeriv_of_contDiffOn_succ hU hu hg hug ih
  cases k with
  | zero => exact iteratedFDeriv_of_contDiffOn_zero hu hug
  | succ k => exact iteratedFDeriv_of_contDiffOn_succ hU hu hg hug (aux k)

end ContDiffRepresentatives

end MemWkpLoc

end TauCeti
