/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Basic
public import TauCeti.MeasureTheory.Measure.Prod

/-!
# Disintegrating a measure over a countable coordinate

A measure `σ` on a product `Y × Z` disintegrates over `Y` when it is the composition-product
`σ.fst ⊗ₘ κ` of its first marginal with a Markov kernel `κ : Kernel Y Z`. Mathlib supplies such a
kernel when the *second* factor `Z` is standard Borel
(`MeasureTheory.Measure.condKernel`). This file supplies one in the complementary regime: when the
*first* factor `Y` is countable with measurable singletons, `Z` is any nonempty measurable space,
and every atom of `σ.fst` has finite mass (equivalently, `σ.fst` is σ-finite; in particular
whenever `σ` is finite).

On a countable `Y` no analytic input is needed — the disintegration is the elementary formula
`κ y s = (σ.fst {y})⁻¹ * σ ({y} ×ˢ s)`, conditioning on the atom `{y}`. The one point that needs
care is the atoms of zero mass, where that formula reads `∞ * 0` and carries no information: they
are given a default value, and the disintegration still holds there because such an atom carries
no `σ`-mass to begin with (`MeasureTheory.Measure.measure_prod_eq_zero_of_fst_eq_zero`).

## Main definitions

* `MeasureTheory.Measure.countableCondKernel` — the conditional kernel `σ.countableCondKernel` of
  a measure `σ` on `Y × Z` over a countable `Y`.

## Main results

* `MeasureTheory.Measure.countableCondKernel_apply`,
  `MeasureTheory.Measure.countableCondKernel_apply_of_ne_zero` and
  `MeasureTheory.Measure.countableCondKernel_apply_of_eq_zero` — the defining formula and its two
  branches, made explicit;
* `MeasureTheory.Measure.compProd_countableCondKernel` — **the disintegration**,
  `σ.fst ⊗ₘ σ.countableCondKernel = σ` for σ-finite `σ.fst`, registered as a
  `MeasureTheory.Measure.IsCondKernel` instance;
* `MeasureTheory.Measure.eq_countableCondKernel_of_ne_zero` — for σ-finite `σ.fst`, every
  conditional kernel of `σ` agrees with this one at every atom of positive mass.

The file also contains two private regression examples showing that the uniqueness statement
cannot be strengthened and that the σ-finiteness hypothesis cannot be dropped.

## Implementation notes

The kernel is built with `ProbabilityTheory.Kernel.ofFunOfCountable`, which upgrades an arbitrary
function on a countable space with measurable singletons to a kernel; the measurability of the
disintegration, the only nontrivial requirement in the standard Borel setting, is free here.

The value at an atom of zero mass is a Dirac measure at `Classical.arbitrary Z`, hence the
`[Nonempty Z]` hypothesis. Some choice is forced: a Markov kernel must return a probability
measure at every point of `Y`, `σ` prescribes none at a null atom, and on an empty `Z` no Markov
kernel exists at all, by `ProbabilityTheory.Kernel.eq_zero_of_isEmpty_right` together with
`ProbabilityTheory.Kernel.not_isMarkovKernel_zero`. The choice is deliberately *not* hidden —
`countableCondKernel_apply_of_eq_zero` names it. A private regression below exhibits two
conditional kernels of one measure that differ at a null atom, so no strengthening of
`eq_countableCondKernel_of_ne_zero` to all atoms is available.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5 and its finite reduction.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

section CondKernel

variable [Countable Y] [MeasurableSingletonClass Y] [Nonempty Z]

/-- The **countable-coordinate kernel construction** for a measure `σ` on `Y × Z`. When every atom
of `σ.fst` has finite mass, this is its conditional kernel over the first coordinate.

At an atom `y` of positive first-marginal mass this is the normalised slice
`s ↦ (σ.fst {y})⁻¹ * σ ({y} ×ˢ s)`; at a null atom, where `σ` prescribes nothing, it is a Dirac
measure. Unlike `MeasureTheory.Measure.condKernel`, this needs no standard-Borel or other
regularity hypothesis on the nonempty second factor `Z`. -/
def countableCondKernel (σ : Measure (Y × Z)) : Kernel Y Z :=
  Kernel.ofFunOfCountable fun y =>
    if σ.fst {y} = 0 then Measure.dirac (Classical.arbitrary Z)
    else ((σ.fst {y})⁻¹ • σ).comap (Prod.mk y)

/-- The defining formula of `countableCondKernel`, with both branches still under the `if`. The
pair of branch lemmas below is the interface to prefer; neither of those mentions the `if`. -/
theorem countableCondKernel_apply (σ : Measure (Y × Z)) (y : Y) :
    countableCondKernel σ y =
      if σ.fst {y} = 0 then Measure.dirac (Classical.arbitrary Z)
      else ((σ.fst {y})⁻¹ • σ).comap (Prod.mk y) := (rfl)

/-- At a null atom the conditional kernel takes its default value. It is a genuine choice, not a
quantity read off `σ`; see the private uniqueness regression below. -/
@[simp] theorem countableCondKernel_apply_of_eq_zero {σ : Measure (Y × Z)} {y : Y}
    (hy : σ.fst {y} = 0) : countableCondKernel σ y = Measure.dirac (Classical.arbitrary Z) := by
  rw [countableCondKernel_apply, ite_eq_left hy]

/-- At an atom of positive mass the conditional kernel is the normalised slice. -/
@[simp] theorem countableCondKernel_apply_of_ne_zero {σ : Measure (Y × Z)} {y : Y}
    (hy : σ.fst {y} ≠ 0) (s : Set Z) :
    countableCondKernel σ y s = (σ.fst {y})⁻¹ * σ ({y} ×ˢ s) := by
  rw [countableCondKernel_apply, ite_eq_right hy, (measurableEmbedding_prodMk_left y).comap_apply,
    Measure.smul_apply, Set.singleton_prod, smul_eq_mul]

/-- `countableCondKernel σ` is a Markov kernel as soon as `σ.fst` is σ-finite, i.e. (on the
countable space `Y`) as soon as every atom of `σ.fst` has finite mass. -/
instance instIsMarkovKernelCountableCondKernel (σ : Measure (Y × Z)) [SigmaFinite σ.fst] :
    IsMarkovKernel (countableCondKernel σ) := by
  refine ⟨fun y => ?_⟩
  by_cases hy : σ.fst {y} = 0
  · rw [countableCondKernel_apply_of_eq_zero hy]
    infer_instance
  · refine ⟨?_⟩
    rw [countableCondKernel_apply_of_ne_zero hy, Set.prod_univ,
      ← Measure.fst_apply (measurableSet_singleton y),
      ENNReal.inv_mul_cancel hy measure_singleton_lt_top.ne]

/-- **The disintegration of a measure over a countable coordinate.** It holds whenever `σ.fst` is
σ-finite, which on the countable space `Y` means that every atom of `σ.fst` has finite mass. -/
@[simp] theorem compProd_countableCondKernel (σ : Measure (Y × Z)) [SigmaFinite σ.fst] :
    σ.fst ⊗ₘ countableCondKernel σ = σ := by
  ext s hs
  -- The atomic decomposition `σ s = ∑' y, σ ({y} ×ˢ (Prod.mk y ⁻¹' s))`.
  have hdecomp : σ s = ∑' y : Y, σ (({y} : Set Y) ×ˢ (Prod.mk y ⁻¹' s)) := by
    rw [← measure_iUnion
      (fun y y' h => Set.disjoint_prod.2 (Or.inl (Set.disjoint_singleton.2 h)))
      fun y => (measurableSet_singleton y).prod (measurable_prodMk_left hs)]
    congr 1
    ext ⟨y, z⟩
    simp
  rw [Measure.compProd_apply hs, lintegral_countable', hdecomp]
  refine tsum_congr fun y => ?_
  by_cases hy : σ.fst {y} = 0
  · rw [hy, mul_zero, measure_prod_eq_zero_of_fst_eq_zero σ hy]
  · rw [countableCondKernel_apply_of_ne_zero hy, mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel hy measure_singleton_lt_top.ne, one_mul]

instance instIsCondKernelCountableCondKernel (σ : Measure (Y × Z)) [SigmaFinite σ.fst] :
    σ.IsCondKernel (countableCondKernel σ) where
  disintegrate := compProd_countableCondKernel σ

/-- Any conditional kernel of a measure `σ` with σ-finite first marginal agrees with
`countableCondKernel σ` at every atom of positive mass. The restriction to such atoms is sharp, as
shown by the first private regression below. -/
theorem eq_countableCondKernel_of_ne_zero (σ : Measure (Y × Z)) [SigmaFinite σ.fst]
    (κ : Kernel Y Z) [σ.IsCondKernel κ] {y : Y} (hy : σ.fst {y} ≠ 0) :
    κ y = countableCondKernel σ y := by
  have := IsCondKernel.isSFiniteKernel σ κ (by rintro rfl; simp at hy)
  ext s hs
  have hslice : σ ({y} ×ˢ s) = σ.fst {y} * κ y s := by
    conv_lhs => rw [← σ.disintegrate κ]
    rw [compProd_apply_prod (measurableSet_singleton y) hs, lintegral_singleton, mul_comm]
  rw [countableCondKernel_apply_of_ne_zero hy, hslice, ← mul_assoc,
    ENNReal.inv_mul_cancel hy measure_singleton_lt_top.ne, one_mul]

end CondKernel

section Regressions

/-! ### Regressions

Two examples that break the contract of `countableCondKernel` if it is read more strongly than it
is stated. The first shows the conclusion of `eq_countableCondKernel_of_ne_zero` cannot be
extended to null atoms; the second shows that `SigmaFinite σ.fst` cannot be dropped. (That
`Nonempty Z` cannot be dropped either is immediate from Mathlib:
`ProbabilityTheory.Kernel.eq_zero_of_isEmpty_right` and
`ProbabilityTheory.Kernel.not_isMarkovKernel_zero` leave no Markov kernel at all on an empty
target.) -/

/-- **Uniqueness genuinely fails at a null atom.** The Dirac measure at `(true, true)` on
`Bool × Bool` gives the atom `false` no mass, and the two kernels below both disintegrate it while
differing there. Thus a conditional kernel is always pinned down on atoms of positive mass, while
uniqueness can fail at null atoms; the default value `countableCondKernel` uses there is a choice,
not a derived quantity. -/
private theorem exists_isCondKernel_pair_ne :
    ∃ κ₁ κ₂ : Kernel Bool Bool,
      (Measure.dirac ((true, true) : Bool × Bool)).IsCondKernel κ₁ ∧
      (Measure.dirac ((true, true) : Bool × Bool)).IsCondKernel κ₂ ∧ κ₁ ≠ κ₂ := by
  have hfst : (Measure.dirac ((true, true) : Bool × Bool)).fst = Measure.dirac true := by
    rw [Measure.fst, Measure.map_dirac' measurable_fst]
  -- Only the atom `true` carries mass, so any Markov kernel taking the value `dirac true` there
  -- disintegrates the measure, whatever it does at `false`.
  have key : ∀ κ : Kernel Bool Bool, IsMarkovKernel κ → κ true = Measure.dirac true →
      (Measure.dirac ((true, true) : Bool × Bool)).fst ⊗ₘ κ
        = Measure.dirac ((true, true) : Bool × Bool) := by
    intro κ _ hκ
    ext s hs
    rw [hfst, Measure.dirac_compProd_apply hs, hκ,
      Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left),
      Measure.dirac_apply' _ hs]
    rfl
  refine ⟨Kernel.const Bool (Measure.dirac true), Kernel.deterministic id measurable_id,
    ⟨key _ inferInstance (Kernel.const_apply _ _)⟩,
    ⟨key _ inferInstance (Kernel.deterministic_apply measurable_id true)⟩, ?_⟩
  intro h
  have hfalse := congrArg (fun κ : Kernel Bool Bool => κ false {true}) h
  simp [Kernel.const_apply, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton true)] at hfalse

/-- **`SigmaFinite σ.fst` cannot be dropped.** At an atom of infinite mass the normalising factor
`(σ.fst {y})⁻¹` is `0`, so the conditional kernel collapses to the zero measure and the
composition-product loses all the mass it was meant to recover. -/
private theorem exists_compProd_countableCondKernel_ne :
    ∃ σ : Measure (Unit × Unit), σ.fst ⊗ₘ countableCondKernel σ ≠ σ := by
  refine ⟨(⊤ : ℝ≥0∞) • Measure.dirac ((), ()), fun h => ?_⟩
  have hfst :
      ((⊤ : ℝ≥0∞) • Measure.dirac ((), ())).fst = (⊤ : ℝ≥0∞) • Measure.dirac () := by
    rw [Measure.fst, Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_dirac' measurable_fst]
  have hzero : countableCondKernel ((⊤ : ℝ≥0∞) • Measure.dirac ((), ())) = 0 := by
    ext y s
    simp [hfst]
  simpa [hzero] using congrArg (· Set.univ) h

end Regressions

end MeasureTheory.Measure
