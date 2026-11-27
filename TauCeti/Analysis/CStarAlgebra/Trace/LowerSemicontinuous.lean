/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic

/-!
# Lower semicontinuity, semifiniteness and density of traces

For a trace `τ : B → ℝ≥0∞` on a C⋆-algebra `B` (`TauCeti.IsTrace`) we consider three regularity
conditions:

* `τ` is **lower semicontinuous** when it is `LowerSemicontinuousOn` the positive cone `B₊` for
  the norm topology;
* `τ` is **semifinite** (`TauCeti.IsSemifinite`) when
  `τ(x) = sup{τ(y) : y ∈ B₊, y ≤ x, τ(y) < ∞}` for every `x ∈ B₊` (Dixmier 1963, Définition 2,
  p. 224);
* `τ` is **densely defined** (`TauCeti.IsDenselyDefined`) when `𝔪_τ⁺` is dense in `B₊`.

For a lower semicontinuous trace and an increasing sequence or net `xᵢ → x` of positive elements
converging in norm, `τ(xᵢ) → τ(x)` (`TauCeti.IsTrace.tendsto_comp_of_monotone`, Dixmier 1963,
Remarque 2, p. 225): the positive cone is closed, so `xᵢ ≤ x` and `τ(xᵢ) ≤ τ(x)` by monotonicity,
while lower semicontinuity at `x` gives the reverse inequality for the supremum. The map
`x ↦ τ(x⋆x)` is lower semicontinuous on all of `B`
(`TauCeti.lowerSemicontinuous_star_mul_self`), as the composition of `τ` with the
norm-continuous map `x ↦ x⋆x` into `B₊`.

## Main definitions

* `TauCeti.IsSemifinite`: semifinite traces.
* `TauCeti.IsDenselyDefined`: densely defined traces.

## Main results

* `TauCeti.IsTrace.iSup_eq_of_monotone`, `TauCeti.IsTrace.tendsto_comp_of_monotone`: continuity
  along increasing nets of positive elements of a lower semicontinuous trace.
* `TauCeti.lowerSemicontinuous_star_mul_self`: `x ↦ τ(x⋆x)` is lower semicontinuous.
* `TauCeti.IsTrace.isSemifinite_of_lt_top`, `TauCeti.isDenselyDefined_of_lt_top`: traces finite
  on `B₊` are semifinite and densely defined.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Définition 2, p. 224; Remarque 2, p. 225.
-/

public section

open scoped ENNReal NNReal
open Filter Topology

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

/-- A trace is **semifinite** if `τ(x) = sup{τ(y) : y ∈ B₊, y ≤ x, τ(y) < ∞}` for every `x ∈ B₊`
(Dixmier 1963, Définition 2, p. 224). -/
def IsSemifinite (τ : B → ℝ≥0∞) : Prop :=
  ∀ ⦃x : B⦄, 0 ≤ x → τ x = ⨆ (y : B) (_ : 0 ≤ y ∧ y ≤ x ∧ τ y < ∞), τ y

/-- A trace is **densely defined** if its finite part `𝔪_τ⁺` is dense in `B₊`. -/
def IsDenselyDefined (τ : B → ℝ≥0∞) : Prop :=
  {x : B | 0 ≤ x} ⊆ closure (finitePart τ)

omit [StarOrderedRing B] in
/-- Unfolds `IsSemifinite`. -/
theorem isSemifinite_iff :
    IsSemifinite τ ↔ ∀ ⦃x : B⦄, 0 ≤ x → τ x = ⨆ (y : B) (_ : 0 ≤ y ∧ y ≤ x ∧ τ y < ∞), τ y :=
  Iff.rfl

omit [StarOrderedRing B] in
/-- Unfolds `IsDenselyDefined`. -/
theorem isDenselyDefined_iff : IsDenselyDefined τ ↔ {x : B | 0 ≤ x} ⊆ closure (finitePart τ) :=
  Iff.rfl

omit [StarOrderedRing B] in
/-- A trace finite on `B₊` is densely defined. -/
theorem isDenselyDefined_of_lt_top (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) : IsDenselyDefined τ :=
  fun x hx ↦ subset_closure (mem_finitePart.2 ⟨hx, hfin x hx⟩)

/-- If `τ` is lower semicontinuous on `B₊`, then `x ↦ τ(x⋆x)` is lower semicontinuous on `B`. -/
theorem lowerSemicontinuous_star_mul_self (hlsc : LowerSemicontinuousOn τ {x | 0 ≤ x}) :
    LowerSemicontinuous fun x : B ↦ τ (star x * x) := by
  rw [← lowerSemicontinuousOn_univ_iff]
  exact hlsc.comp (continuous_star.mul continuous_id).continuousOn
    fun x _ ↦ star_mul_self_nonneg x

namespace IsTrace

/-- A trace finite on `B₊` is semifinite. -/
theorem isSemifinite_of_lt_top (hτ : IsTrace τ) (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) :
    IsSemifinite τ :=
  fun x hx ↦ le_antisymm (le_iSup₂_of_le x ⟨hx, le_rfl, hfin x hx⟩ le_rfl)
    (iSup₂_le fun _ hy ↦ hτ.mono hy.1 hy.2.1)

/-- For a lower semicontinuous trace and an increasing net `xᵢ → x` of positive elements,
`τ(x) = sup τ(xᵢ)` (Dixmier 1963, Remarque 2, p. 225). -/
theorem iSup_eq_of_monotone (hτ : IsTrace τ) (hlsc : LowerSemicontinuousOn τ {x | 0 ≤ x})
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {f : ι → B} (hf : Monotone f)
    (hf₀ : ∀ i, 0 ≤ f i) {x : B} (hx : Tendsto f atTop (𝓝 x)) : ⨆ i, τ (f i) = τ x := by
  have hx₀ : 0 ≤ x := ge_of_tendsto' hx hf₀
  refine le_antisymm (iSup_le fun i ↦ hτ.mono (hf₀ i) (hf.ge_of_tendsto hx i)) ?_
  refine le_of_forall_lt fun y hy ↦ ?_
  have hxw : Tendsto f atTop (𝓝[{x | 0 ≤ x}] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hf₀⟩
  obtain ⟨i, hi⟩ := ((hxw.eventually (hlsc x hx₀ y hy)).exists)
  exact hi.trans_le (le_iSup (fun i ↦ τ (f i)) i)

/-- **Continuity along increasing nets.** For a lower semicontinuous trace and an increasing net
`xᵢ → x` of positive elements, `τ(xᵢ) → τ(x)` (Dixmier 1963, Remarque 2, p. 225). -/
theorem tendsto_comp_of_monotone (hτ : IsTrace τ) (hlsc : LowerSemicontinuousOn τ {x | 0 ≤ x})
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {f : ι → B} (hf : Monotone f)
    (hf₀ : ∀ i, 0 ≤ f i) {x : B} (hx : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun i ↦ τ (f i)) atTop (𝓝 (τ x)) := by
  rw [← hτ.iSup_eq_of_monotone hlsc hf hf₀ hx]
  exact tendsto_atTop_iSup fun i j hij ↦ hτ.mono (hf₀ i) (hf hij)

end IsTrace

end TauCeti
