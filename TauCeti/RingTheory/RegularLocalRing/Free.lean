/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
public import TauCeti.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.ProjectiveDimension
import TauCeti.RingTheory.Depth.WeaklyRegular

/-!
# Maximal Cohen–Macaulay modules over regular local rings

A finite module over a regular local ring is free if its depth is at least the dimension of the
ring. In particular, a Cohen–Macaulay module whose support has the full dimension of the ring is
free. The full-support-dimension hypothesis is essential: a quotient by a parameter is
Cohen–Macaulay but need not be free.

The quantitative input is
`ModuleCat.projectiveDimension_add_depth_le_ringKrullDim`: projective dimension plus depth is
at most the dimension of the regular local ring. Together with the existing global-dimension
bound, Mathlib's
`ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular` (Nailin Guan) proves
this inequality without the Auslander–Buchsbaum formula.

## References

* [The Stacks Project, Lemma 10.106.6](https://stacks.math.columbia.edu/tag/00NT).
* [The Stacks Project, Proposition 10.110.1](https://stacks.math.columbia.edu/tag/00O7).
-/

public section

open CategoryTheory IsLocalRing RingTheory.Sequence

universe v u

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [Small.{v} R]

/-- For a finite nonzero module over a regular local ring, projective dimension plus depth is
at most the Krull dimension of the ring. -/
theorem ModuleCat.projectiveDimension_add_depth_le_ringKrullDim (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] :
    projectiveDimension M + (IsLocalRing.depth M : WithBot ℕ∞) ≤ ringKrullDim R := by
  let lengths : Set ℕ∞ := {n | ∃ rs : List R, IsRegular M rs ∧
    (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ (rs.length : ℕ∞) = n}
  have : Nonempty lengths := ⟨0, [], IsRegular.nil R M, by simp, by simp⟩
  have hdepth : IsLocalRing.depth M = sSup lengths := by
    simpa only [lengths, exists_prop] using IsLocalRing.depth_eq_sSup_length_isRegular M
  have hfin : sSup lengths < ⊤ := by
    rw [← hdepth]
    exact lt_top_iff_ne_top.mpr fun h ↦ not_subsingleton M ((IsLocalRing.depth_eq_top_iff M).mp h)
  -- Finite depth is attained by a regular sequence; bound the projective dimension of its quotient.
  obtain ⟨rs, hreg, hmem, hlen⟩ := ENat.sSup_mem_of_nonempty_of_lt_top hfin
  have hbound := TauCeti.IsRegularLocalRing.hasProjectiveDimensionLE
    (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).ge
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)))
  rw [← projectiveDimension_le_iff,
    ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular M rs
      hreg.toIsWeaklyRegular hmem] at hbound
  rw [← hdepth] at hlen
  simpa [← hlen, _root_.IsRegularLocalRing.spanFinrank_maximalIdeal] using hbound

namespace TauCeti.IsRegularLocalRing

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a regular local ring is free if its depth is at least the dimension of
the ring. This formulation also allows the zero module, whose depth is infinite. -/
theorem free_of_ringKrullDim_le_depth
    (hdepth : ringKrullDim R ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞)) : Module.Free R M := by
  cases subsingleton_or_nontrivial M
  · exact Module.Free.of_subsingleton R M
  have h := ModuleCat.projectiveDimension_add_depth_le_ringKrullDim (ModuleCat.of R M)
  have hd : (depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm
      (IsLocalRing.depth_le_supportDim.trans (Module.supportDim_le_ringKrullDim R M)) hdepth
  rw [hd, ← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)] at h
  have hp : projectiveDimension (ModuleCat.of R M) ≤ 0 :=
    ENat.WithBot.add_le_add_natCast_right_iff.mp (by simpa only [zero_add] using h)
  have : Projective (ModuleCat.of R M) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr ((projectiveDimension_le_iff _ 0).mp hp)
  have : Module.Projective R M := (IsProjective.iff_projective M).mpr this
  exact Module.free_of_flat_of_isLocalRing

/-- **A maximal Cohen–Macaulay module over a regular local ring is free.** Here maximality means
that the dimension of the support equals the dimension of the ring; Cohen–Macaulayness alone
does not suffice. Stacks, Lemma 10.106.6 (00NT). -/
@[stacks 00NT]
theorem free_of_isCohenMacaulay (hM : Module.IsCohenMacaulay R M)
    (hdim : Module.supportDim R M = ringKrullDim R) : Module.Free R M := by
  cases subsingleton_or_nontrivial M
  · exact Module.Free.of_subsingleton R M
  exact free_of_ringKrullDim_le_depth M (hdim ▸ hM.depth_eq.ge)

end TauCeti.IsRegularLocalRing
